import { mkdirSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { deflateSync } from 'node:zlib';
import { createHash } from 'node:crypto';
import { Buffer } from 'node:buffer';

const W = 1024, H = 1024, N = W * H, CX = 512, CY = 486;
const LIMIT = 900 * 1024;
const started=Date.now();
let seed = 0x51a7c0de;
function rand(): number {
  seed = (seed + 0x6d2b79f5) | 0;
  let t = seed;
  t = Math.imul(t ^ (t >>> 15), t | 1);
  t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
  return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
}
const clamp = (x: number, a = 0, b = 1) => Math.max(a, Math.min(b, x));
const smooth = (a: number, b: number, x: number) => { const t = clamp((x-a)/(b-a)); return t*t*(3-2*t); };
function srgbToLin(c: number): number { c /= 255; return c <= .04045 ? c / 12.92 : ((c + .055) / 1.055) ** 2.4; }
function linToSrgb(c: number): number { c=clamp(c); return c<=.0031308?12.92*c:1.055*c**(1/2.4)-.055; }
function hash2(x: number, y: number): number {
  let h = Math.imul(x | 0, 0x45d9f3b) ^ Math.imul(y | 0, 0x27d4eb2d) ^ 0x9e3779b9;
  h = Math.imul(h ^ (h >>> 16), 0x45d9f3b); h = Math.imul(h ^ (h >>> 16), 0x45d9f3b);
  return ((h ^ (h >>> 16)) >>> 0) / 4294967295;
}
function noise(x: number, y: number): number {
  const ix = Math.floor(x), iy = Math.floor(y), fx = x - ix, fy = y - iy;
  const u = fx*fx*(3-2*fx), v = fy*fy*(3-2*fy);
  const a = hash2(ix,iy)*(1-u)+hash2(ix+1,iy)*u;
  const b = hash2(ix,iy+1)*(1-u)+hash2(ix+1,iy+1)*u;
  return a*(1-v)+b*v;
}
function fractal(x: number, y: number): number {
  return (noise(x,y)*.58 + noise(x*2.07+19.1,y*2.07-8.4)*.29 + noise(x*4.11-2.2,y*4.11+31.7)*.13) - .5;
}
const stops = [
  [128,0x1a0d08],[138,0x3d1b0a],[160,0x7a3a12],[190,0xc9762a],[218,0xe8a54b],
  [246,0xb4703a],[278,0x6e4a46],[310,0x40415c],[340,0x22243c],[360,0x0b0b14],
].map(([r,h]) => [r, srgbToLin((h>>16)&255), srgbToLin((h>>8)&255), srgbToLin(h&255)] as number[]);
function baseColor(r: number): [number,number,number] {
  if (r <= 120) return [0,0,0];
  if (r < 128) { const t=(r-120)/8; return [.012*t,.0045*t,.0025*t]; }
  let k = 0; while (k < stops.length-2 && r > stops[k+1][0]) k++;
  const a=stops[k], b=stops[k+1], t=clamp((r-a[0])/(b[0]-a[0]));
  return [a[1]+(b[1]-a[1])*t,a[2]+(b[2]-a[2])*t,a[3]+(b[3]-a[3])*t];
}
const grooveCount=900, grooveOffset=Array.from({length:grooveCount},()=>.34+rand()*.32);
const grooveWidth=Array.from({length:grooveCount},()=>.9+rand()*.45);
const grooveEnd=Array.from({length:grooveCount},()=>300+rand()*62);
const ridge=Array.from({length:grooveCount},(_,i)=>i%7===0);
const grooveStrength=Array.from({length:grooveCount},()=>.56+rand()*.09);
const scleralVeins=Array.from({length:7},(_,i)=>({
  side:i<4?-1:1, start:70+rand()*45, length:110+rand()*58,
  row:315+(i%4)*78+(rand()-.5)*22, slope:(rand()-.5)*.24, phase:rand()*6.28,
}));
const rgb = new Float32Array(N*3);
const radial = new Float32Array(N);
const thetaMap = new Float32Array(N);
const scleraVeinMask = new Float32Array(N);
for (let y=0;y<H;y++) for (let x=0;x<W;x++) {
  const i=y*W+x, dx=x+.5-CX, dy=y+.5-CY, r=Math.hypot(dx,dy), th=Math.atan2(dy,dx);
  radial[i]=r; thetaMap[i]=th;
  const p=i*3;
  if (r > 366) {
    const lx=266,ly=298,lightDist=Math.hypot(x+.5-lx,y+.5-ly),fall=clamp(1-lightDist/900);
    const light=.010+.17*fall**1.65;
    const lidDist=y+.5-lidEdge(x),shadow=.45*(1-smooth(0,45,lidDist));
    const shade=light*(1-shadow), warm=.94+.06*fall;
    rgb[p]=shade*warm; rgb[p+1]=shade*.91; rgb[p+2]=shade*.82;
    const blush=Math.exp(-(((Math.abs(dx)-445)/115)**2+((dy-90)/170)**2));
    rgb[p]*=1+.014*blush;rgb[p+1]*=1-.015*blush;rgb[p+2]*=1-.012*blush;
    let vein=0;
    for(const v of scleralVeins) {
      const u=(v.side<0?x:1023-x)-v.start;
      if(u<0||u>v.length)continue;
      const endFade=smooth(0,14,u)*(1-smooth(v.length-16,v.length,u));
      const curve=v.row+v.slope*u+4*Math.sin(u*.024+v.phase);
      const main=Math.exp(-((y+.5-curve)**2)/(2*1.15**2))*endFade;
      const bu=u-v.length*.48, branchY=curve+(bu>0?bu*.23:-bu*.18);
      const branch=(1-smooth(0,38,Math.abs(bu)))*Math.exp(-((y+.5-branchY)**2)/(2*.85**2))*endFade;
      vein=Math.max(vein,main,branch);
    }
    scleraVeinMask[i]=vein;
    continue;
  }
  if (r < 120) continue;
  let c=baseColor(r);
  if (r<=176) { const inner=.45+.55*smooth(120,176,r);c=c.map(v=>v*inner) as [number,number,number]; }
  if(r>=120&&r<124) {
    const rim=(1-smooth(120,123.5,r))*.022;
    c=[c[0]+rim*.9,c[1]+rim*.40,c[2]+rim*.16];
  }
  if(r>=128&&r<363) {
    const u=((th+Math.PI)/(Math.PI*2))*grooveCount, base=Math.floor(u), local=u-base;
    let gi=base%grooveCount, dist=Infinity;
    for(const candidate of [base-1,base,base+1]) {
      const ci=(candidate+grooveCount)%grooveCount;
      const cd=Math.abs((local+(base-candidate)-grooveOffset[ci])*Math.PI*2*r/grooveCount);
      if(cd<dist){dist=cd;gi=ci;}
    }
    const end=grooveEnd[gi], reach=smooth(128,145,r)*(1-smooth(end-12,end,r));
    const outerWidth=grooveWidth[gi], width=outerWidth*(.45+.55*smooth(128,end,r));
    const cover=1-smooth(width*.48,width*.92,dist);
    const fade=reach*(1-smooth(280,350,r));
    const strength=ridge[gi]?-.31: grooveStrength[gi];
    const factor=1-strength*cover*fade;
    c=c.map(v=>v*factor) as [number,number,number];
    const nv=fractal(th*34,r*.06)*.72+fractal(th*91,r*.31)*.48;
    const modulation=clamp(1+nv*.12+(hash2(x,y)-.5)*.12,.88,1.12);
    c=c.map(v=>v*modulation) as [number,number,number];
  }
  const wobble=Math.sin(th*5+.7)*3.2+Math.sin(th*11+2.1)*2.1+Math.sin(th*19)*.7;
  const rr=200+wobble, d=Math.abs(r-rr);
  const furrow=1-.32*Math.exp(-(((d-5.2)/1.5)**2))-.26*Math.exp(-(((d-8)/1.8)**2));
  const ring=(.65*Math.exp(-((d/2.5)**2))+.2*Math.exp(-((d/4.2)**2)))*furrow;
  c=[c[0]*(1+ring*.3)+ring*.035,c[1]*(1+ring*.19)+ring*.022,c[2]*(1+ring*.07)+ring*.008];
  for (const sr of [158,250]) {
    const broken=.5+.5*noise(th*11+sr,r*.13);
    const boost=.22*Math.exp(-(((r-sr)/1.65)**2))*(.35+.65*broken);
    c=[c[0]*(1+boost),c[1]*(1+boost),c[2]*(1+boost)];
  }
  const limbal=smooth(340,347,r), dark=smooth(359,362,r);
  c=[c[0]*(1-limbal*.72)*(1-dark*.85),c[1]*(1-limbal*.74)*(1-dark*.85),c[2]*(1-limbal*.68)*(1-dark*.85)];
  const rim=Math.exp(-(((r-361)/1.5)**2))*.035;
  c=[c[0]+rim*.38,c[1]+rim*.58,c[2]+rim];
  rgb[p]=c[0]; rgb[p+1]=c[1]; rgb[p+2]=c[2];
}

let softVeins=scleraVeinMask;
for(let pass=0;pass<2;pass++)softVeins=boxBlur(softVeins,2);
for(let i=0;i<N;i++)if(radial[i]>366&&softVeins[i]>.002) {
  const p=i*3,a=clamp(softVeins[i]*2.1)*.30;
  rgb[p]=rgb[p]*(1-a)+srgbToLin(0x6e)*a;
  rgb[p+1]=rgb[p+1]*(1-a)+srgbToLin(0x40)*a;
  rgb[p+2]=rgb[p+2]*(1-a)+srgbToLin(0x3c)*a;
}

// Face-on spiral galaxy with a 12 degree tilt, dusty bulge, and particulate arms.
const gal = new Float32Array(N*3), particleLayer=[new Float32Array(N),new Float32Array(N),new Float32Array(N)];
const gx0=528, gy0=470, tilt=Math.cos(12*Math.PI/180), turnsK=2.35/Math.log(88/10);
for(let n=0;n<6000;n++) {
  const u=rand(), radius=-30*Math.log(Math.exp(-10/30)-u*(Math.exp(-10/30)-Math.exp(-88/30)));
  const half=.55+radius*.012, arm=n&1;
  const theta=turnsK*Math.log(radius/10)+arm*Math.PI+(rand()*2-1)*half;
  const gx=gx0+Math.cos(theta)*radius, gy=gy0+Math.sin(theta)*radius*tilt;
  const hue=clamp((radius-10)/78), cr=1-.13*hue, cg=1-.48*hue, cb=1-.33*hue;
  const power=Math.min(.75,(.20+rand()*.42)*Math.exp(-radius/42)), size=.7+rand()*1.3, sigma=size*.52;
  const reach=Math.ceil(size*2.4);
  for(let y=Math.floor(gy-reach);y<=Math.ceil(gy+reach);y++)for(let x=Math.floor(gx-reach);x<=Math.ceil(gx+reach);x++) {
    if(x<0||y<0||x>=W||y>=H)continue;
    const dx=x+.5-gx,dy=y+.5-gy,d2=dx*dx+dy*dy;if(d2>reach*reach)continue;
    const p=y*W+x,v=power*Math.exp(-d2/(2*sigma*sigma));
    particleLayer[0][p]+=v*cr;particleLayer[1][p]+=v*cg;particleLayer[2][p]+=v*cb;
  }
}
const particleBlur=particleLayer.map(c=>{let v=c;for(let pass=0;pass<3;pass++)v=boxBlur(v,2);return v;});
for(let y=gy0-22;y<=gy0+22;y++)for(let x=gx0-22;x<=gx0+22;x++) {
  const dx=x+.5-gx0,dy=(y+.5-gy0)/tilt,r=Math.hypot(dx,dy),p=(y*W+x)*3;
  if(r>=120)continue;
  const hot=1.35/(1+(r/8)**2.2),amber=smooth(2,18,r);
  gal[p]=hot*(1-.08*amber);gal[p+1]=hot*(1-.35*amber);gal[p+2]=hot*(1-.62*amber);
}
const bulgeChannels=[0,1,2].map(c=>{let v=new Float32Array(N);for(let i=0;i<N;i++)v[i]=gal[i*3+c];for(let pass=0;pass<2;pass++)v=boxBlur(v,2);return v;});
for(let i=0;i<N;i++) {
  const x=i%W,y=(i/W)|0,dx=x+.5-gx0,dy=y+.5-gy0;
  const lane=Math.exp(-(((dy-1.2+.18*dx+.00075*dx*dx)/4.4)**2))*(1-smooth(14,25,Math.abs(dx)));
  const edge=smooth(120,115,radial[i]);
  if(radial[i]<120) for(let c=0;c<3;c++) {
    const p=i*3;rgb[p+c]=Math.max(0,(bulgeChannels[c][i]+particleBlur[c][i]*.55+particleLayer[c][i])*(1-.45*lane)*edge);
  }
}
// Upper-left wet gleam: a soft union of three circular falloffs, clipped to the iris.
const highlightCircles=[[250,300,34],[222,316,22],[268,288,14]];
for(let y=0;y<H;y++)for(let x=0;x<W;x++) {
  const p=(y*W+x)*3, dx=x+.5-CX,dy=y+.5-CY;
  const ellipse=(dx/510)**2+(dy/470)**2;
  if(ellipse>1.04) continue;
  let highlight=0;
  for(const [hx,hy,hr] of highlightCircles) {
    const d=Math.hypot(x+.5-hx,y+.5-hy),v=clamp(1-(d/hr)**2)**1.6;
    highlight=Math.min(1,highlight+v);
  }
  const r=radial[y*W+x],irisClip=(1-smooth(340,350,r))*smooth(128,136,r);
  const gleam=.9*highlight*irisClip;
  const dot=Math.exp(-(((x-754)**2+(y-690)**2)/(2*4*4)))*1.4;
  const glow=Math.exp(-(((x-754)**2+(y-690)**2)/(2*8*8)))*.12;
  const glint=Math.exp(-(((radial[y*W+x]-356)/1.5)**2))*.035*(smooth(180,320,y));
  const v=gleam+dot+glow+glint;
  rgb[p]+=v;rgb[p+1]+=v;rgb[p+2]+=v;
}

// The upper lid occludes the iris and casts a soft edge shadow onto the eye.
function lidEdge(x:number):number { return 300-.0414*(x-380)-.000455*(x-380)*(x-380); }
for(let y=0;y<H;y++)for(let x=0;x<W;x++) {
  const i=y*W+x,p=i*3,edge=lidEdge(x),d=y-edge;
  if(d < -1) {
    const grain=(noise(x*.035,y*.035)-.5)*.003, shade=.018+grain;
    rgb[p]=.002+shade*.55;rgb[p+1]=.0015+shade*.42;rgb[p+2]=.0015+shade*.4;
  } else if(d<13) {
    const sh=.34*Math.exp(-(d*d)/(2*5.2*5.2));
    rgb[p]*=1-sh;rgb[p+1]*=1-sh;rgb[p+2]*=1-sh;
  }
  const wet=Math.exp(-(((d-1.2)/.75)**2))*.045;
  rgb[p]+=wet;rgb[p+1]+=wet*.25;rgb[p+2]+=wet*.24;
}

// Nine curved, tapered lashes with a soft body and a warm upper rim.
const lash=new Float32Array(N),lashRim=new Float32Array(N);
function quad(t:number,p0:number,p1:number,p2:number):number { const u=1-t;return u*u*p0+2*u*t*p1+t*t*p2; }
const lashXs=[260,318,378,438,500,562,625,688,750];
for(const rootX of lashXs) {
  const rootY=lidEdge(rootX)+1,len=82+rand()*112,side=(rand()-.5)*2;
  const controlX=rootX+side*len*.22,endX=rootX+side*len*.42,endY=rootY+len;
  const maxW=2.05+rand()*.95,steps=100;
  for(let j=0;j<steps;j++) {
    const t=j/steps,t2=(j+1)/steps;
    const x=quad(t,rootX,controlX,endX),y=quad(t,rootY,rootY+len*.48,endY);
    const xx=quad(t2,rootX,controlX,endX),yy=quad(t2,rootY,rootY+len*.48,endY);
    const width=maxW*(1-t)**.82+.035,radius=width+5;
    const vx=xx-x,vy=yy-y,seg2=vx*vx+vy*vy,segLen=Math.sqrt(seg2)||1,nx=vy/segLen,ny=-vx/segLen;
    for(let py=Math.max(0,Math.floor(Math.min(y,yy)-radius));py<=Math.min(H-1,Math.ceil(Math.max(y,yy)+radius));py++)
      for(let px=Math.max(0,Math.floor(Math.min(x,xx)-radius));px<=Math.min(W-1,Math.ceil(Math.max(x,xx)+radius));px++) {
        const u=seg2?clamp(((px+.5-x)*vx+(py+.5-y)*vy)/seg2):0;
        const ox=px+.5-(x+u*vx),oy=py+.5-(y+u*vy),d=Math.hypot(ox,oy),id=py*W+px;
        const cov=1-smooth(width*.58,width+1.15,d);
        if(cov>lash[id])lash[id]=cov;
        const upper=ox*nx+oy*ny;
        const rim=smooth(width*.38,width*.9,d)*(1-smooth(width*.9,width+2,d))*smooth(-.2,.8,upper)*(.55+.45*(1-t));
        if(rim>lashRim[id])lashRim[id]=rim;
      }
  }
}
let lashSoft=lash,lashRimSoft=lashRim;
for(let pass=0;pass<4;pass++) { lashSoft=boxBlur(lashSoft,2);lashRimSoft=boxBlur(lashRimSoft,2); }
for(let i=0;i<N;i++) if(lash[i]>.001||lashSoft[i]>.001||lashRimSoft[i]>.001) {
  const p=i*3,a=clamp(lash[i]*.72+lashSoft[i]*.76)*.86, rim=lashRimSoft[i]*.075;
  rgb[p]=rgb[p]*(1-a)+rim;rgb[p+1]=rgb[p+1]*(1-a)+rim*.55;rgb[p+2]=rgb[p+2]*(1-a)+rim*.30;
}

// Chromatic displacement is kept sub-pixel so the radial grooves stay crisp.
const chroma=new Float32Array(rgb.length);
for(let y=0;y<H;y++)for(let x=0;x<W;x++) {
  const i=y*W+x,p=i*3,r=radial[i],dx=(x+.5-CX)/Math.max(1,r),dy=(y+.5-CY)/Math.max(1,r);
  for(let c=0;c<3;c++) {
    const scale=c===0?1.00025:c===2?.9998:1, sx=CX+(x+.5-CX)*scale-.5, sy=CY+(y+.5-CY)*scale-.5;
    const x0=Math.floor(sx),y0=Math.floor(sy),fx=sx-x0,fy=sy-y0;
    const sample=(xx:number,yy:number)=>xx<0||yy<0||xx>=W||yy>=H?0:rgb[(yy*W+xx)*3+c];
    chroma[p+c]=(sample(x0,y0)*(1-fx)+sample(x0+1,y0)*fx)*(1-fy)+(sample(x0,y0+1)*(1-fx)+sample(x0+1,y0+1)*fx)*fy;
  }
}
rgb.set(chroma);

function boxBlur(src:Float32Array, radius:number):Float32Array {
  const tmp=new Float32Array(N), out=new Float32Array(N), div=radius*2+1;
  for(let y=0;y<H;y++) { let sum=0,base=y*W; for(let k=-radius;k<=radius;k++)sum+=src[base+clamp(k,0,W-1)];
    for(let x=0;x<W;x++){tmp[base+x]=sum/div;sum+=src[base+Math.min(W-1,x+radius+1)]-src[base+Math.max(0,x-radius)];} }
  for(let x=0;x<W;x++){let sum=0;for(let k=-radius;k<=radius;k++)sum+=tmp[clamp(k,0,H-1)*W+x];
    for(let y=0;y<H;y++){out[y*W+x]=sum/div;sum+=tmp[Math.min(H-1,y+radius+1)*W+x]-tmp[Math.max(0,y-radius)*W+x];} }
  return out;
}
function bloom(sigma:number, strength:number):void {
  let layer=new Float32Array(N);
  for(let i=0;i<N;i++){const p=i*3,l=.2126*rgb[p]+.7152*rgb[p+1]+.0722*rgb[p+2];layer[i]=Math.max(0,l-.72);}
  const rad=Math.max(1,Math.round(sigma*.58));
  for(let k=0;k<3;k++)layer=boxBlur(layer,rad);
  for(let i=0;i<N;i++){const v=layer[i]*strength,p=i*3;rgb[p]+=v;rgb[p+1]+=v;rgb[p+2]+=v;}
}
bloom(2,.32);bloom(8,.14);

const bayer=[0,48,12,60,3,51,15,63,32,16,44,28,35,19,47,31,8,56,4,52,11,59,7,55,40,24,36,20,43,27,39,23,2,50,14,62,1,49,13,61,34,18,46,30,33,17,45,29,10,58,6,54,9,57,5,53,42,26,38,22,41,25,37,21];
function aces(x:number):number { return clamp((x*(2.51*x+.03))/(x*(2.43*x+.59)+.14)); }
function crc32(buf:Buffer):number { let c=0xffffffff;for(let i=0;i<buf.length;i++){c^=buf[i];for(let j=0;j<8;j++)c=(c>>>1)^((c&1)?0xedb88320:0);}return(c^0xffffffff)>>>0; }
function chunk(type:string,data:Buffer):Buffer { const t=Buffer.from(type),out=Buffer.alloc(12+data.length);out.writeUInt32BE(data.length,0);t.copy(out,4);data.copy(out,8);out.writeUInt32BE(crc32(Buffer.concat([t,data])),8+data.length);return out; }
function encode(quant5=false):Buffer {
  const raw=Buffer.alloc((W*3+1)*H), lut=new Uint8Array(64);
  for(let y=0;y<H;y++) {
    const row=y*(W*3+1);raw[row]=0;
    for(let x=0;x<W;x++) {
      const i=y*W+x,p=i*3,di=row+1+x*3;
  const vig=1-.12*clamp((radial[i]-360)/365);
      for(let c=0;c<3;c++) {
        let v=linToSrgb(aces(rgb[p+c]*vig));
        v=clamp(.5+(v-.5)*1.035);
        const noiseD=(bayer[(y&7)*8+(x&7)]/63-.5)*2/255;
        let q=clamp(v+noiseD)*255;
        if(quant5) q=Math.round(q/8)*8;
        raw[di+c]=Math.max(0,Math.min(255,Math.round(q)));
      }
    }
  }
  const ihdr=Buffer.alloc(13);ihdr.writeUInt32BE(W,0);ihdr.writeUInt32BE(H,4);ihdr[8]=8;ihdr[9]=2;
  return Buffer.concat([Buffer.from([137,80,78,71,13,10,26,10]),chunk('IHDR',ihdr),chunk('IDAT',deflateSync(raw,{level:9})),chunk('IEND',Buffer.alloc(0))]);
}
const outDir=process.env.MAKEFUN_OUTPUT_DIR || '/output';
mkdirSync(outDir,{recursive:true});
let png=encode();
if(png.length>LIMIT)png=encode(true);
if(png.length>LIMIT)throw new Error(`PNG exceeded 1 MiB after fallback quantisation (${png.length} bytes)`);
writeFileSync(join(outDir,'entry.png'),png);
// Deterministic value report used during development and for contest verification.
let sum=0,bright=0,dark=0,max=0,maxI=0;
const vals=new Uint8Array(N);
for(let i=0;i<N;i++) {
  const lum=(.2126*pngPixel(i,0)+.7152*pngPixel(i,1)+.0722*pngPixel(i,2));
  vals[i]=lum;sum+=lum;if(lum>245)bright++;if(lum<12)dark++;if(lum>max){max=lum;maxI=i;}
}
function pngPixel(i:number,c:number):number {
  const x=i%W,y=Math.floor(i/W),p=i*3,raw=linToSrgb(aces(rgb[p+c]*(1-.12*clamp((radial[i]-360)/365))));
  const v=clamp(.5+(raw-.5)*1.035);
  return Math.round(clamp(v+(bayer[(y&7)*8+(x&7)]/63-.5)*2/255)*255);
}
const band:number[]=[];let bandDiff=0,bandPairs=0,bandDark=0;
for(let y=0;y<H;y++)for(let x=0;x<W;x++) { const i=y*W+x;if(radial[i]>=130&&radial[i]<=355){const l=vals[i];band.push(l);if(l<20)bandDark++;if(x+1<W&&radial[i+1]>=130&&radial[i+1]<=355){bandDiff+=Math.abs(l-vals[i+1]);bandPairs++;}} }
const bandMean=band.reduce((a,b)=>a+b,0)/band.length,bandStd=Math.sqrt(band.reduce((a,b)=>a+(b-bandMean)**2,0)/band.length);
band.sort((a,b)=>a-b);
vals.sort();
const annuli:Record<string,number>={};
const annulusBounds=[[0,8],[8,18],[18,32],[32,50],[50,72]],annulusSums=annulusBounds.map(()=>0),annulusCounts=annulusBounds.map(()=>0);
for(let y=gy0-72;y<=gy0+72;y++)for(let x=gx0-72;x<=gx0+72;x++) {
  const d=Math.hypot(x+.5-gx0,y+.5-gy0);let k=annulusBounds.findIndex(([a,b])=>d>=a&&d<b);
  if(k<0)continue;const i=y*W+x,l=.2126*pngPixel(i,0)+.7152*pngPixel(i,1)+.0722*pngPixel(i,2);
  annulusSums[k]+=l;annulusCounts[k]++;
}
for(let k=0;k<annulusBounds.length;k++)annuli[`${annulusBounds[k][0]}-${annulusBounds[k][1]}px`]=annulusSums[k]/annulusCounts[k];
const annulusValues=Object.values(annuli),annulusPass=annulusValues.every((v,i)=>i===0||v<=annulusValues[i-1]*.75);
console.log(JSON.stringify({bytes:png.length,elapsedMs:Date.now()-started,sha256:createHash('sha256').update(png).digest('hex'),mean:sum/N,above245:bright/N*100,below12:dark/N*100,p50:vals[Math.floor(N*.5)],p90:vals[Math.floor(N*.9)],p98:vals[Math.floor(N*.98)],brightest:{x:maxI%W,y:Math.floor(maxI/W),luminance:max},galaxyAnnuliLuminance:annuli,galaxyAnnuliPass25PercentDrop:annulusPass,irisBand:{stddev:bandStd,localContrast:bandDiff/bandPairs,darkest5PercentMedian:band[Math.floor(band.length*.05)],below20Percent:bandDark/band.length*100}},null,2));
