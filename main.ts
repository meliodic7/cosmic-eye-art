import { mkdirSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { createHash } from 'node:crypto';
import { deflateSync, inflateSync } from 'node:zlib';

// A softly lit, close-up eye assembled in linear-light RGB and encoded as PNG.
const SIZE = 1024, PIXELS = SIZE * SIZE, CENTER_X = 512, CENTER_Y = 486;
const LIMIT = 950_000;
const startedAt = Date.now();
const color = new Float32Array(PIXELS * 3);
const radiusAt = new Float32Array(PIXELS);
let randomState = 0x51a7c0de;

function random(): number {
  randomState = (randomState + 0x6d2b79f5) | 0;
  let t = randomState;
  t = Math.imul(t ^ (t >>> 15), t | 1);
  t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
  return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
}
const clamp = (v: number, lo = 0, hi = 1) => Math.max(lo, Math.min(hi, v));
const smooth = (a: number, b: number, v: number) => { const t = clamp((v - a) / (b - a)); return t * t * (3 - 2 * t); };
function linear(v: number): number { v /= 255; return v <= .04045 ? v / 12.92 : ((v + .055) / 1.055) ** 2.4; }
function srgb(v: number): number { v = clamp(v); return v <= .0031308 ? 12.92 * v : 1.055 * v ** (1 / 2.4) - .055; }
function hash2(x: number, y: number): number {
  let h = Math.imul(x | 0, 0x45d9f3b) ^ Math.imul(y | 0, 0x27d4eb2d) ^ 0x9e3779b9;
  h = Math.imul(h ^ (h >>> 16), 0x45d9f3b); h = Math.imul(h ^ (h >>> 16), 0x45d9f3b);
  return ((h ^ (h >>> 16)) >>> 0) / 4294967295;
}
function noise(x: number, y: number): number {
  const ix = Math.floor(x), iy = Math.floor(y), fx = x - ix, fy = y - iy;
  const u = fx * fx * (3 - 2 * fx), v = fy * fy * (3 - 2 * fy);
  const a = hash2(ix, iy) * (1 - u) + hash2(ix + 1, iy) * u;
  const b = hash2(ix, iy + 1) * (1 - u) + hash2(ix + 1, iy + 1) * u;
  return a * (1 - v) + b * v;
}
function fnoise(x: number, y: number): number {
  return noise(x, y) * .58 + noise(x * 2.07 + 19.1, y * 2.07 - 8.4) * .29 + noise(x * 4.11 - 2.2, y * 4.11 + 31.7) * .13 - .5;
}
function at(x: number, y: number): number { return (y * SIZE + x) * 3; }
function lid(x: number): number { return 300 - .0414 * (x - 380) - .000455 * (x - 380) ** 2; }

const paletteStops = [[128,0x1a0d08],[138,0x3d1b0a],[160,0x7a3a12],[190,0xc9762a],[218,0xe8a54b],[246,0xb4703a],[278,0x6e4a46],[310,0x40415c],[340,0x22243c],[360,0x0b0b14]].map(([r,h]) => [r, linear((h >> 16) & 255), linear((h >> 8) & 255), linear(h & 255)] as number[]);
function irisPigment(r: number): [number, number, number] {
  if (r <= 120) return [0, 0, 0];
  if (r < 128) { const q = (r - 120) / 8; return [.012 * q, .0045 * q, .0025 * q]; }
  let k = 0; while (k < paletteStops.length - 2 && r > paletteStops[k + 1][0]) k++;
  const a = paletteStops[k], b = paletteStops[k + 1], t = clamp((r - a[0]) / (b[0] - a[0]));
  return [a[1] + (b[1] - a[1]) * t, a[2] + (b[2] - a[2]) * t, a[3] + (b[3] - a[3]) * t];
}

// Each ray gets independent geometry and strength; multi-scale noise disrupts the fan.
const RAYS = 1500;
const rayOffset = Array.from({ length: RAYS }, (_, i) => .34 + hash2(i, 11) * .32);
const rayWidth = Array.from({ length: RAYS }, (_, i) => .7 + hash2(i, 23) * 2.5);
const rayEnd = Array.from({ length: RAYS }, (_, i) => 296 + hash2(i, 37) * 64);
const rayShade = Array.from({ length: RAYS }, (_, i) => hash2(i, 51) < .125 ? -(0.10 + hash2(i, 53) * .15) : .60 + hash2(i, 51) * .25);
const rayTaper = Array.from({ length: RAYS }, (_, i) => .55 + hash2(i, 67) * .45);
const escapeRays = [
  { angle: -.92, width: 5.7, strength: .035 }, { angle: -.18, width: 3.8, strength: .028 },
  { angle: .74, width: 8.3, strength: .042 }, { angle: 2.16, width: 4.6, strength: .032 },
  { angle: 2.83, width: 6.4, strength: .038 },
].map((ray, i) => ({ ...ray, angle: ray.angle + (hash2(i, 809) - .5) * .19, width: ray.width * (.84 + hash2(i, 811) * .34), strength: ray.strength * (.82 + hash2(i, 813) * .34) }));

type LashSample = { x: number; y: number; w: number; t: number };
type Lash = { samples: LashSample[]; x0: number; x1: number; y0: number; y1: number };
const lashCoverage = { count: 0 };
function buildLashes(): Lash[] {
  const roots = [184, 267, 352, 438, 490, 574, 649, 731, 817];
  return roots.map((baseX, n) => {
    const rootX = baseX + (hash2(n, 101) - .5) * 20, rootY = lid(rootX) + 1;
    const tLength = n === 3 || n === 5 ? .96 : hash2(n, 103);
    const length = 90 + tLength * 120, dir = n === 3 ? 1 : n === 5 ? -1 : (hash2(n, 107) < .5 ? -1 : 1);
    const bend = dir * (20 + hash2(n, 109) * 25), w0 = 3 + hash2(n, 113) * 1.5;
    const x1 = rootX + bend * .45, y1 = rootY + length * .31, x2 = rootX + bend * 1.35, y2 = rootY + length * .72;
    const x3 = rootX + bend * 1.75, y3 = rootY + length, samples: LashSample[] = [];
    for (let step = 0; step < 48; step++) {
      const t = step / 47;
      samples.push({ x: cubic(t, rootX, x1, x2, x3), y: cubic(t, rootY, y1, y2, y3), w: w0 * (1 - t) ** .85, t });
    }
    const pad = w0 + 2.2 + 1;
    return { samples, x0: Math.max(0, Math.floor(Math.min(...samples.map(s => s.x)) - pad)), x1: Math.min(SIZE - 1, Math.ceil(Math.max(...samples.map(s => s.x)) + pad)), y0: Math.max(0, Math.floor(rootY - pad)), y1: Math.min(SIZE - 1, Math.ceil(y3 + pad)) };
  });
}
const lashes = buildLashes();
function paintLashesAt(x: number, y: number, p: number): void {
  let darkest = 0, redRim = 0, greenRim = 0, blueRim = 0;
  for (const lash of lashes) {
    if (x < lash.x0 || x > lash.x1 || y < lash.y0 || y > lash.y1) continue;
    let d2 = Infinity, nearest: LashSample | undefined;
    for (const sample of lash.samples) {
      const q = (x + .5 - sample.x) ** 2 + (y + .5 - sample.y) ** 2;
      if (q < d2) { d2 = q; nearest = sample; }
    }
    if (!nearest) continue;
    const k = Math.exp(-((Math.sqrt(d2) / (nearest.w + 2.2)) ** 2));
    const darken = k * (.72 - .35 * nearest.t);
    if (darken > darkest) darkest = darken;
    if (y + .5 < nearest.y) { redRim += k * .05 * linear(255); greenRim += k * .05 * linear(190); blueRim += k * .05 * linear(112); }
  }
  if (darkest >= .25) lashCoverage.count++;
  if (darkest || redRim) {
    color[p] = color[p] * (1 - darkest) + redRim;
    color[p + 1] = color[p + 1] * (1 - darkest) + greenRim;
    color[p + 2] = color[p + 2] * (1 - darkest) + blueRim;
  }
}

function makeEye(): void {
  for (let y = 0; y < SIZE; y++) for (let x = 0; x < SIZE; x++) {
    const i = y * SIZE + x, dx = x + .5 - CENTER_X, dy = y + .5 - CENTER_Y, r = Math.hypot(dx, dy), theta = Math.atan2(dy, dx), p = i * 3;
    radiusAt[i] = r;
    if (r > 366) {
      const nx = (x + .5 - 392) / 650, ny = (y + .5 - 278) / 680;
      const spherical = clamp((nx * nx + ny * ny) / 1.5);
      const t = smooth(0, 1, spherical);
      const light = [sceneForSrgb(142), sceneForSrgb(135), sceneForSrgb(124)], shadow = [sceneForSrgb(42), sceneForSrgb(39), sceneForSrgb(35)];
      const bottom = .12 * smooth(730, 930, y + .5), shade = clamp(t + bottom);
      for (let c = 0; c < 3; c++) color[p + c] = light[c] * (1 - shade) + shadow[c] * shade;
      paintLashesAt(x, y, p);
      continue;
    }
    const pupilRim = 120 + Math.sin(theta * 7 + .4) * .72 + Math.sin(theta * 13 + 1.7) * .31;
    if (r < pupilRim) { paintLashesAt(x, y, p); continue; }
    let c = irisPigment(r);
    // The inner collar recovers continuously into the fibres, with only a narrow pupil shadow.
    const collar = .72 + .28 * smooth(120, 210, r);
    const pupilShadow = .34 + .66 * smooth(pupilRim, pupilRim + 3, r);
    c = c.map(v => v * collar * pupilShadow) as [number,number,number];
    if (r > 176 && r < 340) { const midLift = 3.0 * (1 - .35 * smooth(300, 340, r)); c = c.map(v => v * (1 + midLift)) as [number,number,number]; }
    if (r >= 120 && r < 124) { const rim = (1 - smooth(120, 123.5, r)) * .022; c = [c[0] + rim * .9, c[1] + rim * .4, c[2] + rim * .16]; }
    if (r >= 128 && r < 363) {
      const u = ((theta + Math.PI) / (2 * Math.PI)) * RAYS, base = Math.floor(u), local = u - base;
      let ray = base % RAYS, nearest = Infinity;
      for (const candidate of [base - 1, base, base + 1]) {
        const ci = (candidate + RAYS) % RAYS, distance = Math.abs((local + base - candidate - rayOffset[ci]) * 2 * Math.PI * r / RAYS);
        if (distance < nearest) { nearest = distance; ray = ci; }
      }
      const end = rayEnd[ray], reach = smooth(128, 148, r) * (1 - smooth(end - 16, end, r));
      const width = rayWidth[ray] * (.38 + .62 * smooth(128, end, r));
      const strand = 1 - smooth(width * .42, width * .98, nearest);
      const broken = clamp(1 + fnoise(theta * 35, r * .075) * .35 + fnoise(theta * 91, r * .29) * .28 + (hash2(x, y) - .5) * .1, .62, 1.25);
      const limbusFade = 1 - .45 * smooth(300, 360, r);
      if (rayShade[ray] < 0) c = c.map(v => v * (1 + (-rayShade[ray]) * strand * reach * rayTaper[ray] * broken)) as [number,number,number];
      else c = c.map(v => v * (1 - rayShade[ray] * strand * reach * rayTaper[ray] * broken * limbusFade)) as [number,number,number];
      const mottling = clamp(1 + fnoise(theta * 25, r * .12) * .26 + (hash2(x, y) - .5) * .1, .82, 1.18);
      c = c.map(v => v * mottling) as [number,number,number];
    }
    const wobble = Math.sin(theta * 5 + .7) * 3.2 + Math.sin(theta * 11 + 2.1) * 2.1 + Math.sin(theta * 19) * .7;
    const ridgeDist = Math.abs(r - (200 + wobble));
    const furrow = 1 - .40 * Math.exp(-(((ridgeDist - 5.2) / 1.5) ** 2)) - .34 * Math.exp(-(((ridgeDist - 8) / 1.8) ** 2));
    const ring = (.65 * Math.exp(-((ridgeDist / 2.5) ** 2)) + .2 * Math.exp(-((ridgeDist / 4.2) ** 2))) * furrow;
    c = [c[0] * (1 + ring * .3) + ring * .035, c[1] * (1 + ring * .19) + ring * .022, c[2] * (1 + ring * .07) + ring * .008];
    for (const band of [158, 250]) { const glimmer = .22 * Math.exp(-(((r - band) / 1.65) ** 2)) * (.35 + .65 * (.5 + .5 * noise(theta * 11 + band, r * .13))); c = c.map(v => v * (1 + glimmer)) as [number,number,number]; }
    const outerLift = .20 * smooth(300, 340, r);
    c = c.map(v => v * (1 + outerLift)) as [number,number,number];
    const limbal = smooth(340, 347, r), edge = smooth(359, 362, r);
    c = [c[0] * (1 - limbal * .58) * (1 - edge * .85), c[1] * (1 - limbal * .60) * (1 - edge * .85), c[2] * (1 - limbal * .53) * (1 - edge * .85)];
    const lip = Math.exp(-(((r - 359.5) / 1.45) ** 2)) * .055;
    color[p] = c[0] + lip * .38; color[p + 1] = c[1] + lip * .58; color[p + 2] = c[2] + lip;
    paintLashesAt(x, y, p);
  }
}

function blur(source: Float32Array, radius: number): Float32Array {
  const temp = new Float32Array(PIXELS), result = new Float32Array(PIXELS), span = radius * 2 + 1;
  for (let y = 0; y < SIZE; y++) {
    const row = y * SIZE; let sum = 0;
    for (let k = -radius; k <= radius; k++) sum += source[row + clamp(k, 0, SIZE - 1)];
    for (let x = 0; x < SIZE; x++) { temp[row + x] = sum / span; sum += source[row + Math.min(SIZE - 1, x + radius + 1)] - source[row + Math.max(0, x - radius)]; }
  }
  for (let x = 0; x < SIZE; x++) {
    let sum = 0; for (let k = -radius; k <= radius; k++) sum += temp[clamp(k, 0, SIZE - 1) * SIZE + x];
    for (let y = 0; y < SIZE; y++) { result[y * SIZE + x] = sum / span; sum += temp[Math.min(SIZE - 1, y + radius + 1) * SIZE + x] - temp[Math.max(0, y - radius) * SIZE + x]; }
  }
  return result;
}

function gaussianBlur(source: Float32Array, sigma: number): Float32Array {
  const radius = Math.ceil(sigma * 3), weights = new Float32Array(radius * 2 + 1);
  let total = 0;
  for (let k = -radius; k <= radius; k++) { const w = Math.exp(-(k * k) / (2 * sigma * sigma)); weights[k + radius] = w; total += w; }
  for (let k = 0; k < weights.length; k++) weights[k] /= total;
  const temp = new Float32Array(PIXELS), result = new Float32Array(PIXELS);
  for (let y = 0; y < SIZE; y++) for (let x = 0; x < SIZE; x++) {
    let sum = 0; for (let k = -radius; k <= radius; k++) sum += source[y * SIZE + clamp(x + k, 0, SIZE - 1)] * weights[k + radius];
    temp[y * SIZE + x] = sum;
  }
  for (let y = 0; y < SIZE; y++) for (let x = 0; x < SIZE; x++) {
    let sum = 0; for (let k = -radius; k <= radius; k++) sum += temp[clamp(y + k, 0, SIZE - 1) * SIZE + x] * weights[k + radius];
    result[y * SIZE + x] = sum;
  }
  return result;
}

function addScleraVeins(): void {
  const paths = [
    [[174, 344], [225, 352], [278, 394]], [[132, 474], [187, 470], [239, 504]],
    [[786, 344], [844, 365], [894, 414]], [[899, 505], [853, 532], [808, 571]],
    [[311, 851], [366, 828], [421, 818]], [[499, 871], [555, 837], [610, 822]],
    [[686, 819], [743, 835], [794, 862]],
  ];
  const mask = new Float32Array(PIXELS);
  for (const [[x0,y0],[x1,y1],[x2,y2]] of paths) {
    const length = Math.hypot(x1 - x0, y1 - y0) + Math.hypot(x2 - x1, y2 - y1);
    for (let step = 0; step <= Math.ceil(length); step++) {
      const t = step / Math.ceil(length), q = 1 - t;
      const x = q*q*x0 + 2*q*t*x1 + t*t*x2, y = q*q*y0 + 2*q*t*y1 + t*t*y2;
      for (let py = Math.max(0, Math.floor(y - 5)); py <= Math.min(SIZE - 1, Math.ceil(y + 5)); py++) for (let px = Math.max(0, Math.floor(x - 5)); px <= Math.min(SIZE - 1, Math.ceil(x + 5)); px++) {
        const d2 = (px + .5 - x) ** 2 + (py + .5 - y) ** 2, i = py * SIZE + px;
        mask[i] = Math.max(mask[i], .20 * Math.exp(-d2 / 3.2));
      }
    }
  }
  const soft = gaussianBlur(mask, 2), vein = [linear(103), linear(87), linear(73)];
  for (let i = 0; i < PIXELS; i++) if (radiusAt[i] > 366 && soft[i] > .001) {
    const a = Math.min(.20, soft[i]), p = i * 3;
    for (let c = 0; c < 3; c++) color[p + c] = color[p + c] * (1 - a) + vein[c] * a;
  }
}

// A continuous, warm spiral glow sits beneath the resolved galaxy particles.
function paintGalaxy(): void {
  const cx = 528, cy = 468, tilt = Math.cos(12 * Math.PI / 180), k = 2.4;
  const particles = [new Float32Array(PIXELS), new Float32Array(PIXELS), new Float32Array(PIXELS)];
  for (let n = 0; n < 12000; n++) {
    const u = random(), r = -34 * Math.log(Math.exp(-4 / 34) - u * (Math.exp(-4 / 34) - Math.exp(-104 / 34)));
    const arm = n & 1, spread = .55 + r * .012, offsetSample = random() * 2 - 1;
    const theta = k * Math.log(r / 4) + arm * Math.PI + Math.sign(offsetSample) * spread * Math.abs(offsetSample) ** 2;
    const px = cx + Math.cos(theta) * r, py = cy + Math.sin(theta) * r * tilt;
    const hue = smooth(5, 88, r), cream = [linear(255), linear(240), linear(210)], rose = [linear(217), linear(138), linear(132)];
    const tint = cream.map((v, c) => v * (1 - hue) + rose[c] * hue);
    const power = .25 + random() * .25, size = .7 + random() * .9, sigma = size * .48, reach = Math.ceil(size * 2.2);
    for (let y = Math.floor(py - reach); y <= Math.ceil(py + reach); y++) for (let x = Math.floor(px - reach); x <= Math.ceil(px + reach); x++) {
      if (x < 0 || y < 0 || x >= SIZE || y >= SIZE) continue;
      const ddx = x + .5 - px, ddy = y + .5 - py, d2 = ddx * ddx + ddy * ddy;
      if (d2 > reach * reach) continue;
      const index = y * SIZE + x, value = power * Math.exp(-d2 / (2 * sigma * sigma));
      for (let c = 0; c < 3; c++) particles[c][index] = Math.max(particles[c][index], value * tint[c]);
    }
  }
  const softenedParticles = particles.map(layer => blur(layer, 2));
  const armGlow = new Float32Array(PIXELS * 3), bulge = new Float32Array(PIXELS * 3);
  const cream = [linear(255), linear(217), linear(160)], rose = [linear(196), linear(97), linear(79)];
  const warmWhite = [linear(255), linear(247), linear(231)], amber = [linear(255), linear(177), linear(91)];
  for (let y = cy - 112; y <= cy + 112; y++) for (let x = cx - 112; x <= cx + 112; x++) {
    const dx = x + .5 - cx, dy = (y + .5 - cy) / tilt, r = Math.hypot(dx, dy), p = (y * SIZE + x) * 3;
    if (r > 112 || r < 1) continue;
    const theta = Math.atan2(dy, dx), phase = theta - k * Math.log(r / 4);
    const wrapped = Math.atan2(Math.sin(phase), Math.cos(phase)), distance = Math.abs(wrapped) * r / Math.sqrt(1 + k * k);
    const width = 6 + (r - 10) * (16 / 94), arm = (.45 - .33 * smooth(10, 104, r)) * Math.exp(-((distance / width) ** 2));
    const hue = smooth(10, 104, r);
    const core = .35 + .60 / (1 + (r / 9) ** 2.2), coreHue = smooth(0, 24, r);
    for (let c = 0; c < 3; c++) {
      armGlow[p + c] = arm * (cream[c] * (1 - hue) + rose[c] * hue);
      bulge[p + c] = core * (warmWhite[c] * (1 - coreHue) + amber[c] * coreHue);
    }
  }
  for (let i = 0; i < PIXELS; i++) if (radiusAt[i] < 126) {
    const x = i % SIZE, y = (i / SIZE) | 0, dx = x + .5 - cx, dy = y + .5 - cy;
    const lane = dy > 0 && Math.hypot(dx, dy) < 30 ? Math.exp(-(((dy - 13 + .10 * dx + .00035 * dx * dx) / 14) ** 2)) * .30 : 0;
    const edgeFade = 1 - smooth(108, 112, radiusAt[i]), p = i * 3, particleFade = Math.exp(-Math.hypot(dx, dy) / 30);
    if (radiusAt[i] < 112) {
      const haze = .0008 + .0025 * radiusAt[i] / 120;
      for (let c = 0; c < 3; c++) {
        const warmHaze = haze * [1, .62, .22][c];
        const glow = armGlow[p + c] + bulge[p + c];
        color[p + c] = Math.max(0, (glow + (softenedParticles[c][i] * .5 + particles[c][i]) * particleFade) * (1 - lane) * edgeFade) + warmHaze;
      }
    }
    else {
      const rim = .12 * (1 - (120 - radiusAt[i]) / 6);
      color[p] += rim * .10; color[p + 1] += rim * .038; color[p + 2] += rim * .008;
    }
  }
}

function addWetLight(): void {
  const hx = 300, hy = 355, theta = Math.atan2(hy - CENTER_Y, hx - CENTER_X) + Math.PI / 2;
  const tx = Math.cos(theta), ty = Math.sin(theta), nx = -ty, ny = tx;
  const layers = [[34, .65], [22, .52], [14, .42]];
  for (let y = 0; y < SIZE; y++) for (let x = 0; x < SIZE; x++) {
    const i = y * SIZE + x, p = i * 3, r = radiusAt[i];
    if (r < 120 + Math.sin(Math.atan2(y + .5 - CENTER_Y, x + .5 - CENTER_X) * 7 + .4) * .72 + Math.sin(Math.atan2(y + .5 - CENTER_Y, x + .5 - CENTER_X) * 13 + 1.7) * .31) continue;
    const theta = Math.atan2(y + .5 - CENTER_Y, x + .5 - CENTER_X);
    if (r >= 120 && r <= 300) for (const ray of escapeRays) {
      let da = Math.abs(theta - ray.angle); da = Math.min(da, Math.PI * 2 - da);
      const shape = Math.exp(-((da / (ray.width * Math.PI / 360)) ** 4)) * (1 + .18 * fnoise(theta * 8 + ray.angle, r * .035));
      const fade = smooth(120, 142, r) * (1 - smooth(276, 300, r));
      const light = ray.strength * shape * fade;
      color[p] += light * .18; color[p + 1] += light * .075; color[p + 2] += light * .018;
    }
    if (r < 352) {
      const dx = x + .5 - hx, dy = y + .5 - hy, along = dx * tx + dy * ty, across = dx * nx + dy * ny;
      const arc = Math.exp(-((across / 10.5) ** 2)) * Math.exp(-((along / 47) ** 6));
      let shine = 0;
      for (const [radius, strength] of layers) {
        const d = Math.hypot(along / 1.32, across);
        shine += strength * clamp(1 - (d / radius) ** 2) ** 1.6;
      }
      const glint = shine * arc;
      color[p] += glint; color[p + 1] += glint; color[p + 2] += glint;
      if (Math.abs(dx) < .55 && Math.abs(dy) < .55) color[p] = color[p + 1] = color[p + 2] = 40;
    }
    const dot = Math.exp(-((x - 754) ** 2 + (y - 690) ** 2) / 32) * 1.4;
    const glow = Math.exp(-((x - 754) ** 2 + (y - 690) ** 2) / 128) * .12;
    const amount = dot + glow; color[p] += amount; color[p + 1] += amount; color[p + 2] += amount;
  }
}

function drawLid(): void {
  for (let y = 0; y < SIZE; y++) for (let x = 0; x < SIZE; x++) {
    const p = at(x, y), d = y + .5 - lid(x);
    if (d < -1) { const grain = (noise(x * .035, y * .035) - .5) * .0007; color[p] = .0054 + grain; color[p + 1] = .0037 + grain * .72; color[p + 2] = .0040 + grain * .75; }
    else if (d < 150) { const s = .45 * Math.exp(-(d * d) / (2 * 45 ** 2)); color[p] *= 1 - s; color[p + 1] *= 1 - s; color[p + 2] *= 1 - s; }
  }
}

function cubic(t: number, a: number, b: number, c: number, d: number): number { const q = 1 - t; return q*q*q*a + 3*q*q*t*b + 3*q*t*t*c + t*t*t*d; }
function finishColor(): void {
  // Tiny radial chromatic split and a restrained highlight bloom.
  const shifted = new Float32Array(color.length);
  for (let y = 0; y < SIZE; y++) for (let x = 0; x < SIZE; x++) {
    const p = at(x, y);
    for (let c = 0; c < 3; c++) {
      const scale = c === 0 ? 1.00025 : c === 2 ? .9998 : 1, sx = CENTER_X + (x + .5 - CENTER_X) * scale - .5, sy = CENTER_Y + (y + .5 - CENTER_Y) * scale - .5;
      const x0 = Math.floor(sx), y0 = Math.floor(sy), fx = sx - x0, fy = sy - y0;
      const sample = (xx: number, yy: number) => xx < 0 || yy < 0 || xx >= SIZE || yy >= SIZE ? 0 : color[at(xx, yy) + c];
      shifted[p + c] = (sample(x0, y0) * (1 - fx) + sample(x0 + 1, y0) * fx) * (1 - fy) + (sample(x0, y0 + 1) * (1 - fx) + sample(x0 + 1, y0 + 1) * fx) * fy;
    }
  }
  color.set(shifted);
  for (const [radius, strength] of [[1, .32], [5, .14]]) {
    let bright = new Float32Array(PIXELS);
    for (let i = 0; i < PIXELS; i++) { const p = i * 3; bright[i] = Math.max(0, .2126 * color[p] + .7152 * color[p + 1] + .0722 * color[p + 2] - .72); }
    for (let j = 0; j < 3; j++) bright = blur(bright, radius);
    for (let i = 0; i < PIXELS; i++) { const v = bright[i] * strength, p = i * 3; color[p] += v; color[p + 1] += v; color[p + 2] += v; }
  }
}

const bayer = [0,48,12,60,3,51,15,63,32,16,44,28,35,19,47,31,8,56,4,52,11,59,7,55,40,24,36,20,43,27,39,23,2,50,14,62,1,49,13,61,34,18,46,30,33,17,45,29,10,58,6,54,9,57,5,53,42,26,38,22,41,25,37,21];
const aces = (v: number) => clamp(v * (2.51 * v + .03) / (v * (2.43 * v + .59) + .14));
function sceneForSrgb(byte: number): number {
  const mapped = linear(clamp(.5 + (byte / 255 - .5) / 1.035) * 255), a = 2.43 * mapped - 2.51, b = .59 * mapped - .03, c = .14 * mapped;
  return (-b - Math.sqrt(b * b - 4 * a * c)) / (2 * a);
}
function crc32(data: Buffer): number { let crc = 0xffffffff; for (const byte of data) { crc ^= byte; for (let j = 0; j < 8; j++) crc = (crc >>> 1) ^ ((crc & 1) ? 0xedb88320 : 0); } return (crc ^ 0xffffffff) >>> 0; }
function pngChunk(type: string, data: Buffer): Buffer { const tag = Buffer.from(type), out = Buffer.alloc(data.length + 12); out.writeUInt32BE(data.length, 0); tag.copy(out, 4); data.copy(out, 8); out.writeUInt32BE(crc32(Buffer.concat([tag, data])), data.length + 8); return out; }
function encode(quantize = false): Buffer {
  const raw = Buffer.alloc((SIZE * 3 + 1) * SIZE);
  for (let y = 0; y < SIZE; y++) {
    const row = y * (SIZE * 3 + 1); raw[row] = 0;
    for (let x = 0; x < SIZE; x++) {
      const i = y * SIZE + x, p = i * 3, target = row + 1 + x * 3, vignette = 1 - .12 * clamp((radiusAt[i] - 360) / 365);
      for (let c = 0; c < 3; c++) {
        const mapped = srgb(aces(color[p + c] * vignette)), adjusted = clamp(.5 + (mapped - .5) * 1.035);
        let value = clamp(adjusted + (bayer[(y & 7) * 8 + (x & 7)] / 63 - .5) * 2 / 255) * 255;
        if (quantize) value = Math.round(value / 4) * 4;
        raw[target + c] = Math.round(clamp(value, 0, 255));
      }
    }
  }
  const header = Buffer.alloc(13); header.writeUInt32BE(SIZE, 0); header.writeUInt32BE(SIZE, 4); header[8] = 8; header[9] = 2;
  return Buffer.concat([Buffer.from([137,80,78,71,13,10,26,10]), pngChunk('IHDR', header), pngChunk('IDAT', deflateSync(raw, { level: 9 })), pngChunk('IEND', Buffer.alloc(0))]);
}

function decodePng(png: Buffer): Buffer {
  let pos = 8; const idat: Buffer[] = [];
  while (pos < png.length) { const length = png.readUInt32BE(pos), type = png.toString('ascii', pos + 4, pos + 8); if (type === 'IDAT') idat.push(png.subarray(pos + 8, pos + 8 + length)); pos += length + 12; if (type === 'IEND') break; }
  const filtered = inflateSync(Buffer.concat(idat)), stride = SIZE * 3, raw = Buffer.alloc(stride * SIZE);
  for (let y = 0; y < SIZE; y++) {
    const source = y * (stride + 1), filter = filtered[source], row = y * stride, prior = row - stride;
    for (let x = 0; x < stride; x++) {
      const left = x >= 3 ? raw[row + x - 3] : 0, above = y ? raw[prior + x] : 0, upperLeft = y && x >= 3 ? raw[prior + x - 3] : 0;
      let predictor = 0;
      if (filter === 1) predictor = left;
      else if (filter === 2) predictor = above;
      else if (filter === 3) predictor = Math.floor((left + above) / 2);
      else if (filter === 4) { const a = left, b = above, c = upperLeft, p = a + b - c, pa = Math.abs(p - a), pb = Math.abs(p - b), pc = Math.abs(p - c); predictor = pa <= pb && pa <= pc ? a : pb <= pc ? b : c; }
      raw[row + x] = (filtered[source + 1 + x] + predictor) & 255;
    }
  }
  return raw;
}

makeEye(); addScleraVeins(); paintGalaxy(); addWetLight(); drawLid(); finishColor();
const outputDir = process.env.MAKEFUN_OUTPUT_DIR || '/output'; mkdirSync(outputDir, { recursive: true });
let quantized = false;
let png = encode(); if (png.length > LIMIT) { quantized = true; png = encode(true); }
if (png.length > LIMIT) throw new Error(`PNG exceeds 950000 bytes (${png.length} bytes)`);
writeFileSync(join(outputDir, 'entry.png'), png);
// A second in-process encoding is also hashed to make the determinism check explicit.
const hashOne = createHash('sha256').update(png).digest('hex'), hashTwo = createHash('sha256').update(encode(quantized)).digest('hex');
const decoded = decodePng(png), luminances = new Uint8Array(PIXELS);
let total = 0, brightPixels = 0, darkPixels = 0, maxLuminance = -1, brightestPixel = [0, 0];
for (let i = 0; i < PIXELS; i++) { const p = i * 3, l = .2126 * decoded[p] + .7152 * decoded[p + 1] + .0722 * decoded[p + 2]; luminances[i] = l; total += l; if (l > 245) brightPixels++; if (l < 12) darkPixels++; if (l > maxLuminance) { maxLuminance = l; brightestPixel = [i % SIZE, (i / SIZE) | 0]; } }
let irisSum = 0, irisSq = 0, horizontalDifference = 0, pairs = 0;
for (let y = 0; y < SIZE; y++) for (let x = 0; x < SIZE; x++) { const i = y * SIZE + x; if (radiusAt[i] >= 130 && radiusAt[i] <= 355) { const l = luminances[i]; irisSum += l; irisSq += l * l; if (x + 1 < SIZE && radiusAt[i + 1] >= 130 && radiusAt[i + 1] <= 355) { horizontalDifference += Math.abs(l - luminances[i + 1]); pairs++; } } }
const irisCount = (() => { let n = 0; for (const r of radiusAt) if (r >= 130 && r <= 355) n++; return n; })();
const irisMean = irisSum / irisCount, irisStd = Math.sqrt(irisSq / irisCount - irisMean * irisMean);
const bounds = [[0,8],[8,26],[26,48],[48,74],[74,104]], annuli: number[] = bounds.map(([lo, hi]) => {
  let sum = 0, count = 0; for (let y = 468 - 104; y <= 468 + 104; y++) for (let x = 528 - 104; x <= 528 + 104; x++) { const d = Math.hypot(x + .5 - 528, y + .5 - 468); if (d >= lo && d < hi) { const p = (y * SIZE + x) * 3; sum += .2126 * decoded[p] + .7152 * decoded[p + 1] + .0722 * decoded[p + 2]; count++; } } return sum / count;
});
const annuliPass = annuli.every((v, i) => i === 0 || v <= annuli[i - 1] * .75);
const report: Record<string, unknown> = { elapsedMs: Date.now() - startedAt, outputBytes: png.length, sha256Run1: hashOne, sha256Run2: hashTwo, hashesMatch: hashOne === hashTwo, meanLuminance: total / PIXELS, above245Percent: brightPixels / PIXELS * 100, below12Percent: darkPixels / PIXELS * 100, brightestPixel, irisBand: { localContrast: horizontalDifference / pairs, standardDeviation: irisStd }, galaxyAnnuli: Object.fromEntries(bounds.map(([a,b], i) => [`${a}-${b}px`, annuli[i]])), galaxyAnnuliPass25PercentDrop: annuliPass, lashCoveragePixels: lashCoverage };
if (process.env.BAND_TEST === '1') {
  const bandReports: { rows: string; meanLuminance: number; sha256: string }[] = [];
  let unique = true, smoothBands = true, cleanRows = true;
  for (let start = 0; start < SIZE; start += 64) {
    const end = Math.min(SIZE, start + 64), bytes = decoded.subarray(start * SIZE * 3, end * SIZE * 3); let sum = 0;
    for (let p = 0; p < bytes.length; p += 3) sum += .2126 * bytes[p] + .7152 * bytes[p + 1] + .0722 * bytes[p + 2];
    const mean = sum / ((end - start) * SIZE), digest = createHash('sha256').update(bytes).digest('hex');
    if (bandReports.length) { const prev = bandReports[bandReports.length - 1]; if (prev.sha256 === digest) unique = false; if (Math.abs(prev.meanLuminance - mean) > 65) smoothBands = false; }
    bandReports.push({ rows: `${start}-${end - 1}`, meanLuminance: mean, sha256: digest });
  }
  const rowMeans = Array.from({ length: SIZE }, (_, y) => {
    let sum = 0; const offset = y * SIZE * 3;
    for (let x = 0; x < SIZE; x++) { const p = offset + x * 3; sum += .2126 * decoded[p] + .7152 * decoded[p + 1] + .0722 * decoded[p + 2]; }
    return sum / SIZE;
  });
  for (let y = 1; y < SIZE - 1; y++) if (Math.abs(rowMeans[y] - (rowMeans[y - 1] + rowMeans[y + 1]) / 2) > 55) cleanRows = false;
  report.bandTest = { bands: bandReports, noAdjacentIdenticalBands: unique, neighbourMeanJumpAtMost65: smoothBands, noSingleRowGarbage: cleanRows, verdict: unique && smoothBands && cleanRows ? 'PASS' : 'FAIL' };
}
console.log(JSON.stringify(report, null, 2));
