# Singularity Bloom

A deterministic 1024 × 1024 close-up eye with a warm spiral galaxy in the pupil. The image is computed from arithmetic in TypeScript, using only the Node.js standard library; it needs no external assets or packages.

Run with Node 22:

```sh
node main.ts
```

The renderer writes `entry.png` to `MAKEFUN_OUTPUT_DIR`, or `/output` when that variable is unset. Set `BAND_TEST=1` to report decoded image luminance, SHA-256 values for each 64-row band, and the seam-check verdict.
