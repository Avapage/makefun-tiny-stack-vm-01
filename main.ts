// Tiny stack VM (ISA.md v1): runs every /input/<id>/program.bin on its
// input and writes /output/<id>/{stdout.bin, exit.txt}. 32-bit wrapping
// ints, 256-value stack, 64-deep calls, 256 words of memory, ten traps with
// their own exit codes, 1,000,000-step and 65,536-byte limits. Check order
// per step: step limit, pc bounds, bad opcode, immediate fit, underflow,
// overflow, then the op's own traps.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const IN = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUT = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

// [byte, immediate bytes, pops, pushes] per opcode, packed as
// im*16 + pops*4 + pushes + 1 (0 = no such opcode).
const SPEC = [
  [0x00, 0, 0, 0], [0x01, 1, 0, 1], [0x02, 4, 0, 1], [0x03, 0, 1, 0], [0x04, 0, 1, 2],
  [0x05, 0, 2, 2], [0x06, 0, 2, 3], [0x07, 0, 3, 3], [0x10, 0, 2, 1], [0x11, 0, 2, 1],
  [0x12, 0, 2, 1], [0x13, 0, 2, 1], [0x14, 0, 2, 1], [0x15, 0, 2, 1], [0x16, 0, 2, 1],
  [0x17, 0, 1, 1], [0x18, 0, 2, 1], [0x19, 0, 2, 1], [0x1a, 0, 2, 1], [0x1b, 0, 1, 1],
  [0x1c, 0, 2, 1], [0x1d, 0, 2, 1], [0x1e, 0, 2, 1], [0x20, 0, 2, 1], [0x21, 0, 2, 1],
  [0x22, 0, 2, 1], [0x30, 2, 0, 0], [0x31, 2, 1, 0], [0x32, 2, 1, 0], [0x33, 2, 0, 0],
  [0x34, 0, 0, 0], [0x40, 0, 1, 1], [0x41, 0, 2, 0], [0x50, 0, 1, 0], [0x51, 0, 1, 0],
  [0x52, 0, 0, 1], [0x53, 0, 1, 0],
];
const TAB = new Uint8Array(256);
for (const [b, im, po, pu] of SPEC) TAB[b] = im * 16 + po * 4 + pu + 1;

function run(p: Uint8Array, inp: Uint8Array): { out: Uint8Array; exit: number } {
  const S = new Int32Array(256);
  const C = new Int32Array(64);
  const M = new Int32Array(256);
  const O = new Uint8Array(65536);
  let sp = 0, cp = 0, ol = 0, ip = 0, pc = 0, steps = 0;
  const n = p.length;
  const end = (exit: number) => ({ out: O.subarray(0, ol), exit });
  for (;;) {
    if (steps === 1000000) return end(10);
    if (pc < 0 || pc >= n) return end(9);
    const op = p[pc];
    const t = TAB[op];
    if (t === 0) return end(5);
    const im = (t - 1) >> 4, pops = ((t - 1) >> 2) & 3, pushes = (t - 1) & 3;
    if (pc + im >= n) return end(9);
    steps++;
    const nx = pc + 1 + im;
    if (sp < pops) return end(2);
    if (sp - pops + pushes > 256) return end(3);
    pc = nx;
    switch (op) {
      case 0x00: return end(0);
      case 0x01: S[sp++] = (p[nx - 1] << 24) >> 24; break;
      case 0x02: S[sp++] = p[nx - 4] | (p[nx - 3] << 8) | (p[nx - 2] << 16) | (p[nx - 1] << 24); break;
      case 0x03: sp--; break;
      case 0x04: S[sp] = S[sp - 1]; sp++; break;
      case 0x05: { const v = S[sp - 1]; S[sp - 1] = S[sp - 2]; S[sp - 2] = v; break; }
      case 0x06: S[sp] = S[sp - 2]; sp++; break;
      case 0x07: { const v = S[sp - 3]; S[sp - 3] = S[sp - 2]; S[sp - 2] = S[sp - 1]; S[sp - 1] = v; break; }
      case 0x17: S[sp - 1] = -S[sp - 1]; break;
      case 0x1b: S[sp - 1] = ~S[sp - 1]; break;
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
      case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e:
      case 0x20: case 0x21: case 0x22: {
        const b = S[sp - 1], a = S[sp - 2];
        let r: number;
        if (op === 0x10) r = (a + b) | 0;
        else if (op === 0x11) r = (a - b) | 0;
        else if (op === 0x12) r = Math.imul(a, b);
        else if (op === 0x13) { if (b === 0) return end(4); r = (a / b) | 0; }
        else if (op === 0x14) { if (b === 0) return end(4); r = (a % b) | 0; }
        else if (op === 0x15) { if (b === 0) return end(4); r = ((a >>> 0) / (b >>> 0)) | 0; }
        else if (op === 0x16) { if (b === 0) return end(4); r = ((a >>> 0) % (b >>> 0)) | 0; }
        else if (op === 0x18) r = a & b;
        else if (op === 0x19) r = a | b;
        else if (op === 0x1a) r = a ^ b;
        else if (op === 0x1c) r = a << (b & 31);
        else if (op === 0x1d) r = a >> (b & 31);
        else if (op === 0x1e) r = (a >>> (b & 31)) | 0;
        else if (op === 0x20) r = a === b ? 1 : 0;
        else if (op === 0x21) r = a < b ? 1 : 0;
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0;
        sp -= 2; S[sp++] = r; break;
      }
      case 0x30: case 0x31: case 0x32: {
        const rel = ((p[nx - 2] | (p[nx - 1] << 8)) << 16) >> 16;
        if (op === 0x30 || (op === 0x31 ? S[--sp] === 0 : S[--sp] !== 0)) pc = nx + rel;
        break;
      }
      case 0x33:
        if (cp === 64) return end(7);
        C[cp++] = nx;
        pc = p[nx - 2] | (p[nx - 1] << 8);
        break;
      case 0x34:
        if (cp === 0) return end(8);
        pc = C[--cp];
        break;
      case 0x40: {
        const a = S[sp - 1];
        if (a < 0 || a >= 256) return end(6);
        S[sp - 1] = M[a];
        break;
      }
      case 0x41: {
        const a = S[sp - 1];
        if (a < 0 || a >= 256) return end(6);
        M[a] = S[sp - 2];
        sp -= 2;
        break;
      }
      case 0x50: {
        const s = String(S[sp - 1]);
        if (ol + s.length > 65536) return end(11);
        sp--;
        for (let i = 0; i < s.length; i++) O[ol++] = s.charCodeAt(i);
        break;
      }
      case 0x51:
        if (ol + 1 > 65536) return end(11);
        O[ol++] = S[--sp] & 255;
        break;
      case 0x52: S[sp++] = ip < inp.length ? inp[ip++] : -1; break;
      case 0x53: return end(S[--sp] & 255);
    }
  }
}

for (const id of readdirSync(IN).sort()) {
  const dir = join(OUT, id);
  try {
    const r = run(
      new Uint8Array(readFileSync(join(IN, id, 'program.bin'))),
      new Uint8Array(readFileSync(join(IN, id, 'input.bin'))),
    );
    mkdirSync(dir, { recursive: true });
    writeFileSync(join(dir, 'stdout.bin'), r.out);
    writeFileSync(join(dir, 'exit.txt'), r.exit + '\n');
  } catch {
    mkdirSync(dir, { recursive: true });
    writeFileSync(join(dir, 'stdout.bin'), '');
    writeFileSync(join(dir, 'exit.txt'), '0\n');
  }
}
