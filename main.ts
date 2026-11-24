// A correct interpreter for make.fun's tiny stack ISA (version 1): 32-bit
// wrapping integers, a 256-value data stack, 64 return addresses, 256 words
// of memory, input and output, ten traps with their own exit codes, and a
// step and an output limit. Runs every /input/<id>/ program and writes its
// stdout and exit code to /output/<id>/. Written from the ISA spec and the
// reference VM's observable behaviour, in my own code.

import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// Opcode byte -> [immediate bytes, pops, pushes].
const OP = new Map([
  [0x00, [0, 0, 0]], [0x01, [1, 0, 1]], [0x02, [4, 0, 1]], [0x03, [0, 1, 0]], [0x04, [0, 1, 2]],
  [0x05, [0, 2, 2]], [0x06, [0, 2, 3]], [0x07, [0, 3, 3]],
  [0x10, [0, 2, 1]], [0x11, [0, 2, 1]], [0x12, [0, 2, 1]], [0x13, [0, 2, 1]], [0x14, [0, 2, 1]],
  [0x15, [0, 2, 1]], [0x16, [0, 2, 1]], [0x17, [0, 1, 1]], [0x18, [0, 2, 1]], [0x19, [0, 2, 1]],
  [0x1a, [0, 2, 1]], [0x1b, [0, 1, 1]], [0x1c, [0, 2, 1]], [0x1d, [0, 2, 1]], [0x1e, [0, 2, 1]],
  [0x20, [0, 2, 1]], [0x21, [0, 2, 1]], [0x22, [0, 2, 1]],
  [0x30, [2, 0, 0]], [0x31, [2, 1, 0]], [0x32, [2, 1, 0]], [0x33, [2, 0, 0]], [0x34, [0, 0, 0]],
  [0x40, [0, 1, 1]], [0x41, [0, 2, 0]], [0x50, [0, 1, 0]], [0x51, [0, 1, 0]], [0x52, [0, 0, 1]], [0x53, [0, 1, 0]],
]);

const OPT = new Array(256);
for (const [k, v] of OP) OPT[k] = v;

const enc = new TextEncoder();

/** Run one program on its input: the bytes it wrote and its exit code. */
function run(p, inp) {
  const D = new Int32Array(256);
  let sp = 0;
  const C = new Int32Array(64);
  let csp = 0;
  const M = new Int32Array(256);
  const out = new Uint8Array(65536);
  let olen = 0, ip = 0, pc = 0, steps = 0;
  const n = p.length;
  const fin = (code) => ({ o: out.subarray(0, olen), c: code });
  for (;;) {
    if (steps === 1000000) return fin(10);
    if (pc < 0 || pc >= n) return fin(9);
    const op = p[pc];
    const info = OPT[op];
    if (info === undefined) return fin(5);
    const imm = info[0], pops = info[1], pushes = info[2];
    if (pc + imm >= n) return fin(9);
    steps++;
    const next = pc + 1 + imm;
    if (sp < pops) return fin(2);
    if (sp - pops + pushes > 256) return fin(3);
    pc = next;
    switch (op) {
      case 0x00: return fin(0);
      case 0x01: D[sp++] = (p[next - 1] << 24) >> 24; break;
      case 0x02: D[sp++] = p[next - 4] | (p[next - 3] << 8) | (p[next - 2] << 16) | (p[next - 1] << 24); break;
      case 0x03: sp--; break;
      case 0x04: D[sp] = D[sp - 1]; sp++; break;
      case 0x05: { const t = D[sp - 1]; D[sp - 1] = D[sp - 2]; D[sp - 2] = t; break; }
      case 0x06: D[sp] = D[sp - 2]; sp++; break;
      case 0x07: { const a = D[sp - 3]; D[sp - 3] = D[sp - 2]; D[sp - 2] = D[sp - 1]; D[sp - 1] = a; break; }
      case 0x17: D[sp - 1] = -D[sp - 1] | 0; break;
      case 0x1b: D[sp - 1] = ~D[sp - 1]; break;
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
      case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e:
      case 0x20: case 0x21: case 0x22: {
        const b = D[sp - 1], a = D[sp - 2];
        let r;
        if (op === 0x10) r = (a + b) | 0;
        else if (op === 0x11) r = (a - b) | 0;
        else if (op === 0x12) r = Math.imul(a, b);
        else if (op === 0x13) { if (b === 0) return fin(4); r = a === -2147483648 && b === -1 ? a : (a / b) | 0; }
        else if (op === 0x14) { if (b === 0) return fin(4); r = b === -1 ? 0 : (a % b) | 0; }
        else if (op === 0x15) { if (b === 0) return fin(4); r = Math.floor((a >>> 0) / (b >>> 0)) | 0; }
        else if (op === 0x16) { if (b === 0) return fin(4); r = ((a >>> 0) % (b >>> 0)) | 0; }
        else if (op === 0x18) r = a & b;
        else if (op === 0x19) r = a | b;
        else if (op === 0x1a) r = a ^ b;
        else if (op === 0x1c) r = a << (b & 31);
        else if (op === 0x1d) r = a >> (b & 31);
        else if (op === 0x1e) r = (a >>> (b & 31)) | 0;
        else if (op === 0x20) r = a === b ? 1 : 0;
        else if (op === 0x21) r = a < b ? 1 : 0;
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0;
        sp -= 2;
        D[sp++] = r;
        break;
      }
      case 0x30: case 0x31: case 0x32: {
        const rel = ((p[next - 2] | (p[next - 1] << 8)) << 16) >> 16;
        let take = true;
        if (op !== 0x30) {
          const v = D[--sp];
          take = op === 0x31 ? v === 0 : v !== 0;
        }
        if (take) pc = next + rel;
        break;
      }
      case 0x33:
        if (csp === 64) return fin(7);
        C[csp++] = next;
        pc = p[next - 2] | (p[next - 1] << 8);
        break;
      case 0x34:
        if (csp === 0) return fin(8);
        pc = C[--csp];
        break;
      case 0x40: {
        const addr = D[sp - 1];
        if (addr < 0 || addr >= 256) return fin(6);
        D[sp - 1] = M[addr];
        break;
      }
      case 0x41: {
        const addr = D[sp - 1], v = D[sp - 2];
        if (addr < 0 || addr >= 256) return fin(6);
        sp -= 2;
        M[addr] = v;
        break;
      }
      case 0x50: {
        const bytes = enc.encode(String(D[sp - 1]));
        if (olen + bytes.length > 65536) return fin(11);
        sp--;
        out.set(bytes, olen);
        olen += bytes.length;
        break;
      }
      case 0x51:
        if (olen + 1 > 65536) return fin(11);
        out[olen++] = D[--sp] & 255;
        break;
      case 0x52: D[sp++] = ip < inp.length ? inp[ip++] : -1; break;
      case 0x53: return fin(D[--sp] & 255);
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const r = run(new Uint8Array(readFileSync(join(I, id, 'program.bin'))), new Uint8Array(readFileSync(join(I, id, 'input.bin'))));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), r.o);
  writeFileSync(join(O, id, 'exit.txt'), `${r.c}\n`);
}
