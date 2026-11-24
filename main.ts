// Tiny stack VM: an exact interpreter for make.fun's tiny stack ISA (the kit's
// ISA.md). For every instance under the input dir it runs program.bin on input.bin
// and writes stdout.bin and exit.txt (the bytes written, the code it ended with).
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// Opcode facts by byte: [immediate bytes, values popped, values pushed]; a missing
// entry is an unknown opcode. Rows run HALT..ROT, ADD..LTU, JMP..RET, LOAD/STORE,
// PRINT/PUTC/IN/EXIT, in opcode order within each row.
const F = new Map([
  [0x00, [0, 0, 0]], [0x01, [1, 0, 1]], [0x02, [4, 0, 1]], [0x03, [0, 1, 0]],
  [0x04, [0, 1, 2]], [0x05, [0, 2, 2]], [0x06, [0, 2, 3]], [0x07, [0, 3, 3]],
  [0x10, [0, 2, 1]], [0x11, [0, 2, 1]], [0x12, [0, 2, 1]], [0x13, [0, 2, 1]],
  [0x14, [0, 2, 1]], [0x15, [0, 2, 1]], [0x16, [0, 2, 1]], [0x17, [0, 1, 1]],
  [0x18, [0, 2, 1]], [0x19, [0, 2, 1]], [0x1a, [0, 2, 1]], [0x1b, [0, 1, 1]],
  [0x1c, [0, 2, 1]], [0x1d, [0, 2, 1]], [0x1e, [0, 2, 1]],
  [0x20, [0, 2, 1]], [0x21, [0, 2, 1]], [0x22, [0, 2, 1]],
  [0x30, [2, 0, 0]], [0x31, [2, 1, 0]], [0x32, [2, 1, 0]], [0x33, [2, 0, 0]], [0x34, [0, 0, 0]],
  [0x40, [0, 1, 1]], [0x41, [0, 2, 0]],
  [0x50, [0, 1, 0]], [0x51, [0, 1, 0]], [0x52, [0, 0, 1]], [0x53, [0, 1, 0]],
]);

// Runs one program to its end; returns the bytes it wrote (kept whole even when it
// traps) and its end code: 0 for HALT, the low byte for EXIT, a trap's own code.
function run(p, inp) {
  const S = new Int32Array(256); // the data stack, at most 256 values
  let sp = 0;
  const C = new Int32Array(64); // return addresses, at most 64
  let d = 0;
  const M = new Int32Array(256); // memory words, all zero at the start
  const out = [];
  let pc = 0;
  let steps = 0;
  let ip = 0;
  const end = (code) => ({ out, code });

  // Each step checks, in the ISA's order: the step limit, the pc range, the opcode,
  // the immediate's fit, then the stack's depth both ways, then the instruction.
  for (;;) {
    if (steps === 1000000) return end(10);
    if (pc < 0 || pc >= p.length) return end(9);
    const op = p[pc];
    const f = F.get(op);
    if (f === undefined) return end(5);
    const [imm, pops, pushes] = f;
    if (pc + imm >= p.length) return end(9);
    steps += 1;
    if (sp < pops) return end(2);
    if (sp - pops + pushes > 256) return end(3);
    const next = pc + 1 + imm;
    pc = next;

    if (op >= 0x10 && op <= 0x22 && op !== 0x17 && op !== 0x1b) {
      // Two-operand instructions: b is the top, a below it; one result goes back.
      const b = S[sp - 1];
      const a = S[sp - 2];
      let r;
      if (op === 0x10) r = (a + b) | 0;
      else if (op === 0x11) r = (a - b) | 0;
      else if (op === 0x12) r = Math.imul(a, b); // the exact low 32 bits
      else if (op === 0x13) {
        if (b === 0) return end(4);
        r = a === -2147483648 && b === -1 ? a : Math.trunc(a / b) | 0;
      } else if (op === 0x14) {
        if (b === 0) return end(4);
        r = b === -1 ? 0 : a % b | 0; // the remainder takes the sign of a
      } else if (op === 0x15) {
        if (b === 0) return end(4);
        r = Math.floor((a >>> 0) / (b >>> 0)) | 0; // both sides unsigned
      } else if (op === 0x16) {
        if (b === 0) return end(4);
        r = (a >>> 0) % (b >>> 0) | 0;
      } else if (op === 0x18) r = a & b;
      else if (op === 0x19) r = a | b;
      else if (op === 0x1a) r = a ^ b;
      else if (op === 0x1c) r = a << (b & 31); // only the count's low 5 bits
      else if (op === 0x1d) r = a >> (b & 31); // arithmetic shift
      else if (op === 0x1e) r = (a >>> (b & 31)) | 0; // logical shift
      else if (op === 0x20) r = a === b ? 1 : 0;
      else if (op === 0x21) r = a < b ? 1 : 0;
      else r = (a >>> 0) < (b >>> 0) ? 1 : 0; // LTU
      S[sp - 2] = r;
      sp -= 1;
      continue;
    }

    switch (op) {
      case 0x00: // HALT
        return end(0);
      case 0x01: // PUSH8: the byte, sign-extended
        S[sp++] = (p[next - 1] << 24) >> 24;
        break;
      case 0x02: // PUSH32: four little-endian bytes
        S[sp++] = p[next - 4] | (p[next - 3] << 8) | (p[next - 2] << 16) | (p[next - 1] << 24);
        break;
      case 0x03: // POP
        sp -= 1;
        break;
      case 0x04: // DUP
        S[sp] = S[sp - 1];
        sp += 1;
        break;
      case 0x05: { // SWAP
        const t = S[sp - 1];
        S[sp - 1] = S[sp - 2];
        S[sp - 2] = t;
        break;
      }
      case 0x06: // OVER
        S[sp] = S[sp - 2];
        sp += 1;
        break;
      case 0x07: { // ROT: ( a b c -- b c a )
        const a = S[sp - 3];
        S[sp - 3] = S[sp - 2];
        S[sp - 2] = S[sp - 1];
        S[sp - 1] = a;
        break;
      }
      case 0x17: // NEG
        S[sp - 1] = -S[sp - 1] | 0;
        break;
      case 0x1b: // NOT
        S[sp - 1] = ~S[sp - 1];
        break;
      case 0x30: // JMP
      case 0x31: // JZ
      case 0x32: { // JNZ: the offset is signed, from the next instruction
        const rel = ((p[next - 2] | (p[next - 1] << 8)) << 16) >> 16;
        let go = true;
        if (op !== 0x30) {
          sp -= 1;
          go = op === 0x31 ? S[sp] === 0 : S[sp] !== 0;
        }
        if (go) pc = next + rel; // a target outside traps 9 next step
        break;
      }
      case 0x33: // CALL: the immediate is an unsigned absolute address
        if (d === 64) return end(7);
        C[d++] = next;
        pc = p[next - 2] | (p[next - 1] << 8);
        break;
      case 0x34: // RET
        if (d === 0) return end(8);
        pc = C[--d];
        break;
      case 0x40: { // LOAD
        const addr = S[sp - 1];
        if (addr < 0 || addr > 255) return end(6);
        S[sp - 1] = M[addr];
        break;
      }
      case 0x41: { // STORE: ( v addr -- )
        const addr = S[sp - 1];
        if (addr < 0 || addr > 255) return end(6);
        M[addr] = S[sp - 2];
        sp -= 2;
        break;
      }
      case 0x50: { // PRINT: the value in decimal ASCII
        const text = String(S[sp - 1]);
        if (out.length + text.length > 65536) return end(11); // writes none of it
        sp -= 1;
        for (let i = 0; i < text.length; i++) out.push(text.charCodeAt(i));
        break;
      }
      case 0x51: // PUTC: one byte, the value's low 8 bits
        if (out.length + 1 > 65536) return end(11);
        out.push(S[--sp] & 255);
        break;
      case 0x52: // IN: the next input byte, -1 once used up
        S[sp++] = ip < inp.length ? inp[ip++] : -1;
        break;
      case 0x53: // EXIT: the code is the value's low byte
        return end(S[--sp] & 255);
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const { out, code } = run(readFileSync(join(I, id, 'program.bin')), readFileSync(join(I, id, 'input.bin')));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), Buffer.from(out));
  writeFileSync(join(O, id, 'exit.txt'), `${code}\n`);
}
