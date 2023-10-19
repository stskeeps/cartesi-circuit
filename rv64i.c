// Copyright Cartesi and individual authors (see AUTHORS)
// SPDX-License-Identifier: LGPL-3.0-or-later
//
// This program is free software: you can redistribute it and/or modify it under
// the terms of the GNU Lesser General Public License as published by the Free
// Software Foundation, either version 3 of the License, or (at your option) any
// later version.
//
// This program is distributed in the hope that it will be useful, but WITHOUT ANY
// WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
// PARTICULAR PURPOSE. See the GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License along
// with this program (see COPYING). If not, see <https://www.gnu.org/licenses/>.
//

// NOLINTBEGIN(google-readability-casting, misc-const-correctness)
#include <stdint.h>
#include <stddef.h>
#include <assert.h>

typedef int8_t int8;
typedef uint8_t uint8;
typedef int16_t int16;
typedef uint16_t uint16;
typedef int32_t int32;
typedef uint32_t uint32;
typedef int64_t int64;
typedef uint64_t uint64;
typedef uint8_t bool;

#define UCYCLE 0x320
#define UHALT 0x328
#define UPC 0x330
#define UX0 0x340


struct UarchState {
    uint64 access_paddr[16];
    uint64 access_val[16];
    uint8 access_readWriteEnd[16];
    uint8 access_pointer;
    uint8 trap;
};

typedef struct UarchState UarchState;

enum UArchStepStatus {
    Success,       // one micro instruction was executed successfully
    CycleOverflow, // already at fixed point: uarch cycle has reached its maximum value
    UArchHalted    // already at fixed point: microarchitecture is halted
};


static inline uint64 readWord(UarchState *a, uint64 paddr) {
    if (a->access_pointer > 16) {
       a->trap = 18;
       return 0;
    }
    if (a->access_readWriteEnd[a->access_pointer] == 0 && a->access_paddr[a->access_pointer] == paddr) {
       return (a->access_val[a->access_pointer++]);
    } else {
       a->access_pointer++;
       a->trap = 19;
       
       return 0;
    }
}

static inline void writeWord(UarchState *a, uint64 paddr, uint64 val) {
    if (a->access_pointer > 16) {
       a->trap = 20;
       return;
    }
    if (a->access_readWriteEnd[a->access_pointer] == 1 && a->access_paddr[a->access_pointer] == paddr && a->access_val[a->access_pointer] == val) {
      a->access_pointer++;
    } else {
      a->access_pointer++;
      a->trap = 21;
    }
}

static inline uint64 readCycle(UarchState *a) {
    return readWord(a, UCYCLE);
}

static inline void writeCycle(UarchState *a, uint64 val) {
    writeWord(a, UCYCLE, val);
}

static inline bool readHaltFlag(UarchState *a) {
    return readWord(a, UHALT) != 0;
}

static inline void setHaltFlag(UarchState *a) {
    writeWord(a, UHALT, 1);
}

static inline uint64 readPc(UarchState *a) {
    return readWord(a, UPC);
}

static inline void writePc(UarchState *a, uint64 val) {
    writeWord(a, UPC, val);
}

static inline uint64 readX(UarchState *a, uint8 reg) {
    __CPROVER_assume(reg < 32);
    return readWord(a, UX0 + (reg << 3));
}

static inline void writeX(UarchState *a, uint8 reg, uint64 val) {
    __CPROVER_assume(reg < 32);
    writeWord(a, UX0 + (reg << 3), val);
}


void require(UarchState *a, bool condition, const char *message) {
    if (!condition) {
      a->trap = 1;
    }
    //assert((condition) && (message));
}

static void dumpInsn(UarchState *a, uint64 pc, uint32 insn, const char *name) {
}

static inline int32 uint64ToInt32(uint64 v) {
    return (int32)(v);
}

static inline uint64 uint64AddInt32(uint64 v, int32 w) {
    return v + w;
}

static inline uint64 uint64SubUInt64(uint64 v, uint64 w) {
    return v - w;
}

static inline uint64 uint64AddUInt64(uint64 v, uint64 w) {
    return v + w;
}

static inline uint64 uint64ShiftRight(uint64 v, uint32 count) {
    return v >> (count & 0x3f);
}

static inline uint64 uint64ShiftLeft(uint64 v, uint32 count) {
    return v << (count & 0x3f);
}

static inline int64 int64ShiftRight(int64 v, uint32 count) {
    return v >> (count & 0x3f);
}

static inline int64 int64AddInt64(int64 v, int64 w) {
    int64 res = 0;
    return v+w;
}

static inline uint32 uint32ShiftRight(uint32 v, uint32 count) {
    return v >> (count & 0x1f);
}

static inline uint32 uint32ShiftLeft(uint32 v, uint32 count) {
    return v << (count & 0x1f);
}

static inline uint64 int32ToUInt64(int32 v) {
    return v;
}

static inline int32 int32ShiftRight(int32 v, uint32 count) {
    return v >> (count & 0x1f);
}

static inline int32 int32AddInt32(int32 v, int32 w) {
    int32 res = 0;
//    __builtin_add_overflow(v, w, &res);
    return v+w;
}

static inline int32 int32SubInt32(int32 v, int32 w) {
    return v-w;
}

static inline uint64 int16ToUInt64(int16 v) {
    return v;
}

static inline uint64 int8ToUInt64(int8 v) {
    return v;
}

// Memory read/write access

static inline uint64 readUInt64(UarchState *a, uint64 paddr) {
    require(a, (paddr & 7) == 0, "misaligned readUInt64 address");
    return readWord(a, paddr);
}


static inline uint32 readUInt32(UarchState *a, uint64 paddr) {
    require(a, (paddr & 3) == 0, "misaligned readUInt32 address");
    uint64 palign = paddr & ~(uint64)(7);
    uint32 bitoffset = uint32ShiftLeft((uint32)(paddr) & (uint32)(7), 3);
    uint64 val64 = readUInt64(a, palign);
    return (uint32)(uint64ShiftRight(val64, bitoffset));
}


static inline uint16 readUInt16(UarchState *a, uint64 paddr) {
    require(a, (paddr & 1) == 0, "misaligned readUInt16 address");
    uint64 palign = paddr & ~(uint64)(7);
    uint32 bitoffset = uint32ShiftLeft((uint32)(paddr) & (uint32)(7), 3);
    uint64 val64 = readUInt64(a, palign);
    return (uint16)(uint64ShiftRight(val64, bitoffset));
}


static inline uint8 readUInt8(UarchState *a, uint64 paddr) {
    uint64 palign = paddr & ~(uint64)(7);
    uint32 bitoffset = uint32ShiftLeft((uint32)(paddr) & (uint32)(7), 3);
    uint64 val64 = readUInt64(a, palign);
    return (uint8)(uint64ShiftRight(val64, bitoffset));
}


static inline void writeUInt64(UarchState *a, uint64 paddr, uint64 val) {
    require(a, (paddr & 7) == 0, "misaligned writeUInt64 address");
    writeWord(a, paddr, val);
}

/// \brief Copies bits from a uint64 word, starting at bit 0, to another uint64 word at the specified bit offset.
/// \param from Source of bits to copy, starting at offset 0.
/// \param count Number of bits to copy.
/// \param to Destination of copy.
/// \param offset Bit offset in destination to copy bits to.
/// \return The uint64 word containing the copy result.
static inline uint64 copyBits(UarchState *a, uint32 from, uint32 count, uint64 to, uint32 offset) {
    require(a, offset + count <= 64, "copyBits count exceeds limit of 64");
    uint64 eraseMask = uint64ShiftLeft(1, count) - 1;
    eraseMask = ~uint64ShiftLeft(eraseMask, offset);
    return uint64ShiftLeft(from, offset) | (to & eraseMask);
}


static inline void writeUInt32(UarchState *a, uint64 paddr, uint32 val) {
    require(a, (paddr & 3) == 0, "misaligned writeUInt32 address");
    uint64 palign = paddr & ~(uint64)(7);

    uint32 bitoffset = uint32ShiftLeft((uint32)(paddr) & (uint32)(7), 3);
    uint64 oldval64 = readUInt64(a, palign);
    uint64 newval64 = copyBits(a, val, 32, oldval64, bitoffset);
    writeUInt64(a, palign, newval64);
}


static inline void writeUInt16(UarchState *a, uint64 paddr, uint16 val) {
    require(a, (paddr & 1) == 0, "misaligned writeUInt16 address");
    uint64 palign = paddr & ~(uint64)(7);
    uint32 bitoffset = uint32ShiftLeft((uint32)(paddr) & (uint32)(7), 3);
    uint64 oldval64 = readUInt64(a, palign);
    uint64 newval64 = copyBits(a, val, 16, oldval64, bitoffset);
    writeUInt64(a, palign, newval64);
}


static inline void writeUInt8(UarchState *a, uint64 paddr, uint8 val) {
    uint64 palign = paddr & ~(uint64)(7);
    uint32 bitoffset = uint32ShiftLeft((uint32)(paddr) & (uint32)(7), 3);
    uint64 oldval64 = readUInt64(a, palign);
    uint64 newval64 = copyBits(a, val, 8, oldval64, bitoffset);
    writeUInt64(a, palign, newval64);
}

// Instruction operand decoders

static inline uint8 operandRd(uint32 insn) {
    return (uint8)(uint32ShiftRight(uint32ShiftLeft(insn, 20), 27));
}

static inline uint8 operandRs1(uint32 insn) {
    return (uint8)(uint32ShiftRight(uint32ShiftLeft(insn, 12), 27));
}

static inline uint8 operandRs2(uint32 insn) {
    return (uint8)(uint32ShiftRight(uint32ShiftLeft(insn, 7), 27));
}

static inline int32 operandImm12(uint32 insn) {
    return int32ShiftRight((int32)(insn), 20);
}

static inline int32 operandImm20(uint32 insn) {
    return (int32)(uint32ShiftLeft(uint32ShiftRight(insn, 12), 12));
}

static inline int32 operandJimm20(uint32 insn) {
    int32 a = (int32)(uint32ShiftLeft((uint32)(int32ShiftRight((int32)(insn), 31)), 20));
    uint32 b = uint32ShiftLeft(uint32ShiftRight(uint32ShiftLeft(insn, 1), 22), 1);
    uint32 c = uint32ShiftLeft(uint32ShiftRight(uint32ShiftLeft(insn, 11), 31), 11);
    uint32 d = uint32ShiftLeft(uint32ShiftRight(uint32ShiftLeft(insn, 12), 24), 12);
    return (int32)((uint32)(a) | b | c | d);
}

static inline int32 operandShamt5(uint32 insn) {
    return (int32)(uint32ShiftRight(uint32ShiftLeft(insn, 7), 27));
}

static inline int32 operandShamt6(uint32 insn) {
    return (int32)(uint32ShiftRight(uint32ShiftLeft(insn, 6), 26));
}

static inline int32 operandSbimm12(uint32 insn) {
    int32 a = (int32)(uint32ShiftLeft((uint32)(int32ShiftRight((int32)(insn), 31)), 12));
    uint32 b = uint32ShiftLeft(uint32ShiftRight(uint32ShiftLeft(insn, 1), 26), 5);
    uint32 c = uint32ShiftLeft(uint32ShiftRight(uint32ShiftLeft(insn, 20), 28), 1);
    uint32 d = uint32ShiftLeft(uint32ShiftRight(uint32ShiftLeft(insn, 24), 31), 11);
    return (int32)((uint32)(a) | b | c | d);
}

static inline int32 operandSimm12(uint32 insn) {
    return (int32)(
        uint32ShiftLeft((uint32)(int32ShiftRight((int32)(insn), 25)), 5) | uint32ShiftRight(uint32ShiftLeft(insn, 20), 27));
}

// Execute instruction


static inline void advancePc(UarchState *a, uint64 pc) {
    uint64 newPc = uint64AddUInt64(pc, 4);
    return writePc(a, newPc);
}


static inline void branch(UarchState *a, uint64 pc) {
    return writePc(a, pc);
}


static inline void executeLUI(UarchState *a, uint32 insn, uint64 pc) {
    dumpInsn(a, pc, insn, "lui");
    uint8 rd = operandRd(insn);
    int32 imm = operandImm20(insn);
    if (rd != 0) {
        writeX(a, rd, int32ToUInt64(imm));
    }
    return advancePc(a, pc);
}


static inline void executeAUIPC(UarchState *a, uint32 insn, uint64 pc) {
    dumpInsn(a, pc, insn, "auipc");
    int32 imm = operandImm20(insn);
    uint8 rd = operandRd(insn);
    if (rd != 0) {
        writeX(a, rd, uint64AddInt32(pc, imm));
    }
    return advancePc(a, pc);
}


static inline void executeJAL(UarchState *a, uint32 insn, uint64 pc) {
    dumpInsn(a, pc, insn, "jal");
    int32 imm = operandJimm20(insn);
    uint8 rd = operandRd(insn);
    if (rd != 0) {
        writeX(a, rd, uint64AddUInt64(pc, 4));
    }
    return branch(a, uint64AddInt32(pc, imm));
}


static inline void executeJALR(UarchState *a, uint32 insn, uint64 pc) {
    dumpInsn(a, pc, insn, "jalr");
    int32 imm = operandImm12(insn);
    uint8 rd = operandRd(insn);
    uint8 rs1 = operandRs1(insn);
    uint64 rs1val = readX(a, rs1);
    if (rd != 0) {
        writeX(a, rd, uint64AddUInt64(pc, 4));
    }
    return branch(a, uint64AddInt32(rs1val, imm) & (~(uint64)(1)));
}


static inline void executeBEQ(UarchState *a, uint32 insn, uint64 pc) {
    dumpInsn(a, pc, insn, "beq");
    int32 imm = operandSbimm12(insn);
    uint8 rs1 = operandRs1(insn);
    uint8 rs2 = operandRs2(insn);
    uint64 rs1val = readX(a, rs1);
    uint64 rs2val = readX(a, rs2);
    if (rs1val == rs2val) {
        return branch(a, uint64AddInt32(pc, imm));
    }
    return advancePc(a, pc);
}


static inline void executeBNE(UarchState *a, uint32 insn, uint64 pc) {
    dumpInsn(a, pc, insn, "bne");
    int32 imm = operandSbimm12(insn);
    uint8 rs1 = operandRs1(insn);
    uint8 rs2 = operandRs2(insn);
    uint64 rs1val = readX(a, rs1);
    uint64 rs2val = readX(a, rs2);
    if (rs1val != rs2val) {
        return branch(a, uint64AddInt32(pc, imm));
    }
    return advancePc(a, pc);
}


static inline void executeBLT(UarchState *a, uint32 insn, uint64 pc) {
    dumpInsn(a, pc, insn, "blt");
    int32 imm = operandSbimm12(insn);
    uint8 rs1 = operandRs1(insn);
    uint8 rs2 = operandRs2(insn);
    int64 rs1val = (int64)(readX(a, rs1));
    int64 rs2val = (int64)(readX(a, rs2));
    if (rs1val < rs2val) {
        return branch(a, uint64AddInt32(pc, imm));
    }
    return advancePc(a, pc);
}


static inline void executeBGE(UarchState *a, uint32 insn, uint64 pc) {
    dumpInsn(a, pc, insn, "bge");
    int32 imm = operandSbimm12(insn);
    uint8 rs1 = operandRs1(insn);
    uint8 rs2 = operandRs2(insn);
    int64 rs1val = (int64)(readX(a, rs1));
    int64 rs2val = (int64)(readX(a, rs2));
    if (rs1val >= rs2val) {
        return branch(a, uint64AddInt32(pc, imm));
    }
    return advancePc(a, pc);
}


static inline void executeBLTU(UarchState *a, uint32 insn, uint64 pc) {
    dumpInsn(a, pc, insn, "bltu");
    int32 imm = operandSbimm12(insn);
    uint8 rs1 = operandRs1(insn);
    uint8 rs2 = operandRs2(insn);
    uint64 rs1val = readX(a, rs1);
    uint64 rs2val = readX(a, rs2);
    if (rs1val < rs2val) {
        return branch(a, uint64AddInt32(pc, imm));
    }
    return advancePc(a, pc);
}


static inline void executeBGEU(UarchState *a, uint32 insn, uint64 pc) {
    dumpInsn(a, pc, insn, "bgeu");
    int32 imm = operandSbimm12(insn);
    uint8 rs1 = operandRs1(insn);
    uint8 rs2 = operandRs2(insn);
    uint64 rs1val = readX(a, rs1);
    uint64 rs2val = readX(a, rs2);
    if (rs1val >= rs2val) {
        return branch(a, uint64AddInt32(pc, imm));
    }
    return advancePc(a, pc);
}


static inline void executeLB(UarchState *a, uint32 insn, uint64 pc) {
    dumpInsn(a, pc, insn, "lb");
    int32 imm = operandImm12(insn);
    uint8 rd = operandRd(insn);
    uint8 rs1 = operandRs1(insn);
    uint64 rs1val = readX(a, rs1);
    int8 i8 = (int8)(readUInt8(a, uint64AddInt32(rs1val, imm)));
    if (rd != 0) {
        writeX(a, rd, int8ToUInt64(i8));
    }
    return advancePc(a, pc);
}


static inline void executeLHU(UarchState *a, uint32 insn, uint64 pc) {
    dumpInsn(a, pc, insn, "lhu");
    int32 imm = operandImm12(insn);
    uint8 rd = operandRd(insn);
    uint8 rs1 = operandRs1(insn);
    uint64 rs1val = readX(a, rs1);
    uint16 u16 = readUInt16(a, uint64AddInt32(rs1val, imm));
    if (rd != 0) {
        writeX(a, rd, u16);
    }
    return advancePc(a, pc);
}


static inline void executeLH(UarchState *a, uint32 insn, uint64 pc) {
    dumpInsn(a, pc, insn, "lh");
    int32 imm = operandImm12(insn);
    uint8 rd = operandRd(insn);
    uint8 rs1 = operandRs1(insn);
    uint64 rs1val = readX(a, rs1);
    int16 i16 = (int16)(readUInt16(a, uint64AddInt32(rs1val, imm)));
    if (rd != 0) {
        writeX(a, rd, int16ToUInt64((int64)(i16)));
    }
    return advancePc(a, pc);
}


static inline void executeLW(UarchState *a, uint32 insn, uint64 pc) {
    dumpInsn(a, pc, insn, "lw");
    int32 imm = operandImm12(insn);
    uint8 rd = operandRd(insn);
    uint8 rs1 = operandRs1(insn);
    uint64 rs1val = readX(a, rs1);
    int32 i32 = (int32)(readUInt32(a, uint64AddInt32(rs1val, imm)));
    if (rd != 0) {
        writeX(a, rd, int32ToUInt64(i32));
    }
    return advancePc(a, pc);
}


static inline void executeLBU(UarchState *a, uint32 insn, uint64 pc) {
    dumpInsn(a, pc, insn, "lbu");
    int32 imm = operandImm12(insn);
    uint8 rd = operandRd(insn);
    uint8 rs1 = operandRs1(insn);
    uint64 rs1val = readX(a, rs1);
    uint8 u8 = readUInt8(a, uint64AddInt32(rs1val, imm));
    if (rd != 0) {
        writeX(a, rd, u8);
    }
    return advancePc(a, pc);
}


static inline void executeSB(UarchState *a, uint32 insn, uint64 pc) {
    dumpInsn(a, pc, insn, "sb");
    int32 imm = operandSimm12(insn);
    uint8 rs1 = operandRs1(insn);
    uint8 rs2 = operandRs2(insn);
    uint64 rs1val = readX(a, rs1);
    uint64 rs2val = readX(a, rs2);
    writeUInt8(a, uint64AddInt32(rs1val, imm), (uint8)(rs2val));
    return advancePc(a, pc);
}


static inline void executeSH(UarchState *a, uint32 insn, uint64 pc) {
    dumpInsn(a, pc, insn, "sh");
    int32 imm = operandSimm12(insn);
    uint8 rs1 = operandRs1(insn);
    uint8 rs2 = operandRs2(insn);
    uint64 rs1val = readX(a, rs1);
    uint64 rs2val = readX(a, rs2);
    writeUInt16(a, uint64AddInt32(rs1val, imm), (uint16)(rs2val));
    return advancePc(a, pc);
}


static inline void executeSW(UarchState *a, uint32 insn, uint64 pc) {
    dumpInsn(a, pc, insn, "sw");
    int32 imm = operandSimm12(insn);
    uint8 rs1 = operandRs1(insn);
    uint8 rs2 = operandRs2(insn);
    uint64 rs1val = readX(a, rs1);
    uint32 rs2val = (uint32)(readX(a, rs2));
    writeUInt32(a, uint64AddInt32(rs1val, imm), rs2val);
    return advancePc(a, pc);
}


static inline void executeADDI(UarchState *a, uint32 insn, uint64 pc) {
    dumpInsn(a, pc, insn, "addi");
    int32 imm = operandImm12(insn);
    uint8 rd = operandRd(insn);
    uint8 rs1 = operandRs1(insn);
    if (rd != 0) {
        uint64 rs1val = readX(a, rs1);
        int64 val = int64AddInt64((int64)(rs1val), (int64)(imm));
        writeX(a, rd, (uint64)(val));
    }
    return advancePc(a, pc);
}


static inline void executeADDIW(UarchState *a, uint32 insn, uint64 pc) {
    dumpInsn(a, pc, insn, "addiw");
    int32 imm = operandImm12(insn);
    uint8 rd = operandRd(insn);
    uint8 rs1 = operandRs1(insn);
    int32 rs1val = uint64ToInt32(readX(a, rs1));
    if (rd != 0) {
        int32 val = int32AddInt32(rs1val, imm);
        writeX(a, rd, int32ToUInt64(val));
    }
    return advancePc(a, pc);
}


static inline void executeSLTI(UarchState *a, uint32 insn, uint64 pc) {
    dumpInsn(a, pc, insn, "slti");
    int32 imm = operandImm12(insn);
    uint8 rd = operandRd(insn);
    uint8 rs1 = operandRs1(insn);
    if (rd != 0) {
        uint64 rs1val = readX(a, rs1);
        if ((int64)(rs1val) < imm) {
            writeX(a, rd, 1);
        } else {
            writeX(a, rd, 0);
        }
    }
    return advancePc(a, pc);
}


static inline void executeSLTIU(UarchState *a, uint32 insn, uint64 pc) {
    dumpInsn(a, pc, insn, "sltiu");
    int32 imm = operandImm12(insn);
    uint8 rd = operandRd(insn);
    uint8 rs1 = operandRs1(insn);
    if (rd != 0) {
        uint64 rs1val = readX(a, rs1);
        if (rs1val < int32ToUInt64(imm)) {
            writeX(a, rd, 1);
        } else {
            writeX(a, rd, 0);
        }
    }
    return advancePc(a, pc);
}


static inline void executeXORI(UarchState *a, uint32 insn, uint64 pc) {
    dumpInsn(a, pc, insn, "xori");
    int32 imm = operandImm12(insn);
    uint8 rd = operandRd(insn);
    uint8 rs1 = operandRs1(insn);
    if (rd != 0) {
        uint64 rs1val = readX(a, rs1);
        writeX(a, rd, rs1val ^ int32ToUInt64(imm));
    }
    return advancePc(a, pc);
}


static inline void executeORI(UarchState *a, uint32 insn, uint64 pc) {
    dumpInsn(a, pc, insn, "ori");
    int32 imm = operandImm12(insn);
    uint8 rd = operandRd(insn);
    uint8 rs1 = operandRs1(insn);
    if (rd != 0) {
        uint64 rs1val = readX(a, rs1);
        writeX(a, rd, rs1val | int32ToUInt64(imm));
    }
    return advancePc(a, pc);
}


static inline void executeANDI(UarchState *a, uint32 insn, uint64 pc) {
    dumpInsn(a, pc, insn, "andi");
    int32 imm = operandImm12(insn);
    uint8 rd = operandRd(insn);
    uint8 rs1 = operandRs1(insn);
    if (rd != 0) {
        uint64 rs1val = readX(a, rs1);
        writeX(a, rd, rs1val & int32ToUInt64(imm));
    }
    return advancePc(a, pc);
}


static inline void executeSLLI(UarchState *a, uint32 insn, uint64 pc) {
    dumpInsn(a, pc, insn, "slli");
    int32 imm = operandShamt6(insn);
    uint8 rd = operandRd(insn);
    uint8 rs1 = operandRs1(insn);
    if (rd != 0) {
        uint64 rs1val = readX(a, rs1);
        writeX(a, rd, uint64ShiftLeft(rs1val, (uint32)(imm)));
    }
    return advancePc(a, pc);
}


static inline void executeSLLIW(UarchState *a, uint32 insn, uint64 pc) {
    dumpInsn(a, pc, insn, "slliw");
    int32 imm = operandShamt5(insn);
    uint8 rd = operandRd(insn);
    uint8 rs1 = operandRs1(insn);
    uint32 rs1val = (uint32)(readX(a, rs1));
    if (rd != 0) {
        writeX(a, rd, int32ToUInt64((int32)(uint32ShiftLeft(rs1val, (uint32)(imm)))));
    }
    return advancePc(a, pc);
}


static inline void executeSRLI(UarchState *a, uint32 insn, uint64 pc) {
    dumpInsn(a, pc, insn, "srli");
    int32 imm = operandShamt6(insn);
    uint8 rd = operandRd(insn);
    uint8 rs1 = operandRs1(insn);
    if (rd != 0) {
        uint64 rs1val = readX(a, rs1);
        writeX(a, rd, uint64ShiftRight(rs1val, (uint32)(imm)));
    }
    return advancePc(a, pc);
}


static inline void executeSRLW(UarchState *a, uint32 insn, uint64 pc) {
    dumpInsn(a, pc, insn, "srlw");
    uint8 rd = operandRd(insn);
    uint8 rs1 = operandRs1(insn);
    uint8 rs2 = operandRs2(insn);
    uint32 rs1val = (uint32)(readX(a, rs1));
    uint32 rs2val = (uint32)(readX(a, rs2));
    int32 rdval = (int32)(uint32ShiftRight(rs1val, rs2val));
    if (rd != 0) {
        writeX(a, rd, int32ToUInt64(rdval));
    }
    return advancePc(a, pc);
}


static inline void executeSRLIW(UarchState *a, uint32 insn, uint64 pc) {
    dumpInsn(a, pc, insn, "srliw");
    int32 imm = operandShamt5(insn);
    uint8 rd = operandRd(insn);
    uint8 rs1 = operandRs1(insn);
    uint32 rs1val = (uint32)(readX(a, rs1));
    int32 rdval = (int32)(uint32ShiftRight(rs1val, (uint32)(imm)));
    if (rd != 0) {
        writeX(a, rd, int32ToUInt64(rdval));
    }
    return advancePc(a, pc);
}


static inline void executeSRAI(UarchState *a, uint32 insn, uint64 pc) {
    dumpInsn(a, pc, insn, "srai");
    int32 imm = operandShamt6(insn);
    uint8 rd = operandRd(insn);
    uint8 rs1 = operandRs1(insn);
    if (rd != 0) {
        uint64 rs1val = readX(a, rs1);
        writeX(a, rd, (uint64)(int64ShiftRight((int64)(rs1val), (uint32)(imm))));
    }
    return advancePc(a, pc);
}


static inline void executeSRAIW(UarchState *a, uint32 insn, uint64 pc) {
    dumpInsn(a, pc, insn, "sraiw");
    int32 imm = operandShamt5(insn);
    uint8 rd = operandRd(insn);
    uint8 rs1 = operandRs1(insn);
    int32 rs1val = uint64ToInt32(readX(a, rs1));
    if (rd != 0) {
        writeX(a, rd, int32ToUInt64(int32ShiftRight(rs1val, (uint32)(imm))));
    }
    return advancePc(a, pc);
}


static inline void executeADD(UarchState *a, uint32 insn, uint64 pc) {
    dumpInsn(a, pc, insn, "add");
    uint8 rd = operandRd(insn);
    uint8 rs1 = operandRs1(insn);
    uint8 rs2 = operandRs2(insn);
    if (rd != 0) {
        uint64 rs1val = readX(a, rs1);
        uint64 rs2val = readX(a, rs2);
        writeX(a, rd, uint64AddUInt64(rs1val, rs2val));
    }
    return advancePc(a, pc);
}


static inline void executeADDW(UarchState *a, uint32 insn, uint64 pc) {
    dumpInsn(a, pc, insn, "addw");
    uint8 rd = operandRd(insn);
    uint8 rs1 = operandRs1(insn);
    uint8 rs2 = operandRs2(insn);
    int32 rs1val = uint64ToInt32(readX(a, rs1));
    int32 rs2val = uint64ToInt32(readX(a, rs2));
    if (rd != 0) {
        int32 val = int32AddInt32(rs1val, rs2val);
        writeX(a, rd, int32ToUInt64(val));
    }
    return advancePc(a, pc);
}


static inline void executeSUB(UarchState *a, uint32 insn, uint64 pc) {
    dumpInsn(a, pc, insn, "sub");
    uint8 rd = operandRd(insn);
    uint8 rs1 = operandRs1(insn);
    uint8 rs2 = operandRs2(insn);
    if (rd != 0) {
        uint64 rs1val = readX(a, rs1);
        uint64 rs2val = readX(a, rs2);
        writeX(a, rd, uint64SubUInt64((int64)(rs1val), (int64) rs2val));
    }
    return advancePc(a, pc);
}


static inline void executeSUBW(UarchState *a, uint32 insn, uint64 pc) {
    dumpInsn(a, pc, insn, "subw");
    uint8 rd = operandRd(insn);
    uint8 rs1 = operandRs1(insn);
    uint8 rs2 = operandRs2(insn);
    int32 rs1val = uint64ToInt32(readX(a, rs1));
    int32 rs2val = uint64ToInt32(readX(a, rs2));
    if (rd != 0) {
        int32 val = int32SubInt32(rs1val, rs2val);
        writeX(a, rd, int32ToUInt64(val));
    }
    return advancePc(a, pc);
}


static inline void executeSLL(UarchState *a, uint32 insn, uint64 pc) {
    dumpInsn(a, pc, insn, "sll");
    uint8 rd = operandRd(insn);
    uint8 rs1 = operandRs1(insn);
    uint8 rs2 = operandRs2(insn);
    if (rd != 0) {
        uint64 rs1val = readX(a, rs1);
        uint32 rs2val = (uint32)(readX(a, rs2));
        writeX(a, rd, uint64ShiftLeft(rs1val, rs2val));
    }
    return advancePc(a, pc);
}


static inline void executeSLLW(UarchState *a, uint32 insn, uint64 pc) {
    dumpInsn(a, pc, insn, "sllw");
    uint8 rd = operandRd(insn);
    uint8 rs1 = operandRs1(insn);
    uint8 rs2 = operandRs2(insn);
    uint32 rs1val = (uint32)(readX(a, rs1));
    uint32 rs2val = (uint32)(readX(a, rs2));
    int32 rdval = (int32)(uint32ShiftLeft((uint32)(rs1val), rs2val));
    if (rd != 0) {
        writeX(a, rd, int32ToUInt64(rdval));
    }
    return advancePc(a, pc);
}


static inline void executeSLT(UarchState *a, uint32 insn, uint64 pc) {
    dumpInsn(a, pc, insn, "slt");
    uint8 rd = operandRd(insn);
    uint8 rs1 = operandRs1(insn);
    uint8 rs2 = operandRs2(insn);
    if (rd != 0) {
        int64 rs1val = (int64)(readX(a, rs1));
        int64 rs2val = (int64)(readX(a, rs2));
        uint64 rdval = 0;
        if (rs1val < rs2val) {
            rdval = 1;
        }
        writeX(a, rd, rdval);
    }
    return advancePc(a, pc);
}


static inline void executeSLTU(UarchState *a, uint32 insn, uint64 pc) {
    dumpInsn(a, pc, insn, "sltu");
    uint8 rd = operandRd(insn);
    uint8 rs1 = operandRs1(insn);
    uint8 rs2 = operandRs2(insn);
    if (rd != 0) {
        uint64 rs1val = readX(a, rs1);
        uint64 rs2val = readX(a, rs2);
        uint64 rdval = 0;
        if (rs1val < rs2val) {
            rdval = 1;
        }
        writeX(a, rd, rdval);
    }
    return advancePc(a, pc);
}


static inline void executeXOR(UarchState *a, uint32 insn, uint64 pc) {
    dumpInsn(a, pc, insn, "xor");
    uint8 rd = operandRd(insn);
    uint8 rs1 = operandRs1(insn);
    uint8 rs2 = operandRs2(insn);
    if (rd != 0) {
        uint64 rs1val = readX(a, rs1);
        uint64 rs2val = readX(a, rs2);
        writeX(a, rd, rs1val ^ rs2val);
    }
    return advancePc(a, pc);
}


static inline void executeSRL(UarchState *a, uint32 insn, uint64 pc) {
    dumpInsn(a, pc, insn, "srl");
    uint8 rd = operandRd(insn);
    uint8 rs1 = operandRs1(insn);
    uint8 rs2 = operandRs2(insn);
    if (rd != 0) {
        uint64 rs1val = readX(a, rs1);
        uint64 rs2val = readX(a, rs2);
        writeX(a, rd, uint64ShiftRight(rs1val, (uint32)(rs2val)));
    }
    return advancePc(a, pc);
}


static inline void executeSRA(UarchState *a, uint32 insn, uint64 pc) {
    dumpInsn(a, pc, insn, "sra");
    uint8 rd = operandRd(insn);
    uint8 rs1 = operandRs1(insn);
    uint8 rs2 = operandRs2(insn);
    if (rd != 0) {
        int64 rs1val = (int64)(readX(a, rs1));
        uint32 rs2val = (uint32)(readX(a, rs2));
        writeX(a, rd, (uint64)(int64ShiftRight(rs1val, rs2val)));
    }
    return advancePc(a, pc);
}


static inline void executeSRAW(UarchState *a, uint32 insn, uint64 pc) {
    dumpInsn(a, pc, insn, "sraw");
    uint8 rd = operandRd(insn);
    uint8 rs1 = operandRs1(insn);
    uint8 rs2 = operandRs2(insn);
    int32 rs1val = uint64ToInt32(readX(a, rs1));
    uint32 rs2val = (uint32)(readX(a, rs2));
    int32 rdval = int32ShiftRight(rs1val, rs2val);
    if (rd != 0) {
        writeX(a, rd, int32ToUInt64(rdval));
    }
    return advancePc(a, pc);
}


static inline void executeOR(UarchState *a, uint32 insn, uint64 pc) {
    dumpInsn(a, pc, insn, "or");
    uint8 rd = operandRd(insn);
    uint8 rs1 = operandRs1(insn);
    uint8 rs2 = operandRs2(insn);
    if (rd != 0) {
        uint64 rs1val = readX(a, rs1);
        uint64 rs2val = readX(a, rs2);
        writeX(a, rd, rs1val | rs2val);
    }
    return advancePc(a, pc);
}


static inline void executeAND(UarchState *a, uint32 insn, uint64 pc) {
    dumpInsn(a, pc, insn, "and");
    uint8 rd = operandRd(insn);
    uint8 rs1 = operandRs1(insn);
    uint8 rs2 = operandRs2(insn);
    if (rd != 0) {
        uint64 rs1val = readX(a, rs1);
        uint64 rs2val = readX(a, rs2);
        writeX(a, rd, rs1val & rs2val);
    }
    return advancePc(a, pc);
}


static inline void executeFENCE(UarchState *a, uint32 insn, uint64 pc) {
    dumpInsn(a, pc, insn, "fence");
    return advancePc(a, pc);
}


static inline void executeLWU(UarchState *a, uint32 insn, uint64 pc) {
    dumpInsn(a, pc, insn, "lwu");
    int32 imm = operandImm12(insn);
    uint8 rd = operandRd(insn);
    uint8 rs1 = operandRs1(insn);
    uint64 rs1val = readX(a, rs1);
    uint32 u32 = readUInt32(a, uint64AddInt32(rs1val, imm));
    if (rd != 0) {
        writeX(a, rd, u32);
    }
    return advancePc(a, pc);
}


static inline void executeLD(UarchState *a, uint32 insn, uint64 pc) {
    dumpInsn(a, pc, insn, "ld");
    int32 imm = operandImm12(insn);
    uint8 rd = operandRd(insn);
    uint8 rs1 = operandRs1(insn);
    uint64 rs1val = readX(a, rs1);
    uint64 u64 = readUInt64(a, uint64AddInt32(rs1val, imm));
    if (rd != 0) {
        writeX(a, rd, u64);
    }
    return advancePc(a, pc);
}


static inline void executeSD(UarchState *a, uint32 insn, uint64 pc) {
    dumpInsn(a, pc, insn, "sd");
    int32 imm = operandSimm12(insn);
    uint8 rs1 = operandRs1(insn);
    uint8 rs2 = operandRs2(insn);
    uint64 rs1val = readX(a, rs1);
    uint64 rs2val = readX(a, rs2);
    writeUInt64(a, uint64AddInt32(rs1val, imm), rs2val);
    return advancePc(a, pc);
}

/// \brief Returns true if the opcode field of an instruction matches the provided argument
static inline bool insnMatchOpcode(uint32 insn, uint32 opcode) {
    return ((insn & 0x7f)) == opcode;
}

/// \brief Returns true if the opcode and funct3 fields of an instruction match the provided arguments
static inline bool insnMatchOpcodeFunct3(uint32 insn, uint32 opcode, uint32 funct3) {
    const uint32 mask = (7 << 12) | 0x7f;
    return (insn & mask) == (uint32ShiftLeft(funct3, 12) | opcode);
}

/// \brief Returns true if the opcode, funct3 and funct7 fields of an instruction match the provided arguments
static inline bool insnMatchOpcodeFunct3Funct7(uint32 insn, uint32 opcode, uint32 funct3, uint32 funct7) {
    const uint32 mask = (0x7f << 25) | (7 << 12) | 0x7f;
    return ((insn & mask)) == (uint32ShiftLeft(funct7, 25) | uint32ShiftLeft(funct3, 12) | opcode);
}

/// \brief Returns true if the opcode, funct3 and 6 most significant bits of funct7 fields of an instruction match the
/// provided arguments
static inline bool insnMatchOpcodeFunct3Funct7Sr1(uint32 insn, uint32 opcode, uint32 funct3, uint32 funct7Sr1) {
    const uint32 mask = (0x3f << 26) | (7 << 12) | 0x7f;
    return ((insn & mask)) == (uint32ShiftLeft(funct7Sr1, 26) | uint32ShiftLeft(funct3, 12) | opcode);
}

// Decode and execute one instruction

static inline void executeInsn(UarchState *a, uint32 insn, uint64 pc) {
    if (insnMatchOpcodeFunct3(insn, 0x13, 0x0)) {
        return executeADDI(a, insn, pc);
    } else if (insnMatchOpcodeFunct3(insn, 0x3, 0x3)) {
        return executeLD(a, insn, pc);
    } else if (insnMatchOpcodeFunct3(insn, 0x63, 0x6)) {
        return executeBLTU(a, insn, pc);
    } else if (insnMatchOpcodeFunct3(insn, 0x63, 0x0)) {
        return executeBEQ(a, insn, pc);
    } else if (insnMatchOpcodeFunct3(insn, 0x13, 0x7)) {
        return executeANDI(a, insn, pc);
    } else if (insnMatchOpcodeFunct3Funct7(insn, 0x33, 0x0, 0x0)) {
        return executeADD(a, insn, pc);
    } else if (insnMatchOpcode(insn, 0x6f)) {
        return executeJAL(a, insn, pc);
    } else if (insnMatchOpcodeFunct3Funct7Sr1(insn, 0x13, 0x1, 0x0)) {
        return executeSLLI(a, insn, pc);
    } else if (insnMatchOpcodeFunct3Funct7(insn, 0x33, 0x7, 0x0)) {
        return executeAND(a, insn, pc);
    } else if (insnMatchOpcodeFunct3(insn, 0x23, 0x3)) {
        return executeSD(a, insn, pc);
    } else if (insnMatchOpcode(insn, 0x37)) {
        return executeLUI(a, insn, pc);
    } else if (insnMatchOpcodeFunct3(insn, 0x67, 0x0)) {
        return executeJALR(a, insn, pc);
    } else if (insnMatchOpcodeFunct3(insn, 0x1b, 0x0)) {
        return executeADDIW(a, insn, pc);
    } else if (insnMatchOpcodeFunct3Funct7Sr1(insn, 0x13, 0x5, 0x0)) {
        return executeSRLI(a, insn, pc);
    } else if (insnMatchOpcodeFunct3Funct7(insn, 0x1b, 0x5, 0x0)) {
        return executeSRLIW(a, insn, pc);
    } else if (insnMatchOpcodeFunct3(insn, 0x63, 0x1)) {
        return executeBNE(a, insn, pc);
    } else if (insnMatchOpcodeFunct3(insn, 0x3, 0x2)) {
        return executeLW(a, insn, pc);
    } else if (insnMatchOpcode(insn, 0x17)) {
        return executeAUIPC(a, insn, pc);
    } else if (insnMatchOpcodeFunct3(insn, 0x63, 0x7)) {
        return executeBGEU(a, insn, pc);
    } else if (insnMatchOpcodeFunct3Funct7(insn, 0x3b, 0x0, 0x0)) {
        return executeADDW(a, insn, pc);
    } else if (insnMatchOpcodeFunct3Funct7Sr1(insn, 0x13, 0x5, 0x10)) {
        return executeSRAI(a, insn, pc);
    } else if (insnMatchOpcodeFunct3Funct7(insn, 0x33, 0x6, 0x0)) {
        return executeOR(a, insn, pc);
    } else if (insnMatchOpcodeFunct3Funct7(insn, 0x1b, 0x5, 0x20)) {
        return executeSRAIW(a, insn, pc);
    } else if (insnMatchOpcodeFunct3(insn, 0x63, 0x5)) {
        return executeBGE(a, insn, pc);
    } else if (insnMatchOpcodeFunct3Funct7(insn, 0x33, 0x0, 0x20)) {
        return executeSUB(a, insn, pc);
    } else if (insnMatchOpcodeFunct3(insn, 0x3, 0x4)) {
        return executeLBU(a, insn, pc);
    } else if (insnMatchOpcodeFunct3Funct7(insn, 0x1b, 0x1, 0x0)) {
        return executeSLLIW(a, insn, pc);
    } else if (insnMatchOpcodeFunct3Funct7(insn, 0x33, 0x5, 0x0)) {
        return executeSRL(a, insn, pc);
    } else if (insnMatchOpcodeFunct3Funct7(insn, 0x33, 0x4, 0x0)) {
        return executeXOR(a, insn, pc);
    } else if (insnMatchOpcodeFunct3(insn, 0x23, 0x2)) {
       return executeSW(a, insn, pc);
    } else if (insnMatchOpcodeFunct3Funct7(insn, 0x33, 0x1, 0x0)) {
        return executeSLL(a, insn, pc);
    } else if (insnMatchOpcodeFunct3(insn, 0x63, 0x4)) {
        return executeBLT(a, insn, pc);
    } else if (insnMatchOpcodeFunct3(insn, 0x23, 0x0)) {
        return executeSB(a, insn, pc);
    } else if (insnMatchOpcodeFunct3Funct7(insn, 0x3b, 0x0, 0x20)) {
        return executeSUBW(a, insn, pc);
    } else if (insnMatchOpcodeFunct3(insn, 0x13, 0x4)) {
        return executeXORI(a, insn, pc);
    } else if (insnMatchOpcodeFunct3Funct7(insn, 0x33, 0x5, 0x20)) {
        return executeSRA(a, insn, pc);
    } else if (insnMatchOpcodeFunct3(insn, 0x3, 0x5)) {
        return executeLHU(a, insn, pc);
    } else if (insnMatchOpcodeFunct3(insn, 0x23, 0x1)) {
        return executeSH(a, insn, pc);
    } else if (insnMatchOpcodeFunct3Funct7(insn, 0x3b, 0x5, 0x0)) {
        return executeSRLW(a, insn, pc);
    } else if (insnMatchOpcodeFunct3(insn, 0x3, 0x6)) {
        return executeLWU(a, insn, pc);
    } else if (insnMatchOpcodeFunct3Funct7(insn, 0x3b, 0x1, 0x0)) {
        return executeSLLW(a, insn, pc);
    } else if (insnMatchOpcodeFunct3(insn, 0x3, 0x0)) {
        return executeLB(a, insn, pc);
    } else if (insnMatchOpcodeFunct3Funct7(insn, 0x33, 0x3, 0x0)) {
        return executeSLTU(a, insn, pc);
    } else if (insnMatchOpcodeFunct3Funct7(insn, 0x3b, 0x5, 0x20)) {
        return executeSRAW(a, insn, pc);
    } else if (insnMatchOpcodeFunct3(insn, 0x3, 0x1)) {
        return executeLH(a, insn, pc);
    } else if (insnMatchOpcodeFunct3(insn, 0x13, 0x6)) {
        return executeORI(a, insn, pc);
    } else if (insnMatchOpcodeFunct3(insn, 0x13, 0x3)) {
        return executeSLTIU(a, insn, pc);
    } else if (insnMatchOpcodeFunct3Funct7(insn, 0x33, 0x2, 0x0)) {
        return executeSLT(a, insn, pc);
    } else if (insnMatchOpcodeFunct3(insn, 0x13, 0x2)) {
        return executeSLTI(a, insn, pc);
    } else if (insnMatchOpcodeFunct3(insn, 0xf, 0x0)) {
        return executeFENCE(a, insn, pc);
    }
    a->trap = 253;    
//    throw std::runtime_error("illegal instruction");
}

enum UArchStepStatus uarch_step(UarchState *a) {
    // This must be the first read in order to match the first log access in machine::verify_state_transition
    uint64 cycle = readCycle(a);
    // do not advance if cycle will overflow
    if (cycle == UINT64_MAX) {
        return CycleOverflow;
    }
    // do not advance if machine is halted
    if (readHaltFlag(a)) {
        return UArchHalted;
    }
    // execute next instruction
    uint64 pc = readPc(a);
    uint32 insn = readUInt32(a, pc);
    executeInsn(a, insn, pc);
    cycle = cycle + 1;
    writeCycle(a, cycle);
    return Success;
}


struct Input {
    uint64 access_paddr[16];
    uint64 access_val[16];
    uint8 access_readWriteEnd[16];
};

typedef struct Input Input;

int rv64i(Input input) {
   UarchState state;
   state.access_pointer = 0;
   state.trap = 0;
   for (int i = 0; i < 16; i++) {
      state.access_paddr[i] = input.access_paddr[i];
      state.access_val[i] = input.access_val[i];
      state.access_readWriteEnd[i] = input.access_readWriteEnd[i];
   }
   enum UArchStepStatus ret = uarch_step(&state);
   int retval = 0;
   if (state.access_readWriteEnd[state.access_pointer] != 2) {
     retval = 22;
   } else if (state.trap > 0) {
     retval = state.trap;
   } else if (ret != Success) {
     retval = 1;
   } else if (state.access_pointer > 16) {
     retval = 16;
   } else if (state.access_readWriteEnd[state.access_pointer] != 2) {
     retval = 17;
   } else {
     retval = 0;
   }
   return retval;
}

#define RAM_SIZE 8192
#define PAGE_SIZE 1024
#define RAM_START 0x70000000
#define RAM_END   0x70004000

struct MicroInput {
   uint64 first_page[1024 / 8];
   uint64 ram[RAM_SIZE / 8];
   uint64 access_paddr[16];
   uint64 access_val[16];
   uint8 access_readWriteEnd[16];
};

int mpc_main(struct MicroInput input) {
	struct Input rv64_input;
	int ret;
	ret = 0;
	for (int i = 0; i < 16; i++) {
		// XXX assert it's 64-bit aligned
		if (input.access_readWriteEnd[i] == 0) {
			uint64 paddr = input.access_paddr[i];
			if (paddr < 1024) {
				if (!(input.access_val[i] != input.first_page[paddr / 8])) {
					ret = 44;
				}
			} else if (paddr >= RAM_START && paddr < RAM_END) {
				if (!(input.access_val[i] != input.ram[(paddr - RAM_START) / 8])) {
					ret = 46;
				}
			} else {
				ret = 45;
			}
		} else if (input.access_readWriteEnd[i] == 1) {
			uint64 paddr = input.access_paddr[i];
                        if (paddr < 1024) {
				input.first_page[paddr / 8] = input.access_val[i];
			} else if (paddr >= RAM_START && paddr < RAM_END) {
				input.ram[(paddr - RAM_START) / 8] = input.access_val[i];
			}
		} else if (input.access_readWriteEnd[i] == 2) {
			break;
		}

	}
	if (ret == 0) {
		for (int i = 0; i < 16; i++) {
			rv64_input.access_paddr[i] = input.access_paddr[i];
			rv64_input.access_val[i] = input.access_val[i];
			rv64_input.access_readWriteEnd[i] = input.access_readWriteEnd[i];
		}
		ret = rv64i(rv64_input);

	}
	return ret;
}

#ifdef OTHER
int main() {
   Input input;
   bzero(&input, sizeof(input));
   return mpc_main(input);
}
#endif
