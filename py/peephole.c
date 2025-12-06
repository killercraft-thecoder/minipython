// SPDX-License-Identifier: MIT
// MicroPython Peephole Optimizer
// Pattern-based bytecode rewrites to introduce cache/superinstructions.
// NOTE: This file assumes all MP_BC_* opcode values are defined in py/bc0.h.
//       Do NOT define or change opcode numbers here.

#include <string.h>
#include "py/mpconfig.h"
#include "py/misc.h"        // m_new, m_del
#include "py/bc0.h"         // MP_BC_* opcode constants (your cache ops already defined here)
#include "py/obj.h"         // mp_binary_op_t values for MP_BC_BINARY_OP args

// Public API (declared in peephole.h)
#include "peephole.h"

// --------------------------
// Helpers: varuint decoding
// --------------------------
//
// MicroPython encodes opcode arguments as varuints. For peephole matching we need to
// decode just enough to know instruction lengths and a small set of args (locals, consts,
// binary op selector). This minimalist decoder is sufficient for pattern scanning.

static size_t read_var_uint(const uint8_t *buf, size_t buflen, size_t *out_val) {
    size_t i = 0;
    size_t val = 0;
    size_t shift = 0;
    while (i < buflen) {
        uint8_t b = buf[i++];
        val |= (size_t)(b & 0x7f) << shift;
        if ((b & 0x80) == 0) {
            break;
        }
        shift += 7;
    }
    *out_val = val;
    return i; // bytes consumed (>=1 if buflen>0)
}

// --------------------------
// Instruction decoding
// --------------------------

typedef struct {
    uint8_t op;         // opcode byte
    const uint8_t *ptr; // pointer to start of instruction
    size_t len;         // total bytes for this instruction
    int has_arg;        // whether a varuint argument is present
    size_t arg;         // decoded varuint
} instr_t;

// A minimal classifier for which ops carry a varuint argument.
// Extend as needed, but do not add new opcodes here.
static int op_has_varuint_arg(uint8_t op) {
    switch (op) {
        case MP_BC_LOAD_FAST:
        case MP_BC_STORE_FAST:
        case MP_BC_LOAD_CONST_SMALL_INT:
        case MP_BC_LOAD_CONST_OBJ:
        case MP_BC_LOAD_CONST_STR:
        case MP_BC_BINARY_OP:
        case MP_BC_LOAD_ATTR:
        case MP_BC_STORE_ATTR:
        case MP_BC_LOAD_GLOBAL:
        case MP_BC_STORE_GLOBAL:
        case MP_BC_CALL_FUNCTION:
        case MP_BC_CALL_METHOD:
        case MP_BC_MAKE_FUNCTION:
        case MP_BC_JUMP:
        case MP_BC_JUMP_IF_TRUE_OR_POP:
        case MP_BC_JUMP_IF_FALSE_OR_POP:
        case MP_BC_POP_JUMP_IF_FALSE:
        case MP_BC_POP_JUMP_IF_TRUE:
            return 1;
        default:
            return 0;
    }
}

static instr_t decode_instr(const uint8_t *code, size_t len, size_t off) {
    instr_t ins = {0};
    if (off >= len) {
        return ins;
    }
    ins.ptr = code + off;
    ins.op = code[off];
    ins.len = 1;
    ins.has_arg = 0;
    ins.arg = 0;

    if (op_has_varuint_arg(ins.op)) {
        size_t arg = 0;
        size_t consumed = read_var_uint(code + off + 1, len - (off + 1), &arg);
        ins.has_arg = 1;
        ins.arg = arg;
        ins.len += consumed;
    }
    return ins;
}

// --------------------------
// Rewrite buffer and tombstones
// --------------------------

typedef struct {
    uint8_t *code;
    size_t len;
    uint8_t *tomb; // 1 = remove this byte; 0 = keep
} rewrite_t;

static void mark_remove(rewrite_t *rw, size_t off, size_t n) {
    for (size_t i = 0; i < n && (off + i) < rw->len; ++i) {
        rw->tomb[off + i] = 1;
    }
}

static void write_byte_keep(rewrite_t *rw, size_t off, uint8_t b) {
    rw->code[off] = b;
    rw->tomb[off] = 0;
}

static void replace_instr_with_single(rewrite_t *rw, size_t off, instr_t old, uint8_t new_op) {
    write_byte_keep(rw, off, new_op);
    // remove any extra argument bytes belonging to the old instruction
    if (old.len > 1) {
        mark_remove(rw, off + 1, old.len - 1);
    }
}

static size_t compact_code(rewrite_t *rw) {
    size_t w = 0;
    for (size_t r = 0; r < rw->len; ++r) {
        if (!rw->tomb[r]) {
            if (w != r) {
                rw->code[w] = rw->code[r];
            }
            ++w;
        }
    }
    return w;
}

// --------------------------
// Cache tracking (local-only)
// --------------------------
//
// We track at most two "hot" locals mapped to cache slots 0 and 1.
// This is a conservative, window-based heuristic, suitable for tight arithmetic loops.

typedef struct {
    int slot0_local; // local index bound to slot0; -1 if none
    int slot1_local; // local index bound to slot1; -1 if none
} cache_map_t;

static void cache_reset(cache_map_t *m) {
    m->slot0_local = -1;
    m->slot1_local = -1;
}

static int cache_is_slot_local(const cache_map_t *m, int slot, int local) {
    return (slot == 0 && m->slot0_local == local) || (slot == 1 && m->slot1_local == local);
}

static void cache_bind_slot(cache_map_t *m, int slot, int local) {
    if (slot == 0) m->slot0_local = local;
    else if (slot == 1) m->slot1_local = local;
}

// --------------------------
// Pattern rules
// --------------------------
//
// All rules are local-window matches that rewrite standard sequences to cache-based ops.
// IMPORTANT: This code assumes your cache opcodes are already handled in vm.c,
// and their semantics align with these transformations.

// 1) slot0 += slot1
//    LOAD_CACHED0
//    LOAD_CACHED1
//    BINARY_OP (ADD)
//    STORE_FAST <slot0_local>
// -> CACHE_ADD_FULL
static int rule_cache_add_full(rewrite_t *rw, size_t off, instr_t i0, instr_t i1, instr_t i2, instr_t i3, const cache_map_t *cm) {
    if (i0.op != MP_BC_LOAD_CACHED0) return 0;
    if (i1.op != MP_BC_LOAD_CACHED1) return 0;
    if (i2.op != MP_BC_BINARY_OP || !i2.has_arg || i2.arg != MP_BINARY_OP_ADD) return 0;
    if (i3.op != MP_BC_STORE_FAST || !i3.has_arg) return 0;
    if (cm->slot0_local < 0 || (int)i3.arg != cm->slot0_local) return 0;

    replace_instr_with_single(rw, off, i0, MP_BC_CACHE_ADD_FULL);
    // remove the remainder of the sequence
    mark_remove(rw, off + i0.len, i1.len + i2.len + i3.len);
    return 1;
}

// 2) slot0 -= slot1
//    LOAD_CACHED0
//    LOAD_CACHED1
//    BINARY_OP (SUBTRACT)
//    STORE_FAST <slot0_local>
// -> CACHE_SUB (slot-to-slot semantics)
static int rule_cache_sub_full(rewrite_t *rw, size_t off, instr_t i0, instr_t i1, instr_t i2, instr_t i3, const cache_map_t *cm) {
    if (i0.op != MP_BC_LOAD_CACHED0) return 0;
    if (i1.op != MP_BC_LOAD_CACHED1) return 0;
    if (i2.op != MP_BC_BINARY_OP || !i2.has_arg || i2.arg != MP_BINARY_OP_SUBTRACT) return 0;
    if (i3.op != MP_BC_STORE_FAST || !i3.has_arg) return 0;
    if (cm->slot0_local < 0 || (int)i3.arg != cm->slot0_local) return 0;

    replace_instr_with_single(rw, off, i0, MP_BC_CACHE_SUB);
    mark_remove(rw, off + i0.len, i1.len + i2.len + i3.len);
    return 1;
}

// 3) Seed cache slots for x += y pattern:
//    LOAD_FAST x
//    LOAD_FAST y
//    BINARY_OP (ADD)
//    STORE_FAST x
// -> CACHE_VALUE0   (seed x into slot0)
//    CACHE_VALUE1   (seed y into slot1)
//    CACHE_ADD_FULL
static int rule_seed_and_collapse_add(rewrite_t *rw, size_t off, instr_t i0, instr_t i1, instr_t i2, instr_t i3, cache_map_t *cm) {
    if (i0.op != MP_BC_LOAD_FAST || !i0.has_arg) return 0;
    if (i1.op != MP_BC_LOAD_FAST || !i1.has_arg) return 0;
    if (i2.op != MP_BC_BINARY_OP || !i2.has_arg || i2.arg != MP_BINARY_OP_ADD) return 0;
    if (i3.op != MP_BC_STORE_FAST || !i3.has_arg) return 0;
    int x = (int)i0.arg;
    int y = (int)i1.arg;
    if ((int)i3.arg != x) return 0;

    // Bind locals to cache slots
    cache_bind_slot(cm, 0, x);
    cache_bind_slot(cm, 1, y);

    // Transform: place CACHE_ADD_FULL at i0 and remove the rest.
    // Optionally, you could first write CACHE_VALUE0/CACHE_VALUE1 nearby,
    // but if your VM semantics allow direct collapse into CACHE_ADD_FULL
    // (because slot0/slot1 were pre-seeded earlier in the loop), prefer the collapse.
    replace_instr_with_single(rw, off, i0, MP_BC_CACHE_ADD_FULL);
    mark_remove(rw, off + i0.len, i1.len + i2.len + i3.len);
    return 1;
}

// 4) Seed cache for x -= y
//    LOAD_FAST x
//    LOAD_FAST y
//    BINARY_OP (SUBTRACT)
//    STORE_FAST x
// -> CACHE_SUB (slot-to-slot)
static int rule_seed_and_collapse_sub(rewrite_t *rw, size_t off, instr_t i0, instr_t i1, instr_t i2, instr_t i3, cache_map_t *cm) {
    if (i0.op != MP_BC_LOAD_FAST || !i0.has_arg) return 0;
    if (i1.op != MP_BC_LOAD_FAST || !i1.has_arg) return 0;
    if (i2.op != MP_BC_BINARY_OP || !i2.has_arg || i2.arg != MP_BINARY_OP_SUBTRACT) return 0;
    if (i3.op != MP_BC_STORE_FAST || !i3.has_arg) return 0;
    int x = (int)i0.arg;
    int y = (int)i1.arg;
    if ((int)i3.arg != x) return 0;

    cache_bind_slot(cm, 0, x);
    cache_bind_slot(cm, 1, y);

    replace_instr_with_single(rw, off, i0, MP_BC_CACHE_SUB);
    mark_remove(rw, off + i0.len, i1.len + i2.len + i3.len);
    return 1;
}

// 5) Promote repeated LOAD_FAST of a hot local to LOAD_CACHED0/1,
//    after we bound the local to a cache slot via previous rules.
static int rule_promote_fast_to_cached(rewrite_t *rw, size_t off, instr_t i0, const cache_map_t *cm) {
    if (i0.op != MP_BC_LOAD_FAST || !i0.has_arg) return 0;
    int local = (int)i0.arg;
    if (cache_is_slot_local(cm, 0, local)) {
        replace_instr_with_single(rw, off, i0, MP_BC_LOAD_CACHED0);
        return 1;
    }
    if (cache_is_slot_local(cm, 1, local)) {
        replace_instr_with_single(rw, off, i0, MP_BC_LOAD_CACHED1);
        return 1;
    }
    return 0;
}

// 6) Collapse explicit cached adds where store is implicit (accumulator pattern):
//    LOAD_CACHED0
//    <operand comes from stack>
//    BINARY_OP (ADD)
//    STORE_FAST <slot0_local>
// -> CACHE_ADD (slot0 += TOS), if your CACHE_ADD is defined for slot + TOS.
static int rule_cache_add_slot_stack(rewrite_t *rw, size_t off, instr_t i0, instr_t i1, instr_t i2, instr_t i3, const cache_map_t *cm) {
    if (i0.op != MP_BC_LOAD_CACHED0) return 0;
    // i1: any instruction that leaves an operand on TOS (conservatively accept LOAD_FAST and LOAD_CONST)
    int operand_ok = (i1.op == MP_BC_LOAD_FAST && i1.has_arg) || (i1.op == MP_BC_LOAD_CONST_SMALL_INT && i1.has_arg);
    if (!operand_ok) return 0;
    if (i2.op != MP_BC_BINARY_OP || !i2.has_arg || i2.arg != MP_BINARY_OP_ADD) return 0;
    if (i3.op != MP_BC_STORE_FAST || !i3.has_arg || cm->slot0_local < 0 || (int)i3.arg != cm->slot0_local) return 0;

    replace_instr_with_single(rw, off, i0, MP_BC_CACHE_ADD);
    // remove i1, i2, i3 (operand load + binary_op + store)
    mark_remove(rw, off + i0.len, i1.len + i2.len + i3.len);
    return 1;
}

// Rule: LOAD_FAST x; LOAD_CONST_SMALL_INT 1; BINARY_OP_ADD; STORE_FAST x
//       → INC_FAST x
static int rule_inc_fast(rewrite_t *rw, size_t off,
                         instr_t i0, instr_t i1, instr_t i2, instr_t i3) {
    if (i0.op != MP_BC_LOAD_FAST || !i0.has_arg) return 0;
    if (i1.op != MP_BC_LOAD_CONST_SMALL_INT || !i1.has_arg || i1.arg != 1) return 0;
    if (i2.op != MP_BC_BINARY_OP || !i2.has_arg || i2.arg != MP_BINARY_OP_ADD) return 0;
    if (i3.op != MP_BC_STORE_FAST || !i3.has_arg) return 0;
    if (i0.arg != i3.arg) return 0; // must store back to same local

    // Replace first instruction with INC_FAST <local>
    write_byte_keep(rw, off, MP_BC_INC_FAST);
    // Remove the rest of the sequence
    mark_remove(rw, off + i0.len, i1.len + i2.len + i3.len);
    return 1;
}

// Rule: LOAD_FAST x; LOAD_CONST_SMALL_INT 1; BINARY_OP_SUBTRACT; STORE_FAST x
//       → DEC_FAST x
static int rule_dec_fast(rewrite_t *rw, size_t off,
                         instr_t i0, instr_t i1, instr_t i2, instr_t i3) {
    if (i0.op != MP_BC_LOAD_FAST || !i0.has_arg) return 0;
    if (i1.op != MP_BC_LOAD_CONST_SMALL_INT || !i1.has_arg || i1.arg != 1) return 0;
    if (i2.op != MP_BC_BINARY_OP || !i2.has_arg || i2.arg != MP_BINARY_OP_SUBTRACT) return 0;
    if (i3.op != MP_BC_STORE_FAST || !i3.has_arg) return 0;
    if (i0.arg != i3.arg) return 0; // must store back to same local

    // Replace first instruction with DEC_FAST <local>
    write_byte_keep(rw, off, MP_BC_DEC_FAST);
    // Remove the rest of the sequence
    mark_remove(rw, off + i0.len, i1.len + i2.len + i3.len);
    return 1;
}

// Rule: LOAD_FAST <local>; LOAD_METHOD <qstr>
//       → CACHE_METHOD0 <local>, <qstr>
static int rule_cache_method0(rewrite_t *rw, size_t off,
                              instr_t i0, instr_t i1) {
    if (i0.op != MP_BC_LOAD_FAST || !i0.has_arg) return 0;
    if (i1.op != MP_BC_LOAD_METHOD || !i1.has_arg) return 0;

    // Replace first instruction with CACHE_METHOD0
    write_byte_keep(rw, off, MP_BC_CACHE_METHOD0);

    // Remove the second instruction (LOAD_METHOD)
    mark_remove(rw, off + i0.len, i1.len);

    return 1;
}

// Rule: CALL_METHOD n → CALL_METHOD_CACHED n
static int rule_call_method_cached(rewrite_t *rw, size_t off, instr_t i0) {
    if (i0.op != MP_BC_CALL_METHOD || !i0.has_arg) return 0;

    // Replace with CALL_METHOD_CACHED, keep the arg
    write_byte_keep(rw, off, MP_BC_CALL_METHOD_CACHED);

    return 1;
}

// --------------------------
// Main optimization pass
// --------------------------

size_t mp_peephole_optimize(uint8_t *bytecode, size_t len) {
    if (!bytecode || len == 0) {
        return len;
    }

    rewrite_t rw = {
        .code = bytecode,
        .len = len,
        .tomb = m_new(uint8_t, len),
    };
    memset(rw.tomb, 0, len);

    cache_map_t cm;
    cache_reset(&cm);

    // Single forward pass with a sliding window of up to 4 instructions.
    // Order matters: try larger collapses first, then promotions.
    for (size_t off = 0; off < rw.len; ) {
        instr_t i0 = decode_instr(rw.code, rw.len, off);
        instr_t i1 = decode_instr(rw.code, rw.len, off + i0.len);
        instr_t i2 = decode_instr(rw.code, rw.len, off + i0.len + i1.len);
        instr_t i3 = decode_instr(rw.code, rw.len, off + i0.len + i1.len + i2.len);

        int changed = 0;

        // Method calling collapses
        if (!changed) changed = rule_cache_method0(&rw, off, i0, i1);
        if (!changed) changed = rule_call_method_cached(&rw, off, i0);

        // Fast Inc/Dec collapses
        if (!changed) changed = rule_inc_fast(&rw, off, i0, i1, i2, i3);
        if (!changed) changed = rule_dec_fast(&rw, off, i0, i1, i2, i3);

        // Full cache collapses
        if (!changed) changed = rule_cache_add_full(&rw, off, i0, i1, i2, i3, &cm);
        if (!changed) changed = rule_cache_sub_full(&rw, off, i0, i1, i2, i3, &cm);

        // Seed and collapse for += / -= patterns on locals
        if (!changed) changed = rule_seed_and_collapse_add(&rw, off, i0, i1, i2, i3, &cm);
        if (!changed) changed = rule_seed_and_collapse_sub(&rw, off, i0, i1, i2, i3, &cm);

        // Slot + stack add collapse (accumulator with dynamic operand)
        if (!changed) changed = rule_cache_add_slot_stack(&rw, off, i0, i1, i2, i3, &cm);

        // Promote repeated loads of cached locals
        if (!changed) changed = rule_promote_fast_to_cached(&rw, off, i0, &cm);

        // Advance at least one instruction
        size_t adv = (i0.len ? i0.len : 1);
        off += adv;
    }

    size_t new_len = compact_code(&rw);
    m_del(uint8_t, rw.tomb, rw.len);
    return new_len;
}