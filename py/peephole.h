// SPDX-License-Identifier: MIT
// MicroPython Peephole Optimizer
// Provides pattern-based bytecode rewrites to introduce cache and superinstructions.

#ifndef MICROPY_PEEPHOLE_H
#define MICROPY_PEEPHOLE_H

#include <stddef.h>
#include <stdint.h>

// Optimize bytecode buffer in-place.
// - bytecode: pointer to bytecode buffer (mutable)
// - len: length of the buffer in bytes
// Returns the new length (may change if compaction removes instructions).
size_t mp_peephole_optimize(uint8_t *bytecode, size_t len);

#endif // MICROPY_PEEPHOLE_H