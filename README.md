# schur-complement-lean

[![Lean 4](https://img.shields.io/badge/Lean-4.28.0-blue)](https://lean-lang.org/)
[![Mathlib](https://img.shields.io/badge/Mathlib-v4.28.0-purple)](https://github.com/leanprover-community/mathlib4)
[![Proofs](https://img.shields.io/badge/proofs-0%20sorry-brightgreen)](SchurComplement)

Standalone Lean 4 / Mathlib module for Schur-complement `nonsing_inv` (`⁻¹`) APIs.

## Scope

This repository contains a clean-room candidate Mathlib contribution targeting Mathlib issue #38808. It extends Mathlib's existing `Mathlib.LinearAlgebra.Matrix.SchurComplement` API with versions stated using `⁻¹` / `nonsing_inv` rather than only `⅟`.

All declarations live in the `Matrix` namespace and are stated over a `CommRing` with general finite index types.

## Declarations

| Declaration | Description |
| --- | --- |
| `Matrix.schurComplement` | Named Schur complement definition `D - C * A⁻¹ * B`. |
| `Matrix.isUnit_fromBlocks_iff_isUnit_schurComplement₁₁` | Invertibility characterisation: `fromBlocks A B C D` is a unit iff the Schur complement is a unit, assuming `[Invertible A]`. |
| `Matrix.inv_fromBlocks₁₁` | Explicit 2x2 block inverse formula using `⁻¹`, assuming `[Invertible A]` and `[Invertible (D - C * ⅟A * B)]`. |
| `Matrix.det_fromBlocks_eq_det_mul_det_schurComplement` | Determinant identity `det (fromBlocks A B C D) = det A * det (schurComplement A B C D)`, assuming `[Invertible A]`. |
| `Matrix.inv_fromBlocks_zero₂₁_zero₁₂` | Block-diagonal inverse `(fromBlocks A 0 0 D)⁻¹ = fromBlocks A⁻¹ 0 0 D⁻¹`, assuming `[Invertible A] [Invertible D]`. |

The helper theorem `Matrix.schurComplement_eq_sub_mul_invOf_mul` records the bridge between `⁻¹` and Mathlib's existing `⅟` formulation when `[Invertible A]`.

## Block-Diagonal Caveat

The block-diagonal inverse theorem intentionally requires `[Invertible A] [Invertible D]`. The unconditional statement is false: if exactly one diagonal block is invertible, the inverse of the full block matrix and the block diagonal of inverses do not agree.

## PR Readiness

This file is PR-oriented but not yet in final Mathlib form. The current header reads `Authors: Harmonic`, and the module lives outside Mathlib's module hierarchy. For a Mathlib PR, it should be relocated into the appropriate Mathlib module path and re-attributed according to Mathlib contribution conventions.

## Building

```bash
lake exe cache get
lake build
```

## Verification

The module is expected to build with Mathlib v4.28.0 and contains no `sorry` or `admit`.
