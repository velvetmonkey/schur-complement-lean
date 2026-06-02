/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harmonic
-/
import Mathlib

/-! # Schur complement: `nonsing_inv` API and block-diagonal inverse

This file extends `Mathlib.LinearAlgebra.Matrix.SchurComplement` with:

* `Matrix.schurComplement`: a named definition for the Schur complement `D - C * A⁻¹ * B`.
* `Matrix.inv_fromBlocks₁₁`: the explicit 2×2 block-inverse formula using `⁻¹` instead of `⅟`.
* `Matrix.det_fromBlocks_eq_det_mul_det_schurComplement`: the determinant identity
  `det (fromBlocks A B C D) = det A * det (schurComplement A B C D)` using `⁻¹`.
* `Matrix.isUnit_fromBlocks_iff_isUnit_schurComplement₁₁`: invertibility characterisation
  using `IsUnit` and `⁻¹`.
* `Matrix.inv_fromBlocks_zero₂₁_zero₁₂`: block-diagonal inverse
  `(fromBlocks A 0 0 D)⁻¹ = fromBlocks A⁻¹ 0 0 D⁻¹`.

All results are stated over a `CommRing` with general `Fintype` / `DecidableEq` index types,
following Mathlib conventions.

## References

* Mathlib issue #38808: "Schur complement for block matrices and singular value bounds"
-/

namespace Matrix

open scoped Matrix

variable {l m n α : Type*}
variable [Fintype l] [Fintype m] [Fintype n]
variable [DecidableEq l] [DecidableEq m] [DecidableEq n]

section CommRing

variable [CommRing α]

/-! ### Named Schur complement -/

/-- The **Schur complement** of a block matrix `[A B; C D]` with respect to the top-left block `A`.
Defined as `D - C * A⁻¹ * B`. When `A` is invertible this equals `D - C * ⅟A * B`. -/
noncomputable def schurComplement (A : Matrix m m α) (B : Matrix m n α) (C : Matrix n m α)
    (D : Matrix n n α) : Matrix n n α :=
  D - C * A⁻¹ * B

omit [Fintype n] [DecidableEq n] in
/-- When `A` is invertible, the Schur complement with `⁻¹` agrees with the one using `⅟`. -/
theorem schurComplement_eq_sub_mul_invOf_mul [Invertible A] (B : Matrix m n α) (C : Matrix n m α)
    (D : Matrix n n α) :
    schurComplement A B C D = D - C * ⅟A * B := by
  simp [schurComplement, invOf_eq_nonsing_inv]

/-! ### Invertibility characterisation -/

/-- A block matrix `fromBlocks A B C D` with `A` invertible is a unit iff its Schur complement
`D - C * A⁻¹ * B` is a unit. This is the `nonsing_inv` version of
`Matrix.isUnit_fromBlocks_iff_of_invertible₁₁`. -/
theorem isUnit_fromBlocks_iff_isUnit_schurComplement₁₁
    {A : Matrix m m α} {B : Matrix m n α} {C : Matrix n m α} {D : Matrix n n α}
    [Invertible A] :
    IsUnit (fromBlocks A B C D) ↔ IsUnit (schurComplement A B C D) := by
  rw [schurComplement_eq_sub_mul_invOf_mul]
  exact isUnit_fromBlocks_iff_of_invertible₁₁

/-! ### Determinant via Schur complement -/

/-- `det (fromBlocks A B C D) = det A * det (schurComplement A B C D)` when `A` is invertible.
This is the `nonsing_inv` version of `Matrix.det_fromBlocks₁₁`. -/
theorem det_fromBlocks_eq_det_mul_det_schurComplement
    (A : Matrix m m α) (B : Matrix m n α) (C : Matrix n m α)
    (D : Matrix n n α) [Invertible A] :
    (fromBlocks A B C D).det = A.det * (schurComplement A B C D).det := by
  rw [schurComplement_eq_sub_mul_invOf_mul, det_fromBlocks₁₁]

/-! ### Explicit block-inverse formula (nonsing_inv version) -/

/-- The explicit block-inverse formula for `(fromBlocks A B C D)⁻¹` when `A` and the Schur
complement `S = D - C * A⁻¹ * B` are both invertible. This is the `⁻¹` analogue of
`Matrix.invOf_fromBlocks₁₁_eq`.

The formula is:
```
(fromBlocks A B C D)⁻¹ =
  fromBlocks (A⁻¹ + A⁻¹ * B * S⁻¹ * C * A⁻¹)  (-(A⁻¹ * B * S⁻¹))
             (-(S⁻¹ * C * A⁻¹))                  S⁻¹
```
-/
theorem inv_fromBlocks₁₁ (A : Matrix m m α) (B : Matrix m n α) (C : Matrix n m α)
    (D : Matrix n n α) [Invertible A] [Invertible (D - C * ⅟A * B)] :
    (fromBlocks A B C D)⁻¹ =
      let S := D - C * A⁻¹ * B
      fromBlocks (A⁻¹ + A⁻¹ * B * S⁻¹ * C * A⁻¹) (-(A⁻¹ * B * S⁻¹))
        (-(S⁻¹ * C * A⁻¹)) S⁻¹ := by
  convert invOf_fromBlocks₁₁_eq A B C D using 1
  all_goals try exact fromBlocks₁₁Invertible A B C D
  · grind +suggestions
  · simp +decide only [invOf_eq_nonsing_inv]

/-! ### Block-diagonal inverse -/

/-- The inverse of a block-diagonal matrix is the block diagonal of inverses,
when both diagonal blocks are invertible. -/
theorem inv_fromBlocks_zero₂₁_zero₁₂ (A : Matrix m m α) (D : Matrix n n α)
    [Invertible A] [Invertible D] :
    (fromBlocks A 0 0 D)⁻¹ = fromBlocks A⁻¹ 0 0 D⁻¹ := by
  convert inv_fromBlocks_zero₂₁_of_isUnit_iff A (0 : Matrix m n α) D ?_ using 1
  · norm_num
  · exact iff_of_true (isUnit_of_invertible A) (isUnit_of_invertible D)

end CommRing

end Matrix
