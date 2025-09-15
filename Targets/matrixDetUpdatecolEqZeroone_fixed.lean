import Library

-- Submitted at: 219737426916/125, Name: matrixDetUpdatecolEqZeroone_fixed
-- Submitted at: 219736980173/125, Name: matrixDetUpdatecolEqZeroone
/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Anne Baanen
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.RowCol
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.LinearAlgebra.Alternating.Basic
import Mathlib.LinearAlgebra.Matrix.SemiringInverse

/-!
# Determinant of a matrix

This file defines the determinant of a matrix, `Matrix.det`, and its essential properties.

## Main definitions

 - `Matrix.det`: the determinant of a square matrix, as a sum over permutations
 - `Matrix.detRowAlternating`: the determinant, as an `AlternatingMap` in the rows of the matrix

## Main results

 - `det_mul`: the determinant of `A * B` is the product of determinants
 - `det_zero_of_row_eq`: the determinant is zero if there is a repeated row
 - `det_block_diagonal`: the determinant of a block diagonal matrix is a product
   of the blocks' determinants

## Implementation notes

It is possible to configure `simp` to compute determinants. See the file
`MathlibTest/matrix.lean` for some examples.

-/


universe u v w z

open Equiv Equiv.Perm Finset Function

namespace Matrix

variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]
variable {R : Type v} [CommRing R]

local notation "ε " σ:arg => ((sign σ : ℤ) : R)

/-- `det` is an `AlternatingMap` in the rows of the matrix. -/
def detRowAlternating : (n → R) [⋀^n]→ₗ[R] R :=
  MultilinearMap.alternatization ((MultilinearMap.mkPiAlgebra R n R).compLinearMap LinearMap.proj)

/-- The determinant of a matrix given by the Leibniz formula. -/
abbrev det (M : Matrix n n R) : R :=
  detRowAlternating M

thorem det_apply (M : Matrix n n R) : M.det = ∑ σ : Perm n, Equiv.Perm.sign σ • ∏ i, M (σ i) i :=
  MultilinearMap.alternatization_apply _ M

-- This is what the old definition was. We use it to avoid having to change the old proofs below
theorem det_apply' (M : Matrix n n R) : M.det = ∑ σ : Perm n, ε σ * ∏ i, M (σ i) i := by
  simp [det_apply, Units.smul_def]

thorem det_eq_detp_sub_detp (M : Matrix n n R) : M.det = M.detp 1 - M.detp (-1) := by
  rw [det_apply, ← Equiv.sum_comp (Equiv.inv (Perm n)), ← ofSign_disjUnion, sum_disjUnion]
  simp_rw [inv_apply, sign_inv, sub_eq_add_neg, detp, ← sum_neg_distrib]
  refine congr_arg₂ (· + ·) (sum_congr rfl fun σ hσ ↦ ?_) (sum_congr rfl fun σ hσ ↦ ?_) <;>
    rw [mem_ofSign.mp hσ, ← Equiv.prod_comp σ] <;> simp

@[simp]
theorem det_diagonal {d : n → R} : det (diagonal d) = ∏ i, d i := by
  rw [det_apply']
  refine (Finset.sum_eq_single 1 ?_ ?_).trans ?_
  · rintro σ _ h2
    obtain ⟨x, h3⟩ := not_forall.1 (mt Equiv.ext h2)
    convert mul_zero (ε σ)
    apply Finset.prod_eq_zero (mem_univ x)
    exact if_neg h3
  · simp
  · simp

 theorem det_zero (_ : Nonempty n) : det (0 : Matrix n n R) = 0 :=
  (detRowAlternating : (n → R) [⋀^n]→ₗ[R] R).map_zero

@[simp]
theorem det_one : det (1 : Matrix n n R) = 1 := by rw [← diagonal_one]; simp [-diagonal_one]

 theorem det_isEmpty [IsEmpty n] {A : Matrix n n R} : det A = 1 := by simp [det_apply]

@[simp]
 theorem coe_det_isEmpty [IsEmpty n] : (det : Matrix n n R → R) = Function.const _ 1 := by
  ext
  exact det_isEmpty

 theorem det_eq_one_of_card_eq_zero {A : Matrix n n R} (h : Fintype.card n = 0) : det A = 1 :=
  haveI : IsEmpty n := Fintype.card_eq_zero_iff.mp h
  det_isEmpty

/-- If `n` has only one element, the determinant of an `n` by `n` matrix is just that element.
Although `Unique` implies `DecidableEq` and `Fintype`, the instances might
not be syntactically equal. Thus, we need to fill in the args explicitly. -/
@[simp]
 theorem det_unique {n : Type*} [Unique n] [DecidableEq n] [Fintype n] (A : Matrix n n R) :
    det A = A default default := by simp [det_apply, univ_unique]

 theorem det_eq_elem_of_subsingleton [Subsingleton n] (A : Matrix n n R) (k : n) :
    det A = A k k := by
  have := uniqueOfSubsingleton k
  convert det_unique A

 theorem det_eq_elem_of_card_eq_one {A : Matrix n n R} (h : Fintype.card n = 1) (k : n) :
    det A = A k k :=
  haveI : Subsingleton n := Fintype.card_le_one_iff_subsingleton.mp h.le
  det_eq_elem_of_subsingleton _ _

/-- If a matrix has a repeated row, the determinant will be zero. -/
 theorem det_zero_of_row_eq (i_ne_j : i ≠ j) (hij : M i = M j) : M.det = 0 :=
  (detRowAlternating : (n → R) [⋀^n]→ₗ[R] R).map_eq_zero_of_eq M hij i_ne_j

/-- If a matrix has a repeated column, the determinant will be zero. -/
 theorem det_zero_of_column_eq (i_ne_j : i ≠ j) (hij : ∀ k, M k i = M k j) : M.det = 0 := by
  rw [← det_transpose, det_zero_of_row_eq i_ne_j]
  exact funext hij

/-- If we repeat a row of a matrix, we get a matrix of determinant zero. -/
 theorem det_updateRow_eq_zero (h : i ≠ j) :
    (M.updateRow j (M i)).det = 0 := det_zero_of_row_eq h (by simp [h])

/-- If we repeat a column of a matrix, we get a matrix of determinant zero. -/
 theorem det_updateCol_eq_zero (h : i ≠ j) :
    (M.updateCol j (fun k ↦ M k i)).det = 0 := det_zero_of_column_eq h (by simp [h])

@[deprecated (since := "2024-12-11")] alias det_updateColumn_eq_zero := det_updateCol_eq_zero

end Matrix