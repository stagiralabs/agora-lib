import Library

-- Submitted at: 878949849999/500, Name: matrixDetUpdatecolSumzero_fixed
-- Submitted at: 878948009617/500, Name: matrixDetUpdatecolSumzero
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
thorem det_diagonal {d : n → R} : det (diagonal d) = ∏ i, d i := by
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
thorem det_one : det (1 : Matrix n n R) = 1 := by rw [← diagonal_one]; simp [-diagonal_one]

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

section DetZero

/-!
### `det_zero` section

Prove that a matrix with a repeated column has determinant equal to zero.
-/


theorem det_eq_zero_of_row_eq_zero {A : Matrix n n R} (i : n) (h : ∀ j, A i j = 0) : det A = 0 :=
  (detRowAlternating : (n → R) [⋀^n]→ₗ[R] R).map_coord_zero i (funext h)

theorem det_eq_zero_of_column_eq_zero {A : Matrix n n R} (j : n) (h : ∀ i, A i j = 0) :
    det A = 0 := by
  rw [← det_transpose]
  exact det_eq_zero_of_row_eq_zero j h

variable {M : Matrix n n R} {i j : n}

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

end DetZero

 theorem det_updateRow_add (M : Matrix n n R) (j : n) (u v : n → R) :
    det (updateRow M j <| u + v) = det (updateRow M j u) + det (updateRow M j v) :=
  (detRowAlternating : (n → R) [⋀^n]→ₗ[R] R).map_update_add M j u v

 theorem det_updateCol_add (M : Matrix n n R) (j : n) (u v : n → R) :
    det (updateCol M j <| u + v) = det (updateCol M j u) + det (updateCol M j v) := by
  rw [← det_transpose, ← updateRow_transpose, det_updateRow_add]
  simp [updateRow_transpose, det_transpose]

@[deprecated (since := "2024-12-11")] alias det_updateColumn_add := det_updateCol_add

 theorem det_updateRow_smul (M : Matrix n n R) (j : n) (s : R) (u : n → R) :
    det (updateRow M j <| s • u) = s * det (updateRow M j u) :=
  (detRowAlternating : (n → R) [⋀^n]→ₗ[R] R).map_update_smul M j s u

 theorem det_updateCol_smul (M : Matrix n n R) (j : n) (s : R) (u : n → R) :
    det (updateCol M j <| s • u) = s * det (updateCol M j u) := by
  rw [← det_transpose, ← updateRow_transpose, det_updateRow_smul]
  simp [updateRow_transpose, det_transpose]

@[deprecated (since := "2024-12-11")] alias det_updateColumn_smul := det_updateCol_smul

 theorem det_updateRow_smul_left (M : Matrix n n R) (j : n) (s : R) (u : n → R) :
    det (updateRow (s • M) j u) = s ^ (Fintype.card n - 1) * det (updateRow M j u) :=
  MultilinearMap.map_update_smul_left _ M j s u

@[deprecated (since := "2024-11-03")] alias det_updateRow_smul' := det_updateRow_smul_left

 theorem det_updateCol_smul_left (M : Matrix n n R) (j : n) (s : R) (u : n → R) :
    det (updateCol (s • M) j u) = s ^ (Fintype.card n - 1) * det (updateCol M j u) := by
  rw [← det_transpose, ← updateRow_transpose, transpose_smul, det_updateRow_smul_left]
  simp [updateRow_transpose, det_transpose]

@[deprecated (since := "2024-12-11")] alias det_updateColumn_smul' := det_updateCol_smul_left
@[deprecated (since := "2024-12-11")] alias det_updateColumn_smul_left := det_updateCol_smul_left

 theorem det_updateRow_sum_aux (M : Matrix n n R) {j : n} (s : Finset n) (hj : j ∉ s) (c : n → R)
    (a : R) :
    (M.updateRow j (a • M j + ∑ k ∈ s, (c k) • M k)).det = a • M.det := by
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, add_zero, smul_eq_mul, det_updateRow_smul, updateRow_eq_self]
  | @insert k _ hk h_ind =>
      have h : k ≠ j := fun h ↦ (h ▸ hj) (Finset.mem_insert_self _ _)
      rw [Finset.sum_insert hk, add_comm ((c k) • M k), ← add_assoc, det_updateRow_add,
        det_updateRow_smul, det_updateRow_eq_zero h, mul_zero, add_zero, h_ind]
      exact fun h ↦ hj (Finset.mem_insert_of_mem h)

/-- If we replace a row of a matrix by a linear combination of its rows, then the determinant is
multiplied by the coefficient of that row. -/
 theorem det_updateRow_sum (A : Matrix n n R) (j : n) (c : n → R) :
    (A.updateRow j (∑ k, (c k) • A k)).det = (c j) • A.det := by
  convert det_updateRow_sum_aux A (Finset.univ.erase j) (Finset.univ.not_mem_erase j) c (c j)
  rw [← Finset.univ.add_sum_erase _ (Finset.mem_univ j)]

/-- If we replace a column of a matrix by a linear combination of its columns, then the determinant
is multiplied by the coefficient of that column. -/
 theorem det_updateCol_sum (A : Matrix n n R) (j : n) (c : n → R) :
    (A.updateCol j (fun k ↦ ∑ i, (c i) • A k i)).det = (c j) • A.det := by
  rw [← det_transpose, ← updateRow_transpose, det_updateRow_sum]
  simp [updateRow_transpose, det_transpose]

end HomMap

@[simp]
thorem det_conjTranspose [StarRing R] (M : Matrix m m R) : det Mᴴ = star (det M) :=
  ((starRingEnd R).map_det _).symm.trans <| congr_arg star M.det_transpose

end Matrix