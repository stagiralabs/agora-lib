import Library

-- Submitted at: 1758363610761/1000, Name: isapproximatesubgroupPowInterPowCovbysmulSqInterSqzero
/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Combinatorics.Additive.CovBySMul
import Mathlib.Combinatorics.Additive.RuzsaCovering
import Mathlib.Combinatorics.Additive.SmallTripling

/-!
# Approximate subgroups

This file defines approximate subgroups of a group, namely symmetric sets `A` such that `A * A` can
be covered by a small number of translates of `A`.

## Main results

Approximate subgroups are a central concept in additive combinatorics, as a natural weakening and
flexible substitute of genuine subgroups. As such, they share numerous properties with subgroups:
* `IsApproximateSubgroup.image`: Group homomorphisms send approximate subgroups to approximate
  subgroups
* `IsApproximateSubgroup.pow_inter_pow`: The intersection of (non-trivial powers of) two approximate
  subgroups is an approximate subgroup. Warning: The intersection of two approximate subgroups isn't
  an approximate subgroup in general.

Approximate subgroups are close qualitatively and quantitatively to other concepts in additive
combinatorics:
* `IsApproximateSubgroup.card_pow_le`: An approximate subgroup has small powers.
* `IsApproximateSubgroup.of_small_tripling`: A set of small tripling can be made an approximate
  subgroup by squaring.

It can be readily confirmed that approximate subgroups are a weakening of subgroups:
* `isApproximateSubgroup_one`: A 1-approximate subgroup is the same thing as a subgroup.
-/

open scoped Finset Pointwise

variable {G : Type*} [Group G] {A B : Set G} {K L : ℝ} {m n : ℕ}

/--
An approximate subgroup in a group is a symmetric set `A` containing the identity and such that
`A + A` can be covered by a small number of translates of `A`.

In practice, we will take `K` fixed and `A` large but finite.
-/
structure IsApproximateAddSubgroup {G : Type*} [AddGroup G] (K : ℝ) (A : Set G) : Prop where
  zero_mem : 0 ∈ A
  neg_eq_self : -A = A
  two_nsmul_covByVAdd : CovByVAdd G K (2 • A) A

/--
An approximate subgroup in a group is a symmetric set `A` containing the identity and such that
`A * A` can be covered by a small number of translates of `A`.

In practice, we will take `K` fixed and `A` large but finite.
-/
@[to_additive]
structure IsApproximateSubgroup (K : ℝ) (A : Set G) : Prop where
  one_mem : 1 ∈ A
  inv_eq_self : A⁻¹ = A
  sq_covBySMul : CovBySMul G K (A ^ 2) A

namespace IsApproximateSubgroup

@[to_additive] lemma nonempty (hA : IsApproximateSubgroup K A) : A.Nonempty := ⟨1, hA.one_mem⟩

@[to_additive one_le]
lemma one_le (hA : IsApproximateSubgroup K A) : 1 ≤ K := by
  obtain ⟨F, hF, hSF⟩ := hA.sq_covBySMul
  have hF₀ : F ≠ ∅ := by rintro rfl; simp [hA.nonempty.pow.ne_empty] at hSF
  exact hF.trans' <| by simpa [Finset.nonempty_iff_ne_empty]

@[to_additive]
lemma mono (hKL : K ≤ L) (hA : IsApproximateSubgroup K A) : IsApproximateSubgroup L A where
  one_mem := hA.one_mem
  inv_eq_self := hA.inv_eq_self
  sq_covBySMul := hA.sq_covBySMul.mono hKL

@[to_additive]
lemma card_pow_le [DecidableEq G] {A : Finset G} (hA : IsApproximateSubgroup K (A : Set G)) :
    ∀ {n}, #(A ^ n) ≤ K ^ (n - 1) * #A
  | 0 => by simpa using hA.nonempty
  | 1 => by simp
  | n + 2 => by
    obtain ⟨F, hF, hSF⟩ := hA.sq_covBySMul
    calc
      (#(A ^ (n + 2)) : ℝ) ≤ #(F ^ (n + 1) * A) := by
        gcongr; exact mod_cast Set.pow_subset_pow_mul_of_sq_subset_mul hSF (by omega)
      _ ≤ #(F ^ (n + 1)) * #A := mod_cast Finset.card_mul_le
      _ ≤ #F ^ (n + 1) * #A := by gcongr; exact mod_cast Finset.card_pow_le
      _ ≤ K ^ (n + 1) * #A := by gcongr

@[to_additive]
lemma card_mul_self_le [DecidableEq G] {A : Finset G} (hA : IsApproximateSubgroup K (A : Set G)) :
    #(A * A) ≤ K * #A := by simpa [sq] using hA.card_pow_le (n := 2)

@[to_additive]
lemma image {F H : Type*} [Group H] [FunLike F G H] [MonoidHomClass F G H] (f : F)
    (hA : IsApproximateSubgroup K A) : IsApproximateSubgroup K (f '' A) where
  one_mem := ⟨1, hA.one_mem, map_one _⟩
  inv_eq_self := by simp [← Set.image_inv, hA.inv_eq_self]
  sq_covBySMul := by
    classical
    obtain ⟨F, hF, hAF⟩ := hA.sq_covBySMul
    refine ⟨F.image f, ?_, ?_⟩
    · calc
        (#(F.image f) : ℝ) ≤ #F := mod_cast F.card_image_le
        _ ≤ K := hF
    · simp only [← Set.image_pow, Finset.coe_image, ← Set.image_mul, smul_eq_mul] at hAF ⊢
      gcongr

@[to_additive]
lemma subgroup {S : Type*} [SetLike S G] [SubgroupClass S G] {H : S} :
    IsApproximateSubgroup 1 (H : Set G) where
  one_mem := OneMemClass.one_mem H
  inv_eq_self := inv_coe_set
  sq_covBySMul := ⟨{1}, by simp⟩

open Finset in
@[to_additive]
lemma of_small_tripling [DecidableEq G] {A : Finset G} (hA₁ : 1 ∈ A) (hAsymm : A⁻¹ = A)
    (hA : #(A ^ 3) ≤ K * #A) : IsApproximateSubgroup (K ^ 3) (A ^ 2 : Set G) where
  one_mem := by rw [sq, ← one_mul 1]; exact Set.mul_mem_mul hA₁ hA₁
  inv_eq_self := by simp [← inv_pow, hAsymm, ← coe_inv]
  sq_covBySMul := by
    replace hA := calc (#(A ^ 4 * A) : ℝ)
      _ = #(A ^ 5) := by rw [← pow_succ]
      _ ≤ K ^ 3 * #A := small_pow_of_small_tripling (by omega) hA hAsymm
    have hA₀ : A.Nonempty := ⟨1, hA₁⟩
    obtain ⟨F, -, hF, hAF⟩ := ruzsa_covering_mul hA₀ hA
    exact ⟨F, hF, by norm_cast; simpa [div_eq_mul_inv, pow_succ, mul_assoc, hAsymm] using hAF⟩

open Set in
@[to_additive]
lemma pow_inter_pow_covBySMul_sq_inter_sq
    (hA : IsApproximateSubgroup K A) (hB : IsApproximateSubgroup L B) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    CovBySMul G (K ^ (m - 1) * L ^ (n - 1)) (A ^ m ∩ B ^ n) (A ^ 2 ∩ B ^ 2) := by
  exact?
