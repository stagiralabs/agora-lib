import Library

-- Submitted at: 219737102806/125, Name: privateZlatticeCovolumeFrontierEquivfunzero
/-
Copyright (c) 2024 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.Analysis.BoxIntegral.UnitPartition
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Covolume of ℤ-lattices

Let `E` be a finite dimensional real vector space.

Let `L` be a `ℤ`-lattice `L` defined as a discrete `ℤ`-submodule of `E` that spans `E` over `ℝ`.

## Main definitions and results

* `ZLattice.covolume`: the covolume of `L` defined as the volume of an arbitrary fundamental
domain of `L`.

* `ZLattice.covolume_eq_measure_fundamentalDomain`: the covolume of `L` does not depend on the
choice of the fundamental domain of `L`.

* `ZLattice.covolume_eq_det`: if `L` is a lattice in `ℝ^n`, then its covolume is the absolute
value of the determinant of any `ℤ`-basis of `L`.

* `ZLattice.covolume.tendsto_card_div_pow`: Let `s` be a bounded measurable set of `ι → ℝ`, then
the number of points in `s ∩ n⁻¹ • L` divided by `n ^ card ι` tends to `volume s / covolume L`
when `n : ℕ` tends to infinity. See also `ZLattice.covolume.tendsto_card_div_pow'` for a version
for `InnerProductSpace ℝ E` and `ZLattice.covolume.tendsto_card_div_pow''` for the general version.

* `ZLattice.covolume.tendsto_card_le_div`: Let `X` be a cone in `ι → ℝ` and let `F : (ι → ℝ) → ℝ`
be a function such that `F (c • x) = c ^ card ι * F x`. Then the number of points `x ∈ X` such that
`F x ≤ c` divided by `c` tends to `volume {x ∈ X | F x ≤ 1} / covolume L` when `c : ℝ` tends to
infinity. See also `ZLattice.covolume.tendsto_card_le_div'` for a version for
`InnerProductSpace ℝ E` and `ZLattice.covolume.tendsto_card_le_div''` for the general version.

## Naming convention

Some results are true in the case where the ambient finite dimensional real vector space is the
pi-space `ι → ℝ` and in the case where it is an `InnerProductSpace`. We use the following
convention: the plain name is for the pi case, for eg. `volume_image_eq_volume_div_covolume`. For
the same result in the `InnerProductSpace` case, we add a `prime`, for eg.
`volume_image_eq_volume_div_covolume'`. When the same result exists in the
general case, we had two primes, eg. `covolume.tendsto_card_div_pow''`.

-/

noncomputable section

namespace ZLattice

open Submodule MeasureTheory Module MeasureTheory Module ZSpan

section General

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] (L : Submodule ℤ E)

/-- The covolume of a `ℤ`-lattice is the volume of some fundamental domain; see
`ZLattice.covolume_eq_volume` for the proof that the volume does not depend on the choice of
the fundamental domain. -/
def covolume (μ : Measure E := by volume_tac) : ℝ := (addCovolume L E μ).toReal

end General

section Basic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]
variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
variable (μ : Measure E := by volume_tac) [Measure.IsAddHaarMeasure μ]

/-- A more general version of `ZLattice.volume_image_eq_volume_div_covolume`;
see the `Naming conventions` section in the introduction. -/
theorem volume_image_eq_volume_div_covolume' {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] {ι : Type*} [Fintype ι]
    (b : Basis ι ℤ L) {s : Set E} (hs : NullMeasurableSet s) :
    volume ((b.ofZLatticeBasis ℝ).equivFun '' s) = volume s / ENNReal.ofReal (covolume L) := by
  classical
  let e : Fin (finrank ℝ E) ≃ ι :=
    Fintype.equivOfCardEq (by rw [Fintype.card_fin, finrank_eq_card_basis (b.ofZLatticeBasis ℝ)])
  let f := (EuclideanSpace.equiv ι ℝ).symm.trans
    ((stdOrthonormalBasis ℝ E).reindex e).repr.toContinuousLinearEquiv.symm
  have hf : MeasurePreserving f :=
    ((stdOrthonormalBasis ℝ E).reindex e).measurePreserving_repr_symm.comp
      (EuclideanSpace.volume_preserving_measurableEquiv ι).symm
  rw [← hf.measure_preimage hs, ← (covolume_comap L volume volume hf),
    ← volume_image_eq_volume_div_covolume (ZLattice.comap ℝ L f.toLinearMap)
    (b.ofZLatticeComap ℝ L f.toLinearEquiv), Basis.ofZLatticeBasis_comap,
    ← f.image_symm_eq_preimage, ← Set.image_comp]
  simp only [Basis.equivFun_apply, ContinuousLinearEquiv.symm_toLinearEquiv, Basis.map_equivFun,
    LinearEquiv.symm_symm, Function.comp_apply, LinearEquiv.trans_apply,
    ContinuousLinearEquiv.coe_toLinearEquiv, ContinuousLinearEquiv.apply_symm_apply]

end Basic

namespace covolume

section General

open Filter Fintype Pointwise Topology BoxIntegral Bornology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {L : Submodule ℤ E} [DiscreteTopology L] [IsZLattice ℝ L]
variable {ι : Type*} [Fintype ι] (b : Basis ι ℤ L)

/-- A version of `ZLattice.covolume.tendsto_card_div_pow` for the general case;
see the `Naming convention` section in the introduction. -/
/-- A version of `ZLattice.covolume.tendsto_card_le_div` for the general case;
see the `Naming conventions` section in the introduction. -/

end General

section Pi

open Filter Fintype Pointwise Topology Bornology

private theorem frontier_equivFun {E : Type*} [AddCommGroup E] [Module ℝ E] {ι : Type*} [Fintype ι]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    (b : Basis ι ℝ E) (s : Set E) :
    frontier (b.equivFun '' s) = b.equivFun '' (frontier s) := by
  exact?