import Library

-- Submitted at: 351670669561/200, Name: contmdiffmapCoeOnezero
/-
Copyright (c) 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri
-/
import Mathlib.Geometry.Manifold.Algebra.Structures

/-!
# Algebraic structures over `C^n` functions

In this file, we define instances of algebraic structures over `C^n` functions.
-/


noncomputable section

open scoped Manifold ContDiff

open TopologicalSpace

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H : Type*}
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {N : Type*} [TopologicalSpace N] [ChartedSpace H N]
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] {H'' : Type*} [TopologicalSpace H'']
  {I'' : ModelWithCorners 𝕜 E'' H''} {N' : Type*} [TopologicalSpace N'] [ChartedSpace H'' N']
  {n : WithTop ℕ∞}

namespace ContMDiffMap

@[to_additive]
protected instance instMul {G : Type*} [Mul G] [TopologicalSpace G] [ChartedSpace H' G]
    [ContMDiffMul I' n G] : Mul C^n⟮I, N; I', G⟯ :=
  ⟨fun f g => ⟨f * g, f.contMDiff.mul g.contMDiff⟩⟩

@[to_additive (attr := simp)]
theorem coe_mul {G : Type*} [Mul G] [TopologicalSpace G] [ChartedSpace H' G] [ContMDiffMul I' n G]
    (f g : C^n⟮I, N; I', G⟯) : ⇑(f * g) = f * g :=
  rfl

@[to_additive (attr := simp)]
theorem mul_comp {G : Type*} [Mul G] [TopologicalSpace G] [ChartedSpace H' G] [ContMDiffMul I' n G]
    (f g : C^n⟮I'', N'; I', G⟯) (h : C^n⟮I, N; I'', N'⟯) : (f * g).comp h = f.comp h * g.comp h :=
  rfl

@[to_additive]
protected instance instOne {G : Type*} [One G] [TopologicalSpace G] [ChartedSpace H' G] :
    One C^n⟮I, N; I', G⟯ :=
  ⟨ContMDiffMap.const (1 : G)⟩

@[to_additive (attr := by exact?
