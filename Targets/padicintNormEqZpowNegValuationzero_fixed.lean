import Library

-- Submitted at: 219737510296/125, Name: padicintNormEqZpowNegValuationzero_fixed
-- Submitted at: 1757896152453/1000, Name: padicintNormEqZpowNegValuationzero
/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Mario Carneiro, Johan Commelin
-/
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# p-adic integers

This file defines the `p`-adic integers `ℤ_[p]` as the subtype of `ℚ_[p]` with norm `≤ 1`.
We show that `ℤ_[p]`
* is complete,
* is nonarchimedean,
* is a normed ring,
* is a local ring, and
* is a discrete valuation ring.

The relation between `ℤ_[p]` and `ZMod p` is established in another file.

## Important definitions

* `PadicInt` : the type of `p`-adic integers

## Notation

We introduce the notation `ℤ_[p]` for the `p`-adic integers.

## Implementation notes

Much, but not all, of this file assumes that `p` is prime. This assumption is inferred automatically
by taking `[Fact p.Prime]` as a type class argument.

Coercions into `ℤ_[p]` are set up to work with the `norm_cast` tactic.

## References

* [F. Q. Gouvêa, *p-adic numbers*][gouvea1997]
* [R. Y. Lewis, *A formal proof of Hensel's lemma over the p-adic integers*][lewis2019]
* <https://en.wikipedia.org/wiki/P-adic_number>

## Tags

p-adic, p adic, padic, p-adic integer
-/


open Padic Metric IsLocalRing

noncomputable section

variable (p : ℕ) [hp : Fact p.Prime]

/-- The `p`-adic integers `ℤ_[p]` are the `p`-adic numbers with norm `≤ 1`. -/
def PadicInt : Type := {x : ℚ_[p] // ‖x‖ ≤ 1}

/-- The ring of `p`-adic integers. -/
notation "ℤ_[" p "]" => PadicInt p

namespace PadicInt
variable {p} {x y : ℤ_[p]}

/-! ### Ring structure and coercion to `ℚ_[p]` -/

instance : Coe ℤ_[p] ℚ_[p] :=
  ⟨Subtype.val⟩

theorem ext {x y : ℤ_[p]} : ((x : ℚ_[p]) = y) → x = y :=
  Subtype.ext

variable (p)

/-- The `p`-adic integers as a subring of `ℚ_[p]`. -/
def subring : Subring ℚ_[p] where
  carrier := { x : ℚ_[p] | ‖x‖ ≤ 1 }
  zero_mem' := by norm_num
  one_mem' := by norm_num
  add_mem' hx hy := (padicNormE.nonarchimedean _ _).trans <| max_le_iff.2 ⟨hx, hy⟩
  mul_mem' hx hy := (padicNormE.mul _ _).trans_le <| mul_le_one₀ hx (norm_nonneg _) hy
  neg_mem' hx := (norm_neg _).trans_le hx

@[simp]
theorem mem_subring_iff {x : ℚ_[p]} : x ∈ subring p ↔ ‖x‖ ≤ 1 := Iff.rfl

variable {p}

/-- Addition on `ℤ_[p]` is inherited from `ℚ_[p]`. -/
instance : Add ℤ_[p] := (by infer_instance : Add (subring p))

/-- Multiplication on `ℤ_[p]` is inherited from `ℚ_[p]`. -/
instance : Mul ℤ_[p] := (by infer_instance : Mul (subring p))

/-- Negation on `ℤ_[p]` is inherited from `ℚ_[p]`. -/
instance : Neg ℤ_[p] := (by infer_instance : Neg (subring p))

/-- Subtraction on `ℤ_[p]` is inherited from `ℚ_[p]`. -/
instance : Sub ℤ_[p] := (by infer_instance : Sub (subring p))

/-- Zero on `ℤ_[p]` is inherited from `ℚ_[p]`. -/
instance : Zero ℤ_[p] := (by infer_instance : Zero (subring p))

instance : Inhabited ℤ_[p] := ⟨0⟩

/-- One on `ℤ_[p]` is inherited from `ℚ_[p]`. -/
instance : One ℤ_[p] := ⟨⟨1, by norm_num⟩⟩

@[simp]
theorem mk_zero {h} : (⟨0, h⟩ : ℤ_[p]) = (0 : ℤ_[p]) := rfl

@[simp, norm_cast]
theorem coe_add (z1 z2 : ℤ_[p]) : ((z1 + z2 : ℤ_[p]) : ℚ_[p]) = z1 + z2 := rfl

@[simp, norm_cast]
theorem coe_mul (z1 z2 : ℤ_[p]) : ((z1 * z2 : ℤ_[p]) : ℚ_[p]) = z1 * z2 := rfl

@[simp, norm_cast]
theorem coe_neg (z1 : ℤ_[p]) : ((-z1 : ℤ_[p]) : ℚ_[p]) = -z1 := rfl

@[simp, norm_cast]
theorem coe_sub (z1 z2 : ℤ_[p]) : ((z1 - z2 : ℤ_[p]) : ℚ_[p]) = z1 - z2 := rfl

@[simp, norm_cast]
theorem coe_one : ((1 : ℤ_[p]) : ℚ_[p]) = 1 := rfl

@[simp, norm_cast]
theorem coe_zero : ((0 : ℤ_[p]) : ℚ_[p]) = 0 := rfl

@[simp] lemma coe_eq_zero : ((x : ℚ_[p]) = 0) ↔ x = 0 := by rw [← coe_zero, Subtype.coe_inj]

lemma coe_ne_zero : ((x : ℚ_[p]) ≠ 0) ↔ x ≠ 0 := coe_eq_zero.not

instance : AddCommGroup ℤ_[p] := (by infer_instance : AddCommGroup (subring p))

instance instCommRing : CommRing ℤ_[p] := (by infer_instance : CommRing (subring p))

@[simp, norm_cast]
theorem coe_natCast (n : ℕ) : ((n : ℤ_[p]) : ℚ_[p]) = n := rfl

@[simp, norm_cast]
theorem coe_intCast (z : ℤ) : ((z : ℤ_[p]) : ℚ_[p]) = z := rfl

/-- The coercion from `ℤ_[p]` to `ℚ_[p]` as a ring homomorphism. -/
def Coe.ringHom : ℤ_[p] →+* ℚ_[p] := (subring p).subtype

@[simp, norm_cast]
theorem coe_pow (x : ℤ_[p]) (n : ℕ) : ((x ^ n : ℤ_[p]) : ℚ_[p]) = ((x : ℚ_[p]) ^ n) := rfl

theorem mk_coe (k : ℤ_[p]) : (⟨k, k.2⟩ : ℤ_[p]) = k := by simp

/-- The inverse of a `p`-adic integer with norm equal to `1` is also a `p`-adic integer.
Otherwise, the inverse is defined to be `0`. -/
def inv : ℤ_[p] → ℤ_[p]
  | ⟨k, _⟩ => if h : ‖k‖ = 1 then ⟨k⁻¹, by simp [h]⟩ else 0

instance : CharZero ℤ_[p] where
  cast_injective m n h :=
    Nat.cast_injective (R := ℚ_[p]) (by rw [Subtype.ext_iff] at h; norm_cast at h)

@[norm_cast]
theorem intCast_eq (z1 z2 : ℤ) : (z1 : ℤ_[p]) = z2 ↔ z1 = z2 := by simp

/-! ### Norm -/

theorem norm_le_one (z : ℤ_[p]) : ‖z‖ ≤ 1 := z.2

@[simp]
theorem padic_norm_e_of_padicInt (z : ℤ_[p]) : ‖(z : ℚ_[p])‖ = ‖z‖ := by simp [show ‖z‖ = ‖(z : ℚ_[p])‖ from rfl]

/-! ### Valuation on `ℤ_[p]` -/

/-- `PadicInt.valuation` lifts the `p`-adic valuation on `ℚ` to `ℤ_[p]`. -/
def valuation (x : ℤ_[p]) : ℕ := ((x : ℚ_[p]).valuation).toNat

@[simp, norm_cast] lemma valuation_coe (x : ℤ_[p]) : (x : ℚ_[p]).valuation = x.valuation := by
  simp [valuation]

@[simp] lemma valuation_zero : valuation (0 : ℤ_[p]) = 0 := by simp [valuation]
@[simp] lemma valuation_one : valuation (1 : ℤ_[p]) = 0 := by simp [valuation]
@[simp] lemma valuation_p : valuation (p : ℤ_[p]) = 1 := by simp [valuation]

@[simp]
lemma valuation_pow (x : ℤ_[p]) (n : ℕ) : (x ^ n).valuation = n * x.valuation := by
  zify; simp [← valuation_coe]

lemma norm_eq_zpow_neg_valuation {x : ℤ_[p]} (hx : x ≠ 0) : ‖x‖ = p ^ (-(x.valuation : ℤ)) := by
  have hx' : ((x : ℚ_[p]) ≠ 0) := coe_ne_zero.2 hx
  calc
    ‖x‖ = ‖(x : ℚ_[p])‖ := (padic_norm_e_of_padicInt x).symm
    _ = p ^ (-( (x : ℚ_[p]).valuation : ℤ)) := by simpa using Padic.norm_eq_zpow_neg_valuation hx'
    _ = p ^ (-(x.valuation : ℤ)) := by simpa [valuation_coe]

end PadicInt