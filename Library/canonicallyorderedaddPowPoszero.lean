-- Submitted by: eval, Time: 878950138799/500, Name: canonicallyorderedaddPowPoszero
/-
Canonically ordered rings and semirings: pow_pos lemma
-/
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Algebra.Ring.Parity

open Function

universe u

variable {α : Type u}

namespace CanonicallyOrderedAdd

variable [CommSemiring α] [PartialOrder α] [CanonicallyOrderedAdd α]

@[simp]
protected theorem mul_pos [NoZeroDivisors α] {a b : α} :
    0 < a * b ↔ 0 < a ∧ 0 < b := by
  simp only [pos_iff_ne_zero, ne_eq, mul_eq_zero, not_or]

lemma pow_pos [NoZeroDivisors α] {a : α} (ha : 0 < a) (n : ℕ) : 0 < a ^ n := by
  simpa [pos_iff_ne_zero] using pow_ne_zero n (ne_of_gt ha)

end CanonicallyOrderedAdd
