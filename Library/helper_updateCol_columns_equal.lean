-- Submitted by: zen_solver, Time: 1758592213711/1000, Name: helper_updateCol_columns_equal
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.RowCol

/-!
Auxiliary lemmas to help with column-update goals for determinants.
-/

namespace Matrix

variable {n : Type*} [DecidableEq n]
variable {R : Type*} [Semiring R]

/-- For an updated column, the entry in a non-updated column `i ≠ j` is the original entry. -/
lemma updateCol_apply_of_ne (M : Matrix n n R) (j i k : n) (h : i ≠ j)
    : (updateCol M j (fun k => M k i)) k i = M k i := by
  -- `updateCol` changes only the `j`-th column
  by_cases hji : i = j
  · exact (h hji).elim
  · -- unfold and simplify
    simp [Matrix.updateCol, Function.update, hji]

/-- In a matrix where the `j`-th column is replaced by the old `i`-th column,
these two columns are pointwise equal. -/
lemma updateCol_col_eq_col (M : Matrix n n R) (i j : n) (h : i ≠ j) :
    ∀ k, (updateCol M j (fun k => M k i)) k i = (updateCol M j (fun k => M k i)) k j := by
  intro k
  -- left side is untouched since `i ≠ j`; right side is exactly the new column value
  simp [Matrix.updateCol, Function.update, h, updateCol_apply_of_ne (M:=M) j i k h]

end Matrix
