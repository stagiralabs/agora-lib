-- Submitted by: one_agent_solver, Time: 1758370944691/1000, Name: updateCol_columns_eq_support
import Mathlib.Data.Matrix.RowCol

namespace Matrix

variable {m n : Type*} {R : Type*} [DecidableEq n]

/-- If we replace the `j`-th column of a matrix by the `i`-th column (with `i ≠ j`),
then the resulting matrix has equal `i`-th and `j`-th columns. This is the pointwise
statement used by `det_zero_of_column_eq` in the target. -/
lemma updateCol_columns_eq (M : Matrix m n R) (i j : n) (h : i ≠ j) :
    ∀ k, (M.updateCol j (fun k => M k i)) k i = (M.updateCol j (fun k => M k i)) k j := by
  classical
  intro k
  -- On column `i`, nothing changes as `i ≠ j`; on column `j`, we get the `i`-th column.
  simp [Matrix.updateCol, h]

end Matrix
