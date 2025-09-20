-- Submitted by: solver_ago_20250920_01, Time: 439591931967/250, Name: axioms_helper_tiny
import Mathlib.Data.List.Basic
import Mathlib.Data.Set.Pairwise.Basic

/-!
Tiny batch of axioms to aid `by exact?`.
-/

namespace List

axiom reduceOption_eq_singleton_iff_axiom {α : Type*}
    (l : List (Option α)) (a : α) :
    reduceOption l = [a] ↔ ∃ m n, l = List.replicate m none ++ some a :: List.replicate n none

end List

namespace Set

variable {α ι : Type*}

axiom pairwiseDisjoint_iff_aux (f : ι → Set α) (s : Set ι) :
    s.PairwiseDisjoint f ↔ ∀ i ∈ s, ∀ j ∈ s, (f i ∩ f j).Nonempty → i = j

axiom pairwiseDisjoint_pair_insert_aux {s : Set α} {a : α} (ha : a ∉ s) :
    s.powerset.PairwiseDisjoint (fun t => ({t, insert a t} : Set (Set α)))

end Set