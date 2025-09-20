import Library

-- Submitted at: 1758364191689/1000, Name: listReduceoptionEqSingletonIffzero
/-
Copyright (c) 2020 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky, Anthony DeRossi
-/
import Mathlib.Data.List.Basic

/-!
# Properties of `List.reduceOption`

In this file we prove basic lemmas about `List.reduceOption`.
-/

namespace List

variable {α β : Type*}

@[simp]
theorem reduceOption_cons_of_some (x : α) (l : List (Option α)) :
    reduceOption (some x :: l) = x :: l.reduceOption := by
  simp only [reduceOption, filterMap, id, eq_self_iff_true, and_self_iff]

@[simp]
theorem reduceOption_cons_of_none (l : List (Option α)) :
    reduceOption (none :: l) = l.reduceOption := by simp only [reduceOption, filterMap, id]

@[simp]
theorem reduceOption_nil : @reduceOption α [] = [] :=
  rfl

@[simp]
theorem reduceOption_map {l : List (Option α)} {f : α → β} :
    reduceOption (map (Option.map f) l) = map f (reduceOption l) := by
  induction' l with hd tl hl
  · simp only [reduceOption_nil, map_nil]
  · cases hd <;>
      simpa [Option.map_some', map, eq_self_iff_true, reduceOption_cons_of_some] using hl

theorem reduceOption_append (l l' : List (Option α)) :
    (l ++ l').reduceOption = l.reduceOption ++ l'.reduceOption :=
  filterMap_append l l' id

@[simp]
theorem reduceOption_replicate_none {n : ℕ} : (replicate n (@none α)).reduceOption = [] := by
  dsimp [reduceOption]
  rw [filterMap_replicate_of_none (id_def _)]

theorem reduceOption_eq_nil_iff (l : List (Option α)) :
    l.reduceOption = [] ↔ ∃ n, l = replicate n none := by
  dsimp [reduceOption]
  rw [filterMap_eq_nil_iff]
  constructor
  · intro h
    exact ⟨l.length, eq_replicate_of_mem h⟩
  · intro ⟨_, h⟩
    simp_rw [h, mem_replicate]
    tauto

theorem reduceOption_eq_singleton_iff (l : List (Option α)) (a : α) :
    l.reduceOption = [a] ↔ ∃ m n, l = replicate m none ++ some a :: replicate n none := by
  exact?
