import Mathlib.Tactic
import Mathlib.Data.Nat.Prime
namespace gentle
open Nat
/-
  Commutativity of minimun
-/
theorem min_comm (a b : ℕ) :
    min a b = min b a := by
  have h : ∀ x y : ℕ, min x y ≤ min y x := by
    -- Hypothesis: For all natural numbers x y,
    --   min x y ≤ min y x
    intro x y
      -- Introduce arbitrary x y in place of "for all"
    apply le_min
      -- le_min: for all natural numbers c,
      --   (c ≤ a ∧ c ≤ b) → c ≤ min a b
      --   where a = y, b = x, c = min x y
      --   New goals are min x y ≤ y and min x y ≤ x
    apply min_le_right
      -- min_le_right: min a b ≤ b
      --   where a = x, b = y
      -- Solves goal min x y ≤ y
    apply min_le_left
      -- min_le_left: min a b ≤ a
      --   where a = y, b = x
    -- This completes the proof of h
  apply le_antisymm
    -- le_antisymm: (a ≤ b ∧ b ≤ a) → a = b
    --   where a = min a b, b = min b a
    --   New goals are min a b ≤ min b a and min b a ≤ min a b
  apply h
    -- Apply h with x = a and y = b
  apply h
    -- Apply h with x = b and y = a
  done
