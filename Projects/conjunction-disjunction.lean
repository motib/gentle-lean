import Mathlib.Tactic
import Mathlib.Data.Int.Basic

-- Author: https://www.weizmann.ac.il/sci-tea/benari/

namespace gentle
/-
  Conjunction and disjunction
-/
theorem lt_iff_le_eq {a b : Int} :
    a < b ↔ (a ≤ b ∧ a ≠ b) := by
  rw [lt_iff_le_not_le]
    -- lt_iff_le_not_le : a < b ↔ (a ≤ b ∧ ¬b ≤ a)

  constructor
    -- Creates two subgoals (mp and mpr) from the current ↔ goal
    -- First subgoal is (a ≤ b ∧ ¬b ≤ a) → (a ≤ b ∧ a ≠ b)

  -- Prove the mp subgoal
  · rintro ⟨h0, h1⟩
    -- rintro introduces the premise as a hypothesis and also
    --   performs an rcases on the hypothesis to split it
    --   two sub-hypotheses a ≤ b and ¬b ≤ a
    constructor
      -- Creates two subgoals from the current conjunctive goal
    · exact h0
        -- Proves the second subgoal
    · intro h2
        -- a ≠ b is a = b → False
      apply h1
        -- Replace False with the negation of the hypothesis
      rw [h2]
        -- Proof is complete since b ≤ b

  -- Prove the mpr subgoal
  · rintro ⟨h0, h1⟩
    constructor
    · exact h0
    · intro h2
      apply h1
      apply le_antisymm h0 h2
        --  le_antisymm (a ≤ b) → (b ≤ a) → a = b
  done

theorem lt_abs {x y : Int} :
    x < |y| ↔ (x < y ∨ x < -y) := by
  rcases le_or_gt 0 y with h | h
    -- Absolute value depends on sign of y
    -- le_or_gt 0 y: a ≤ b ∨ a > b

    -- y is positive
  · rw [abs_of_nonneg h]
    -- abs_of_nonneg: 0 ≤ a → |a| = a
    constructor
      -- Split iff into mp and mpr
    · intro h'
      left
        -- The current goal is a disjunction
        --   so tell Lean which disjunct we want to prove
      exact h'
    . intro h'
      rcases h' with h' | h'
        -- The hypothesis is a disjunction and we have to prove
        --   the goal for each disjunct
      · exact h'
      . linarith
        -- The hypotheses are 0 ≤ y and x < -y
        -- Lean can prove that this implies the goal x < y
  -- y is negative
  · rw [abs_of_neg h]
    constructor
    · intro h'
      right
      exact h'
    . intro h'
      rcases h' with h' | h'
      · linarith
      . exact h'
  done
