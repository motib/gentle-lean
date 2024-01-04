import Mathlib.Tactic
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.BigOperators.Basic

namespace gentle

open Nat Finset BigOperators

theorem sum_id (n : ℕ) :
    ∑ i in range (n + 1), i = n * (n + 1) / 2 := by
  symm
    -- Prove the symmetric equality
  have : 0 < 2 := by norm_num
    -- Unnamed hypothesis, referred to as "this"
  apply Nat.div_eq_of_eq_mul_right this
    -- div_eq_of_eq_mul_right:
    --   (0 < n) ∧ (m = n * k) → m / n = k
  induction' n with k ih
    -- Induction over n
    -- Base case
  · simp
      -- Inductive step
  · rw [Finset.sum_range_succ]
      -- Finset.sum_range_succ:
      --   ∑ x in range (n + 1), f x = ∑ x in range n, f x + f n
    rw [mul_add 2]
      -- mul_add: a * (b + c) = a * b + a * c
    rw [← ih]
      -- Substitute the inductive hypothesis
    rw [succ_eq_add_one]
      -- succ_eq_add_one : succ n = n + 1
    ring
  done
