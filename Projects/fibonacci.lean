import Mathlib.Tactic

namespace gentle

-- Define Fibonacci from 0
-- Define as a map from ℕ to ℚ in order to prove
--   the theorem below
def fib : ℕ → ℚ
  | 0 => 0
  | 1 => 1
  | n + 2 => fib (n + 1) + fib n

theorem seven_fourths (n : ℕ) : fib n < (7 / 4 : ℚ) ^ n := by
  -- twoStepInduction enables a proof with two base cases
  induction' n using Nat.twoStepInduction with k ih1 ih2
    -- Proofs for 0, 1 are trivial by definition
    --   and simple inequalities

  ·  rw [fib] ; norm_num
  ·  rw [fib] ; norm_num
    -- Inductive step
    -- First prove two numerical hypotheses that will be needed

  · have h1 : 0 < (7/4:ℚ)^k := by apply pow_pos ; norm_num
    have h2 : 1+(7/4:ℚ) < (7/4)^2 := by norm_num

   -- Use calc to prove that fib (k + 2) < (7/4)^(k+2)
    calc fib (k + 2) = fib (k + 1) + fib k := by rw [fib]
       _ < (7/4)^(k+1) + (7/4)^k := by rel [ih1, ih2]
         -- Tactic rel is used to substitute the hypotheses
         --   into the expression
       _ = (7/4)^k * (1+(7/4)) := by ring
         -- mul_lt_mul_left: 0 < a → a * b < a * c ↔ b < c
         -- First use h1 to prove 0 < a and then
         --   use h2 on the right-to-left implication
       _ < (7/4)^k * (7/4)^2 := by
           apply (mul_lt_mul_left  h1).mpr h2
       _ = (7/4)^(k+2) := by ring
  done

-- Seven_fourths theorem proved using gcongr
theorem seven_fourths_gcongr (n : ℕ) : fib n < (7 / 4 : ℚ) ^ n := by
  induction' n using Nat.twoStepInduction with k ih1 ih2
  ·  rw [fib] ; norm_num
  ·  rw [fib] ; norm_num
  · calc fib (k + 2) = fib (k + 1) + fib k := by rw [fib]
       _ < (7/4)^(k+1) + (7/4)^k := by gcongr
       _ = (7/4)^k * (1+(7/4)) := by ring
       _ < (7/4)^k * (7/4)^2 := by gcongr ; norm_num
       _ = (7/4)^(k+2) := by ring
  done
