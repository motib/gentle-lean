import Mathlib.Tactic
import Mathlib.Data.Nat.Prime

-- Author: https://www.weizmann.ac.il/sci-tea/benari/

namespace gentle
open Nat
/-
  There exists an infinite number of primes
-/
theorem exists_infinite_primes (n : ℕ) :
    ∃ p, n ≤ p ∧ Nat.Prime p := by
      -- For all natural numbers n,
      --   there exists a natural number p,
      --   such that n ≤ p and p is a prime
  let p := minFac (n !  + 1)
    -- if n ! + 1 ≠ 1, p is its smallest prime factor
  have f1 : n ! + 1 ≠ 1 := by
    apply Nat.ne_of_gt <| succ_lt_succ <| factorial_pos _
      -- factorial_pos: n ! > 0
      -- succ_lt_succ: m < n → succ m < succ n
      --   where m = 0, n = n !
      --   succ(essor of) n is the formal definition of n + 1
      -- ne_of_gt: b < a → b ≠ a
      --   where b = 1 and a = n ! + 1
      -- <| means that the formula on its right is
      --   the input to the one on its left

  have pp : Nat.Prime p := by
    apply minFac_prime f1
      -- minFac_prime: if n ≠ 1 then
      --   the smallest prime factor of n prime,
      --     where n = n ! + 1
      -- f1 proves pp

  have np : n ≤ p := by
    apply le_of_not_ge
      -- le_of_not_ge: ¬a ≥ b → a ≤ b
      --   where a = n, b = p
      -- New goal is ¬n > p
    intro h
      -- By definition of negation, n ≥ p → False
      -- Assume n ≥ p and make False the new goal
      --   to prove np by contradiction
    have h₁ : p ∣ n ! := by
      apply dvd_factorial (minFac_pos _) h
        -- minFac_pos: 0 < minFac n,
        --   where _ means that this holds for any n
        -- dvd_factorial: (0 < m ∨ m ≤ n) → m ∣ n !
        --   where m = p
        -- p is natural so 0 < m and
        -- p ≤ n by assumption (intro) h
        -- h₁ is proved

    have h₂ : p ∣ 1 := by
      apply (Nat.dvd_add_iff_right h₁).mpr (minFac_dvd _)
        -- minFac_dvd: minFac n ∣ n,
        --   where _ means that this holds for any n
        -- dvd_add_iff_right: k ∣ m → (k ∣ n ↔ (k ∣ m) + n)
        --   where k = p, m = n !, n = 1
        --   p ∣ n ! by h₁, so p | 1 iff p ∣ n ! + 1
        -- mpr (MP reverse): p ∣ n ! + 1 → p | 1
        --   p ∣ n ! + 1 by definition
        --   since pp shows that p is prime
        -- p ∣ is proved

    apply Nat.Prime.not_dvd_one pp
      -- if p is a prime (true by pp) then ¬p ∣ 1
      --   which is p | 1 → False
    exact h₂
      -- Use MP with h₂, proving False and
      --   thus np by contradiction,
      --   since by definition a prime is ≥ 2
    -- The proof of np : np: n ≤ p is (finally) complete

  use p
    -- Introduce free variable p for the bound variable p
    --   to get n ≤ p ∧ Nat.Prime p
    -- Since both conjuncts are hypotheses,
    --   the proof is complete
  done

theorem exists_infinite_primes_sorry (n : ℕ) :
    ∃ p, n ≤ p ∧ Nat.Prime p := by
  let p := minFac (n !  + 1)
  have f1 : n ! + 1 ≠ 1 := by
    apply Nat.ne_of_gt <| succ_lt_succ <| factorial_pos _
  have pp : Nat.Prime p := by
    apply minFac_prime f1
  have np : n ≤ p       := by sorry
  use p
  done
