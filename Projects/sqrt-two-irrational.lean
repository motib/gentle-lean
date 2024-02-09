import Mathlib.Tactic
import Mathlib.Data.Nat.Prime
import Std.Data.Nat.Gcd

-- Author: https://www.weizmann.ac.il/sci-tea/benari/

namespace gentle
open Nat
/-
 Prove that for two coprime natural numbers m, n
   (with no common factors other than 1),
   m ^ 2 ≠ 2 * n ^ 2
 Start with two preliminary lemmas
-/
lemma pow_two (a : ℕ) : a ^ 2 = a * a := by
  rw [Nat.pow_succ]
    -- Nat.pow_succ:  n ^ succ m = n ^ m * n,
    --   where n = a, m = 1, succ m = 1 + 1
    -- New goal is a ^ 1 * a = a * a
  rw [pow_one]
    -- pow_one: a ^ 1 = a
  done

lemma even_of_even_sqr (m : ℕ) (h : 2 ∣ m ^ 2) : 2 ∣ m := by
  rw [pow_two] at h
    -- pow_two (lemma): a ^ 2 = a * a,
    --   where a = m
    -- New goal is 2 ∣ m
  rw [prime_two.dvd_mul] at h
    -- prime_two: 2 is prime
    -- dvd_mul: if p is prime then p ∣ m * m ↔ p ∣ m ∨ p ∣ m,
    --   where p = 2, m = m,
    -- Apply to h : 2 | m * m → 2 | m ∨ 2 | m
    -- h is now 2 | m ∨ 2 | m, goal is still 2 ∣ m

  rcases h with h₁ | h₁
    -- Splits disjunctive hypothesis h: 2 | m ∨ 2 ∣ m  into
    --   two (identical ) subformulas 2 ∣ m, 2 ∣ m
    -- Both need to be proved
  · exact h₁
      -- 2 ∣ m proves 2 ∣ m
  · exact h₁
      -- 2 ∣ m proves 2 ∣ m
  done

theorem sqr_not_even (m n : ℕ) (coprime_mn : Coprime m n) :
    m ^ 2 ≠ 2 * n ^ 2 := by
  intro sqr_eq
    -- Assume sqr_eq: m ^ 2 = 2 * n ^ 2 and
    --   prove a contradiction
  have two_dvd_m : 2 ∣ m := by
    apply even_of_even_sqr
      --  even_of_even_sqr (lemma): 2 ∣ m ^ 2 → 2 ∣ m
      --  New goal is 2 ∣ m ^ 2
    rw [sqr_eq]
      -- sqr_eq: m ^ 2 = 2 * n ^ 2.
      -- Apply to the current goal.
      -- The new goal is 2 ∣ 2 * n ^ 2
    apply dvd_mul_right
      -- dvd_mul_right: a ∣ a * b,
      --   where a = 2, b = n ^ 2
      -- Apply to the current goal to prove two_dvd_m : 2 ∣ m

  have h : ∃ c, m = c * 2 := by
    apply dvd_iff_exists_eq_mul_left.mp two_dvd_m
      -- dvd_iff_exists_eq_mul_left: a ∣ b ↔ ∃ c, b = c * a
      --   where a = 2, b = m, c = c
      -- Use MP with two_dvd_m: 2 ∣ m to prove h

  rcases h with ⟨k, meq⟩
    -- h : ∃ c, m = c * 2 is an existential formula
    --   rcases on h:
    --     k is the free variable for the bound variable c
    --     meq : m = k * 2 is a new hypothesis
    -- Type ⟨ ⟩ using \< \>

  have h₁ : 2 * (2 * k ^ 2) = 2 * n ^ 2 := by
    rw [← sqr_eq]
      -- sqr_eq : m ^ 2 = 2 * n ^ 2
      -- ← is right to left rewriting of 2 * n ^ 2 in h₁
      -- New goal is 2 * (2 * k ^ 2) = m ^ 2
    rw [meq]
      -- Rewrite m = k * 2 in h₁
      -- New goal is  2 * (2 * k ^ 2) = (k * 2) ^ 2
    ring
      -- Prove goal by using the ring axioms

  have h₂ : 2 * k ^ 2 = n ^ 2 := by
    apply (mul_right_inj' (by norm_num : 2 ≠ 0)).mp h₁
      -- mul_right_inj': a ≠ 0 → (a * b = a * c ↔ b = c)
      --   where a = 2, b = 2 * k ^ 2, c = n ^ 2
      -- norm_num: solves equalities and inequalities like 2 ≠ 0
      -- Since 2 ≠ 0, MP on h₁ proves h₂

  have h₃ : 2 ∣ n := by
    apply even_of_even_sqr
      -- even_of_even_sqr (lemma) : 2 ∣ m ^ 2 → 2 ∣ m
      --   where m = n
      -- New goal is 2 ∣ n ^ 2
    rw [← h₂]
      -- Rewrite right-to-left of h₂ in the goal
      -- New goal is 2 ∣ 2 * k ^ 2
    apply dvd_mul_right
      -- dvd_mul_right : a ∣ a * b,
      --   where a = 2, b = k ^ 2 to prove h₃

  have h₄ : 2 ∣ Nat.gcd m n := by
    apply Nat.dvd_gcd
      -- Nat.dvd_gcd : (k ∣ m ∧ k | m) → k ∣ gcd m n
      --   k = 2, m = m, n = n
      -- New goals are 2 ∣ m and 2 ∣ n
    · exact two_dvd_m
      -- First goal is two_dvd_m
    . exact h₃
      -- Second goal is h₃

  have h₅ : 2 ∣ 1 := by
    rw [Coprime.gcd_eq_one] at h₄
      -- if m and n are coprime then gcd m n = 1,
      --   where m = 2 and n = 1
      -- Apply to h₄
      -- New goals are 2 ∣ 1 and m, n are coprime
    exact h₄
      -- Proves 2 ∣ 1
    exact coprime_mn
      -- Assumption that m, n are coprime
  norm_num at h₅
    -- Goal is 2 ∣ 1
    -- norn_num can prove that this is False
    -- Proving the contradiction of the initial assumption
  done
