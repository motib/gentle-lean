import Mathlib.Tactic
import Mathlib.Data.Nat.Prime

-- Author: https://www.weizmann.ac.il/sci-tea/benari/

namespace gentle
open Nat
/-
  Commutativity of gcd
-/
theorem gcd_comm (m n : ℕ) :
    Nat.gcd m n = Nat.gcd n m := by
  apply Nat.dvd_antisymm
    -- dvd_antisymm: (m ∣ n ∧ n ∣ m) → m = n,
    --   where m = gcd m n, n = gcd n m
    -- Two new goals: gcd m n ∣ gcd n m, gcd n m ∣ gcd m n

  -- First goal
  apply Nat.dvd_gcd
      -- dvd_gcd: (k ∣ m ∧ k ∣ n) → k ∣ gcd m n,
      --   where k = gcd m n, m = n, n = m
      -- New goals are gcd m n ∣ n and gcd m n ∣ m
  apply Nat.gcd_dvd_right
      -- gcd_dvd_right: gcd m n ∣ n,
      --   where m = m, n = n
  apply Nat.gcd_dvd_left
      -- gcd_dvd_left: gcd m n ∣ m
      --   where m = m, n = n

  -- Second goal
  apply Nat.dvd_gcd
      -- dvd_gcd: (k ∣ m ∧ k ∣ n) → k ∣ gcd m n,
      --   where k = gcd n m, m = m, n = n
      -- New goals are gcd n m ∣ m and gcd n m ∣ n
  apply Nat.gcd_dvd_right
      -- gcd_dvd_right: gcd m n ∣ n,
      --   where m = n, n = m
  apply Nat.gcd_dvd_left
      -- gcd_dvd_left: gcd m n ∣ m
      --   where m = n, n = m
  done
