import Mathlib.Tactic

namespace gentle

-- Inductive definition of natural numbers
inductive Nat
| zero : Nat
| succ : Nat → Nat

-- Open a namespace so we can use zero and succ
--   instead of Nat.zero and Nat.succ
namespace Nat

-- Inductive definition of addition
def add : Nat → Nat → Nat
  | x, zero => x
  | x, succ y => succ (add x y)

-- For a natural number n, 0 + n = n
theorem zero_add (n : Nat) :
    add zero n = n := by
  induction' n with k ih
    -- Base case 0 + 0 = 0
    -- Follows by base case of the
    --   inductive definition of add
  · rfl
      -- Inductive step
      --   0 + (k+1) = k+1
  · rw [add]
      -- By inductive definition of add
      --   0 + (k+1) = (0 + k) + 1
    rw [ih]
      -- By the inductive hypothesis (0+k) = k
  done

-- For natural numbers m, n,
--   (m+1) + n = (m+n) + 1
theorem succ_add (m n : Nat) :
    add (succ m) n = succ (add m n) := by
  induction' n with k ih
  · rfl
    -- Base case (m+1) + 0 = m+1
    -- Follows by base case of the
    --   inductive definition of add
  · rw [add]
      -- Inductive step
      --   (m+1) + (k+1) = (m + (k+1)) + 1
      -- From the inductive definition of add:
      --   x, succ y => succ (add x y)
      --   we get ((m+1) + k) + 1 = (m + (k+1)) + 1
    rw [ih]
      -- The inductive hypothesis is
      --   (m+1) + k = (m+k) + 1, from which
      --   we get ((m+k) + 1) + 1 = (m + (k+1)) + 1
    rfl
      -- Solved by reflexivity
  done

theorem div_prod1 {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) :
    m ∣ n * k := by
  rcases h with ⟨a, h1⟩ | ⟨b, h2⟩
  · rw [h1]
    rw [mul_assoc]
    apply dvd_mul_right
  · rw [h2]
    rw [mul_comm]
    rw [mul_assoc]
    apply dvd_mul_right
  done

theorem div_prod2 {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) :
    m ∣ n * k := by
  -- The disjunctive hypothesis gives rise to two goals
  -- rfl uses the definition of m ∣ n as
  --   there exists a such that n = m * a
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [mul_assoc]
    apply dvd_mul_right
      -- dvd_mul_right: a ∣ a * b
  · rw [mul_comm, mul_assoc]
    apply dvd_mul_right
  done
