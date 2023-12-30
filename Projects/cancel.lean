import Mathlib.Data.Int.Basic
namespace gentle
open Int
/-
  Cancellation in addition and multiplication by zero
-/
theorem neg_add_cancel_left (a b : Int) :
    -a + (a + b) = b := by
  rw [← add_assoc]
    -- add_assoc: a + b + c = a + (b + c)
    -- Addition is left associative: a + b + c = (a + b) + c
    -- New goal is -a + a + b = b
  rw [add_left_neg]
    -- add_left_neg: -a + a = 0
    -- New goal is 0 + b = b
  exact zero_add b
    -- zero_add: 0 + a = a, where a = b
  done

theorem add_left_cancel {a b c : Int}
    (h : a + b = a + c) : b = c := by
  rw [← neg_add_cancel_left a b]
    -- neg_add_cancel (above): -a + (a + b) = b
    -- New goal is -a + (a + b) = c
  rw [h]
    -- New goal is -a + (a + c) = c
  exact neg_add_cancel_left a c
    -- neg_add_cancel (above): -a + (a + b) = b, where b = c
  done

theorem mul_zero {a : Int} :
    a * 0 = 0 := by
  have h : a * 0 + a * 0 = a * 0 + 0 := by
    rw [← mul_add]
      -- Distribute multiplcation over addition (reversed)
      -- mul_add: a * (b + c) = a * b + a * c,
      --   where a = a, b = 0, c = 0
      -- New goal is a * (0 + 0) = a * 0 + 0
    rw [add_zero]
      -- add_zero: a + 0 = 0
      -- New goal is a * 0 = a * 0 + 0
    rw [add_zero]
      -- h is proved
  exact add_left_cancel h
    -- add_left_cancel (above): if a + b = a + c then b = c,
    --   where a = a * 0, b = 0, c = 0
  done
