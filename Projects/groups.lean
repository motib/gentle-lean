import Mathlib.Tactic
import Mathlib.Data.Rat.NNRat

namespace gentle

-- Define the class of an additive group
-- Extend the classes to obtain +, 0, -
class AddGroup (α : Type*) extends Add α, Zero α, Neg α where
  add_assoc : ∀ x y z : α, x + y + z = x + (y + z)
  add_zero : ∀ x : α, x + 0 = x
  zero_add : ∀ x : α, 0 + x = x
  add_left_neg : ∀ x : α, -x + x = 0

#check AddGroup

-- Open namespace so that AddGroup need not be added
--   to each theorem
namespace AddGroup

-- AddGroup maps a type α to a group of elements of type α
-- Declare a _type_ G that is a group of elements of type α
variable {G : Type*} [AddGroup G]

-----------------------------------------------------------

theorem add_right_neg (a : G) : a + (-a) = 0 := by
    -- Theorem is not a - a = 0 since subtraction has
    --   not yet been defined
  have h : -(a + (-a)) + (a + (-a) + (a + (-a))) = 0 := by
    rw [add_assoc]
    rw [← add_assoc (-a) a]
      -- After rewriting associativity new goal is
      --   -(a + -a) + (a + (-a + a -a)) = 0
      -- Now add_left_neg axiom can be used
    rw [add_left_neg]
    rw [zero_add]
    rw [add_left_neg]
  rw [← h]
    -- After using hypothesis to rewrite 0 new goal is
    --   a + -a = -(a + -a) + (a + (-a + a -a))
  rw [← add_assoc]
  rw [add_left_neg]
  rw [zero_add]
  done

-----------------------------------------------------------

theorem add_neg_cancel_right (a b : G) : a + b + -b = a := by
  rw [add_assoc, add_right_neg, add_zero]

theorem neg_add_cancel_left (a b : G) : -a + (a + b) = b := by
  rw [← add_assoc, add_left_neg, zero_add]

theorem add_left_cancel {a b c : G} (h : a + b = a + c) : b = c := by
  rw [← neg_add_cancel_left a b, h, neg_add_cancel_left]

theorem add_right_cancel {a b c : G} (h : a + b = c + b) : a = c := by
  rw [← add_neg_cancel_right a b, h, add_neg_cancel_right]

-----------------------------------------------------------

theorem my_add_right_neg (a : ℤ) : a + (-a) = 0 := by
  have h : -(a + (-a)) + (a + (-a) + (a + (-a))) = 0 := by
    rw [Int.add_assoc, ← Int.add_assoc (-a) a,
        Int.add_left_neg, Int.zero_add, Int.add_left_neg]
  rw [← h, ← Int.add_assoc, Int.add_left_neg, Int.zero_add]
  done

-----------------------------------------------------------

class Group (α : Type*) extends Mul α, One α, Inv α where
  mul_assoc : ∀ x y z : α, x * y * z = x * (y * z)
  mul_one : ∀ x : α, x * 1 = x
  one_mul : ∀ x : α, 1 * x = x
  mul_left_inv : ∀ x : α, x⁻¹ * x = 1

namespace Group
variable {G : Type*} [Group G]

theorem mul_right_inv (a : G) : a * a⁻¹ = 1 := by
  have h : (a * a⁻¹)⁻¹ * (a * a⁻¹ * (a * a⁻¹)) = 1 := by
    rw [mul_assoc, ← mul_assoc a⁻¹ a, mul_left_inv, one_mul, mul_left_inv]
  rw [← h, ← mul_assoc, mul_left_inv, one_mul]
