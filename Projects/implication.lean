import Mathlib.Tactic
namespace gentle
/-
  Implication
-/
theorem T1a {A : Prop} : (¬A → A) → A := by
  intro h1
  by_contra h2
    -- Prove A by contradction: assume A and prove False
  apply h2
    -- Modus ponens
  apply h1
    -- Replace goal by the hypothesis
  exact h2
  done

-- Another proof of the same theorem
theorem T1b {A : Prop} : (¬A → A) → A := by
  intro h1
  contrapose! h1
    -- Replace h1 by its contrapositive
    -- Push negation inward (!)
  constructor
    -- Split conjunction
  · exact h1
  · exact h1
  done

theorem T2 {A B : Prop} : ((A → B) → A) → A := by
  intro h1
  contrapose! h1
    -- Replace h1 by its contrapositive
    --   and push negation inward
  constructor
    -- Split conjunction
  · contrapose! h1
      -- Goal is A → B, h1 is ¬A
      -- Make ¬(A → B) the hypothesis and A the goal
      -- Push negation inward (!)
    rcases h1 with ⟨h2, _⟩
      -- Split the hypothesis
    · exact h2
      -- Only need to use left subformula
      --   of the conjunction
  · exact h1
  done

theorem T3 {A B C : Prop} : (A → B) ∨ (B → C) := by
  have h1 : ¬(A → B) → (B → C) := by
    -- Prove the implication equivalent to the disjunction
    intro h2
    intro h3
    contrapose! h2
      -- Contrapositive of ¬(A → B)
    intro
      -- No need to name the new hypothesis
    exact h3
  contrapose! h1
  exact h1
  done
