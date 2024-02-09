import Mathlib.Tactic
import Mathlib.Data.Real.NNReal

-- Axiomatization of geometry according to
-- David M. Clark and Samrat Pathania
-- A Full Axiomatic Development of High School Geometry
-- Springer, 2023
-- https://link.springer.com/book/10.1007/978-3-031-23525-2

namespace gentle

-- Point in Cartesian plane
structure Point where
  x : ℝ
  y : ℝ

-- The cartesian plane is a set of points and a distance function
-- Axioms:
--   the distance function is zero from A to A and
--   the distance function is symmetrical between A and B
structure Cartesian_Plane where
  P : Set Point
  d : Point → Point → NNReal
  zero : ∀ A : Point, d A A = 0
  symm : ∀ A B : Point, d A B = d B A

namespace Cartesian_Plane

-- Declare a cartesian plane
variable (Plane : Cartesian_Plane)

-- Define: B is between A and C
def btw (A B C : Point) :=
  Plane.d A C = Plane.d A B + Plane.d B C

-- Define: the line ↔AB consists of A, B and all points between
--         or further from A than B or further from B than A
def line (A B : Point) :=
  {A, B} ∪ {D : Point | Plane.btw A D B ∨ Plane.btw A B D ∨ Plane.btw D A B}

-- Define: A B C are collinear if they are on the same line
def col (A B C : Point) : Prop :=
  C ∈ Plane.line A B

-- If B is between A and C then A B C are collinear
--   Introduce the hypothesis and use definitions of col and line
--   Extract disjunction that is the same as the hypothesis
lemma L_1_col (A B C : Point) :
    Plane.btw A B C → Plane.col A B C := by
  intro h
  rw [col, line]
  right ; right ; left
  exact h
  done

-- If B is between A and C then it is between C and A
--   Introduce hypothesis and use definition of btw
--   Use symmetry of d and commutativity of addition
--   Restore btw and the goal is the hypothesis
lemma L_1_btw (A B C : Point) :
    Plane.btw A B C → Plane.btw C B A := by
  intro h
  rw [btw]
  rw [Plane.symm B A, Plane.symm C B, Plane.symm C A, add_comm]
  rw [← btw]
  exact h
  done

-- Additional definitions and axioms

-- Define: the segment AB consists of A, B and all points between
def seg (A B : Point) :=
  {A, B} ∪ {D : Point | Plane.btw A D B}

-- Define: the ray →AB consists of A, B and all points between
--         or further from A than B
def ray (A B : Point) :=
  {A, B} ∪ {D : Point | Plane.btw A D B ∨ Plane.btw A B D}

-- Axiom: any two points are contained in exactly one line
def  pa2 (A B : Point) : Prop :=
    ∀ C₁ C₂ C₃ C₄ : Point,
    {A, B} ⊆ Plane.line C₁ C₂ ∧ {A, B} ⊆ Plane.line C₃ C₄ →
    {C₃, C₄} ⊆ Plane.line C₁ C₂

-- Axiom: there are at least three non-collinear lines
def pa3 := ∃ A B C, ¬ Plane.col A B C

-- Axiom: given three collinear points exactly one is between the other two
def unq (A B C : Point) : Prop :=
  Plane.col A B C →
    (Plane.btw A B C ∧ ¬ Plane.btw B A C ∧ ¬ Plane.btw A C B) ∨
    (Plane.btw A C B ∧ ¬ Plane.btw B A C ∧ ¬ Plane.btw A B C) ∨
    (Plane.btw B A C ∧ ¬ Plane.btw A B C ∧ ¬ Plane.btw A C B)

-- Axiom: if B, D are two points, there are points to the left of A,
--   between B and D and to the right of D
--   Therefore, there are an infinite number of points
def inf (B D : Point) : Prop :=
  B ≠ D →
    (∃ A C E : Point,
      Plane.btw A B C ∧ Plane.btw B C D ∧ Plane.btw C D E)
