import Mathlib.Topology.Basic
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Nat.GCD.Basic
open BigOperators
open Finset
open Function

example: {n : ℤ | 12∣ n} ⊆ {n : ℤ | 3∣n} := by
  intro x
  intro h
  simp
  simp at h
  rcases h with ⟨k, hk⟩
  use 4*k
  linarith

def B : Finset ℕ := {1,2,3,4}
def PB := B.powerset
#eval PB
#check (Finset.range 10)
#eval Finset.range 10
#eval B

example: ∀A ⊆ (Finset.range 101), card A = 10 → ∃ X,Y ⊆ A ∧ X ≠ Y ∧ ∑ x in X, x = ∑ y in Y, y := by sorry
#eval Finset.range 101
#check Finset.range 101
#check {Finset.range 101}
#check {0}
#check 0
-- #eval {0,1}
#eval 0

-- Smaller Example to work through for practice on syntax and how to apply pigeonhole principle
-- Task: Formalize that f(x)=x^2 is not injective using the pigeonhole principle

-- Straight-forward proof using the fact that g(-1) = g(1) but 1 ≠ -1
def g (x : ℤ) := x^2
example: ¬ Injective g := by
intro h
rw[Injective] at h
specialize @h 1 (-1)
simp [g] at h
-- rw[g, g] at h

--Prove the same result using the pigeonhole principle:
example: ¬ Injective g := by sorry


-- Components to Understand
-- 1. Understanding how to make a function from integers to integers, specifically f(x) = x^2
-- 2. Undestanding how to make finite sets s = {1, -2, 2} and t = {1, 4}
-- 3. How to show that ∀x ∈ s, f(x) ∈ t
-- 4. How to show that the cardinality of s is less than the cardinality of t

-- 1:
variable (f : ℤ → ℤ)
#check g (-1)
#eval g (-2)

-- 2:
def s : Finset ℤ  := {1, -2, 2}
def t: Finset ℤ := {1, 4}
