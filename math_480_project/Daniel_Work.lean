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
#eval {0,1}
#eval 0

-- Smaller Example to work through for practice on syntax and how to apply pigeonhole principle
-- Task: Formalize that f(x)=x^2 is not injective using the pigeonhole principle
example: (α: Type ℤ) (β: Type ℤ) (f: α → β) fun x ↦ x^2 : ¬ Injective fun x ↦ x^2 := by sorry
