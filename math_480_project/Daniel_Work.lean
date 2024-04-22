import Mathlib.Topology.Basic
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Nat.GCD.Basic
open BigOperators
open Finset


example: {n : ℤ | 12∣ n} ⊆ {n : ℤ | 3∣n} := by
  intro x
  intro h
  simp
  simp at h
  rcases h with ⟨k, hk⟩
  use 4*k
  linarith

def A : Finset ℕ := {1,2,3,4}
def PA := A.powerset
#eval PA
#check (Finset.range 10)
#eval Finset.range 10

example: ∀A ⊆ {1, 2, 3, 4, 5}, card A = 10 → ∃ X,Y ⊆ A ∧ X ≠ Y ∧ ∑ x in X, x = ∑ y in Y, y := by sorry
