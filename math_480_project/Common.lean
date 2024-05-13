import Mathlib.Topology.Basic
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Finset.Image
open BigOperators
open Finset
open Function

def range_1_to_100 := Finset.range 101 \ Finset.range 1

example (s : Finset ℕ) (h : ∀ x ∈ s, x < 100) : s.card < 101 := by
  have h' : ∀ x ∈ s, x < 101 := by
    intro x hx
    exact Nat.lt_of_lt_of_le (h x hx) (Nat.lt_succ_self 100)
  exact card_lt_of_bdd s 101 h'

example : ∀ A ⊆ range_1_to_100, A.card = 10 → ∃ X, Y ⊆ A ∧ X ≠ Y ∧ ∑ x in X, x = ∑ y in Y, y := by
  intros A hA hcardA
  have h : A.card = 10 := hcardA
  let powersetA := powerset A
  let sums := powersetA.image (fun s => ∑ x in s, x)
  have h_powersetA : powersetA.card = 2 ^ A.card := Finset.card_powerset A
  have h_card_powersetA : (2 : ℕ) ^ A.card = 1024 := by simp [h]
  have ineq : 10 * 100 < 1024 := by norm_num
  have h_sums : sums.card < powersetA.card := by
    rw [h_powersetA]
    -- rw [card_lt_of_]
    -- need a lemma that says that if s is a subset of ℕ, and ∀x ∈ s, x < n, then s.card < n+1
    -- probbly called card_lt_of_bdd
    exact Nat.lt_of_le_of_lt (Finset.card_image_le sums) ineq
  obtain ⟨X, hX, Y, hY, hXY, hsum⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to h_sums (λ s hs => Finset.mem_powerset.mp hs)
  use X, Y
  split
  · exact Finset.mem_powerset.mp hX
  split
  · exact Finset.mem_powerset.mp hY
  split
  · exact hXY
  exact hsum



example : ∀ A ⊆ range_1_to_100, A.card = 10 → ∃ X, Y ⊆ A ∧ X ≠ Y ∧ ∑ x in X, x = ∑ y in Y, y := by
intro A subsetA cardA
apply Finset.exists_ne_map_eq_of_card_lt_of_maps_to
