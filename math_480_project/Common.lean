import Mathlib.Topology.Basic
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Finset.Image
open BigOperators
open Finset
open Function

-- Lemma to prove that if all elements in a finite set s are less than n, then the cardinality of s is less than or equal to n
lemma sums_card_bdd  (s : Finset ℕ) (h : ∀ x ∈ s, x < n) : s.card <= n := by
  -- Proving that n equals the cardinality of the range n
  have : n = Finset.card (Finset.range n) := by simp
  -- Rewriting the goal using the above fact
  rw [this]
  -- Applying the cardinality monotonicity lemma
  apply Finset.card_mono
  -- Introducing the assumption that x is in s
  intro x xins
  -- Rewriting the goal using membership in the range
  rw [mem_range]
  -- Applying the hypothesis that x is less than n
  apply h x
  -- Concluding that x is in s
  exact xins

-- Lemma to prove that if the cardinality of a set s is at most 10 and all elements are at most 100, then the sum of elements in s is at most 1000
lemma sums_bdd (s: Finset ℕ) (cards: s.card <=  10) (selem: ∀x ∈ s, x ≤ 100) :  ∑ x in s, x ≤ 1000 := by
  -- Proving that the sum of elements in s is less than or equal to the cardinality of s times 100
  have : ∑ x in s, x ≤ s.card * 100 := by
    apply Finset.sum_le_card_nsmul s (fun x ↦ x) 100 selem
  -- Using linear arithmetic to conclude the result
  linarith

-- Define the range from 1 to 100 as a finite set
def range_1_to_100 := Finset.range 101 \ Finset.range 1

-- Example to prove the existence of two different subsets X and Y of A such that their sums are equal
example: ∀A ⊆ range_1_to_100, card A = 10 → ∃ X⊆ A, ∃Y ⊆ A, X ≠ Y ∧ ∑ x in X, x = ∑ y in Y, y := by
  intros A hA hcardA
  have h : A.card = 10 := hcardA
  -- Create the powerset of A and a set of sums of elements in the powerset
  let powersetA := powerset A
  let sums := powersetA.image (fun s => ∑ x in s, x)
  -- Proving the cardinality of the powerset of A
  have h_powersetA : powersetA.card = 2 ^ A.card := Finset.card_powerset A
  -- Simplifying the cardinality of the powerset of A using the fact that A.card = 10
  have h_card_powersetA : (2 : ℕ) ^ A.card = 1024 := by simp [h]
  -- Proving that the cardinality of the set of all sums is upper bounded by 1001
  have sum_card_bdd : sums.card <= 1001 := by
    apply sums_card_bdd
    intro subsetsum subsetsumh
    simp [sums] at subsetsumh
    rcases subsetsumh with ⟨a, subseta, suma⟩
    rw[← suma]
    -- Applying the sums_bdd lemma to prove that the sum of elements in a is less than or equal to 1000
    have : ∑ x in a, x ≤ 1000 := by
      apply sums_bdd
      rw[← hcardA]
      apply Finset.card_mono
      simp
      exact decidableExistsOfDecidableSubsets.proof_3 a subseta
      intro x hx
      have: x ∈ A := by
        rw[mem_powerset] at subseta
        exact subseta hx
      have: x ∈ range_1_to_100 := by
        exact hA this
      simp[range_1_to_100] at this
      linarith
    linarith
  -- Proving that the cardinality of the set of all sums is less than the cardinality of the powerset of A
  have h_sums : sums.card < powersetA.card := by
    rw [h_powersetA, h_card_powersetA]
    linarith
  -- Proving that every element in the powerset of A maps to an element in the set of sums
  have: ∀a ∈ powersetA, (fun s => ∑ x in s, x) a ∈ sums := by
    simp[sums, powersetA]
    intro a2 a2h
    use a2
  -- Applying the pigeonhole principle to prove the existence of two different subsets X and Y with equal sums
  have:  ∃ x ∈ powersetA, ∃ y ∈ powersetA, x ≠ y ∧ (fun s => ∑ x in s, x) x = (fun s => ∑ x in s, x) y := by
    apply Finset.exists_ne_map_eq_of_card_lt_of_maps_to h_sums this
  simp[powersetA] at this
  exact this
