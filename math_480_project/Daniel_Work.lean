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


-- Components to Understand for smaller g(x) = x^2 example
-- 1. Understanding how to make a function from integers to integers, specifically f(x) = x^2
-- 2. Undestanding how to make finite sets s = {1, -2, 2} and t = {1, 4}
-- 3. How to show that ∀x ∈ s, f(x) ∈ t
-- 4. How to show that the cardinality of t is less than the cardinality of s

-- 1:
variable (f : ℤ → ℤ)
#check g (-1)
#eval g (-2)

#check Finset.mk
-- 2:
def s : Finset ℤ  := {1, -2, 2}
def t: Finset ℤ := {1, 4}

-- 3: Showing that ∀x ∈ s, f(x) ∈ t
example: ∀ x ∈ s, g (x) ∈ t := by
simp [s, t, g]

-- Minimum working example to figure out what's going on above
example: ({1, 2}: Finset ℤ)  ⊆ {1, 2, 3} := by
simp

-- 4: Showing that the cardinality of t is less than the cardinality of s
lemma t_lt_s: t.card < s.card := by
decide

-- #check Finset.exists_ne_map_eq_of_card_lt_of_maps_to

--Proving that g(x) = x^2 is not injective using the pigeonhole principle:
example: ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ g x = g y := by
apply Finset.exists_ne_map_eq_of_card_lt_of_maps_to t_lt_s
simp [s, t, g]

-- Components to understand for Prop 3.19
-- 1. Understanding how to make a function that maps a finite set of size 10 and is a subset of A to its sum
-- 2. Understanding how to show that one finite set is a subset of another i.e. X ⊆ A, Y ⊆ A
-- 3. Understanding how to argue that the "sum" of the finite sets is lower and upper bounded i.e. it can't be less than 0 and more than 1000
-- 4. Understanding how to apply number of subsets theorem
-- 5. Understanding how to argue that the cardinality of t is less than or equal to 1001
-- 6. How to make t of type finset
-- 7. Find alternative version of pigeonhole principle that doesn't require both s and t to be finite sets

-- variable (A : Finset ℕ)
-- def t' := {σ | ∃ B ⊆ A, ∑ x in B, x = σ}
-- variable (h : Set.card t' < 10)

-- Useful Lemma
lemma sums_card_bdd  (s : Finset ℕ) (h : ∀ x ∈ s, x < n) : s.card <= n := by
  have : n = Finset.card (Finset.range n) := by simp
  rw [this]
  apply Finset.card_mono
  intro x xins
  rw [mem_range]
  apply h x
  exact xins

lemma sums_bdd (s: Finset ℕ) (cards: s.card ≤  10) (selem: ∀x ∈ s, x ≤ 100) :  ∑ x in s, x ≤ 1000 := by
  have : ∑ x in s, x ≤ s.card * 100 := by
    apply Finset.sum_le_card_nsmul s (fun x ↦ x) 100 selem
  linarith


-- Updated Prop 3.19 with correct range
def range_1_to_100 := Finset.range 101 \ Finset.range 1
example: ∀A ⊆ range_1_to_100, card A = 10 → ∃ X,Y ⊆ A ∧ X ≠ Y ∧ ∑ x in X, x = ∑ y in Y, y := by
  intros A hA hcardA
  have h : A.card = 10 := hcardA
  -- Creating summing function that takes in a subset of A and sums its elements
  let powersetA := powerset A
  let sums := powersetA.image (fun s => ∑ x in s, x)
  have h_powersetA : powersetA.card = 2 ^ A.card := Finset.card_powerset A
  have h_card_powersetA : (2 : ℕ) ^ A.card = 1024 := by simp [h]
  have ineq : 10 * 100 < 1024 := by norm_num
  -- Showing that the cardinality of the set of all the sums is less than the cardinality of the power set of A
  have h_sums : sums.card < powersetA.card := by sorry
  -- rw [h_powersetA, h_card_powersetA]
  -- Showing that the cardinality of the set of all the sums is upper bounded
  have sum_card_bdd : sums.card <= 1001 := by
      apply sums_card_bdd
      intro subsetsum subsetsumh
      simp [sums] at subsetsumh
      rcases subsetsumh with ⟨a, subseta, suma⟩
      rw[← suma]
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
        have: x ∈ range_1_to_100 := by sorry
        rw[mem_range] at this

      linarith








-- Smaller Example
example: ∃ X ∈ Finset.range 100, ∃ Y ∈ Finset.range 100, X ≠ Y ∧ X/2 = Y/2 := by
apply Finset.exists_ne_map_eq_of_card_lt_of_maps_to (t := Finset.range 50)
. decide
intro c ch
rw[mem_range]
rw[mem_range] at ch
rw[Nat.div_lt_iff_lt_mul]
exact ch
norm_num

def a : Finset ℤ := {1,2,3}
example (h: t ⊆ a): ∀x ∈ t, x ≤ 3 := by sorry
