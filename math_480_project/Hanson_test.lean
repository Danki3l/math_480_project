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
-- Adjust the range here to go from 1 to 100
def range_1_to_100 := Finset.range 101 \ Finset.range 1
example: ∀A ⊆ range_1_to_100, card A = 10 → ∃ X,Y ⊆ A ∧ X ≠ Y ∧ ∑ x in X, x = ∑ y in Y, y := by sorry

-- 1. Understanding how to make a function that maps a finite set of size 10 and is a subset of A to its sum
def sum_of_subset (A : Finset ℕ) (B : Finset ℕ) (h : B ⊆ A) : ℕ :=
  ∑ x in B, x
-- 2. Understanding how to show that one finite set is a subset of another i.e. X ⊆ A, Y ⊆ A
example (X Y A : Finset ℕ) (hX : X ⊆ A) (hY : Y ⊆ A) : true := by
  trivial
-- 3. Understanding how to argue that the "sum" of the finite sets is lower and upper bounded i.e. it can't be less than 0 and more than 1000
example (A : Finset ℕ) (B : Finset ℕ) (h : B ⊆ A) : 0 ≤ sum_of_subset A B h ∧ sum_of_subset A B h ≤ 1000 := by
  split
  apply Finset.sum_nonneg
  apply Finset.sum_le_card_mul_max
-- 4. Understanding how to apply number of subsets theorem
example (A : Finset ℕ) : A.powerset.card = 2^(A.card) := by
  exact Finset.card_powerset A
-- 5. Understanding how to argue that the cardinality of t is less than or equal to 1001
set_option maxRecDepth 10000
example (A : Finset ℕ) (h : A ⊆ Finset.range 1001) : A.card ≤ 1001 :=
  Finset.card_le_card h
-- 6. How to make t' of type finset
variable (A : Finset ℕ)
def t' := {σ | ∃ B ⊆ A, ∑ x in B, x = σ}
#check t'
-- 7. Find alternative version of pigeonhole principle that doesn't require both s and t to be finite sets

variable {α : Type*}
variable (s : set α)
variable [finite s]
variable [decidable_eq α]
variable [finite s]

def set_to_finset {α : Type*} [decidable_eq α] (s : set α) [finite s] : finset α :=
⟨s.to_list, s.to_list_nodup⟩

example : theorem_about_finset (set_to_finset s) :=


-- 8. Understanding how to apply pigeonhole principle to show that there exists X, Y ⊆ A such that X ≠ Y and ∑ x in X, x = ∑ y in Y, y
