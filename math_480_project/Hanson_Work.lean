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

-- Adjust the range here to go from 1 to 100
def range_1_to_100 := Finset.range 101 \ Finset.range 1
example: ∀A ⊆ range_1_to_100, card A = 10 → ∃ X,Y ⊆ A ∧ X ≠ Y ∧ ∑ x in X, x = ∑ y in Y, y := by sorry
#eval range_1_to_100
#check range_1_to_100
#check {range_1_to_100}
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
def f (x : ℤ) : ℤ := x^2
#check g (-1)
#eval g (-2)

-- 2:
def s : Finset ℤ  := {1, -2, 2}
def t: Finset ℤ := {1, 4}

-- 3:
example: ∀x ∈ s, f x ∈ t := by
  intro x
  intro hx
  cases hx;
  simp [f];
  apply Finset.mem_insert_of_mem;
  apply Finset.mem_singleton_self

-- 4:
def B : Finset ℕ := {1,2,3,4}
def A : Finset ℕ := {1,2,3}

example: card A < card B := by
  apply Finset.card_lt_card
  split
  { show A ⊆ B, from by
    intros a ha
    simp at ha
    cases ha; simp [ha]; apply Finset.mem_insert_of_mem; apply Finset.mem_insert_of_mem; apply Finset.mem_insert_of_mem; apply Finset.mem_singleton_self }
  { show ∃x ∈ B, x ∉ A, by
    use 4
    split
    { apply Finset.mem_insert_self }
    { intro contra
      have h : 4 ∈ {1, 2, 3} := by assumption
      simp at h }
  }
