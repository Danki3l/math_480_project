import Mathlib.Topology.Basic
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Finset.Basic
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
def S : Finset ℤ := {-2, -1, 0, 1, 2}
def T: Finset ℤ := {0, 1, 4}

lemma maps_to_g : ∀ x ∈ S, g x ∈ T := by
  intro x hx
  fin_cases x
  simp [g]

example: ¬ Injective g := by
  apply Finset.exists_ne_map_eq_of_card_lt_of_maps_to
  show Finset.card S > Finset.card T
  simp [g, S, T, card]
  exact maps_to_g


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

-- 3: Showing that ∀x ∈ s, f(x) ∈ t
example: ∀ x ∈ s, g (x) ∈ t := by
simp [s, t, g]

-- Minimum working example to figure out what's going on above
example: ({1, 2}: Finset ℤ)  ⊆ {1, 2, 3} := by
simp

-- 4: Showing that the cardinality of t is less than the cardinality of s
example: card t < card s := by
simp [s, t, card, g]

-- decide




theorem my_theorem (A : finset nat) (hA : A ⊆ range 100) (hCard : card A = 10) :
  ∃ (X Y : finset nat), X ≤ A ∧ Y ≤ A ∧ X ≠ Y ∧ ∑ x in X, x = ∑ y in Y, y :=
by
  {
    obtain [f, hf] : finset.exists_ne_map_eq_of_card_lt_of_maps_to (finset.range 100) A 10 $ λ a, a :=
    {
      intro a,
      cases (hA a) with ha nh,
      { contradiction },
      { exact ha },
    },
    {
      refine exists.intro _ _,
      { exact finset.image f A },
      { exact finset.preimage (λ x, x ∈ A) f (finset.range 100) },
      {
        intros x hx,
        cases (hf x) with byA nbyA,
        { exact byA },
        { contradiction }
      },
      {
        rw [finset.sum_image_eq hf],
        exact finset.sum_const _ _ (card A)
      },
      {
        rw [finset.sum_preimage_eq hf],
        rw [finset.card_range],
        exact nat.sum_const _ _ 100
      },
      {
        intro hxy,
        rw [finset.ext'] at hxy,
        cases hxy with hx hy,
        {
          cases (hf hx) with byA nbyA,
          { exact byA },
          { contradiction }
        },
        {
          cases (mem_preimage _ _ f (finset.range 100)) hy with hyA nhyA,
          { exact nhyA },
          { contradiction }
        }
      }
    }
  }
