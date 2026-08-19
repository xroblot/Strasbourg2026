/-
  # Introduction to Lean: Formalizing Mathematics with Mathlib
  Summer school "Proof assistants and applications"
  IRMA, Université de Strasbourg, August 31 – September 4, 2026
  Xavier Roblot (Université Claude Bernard Lyon I)

  ## Part 1 — Logic and the basics — SOLUTIONS

  (This file mirrors `Part1.lean`: one solution per `sorry`
   exercise, in the same order and the same sections.)
-/
import Mathlib.Tactic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.Real.Pi.Irrational
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.FLT.Three

noncomputable section

variable (P Q R : Prop)

/- ## Implication -/

example : P → Q → P := by
  intro hP _
  exact hP

-- Modus ponens
example : P → (P → Q) → Q := by
  intro hP h
  exact h hP

example : (P → Q) → (Q → R) → P → R := by
  intro h1 h2 hP
  exact h2 (h1 hP)

/- ## Negation, True, False -/

example : P → ¬¬P := by
  intro hP h
  exact h hP

example : (P → Q) → ¬Q → ¬P := by
  intro h hnQ hP
  exact hnQ (h hP)

-- The converse of the contrapositive (classical: use `by_contra`)
example : (¬Q → ¬P) → P → Q := by
  intro h hP
  by_contra hQ
  exact h hQ hP

/- ## Conjunction and disjunction -/

example : (P → Q → R) → P ∧ Q → R := by
  intro h ⟨hP, hQ⟩
  exact h hP hQ

example : P ∨ Q ↔ Q ∨ P := by
  constructor
  · rintro (hP | hQ)
    · right; exact hP
    · left; exact hQ
  · rintro (hQ | hP)
    · right; exact hQ
    · left; exact hP

example : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
  constructor
  · intro h
    exact ⟨fun hP ↦ h (Or.inl hP), fun hQ ↦ h (Or.inr hQ)⟩
  · intro ⟨hnP, hnQ⟩ hPQ
    rcases hPQ with hP | hQ
    · exact hnP hP
    · exact hnQ hQ

-- The other De Morgan law
-- (the → direction requires excluded middle: try `by_cases`)
example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
  constructor
  · intro h
    by_cases hP : P
    · right; intro hQ; exact h ⟨hP, hQ⟩
    · left; exact hP
  · rintro (hnP | hnQ) ⟨hP, hQ⟩
    · exact hnP hP
    · exact hnQ hQ

/- ## Equivalence -/

-- Transitivity of ↔
example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  intro h1 h2
  exact Iff.trans h1 h2

example : ¬(P ↔ ¬P) := by
  intro h
  have hnP : ¬P := fun hP ↦ Iff.mp h hP hP
  exact hnP (Iff.mpr h hnP)

/- # Quantifiers -/

variable (α : Type*) (f g : α → Prop)

example : (∀ x, f x ∧ g x) → ∀ x, f x := by
  intro h x
  exact And.left (h x)

example : (∀ x, f x ∧ g x) ↔ (∀ x, f x) ∧ (∀ x, g x) := by
  constructor
  · intro h; exact ⟨fun x ↦ And.left (h x), fun x ↦ And.right (h x)⟩
  · intro ⟨h1, h2⟩ x; exact ⟨h1 x, h2 x⟩

example : (∃ x, f x ∨ g x) ↔ (∃ x, f x) ∨ (∃ x, g x) := by
  constructor
  · rintro ⟨x, hx | hx⟩
    · exact Or.inl ⟨x, hx⟩
    · exact Or.inr ⟨x, hx⟩
  · rintro (⟨x, hx⟩ | ⟨x, hx⟩)
    · exact ⟨x, Or.inl hx⟩
    · exact ⟨x, Or.inr hx⟩

example (h : ¬ ∀ x, f x) : ∃ x, ¬ f x := by
  by_contra h'
  push Not at h'
  exact h h'

/- # Sets and functions -/

example (s t : Set α) : s ⊆ s ∪ t := by
  intro x hx
  exact Or.inl hx

example (s t : Set α) : s ∩ t = t ∩ s := by
  ext x
  constructor
  · rintro ⟨hs, ht⟩; exact ⟨ht, hs⟩
  · rintro ⟨ht, hs⟩; exact ⟨hs, ht⟩

example {β : Type*} (f : α → β) (s t : Set β) :
    f ⁻¹' (s ∩ t) = f ⁻¹' s ∩ f ⁻¹' t := by
  ext x; simp

example {β : Type*} {f : α → β} (hf : Function.Injective f)
    (s t : Set α) : f '' (s ∩ t) = f '' s ∩ f '' t := by
  ext y
  constructor
  · rintro ⟨x, ⟨hxs, hxt⟩, rfl⟩
    exact ⟨⟨x, hxs, rfl⟩, ⟨x, hxt, rfl⟩⟩
  · rintro ⟨⟨x, hxs, rfl⟩, ⟨x', hxt, hxx'⟩⟩
    have : x = x' := hf (Eq.symm hxx')
    subst this
    exact ⟨x, ⟨hxs, hxt⟩, rfl⟩

/- # Types, coercions and subtypes -/

-- Casts commute with multiplication
example (n m : ℕ) : ((n * m : ℕ) : ℝ) = (n : ℝ) * (m : ℝ) := by
  push_cast
  ring

-- With a hypothesis, subtraction survives the cast
-- (`Nat.cast_sub h` also does it in one rewrite)
example (n : ℕ) (h : 5 ≤ n) : ((n - 5 : ℕ) : ℤ) = (n : ℤ) - 5 := by
  lia

-- Two positive naturals with the same value are equal
example (x y : { n : ℕ // 0 < n }) (h : (x : ℕ) = (y : ℕ)) : x = y :=
  Subtype.ext h

-- A function cannot distinguish two proofs of the same proposition:
-- by proof irrelevance the two arguments are definitionally equal
example (p : Prop) (f : p → ℕ) (h₁ h₂ : p) : f h₁ = f h₂ := rfl
