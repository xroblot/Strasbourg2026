/-
  # Introduction to Lean: Formalizing Mathematics with Mathlib
  Summer school "Proof assistants and applications"
  IRMA, Université de Strasbourg, August 31 – September 4, 2026
  Xavier Roblot (Université Claude Bernard Lyon I)

  ## Part 3 — Two more ambitious proofs — SOLUTIONS

  (This file mirrors `Part3.lean`: one solution per `sorry`
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

/- # Two more ambitious proofs -/

/- ## Construction of ℤ from ℕ × ℕ -/

def rZ : ℕ × ℕ → ℕ × ℕ → Prop := fun (a, b) (c, d) ↦ a + d = c + b

theorem rZ_iff (a b c d : ℕ) :
    rZ (a, b) (c, d) ↔ a + d = c + b := Iff.rfl
theorem rZ_iff' (x y : ℕ × ℕ) :
    rZ x y ↔ x.1 + y.2 = y.1 + x.2 := Iff.rfl

theorem rZ_reflexive : ∀ x : ℕ × ℕ, rZ x x := by
  rintro ⟨a, b⟩
  simp [rZ_iff]

theorem rZ_symmetric : ∀ {x y : ℕ × ℕ}, rZ x y → rZ y x := by
  intro x y h
  simp only [rZ_iff'] at *
  lia

theorem rZ_transitive :
    ∀ {x y z : ℕ × ℕ}, rZ x y → rZ y z → rZ x z := by
  intro x y z h1 h2
  simp only [rZ_iff'] at *
  lia

instance rZSetoid : Setoid (ℕ × ℕ) where
  r := rZ
  iseqv := ⟨rZ_reflexive, rZ_symmetric, rZ_transitive⟩

@[simp] theorem rZ_equiv_def (a b c d : ℕ) :
    (a, b) ≈ (c, d) ↔ a + d = c + b := Iff.rfl

abbrev ZZ := Quotient rZSetoid

namespace ZZ

instance : Zero ZZ := ⟨⟦(0, 0)⟧⟩
instance : One  ZZ := ⟨⟦(1, 0)⟧⟩

def neg : ZZ → ZZ :=
  Quotient.lift (fun x : ℕ × ℕ ↦ (⟦(x.2, x.1)⟧ : ZZ)) (by
    intro ⟨a, b⟩ ⟨c, d⟩ h
    apply Quotient.sound
    simp only [rZ_equiv_def] at h ⊢; lia)

instance : Neg ZZ := ⟨neg⟩

@[simp] theorem neg_def (a b : ℕ) :
    -(⟦(a, b)⟧ : ZZ) = ⟦(b, a)⟧ := rfl

def add_aux (x y : ℕ × ℕ) : ZZ := ⟦(x.1 + y.1, x.2 + y.2)⟧

theorem add_aux_sound (x₁ y₁ x₂ y₂ : ℕ × ℕ)
    (h₁ : x₁ ≈ x₂) (h₂ : y₁ ≈ y₂) :
    add_aux x₁ y₁ = add_aux x₂ y₂ := by
  obtain ⟨a, b⟩ := x₁; obtain ⟨c, d⟩ := y₁
  obtain ⟨e, f⟩ := x₂; obtain ⟨g, h⟩ := y₂
  simp only [add_aux, rZ_equiv_def] at *
  apply Quotient.sound
  simp only [rZ_equiv_def]; lia

def add : ZZ → ZZ → ZZ := Quotient.lift₂ add_aux add_aux_sound

instance : Add ZZ := ⟨add⟩

@[simp] theorem add_def (a b c d : ℕ) :
    (⟦(a, b)⟧ + ⟦(c, d)⟧ : ZZ) = ⟦(a + c, b + d)⟧ := rfl

theorem add_comm' (x y : ZZ) : x + y = y + x := by
  refine Quotient.inductionOn₂ x y ?_
  rintro ⟨a, b⟩ ⟨c, d⟩
  simp only [add_def]
  apply Quotient.sound
  simp only [rZ_equiv_def]; lia

end ZZ

#check Int.cast

/- ## Schröder-Bernstein theorem -/

section SchroederBernstein

open Set Function Classical

variable {α β : Type*} [Nonempty β] (f : α → β) (g : β → α)

private def sbAux : ℕ → Set α
  | 0     => univ \ g '' univ
  | n + 1 => g '' (f '' sbAux n)

private def sbSet := ⋃ n, sbAux f g n

private def sbFun (x : α) : β :=
  if x ∈ sbSet f g then f x else invFun g x

private theorem sb_right_inv {x : α} (hx : x ∉ sbSet f g) :
    g (invFun g x) = x := by
  have h1 : x ∈ g '' univ := by
    contrapose! hx
    rw [sbSet, mem_iUnion]; use 0
    rw [sbAux, mem_diff]; exact ⟨mem_univ _, hx⟩
  have h2 : ∃ y, g y = x := by simp at h1; exact h1
  exact invFun_eq h2

private theorem sb_injective (hf : Injective f) :
    Injective (sbFun f g) := by
  set A := sbSet f g with A_def
  set h := sbFun f g with h_def
  intro x₁ x₂ (hxeq : h x₁ = h x₂)
  simp only [h_def, sbFun, ← A_def] at hxeq
  by_cases xA : x₁ ∈ A ∨ x₂ ∈ A
  · wlog x₁A : x₁ ∈ A generalizing x₁ x₂ hxeq xA
    · symm
      apply this (Eq.symm hxeq) (Or.symm xA) (Or.resolve_left xA x₁A)
    have x₂A : x₂ ∈ A := by
      apply Iff.mp _root_.not_imp_self
      intro (x₂nA : x₂ ∉ A)
      rw [if_pos x₁A, if_neg x₂nA] at hxeq
      rw [A_def, sbSet, mem_iUnion] at x₁A
      have x₂eq : x₂ = g (f x₁) := by rw [hxeq, sb_right_inv f g x₂nA]
      rcases x₁A with ⟨n, hn⟩
      rw [A_def, sbSet, mem_iUnion]; use n + 1
      simp [sbAux]; exact ⟨x₁, hn, Eq.symm x₂eq⟩
    rw [if_pos x₁A, if_pos x₂A] at hxeq; exact hf hxeq
  push Not at xA
  rw [if_neg (And.left xA), if_neg (And.right xA)] at hxeq
  rw [← sb_right_inv f g (And.left xA), hxeq,
    sb_right_inv f g (And.right xA)]

private theorem sb_surjective (hg : Injective g) :
    Surjective (sbFun f g) := by
  set A := sbSet f g with A_def
  set h := sbFun f g with h_def
  intro y
  by_cases gyA : g y ∈ A
  · rw [A_def, sbSet, mem_iUnion] at gyA
    rcases gyA with ⟨n, hn⟩
    rcases n with _ | n
    · simp [sbAux] at hn
    simp [sbAux] at hn
    rcases hn with ⟨x, xmem, hx⟩
    use x
    have : x ∈ A := by rw [A_def, sbSet, mem_iUnion]; exact ⟨n, xmem⟩
    rw [h_def, sbFun, if_pos this]; exact hg hx
  use g y
  rw [h_def, sbFun, if_neg gyA]
  apply leftInverse_invFun hg

theorem schroeder_bernstein {f : α → β} {g : β → α}
    (hf : Injective f) (hg : Injective g) :
    ∃ h : α → β, Bijective h :=
  ⟨sbFun f g, sb_injective f g hf, sb_surjective f g hg⟩

end SchroederBernstein
