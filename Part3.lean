/-
  # Introduction to Lean: Formalizing Mathematics with Mathlib
  Summer school "Proof assistants and applications"
  IRMA, Université de Strasbourg, August 31 – September 4, 2026
  Xavier Roblot (Université Claude Bernard Lyon I)

  ## Part 3 — Two more ambitious proofs

  The construction of ℤ from ℕ × ℕ, and the Schröder–Bernstein theorem.

  The keyboard shortcuts, a tour of the Lean syntax and the notes on
  how to work on these files are at the top of `Part1.lean`.

  References:
  * Formalising Mathematics 2024, K. Buzzard
  * Theorem Proving in Lean 4, J. Avigad et al.
  * Mathematics in Lean, J. Avigad & P. Massot
  * M2 Lyon 2024-25, S. Morel, F. A. E. Nuccio, X. Roblot
-/
import Mathlib.Tactic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.Real.Pi.Irrational
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.FLT.Three

noncomputable section

  # Two more ambitious proofs

  ## Construction of ℤ from ℕ × ℕ

  The idea: an integer `a - b` is represented by the pair
  `(a, b) ∈ ℕ × ℕ`. Two pairs `(a, b)` and `(c, d)` represent the
  same integer if `a - b = c - d`, which can be written without
  subtraction as: `a + d = c + b`.

  This defines an equivalence relation on `ℕ × ℕ`, and `ℤ` is its
  quotient.
-/

-- The equivalence relation
def rZ : ℕ × ℕ → ℕ × ℕ → Prop := fun (a, b) (c, d) ↦ a + d = c + b

-- Useful reformulations
theorem rZ_iff (a b c d : ℕ) :
    rZ (a, b) (c, d) ↔ a + d = c + b := Iff.rfl
theorem rZ_iff' (x y : ℕ × ℕ) :
    rZ x y ↔ x.1 + y.2 = y.1 + x.2 := Iff.rfl

/-
  The three proofs below all have the same structure: destruct the
  pairs (`rintro ⟨a, b⟩ ...` or `intro`), unfold `rZ` into an
  arithmetic equality (via `rZ_iff` / `rZ_iff'`), then conclude by
  linear arithmetic with `lia`.
-/

/- TODO -/

-- rZ is reflexive
-- Hint: `rintro ⟨a, b⟩`, then `simp [rZ_iff]`
theorem rZ_reflexive : ∀ x : ℕ × ℕ, rZ x x := by
  sorry

-- rZ is symmetric
-- (x and y are implicit: introduce them with `intro x y h`)
theorem rZ_symmetric : ∀ {x y : ℕ × ℕ}, rZ x y → rZ y x := by
  sorry

-- rZ is transitive
-- Hint: `intro x y z h1 h2`, then `simp only [rZ_iff'] at *`
--   and `lia`
theorem rZ_transitive :
    ∀ {x y z : ℕ × ℕ}, rZ x y → rZ y z → rZ x z := by
  sorry

/- END TODO -/

-- We make it a `Setoid`.
-- A `Setoid α` is the data of a type `α` equipped with an
-- equivalence relation:
--   - a field `r : α → α → Prop` (the relation),
--   - a field `iseqv : Equivalence r` (the proof that it is
--     reflexive, symmetric, transitive).
-- This is exactly what is needed to pass to the quotient: Lean
-- reserves the notation `a ≈ b` (\~~) for the relation of the
-- current `Setoid`, and `Quotient s` for the associated quotient.
instance rZSetoid : Setoid (ℕ × ℕ) where
  r := rZ
  iseqv := ⟨rZ_reflexive, rZ_symmetric, rZ_transitive⟩

@[simp] theorem rZ_equiv_def (a b c d : ℕ) :
    (a, b) ≈ (c, d) ↔ a + d = c + b := Iff.rfl

-- Our version of ℤ: the quotient type
abbrev ZZ := Quotient rZSetoid

namespace ZZ

-- 0 and 1 in ZZ
-- `⟦x⟧` is the notation for the equivalence class of `x` in the
-- quotient (it is `Quotient.mk` applied to `x`). It is typed with
-- `\[[` for `⟦` and `\]]` for `⟧`.
instance : Zero ZZ := ⟨⟦(0, 0)⟧⟩
instance : One  ZZ := ⟨⟦(1, 0)⟧⟩

-- Negation: (a, b) ↦ (b, a) — defined via Quotient.lift
-- `Quotient.lift` lets us define a function OUT OF a quotient:
-- we provide
--   (1) a function on representatives, here `fun (a, b) ↦ ⟦(b, a)⟧`,
--   (2) a proof that it is *compatible* with the relation (two
--       equivalent representatives have the same image).
-- Lean then derives a well-defined `ZZ → ZZ`.
-- (For an equality of classes, use `Quotient.sound` :
--  `x ≈ y → ⟦x⟧ = ⟦y⟧`.)
def neg : ZZ → ZZ :=
  Quotient.lift (fun x : ℕ × ℕ ↦ (⟦(x.2, x.1)⟧ : ZZ)) (by
    intro ⟨a, b⟩ ⟨c, d⟩ h
    apply Quotient.sound
    simp only [rZ_equiv_def] at h ⊢; lia)

instance : Neg ZZ := ⟨neg⟩

@[simp] theorem neg_def (a b : ℕ) :
    -(⟦(a, b)⟧ : ZZ) = ⟦(b, a)⟧ := rfl

-- Addition: (a, b) + (c, d) = (a+c, b+d)
def add_aux (x y : ℕ × ℕ) : ZZ := ⟦(x.1 + y.1, x.2 + y.2)⟧

/-
  To define an operation on a quotient, we first define it on
  representatives (`add_aux`), then prove that it does not depend on
  the choice of representatives (`add_aux_sound`): this is what lets
  `Quotient.lift₂` push it down to the quotient.

  `Quotient.lift₂` is simply the *two*-argument version of
  `Quotient.lift` (used above for negation): here addition takes two
  classes as input, hence the compatibility to check in *both*
  variables (`h₁` and `h₂`).

  To prove an equality *between classes*, we use `Quotient.sound`
  (two equivalent representatives have the same class).
-/

/- TODO -/

-- Show that add_aux is compatible with the relation
-- (needed for Quotient.lift₂)
-- Hint: destruct the four pairs, unfold the hypotheses with
--   `simp only [add_aux, rZ_equiv_def] at *`, then
--   `apply Quotient.sound` and `lia`
theorem add_aux_sound (x₁ y₁ x₂ y₂ : ℕ × ℕ)
    (h₁ : x₁ ≈ x₂) (h₂ : y₁ ≈ y₂) :
    add_aux x₁ y₁ = add_aux x₂ y₂ := by
  sorry

-- Define addition on ZZ via Quotient.lift₂
def add : ZZ → ZZ → ZZ := Quotient.lift₂ add_aux add_aux_sound

instance : Add ZZ := ⟨add⟩

@[simp] theorem add_def (a b c d : ℕ) :
    (⟦(a, b)⟧ + ⟦(c, d)⟧ : ZZ) = ⟦(a + c, b + d)⟧ := rfl

-- Show that addition is commutative
-- `Quotient.inductionOn₂` reduces a goal about two classes to a
-- goal about their representatives:
--   `refine Quotient.inductionOn₂ x y ?_`, then
--   `rintro ⟨a, b⟩ ⟨c, d⟩`.
-- Conclude with `simp only [add_def]`, `apply Quotient.sound`, `lia`.
theorem add_comm' (x y : ZZ) : x + y = y + x := by
  sorry

/- END TODO -/

end ZZ

-- The final result: ZZ is isomorphic to ℤ as rings
-- (full proof in the solutions)
#check Int.cast  -- the canonical morphism ℤ → R

/-
  ## Schröder-Bernstein theorem

  If `f : α → β` and `g : β → α` are both injective,
  then there exists a bijection `h : α → β`.

  https://en.wikipedia.org/wiki/Schröder–Bernstein_theorem

  Source: *Mathematics in Lean*, J. Avigad et al.,
  chapter 4, section 3.
  https://leanprover-community.github.io/mathematics_in_lean/

  **Proof idea.** We partition `α` into two parts: the set `sbSet`
  of elements "coming from the f side" (defined by iterating
  `g ∘ f` starting from the points outside the image of `g`), and
  its complement. We build `sbFun`, which applies `f` on `sbSet`
  and the inverse `g⁻¹` elsewhere. It remains to show that `sbFun`
  is injective and then surjective (hence bijective) — this is the
  purpose of the three lemmas below, assembled at the end.
-/

section SchroederBernstein

open Set Function Classical

variable {α β : Type*} [Nonempty β] (f : α → β) (g : β → α)

-- `sbAux n` is the n-th level of the construction:
--   sbAux 0     = α \ g(β)      (elements not in the image of g)
--   sbAux (n+1) = g(f(sbAux n)) (propagation by g ∘ f)
def sbAux : ℕ → Set α
  | 0     => univ \ g '' univ
  | n + 1 => g '' (f '' sbAux n)

-- `sbSet` = ⋃ sbAux n  (the union of all levels)
-- Intuition: these are the elements of α "coming from the f side"
def sbSet := ⋃ n, sbAux f g n

-- `sbFun` is the bijection we are after:
--   on sbSet, we use f  ("f side")
--   elsewhere, we use g⁻¹ (g injective ⟹ invertible on its image)
def sbFun (x : α) : β :=
  if x ∈ sbSet f g then f x else invFun g x

/- TODO -/

-- If x ∉ sbSet, then x is in the image of g, so invFun g is
-- indeed a right inverse
-- Hint: first show `x ∈ g '' univ` by contraposition
--   (case n=0 of sbAux), then use `invFun_eq`
theorem sb_right_inv {x : α} (hx : x ∉ sbSet f g) :
    g (invFun g x) = x := by
  sorry

-- sbFun is injective if f is
-- Strategy: `set A := sbSet f g`, `set h := sbFun f g`,
--   `by_cases` on `x₁ ∈ A ∨ x₂ ∈ A`, `wlog` to assume x₁ ∈ A,
--   then `push Not` for the case ¬(x₁ ∈ A ∨ x₂ ∈ A)
theorem sb_injective (hf : Injective f) :
    Injective (sbFun f g) := by
  sorry

-- sbFun is surjective if g is
-- Strategy: `by_cases` on `g y ∈ A`, then `leftInverse_invFun`
theorem sb_surjective (hg : Injective g) :
    Surjective (sbFun f g) := by
  sorry

-- Main theorem: assemble the three lemmas above
-- Hint: `Bijective` destructs into `Injective ∧ Surjective`;
--   provide the witness `sbFun f g` then the two lemmas,
--   via `exact ⟨_, _, _⟩`
theorem schroeder_bernstein {f : α → β} {g : β → α}
    (hf : Injective f) (hg : Injective g) :
    ∃ h : α → β, Bijective h := by
  sorry

/- END TODO -/

end SchroederBernstein
