/-
  # Introduction to Lean: Formalizing Mathematics with Mathlib
  Summer school "Proof assistants and applications"
  IRMA, Université de Strasbourg, August 31 – September 4, 2026
  Xavier Roblot (Université Claude Bernard Lyon I)

  ## Part 1 — Logic and the basics

  Propositions and proofs, quantifiers, sets and functions.

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

/-
  # First steps

  Lean is a proof assistant: it checks that your proofs are correct.
-/

-- `#check` displays the type of an expression
-- (Lean checks types in real time)
#check Nat.add_comm   -- ∀ (n m : ℕ), n + m = m + n

-- `#eval` evaluates an expression
#eval 2 ^ 10          -- 1024

/-
  ## Keyboard shortcuts

  | Shortcut      | Symbol  | Shortcut      | Symbol  |
  |---------------|---------|---------------|---------|
  | `\to`         |   `→`   | `\iff`        |   `↔`   |
  | `\and`        |   `∧`   | `\or`         |   `∨`   |
  | `\not`        |   `¬`   | `\ne`         |   `≠`   |
  | `\forall`     |   `∀`   | `\exists`     |   `∃`   |
  | `\<`          |   `⟨`   | `\>`          |   `⟩`   |
  | `\in`         |   `∈`   | `\notin`      |   `∉`   |
  | `\sub`        |   `⊆`   | `\|`          |   `∣`   |
  | `\union`      |   `∪`   | `\inter`      |   `∩`   |
  | `\N`          |   `ℕ`   | `\Z`          |   `ℤ`   |
  | `\R`          |   `ℝ`   | `\C`          |   `ℂ`   |
  | `\alpha`      |   `α`   | `\beta`       |   `β`   |
  | `\smul`       |   `•`   | `\le`         |   `≤`   |
  | `\-1`         |   `⁻¹`  | `\comp`       |   `∘`   |
  | `\mapsto`     |   `↦`   | `\cdot`       |   `·`   |
  | `\[[`         |   `⟦`   | `\]]`         |   `⟧`   |
-/

/-
  ## Lean syntax at a glance

  Every theorem in this file has the following shape:

    theorem my_theorem (h₁ : Hypothesis₁) (h₂ : Hypothesis₂) : Conclusion := by
      tactic₁    -- transforms the goal
      tactic₂    -- ...
      ...

  For a nameless result: `example : Conclusion := by ...`

  Reading a signature:

  | Notation     | Meaning                                                        |
  |--------------|----------------------------------------------------------------|
  | `(h : P)`   | explicit argument named `h` of type `P`                       |
  | `{h : P}`   | implicit argument (Lean infers it from context)                |
  | `[inst : C]`| type-class instance (e.g. `[Group G]` = "G has a group        |
  |              | structure", looked up automatically by Lean)                   |
  | `h : P ⊢ Q` | in the Infoview: hypothesis `h : P`, goal to prove is `Q`     |

  The `variable` command at the top of a section declares variables
  in scope. They are silently added to any `example` or `theorem`
  that uses them.

  **Terms vs tactics.**
  A proof can be written as a *term* (a direct expression of the right
  type) or in *tactic mode* (after `by`). In tactic mode, tactics
  transform the goal step by step. Both styles are equivalent — tactic
  mode is usually more readable.
-/

/-
  ⚠ **Pedagogical note** ⚠

  Most exercises in this tutorial could be solved in *one line* by
  a single Mathlib lemma (which `exact?` often finds on its own), or
  even by an automation tactic such as `simp`, `tauto` or `aesop`.
  That is not the point!

  The goal here is to build proofs *step by step*, by hand, to get
  familiar with the basic tactics. The hints provided therefore
  deliberately point to *intermediate* lemmas, not to the one that
  closes the goal directly.

  (The only exception is the section "Searching Mathlib", where the
  whole game is precisely to track down the right lemma.)
-/

/-
  ## How to work on this file

  - **The Infoview** (panel on the right) shows the *proof state* at
    the cursor: the hypotheses above, the current goal below `⊢`.
    If you don't see it: Command palette (Ctrl/Cmd+Shift+P)
    → "Lean 4: Toggle Infoview".
  - Each exercise has a proof that is just `sorry`.
    **Replace `sorry`** with your own proof, one tactic at a time,
    watching the goal change in the Infoview.
  - The proof is complete when the Infoview shows **"No goals"** and
    the yellow warning on `sorry` disappears.
    A red underline means an error — hover to read the message.
  - A bullet `·` focuses on a single subgoal (e.g. after `constructor`).
  - **Hover** over any name to see its type and documentation.

  **Reading the Infoview — concrete example.**
  Place the cursor just after `intro hP` in the proof below.
  The Infoview shows three blocks:

    P Q R : Prop      ← variables in scope (declared with `variable`)
    hP : P            ← hypothesis added by `intro hP`
    ⊢ P               ← current goal: what remains to prove

  After `exact hP`, the Infoview shows "No goals" — proof done.
  Try it: move the cursor between the two lines to watch the state evolve.
-/

-- (example for the Infoview walkthrough — self-contained, try placing your cursor here)
example (P : Prop) : P → P := by
  intro hP    -- ← cursor here → Infoview: P : Prop / hP : P / ⊢ P
  exact hP    -- ← cursor here → Infoview: No goals

/-
  # Propositions and proofs

  Propositions live in the type `Prop`.
  The `sorry` tactic accepts any goal without proving it.
-/

variable (P Q R : Prop)

/-
  ## Implication

  A proof in *tactic mode* is written after `by`. The basic tactics:
  - `intro h` : to prove a goal `P → Q`, assume `P` (call it `h`)
    and prove `Q`;
  - `exact h` : close the goal with a term `h` whose type is exactly
    the goal;
  - `apply h` : from `h : P → Q`, reduce the goal `Q` to the goal `P`.
-/

example : P → P := by
  intro hP
  exact hP

example (h : P → Q) (hP : P) : Q := by
  apply h
  exact hP

-- The `have` tactic introduces a named intermediate result
example (h1 : P → Q) (h2 : Q → R) (hP : P) : R := by
  have hQ : Q := by
    apply h1
    exact hP
  exact h2 (h1 hP)

-- The `rfl` tactic proves a reflexive equality
example : P = P := by
  rfl

-- The `trivial` tactic proves `True` (and other obvious goals)
example : True := by
  trivial

-- The `exfalso` tactic replaces the goal by `False`
example : False → P := by
  intro h
  exfalso
  exact h

/- TODO -/

example : P → Q → P := by
  intro hP hQ
  exact hP

-- Modus ponens
example : P → ((P → Q) → Q) := by
  intro hP
  intro hPQ
  apply hPQ
  exact hP

example : (P → Q) → (Q → R) → P → R := by
  sorry

/- END TODO -/

/-
  ## Negation, True, False

  `¬P` is *defined* as `P → False`.
  The `change` tactic replaces the goal by a *definitionally* equal
  term.
-/

-- `change` lets us unfold the definition of ¬ explicitly
example : ¬True → False := by
  change (True → False) → False
  intro h
  exact h trivial

-- `by_contra` tactic: assume ¬P and look for a contradiction
example : ¬¬P → P := by
  intro h
  by_contra hP
  apply h
  exact hP

-- `by_cases` tactic: case split on P ∨ ¬P (excluded middle)
example : ¬¬P → P := by
  intro h
  by_cases hP : P
  · exact hP
  · exfalso; exact h hP

/- TODO -/

example : P → ¬¬P := by
  intro hP
  intro hnP
  exact hnP hP

example : (P → Q) → ¬Q → ¬P := by
  sorry

-- The converse of the contrapositive (classical: use `by_contra`)
example : (¬Q → ¬P) → P → Q := by
  sorry

/- END TODO -/

/-
  ## Conjunction and disjunction

  Tactics: `constructor`, `obtain`, `left`, `right`, `rcases`
-/

-- `obtain ⟨hP, hQ⟩ := h` destructs `h : P ∧ Q` into two hypotheses
-- `exact ⟨hQ, hP⟩` builds a proof of `Q ∧ P`
example : P ∧ Q → Q ∧ P := by
  intro h
  obtain ⟨hP, hQ⟩ := h
  exact ⟨hQ, hP⟩

example : P ∨ Q → Q ∨ P := by
  intro h
  obtain hP | hQ := h
--  rcases h with hP | hQ
  · right
    exact hP
  · left
    exact hQ

-- `constructor` splits a goal `A ↔ B` into the two implications
-- `A → B` and `B → A`
example : P ∧ Q ↔ Q ∧ P := by
  constructor
  · intro ⟨hP, hQ⟩
    exact ⟨hQ, hP⟩
  · intro ⟨hQ, hP⟩
    exact ⟨hP, hQ⟩

/- TODO -/

example : (P → Q → R) → P ∧ Q → R := by
  sorry

example : P ∨ Q ↔ Q ∨ P := by
  sorry

-- De Morgan's law (the ← direction requires excluded middle)
example : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
  sorry

-- The other De Morgan law
-- (the → direction requires excluded middle: try `by_cases`)
example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
  sorry

/- END TODO -/

/-
  ## Equivalence

  `P ↔ Q` can also be destructed with `obtain ⟨h1, h2⟩ := h`.
-/

-- Destructing ↔ with obtain
example : (P ↔ Q) → (Q ↔ P) := by
  intro ⟨hpq, hqp⟩
  exact ⟨hqp, hpq⟩

/- TODO -/

-- Transitivity of ↔
example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  sorry

example : ¬(P ↔ ¬P) := by
  sorry

/- END TODO -/

/-
  # Quantifiers

  `∀ x : α, P x` : "for all x, P x"   — tactic `intro`
  `∃ x : α, P x` : "there exists x such that P x"  — tactic `use`

  Use `\forall` and `\exists` to write `∀` and `∃`.
-/

variable (α : Type*) (f g : α → Prop)

example (h : ∀ x : α, f x) (a : α) : f a := by
  exact h a

example (a : α) (h : f a) : ∃ x, f x := by
  use a

example (h : ∀ x, f x → g x) (h' : ∃ x, f x) : ∃ x, g x := by
  obtain ⟨a, ha⟩ := h'
  refine ⟨a, ?_⟩
  apply h
  exact ha



/- TODO -/

example : (∀ x, f x ∧ g x) → ∀ x, f x := by
  sorry

example : (∀ x, f x ∧ g x) ↔ (∀ x, f x) ∧ (∀ x, g x) := by
  sorry

example : (∃ x, f x ∨ g x) ↔ (∃ x, f x) ∨ (∃ x, g x) := by
  sorry

-- Negation of quantifiers
-- Hint: `by_contra h'`, then `push Not at h'` — the `push Not`
--   tactic pushes negations inward (`¬ ∀` becomes `∃ ¬`,
--   `¬ ∃` becomes `∀ ¬`, etc.)
example (h : ¬ ∀ x, f x) : ∃ x, ¬ f x := by
  sorry

/- END TODO -/

/-
  # Sets and functions

  `s ⊆ t`    : s is a subset of t  — prove it with `intro x hx`
  `f '' s`   = image of `s` under `f`     = { f x | x ∈ s }
  `f ⁻¹' t`  = preimage of `t` under `f`  = { x | f x ∈ t }

  Useful tactics: `ext` (extensionality: reduce an equality of
  sets/functions to a pointwise statement), and `rintro` (a version
  of `intro` that also destructures patterns on the fly, like
  `⟨a, b⟩` for `∧`/`∃` or `h | h` for `∨`).
-/

-- Proving `s ⊆ t`: introduce an element with `intro x hx`
example (s t u : Set α) (hst : s ⊆ t) (htu : t ⊆ u) : s ⊆ u := by
  intro x hx
  apply htu
  apply hst
  exact hx
  -- exact htu (hst hx)

-- `ext x` reduces a set equality `s = t` to `x ∈ s ↔ x ∈ t`
example (s : Set α) : s ∩ s = s := by
  ext x
  constructor
  · intro ⟨hx, hx'⟩
    exact hx
  · intro hx; exact ⟨hx, hx⟩

-- In the pattern `⟨x, hx | hx, rfl⟩`, the `|` destructs an `∨`, and
--  `rfl` means one of the hypotheses has the form `y = f x`:
--  Lean immediately substitutes `y` by `f x` everywhere
example {β : Type*} (f : α → β) (s t : Set α) :
    f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y
  constructor
  · rintro ⟨x, hx | hx, rfl⟩
    · left
      exact ⟨x, hx, rfl⟩


      -- exact Or.inl ⟨x, hx, rfl⟩
    · exact Or.inr ⟨x, hx, rfl⟩
  · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
    · exact ⟨x, Or.inl hx, rfl⟩
    · exact ⟨x, Or.inr hx, rfl⟩

#print Function.Injective

-- The composition of two injections is injective
example {β γ : Type*} {f : α → β} {g : β → γ}
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (g ∘ f) := by
  intro a b hab
  apply hf
  apply hg
  exact hab

-- The image of an intersection is contained in the intersection
-- of the images
example {β : Type*} (f : α → β) (s t : Set α) :
    f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  intro y hy
  obtain ⟨x, ⟨hxs, hxt⟩, rfl⟩ := hy
  exact ⟨⟨x, hxs, rfl⟩, ⟨x, hxt, rfl⟩⟩

/- TODO -/

-- s ⊆ s ∪ t
example (s t : Set α) : s ⊆ s ∪ t := by
  sorry

-- s ∩ t = t ∩ s
-- Hint: `ext x`, then `constructor` and `rintro ⟨h1, h2⟩`
example (s t : Set α) : s ∩ t = t ∩ s := by
  sorry

-- The preimage respects intersection:
-- f ⁻¹' (s ∩ t) = f ⁻¹' s ∩ f ⁻¹' t
-- Easy mode: `ext x` then `simp`
example {β : Type*} (f : α → β) (s t : Set β) :
    f ⁻¹' (s ∩ t) = f ⁻¹' s ∩ f ⁻¹' t := by
  sorry

-- If f is injective, image(s ∩ t) = image(s) ∩ image(t)
-- Hint for ←: `rintro ⟨⟨x, hxs, rfl⟩, ⟨x', hxt, hxx'⟩⟩`,
--   then `hf` and `subst`
example {β : Type*} {f : α → β} (hf : Function.Injective f)
    (s t : Set α) : f '' (s ∩ t) = f '' s ∩ f '' t := by
  sorry

/- END TODO -/

/-
