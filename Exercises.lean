/-
  # Introduction to Lean: Formalizing Mathematics with Mathlib
  Summer school "Proof assistants and applications"
  IRMA, Université de Strasbourg, August 31 – September 4, 2026
  Xavier Roblot (Université Claude Bernard Lyon I)

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
  # Algebraic structures

  Lean/Mathlib represents algebraic structures with **type classes**.
  For instance, writing `[Group G]` means
  "G is equipped with a group structure".

  The structures form a hierarchy:
    Monoid → Group → CommGroup
    Ring → CommRing → Field
    AddCommGroup + scalars → Module (generalizes vector space)
-/

/-
  **Instance synthesis**

  Lean maintains a database of type class *instances*.
  When we want to apply a lemma whose signature contains
  `[CommRing R]`, Lean automatically searches this database for an
  instance of `CommRing R` for the type `R` at hand — this is
  *instance synthesis*. The `inferInstance` command triggers this
  search explicitly, and the `#synth` command lets us check that an
  instance exists (and find its name).
-/

#synth CommRing ℤ   -- Int.instCommRing
#synth Monoid ℝ      -- Real.instField
#synth Field ℂ      -- Complex.instField

/-
  **What can be an instance**: only *type classes* may appear in
  this database. An ordinary proposition (like `Nat.Prime 5 : Prop`)
  cannot appear directly. This is why we use `Fact P`: it is a type
  class with a single field `out : P`, which lets us register a
  proposition in the instance database.
-/
-- (`norm_num` proves goals about concrete numbers,
--  here `Nat.Prime 5`)
example : Field (ZMod 5) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact inferInstance

/-
  ## Groups

  A group morphism `f : G →* H` satisfies `f (a * b) = f a * f b`.
  Lean automatically derives `f 1 = 1` and `f (a⁻¹) = f(a)⁻¹`.
-/

#check MonoidHom.map_one
#check MonoidHom.map_mul

-- f(1_G) = 1_H
example {G H : Type*} [Group G] [Group H] (f : G →* H) : f 1 = 1 :=
  map_one f

#check eq_inv_of_mul_eq_one_left

-- f(a⁻¹) = f(a)⁻¹
-- `rw [h]` rewrites the goal using an equality `h` (left-to-right);
--   `rw [← h]` rewrites right-to-left. A list `rw [h1, h2, ...]`
--   applies the rewrites in order.
-- Idea: show f(a) * f(a⁻¹) = 1, then conclude with
--   `eq_inv_of_mul_eq_one_left`
example {G H : Type*} [Group G] [Group H] (f : G →* H) (a : G) :
    f a⁻¹ = (f a)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← map_mul f, inv_mul_cancel, map_one f]

-- The `group` tactic proves identities valid in *any* group
-- (analogue of `ring`)
example {G : Type*} [Group G] (x y z : G) :
    x * (y * z) * (x * z)⁻¹ * (x * y * x⁻¹)⁻¹ = 1 := by group

-- The `abel` tactic does the same in an abelian group
-- (written additively)
example {G : Type*} [AddCommGroup G] (x y z : G) :
    z + x + (y - z - x) = y := by abel

/- TODO -/

-- If f is injective, then: f(a) = 1 → a = 1
example {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) (a : G) (h : f a = 1) : a = 1 := by
  sorry

-- In a commutative monoid, (a * b) ^ n = a ^ n * b ^ n
-- Hint: `pow_succ x n : x ^ (n + 1) = x ^ n * x`
--   and `mul_mul_mul_comm`
--
-- The `simp` tactic simplifies the goal by applying a database of
-- lemmas automatically. `simp?` does the same but displays the
-- lemmas it used — useful to understand, or to replace `simp` by a
-- more explicit call.
--
-- Skeleton of the induction:
--   induction n with
--   | zero   => simp        -- base case: (a * b) ^ 0 = 1 = 1 * 1
--   | succ n ih => ...
example {M : Type*} [CommMonoid M] (a b : M) (n : ℕ) :
    (a * b) ^ n = a ^ n * b ^ n := by
  sorry

-- In a group where every element satisfies a ^ 2 = 1,
-- multiplication is commutative.
-- Approach: first show every element is its own inverse,
--   i.e. ∀ x, x⁻¹ = x.
--   For that: x * x = 1 (since x ^ 2 = 1), then use
--   `eq_inv_of_mul_eq_one_left`.
--   Then: a * b = (a * b)⁻¹ = b⁻¹ * a⁻¹ = b * a.
--   (`mul_inv_rev` gives (a * b)⁻¹ = b⁻¹ * a⁻¹)
example {G : Type*} [Group G] (h : ∀ a : G, a ^ 2 = 1) (a b : G) :
    a * b = b * a := by
  sorry

-- The preimage of a subgroup under a morphism preserves inclusion
-- `S.comap φ` is the preimage of S under φ (a subgroup of G)
-- Secondary hint: `Subgroup.mem_comap` : `a ∈ S.comap φ ↔ φ a ∈ S`
example {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (S T : Subgroup H) (hST : S ≤ T) : S.comap φ ≤ T.comap φ := by
  sorry

/- END TODO -/

/-
  ## Rings and fields

  The `ring` tactic proves algebraic identities in a `CommRing`.
  A ring morphism `f : R →+* S` preserves +, * and 1
  (`map_add`, `map_mul`, `map_pow`).
  A field (`Field`) is a `CommRing` where every nonzero element is
  invertible; convention: `0⁻¹ = 0`.
-/

-- Commutativity is an assumption, not a theorem: `Ring` ≠ `CommRing`
example {R : Type*} [CommRing R] (a b : R) :
    a * b = b * a := mul_comm a b

-- `ring` proves polynomial identities in a `CommRing`
example {R : Type*} [CommRing R] (a b : R) :
    (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by ring

-- A ring morphism preserves powers and sums
example {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (a b : R) : f (a ^ 2 + b ^ 2) = f a ^ 2 + f b ^ 2 := by
  rw [map_add, map_pow, map_pow]

-- In a field, a zero product implies a zero factor
example {K : Type*} [Field K] (a b : K) (h : a * b = 0) :
    a = 0 ∨ b = 0 :=
  Iff.mp mul_eq_zero h

/- TODO -/

-- Factorization of a³ - b³ (use `ring`)
-- The same statement is false in a noncommutative `Ring`:
-- `ring` requires `CommRing`
example {R : Type*} [CommRing R] (a b : R) :
    a ^ 3 - b ^ 3 = (a - b) * (a ^ 2 + a * b + b ^ 2) := by
  sorry

-- The inverse of the inverse is the element itself (for a ≠ 0)
-- Hint: `inv_ne_zero`, `mul_inv_cancel₀`, `inv_mul_cancel₀`
example {K : Type*} [Field K] (a : K) (ha : a ≠ 0) : (a⁻¹)⁻¹ = a := by
  sorry

-- Left cancellation in a field: a ≠ 0, a * b = a * c → b = c
-- Hint: multiply by a⁻¹ on the left, then `mul_assoc`
--   and `inv_mul_cancel₀`
example {K : Type*} [Field K] (a b c : K) (ha : a ≠ 0)
    (h : a * b = a * c) : b = c := by
  sorry

-- The units of ℤ are exactly ±1 (a bit harder)
-- Note: `↑x` (type `\u`) is the integer value of the unit `x`
--   — the coercion ℤˣ → ℤ.
-- Approach: ↑x ∣ 1 (witness ↑x⁻¹), so ↑x is a unit of ℤ,
--   hence ↑x = ±1
#check @Units.mul_inv     -- ↑x * ↑x⁻¹ = 1 in ℤˣ
#check isUnit_of_dvd_one  -- a ∣ 1 → IsUnit a
#check Int.isUnit_iff     -- IsUnit n ↔ n = 1 ∨ n = -1
example (x : ℤˣ) : (x : ℤ) = 1 ∨ (x : ℤ) = -1 := by
  sorry

/- END TODO -/

/-
  # Analysis and topology

  **A note on filters**: *filters* are a central abstraction in
  Mathlib, both in analysis and in topology. On the analysis side,
  limits are written with them: `Filter.Tendsto f (nhds a) (nhds b)`
  means `f(x) → b` as `x → a`, which unifies limits at a point, at
  infinity, convergent sequences, etc. On the topology side, they
  underpin neighborhoods (`𝓝 x`), continuity, closure, and even
  compactness. We do not go into these details here.
-/

/-
  ## Continuity

  `Continuous f`      : f is continuous everywhere
  `ContinuousAt f x`  : f is continuous at x
  `ContinuousOn f s`  : f is continuous on the set s

  The `fun_prop` tactic automatically proves *functional* properties
  of the usual functions: not only continuity, but also
  differentiability, measurability, integrability, etc.
  We use it here for continuity.
-/

-- fun_prop in action
example : Continuous (fun x : ℝ ↦ x ^ 2 + 1) := by fun_prop
example : Continuous (fun x : ℝ ↦ Real.sin (Real.exp x)) := by
  fun_prop

-- The composition of two continuous functions is continuous
example {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    Continuous (g ∘ f) := Continuous.comp hg hf

-- `Continuous` coincides with the classical ε-δ definition
-- (in a metric space)
example {f : ℝ → ℝ} : Continuous f ↔
    ∀ x, ∀ ε > 0, ∃ δ > 0,
      ∀ x', dist x' x < δ → dist (f x') (f x) < ε :=
  Metric.continuous_iff

/- TODO -/

-- x ↦ cos x + x ^ 2 is continuous
example : Continuous (fun x : ℝ ↦ Real.cos x + x ^ 2) := by
  sorry

-- If f and g are continuous, x ↦ f x * g x is continuous
example {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x ↦ f x * g x) := by
  sorry

/- END TODO -/

-- Intermediate value theorem
#check intermediate_value_uIcc

/-
  ## Derivatives

  `HasDerivAt f f' x`   : f is differentiable at x, with derivative f'
  `deriv f x`           : the derivative of f at x
  `Differentiable ℝ f`  : f is differentiable everywhere

  `fun_prop` also checks differentiability.
-/

-- Derivatives of the usual functions
example : deriv Real.sin = Real.cos := by
  ext x
  simp [Real.deriv_sin]

example : deriv Real.exp = Real.exp := by
  ext x
  simp [Real.deriv_exp]

-- `simp` can also compute the derivative of simple functions
-- at a point
example : deriv (fun x : ℝ ↦ x ^ 5) 6 = 5 * 6 ^ 4 := by simp

-- fun_prop checks differentiability
example : Differentiable ℝ
    (fun x : ℝ ↦ Real.cos (Real.sin x) * Real.exp x) := by fun_prop

-- Two theorems of differential calculus
#check exists_deriv_eq_zero        -- Rolle's theorem
#check exists_hasDerivAt_eq_slope  -- Mean value theorem

/- TODO -/

-- x ↦ x ^ 3 + x is differentiable
-- Hint: a sum of differentiable functions is differentiable
--   (`Differentiable.add`).
-- Of course, `fun_prop` handles all of this on its own.
example : Differentiable ℝ (fun x : ℝ ↦ x ^ 3 + x) := by
  sorry

-- The derivative of x ↦ x ^ 2 is x ↦ 2 * x
-- Hint: start with `ext x`, then `simp`
example : deriv (fun x : ℝ ↦ x ^ 2) = fun x ↦ 2 * x := by
  sorry

/- END TODO -/

-- Fundamental theorem of calculus
#check intervalIntegral.integral_eq_sub_of_hasDerivAt

/-
  ## Topology

  `IsOpen s`    : s is open
  `IsClosed s`  : s is closed
  `IsCompact s` : s is compact
-/

-- Examples of open and closed sets
example : IsOpen (Set.Ioo (0 : ℝ) 1) := isOpen_Ioo
example : IsClosed (Set.Icc (0 : ℝ) 1) := isClosed_Icc

-- The preimage of an open set under a continuous function is open
example {f : ℝ → ℝ} (hf : Continuous f) {s : Set ℝ} (hs : IsOpen s) :
    IsOpen (f ⁻¹' s) := IsOpen.preimage hf hs

/- TODO -/

-- The preimage of a closed set under a continuous function is closed
example {f : ℝ → ℝ} (hf : Continuous f) {s : Set ℝ}
    (hs : IsClosed s) : IsClosed (f ⁻¹' s) := by
  sorry

-- The image of a compact set under a continuous function is compact
example {f : ℝ → ℝ} (hf : Continuous f) {s : Set ℝ}
    (hs : IsCompact s) : IsCompact (f '' s) := by
  sorry

-- Bolzano: a continuous function that changes sign on [0, 1]
-- has a zero there. (a longer proof, in several steps)
-- Hint: the intermediate value theorem (cf. the `#check` above)
--   gives an inclusion `Set.Icc (f 0) (f 1) ⊆ f '' Set.Icc 0 1`;
--   show that `0` belongs to the left-hand interval, then read off
--   a point of `Set.Icc 0 1` from the image.
example (f : ℝ → ℝ) (hf : Continuous f) (h0 : f 0 < 0)
    (h1 : 0 < f 1) : ∃ x ∈ Set.Icc (0 : ℝ) 1, f x = 0 := by
  sorry

/- END TODO -/

-- Extreme value theorem: a continuous function on a nonempty
-- compact attains its minimum
#check IsCompact.exists_isMinOn

-- Heine-Cantor: continuous on a compact → uniformly continuous
#check IsCompact.uniformContinuousOn_of_continuous

-- Heine-Borel: compact ↔ closed and bounded (in ℝⁿ)
#check Metric.isCompact_iff_isClosed_bounded

/-
  # Searching Mathlib

  Mathlib contains thousands of lemmas.
  Here are the tools to find them.

  ## Interactive tactics (in a proof)

  `exact?`  — looks for a lemma that proves the current goal exactly
  `apply?`  — looks for a lemma whose conclusion matches the goal
  `simp?`   — finds the simp lemmas that close or simplify the goal

  ## In-editor search commands (no browser needed)

  Mathlib ships two commands that query the search engines directly
  from the editor and show clickable results in the Infoview:

  * `#loogle <pattern>` — Loogle search, by type pattern or by
    constant names:
      `#loogle ?a ∣ ?b → ?a ∣ ?b * ?c`     (type pattern)
      `#loogle Nat.gcd, Nat.lcm`           (by names)
  * `#leansearch "..."` — natural-language search; the query must
    end with `.` or `?`.

  Both also work inside a `by` block, where the results offer
  ready-made `exact …`/`apply …`.

  ## Search engines (in the browser)

  * **Mathlib docs**:
    https://leanprover-community.github.io/mathlib4_docs
    Search by name, type, module.

  * **Loogle**: https://loogle.lean-lang.org
    Search by type pattern. Example: `?a ∣ ?b → ?a ∣ ?b * ?c`

  * **LeanSearch**: https://leansearch.net
    Natural language search. Example: "prime divides product"
-/

-- The commands below query Loogle / LeanSearch from the editor.
-- They are commented out because each one makes a network call;
-- **remove the `--`** in front of a line to run it and see the
-- (clickable) results in the Infoview.

-- #loogle ?a ∣ ?b → ?a ∣ ?b * ?c
-- #loogle Nat.gcd, Nat.lcm
-- #leansearch "a prime dividing a product divides a factor?"

-- Exercise: find and use the right lemma in each case.
-- Unlike the rest of the tutorial — where hints never give the
-- final lemma — here the goal IS to track down the lemma that
-- closes the goal in one line.
-- (use `exact?` or the search engines above)

/- TODO -/

-- If a ∣ b and b ∣ c, then a ∣ c
example (a b c : ℤ) (h1 : a ∣ b) (h2 : b ∣ c) : a ∣ c := by
  sorry

-- gcd(a, b) * lcm(a, b) = a * b
example (a b : ℕ) : Nat.gcd a b * Nat.lcm a b = a * b := by
  sorry

-- π is irrational
example : Irrational Real.pi := by
  sorry

-- Fermat's Last Theorem for n = 3
-- (`FermatLastTheoremFor n` means:
--  ∀ a b c : ℕ, a ≠ 0 → b ≠ 0 → c ≠ 0 → a^n + b^n ≠ c^n)
example : FermatLastTheoremFor 3 := by
  sorry

/- END TODO -/

/-
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

end
