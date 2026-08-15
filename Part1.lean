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
  # What is Lean?

  Lean is a **proof assistant**: a language in which statements and
  proofs are written formally, and a program that checks them.

  *Formally* means a statement is not a sentence for a benevolent
  reader to interpret, but an expression whose meaning is fixed by the
  rules of the language. *Checks* means a small program — the
  **kernel** — verifies every inference. It has no notion of what is
  obvious, and no bad days.

  The trade: you gain certainty, and the right to build on other
  people's work without re-reading it; you pay by having to say
  everything. "Similarly", "without loss of generality" and "clearly"
  must all be supplied. Much of the skill of formalizing is telling
  which of those silent steps are routine, and which were hiding the
  content of the proof.

  In exchange the machine understands the statement, so it can help:
  it shows what remains to be proved, finds lemmas, and closes routine
  goals by itself.
-/

/-
  ## How Lean is put together

  What happens between the text you type and the verdict:

    source text
       ↓  **parser**       — text to syntax tree
       ↓  **macros**       — expand notation
       ↓  **elaborator**   — syntax to a term of the core language:
       ↓                     implicit arguments, instances, coercions,
       ↓                     and running `by` blocks
       ↓  **kernel**       — re-checks the finished term

  Everything convenient lives in the **elaborator** — a large, subtle
  piece of software, as are the tactics and Mathlib. The point: *none
  of them has to be trusted*. A tactic does not assert a theorem, it
  **builds a term**, which the kernel then re-checks. A bug in a
  tactic, in the elaborator or in a Mathlib proof cannot make Lean
  accept a false statement; it can only produce a term the kernel
  rejects.

  Nor need you trust the kernel. Proof terms can be **exported** and
  checked by programs written elsewhere, in other languages: the *Lean
  Kernel Arena* (https://arena.lean-lang.org) runs more than a dozen
  independent checkers against a common suite — proofs to accept, and
  invalid proofs to reject. Better still, **you can write your own
  kernel**: the format is documented, the test suite downloadable, a
  checker a few thousand lines. Accept a theorem because *your* checker
  accepts it, and you are trusting no one at all. That is the answer to
  "who checks the checker?" — not perfect software, but a design in
  which conviction never rests on anyone's word.

  It also explains why proofs written as terms and proofs written with
  tactics are the same thing: tactics write the term for you.

  Lean is its own implementation language. The elaborator, the tactics
  and Mathlib are written in Lean, run by an **interpreter** (which
  also executes `#eval`) or compiled to C — hence users can add
  notation, tactics, even elaboration rules, without touching the
  kernel.

  Two caveats. The kernel is small but not infallible: soundness bugs
  have been found, and are treated as serious public events. And, far
  more important in practice, the kernel guarantees that *the statement
  you wrote* was proved — not that you wrote the statement you meant.
  Reading statements carefully remains your job.

  (References in `References.md`.)
-/

/-
  # What is Mathlib?

  A proof assistant alone proves nothing interesting: you would have to
  build the real numbers before stating that a continuous function on a
  closed interval is bounded.

  **Mathlib** is the community's answer: one unified library of
  formalized mathematics — well over a million lines, hundreds of
  contributors, every addition reviewed — covering much of an
  undergraduate and graduate curriculum.

  Two features matter more than its size.

  It is **unified**: one notion of group, of topological space, of
  limit, everything built on them. A theorem about compact spaces
  applies to a closed interval because that interval is known to be
  compact, in the same library, with no translation layer. Hence a new
  statement takes a few lines — the vocabulary is already there.

  It is **general**: results are stated in their natural generality,
  often beyond the version you were taught. Looking for "a product of
  continuous functions is continuous", you find a statement about
  topological semirings. Reading that generality, and locating your own
  case inside it, is much of what learning Mathlib means.

  So this course is about two things. The language takes a few hours;
  the library is the work of a career — but finding your way around it
  is a skill you can start acquiring today.

  **History.** Kevin Hartnett, *The Proof in the Code: How a Truth
  Machine Is Transforming Math and AI* (Quanta Books, 2026) tells the
  story of Lean and Mathlib. Journalism, no prerequisites.
-/

/-
  # Everything has a type

  Every expression has exactly one **type**, fixed when it is
  elaborated; `#check e` displays it. What is striking is how far the
  idea goes: types themselves, functions, statements and *proofs* all
  have types, in one and the same language.
-/

-- Ordinary values
#check 2                      -- ℕ  (the default for a bare numeral)
#check (2 : ℝ)                -- ℝ  (a type ascription forces the choice)
#check (2, 3)                 -- ℕ × ℕ

-- Types are themselves expressions, with a type of their own
#check ℕ                       -- Type
#check ℝ → ℝ                   -- Type

-- Functions
#check fun n : ℕ ↦ n + 1      -- ℕ → ℕ
#check Nat.succ               -- ℕ → ℕ

-- Statements: a *statement* is an expression of type `Prop`…
#check 2 + 2 = 4              -- Prop
#check 2 + 2 = 5              -- Prop  ← being a statement is not being true!
#check ∀ n : ℕ, n + 0 = n     -- Prop

-- … and a *proof* is an expression whose type is the statement proved.
-- This is the single most important idea in Lean.
#check Nat.add_comm           -- ∀ (n m : ℕ), n + m = m + n
#check Nat.add_comm 2 3       -- 2 + 3 = 3 + 2

/-
  `Nat.add_comm` is not a label pointing at a theorem stored elsewhere:
  it *is* the proof, and its type is the statement. Applied to `2` and
  `3` like a function, it yields a proof of that instance.

  So "having a proof of P" is "having a term of type P", and checking a
  proof is checking a type. Hence terms and tactics, below, are not
  really two things.
-/

/-
  ## Lean also computes

  Lean is a programming language too, so some expressions can simply be
  run: `#eval e` computes the value of `e`. This is the interpreter
  mentioned above — handy to check a definition against an example.
-/

#eval 2 ^ 10                  -- 1024
#eval (List.range 5).sum      -- 10

/-
  # The shape of a statement

    theorem my_theorem (h₁ : Hypothesis₁) (h₂ : Hypothesis₂) : Conclusion := by
      tactic₁    -- transforms the goal
      tactic₂    -- ...

  Read it as: *under h₁ and h₂, the conclusion holds, and here is why*.
  Before the colon, what you are given; after it, what you must
  establish; after `:=`, the proof. Unnamed results are written
  `example : Conclusion := by ...`, which we use constantly.

  **Terms versus tactics.** A proof can be a *term* — an expression
  whose type is the statement, like `mul_comm a b` — or a sequence of
  tactics after `by`, each transforming the goal until nothing is left.
  As we saw, these are the same thing: tactics build the term for you.
  Most proofs mix the two.

  The `variable` command declares variables shared by several
  statements; they are added silently to any result that mentions them.
-/

/-
  ## Reading a Mathlib statement

  Three kinds of brackets appear in a signature, and they decide what
  *you* must supply and what Lean works out on its own.

  | Notation        | Meaning                                          |
  |-----------------|--------------------------------------------------|
  | `(a b : G)`     | **explicit** — you write them                    |
  | `{G : Type*}`   | **implicit** — Lean infers them from the context |
  | `[CommMagma G]` | **instance** — Lean looks it up in its database  |

  Instance brackets are the mechanism behind the generality described
  above: `[Group G]` reads "G is equipped with a group structure", and
  Lean finds that structure by itself. Prefixing a name with `@` makes
  everything explicit — useful when Lean guesses wrong.
-/

-- Compare the two: `@` reveals the hidden arguments
#check mul_comm
#check @mul_comm

-- In everyday use you only write the explicit ones
example (a b : ℤ) : a * b = b * a := mul_comm a b

-- The same proof with every argument spelled out.
-- `_` asks Lean to fill in the instance itself
example (a b : ℤ) : a * b = b * a := @mul_comm ℤ _ a b

-- Implicit arguments are recovered from the *other* arguments:
-- in `hab : f a = f b`, Lean reads off `α`, `β` and `f`
example {α β : Type} {f : α → β} (hf : Function.Injective f)
    (a b : α) (hab : f a = f b) : a = b := hf hab

/-
  # The Infoview: reading the proof state

  The single most important habit to acquire. The panel on the right
  shows, at your cursor, exactly where the proof stands. A proof is a
  journey through these states, and the Infoview is the map. If you do
  not see it: `Ctrl/Cmd+Shift+P` → "Lean 4: Toggle Infoview".

  Two parts, separated by the turnstile `⊢`:

    P Q R : Prop      ← what is in scope, and what you may use
    hP : P            ← a hypothesis, with the name you gave it
    ⊢ P               ← the goal: what remains to be proved

  Put your cursor after `intro hP` below, then after `exact hP`, and
  watch the state change. "What does the Infoview say?" answers most
  difficulties.
-/

-- (self-contained — try placing your cursor on each line in turn)
example (P : Prop) : P → P := by
  intro hP    -- ← cursor here → Infoview: P : Prop / hP : P / ⊢ P
  exact hP    -- ← cursor here → Infoview: No goals

/-
  While Lean is thinking, orange bars in the left margin mean the file
  is still being processed — wait for them to clear before trusting
  what you see. A red underline is an error: hover to read the message.
-/

/-
  # How to work on this file

  The exercises are the occurrences of `sorry`, grouped in blocks
  marked `/- TODO -/ … /- END TODO -/`. `sorry` closes any goal without
  proving it: it is how one leaves a hole on purpose, and Lean warns on
  every such hole, so nothing is ever silently assumed.

  - **Replace `sorry`** with your proof, one tactic at a time, watching
    the goal change in the Infoview.
  - Done when the Infoview shows **"No goals"** and the warning goes.
  - A bullet `·` focuses on one subgoal — e.g. after `constructor`.
  - **Hover** over any name for its type and documentation.

  Solutions are in the `Solutions/` directory.

  ⚠ Most exercises could be closed in one line by a single Mathlib
  lemma — which `exact?` often finds — or by `simp`, `tauto` or
  `aesop`. That is not the point: the goal is to build proofs *by
  hand*, to get a feel for the basic tactics. The hints therefore point
  at *intermediate* lemmas, never at the one that closes the goal. (The
  exception is "Searching Mathlib" in Part 2, where finding the lemma
  is precisely the exercise.)
-/

/-
  ## Keyboard shortcuts — reference

  Unicode is typed as a backslash sequence followed by space or tab.
  Nothing to memorise; come back to this table. Hovering over a symbol
  also tells you how to type it.

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
  # Types, coercions and subtypes

  Everything in Lean has exactly one type, and Lean is strict about it.
  This section collects the three things that surprise newcomers most:
  how a numeral gets its type, how Lean moves between `ℕ`, `ℤ`, `ℝ`,
  and how one carries a property around with an element.
-/

/-
  ## Strict typing and elaboration

  A numeral such as `2` has no intrinsic type: Lean *elaborates* it,
  that is, it decides the type from the context. With no constraint
  at all, the default is `ℕ`.
-/

#check 2            -- ℕ
#check (2 : ℝ)      -- ℝ
#check (2 : ℤ)      -- ℤ

-- This matters, because ℕ-subtraction is *truncated* at zero:
#eval (2 - 5 : ℕ)   -- 0, not -3
#eval (2 - 5 : ℤ)   -- -3

-- The type ascription `(e : T)` is how you force a choice.
-- Here it changes the *statement*, not just its display:
example : (2 - 5 : ℕ) = 0 := by norm_num

/-
  `show` restates the goal in a definitionally equal form. It changes
  nothing mathematically, but it lets you say what you mean.
-/
example (n : ℕ) : n + 0 = n := by
  show n + 0 = n
  simp

/-
  ## Coercions: the `↑` arrow

  Lean does not silently identify `ℕ` with `ℝ`. Instead it inserts a
  *coercion*, displayed `↑n` (here `Nat.cast n`). So in `(n : ℕ)` and
  `x + n` with `x : ℝ`, what is really written is `x + ↑n`.
-/

example (n : ℕ) (x : ℝ) : ℝ := x + n     -- really `x + ↑n`

#check fun (n : ℕ) ↦ (n : ℝ)            -- ℕ → ℝ, i.e. `Nat.cast`

/-
  Two tactics do the bookkeeping:
  * `push_cast` pushes coercions *towards the leaves*
    (`↑(a + b)` becomes `↑a + ↑b`);
  * `norm_cast` normalises them and tries to close the goal;
    `exact_mod_cast h` is `exact h` up to coercions.
-/

example (n m : ℕ) : ((n + m : ℕ) : ℝ) = (n : ℝ) + (m : ℝ) := by
  push_cast
  ring

-- ⚠ Coercion does *not* commute with ℕ-subtraction without a hypothesis:
-- `↑(n - m) = ↑n - ↑m` is false in general (take n = 2, m = 5).

/-
  ## `↑` versus `⇑`

  There is a second arrow. A *bundled* morphism, say `f : G →* H`, is
  not a function: it is a structure packaging a function together with
  the proof that it preserves multiplication. Writing `f x` silently
  applies the coercion-to-function `⇑f`.

  Rule of thumb: `↑` coerces a *value* to another type, `⇑` coerces a
  *bundled object* to the function it contains.
-/

example {G H : Type*} [Group G] [Group H] (f : G →* H) (x y : G) :
    f (x * y) = f x * f y :=
  f.map_mul x y

/-
  ## Subtypes

  `{x : α // p x}` is the type of elements of `α` satisfying `p`.
  One of its terms is a *pair*: a value and a proof.
  * `x.val` (also written `↑x`) is the underlying element;
  * `x.property` is the proof that it satisfies `p`.
-/

-- The positive naturals
#check ({ n : ℕ // 0 < n })

example (x : { n : ℕ // 0 < n }) : 0 < x.val := x.property

-- Building a term: give the value and the proof
example : { n : ℕ // 0 < n } := ⟨1, Nat.one_pos⟩

/-
  ## Proof irrelevance

  In Lean, any two proofs of the same proposition are *equal* — and
  equal by definition, so `rfl` proves it.
-/

example (p : Prop) (h₁ h₂ : p) : h₁ = h₂ := rfl

/-
  This is exactly what makes subtypes usable: to prove that two terms
  of `{x : α // p x}` are equal, only the values matter, since the
  proof components are automatically equal. That is `Subtype.ext`.
-/

example (x y : { n : ℕ // 0 < n }) (h : x.val = y.val) : x = y :=
  Subtype.ext h

/- TODO -/

-- Casts commute with multiplication.
-- Hint: push the coercions towards the leaves, then finish with `ring`
example (n m : ℕ) : ((n * m : ℕ) : ℝ) = (n : ℝ) * (m : ℝ) := by
  sorry

-- With a hypothesis, subtraction does survive the cast.
-- Hint: ℕ-subtraction is truncated, so `h` has to be used;
--   look for the cast lemma for `-` that takes such a hypothesis
example (n : ℕ) (h : 5 ≤ n) : ((n - 5 : ℕ) : ℤ) = (n : ℤ) - 5 := by
  sorry

-- Two positive naturals with the same value are equal.
-- Hint: only the values matter — the proof components are equal
--   for free (proof irrelevance)
example (x y : { n : ℕ // 0 < n }) (h : (x : ℕ) = (y : ℕ)) : x = y := by
  sorry

-- A function cannot distinguish two proofs of the same proposition.
-- Hint: no lemma needed here — think about what `rfl` can already do
example (p : Prop) (f : p → ℕ) (h₁ h₂ : p) : f h₁ = f h₂ := by
  sorry

/- END TODO -/
