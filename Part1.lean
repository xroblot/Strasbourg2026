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

  Lean is a **proof assistant**: a language in which mathematical
  statements and their proofs are written formally, and a program that
  checks those proofs.

  "Formally" means that a statement is not a sentence to be interpreted
  by a benevolent reader, but an expression whose meaning is completely
  determined by the rules of the language. And "checks" means what it
  says: a small program, the *kernel*, verifies every single inference
  against a fixed set of rules. It has no notion of what is obvious, no
  willingness to grant you a step, and no bad days. If it accepts your
  proof, the result follows from the axioms — full stop.

  This is a trade. What you gain is certainty, and the ability to build
  on other people's work without re-reading it. What you pay is that
  everything must be said. Steps that a human reader grants you in
  silence — "similarly", "without loss of generality", "clearly" —
  have to be supplied. Much of the skill of formalizing lies in
  recognising which of those silent steps are genuinely routine, and
  which were hiding the actual content of the proof.

  A second, less advertised benefit: because the machine understands
  the statement, it can *help*. It tells you at every moment what
  remains to be proved, it finds lemmas for you, and it discharges
  routine goals by itself. Working in Lean feels much less like
  dictating a proof to a machine than like having a conversation with
  a very literal-minded colleague.

  Lean is a full programming language as well, and it is used as one.
  We will barely touch that side of it here.
-/

/-
  ## How Lean is put together

  It is worth knowing, in outline, what happens between the text you
  type and the verdict you get. The claim "the machine checked it"
  means something quite precise, and the precision is reassuring.

  Your file goes through a pipeline:

    source text
       ↓  **parser**        — turns the text into a syntax tree,
       ↓                      following the notation rules in scope
       ↓  **macros**        — expand user-defined notation into
       ↓                      more primitive syntax
       ↓  **elaborator**    — turns syntax into a *term* of the core
       ↓                      language: this is where implicit
       ↓                      arguments are guessed, instances found,
       ↓                      coercions inserted, `by` blocks run
       ↓  **kernel**        — re-checks the finished term against the
                              rules of the underlying type theory

  Almost everything convenient about Lean lives in the **elaborator**.
  It is a large, subtle piece of software. So are the tactics, and so
  is Mathlib. And here is the point: *none of them has to be trusted*.

  A tactic does not assert a theorem; it **builds a term**, and the
  term is then handed to the kernel. The kernel is small, it
  implements one fixed theory (the Calculus of Inductive
  Constructions), and it knows nothing about tactics, notation or
  instances. A bug in a tactic, in the elaborator, or in a Mathlib
  proof therefore cannot make Lean accept a false statement: it can
  only produce a term that the kernel rejects. Everything you trust is
  concentrated in one small, heavily scrutinised component — the
  *trusted computing base*. Proof terms can even be exported and
  re-checked by independently written checkers.

  This also explains something you will meet in a minute: why proofs
  written as terms and proofs written with tactics are the same thing.
  Tactics are simply programs that write the term for you.

  One last component: Lean is its own implementation language. The
  elaborator, the tactics and Mathlib are written in Lean, and run
  either through an **interpreter** — that is what executes `#eval`,
  and what runs your tactics as you type — or through a **compiler**
  that emits C for released code. This is why users can add their own
  notation, their own tactics, even their own elaboration rules,
  without touching the kernel.

  Two honest caveats. First, the kernel is small but not infallible;
  soundness bugs have been found, and are treated as serious public
  events. Second, and far more important in practice: the kernel
  guarantees that *the statement you wrote* has been proved. It cannot
  tell you that you wrote the statement you meant. Reading statements
  carefully is, and remains, your job.

  (References for this section are in `References.md`.)
-/

/-
  # What is Mathlib?

  A proof assistant on its own proves nothing interesting: you would
  have to build the real numbers before you could state that a
  continuous function on a closed interval is bounded.

  **Mathlib** is the answer to that problem. It is a single, unified
  library of formalized mathematics, built by the Lean community over
  the last several years — well over a million lines, hundreds of
  contributors, and a review process that every addition goes through.
  It covers a great deal of an undergraduate and graduate curriculum:
  algebra, topology, analysis, measure theory, category theory, number
  theory, and more.

  Two features matter more than its size.

  First, it is **unified**. There is one notion of group, one notion of
  topological space, one notion of limit, and everything is built on
  top of them. A theorem about compact spaces applies to the closed
  interval because the closed interval is known to be compact, in the
  same library, with no translation layer. This is what makes it
  possible to state a new result in a few lines: the vocabulary is
  already there.

  Second, it is **general**. Results are stated in the natural
  generality — often more general than the version you were taught.
  This is occasionally disconcerting: looking for "the product of two
  continuous functions is continuous", you find a statement about
  topological semirings. Learning to read that generality, and to see
  your own special case inside it, is a large part of learning Mathlib.

  So this course is really about two things: the language, and the
  library. The language can be learned in a few hours. The library is
  the work of a career — but finding your way around it is a skill you
  can start acquiring today, and we will spend real time on it.

  **How all this came about.** The story of Lean and of Mathlib — from
  a code-checking project at Microsoft Research to a library that has
  changed how a part of the mathematical community works — is told at
  book length in Kevin Hartnett, *The Proof in the Code: How a Truth
  Machine Is Transforming Math and AI* (Quanta Books, 2026). It is
  journalism rather than mathematics, and it requires nothing of what
  we do here; read it for the history and the people.
-/

/-
  # Everything has a type

  Lean's basic discipline is that every expression has exactly one
  **type**, known at the time the expression is elaborated. `2` is a
  natural number, `ℝ` is a type, `Nat.add_comm` is a proof.

  Two commands let you interrogate this:
  * `#check e` displays the type of `e`;
  * `#eval e` computes the value of `e`, when it can be computed.

  Try moving your cursor onto the lines below, and watch the panel on
  the right.
-/

-- The type of a theorem *is* its statement — a proof is a term
-- whose type is the thing proved. More on this in a moment.
#check Nat.add_comm   -- ∀ (n m : ℕ), n + m = m + n

#eval 2 ^ 10          -- 1024

/-
  # The shape of a statement

  Every result in this file has the following shape:

    theorem my_theorem (h₁ : Hypothesis₁) (h₂ : Hypothesis₂) : Conclusion := by
      tactic₁    -- transforms the goal
      tactic₂    -- ...
      ...

  Read it as: *under the hypotheses h₁ and h₂, the conclusion holds,
  and here is why*. Everything before the colon is what you are given;
  what follows the colon is what you must establish; and what follows
  `:=` is the proof itself. When the result does not need a name, write
  `example : Conclusion := by ...` — we use this constantly below.

  **Terms versus tactics.**
  A proof can be written in two styles. As a *term*: a direct
  expression whose type is the statement, as in `mul_comm a b`. Or in
  *tactic mode*, after `by`: a sequence of instructions, each
  transforming the goal until nothing is left. The two are equivalent —
  tactic mode simply builds the term for you, step by step — and one
  often writes proofs whose overall shape is tactic mode with small
  terms inside.

  The `variable` command declares variables shared by several
  statements. They are added silently to any `example` or `theorem`
  that mentions them.
-/

/-
  ## Reading a Mathlib statement

  In a signature, three kinds of brackets appear, and they decide what
  *you* must supply and what Lean works out on its own.

  | Notation      | Meaning                                             |
  |---------------|-----------------------------------------------------|
  | `(a b : G)`   | **explicit** — you write them                       |
  | `{G : Type*}` | **implicit** — Lean infers them from the context    |
  | `[CommMagma G]` | **instance** — Lean looks it up in its database   |

  The instance brackets are the mechanism behind the generality
  discussed above: `[Group G]` reads "G is equipped with a group
  structure", and Lean finds that structure by itself, whether `G` is
  `ℤ`, a matrix group, or the units of a ring.

  Prefixing a name with `@` makes *everything* explicit — useful when
  Lean guesses wrong, and to see what is really going on.
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

  This is the single most important habit to acquire. The panel on the
  right — the **Infoview** — shows, at the position of your cursor,
  exactly where the proof stands: the hypotheses currently available,
  and the goal that remains. A proof is a journey through these states,
  and the Infoview is the map.

  If you do not see it: command palette (`Ctrl/Cmd+Shift+P`)
  → "Lean 4: Toggle Infoview".

  The display has two parts, separated by the turnstile `⊢`:

    P Q R : Prop      ← what is in scope, and what you may use
    hP : P            ← a hypothesis, with the name you gave it
    ⊢ P               ← the goal: what remains to be proved

  Place your cursor just after `intro hP` in the proof below, then just
  after `exact hP`, and watch the state change. Do this constantly: the
  question "what does the Infoview say?" answers most difficulties.
-/

-- (self-contained — try placing your cursor on each line in turn)
example (P : Prop) : P → P := by
  intro hP    -- ← cursor here → Infoview: P : Prop / hP : P / ⊢ P
  exact hP    -- ← cursor here → Infoview: No goals

/-
  Two things to know while Lean is thinking. Orange or yellow bars in
  the left margin mean the file is still being processed — nothing is
  wrong, Lean is simply working; wait for them to clear before trusting
  what you see. And a red underline is an error: hover over it to read
  the message, which is usually more helpful than it first appears.
-/

/-
  # How to work on this file

  The exercises are the occurrences of `sorry`, grouped in blocks
  marked `/- TODO -/ … /- END TODO -/`.

  `sorry` is a tactic that closes any goal without proving it. It is
  how one leaves a hole on purpose — and Lean flags every such hole
  with a warning, so nothing is ever silently assumed.

  - **Replace `sorry`** with your own proof, one tactic at a time,
    watching the goal change in the Infoview.
  - The proof is complete when the Infoview shows **"No goals"** and
    the warning on `sorry` disappears.
  - A bullet `·` focuses on a single subgoal — for instance after
    `constructor`, which splits a conjunction in two.
  - **Hover** over any name to see its type and its documentation.

  Solutions to every exercise are in the `Solutions/` directory.
-/

/-
  ⚠ **A word on how to solve the exercises** ⚠

  Most exercises below could be closed in one line by a single Mathlib
  lemma — which `exact?` will often find for you — or by an automation
  tactic such as `simp`, `tauto` or `aesop`.

  That is not the point. The goal here is to build proofs *by hand*,
  step by step, to get a feel for what the basic tactics do. The hints
  therefore deliberately point at *intermediate* lemmas, never at the
  one that closes the goal.

  (The one exception is the section "Searching Mathlib" in Part 2,
  where tracking down the right lemma is precisely the exercise.)
-/

/-
  ## Keyboard shortcuts — reference

  Unicode is entered by typing a backslash sequence followed by space
  or tab. You do not need to memorise this table; come back to it.

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

  Hovering over a symbol also tells you how to type it.
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

#check fun (n : ℕ) => (n : ℝ)            -- ℕ → ℝ, i.e. `Nat.cast`

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
