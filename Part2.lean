/-
  # Introduction to Lean: Formalizing Mathematics with Mathlib
  Summer school "Proof assistants and applications"
  IRMA, Université de Strasbourg, August 31 – September 4, 2026
  Xavier Roblot (Université Claude Bernard Lyon I)

  ## Part 2 — Algebraic structures, analysis and topology

  Algebraic structures, analysis and topology, and how to search Mathlib.

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
#synth Monoid ℝ      -- Real.instMonoid
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
