/-
  # Introduction to Lean: Formalizing Mathematics with Mathlib
  Summer school "Proof assistants and applications"
  IRMA, Université de Strasbourg, August 31 – September 4, 2026
  Xavier Roblot (Université Claude Bernard Lyon I)

  ## Part 2 — Algebraic structures, analysis and topology — SOLUTIONS

  (This file mirrors `Part2.lean`: one solution per `sorry`
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

/- # Algebraic structures -/

/- ## Groups -/

-- Trivial kernel if injective
example {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) (a : G) (h : f a = 1) : a = 1 := by
  apply hf
  rw [h, map_one f]

-- (ab)^n = a^n * b^n in a commutative monoid
example {M : Type*} [CommMonoid M] (a b : M) (n : ℕ) :
    (a * b) ^ n = a ^ n * b ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ (a * b), ih, pow_succ a, pow_succ b]
    exact mul_mul_mul_comm (a ^ n) (b ^ n) a b

-- Exponent-2 group ⟹ commutative
example {G : Type*} [Group G] (h : ∀ a : G, a ^ 2 = 1) (a b : G) :
    a * b = b * a := by
  have hself : ∀ x : G, x⁻¹ = x := by
    intro x
    have hx : x * x = 1 := by have := h x; rwa [pow_two] at this
    exact Eq.symm (eq_inv_of_mul_eq_one_left hx)
  calc a * b = (a * b)⁻¹ := Eq.symm (hself (a * b))
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by rw [hself a, hself b]

-- The preimage of a subgroup preserves inclusion
example {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (S T : Subgroup H) (hST : S ≤ T) : S.comap φ ≤ T.comap φ := by
  intro x hx
  rw [Subgroup.mem_comap] at hx ⊢
  exact hST hx

/- ## Rings and fields -/

-- Factorization of a³ - b³
example {R : Type*} [CommRing R] (a b : R) :
    a ^ 3 - b ^ 3 = (a - b) * (a ^ 2 + a * b + b ^ 2) := by ring

-- (a⁻¹)⁻¹ = a for a ≠ 0
example {K : Type*} [Field K] (a : K) (ha : a ≠ 0) : (a⁻¹)⁻¹ = a := by
  apply mul_left_cancel₀ (inv_ne_zero ha)
  rw [mul_inv_cancel₀ (inv_ne_zero ha), inv_mul_cancel₀ ha]

-- Cancellation in a field
example {K : Type*} [Field K] (a b c : K) (ha : a ≠ 0)
    (h : a * b = a * c) : b = c := by
  have key : a⁻¹ * (a * b) = a⁻¹ * (a * c) := congr_arg (a⁻¹ * ·) h
  rwa [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ ha, one_mul,
    one_mul] at key

-- The units of ℤ are exactly ±1 (a bit harder)
example (x : ℤˣ) : (x : ℤ) = 1 ∨ (x : ℤ) = -1 := by
  -- ↑x divides 1 (witness ↑x⁻¹), so ↑x is a unit of ℤ, hence ↑x = ±1
  have hdvd : (↑x : ℤ) ∣ 1 := ⟨↑x⁻¹, Eq.symm (Units.mul_inv x)⟩
  exact Int.isUnit_iff.mp (isUnit_of_dvd_one hdvd)

/- # Analysis and topology -/

/- ## Continuity -/

example : Continuous (fun x : ℝ ↦ Real.cos x + x ^ 2) := by fun_prop

example {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x ↦ f x * g x) :=
  Continuous.mul hf hg

/- ## Derivatives -/

-- A sum of differentiable functions is differentiable
-- (`fun_prop` also works)
example : Differentiable ℝ (fun x : ℝ ↦ x ^ 3 + x) :=
  Differentiable.add (differentiable_pow 3) differentiable_id

example : deriv (fun x : ℝ ↦ x ^ 2) = fun x ↦ 2 * x := by
  ext x; simp [mul_comm]

/- ## Topology -/

example {f : ℝ → ℝ} (hf : Continuous f) {s : Set ℝ}
    (hs : IsClosed s) : IsClosed (f ⁻¹' s) :=
  IsClosed.preimage hf hs

example {f : ℝ → ℝ} (hf : Continuous f) {s : Set ℝ}
    (hs : IsCompact s) : IsCompact (f '' s) :=
  IsCompact.image hs hf

-- Bolzano: a continuous function that changes sign on [0, 1]
-- has a zero there
example (f : ℝ → ℝ) (hf : Continuous f) (h0 : f 0 < 0)
    (h1 : 0 < f 1) : ∃ x ∈ Set.Icc (0 : ℝ) 1, f x = 0 := by
  -- the IVT: [f 0, f 1] is contained in the image of [0, 1]
  have hsub := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1)
    (Continuous.continuousOn hf)
  -- 0 lies in [f 0, f 1] since f 0 < 0 < f 1
  have h0mem : (0 : ℝ) ∈ Set.Icc (f 0) (f 1) :=
    Set.mem_Icc.mpr ⟨le_of_lt h0, le_of_lt h1⟩
  -- so 0 is in the image: extract a preimage point
  obtain ⟨x, hx, hfx⟩ := hsub h0mem
  exact ⟨x, hx, hfx⟩

/- # Searching Mathlib -/

example (a b c : ℤ) (h1 : a ∣ b) (h2 : b ∣ c) : a ∣ c :=
  dvd_trans h1 h2

example (a b : ℕ) : Nat.gcd a b * Nat.lcm a b = a * b :=
  Nat.gcd_mul_lcm a b

example : Irrational Real.pi :=
  irrational_pi

example : FermatLastTheoremFor 3 :=
  fermatLastTheoremThree
