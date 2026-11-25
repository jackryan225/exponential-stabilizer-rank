import StabilizerRank.Def
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Tactic.IntervalCases

/-!
# Bridge to the formal-conjectures target `superpolynomial_stabilizer_rank`

The definitions in namespace `FCBridge` are copied word for word from
`FormalConjectures/Arxiv/2106.03214/StabilizerRank.lean` of google-deepmind/formal-conjectures, pull request 8164
(head `b586a02bfe12389907c12cfd03121b8430e28dff`, open on 25 November 2026). `SuperpolynomialStabilizerRank` is the statement
of its theorem `superpolynomial_stabilizer_rank`.

`bridge` proves that statement from two statements of `Challenge/Statement.lean`: `t_state` and `standard_form`. Both are
proved in `StabilizerRank/Final.lean`; `standard_form` without hypothesis, `t_state` with the hypothesis `MatrixSpectralPlane`.
This file imports Mathlib and `StabilizerRank.Def` only.
-/

namespace FCBridge

open Filter Topology

/-- The computational-basis indices of $n$ qubits. -/
abbrev BitVector (n : ℕ) := Fin n → ZMod 2

/-- A linear Boolean function with coefficient vector $l$. -/
def linearValue {n : ℕ} (l x : BitVector n) : ZMod 2 := ∑ i, l i * x i

/-- A Boolean quadratic function. Diagonal coefficients also supply linear terms. -/
def quadraticValue {n : ℕ} (q : Matrix (Fin n) (Fin n) (ZMod 2))
    (x : BitVector n) : ZMod 2 := ∑ i, ∑ j, q i j * x i * x j

open scoped Classical in
/-- An unnormalized stabilizer function on the affine subspace $t+U$. -/
noncomputable def stabilizerFunction {n : ℕ} (U : Submodule (ZMod 2) (BitVector n))
    (t l : BitVector n) (q : Matrix (Fin n) (Fin n) (ZMod 2)) (x : BitVector n) : ℂ :=
  if x - t ∈ U then
    Complex.I ^ (linearValue l x).val * (-1) ^ (quadraticValue q x).val
  else 0

/-- An unnormalized quadratic-phase representative on a nonempty affine support. -/
def IsStabilizerFunction {n : ℕ} (f : BitVector n → ℂ) : Prop :=
  ∃ U t l q, f = stabilizerFunction U t l q

/-- An exact decomposition into $r$ stabilizer functions with arbitrary complex coefficients. -/
def HasStabilizerDecomposition {n : ℕ} (r : ℕ) (f : BitVector n → ℂ) : Prop :=
  ∃ (c : Fin r → ℂ) (s : Fin r → BitVector n → ℂ),
    (∀ j, IsStabilizerFunction (s j)) ∧ ∀ x, f x = ∑ j, c j * s j x

/-- The relative phase between the two amplitudes of the qubit $T$ state. -/
noncomputable def magicPhase : ℂ := Complex.exp (Real.pi * Complex.I / 4)

/-- Hamming weight of a Boolean vector. -/
def weight {n : ℕ} (x : BitVector n) : ℕ := ∑ i, (x i).val

/-- The amplitudes of $T^{\otimes n}$ with their common normalization removed. -/
noncomputable def magicState (n : ℕ) (x : BitVector n) : ℂ := magicPhase ^ weight x

/-- The statement of `superpolynomial_stabilizer_rank` (PR 8164). -/
def SuperpolynomialStabilizerRank : Prop :=
  ∀ d C : ℕ, ∃ N : ℕ, ∀ n ≥ N, ∀ r : ℕ,
    HasStabilizerDecomposition r (magicState n) → C * n ^ d < r

/-- The statement of `Challenge.t_state`. -/
def TState : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (n J : ℕ) (s : Fin J → (Fin n → ZMod 2) → ℂ),
    (∀ j, StabilizerRank.IsStabilizer Complex.I (s j)) →
    (∀ b, Complex.exp (Complex.I * (Real.pi / 4)) ^ (∑ k, (b k).val) = ∑ j, s j b) → (2 : ℝ) ^ (c * n) ≤ J

/-- The statement of `Challenge.standard_form`. -/
def StandardForm : Prop :=
  ∀ {Q : Type} [Fintype Q] [DecidableEq Q] (ψ : (Q → ZMod 2) → ℂ), StabilizerRank.IsStabilizer Complex.I ψ ↔
    ∃ (a : ℂ) (A : AffineSubspace (ZMod 2) (Q → ZMod 2)) (l : Q → ℕ) (q : Q → Q → ℕ), ∀ b : Q → ZMod 2,
      ψ b = a * ((open Classical in if b ∈ A then 1 else 0) * (Complex.I ^ (∑ k, l k * (b k).val) *
        (-1) ^ (∑ k, ∑ m, q k m * ((b k).val * (b m).val))))

/-- `i ^ (s mod 2) = i ^ s * (-1) ^ P` when `2 P + s = s * s`. -/
theorem I_pow_mod_two (s P : ℕ) (h : 2 * P + s = s * s) :
    Complex.I ^ (s % 2) = Complex.I ^ s * (-1) ^ P := by
  have h4 : s * s % 4 = s % 2 := by
    obtain ⟨r, hr⟩ : ∃ r, s % 4 = r := ⟨_, rfl⟩
    have hr4 : r < 4 := hr ▸ Nat.mod_lt s (by norm_num)
    rw [Nat.mul_mod, ← Nat.mod_mod_of_dvd s (by norm_num : 2 ∣ 4), hr]
    interval_cases r <;> rfl
  have e : Complex.I ^ s * (-1) ^ P = Complex.I ^ (s * s) := by
    rw [← Complex.I_sq, ← pow_mul, ← pow_add, ← h]
    ring_nf
  rw [e, pow_eq_pow_mod (s * s) Complex.I_pow_four, h4]

/-- `(-1) ^ z.val = (-1) ^ N` when `N` is a natural number with image `z` in `ZMod 2`. -/
theorem neg_one_pow_val {z : ZMod 2} {N : ℕ} (h : (N : ZMod 2) = z) : (-1 : ℂ) ^ z.val = (-1) ^ N := by
  rw [← h, ZMod.val_natCast, ← neg_one_pow_eq_pow_mod_two]

/-- The phase of a stabilizer function of PR 8164, in the standard form of `Challenge.standard_form`. -/
theorem phase_eq {n : ℕ} (l x : BitVector n) (q : Matrix (Fin n) (Fin n) (ZMod 2)) :
    Complex.I ^ (linearValue l x).val * (-1) ^ (quadraticValue q x).val =
      Complex.I ^ (∑ k, (l k).val * (x k).val) *
        (-1) ^ (∑ k, ∑ m, ((q k m).val + if k < m then (l k).val * (l m).val else 0) * ((x k).val * (x m).val)) := by
  obtain ⟨a, ha_def⟩ : ∃ a : Fin n → ℕ, ∀ k, a k = (l k).val * (x k).val := ⟨_, fun _ => rfl⟩
  have hval : ∀ z : ZMod 2, z.val ≤ 1 := fun z => Nat.lt_succ_iff.mp (ZMod.val_lt z)
  have ha : ∀ k, a k * a k = a k := by
    intro k
    have h1 := hval (l k)
    have h2 := hval (x k)
    rw [ha_def]
    interval_cases (l k).val <;> interval_cases (x k).val <;> rfl
  obtain ⟨s, hs⟩ : ∃ s, s = ∑ k, a k := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P, P = ∑ k, ∑ m, (if k < m then a k * a m else 0) := ⟨_, rfl⟩
  -- 2 P + s = s * s
  have hsplit : ∀ k m : Fin n, a k * a m =
      (if k < m then a k * a m else 0) + (if m < k then a m * a k else 0) + (if m = k then a m else 0) := by
    intro k m
    rcases lt_trichotomy k m with h | h | h
    · simp [h, h.ne', not_lt.mpr h.le]
    · subst h; simp [ha]
    · simp [h, h.ne, not_lt.mpr h.le, mul_comm]
  have hss : s * s = 2 * P + s := by
    have e1 : s * s = ∑ k, ∑ m, ((if k < m then a k * a m else 0) + (if m < k then a m * a k else 0) +
        (if m = k then a m else 0)) := by
      rw [hs, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun m _ => hsplit k m
    have e2 : ∑ k : Fin n, ∑ m : Fin n, (if m < k then a m * a k else 0) = P := by
      rw [hP, Finset.sum_comm]
    have e3 : ∑ k : Fin n, ∑ m : Fin n, (if m = k then a m else 0) = s := by
      rw [hs]
      exact Finset.sum_congr rfl fun k _ => by simp
    simp only [Finset.sum_add_distrib] at e1
    rw [e1, e2, e3, ← hP]
    ring
  -- the linear part
  have hs' : ∑ k, (l k).val * (x k).val = s := by
    rw [hs]
    exact Finset.sum_congr rfl fun k _ => (ha_def k).symm
  have hlin : ((s : ℕ) : ZMod 2) = linearValue l x := by
    rw [← hs']
    simp [linearValue, ZMod.natCast_val, ZMod.cast_id']
  -- the quadratic part
  have hquad : ((∑ k, ∑ m, (q k m).val * ((x k).val * (x m).val) : ℕ) : ZMod 2) = quadraticValue q x := by
    simp [quadraticValue, ZMod.natCast_val, ZMod.cast_id', mul_assoc]
  have hsplitq : (∑ k, ∑ m, ((q k m).val + if k < m then (l k).val * (l m).val else 0) * ((x k).val * (x m).val)) =
      (∑ k, ∑ m, (q k m).val * ((x k).val * (x m).val)) + P := by
    rw [hP, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [ha_def k, ha_def m]
    split_ifs <;> ring
  rw [neg_one_pow_val hquad, hsplitq, pow_add, ← hlin, ZMod.val_natCast, I_pow_mod_two s P hss.symm, hs']
  ring

/-- Exponential beats polynomial. -/
theorem eventually_lt_two_rpow {c : ℝ} (hc : 0 < c) (d C : ℕ) :
    ∃ N : ℕ, ∀ n ≥ N, ((C * n ^ d : ℕ) : ℝ) < (2 : ℝ) ^ (c * n) := by
  have hb : 1 < (2 : ℝ) ^ c := Real.one_lt_rpow (by norm_num) hc
  have ht := (tendsto_pow_const_div_const_pow_of_one_lt d hb).eventually
    (gt_mem_nhds (show (0 : ℝ) < 1 / ((C : ℝ) + 1) by positivity))
  obtain ⟨N, hN⟩ := eventually_atTop.mp ht
  refine ⟨N, fun n hn => ?_⟩
  have h1 := hN n hn
  have hpos : 0 < ((2 : ℝ) ^ c) ^ n := by positivity
  have h2 : (n : ℝ) ^ d * ((C : ℝ) + 1) < ((2 : ℝ) ^ c) ^ n := by
    rw [div_lt_div_iff₀ hpos (by positivity)] at h1
    linarith
  have h3 : ((2 : ℝ) ^ c) ^ n = (2 : ℝ) ^ (c * n) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  push_cast
  nlinarith [pow_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) d]

/-- **Bridge.** `t_state` and `standard_form` of `Challenge/Statement.lean` imply the formal-conjectures statement
`superpolynomial_stabilizer_rank` as written in pull request 8164. -/
theorem bridge (hT : TState) (hS : StandardForm) : SuperpolynomialStabilizerRank := by
  obtain ⟨c, hc, hbound⟩ := hT
  intro d C
  obtain ⟨N, hN⟩ := eventually_lt_two_rpow hc d C
  refine ⟨N, fun n hn r ⟨coef, s, hs, hsum⟩ => ?_⟩
  choose U t l q hfun using hs
  -- each term is a stabilizer vector of `StabilizerRank.Def`
  have hstab : ∀ j, StabilizerRank.IsStabilizer Complex.I (fun x => coef j * s j x) := by
    intro j
    have hA : ∀ b, b ∈ AffineSubspace.mk' (t j) (U j) ↔ b - t j ∈ U j := fun b => by
      rw [AffineSubspace.mem_mk', vsub_eq_sub]
    refine (hS _).mpr ⟨coef j, AffineSubspace.mk' (t j) (U j), fun k => (l j k).val,
      fun k m => (q j k m).val + if k < m then (l j k).val * (l j m).val else 0, fun b => ?_⟩
    rw [hfun j, stabilizerFunction]
    by_cases hb : b - t j ∈ U j
    · rw [if_pos hb, if_pos ((hA b).mpr hb), phase_eq]; ring
    · rw [if_neg hb, if_neg fun h => hb ((hA b).mp h)]; ring
  have hJ := hbound n r (fun j x => coef j * s j x) hstab (fun b => by
    rw [← hsum b, magicState, magicPhase, weight]
    congr 2
    ring)
  exact_mod_cast (hN n hn).trans_le hJ

end FCBridge

#print axioms FCBridge.bridge
