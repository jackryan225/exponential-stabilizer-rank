import StabilizerRank.Reduce
import StabilizerRank.Orbit
import Mathlib.Analysis.Complex.Norm

/-!
# The exact stabilizer rank of copies of a vector, given prices in the plane
-/

namespace StabilizerRank

open Real NOF OAI OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor

variable {F : Type*} [Field F]

section powers

variable {B : Type} [AddCommGroup B] [Module Z2 B] {g : B → F}

/-- `n` copies of `g` are the sum of `J` quadratic phases on affine subspaces. -/
def Dec (g : B → F) (n J : ℕ) : Prop :=
  ∃ s : Fin J → (Fin n → B) → F, (∀ j, Stab (s j)) ∧ ∀ b, gates g (Fin n) b = ∑ j, s j b

theorem dec_bound (h : ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ J : ℕ,
      (∃ (a : Fin J → F) (A : Fin J → AffineSubspace Z2 (Fin n → B)) (χ : Fin J → (Fin n → B) → F),
        (∀ j, IsPhase (χ j)) ∧ ∀ b, gates g (Fin n) b = ∑ j, a j * (ind F (b ∈ A j) * χ j b)) →
      (2 : ℝ) ^ (c * n) ≤ J) :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ J : ℕ, Dec g n J → (2 : ℝ) ^ (c * n) ≤ J := by
  obtain ⟨c, hc, n₀, h⟩ := h
  refine ⟨c, hc, n₀, fun n hn J hJ => h n hn J ?_⟩
  obtain ⟨s, hs, hd⟩ := hJ
  choose a A χ hχ he using fun j => (hs j).affine
  refine ⟨a, A, χ, hχ, fun b => ?_⟩
  rw [hd]
  exact Finset.sum_congr rfl fun j _ => he j b

/-- Copies of a vector that is not a stabilizer vector are not a stabilizer vector. -/
theorem not_stab_gates {x₀ : B} (hx : g x₀ = 1) (hg : ¬ Stab g) {n : ℕ} (hn : 1 ≤ n) : ¬ Stab (gates g (Fin n)) := by
  classical
  intro h
  apply hg
  let i₀ : Fin n := ⟨0, hn⟩
  have h1 := h.pull (Function.update (fun _ => x₀) i₀ 0) (LinearMap.single Z2 (fun _ : Fin n => B) i₀)
  have e : (fun v : B => gates g (Fin n) (Function.update (fun _ => x₀) i₀ 0 +
      (LinearMap.single Z2 (fun _ : Fin n => B) i₀) v)) = g := by
    funext v
    rw [gates, Finset.prod_eq_single i₀]
    · rw [Pi.add_apply, Function.update_self, LinearMap.single_apply, Pi.single_eq_same, zero_add]
    · intro i _ hi
      rw [Pi.add_apply, Function.update_of_ne hi, LinearMap.single_apply, Pi.single_eq_of_ne hi, add_zero, hx]
    · intro h0
      exact absurd (Finset.mem_univ _) h0
  rwa [e] at h1

/-- The bound for all `n`. -/
theorem dec_all {x₀ : B} (hx : g x₀ = 1) (hg : ¬ Stab g)
    (h : ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ J : ℕ, Dec g n J → (2 : ℝ) ^ (c * n) ≤ J) :
    ∃ c : ℝ, 0 < c ∧ ∀ n J : ℕ, Dec g n J → (2 : ℝ) ^ (c * n) ≤ J := by
  obtain ⟨c, hc, n₀, h⟩ := h
  have hd : (0 : ℝ) < n₀ + 1 := by positivity
  refine ⟨min c (1 / (n₀ + 1)), lt_min hc (by positivity), fun n J hJ => ?_⟩
  by_cases hn : n₀ ≤ n
  · refine le_trans (rpow_le_rpow_of_exponent_le (by norm_num) ?_) (h n hn J hJ)
    exact mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg n)
  · have hn' : (n : ℝ) ≤ n₀ + 1 := by
      have : n ≤ n₀ + 1 := by omega
      exact_mod_cast this
    have hJ0 : J ≠ 0 := by
      rintro rfl
      obtain ⟨s, -, hs⟩ := hJ
      have := hs fun _ => x₀
      rw [gates, Fin.sum_univ_zero, Finset.prod_eq_one fun i _ => hx] at this
      exact one_ne_zero this
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · rw [Nat.cast_zero, mul_zero, rpow_zero]
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hJ0
    · have hJ1 : J ≠ 1 := by
        rintro rfl
        obtain ⟨s, hs, hd⟩ := hJ
        apply not_stab_gates hx hg hpos
        have e : gates g (Fin n) = s 0 := by
          funext b
          rw [hd, Fin.sum_univ_one]
        rw [e]
        exact hs 0
      have hJ2 : (2 : ℝ) ≤ J := by
        have : 2 ≤ J := by omega
        exact_mod_cast this
      refine le_trans ?_ hJ2
      calc (2 : ℝ) ^ (min c (1 / (n₀ + 1)) * n) ≤ (2 : ℝ) ^ (1 : ℝ) := by
            refine rpow_le_rpow_of_exponent_le (by norm_num) ?_
            calc min c (1 / ((n₀ : ℝ) + 1)) * n ≤ 1 / ((n₀ : ℝ) + 1) * n :=
                  mul_le_mul_of_nonneg_right (min_le_right _ _) (Nat.cast_nonneg n)
              _ ≤ 1 := by
                rw [one_div_mul_eq_div, div_le_one hd]
                exact hn'
        _ = 2 := rpow_one 2

/-- Scalar multiples of the gate. -/
theorem Dec.smul {a : F} {n J : ℕ} (h : Dec g n J) : Dec (fun x => a * g x) n J := by
  obtain ⟨s, hs, hd⟩ := h
  refine ⟨fun j b => a ^ n * s j b, fun j => (hs j).smul _, fun b => ?_⟩
  rw [gates, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Finset.mul_sum, ← hd]
  rfl

theorem Stab.power {W : Type} [AddCommGroup W] [Module Z2 W] {s : W → F} (h : Stab s) (n : ℕ) :
    Stab (fun w : Fin n → W => ∏ i, s (w i)) := by
  obtain ⟨U, w₀, c, φ, hφ, h⟩ := h
  refine ⟨Submodule.pi Set.univ fun _ => U, fun _ => w₀, c ^ n, fun v => ∏ i, φ (v i), ?_, fun w => ?_⟩
  · exact IsPhase.prod Finset.univ (fun i (v : Fin n → W) => φ (v i)) fun i _ =>
      (hφ.comp (LinearMap.proj (R := Z2) (φ := fun _ : Fin n => W) i) : IsPhase fun v : Fin n → W => φ (v i))
  · simp only [h]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Finset.prod_mul_distrib, prod_ind]
    congr 2
    apply ind_congr
    rw [Submodule.mem_pi]
    exact ⟨fun h0 i _ => h0 i, fun h0 i => h0 i (Set.mem_univ i)⟩

/-- **Every vector that is not a stabilizer vector**, over a field of complex numbers type: here over `ℂ`. -/
theorem exponential_of_not_stab (P : SpectralPlacementPrices ℂ Plane) [Fintype B] {g : B → ℂ} (hg : ¬ Stab g) :
    ∃ c : ℝ, 0 < c ∧ ∀ n J : ℕ, Dec g n J → (2 : ℝ) ^ (c * n) ≤ J := by
  classical
  have hne : ∃ x₀, g x₀ ≠ 0 := by
    by_contra hne
    push Not at hne
    apply hg
    have : g = fun _ => 0 := funext hne
    rw [this]
    exact Stab.zero
  obtain ⟨x₀, hx₀⟩ := hne
  let g' (x : B) : ℂ := (g x₀)⁻¹ * g x
  have hx : g' x₀ = 1 := inv_mul_cancel₀ hx₀
  have hg' : ¬ Stab g' := by
    intro h
    apply hg
    have e : g = fun x => g x₀ * g' x := by
      funext x
      simp only [g']
      rw [mul_inv_cancel_left₀ hx₀]
    rw [e]
    exact h.smul _
  obtain ⟨a, ha0, ha4, hrep⟩ := exists_one_bit (g := g') (by norm_num) hg'
  obtain ⟨r, hr0, hr, hrr⟩ : ∃ r : ℂ, r ≠ 0 ∧ (∀ N : ℕ, 0 < N → r ^ N ≠ 1) ∧ RepE g' (tg r) := by
    by_cases hroot : ∀ N : ℕ, 0 < N → a ^ N ≠ 1
    · exact ⟨a, ha0, hroot, hrep⟩
    · push Not at hroot
      obtain ⟨N, hN, haN⟩ := hroot
      have n1 : ‖a‖ = 1 := Complex.norm_eq_one_of_pow_eq_one haN hN.ne'
      have s1 : 1 + a ≠ 0 := by
        intro h
        apply ha4
        rw [(neg_eq_of_add_eq_zero_right h).symm]
        norm_num
      have s2 : 1 - a ≠ 0 := by
        intro h
        apply ha4
        rw [← sub_eq_zero.mp h]
        norm_num
      refine ⟨(1 - a) / (1 + a), div_ne_zero s2 s1, fun M hM hr => ?_, rep_hadamard s1 hrep⟩
      have n2 : ‖(1 - a) / (1 + a)‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hr hM.ne'
      rw [norm_div, div_eq_one_iff_eq (norm_ne_zero_iff.mpr s1)] at n2
      have n3 : Complex.normSq (1 - a) = Complex.normSq (1 + a) := by
        rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, n2]
      have n4 : Complex.normSq a = 1 := by rw [Complex.normSq_eq_norm_sq, n1, one_pow]
      rw [Complex.normSq_apply] at n4
      rw [Complex.normSq_apply, Complex.normSq_apply] at n3
      simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im] at n3
      have re0 : a.re = 0 := by nlinarith
      have im1 : a.im * a.im = 1 := by rw [re0] at n4; linarith
      apply ha4
      have e : a = (a.im : ℂ) * Complex.I := by
        apply Complex.ext
        · simp [re0]
        · simp
      rw [e, mul_pow]
      have e1 : (a.im : ℂ) ^ 4 = 1 := by
        have : a.im ^ 4 = 1 := by
          calc a.im ^ 4 = (a.im * a.im) * (a.im * a.im) := by ring
            _ = 1 := by rw [im1, one_mul]
        exact_mod_cast this
      rw [e1, Complex.I_pow_four, one_mul]
  obtain ⟨c, hc, h⟩ := dec_all hx hg' (dec_bound (rank_generic P (by norm_num) hx hr0 hr hrr))
  refine ⟨c, hc, fun n J hJ => h n J ?_⟩
  exact hJ.smul

end powers

/-! ### Blocks of qubits -/

/-- The bits in blocks. -/
def blocks (n : ℕ) (Q : Type) : (Fin n → Q → Z2) →ₗ[Z2] (Fin n × Q → Z2) where
  toFun b p := b p.1 p.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def unblocks (n : ℕ) (Q : Type) : (Fin n × Q → Z2) →ₗ[Z2] (Fin n → Q → Z2) where
  toFun b i q := b (i, q)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **The dichotomy, hard part**: if a vector of finitely many qubits is not a stabilizer vector, then its `n`-th tensor power
is not a sum of fewer than `2 ^ (c n)` stabilizer vectors. -/
theorem dichotomy (P : SpectralPlacementPrices ℂ Plane) {Q : Type} [Fintype Q] [DecidableEq Q] (ψ : (Q → ZMod 2) → ℂ)
    (hψ : ¬ IsStabilizer Complex.I ψ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (n J : ℕ) (s : Fin J → (Fin n × Q → ZMod 2) → ℂ), (∀ j, IsStabilizer Complex.I (s j)) →
      (∀ b, ∏ i, ψ (fun q => b (i, q)) = ∑ j, s j b) → (2 : ℝ) ^ (c * n) ≤ J := by
  have h2 : (2 : ℂ) ≠ 0 := by norm_num
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  have hg : ¬ Stab ψ := fun h => hψ (isStabilizer_of_stab hI h2 h)
  obtain ⟨c, hc, h⟩ := exponential_of_not_stab P hg
  refine ⟨c, hc, fun n J s hs hb => h n J ⟨fun j b => s j (blocks n Q b), fun j => ?_, fun b => ?_⟩⟩
  · have := ((isStabilizer_iff hI h2).mp (hs j)).pull 0 (blocks n Q)
    simpa only [zero_add] using this
  · exact hb (blocks n Q b)

/-- **The dichotomy, easy part**: the tensor powers of a stabilizer vector are stabilizer vectors. -/
theorem dichotomy_easy {Q : Type} [Fintype Q] [DecidableEq Q] (ψ : (Q → ZMod 2) → ℂ) (hψ : IsStabilizer Complex.I ψ)
    (n : ℕ) : IsStabilizer Complex.I (fun b : Fin n × Q → ZMod 2 => ∏ i, ψ (fun q => b (i, q))) := by
  have h2 : (2 : ℂ) ≠ 0 := by norm_num
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  refine isStabilizer_of_stab hI h2 ?_
  have := (((isStabilizer_iff hI h2).mp hψ).power n).pull 0 (unblocks n Q)
  simp only [zero_add] at this
  exact this

/-- The vector `|0⟩ + ω |1⟩` with `ω ^ 4 = -1` is not a stabilizer vector. -/
theorem not_stab_t (h2 : (2 : F) ≠ 0) {ω : F} (hω : ω ^ 4 = -1) : ¬ Stab (tg ω) := by
  intro h
  have hω0 : ω ≠ 0 := by
    rintro rfl
    norm_num at hω
  have t0 : tg ω 0 = 1 := by simp [tg]
  have t1 : tg ω 1 = ω := by simp [tg]
  have := h.ratio 0 1 (by rw [t0]; exact one_ne_zero) (by rw [t1]; exact hω0)
  rw [t0, t1, hω, one_pow] at this
  apply h2
  calc (2 : F) = 1 + 1 := by norm_num
    _ = -1 + 1 := by nth_rw 1 [this]
    _ = 0 := by norm_num

/-- **`T` states over every field of characteristic not two**: `n` copies of `|0⟩ + ω |1⟩`, `ω ^ 4 = -1`. -/
theorem t_states (P : SpectralPlacementPrices F Plane) (h2 : (2 : F) ≠ 0) {ω : F} (hω : ω ^ 4 = -1) :
    ∃ c : ℝ, 0 < c ∧ ∀ (n J : ℕ) (s : Fin J → (Fin n → ZMod 2) → F), (∀ j, IsStabilizer (ω ^ 2) (s j)) →
      (∀ b, ω ^ (∑ k, (b k).val) = ∑ j, s j b) → (2 : ℝ) ^ (c * n) ≤ J := by
  have hI : (ω ^ 2) ^ 4 = 1 := by
    rw [← pow_mul, show 2 * 4 = 4 * 2 from rfl, pow_mul, hω]
    norm_num
  obtain ⟨c, hc, h⟩ := dec_all (g := tg ω) (x₀ := 0) (by simp [tg]) (not_stab_t h2 hω)
    (dec_bound (rank_lower_bound P h2 (g := tg ω) (x₀ := 0) (by simp [tg]) (rep_and h2 hω)))
  refine ⟨c, hc, fun n J s hs hb => h n J ⟨s, fun j => stab_of_isStabilizer h2 hI (hs j), fun b => ?_⟩⟩
  rw [← hb, gates, ← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_congr rfl fun k _ => tg_eq_pow ω (b k)

end StabilizerRank
