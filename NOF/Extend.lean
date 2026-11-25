import NOF.Free
import OAI.LinearAlgebra.SpectralBooks.FiniteIntervalExtension
import OAI.LinearAlgebra.SpectralBooks.SpectralExtension

/-!
# Adding one party

A spectral point extends to one more party with a bound on the price of a new tensor, if the old prices of all
contractions of its powers are bounded.
-/

namespace NOF

open Real OAI OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open scoped NNReal

variable {I : Type} {K : Type*} [Fintype I] [Nontrivial I] [Field K]

/-- The logarithmic price of the binary diagonal is one. -/
theorem logPoint_fullBinary (f : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} (Option I) K → _ → Prop)) :
    logPoint f (intervalFullBinary : NonzeroProduct.{0} (Option I) K) = 1 := by
  change Real.logb 2 (f.val (2 : TensorClass.{0} (Option I) K) : ℝ) = 1
  have : f.val (2 : TensorClass.{0} (Option I) K) = 2 := map_ofNat (normalizedSpectrum.toRingHom f) 2
  rw [this]
  norm_num

theorem classContractionPrice_nonneg (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I K → _ → Prop))
    (X : TensorClass.{0} (Option I) K) : 0 ≤ classContractionPrice φ X := by
  induction X using Quotient.inductionOn with
  | h X => exact contractionPrice_nonneg φ X

/-- One more party with a bound on the price of `U`. -/
theorem exists_extension (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I K → _ → Prop))
    (U : NonzeroProduct.{0} (Option I) K) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ m : ℕ, classContractionPrice φ (classOfProduct (m • U)) ≤ m * c) :
    ∃ f : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} (Option I) K → _ → Prop),
      (∀ X, logPoint f (embedOldProduct X) = logPoint φ X) ∧ logPoint f U ≤ c := by
  classical
  let E : (NonzeroProduct.{0} I K × ℕ × ℕ) →+ NonzeroProduct.{0} (Option I) K :=
    AddMonoidHom.coprod embedOldProduct
      (AddMonoidHom.coprod (multiplesHom _ U) (multiplesHom _ intervalFullBinary))
  let target : (NonzeroProduct.{0} I K × ℕ × ℕ) →+ ℝ :=
    AddMonoidHom.coprod (logPoint φ) (AddMonoidHom.coprod (multiplesHom ℝ c) (multiplesHom ℝ 1))
  let G : AddSubmonoid (NonzeroProduct.{0} I K × ℕ × ℕ) :=
    { carrier := {x | x.2.1 = 0}
      zero_mem' := rfl
      add_mem' := by
        intro a b ha hb
        have ha' : a.2.1 = 0 := ha
        have hb' : b.2.1 = 0 := hb
        change a.2.1 + b.2.1 = 0
        rw [ha', hb'] }
  have hE (X : NonzeroProduct.{0} I K) (m k : ℕ) : E (X, m, k) = embedOldProduct X + (m • U + k • intervalFullBinary) := by
    simp [E]
  have hT (X : NonzeroProduct.{0} I K) (m k : ℕ) : target (X, m, k) = logPoint φ X + (m * c + k) := by
    simp [target]
  -- the contraction price of a product
  have split (X : NonzeroProduct.{0} I K) (m k : ℕ) : classContractionPrice φ (classOfProduct (E (X, m, k))) =
      logPoint φ X + (classContractionPrice φ (classOfProduct (m • U)) + k) := by
    rw [hE, classContractionPrice_embedOldProduct_add]
    congr 1
    have hd : classOfProduct (m • U + k • (intervalFullBinary : NonzeroProduct.{0} (Option I) K)) =
        (((2 ^ k : ℕ) : TensorClass.{0} (Option I) K)) * classOfProduct (m • U) := by
      change classOfProduct (m • U) * (2 : TensorClass.{0} (Option I) K) ^ k = _
      rw [Nat.cast_pow, Nat.cast_ofNat, mul_comm]
    rw [hd, classContractionPrice_natCast_mul φ (pow_pos (by decide : 0 < 2) _) (m • U).toMul.property, add_comm]
    simp only [Nat.cast_pow, Nat.cast_ofNat, Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one]
  obtain ⟨f, hle, heq⟩ := spectral_extension_of_contraction_bounds (I := Option I) E target G
    (fun x => classContractionPrice φ (classOfProduct x))
    (fun h => classContractionPrice_mono φ h)
    (by
      rintro ⟨X, m, k⟩
      change classContractionPrice φ (classOfProduct (E (X, m, k))) ≤ target (X, m, k)
      rw [split, hT]
      have := h m
      linarith)
    (by
      rintro ⟨X, m, k⟩ hx
      have hm : m = 0 := hx
      subst hm
      change target (X, 0, k) ≤ classContractionPrice φ (classOfProduct (E (X, 0, k)))
      rw [split, hT]
      have := classContractionPrice_nonneg φ (classOfProduct (0 • U))
      push_cast
      linarith)
    (by
      rintro ⟨X, m, k⟩
      rw [hT]
      have := spectralLogHom_nonneg unit_le_nonzeroClass φ X
      positivity)
    (fun x L z hx => classContractionPrice_ordinary_sum φ x L z hx)
    (0, 0, 1) rfl (by rw [hT]; simp)
    (fun f => by rw [hE]; simp [logPoint_fullBinary])
  refine ⟨f, fun X => ?_, ?_⟩
  · have := heq (X, 0, 0) rfl
    rw [hE, hT] at this
    simpa using this
  · have := hle (0, 1, 0)
    rw [hE, hT] at this
    simpa using this

end NOF
