import StabilizerRank.All
import StabilizerRank.Standard
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Final statements

The only hypothesis is `MatrixSpectralPlane`. It is the statement of the theorem
`OAI.LinearAlgebra.SpectralBooks.matrix_spectral_plane` of the OpenAI library, word for word.
-/

universe u

namespace StabilizerRank.Final

open OAI.LinearAlgebra.SpectralBooks

/-- The statement of `OAI.LinearAlgebra.SpectralBooks.matrix_spectral_plane`. -/
def MatrixSpectralPlane : Prop :=
  ∀ (F : Type u) [Field F], ∃ P : SpectralPlacementPrices F (EuclideanSpace ℝ (Fin 2)),
    ∀ {I : Type} [Fintype I] (T : SiteTensor.Raw.{0} I F), ConvexOn ℝ Set.univ (P.price T)

/-- **Exact stabilizer rank, all vectors.** If a vector `ψ` of finitely many qubits is not a stabilizer vector, then there is
`c > 0` such that for all `n` the `n`-th tensor power of `ψ` is not a sum of fewer than `2 ^ (c n)` stabilizer vectors. -/
theorem stabilizer_rank_exponential (plane : MatrixSpectralPlane.{0}) :
    ∀ {Q : Type} [Fintype Q] [DecidableEq Q] (ψ : (Q → ZMod 2) → ℂ), ¬ IsStabilizer Complex.I ψ →
    ∃ c : ℝ, 0 < c ∧ ∀ (n J : ℕ) (s : Fin J → (Fin n × Q → ZMod 2) → ℂ), (∀ j, IsStabilizer Complex.I (s j)) →
      (∀ b, ∏ i, ψ (fun q => b (i, q)) = ∑ j, s j b) → (2 : ℝ) ^ (c * n) ≤ J := by
  intro Q _ _ ψ hψ
  obtain ⟨P, -⟩ := plane ℂ
  exact dichotomy P ψ hψ

/-- The other case: the tensor powers of a stabilizer vector are stabilizer vectors (no hypothesis). -/
theorem tensor_power : ∀ {Q : Type} [Fintype Q] [DecidableEq Q] (ψ : (Q → ZMod 2) → ℂ), IsStabilizer Complex.I ψ → ∀ n : ℕ,
    IsStabilizer Complex.I (fun b : Fin n × Q → ZMod 2 => ∏ i, ψ (fun q => b (i, q))) :=
  fun ψ hψ n => dichotomy_easy ψ hψ n

/-- **`T` states.** There is `c > 0` such that for all `n` the vector `(|0⟩ + e^{iπ/4} |1⟩)^{⊗ n}` is not a sum of fewer than
`2 ^ (c n)` stabilizer vectors. -/
theorem t_state (plane : MatrixSpectralPlane.{0}) :
    ∃ c : ℝ, 0 < c ∧ ∀ (n J : ℕ) (s : Fin J → (Fin n → ZMod 2) → ℂ), (∀ j, IsStabilizer Complex.I (s j)) →
      (∀ b, Complex.exp (Complex.I * (Real.pi / 4)) ^ (∑ k, (b k).val) = ∑ j, s j b) → (2 : ℝ) ^ (c * n) ≤ J := by
  obtain ⟨P, -⟩ := plane ℂ
  have h4 : Complex.exp (Complex.I * (Real.pi / 4)) ^ 4 = -1 := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_pi_mul_I]
    congr 1
    push_cast
    ring
  have h2 : Complex.exp (Complex.I * (Real.pi / 4)) ^ 2 = Complex.I := by
    rw [← Complex.exp_nat_mul]
    have : ((2 : ℕ) : ℂ) * (Complex.I * (Real.pi / 4)) = Real.pi / 2 * Complex.I := by
      push_cast
      ring
    rw [this, Complex.exp_pi_div_two_mul_I]
  have := t_states P (by norm_num) h4
  rw [h2] at this
  exact this

/-- **`T` states over every field of characteristic not two** that has an element `ω` with `ω ^ 4 = -1`. -/
theorem t_state_field (plane : MatrixSpectralPlane.{u}) :
    ∀ (F : Type u) [Field F], (2 : F) ≠ 0 → ∀ ω : F, ω ^ 4 = -1 →
    ∃ c : ℝ, 0 < c ∧ ∀ (n J : ℕ) (s : Fin J → (Fin n → ZMod 2) → F), (∀ j, IsStabilizer (ω ^ 2) (s j)) →
      (∀ b, ω ^ (∑ k, (b k).val) = ∑ j, s j b) → (2 : ℝ) ^ (c * n) ≤ J := by
  intro F _ h2 ω hω
  obtain ⟨P, -⟩ := plane F
  exact t_states P h2 hω

/-- The stabilizer vectors are the vectors in standard form (no hypothesis). -/
theorem standard_form : ∀ {Q : Type} [Fintype Q] [DecidableEq Q] (ψ : (Q → ZMod 2) → ℂ), IsStabilizer Complex.I ψ ↔
    ∃ (a : ℂ) (A : AffineSubspace (ZMod 2) (Q → ZMod 2)) (l : Q → ℕ) (q : Q → Q → ℕ), ∀ b : Q → ZMod 2,
      ψ b = a * ((open Classical in if b ∈ A then 1 else 0) * (Complex.I ^ (∑ k, l k * (b k).val) *
        (-1) ^ (∑ k, ∑ m, q k m * ((b k).val * (b m).val)))) :=
  fun ψ => isStabilizer_iff_standard Complex.I_sq (by norm_num) ψ

/-- **The same with the standard form of stabilizer vectors** (no definition of ours in the statement): if `ψ` is not of the
form `a [b ∈ A] i ^ l(b) (-1) ^ q(b)`, then `ψ^{⊗n}` is not a sum of fewer than `2 ^ (c n)` vectors of that form. -/
theorem stabilizer_rank_exponential_standard (plane : MatrixSpectralPlane.{0}) :
    ∀ {Q : Type} [Fintype Q] [DecidableEq Q] (ψ : (Q → ZMod 2) → ℂ),
    (¬ ∃ (a : ℂ) (A : AffineSubspace (ZMod 2) (Q → ZMod 2)) (l : Q → ℕ) (q : Q → Q → ℕ), ∀ b : Q → ZMod 2,
      ψ b = a * ((open Classical in if b ∈ A then 1 else 0) * (Complex.I ^ (∑ k, l k * (b k).val) *
        (-1) ^ (∑ k, ∑ m, q k m * ((b k).val * (b m).val))))) →
    ∃ c : ℝ, 0 < c ∧ ∀ (n J : ℕ) (a : Fin J → ℂ) (A : Fin J → AffineSubspace (ZMod 2) (Fin n × Q → ZMod 2))
      (l : Fin J → Fin n × Q → ℕ) (q : Fin J → Fin n × Q → Fin n × Q → ℕ),
      (∀ b : Fin n × Q → ZMod 2, ∏ i, ψ (fun x => b (i, x)) = ∑ j, a j * ((open Classical in if b ∈ A j then 1 else 0) *
        (Complex.I ^ (∑ k, l j k * (b k).val) * (-1) ^ (∑ k, ∑ m, q j k m * ((b k).val * (b m).val))))) →
      (2 : ℝ) ^ (c * n) ≤ J := by
  intro Q _ _ ψ hψ
  have hψ' : ¬ IsStabilizer Complex.I ψ := fun h => hψ ((standard_form ψ).mp h)
  obtain ⟨c, hc, h⟩ := stabilizer_rank_exponential plane ψ hψ'
  refine ⟨c, hc, fun n J a A l q hb => h n J _ (fun j => (standard_form _).mpr ⟨a j, A j, l j, q j, fun b => rfl⟩) hb⟩

end StabilizerRank.Final
