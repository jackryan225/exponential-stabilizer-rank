import StabilizerRank.Def
import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.Complex.Exponential
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The exact stabilizer rank: statements

This file and `StabilizerRank/Def.lean` import Mathlib only. The proofs are in the other files.
-/

universe u

namespace Challenge

open StabilizerRank

/-- **Exact stabilizer rank, all vectors.** If a vector `ψ` of finitely many qubits is not a stabilizer vector, then there is
`c > 0` such that for all `n` the `n`-th tensor power of `ψ` is not a sum of fewer than `2 ^ (c n)` stabilizer vectors. -/
theorem stabilizer_rank_exponential :
    ∀ {Q : Type} [Fintype Q] [DecidableEq Q] (ψ : (Q → ZMod 2) → ℂ), ¬ IsStabilizer Complex.I ψ →
    ∃ c : ℝ, 0 < c ∧ ∀ (n J : ℕ) (s : Fin J → (Fin n × Q → ZMod 2) → ℂ), (∀ j, IsStabilizer Complex.I (s j)) →
      (∀ b, ∏ i, ψ (fun q => b (i, q)) = ∑ j, s j b) → (2 : ℝ) ^ (c * n) ≤ J := by
  sorry

/-- The other case: the tensor powers of a stabilizer vector are stabilizer vectors. -/
theorem tensor_power : ∀ {Q : Type} [Fintype Q] [DecidableEq Q] (ψ : (Q → ZMod 2) → ℂ), IsStabilizer Complex.I ψ → ∀ n : ℕ,
    IsStabilizer Complex.I (fun b : Fin n × Q → ZMod 2 => ∏ i, ψ (fun q => b (i, q))) := by
  sorry

/-- **`T` states.** There is `c > 0` such that for all `n` the vector `(|0⟩ + e^{iπ/4} |1⟩)^{⊗ n}` is not a sum of fewer than
`2 ^ (c n)` stabilizer vectors. -/
theorem t_state :
    ∃ c : ℝ, 0 < c ∧ ∀ (n J : ℕ) (s : Fin J → (Fin n → ZMod 2) → ℂ), (∀ j, IsStabilizer Complex.I (s j)) →
      (∀ b, Complex.exp (Complex.I * (Real.pi / 4)) ^ (∑ k, (b k).val) = ∑ j, s j b) → (2 : ℝ) ^ (c * n) ≤ J := by
  sorry

/-- **`T` states over every field of characteristic not two** that has an element `ω` with `ω ^ 4 = -1`. -/
theorem t_state_field :
    ∀ (F : Type u) [Field F], (2 : F) ≠ 0 → ∀ ω : F, ω ^ 4 = -1 →
    ∃ c : ℝ, 0 < c ∧ ∀ (n J : ℕ) (s : Fin J → (Fin n → ZMod 2) → F), (∀ j, IsStabilizer (ω ^ 2) (s j)) →
      (∀ b, ω ^ (∑ k, (b k).val) = ∑ j, s j b) → (2 : ℝ) ^ (c * n) ≤ J := by
  sorry

/-- The stabilizer vectors are the vectors `a [b ∈ A] i ^ l(b) (-1) ^ q(b)` with a scalar `a`, an affine subspace `A` of the
space of bit strings, `l(b) = ∑ l_k b_k` and `q(b) = ∑ q_{km} b_k b_m` (the standard form). -/
theorem standard_form : ∀ {Q : Type} [Fintype Q] [DecidableEq Q] (ψ : (Q → ZMod 2) → ℂ), IsStabilizer Complex.I ψ ↔
    ∃ (a : ℂ) (A : AffineSubspace (ZMod 2) (Q → ZMod 2)) (l : Q → ℕ) (q : Q → Q → ℕ), ∀ b : Q → ZMod 2,
      ψ b = a * ((open Classical in if b ∈ A then 1 else 0) * (Complex.I ^ (∑ k, l k * (b k).val) *
        (-1) ^ (∑ k, ∑ m, q k m * ((b k).val * (b m).val)))) := by
  sorry

/-- **The same with the standard form of stabilizer vectors** (no definition of ours in the statement): if `ψ` is not of the
form `a [b ∈ A] i ^ l(b) (-1) ^ q(b)`, then `ψ^{⊗n}` is not a sum of fewer than `2 ^ (c n)` vectors of that form. -/
theorem stabilizer_rank_exponential_standard :
    ∀ {Q : Type} [Fintype Q] [DecidableEq Q] (ψ : (Q → ZMod 2) → ℂ),
    (¬ ∃ (a : ℂ) (A : AffineSubspace (ZMod 2) (Q → ZMod 2)) (l : Q → ℕ) (q : Q → Q → ℕ), ∀ b : Q → ZMod 2,
      ψ b = a * ((open Classical in if b ∈ A then 1 else 0) * (Complex.I ^ (∑ k, l k * (b k).val) *
        (-1) ^ (∑ k, ∑ m, q k m * ((b k).val * (b m).val))))) →
    ∃ c : ℝ, 0 < c ∧ ∀ (n J : ℕ) (a : Fin J → ℂ) (A : Fin J → AffineSubspace (ZMod 2) (Fin n × Q → ZMod 2))
      (l : Fin J → Fin n × Q → ℕ) (q : Fin J → Fin n × Q → Fin n × Q → ℕ),
      (∀ b : Fin n × Q → ZMod 2, ∏ i, ψ (fun x => b (i, x)) = ∑ j, a j * ((open Classical in if b ∈ A j then 1 else 0) *
        (Complex.I ^ (∑ k, l j k * (b k).val) * (-1) ^ (∑ k, ∑ m, q j k m * ((b k).val * (b m).val))))) →
      (2 : ℝ) ^ (c * n) ≤ J := by
  sorry

end Challenge
