import StabilizerRank.Final

/-!
# Sanity checks of the definition
-/

namespace StabilizerRank

/-- Every basis vector is a stabilizer vector. -/
theorem basis_vector {Q : Type} [Fintype Q] [DecidableEq Q] (x : Q → ZMod 2) (c : ℂ) :
    IsStabilizer Complex.I (fun b : Q → ZMod 2 => if b = x then c else 0) := by
  have h := orbit_translate Complex.I_sq (by norm_num) (IsStabilizer.zeros (i := Complex.I) (Q := Q) c) x
  refine orbit_congr h fun b => ?_
  have : x + b = 0 ↔ b = x := by
    rw [add_eq_zero_iff_eq_neg, eq_comm]
    have e : -b = b := by
      rw [neg_eq_iff_add_eq_zero]
      exact add_self' b
    rw [e]
  simp only [this]

/-- Every vector of `n` qubits is a sum of `2 ^ n` stabilizer vectors: the theorems do not speak about an empty set of
decompositions. -/
theorem exists_decomposition (n : ℕ) (ψ : (Fin n → ZMod 2) → ℂ) : ∃ s : Fin (2 ^ n) → (Fin n → ZMod 2) → ℂ,
    (∀ j, IsStabilizer Complex.I (s j)) ∧ ∀ b, ψ b = ∑ j, s j b := by
  classical
  have e : Fintype.card (Fin n → ZMod 2) = 2 ^ n := by rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]
  let f : (Fin n → ZMod 2) ≃ Fin (2 ^ n) := Fintype.equivFinOfCardEq e
  refine ⟨fun j b => if b = f.symm j then ψ (f.symm j) else 0, fun j => basis_vector _ _, fun b => ?_⟩
  rw [← Equiv.sum_comp f]
  simp

/-- The vector `|0⟩ + |1⟩` is a stabilizer vector. -/
theorem plus_state : IsStabilizer Complex.I (fun _ : Fin 1 → ZMod 2 => (1 : ℂ)) := by
  refine orbit_congr ((IsStabilizer.zeros (i := Complex.I) (Q := Fin 1) 1).hadamard 0) fun b => ?_
  have h0 : Function.update b 0 0 = 0 := by
    funext q
    rw [Subsingleton.elim q 0, Function.update_self]
    rfl
  have h1 : Function.update b 0 (1 : ZMod 2) ≠ 0 := by
    intro h
    have := congrFun h 0
    rw [Function.update_self] at this
    exact absurd this (by decide)
  rw [if_pos h0, if_neg h1, mul_zero, add_zero]

/-- The vector `|0⟩ + e^{iπ/4} |1⟩` is not a stabilizer vector. -/
theorem t_state_not_stabilizer :
    ¬ IsStabilizer Complex.I (fun b : Fin 1 → ZMod 2 => Complex.exp (Complex.I * (Real.pi / 4)) ^ (b 0).val) := by
  intro h
  have h4 : Complex.exp (Complex.I * (Real.pi / 4)) ^ 4 = -1 := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_pi_mul_I]
    congr 1
    push_cast
    ring
  have hs := (isStabilizer_iff Complex.I_sq (by norm_num)).mp h
  have := hs.ratio (fun _ => 0) (fun _ => 1) (pow_ne_zero _ (Complex.exp_ne_zero _)) (pow_ne_zero _ (Complex.exp_ne_zero _))
  rw [val_zero, val_one, pow_zero, pow_one, h4] at this
  norm_num at this

end StabilizerRank
