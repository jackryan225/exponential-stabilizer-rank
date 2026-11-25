import StabilizerRank.Main
import StabilizerRank.Def

/-!
# The orbit of `|0…0⟩` under `H`, `S`, `CNOT` consists of quadratic phases on affine subspaces
-/

namespace StabilizerRank

open NOF

variable {F : Type*} [Field F]

section general

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W] {s : W → F}

theorem Stab.mul_phase (h : Stab s) {χ : W → F} (hχ : IsPhase χ) : Stab (fun w => χ w * s w) := by
  obtain ⟨U, w₀, c, φ, hφ, h⟩ := h
  refine ⟨U, w₀, c * χ w₀, fun v => φ v * (χ v * form χ w₀ v), hφ.mul_phase (hχ.shift w₀), fun w => ?_⟩
  beta_reduce
  rw [h]
  have e : χ w = χ w₀ * (χ (w - w₀) * form χ w₀ (w - w₀)) := by
    rw [← hχ.shift_eq, add_sub_cancel]
  rw [e]
  ring

theorem Stab.involution (h : Stab s) (E : W →ₗ[ZMod 2] W) (hE : ∀ w, E (E w) = w) : Stab (fun w => s (E w)) := by
  obtain ⟨U, w₀, c, φ, hφ, h⟩ := h
  refine ⟨U.comap E, E w₀, c, fun v => φ (E v), hφ.comp E, fun w => ?_⟩
  beta_reduce
  rw [h]
  have e : E (w - E w₀) = E w - w₀ := by rw [map_sub, hE]
  have e2 : ind F (w - E w₀ ∈ U.comap E) = ind F (E w - w₀ ∈ U) := by
    apply ind_congr
    rw [Submodule.mem_comap, e]
  rw [e2, e]

theorem Stab.smul (h : Stab s) (a : F) : Stab (fun w => a * s w) := by
  obtain ⟨U, w₀, c, φ, hφ, h⟩ := h
  refine ⟨U, w₀, a * c, φ, hφ, fun w => ?_⟩
  beta_reduce
  rw [h, mul_assoc]

/-- Substitution of affine maps. -/
theorem Stab.pull {V : Type} [AddCommGroup V] [Module (ZMod 2) V] (h : Stab s) (w₁ : W) (L : V →ₗ[ZMod 2] W) :
    Stab (fun v => s (w₁ + L v)) := by
  obtain ⟨U, w₀, c, φ, hφ, h⟩ := h
  by_cases hex : ∃ v₀, w₁ + L v₀ - w₀ ∈ U
  · obtain ⟨v₀, hv₀⟩ := hex
    refine ⟨U.comap L, v₀, c * φ (w₁ + L v₀ - w₀), fun v => φ (L v) * form φ (w₁ + L v₀ - w₀) (L v),
      (hφ.shift _).comp L, fun v => ?_⟩
    beta_reduce
    rw [h]
    have e : w₁ + L v - w₀ = (w₁ + L v₀ - w₀) + L (v - v₀) := by
      rw [map_sub]
      abel
    have e2 : ind F (w₁ + L v - w₀ ∈ U) = ind F (v - v₀ ∈ U.comap L) := by
      apply ind_congr
      rw [e, Submodule.mem_comap]
      exact U.add_mem_iff_right hv₀
    rw [e2, e, hφ.shift_eq]
    ring
  · refine ⟨⊥, 0, 0, fun _ => 1, IsPhase.one, fun v => ?_⟩
    beta_reduce
    rw [h, ind_false (fun h0 => hex ⟨v, h0⟩)]
    ring

/-- The form with an affine subspace. -/
theorem Stab.affine (h : Stab s) : ∃ (a : F) (A : AffineSubspace (ZMod 2) W) (χ : W → F), IsPhase χ ∧
    ∀ w, s w = a * (ind F (w ∈ A) * χ w) := by
  obtain ⟨U, w₀, c, φ, hφ, h⟩ := h
  refine ⟨c * φ w₀, AffineSubspace.mk' w₀ U, fun v => φ v * form φ w₀ v, hφ.shift w₀, fun w => ?_⟩
  rw [h]
  have e : ind F (w ∈ AffineSubspace.mk' w₀ U) = ind F (w - w₀ ∈ U) := by
    apply ind_congr
    rw [AffineSubspace.mem_mk', vsub_eq_sub]
  have e2 : w - w₀ = w₀ + w := by
    rw [sub_eq_iff_eq_add, add_assoc, add_comm w, ← add_assoc, add_self', zero_add]
  rw [e, e2, hφ.shift_eq]
  ring

/-- All values of the phase on the support differ by fourth roots of unity. -/
theorem Stab.ratio (h : Stab s) (u v : W) (hu : s u ≠ 0) (hv : s v ≠ 0) : s u ^ 4 = s v ^ 4 := by
  obtain ⟨a, A, χ, hχ, h⟩ := h.affine
  have h1 (w : W) (hw : s w ≠ 0) : s w = a * χ w := by
    rw [h] at hw ⊢
    by_cases hm : w ∈ A
    · rw [ind_true hm, one_mul]
    · rw [ind_false hm] at hw
      exact absurd (by ring) hw
  have h2 (w : W) : χ w ^ 4 = 1 := by
    have e : χ w ^ 4 = (χ w * χ w) * (χ w * χ w) := by ring
    rw [e, hχ.sq, hχ.form_sq]
  rw [h1 u hu, h1 v hv, mul_pow, mul_pow, h2, h2]

/-- The support is an affine subspace. -/
theorem Stab.support (h : Stab s) (u v w : W) (hu : s u ≠ 0) (hv : s v ≠ 0) (hw : s w ≠ 0) : s (u + v + w) ≠ 0 := by
  obtain ⟨U, w₀, c, φ, hφ, h⟩ := h
  have h1 (x : W) (hx : s x ≠ 0) : c ≠ 0 ∧ x - w₀ ∈ U := by
    rw [h] at hx
    constructor
    · rintro rfl
      exact hx (by ring)
    · by_contra hm
      rw [ind_false hm] at hx
      exact hx (by ring)
  have e : u + v + w - w₀ = (u - w₀) + (v - w₀) + (w - w₀) := by
    have h2 : w₀ + w₀ = 0 := add_self' w₀
    have e2 : u - w₀ + (v - w₀) + (w - w₀) = u + v + w - w₀ - (w₀ + w₀) := by abel
    rw [e2, h2, sub_zero]
  rw [h, e, ind_true (U.add_mem (U.add_mem (h1 u hu).2 (h1 v hv).2) (h1 w hw).2), one_mul]
  exact mul_ne_zero (h1 u hu).1 (hφ.ne _)

end general

section qubits

variable {Q : Type} [Fintype Q] [DecidableEq Q]

/-- The sum over the strings that agree with `w` away from `k`. -/
theorem sum_update (w : Q → Z2) (k : Q) (H : (Q → Z2) → F) :
    ∑ v, ind F (∀ j, j ≠ k → w j = v j) * H v = ∑ y : Z2, H (Function.update w k y) := by
  classical
  symm
  have inj : Function.Injective (Function.update w k) := Function.update_injective w k
  rw [← Finset.sum_image (f := H) (g := Function.update w k) (s := Finset.univ) (fun x _ y _ h => inj h)]
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image (Function.update w k)))]
  · refine Finset.sum_congr rfl fun v hv => ?_
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hv
    rw [ind_true, one_mul]
    intro j hj
    rw [Function.update_of_ne hj]
  · intro v _ hv
    rw [ind_false, zero_mul]
    intro h
    apply hv
    refine Finset.mem_image.mpr ⟨v k, Finset.mem_univ _, ?_⟩
    funext j
    by_cases hj : j = k
    · subst hj
      rw [Function.update_self]
    · rw [Function.update_of_ne hj, h j hj]

theorem sg_eq_pow (x : Z2) : sg F x = (-1) ^ x.val := by
  have : (1 : Z2).val = 1 := rfl
  rcases z2_cases x with rfl | rfl <;> simp [sg, this]

/-- The map that replaces the coordinate `k`. -/
def replace (k : Q) (U : Submodule Z2 (Q → Z2)) : U × Z2 →ₗ[Z2] (Q → Z2) where
  toFun p := Function.update p.1.1 k p.2
  map_add' p q := by
    funext j
    by_cases hj : j = k
    · subst hj
      simp
    · simp [Function.update_of_ne hj]
  map_smul' a p := by
    funext j
    by_cases hj : j = k
    · subst hj
      simp
    · simp [Function.update_of_ne hj]

theorem Stab.hadamard (h2 : (2 : F) ≠ 0) {s : (Q → Z2) → F} (h : Stab s) (k : Q) :
    Stab (fun b => s (Function.update b k 0) + (-1) ^ (b k).val * s (Function.update b k 1)) := by
  classical
  obtain ⟨U, w₀, c, φ, hφ, h⟩ := h
  let _ : Fintype U := Fintype.ofFinite U
  refine Push.stab h2 ?_
  let l : U × Z2 →ₗ[Z2] Z2 := (LinearMap.proj (R := Z2) (φ := fun _ : Q => Z2) k).comp
    (U.subtype.comp (LinearMap.fst Z2 U Z2)) + w₀ k • LinearMap.snd Z2 U Z2
  have hl (p : U × Z2) : l p = p.1.1 k + w₀ k * p.2 := rfl
  refine ⟨U × Z2, inferInstance, inferInstance, inferInstance, replace k U, Function.update w₀ k 0, c,
    fun p => φ p.1.1 * sg F (l p * p.2), ?_, fun w => ?_⟩
  · exact (hφ.comp (U.subtype.comp (LinearMap.fst Z2 U Z2))).mul_phase (isPhase_sg l (LinearMap.snd Z2 U Z2))
  · beta_reduce
    -- the sum over the fibre
    have e1 : s (Function.update w k 0) + (-1) ^ (w k).val * s (Function.update w k 1) =
        ∑ y : Z2, sg F (y * w k) * s (Function.update w k y) := by
      have a1 : sg F ((0 : Z2) * w k) = 1 := by simp [sg]
      have a2 : sg F ((1 : Z2) * w k) = (-1) ^ (w k).val := by rw [one_mul, sg_eq_pow]
      have a3 (H : Z2 → F) : ∑ y : Z2, H y = H 0 + H 1 := Fin.sum_univ_two H
      rw [a3, a1, a2, one_mul]
    have e2 : ∑ y : Z2, sg F (y * w k) * s (Function.update w k y) =
        ∑ v, ind F (∀ j, j ≠ k → w j = v j) * (sg F (v k * w k) * s v) := by
      rw [sum_update w k fun v => sg F (v k * w k) * s v]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [Function.update_self]
    rw [e1, e2, sum_shift w₀, Fintype.sum_prod_type]
    rw [sum_submodule U]
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [Finset.mul_sum, Finset.sum_eq_single (w k)]
      · have e3 : ind F (w = Function.update w₀ k 0 + replace k U (u, w k)) =
            ind F (∀ j, j ≠ k → w j = (w₀ + u.1) j) := by
          apply ind_congr
          change w = Function.update w₀ k 0 + Function.update u.1 k (w k) ↔ _
          constructor
          · intro h3 j hj
            have := congrFun h3 j
            rwa [Pi.add_apply, Function.update_of_ne hj, Function.update_of_ne hj] at this
          · intro h3
            funext j
            by_cases hj : j = k
            · subst hj
              rw [Pi.add_apply, Function.update_self, Function.update_self, zero_add]
            · rw [Pi.add_apply, Function.update_of_ne hj, Function.update_of_ne hj]
              exact h3 j hj
        have e4 : l (u, w k) * w k = (w₀ + u.1) k * w k := by
          rw [hl, Pi.add_apply]
          have : w k * w k = w k := by rcases z2_cases (w k) with h3 | h3 <;> rw [h3] <;> rfl
          calc (u.1 k + w₀ k * w k) * w k = u.1 k * w k + w₀ k * (w k * w k) := by ring
            _ = (w₀ k + u.1 k) * w k := by rw [this]; ring
        rw [e3, h, add_sub_cancel_left, ind_true u.2, one_mul]
        change _ = c * (_ * (φ u.1 * sg F (l (u, w k) * w k)))
        rw [e4]
        ring
      · intro z _ hz
        rw [ind_false, zero_mul, mul_zero]
        intro h3
        apply hz
        have := congrFun h3 k
        change w k = Function.update w₀ k 0 k + Function.update u.1 k z k at this
        rw [Function.update_self, Function.update_self, zero_add] at this
        exact this.symm
      · intro hz
        exact absurd (Finset.mem_univ _) hz
    · intro v hv
      rw [h, add_sub_cancel_left, ind_false hv]
      ring

/-- Every stabilizer vector is a quadratic phase on an affine subspace. -/
theorem stab_of_isStabilizer (h2 : (2 : F) ≠ 0) {ι : F} (hι : ι ^ 4 = 1) {s : (Q → ZMod 2) → F}
    (h : IsStabilizer ι s) : Stab s := by
  classical
  induction h with
  | zeros c =>
    refine ⟨⊥, 0, c, fun _ => 1, IsPhase.one, fun w => ?_⟩
    rw [sub_zero, mul_one, ind_congr (Submodule.mem_bot Z2), ind_eq_ite]
    by_cases hw : w = 0 <;> simp [hw]
  | hadamard k ψ _ ih => exact ih.hadamard h2 k
  | phase k ψ _ ih =>
    have e : (fun b : Q → ZMod 2 => ι ^ (b k).val * ψ b) = fun b => tg ι (b k) * ψ b := by
      funext b
      rw [tg_eq_pow]
    rw [e]
    exact ih.mul_phase ((isPhase_tg hι).comp (LinearMap.proj (R := Z2) (φ := fun _ : Q => Z2) k))
  | cnot k l hkl ψ _ ih =>
    let E : (Q → Z2) →ₗ[Z2] (Q → Z2) :=
      { toFun := fun b => Function.update b l (b l + b k)
        map_add' := fun b b' => by
          funext j
          by_cases hj : j = l
          · subst hj
            simp
            ring
          · simp [Function.update_of_ne hj]
        map_smul' := fun a b => by
          funext j
          by_cases hj : j = l
          · subst hj
            simp
            ring
          · simp [Function.update_of_ne hj] }
    refine ih.involution E fun w => ?_
    change Function.update (Function.update w l (w l + w k)) l
      (Function.update w l (w l + w k) l + Function.update w l (w l + w k) k) = w
    rw [Function.update_self, Function.update_of_ne hkl, Function.update_idem, add_assoc, add_self' (w k), add_zero,
      Function.update_eq_self]

end qubits

end StabilizerRank
