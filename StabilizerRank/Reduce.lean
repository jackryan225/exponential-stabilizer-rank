import StabilizerRank.Dense

/-!
# A vector that is not a stabilizer vector represents such a vector of one qubit
-/

namespace StabilizerRank

open NOF

variable {F : Type*} [Field F] {B : Type} [AddCommGroup B] [Module Z2 B] {g : B → F}

section closure

variable {W : Type} [AddCommGroup W] [Module Z2 W] [Fintype W]

theorem RepE.phase {φ : W → F} (hφ : IsPhase φ) : RepE g φ := by
  refine ⟨Empty, inferInstance, (Rep.direct hφ (0 : Empty → B) 0).congr fun w => ?_⟩
  simp [gates]

omit [Fintype W] in
theorem RepE.translate {f : W → F} (h : RepE g f) (w₁ : W) : RepE g (fun w => f (w₁ + w)) := by
  obtain ⟨S, i, V, i1, i2, i3, ι, w₀, c, φ, L, b, hφ, h⟩ := h
  refine ⟨S, i, V, i1, i2, i3, ι, w₀ - w₁, c, φ, L, b, hφ, fun w => ?_⟩
  beta_reduce
  rw [h]
  congr 1
  refine Finset.sum_congr rfl fun v _ => ?_
  congr 1
  apply ind_congr
  rw [sub_add_eq_add_sub, eq_sub_iff_add_eq, add_comm w]

/-- Substitution of affine maps. -/
theorem RepE.subst {V : Type} [AddCommGroup V] [Module Z2 V] [Fintype V] {f : W → F} (h : RepE g f) (w₁ : W)
    (L : V →ₗ[Z2] W) : RepE g (fun v => f (w₁ + L v)) :=
  RepE.pull (h.translate w₁) L

theorem isPhase_eps {ε : F} (h : ε * ε = 1) (l m : W →ₗ[Z2] Z2) : IsPhase (fun w => tg ε (l w * m w)) := by
  rcases mul_self_eq_one_iff.mp h with rfl | rfl
  · have : (fun w => tg (1 : F) (l w * m w)) = fun _ => 1 := by
      funext w
      simp [tg]
    rw [this]
    exact IsPhase.one
  · exact isPhase_sg l m

/-- The gate itself. -/
theorem RepE.self [Fintype B] : RepE g g := by
  refine ⟨Unit, inferInstance, (Rep.direct (g := g) (IsPhase.one (F := F) (W := B)) (0 : Unit → B)
    (LinearMap.pi fun _ => LinearMap.id)).congr fun w => ?_⟩
  simp [gates]

/-- The sum over one bit. -/
theorem RepE.sumBit {f : W × Z2 → F} (h : RepE g f) : RepE g (fun w => f (w, 0) + f (w, 1)) := by
  classical
  refine (h.push (LinearMap.fst Z2 W Z2)).congr fun w => ?_
  rw [Fintype.sum_prod_type, Finset.sum_eq_single w]
  · have a3 (H : Z2 → F) : ∑ y : Z2, H y = H 0 + H 1 := Fin.sum_univ_two H
    rw [a3, ind_true (p := w = (LinearMap.fst Z2 W Z2) (w, 0)) rfl, ind_true (p := w = (LinearMap.fst Z2 W Z2) (w, 1)) rfl,
      one_mul, one_mul]
  · intro u _ hu
    refine Finset.sum_eq_zero fun y _ => ?_
    rw [ind_false, zero_mul]
    exact fun h0 => hu h0.symm
  · intro hw
    exact absurd (Finset.mem_univ _) hw

end closure

section reduce

variable (h30 : (30 : F) ≠ 0) (H : ∀ f : Z2 → F, RepE g f → f 0 ≠ 0 → f 1 ≠ 0 → f 0 ^ 4 = f 1 ^ 4)

variable {W : Type} [AddCommGroup W] [Module Z2 W] [Fintype W]

include H in
/-- Two points. -/
theorem line {h : W → F} (hh : RepE g h) {x y : W} (hx : h x ≠ 0) (hy : h y ≠ 0) : h x ^ 4 = h y ^ 4 := by
  have h1 := H _ (hh.subst x (LinearMap.toSpanSingleton Z2 W (x + y)))
  have e0 : x + (LinearMap.toSpanSingleton Z2 W (x + y)) 0 = x := by rw [map_zero, add_zero]
  have e1 : x + (LinearMap.toSpanSingleton Z2 W (x + y)) 1 = y := by
    rw [LinearMap.toSpanSingleton_apply, one_smul, ← add_assoc, add_self', zero_add]
  rw [e0, e1] at h1
  exact h1 hx hy

include h30 H in
/-- Four points. -/
theorem plane {f : Z2 × Z2 → F} (hf : RepE g f) (h00 : f (0, 0) ≠ 0) (h10 : f (1, 0) ≠ 0) (h01 : f (0, 1) ≠ 0) :
    f (1, 1) * f (0, 0) = f (1, 0) * f (0, 1) ∨ f (1, 1) * f (0, 0) = -(f (1, 0) * f (0, 1)) := by
  classical
  have h2 : (2 : F) ≠ 0 := by
    intro h
    apply h30
    calc (30 : F) = 2 * 15 := by norm_num
      _ = 0 := by rw [h, zero_mul]
  have h15 : (15 : F) ≠ 0 := by
    intro h
    apply h30
    calc (30 : F) = 2 * 15 := by norm_num
      _ = 0 := by rw [h, mul_zero]
  have h20 : (20 : F) ≠ 0 := by
    intro h
    have h5 : (5 : F) ≠ 0 := by
      intro h
      apply h30
      calc (30 : F) = 6 * 5 := by norm_num
        _ = 0 := by rw [h, mul_zero]
    have : (20 : F) = 2 * 2 * 5 := by norm_num
    rw [this] at h
    exact mul_ne_zero (mul_ne_zero h2 h2) h5 h
  set a := f (0, 0) with ha
  set b := f (1, 0) with hb
  set c := f (0, 1) with hc
  set d := f (1, 1) with hd
  have hb4 : b ^ 4 = a ^ 4 := line H hf h10 h00
  have hc4 : c ^ 4 = a ^ 4 := line H hf h01 h00
  have pb : (a / b) ^ 4 = 1 := by rw [div_pow, hb4, div_self (pow_ne_zero 4 h00)]
  have pc : (a / c) ^ 4 = 1 := by rw [div_pow, hc4, div_self (pow_ne_zero 4 h00)]
  have hp : IsPhase (fun w : Z2 × Z2 => tg (a / b) w.1 * tg (a / c) w.2) :=
    ((isPhase_tg pb).comp (LinearMap.fst Z2 Z2 Z2)).mul_phase ((isPhase_tg pc).comp (LinearMap.snd Z2 Z2 Z2))
  have hk := ((RepE.phase (g := g) hp).mul hf).smul a⁻¹
  set τ := d * a / (b * c) with hτ
  have t0 (κ : F) : tg κ 0 = 1 := by simp [tg]
  have t1 (κ : F) : tg κ 1 = κ := by simp [tg]
  have k00 : a⁻¹ * (tg (a / b) (0 : Z2) * tg (a / c) (0 : Z2) * f (0, 0)) = 1 := by
    rw [t0, t0, ← ha]
    field_simp
  have k10 : a⁻¹ * (tg (a / b) (1 : Z2) * tg (a / c) (0 : Z2) * f (1, 0)) = 1 := by
    rw [t0, t1, ← hb]
    field_simp
  have k01 : a⁻¹ * (tg (a / b) (0 : Z2) * tg (a / c) (1 : Z2) * f (0, 1)) = 1 := by
    rw [t0, t1, ← hc]
    field_simp
  have k11 : a⁻¹ * (tg (a / b) (1 : Z2) * tg (a / c) (1 : Z2) * f (1, 1)) = τ := by
    rw [t1, t1, ← hd, hτ]
    field_simp
  have hs := H _ hk.sumBit
  simp only [k00, k10, k01, k11] at hs
  have goal : τ = 1 ∨ τ = -1 := by
    by_cases hτ0 : τ = 0
    · exfalso
      rw [hτ0] at hs
      have := hs (by norm_num; exact h2) (by norm_num)
      apply h15
      have e : (15 : F) = (1 + 1) ^ 4 - (1 + 0) ^ 4 := by norm_num
      rw [e, this, sub_self]
    · have hτ4 : τ ^ 4 = 1 := by
        have := line H hk (x := (1, 1)) (y := (0, 0))
        beta_reduce at this
        rw [k00, k11, one_pow] at this
        exact this hτ0 one_ne_zero
      by_contra hne
      push Not at hne
      have hs2 : τ ^ 2 = -1 := by
        have e : (τ - 1) * ((τ + 1) * (τ ^ 2 + 1)) = 0 := by
          have : (τ - 1) * ((τ + 1) * (τ ^ 2 + 1)) = τ ^ 4 - 1 := by ring
          rw [this, hτ4, sub_self]
        rcases mul_eq_zero.mp e with e | e
        · exact absurd (sub_eq_zero.mp e) hne.1
        · rcases mul_eq_zero.mp e with e | e
          · exact absurd (eq_neg_of_add_eq_zero_left e) hne.2
          · exact eq_neg_of_add_eq_zero_left e
      have e4 : (1 + τ) ^ 4 = -4 := by
        have : (1 + τ) ^ 4 = (1 + τ ^ 2 + 2 * τ) ^ 2 := by ring
        rw [this, hs2]
        have : ((1 : F) + -1 + 2 * τ) ^ 2 = 4 * τ ^ 2 := by ring
        rw [this, hs2]
        ring
      have h4 : (4 : F) ≠ 0 := by
        have : (4 : F) = 2 * 2 := by norm_num
        rw [this]
        exact mul_ne_zero h2 h2
      have n1 : (1 : F) + τ ≠ 0 := by
        intro h0
        rw [h0] at e4
        apply h4
        have : (4 : F) = -(0 ^ 4) := by
          rw [e4]
          ring
        rw [this]
        norm_num
      have := hs (by norm_num; exact h2) n1
      rw [e4] at this
      apply h20
      have e : (20 : F) = (1 + 1) ^ 4 - (-4) := by norm_num
      rw [e, this, sub_self]
  have hbc : b * c ≠ 0 := mul_ne_zero h10 h01
  rcases goal with h1 | h1
  · left
    rw [hτ, div_eq_iff hbc, one_mul] at h1
    exact h1
  · right
    rw [hτ, div_eq_iff hbc, neg_one_mul] at h1
    exact h1

/-- The map of three bits. -/
def span3 (u v w : W) : Z2 × Z2 × Z2 →ₗ[Z2] W :=
  (LinearMap.toSpanSingleton Z2 W u).comp (LinearMap.fst Z2 Z2 (Z2 × Z2)) +
    ((LinearMap.toSpanSingleton Z2 W v).comp ((LinearMap.fst Z2 Z2 Z2).comp (LinearMap.snd Z2 Z2 (Z2 × Z2))) +
      (LinearMap.toSpanSingleton Z2 W w).comp ((LinearMap.snd Z2 Z2 Z2).comp (LinearMap.snd Z2 Z2 (Z2 × Z2))))

omit [Fintype W] in
theorem span3_apply (u v w : W) (p : Z2 × Z2 × Z2) : span3 u v w p = p.1 • u + (p.2.1 • v + p.2.2 • w) := rfl

/-- The map of two bits. -/
def span2 (u v : W) : Z2 × Z2 →ₗ[Z2] W :=
  (LinearMap.toSpanSingleton Z2 W u).comp (LinearMap.fst Z2 Z2 Z2) +
    (LinearMap.toSpanSingleton Z2 W v).comp (LinearMap.snd Z2 Z2 Z2)

omit [Fintype W] in
theorem span2_apply (u v : W) (p : Z2 × Z2) : span2 u v p = p.1 • u + p.2 • v := rfl

include h30 H in
/-- Four points of an affine plane. -/
theorem plane' {h : W → F} (hh : RepE g h) (x u v : W) (hx : h x ≠ 0) (hu : h (x + u) ≠ 0) (hv : h (x + v) ≠ 0) :
    h (x + (u + v)) * h x = h (x + u) * h (x + v) ∨ h (x + (u + v)) * h x = -(h (x + u) * h (x + v)) := by
  have h1 := plane h30 H (hh.subst x (span2 u v))
  simp only [span2_apply, zero_smul, one_smul, add_zero, zero_add] at h1
  exact h1 hx hu hv

include h30 H in
/-- The support is an affine subspace. -/
theorem support' {h : W → F} (hh : RepE g h) (x u v : W) (hx : h x ≠ 0) (hu : h (x + u) ≠ 0) (hv : h (x + v) ≠ 0) :
    h (x + (u + v)) ≠ 0 := by
  intro h0
  rcases plane' h30 H hh x u v hx hu hv with h1 | h1
  · rw [h0, zero_mul] at h1
    exact mul_ne_zero hu hv h1.symm
  · rw [h0, zero_mul, zero_eq_neg] at h1
    exact mul_ne_zero hu hv h1

include h30 H in
/-- Eight points: the third difference is trivial. -/
theorem cube {h : W → F} (hh : RepE g h) (x u v w : W) (hx : h x = 1) (hu : h (x + u) ≠ 0) (hv : h (x + v) ≠ 0)
    (hw : h (x + w) ≠ 0) : h (x + (u + (v + w))) * (h (x + u) * h (x + v) * h (x + w)) =
      h (x + (u + v)) * h (x + (u + w)) * h (x + (v + w)) := by
  classical
  have h2 : (2 : F) ≠ 0 := by
    intro h
    apply h30
    calc (30 : F) = 2 * 15 := by norm_num
      _ = 0 := by rw [h, zero_mul]
  have hx0 : h x ≠ 0 := by rw [hx]; exact one_ne_zero
  have huv := support' h30 H hh x u v hx0 hu hv
  have huw := support' h30 H hh x u w hx0 hu hw
  have hvw := support' h30 H hh x v w hx0 hv hw
  set a1 := h (x + u)
  set a2 := h (x + v)
  set a3 := h (x + w)
  set a12 := h (x + (u + v))
  set a13 := h (x + (u + w))
  set a23 := h (x + (v + w))
  set a := h (x + (u + (v + w)))
  have q1 : a1 ^ 4 = 1 := by rw [line H hh hu hx0, hx, one_pow]
  have q2 : a2 ^ 4 = 1 := by rw [line H hh hv hx0, hx, one_pow]
  have q3 : a3 ^ 4 = 1 := by rw [line H hh hw hx0, hx, one_pow]
  have i1 : (a1⁻¹) ^ 4 = 1 := by rw [inv_pow, q1, inv_one]
  have i2 : (a2⁻¹) ^ 4 = 1 := by rw [inv_pow, q2, inv_one]
  have i3 : (a3⁻¹) ^ 4 = 1 := by rw [inv_pow, q3, inv_one]
  have eps {p q r : F} (hp : p ≠ 0) (hq : q ≠ 0) (hr : r * h x = p * q ∨ r * h x = -(p * q)) :
      (r / (p * q)) * (r / (p * q)) = 1 := by
    rw [hx, mul_one] at hr
    have hpq := mul_ne_zero hp hq
    rcases hr with rfl | rfl
    · rw [div_self hpq, one_mul]
    · rw [neg_div, div_self hpq]
      norm_num
  set e12 := a12 / (a1 * a2) with he12
  set e13 := a13 / (a1 * a3) with he13
  set e23 := a23 / (a2 * a3) with he23
  have s12 : e12 * e12 = 1 := eps hu hv (plane' h30 H hh x u v hx0 hu hv)
  have s13 : e13 * e13 = 1 := eps hu hw (plane' h30 H hh x u w hx0 hu hw)
  have s23 : e23 * e23 = 1 := eps hv hw (plane' h30 H hh x v w hx0 hv hw)
  let p1 : Z2 × Z2 × Z2 →ₗ[Z2] Z2 := LinearMap.fst Z2 Z2 (Z2 × Z2)
  let p2 : Z2 × Z2 × Z2 →ₗ[Z2] Z2 := (LinearMap.fst Z2 Z2 Z2).comp (LinearMap.snd Z2 Z2 (Z2 × Z2))
  let p3 : Z2 × Z2 × Z2 →ₗ[Z2] Z2 := (LinearMap.snd Z2 Z2 Z2).comp (LinearMap.snd Z2 Z2 (Z2 × Z2))
  let χ (p : Z2 × Z2 × Z2) : F := (tg a1⁻¹ p.1 * tg a2⁻¹ p.2.1 * tg a3⁻¹ p.2.2) *
    (tg e12 (p.1 * p.2.1) * tg e13 (p.1 * p.2.2) * tg e23 (p.2.1 * p.2.2))
  have hχ : IsPhase χ := (((isPhase_tg i1).comp p1).mul_phase ((isPhase_tg i2).comp p2) |>.mul_phase ((isPhase_tg i3).comp p3))
    |>.mul_phase (((isPhase_eps s12 p1 p2).mul_phase (isPhase_eps s13 p1 p3)).mul_phase (isPhase_eps s23 p2 p3))
  let f (p : Z2 × Z2 × Z2) : F := χ p * h (x + span3 u v w p)
  have hf : RepE g f := (RepE.phase (g := g) hχ).mul (hh.subst x (span3 u v w))
  have t0 (κ : F) : tg κ 0 = 1 := by simp [tg]
  have t1 (κ : F) : tg κ 1 = κ := by simp [tg]
  have f000 : f (0, 0, 0) = 1 := by
    simp only [f, χ, span3_apply, zero_smul, mul_zero, t0, add_zero, hx, mul_one]
  have f100 : f (1, 0, 0) = 1 := by
    simp only [f, χ, span3_apply, zero_smul, one_smul, mul_zero, zero_mul, t0, t1, add_zero, mul_one]
    exact inv_mul_cancel₀ hu
  have f010 : f (0, 1, 0) = 1 := by
    simp only [f, χ, span3_apply, zero_smul, one_smul, mul_zero, zero_mul, t0, t1, add_zero, zero_add, mul_one, one_mul]
    exact inv_mul_cancel₀ hv
  have f001 : f (0, 0, 1) = 1 := by
    simp only [f, χ, span3_apply, zero_smul, one_smul, mul_zero, zero_mul, t0, t1, add_zero, zero_add, mul_one, one_mul]
    exact inv_mul_cancel₀ hw
  have inv {e : F} (he : e * e = 1) : e = e⁻¹ := by
    rcases mul_self_eq_one_iff.mp he with rfl | rfl <;> norm_num
  have f110 : f (1, 1, 0) = 1 := by
    simp only [f, χ, span3_apply, zero_smul, one_smul, mul_zero, zero_mul, t0, t1, add_zero, zero_add, mul_one, one_mul]
    change a1⁻¹ * a2⁻¹ * e12 * a12 = 1
    rw [inv s12, he12]
    field_simp
  have f101 : f (1, 0, 1) = 1 := by
    simp only [f, χ, span3_apply, zero_smul, one_smul, mul_zero, zero_mul, t0, t1, add_zero, zero_add, mul_one, one_mul]
    change a1⁻¹ * a3⁻¹ * e13 * a13 = 1
    rw [inv s13, he13]
    field_simp
  have f011 : f (0, 1, 1) = 1 := by
    simp only [f, χ, span3_apply, zero_smul, one_smul, mul_zero, zero_mul, t0, t1, add_zero, zero_add, mul_one, one_mul]
    change a2⁻¹ * a3⁻¹ * e23 * a23 = 1
    rw [inv s23, he23]
    field_simp
  have f111 : f (1, 1, 1) = a * (a1 * a2 * a3) / (a12 * a13 * a23) := by
    simp only [f, χ, span3_apply, one_smul, mul_one, t1]
    change a1⁻¹ * a2⁻¹ * a3⁻¹ * (e12 * e13 * e23) * a = _
    rw [inv s12, inv s13, inv s23, he12, he13, he23]
    field_simp
  have hden : a12 * a13 * a23 ≠ 0 := mul_ne_zero (mul_ne_zero huv huw) hvw
  -- the top value is a sign
  have top : f (1, 1, 1) = 1 ∨ f (1, 1, 1) = -1 := by
    have e (p q r : Z2) : ((1, 0, 0) : Z2 × Z2 × Z2) + ((0, 1, 0) + (0, 0, 1)) = (1, 1, 1) := rfl
    have h1 := plane' h30 H hf (1, 0, 0) (0, 1, 0) (0, 0, 1)
    have e1 : ((1, 0, 0) : Z2 × Z2 × Z2) + (0, 1, 0) = (1, 1, 0) := rfl
    have e2 : ((1, 0, 0) : Z2 × Z2 × Z2) + (0, 0, 1) = (1, 0, 1) := rfl
    have e3 : ((1, 0, 0) : Z2 × Z2 × Z2) + ((0, 1, 0) + (0, 0, 1)) = (1, 1, 1) := rfl
    rw [e1, e2, e3, f100, f110, f101, mul_one, mul_one] at h1
    exact h1 one_ne_zero one_ne_zero one_ne_zero
  have fin : f (1, 1, 1) = 1 := by
    rcases top with h1 | h1
    · exact h1
    · exfalso
      -- sum over the last bit
      let A : (Z2 × Z2) × Z2 →ₗ[Z2] Z2 × Z2 × Z2 := (LinearEquiv.prodAssoc Z2 Z2 Z2 Z2).toLinearMap
      have hk := (hf.pull A).sumBit
      have h3 := plane h30 H hk
      have c00 : f (A ((0, 0), 0)) + f (A ((0, 0), 1)) = 2 := by
        change f (0, 0, 0) + f (0, 0, 1) = 2
        rw [f000, f001]
        norm_num
      have c10 : f (A ((1, 0), 0)) + f (A ((1, 0), 1)) = 2 := by
        change f (1, 0, 0) + f (1, 0, 1) = 2
        rw [f100, f101]
        norm_num
      have c01 : f (A ((0, 1), 0)) + f (A ((0, 1), 1)) = 2 := by
        change f (0, 1, 0) + f (0, 1, 1) = 2
        rw [f010, f011]
        norm_num
      have c11 : f (A ((1, 1), 0)) + f (A ((1, 1), 1)) = 0 := by
        change f (1, 1, 0) + f (1, 1, 1) = 0
        rw [f110, h1]
        norm_num
      rw [c00, c10, c01, c11, zero_mul] at h3
      have h4 : (2 : F) * 2 ≠ 0 := mul_ne_zero h2 h2
      rcases h3 h2 h2 h2 with h5 | h5
      · exact h4 h5.symm
      · exact h4 (zero_eq_neg.mp h5)
  rw [f111, div_eq_iff hden, one_mul] at fin
  exact fin

include h30 H in
/-- **If all represented functions of one bit are stabilizer vectors, then all represented functions are.** -/
theorem stab_of_one_bit {h : W → F} (hh : RepE g h) : Stab h := by
  classical
  by_cases hex : ∃ x, h x ≠ 0
  · obtain ⟨x, hx⟩ := hex
    let k (w : W) : F := (h x)⁻¹ * h w
    have hk : RepE g k := hh.smul _
    have kx : k x = 1 := inv_mul_cancel₀ hx
    have kx0 : k x ≠ 0 := by rw [kx]; exact one_ne_zero
    let U : Submodule Z2 W :=
      { carrier := {u | k (x + u) ≠ 0}
        zero_mem' := by
          change k (x + 0) ≠ 0
          rwa [add_zero]
        add_mem' := fun {u v} hu hv => support' h30 H hk x u v kx0 hu hv
        smul_mem' := by
          intro c u hu
          rcases z2_cases c with rfl | rfl
          · change k (x + (0 : Z2) • u) ≠ 0
            rwa [zero_smul, add_zero]
          · change k (x + (1 : Z2) • u) ≠ 0
            rwa [one_smul] }
    have memU (u : W) : u ∈ U ↔ k (x + u) ≠ 0 := Iff.rfl
    let φ (u : U) : F := k (x + u)
    have hφ : IsPhase φ := by
      refine ⟨fun u => u.2, ?_, fun u u' v => ?_⟩
      · change k (x + 0) = 1
        rw [add_zero, kx]
      · have n (u : U) : φ u ≠ 0 := u.2
        have c := cube h30 H hk x u u' v kx u.2 u'.2 v.2
        have e1 : k (x + (u.1 + (u'.1 + v.1))) = φ (u + u' + v) := by
          change _ = k (x + (u.1 + u'.1 + v.1))
          rw [add_assoc u.1]
        have e2 : k (x + (u.1 + u'.1)) = φ (u + u') := rfl
        have e3 : k (x + (u.1 + v.1)) = φ (u + v) := rfl
        have e4 : k (x + (u'.1 + v.1)) = φ (u' + v) := rfl
        rw [e1, e2, e3, e4] at c
        change φ (u + u' + v) * (φ u * φ u' * φ v) = φ (u + u') * φ (u + v) * φ (u' + v) at c
        have n1 := n u
        have n2 := n u'
        have n3 := n v
        have n4 := n (u + u')
        rw [form, form, form]
        field_simp
        linear_combination c
    obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective U.subtype U.ker_subtype
    refine ⟨U, x, h x, fun w => φ (π w), hφ.comp π, fun w => ?_⟩
    have hw : h w = h x * k w := by
      simp only [k]
      rw [mul_inv_cancel_left₀ hx]
    have e : x + (w - x) = w := by abel
    rw [hw]
    congr 1
    by_cases hm : w - x ∈ U
    · rw [ind_true hm, one_mul]
      have := LinearMap.congr_fun hπ ⟨w - x, hm⟩
      change π (w - x) = ⟨w - x, hm⟩ at this
      beta_reduce
      rw [this]
      change _ = k (x + (w - x))
      rw [e]
    · rw [ind_false hm, zero_mul]
      rw [memU, not_not, e] at hm
      exact hm
  · push Not at hex
    refine ⟨⊥, 0, 0, fun _ => 1, IsPhase.one, fun w => ?_⟩
    rw [hex]
    ring

end reduce

/-- A gate that is not a stabilizer vector represents a one-bit gate that is not one. -/
theorem exists_one_bit [Fintype B] (h30 : (30 : F) ≠ 0) (hg : ¬ Stab g) :
    ∃ a : F, a ≠ 0 ∧ a ^ 4 ≠ 1 ∧ RepE g (tg a) := by
  by_contra hne
  push Not at hne
  apply hg
  refine stab_of_one_bit h30 (fun f hf h0 h1 => ?_) RepE.self
  by_contra h4
  refine hne (f 1 / f 0) (div_ne_zero h1 h0) ?_ ?_
  · intro h
    rw [div_pow, div_eq_one_iff_eq (pow_ne_zero 4 h0)] at h
    exact h4 h.symm
  · refine (hf.smul (f 0)⁻¹).congr fun x => ?_
    rcases z2_cases x with rfl | rfl
    · simp [tg, h0]
    · simp [tg]
      rw [div_eq_inv_mul]

/-- The Hadamard transform of a one-bit gate. -/
theorem rep_hadamard {a : F} (ha : 1 + a ≠ 0) (h : RepE g (tg a)) : RepE g (tg ((1 - a) / (1 + a))) := by
  have h1 : RepE g (fun p : Z2 × Z2 => sg F (p.1 * p.2)) :=
    RepE.phase (isPhase_sg (LinearMap.fst Z2 Z2 Z2) (LinearMap.snd Z2 Z2 Z2))
  have h2 : RepE g (fun p : Z2 × Z2 => tg a p.2) := h.pull (LinearMap.snd Z2 Z2 Z2)
  refine ((h1.mul h2).sumBit.smul (1 + a)⁻¹).congr fun x => ?_
  rcases z2_cases x with rfl | rfl
  · simp [tg, sg, ha]
  · simp [tg, sg]
    rw [div_eq_inv_mul, sub_eq_add_neg]

end StabilizerRank
