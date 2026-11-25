import StabilizerRank.Rep

/-!
# Every Boolean function is represented with T gates
-/

namespace StabilizerRank

open NOF

variable {F : Type*} [Field F]

abbrev Z2 := ZMod 2

/-- The sign. -/
def sg (F : Type*) [Field F] (x : Z2) : F := if x = 0 then 1 else -1

/-- The T gate. -/
def tg (ω : F) (x : Z2) : F := if x = 0 then 1 else ω

theorem z2_cases (x : Z2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem one_ne : (1 : Z2) ≠ 0 := by decide

theorem one_add_one : (1 : Z2) + 1 = 0 := by decide

theorem sg_add (x y : Z2) : sg F (x + y) = sg F x * sg F y := by
  rcases z2_cases x with rfl | rfl <;> rcases z2_cases y with rfl | rfl <;> simp [sg, one_add_one]

theorem sg_ne (x : Z2) : sg F x ≠ 0 := by
  rw [sg]
  split_ifs
  · exact one_ne_zero
  · exact neg_ne_zero.mpr one_ne_zero

/-- Fourth roots of unity are phases. -/
theorem isPhase_tg {κ : F} (h : κ ^ 4 = 1) : IsPhase (tg κ) := by
  have hκ : κ ≠ 0 := by
    rintro rfl
    simp at h
  have h2 : κ ^ 2 * κ ^ 2 = 1 := by rw [← pow_add]; exact h
  refine IsPhase.of_add (by simp [tg]) (fun u => ?_) (fun u v => if u = 0 ∨ v = 0 then 1 else κ ^ 2) (fun u v => ?_)
    (fun u u' v => ?_)
  · rw [tg]
    split_ifs
    · exact one_ne_zero
    · exact hκ
  · rcases z2_cases u with rfl | rfl <;> rcases z2_cases v with rfl | rfl
    · simp [tg]
    · simp [tg]
    · simp [tg]
    · simp only [tg, one_add_one, one_ne, ite_true, ite_false, or_self]
      rw [← h2]
      ring
  · rcases z2_cases u with rfl | rfl <;> rcases z2_cases u' with rfl | rfl <;> rcases z2_cases v with rfl | rfl <;>
      simp [one_add_one, h2]

section

variable {W : Type} [AddCommGroup W] [Module Z2 W]

/-- Products of two linear forms. -/
theorem isPhase_sg (l m : W →ₗ[Z2] Z2) : IsPhase (fun w => sg F (l w * m w)) := by
  refine IsPhase.of_add (by simp [sg]) (fun u => sg_ne _) (fun u v => sg F (l u * m v + l v * m u)) (fun u v => ?_)
    (fun u u' v => ?_)
  · rw [← sg_add, ← sg_add, map_add, map_add]
    congr 1
    ring
  · rw [← sg_add, map_add, map_add]
    congr 1
    ring

/-- The seven linear forms. -/
def seven (d a b : W →ₗ[Z2] Z2) : W →ₗ[Z2] (Fin 7 → Z2) :=
  LinearMap.pi ![d, a, b, d + a + b, d + a, a + b, d + b]

/-- The cubic sign is a quadratic phase times seven T gates. -/
theorem cubic_eq {ω : F} (hω : ω ^ 4 = -1) (x y z : Z2) :
    sg F (x * y * z) = (tg (ω ^ 2)⁻¹ (x + y) * tg (ω ^ 2)⁻¹ (y + z) * tg (ω ^ 2)⁻¹ (x + z)) *
      (tg ω x * tg ω y * tg ω z * tg ω (x + y + z) * tg ω (x + y) * tg ω (y + z) * tg ω (x + z)) := by
  have hω0 : ω ≠ 0 := by
    rintro rfl
    simp at hω
  have e2 : (ω ^ 2)⁻¹ * (ω ^ 2)⁻¹ * (ω * ω * ω * ω) = 1 := by field_simp
  have e4 : ω * ω * ω * ω = -1 := by rw [← hω]; ring
  rcases z2_cases x with rfl | rfl <;> rcases z2_cases y with rfl | rfl <;> rcases z2_cases z with rfl | rfl <;>
    simp only [tg, sg, add_zero, zero_add, mul_zero, mul_one, one_mul, one_add_one, one_ne, ite_true,
      ite_false] <;> first | exact e2.symm | exact e4.symm | linear_combination -e2 | linear_combination -e4

/-- A quadratic sign times a cubic sign. -/
theorem rep_cubic [Fintype W] {ω : F} (hω : ω ^ 4 = -1) (l m d a b : W →ₗ[Z2] Z2) :
    RepE (tg ω) (fun w => sg F (l w * m w) * sg F (d w * a w * b w)) := by
  have hκ : ((ω ^ 2)⁻¹) ^ 4 = 1 := by
    rw [inv_pow, ← pow_mul]
    have : ω ^ (2 * 4) = 1 := by
      rw [show 2 * 4 = 4 * 2 from rfl, pow_mul, hω]
      norm_num
    rw [this, inv_one]
  have hφ : IsPhase (fun w => sg F (l w * m w) * (tg (ω ^ 2)⁻¹ ((d + a) w) * tg (ω ^ 2)⁻¹ ((a + b) w) *
      tg (ω ^ 2)⁻¹ ((d + b) w))) :=
    (isPhase_sg l m).mul_phase ((((isPhase_tg hκ).comp (d + a)).mul_phase ((isPhase_tg hκ).comp (a + b))).mul_phase
      ((isPhase_tg hκ).comp (d + b)))
  refine ⟨Fin 7, inferInstance, (Rep.direct (g := tg ω) hφ 0 (seven d a b)).congr fun w => ?_⟩
  rw [cubic_eq hω, gates, zero_add, Fin.prod_univ_seven]
  simp only [seven, LinearMap.pi_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, LinearMap.add_apply]
  ring

end

/-- The conjunction from a set that is not affine: if `x, y, z` are in the set and `x + y + z` is not. -/
theorem rep_and_of_nonaffine {B : Type} [AddCommGroup B] [Module Z2 B] (p : B → Prop) {x y z : B} (hx : p x) (hy : p y)
    (hz : p z) (hxyz : ¬ p (x + y + z)) :
    RepE (fun b => ind F (p b)) (fun q : Z2 × Z2 × Z2 => ind F (q.2.2 = q.1 * q.2.1)) := by
  classical
  let W := Z2 × Z2 × Z2
  let a : W →ₗ[Z2] Z2 := LinearMap.fst _ _ _
  let b : W →ₗ[Z2] Z2 := (LinearMap.fst _ _ _).comp (LinearMap.snd _ _ _)
  let c : W →ₗ[Z2] Z2 := (LinearMap.snd _ _ _).comp (LinearMap.snd _ _ _)
  -- the NAND of two linear forms
  let N (l m : W →ₗ[Z2] Z2) : W →ₗ[Z2] B := l.smulRight (x + y) + m.smulRight (x + z)
  have val (l m : W →ₗ[Z2] Z2) (w : W) : ind F (p (x + N l m w)) = ind F (¬ (l w = 1 ∧ m w = 1)) := by
    apply ind_congr
    change p (x + (l w • (x + y) + m w • (x + z))) ↔ _
    rcases z2_cases (l w) with h1 | h1 <;> rcases z2_cases (m w) with h2 | h2 <;> rw [h1, h2]
    · simp only [zero_smul, add_zero]
      exact ⟨fun _ h => absurd h.1 (by decide), fun _ => hx⟩
    · simp only [zero_smul, one_smul, zero_add]
      rw [← add_assoc, add_self', zero_add]
      exact ⟨fun _ h => absurd h.1 (by decide), fun _ => hz⟩
    · simp only [zero_smul, one_smul, add_zero]
      rw [← add_assoc, add_self', zero_add]
      exact ⟨fun _ h => absurd h.2 (by decide), fun _ => hy⟩
    · rw [one_smul, one_smul]
      have e : x + (x + y + (x + z)) = x + y + z := by
        have e1 : x + (x + y + (x + z)) = (x + x) + (x + y + z) := by abel
        rw [e1, add_self', zero_add]
      rw [e]
      exact ⟨fun h => absurd h hxyz, fun h => absurd ⟨rfl, rfl⟩ h⟩
  let L : W →ₗ[Z2] (Fin 3 → B) := LinearMap.pi ![N (a + c) (b + c), N (a + c) c, N (b + c) c]
  refine ⟨Fin 3, inferInstance, (Rep.direct (g := fun b => ind F (p b)) (IsPhase.one (W := W)) (fun _ => x) L).congr
    fun w => ?_⟩
  rw [one_mul, gates, Fin.prod_univ_three]
  change _ = ind F (p (x + N (a + c) (b + c) w)) * ind F (p (x + N (a + c) c w)) * ind F (p (x + N (b + c) c w))
  rw [val, val, val, ind_mul, ind_mul]
  apply ind_congr
  obtain ⟨s, t, u⟩ := w
  change u = s * t ↔ (¬ (s + u = 1 ∧ t + u = 1) ∧ ¬ (s + u = 1 ∧ u = 1)) ∧ ¬ (t + u = 1 ∧ u = 1)
  revert s t u
  decide

/-! ### Graphs of Boolean functions -/

/-- The conjunction from the cubic sign. -/
theorem rep_and_of_cubic {B : Type} [AddCommGroup B] [Module Z2 B] (h2 : (2 : F) ≠ 0) {g : B → F}
    (hc : ∀ (W : Type) [AddCommGroup W] [Module Z2 W] [Fintype W] (l m d a b : W →ₗ[Z2] Z2),
      RepE g (fun w => sg F (l w * m w) * sg F (d w * a w * b w))) :
    RepE g (fun q : Z2 × Z2 × Z2 => ind F (q.2.2 = q.1 * q.2.1)) := by
  classical
  let W := Z2 × (Z2 × Z2 × Z2)
  let d : W →ₗ[Z2] Z2 := LinearMap.fst _ _ _
  let a : W →ₗ[Z2] Z2 := (LinearMap.fst _ _ _).comp (LinearMap.snd _ _ _)
  let b : W →ₗ[Z2] Z2 := ((LinearMap.fst _ _ _).comp (LinearMap.snd _ _ _)).comp (LinearMap.snd _ _ _)
  let c : W →ₗ[Z2] Z2 := ((LinearMap.snd _ _ _).comp (LinearMap.snd _ _ _)).comp (LinearMap.snd _ _ _)
  have h := ((hc W d c d a b).push (LinearMap.snd Z2 Z2 (Z2 × Z2 × Z2))).smul 2⁻¹
  refine h.congr fun q => ?_
  rw [Fintype.sum_prod_type]
  have inner (x : Z2) : ∑ q' : Z2 × Z2 × Z2, ind F (q = (LinearMap.snd Z2 Z2 (Z2 × Z2 × Z2)) (x, q')) *
      (sg F (d (x, q') * c (x, q')) * sg F (d (x, q') * a (x, q') * b (x, q'))) =
      sg F (x * q.2.2) * sg F (x * q.1 * q.2.1) := by
    rw [Finset.sum_eq_single q]
    · rw [ind_true (p := q = (LinearMap.snd Z2 Z2 (Z2 × Z2 × Z2)) (x, q)) rfl, one_mul]
      rfl
    · intro q' _ hq
      rw [ind_false, zero_mul]
      intro h0
      exact hq h0.symm
    · intro hq
      exact absurd (Finset.mem_univ _) hq
  simp only [inner]
  have huniv : (Finset.univ : Finset Z2) = {0, 1} := by decide
  rw [huniv, Finset.sum_pair (by decide)]
  simp only [zero_mul, one_mul]
  obtain ⟨x, y, z⟩ := q
  change ind F (z = x * y) = 2⁻¹ * (sg F 0 * sg F 0 + sg F z * sg F (x * y))
  have s0 : sg F 0 = 1 := by simp [sg]
  rw [← sg_add z (x * y), s0, one_mul]
  by_cases hz : z = x * y
  · rw [ind_true hz, hz]
    have : x * y + x * y = 0 := add_self' (x * y)
    rw [this, s0, show (1 : F) + 1 = 2 by norm_num, inv_mul_cancel₀ h2]
  · rw [ind_false hz]
    have h1 : z + x * y = 1 := by
      rcases z2_cases (z + x * y) with h0 | h0
      · exfalso
        apply hz
        have : z + x * y + x * y = x * y := by rw [h0, zero_add]
        rwa [add_assoc, add_self', add_zero] at this
      · exact h0
    rw [h1]
    simp [sg]

theorem rep_and (h2 : (2 : F) ≠ 0) {ω : F} (hω : ω ^ 4 = -1) :
    RepE (tg ω) (fun q : Z2 × Z2 × Z2 => ind F (q.2.2 = q.1 * q.2.1)) :=
  rep_and_of_cubic h2 fun _ _ _ _ l m d a b => rep_cubic hω l m d a b

/-- The cubic sign of three bits, as a gate. -/
def ccz (F : Type*) [Field F] (b : Fin 3 → Z2) : F := sg F (b 0 * b 1 * b 2)

theorem rep_and_ccz (h2 : (2 : F) ≠ 0) : RepE (ccz F) (fun q : Z2 × Z2 × Z2 => ind F (q.2.2 = q.1 * q.2.1)) := by
  refine rep_and_of_cubic h2 fun W _ _ _ l m d a b => ?_
  let L : W →ₗ[Z2] (Fin 1 → Fin 3 → Z2) := LinearMap.pi fun _ => LinearMap.pi ![d, a, b]
  refine ⟨Fin 1, inferInstance, (Rep.direct (g := ccz F) (isPhase_sg l m) 0 L).congr fun w => ?_⟩
  rw [gates, zero_add, Fin.prod_univ_one]
  rfl

variable {B : Type} [AddCommGroup B] [Module Z2 B]

theorem rep_xor (g : B → F) : RepE g (fun q : Z2 × Z2 × Z2 => ind F (q.2.2 = q.1 + q.2.1)) := by
  classical
  let ι : Z2 × Z2 →ₗ[Z2] Z2 × Z2 × Z2 := LinearMap.prod (LinearMap.fst _ _ _)
    (LinearMap.prod (LinearMap.snd _ _ _) (LinearMap.fst _ _ _ + LinearMap.snd _ _ _))
  refine (RepE.affine (g := g) ι 0).congr fun q => ?_
  have key (v : Z2 × Z2) : (q = 0 + ι v) ↔ (v = (q.1, q.2.1) ∧ q.2.2 = q.1 + q.2.1) := by
    obtain ⟨x, y, z⟩ := q
    obtain ⟨s, t⟩ := v
    have e : (0 : Z2 × Z2 × Z2) + ι (s, t) = (s, t, s + t) := by
      rw [zero_add]
      rfl
    rw [e, Prod.mk.injEq, Prod.mk.injEq, Prod.mk.injEq]
    constructor
    · rintro ⟨rfl, rfl, rfl⟩
      exact ⟨⟨rfl, rfl⟩, rfl⟩
    · rintro ⟨⟨rfl, rfl⟩, h3⟩
      exact ⟨rfl, rfl, h3⟩
  rw [Finset.sum_eq_single (q.1, q.2.1)]
  · apply ind_congr
    rw [key]
    simp
  · intro v _ hv
    rw [ind_false]
    intro h0
    exact hv ((key v).mp h0).1
  · intro h0
    exact absurd (Finset.mem_univ _) h0

section

variable {W : Type} [AddCommGroup W] [Module Z2 W] [Fintype W]

/-- The graph of `γ` is represented. -/
def Comp (g : B → F) (γ : W → Z2) : Prop := RepE g (fun p : W × Z2 => ind F (p.2 = γ p.1))

theorem Comp.affine (g : B → F) (l : W →ₗ[Z2] Z2) (a : Z2) : Comp g (fun w => a + l w) := by
  classical
  refine (RepE.affine (g := g) (LinearMap.prod LinearMap.id l) ((0 : W), a)).congr fun p => ?_
  rw [Finset.sum_eq_single p.1]
  · apply ind_congr
    rw [Prod.ext_iff]
    simp
  · intro v _ hv
    rw [ind_false]
    intro h0
    have := congrArg Prod.fst h0
    simp at this
    exact hv this.symm
  · intro h0
    exact absurd (Finset.mem_univ _) h0

/-- Binary operations with a represented graph. -/
theorem Comp.op {g : B → F} {γ γ' : W → Z2} (h : Comp g γ) (h' : Comp g γ') (o : Z2 → Z2 → Z2)
    (ho : RepE g (fun q : Z2 × Z2 × Z2 => ind F (q.2.2 = o q.1 q.2.1))) : Comp g (fun w => o (γ w) (γ' w)) := by
  classical
  let T := (W × Z2) × (Z2 × Z2)
  let θ₁ : T →ₗ[Z2] W × Z2 := LinearMap.prod ((LinearMap.fst _ _ _).comp (LinearMap.fst _ _ _))
    ((LinearMap.fst _ _ _).comp (LinearMap.snd _ _ _))
  let θ₂ : T →ₗ[Z2] W × Z2 := LinearMap.prod ((LinearMap.fst _ _ _).comp (LinearMap.fst _ _ _))
    ((LinearMap.snd _ _ _).comp (LinearMap.snd _ _ _))
  let θ₃ : T →ₗ[Z2] Z2 × Z2 × Z2 := LinearMap.prod ((LinearMap.fst _ _ _).comp (LinearMap.snd _ _ _))
    (LinearMap.prod ((LinearMap.snd _ _ _).comp (LinearMap.snd _ _ _)) ((LinearMap.snd _ _ _).comp (LinearMap.fst _ _ _)))
  have hh := (((h.pull θ₁).mul (h'.pull θ₂)).mul (ho.pull θ₃)).push (LinearMap.fst Z2 (W × Z2) (Z2 × Z2))
  refine RepE.congr hh fun p => ?_
  rw [Finset.sum_eq_single (p, (γ p.1, γ' p.1))]
  · rw [ind_true (p := p = (LinearMap.fst Z2 (W × Z2) (Z2 × Z2)) (p, (γ p.1, γ' p.1))) rfl, one_mul]
    change _ = ind F (γ p.1 = γ p.1) * ind F (γ' p.1 = γ' p.1) * ind F (p.2 = o (γ p.1) (γ' p.1))
    rw [ind_true (p := γ p.1 = γ p.1) rfl, ind_true (p := γ' p.1 = γ' p.1) rfl, one_mul, one_mul]
  · rintro ⟨p', c1, c2⟩ _ hp
    change ind F (p = p') * (ind F (c1 = γ p'.1) * ind F (c2 = γ' p'.1) * ind F (p'.2 = o c1 c2)) = 0
    by_cases h1 : p = p'
    · by_cases h2 : c1 = γ p'.1
      · by_cases h3 : c2 = γ' p'.1
        · exact absurd (by rw [h1, h2, h3]) hp
        · rw [ind_false h3]
          ring
      · rw [ind_false h2]
        ring
    · rw [ind_false h1]
      ring
  · intro h0
    exact absurd (Finset.mem_univ _) h0

omit [Fintype W] in
theorem Comp.congr {g : B → F} {γ γ' : W → Z2} (h : Comp g γ) (e : ∀ w, γ' w = γ w) : Comp g γ' := by
  have : γ' = γ := funext e
  rwa [this]

theorem Comp.const (g : B → F) (a : Z2) : Comp g (fun _ : W => a) :=
  (Comp.affine g 0 a).congr fun w => by simp

theorem Comp.sum {g : B → F} {ι : Type*} (s : Finset ι) (γ : ι → W → Z2) (h : ∀ i ∈ s, Comp g (γ i)) :
    Comp g (fun w => ∑ i ∈ s, γ i w) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact (Comp.const g 0).congr fun w => by simp
  | insert i s hi ih =>
    have h1 := (h i (Finset.mem_insert_self i s)).op (ih fun j hj => h j (Finset.mem_insert_of_mem hj)) (· + ·) (rep_xor g)
    exact h1.congr fun w => by rw [Finset.sum_insert hi]

theorem Comp.prod {g : B → F} (hand : RepE g (fun q : Z2 × Z2 × Z2 => ind F (q.2.2 = q.1 * q.2.1))) {ι : Type*}
    (s : Finset ι) (γ : ι → W → Z2) (h : ∀ i ∈ s, Comp g (γ i)) : Comp g (fun w => ∏ i ∈ s, γ i w) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact (Comp.const g 1).congr fun w => by simp
  | insert i s hi ih =>
    have h1 := (h i (Finset.mem_insert_self i s)).op (ih fun j hj => h j (Finset.mem_insert_of_mem hj)) (· * ·)
      hand
    exact h1.congr fun w => by rw [Finset.prod_insert hi]

/-- Every Boolean function is represented. -/
theorem comp_all {g : B → F} (hand : RepE g (fun q : Z2 × Z2 × Z2 => ind F (q.2.2 = q.1 * q.2.1))) (γ : W → Z2) :
    Comp g γ := by
  classical
  let _ : Fintype (W →ₗ[Z2] Z2) := Fintype.ofInjective (fun l : W →ₗ[Z2] Z2 => (l : W → Z2)) DFunLike.coe_injective
  -- the indicator of a point
  let δ (p w : W) : Z2 := ∏ l : W →ₗ[Z2] Z2, (l p + 1 + l w)
  have hδ (p w : W) : δ p w = if w = p then 1 else 0 := by
    by_cases h : w = p
    · rw [ite_eq_left h, h]
      refine Finset.prod_eq_one fun l _ => ?_
      rcases z2_cases (l p) with h0 | h0 <;> rw [h0] <;> decide
    · rw [ite_eq_right h]
      have : ∃ l : W →ₗ[Z2] Z2, l (w - p) ≠ 0 := by
        by_contra! h0
        have := (Module.forall_dual_apply_eq_zero_iff Z2 (w - p)).mp h0
        exact h (sub_eq_zero.mp this)
      obtain ⟨l, hl⟩ := this
      refine Finset.prod_eq_zero (Finset.mem_univ l) ?_
      rw [map_sub] at hl
      rcases z2_cases (l p) with h0 | h0 <;> rcases z2_cases (l w) with h1 | h1 <;> rw [h0, h1] at hl ⊢
      · exact absurd (by decide) hl
      · decide
      · decide
      · exact absurd (by decide) hl
  have hδc (p : W) : Comp g (δ p) :=
    Comp.prod hand Finset.univ (fun (l : W →ₗ[Z2] Z2) w => l p + 1 + l w) fun l _ => Comp.affine g l (l p + 1)
  have h1 : Comp g (fun w => ∑ p ∈ Finset.univ.filter (fun p => γ p = 1), δ p w) :=
    Comp.sum _ _ fun p _ => hδc p
  refine h1.congr fun w => ?_
  simp only [hδ]
  rw [Finset.sum_ite_eq]
  by_cases h : γ w = 1
  · rw [ite_eq_left (by simp [h]), h]
  · rw [ite_eq_right (by simp [h])]
    exact (z2_cases (γ w)).resolve_right h

/-- Every function with values zero and one is represented. -/
theorem rep_zeroOne {g : B → F} (hand : RepE g (fun q : Z2 × Z2 × Z2 => ind F (q.2.2 = q.1 * q.2.1))) (p : W → Prop) :
    RepE g (fun w => ind F (p w)) := by
  classical
  let γ : W → Z2 := fun w => if p w then 1 else 0
  have h := comp_all hand γ
  have h1 : RepE g (fun q : W × Z2 => ∑ w, ind F (q = ((0 : W), (1 : Z2)) + (LinearMap.inl Z2 W Z2) w)) :=
    RepE.affine _ _
  refine RepE.congr ((h.mul h1).push (LinearMap.fst Z2 W Z2)) fun w => ?_
  rw [Finset.sum_eq_single (w, (1 : Z2))]
  · rw [ind_true (p := w = (LinearMap.fst Z2 W Z2) (w, (1 : Z2))) rfl, one_mul, Finset.sum_eq_single w]
    · rw [ind_true (p := (w, (1 : Z2)) = ((0 : W), (1 : Z2)) + (LinearMap.inl Z2 W Z2) w) (by simp), mul_one]
      apply ind_congr
      change p w ↔ 1 = γ w
      by_cases hp : p w
      · simp [γ, hp]
      · simp [γ, hp]
    · intro v _ hv
      rw [ind_false]
      intro h0
      have := congrArg Prod.fst h0
      simp at this
      exact hv this.symm
    · intro h0
      exact absurd (Finset.mem_univ _) h0
  · rintro ⟨w', c⟩ _ hne
    by_cases h3 : w = w'
    · have : ∑ v, ind F ((w', c) = ((0 : W), (1 : Z2)) + (LinearMap.inl Z2 W Z2) v) = 0 := by
        refine Finset.sum_eq_zero fun v _ => ?_
        rw [ind_false]
        intro h0
        apply hne
        have := congrArg Prod.snd h0
        simp at this
        rw [h3, this]
      rw [this]
      ring
    · rw [ind_false (p := w = (LinearMap.fst Z2 W Z2) (w', c)) h3, zero_mul]
  · intro h0
    exact absurd (Finset.mem_univ _) h0

end

end StabilizerRank
