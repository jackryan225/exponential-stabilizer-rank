import StabilizerRank.Orbit

/-!
# The standard form of stabilizer vectors

The orbit of the multiples of `|0…0⟩` under `H`, `S`, `CNOT` is the set of the vectors `a [b ∈ A] i ^ l(b) (-1) ^ q(b)` with a
scalar `a`, an affine subspace `A`, `l(b) = ∑ l_k b_k` and `q(b) = ∑ q_{km} b_k b_m`.
-/

namespace StabilizerRank

open NOF

variable {F : Type*} [Field F] {ι : F} {Q : Type} [Fintype Q] [DecidableEq Q]

/-- Fourth roots of unity are powers of `ι`. -/
theorem exists_pow (hι : ι ^ 2 = -1) {κ : F} (hκ : κ ^ 4 = 1) : ∃ m : ℕ, κ = ι ^ m := by
  have e : (κ - 1) * ((κ + 1) * ((κ - ι) * (κ + ι))) = 0 := by
    have e1 : (κ - 1) * ((κ + 1) * ((κ - ι) * (κ + ι))) = (κ ^ 2 - 1) * (κ ^ 2 - ι ^ 2) := by ring
    rw [e1, hι]
    have e2 : (κ ^ 2 - 1) * (κ ^ 2 - -1) = κ ^ 4 - 1 := by ring
    rw [e2, hκ, sub_self]
  rcases mul_eq_zero.mp e with e | e
  · exact ⟨0, by rw [sub_eq_zero.mp e, pow_zero]⟩
  rcases mul_eq_zero.mp e with e | e
  · exact ⟨2, by rw [eq_neg_of_add_eq_zero_left e, hι]⟩
  rcases mul_eq_zero.mp e with e | e
  · exact ⟨1, by rw [sub_eq_zero.mp e, pow_one]⟩
  · refine ⟨3, ?_⟩
    rw [eq_neg_of_add_eq_zero_left e, show 3 = 2 + 1 from rfl, pow_succ, hι]
    ring

theorem val_one : (1 : ZMod 2).val = 1 := rfl

theorem val_zero : (0 : ZMod 2).val = 0 := rfl

theorem form_explicit {φ : (Q → ZMod 2) → F} (hφ : IsPhase φ) (k : Q) (s : Finset Q) :
    ∃ q : Q → ℕ, ∀ b : Q → ZMod 2, form φ (res s b) (b k • (Pi.single k 1 : Q → ZMod 2)) =
      (-1) ^ (∑ m, q m * ((b m).val * (b k).val)) := by
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨fun _ => 0, fun b => ?_⟩
    have : res ∅ b = 0 := by
      funext q
      simp [res]
    rw [this, hφ.form_zero]
    simp
  | insert l s hl ih =>
    obtain ⟨q, hq⟩ := ih
    obtain ⟨ε, hε⟩ : ∃ ε : ℕ, form φ (Pi.single l 1 : Q → ZMod 2) (Pi.single k 1 : Q → ZMod 2) = (-1) ^ ε := by
      rcases hφ.form_eq (Pi.single l 1 : Q → ZMod 2) (Pi.single k 1 : Q → ZMod 2) with h | h
      · exact ⟨0, by rw [h, pow_zero]⟩
      · exact ⟨1, by rw [h, pow_one]⟩
    refine ⟨fun m => q m + if m = l then ε else 0, fun b => ?_⟩
    rw [res_insert hl, hφ.mul, hq]
    have e : form φ (b l • (Pi.single l 1 : Q → ZMod 2)) (b k • (Pi.single k 1 : Q → ZMod 2)) =
        (-1) ^ (ε * ((b l).val * (b k).val)) := by
      rcases z2_cases (b l) with hb | hb <;> rcases z2_cases (b k) with hc | hc <;> rw [hb, hc]
      · rw [zero_smul, hφ.form_zero]
        simp
      · rw [zero_smul, hφ.form_zero]
        simp
      · rw [zero_smul, IsPhase.form_comm, hφ.form_zero]
        simp
      · rw [one_smul, one_smul, hε, val_one, mul_one, mul_one]
    rw [e, ← pow_add]
    congr 1
    simp only [add_mul, ite_mul, zero_mul]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ l, if_pos (Finset.mem_univ l)]

theorem phase_explicit (hι : ι ^ 2 = -1) {φ : (Q → ZMod 2) → F} (hφ : IsPhase φ) :
    ∃ (l : Q → ℕ) (q : Q → Q → ℕ), ∀ b : Q → ZMod 2, φ b = ι ^ (∑ k, l k * (b k).val) *
      (-1) ^ (∑ k, ∑ m, q k m * ((b k).val * (b m).val)) := by
  have key : ∀ s : Finset Q, ∃ (l : Q → ℕ) (q : Q → Q → ℕ), ∀ b : Q → ZMod 2, φ (res s b) =
      ι ^ (∑ k, l k * (b k).val) * (-1) ^ (∑ k, ∑ m, q k m * ((b k).val * (b m).val)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨fun _ => 0, fun _ _ => 0, fun b => ?_⟩
      have : res ∅ b = 0 := by
        funext q
        simp [res]
      rw [this, hφ.zero]
      simp
    | insert k s hk ih =>
      obtain ⟨l, q, h⟩ := ih
      obtain ⟨q', h'⟩ := form_explicit hφ k s
      have h4 : φ (Pi.single k 1 : Q → ZMod 2) ^ 4 = 1 := by
        have e : φ (Pi.single k 1 : Q → ZMod 2) ^ 4 = (φ (Pi.single k 1) * φ (Pi.single k 1)) *
          (φ (Pi.single k 1) * φ (Pi.single k 1)) := by ring
        rw [e, hφ.sq, hφ.form_sq]
      obtain ⟨m, hm⟩ := exists_pow hι h4
      refine ⟨fun j => l j + if j = k then m else 0, fun j i => q j i + if i = k then q' j else 0, fun b => ?_⟩
      rw [res_insert hk, hφ.add, h, h']
      have e : φ (b k • (Pi.single k 1 : Q → ZMod 2)) = ι ^ (m * (b k).val) := by
        rcases z2_cases (b k) with hc | hc <;> rw [hc]
        · rw [zero_smul, hφ.zero, val_zero, mul_zero, pow_zero]
        · rw [one_smul, hm, val_one, mul_one]
      rw [e]
      have e1 : ∑ j, (l j + if j = k then m else 0) * (b j).val = ∑ j, l j * (b j).val + m * (b k).val := by
        simp only [add_mul, ite_mul, zero_mul]
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ k, if_pos (Finset.mem_univ k)]
      have e2 : ∑ j, ∑ i, (q j i + if i = k then q' j else 0) * ((b j).val * (b i).val) =
          ∑ j, ∑ i, q j i * ((b j).val * (b i).val) + ∑ j, q' j * ((b j).val * (b k).val) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [add_mul, ite_mul, zero_mul]
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ k, if_pos (Finset.mem_univ k)]
      rw [e1, e2, pow_add, pow_add]
      ring
  obtain ⟨l, q, h⟩ := key Finset.univ
  refine ⟨l, q, fun b => ?_⟩
  rw [← h]
  congr 1
  funext j
  simp [res]

/-- The phase `i ^ l(b) (-1) ^ q(b)`. -/
theorem isPhase_explicit (hι : ι ^ 4 = 1) (l : Q → ℕ) (q : Q → Q → ℕ) :
    IsPhase (fun b : Q → Z2 => ι ^ (∑ k, l k * (b k).val) * (-1) ^ (∑ k, ∑ m, q k m * ((b k).val * (b m).val))) := by
  have h1 : IsPhase (fun b : Q → Z2 => ∏ k, tg ι (b k) ^ l k) :=
    IsPhase.prod Finset.univ (fun k (b : Q → Z2) => tg ι (b k) ^ l k) fun k _ =>
      ((isPhase_tg hι).comp (LinearMap.proj (R := Z2) (φ := fun _ : Q => Z2) k)).pow (l k)
  have h2 : IsPhase (fun b : Q → Z2 => ∏ k, ∏ m, sg F (b k * b m) ^ q k m) :=
    IsPhase.prod Finset.univ (fun k (b : Q → Z2) => ∏ m, sg F (b k * b m) ^ q k m) fun k _ =>
      IsPhase.prod Finset.univ (fun m (b : Q → Z2) => sg F (b k * b m) ^ q k m) fun m _ =>
        (isPhase_sg (LinearMap.proj (R := Z2) (φ := fun _ : Q => Z2) k)
          (LinearMap.proj (R := Z2) (φ := fun _ : Q => Z2) m)).pow (q k m)
  have e : (fun b : Q → Z2 => ι ^ (∑ k, l k * (b k).val) * (-1) ^ (∑ k, ∑ m, q k m * ((b k).val * (b m).val))) =
      fun b => (∏ k, tg ι (b k) ^ l k) * ∏ k, ∏ m, sg F (b k * b m) ^ q k m := by
    funext b
    congr 1
    · rw [← Finset.prod_pow_eq_pow_sum]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [tg_eq_pow, ← pow_mul, mul_comm]
    · rw [← Finset.prod_pow_eq_pow_sum]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← Finset.prod_pow_eq_pow_sum]
      refine Finset.prod_congr rfl fun m _ => ?_
      rw [sg_mul_eq_pow, ← pow_mul, mul_comm]
  rw [e]
  exact h1.mul_phase h2

theorem stab_of_affine {W : Type} [AddCommGroup W] [Module (ZMod 2) W] {s : W → F} (a : F) (A : AffineSubspace (ZMod 2) W)
    {χ : W → F} (hχ : IsPhase χ) (h : ∀ w, s w = a * (ind F (w ∈ A) * χ w)) : Stab s := by
  by_cases hex : ∃ w₀, w₀ ∈ A
  · obtain ⟨w₀, hw₀⟩ := hex
    refine ⟨A.direction, w₀, a * χ w₀, fun v => χ v * form χ w₀ v, hχ.shift w₀, fun w => ?_⟩
    rw [h]
    have e : ind F (w ∈ A) = ind F (w - w₀ ∈ A.direction) := by
      apply ind_congr
      rw [← vsub_eq_sub, AffineSubspace.vsub_right_mem_direction_iff_mem hw₀]
    have e2 : χ w = χ w₀ * (χ (w - w₀) * form χ w₀ (w - w₀)) := by
      rw [← hχ.shift_eq, add_sub_cancel]
    rw [e, e2]
    ring
  · refine ⟨⊥, 0, 0, fun _ => 1, IsPhase.one, fun w => ?_⟩
    rw [h, ind_false (fun h0 => hex ⟨w, h0⟩)]
    ring

open Classical in
/-- **The orbit is the set of the vectors in standard form.** -/
theorem isStabilizer_iff_standard (hι : ι ^ 2 = -1) (h2 : (2 : F) ≠ 0) (ψ : (Q → ZMod 2) → F) : IsStabilizer ι ψ ↔
    ∃ (a : F) (A : AffineSubspace (ZMod 2) (Q → ZMod 2)) (l : Q → ℕ) (q : Q → Q → ℕ), ∀ b : Q → ZMod 2,
      ψ b = a * ((if b ∈ A then 1 else 0) * (ι ^ (∑ k, l k * (b k).val) *
        (-1) ^ (∑ k, ∑ m, q k m * ((b k).val * (b m).val)))) := by
  have h4 : ι ^ 4 = 1 := by rw [show 4 = 2 * 2 from rfl, pow_mul, hι]; norm_num
  rw [isStabilizer_iff hι h2]
  constructor
  · intro h
    obtain ⟨a, A, χ, hχ, h⟩ := h.affine
    obtain ⟨l, q, hlq⟩ := phase_explicit hι hχ
    refine ⟨a, A, l, q, fun b => ?_⟩
    rw [h, hlq, ind_eq_ite]
  · rintro ⟨a, A, l, q, h⟩
    refine stab_of_affine a A (isPhase_explicit h4 l q) fun b => ?_
    rw [h, ind_eq_ite]

end StabilizerRank
