import NOF.Table
import NCBound.Circle

/-!
# The table exists

If the lift of every table was at most as expensive as the matrix product, a new party could hold the three labels for
free. It would be the midpoint of every side of the triangle.
-/

namespace NOF

open Real OAI OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor OAI.Hierarchy
open scoped NNReal

/-- The plane. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- An equilateral triangle with side one, and the midpoints of two sides. -/
noncomputable def place : Old → Plane
  | .o1 => 0
  | .o2 => NCBound.dir 0
  | .o3 => NCBound.dir (π / 3)
  | .m2 => (1 / 2 : ℝ) • NCBound.dir 0
  | .m3 => (1 / 2 : ℝ) • NCBound.dir (π / 3)

theorem norm_dir_sub : ‖NCBound.dir 0 - NCBound.dir (π / 3)‖ = 1 := by
  have h : ‖NCBound.dir 0 - NCBound.dir (π / 3)‖ ^ 2 = 1 ^ 2 := by
    rw [norm_sub_sq_real, NCBound.inner_dir, NCBound.norm_dir, NCBound.norm_dir, zero_sub, cos_neg, cos_pi_div_three]
    norm_num
  exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp h

theorem dist_o1_o2 : dist (place .o1) (place .o2) = 1 := by
  simp [place, dist_eq_norm, NCBound.norm_dir]

theorem dist_o1_o3 : dist (place .o1) (place .o3) = 1 := by
  simp [place, dist_eq_norm, NCBound.norm_dir]

theorem dist_o2_o3 : dist (place .o2) (place .o3) = 1 := by
  simp [place, dist_eq_norm, norm_dir_sub]

theorem dist_m2_o1 : dist (place .m2) (place .o1) = 1 / 2 := by
  simp [place, norm_smul, NCBound.norm_dir]

theorem dist_m3_o1 : dist (place .m3) (place .o1) = 1 / 2 := by
  simp [place, norm_smul, NCBound.norm_dir]

theorem half_sub (v : Plane) : (1 / 2 : ℝ) • v - v = (-(1 / 2) : ℝ) • v := by
  rw [neg_smul, sub_eq_iff_eq_add, ← sub_eq_neg_add, eq_sub_iff_add_eq, ← add_smul]
  norm_num

theorem dist_m2_o2 : dist (place .m2) (place .o2) = 1 / 2 := by
  rw [dist_eq_norm, place, place, half_sub, norm_smul, NCBound.norm_dir]
  norm_num

theorem dist_m3_o3 : dist (place .m3) (place .o3) = 1 / 2 := by
  rw [dist_eq_norm, place, place, half_sub, norm_smul, NCBound.norm_dir]
  norm_num

theorem dist_m2_m3 : dist (place .m2) (place .m3) = 1 / 2 := by
  rw [dist_eq_norm, place, place, ← smul_sub, norm_smul, norm_dir_sub]
  norm_num

theorem place_injective : Function.Injective place := by
  have h (a b : Old) (c : ℝ) (hc : 0 < c) (h : dist (place a) (place b) = c) : place a ≠ place b := by
    intro e
    rw [e, dist_self] at h
    exact hc.ne h
  have h1 := h _ _ _ one_pos dist_o1_o2
  have h2 := h _ _ _ one_pos dist_o1_o3
  have h3 := h _ _ _ one_pos dist_o2_o3
  have h4 := h _ _ _ (by norm_num) dist_m2_o1
  have h5 := h _ _ _ (by norm_num) dist_m3_o1
  have h6 := h _ _ _ (by norm_num) dist_m2_o2
  have h7 := h _ _ _ (by norm_num) dist_m3_o3
  have h8 := h _ _ _ (by norm_num) dist_m2_m3
  have h9 : place .m2 ≠ place .o3 := by
    intro e
    have : ‖place .m2‖ = ‖place .o3‖ := by rw [e]
    simp [place, norm_smul, NCBound.norm_dir] at this
  have h10 : place .m3 ≠ place .o2 := by
    intro e
    have : ‖place .m3‖ = ‖place .o2‖ := by rw [e]
    simp [place, norm_smul, NCBound.norm_dir] at this
  intro a b hab
  cases a <;> cases b <;> first | rfl | exact absurd hab (by assumption) | exact absurd hab.symm (by assumption)

variable {K : Type*} [Field K]

/-- The logarithmic price of a product. -/
theorem rawLogPrice_mul {I : Type} [Fintype I] [Nonempty I]
    (f : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I K → _ → Prop)) (c : ℝ) {A B : Raw.{0} I K}
    (hA : A.coeff ≠ 0) (hB : B.coeff ≠ 0) : rawLogPrice f c (A.mul B) = rawLogPrice f c A + rawLogPrice f c B := by
  have hm : f.val (ofRaw (A.mul B)) = f.val (ofRaw A) * f.val (ofRaw B) := by
    rw [ofRaw_mul]
    exact map_mul (normalizedSpectrum.toRingHom f) _ _
  have h1 : (0 : ℝ) < f.val (ofRaw A) := by
    exact_mod_cast zero_lt_one.trans_le (one_le_raw_spectralValue f A hA)
  have h2 : (0 : ℝ) < f.val (ofRaw B) := by
    exact_mod_cast zero_lt_one.trans_le (one_le_raw_spectralValue f B hB)
  simp only [rawLogPrice, hm, NNReal.coe_mul]
  rw [Real.logb_mul h1.ne' h2.ne', mul_add]

theorem mul_coeff_ne_zero {I : Type} [Fintype I] {A B : Raw.{0} I K} (hA : A.coeff ≠ 0) (hB : B.coeff ≠ 0) :
    (A.mul B).coeff ≠ 0 := by
  obtain ⟨a, ha⟩ := Function.ne_iff.mp hA
  obtain ⟨b, hb⟩ := Function.ne_iff.mp hB
  intro h
  have : (A.mul B).coeff (fun i => (a i, b i)) = 0 := congrFun h _
  exact mul_ne_zero ha hb this

/-- A label shared by `a`, the new party and `b`. -/
noncomputable def label (K : Type*) [Field K] (a b : Old) : Raw.{0} (Option Old) K :=
  (Raw.diagonal (Fin 3) K (Fin 2)).group ![some a, none, some b]

theorem label_coeff (a b : Old) (t : ∀ i, (label K a b).Leg i) : (label K a b).coeff t =
    ind K (letter (q := 2) (t (some a) ⟨(0 : Fin 3), rfl⟩) = letter (q := 2) (t none ⟨(1 : Fin 3), rfl⟩) ∧
      letter (q := 2) (t (some b) ⟨(2 : Fin 3), rfl⟩) = letter (q := 2) (t none ⟨(1 : Fin 3), rfl⟩)) := by
  classical
  let lab : Fin 3 → Fin 2 := fun s => t (![some a, none, some b] s) ⟨s, rfl⟩
  change (Raw.diagonal (Fin 3) K (Fin 2)).coeff lab = ind K (lab 0 = lab 1 ∧ lab 2 = lab 1)
  rw [Raw.diagonal_coeff_at (K := K) (1 : Fin 3) lab, ← ind_eq_ite]
  apply ind_congr
  refine ⟨fun h => ⟨h 0, h 2⟩, fun h i => ?_⟩
  fin_cases i
  · exact h.1
  · rfl
  · exact h.2

theorem label_ne_zero (a b : Old) : (label K a b).coeff ≠ 0 :=
  ((Raw.diagonal (Fin 3) K (Fin 2)).group_ne_zero_iff _).2 (diagonal_ne_zero _ (by norm_num))

/-- The product of the three labels is a restriction of the shared labels. -/
theorem labels_restrict : (((label K .o1 .o3).mul (label K .o1 .o2)).mul (label K .o2 .o3)).Restricts
    (shared K (Fin 2) (Fin 2) (Fin 2)) := by
  classical
  let read : ∀ i, (((label K .o1 .o3).mul (label K .o1 .o2)).mul (label K .o2 .o3)).Leg i →
      NLeg (Fin 2) (Fin 2) (Fin 2) i := fun i =>
    match i with
    | none => fun t => (t.1.1 ⟨(1 : Fin 3), rfl⟩, t.1.2 ⟨(1 : Fin 3), rfl⟩, t.2 ⟨(1 : Fin 3), rfl⟩)
    | some .o1 => fun t => (t.1.1 ⟨(0 : Fin 3), rfl⟩, t.1.2 ⟨(0 : Fin 3), rfl⟩)
    | some .o2 => fun t => (t.1.2 ⟨(2 : Fin 3), rfl⟩, t.2 ⟨(0 : Fin 3), rfl⟩)
    | some .o3 => fun t => (t.2 ⟨(2 : Fin 3), rfl⟩, t.1.1 ⟨(2 : Fin 3), rfl⟩)
    | some .m2 => fun _ => PUnit.unit
    | some .m3 => fun _ => PUnit.unit
  refine restricts_of_read (T := shared K (Fin 2) (Fin 2) (Fin 2)) read fun t => ?_
  have e1 : (((label K .o1 .o3).mul (label K .o1 .o2)).mul (label K .o2 .o3)).coeff t =
      (label K .o1 .o3).coeff (fun i => (t i).1.1) * (label K .o1 .o2).coeff (fun i => (t i).1.2) *
        (label K .o2 .o3).coeff (fun i => (t i).2) := rfl
  rw [e1, label_coeff, label_coeff, label_coeff, ind_mul, ind_mul]
  change _ = ind K (Agree' fun i => read i (t i))
  apply ind_congr
  constructor
  · intro h
    exact ⟨⟨h.1.1.1.trans h.1.1.2.symm, h.1.2.1.trans h.1.2.2.symm, h.2.1.trans h.2.2.symm⟩,
      Prod.ext h.1.1.1.symm (Prod.ext h.1.2.1.symm h.2.1.symm)⟩
  · intro h
    have h4 := congrArg Prod.fst h.2
    have h5 := congrArg (fun p => p.2.1) h.2
    have h6 := congrArg (fun p => p.2.2) h.2
    exact ⟨⟨⟨h4.symm, h.1.1.symm.trans h4.symm⟩, h5.symm, h.1.2.1.symm.trans h5.symm⟩, h6.symm, h.1.2.2.symm.trans h6.symm⟩

/-- **The table.** -/
theorem exists_table (P : SpectralPlacementPrices K Plane) :
    ∃ (m : ℕ) (T : Bits m → Bits m → Bits m → K), 3 * (m : ℝ) < P.price (hat T) place := by
  classical
  by_contra! h
  let y : Old ↪ Plane := ⟨place, place_injective⟩
  obtain ⟨φ, hφ⟩ := P.normalized y
  have hD := P.diagonal_pos y
  set D := P.price (Raw.diagonal Old K (Fin 2)) y with hDdef
  -- the new party
  let U : NonzeroProduct.{0} (Option Old) K := Additive.ofMul ⟨ofRaw (shared K (Fin 2) (Fin 2) (Fin 2)),
    fun h0 => shared_ne_zero ((ofRaw_eq_zero_iff _).mp h0)⟩
  have hU (m : ℕ) : classContractionPrice φ (classOfProduct (m • U)) ≤ m * (3 / D) := by
    refine (classContractionPrice_mono φ (shared_pow_le K m)).trans ?_
    change contractionPrice φ (shared K (Bits m) (Bits m) (Bits m)) ≤ _
    refine ciSup_le fun ξ => ?_
    refine (rawLogPrice_mono φ zero_le_one (contract_restricts ξ)).trans ?_
    by_cases h0 : (hat fun x y z : Bits m => ξ (x, y, z)).coeff = 0
    · rw [rawLogPrice_zero φ 1 _ h0]
      positivity
    · have h1 := h m (fun x y z => ξ (x, y, z))
      have h2 : P.price (hat fun x y z : Bits m => ξ (x, y, z)) place = D * _ := hφ _ h0
      rw [h2] at h1
      rw [rawLogPrice, one_mul, ← mul_div_assoc, le_div_iff₀ hD]
      linarith
  obtain ⟨f, hold, hfU⟩ := exists_extension φ U (3 / D) (by positivity) hU
  obtain ⟨X, met, Q, ι, -, hdist, hprice⟩ := exists_metric_price_realization f D hD.le
  -- the old distances
  have old (a b : Old) : dist (ι (some a)) (ι (some b)) = dist (place a) (place b) := by
    let W : Raw.{0} Old K := (Raw.diagonal (Fin 2) K (Fin 2)).group ![a, b]
    have hW : W.coeff ≠ 0 := ((Raw.diagonal (Fin 2) K (Fin 2)).group_ne_zero_iff _).2 (diagonal_ne_zero _ (by norm_num))
    have e1 : P.price W y = dist (place a) (place b) := by
      change P.price ((Raw.diagonal (Fin 2) K (Fin 2)).group ![a, b]) y = _
      rw [← P.group, P.wire]
      rfl
    have e2 := group_some_logPrice_of_old_logPoint φ f hold W
    have e3 : ofRaw (W.group some) = ofRaw ((Raw.diagonal (Fin 2) K (Fin 2)).group ![some a, some b]) := by
      have := ofRaw_eq_iff.mpr (Raw.group_group_equivalent (Raw.diagonal (Fin 2) K (Fin 2)) ![a, b]
        (some : Old → Option Old))
      have e : (some : Old → Option Old) ∘ ![a, b] = ![some a, some b] := by
        funext i
        fin_cases i <;> rfl
      rw [e] at this
      exact this
    rw [hdist, rawWireDistance, rawLogPrice, ← e3, ← e1, hφ W hW]
    simp only [rawLogPrice, one_mul] at e2
    rw [e2]
  -- the prices of the labels
  have lab (a b : Old) : Q.price (Raw.diagonal (Fin 3) K (Fin 2)) ![ι (some a), ι none, ι (some b)] =
      rawLogPrice f D (label K a b) := by
    have e : ![ι (some a), ι none, ι (some b)] = ι ∘ ![some a, none, some b] := by
      funext i
      fin_cases i <;> rfl
    rw [e, hprice]
    rfl
  have total : rawLogPrice f D (label K .o1 .o3) + rawLogPrice f D (label K .o1 .o2) +
      rawLogPrice f D (label K .o2 .o3) ≤ 3 := by
    rw [← rawLogPrice_mul f D (label_ne_zero _ _) (label_ne_zero _ _),
      ← rawLogPrice_mul f D (mul_coeff_ne_zero (label_ne_zero _ _) (label_ne_zero _ _)) (label_ne_zero _ _)]
    refine (rawLogPrice_mono f hD.le labels_restrict).trans ?_
    have e : rawLogPrice f D (shared K (Fin 2) (Fin 2) (Fin 2)) = D * logPoint f U := rfl
    rw [e]
    calc D * logPoint f U ≤ D * (3 / D) := mul_le_mul_of_nonneg_left hfU hD.le
      _ = 3 := by field_simp
  have low (a b : Old) : dist (place a) (place b) ≤ rawLogPrice f D (label K a b) := by
    rw [← lab, ← old]
    exact Q.dist_le_diagonal ![ι (some a), ι none, ι (some b)] 0 2
  have l13 := low .o1 .o3
  have l12 := low .o1 .o2
  have l23 := low .o2 .o3
  rw [dist_o1_o3] at l13
  rw [dist_o1_o2] at l12
  rw [dist_o2_o3] at l23
  have free (a b : Old) (hd : dist (place a) (place b) = 1) (hl : rawLogPrice f D (label K a b) ≤ 1) :
      dist (ι (some a)) (ι none) + dist (ι none) (ι (some b)) ≤ 1 := by
    have := between_of_free Q (ι (some a)) (ι none) (ι (some b)) (by rw [lab, old, hd]; exact hl)
    rwa [old, hd] at this
  have f13 := free .o1 .o3 dist_o1_o3 (by linarith)
  have f12 := free .o1 .o2 dist_o1_o2 (by linarith)
  have f23 := free .o2 .o3 dist_o2_o3 (by linarith)
  have t13 := dist_triangle (ι (some .o1)) (ι none) (ι (some .o3))
  have t12 := dist_triangle (ι (some .o1)) (ι none) (ι (some .o2))
  have t23 := dist_triangle (ι (some .o2)) (ι none) (ι (some .o3))
  rw [old, dist_o1_o3] at t13
  rw [old, dist_o1_o2] at t12
  rw [old, dist_o2_o3] at t23
  have c1 := dist_comm (ι (some .o1)) (ι none)
  have c2 := dist_comm (ι (some .o2)) (ι none)
  have c3 := dist_comm (ι (some .o3)) (ι none)
  -- the new party is the midpoint of two sides
  have m2 : ι none = ι (some .m2) := by
    apply midpoint_unique Q (a := ι (some .o1)) (b := ι (some .o2))
    · rw [old, dist_o1_o2]; linarith
    · rw [old, dist_o1_o2]; linarith
    · rw [old, old, dist_o1_o2, dist_m2_o1]
    · rw [old, old, dist_o1_o2, dist_m2_o2]
  have m3 : ι none = ι (some .m3) := by
    apply midpoint_unique Q (a := ι (some .o1)) (b := ι (some .o3))
    · rw [old, dist_o1_o3]; linarith
    · rw [old, dist_o1_o3]; linarith
    · rw [old, old, dist_o1_o3, dist_m3_o1]
    · rw [old, old, dist_o1_o3, dist_m3_o3]
  have e := old .m2 .m3
  rw [← m2, ← m3, dist_self, dist_m2_m3] at e
  norm_num at e

end NOF
