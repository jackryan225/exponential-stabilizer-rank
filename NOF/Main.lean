import NOF.Prop
import OAI.Hierarchy.ForceSelection

/-!
# A table on three groups of bits that costs more than its bits, given prices in the plane
-/

namespace NOF

open Real OAI OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor OAI.Hierarchy
open scoped NNReal

variable {K : Type*} [Field K]

/-! ### Powers -/

section power

variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]

/-- The tensor power of a table. -/
def tpow (T : X → Y → Z → K) (N : ℕ) (x : Fin N → X) (y : Fin N → Y) (z : Fin N → Z) : K :=
  ∏ i, T (x i) (y i) (z i)

theorem hat_pow_le (T : X → Y → Z → K) (N : ℕ) : (ofRaw (hat T)) ^ N ≤ ofRaw (hat (tpow T N)) := by
  classical
  induction N with
  | zero =>
    rw [pow_zero]
    let read : ∀ i : Old, PUnit → OLeg (Fin 0 → X) (Fin 0 → Y) (Fin 0 → Z) i := fun i =>
      match i with
      | .o1 => fun _ => (Fin.elim0, Fin.elim0)
      | .o2 => fun _ => (Fin.elim0, Fin.elim0)
      | .o3 => fun _ => (Fin.elim0, Fin.elim0)
      | .m2 => fun _ => PUnit.unit
      | .m3 => fun _ => PUnit.unit
    refine restricts_of_read (S := Raw.one Old K) (T := hat (tpow T 0)) read fun a => ?_
    have e : ∀ b : ∀ i, OLeg (Fin 0 → X) (Fin 0 → Y) (Fin 0 → Z) i,
        (1 : K) = ind K (Agree b) * tpow T 0 (b .o1).1 (b .o1).2 (b .o2).2 := by
      intro b
      rw [ind_true ⟨Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _⟩]
      simp [tpow]
    exact e _
  | succ N ih =>
    rw [pow_succ]
    refine (mul_mono ih le_rfl).trans ?_
    rw [← ofRaw_mul]
    let read : ∀ i, OLeg (Fin N → X) (Fin N → Y) (Fin N → Z) i × OLeg X Y Z i →
        OLeg (Fin (N + 1) → X) (Fin (N + 1) → Y) (Fin (N + 1) → Z) i := fun i =>
      match i with
      | .o1 => fun p => (Fin.snoc p.1.1 p.2.1, Fin.snoc p.1.2 p.2.2)
      | .o2 => fun p => (Fin.snoc p.1.1 p.2.1, Fin.snoc p.1.2 p.2.2)
      | .o3 => fun p => (Fin.snoc p.1.1 p.2.1, Fin.snoc p.1.2 p.2.2)
      | .m2 => fun _ => PUnit.unit
      | .m3 => fun _ => PUnit.unit
    refine restricts_of_read (S := (hat (tpow T N)).mul (hat T)) (T := hat (tpow T (N + 1))) read fun a => ?_
    have snoc_eq {W : Type} (s s' : Fin N → W) (t t' : W) :
        (Fin.snoc s t : Fin (N + 1) → W) = Fin.snoc s' t' ↔ s = s' ∧ t = t' := by
      constructor
      · intro h
        refine ⟨funext fun i => ?_, ?_⟩
        · have := congrFun h (Fin.castSucc i)
          simpa using this
        · have := congrFun h (Fin.last N)
          simpa using this
      · rintro ⟨rfl, rfl⟩
        rfl
    have e : ∀ a : ∀ i, OLeg (Fin N → X) (Fin N → Y) (Fin N → Z) i × OLeg X Y Z i,
        (ind K (Agree fun i => (a i).1) * tpow T N (a .o1).1.1 (a .o1).1.2 (a .o2).1.2) *
          (ind K (Agree fun i => (a i).2) * T (a .o1).2.1 (a .o1).2.2 (a .o2).2.2) =
        ind K (Agree fun i => read i (a i)) * tpow T (N + 1) (Fin.snoc (a .o1).1.1 (a .o1).2.1)
          (Fin.snoc (a .o1).1.2 (a .o1).2.2) (Fin.snoc (a .o2).1.2 (a .o2).2.2) := by
      intro a
      have hv : tpow T (N + 1) (Fin.snoc (a .o1).1.1 (a .o1).2.1) (Fin.snoc (a .o1).1.2 (a .o1).2.2)
            (Fin.snoc (a .o2).1.2 (a .o2).2.2) =
          tpow T N (a .o1).1.1 (a .o1).1.2 (a .o2).1.2 * T (a .o1).2.1 (a .o1).2.2 (a .o2).2.2 := by
        rw [tpow, Fin.prod_univ_castSucc]
        simp [tpow]
      have hi : ind K (Agree fun i => read i (a i)) = ind K (Agree fun i => (a i).1) * ind K (Agree fun i => (a i).2) := by
        rw [ind_mul]
        apply ind_congr
        simp only [Agree, read, snoc_eq]
        tauto
      rw [hv, hi]
      ring
    exact e a

theorem hat_ne_zero {T : X → Y → Z → K} (h : ∃ x y z, T x y z ≠ 0) : (hat T).coeff ≠ 0 := by
  classical
  obtain ⟨x, y, z, h⟩ := h
  let b : ∀ i, OLeg X Y Z i := fun i =>
    match i with
    | .o1 => (x, y)
    | .o2 => (y, z)
    | .o3 => (z, x)
    | .m2 => PUnit.unit
    | .m3 => PUnit.unit
  intro h0
  have h1 : (hat T).coeff b = 0 := congrFun h0 b
  have h2 : (hat T).coeff b = ind K (Agree b) * T x y z := rfl
  rw [ind_true ⟨rfl, rfl, rfl⟩, one_mul] at h2
  exact h (h2.symm.trans h1)

theorem exists_of_hat_ne_zero {T : X → Y → Z → K} (h : (hat T).coeff ≠ 0) : ∃ x y z, T x y z ≠ 0 := by
  classical
  by_contra! h0
  apply h
  funext a
  have e : ∀ a : ∀ i, OLeg X Y Z i, ind K (Agree a) * T (a .o1).1 (a .o1).2 (a .o2).2 = 0 := by
    intro a
    rw [h0, mul_zero]
  exact e a

/-- Prices of powers. -/
theorem price_pow (P : SpectralPlacementPrices K Plane) (T : X → Y → Z → K) (hT : (hat T).coeff ≠ 0) (N : ℕ) :
    N * P.price (hat T) place ≤ P.price (hat (tpow T N)) place := by
  rcases P.all_zero_or_normalized_at place with price | ⟨φ, c, hc, price⟩
  · rw [price, price, mul_zero]
  · rw [price, price, rawLogPrice, rawLogPrice]
    have h1 : (1 : ℝ) ≤ φ.val (ofRaw (hat T)) := by exact_mod_cast one_le_raw_spectralValue φ _ hT
    have h2 := φ.2.2.2.2.2 _ _ (hat_pow_le T N)
    have h3 : φ.val ((ofRaw (hat T)) ^ N) = φ.val (ofRaw (hat T)) ^ N := map_pow (normalizedSpectrum.toRingHom φ) _ N
    have h4 : ((φ.val (ofRaw (hat T))) ^ N : ℝ) ≤ φ.val (ofRaw (hat (tpow T N))) := by
      rw [h3] at h2
      exact_mod_cast h2
    have h5 := logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) h4
    rw [logb_pow] at h5
    have := mul_le_mul_of_nonneg_left h5 hc.le
    linarith

end power

/-! ### A table with values zero and one -/

section zeroOne

variable {Q : Type} [Fintype Q]

open Classical in
/-- The values of a power of a table. -/
noncomputable def values (T : Q → Q → Q → K) (M : ℕ) : Finset K :=
  Finset.univ.image fun p : (Fin M → Q) × (Fin M → Q) × (Fin M → Q) => tpow T M p.1 p.2.1 p.2.2

theorem mem_values (T : Q → Q → Q → K) (M : ℕ) (x y z : Fin M → Q) : tpow T M x y z ∈ values T M := by
  classical
  exact Finset.mem_image.mpr ⟨(x, y, z), Finset.mem_univ _, rfl⟩

/-- A power of a table has few values. -/
theorem card_values (T : Q → Q → Q → K) (M : ℕ) :
    (values T M).card ≤ (M + 1) ^ Fintype.card (Q × Q × Q) := by
  classical
  let g (c : Q × Q × Q → Fin (M + 1)) : K := ∏ t, T t.1 t.2.1 t.2.2 ^ (c t : ℕ)
  have hsub : values T M ⊆ Finset.univ.image g := by
    intro v hv
    obtain ⟨⟨x, y, z⟩, -, rfl⟩ := Finset.mem_image.mp hv
    let c : Q × Q × Q → Fin (M + 1) := fun t =>
      ⟨(Finset.univ.filter fun i : Fin M => (x i, y i, z i) = t).card, by
        have := Finset.card_le_univ (Finset.univ.filter fun i : Fin M => (x i, y i, z i) = t)
        rw [Fintype.card_fin] at this
        omega⟩
    refine Finset.mem_image.mpr ⟨c, Finset.mem_univ _, ?_⟩
    change ∏ t : Q × Q × Q, T t.1 t.2.1 t.2.2 ^ (c t : ℕ) = ∏ i, T (x i) (y i) (z i)
    rw [← Finset.prod_fiberwise (s := Finset.univ) (g := fun i : Fin M => (x i, y i, z i))
      (f := fun i => T (x i) (y i) (z i))]
    refine Finset.prod_congr rfl fun t _ => ?_
    rw [Finset.prod_congr rfl (g := fun _ => T t.1 t.2.1 t.2.2)]
    · rw [Finset.prod_const]
    · intro i hi
      rw [Finset.mem_filter] at hi
      rw [← hi.2]
  refine (Finset.card_le_card hsub).trans (Finset.card_image_le.trans ?_)
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin]

/-- The value with a given number. -/
noncomputable def theValue (T : Q → Q → Q → K) (M : ℕ) (s : Fin (values T M).card) : K :=
  ((values T M).equivFin.symm s : K)

theorem theValue_eq_iff (T : Q → Q → Q → K) (M : ℕ) (s : Fin (values T M).card) (v : values T M) :
    (v : K) = theValue T M s ↔ s = (values T M).equivFin v := by
  rw [theValue, ← Equiv.symm_apply_eq, Subtype.ext_iff, eq_comm]

open Classical in
/-- The table that tests the value. -/
noncomputable def valueTest (T : Q → Q → Q → K) (M : ℕ) (x : (Fin M → Q) × Fin (values T M).card)
    (y z : Fin M → Q) : K :=
  if tpow T M x.1 y z = theValue T M x.2 then 1 else 0

theorem valueTest_restricts (T : Q → Q → Q → K) (M : ℕ) :
    (hat (tpow T M)).Restricts (hat (valueTest T M)) := by
  classical
  let _ : DecidableEq Old := fun a b => Classical.propDecidable (a = b)
  let V := Fin (values T M).card
  let A := Fin M → Q
  let N : ∀ i, OLeg A A A i → OLeg (A × V) A A i → K := fun i =>
    match i with
    | .o1 => fun a b => if b.1.1 = a.1 ∧ b.2 = a.2 then theValue T M b.1.2 else 0
    | .o2 => fun a b => if b = a then 1 else 0
    | .o3 => fun a b => if b.1 = a.1 ∧ b.2.1 = a.2 then 1 else 0
    | .m2 => fun _ _ => 1
    | .m3 => fun _ _ => 1
  have key : ∀ a : ∀ i, OLeg A A A i, ind K (Agree a) * tpow T M (a .o1).1 (a .o1).2 (a .o2).2 =
      ∑ b : ∀ i, OLeg (A × V) A A i, ind K (Agree b) * valueTest T M (b .o1).1 (b .o1).2 (b .o2).2 *
        ∏ i, N i (a i) (b i) := by
    intro a
    have prod (b : ∀ i, OLeg (A × V) A A i) : ∏ i, N i (a i) (b i) =
        (if (b .o1).1.1 = (a .o1).1 ∧ (b .o1).2 = (a .o1).2 then theValue T M (b .o1).1.2 else 0) *
        ((if b .o2 = a .o2 then 1 else 0) *
          (if (b .o3).1 = (a .o3).1 ∧ (b .o3).2.1 = (a .o3).2 then 1 else 0)) := by
      rw [prod_old]
      simp [N]
    -- the only term
    let v : values T M := ⟨tpow T M (a .o1).1 (a .o1).2 (a .o2).2, mem_values T M _ _ _⟩
    let σ : V := (values T M).equivFin v
    have hσv : tpow T M (a .o1).1 (a .o1).2 (a .o2).2 = theValue T M σ := (theValue_eq_iff T M σ v).mpr rfl
    let b0 : ∀ i, OLeg (A × V) A A i := fun i =>
      match i with
      | .o1 => (((a .o1).1, σ), (a .o1).2)
      | .o2 => a .o2
      | .o3 => ((a .o3).1, ((a .o3).2, σ))
      | .m2 => PUnit.unit
      | .m3 => PUnit.unit
    rw [Finset.sum_eq_single b0]
    · rw [prod]
      by_cases h : Agree a
      · have h' : Agree b0 := ⟨Prod.ext h.1 rfl, h.2.1, h.2.2⟩
        rw [ind_true h, ind_true h']
        simp [b0, valueTest, ← hσv]
      · have h' : ¬ Agree b0 := by
          rintro ⟨h1, h2, h3⟩
          exact h ⟨congrArg Prod.fst h1, h2, h3⟩
        rw [ind_false h, ind_false h', zero_mul, zero_mul, zero_mul]
    · intro b _ hb
      by_contra h0
      obtain ⟨hc, hp⟩ := mul_ne_zero_iff.mp h0
      rw [prod] at hp
      obtain ⟨p1, p23⟩ := mul_ne_zero_iff.mp hp
      obtain ⟨p2, p3⟩ := mul_ne_zero_iff.mp p23
      have q1 : (b .o1).1.1 = (a .o1).1 ∧ (b .o1).2 = (a .o1).2 := by
        by_contra h; exact p1 (ite_eq_right h)
      have q2 : b .o2 = a .o2 := by
        by_contra h; exact p2 (ite_eq_right h)
      have q3 : (b .o3).1 = (a .o3).1 ∧ (b .o3).2.1 = (a .o3).2 := by
        by_contra h; exact p3 (ite_eq_right h)
      obtain ⟨hc1, hc2⟩ := mul_ne_zero_iff.mp hc
      have ha : Agree b := by
        by_contra h; exact hc1 (ind_false h)
      have hv : tpow T M (b .o1).1.1 (b .o1).2 (b .o2).2 = theValue T M (b .o1).1.2 := by
        by_contra h; exact hc2 (ite_eq_right h)
      rw [q1.1, q1.2, q2] at hv
      have hσ : (b .o1).1.2 = σ := (theValue_eq_iff T M _ v).mp hv
      apply hb
      funext i
      cases i
      · exact Prod.ext (Prod.ext q1.1 hσ) q1.2
      · exact q2
      · refine Prod.ext q3.1 (Prod.ext q3.2 ?_)
        have := congrArg Prod.snd ha.1
        exact this.symm.trans hσ
      · rfl
      · rfl
    · intro h
      exact absurd (Finset.mem_univ b0) h
  exact ⟨N, key⟩

end zeroOne

/-- A zero-one table whose lift is more expensive than the matrix product. -/
theorem exists_zero_one (P : SpectralPlacementPrices K Plane) :
    ∃ (X Y Z : Type) (_ : Fintype X) (_ : Fintype Y) (_ : Fintype Z) (_ : Nonempty X) (_ : Nonempty Y) (_ : Nonempty Z)
      (S : X → Y → Z → Prop) (_ : ∀ x y z, Decidable (S x y z)),
      logb 2 (Fintype.card X) + logb 2 (Fintype.card Y) + logb 2 (Fintype.card Z) <
        P.price (hat fun x y z => if S x y z then (1 : K) else 0) place := by
  classical
  obtain ⟨m, T, hT⟩ := exists_table P
  have hne : (hat T).coeff ≠ 0 := by
    intro h
    rw [P.zero_tensor _ h] at hT
    have : (0 : ℝ) ≤ 3 * m := by positivity
    linarith
  have : Nonempty (Bits m) := by
    rw [← Fintype.card_pos_iff, card_bits]
    positivity
  set η := P.price (hat T) place - 3 * m with hη
  have hη0 : 0 < η := by linarith
  set q := Fintype.card (Bits m × Bits m × Bits m) with hq
  -- the power
  have lim : Filter.Tendsto (fun k : ℕ => (k : ℝ) ^ 1 / 2 ^ k) Filter.atTop (nhds 0) :=
    tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num)
  have ev := lim.eventually (gt_mem_nhds (show (0 : ℝ) < η / (2 * (q + 1)) by positivity))
  obtain ⟨k, hk⟩ := (ev.and (Filter.eventually_ge_atTop 1)).exists
  obtain ⟨hk1, hk2⟩ := hk
  let M := 2 ^ k - 1
  have hM : M + 1 = 2 ^ k := Nat.sub_add_cancel (Nat.one_le_two_pow)
  let A := Fin M → Bits m
  let V := Fin (values T M).card
  have hVne : Nonempty V := ⟨(values T M).equivFin ⟨_, mem_values T M (fun _ => Classical.arbitrary _)
    (fun _ => Classical.arbitrary _) (fun _ => Classical.arbitrary _)⟩⟩
  refine ⟨A × V, A, A, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    fun x y z => tpow T M x.1 y z = theValue T M x.2, fun x y z => inferInstance, ?_⟩
  have cardA : logb 2 (Fintype.card A : ℝ) = M * m := by
    have : Fintype.card A = (2 ^ m) ^ M := by
      rw [Fintype.card_fun, card_bits, Fintype.card_fin]
    rw [this]
    push_cast
    rw [logb_pow, logb_pow, logb_self_eq_one (by norm_num), mul_one]
  have hV0 : 0 < Fintype.card V := Fintype.card_pos
  have hA0 : 0 < Fintype.card A := Fintype.card_pos
  have cardV : logb 2 (Fintype.card V : ℝ) ≤ q * k := by
    have h1 : (Fintype.card V : ℝ) ≤ ((2 : ℝ) ^ k) ^ q := by
      rw [Fintype.card_fin]
      have := card_values T M
      rw [hM] at this
      exact_mod_cast this
    have h2 := logb_le_logb_of_le (b := 2) (by norm_num) (by exact_mod_cast hV0) h1
    rw [logb_pow, logb_pow, logb_self_eq_one (by norm_num), mul_one] at h2
    exact h2
  have cardAV : logb 2 (Fintype.card (A × V) : ℝ) = M * m + logb 2 (Fintype.card V : ℝ) := by
    rw [Fintype.card_prod]
    push_cast
    rw [logb_mul (by exact_mod_cast hA0.ne') (by exact_mod_cast hV0.ne'), cardA]
  rw [cardAV, cardA]
  have up : M * P.price (hat T) place ≤ P.price (hat (valueTest T M)) place :=
    (price_pow P T hne M).trans (price_mono P (valueTest_restricts T M) place)
  have e : P.price (hat (valueTest T M)) place =
      P.price (hat fun (x : A × V) (y z : A) => if tpow T M x.1 y z = theValue T M x.2 then (1 : K) else 0) place := by
    congr!
  refine lt_of_lt_of_le ?_ (up.trans e.le)
  have hP : P.price (hat T) place = 3 * m + η := by rw [hη]; ring
  rw [hP]
  -- `q k < M η`
  have hMr : (M : ℝ) = 2 ^ k - 1 := by
    have : (M : ℝ) + 1 = 2 ^ k := by exact_mod_cast hM
    linarith
  have h2k : (2 : ℝ) ≤ 2 ^ k := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk2
  have hkk : (k : ℝ) * (2 * (q + 1)) < η * 2 ^ k := by
    rw [pow_one, div_lt_div_iff₀ (by positivity) (by positivity)] at hk1
    exact hk1
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk2
  have : (q : ℝ) * k < M * η := by
    rw [hMr]
    nlinarith
  linarith

/-! ### From powers to all lengths -/

/-- From powers to all large lengths. -/
theorem exponential_of_powers {R : ℕ → ℕ → Prop} {c : ℝ} (hc : 0 < c) (z : ℕ)
    (h : ∀ N n J : ℕ, N * z ≤ n → R n J → 1 ≤ J ∧ N * c ≤ logb 2 J) :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ J : ℕ, R n J → (2 : ℝ) ^ (c * n) ≤ J := by
  have hz : 0 < z + 1 := Nat.succ_pos _
  refine ⟨c / (2 * ((z + 1 : ℕ) : ℝ)), by positivity, 2 * (z + 1), fun n hn J hJ => ?_⟩
  set w := z + 1 with hw
  let N := n / w
  have hNz : N * z ≤ n := by
    calc N * z ≤ N * w := Nat.mul_le_mul_left _ (Nat.le_succ _)
      _ ≤ n := Nat.div_mul_le_self n w
  obtain ⟨hJ1, hlog⟩ := h N n J hNz hJ
  -- `N ≥ n / (2 w)`
  have hN : (n : ℝ) ≤ 2 * w * N := by
    have h1 : n < (N + 1) * w := by
      have := Nat.lt_div_mul_add (a := n) hz
      have e : (N + 1) * w = n / w * w + w := by ring
      omega
    have h2 : w ≤ N * w := by
      have : 2 ≤ N := (Nat.le_div_iff_mul_le hz).mpr hn
      nlinarith
    have h3 : n ≤ 2 * w * N := by nlinarith
    exact_mod_cast h3
  have hJ0 : (0 : ℝ) < J := by exact_mod_cast hJ1
  rw [← logb_le_logb (b := 2) (by norm_num) (rpow_pos_of_pos (by norm_num) _) hJ0,
    logb_rpow (by norm_num) (by norm_num)]
  have hwr : (0 : ℝ) < w := by exact_mod_cast hz
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  have h4 := mul_le_mul_of_nonneg_left hN hc.le
  have h5 := mul_le_mul_of_nonneg_left hlog (show (0 : ℝ) ≤ 2 * w by positivity)
  nlinarith

end NOF
