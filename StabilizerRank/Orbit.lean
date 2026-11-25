import StabilizerRank.Clifford

/-!
# Every quadratic phase on an affine subspace is in the orbit of `|0…0⟩`

With `stab_of_isStabilizer`: the orbit of the multiples of `|0…0⟩` under `H`, `S`, `CNOT` is the set of the quadratic phases on
affine subspaces (the standard form of stabilizer vectors).
-/

namespace StabilizerRank

open NOF

variable {F : Type*} [Field F] {ι : F} {Q : Type} [Fintype Q] [DecidableEq Q] {ψ : (Q → ZMod 2) → F}

theorem orbit_congr {ψ' : (Q → ZMod 2) → F} (h : IsStabilizer ι ψ) (e : ∀ b, ψ' b = ψ b) : IsStabilizer ι ψ' := by
  have : ψ' = ψ := funext e
  rwa [this]

theorem orbit_smul (h : IsStabilizer ι ψ) (a : F) : IsStabilizer ι (fun b => a * ψ b) := by
  induction h with
  | zeros c =>
    refine orbit_congr (IsStabilizer.zeros (a * c)) fun b => ?_
    rw [mul_ite, mul_zero]
  | hadamard k ψ _ ih =>
    refine orbit_congr (ih.hadamard k) fun b => ?_
    ring
  | phase k ψ _ ih =>
    refine orbit_congr (ih.phase k) fun b => ?_
    ring
  | cnot k l hkl ψ _ ih => exact ih.cnot k l hkl

theorem update_bit (b : Q → ZMod 2) (k : Q) {a : ZMod 2} (h : b k = a) : Function.update b k a = b := by
  rw [← h, Function.update_eq_self]

section two

variable (hι : ι ^ 2 = -1) (h2 : (2 : F) ≠ 0)

theorem orbit_s (h : IsStabilizer ι ψ) (k : Q) : IsStabilizer ι (fun b => tg ι (b k) * ψ b) :=
  orbit_congr (h.phase k) fun b => by rw [tg_eq_pow]

include hι in
/-- All fourth roots of unity. -/
theorem orbit_tg {κ : F} (hκ : κ ^ 4 = 1) (h : IsStabilizer ι ψ) (k : Q) : IsStabilizer ι (fun b => tg κ (b k) * ψ b) := by
  have e : (κ - 1) * ((κ + 1) * ((κ - ι) * (κ + ι))) = 0 := by
    have e1 : (κ - 1) * ((κ + 1) * ((κ - ι) * (κ + ι))) = (κ ^ 2 - 1) * (κ ^ 2 - ι ^ 2) := by ring
    rw [e1, hι]
    have e2 : (κ ^ 2 - 1) * (κ ^ 2 - -1) = κ ^ 4 - 1 := by ring
    rw [e2, hκ, sub_self]
  rcases mul_eq_zero.mp e with e | e
  · refine orbit_congr h fun b => ?_
    rw [sub_eq_zero.mp e]
    simp [tg]
  rcases mul_eq_zero.mp e with e | e
  · refine orbit_congr (orbit_s (orbit_s h k) k) fun b => ?_
    rw [eq_neg_of_add_eq_zero_left e]
    rcases z2_cases (b k) with h1 | h1 <;> rw [h1]
    · simp [tg]
    · simp only [tg, one_ne, if_false]
      rw [← mul_assoc, ← pow_two, hι]
  rcases mul_eq_zero.mp e with e | e
  · rw [sub_eq_zero.mp e]
    exact orbit_s h k
  · refine orbit_congr (orbit_s (orbit_s (orbit_s h k) k) k) fun b => ?_
    rw [eq_neg_of_add_eq_zero_left e]
    rcases z2_cases (b k) with h1 | h1 <;> rw [h1]
    · simp [tg]
    · simp only [tg, one_ne, if_false]
      rw [← mul_assoc ι ι, ← pow_two, hι]
      ring

include hι h2 in
/-- The gate `X`. -/
theorem orbit_x (h : IsStabilizer ι ψ) (k : Q) : IsStabilizer ι (fun b => ψ (Function.update b k (b k + 1))) := by
  have h4 : (-1 : F) ^ 4 = 1 := by norm_num
  have h3 := orbit_smul ((orbit_tg hι h4 (h.hadamard k) k).hadamard k) (2⁻¹)
  refine orbit_congr h3 fun b => ?_
  simp only [Function.update_self, Function.update_idem]
  have e1 : (1 : ZMod 2).val = 1 := rfl
  have e0 : (0 : ZMod 2).val = 0 := rfl
  rcases z2_cases (b k) with hb | hb <;> rw [hb]
  · simp only [tg, one_ne, if_false, if_true, e0, e1, pow_zero, pow_one, zero_add]
    field_simp
    ring
  · have : (1 : ZMod 2) + 1 = 0 := by decide
    simp only [this, tg, one_ne, if_false, if_true, e0, e1, pow_zero, pow_one]
    field_simp
    ring

include hι h2 in
/-- Translations. -/
theorem orbit_translate (h : IsStabilizer ι ψ) (w : Q → ZMod 2) : IsStabilizer ι (fun b => ψ (w + b)) := by
  have key : ∀ s : Finset Q, IsStabilizer ι (fun b => ψ ((fun q => if q ∈ s then w q else 0) + b)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      refine orbit_congr h fun b => ?_
      congr 1
      funext q
      simp
    | insert k s hk ih =>
      rcases z2_cases (w k) with hw | hw
      · refine orbit_congr ih fun b => ?_
        congr 2
        funext q
        by_cases hq : q = k
        · subst hq
          simp [hk, hw]
        · simp [hq]
      · refine orbit_congr (orbit_x hι h2 ih k) fun b => ?_
        congr 1
        funext q
        by_cases hq : q = k
        · subst hq
          simp [hk, hw, add_comm]
        · simp [hq]
  refine orbit_congr (key Finset.univ) fun b => ?_
  congr 2
  funext q
  simp

include h2 in
/-- The gate `CZ`. -/
theorem orbit_cz (h : IsStabilizer ι ψ) {k l : Q} (hkl : k ≠ l) : IsStabilizer ι (fun b => sg F (b l * b k) * ψ b) := by
  have h3 := orbit_smul (((h.hadamard l).cnot k l hkl).hadamard l) (2⁻¹)
  refine orbit_congr h3 fun b => ?_
  simp only [Function.update_self, Function.update_idem, Function.update_of_ne hkl]
  have e1 : (1 : ZMod 2).val = 1 := rfl
  have e0 : (0 : ZMod 2).val = 0 := rfl
  have e2 : (1 : ZMod 2) + 1 = 0 := by decide
  rcases z2_cases (b l) with hb | hb <;> rcases z2_cases (b k) with hc | hc <;> rw [hb, hc] <;>
    simp only [e2, sg, mul_zero, zero_mul, mul_one, one_ne, if_false, if_true, e0, e1, pow_zero, pow_one, zero_add, add_zero] <;>
    rw [update_bit b l hb] <;> field_simp <;> ring

include hι h2 in
theorem orbit_eps {ε : F} (hε : ε * ε = 1) (h : IsStabilizer ι ψ) {k l : Q} (hkl : k ≠ l) :
    IsStabilizer ι (fun b => tg ε (b l * b k) * ψ b) := by
  rcases mul_self_eq_one_iff.mp hε with rfl | rfl
  · refine orbit_congr h fun b => ?_
    simp [tg]
  · exact orbit_cz h2 h hkl

/-! ### Quadratic phases -/

/-- The restriction of a string to a set of coordinates. -/
def res (s : Finset Q) (b : Q → ZMod 2) : Q → ZMod 2 := fun q => if q ∈ s then b q else 0

theorem res_insert {s : Finset Q} {k : Q} (hk : k ∉ s) (b : Q → ZMod 2) :
    res (insert k s) b = res s b + b k • (Pi.single k 1 : Q → ZMod 2) := by
  funext q
  by_cases hq : q = k
  · subst hq
    simp [res, hk]
  · simp [res, hq]

include hι h2 in
theorem orbit_form {φ : (Q → ZMod 2) → F} (hφ : IsPhase φ) {k : Q} (s : Finset Q) (hk : k ∉ s) (h : IsStabilizer ι ψ) :
    IsStabilizer ι (fun b => form φ (res s b) (b k • (Pi.single k 1 : Q → ZMod 2)) * ψ b) := by
  induction s using Finset.induction_on with
  | empty =>
    refine orbit_congr h fun b => ?_
    have : res ∅ b = 0 := by
      funext q
      simp [res]
    rw [this, hφ.form_zero, one_mul]
  | insert l s hl ih =>
    have hkl : k ≠ l := fun h0 => hk (h0 ▸ Finset.mem_insert_self l s)
    have hks : k ∉ s := fun h0 => hk (Finset.mem_insert_of_mem h0)
    set ε := form φ (Pi.single l 1 : Q → ZMod 2) (Pi.single k 1 : Q → ZMod 2) with hε
    refine orbit_congr (orbit_eps hι h2 (ε := ε) (hφ.form_sq _ _) (ih hks) hkl) fun b => ?_
    rw [res_insert hl, hφ.mul]
    have e : form φ (b l • (Pi.single l 1 : Q → ZMod 2)) (b k • (Pi.single k 1 : Q → ZMod 2)) = tg ε (b l * b k) := by
      rcases z2_cases (b l) with hb | hb <;> rcases z2_cases (b k) with hc | hc <;> rw [hb, hc]
      · rw [zero_smul, hφ.form_zero]
        simp [tg]
      · rw [zero_smul, hφ.form_zero]
        simp [tg]
      · rw [zero_smul, IsPhase.form_comm, hφ.form_zero]
        simp [tg]
      · rw [one_smul, one_smul]
        simp [tg, hε]
    rw [e]
    ring

include hι h2 in
/-- Multiplication with a quadratic phase. -/
theorem orbit_phase {φ : (Q → ZMod 2) → F} (hφ : IsPhase φ) (h : IsStabilizer ι ψ) :
    IsStabilizer ι (fun b => φ b * ψ b) := by
  have key : ∀ s : Finset Q, IsStabilizer ι (fun b => φ (res s b) * ψ b) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      refine orbit_congr h fun b => ?_
      have : res ∅ b = 0 := by
        funext q
        simp [res]
      rw [this, hφ.zero, one_mul]
    | insert k s hk ih =>
      have h4 : φ (Pi.single k 1 : Q → ZMod 2) ^ 4 = 1 := by
        have e : φ (Pi.single k 1 : Q → ZMod 2) ^ 4 = (φ (Pi.single k 1) * φ (Pi.single k 1)) *
          (φ (Pi.single k 1) * φ (Pi.single k 1)) := by ring
        rw [e, hφ.sq, hφ.form_sq]
      refine orbit_congr (orbit_tg hι h4 (orbit_form hι h2 hφ s hk ih) k) fun b => ?_
      rw [res_insert hk, hφ.add]
      have e : φ (b k • (Pi.single k 1 : Q → ZMod 2)) = tg (φ (Pi.single k 1)) (b k) := by
        rcases z2_cases (b k) with hc | hc <;> rw [hc]
        · rw [zero_smul, hφ.zero]
          simp [tg]
        · rw [one_smul]
          simp [tg]
      rw [e]
      ring
  refine orbit_congr (key Finset.univ) fun b => ?_
  congr 2
  funext q
  simp [res]

end two

/-! ### Linear maps -/

theorem orbit_cnot (h : IsStabilizer ι ψ) {k l : Q} (hkl : k ≠ l) (a : ZMod 2) :
    IsStabilizer ι (fun b => ψ (Function.update b l (b l + b k * a))) := by
  rcases z2_cases a with rfl | rfl
  · refine orbit_congr h fun b => ?_
    rw [mul_zero, add_zero, Function.update_eq_self]
  · refine orbit_congr (h.cnot k l hkl) fun b => ?_
    rw [mul_one]

/-- `CNOT` gates with one control. -/
theorem orbit_out (h : IsStabilizer ι ψ) (k : Q) (d : Q → ZMod 2) (hd : d k = 0) :
    IsStabilizer ι (fun b => ψ (b + b k • d)) := by
  have key : ∀ s : Finset Q, k ∉ s → IsStabilizer ι (fun b => ψ (fun q => b q + if q ∈ s then b k * d q else 0)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      refine orbit_congr h fun b => ?_
      congr 1
      funext q
      simp
    | insert l s hl ih =>
      intro hk
      have hkl : k ≠ l := fun h0 => hk (h0 ▸ Finset.mem_insert_self l s)
      have hks : k ∉ s := fun h0 => hk (Finset.mem_insert_of_mem h0)
      refine orbit_congr (orbit_cnot (ih hks) hkl (d l)) fun b => ?_
      congr 1
      funext q
      by_cases hq : q = l
      · subst hq
        simp [hl]
      · simp [hq, Function.update_of_ne hkl]
  refine orbit_congr (key (Finset.univ.erase k) (Finset.notMem_erase k _)) fun b => ?_
  congr 1
  funext q
  by_cases hq : q = k
  · subst hq
    simp [hd]
  · simp [hq]

/-- `CNOT` gates with one target. -/
theorem orbit_in (h : IsStabilizer ι ψ) (k : Q) (L : Q → ZMod 2) :
    IsStabilizer ι (fun b => ψ (Function.update b k (b k + ∑ j ∈ Finset.univ.erase k, b j * L j))) := by
  have key : ∀ s : Finset Q, k ∉ s → IsStabilizer ι (fun b => ψ (Function.update b k (b k + ∑ j ∈ s, b j * L j))) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      refine orbit_congr h fun b => ?_
      rw [Finset.sum_empty, add_zero, Function.update_eq_self]
    | insert l s hl ih =>
      intro hk
      have hkl : l ≠ k := fun h0 => hk (h0 ▸ Finset.mem_insert_self l s)
      have hks : k ∉ s := fun h0 => hk (Finset.mem_insert_of_mem h0)
      refine orbit_congr (orbit_cnot (ih hks) hkl (L l)) fun b => ?_
      congr 1
      rw [Function.update_self, Function.update_idem, Finset.sum_insert hl, add_assoc]
      congr 3
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Function.update_of_ne]
      rintro rfl
      exact hks hj
  exact key _ (Finset.notMem_erase k _)

/-- One more vector in the subspace. -/
theorem orbit_sup {U : Submodule (ZMod 2) (Q → ZMod 2)} {v : Q → ZMod 2} (hv : v ∉ U)
    (h : IsStabilizer ι (fun b => ind F (b ∈ U))) :
    IsStabilizer ι (fun b => ind F (b ∈ Submodule.span (ZMod 2) {v} ⊔ U)) := by
  obtain ⟨ℓ, hℓv, hℓU⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hv inferInstance
  have hU (u : Q → ZMod 2) (hu : u ∈ U) : ℓ u = 0 := by
    have : ℓ u ∈ U.map ℓ := ⟨u, hu, rfl⟩
    rw [hℓU] at this
    exact this
  have hv1 : ℓ v = 1 := (z2_cases (ℓ v)).resolve_left hℓv
  let L (q : Q) : ZMod 2 := ℓ (Pi.single q 1)
  have hℓ (x : Q → ZMod 2) : ℓ x = ∑ q, x q * L q := by
    conv_lhs => rw [← Finset.univ_sum_single x]
    rw [map_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    have : (Pi.single q (x q) : Q → ZMod 2) = x q • Pi.single q 1 := by
      rw [← Pi.single_smul, smul_eq_mul, mul_one]
    rw [this, map_smul, smul_eq_mul]
  obtain ⟨k, hk⟩ : ∃ k, v k * L k ≠ 0 := by
    by_contra hne
    push Not at hne
    rw [hℓ, Finset.sum_eq_zero fun q _ => hne q] at hv1
    exact absurd hv1 (by decide)
  have hvk : v k = 1 := (z2_cases (v k)).resolve_left (left_ne_zero_of_mul hk)
  have hLk : L k = 1 := (z2_cases (L k)).resolve_left (right_ne_zero_of_mul hk)
  set e : Q → ZMod 2 := Pi.single k 1 with he
  have hek : e k = 1 := by simp [e]
  set d : Q → ZMod 2 := v + e with hd
  have hdk : d k = 0 := by rw [hd, Pi.add_apply, hvk, hek]; decide
  have hℓe : ℓ e = 1 := hLk
  have hℓd : ℓ d = 0 := by rw [hd, map_add, hv1, hℓe]; decide
  have two (x : ZMod 2) : x + x = 0 := by rcases z2_cases x with rfl | rfl <;> decide
  have twov (x : Q → ZMod 2) : x + x = 0 := add_self' x
  -- the two involutions
  let E1 (x : Q → ZMod 2) : Q → ZMod 2 := x + x k • d
  let E2 (x : Q → ZMod 2) : Q → ZMod 2 := x + (ℓ x + x k) • e
  have E1k (x : Q → ZMod 2) : E1 x k = x k := by
    change x k + x k * d k = x k
    rw [hdk, mul_zero, add_zero]
  have E1ℓ (x : Q → ZMod 2) : ℓ (E1 x) = ℓ x := by
    change ℓ (x + x k • d) = ℓ x
    rw [map_add, map_smul, hℓd, smul_zero, add_zero]
  have E11 (x : Q → ZMod 2) : E1 (E1 x) = x := by
    change E1 x + E1 x k • d = x
    rw [E1k]
    change x + x k • d + x k • d = x
    rw [add_assoc, twov, add_zero]
  have E2k (x : Q → ZMod 2) : E2 x k = ℓ x := by
    change x k + (ℓ x + x k) * e k = ℓ x
    rw [hek, mul_one, add_comm (ℓ x), ← add_assoc, two, zero_add]
  have E2ℓ (x : Q → ZMod 2) : ℓ (E2 x) = x k := by
    change ℓ (x + (ℓ x + x k) • e) = x k
    rw [map_add, map_smul, hℓe, smul_eq_mul, mul_one, ← add_assoc, two, zero_add]
  have E22 (x : Q → ZMod 2) : E2 (E2 x) = x := by
    change E2 x + (ℓ (E2 x) + E2 x k) • e = x
    rw [E2ℓ, E2k]
    change x + (ℓ x + x k) • e + (x k + ℓ x) • e = x
    rw [add_comm (x k), add_assoc, twov, add_zero]
  have E2eq (x : Q → ZMod 2) : E2 x = Function.update x k (x k + ∑ j ∈ Finset.univ.erase k, x j * L j) := by
    funext q
    by_cases hq : q = k
    · subst hq
      rw [Function.update_self, E2k, hℓ, ← Finset.add_sum_erase _ _ (Finset.mem_univ q), hLk, mul_one]
    · rw [Function.update_of_ne hq]
      change x q + (ℓ x + x k) * e q = x q
      have : e q = 0 := by simp [e, hq]
      rw [this, mul_zero, add_zero]
  have c1 {φ : (Q → ZMod 2) → F} (hφ : IsStabilizer ι φ) : IsStabilizer ι (fun b => φ (E1 b)) := orbit_out hφ k d hdk
  have c2 {φ : (Q → ZMod 2) → F} (hφ : IsStabilizer ι φ) : IsStabilizer ι (fun b => φ (E2 b)) :=
    orbit_congr (orbit_in hφ k L) fun b => by rw [E2eq]
  have upd (b : Q → ZMod 2) (t : ZMod 2) : E1 (E2 (Function.update b k t)) = E1 (E2 b) + (b k + t) • v := by
    have u : Function.update b k t = b + (b k + t) • e := by
      funext q
      by_cases hq : q = k
      · subst hq
        rw [Function.update_self]
        change t = b q + (b q + t) * e q
        rw [hek, mul_one, ← add_assoc, two, zero_add]
      · rw [Function.update_of_ne hq]
        change b q = b q + (b k + t) * e q
        have : e q = 0 := by simp [e, hq]
        rw [this, mul_zero, add_zero]
    have u2 : E2 (Function.update b k t) = E2 b + (b k + t) • e := by
      change Function.update b k t + (ℓ (Function.update b k t) + Function.update b k t k) • e = b + (ℓ b + b k) • e + (b k + t) • e
      rw [Function.update_self, u, map_add, map_smul, hℓe, smul_eq_mul, mul_one]
      have : ℓ b + (b k + t) + t = ℓ b + b k := by
        rw [add_assoc, add_assoc (b k), two, add_zero]
      rw [this]
      abel
    rw [u2]
    change E2 b + (b k + t) • e + (E2 b + (b k + t) • e) k • d = E2 b + E2 b k • d + (b k + t) • v
    have : (E2 b + (b k + t) • e) k = E2 b k + (b k + t) := by
      change E2 b k + (b k + t) * e k = _
      rw [hek, mul_one]
    rw [this, add_smul (E2 b k)]
    have ev : (b k + t) • v = (b k + t) • e + (b k + t) • d := by
      rw [← smul_add, hd]
      congr 1
      rw [add_comm v, ← add_assoc, twov, zero_add]
    rw [ev]
    abel
  have h3 := c1 (c2 ((c2 (c1 h)).hadamard k))
  refine orbit_congr h3 fun b => ?_
  beta_reduce
  set x := E2 (E1 b) with hx
  have hxb : E1 (E2 x) = b := by rw [hx, E22, E11]
  have hxk : x k = ℓ b := by rw [hx, E2k, E1ℓ]
  rw [upd, upd, hxb, hxk, add_zero]
  have n1 : b + (ℓ b + 1) • v ∉ U := by
    intro h0
    have := hU _ h0
    rw [map_add, map_smul, hv1, smul_eq_mul, mul_one, ← add_assoc, two, zero_add] at this
    exact absurd this (by decide)
  rw [ind_false n1, mul_zero, add_zero]
  apply ind_congr
  rw [Submodule.mem_sup]
  constructor
  · rintro ⟨y, hy, z, hz, rfl⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
    have : ℓ (c • v + z) = c := by rw [map_add, map_smul, hv1, hU z hz, smul_eq_mul, mul_one, add_zero]
    rw [this, add_comm (c • v), add_assoc, twov, add_zero]
    exact hz
  · intro h0
    refine ⟨ℓ b • v, Submodule.mem_span_singleton.mpr ⟨ℓ b, rfl⟩, b + ℓ b • v, h0, ?_⟩
    rw [add_comm b, ← add_assoc, twov, zero_add]

/-- Indicators of subspaces. -/
theorem orbit_subspace (U : Submodule (ZMod 2) (Q → ZMod 2)) : IsStabilizer ι (fun b => ind F (b ∈ U)) := by
  classical
  obtain ⟨S, hS⟩ : U.FG := IsNoetherian.noetherian U
  subst hS
  induction S using Finset.induction_on with
  | empty =>
    refine orbit_congr (IsStabilizer.zeros 1) fun b => ?_
    rw [Finset.coe_empty, Submodule.span_empty, ind_congr (Submodule.mem_bot _), ind_eq_ite]
  | insert v S _ ih =>
    rw [Finset.coe_insert, Submodule.span_insert]
    by_cases hv : v ∈ Submodule.span (ZMod 2) (S : Set (Q → ZMod 2))
    · rwa [sup_eq_right.mpr ((Submodule.span_singleton_le_iff_mem v _).mpr hv)]
    · exact orbit_sup hv ih

/-- **Every quadratic phase on an affine subspace is a stabilizer vector.** -/
theorem isStabilizer_of_stab (hι : ι ^ 2 = -1) (h2 : (2 : F) ≠ 0) (h : Stab ψ) : IsStabilizer ι ψ := by
  obtain ⟨U, w₀, c, φ, hφ, h⟩ := h
  refine orbit_congr (orbit_translate hι h2 (orbit_smul (orbit_phase hι h2 hφ (orbit_subspace U)) c) w₀) fun b => ?_
  have e : b - w₀ = w₀ + b := by
    rw [sub_eq_iff_eq_add, add_comm w₀, add_assoc, add_self', add_zero]
  rw [h, e]
  ring

/-- **The orbit of `|0…0⟩` under the Clifford gates is the set of quadratic phases on affine subspaces.** -/
theorem isStabilizer_iff (hι : ι ^ 2 = -1) (h2 : (2 : F) ≠ 0) : IsStabilizer ι ψ ↔ Stab ψ :=
  ⟨stab_of_isStabilizer h2 (by rw [show 4 = 2 * 2 from rfl, pow_mul, hι]; norm_num), isStabilizer_of_stab hι h2⟩

end StabilizerRank
