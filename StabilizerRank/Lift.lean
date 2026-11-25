import StabilizerRank.Push
import NOF.Main
import OAI.LinearAlgebra.SpectralBooks.TriangleSemiperimeter

/-!
# Stabilizer functions are cheap

The lift of a quadratic phase on an affine subspace to the three parties costs at most the number of bits.
-/

namespace StabilizerRank

open Real NOF OAI OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor OAI.Hierarchy
open scoped NNReal

variable {F : Type*} [Field F]

section general

variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]

/-- Multiplication by a cylinder function. -/
theorem mul_cylinder_restricts (T : X → Y → Z → F) (u : X → Y → F) (v : Y → Z → F) (w : Z → X → F) :
    (hat fun x y z => T x y z * (u x y * v y z * w z x)).Restricts (hat T) := by
  classical
  let _ : DecidableEq Old := fun a b => Classical.propDecidable (a = b)
  let M : ∀ i, OLeg X Y Z i → OLeg X Y Z i → F := fun i =>
    match i with
    | .o1 => fun a b => if b = a then u a.1 a.2 else 0
    | .o2 => fun a b => if b = a then v a.1 a.2 else 0
    | .o3 => fun a b => if b = a then w a.1 a.2 else 0
    | .m2 => fun _ _ => 1
    | .m3 => fun _ _ => 1
  have key : ∀ a : ∀ i, OLeg X Y Z i, ind F (Agree a) * (T (a .o1).1 (a .o1).2 (a .o2).2 *
        (u (a .o1).1 (a .o1).2 * v (a .o1).2 (a .o2).2 * w (a .o2).2 (a .o1).1)) =
      ∑ b : ∀ i, OLeg X Y Z i, ind F (Agree b) * T (b .o1).1 (b .o1).2 (b .o2).2 * ∏ i, M i (a i) (b i) := by
    intro a
    rw [Finset.sum_eq_single a]
    · have hp : ∏ i, M i (a i) (a i) = u (a .o1).1 (a .o1).2 * v (a .o2).1 (a .o2).2 * w (a .o3).1 (a .o3).2 := by
        rw [prod_old]
        simp [M, mul_assoc]
      rw [hp]
      by_cases h : Agree a
      · rw [ind_true h, one_mul, one_mul]
        obtain ⟨h1, h2, h3⟩ := h
        rw [← h2, ← h3, ← h1]
      · rw [ind_false h, zero_mul, zero_mul, zero_mul]
    · intro b _ hb
      obtain ⟨i, hi⟩ : ∃ i, b i ≠ a i := Function.ne_iff.mp hb
      have h0 : M i (a i) (b i) = 0 := by
        cases i
        · exact ite_eq_right hi
        · exact ite_eq_right hi
        · exact ite_eq_right hi
        · exact absurd rfl hi
        · exact absurd rfl hi
      rw [Finset.prod_eq_zero (Finset.mem_univ i) h0, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ a) h
  exact ⟨M, key⟩

/-- Renaming the labels. -/
theorem comp_restricts {X' Y' Z' : Type} [Fintype X'] [Fintype Y'] [Fintype Z'] (T : X' → Y' → Z' → F) {a : X → X'}
    {b : Y → Y'} {c : Z → Z'} (ha : Function.Injective a) (hb : Function.Injective b) (hc : Function.Injective c) :
    (hat fun x y z => T (a x) (b y) (c z)).Restricts (hat T) := by
  let read : ∀ i, OLeg X Y Z i → OLeg X' Y' Z' i := fun i =>
    match i with
    | .o1 => fun p => (a p.1, b p.2)
    | .o2 => fun p => (b p.1, c p.2)
    | .o3 => fun p => (c p.1, a p.2)
    | .m2 => fun _ => PUnit.unit
    | .m3 => fun _ => PUnit.unit
  refine restricts_of_read (S := hat fun x y z => T (a x) (b y) (c z)) (T := hat T) read fun p => ?_
  have key : ∀ p : ∀ i, OLeg X Y Z i, ind F (Agree p) * T (a (p .o1).1) (b (p .o1).2) (c (p .o2).2) =
      ind F (Agree fun i => read i (p i)) * T (a (p .o1).1) (b (p .o1).2) (c (p .o2).2) := by
    intro p
    congr 1
    apply ind_congr
    exact ⟨fun h => ⟨congrArg a h.1, congrArg b h.2.1, congrArg c h.2.2⟩, fun h => ⟨ha h.1, hb h.2.1, hc h.2.2⟩⟩
  exact key p

end general

/-! ### Four labels -/

/-- The label shared by the three vertices costs at most three halves. -/
theorem label3_price (P : SpectralPlacementPrices F Plane) (q : ℕ) (hq : 0 < q) :
    P.price ((Raw.diagonal (Fin 3) F (Fin q)).group ![Old.o1, Old.o2, Old.o3]) place ≤ 3 / 2 * logb 2 q := by
  classical
  rw [← P.group]
  have h1 := price_le_diagonal_mul_log_rank P (Raw.diagonal (Fin 3) F (Fin q)) (place ∘ ![Old.o1, Old.o2, Old.o3]) q
    (restrict_refl _)
  refine h1.trans ?_
  have hlog : 0 ≤ logb 2 (q : ℝ) := logb_nonneg (by norm_num) (by exact_mod_cast hq)
  refine mul_le_mul_of_nonneg_right ?_ hlog
  rw [P.price_binaryDiagonal_eq]
  have h2 := P.diagonal_triangle_le_half_perimeter (place .o1) (place .o2) (place .o3)
  have h3 := dist_comm (place .o3) (place .o1)
  rw [dist_o1_o2, dist_o2_o3, h3, dist_o1_o3] at h2
  refine le_trans (le_of_eq ?_) (h2.trans (by norm_num))
  congr 1
  ext x
  simp [Fin.exists_fin_succ, eq_comm]

theorem label3_coeff (q : ℕ) (u v w : Old) (x : ∀ i, ((Raw.diagonal (Fin 3) F (Fin q)).group ![u, v, w]).Leg i) :
    ((Raw.diagonal (Fin 3) F (Fin q)).group ![u, v, w]).coeff x =
      ind F (letter (q := q) (x u ⟨(0 : Fin 3), rfl⟩) = letter (q := q) (x v ⟨(1 : Fin 3), rfl⟩) ∧
        letter (q := q) (x w ⟨(2 : Fin 3), rfl⟩) = letter (q := q) (x v ⟨(1 : Fin 3), rfl⟩)) := by
  classical
  let lab : Fin 3 → Fin q := fun s => x (![u, v, w] s) ⟨s, rfl⟩
  change (Raw.diagonal (Fin 3) F (Fin q)).coeff lab = ind F (lab 0 = lab 1 ∧ lab 2 = lab 1)
  rw [Raw.diagonal_coeff_at (K := F) (1 : Fin 3) lab, ← ind_eq_ite]
  apply ind_congr
  refine ⟨fun h => ⟨h 0, h 2⟩, fun h i => ?_⟩
  fin_cases i
  · exact h.1
  · rfl
  · exact h.2

section quad

variable (A₁ A₂ A₃ A₀ : Type) [Fintype A₁] [Fintype A₂] [Fintype A₃] [Fintype A₀]

/-- The indices of four labels: `A₁` is shared by `o2, o3`, `A₂` by `o1, o3`, `A₃` by `o1, o2`, and `A₀` by all. -/
abbrev QLeg : Old → Type
  | .o1 => A₂ × A₃ × A₀
  | .o2 => A₃ × A₁ × A₀
  | .o3 => A₁ × A₂ × A₀
  | .m2 => PUnit
  | .m3 => PUnit

instance : ∀ i, Fintype (QLeg A₁ A₂ A₃ A₀ i)
  | .o1 => inferInstanceAs (Fintype (A₂ × A₃ × A₀))
  | .o2 => inferInstanceAs (Fintype (A₃ × A₁ × A₀))
  | .o3 => inferInstanceAs (Fintype (A₁ × A₂ × A₀))
  | .m2 => inferInstanceAs (Fintype PUnit)
  | .m3 => inferInstanceAs (Fintype PUnit)

variable {A₁ A₂ A₃ A₀}

def QAgree (b : ∀ i, QLeg A₁ A₂ A₃ A₀ i) : Prop :=
  ((b .o2).2.1 = (b .o3).1 ∧ (b .o1).1 = (b .o3).2.1) ∧ (b .o1).2.1 = (b .o2).1 ∧
    (b .o1).2.2 = (b .o2).2.2 ∧ (b .o3).2.2 = (b .o2).2.2

variable (F A₁ A₂ A₃ A₀)

noncomputable def quad : Raw.{0} Old F where
  Leg := QLeg A₁ A₂ A₃ A₀
  finiteLeg := inferInstance
  coeff b := ind F (QAgree b)

theorem quad_price (P : SpectralPlacementPrices F Plane) [Nonempty A₁] [Nonempty A₂] [Nonempty A₃] [Nonempty A₀] :
    P.price (quad F A₁ A₂ A₃ A₀) place ≤ logb 2 (Fintype.card A₁) + logb 2 (Fintype.card A₂) +
      logb 2 (Fintype.card A₃) + 3 / 2 * logb 2 (Fintype.card A₀) := by
  classical
  have h1 : 0 < Fintype.card A₁ := Fintype.card_pos
  have h2 : 0 < Fintype.card A₂ := Fintype.card_pos
  have h3 : 0 < Fintype.card A₃ := Fintype.card_pos
  have h0 : 0 < Fintype.card A₀ := Fintype.card_pos
  let e1 := Fintype.equivFin A₁
  let e2 := Fintype.equivFin A₂
  let e3 := Fintype.equivFin A₃
  let e0 := Fintype.equivFin A₀
  let W1 : Raw.{0} Old F := (Raw.diagonal (Fin 2) F (Fin (Fintype.card A₁))).group ![Old.o2, Old.o3]
  let W2 : Raw.{0} Old F := (Raw.diagonal (Fin 2) F (Fin (Fintype.card A₂))).group ![Old.o1, Old.o3]
  let W3 : Raw.{0} Old F := (Raw.diagonal (Fin 2) F (Fin (Fintype.card A₃))).group ![Old.o1, Old.o2]
  let W0 : Raw.{0} Old F := (Raw.diagonal (Fin 3) F (Fin (Fintype.card A₀))).group ![Old.o1, Old.o2, Old.o3]
  let T : Raw.{0} Old F := ((W1.mul W2).mul W3).mul W0
  let r1 : ∀ i, QLeg A₁ A₂ A₃ A₀ i → Fin (Fintype.card A₁) := fun i =>
    match i with
    | .o1 => fun _ => ⟨0, h1⟩
    | .o2 => fun a => e1 a.2.1
    | .o3 => fun a => e1 a.1
    | .m2 => fun _ => ⟨0, h1⟩
    | .m3 => fun _ => ⟨0, h1⟩
  let r2 : ∀ i, QLeg A₁ A₂ A₃ A₀ i → Fin (Fintype.card A₂) := fun i =>
    match i with
    | .o1 => fun a => e2 a.1
    | .o2 => fun _ => ⟨0, h2⟩
    | .o3 => fun a => e2 a.2.1
    | .m2 => fun _ => ⟨0, h2⟩
    | .m3 => fun _ => ⟨0, h2⟩
  let r3 : ∀ i, QLeg A₁ A₂ A₃ A₀ i → Fin (Fintype.card A₃) := fun i =>
    match i with
    | .o1 => fun a => e3 a.2.1
    | .o2 => fun a => e3 a.1
    | .o3 => fun _ => ⟨0, h3⟩
    | .m2 => fun _ => ⟨0, h3⟩
    | .m3 => fun _ => ⟨0, h3⟩
  let r0 : ∀ i, QLeg A₁ A₂ A₃ A₀ i → Fin (Fintype.card A₀) := fun i =>
    match i with
    | .o1 => fun a => e0 a.2.2
    | .o2 => fun a => e0 a.2.2
    | .o3 => fun a => e0 a.2.2
    | .m2 => fun _ => ⟨0, h0⟩
    | .m3 => fun _ => ⟨0, h0⟩
  have hr : (quad F A₁ A₂ A₃ A₀).Restricts T := by
    refine restricts_of_read (S := quad F A₁ A₂ A₃ A₀) (T := T)
      (fun i a => (((fun _ => r1 i a, fun _ => r2 i a), fun _ => r3 i a), fun _ => r0 i a)) fun a => ?_
    have key : ∀ a : ∀ i, QLeg A₁ A₂ A₃ A₀ i, ind F (QAgree a) =
        T.coeff (fun i => (((fun _ => r1 i (a i), fun _ => r2 i (a i)), fun _ => r3 i (a i)), fun _ => r0 i (a i))) := by
      intro a
      have w1 : W1.coeff (fun i _ => r1 i (a i)) = ind F (r1 .o2 (a .o2) = r1 .o3 (a .o3)) :=
        (wire_coeff _ Old.o2 Old.o3 (fun i _ => r1 i (a i))).trans (ind_eq_ite _).symm
      have w2 : W2.coeff (fun i _ => r2 i (a i)) = ind F (r2 .o1 (a .o1) = r2 .o3 (a .o3)) :=
        (wire_coeff _ Old.o1 Old.o3 (fun i _ => r2 i (a i))).trans (ind_eq_ite _).symm
      have w3 : W3.coeff (fun i _ => r3 i (a i)) = ind F (r3 .o1 (a .o1) = r3 .o2 (a .o2)) :=
        (wire_coeff _ Old.o1 Old.o2 (fun i _ => r3 i (a i))).trans (ind_eq_ite _).symm
      have w0 : W0.coeff (fun i _ => r0 i (a i)) = ind F (r0 .o1 (a .o1) = r0 .o2 (a .o2) ∧
          r0 .o3 (a .o3) = r0 .o2 (a .o2)) := label3_coeff _ Old.o1 Old.o2 Old.o3 (fun i _ => r0 i (a i))
      have e : T.coeff (fun i => (((fun _ => r1 i (a i), fun _ => r2 i (a i)), fun _ => r3 i (a i)), fun _ => r0 i (a i))) =
        W1.coeff (fun i _ => r1 i (a i)) * W2.coeff (fun i _ => r2 i (a i)) * W3.coeff (fun i _ => r3 i (a i)) *
          W0.coeff (fun i _ => r0 i (a i)) := rfl
      rw [e, w1, w2, w3, w0, ind_mul, ind_mul, ind_mul]
      apply ind_congr
      simp only [QAgree, r1, r2, r3, r0, EmbeddingLike.apply_eq_iff_eq]
      tauto
    exact key a
  refine (price_mono P hr place).trans ?_
  let U : Fin 4 → Raw.{0} Old F := ![W1, W2, W3, W0]
  have h := WirePrice.product P place T U (fun e => by
    fin_cases e
    · exact ((Raw.diagonal (Fin 2) F (Fin (Fintype.card A₁))).group_ne_zero_iff _).2 (diagonal_ne_zero _ h1)
    · exact ((Raw.diagonal (Fin 2) F (Fin (Fintype.card A₂))).group_ne_zero_iff _).2 (diagonal_ne_zero _ h2)
    · exact ((Raw.diagonal (Fin 2) F (Fin (Fintype.card A₃))).group_ne_zero_iff _).2 (diagonal_ne_zero _ h3)
    · exact ((Raw.diagonal (Fin 3) F (Fin (Fintype.card A₀))).group_ne_zero_iff _).2 (diagonal_ne_zero _ h0))
    (by rw [Fin.prod_univ_four]; rfl)
  rw [h, Fin.sum_univ_four]
  change P.price W1 place + P.price W2 place + P.price W3 place + P.price W0 place ≤ _
  have hw0 := label3_price P (Fintype.card A₀) h0
  rw [WirePrice.wire, WirePrice.wire, WirePrice.wire, dist_o1_o3, dist_o1_o2, dist_o2_o3, one_mul, one_mul, one_mul]
  linarith

end quad

/-! ### Subspaces -/

section subspace

variable {X Y Z : Type} [AddCommGroup X] [Module (ZMod 2) X] [Fintype X] [AddCommGroup Y] [Module (ZMod 2) Y] [Fintype Y]
  [AddCommGroup Z] [Module (ZMod 2) Z] [Fintype Z]

theorem subspace_price (P : SpectralPlacementPrices F Plane) (U : Submodule (ZMod 2) (X × Y × Z)) :
    P.price (hat fun (x : X) (y : Y) (z : Z) => ind F ((x, y, z) ∈ U)) place ≤
      logb 2 (Fintype.card X) + logb 2 (Fintype.card Y) + logb 2 (Fintype.card Z) := by
  classical
  let W := X × Y × Z
  let px : W →ₗ[ZMod 2] X := LinearMap.fst _ _ _
  let py : W →ₗ[ZMod 2] Y := (LinearMap.fst _ _ _).comp (LinearMap.snd _ _ _)
  let pz : W →ₗ[ZMod 2] Z := (LinearMap.snd _ _ _).comp (LinearMap.snd _ _ _)
  let K₁ := U ⊓ LinearMap.ker px ⊓ LinearMap.ker py
  let K₂ := U ⊓ LinearMap.ker py ⊓ LinearMap.ker pz
  let K₃ := U ⊓ LinearMap.ker px ⊓ LinearMap.ker pz
  have mem1 (w : W) : w ∈ K₁ ↔ w ∈ U ∧ px w = 0 ∧ py w = 0 := by
    change (w ∈ U ∧ px w = 0) ∧ py w = 0 ↔ _
    tauto
  have mem2 (w : W) : w ∈ K₂ ↔ w ∈ U ∧ py w = 0 ∧ pz w = 0 := by
    change (w ∈ U ∧ py w = 0) ∧ pz w = 0 ↔ _
    tauto
  have mem3 (w : W) : w ∈ K₃ ↔ w ∈ U ∧ px w = 0 ∧ pz w = 0 := by
    change (w ∈ U ∧ px w = 0) ∧ pz w = 0 ↔ _
    tauto
  have ext3 {w w' : W} (h1 : px w = px w') (h2 : py w = py w') (h3 : pz w = pz w') : w = w' :=
    Prod.ext h1 (Prod.ext h2 h3)
  let S := K₁ ⊔ K₂ ⊔ K₃
  have hS : S ≤ U := sup_le (sup_le (fun w h => ((mem1 w).mp h).1) (fun w h => ((mem2 w).mp h).1))
    (fun w h => ((mem3 w).mp h).1)
  obtain ⟨M, hM1, hM2⟩ : ∃ M : Submodule (ZMod 2) W, S ⊓ M = ⊥ ∧ S ⊔ M = U := by
    obtain ⟨C, hC⟩ := Submodule.exists_isCompl (Submodule.comap U.subtype S)
    refine ⟨C.map U.subtype, ?_, ?_⟩
    · rw [eq_bot_iff]
      rintro x ⟨hx1, hx2⟩
      obtain ⟨y, hy, rfl⟩ := hx2
      have : y ∈ Submodule.comap U.subtype S ⊓ C := ⟨hx1, hy⟩
      rw [hC.inf_eq_bot] at this
      rw [Submodule.mem_bot] at this
      rw [this]
      simp
    · have h3 := congrArg (Submodule.map U.subtype) hC.sup_eq_top
      rw [Submodule.map_sup, Submodule.map_comap_subtype, Submodule.map_subtype_top, inf_eq_right.mpr hS] at h3
      exact h3
  have hMU : M ≤ U := hM2 ▸ le_sup_right
  let _ : Fintype K₁ := Fintype.ofFinite _
  let _ : Fintype K₂ := Fintype.ofFinite _
  let _ : Fintype K₃ := Fintype.ofFinite _
  let _ : Fintype M := Fintype.ofFinite _
  -- uniqueness of the part in `M`
  have inS {d : W} (h : d ∈ S) {μ μ' : M} (e : d + μ = μ') : μ = μ' := by
    have h1 : (μ' - μ : W) ∈ S := by
      rw [← e, add_sub_cancel_right]
      exact h
    have h2 : (μ' - μ : W) ∈ S ⊓ M := ⟨h1, M.sub_mem μ'.2 μ.2⟩
    rw [hM1, Submodule.mem_bot, sub_eq_zero] at h2
    exact Subtype.ext h2.symm
  have hK1 (κ : K₁) : (κ : W) ∈ S := Submodule.mem_sup_left (Submodule.mem_sup_left κ.2)
  have hK2 (κ : K₂) : (κ : W) ∈ S := Submodule.mem_sup_left (Submodule.mem_sup_right κ.2)
  have hK3 (κ : K₃) : (κ : W) ∈ S := Submodule.mem_sup_right κ.2
  -- the coordinates seen by the parties
  let s12 (w : W) : X × Y := (px w, py w)
  let s23 (w : W) : Y × Z := (py w, pz w)
  let s31 (w : W) : Z × X := (pz w, px w)
  have inj12 : Function.Injective (fun p : K₂ × K₃ × M => s12 (p.1 + p.2.1 + p.2.2)) := by
    rintro ⟨κ₂, κ₃, μ⟩ ⟨κ₂', κ₃', μ'⟩ h
    have hx := congrArg Prod.fst h
    have hy := congrArg Prod.snd h
    simp only [s12, map_add] at hx hy
    have d1 : ((κ₂ : W) + κ₃ + μ) - (κ₂' + κ₃' + μ') ∈ K₁ := by
      rw [mem1]
      refine ⟨U.sub_mem (U.add_mem (U.add_mem (hS (hK2 _)) (hS (hK3 _))) (hMU μ.2))
        (U.add_mem (U.add_mem (hS (hK2 _)) (hS (hK3 _))) (hMU μ'.2)), ?_, ?_⟩
      · simp only [map_sub, map_add]
        rw [hx, sub_self]
      · simp only [map_sub, map_add]
        rw [hy, sub_self]
    have d2 : μ = μ' := by
      apply inS (d := -(((κ₂ : W) + κ₃ + μ) - (κ₂' + κ₃' + μ')) + (κ₂ - κ₂') + (κ₃ - κ₃'))
      · refine S.add_mem (S.add_mem (S.neg_mem ?_) (S.sub_mem (hK2 _) (hK2 _))) (S.sub_mem (hK3 _) (hK3 _))
        exact Submodule.mem_sup_left (Submodule.mem_sup_left d1)
      · abel
    subst d2
    have hx' := add_right_cancel hx
    have hy' := add_right_cancel hy
    have e2 := (mem2 κ₂).mp κ₂.2
    have e2' := (mem2 κ₂').mp κ₂'.2
    have e3 := (mem3 κ₃).mp κ₃.2
    have e3' := (mem3 κ₃').mp κ₃'.2
    rw [e3.2.1, e3'.2.1, add_zero, add_zero] at hx'
    rw [e2.2.1, e2'.2.1, zero_add, zero_add] at hy'
    have q2 : κ₂ = κ₂' := Subtype.ext (ext3 hx' (e2.2.1.trans e2'.2.1.symm) (e2.2.2.trans e2'.2.2.symm))
    have q3 : κ₃ = κ₃' := Subtype.ext (ext3 (e3.2.1.trans e3'.2.1.symm) hy' (e3.2.2.trans e3'.2.2.symm))
    rw [q2, q3]
  have inj23 : Function.Injective (fun p : K₃ × K₁ × M => s23 (p.1 + p.2.1 + p.2.2)) := by
    rintro ⟨κ₃, κ₁, μ⟩ ⟨κ₃', κ₁', μ'⟩ h
    have hy := congrArg Prod.fst h
    have hz := congrArg Prod.snd h
    simp only [s23, map_add] at hy hz
    have d1 : ((κ₃ : W) + κ₁ + μ) - (κ₃' + κ₁' + μ') ∈ K₂ := by
      rw [mem2]
      refine ⟨U.sub_mem (U.add_mem (U.add_mem (hS (hK3 _)) (hS (hK1 _))) (hMU μ.2))
        (U.add_mem (U.add_mem (hS (hK3 _)) (hS (hK1 _))) (hMU μ'.2)), ?_, ?_⟩
      · simp only [map_sub, map_add]
        rw [hy, sub_self]
      · simp only [map_sub, map_add]
        rw [hz, sub_self]
    have d2 : μ = μ' := by
      apply inS (d := -(((κ₃ : W) + κ₁ + μ) - (κ₃' + κ₁' + μ')) + (κ₃ - κ₃') + (κ₁ - κ₁'))
      · refine S.add_mem (S.add_mem (S.neg_mem ?_) (S.sub_mem (hK3 _) (hK3 _))) (S.sub_mem (hK1 _) (hK1 _))
        exact Submodule.mem_sup_left (Submodule.mem_sup_right d1)
      · abel
    subst d2
    have hy' := add_right_cancel hy
    have hz' := add_right_cancel hz
    have e1 := (mem1 κ₁).mp κ₁.2
    have e1' := (mem1 κ₁').mp κ₁'.2
    have e3 := (mem3 κ₃).mp κ₃.2
    have e3' := (mem3 κ₃').mp κ₃'.2
    rw [e1.2.2, e1'.2.2, add_zero, add_zero] at hy'
    rw [e3.2.2, e3'.2.2, zero_add, zero_add] at hz'
    have q1 : κ₁ = κ₁' := Subtype.ext (ext3 (e1.2.1.trans e1'.2.1.symm) (e1.2.2.trans e1'.2.2.symm) hz')
    have q3 : κ₃ = κ₃' := Subtype.ext (ext3 (e3.2.1.trans e3'.2.1.symm) hy' (e3.2.2.trans e3'.2.2.symm))
    rw [q1, q3]
  have inj31 : Function.Injective (fun p : K₁ × K₂ × M => s31 (p.1 + p.2.1 + p.2.2)) := by
    rintro ⟨κ₁, κ₂, μ⟩ ⟨κ₁', κ₂', μ'⟩ h
    have hz := congrArg Prod.fst h
    have hx := congrArg Prod.snd h
    simp only [s31, map_add] at hz hx
    have d1 : ((κ₁ : W) + κ₂ + μ) - (κ₁' + κ₂' + μ') ∈ K₃ := by
      rw [mem3]
      refine ⟨U.sub_mem (U.add_mem (U.add_mem (hS (hK1 _)) (hS (hK2 _))) (hMU μ.2))
        (U.add_mem (U.add_mem (hS (hK1 _)) (hS (hK2 _))) (hMU μ'.2)), ?_, ?_⟩
      · simp only [map_sub, map_add]
        rw [hx, sub_self]
      · simp only [map_sub, map_add]
        rw [hz, sub_self]
    have d2 : μ = μ' := by
      apply inS (d := -(((κ₁ : W) + κ₂ + μ) - (κ₁' + κ₂' + μ')) + (κ₁ - κ₁') + (κ₂ - κ₂'))
      · refine S.add_mem (S.add_mem (S.neg_mem ?_) (S.sub_mem (hK1 _) (hK1 _))) (S.sub_mem (hK2 _) (hK2 _))
        exact Submodule.mem_sup_right d1
      · abel
    subst d2
    have hx' := add_right_cancel hx
    have hz' := add_right_cancel hz
    have e1 := (mem1 κ₁).mp κ₁.2
    have e1' := (mem1 κ₁').mp κ₁'.2
    have e2 := (mem2 κ₂).mp κ₂.2
    have e2' := (mem2 κ₂').mp κ₂'.2
    rw [e1.2.1, e1'.2.1, zero_add, zero_add] at hx'
    rw [e2.2.2, e2'.2.2, add_zero, add_zero] at hz'
    have q1 : κ₁ = κ₁' := Subtype.ext (ext3 (e1.2.1.trans e1'.2.1.symm) (e1.2.2.trans e1'.2.2.symm) hz')
    have q2 : κ₂ = κ₂' := Subtype.ext (ext3 hx' (e2.2.1.trans e2'.2.1.symm) (e2.2.2.trans e2'.2.2.symm))
    rw [q1, q2]
  -- the cardinalities
  have c12 := Fintype.card_le_of_injective _ inj12
  have c23 := Fintype.card_le_of_injective _ inj23
  have c31 := Fintype.card_le_of_injective _ inj31
  -- the sum
  let Ψ (q : K₁ × K₂ × K₃ × M) : W := q.1 + q.2.1 + q.2.2.1 + q.2.2.2
  have hΨU (q : K₁ × K₂ × K₃ × M) : Ψ q ∈ U :=
    U.add_mem (U.add_mem (U.add_mem (hS (hK1 _)) (hS (hK2 _))) (hS (hK3 _))) (hMU q.2.2.2.2)
  have v12 (q : K₁ × K₂ × K₃ × M) : s12 (q.2.1 + q.2.2.1 + q.2.2.2) = s12 (Ψ q) := by
    have e1 := (mem1 q.1).mp q.1.2
    simp only [s12, Ψ, map_add]
    rw [e1.2.1, e1.2.2, zero_add, zero_add]
  have v23 (q : K₁ × K₂ × K₃ × M) : s23 (q.2.2.1 + q.1 + q.2.2.2) = s23 (Ψ q) := by
    have e2 := (mem2 q.2.1).mp q.2.1.2
    simp only [s23, Ψ, map_add]
    rw [e2.2.1, e2.2.2, add_zero, add_zero, add_comm (py (q.2.2.1 : W)), add_comm (pz (q.2.2.1 : W))]
  have v31 (q : K₁ × K₂ × K₃ × M) : s31 (q.1 + q.2.1 + q.2.2.2) = s31 (Ψ q) := by
    have e3 := (mem3 q.2.2.1).mp q.2.2.1.2
    simp only [s31, Ψ, map_add]
    rw [e3.2.1, e3.2.2, add_zero, add_zero]
  have hΨinj : Function.Injective Ψ := by
    intro q q' h
    have h1 := v12 q
    have h2 := v12 q'
    rw [h] at h1
    have h3 := inj12 (a₁ := (q.2.1, q.2.2.1, q.2.2.2)) (a₂ := (q'.2.1, q'.2.2.1, q'.2.2.2)) (h1.trans h2.symm)
    have h4 := v23 q
    have h5 := v23 q'
    rw [h] at h4
    have h6 := inj23 (a₁ := (q.2.2.1, q.1, q.2.2.2)) (a₂ := (q'.2.2.1, q'.1, q'.2.2.2)) (h4.trans h5.symm)
    rw [Prod.mk.injEq, Prod.mk.injEq] at h3 h6
    exact Prod.ext h6.2.1 (Prod.ext h3.1 (Prod.ext h3.2.1 h3.2.2))
  have hΨsurj (w : W) (hw : w ∈ U) : ∃ q, Ψ q = w := by
    rw [← hM2] at hw
    obtain ⟨σ, hσ, μ, hμ, rfl⟩ := Submodule.mem_sup.mp hw
    obtain ⟨τ, hτ, κ₃, h3, rfl⟩ := Submodule.mem_sup.mp hσ
    obtain ⟨κ₁, h1, κ₂, h2, rfl⟩ := Submodule.mem_sup.mp hτ
    exact ⟨(⟨κ₁, h1⟩, ⟨κ₂, h2⟩, ⟨κ₃, h3⟩, ⟨μ, hμ⟩), rfl⟩
  -- the restriction
  have hr : (hat fun (x : X) (y : Y) (z : Z) => ind F ((x, y, z) ∈ U)).Restricts (quad F K₁ K₂ K₃ M) := by
    let _ : DecidableEq Old := fun a b => Classical.propDecidable (a = b)
    let N : ∀ i, OLeg X Y Z i → QLeg K₁ K₂ K₃ M i → F := fun i =>
      match i with
      | .o1 => fun a b => ind F (a = s12 (b.1 + b.2.1 + b.2.2))
      | .o2 => fun a b => ind F (a = s23 (b.1 + b.2.1 + b.2.2))
      | .o3 => fun a b => ind F (a = s31 (b.1 + b.2.1 + b.2.2))
      | .m2 => fun _ _ => 1
      | .m3 => fun _ _ => 1
    have key : ∀ a : ∀ i, OLeg X Y Z i, ind F (Agree a) * ind F (((a .o1).1, (a .o1).2, (a .o2).2) ∈ U) =
        ∑ b : ∀ i, QLeg K₁ K₂ K₃ M i, ind F (QAgree b) * ∏ i, N i (a i) (b i) := by
      intro a
      let β (q : K₁ × K₂ × K₃ × M) : ∀ i, QLeg K₁ K₂ K₃ M i := fun i =>
        match i with
        | .o1 => (q.2.1, q.2.2.1, q.2.2.2)
        | .o2 => (q.2.2.1, q.1, q.2.2.2)
        | .o3 => (q.1, q.2.1, q.2.2.2)
        | .m2 => PUnit.unit
        | .m3 => PUnit.unit
      have step1 : ∑ q : K₁ × K₂ × K₃ × M, ind F (QAgree (β q)) * ∏ i, N i (a i) (β q i) =
          ∑ b : ∀ i, QLeg K₁ K₂ K₃ M i, ind F (QAgree b) * ∏ i, N i (a i) (b i) := by
        refine Finset.sum_of_injOn β ?_ (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)) ?_ (fun _ _ => rfl)
        · intro q _ q' _ h
          have h1 := congrFun h Old.o1
          have h2 := congrFun h Old.o2
          simp only [β, Prod.mk.injEq] at h1 h2
          exact Prod.ext h2.2.1 (Prod.ext h1.1 (Prod.ext h1.2.1 h1.2.2))
        · intro b _ hb
          rw [ind_false, zero_mul]
          rintro ⟨⟨h1, h2⟩, h3, h4, h5⟩
          apply hb
          refine ⟨((b .o3).1, (b .o1).1, (b .o1).2.1, (b .o1).2.2), Finset.mem_coe.mpr (Finset.mem_univ _), ?_⟩
          funext i
          cases i
          · rfl
          · exact Prod.ext h3 (Prod.ext h1.symm h4)
          · exact Prod.ext rfl (Prod.ext h2 (h4.trans h5.symm))
          · rfl
          · rfl
      have term (q : K₁ × K₂ × K₃ × M) : ind F (QAgree (β q)) * ∏ i, N i (a i) (β q i) =
          ind F (Agree a ∧ Ψ q = ((a .o1).1, (a .o1).2, (a .o2).2)) := by
        rw [ind_true (p := QAgree (β q)) ⟨⟨rfl, rfl⟩, rfl, rfl, rfl⟩, one_mul, prod_old]
        have n1 : N .o1 (a .o1) (β q .o1) = ind F (a .o1 = s12 (Ψ q)) := by
          rw [← v12]
        have n2 : N .o2 (a .o2) (β q .o2) = ind F (a .o2 = s23 (Ψ q)) := by
          rw [← v23]
        have n3 : N .o3 (a .o3) (β q .o3) = ind F (a .o3 = s31 (Ψ q)) := by
          rw [← v31]
        have n4 : N .m2 (a .m2) (β q .m2) = 1 := rfl
        rw [n1, n2, n3, n4, mul_one, mul_one, ind_mul, ind_mul]
        apply ind_congr
        constructor
        · rintro ⟨h1, h2, h3⟩
          refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
          · rw [h1, h3]
          · rw [h1, h2]
          · rw [h2, h3]
          · rw [h1, h2]
            rfl
        · rintro ⟨⟨h1, h2, h3⟩, h4⟩
          refine ⟨?_, ?_, ?_⟩
          · rw [h4]
            rfl
          · rw [h4]
            exact Prod.ext h2.symm rfl
          · rw [h4]
            exact Prod.ext h3.symm h1.symm
      rw [← step1]
      simp only [term]
      by_cases hA : Agree a
      · by_cases hU : ((a .o1).1, (a .o1).2, (a .o2).2) ∈ U
        · obtain ⟨q, hq⟩ := hΨsurj _ hU
          rw [ind_true hA, ind_true hU, one_mul, Finset.sum_eq_single q]
          · rw [ind_true ⟨hA, hq⟩]
          · intro q' _ hq'
            rw [ind_false]
            rintro ⟨-, h⟩
            exact hq' (hΨinj (h.trans hq.symm))
          · intro h
            exact absurd (Finset.mem_univ _) h
        · rw [ind_false hU, mul_zero]
          symm
          refine Finset.sum_eq_zero fun q _ => ?_
          rw [ind_false]
          rintro ⟨-, h⟩
          apply hU
          rw [← h]
          exact hΨU q
      · rw [ind_false hA, zero_mul]
        symm
        refine Finset.sum_eq_zero fun q _ => ?_
        rw [ind_false (fun h => hA h.1)]
    exact ⟨N, key⟩
  refine (price_mono P hr place).trans ((quad_price F K₁ K₂ K₃ M P).trans ?_)
  have pos (A : Type) [Fintype A] [Nonempty A] : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  have l12 : logb 2 (Fintype.card K₂) + logb 2 (Fintype.card K₃) + logb 2 (Fintype.card M) ≤
      logb 2 (Fintype.card X) + logb 2 (Fintype.card Y) := by
    rw [← logb_mul (pos K₂).ne' (pos K₃).ne', ← logb_mul (mul_pos (pos K₂) (pos K₃)).ne' (pos M).ne',
      ← logb_mul (pos X).ne' (pos Y).ne']
    refine logb_le_logb_of_le (by norm_num) (mul_pos (mul_pos (pos K₂) (pos K₃)) (pos M)) ?_
    rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_prod, ← mul_assoc] at c12
    exact_mod_cast c12
  have l23 : logb 2 (Fintype.card K₃) + logb 2 (Fintype.card K₁) + logb 2 (Fintype.card M) ≤
      logb 2 (Fintype.card Y) + logb 2 (Fintype.card Z) := by
    rw [← logb_mul (pos K₃).ne' (pos K₁).ne', ← logb_mul (mul_pos (pos K₃) (pos K₁)).ne' (pos M).ne',
      ← logb_mul (pos Y).ne' (pos Z).ne']
    refine logb_le_logb_of_le (by norm_num) (mul_pos (mul_pos (pos K₃) (pos K₁)) (pos M)) ?_
    rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_prod, ← mul_assoc] at c23
    exact_mod_cast c23
  have l31 : logb 2 (Fintype.card K₁) + logb 2 (Fintype.card K₂) + logb 2 (Fintype.card M) ≤
      logb 2 (Fintype.card Z) + logb 2 (Fintype.card X) := by
    rw [← logb_mul (pos K₁).ne' (pos K₂).ne', ← logb_mul (mul_pos (pos K₁) (pos K₂)).ne' (pos M).ne',
      ← logb_mul (pos Z).ne' (pos X).ne']
    refine logb_le_logb_of_le (by norm_num) (mul_pos (mul_pos (pos K₁) (pos K₂)) (pos M)) ?_
    rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_prod, ← mul_assoc] at c31
    exact_mod_cast c31
  linarith

/-- **Stabilizer functions are cheap.** -/
theorem stab_price (P : SpectralPlacementPrices F Plane) {s : X × Y × Z → F} (hs : Stab s) :
    P.price (hat fun (x : X) (y : Y) (z : Z) => s (x, y, z)) place ≤
      logb 2 (Fintype.card X) + logb 2 (Fintype.card Y) + logb 2 (Fintype.card Z) := by
  classical
  obtain ⟨U, w₀, c, φ, hφ, hs⟩ := hs
  let ix (x : X) : X × Y × Z := (x, 0, 0)
  let iy (y : Y) : X × Y × Z := (0, y, 0)
  let iz (z : Z) : X × Y × Z := (0, 0, z)
  have dec (x : X) (y : Y) (z : Z) : ((x, y, z) : X × Y × Z) = ix x + iy y + iz z := by
    simp [ix, iy, iz]
  let u (x : X) (y : Y) : F := c * (φ (ix x) * φ (iy y) * form φ (ix x) (iy y))
  let v (y : Y) (z : Z) : F := form φ (iy y) (iz z) * φ (iz z)
  let w (z : Z) (x : X) : F := form φ (ix x) (iz z)
  let T (x : X) (y : Y) (z : Z) : F := ind F ((x, y, z) ∈ U) * (u x y * v y z * w z x)
  have hT (x : X) (y : Y) (z : Z) : T x y z = c * (ind F ((x, y, z) ∈ U) * φ (x, y, z)) := by
    simp only [T, u, v, w]
    have e : φ (x, y, z) = φ (ix x) * φ (iy y) * form φ (ix x) (iy y) * φ (iz z) *
        (form φ (ix x) (iz z) * form φ (iy y) (iz z)) := by
      rw [dec, hφ.add, hφ.add, hφ.mul]
    rw [e]
    ring
  have h1 : (hat T).Restricts (hat fun (x : X) (y : Y) (z : Z) => ind F ((x, y, z) ∈ U)) :=
    mul_cylinder_restricts _ u v w
  have h2 : (hat fun (x : X) (y : Y) (z : Z) => T (x - w₀.1) (y - w₀.2.1) (z - w₀.2.2)).Restricts (hat T) :=
    comp_restricts T (sub_left_injective) (sub_left_injective) (sub_left_injective)
  have h3 : (fun (x : X) (y : Y) (z : Z) => s (x, y, z)) = fun x y z => T (x - w₀.1) (y - w₀.2.1) (z - w₀.2.2) := by
    funext x y z
    rw [hs, hT]
    rfl
  rw [h3]
  exact ((price_mono P h2 place).trans (price_mono P h1 place)).trans (subspace_price P U)

end subspace

end StabilizerRank
