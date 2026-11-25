import StabilizerRank.Phase
import NOF.Ind
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Sums of quadratic phases along linear maps

Every such sum is zero or a quadratic phase on an affine subspace.
-/

namespace StabilizerRank

open NOF

variable {F : Type*} [Field F] {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

/-- `s` is a multiple of the push-forward of a quadratic phase along an affine map. -/
def Push (s : W → F) : Prop :=
  ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 2) V) (_ : Fintype V) (ι : V →ₗ[ZMod 2] W) (w₀ : W) (c : F)
    (φ : V → F), IsPhase φ ∧ ∀ w, s w = c * ∑ v, ind F (w = w₀ + ι v) * φ v

/-- `s` is zero or a multiple of a quadratic phase on an affine subspace. -/
def Stab (s : W → F) : Prop :=
  ∃ (U : Submodule (ZMod 2) W) (w₀ : W) (c : F) (φ : W → F), IsPhase φ ∧
    ∀ w, s w = c * (ind F (w - w₀ ∈ U) * φ (w - w₀))

theorem Stab.zero : Stab (fun _ : W => (0 : F)) :=
  ⟨⊥, 0, 0, fun _ => 1, IsPhase.one, fun w => by simp⟩

section sums

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

/-- A sum that vanishes outside a subspace. -/
theorem sum_submodule [Fintype V] (H : Submodule (ZMod 2) V) [Fintype H] (G : V → F) (h : ∀ v, v ∉ H → G v = 0) :
    ∑ v, G v = ∑ v : H, G v := by
  classical
  have h1 : ∑ v : H, G v = ∑ v ∈ Finset.univ.filter (fun v => v ∈ H), G v := by
    rw [Finset.sum_filter, ← Finset.sum_filter]
    exact (Finset.sum_subtype (Finset.univ.filter fun v => v ∈ H) (fun x => by simp) G).symm
  rw [h1]
  symm
  refine Finset.sum_subset (Finset.subset_univ _) fun v _ hv => h v ?_
  simpa using hv

theorem sum_shift [Fintype V] (a : V) (G : V → F) : ∑ v, G v = ∑ v, G (a + v) :=
  (Equiv.sum_comp (Equiv.addLeft a) G).symm

/-- The subspace on which the defect with `e` is trivial. -/
def ker (φ : V → F) (hφ : IsPhase φ) (e : V) : Submodule (ZMod 2) V where
  carrier := {v | form φ v e = 1}
  zero_mem' := hφ.form_zero e
  add_mem' := by
    intro a b ha hb
    have ha' : form φ a e = 1 := ha
    have hb' : form φ b e = 1 := hb
    change form φ (a + b) e = 1
    rw [hφ.mul, ha', hb', one_mul]
  smul_mem' := by
    intro c a ha
    have ha' : form φ a e = 1 := ha
    change form φ (c • a) e = 1
    fin_cases c
    · change form φ ((0 : ZMod 2) • a) e = 1
      rw [zero_smul, hφ.form_zero]
    · change form φ ((1 : ZMod 2) • a) e = 1
      rw [one_smul, ha']

theorem card_submodule_lt [Fintype V] (H : Submodule (ZMod 2) V) [Fintype H] {v : V} (hv : v ∉ H) :
    Fintype.card H < Fintype.card V :=
  Fintype.card_subtype_lt (p := fun v => v ∈ H) hv

end sums

/-- The reduction step: if the map is not injective, the sum is zero or a sum over a smaller space. -/
theorem push_step (h2 : (2 : F) ≠ 0) {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V] (ι : V →ₗ[ZMod 2] W)
    (w₀ : W) (φ : V → F) (hφ : IsPhase φ) {e : V} (he : e ≠ 0) (hι : ι e = 0) :
    (∀ w, ∑ v, ind F (w = w₀ + ι v) * φ v = 0) ∨
      ∃ (H : Submodule (ZMod 2) V) (_ : Fintype H) (w₁ : W) (c : F) (ψ : H → F), Fintype.card H < Fintype.card V ∧
        IsPhase ψ ∧ ∀ w, ∑ v, ind F (w = w₀ + ι v) * φ v = c * ∑ v : H, ind F (w = w₁ + ι v) * ψ v := by
  classical
  let H := ker φ hφ e
  let _ : Fintype H := Fintype.ofFinite H
  have memH (v : V) : v ∈ H ↔ form φ v e = 1 := Iff.rfl
  have notH (v : V) : v ∉ H ↔ form φ v e = -1 := by
    rw [memH]
    constructor
    · intro h
      exact (hφ.form_eq v e).resolve_left h
    · intro h h'
      rw [h] at h'
      apply h2
      have : (1 : F) + 1 = 0 := by
        nth_rw 1 [← h']
        ring
      rw [← this]
      norm_num
  -- the two parts of the sum
  let P (w : W) : F := ∑ v, ind F (v ∈ H) * (ind F (w = w₀ + ι v) * φ v)
  let N (w : W) : F := ∑ v, ind F (v ∉ H) * (ind F (w = w₀ + ι v) * φ v)
  have split (w : W) : ∑ v, ind F (w = w₀ + ι v) * φ v = P w + N w := by
    simp only [P, N]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    by_cases hv : v ∈ H
    · rw [ind_true hv, ind_false (p := v ∉ H) (not_not.mpr hv)]
      ring
    · rw [ind_false hv, ind_true (p := v ∉ H) hv]
      ring
  have PH (w : W) : P w = ∑ v : H, ind F (w = w₀ + ι v) * φ v := by
    simp only [P]
    rw [sum_submodule H _ (fun v hv => by rw [ind_false hv, zero_mul])]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [ind_true v.2, one_mul]
  have shifted (v : V) : φ (e + v) = φ e * φ v * form φ v e := by
    rw [hφ.add, IsPhase.form_comm]
  have ιe (v : V) : ι (e + v) = ι v := by rw [map_add, hι, zero_add]
  have hφH : IsPhase (fun v : H => φ v) := hφ.comp H.subtype
  by_cases heH : e ∈ H
  · -- `φ e = ± 1`
    have hsq : φ e * φ e = 1 := by rw [hφ.sq, (memH e).mp heH]
    have hmem (v : V) : e + v ∈ H ↔ v ∈ H := by
      constructor
      · intro h
        have := H.add_mem heH h
        rwa [← add_assoc, add_self', zero_add] at this
      · exact fun h => H.add_mem heH h
    have hP (w : W) : P w = φ e * P w := by
      have h1 : P w = ∑ v, ind F (e + v ∈ H) * (ind F (w = w₀ + ι (e + v)) * φ (e + v)) := sum_shift e _
      conv_lhs => rw [h1]
      simp only [P]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [ind_congr (hmem v), ιe, shifted]
      by_cases hv : v ∈ H
      · rw [(memH v).mp hv]
        ring
      · rw [ind_false hv]
        ring
    have hN (w : W) : N w = -(φ e * N w) := by
      have h1 : N w = ∑ v, ind F (e + v ∉ H) * (ind F (w = w₀ + ι (e + v)) * φ (e + v)) := sum_shift e _
      conv_lhs => rw [h1]
      simp only [N]
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [ind_congr (not_congr (hmem v)), ιe, shifted]
      by_cases hv : v ∈ H
      · rw [ind_false (p := v ∉ H) (not_not.mpr hv)]
        ring
      · rw [(notH v).mp hv]
        ring
    rcases mul_self_eq_one_iff.mp hsq with h1 | h1
    · -- `φ e = 1`: a complement of `e` in `H`
      have hN0 (w : W) : N w = 0 := by
        have := hN w
        rw [h1, one_mul] at this
        have h3 : 2 * N w = 0 := by
          nth_rw 1 [two_mul, this]
          ring
        exact (mul_eq_zero.mp h3).resolve_left h2
      let L : Submodule (ZMod 2) V := Submodule.span (ZMod 2) {e}
      have hL (x : V) : x ∈ L ↔ x = 0 ∨ x = e := by
        rw [Submodule.mem_span_singleton]
        constructor
        · rintro ⟨a, rfl⟩
          fin_cases a
          · exact Or.inl (zero_smul _ _)
          · exact Or.inr (one_smul _ _)
        · rintro (rfl | rfl)
          · exact ⟨0, zero_smul _ _⟩
          · exact ⟨1, one_smul _ _⟩
      have hLH : L ≤ H := by
        rw [Submodule.span_singleton_le_iff_mem]
        exact heH
      obtain ⟨C, hC1, hC2⟩ : ∃ C : Submodule (ZMod 2) V, L ⊓ C = ⊥ ∧ L ⊔ C = H := by
        obtain ⟨C', hC'⟩ := Submodule.exists_isCompl (Submodule.comap H.subtype L)
        refine ⟨C'.map H.subtype, ?_, ?_⟩
        · rw [eq_bot_iff]
          rintro x ⟨hx1, hx2⟩
          obtain ⟨y, hy, rfl⟩ := hx2
          have : y ∈ Submodule.comap H.subtype L ⊓ C' := ⟨hx1, hy⟩
          rw [hC'.inf_eq_bot] at this
          rw [Submodule.mem_bot] at this
          rw [this]
          simp
        · have h3 := congrArg (Submodule.map H.subtype) hC'.sup_eq_top
          rw [Submodule.map_sup, Submodule.map_comap_subtype, Submodule.map_subtype_top, inf_eq_right.mpr hLH] at h3
          exact h3
      have heC : e ∉ C := by
        intro h
        have : e ∈ L ⊓ C := ⟨(hL e).mpr (Or.inr rfl), h⟩
        rw [hC1, Submodule.mem_bot] at this
        exact he this
      have hCH : C ≤ H := hC2 ▸ le_sup_right
      let _ : Fintype C := Fintype.ofFinite C
      refine Or.inr ⟨C, inferInstance, w₀, 2, fun v => φ v, card_submodule_lt C heC, hφ.comp C.subtype, fun w => ?_⟩
      rw [split, hN0, add_zero]
      -- the elements of `H` are in `C` or in `e + C`
      have dec (v : V) : ind F (v ∈ H) = ind F (v ∈ C) + ind F (e + v ∈ C) := by
        by_cases hv : v ∈ H
        · rw [ind_true hv]
          have hv' : v ∈ L ⊔ C := by rw [hC2]; exact hv
          obtain ⟨l, hl, c, hc, rfl⟩ := Submodule.mem_sup.mp hv'
          rcases (hL l).mp hl with rfl | rfl
          · have h4 : ¬ (e + (0 + c) ∈ C) := by
              intro h
              rw [zero_add] at h
              exact heC ((Submodule.add_mem_iff_left C hc).mp h)
            rw [zero_add] at h4 ⊢
            rw [ind_true hc, ind_false h4, add_zero]
          · have h4 : ¬ (l + c ∈ C) := fun h => heC ((Submodule.add_mem_iff_left C hc).mp h)
            have h5 : l + (l + c) ∈ C := by
              rw [← add_assoc, add_self', zero_add]
              exact hc
            rw [ind_false h4, ind_true h5, zero_add]
        · have h4 : ¬ (v ∈ C) := fun h => hv (hCH h)
          have h5 : ¬ (e + v ∈ C) := fun h => hv ((hmem v).mp (hCH h))
          rw [ind_false hv, ind_false h4, ind_false h5, add_zero]
      have hPC : P w = (∑ v, ind F (v ∈ C) * (ind F (w = w₀ + ι v) * φ v)) +
          ∑ v, ind F (e + v ∈ C) * (ind F (w = w₀ + ι v) * φ v) := by
        simp only [P]
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [dec, add_mul]
      have second : ∑ v, ind F (e + v ∈ C) * (ind F (w = w₀ + ι v) * φ v) =
          ∑ v, ind F (v ∈ C) * (ind F (w = w₀ + ι v) * φ v) := by
        rw [sum_shift e]
        refine Finset.sum_congr rfl fun v _ => ?_
        have e1 : e + (e + v) = v := by rw [← add_assoc, add_self', zero_add]
        rw [e1, ιe, shifted, h1]
        by_cases hv : v ∈ C
        · rw [(memH v).mp (hCH hv)]
          ring
        · rw [ind_false hv]
          ring
      rw [hPC, second, ← two_mul]
      congr 1
      rw [sum_submodule C _ (fun v hv => by rw [ind_false hv, zero_mul])]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [ind_true v.2, one_mul]
    · -- `φ e = -1`: the other coset of `H`
      have hP0 (w : W) : P w = 0 := by
        have := hP w
        rw [h1] at this
        have h3 : 2 * P w = 0 := by
          nth_rw 1 [two_mul, this]
          ring
        exact (mul_eq_zero.mp h3).resolve_left h2
      by_cases hall : ∀ v, v ∈ H
      · refine Or.inl fun w => ?_
        rw [split, hP0, zero_add]
        simp only [N]
        refine Finset.sum_eq_zero fun v _ => ?_
        rw [ind_false (p := v ∉ H) (not_not.mpr (hall v)), zero_mul]
      · push Not at hall
        obtain ⟨a, ha⟩ := hall
        refine Or.inr ⟨H, inferInstance, w₀ + ι a, φ a, fun v => φ v * form φ a v, card_submodule_lt H ha,
          (hφ.shift a).comp H.subtype, fun w => ?_⟩
        rw [split, hP0, zero_add]
        have hc (v : V) : a + v ∉ H ↔ v ∈ H := by
          rw [notH, memH, hφ.mul, (notH a).mp ha]
          constructor
          · intro h
            have := congrArg (fun x => -x) h
            simpa using this
          · intro h
            rw [h, mul_one]
        have h3 : N w = ∑ v, ind F (a + v ∉ H) * (ind F (w = w₀ + ι (a + v)) * φ (a + v)) := sum_shift a _
        rw [h3, sum_submodule H _ (fun v hv => by rw [ind_false (fun h => hv ((hc v).mp h)), zero_mul]), Finset.mul_sum]
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [ind_true ((hc v).mpr v.2), one_mul, map_add, add_assoc, hφ.shift_eq]
        ring
  · -- `φ e` is a square root of `-1`
    have hN (w : W) : N w = φ e * P w := by
      have h1 : N w = ∑ v, ind F (e + v ∉ H) * (ind F (w = w₀ + ι (e + v)) * φ (e + v)) := sum_shift e _
      have hc (v : V) : e + v ∉ H ↔ v ∈ H := by
        rw [notH, memH, hφ.mul, (notH e).mp heH]
        constructor
        · intro h
          have := congrArg (fun x => -x) h
          simpa using this
        · intro h
          rw [h, mul_one]
      rw [h1]
      simp only [P]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [ind_congr (hc v), ιe, shifted]
      by_cases hv : v ∈ H
      · rw [(memH v).mp hv]
        ring
      · rw [ind_false hv]
        ring
    refine Or.inr ⟨H, inferInstance, w₀, 1 + φ e, fun v => φ v, card_submodule_lt H heH, hφH, fun w => ?_⟩
    rw [split, hN, PH]
    ring

/-- **Every push-forward of a quadratic phase is zero or a quadratic phase on an affine subspace.** -/
theorem Push.stab (h2 : (2 : F) ≠ 0) {s : W → F} (hs : Push s) : Stab s := by
  classical
  obtain ⟨V, i1, i2, i3, ι, w₀, c, φ, hφ, hs⟩ := hs
  -- induction on the size of the space
  have main : ∀ n : ℕ, ∀ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 2) V) (_ : Fintype V) (ι : V →ₗ[ZMod 2] W)
      (w₀ : W) (φ : V → F), Fintype.card V = n → IsPhase φ → Stab (fun w => ∑ v, ind F (w = w₀ + ι v) * φ v) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro V i1 i2 i3 ι w₀ φ hn hφ
      by_cases hinj : Function.Injective ι
      · -- extend the phase to the whole space
        obtain ⟨p, hp⟩ := ι.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hinj)
        have hp' (v : V) : p (ι v) = v := LinearMap.congr_fun hp v
        refine ⟨LinearMap.range ι, w₀, 1, fun w => φ (p w), hφ.comp p, fun w => ?_⟩
        beta_reduce
        rw [one_mul]
        by_cases hw : w - w₀ ∈ LinearMap.range ι
        · obtain ⟨v, hv⟩ := hw
          rw [ind_true ⟨v, hv⟩, one_mul, ← hv, hp', Finset.sum_eq_single v]
          · rw [ind_true (by rw [hv]; abel), one_mul]
          · intro u _ hu
            rw [ind_false, zero_mul]
            intro h
            apply hu
            apply hinj
            rw [hv, h]
            abel
          · intro h
            exact absurd (Finset.mem_univ v) h
        · rw [ind_false hw, zero_mul]
          refine Finset.sum_eq_zero fun v _ => ?_
          rw [ind_false, zero_mul]
          intro h
          exact hw ⟨v, by rw [h]; abel⟩
      · obtain ⟨e, he, hιe⟩ : ∃ e, e ≠ 0 ∧ ι e = 0 := by
          by_contra! h0
          apply hinj
          rw [← LinearMap.ker_eq_bot, eq_bot_iff]
          intro x hx
          by_contra hx0
          exact h0 x (fun h => hx0 (by rw [h]; exact Submodule.zero_mem _)) hx
        rcases push_step h2 ι w₀ φ hφ he hιe with h0 | ⟨H, iH, w₁, c, ψ, hlt, hψ, hH⟩
        · have e0 : (fun w => ∑ v, ind F (w = w₀ + ι v) * φ v) = fun _ => (0 : F) := funext h0
          rw [e0]
          exact Stab.zero
        · obtain ⟨U, w₂, c', χ, hχ, hU⟩ := ih (Fintype.card H) (hn ▸ hlt) H inferInstance inferInstance iH
            (ι.comp H.subtype) w₁ ψ rfl hψ
          refine ⟨U, w₂, c * c', χ, hχ, fun w => ?_⟩
          beta_reduce
          rw [hH w]
          have := hU w
          simp only [LinearMap.comp_apply, Submodule.subtype_apply] at this
          rw [this]
          ring
  obtain ⟨U, w₁, c', χ, hχ, hU⟩ := main _ V i1 i2 i3 ι w₀ φ rfl hφ
  refine ⟨U, w₁, c * c', χ, hχ, fun w => ?_⟩
  have := hU w
  beta_reduce at this
  rw [hs, this]
  ring

end StabilizerRank
