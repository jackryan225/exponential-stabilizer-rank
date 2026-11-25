import StabilizerRank.Push
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.Pi

/-!
# Functions that are represented with gates

`Rep g S f`: `f` is a push-forward of a quadratic phase times the gate function `∏ i : S, g (b i)` at affine forms.
-/

namespace StabilizerRank

open NOF

variable {F : Type*} [Field F] {W U : Type} [AddCommGroup W] [Module (ZMod 2) W] [AddCommGroup U] [Module (ZMod 2) U]
  {B : Type} [AddCommGroup B] [Module (ZMod 2) B]

/-- The gate function. -/
def gates (g : B → F) (S : Type) [Fintype S] (b : S → B) : F := ∏ i, g (b i)

def Rep (g : B → F) (S : Type) [Fintype S] (f : W → F) : Prop :=
  ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 2) V) (_ : Fintype V) (ι : V →ₗ[ZMod 2] W) (w₀ : W) (c : F)
    (φ : V → F) (L : V →ₗ[ZMod 2] (S → B)) (b : S → B),
    IsPhase φ ∧ ∀ w, f w = c * ∑ v, ind F (w = w₀ + ι v) * (φ v * gates g S (b + L v))

def RepE (g : B → F) (f : W → F) : Prop := ∃ (S : Type) (_ : Fintype S), Rep g S f

variable {g : B → F} {S S' : Type} [Fintype S] [Fintype S'] {f f' : W → F}

theorem Rep.congr (h : Rep g S f) (e : ∀ w, f' w = f w) : Rep g S f' := by
  have : f' = f := funext e
  rwa [this]

theorem RepE.congr (h : RepE g f) (e : ∀ w, f' w = f w) : RepE g f' := by
  obtain ⟨S, i, h⟩ := h
  exact ⟨S, i, h.congr e⟩

theorem Rep.zero : Rep g S (fun _ : W => (0 : F)) :=
  ⟨PUnit, inferInstance, inferInstance, inferInstance, 0, 0, 0, fun _ => 1, 0, 0, IsPhase.one, fun w => by simp⟩

theorem Rep.smul (h : Rep g S f) (a : F) : Rep g S (fun w => a * f w) := by
  obtain ⟨V, i1, i2, i3, ι, w₀, c, φ, L, b, hφ, h⟩ := h
  exact ⟨V, i1, i2, i3, ι, w₀, a * c, φ, L, b, hφ, fun w => by beta_reduce; rw [h, mul_assoc]⟩

/-- Phases times gates at linear forms. -/
theorem Rep.direct [Fintype W] {φ : W → F} (hφ : IsPhase φ) (b : S → B) (L : W →ₗ[ZMod 2] (S → B)) :
    Rep g S (fun w => φ w * gates g S (b + L w)) := by
  classical
  refine ⟨W, inferInstance, inferInstance, inferInstance, LinearMap.id, 0, 1, φ, L, b, hφ, fun w => ?_⟩
  rw [one_mul, Finset.sum_eq_single w]
  · rw [ind_true (by simp), one_mul]
  · intro v _ hv
    rw [ind_false, zero_mul]
    intro h
    apply hv
    rw [h]
    simp
  · intro h
    exact absurd (Finset.mem_univ w) h

/-- Indicators of affine subspaces, given by a parametrization. -/
theorem Rep.affine {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V] (ι : V →ₗ[ZMod 2] W) (w₀ : W) :
    Rep g Empty (fun w => ∑ v, ind F (w = w₀ + ι v)) := by
  refine ⟨V, inferInstance, inferInstance, inferInstance, ι, w₀, 1, fun _ => 1, 0, 0, IsPhase.one, fun w => ?_⟩
  simp [gates]

/-- Sums over the fibres of a linear map. -/
theorem Rep.push [Fintype W] (h : Rep g S f) (π : W →ₗ[ZMod 2] U) : Rep g S (fun u => ∑ w, ind F (u = π w) * f w) := by
  classical
  obtain ⟨V, i1, i2, i3, ι, w₀, c, φ, L, b, hφ, h⟩ := h
  refine ⟨V, i1, i2, i3, π.comp ι, π w₀, c, φ, L, b, hφ, fun u => ?_⟩
  simp only [h]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.sum_eq_single (w₀ + ι v)]
  · rw [ind_true (p := w₀ + ι v = w₀ + ι v) rfl, map_add, LinearMap.comp_apply]
    ring
  · intro w _ hw
    rw [ind_false (p := w = w₀ + ι v) hw]
    ring
  · intro hw
    exact absurd (Finset.mem_univ _) hw

/-- Products. -/
theorem Rep.mul (h : Rep g S f) (h' : Rep g S' f') : Rep g (S ⊕ S') (fun w => f w * f' w) := by
  classical
  obtain ⟨V, i1, i2, i3, ι, w₀, c, φ, L, b, hφ, h⟩ := h
  obtain ⟨V', i1', i2', i3', ι', w₀', c', φ', L', b', hφ', h'⟩ := h'
  by_cases hex : ∃ a a', w₀ + ι a = w₀' + ι' a'
  · obtain ⟨a, a', ha⟩ := hex
    let D : V × V' →ₗ[ZMod 2] W := ι.comp (LinearMap.fst _ _ _) - ι'.comp (LinearMap.snd _ _ _)
    let H := LinearMap.ker D
    let _ : Fintype H := Fintype.ofFinite H
    let p1 : H →ₗ[ZMod 2] V := (LinearMap.fst _ _ _).comp H.subtype
    let p2 : H →ₗ[ZMod 2] V' := (LinearMap.snd _ _ _).comp H.subtype
    let L'' : H →ₗ[ZMod 2] (S ⊕ S' → B) := LinearMap.pi (Sum.rec
      (fun i => (LinearMap.proj i).comp (L.comp p1)) (fun j => (LinearMap.proj j).comp (L'.comp p2)))
    refine ⟨H, inferInstance, inferInstance, inferInstance, ι.comp p1, w₀ + ι a, c * c' * (φ a * φ' a'),
      fun p => (φ (p1 p) * form φ a (p1 p)) * (φ' (p2 p) * form φ' a' (p2 p)), L'',
      Sum.elim (b + L a) (b' + L' a'), ?_, fun w => ?_⟩
    · exact ((hφ.shift a).comp p1).mul_phase ((hφ'.shift a').comp p2)
    · beta_reduce
      rw [h, h']
      let G (q : V × V') : F := (ind F (w = w₀ + ι q.1) * (φ q.1 * gates g S (b + L q.1))) *
        (ind F (w = w₀' + ι' q.2) * (φ' q.2 * gates g S' (b' + L' q.2)))
      have e1 : c * (∑ v, ind F (w = w₀ + ι v) * (φ v * gates g S (b + L v))) *
          (c' * ∑ v, ind F (w = w₀' + ι' v) * (φ' v * gates g S' (b' + L' v))) = c * c' * ∑ q : V × V', G q := by
        rw [Fintype.sum_prod_type]
        simp only [G]
        rw [mul_mul_mul_comm, Finset.sum_mul_sum]
      rw [e1, sum_shift (a, a') G, sum_submodule H (fun q => G ((a, a') + q))]
      · conv_rhs => rw [mul_assoc (c * c'), Finset.mul_sum]
        refine congrArg (c * c' * ·) ?_
        refine Finset.sum_congr rfl fun q _ => ?_
        have hq : ι q.1.1 = ι' q.1.2 := by
          have := q.2
          rw [LinearMap.mem_ker] at this
          exact sub_eq_zero.mp this
        have i1 : ind F (w = w₀ + ι (a + q.1.1)) = ind F (w = w₀ + ι a + ι q.1.1) := by
          rw [map_add, add_assoc]
        have i2 : ind F (w = w₀' + ι' (a' + q.1.2)) = ind F (w = w₀ + ι a + ι q.1.1) := by
          rw [map_add, ← hq, ← add_assoc, ← ha]
        have g1 : gates g (S ⊕ S') (Sum.elim (b + L a) (b' + L' a') + L'' q) =
            gates g S (b + L (a + q.1.1)) * gates g S' (b' + L' (a' + q.1.2)) := by
          rw [gates, Fintype.prod_sum_type]
          congr 1
          · refine Finset.prod_congr rfl fun i _ => ?_
            congr 1
            change (b i + L a i) + L q.1.1 i = b i + L (a + q.1.1) i
            rw [map_add, Pi.add_apply]
            abel
          · refine Finset.prod_congr rfl fun i _ => ?_
            congr 1
            change (b' i + L' a' i) + L' q.1.2 i = b' i + L' (a' + q.1.2) i
            rw [map_add, Pi.add_apply]
            abel
        have hG : G ((a, a') + q.1) = (ind F (w = w₀ + ι (a + q.1.1)) * (φ (a + q.1.1) * gates g S (b + L (a + q.1.1)))) *
          (ind F (w = w₀' + ι' (a' + q.1.2)) * (φ' (a' + q.1.2) * gates g S' (b' + L' (a' + q.1.2)))) := rfl
        rw [hG, i1, i2, g1, hφ.shift_eq, hφ'.shift_eq]
        change _ = φ a * φ' a' * (ind F (w = w₀ + ι a + ι q.1.1) * ((φ q.1.1 * form φ a q.1.1) *
          (φ' q.1.2 * form φ' a' q.1.2) * (gates g S (b + L (a + q.1.1)) * gates g S' (b' + L' (a' + q.1.2)))))
        by_cases hw : w = w₀ + ι a + ι q.1.1
        · rw [ind_true hw]
          ring
        · rw [ind_false hw]
          ring
      · intro q hq
        have hG : G ((a, a') + q) = (ind F (w = w₀ + ι (a + q.1)) * (φ (a + q.1) * gates g S (b + L (a + q.1)))) *
          (ind F (w = w₀' + ι' (a' + q.2)) * (φ' (a' + q.2) * gates g S' (b' + L' (a' + q.2)))) := rfl
        rw [hG]
        by_cases h1 : w = w₀ + ι (a + q.1)
        · by_cases h2 : w = w₀' + ι' (a' + q.2)
          · exfalso
            apply hq
            rw [LinearMap.mem_ker]
            change ι q.1 - ι' q.2 = 0
            rw [sub_eq_zero]
            have h3 := h1.symm.trans h2
            rw [map_add, map_add, ← add_assoc, ← add_assoc, ha] at h3
            exact add_left_cancel h3
          · rw [ind_false h2]
            ring
        · rw [ind_false h1]
          ring
  · refine Rep.zero.congr fun w => ?_
    rw [h, h']
    by_cases h1 : ∃ a, w = w₀ + ι a
    · obtain ⟨a, ha⟩ := h1
      have : ∑ v, ind F (w = w₀' + ι' v) * (φ' v * gates g S' (b' + L' v)) = 0 := by
        refine Finset.sum_eq_zero fun v _ => ?_
        rw [ind_false, zero_mul]
        intro h2
        exact hex ⟨a, v, ha.symm.trans h2⟩
      rw [this]
      ring
    · have : ∑ v, ind F (w = w₀ + ι v) * (φ v * gates g S (b + L v)) = 0 := by
        refine Finset.sum_eq_zero fun v _ => ?_
        rw [ind_false, zero_mul]
        intro h2
        exact h1 ⟨v, h2⟩
      rw [this]
      ring

/-- A function of the second component. -/
theorem Rep.snd [Fintype U] (h : Rep g S f) : Rep g S (fun p : U × W => f p.2) := by
  classical
  obtain ⟨V, i1, i2, i3, ι, w₀, c, φ, L, b, hφ, h⟩ := h
  refine ⟨U × V, inferInstance, inferInstance, inferInstance, LinearMap.prodMap LinearMap.id ι, (0, w₀), c,
    fun p => φ p.2, L.comp (LinearMap.snd _ _ _), b, (hφ.comp (LinearMap.snd (ZMod 2) U V) : IsPhase fun p : U × V => φ p.2), fun p => ?_⟩
  beta_reduce
  rw [h, Fintype.sum_prod_type]
  congr 1
  rw [Finset.sum_eq_single p.1]
  · refine Finset.sum_congr rfl fun v _ => ?_
    congr 1
    apply ind_congr
    change p.2 = w₀ + ι v ↔ p = (0 + p.1, w₀ + ι v)
    rw [zero_add, Prod.ext_iff]
    exact ⟨fun h => ⟨rfl, h⟩, fun h => h.2⟩
  · intro u _ hu
    refine Finset.sum_eq_zero fun v _ => ?_
    rw [ind_false, zero_mul]
    intro h0
    apply hu
    have := congrArg Prod.fst h0
    change p.1 = 0 + u at this
    rw [zero_add] at this
    exact this.symm
  · intro hu
    exact absurd (Finset.mem_univ _) hu

theorem RepE.mul (h : RepE g f) (h' : RepE g f') : RepE g (fun w => f w * f' w) := by
  obtain ⟨S, i, h⟩ := h
  obtain ⟨S', i', h'⟩ := h'
  exact ⟨S ⊕ S', inferInstance, h.mul h'⟩

theorem RepE.push [Fintype W] (h : RepE g f) (π : W →ₗ[ZMod 2] U) :
    RepE g (fun u => ∑ w, ind F (u = π w) * f w) := by
  obtain ⟨S, i, h⟩ := h
  exact ⟨S, i, h.push π⟩

theorem RepE.smul (h : RepE g f) (a : F) : RepE g (fun w => a * f w) := by
  obtain ⟨S, i, h⟩ := h
  exact ⟨S, i, h.smul a⟩

/-- Substitution of linear maps. -/
theorem RepE.pull [Fintype W] [Fintype U] (h : RepE g f) (θ : U →ₗ[ZMod 2] W) : RepE g (fun u => f (θ u)) := by
  classical
  obtain ⟨S, i, h⟩ := h
  have h1 : Rep g S (fun p : U × W => f p.2) := h.snd
  have h2 : Rep g Empty (fun p : U × W => ∑ u, ind F (p = (0 : U × W) + (LinearMap.prod LinearMap.id θ) u)) :=
    Rep.affine _ _
  refine RepE.congr (RepE.push ⟨_, inferInstance, h2.mul h1⟩ (LinearMap.fst (ZMod 2) U W)) fun u => ?_
  rw [Finset.sum_eq_single (u, θ u)]
  · rw [ind_true (p := u = (LinearMap.fst (ZMod 2) U W) (u, θ u)) rfl, one_mul, Finset.sum_eq_single u]
    · rw [ind_true (by simp), one_mul]
    · intro v _ hv
      rw [ind_false]
      intro h0
      apply hv
      have := congrArg Prod.fst h0
      simp at this
      exact this.symm
    · intro hu
      exact absurd (Finset.mem_univ _) hu
  · intro p _ hp
    by_cases h0 : u = p.1
    · have : ∑ v, ind F (p = (0 : U × W) + (LinearMap.prod LinearMap.id θ) v) = 0 := by
        refine Finset.sum_eq_zero fun v _ => ?_
        rw [ind_false]
        intro h3
        apply hp
        have e1 := congrArg Prod.fst h3
        have e2 := congrArg Prod.snd h3
        simp at e1 e2
        rw [Prod.ext_iff]
        refine ⟨h0.symm, ?_⟩
        rw [e2, ← e1, ← h0]
      rw [this]
      ring
    · rw [ind_false (p := u = (LinearMap.fst (ZMod 2) U W) p) h0, zero_mul]
  · intro hu
    exact absurd (Finset.mem_univ _) hu

theorem RepE.affine {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V] (ι : V →ₗ[ZMod 2] W) (w₀ : W) :
    RepE g (fun w => ∑ v, ind F (w = w₀ + ι v)) := ⟨Empty, inferInstance, Rep.affine ι w₀⟩

/-! ### Powers -/

theorem prod_ind {ι : Type*} [Fintype ι] (p : ι → Prop) : ∏ i, ind F (p i) = ind F (∀ i, p i) := by
  classical
  by_cases h : ∀ i, p i
  · rw [ind_true h]
    exact Finset.prod_eq_one fun i _ => ind_true (h i)
  · rw [ind_false h]
    push Not at h
    obtain ⟨i, hi⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ind_false hi)

theorem Rep.pow (h : Rep g S f) (N : ℕ) : Rep g (Fin N × S) (fun w : Fin N → W => ∏ i, f (w i)) := by
  classical
  obtain ⟨V, i1, i2, i3, ι, w₀, c, φ, L, b, hφ, h⟩ := h
  refine ⟨Fin N → V, inferInstance, inferInstance, inferInstance, ι.compLeft (Fin N), fun _ => w₀, c ^ N,
    fun v => ∏ i, φ (v i), LinearMap.pi fun p : Fin N × S => (LinearMap.proj p.2).comp (L.comp (LinearMap.proj p.1)),
    fun p => b p.2, ?_, fun w => ?_⟩
  · exact IsPhase.prod Finset.univ (fun i (v : Fin N → V) => φ (v i)) fun i _ =>
      (hφ.comp (LinearMap.proj (R := ZMod 2) (φ := fun _ : Fin N => V) i) : IsPhase fun v : Fin N → V => φ (v i))
  · simp only [h]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Finset.prod_univ_sum,
      Fintype.piFinset_univ]
    congr 1
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, prod_ind]
    congr 1
    · apply ind_congr
      rw [funext_iff]
      exact Iff.rfl
    · congr 1
      rw [gates, Fintype.prod_prod_type]
      rfl

/-- Unused gates. -/
theorem Rep.embed {x₀ : B} (hg : g x₀ = 1) (h : Rep g S f) {n : ℕ} (e : S ↪ Fin n) : Rep g (Fin n) f := by
  classical
  obtain ⟨V, i1, i2, i3, ι, w₀, c, φ, L, b, hφ, h⟩ := h
  let E : (S → B) →ₗ[ZMod 2] (Fin n → B) :=
    { toFun := fun x => Function.extend e x 0
      map_add' := fun x y => by
        funext k
        by_cases hk : ∃ s, e s = k
        · obtain ⟨s, rfl⟩ := hk
          rw [Pi.add_apply, e.injective.extend_apply, e.injective.extend_apply, e.injective.extend_apply, Pi.add_apply]
        · rw [Pi.add_apply, Function.extend_apply' _ _ _ hk, Function.extend_apply' _ _ _ hk,
            Function.extend_apply' _ _ _ hk, Pi.zero_apply, add_zero]
      map_smul' := fun a x => by
        funext k
        by_cases hk : ∃ s, e s = k
        · obtain ⟨s, rfl⟩ := hk
          rw [Pi.smul_apply, e.injective.extend_apply, e.injective.extend_apply, Pi.smul_apply, RingHom.id_apply]
        · rw [Pi.smul_apply, Function.extend_apply' _ _ _ hk, Function.extend_apply' _ _ _ hk, Pi.zero_apply, smul_zero] }
  refine ⟨V, i1, i2, i3, ι, w₀, c, φ, E.comp L, Function.extend e b (fun _ => x₀), hφ, fun w => ?_⟩
  rw [h]
  congr 1
  refine Finset.sum_congr rfl fun v _ => ?_
  congr 2
  have e1 : ∏ s, g (b s + L v s) = ∏ k ∈ Finset.univ.map e,
      g ((Function.extend e b (fun _ => x₀) + (E.comp L) v) k) := by
    rw [Finset.prod_map]
    refine Finset.prod_congr rfl fun s _ => ?_
    change _ = g (Function.extend e b (fun _ => x₀) (e s) + Function.extend e (L v) 0 (e s))
    rw [e.injective.extend_apply, e.injective.extend_apply]
  rw [gates, gates]
  change ∏ s, g (b s + L v s) = _
  rw [e1]
  refine Finset.prod_subset (Finset.subset_univ _) fun k _ hk => ?_
  have hk' : ¬ ∃ s, e s = k := by
    rintro ⟨s, rfl⟩
    exact hk (Finset.mem_map.mpr ⟨s, Finset.mem_univ _, rfl⟩)
  change g (Function.extend e b (fun _ => x₀) k + Function.extend e (L v) 0 k) = 1
  rw [Function.extend_apply' _ _ _ hk', Function.extend_apply' _ _ _ hk', Pi.zero_apply, add_zero, hg]

/-! ### Decompositions -/

/-- A decomposition of the gate function gives a decomposition of every represented function. -/
theorem Rep.decompose (h : Rep g S f) {J : ℕ} (a : Fin J → F) (A : Fin J → AffineSubspace (ZMod 2) (S → B))
    (χ : Fin J → (S → B) → F) (hχ : ∀ j, IsPhase (χ j))
    (hd : ∀ b, gates g S b = ∑ j, a j * (ind F (b ∈ A j) * χ j b)) :
    ∃ s : Fin J → W → F, (∀ j, Push (s j)) ∧ ∀ w, f w = ∑ j, s j w := by
  classical
  obtain ⟨V, i1, i2, i3, ι, w₀, c, φ, L, b, hφ, h⟩ := h
  refine ⟨fun j w => c * ∑ v, ind F (w = w₀ + ι v) * (φ v * (a j * (ind F (b + L v ∈ A j) * χ j (b + L v)))), fun j => ?_,
    fun w => ?_⟩
  · by_cases hex : ∃ v₀, b + L v₀ ∈ A j
    · obtain ⟨v₀, hv₀⟩ := hex
      let H := (A j).direction.comap L
      let _ : Fintype H := Fintype.ofFinite H
      refine ⟨H, inferInstance, inferInstance, inferInstance, ι.comp H.subtype, w₀ + ι v₀,
        c * a j * (φ v₀ * χ j (b + L v₀)),
        fun p => (φ p * form φ v₀ p) * (χ j (L p) * form (χ j) (b + L v₀) (L p)), ?_, fun w => ?_⟩
      · exact ((hφ.shift v₀).comp H.subtype).mul_phase (((hχ j).shift (b + L v₀)).comp (L.comp H.subtype))
      · beta_reduce
        rw [sum_shift v₀]
        rw [sum_submodule H]
        · conv_rhs => rw [mul_assoc, mul_assoc, Finset.mul_sum, Finset.mul_sum]
          refine congrArg (c * ·) ?_
          refine Finset.sum_congr rfl fun p _ => ?_
          have hm : b + L (v₀ + p.1) ∈ A j := by
            have h1 : L p.1 ∈ (A j).direction := p.2
            have h2 := (AffineSubspace.vadd_mem_iff_mem_direction (L p.1) hv₀).mpr h1
            rw [vadd_eq_add] at h2
            rw [map_add]
            have e : b + (L v₀ + L p.1) = L p.1 + (b + L v₀) := by abel
            rw [e]
            exact h2
          have e2 : b + L (v₀ + p.1) = (b + L v₀) + L p.1 := by rw [map_add, add_assoc]
          rw [ind_true hm, e2, hφ.shift_eq, (hχ j).shift_eq]
          have e3 : ind F (w = w₀ + ι (v₀ + p.1)) = ind F (w = w₀ + ι v₀ + (ι.comp H.subtype) p) := by
            rw [map_add, ← add_assoc]
            rfl
          rw [e3]
          ring
        · intro v hv
          have : ¬ b + L (v₀ + v) ∈ A j := by
            intro h1
            apply hv
            change L v ∈ (A j).direction
            rw [← AffineSubspace.vadd_mem_iff_mem_direction (L v) hv₀, vadd_eq_add]
            have e : L v + (b + L v₀) = b + L (v₀ + v) := by rw [map_add]; abel
            rw [e]
            exact h1
          rw [ind_false this]
          ring
    · refine ⟨PUnit, inferInstance, inferInstance, inferInstance, 0, 0, 0, fun _ => 1, IsPhase.one, fun w => ?_⟩
      beta_reduce
      rw [zero_mul]
      have : ∑ v, ind F (w = w₀ + ι v) * (φ v * (a j * (ind F (b + L v ∈ A j) * χ j (b + L v)))) = 0 := by
        refine Finset.sum_eq_zero fun v _ => ?_
        rw [ind_false (fun h0 => hex ⟨v, h0⟩)]
        ring
      rw [this, mul_zero]
  · beta_reduce
    rw [h]
    rw [← Finset.mul_sum, Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [← Finset.mul_sum, ← Finset.mul_sum, hd]

end StabilizerRank
