import StabilizerRank.Clifford
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Products of gates are dense in all tables

If `r` is not a root of unity, then the products of `r ^ ℓ(w)` over linear forms `ℓ` are Zariski dense in the space of all
functions on a finite space of bit strings. Prices pass to the closure. So the products reach every price.
-/

namespace StabilizerRank

open Real NOF OAI OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor OAI.Hierarchy

variable {F : Type*} [Field F]

/-! ### Characters -/

section characters

variable {W : Type} [AddCommGroup W] [Module Z2 W]

theorem sg_rat (x : Z2) : sg ℚ x = 1 - 2 * (x.val : ℚ) := by
  have : (1 : Z2).val = 1 := rfl
  rcases z2_cases x with rfl | rfl
  · simp [sg]
  · simp [sg, this]
    norm_num

/-- The sign character of the dual. -/
def sgHom (w : W) : Multiplicative (W →ₗ[Z2] Z2) →* ℚ where
  toFun l := sg ℚ (l.toAdd w)
  map_one' := by
    change sg ℚ ((0 : W →ₗ[Z2] Z2) w) = 1
    rw [LinearMap.zero_apply]
    simp [sg]
  map_mul' l m := by
    change sg ℚ ((l.toAdd + m.toAdd) w) = _
    rw [LinearMap.add_apply, sg_add]

theorem sgHom_injective : Function.Injective (sgHom (W := W)) := by
  intro v w h
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff Z2]
  intro l
  have h1 : sg ℚ (l v) = sg ℚ (l w) := DFunLike.congr_fun h (Multiplicative.ofAdd l)
  rw [map_sub, sub_eq_zero]
  rcases z2_cases (l v) with h2 | h2 <;> rcases z2_cases (l w) with h3 | h3 <;> rw [h2, h3] at h1 ⊢
  · exfalso
    simp [sg] at h1
    norm_num at h1
  · exfalso
    simp [sg] at h1
    norm_num at h1

/-- A function on bit strings is determined by its sum and by its sums over the half spaces. -/
theorem eq_of_sums [Fintype W] (k k' : W → ℕ) (h0 : ∑ w, k w = ∑ w, k' w)
    (h : ∀ l : W →ₗ[Z2] Z2, ∑ w, (l w).val * k w = ∑ w, (l w).val * k' w) : k = k' := by
  classical
  have ind : LinearIndependent ℚ (fun w : W => (sgHom w : Multiplicative (W →ₗ[Z2] Z2) → ℚ)) :=
    (linearIndependent_monoidHom (Multiplicative (W →ₗ[Z2] Z2)) ℚ).comp sgHom sgHom_injective
  rw [Fintype.linearIndependent_iff] at ind
  have h1 : ∑ w, ((k w : ℚ) - k' w) • (sgHom w : Multiplicative (W →ₗ[Z2] Z2) → ℚ) = 0 := by
    funext l
    rw [Finset.sum_apply, Pi.zero_apply]
    have e (w : W) : (((k w : ℚ) - k' w) • (sgHom w : Multiplicative (W →ₗ[Z2] Z2) → ℚ)) l =
        ((k w : ℚ) - k' w) - 2 * (((l.toAdd w).val * k w : ℕ) - ((l.toAdd w).val * k' w : ℕ) : ℚ) := by
      change ((k w : ℚ) - k' w) * sg ℚ (l.toAdd w) = _
      rw [sg_rat]
      push_cast
      ring
    simp only [e]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, ← Nat.cast_sum,
      ← Nat.cast_sum, ← Nat.cast_sum, ← Nat.cast_sum, h0, h l.toAdd]
    ring
  funext w
  have := ind _ h1 w
  rw [sub_eq_zero] at this
  exact_mod_cast this

variable [Fintype W] [Fintype (W →ₗ[Z2] Z2)]

/-- The product of powers of the gate at linear forms. -/
def mono (r : F) (p : ℕ × ((W →ₗ[Z2] Z2) → ℕ)) (w : W) : F := r ^ p.1 * ∏ l, tg r (l w) ^ p.2 l

/-- The exponent. -/
def expo (k : W → ℕ) (p : ℕ × ((W →ₗ[Z2] Z2) → ℕ)) : ℕ := ∑ w, (p.1 + ∑ l, (l w).val * p.2 l) * k w

theorem mono_eq (r : F) (p : ℕ × ((W →ₗ[Z2] Z2) → ℕ)) (w : W) : mono r p w = r ^ (p.1 + ∑ l, (l w).val * p.2 l) := by
  rw [mono, pow_add, ← Finset.prod_pow_eq_pow_sum]
  congr 1
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [tg_eq_pow, pow_mul]

theorem expo_add (k : W → ℕ) (p q : ℕ × ((W →ₗ[Z2] Z2) → ℕ)) : expo k (p + q) = expo k p + expo k q := by
  rw [expo, expo, expo, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  have : ∑ l : W →ₗ[Z2] Z2, (l w).val * (p + q).2 l = ∑ l, (l w).val * p.2 l + ∑ l, (l w).val * q.2 l := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    change _ * (p.2 l + q.2 l) = _
    ring
  rw [this]
  change (p.1 + q.1 + _) * k w = _
  ring

/-- The character that belongs to a monomial. -/
def monoHom (r : F) (k : W →₀ ℕ) : Multiplicative (ℕ × ((W →ₗ[Z2] Z2) → ℕ)) →* F where
  toFun p := r ^ expo k p.toAdd
  map_one' := by
    have h := expo_add (k : W → ℕ) 0 0
    rw [add_zero] at h
    have : expo (k : W → ℕ) 0 = 0 := by omega
    change r ^ expo (k : W → ℕ) 0 = 1
    rw [this, pow_zero]
  map_mul' p q := by
    change r ^ expo (k : W → ℕ) (p.toAdd + q.toAdd) = _
    rw [expo_add, pow_add]

theorem monoHom_injective {r : F} (hr0 : r ≠ 0) (hr : ∀ N : ℕ, 0 < N → r ^ N ≠ 1) :
    Function.Injective (monoHom (W := W) r) := by
  classical
  have key : ∀ m n : ℕ, r ^ m = r ^ n → m = n := by
    have aux : ∀ m n : ℕ, m < n → r ^ m ≠ r ^ n := by
      intro m n hmn h
      apply hr (n - m) (by omega)
      have : r ^ m * r ^ (n - m) = r ^ m * 1 := by rw [← pow_add, mul_one, h]; congr 1; omega
      exact mul_left_cancel₀ (pow_ne_zero m hr0) this
    intro m n h
    rcases lt_trichotomy m n with h1 | h1 | h1
    · exact absurd h (aux m n h1)
    · exact h1
    · exact absurd h.symm (aux n m h1)
  intro k k' h
  have h1 (p : ℕ × ((W →ₗ[Z2] Z2) → ℕ)) : expo (k : W → ℕ) p = expo (k' : W → ℕ) p :=
    key _ _ (DFunLike.congr_fun h (Multiplicative.ofAdd p))
  apply DFunLike.coe_injective
  apply eq_of_sums
  · have := h1 (1, 0)
    simpa [expo] using this
  · intro l
    have := h1 (0, Pi.single l 1)
    simpa [expo, Pi.single_apply, Finset.sum_ite_eq', mul_ite] using this

/-- **Density**: a polynomial that vanishes at all the products is zero. -/
theorem dense {r : F} (hr0 : r ≠ 0) (hr : ∀ N : ℕ, 0 < N → r ^ N ≠ 1) (Q : MvPolynomial W F)
    (hQ : ∀ p, MvPolynomial.eval (mono r p) Q = 0) : Q = 0 := by
  classical
  have ind : LinearIndependent F (fun k : W →₀ ℕ =>
      (monoHom r k : Multiplicative (ℕ × ((W →ₗ[Z2] Z2) → ℕ)) → F)) :=
    (linearIndependent_monoidHom _ F).comp (monoHom r) (monoHom_injective hr0 hr)
  rw [linearIndependent_iff'] at ind
  have h1 : ∑ k ∈ Q.support, Q.coeff k • (monoHom r k : Multiplicative (ℕ × ((W →ₗ[Z2] Z2) → ℕ)) → F) = 0 := by
    funext p
    rw [Finset.sum_apply, Pi.zero_apply, ← hQ p.toAdd, MvPolynomial.eval_eq']
    refine Finset.sum_congr rfl fun k _ => ?_
    change Q.coeff k * r ^ expo (k : W → ℕ) p.toAdd = _
    congr 1
    rw [expo, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [mono_eq, pow_mul]
  rw [← MvPolynomial.support_eq_empty, Finset.eq_empty_iff_forall_notMem]
  intro k hk
  exact (MvPolynomial.mem_support_iff.mp hk) (ind _ _ h1 k hk)

end characters

/-! ### Representation of the products -/

section rep

variable {W : Type} [AddCommGroup W] [Module Z2 W] [Fintype W] {B : Type} [AddCommGroup B] [Module Z2 B] {g : B → F}

theorem RepE.one : RepE g (fun _ : W => (1 : F)) := by
  refine ⟨Empty, inferInstance, (Rep.direct (IsPhase.one (F := F) (W := W)) (0 : Empty → B) 0).congr fun w => ?_⟩
  simp [gates]

theorem RepE.power {f : W → F} (h : RepE g f) (m : ℕ) : RepE g (fun w => f w ^ m) := by
  induction m with
  | zero => exact RepE.one.congr fun w => pow_zero _
  | succ m ih => exact (ih.mul h).congr fun w => pow_succ _ _

theorem RepE.finprod {ι : Type*} (s : Finset ι) {f : ι → W → F} (h : ∀ i, RepE g (f i)) :
    RepE g (fun w => ∏ i ∈ s, f i w) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact RepE.one.congr fun w => Finset.prod_empty
  | insert i s hi ih => exact ((h i).mul ih).congr fun w => Finset.prod_insert hi

theorem RepE.mono [Fintype (W →ₗ[Z2] Z2)] {r : F} (h : RepE g (tg r)) (p : ℕ × ((W →ₗ[Z2] Z2) → ℕ)) :
    RepE g (mono (W := W) r p) :=
  (RepE.finprod Finset.univ (f := fun l w => tg r (l w) ^ p.2 l) fun l => (h.pull l).power (p.2 l)).smul _

end rep

/-! ### Prices -/

/-- If a gate that is not a root of unity is represented, then a table with a large price is represented. -/
theorem exists_rep_table (P : SpectralPlacementPrices F Plane) {B : Type} [AddCommGroup B] [Module Z2 B] {g : B → F}
    {r : F} (hr0 : r ≠ 0) (hr : ∀ N : ℕ, 0 < N → r ^ N ≠ 1) (hrep : RepE g (tg r)) :
    ∃ (a b c : ℕ) (T : (Fin a → Z2) → (Fin b → Z2) → (Fin c → Z2) → F),
      (a : ℝ) + b + c < P.price (hat T) place ∧
      RepE g (fun w : (Fin a → Z2) × (Fin b → Z2) × (Fin c → Z2) => T w.1 w.2.1 w.2.2) := by
  classical
  obtain ⟨a, b, c, S, hS⟩ := exists_bit_table P
  let X := Fin a → Z2
  let Y := Fin b → Z2
  let Z := Fin c → Z2
  let _ : Fintype ((X × Y × Z) →ₗ[Z2] Z2) :=
    Fintype.ofInjective (fun l => (l : X × Y × Z → Z2)) DFunLike.coe_injective
  set T₀ : X → Y → Z → F := fun x y z => ind F (S x y z) with hT₀
  let tab (f : X × Y × Z → F) : X → Y → Z → F := fun x y z => f (x, y, z)
  have hne : (hat T₀).coeff ≠ 0 := by
    intro h
    have h0 := P.zero_tensor _ h place
    have : (0 : ℝ) ≤ a + b + c := by positivity
    linarith
  let D₀ : Set (X × Y × Z → F) := Set.range (StabilizerRank.mono (W := X × Y × Z) r)
  let D : Set ((∀ i, OLeg X Y Z i) → F) := (fun f => (hat (tab f)).coeff) '' D₀
  have h0 : (fun w : X × Y × Z => T₀ w.1 w.2.1 w.2.2) ∈ affineZariskiClosure D₀ := by
    intro Q hQ
    rw [dense hr0 hr Q fun p => hQ _ ⟨p, rfl⟩, map_zero]
  let pol (l : ∀ i, OLeg X Y Z i) : MvPolynomial (X × Y × Z) F :=
    MvPolynomial.C (ind F (Agree l)) * MvPolynomial.X ((l .o1).1, (l .o1).2, (l .o2).2)
  have hpol (f : X × Y × Z → F) : (fun l => MvPolynomial.eval f (pol l)) = (hat (tab f)).coeff := by
    funext l
    simp only [pol, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
    rfl
  have h1 : (hat T₀).coeff ∈ affineZariskiClosure D := by
    have := mapsTo_affineZariskiClosure_of_polynomial pol (S := D₀) (T := D)
      (fun f hf => ⟨f, hf, (hpol f).symm⟩) h0
    have e := hpol (fun w => T₀ w.1 w.2.1 w.2.2)
    rw [← show (hat (tab fun w => T₀ w.1 w.2.1 w.2.2)).coeff = (hat T₀).coeff from rfl, ← e]
    exact this
  obtain ⟨Y', hD, -, j, hj, hlt⟩ := ForceSelection.exists_summand_of_decompositions (A := OLeg X Y Z) (J := Fin 1) P place
    h1 hne (fun _ => True) (fun z _ => ⟨fun _ => z, by simp, trivial⟩)
    (ε := P.price (hat T₀) place - (a + b + c)) (by linarith)
  rw [Fintype.card_fin, Nat.cast_one, logb_one, mul_zero, sub_zero] at hlt
  rw [Fin.sum_univ_one] at hD
  obtain ⟨f, ⟨p, rfl⟩, hf⟩ := hD
  have hj0 : j = 0 := Subsingleton.elim _ _
  subst hj0
  refine ⟨a, b, c, tab (StabilizerRank.mono r p), ?_, RepE.mono hrep p⟩
  have h2 : P.price (ForceSelection.raw (A := OLeg X Y Z) (Y' 0)) place = P.price (hat (tab (StabilizerRank.mono r p))) place := by
    rw [← hf]
    rfl
  have h3 : P.price (ForceSelection.raw (A := OLeg X Y Z) (hat T₀).coeff) place = P.price (hat T₀) place := rfl
  rw [h2, h3] at hlt
  linarith

/-- **Generic gates**: if a gate that is not a root of unity is represented, the rank is exponential. -/
theorem rank_generic (P : SpectralPlacementPrices F Plane) (h2 : (2 : F) ≠ 0) {B : Type} [AddCommGroup B] [Module Z2 B]
    {g : B → F} {x₀ : B} (hg : g x₀ = 1) {r : F} (hr0 : r ≠ 0) (hr : ∀ N : ℕ, 0 < N → r ^ N ≠ 1) (hrep : RepE g (tg r)) :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ J : ℕ,
      (∃ (a : Fin J → F) (A : Fin J → AffineSubspace Z2 (Fin n → B)) (χ : Fin J → (Fin n → B) → F),
        (∀ j, IsPhase (χ j)) ∧ ∀ b, gates g (Fin n) b = ∑ j, a j * (ind F (b ∈ A j) * χ j b)) →
      (2 : ℝ) ^ (c * n) ≤ J := by
  obtain ⟨a, b, c, T, hT, S₀, _, h⟩ := exists_rep_table P hr0 hr hrep
  exact rank_core P h2 hg hT h

end StabilizerRank
