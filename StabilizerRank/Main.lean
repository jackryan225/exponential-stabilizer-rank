import StabilizerRank.Boolean
import StabilizerRank.Lift

/-!
# The stabilizer rank of T states, given prices in the plane
-/

namespace StabilizerRank

open Real NOF OAI OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor OAI.Hierarchy
open scoped NNReal

variable {F : Type*} [Field F]

/-- The price of a sum. -/
theorem price_sum_le {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] (P : SpectralPlacementPrices F Plane)
    {f : X → Y → Z → F} {J : ℕ} (t : Fin J → X → Y → Z → F) (hsum : ∀ x y z, f x y z = ∑ j, t j x y z) (B : ℝ)
    (hB : ∀ j, P.price (hat (t j)) place ≤ B) (hne : (hat f).coeff ≠ 0) :
    1 ≤ J ∧ P.price (hat f) place ≤ B + P.price (Raw.diagonal Old F (Fin 2)) place * logb 2 J := by
  classical
  let S (j : Fin J) : (∀ i, OLeg X Y Z i) → F := (hat (t j)).coeff
  have hS : ∑ j, S j = (hat f).coeff := by
    funext a
    rw [Finset.sum_apply]
    have e : ∀ a : ∀ i, OLeg X Y Z i, (∑ j, ind F (Agree a) * t j (a .o1).1 (a .o1).2 (a .o2).2) =
        ind F (Agree a) * f (a .o1).1 (a .o1).2 (a .o2).2 := by
      intro a
      rw [hsum, Finset.mul_sum]
    exact e a
  have hJ : 1 ≤ J := by
    by_contra hJ
    have : J = 0 := by omega
    subst this
    exact hne (hS.symm.trans (Fintype.sum_empty _))
  refine ⟨hJ, le_of_forall_pos_le_add fun ε hε => ?_⟩
  obtain ⟨Y', -, hY', j, hj, hlt⟩ := ForceSelection.exists_summand_of_decompositions (A := OLeg X Y Z) P place
    (subset_affineZariskiClosure {(hat f).coeff} rfl) hne (fun R : Fin J → (∀ i, OLeg X Y Z i) → F => R = S)
    (fun z hz => ⟨S, hS.trans (Set.mem_singleton_iff.mp hz).symm, rfl⟩) hε
  subst hY'
  have h1 : P.price (ForceSelection.raw (A := OLeg X Y Z) (S j)) place ≤ B := hB j
  rw [Fintype.card_fin] at hlt
  have h2 : P.price (ForceSelection.raw (A := OLeg X Y Z) (hat f).coeff) place = P.price (hat f) place := rfl
  rw [h2] at hlt
  linarith

/-- Padding to strings of bits. -/
theorem exists_bits (A : Type) [Fintype A] [Nonempty A] :
    ∃ a : ℕ, (a : ℝ) ≤ logb 2 (Fintype.card A) + 1 ∧ Nonempty (A ↪ (Fin a → Z2)) := by
  classical
  have h1 : (1 : ℝ) ≤ Fintype.card A := by exact_mod_cast Fintype.card_pos
  have h0 : 0 ≤ logb 2 (Fintype.card A : ℝ) := logb_nonneg (by norm_num) h1
  refine ⟨⌈logb 2 (Fintype.card A : ℝ)⌉₊, (Nat.ceil_lt_add_one h0).le, ?_⟩
  apply Function.Embedding.nonempty_of_card_le
  rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]
  have h2 : logb 2 (Fintype.card A : ℝ) ≤ (⌈logb 2 (Fintype.card A : ℝ)⌉₊ : ℕ) := Nat.le_ceil _
  rw [logb_le_iff_le_rpow (by norm_num) (by linarith), rpow_natCast] at h2
  exact_mod_cast h2

/-- A zero-one table on strings of bits whose lift is more expensive than the matrix product. -/
theorem exists_bit_table (P : SpectralPlacementPrices F Plane) :
    ∃ (a b c : ℕ) (S : (Fin a → Z2) → (Fin b → Z2) → (Fin c → Z2) → Prop),
      (a : ℝ) + b + c < P.price (hat fun x y z => ind F (S x y z)) place := by
  classical
  obtain ⟨X, Y, Z, _, _, _, _, _, _, S, _, hS⟩ := exists_zero_one P
  set T : X → Y → Z → F := fun x y z => if S x y z then 1 else 0 with hT
  set cost := logb 2 (Fintype.card X : ℝ) + logb 2 (Fintype.card Y : ℝ) + logb 2 (Fintype.card Z : ℝ) with hcost
  have cost0 : 0 ≤ cost := by
    have h1 : 0 ≤ logb 2 (Fintype.card X : ℝ) := logb_nonneg (by norm_num) (by exact_mod_cast Fintype.card_pos)
    have h2 : 0 ≤ logb 2 (Fintype.card Y : ℝ) := logb_nonneg (by norm_num) (by exact_mod_cast Fintype.card_pos)
    have h3 : 0 ≤ logb 2 (Fintype.card Z : ℝ) := logb_nonneg (by norm_num) (by exact_mod_cast Fintype.card_pos)
    linarith
  have hne : (hat T).coeff ≠ 0 := by
    intro h
    have := P.zero_tensor _ h place
    linarith
  set δ := P.price (hat T) place - cost with hδ
  have hδ0 : 0 < δ := by linarith
  obtain ⟨M, hM⟩ := exists_nat_gt (3 / δ)
  have hM3 : 3 < M * δ := by rwa [div_lt_iff₀ hδ0] at hM
  obtain ⟨a, ha, ⟨eX⟩⟩ := exists_bits (Fin M → X)
  obtain ⟨b, hb, ⟨eY⟩⟩ := exists_bits (Fin M → Y)
  obtain ⟨c, hc, ⟨eZ⟩⟩ := exists_bits (Fin M → Z)
  have card (W : Type) [Fintype W] : logb 2 (Fintype.card (Fin M → W) : ℝ) = M * logb 2 (Fintype.card W : ℝ) := by
    rw [Fintype.card_fun, Fintype.card_fin]
    push_cast
    rw [logb_pow]
  rw [card] at ha hb hc
  let S' (x' : Fin a → Z2) (y' : Fin b → Z2) (z' : Fin c → Z2) : Prop :=
    ∃ x y z, eX x = x' ∧ eY y = y' ∧ eZ z = z' ∧ ∀ i, S (x i) (y i) (z i)
  refine ⟨a, b, c, S', ?_⟩
  have e : (fun x y z => ind F (S' (eX x) (eY y) (eZ z))) = tpow T M := by
    funext x y z
    rw [tpow, hT]
    simp only [Fintype.prod_boole]
    rw [← ind_eq_ite]
    apply ind_congr
    constructor
    · rintro ⟨x', y', z', h1, h2, h3, h⟩
      rw [← eX.injective h1, ← eY.injective h2, ← eZ.injective h3]
      exact h
    · intro h
      exact ⟨x, y, z, rfl, rfl, rfl, h⟩
  have low : M * P.price (hat T) place ≤ P.price (hat fun x y z => ind F (S' x y z)) place := by
    refine (price_pow P T hne M).trans ?_
    rw [← e]
    exact price_mono P (comp_restricts (fun x y z => ind F (S' x y z)) eX.injective eY.injective eZ.injective) place
  refine lt_of_lt_of_le ?_ low
  have : (M : ℝ) * P.price (hat T) place = M * δ + M * cost := by rw [hδ]; ring
  have e' : (M : ℝ) * cost = M * logb 2 (Fintype.card X : ℝ) + M * logb 2 (Fintype.card Y : ℝ) +
    M * logb 2 (Fintype.card Z : ℝ) := by rw [hcost]; ring
  linarith

/-- The coordinates of a string of triples. -/
def triples {X Y Z : Type} [AddCommGroup X] [Module Z2 X] [AddCommGroup Y] [Module Z2 Y] [AddCommGroup Z] [Module Z2 Z]
    (N : ℕ) : (Fin N → X × Y × Z) →ₗ[Z2] (Fin N → X) × (Fin N → Y) × (Fin N → Z) where
  toFun w := (fun i => (w i).1, fun i => (w i).2.1, fun i => (w i).2.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **The core**: a table on strings of bits that is represented by gates and whose lift is more expensive than the matrix
product. Then a decomposition of `n` gates into quadratic phases on affine subspaces has exponentially many terms. -/
theorem rank_core (P : SpectralPlacementPrices F Plane) (h2 : (2 : F) ≠ 0) {B : Type} [AddCommGroup B] [Module Z2 B]
    {g : B → F} {x₀ : B} (hg : g x₀ = 1) {a b c : ℕ} {T : (Fin a → Z2) → (Fin b → Z2) → (Fin c → Z2) → F}
    (hS : (a : ℝ) + b + c < P.price (hat T) place) {S₀ : Type} [Fintype S₀]
    (hrep : Rep g S₀ (fun w : (Fin a → Z2) × (Fin b → Z2) × (Fin c → Z2) => T w.1 w.2.1 w.2.2)) :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ J : ℕ,
      (∃ (a : Fin J → F) (A : Fin J → AffineSubspace Z2 (Fin n → B)) (χ : Fin J → (Fin n → B) → F),
        (∀ j, IsPhase (χ j)) ∧ ∀ b, gates g (Fin n) b = ∑ j, a j * (ind F (b ∈ A j) * χ j b)) →
      (2 : ℝ) ^ (c * n) ≤ J := by
  classical
  let X := Fin a → Z2
  let Y := Fin b → Z2
  let Z := Fin c → Z2
  set δ := P.price (hat T) place - (a + b + c) with hδ
  have hδ0 : 0 < δ := by linarith
  have hne : (hat T).coeff ≠ 0 := by
    intro h
    have h0 := P.zero_tensor _ h place
    have : (0 : ℝ) ≤ a + b + c := by positivity
    linarith
  let y : Old ↪ Plane := ⟨place, place_injective⟩
  have hD := P.diagonal_pos y
  set D := P.price (Raw.diagonal Old F (Fin 2)) place with hDdef
  have hD' : 0 < D := hD
  refine exponential_of_powers (c := δ / D) (by positivity) (Fintype.card S₀) fun N n J hn hJ => ?_
  obtain ⟨α, A, χ, hχ, hd⟩ := hJ
  -- the power is represented by `n` gates
  have hc : Fintype.card (Fin N × S₀) ≤ Fintype.card (Fin n) := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    exact hn
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hc
  have r1 := ((hrep.pow N).push (triples (X := X) (Y := Y) (Z := Z) N)).embed hg e
  have r2 : Rep g (Fin n) (fun u : (Fin N → X) × (Fin N → Y) × (Fin N → Z) => tpow T N u.1 u.2.1 u.2.2) := by
    refine r1.congr fun u => ?_
    rw [Finset.sum_eq_single (fun i => (u.1 i, u.2.1 i, u.2.2 i))]
    · rw [ind_true (p := u = triples N fun i => (u.1 i, u.2.1 i, u.2.2 i)) rfl, one_mul]
      rfl
    · intro w _ hw
      rw [ind_false, zero_mul]
      intro h
      apply hw
      funext i
      rw [h]
      rfl
    · intro h
      exact absurd (Finset.mem_univ _) h
  obtain ⟨s, hs, hsum⟩ := r2.decompose α A χ hχ hd
  -- every summand is cheap
  have card (m : ℕ) : logb 2 (Fintype.card (Fin N → Fin m → Z2) : ℝ) = N * m := by
    rw [Fintype.card_fun, Fintype.card_fun, ZMod.card, Fintype.card_fin, Fintype.card_fin]
    push_cast
    rw [logb_pow, logb_pow, logb_self_eq_one (by norm_num), mul_one]
  have cheap (j : Fin J) : P.price (hat fun x y z => s j (x, y, z)) place ≤ N * (a + b + c) := by
    refine (stab_price P ((hs j).stab h2)).trans (le_of_eq ?_)
    rw [card, card, card]
    ring
  obtain ⟨x0, y0, z0, h0⟩ := exists_of_hat_ne_zero hne
  have hne' : (hat (tpow T N)).coeff ≠ 0 := by
    refine hat_ne_zero ⟨fun _ => x0, fun _ => y0, fun _ => z0, ?_⟩
    rw [tpow]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => h0
  obtain ⟨hJ1, hup⟩ := price_sum_le P (fun j x y z => s j (x, y, z)) (fun x y z => hsum (x, y, z)) _ cheap hne'
  refine ⟨hJ1, ?_⟩
  have low := price_pow P T hne N
  have : (N : ℝ) * P.price (hat T) place = N * δ + N * (a + b + c) := by rw [hδ]; ring
  rw [← mul_div_assoc, div_le_iff₀ hD']
  linarith

/-- **Products of gates**: if conjunctions are represented by the gate, then a decomposition of `n` gates into quadratic
phases on affine subspaces has exponentially many terms. -/
theorem rank_lower_bound (P : SpectralPlacementPrices F Plane) (h2 : (2 : F) ≠ 0) {B : Type} [AddCommGroup B] [Module Z2 B]
    {g : B → F} {x₀ : B} (hg : g x₀ = 1) (hand : RepE g (fun q : Z2 × Z2 × Z2 => ind F (q.2.2 = q.1 * q.2.1))) :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ J : ℕ,
      (∃ (a : Fin J → F) (A : Fin J → AffineSubspace Z2 (Fin n → B)) (χ : Fin J → (Fin n → B) → F),
        (∀ j, IsPhase (χ j)) ∧ ∀ b, gates g (Fin n) b = ∑ j, a j * (ind F (b ∈ A j) * χ j b)) →
      (2 : ℝ) ^ (c * n) ≤ J := by
  classical
  obtain ⟨a, b, c, S, hS⟩ := exists_bit_table P
  obtain ⟨S₀, _, hrep⟩ := rep_zeroOne (W := (Fin a → Z2) × (Fin b → Z2) × (Fin c → Z2)) hand
    (fun w => S w.1 w.2.1 w.2.2)
  exact rank_core P h2 hg hS hrep

/-! ### The standard form of stabilizer states -/

theorem tg_eq_pow (κ : F) (x : Z2) : tg κ x = κ ^ x.val := by
  rcases z2_cases x with rfl | rfl
  · simp [tg]
  · have : (1 : Z2).val = 1 := rfl
    simp [tg, this]

theorem sg_mul_eq_pow (x y : Z2) : sg F (x * y) = (-1) ^ (x.val * y.val) := by
  have : (1 : Z2).val = 1 := rfl
  rcases z2_cases x with rfl | rfl <;> rcases z2_cases y with rfl | rfl <;> simp [sg, this]

theorem IsPhase.pow {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] {φ : W → F} (h : IsPhase φ) (m : ℕ) : IsPhase (fun w => φ w ^ m) := by
  have := IsPhase.prod (Finset.range m) (fun _ => φ) fun _ _ => h
  simpa using this

/-- The phase `i ^ l(b) (-1) ^ q(b)`. -/
theorem isPhase_standard {ι : F} (hι : ι ^ 4 = 1) {n : ℕ} (l : Fin n → ℕ) (q : Fin n → Fin n → ℕ) :
    IsPhase (fun b : Fin n → Z2 => ι ^ (∑ k, l k * (b k).val) * (-1) ^ (∑ k, ∑ m, q k m * ((b k).val * (b m).val))) := by
  have h1 : IsPhase (fun b : Fin n → Z2 => ∏ k, tg ι (b k) ^ l k) :=
    IsPhase.prod Finset.univ (fun k (b : Fin n → Z2) => tg ι (b k) ^ l k) fun k _ =>
      ((isPhase_tg hι).comp (LinearMap.proj (R := Z2) (φ := fun _ : Fin n => Z2) k)).pow (l k)
  have h2 : IsPhase (fun b : Fin n → Z2 => ∏ k, ∏ m, sg F (b k * b m) ^ q k m) :=
    IsPhase.prod Finset.univ (fun k (b : Fin n → Z2) => ∏ m, sg F (b k * b m) ^ q k m) fun k _ =>
      IsPhase.prod Finset.univ (fun m (b : Fin n → Z2) => sg F (b k * b m) ^ q k m) fun m _ =>
        (isPhase_sg (LinearMap.proj (R := Z2) (φ := fun _ : Fin n => Z2) k)
          (LinearMap.proj (R := Z2) (φ := fun _ : Fin n => Z2) m)).pow (q k m)
  have e : (fun b : Fin n → Z2 => ι ^ (∑ k, l k * (b k).val) * (-1) ^ (∑ k, ∑ m, q k m * ((b k).val * (b m).val))) =
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

/-- The same phase with the bits in blocks. -/
theorem isPhase_blocks {ι : F} (hι : ι ^ 4 = 1) {n m : ℕ} (l : Fin n × Fin m → ℕ)
    (q : Fin n × Fin m → Fin n × Fin m → ℕ) : IsPhase (fun b : Fin n → Fin m → Z2 => ι ^ (∑ k, l k * (b k.1 k.2).val) *
      (-1) ^ (∑ k, ∑ k', q k k' * ((b k.1 k.2).val * (b k'.1 k'.2).val))) := by
  let co (k : Fin n × Fin m) : (Fin n → Fin m → Z2) →ₗ[Z2] Z2 :=
    (LinearMap.proj (R := Z2) (φ := fun _ : Fin m => Z2) k.2).comp
      (LinearMap.proj (R := Z2) (φ := fun _ : Fin n => Fin m → Z2) k.1)
  have h1 : IsPhase (fun b : Fin n → Fin m → Z2 => ∏ k, tg ι (b k.1 k.2) ^ l k) :=
    IsPhase.prod Finset.univ (fun k (b : Fin n → Fin m → Z2) => tg ι (b k.1 k.2) ^ l k) fun k _ =>
      ((isPhase_tg hι).comp (co k)).pow (l k)
  have h2 : IsPhase (fun b : Fin n → Fin m → Z2 => ∏ k, ∏ k', sg F (b k.1 k.2 * b k'.1 k'.2) ^ q k k') :=
    IsPhase.prod Finset.univ (fun k (b : Fin n → Fin m → Z2) => ∏ k', sg F (b k.1 k.2 * b k'.1 k'.2) ^ q k k') fun k _ =>
      IsPhase.prod Finset.univ (fun k' (b : Fin n → Fin m → Z2) => sg F (b k.1 k.2 * b k'.1 k'.2) ^ q k k') fun k' _ =>
        (isPhase_sg (co k) (co k')).pow (q k k')
  have e : (fun b : Fin n → Fin m → Z2 => ι ^ (∑ k, l k * (b k.1 k.2).val) *
      (-1) ^ (∑ k, ∑ k', q k k' * ((b k.1 k.2).val * (b k'.1 k'.2).val))) =
      fun b => (∏ k, tg ι (b k.1 k.2) ^ l k) * ∏ k, ∏ k', sg F (b k.1 k.2 * b k'.1 k'.2) ^ q k k' := by
    funext b
    congr 1
    · rw [← Finset.prod_pow_eq_pow_sum]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [tg_eq_pow, ← pow_mul, mul_comm]
    · rw [← Finset.prod_pow_eq_pow_sum]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← Finset.prod_pow_eq_pow_sum]
      refine Finset.prod_congr rfl fun k' _ => ?_
      rw [sg_mul_eq_pow, ← pow_mul, mul_comm]
  rw [e]
  exact h1.mul_phase h2

open Classical in
/-- **The exact stabilizer rank of `n` T states is exponential**, given prices in the plane. -/
theorem t_state (P : SpectralPlacementPrices F Plane) (h2 : (2 : F) ≠ 0) {ω : F} (hω : ω ^ 4 = -1) :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ (J : ℕ) (a : Fin J → F) (A : Fin J → AffineSubspace (ZMod 2) (Fin n → ZMod 2))
      (l : Fin J → Fin n → ℕ) (q : Fin J → Fin n → Fin n → ℕ),
      (∀ b : Fin n → ZMod 2, ω ^ (∑ k, (b k).val) = ∑ j, a j * ((if b ∈ A j then 1 else 0) *
        ((ω ^ 2) ^ (∑ k, l j k * (b k).val) * (-1) ^ (∑ k, ∑ m, q j k m * ((b k).val * (b m).val))))) →
      (2 : ℝ) ^ (c * n) ≤ J := by
  obtain ⟨c, hc, n₀, h⟩ := rank_lower_bound P h2 (g := tg ω) (x₀ := 0) (by simp [tg]) (rep_and h2 hω)
  refine ⟨c, hc, n₀, fun n hn J a A l q hb => h n hn J ⟨a, A, _, fun j => isPhase_standard (ι := ω ^ 2) ?_ (l j) (q j),
    fun b => ?_⟩⟩
  · rw [← pow_mul, show 2 * 4 = 4 * 2 from rfl, pow_mul, hω]
    norm_num
  · rw [gates]
    have e : ∏ i, tg ω (b i) = ω ^ (∑ k, (b k).val) := by
      rw [← Finset.prod_pow_eq_pow_sum]
      exact Finset.prod_congr rfl fun k _ => tg_eq_pow ω (b k)
    rw [e, hb]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ind_eq_ite]

open Classical in
/-- **Conjunctions of sets that are not affine**, given prices in the plane: if `S` is a set of strings of `m` bits with
`x, y, z ∈ S` and `x + y + z ∉ S`, then the indicator of `S ^ n` is not a linear combination of fewer than `2 ^ (c n)`
quadratic phases on affine subspaces. For `S = {00, 01, 10}` this is the conjunction of `n` disjoint clauses of width two. -/
theorem and_nonaffine (P : SpectralPlacementPrices F Plane) (h2 : (2 : F) ≠ 0) {ι : F} (hι : ι ^ 4 = 1) {m : ℕ}
    (S : Set (Fin m → ZMod 2)) {x y z : Fin m → ZMod 2} (hx : x ∈ S) (hy : y ∈ S) (hz : z ∈ S) (hxyz : x + y + z ∉ S) :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ (J : ℕ) (a : Fin J → F)
      (A : Fin J → AffineSubspace (ZMod 2) (Fin n → Fin m → ZMod 2)) (l : Fin J → Fin n × Fin m → ℕ)
      (q : Fin J → Fin n × Fin m → Fin n × Fin m → ℕ),
      (∀ b : Fin n → Fin m → ZMod 2, (if ∀ i, b i ∈ S then (1 : F) else 0) = ∑ j, a j * ((if b ∈ A j then 1 else 0) *
        (ι ^ (∑ k, l j k * (b k.1 k.2).val) * (-1) ^ (∑ k, ∑ k', q j k k' * ((b k.1 k.2).val * (b k'.1 k'.2).val))))) →
      (2 : ℝ) ^ (c * n) ≤ J := by
  obtain ⟨c, hc, n₀, h⟩ := rank_lower_bound P h2 (g := fun b => ind F (b ∈ S)) (x₀ := x) (ind_true hx)
    (rep_and_of_nonaffine (fun b => b ∈ S) hx hy hz hxyz)
  refine ⟨c, hc, n₀, fun n hn J a A l q hb => h n hn J ⟨a, A, _, fun j => isPhase_blocks hι (l j) (q j), fun b => ?_⟩⟩
  rw [gates, prod_ind, ind_eq_ite, hb]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ind_eq_ite]

open Classical in
/-- **Cubic phases are not sums of few quadratic phases**, given prices in the plane: `(-1) ^ (x₁y₁z₁ + ⋯ + x_n y_n z_n)` is
not a linear combination of fewer than `2 ^ (c n)` quadratic phases on affine subspaces (`n` CCZ states). -/
theorem ccz_state (P : SpectralPlacementPrices F Plane) (h2 : (2 : F) ≠ 0) {ι : F} (hι : ι ^ 4 = 1) :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ (J : ℕ) (a : Fin J → F)
      (A : Fin J → AffineSubspace (ZMod 2) (Fin n → Fin 3 → ZMod 2)) (l : Fin J → Fin n × Fin 3 → ℕ)
      (q : Fin J → Fin n × Fin 3 → Fin n × Fin 3 → ℕ),
      (∀ b : Fin n → Fin 3 → ZMod 2, (-1 : F) ^ (∑ i, (b i 0).val * (b i 1).val * (b i 2).val) =
        ∑ j, a j * ((if b ∈ A j then 1 else 0) * (ι ^ (∑ k, l j k * (b k.1 k.2).val) *
          (-1) ^ (∑ k, ∑ k', q j k k' * ((b k.1 k.2).val * (b k'.1 k'.2).val))))) → (2 : ℝ) ^ (c * n) ≤ J := by
  obtain ⟨c, hc, n₀, h⟩ := rank_lower_bound P h2 (g := ccz F) (x₀ := 0) (by simp [ccz, sg]) (rep_and_ccz h2)
  refine ⟨c, hc, n₀, fun n hn J a A l q hb => h n hn J ⟨a, A, _, fun j => isPhase_blocks hι (l j) (q j), fun b => ?_⟩⟩
  have e : gates (ccz F) (Fin n) b = (-1 : F) ^ (∑ i, (b i 0).val * (b i 1).val * (b i 2).val) := by
    rw [gates, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    have h1 : (1 : Z2).val = 1 := rfl
    rw [ccz]
    rcases z2_cases (b i 0) with h3 | h3 <;> rcases z2_cases (b i 1) with h4 | h4 <;>
      rcases z2_cases (b i 2) with h5 | h5 <;> rw [h3, h4, h5] <;> simp [sg, h1]
  rw [e, hb]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ind_eq_ite]

end StabilizerRank
