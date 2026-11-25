import NOF.Ind
import OAI.Hierarchy.WireProductPrice
import OAI.Hierarchy.DiagonalRankPrice
import OAI.LinearAlgebra.MatrixExponent.Rectangle
import OAI.LinearAlgebra.SpectralBooks.Theorem

/-!
# Two lemmas on spectral prices

* a label that is shared by three sites at the price of one side is free only if the third site is on the segment;
* midpoints are unique.
-/

namespace NOF

open Real OAI OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor OAI.Hierarchy
  OAI.LinearAlgebra.MatrixExponent

section general

variable {I : Type} [Fintype I] {F : Type*} [Field F]

/-- Reading coordinates gives a restriction. -/
theorem restricts_of_read {S T : Raw.{0} I F} (e : ∀ i, S.Leg i → T.Leg i)
    (h : ∀ x, S.coeff x = T.coeff (fun i => e i (x i))) : S.Restricts T := by
  classical
  refine ⟨fun i b a => if a = e i b then 1 else 0, fun x => ?_⟩
  simp_rw [Fintype.prod_boole]
  simp [h, ← funext_iff]

theorem price_mono [Nonempty I] {X : Type*} [MetricSpace X] (P : SpectralPlacementPrices F X) {S T : Raw.{0} I F}
    (h : S.Restricts T) (x : I → X) : P.price S x ≤ P.price T x := by
  rcases P.all_zero_or_normalized_at x with price | ⟨φ, c, hc, price⟩
  · rw [price, price]
  · rw [price, price]
    exact rawLogPrice_mono φ hc.le h

theorem diagonal_ne_zero (J : Type) [Fintype J] [Nonempty J] {q : ℕ} (hq : 0 < q) :
    (Raw.diagonal J F (Fin q)).coeff ≠ 0 := by
  intro hz
  have h := congrFun hz (fun _ => (⟨0, hq⟩ : Fin q))
  change (Raw.diagonal J F (Fin q)).coeff _ = 0 at h
  simp [Raw.diagonal_coeff_at (Classical.arbitrary J)] at h

/-- A letter, with its type in normal form. -/
abbrev letter {q : ℕ} (a : Fin q) : Fin q := a

omit [Fintype I] in
/-- The coefficients of a wire. -/
theorem wire_coeff (q : ℕ) (u v : I) (x : ∀ i, ((Raw.diagonal (Fin 2) F (Fin q)).group ![u, v]).Leg i) :
    ((Raw.diagonal (Fin 2) F (Fin q)).group ![u, v]).coeff x =
      if letter (q := q) (x u ⟨(0 : Fin 2), rfl⟩) = letter (q := q) (x v ⟨(1 : Fin 2), rfl⟩) then 1 else 0 := by
  classical
  let lab : Fin 2 → Fin q := fun s => x (![u, v] s) ⟨s, rfl⟩
  change (Raw.diagonal (Fin 2) F (Fin q)).coeff lab = if lab 0 = lab 1 then 1 else 0
  rw [Raw.diagonal_coeff_at (K := F) (1 : Fin 2) lab]
  congr 1
  refine propext ⟨fun h => h 0, fun h i => ?_⟩
  fin_cases i
  · exact h
  · rfl

end general

/-- The product of three wires with the sides `i, j, k` of a matrix product. -/
noncomputable def triangle (F : Type*) [Field F] (i j k : ℕ) : Raw.{0} (Fin 3) F :=
  (((Raw.diagonal (Fin 2) F (Fin i)).group ![(0 : Fin 3), 2]).mul
    ((Raw.diagonal (Fin 2) F (Fin k)).group ![(0 : Fin 3), 1])).mul
    ((Raw.diagonal (Fin 2) F (Fin j)).group ![(1 : Fin 3), 2])

theorem triangle_price {F X : Type*} [Field F] [MetricSpace X] (P : SpectralPlacementPrices F X) (x : Fin 3 → X)
    {i j k : ℕ} (hi : 0 < i) (hj : 0 < j) (hk : 0 < k) :
    P.price (triangle F i j k) x = dist (x 0) (x 2) * logb 2 i + dist (x 0) (x 1) * logb 2 k +
      dist (x 1) (x 2) * logb 2 j := by
  let U : Fin 3 → Raw.{0} (Fin 3) F := ![(Raw.diagonal (Fin 2) F (Fin i)).group ![(0 : Fin 3), 2],
    (Raw.diagonal (Fin 2) F (Fin k)).group ![(0 : Fin 3), 1], (Raw.diagonal (Fin 2) F (Fin j)).group ![(1 : Fin 3), 2]]
  have h := WirePrice.product P x (triangle F i j k) U (fun e => by
    fin_cases e
    · exact ((Raw.diagonal (Fin 2) F (Fin i)).group_ne_zero_iff _).2 (diagonal_ne_zero _ hi)
    · exact ((Raw.diagonal (Fin 2) F (Fin k)).group_ne_zero_iff _).2 (diagonal_ne_zero _ hk)
    · exact ((Raw.diagonal (Fin 2) F (Fin j)).group_ne_zero_iff _).2 (diagonal_ne_zero _ hj))
    (by rw [Fin.prod_univ_three]; rfl)
  rw [h, Fin.sum_univ_three]
  change P.price ((Raw.diagonal (Fin 2) F (Fin i)).group ![(0 : Fin 3), 2]) x +
    P.price ((Raw.diagonal (Fin 2) F (Fin k)).group ![(0 : Fin 3), 1]) x +
    P.price ((Raw.diagonal (Fin 2) F (Fin j)).group ![(1 : Fin 3), 2]) x = _
  rw [WirePrice.wire, WirePrice.wire, WirePrice.wire]

/-- A rank bound for the matrix product. -/
theorem triangle_restricts {F : Type*} [Field F] {i j k r : ℕ} (h : Rectangle.RankLE F i j k r) :
    (triangle F i j k).Restricts (Raw.diagonal (Fin 3) F (Fin r)) := by
  classical
  obtain ⟨a, b, c, h⟩ := h
  have diag : (Raw.diagonal (Fin 3) F (Fin r)).coeff =
      Crossing.basisTensor (F := F) (A := fun _ : Fin 3 => Fin r) (fun r _ => r) := by
    funext a
    simp only [Raw.diagonal, Crossing.basisTensor]
    apply Finset.sum_congr rfl
    intro r _
    split_ifs <;> rfl
  change Crossing.IsRestriction (triangle F i j k).coeff (Raw.diagonal (Fin 3) F (Fin r)).coeff
  rw [diag]
  apply (Crossing.restriction_basisTensor_iff (fun (l : Fin r) (_ : Fin 3) => l) (triangle F i j k).coeff).mpr
  let M : (s : Fin 3) → (triangle F i j k).Leg s → Fin r → F := fun s =>
    match s with
    | 0 => fun t l => a l (t.1.1 ⟨(0 : Fin 2), rfl⟩, t.1.2 ⟨(0 : Fin 2), rfl⟩)
    | 1 => fun t l => b l (t.1.2 ⟨(1 : Fin 2), rfl⟩, t.2 ⟨(0 : Fin 2), rfl⟩)
    | 2 => fun t l => c l (t.1.1 ⟨(1 : Fin 2), rfl⟩, t.2 ⟨(1 : Fin 2), rfl⟩)
  refine ⟨M, fun x => ?_⟩
  have e : (triangle F i j k).coeff x =
      ((Raw.diagonal (Fin 2) F (Fin i)).group ![(0 : Fin 3), 2]).coeff (fun s => (x s).1.1) *
      ((Raw.diagonal (Fin 2) F (Fin k)).group ![(0 : Fin 3), 1]).coeff (fun s => (x s).1.2) *
      ((Raw.diagonal (Fin 2) F (Fin j)).group ![(1 : Fin 3), 2]).coeff (fun s => (x s).2) := rfl
  rw [e, wire_coeff, wire_coeff, wire_coeff]
  have h' := h ((x 0).1.1 ⟨(0 : Fin 2), rfl⟩, (x 0).1.2 ⟨(0 : Fin 2), rfl⟩)
    ((x 1).1.2 ⟨(1 : Fin 2), rfl⟩, (x 1).2 ⟨(0 : Fin 2), rfl⟩)
    ((x 2).1.1 ⟨(1 : Fin 2), rfl⟩, (x 2).2 ⟨(1 : Fin 2), rfl⟩)
  simp only [Fin.prod_univ_three]
  change _ = ∑ l, a l _ * b l _ * c l _
  rw [h', ite_and, ite_and]
  split_ifs <;> simp

/-- **Free copies lie between.** If a bit that is shared by `a`, `y`, `b` costs the same as a bit that is shared by
`a` and `b`, then `y` lies between `a` and `b`. -/
theorem between_of_free {F X : Type*} [Field F] [MetricSpace X] (P : SpectralPlacementPrices F X) (a y b : X)
    (h : P.price (Raw.diagonal (Fin 3) F (Fin 2)) ![a, y, b] ≤ dist a b) :
    dist a y + dist y b ≤ dist a b := by
  -- the inequality for each small exponent `p`
  have key : ∀ p : ℝ, 0 < p → p ≤ 1 → dist a y + dist y b ≤ dist a b * (1 + 2 * p) := by
    intro p hp hp1
    have up := Rectangle.upper F (a := 1) (b := p) (c := p) zero_le_one hp.le hp.le
    have hU : Rectangle.U 1 p p = 1 + p + p ^ 2 / 4 := by
      have h1 : p ≤ min 1 p := by rw [min_eq_right hp1]
      rw [Rectangle.U, ite_eq_left h1, Rectangle.benchmark]
      have h2 : (1 + p) * p - 1 * p = p ^ 2 := by ring
      rw [h2, max_eq_left (by positivity)]
      field_simp
    rw [hU] at up
    have lt : Rectangle.exponent F 1 p p < 1 + p + p ^ 2 := by nlinarith
    obtain ⟨n, r, hn, hr, hrn⟩ := (Rectangle.exponent_lt_iff_rank zero_le_one hp.le hp.le).mp lt
    have hn0 : 0 < n := by omega
    have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
    have hs1 := Rectangle.side_pos hn0 1
    have hsp := Rectangle.side_pos hn0 p
    have hL : 0 < logb 2 (n : ℝ) := logb_pos (by norm_num) hn1
    -- price of the triangle from below
    have low := triangle_price P ![a, y, b] hs1 hsp hsp
    have upp := price_le_diagonal_mul_log_rank P (triangle F _ _ _) ![a, y, b] r (triangle_restricts hr)
    have side_ge (t : ℝ) : t * logb 2 n ≤ logb 2 (Rectangle.side n t : ℝ) := by
      rw [← logb_rpow_eq_mul_logb_of_pos (by positivity)]
      apply logb_le_logb_of_le (by norm_num) (by positivity)
      exact Nat.le_ceil _
    have hlogr : logb 2 (r : ℝ) ≤ (1 + p + p ^ 2) * logb 2 n := by
      rcases Nat.eq_zero_or_pos r with h0 | h0
      · rw [h0]
        simp only [Nat.cast_zero, logb_zero]
        positivity
      · rw [← logb_rpow_eq_mul_logb_of_pos (by positivity)]
        exact logb_le_logb_of_le (by norm_num) (by exact_mod_cast h0) hrn.le
    have hlogr0 : 0 ≤ logb 2 (r : ℝ) := by
      rcases Nat.eq_zero_or_pos r with h0 | h0
      · simp [h0]
      · exact logb_nonneg (by norm_num) (by exact_mod_cast h0)
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at low
    rw [low] at upp
    have hab : 0 ≤ dist a b := dist_nonneg
    have hay : 0 ≤ dist a y := dist_nonneg
    have hyb : 0 ≤ dist y b := dist_nonneg
    have e1 := mul_le_mul_of_nonneg_left (side_ge 1) hab
    have e2 := mul_le_mul_of_nonneg_left (side_ge p) hay
    have e3 := mul_le_mul_of_nonneg_left (side_ge p) hyb
    have e4 : P.price (Raw.diagonal (Fin 3) F (Fin 2)) ![a, y, b] * logb 2 r ≤
        dist a b * ((1 + p + p ^ 2) * logb 2 n) :=
      (mul_le_mul_of_nonneg_right h hlogr0).trans (mul_le_mul_of_nonneg_left hlogr hab)
    have e6 : 0 ≤ dist a b * (p ^ 2 * logb 2 n) := by positivity
    have e5 : (dist a y + dist y b) * (p * logb 2 n) ≤ (dist a b * (1 + 2 * p)) * (p * logb 2 n) := by
      have l1 : dist a b * (1 * logb 2 n) + dist a y * (p * logb 2 n) + dist y b * (p * logb 2 n) ≤
          dist a b * ((1 + p + p ^ 2) * logb 2 n) := by linarith
      have l2 : dist a b * ((1 + p + p ^ 2) * logb 2 n) = dist a b * (1 * logb 2 n) +
          dist a b * (p * logb 2 n) + dist a b * (p ^ 2 * logb 2 n) := by ring
      have l3 : dist a b * (1 + 2 * p) * (p * logb 2 n) =
          dist a b * (p * logb 2 n) + 2 * (dist a b * (p ^ 2 * logb 2 n)) := by ring
      linarith
    exact le_of_mul_le_mul_right e5 (by positivity)
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hab : 0 ≤ dist a b := dist_nonneg
  let p : ℝ := min 1 (ε / (2 * dist a b + 1))
  have hp : 0 < p := lt_min one_pos (by positivity)
  refine (key p hp (min_le_left _ _)).trans ?_
  have : p * (2 * dist a b + 1) ≤ ε := by
    have := min_le_right (1 : ℝ) (ε / (2 * dist a b + 1))
    calc p * (2 * dist a b + 1) ≤ ε / (2 * dist a b + 1) * (2 * dist a b + 1) := by gcongr
      _ = ε := by field_simp
  nlinarith

/-- Midpoints are unique in a spectral space. -/
theorem midpoint_unique {F X : Type*} [Field F] [MetricSpace X] (P : SpectralPlacementPrices F X) {a b m m' : X}
    (h1 : dist m a = dist a b / 2) (h2 : dist m b = dist a b / 2)
    (h1' : dist m' a = dist a b / 2) (h2' : dist m' b = dist a b / 2) : m = m' := by
  obtain ⟨Y, met, Q, ⟨f⟩, -, hg⟩ := P.exists_complete_geodesic_extension_unpointed
  have cat := Q.catZero hg
  obtain ⟨γ, -, hγ⟩ := cat (f.map a) (f.map b)
  have eq (z : X) (hz1 : dist z a = dist a b / 2) (hz2 : dist z b = dist a b / 2) : f.map z = γ (1 / 2) := by
    have h := hγ (f.map z) (1 / 2) ⟨by norm_num, by norm_num⟩
    rw [f.isometry.dist_eq, f.isometry.dist_eq, f.isometry.dist_eq, hz1, hz2] at h
    have h0 : dist (f.map z) (γ (1 / 2)) ^ 2 ≤ 0 := by
      refine h.trans (le_of_eq ?_)
      ring
    exact dist_eq_zero.mp (pow_eq_zero_iff (two_ne_zero) |>.mp (le_antisymm h0 (sq_nonneg _)))
  exact f.isometry.injective ((eq m h1 h2).trans (eq m' h1' h2').symm)

end NOF
