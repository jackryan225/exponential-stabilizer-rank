import NOF.Extend

/-!
# A table whose lift is more expensive than the matrix product

Five parties: the vertices of an equilateral triangle and the midpoints of two sides.
-/

namespace NOF

open Real OAI OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor OAI.Hierarchy
open scoped NNReal

/-- The five old parties. -/
inductive Old
  | o1 | o2 | o3 | m2 | m3
  deriving DecidableEq

instance : Fintype Old := ⟨{.o1, .o2, .o3, .m2, .m3}, fun x => by cases x <;> decide⟩

theorem prod_old {M : Type*} [CommMonoid M] (f : Old → M) : ∏ i, f i = f .o1 * (f .o2 * (f .o3 * (f .m2 * f .m3))) := by
  have huniv : (Finset.univ : Finset Old) = {.o1, .o2, .o3, .m2, .m3} := rfl
  rw [huniv, Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_singleton]

instance : Nontrivial Old := ⟨⟨.o1, .o2, by decide⟩⟩

/-- The indices of the parties: `o1` holds `(x, y)`, `o2` holds `(y, z)`, `o3` holds `(z, x)`. -/
abbrev OLeg (X Y Z : Type) : Old → Type
  | .o1 => X × Y
  | .o2 => Y × Z
  | .o3 => Z × X
  | .m2 => PUnit
  | .m3 => PUnit

instance (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] : ∀ i, Fintype (OLeg X Y Z i)
  | .o1 => inferInstanceAs (Fintype (X × Y))
  | .o2 => inferInstanceAs (Fintype (Y × Z))
  | .o3 => inferInstanceAs (Fintype (Z × X))
  | .m2 => inferInstanceAs (Fintype PUnit)
  | .m3 => inferInstanceAs (Fintype PUnit)

section

variable {K : Type*} [Field K] {X Y Z X' Y' Z' : Type} [Fintype X] [Fintype Y] [Fintype Z] [Fintype X'] [Fintype Y']
  [Fintype Z']

/-- The three shared labels agree. -/
def Agree (a : ∀ i, OLeg X Y Z i) : Prop :=
  (a .o1).1 = (a .o3).2 ∧ (a .o1).2 = (a .o2).1 ∧ (a .o2).2 = (a .o3).1

/-- The lift of a table to the three parties. -/
noncomputable def hat (T : X → Y → Z → K) : Raw.{0} Old K where
  Leg := OLeg X Y Z
  finiteLeg := inferInstance
  coeff a := ind K (Agree a) * T (a .o1).1 (a .o1).2 (a .o2).2

/-- The indices with the new party, who holds all three labels. -/
abbrev NLeg (X Y Z : Type) : Option Old → Type
  | none => X × Y × Z
  | some i => OLeg X Y Z i

instance (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] : ∀ i, Fintype (NLeg X Y Z i)
  | none => inferInstanceAs (Fintype (X × Y × Z))
  | some i => inferInstanceAs (Fintype (OLeg X Y Z i))

/-- The three shared labels agree, also with the new party. -/
def Agree' (b : ∀ i, NLeg X Y Z i) : Prop :=
  ((b (some .o1)).1 = (b (some .o3)).2 ∧ (b (some .o1)).2 = (b (some .o2)).1 ∧ (b (some .o2)).2 = (b (some .o3)).1) ∧
    b none = ((b (some .o1)).1, (b (some .o1)).2, (b (some .o2)).2)

/-- Three labels, each shared by two of the old parties and the new party. -/
noncomputable def shared (K : Type*) [Field K] (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] :
    Raw.{0} (Option Old) K where
  Leg := NLeg X Y Z
  finiteLeg := inferInstance
  coeff b := ind K (Agree' b)

/-- The contraction of the shared labels with a functional of the new party is the lift of a table. -/
theorem contract_restricts (ξ : (shared K X Y Z).Leg none → K) :
    ((shared K X Y Z).contractNew ξ).Restricts (hat fun x y z => ξ (x, y, z)) := by
  classical
  refine restricts_of_read (T := hat fun x y z => ξ (x, y, z)) (fun i a => a) fun a => ?_
  have e : ∀ a : ∀ i, OLeg X Y Z i, (∑ b : X × Y × Z, ξ b * ind K (Agree a ∧ b = ((a .o1).1, (a .o1).2, (a .o2).2))) =
      ind K (Agree a) * ξ ((a .o1).1, (a .o1).2, (a .o2).2) := by
    intro a
    rw [Finset.sum_eq_single ((a .o1).1, (a .o1).2, (a .o2).2)]
    · by_cases h : Agree a
      · rw [ind_true ⟨h, rfl⟩, ind_true h, mul_one, one_mul]
      · rw [ind_false (fun h' => h h'.1), ind_false h, mul_zero, zero_mul]
    · intro b _ hb
      rw [ind_false (fun h' => hb h'.2), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  exact e a

/-- Products of shared labels. -/
theorem shared_mul_restricts : ((shared K X Y Z).mul (shared K X' Y' Z')).Restricts
    (shared K (X × X') (Y × Y') (Z × Z')) := by
  classical
  let read : ∀ i, NLeg X Y Z i × NLeg X' Y' Z' i → NLeg (X × X') (Y × Y') (Z × Z') i := fun i =>
    match i with
    | none => fun p => ((p.1.1, p.2.1), (p.1.2.1, p.2.2.1), (p.1.2.2, p.2.2.2))
    | some .o1 => fun p => ((p.1.1, p.2.1), (p.1.2, p.2.2))
    | some .o2 => fun p => ((p.1.1, p.2.1), (p.1.2, p.2.2))
    | some .o3 => fun p => ((p.1.1, p.2.1), (p.1.2, p.2.2))
    | some .m2 => fun _ => PUnit.unit
    | some .m3 => fun _ => PUnit.unit
  refine restricts_of_read (S := (shared K X Y Z).mul (shared K X' Y' Z'))
    (T := shared K (X × X') (Y × Y') (Z × Z')) read fun a => ?_
  have e : ∀ a : ∀ i, NLeg X Y Z i × NLeg X' Y' Z' i,
      ind K (Agree' fun i => (a i).1) * ind K (Agree' fun i => (a i).2) = ind K (Agree' fun i => read i (a i)) := by
    intro a
    rw [ind_mul]
    apply ind_congr
    simp only [Agree', read, Prod.ext_iff]
    tauto
  exact e a

theorem one_restricts_shared : (Raw.one (Option Old) K).Restricts (shared K PUnit PUnit PUnit) := by
  classical
  let read : ∀ i : Option Old, PUnit → NLeg PUnit PUnit PUnit i := fun i =>
    match i with
    | none => fun _ => (PUnit.unit, PUnit.unit, PUnit.unit)
    | some .o1 => fun _ => (PUnit.unit, PUnit.unit)
    | some .o2 => fun _ => (PUnit.unit, PUnit.unit)
    | some .o3 => fun _ => (PUnit.unit, PUnit.unit)
    | some .m2 => fun _ => PUnit.unit
    | some .m3 => fun _ => PUnit.unit
  refine restricts_of_read (S := Raw.one (Option Old) K) (T := shared K PUnit PUnit PUnit) read fun a => ?_
  have e : (1 : K) = ind K (Agree' (X := PUnit) (Y := PUnit) (Z := PUnit) fun i => read i PUnit.unit) := by
    rw [ind_true]
    exact ⟨⟨rfl, rfl, rfl⟩, rfl⟩
  exact e

theorem shared_ne_zero [Nonempty X] [Nonempty Y] [Nonempty Z] : (shared K X Y Z).coeff ≠ 0 := by
  classical
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨y⟩ := ‹Nonempty Y›
  obtain ⟨z⟩ := ‹Nonempty Z›
  let b : ∀ i, NLeg X Y Z i := fun i =>
    match i with
    | none => (x, y, z)
    | some .o1 => (x, y)
    | some .o2 => (y, z)
    | some .o3 => (z, x)
    | some .m2 => PUnit.unit
    | some .m3 => PUnit.unit
  intro h
  have h0 : (shared K X Y Z).coeff b = 0 := congrFun h b
  have h1 : (shared K X Y Z).coeff b = 1 := ind_true ⟨⟨rfl, rfl, rfl⟩, rfl⟩
  rw [h1] at h0
  exact one_ne_zero h0

end

/-- Strings of `m` bits. -/
def Bits : ℕ → Type
  | 0 => PUnit
  | m + 1 => Bits m × Fin 2

instance : ∀ m, Fintype (Bits m)
  | 0 => inferInstanceAs (Fintype PUnit)
  | m + 1 =>
    let _ : Fintype (Bits m) := instFintypeBits m
    inferInstanceAs (Fintype (Bits m × Fin 2))

theorem card_bits (m : ℕ) : Fintype.card (Bits m) = 2 ^ m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change Fintype.card (Bits m × Fin 2) = _
    rw [Fintype.card_prod, ih, Fintype.card_fin, pow_succ]

/-- The powers of the shared labels are shared strings. -/
theorem shared_pow_le (K : Type*) [Field K] (m : ℕ) :
    (ofRaw (shared K (Fin 2) (Fin 2) (Fin 2))) ^ m ≤ ofRaw (shared K (Bits m) (Bits m) (Bits m)) := by
  induction m with
  | zero =>
    rw [pow_zero]
    exact one_restricts_shared
  | succ m ih =>
    rw [pow_succ]
    refine (mul_mono ih le_rfl).trans ?_
    rw [← ofRaw_mul]
    exact shared_mul_restricts

end NOF
