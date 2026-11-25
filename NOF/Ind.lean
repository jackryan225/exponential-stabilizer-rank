import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic

/-!
# Indicators
-/

namespace NOF

variable {F : Type*} [Field F]

open Classical in
/-- The indicator of a proposition. -/
noncomputable def ind (K : Type*) [Zero K] [One K] (p : Prop) : K := if p then 1 else 0

theorem ind_true {p : Prop} (h : p) : ind F p = 1 := ite_eq_left h

theorem ind_false {p : Prop} (h : ¬ p) : ind F p = 0 := ite_eq_right h

theorem ind_congr {p q : Prop} (h : p ↔ q) : ind F p = ind F q := by rw [propext h]

theorem ind_mul (p q : Prop) : ind F p * ind F q = ind F (p ∧ q) := by
  by_cases hp : p <;> by_cases hq : q
  · rw [ind_true hp, ind_true hq, ind_true ⟨hp, hq⟩, one_mul]
  · rw [ind_false hq, ind_false (p := p ∧ q) (fun h => hq h.2), mul_zero]
  · rw [ind_false hp, ind_false (p := p ∧ q) (fun h => hp h.1), zero_mul]
  · rw [ind_false hp, ind_false (p := p ∧ q) (fun h => hp h.1), zero_mul]

theorem ind_eq_ite (p : Prop) [Decidable p] : ind F p = if p then 1 else 0 := by
  unfold ind
  congr

end NOF
