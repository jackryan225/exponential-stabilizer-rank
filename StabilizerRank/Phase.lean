import Mathlib.Algebra.Module.ZMod
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic

/-!
# Quadratic phases on elementary abelian two-groups
-/

namespace StabilizerRank

variable {F : Type*} [Field F] {V W : Type*} [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]

theorem add_self' (u : W) : u + u = 0 := by
  have h : (2 : ZMod 2) • u = 0 := by
    rw [show (2 : ZMod 2) = 0 from rfl, zero_smul]
  rwa [two_smul] at h

/-- The defect of multiplicativity. -/
def form (φ : W → F) (u v : W) : F := φ (u + v) * (φ u)⁻¹ * (φ v)⁻¹

/-- A quadratic phase: nonzero, normalized, and the defect is multiplicative. -/
structure IsPhase (φ : W → F) : Prop where
  ne : ∀ u, φ u ≠ 0
  zero : φ 0 = 1
  mul : ∀ u u' v, form φ (u + u') v = form φ u v * form φ u' v

namespace IsPhase

variable {φ ψ : W → F}

theorem add (h : IsPhase φ) (u v : W) : φ (u + v) = φ u * φ v * form φ u v := by
  have h1 := h.ne u
  have h2 := h.ne v
  rw [form]
  field_simp

omit [Module (ZMod 2) W] in
theorem form_comm (φ : W → F) (u v : W) : form φ u v = form φ v u := by
  rw [form, form, add_comm u v]
  ring

theorem mul_right (h : IsPhase φ) (u v v' : W) : form φ u (v + v') = form φ u v * form φ u v' := by
  rw [form_comm φ u, h.mul, form_comm φ u v, form_comm φ u v']

theorem form_zero (h : IsPhase φ) (v : W) : form φ 0 v = 1 := by
  rw [form, zero_add, h.zero, inv_one, mul_one, mul_inv_cancel₀ (h.ne v)]

theorem form_sq (h : IsPhase φ) (u v : W) : form φ u v * form φ u v = 1 := by
  rw [← h.mul, add_self', h.form_zero]

theorem form_eq (h : IsPhase φ) (u v : W) : form φ u v = 1 ∨ form φ u v = -1 :=
  mul_self_eq_one_iff.mp (h.form_sq u v)

theorem sq (h : IsPhase φ) (u : W) : φ u * φ u = form φ u u := by
  have h1 := h.add u u
  rw [add_self', h.zero] at h1
  have h2 := h.form_sq u u
  calc φ u * φ u = φ u * φ u * (form φ u u * form φ u u) := by rw [h2, mul_one]
    _ = (φ u * φ u * form φ u u) * form φ u u := by ring
    _ = form φ u u := by rw [← h1, one_mul]

omit [Module (ZMod 2) W] in
/-- A function with a bimultiplicative defect. -/
theorem of_add (h0 : φ 0 = 1) (hne : ∀ u, φ u ≠ 0) (B : W → W → F) (hB : ∀ u v, φ (u + v) = φ u * φ v * B u v)
    (hm : ∀ u u' v, B (u + u') v = B u v * B u' v) : IsPhase φ := by
  have e (u v : W) : form φ u v = B u v := by
    rw [form, hB]
    have h1 := hne u
    have h2 := hne v
    field_simp
  exact ⟨hne, h0, fun u u' v => by rw [e, e, e, hm]⟩

omit [Module (ZMod 2) W] in
theorem one : IsPhase (fun _ : W => (1 : F)) :=
  of_add rfl (fun _ => one_ne_zero) (fun _ _ => 1) (fun _ _ => by simp) (fun _ _ _ => by simp)

theorem mul_phase (h : IsPhase φ) (h' : IsPhase ψ) : IsPhase (fun u => φ u * ψ u) :=
  of_add (by rw [h.zero, h'.zero, mul_one]) (fun u => mul_ne_zero (h.ne u) (h'.ne u))
    (fun u v => form φ u v * form ψ u v) (fun u v => by rw [h.add, h'.add]; ring)
    (fun u u' v => by rw [h.mul, h'.mul]; ring)

theorem prod {ι : Type*} (s : Finset ι) (φ : ι → W → F) (h : ∀ i ∈ s, IsPhase (φ i)) :
    IsPhase (fun u => ∏ i ∈ s, φ i u) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using one
  | insert i s hi ih =>
    have := (h i (Finset.mem_insert_self i s)).mul_phase (ih fun j hj => h j (Finset.mem_insert_of_mem hj))
    simpa only [Finset.prod_insert hi] using this

theorem comp (h : IsPhase φ) (L : V →ₗ[ZMod 2] W) : IsPhase (fun v => φ (L v)) :=
  of_add (by rw [map_zero, h.zero]) (fun v => h.ne _) (fun u v => form φ (L u) (L v))
    (fun u v => by rw [map_add, h.add]) (fun u u' v => by rw [map_add, h.mul])

/-- The phase seen from another base point. -/
theorem shift (h : IsPhase φ) (a : W) : IsPhase (fun v => φ v * form φ a v) :=
  of_add (by rw [h.zero, form_comm, h.form_zero, mul_one])
    (fun v => mul_ne_zero (h.ne v) (fun h0 => by
      have := h.form_sq a v
      rw [h0, mul_zero] at this
      exact zero_ne_one this))
    (form φ) (fun u v => by rw [h.add, h.mul_right]; ring) h.mul

theorem shift_eq (h : IsPhase φ) (a v : W) : φ (a + v) = φ a * (φ v * form φ a v) := by
  rw [h.add]
  ring

end IsPhase

end StabilizerRank
