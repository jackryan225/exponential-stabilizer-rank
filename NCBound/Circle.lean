import Mathlib

/-!
# Unit vectors of the plane

The plane and the unit vector of a given angle.
-/

namespace NCBound

open Real

/-- The plane. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The unit vector of angle `θ`. -/
noncomputable def dir (θ : ℝ) : Plane := !₂[cos θ, sin θ]

theorem norm_dir (θ : ℝ) : ‖dir θ‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp [dir, Fin.sum_univ_two]

theorem inner_dir (θ φ : ℝ) : inner ℝ (dir θ) (dir φ) = cos (θ - φ) := by
  simp [dir, PiLp.inner_apply, Fin.sum_univ_two, cos_sub]
  ring

end NCBound
