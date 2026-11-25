import Challenge.Statement
import StabilizerRank.Final

/-! Compares the statements in `Challenge/Statement.lean` (Mathlib only, with `StabilizerRank/Def.lean`) with the proved
theorems. Three of them have one more hypothesis in front: `MatrixSpectralPlane`, the statement of the theorem
`OAI.LinearAlgebra.SpectralBooks.matrix_spectral_plane` of the OpenAI library. Both the definitional check and the syntactic
check must pass. The second one runs a few lines of Lean code. -/

open StabilizerRank.Final

universe u

example : (MatrixSpectralPlane.{0} → type_of% @Challenge.stabilizer_rank_exponential) =
    type_of% @StabilizerRank.Final.stabilizer_rank_exponential := by with_reducible rfl
example : (MatrixSpectralPlane.{0} → type_of% @Challenge.t_state) = type_of% @StabilizerRank.Final.t_state := by
  with_reducible rfl
example : (MatrixSpectralPlane.{u} → type_of% @Challenge.t_state_field.{u}) =
    type_of% @StabilizerRank.Final.t_state_field.{u} := by with_reducible rfl
example : (MatrixSpectralPlane.{0} → type_of% @Challenge.stabilizer_rank_exponential_standard) =
    type_of% @StabilizerRank.Final.stabilizer_rank_exponential_standard := by with_reducible rfl
example : type_of% @Challenge.tensor_power = type_of% @StabilizerRank.Final.tensor_power := by with_reducible rfl
example : type_of% @Challenge.standard_form = type_of% @StabilizerRank.Final.standard_form := by with_reducible rfl

open Lean in
run_meta do
  let env ← getEnv
  let get (n : Name) : MetaM ConstantInfo := do
    let some c := env.find? n | throwError "{n} not found"
    pure c
  -- statements with the hypothesis in front
  for s in [`stabilizer_rank_exponential, `t_state, `t_state_field, `stabilizer_rank_exponential_standard] do
    let a ← get (`Challenge ++ s)
    let b ← get (`StabilizerRank.Final ++ s)
    let .forallE _ h body _ := b.type | throwError "{s}: no hypothesis"
    unless h.isAppOf ``StabilizerRank.Final.MatrixSpectralPlane do throwError "{s}: other hypothesis"
    unless a.levelParams == b.levelParams && a.type == body do throwError "{s}: the two statements differ"
  -- statements without hypothesis
  for s in [`tensor_power, `standard_form] do
    let a ← get (`Challenge ++ s)
    let b ← get (`StabilizerRank.Final ++ s)
    unless a.levelParams == b.levelParams && a.type == b.type do throwError "{s}: the two statements differ"
  logInfo "the statements are equal as terms"
