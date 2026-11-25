import Challenge.Statement
import Solution

/-! Compares the statements in `Challenge/Statement.lean` with the theorems in `unconditional/Solution.lean`, and the
hypothesis `MatrixSpectralPlane` with the statement of `OAI.LinearAlgebra.SpectralBooks.matrix_spectral_plane`. -/

universe u

example : type_of% @Challenge.stabilizer_rank_exponential = type_of% @Solution.stabilizer_rank_exponential := by
  with_reducible rfl
example : type_of% @Challenge.tensor_power = type_of% @Solution.tensor_power := by with_reducible rfl
example : type_of% @Challenge.t_state = type_of% @Solution.t_state := by with_reducible rfl
example : type_of% @Challenge.t_state_field.{u} = type_of% @Solution.t_state_field.{u} := by with_reducible rfl
example : type_of% @Challenge.standard_form = type_of% @Solution.standard_form := by with_reducible rfl
example : type_of% @Challenge.stabilizer_rank_exponential_standard =
    type_of% @Solution.stabilizer_rank_exponential_standard := by with_reducible rfl

open Lean in
run_meta do
  let env ← getEnv
  let get (n : Name) : MetaM ConstantInfo := do
    let some c := env.find? n | throwError "{n} not found"
    pure c
  for s in [`stabilizer_rank_exponential, `tensor_power, `t_state, `t_state_field, `standard_form,
      `stabilizer_rank_exponential_standard] do
    let a ← get (`Challenge ++ s)
    let b ← get (`Solution ++ s)
    unless a.levelParams == b.levelParams && a.type == b.type do throwError "{s}: the two statements differ"
  -- the hypothesis: the body of the definition and the type of the theorem of OpenAI, with the same universe name
  let d ← get ``StabilizerRank.Final.MatrixSpectralPlane
  let t ← get ``OAI.LinearAlgebra.SpectralBooks.matrix_spectral_plane
  let [ud] := d.levelParams | throwError "universe"
  let [ut] := t.levelParams | throwError "universe"
  let some v := d.value? | throwError "no value"
  unless v == t.type.instantiateLevelParams [ut] [.param ud] do throwError "the hypothesis is not the theorem of OpenAI"
  logInfo "the statements are equal as terms, and the hypothesis is the statement of matrix_spectral_plane"
