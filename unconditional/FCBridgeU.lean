import Solution
import Check.FCBridge

/-!
# The formal-conjectures target without hypothesis

`FCBridge.bridge` (`Check/FCBridge.lean`) proves the statement of `superpolynomial_stabilizer_rank` of
google-deepmind/formal-conjectures pull request 8164 from the statements `t_state` and `standard_form`. Here the first is
the theorem without hypothesis of `unconditional/Solution.lean`; the second has no hypothesis in `StabilizerRank/Final.lean`.
-/

namespace FCBridgeU

/-- The statement `superpolynomial_stabilizer_rank` of formal-conjectures pull request 8164 (copied word for word in
`Check/FCBridge.lean`), without hypothesis. -/
theorem superpolynomial_stabilizer_rank : FCBridge.SuperpolynomialStabilizerRank :=
  FCBridge.bridge Solution.t_state StabilizerRank.Final.standard_form

end FCBridgeU
