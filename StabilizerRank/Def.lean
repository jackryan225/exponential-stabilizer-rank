import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Logic.Function.Basic

/-!
# Stabilizer vectors: definition (Mathlib only)

The qubits are indexed by a finite set `Q` (for example `Fin n`, or `Fin n × Fin m` for `n` blocks of `m` qubits). A vector of
these qubits with entries in a field `F` is a function `(Q → ZMod 2) → F`: the amplitude at every string of bits. `i` is a
square root of `-1`.
-/

namespace StabilizerRank

/-- The stabilizer vectors: the multiples of `|0…0⟩`, and everything that is obtained from them by the gates `H` (Hadamard,
without the factor `1/√2`), `S = diag(1, i)` and `CNOT` on some of the qubits. -/
inductive IsStabilizer {F : Type*} [Field F] (i : F) {Q : Type} [Fintype Q] [DecidableEq Q] : ((Q → ZMod 2) → F) → Prop
  | zeros (c : F) : IsStabilizer i (fun b => if b = 0 then c else 0)
  | hadamard (k : Q) (ψ : (Q → ZMod 2) → F) : IsStabilizer i ψ →
      IsStabilizer i (fun b => ψ (Function.update b k 0) + (-1) ^ (b k).val * ψ (Function.update b k 1))
  | phase (k : Q) (ψ : (Q → ZMod 2) → F) : IsStabilizer i ψ → IsStabilizer i (fun b => i ^ (b k).val * ψ b)
  | cnot (k l : Q) (h : k ≠ l) (ψ : (Q → ZMod 2) → F) : IsStabilizer i ψ →
      IsStabilizer i (fun b => ψ (Function.update b l (b l + b k)))

end StabilizerRank
