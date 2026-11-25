# Fidelity note: exact stabilizer rank of tensor powers

Written on 25 November 2026 as the release check of this repository. It says exactly which statements the Lean
files of this folder prove, which question of the literature they answer, how they relate to the Lean target of
formal-conjectures pull request 8164, and which part is a short corollary of the OpenAI paper.

## (a) The Lean statements

All statements are in `Challenge/Statement.lean` (Mathlib and `StabilizerRank/Def.lean` only, proofs `sorry`). The proofs are
in `StabilizerRank/Final.lean`. `Check/SameStatement.lean` checks that the proved theorems have these types (definitional and
syntactic check), with `MatrixSpectralPlane` in front where the table says so.

Definition (`StabilizerRank/Def.lean`). The qubits are a finite type `Q`. A vector is a function `(Q → ZMod 2) → F`. A
stabilizer vector is a vector that we get from `c |0…0⟩` (any `c`, also `0`) by finitely many gates `H` (without `1/√2`),
`S = diag(1, i)` and `CNOT`. Over `ℂ` with `i = Complex.I` this is the usual set of stabilizer states and their multiples.
`standard_form` proves that it is the set `a [b ∈ A] i^{l(b)} (-1)^{q(b)}`. A decomposition is a sum of `J` stabilizer vectors.
Because multiples of stabilizer vectors are stabilizer vectors, the least such `J` is the usual exact stabilizer rank (least
number of terms of a linear combination of stabilizer states, Bravyi-Smith-Smolin).

| Lean name | In words | Hypothesis today | Systems | Exact or approximate |
|---|---|---|---|---|
| `stabilizer_rank_exponential` | If a vector `ψ` of finitely many qubits (complex entries) is not a stabilizer vector, there is `c > 0` such that for every `n ≥ 0` every decomposition of `ψ^{⊗n}` into stabilizer vectors has at least `2^{cn}` terms. | `MatrixSpectralPlane` | qubits only | exact |
| `tensor_power` | If `ψ` is a stabilizer vector, every tensor power of `ψ` is a stabilizer vector. | none | qubits | exact |
| `t_state` | The same bound for `ψ = |0⟩ + e^{iπ/4}|1⟩` (the T state; one qubit, so `ψ^{⊗n}` is `b ↦ e^{iπ/4·|b|}`). | `MatrixSpectralPlane` | qubits | exact |
| `t_state_field` | The same over every field `F` with `2 ≠ 0` and an element `ω` with `ω^4 = -1`; stabilizer vectors are defined with `i = ω^2`, the vector is `b ↦ ω^{|b|}`. | `MatrixSpectralPlane` (over `F`) | qubits | exact |
| `standard_form` | Stabilizer vectors are exactly the vectors `a [b ∈ A] i^{Σ l_k b_k} (-1)^{Σ q_km b_k b_m}` (`A` an affine subspace over `F_2`, `l, q` natural numbers). | none | qubits | (definition check) |
| `stabilizer_rank_exponential_standard` | `stabilizer_rank_exponential` with both "stabilizer vector" occurrences written in standard form, so that the statement uses no definition of ours. | `MatrixSpectralPlane` | qubits | exact |

`MatrixSpectralPlane` is the statement of `OAI.LinearAlgebra.SpectralBooks.matrix_spectral_plane` (openai/math, commit
`3344da5`, `lean/OAI/LinearAlgebra/SpectralBooks/EveryField.lean`, line 67). I compared the two texts: same binders, same
structure `SpectralPlacementPrices F (EuclideanSpace ℝ (Fin 2))`, same convexity clause; the universe of `F` is the parameter
`u` (`Type*` in OpenAI's file). The proofs use only the existence of the prices (`obtain ⟨P, -⟩ := plane _`), not convexity.

**Without hypothesis (built 25 November 2026):** `unconditional/Solution.lean` fills `MatrixSpectralPlane` with OpenAI's
theorem `matrix_spectral_plane` (`Solution.plane`) and states all six theorems without hypothesis (`Solution.*`);
`unconditional/FCBridgeU.lean` proves the formal-conjectures statement of part (c) without hypothesis
(`FCBridgeU.superpolynomial_stabilizer_rank`). This folder with the 7,283-file import closure of
`EveryField.lean` built (`lake build Unconditional`, 16,410 jobs, exit 0; the README says how the two build stages ran); `unconditional/SameStatementU.lean` printed "the
statements are equal as terms, and the hypothesis is the statement of matrix_spectral_plane"; `#print axioms` gave
`propext, Classical.choice, Quot.sound` for all 9 results of `unconditional/AxiomsU.lean`; `leanchecker` replayed our 27
modules with exit 0 (not the OpenAI modules). Logs in `logs/`, results in the README table.
**Conditional form (default build, no plane closure needed):** `StabilizerRank/Final.lean` proves the four rank bounds with
the hypothesis `MatrixSpectralPlane`; `tensor_power`, `standard_form` and `FCBridge.bridge` (an implication) need none.

**Not in Lean.**
- Systems with more than two levels: nothing. An extension to every prime dimension exists as an unformalized draft and is
  not part of this release.
- The paper `paper/stabilizer-rank.tex` (qubits only) is an informal account. Its Lemmas 2.1 to 2.3 are not formalized in
  that form; the Lean proof takes another route there. The claim of this repository rests on the Lean check, not on the
  paper. Reads of the paper: Gemini 4 Neon gave a blind proof of Lemma 2.3 by another route (checked line by line by
  Claude). GPT-6.2 Astra read an earlier, longer version line by line as a hostile referee, with the source of the OpenAI
  paper at hand (25 November 2026). It found no error and no statement that proves too much. It found one gap: Step 0 of
  the proof of Lemma 3.1 said without proof that two functions are in a set (a limit of roots keeps the cover
  inequality). The paper now writes that step out along the lines Astra gave, and its Step 2 says how the same argument
  applies to `q_C`. Two Claude agents checked the new text one after the other; no other model has read it. Astra also
  found that Remark 4 said "one qubit" where the short argument covers the T state; the remark now says "the state T".
- `CCZ`: no checked top-level statement. Over `ℂ` it is an instance of `stabilizer_rank_exponential` once one proves that
  the CCZ vector is not a stabilizer vector; that step is not in Lean. `StabilizerRank/Main.lean` has an internal lemma
  `ccz_state` (compiled with the rest; axioms not printed; no separate statement file): over every field with `2 ≠ 0`, for
  every `ι` with `ι^4 = 1`, given planar prices over that field, there are `c > 0` and `n₀` such that for `n ≥ n₀` the
  function `(-1)^{Σ x_i y_i z_i}` is not a linear combination of fewer than `2^{cn}` functions `[x ∈ A] ι^{l(x)} (-1)^{q(x)}`.
  An early draft of the paper (remark "Machine check") said that CCZ over every field is proved in Lean; the paper now
  states exactly the above.
- `and_nonaffine` (`StabilizerRank/Main.lean`): a second internal lemma of the same kind and with the same status (compiled
  with the rest; axioms not printed; no separate statement file). Over every field with `2 ≠ 0`, for every `ι` with
  `ι^4 = 1`, given planar prices over that field: if a set `S` of strings of `m` bits contains `x, y, z` and does not
  contain `x + y + z`, then for large `n` the indicator of `S^n` is not a linear combination of fewer than `2^{cn}`
  functions `[b ∈ A] ι^{l(b)} (-1)^{q(b)}`. Over `ℂ` this is a case of `stabilizer_rank_exponential_standard`.
- Approximate stabilizer rank, stabilizer extent, stabilizer fidelity: nothing.
- The constant: `c` is not computed and not effective.

## (b) The open question in the literature

**Bravyi, Smith, Smolin**, "Trading classical and quantum computational resources", Phys. Rev. X 6, 021043 (2016),
arXiv:1506.01396, discussion after Theorem 4 (pages 4 and 5 of the arXiv version). `χ_n` is the stabilizer rank of
`|H^{⊗n}⟩`; `|H⟩` is Clifford-equivalent to `|T⟩`, so `χ_n = χ(|T⟩^{⊗n})`. They pose Conjecture 1 (for a single-qubit state
`φ`: `χ(φ^{⊗n}) = 1` if `φ` is a stabilizer state, `= χ_n` if `φ` is a magic state, `> χ_n` otherwise), say that
super-polynomial growth follows if universal quantum computation has no polynomial-time classical simulation, say that they
could not prove such a lower bound without assumptions, prove `χ_n = Ω(n^{1/2})` (Appendix C), and then write:
"We conjecture that in fact χn ≥ 2^{Ω(n)}."

What we prove (given the plane): exactly this exponential bound for exact rank (`t_state`), and exponential growth of
`χ(φ^{⊗n})` for every non-stabilizer `φ` of any number of qubits. We do NOT prove the optimality part of Conjecture 1
(that magic states have the smallest rank).

Later statements that call the question open (all read in the source on 25 November 2026):
- **Bravyi, Browne, Calpin, Campbell, Gosset, Howard**, "Simulation of quantum circuits by low-rank stabilizer
  decompositions", Quantum 3, 181 (2019), arXiv:1808.00128. Section 1: they have no technique for unconditional
  super-polynomial lower bounds. End of Section 3 (open questions): exponential lower bounds on the stabilizer rank of `n`-qubit
  magic states are "of great interest". Section 5.4: no technique gives lower bounds exponential in the number of copies.
- **Peleg, Shpilka, Volk**, "Lower bounds on stabilizer rank", Quantum 6, 652 (2022), arXiv:2106.03214v2. Section 1.1:
  super-polynomial lower bounds for `|H^{⊗n}⟩` are called "a challenging open problem". Section 1.5: they cannot prove
  super-polynomial or even super-linear bounds. Section 1.3: a super-linear bound would answer an open question of R. Williams
  (a Boolean function in P that needs super-linearly many quadratic phases), through `T_n = Σ_{j<8} b_j [|x| ≡ j mod 8]`.
- **Quantum open problems list**, record `op_37f7b003ec78a028` (github.com/Naixu-Guo/quantum-open-problems,
  `database/problems_json/op_37f7b003ec78a028.json`, revision 2, repository pushed 23 November 2026): "Asymptotic growth of the
  stabilizer rank of T-state tensor powers", status **Unsolved**. It asks whether `χ(|T⟩^{⊗n})` is polynomially bounded, and,
  as a sharper sub-question, whether `γ = lim (1/n) log2 χ(|T⟩^{⊗n})` is strictly positive. Its comment: the exact-rank problem
  has neither a polynomial upper bound nor a super-polynomial lower bound. `t_state` gives `γ ≥ c > 0`.
- Also: Wei, Wu, Liu, Liu, arXiv:2610.02172 (1 October 2026; they prove the Gaussian analogue and call the stabilizer rank
  problem longstanding; their methods "do not extend directly to stabilizer rank"); Reardon-Smith, arXiv:2610.03699
  (2 October 2026; best stabilizer lower bounds quadratic); Tulsyan, hexagon:2611.00090 (4 November 2026; open-problem list
  item 24, `χ(|T⟩^{⊗t}) = 2^{Ω(t)}`, status open); unitaryfoundation/stabrank pull request 200 (16 November 2026: asymptotic
  exponents open); formal-conjectures issue 8163 and pull request 8164 (21 November 2026, category "research open").

## (c) The formal-conjectures target

google-deepmind/formal-conjectures pull request 8164 (opened 21 November 2026, head `b586a02`, OPEN, not
merged, two approving reviews), file `FormalConjectures/Arxiv/2106.03214/StabilizerRank.lean`:

```lean
@[category research open, question, AMS 15 81]
theorem superpolynomial_stabilizer_rank :
    ∀ d C : ℕ, ∃ N : ℕ, ∀ n ≥ N, ∀ r : ℕ,
      HasStabilizerDecomposition r (magicState n) → C * n ^ d < r := by
  sorry
```

with (same file)

```lean
noncomputable def stabilizerFunction {n : ℕ} (U : Submodule (ZMod 2) (BitVector n))
    (t l : BitVector n) (q : Matrix (Fin n) (Fin n) (ZMod 2)) (x : BitVector n) : ℂ :=
  if x - t ∈ U then
    Complex.I ^ (linearValue l x).val * (-1) ^ (quadraticValue q x).val
  else 0
def HasStabilizerDecomposition {n : ℕ} (r : ℕ) (f : BitVector n → ℂ) : Prop :=
  ∃ (c : Fin r → ℂ) (s : Fin r → BitVector n → ℂ),
    (∀ j, IsStabilizerFunction (s j)) ∧ ∀ x, f x = ∑ j, c j * s j x
noncomputable def magicState (n : ℕ) (x : BitVector n) : ℂ := magicPhase ^ weight x   -- magicPhase = exp(π i / 4)
```

(`linearValue l x = Σ l_i x_i` and `quadraticValue q x = Σ q_ij x_i x_j` are computed in `ZMod 2`.)

**Does our theorem imply it as written? YES**, without hypothesis: `FCBridgeU.superpolynomial_stabilizer_rank` (built
25 November 2026).
Comparison:
- *Vector:* `magicState n x = exp(πi/4)^{|x|}`; `t_state` uses `exp(i·π/4)^{Σ (b k).val}`. Same function.
- *Stabilizer states:* theirs are `[x - t ∈ U] · i^{(l·x mod 2)} · (-1)^{q(x) mod 2}` (support never empty; coefficients
  separate). Ours (`standard_form`) are `a [x ∈ A] i^{Σ l_k x_k} (-1)^{Σ q_km x_k x_m}` with the exponent of `i` an integer.
  The only difference is "mod 2" in the exponent of `i`. It is harmless: for `s = Σ_k a_k` with `a_k = l_k x_k ∈ {0,1}`,
  `i^{s mod 2} = i^s · (-1)^{s(s-1)/2}` and `s(s-1)/2 = Σ_{k<m} a_k a_m` is a quadratic form. So every function of theirs is
  one of ours with `q'_km = q_km + [k < m] l_k l_m` (and every nonzero one of ours is a multiple of one of theirs).
- *Rank:* both count terms of an exact decomposition with complex coefficients; theirs bounds every `r` that admits a
  decomposition, ours bounds every `J`. Same notion.
- *Quantifiers:* ours gives `c > 0` with `2^{cn} ≤ J` for ALL `n`; theirs asks, for every polynomial `C n^d`, for some `N`
  with `C n^d < r` for `n ≥ N`. Exponential beats every polynomial.

**The bridge is written and compiled:** `Check/FCBridge.lean` (Mathlib and `StabilizerRank/Def.lean` only). It copies the PR
definitions word for word (checked by a text comparison of all nine definitions and the statement) and proves

```lean
theorem FCBridge.bridge (hT : TState) (hS : StandardForm) : SuperpolynomialStabilizerRank
```

where `TState` and `StandardForm` are the statements of `Challenge.t_state` and `Challenge.standard_form` (text comparison:
identical) and `SuperpolynomialStabilizerRank` is the PR statement. `lake env lean Check/FCBridge.lean`: no error, axioms
`propext, Classical.choice, Quot.sound` (25 November 2026, about 08:00Z; 3 s; sha256 of the file `f8f79fa3…`). Its proof, in
short (the file has about 60 lines of proof):

```lean
-- phase_eq: I^(l·x mod 2) * (-1)^(q(x) mod 2) = I^(Σ l_k x_k) * (-1)^(Σ_k Σ_m (q_km + [k<m] l_k l_m) x_k x_m)
--   (from 2P + s = s*s with P = Σ_{k<m} a_k a_m, s = Σ a_k, and s*s ≡ s mod 2 (mod 4))
-- eventually_lt_two_rpow: c > 0 → ∀ d C, ∃ N, ∀ n ≥ N, C * n^d < 2^(c n)   (tendsto_pow_const_div_const_pow_of_one_lt)
theorem bridge (hT : TState) (hS : StandardForm) : SuperpolynomialStabilizerRank := by
  obtain ⟨c, hc, hbound⟩ := hT
  intro d C
  obtain ⟨N, hN⟩ := eventually_lt_two_rpow hc d C
  refine ⟨N, fun n hn r ⟨coef, s, hs, hsum⟩ => ?_⟩
  choose U t l q hfun using hs
  have hstab : ∀ j, IsStabilizer Complex.I (fun x => coef j * s j x) := fun j =>
    (hS _).mpr ⟨coef j, AffineSubspace.mk' (t j) (U j), fun k => (l j k).val,
      fun k m => (q j k m).val + if k < m then (l j k).val * (l j m).val else 0, ... phase_eq ...⟩
  have hJ := hbound n r (fun j x => coef j * s j x) hstab (fun b => by rw [← hsum b, ...])
  exact_mod_cast (hN n hn).trans_le hJ
```

With the proved theorems: `bridge (StabilizerRank.Final.t_state plane) StabilizerRank.Final.standard_form` proves the PR
statement from `MatrixSpectralPlane.{0}`; `bridge Solution.t_state StabilizerRank.Final.standard_form` proves it with no
hypothesis. The second composition is `FCBridgeU.superpolynomial_stabilizer_rank` in `unconditional/FCBridgeU.lean`; it was
built on 25 November 2026, axioms `propext, Classical.choice, Quot.sound` (`logs/p5r-6-axiomsu.txt`).
Status of the target: nobody has claimed or closed it (gh search of issues and pull requests, 25 November 2026, about 07:45Z
and again 08:28Z: pull request 8164 open, head `b586a02`, no comments; only #8163 and #8164 mention stabilizer rank).

## (c2) Independent reads of the statements, 25 November 2026

- **GPT-6.2 Astra (OpenAI), blind read.** It received the claim in words and the Lean files (`StabilizerRank/Def.lean`,
  `Challenge/Statement.lean`, `StabilizerRank/Final.lean`, `unconditional/Solution.lean`, the two statement checks,
  `Check/FCBridge.lean`, `unconditional/FCBridgeU.lean`, the axiom outputs). It did not receive the README, this note or the
  paper. It answered seven questions. First line of its answer: "FIDELITY OK". In short: the inductive definition gives
  exactly the complex multiples of stabilizer states (it checked the Hadamard, phase and CNOT rules bit by bit); the main
  statement has the quantifiers of the claim, holds for `n = 0` with equality possible, and its hypothesis can be met; the
  T statement uses `exp(iπ/4)^{|b|}`; the standard form is the usual one; `MatrixSpectralPlane` is the statement of OpenAI's
  theorem and the theorems of `unconditional/` have no other assumption; the formal-conjectures statement is proved.
  Its weakest point: it had no network, so it could not compare the copied definitions with the file of the pull request.
- **That comparison, made afterwards.** The file `FormalConjectures/Arxiv/2106.03214/StabilizerRank.lean` at the head commit
  `b586a02bfe12389907c12cfd03121b8430e28dff` of pull request 8164 (git blob `5c7d01389c24573d7f99d5498006dd4166618247`,
  210 lines) was fetched through the GitHub API. `diff` of its lines 40 to 75 against lines 26 to 60 of `Check/FCBridge.lean`:
  one sentence of a comment differs, nothing else. The statement of `superpolynomial_stabilizer_rank` is the same text as
  `SuperpolynomialStabilizerRank`. The pull request was open and not merged at that time. The copy was not compiled inside
  the formal-conjectures repository (that file starts with `module` and `public import FormalConjecturesUtil`).
- **Gemini 4 Neon (Google), second read.** It received the first lines of the README and the complete text of the statement
  files and of the bridge definitions, and eight questions. First line of its answer: "SECOND READ OK". It found no extra
  hypothesis, no wrong model, no vacuous statement and no claim beyond the Lean statements. It checked the gate rules, the
  cases `n = 0`, `J = 0`, `Q` empty and `ψ = 0`, the identity `i^{s mod 2} = i^s (-1)^{s(s-1)/2}`, and why the bridge needs
  only one inclusion of the two families. It looked for a short decomposition over a finite field (for example 9 or 17
  elements) and found none. It asked for clearer words in five places of the README (what a stabilizer vector is; that `c`
  depends on `ψ`; "gives a proof" for the part on paper; the parts of the models; the sentence on OpenAI's review). Those
  five places were changed.

## (d) What is a corollary of the OpenAI paper and what is ours

**Short corollary of OpenAI's paper** ("Euclidean geometry in the asymptotic spectrum of tensors", 24 November 2026): the
single-qubit T case. The price of a stabilizer state of `3h` qubits split into three blocks of `h` qubits is at most `3h/2` (GHZ/EPR normal form of
tripartite stabilizer states, Bravyi-Fattal-Gottesman 2006); the theorem "Exact extension" (2) of the paper, on a triangle
with two side midpoints, gives a table above that value; Clifford+T universality gives Zariski density. An expert of the paper
gets this in a few lines. Our paper says so (Remark 4; the point came from our internal review). The OpenAI texts do not state
it: I searched the paper source, all OpenAI paper sources (local copies), `CONTENTS.md`, `overview.tex`, the
docs and the Lean library at `3344da5` (= the latest commit of openai/math, 25 November 00:18Z) for stabilizer rank,
stabilizer state, magic state, Bravyi, Clifford gate or group: no hit.

**Ours:**
1. The dichotomy for EVERY vector of finitely many qubits (Lean, given the plane): reduction of a non-stabilizer vector of
   many qubits to a one-qubit vector `(1, a)`, `a ≠ 0`, `a^4 ≠ 1`, by stabilizer operations (4 points of a plane, 8 points of
   a cube); the Hadamard trick for roots of unity; Zariski density of products of the resulting gates (independence of
   characters). The Lean proof does not use Bravyi-Fattal-Gottesman or gate injection: `StabilizerRank/Lift.lean` bounds the
   price of a stabilizer vector by a direct subspace decomposition.
2. The machine check: 23 files of ours on top of 867 unchanged OpenAI files, Mathlib-only statements, a standard-form
   statement without our definitions, and the bridge to the formal-conjectures target.

Nothing else is claimed. The paper is an informal account of item 1.

## Novelty search (part 2 of the release check), 25 November 2026, 07:40Z to 08:15Z

No earlier or concurrent unconditional super-polynomial lower bound on the exact stabilizer rank of `ψ^{⊗n}` was found.
Places: hexagonmath.org (site search for 14 terms, and FULL TEXT of 1,550 of the 1,560 works, all except 10 works of
unrelated subjects; only hit hexagon:2611.00090, which lists the question as open); nilradical.ai (group theory only);
formal-conjectures (issues and pull requests; only #8163/#8164, open); Semantic Scholar citations of BSS 2016 (467) and
PSV 2022 (21), titles and abstracts; arXiv search (quoted phrases "stabilizer rank", "stabiliser rank", "stabilizer extent",
"Clifford rank", "magic state" + "exponential lower bound", sorted by date, all fields; read 2610.02172, 2610.03699,
2610.17500, 2611.06119, 2610.35579); vibemathed.com (live dataset, 1,355 entries: none); Zenodo through DataCite (36 records
for "stabilizer rank": small-copy certificates and Pei, Zenodo 24023348, 6 November 2026, CONDITIONAL on the hardness of
syndrome decoding); GitHub (cslib-frontier: only a 2-term Clifford decomposition of the T gate; code search for the target
name: only the PR; issues and pull requests since 15 November); Palomar registry (quant-ph and cs.CC indexes: none);
MathOverflow, Quantum Computing and CS Theory Stack Exchange (nothing after 2024); openai/math (part (d)). Two earlier searches
of ours agree. Not covered: Google Scholar, full text of all
arXiv quant-ph papers of October and November 2026 (only titles, abstracts and citation lists).

**Second search, 25 November 2026, 10:52Z to 10:58Z** (GPT-6.2 Sol, web search; queries and sources recorded): verdict NOT
FOUND. No public proof or claim of an unconditional exponential lower bound on the exact stabilizer rank of `T^{⊗n}`, of
`ψ^{⊗n}` for a fixed non-stabilizer vector of several qubits. OpenAI's paper and Lean
release do not state the corollary. Formal-conjectures issue 8163 and pull request 8164 are open (head `b586a02`, the copied
version; two approvals check the formulation, no proof). The quantum open problems record `op_37f7b003ec78a028` says
Unsolved. Added references: Labib (arXiv:2107.10551, order `n` for a qudit magic state, in each prime dimension) and Theorem 1.6 of
Mehraban and Tahmasbi (super-polynomial exact rank of `T^{⊗m}` unless the permanent has polynomial-size circuits; a
conditional bound). Not reached in this search: the arXiv search form and API, Semantic Scholar and Google Scholar citation
lists (the publisher citation lists were read), Zenodo records (24023348 known only through an indexed abstract).

**Third search, 25 November 2026, 11:29Z to 11:33Z** (GPT-6.2 Sol, web search; and our own queries to the GitHub API at
11:32Z). No public proof or claim of an exponential lower bound on the exact stabilizer rank of `T^{⊗n}` or of `ψ^{⊗n}` was
found, and no Lean proof of the formal-conjectures statement. The best public unconditional bound is of order `n^2 / log n`
(Sinha and Lovitz, arXiv:2610.06819; it covers exact rank and one qubit). Read for this search: the arXiv listings of
quant-ph, cs.CC, math.AG and math.CO for 23 to 25 November 2026; the public pages that discuss the OpenAI paper; openai/math
(head still `3344da5`, no open issue, no later commit); formal-conjectures issue 8163 and pull request 8164 (both open, head
`b586a02`); GitHub issues, pull requests and repositories with "stabilizer rank" since 20 November; hexagonmath.org
(catalogue of 24 and 25 November, full text of the two hits); the Palomar registry, nilradical.ai and proofatlas.ai (no
entry). Not reached: the Zenodo record 24023348 in full text (a conditional bound, known through an indexed abstract),
vibemathed.com (time-out in this search; its data set was read at 06:52Z), complete cited-by lists.
