# Exact stabilizer rank of tensor powers, in Lean 4

**Claim.** Let `ψ` be a vector of finitely many qubits that is not a stabilizer vector. (A stabilizer vector is a complex
multiple of a stabilizer state; the zero vector counts.) Then there is a number `c > 0` such that, for every `n`, the tensor
power `ψ^{⊗n}` is not a sum of fewer than `2^{cn}` stabilizer vectors: the exact stabilizer rank of `ψ^{⊗n}` is at least
`2^{cn}`. The number `c` depends on `ψ` and is not computed. Lean 4 checks this theorem
(`Solution.stabilizer_rank_exponential`). The proof uses one theorem that we did not prove: OpenAI's spectral plane theorem
`matrix_spectral_plane`, which OpenAI proved in its own Lean library. The Lean kernel checked our files together with that
library, and the axioms are the three standard ones. For the T state the claim gives the bound `χ(T^{⊗n}) ≥ 2^{Ω(n)}` that
Bravyi, Smith and Smolin conjectured in 2016. That case is a short corollary of OpenAI's paper. The claim does not give the
other part of their Conjecture 1 (magic states have the smallest rank).

**Scope.**
- **Exact rank only.** Nothing about approximate stabilizer rank, stabilizer extent, or classical simulation in general. The
  constant `c` is not computed. Details: "What is not claimed".
- **In Lean (qubits only, exact rank only):** `stabilizer_rank_exponential` (the exact stabilizer rank of `ψ^{⊗n}` grows
  exponentially for every non-stabilizer vector `ψ` of finitely many qubits), `t_state` (the T state over the complex
  numbers), `t_state_field` (the T state over every field with `2 ≠ 0` and an element `ω` with `ω^4 = -1`),
  `stabilizer_rank_exponential_standard` (the first statement with stabilizer vectors in standard form), `tensor_power` and
  `standard_form`. The first four have the one hypothesis `MatrixSpectralPlane` (the statement of OpenAI's theorem, see "The
  deep input"); `unconditional/Solution.lean` fills it with OpenAI's theorem itself.
  `StabilizerRank/Main.lean` has two more lemmas of the same kind, over every field with `2 ≠ 0` and with the prices as a
  hypothesis: `and_nonaffine` (the conjunction of `n` copies of a set of bit strings that is not an affine subspace) and
  `ccz_state` (the function `(-1)^{x_1 y_1 z_1 + ⋯ + x_n y_n z_n}`). Over the complex numbers both are cases of the main
  statement. They compile with the rest. They have no statement file and their axioms were not printed.
- **Qubits only.** Nothing is claimed for systems with more than two levels. An extension to every prime dimension exists
  as an unformalized draft and is not part of this release.
- **The paper** `paper/stabilizer-rank.tex` is an informal account of the theorem for qubits. It is not formalized, and in
  places its route differs from the Lean proof (Lemmas 2.1 to 2.3). The claim of this repository rests on the Lean check,
  not on the paper. Gemini 4 Neon received the statement of Lemma 2.3 of the paper (from several qubits to one) with all
  definitions and no proof, and returned a complete proof by a different route; Claude checked that proof line by line and
  found no gap. GPT-6.2 Astra read an earlier, longer version of the paper line by line as a hostile referee. It found no
  error and one gap: Step 0 of the proof of the extension lemma (Lemma 3.1) said without proof that two functions are in a
  set. The paper now writes that step out along the lines that Astra gave. Claude read the paper line by line, and two
  Claude agents checked the new text one after the other. No model other than Claude has read the new text.
- **A short corollary of OpenAI's paper:** the case of the T state, that is, the 2016 question itself (see "What is a
  corollary and what is new"). Our part is the extension to every non-stabilizer vector of any number of qubits, the
  machine-checked proof, and the Lean proof of the formal-conjectures target below.
- **Bridge to the DeepMind target:** `Check/FCBridge.lean` proves the Lean statement `superpolynomial_stabilizer_rank` of
  google-deepmind/formal-conjectures pull request 8164 (definitions and statement copied unchanged, comments aside; the
  pull request is open and not merged) from
  `t_state` and `standard_form`; `unconditional/FCBridgeU.lean` applies it to the theorems without hypothesis (see "The
  formal-conjectures target").

Research driven, orchestrated and reviewed by Jack Ryan. Claude (by Anthropic), GPT-6.2 Astra (by OpenAI) and Gemini 4 Neon
(by Google) collaborated in finding and writing the proofs. Formalized in Lean 4: the six statements of `Challenge/Statement.lean`
(`stabilizer_rank_exponential`, `tensor_power`, `t_state`, `t_state_field`, `standard_form`,
`stabilizer_rank_exponential_standard`) and the formal-conjectures statement `superpolynomial_stabilizer_rank`, all without
hypothesis in `unconditional/`. The parts in detail: Claude found
and wrote the proofs and the Lean files. Gemini 4 Neon wrote a second proof of Lemma 2.3 of the paper, blind and by another
route, and made a second read of the claim against the Lean statements. GPT-6.2 Astra compared the Lean statements with
the claim in a blind read, read an earlier version of the paper line by line, and gave the argument for Step 0 of Lemma 3.1 that the paper now
writes out. GPT-6.2 Sol (by OpenAI) searched the literature and reviewed this text.

No professional mathematician has refereed this repository.

**The result rests on OpenAI's spectral plane theorem** (`matrix_spectral_plane`, paper "Euclidean geometry in the asymptotic
spectrum of tensors", 24 November 2026, https://github.com/openai/math). That theorem is proved in OpenAI's Lean library; it is
not proved by us. Our Lean files in `StabilizerRank/` take its statement as their one hypothesis (`MatrixSpectralPlane`);
`unconditional/Solution.lean` fills that hypothesis with OpenAI's theorem itself, and this form was built on
25 November 2026, together with the 7,283 files of the theorem's import closure. OpenAI's own catalog lists its
formalization as not reviewed. Proof checkers have checked what the section "What is checked" says.

## The theorem

Let `ψ` be a vector of `m` qubits with complex entries. Suppose that `ψ` is not a stabilizer vector. Then there is a number
`c > 0` with this property: for every `n`, the tensor power `ψ^{⊗n}` is not a sum of fewer than `2^{cn}` stabilizer vectors.
(In Lean this is proved from OpenAI's theorem: with the hypothesis `MatrixSpectralPlane` in `StabilizerRank/Final.lean`, and
with that hypothesis filled in by OpenAI's theorem in `unconditional/Solution.lean`.)

If `ψ` is a stabilizer vector, then every tensor power of `ψ` is a stabilizer vector. So for each `ψ` there are two cases. The
exact stabilizer rank of `ψ^{⊗n}` is at most 1 for all `n`, or it grows exponentially in `n`.

The T state is the case `m = 1`, `ψ = |0⟩ + e^{iπ/4} |1⟩`. The repository states this case separately. It also proves it over
every field `F` in which 2 is not zero and which has an element `ω` with `ω^4 = -1`: there the gate `S` uses `ω^2` in place of
`i`, and the vector is `b ↦ ω^{|b|}`. Both need the same hypothesis as the main theorem.

### The terms

- A vector of `m` qubits is a function from the strings of `m` bits to the complex numbers. The value at a string is the
  amplitude of that string.
- The gate `H` (Hadamard) on qubit `k` maps `ψ` to the vector whose value at `b` is `ψ(b with b_k = 0) + (-1)^{b_k} ψ(b with
  b_k = 1)`. We leave out the factor `1/√2`. This changes nothing, because all multiples of a stabilizer vector are
  stabilizer vectors.
- The gate `S` on qubit `k` multiplies the value at `b` by `i^{b_k}`.
- The gate `CNOT` with control `k` and target `l` (`k ≠ l`) maps `ψ` to the vector whose value at `b` is `ψ(b with b_l replaced by
  b_l + b_k mod 2)`.
- A stabilizer vector is a vector that we get from a multiple `c |0…0⟩` (the vector with value `c` at the string of zeros and
  value 0 elsewhere) by a finite sequence of the gates `H`, `S` and `CNOT`. Here `c` can be zero.
- The tensor power `ψ^{⊗n}` is the vector of `nm` qubits whose value at `n` strings `b_1, …, b_n` of `m` bits is the product
  `ψ(b_1) ψ(b_2) ⋯ ψ(b_n)`.
- The exact stabilizer rank of a vector is the smallest number `J` of stabilizer vectors whose sum is the vector.

The repository also proves the standard form: a vector is a stabilizer vector if and only if it has the form
`a [b ∈ A] i^{l(b)} (-1)^{q(b)}`, with a complex number `a`, an affine subspace `A` of the space of bit strings over the field
with two elements, a linear form `l(b) = Σ l_k b_k` and a quadratic form `q(b) = Σ q_{km} b_k b_m` with integer coefficients.

### The statements in Lean

`StabilizerRank/Def.lean` imports Mathlib only; `Challenge/Statement.lean` imports Mathlib and `StabilizerRank/Def.lean`. `StabilizerRank/Def.lean` has the definition of
stabilizer vectors, an inductive definition with four rules, one for `c |0…0⟩` and one for each gate. The main statement is:

```lean
theorem stabilizer_rank_exponential :
    ∀ {Q : Type} [Fintype Q] [DecidableEq Q] (ψ : (Q → ZMod 2) → ℂ), ¬ IsStabilizer Complex.I ψ →
    ∃ c : ℝ, 0 < c ∧ ∀ (n J : ℕ) (s : Fin J → (Fin n × Q → ZMod 2) → ℂ), (∀ j, IsStabilizer Complex.I (s j)) →
      (∀ b, ∏ i, ψ (fun q => b (i, q)) = ∑ j, s j b) → (2 : ℝ) ^ (c * n) ≤ J
```

The qubits of `ψ` are the elements of a finite set `Q`. The qubits of the tensor power are the pairs `(i, q)`. The file has
five more statements: `tensor_power` (the case of a stabilizer vector), `t_state`, `t_state_field`, `standard_form`, and
`stabilizer_rank_exponential_standard`. The last one is the main statement with stabilizer vectors written in standard form.
Its conclusion uses no definition of ours (its hypothesis `MatrixSpectralPlane` is the statement of OpenAI's theorem).

`StabilizerRank/Sanity.lean` has small checks of the definition: every vector of `n` qubits is a sum of `2^n` stabilizer
vectors (so the theorems do not speak about an empty set), `|0⟩ + |1⟩` is a stabilizer vector, and the T state is not one.

## The deep input

The proof uses one theorem that we did not prove: `OAI.LinearAlgebra.SpectralBooks.matrix_spectral_plane`. It is in the file
`OAI/LinearAlgebra/SpectralBooks/EveryField.lean` of openai/math, commit `3344da59991ed94f9ba711217b29c1d760badfa6`, folder
`lean/`. The paper is "Euclidean geometry in the asymptotic spectrum of tensors" (OpenAI, 24 November 2026). The theorem says:
over every field there are prices for tensors whose legs sit at points of the Euclidean plane, and these prices are convex in
the positions. A wire of dimension `q` between two points costs the distance times `log2 q`. Prices add under tensor products
and do not grow under restrictions. A sum of `J` tensors costs at most the largest price of a term plus `log2 J` times the
price of one bit that all occupied sites share (the diagonal tensor with two values). Our proof uses only the existence of these
prices. It does not use the convexity part of the theorem.

The import closure of `EveryField.lean` has 7,283 files. A GitHub runner cannot build it in its time limit. For this reason the
repository has two forms of each theorem.

1. **Conditional form** (default build). `StabilizerRank/Final.lean` proves the four rank bounds with one hypothesis,
   `MatrixSpectralPlane` (`tensor_power` and `standard_form` need none). Its definition is the statement of `matrix_spectral_plane`, word for word. Only 867 OpenAI files
   are needed for this, because our proof uses only the parts of the theory of prices that come before `EveryField.lean`.
   `Check/Plane.lean` prints the hypothesis.
2. **Form without hypothesis** (`unconditional/`). `unconditional/Solution.lean` fills in the hypothesis with
   `matrix_spectral_plane` itself. `unconditional/build.sh` fetches the 7,283 files from openai/math and from the two
   third-party libraries that they import, applies the two compatibility patches of openai/math, checks the SHA-256 sums in
   `unconditional/SHA256SUMS`, and builds. `unconditional/SameStatementU.lean` checks that the theorems are the statements of
   `Challenge/Statement.lean` and that `MatrixSpectralPlane` is the statement of `matrix_spectral_plane`.

## What is checked

| Check | Tool | Hypothesis | Result |
|---|---|---|---|
| Build of `StabilizerRank` (895 files) | Lean 4.34.1 kernel (`lake build`) | `MatrixSpectralPlane` | passed, 9,819 jobs, 25 November 2026 (`logs/p5r-2c-build.txt`); the GitHub workflow has not run |
| Axioms of the 8 results | `#print axioms` (`Check/Axioms.lean`) | | `propext`, `Classical.choice`, `Quot.sound` only, 8 of 8 (`logs/p5r-3-axioms.txt`) |
| Statements equal to `Challenge/Statement.lean` | `Check/SameStatement.lean` (definitional and syntactic) | | passed (`logs/p5r-4-same.txt`) |
| Form without hypothesis | `lake build Unconditional` (`Solution`, `SameStatementU`, `FCBridgeU`, with the 7,283 files of the import closure of `EveryField.lean`) | none | passed, 16,410 jobs (`logs/p5r-5-uncond.txt`); `SameStatementU`: "the statements are equal as terms, and the hypothesis is the statement of matrix_spectral_plane" |
| Axioms without hypothesis | `#print axioms` (`unconditional/AxiomsU.lean`) | none | `propext`, `Classical.choice`, `Quot.sound` only, 9 of 9: `Solution.plane`, the six `Solution.*` theorems, `FCBridge.bridge`, `FCBridgeU.superpolynomial_stabilizer_rank` (`logs/p5r-6-axiomsu.txt`) |
| Second check | `leanchecker` | none | our 27 modules (`NCBound`, `NOF`, `StabilizerRank`, `Check.FCBridge`, `FCBridgeU`, `SameStatementU`, `Solution`) replayed, exit 0 (`logs/p5r-7-leanchecker.txt`); the OpenAI modules were not replayed |
| Bridge to formal-conjectures PR 8164 | `Check/FCBridge.lean`, `unconditional/FCBridgeU.lean` | none | `FCBridgeU.superpolynomial_stabilizer_rank` built; axioms above |

The checks ran on 25 November 2026 in two stages. First, a clean build in a fresh copy of this folder: the SHA-256 sums of
`OAI-SHA256SUMS`, `FixedPointTheorems-SHA256SUMS` and `unconditional/SHA256SUMS` were checked, Mathlib came from
`lake exe cache get`, and the compiled modules of the import closure came from an earlier build of the same files on the
same machine (Lake checked their traces and rebuilt the modules whose traces did not match, some files of the third-party
library `Lemmata`). Two earlier attempts of that build were stopped (a system-wide limit on open files; a restart to rebuild
those modules first). `logs/clean-build/` has the outputs of its cache and copy steps. Second, after that build we removed
lemmas that the theorems of this repository do not use: one file of `NOF/` was deleted, and `NOF/Main.lean` and
`NCBound/Circle.lean` were shortened. Every step of the table then ran again in a copy of the clean build folder with the
files of this version. Lake compiled the changed modules and all modules that import them, 17 modules of ours, and took the
compiled OpenAI modules from the clean build. The SHA-256 sums of the 35 Lean and build files of ours in that folder are the
sums in `SHA256SUMS`. The files `logs/p5r-*.txt` are the outputs of the steps of this second run; the table reports this run.

The table lists every check that passed. `leanchecker` runs the same kernel code a second time. A proof checker that is a
separate implementation of the kernel has not checked the result.

The OpenAI catalog file `lean/formalization.yaml` says `automation: methods: method: agent` and `review: status: unchecked`.
Our scan of the 7,283 files found no `sorry`, no `axiom`, no `native_decide`, no `unsafe` or `extern` code, and no file,
process or network access (one `IO.mkRef` makes a cache). It found metaprogramming that builds terms for the kernel. The kernel
checks those terms. The 895 files of the conditional form have no metaprogramming.

## What is not claimed

- **Approximate rank.** The theorem is about exact sums. It says nothing about sums that are only close to `ψ^{⊗n}`. The
  known lower bounds for approximate rank are nearly quadratic in `n` (see below).
- **The constant.** The proof gives some `c > 0` for each `ψ`. It does not compute `c`. For the T state the best known upper bound is `O(2^{0.3963 n})`, so `c ≤ 0.3963` there.
- **Classical simulation.** The exact rank bounds one family of simulation methods. It is not a lower bound for classical
  simulation in general.
- **Qudits.** The theorem is for qubits. Nothing here covers systems with more than two levels.
- **Mixed states and other gate sets.** The theorem is about pure vectors and the stabilizer vectors defined above.
- **The optimality part of Conjecture 1 of Bravyi, Smith and Smolin** (magic states have the smallest stabilizer rank among
  non-stabilizer single-qubit states). We prove only that every non-stabilizer vector has exponential rank.

## What is a corollary and what is new

Bravyi, Smith and Smolin conjectured in 2016 that the exact stabilizer rank of `n` copies of a magic state is `2^{Ω(n)}`.
For the T state this follows in a few lines from the OpenAI paper: the price of a stabilizer state of `3h` qubits, split
into three blocks of `h` qubits, is at most `3h/2` (GHZ/EPR form of three-party stabilizer states, Bravyi-Fattal-Gottesman 2006), the paper's theorem
"Exact extension" (2) on a triangle with two side midpoints gives a table above that value, and Clifford+T gates are dense.
The OpenAI paper and library do not state this corollary (we searched them on 25 November 2026), but the credit for the
mechanism is OpenAI's. What we add: the dichotomy for every vector of any number of qubits (a reduction to one qubit by
stabilizer operations and a density argument), a proof that uses no GHZ/EPR normal form (`StabilizerRank/Lift.lean`), the
machine check, and a bridge to the open Lean target of formal-conjectures (below). The paper `paper/stabilizer-rank.tex`
is an informal account of the same theorem.

## The formal-conjectures target

google-deepmind/formal-conjectures pull request 8164 (open on 25 November 2026) states the question of Peleg, Shpilka and
Volk as the Lean theorem `superpolynomial_stabilizer_rank`: for all `d, C` there is `N` such that for `n ≥ N` every exact
decomposition of `T^{⊗n}` into `r` stabilizer functions has `C n^d < r`. `Check/FCBridge.lean` copies its definitions and its statement
unchanged (comments and layout aside) and proves that statement from `t_state` and `standard_form`. On 25 November 2026 we
compared the copy with the file of the pull request at its head commit `b586a02bfe12389907c12cfd03121b8430e28dff` (`diff`): the
nine definitions and the statement are the same text; one sentence of a comment is left out. The copy was not compiled inside
the formal-conjectures repository. Their stabilizer functions use `i^{(l·x mod 2)}`; ours use
`i^{l·x}` with an integer exponent; the two families agree because `i^{s mod 2} = i^s (-1)^{s(s-1)/2}` and `s(s-1)/2` is a
quadratic form in the bits (their decompositions carry the scalar factors in the coefficients). So the target holds given
`MatrixSpectralPlane`; `unconditional/FCBridgeU.lean` proves it without hypothesis (`FCBridgeU.superpolynomial_stabilizer_rank`).

## Earlier work

We looked up each of these sources on 25 November 2026 (abstract pages on arXiv; for Dutt and for Theorem 1.6 of
Mehraban and Tahmasbi also the text).

- S. Bravyi, G. Smith, J. Smolin, "Trading classical and quantum computational resources", Phys. Rev. X 6, 021043 (2016),
  arXiv:1506.01396. Classical simulation with sums of stabilizer vectors for tensor powers of magic states.
- S. Peleg, A. Shpilka, B. L. Volk, "Lower bounds on stabilizer rank", arXiv:2106.03214. A lower bound of order `n` for the
  stabilizer rank of the `n`-th tensor power of single-qubit magic states.
- B. Lovitz, V. Steffan, "New techniques for bounding stabilizer rank", arXiv:2110.07781. An explicit family of product states
  with exponential stabilizer rank and constant approximate stabilizer rank. These are products of different states. Our
  theorem is about powers of one fixed vector.
- S. Mehraban, M. Tahmasbi, "Quadratic lower bounds on the approximate stabilizer rank: a probabilistic approach",
  arXiv:2305.10277. A lower bound of order `n^2`, up to logarithmic factors, for approximate rank, for a wide range of the
  approximation parameters. Their abstract also answers a question of R. Williams (2018) with a super-linear bound: a
  function computable in polynomial time needs super-linearly many exponentials of quadratic forms over the field with two
  elements. Their Theorem 1.6 is a conditional bound: the exact rank of `T^{⊗m}` is super-polynomial unless the permanent has
  polynomial-size circuits.
- F. Labib, "Stabilizer rank and higher-order Fourier analysis", Quantum 6, 645 (2022), arXiv:2107.10551. A lower bound of
  order `n` for the stabilizer rank of `n` copies of a qudit analogue of the magic state, in each prime dimension.
- P. Sinha, B. Lovitz, "Improved bounds on stabilizer extent and Clifford rank", arXiv:2610.06819 (5 October 2026). A lower
  bound of order `n^2 / log n` for the approximate stabilizer rank of tensor powers of any non-stabilizer qubit state.
- H. Qassim, H. Pashayan, D. Gosset, "Improved upper bounds on the stabilizer rank of magic states", Quantum 5, 606 (2021),
  arXiv:2106.07740. The upper bound `O(2^{0.3963 n})` for T states.
- A. Dutt, "A note on tomography of states with low stabilizer rank", arXiv:2610.03658 (2 October 2026). Section 3 gives a
  lower bound of order `n^2` up to polylogarithmic factors as the best known result for the stabilizer rank of `n` T states.
- F. Wei, K.-W. Wu, Z. Liu, Z.-W. Liu, "Robust exponential lower bounds for fermionic and bosonic Gaussian ranks",
  arXiv:2610.02172 (1 October 2026). The same kind of dichotomy for Gaussian rank (every pure non-Gaussian state, of definite parity
  in the fermionic case; approximate border rank). They call the stabilizer rank problem longstanding and say that their methods do not extend directly to it.
- O. Reardon-Smith, arXiv:2610.03699 (2 October 2026): exponential lower bounds for fermionic Gaussian rank; best stabilizer rank
  lower bounds quadratic.
- Y. R. Pei, Zenodo 10.5281/zenodo.24023348 (6 November 2026): an exponential lower bound for `χ(T^{⊗t})` CONDITIONAL on the
  exponential hardness of syndrome decoding.

Before this work, the best unconditional lower bounds for the exact stabilizer rank of tensor powers that we found are these
polynomial bounds. We found no earlier statement of an exponential lower bound for the exact stabilizer rank of `ψ^{⊗n}`. If you know
one, please tell us.

## The proof in short

1. **Stabilizer vectors are cheap.** Write `n` copies of `ψ` as a function of three groups of bits. The price of a stabilizer
   vector on these legs is at most the number of bits (`StabilizerRank/Lift.lean`). A sum of `J` terms adds at most a constant
   times `log2 J` (`StabilizerRank/Main.lean`).
2. **Some table is expensive.** There is a table of zeros and ones on three groups of bits whose price is larger than the
   number of bits. This uses that midpoints are unique in the plane of prices and a lemma on three legs at the corners of a
   triangle (`NOF/`). Its powers are expensive in proportion to the power.
3. **The tables reachable from copies of `ψ` are dense.** We use operations that keep "few stabilizer terms": multiplication with a quadratic
   phase, substitution of affine maps, and sums over one bit. With them, copies of a vector that is not a stabilizer vector
   give a one-qubit vector `(1, a)` with `a ≠ 0` and `a^4 ≠ 1` (`StabilizerRank/Reduce.lean`; the argument looks at 4 points
   of a plane and 8 points of a cube). If `a` is a root of unity, the Hadamard transform gives `(1, (1-a)/(1+a))`, and
   `(1-a)/(1+a)` is not a root of unity. Products of powers of such a gate along linear forms are dense in all tables in the
   Zariski topology (`StabilizerRank/Dense.lean`, independence of characters). The tensors with a price at most a bound form a
   closed set in the Zariski topology (a theorem in the OpenAI files), so some product has a large price.
4. **Count.** Compare the price of the `N`-th power of the expensive table with the bound from step 1.

## Files

| Folder | Content | Origin |
|---|---|---|
| `OAI/` | 867 files, unchanged | openai/math, commit `3344da5…`, folder `lean/`; Apache 2.0, `OAI-LICENSE`; sums in `OAI-SHA256SUMS` |
| `FixedPointTheorems/` | 5 files | harfe/fixed-point-theorems-lean4, commit `770940d…`, with the patch `lean/patches/fixed-point-theorems-lean4341.patch` of openai/math; MIT, `FixedPointTheorems-LICENSE`; sums in `FixedPointTheorems-SHA256SUMS` |
| `NCBound/Circle.lean` | unit vectors of the plane | ours |
| `NOF/` | 6 files: prices of tables on three groups of bits | ours |
| `StabilizerRank.lean`, `StabilizerRank/` | 1 + 15 files: the stabilizer rank | ours |
| `Challenge/`, `Check/` | statements and checks (`Check/FCBridge.lean`: bridge to formal-conjectures PR 8164) | ours |
| `FIDELITY.md` | which statement is machine-checked, the question it answers, the bridge | ours |
| `unconditional/` | the form without hypothesis (`Solution.lean`), its statement check, its axioms, and `FCBridgeU.lean` (the formal-conjectures target without hypothesis) | ours |
| `paper/stabilizer-rank.tex` | the paper: an informal account of the theorem for qubits (not formalized) | ours |
| `logs/` | outputs of the steps of the checks (`p5r-*.txt`) and of the clean build before them (`clean-build/`) | ours |
| `SHA256SUMS` | SHA-256 sums of all other files of this repository (`shasum -a 256 -c SHA256SUMS`) | ours |

At the OpenAI commit we found no NOTICE file, and the copied files have no copyright headers. We changed none of them. Our
files are under the Apache License 2.0 (`LICENSE`). `Check/FCBridge.lean` copies nine definitions and one statement from the
file `FormalConjectures/Arxiv/2106.03214/StabilizerRank.lean` of pull request 8164 of google-deepmind/formal-conjectures
(Copyright 2026 The Formal Conjectures Authors, Apache License 2.0).

## How to build

```sh
lake exe cache get
lake build                              # the conditional form
lake env lean Check/Axioms.lean
lake build Challenge && lake env lean Check/SameStatement.lean
lake build Check && lake env lean Check/FCBridge.lean
sh unconditional/build.sh               # the form without hypothesis: many hours and much memory
```

`unconditional/build.sh` ends with `lake build Unconditional` (this builds `Solution`, `SameStatementU` and `FCBridgeU`) and
`lake env lean unconditional/AxiomsU.lean`.

Toolchain: Lean 4.34.1 (`lean-toolchain`), Mathlib commit `d13f23b723b8a846827a245b89c10fc7d3f11612`.
