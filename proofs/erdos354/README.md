# Erdős 354: full formal answers and parameter existence

The package covers the base-two theorem and both quantifier readings of the variable-base extension. All statements use the same floor sequences, interleaving, and indexed finite-sum definition of completeness.

| Statement | Proof |
| --- | --- |
| Base 2 works for every positive coefficient pair with irrational ratio | Jensen Kohlmeyer and Liam Kruer |
| Some fixed base in (1,2) works for every such pair | Kenta Kitamura; witness √φ |
| Every base in (1,2) works for every such pair | False; `ParameterExistence.lean` constructs a counterexample |

All 12 modules pass Lean 4.33.1 without warnings. The final endpoints depend only on `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` or unproved parameter-existence premise remains. The exact source hashes and checks are recorded in `verification.json`.

The combined endpoint is `Erdos354Full.full_solution` in `FullSolution.lean`. It includes an explicit existential counterexample, not a hypothesis that one exists. `Erdos354Full.variable_base_answer` gives the negative answer to the universal formulation. [The mathematical proof note](PROOF.md) explains the new recurrence construction and identifies the sources for the other two components.

## The parameter-existence proof

The new proof establishes the premise that was previously missing. It uses a different algebraic base from the Salem number in Geneson's paper: a real root γ in (1,2) of

```text
X^6 - X^5 - X^4 - X^3 - X^2 - X - 1.
```

For this base it constructs η > 0 with

```text
3/20 < fract(η γ^j) < 1/4    for every integer j ≥ 1.
```

Thus it proves exactly the parameter existence needed for the counterexample to the universal version of #354. It does not claim to formalize Geneson's stronger location of the base below φ or his exclusion of every ratio rγ^k. The required irrational coefficient ratio is proved.

The construction uses the integer sequence beginning with six ones and continuing by summing the preceding six terms. Its terms are all 1 modulo 5. Let c₀,...,c₅ be the coefficients of the quotient of the characteristic polynomial by X−γ. They satisfy

```text
0 < c₀ < ... < c₅ = 1,
Σ cᵢ = 5/(γ−1) > 5.
```

The weighted sums Σ cᵢ Uₙ₊ᵢ grow exactly as γⁿ. After subtracting the matching geometric sequence, the error satisfies a recurrence with nonnegative coefficients 1−cᵢ whose sum is less than one. A finite-memory contraction estimate proves that this absolute error tends to zero. Dividing by 5 and shifting sufficiently far gives the displayed fractional-part bounds.

Finally set α = 2ηγ and β = α(1+γ). Both coefficients are positive, α/β = 1/(1+γ) is irrational, and every term of both floor sequences is even. Every indexed finite sum is therefore even, so the interleaving is incomplete.

This real recurrence proof avoids importing any unformalized theorem about Pisot or Salem numbers. The relevant Pisot-number family appears in [Dubickas 2006, page 332](https://doi.org/10.1017/S0017089506003090); the final parity construction is the one used in [Geneson, Corollary 12](https://arxiv.org/html/2609.25107v1#Thmtheorem12).

## Modules

- `Erdos354Definitions.lean`: the shared definitions, copied from Formal Conjectures and imported over Mathlib alone, without either admitted problem theorem.
- `KohlmeyerKruerPartI.lean`: the original base-two argument, with an explicit endpoint.
- `KitamuraPartII.lean`: the original existential argument.
- `Combined.lean`: their combined affirmative endpoints.
- `QuantifierObstruction.lean`: parity obstruction and the implication from the parameter witness.
- `RecurrenceDecay.lean`: the general finite-memory decay estimate.
- `MultinacciBase.lean`: existence and irrationality of γ.
- `MultinacciAsymptotic.lean`: vanishing absolute error for the six-term recurrence.
- `MultinacciIntegers.lean`: the mod-5 sequence and the uniform fractional-part witness.
- `ParameterExistence.lean`: the unconditional parameter theorem and counterexample.
- `FullSolution.lean`: the final base-two, existential-base, and universal-counterexample results.

## Quantifier scope and source wording

Graham's Question 12, printed page 36 (PDF page 15), and Erdős–Graham, printed page 58 (PDF page 54), leave the variable-base quantifier implicit. The current Formal Conjectures part (ii) is existential. The universal interpretation is a different statement with a different answer. This package proves both answers explicitly rather than relying on the ambiguous wording.

Completeness means that every sufficiently large integer is a sum of terms with distinct indices. Equal values at different indices remain separate occurrences.

## Rechecking

For a fresh checkout, run from `proofs/erdos354` with Elan and Python 3 installed:

```sh
lake update
lake exe cache get
lake --wfail build
python3 verify.py
```

The script checks every module in dependency order, fails on compiler warnings or unapproved axioms, and writes compiler logs and a source-hashed `verification.json`. The allowed axioms are `propext`, `Classical.choice`, and `Quot.sound`. Use the default command for a fresh end-to-end check; `--reuse` only provides a faster incremental check.

The only library dependency is public Mathlib, revision `0df444a360eaa60ab8c11dca51a86af692955474`, with Lean 4.33.1. The completeness definitions are copied explicitly, so the proof does not depend on a private Formal Conjectures snapshot. `--lean` and `--workspace` can point to another matching installation. `lakefile.toml` and `lean-toolchain` describe a fresh Lake setup. The recorded verification uses the matching local Mathlib cache, recompiles all twelve modules, and audits the stated endpoints; it is not a rebuild of Mathlib from source or an independent human review.

The original Lean components are in `sources/`; `sources.json` records the research-source URLs. `logs/source-adaptations.diff` records the original component adaptations. Neither component's mathematical argument was changed. External research PDFs and scans are referenced at their original URLs rather than redistributed here.

## Sources and attribution

- [Kohlmeyer–Kruer Lean proof](https://jenwin.io/papers/Erdos354PartI.lean).
- [Kitamura Lean proof, pinned commit](https://github.com/KitaKen1/erdos-354-part-ii/blob/5536b1874d734cfaac522a379722b8cd828dd343/lean/Erdos354PartIIFC.lean).
- [Graham 1971](https://mathweb.ucsd.edu/~ronspubs/71_08_integer_sums.pdf#page=15).
- [Erdős–Graham 1980](https://mathweb.ucsd.edu/~ronspubs/80_11_number_theory.pdf#page=54).
- [Dubickas 2006](https://doi.org/10.1017/S0017089506003090).
- [Geneson 2026](https://arxiv.org/html/2609.25107v1#Thmtheorem12).

The parameter-existence formalization and integration were prepared for Jensen Kohlmeyer with Codex assistance on October 10, 2026. This is the first public edition of that new source. The earlier base-two work remains jointly attributed to Jensen Kohlmeyer and Liam Kruer. The existential-base proof belongs to Kenta Kitamura; the previously published universal negative answer belongs to Jesse Geneson. Including Kitamura's proof as a credited dependency does not claim his authorship or priority for the submitter. See `NOTICE` for the component attribution and Apache-2.0 notices.
