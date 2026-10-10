# Mathematical manuscripts and original proof sources

This is Jensen Kohlmeyer’s public source edition of work coauthored with Liam Kruer. Will Howe and Grant Huffman are also authors of the minimal-graph manuscripts, as recorded in the PDFs. All manuscript acknowledgments and borrowed-source credits are preserved.

The original files are copied without mathematical edits from the authors’ supplied portfolio materials. This publication does not backdate the files or claim priority over earlier literature. `SOURCE_MANIFEST.json` records SHA-256 hashes, exact scopes and credits. Dated Conjectures.io records and earlier original repositories are independent evidence where linked by the JSP submissions. A manuscript date alone is not proof of public disclosure.

Fresh Lean build results will be recorded separately per target. Preserving a Lean file is not a claim that this whole collection has passed a clean build. Some files are validator submission bodies and require the stated imports, namespace and pinned dependencies.

| Work | Manuscript | Original proof source |
| --- | --- | --- |
| A graph without repeated midpoints | [PDF](papers/Green15-Kohlmeyer-Kruer.pdf) | [Lean](proofs/Green15.lean) |
| Cover the cube in two moves | [PDF](papers/green40-covering-codes.pdf) | [Lean](proofs/Green40RadiusTwo.lean) |
| One point changes the answer | [PDF](papers/Green47-Kohlmeyer-Kruer.pdf) | [Lean](proofs/Green47Counterexample.lean) |
| Structure inside a sumset | [PDF](papers/green51-one-half.pdf) | [Lean](proofs/Green51OneHalf.lean) |
| Ordowski’s second question: no odd solution | [PDF](papers/ordowski-conjecture-2.pdf) | [Lean](proofs/OrdowskiConjecture2.lean) |
| Bala 1: the square endpoint | [PDF](papers/bala-conjectures-1-and-2.pdf) | [Lean](proofs/BalaConjectures1And2.lean) |
| Bala 2: the shortened sum | [PDF](papers/bala-conjectures-1-and-2.pdf) | [Lean](proofs/BalaConjectures1And2.lean) |
| Bala 4: square divisibility | [PDF](papers/bala-conjecture-4.pdf) | [Lean](proofs/BalaConjecture4.lean) |
| Wilson: when a reciprocal determinant is an integer | [PDF](papers/wilson-integrality-a060841.pdf) | [Lean](proofs/Wilson_Integrality_Conjecture_A060841.lean) |
| Sauras Altuzarra I: an exact denominator | [PDF](papers/sauras-altuzarra-conjecture-i.pdf) | [Lean](proofs/SaurasAltuzarraConjectureI.lean) |
| A Counterexample to the Square Conjecture for Triangular Matchstick Prime Sums | [PDF](papers/triangular-matchstick-prime-sums.pdf) | [Lean](proofs/TriangularMatchstickPrimeSums.lean) |
| Sun 5: gaps that never disappear | [PDF](papers/sun-conjecture-5.pdf) | [Lean](proofs/SunConjecture5.lean) |
| Wong: connectedness in one direction | [PDF](papers/wong-235893.pdf) | [Lean](proofs/Wong235893.lean) |
| Dillies: the convex VC₂ bound in ℝ³ | [PDF](papers/dillies-convex-vc2.pdf) | [Lean](proofs/DilliesConvexVC2Conjecture.lean) |
| Bala A141057: congruences at integer indices | [PDF](papers/bala-a141057-supercongruence.pdf) | [Lean](proofs/BalaA141057Conjecture.lean) |
| Quartic minimal graphs are affine | [PDF](papers/quartic-minimal-graphs.pdf) | [Lean](proofs/QuarticMinimalGraphs.lean) |
| Polynomial minimal graphs in dimension eight | [PDF](papers/polynomial-minimal-graphs-dimension-eight.pdf) | [Lean](proofs/PolynomialMinimalGraphsDimensionEight.lean) |
| Erdős 14 | [PDF](papers/erdos-14.pdf) | [Lean](proofs/Erdos14PartI.lean), [Lean](proofs/Erdos14PartIICounterexample.lean) |
| Erdős 108 | [PDF](papers/erdos108-arc-graphs.pdf) | [Lean](proofs/Erdos108.lean) |
| Erdős 859 | [PDF](papers/erdos859-divisor-sums.pdf) | [Lean](proofs/Erdos859Counterexample.lean) |
| Erdős 944 | [PDF](papers/erdos-944.pdf) | [Lean](proofs/Erdos944.lean) |
| Erdős 1062 | [PDF](papers/erdos1062-fork-free-density.pdf) | [Lean](proofs/Erdos1062PartII.lean) |

The mathematical and formalization contributions are distinguished in each prize submission. No private identity documents, payment details or unpublished collaborator correspondence belong in this repository.

## Reproduce the accepted Erdős proofs

Install the Lean version in `lean-toolchain`, then run:

```sh
lake update
lake exe cache get
lake build Solutions.Erdos14i Solutions.Erdos14ii Solutions.Erdos108 Solutions.Erdos944 Solutions.Erdos859 Solutions.Erdos1062
```

The wrappers under `Solutions/` each print the target and its complete axiom closure. Expected dependencies are `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` is permitted. `accepted/PROVENANCE.json` binds each original proof body to its public service download and SHA-256. `references/PROVENANCE.json` records the frozen reference-source hashes. Erdős 272’s wrapper is also available for the separately identified Szabó linear-error variant.

A full fresh proof compilation can be lengthy, especially for Erdős 1062. Logs report cached-library reuse explicitly; they do not claim a fresh build of Lean or all of Mathlib.

## Catalog scope under review

The following manuscripts settle separately stated original questions. The broader JSP entries require a scope ruling before a complete-solution catalog submission.

| Original question | Complete mathematical proof | Companion source |
| --- | --- | --- |
| Erdős 18(b), factorial divisors | [PDF](papers/erdos18b-factorial-divisors.pdf) | [Lean](proofs/Erdos18b.lean) |
| Szabó’s linear-error variant of Erdős 272 | [PDF](papers/erdos-272.pdf) | [Lean](proofs/Erdos272.lean) |
| Erdős 354(i), multiplier two | [PDF](papers/erdos354-Kohlmeyer-Kruer.pdf) | [Lean](proofs/Erdos354PartI.lean) |

These listings do not assert that every question grouped into the corresponding JSP records has been resolved.
