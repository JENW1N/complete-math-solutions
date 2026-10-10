# Erdős 1062: scope of the complete formalization

Scope review dated October 10, 2026. This note identifies the mathematical target
and its relationship to the submitted source. It is not a successful local build
report. Actual compilation results and transitive axiom audits are recorded
separately; if `verification/erdos1062-full.json` is supplied, its checked source
version, completed stages, and conclusion determine what verification is claimed.

## Original question and definitions

[Erdős problem 1062](https://www.erdosproblems.com/1062) asks for the largest
cardinality `f(n)` of a subset of `{1,...,n}` in which no member divides two
distinct other members. It asks both how large `f(n)` can be and whether
`lim f(n)/n` is irrational. The original page was available through its indexed
text during this review; a direct page request returned HTTP 403.

The reference definition in
[FormalConjectures/ErdosProblems/1062.lean](../FormalConjectures/ErdosProblems/1062.lean)
has the intended direction of divisibility: for each `a ∈ A`, the set of members
`b ∈ A \ {a}` satisfying `a ∣ b` is a subsingleton. Thus a pair `{a,2a}` is
allowed, whereas `{a,2a,3a}` is forbidden. `f(n)` uses `Nat.findGreatest` over
cardinalities of such subsets of `Set.Icc 1 n`. The interval is finite, the empty
set is admissible, and the search bound `n` covers every possible cardinality.

The reference file supplies a formal target for part (ii), but still has a TODO
for part (i). Consequently the explicit part (i) statement below is a proposed
formal statement for review, not an existing maintainer-approved
FormalConjectures theorem. A proof of part (ii) alone does not answer the full
extremal question represented by JSP-000882.

## Exact finite target, including zero

For an integer `t ≥ 1`, put `ell_b(t) = floor(log_b(t))` and define

```text
R(t) = 1 + ell_3(t) + floor(ell_2(t)/2)
       + 1_{ell_2(t) is odd and 2 * 3^ell_3(t) ≤ t}.

B(t) ⇔ ∃ j,b ∈ ℕ,
           4^j ≤ t and 4*t < 5*4^j
           and 10*3^b ≤ t and t < 12*3^b.

g(t) = R(t) - 1_{B(t)}, as an integer.
```

Set `R(0) = 0`. The displayed inequalities make `B(0)` false, so `g(0) = 0`.
The exact finite answer is

```text
For every n ∈ ℕ,
  (f(n) : ℤ) = Σ_{1 ≤ q ≤ n, gcd(q,6)=1} g(floor(n/q)).
```

The sum is empty at `n = 0`, agreeing with `f(0) = 0`. In Lean, `Nat.log` and
natural-number division encode the integer logarithms and floors; `g` takes
values in `ℤ`, so subtraction inside the sum is signed. The source also exposes
the equivalent natural-number sum of the ranks minus the number of exceptional
cores. These arithmetic definitions do not refer to `f` or optimize over
fork-free sets, so the identity determines the extremal value rather than
restating its definition.

The paper also writes the rank with `floor(log_4(t))` and an overlap
indicator. These agree with the displayed parity form: `Nat.log 4 t` equals
`Nat.log 2 t / 2`, and the odd binary-log condition is equivalent to
`2 * 4^(Nat.log 4 t) ≤ t` for positive `t`. The interval endpoints relevant to
the real cutoffs are integral (a nonempty exceptional window has `j ≥ 2`), so
using `floor(n/q)` preserves those conditions.

The full target combines this identity for every `n` with convergence of
`(f(n) : ℝ) / n` to an irrational real number. The proposed wrapper identifies
the limit as `Bounty.explicitDensity`. The ratio's value at zero has no effect on
the limit at infinity. No finite computation or numerical approximation to the
density is substituted for either universal assertion.

## Mathematical manuscript and source map

The full manuscript is Liam Kruer and Jensen Kohlmeyer's
[*An exact formula for fork-free sets of integers and the irrationality of their density*](https://github.com/JENW1N/complete-math-solutions/blob/2fb37782da6f1f125c44bdd9cca5b2a205d9aad8/papers/erdos1062-fork-free-density.pdf).
The linked immutable baseline is
`2fb37782da6f1f125c44bdd9cca5b2a205d9aad8`; the PDF's SHA-256 is
`f7fa42bf289cfd28e1dc022ba5262323c9b791a08e585338dc78d2fa2dd7d5ea`.
Its internal date is September 21, 2026. Theorem 1.1 gives the finite formula;
Theorem 1.2 identifies the density; Theorem 1.3 proves irrationality. Theorem 1.1
also places a maximizing set inside `(n/8,n]`. That additional localization is
stronger than the original question and is not required for the full target
specified here.

The accepted body already contains the unconditional finite identity. Its
declaration map is as follows; line numbers refer to
[`accepted/erdos1062.lean` at the immutable baseline](https://github.com/JENW1N/complete-math-solutions/blob/2fb37782da6f1f125c44bdd9cca5b2a205d9aad8/accepted/erdos1062.lean).

| Declaration | Location | Role |
| --- | --- | --- |
| `Bounty.smoothRankBound` | line 936 | Arithmetic definition of `R`. |
| `Bounty.badWindow` | line 1109 | Arithmetic predicate `B`. |
| `Bounty.coprimeCores` | line 1459 | Exactly the positive integers at most `n` coprime to six. |
| `Bounty.lossCores` | line 1590 | Cores whose quotient cutoff satisfies `B`. |
| `Bounty.globalUpper` | line 1643 | Rank sum minus exceptional-core count. |
| `Bounty.cutoffCertificate_witness` | line 2213 | Constructs an attaining fork-free set from a certificate. |
| `Bounty.cutoffAvailability` | line 50424 | Supplies the certificate availability without an extra hypothesis. |
| `Bounty.f_eq_globalUpper` | line 50426 | Unconditional equality for every natural `n`. |
| `Bounty.signedRank` | line 65918 | Real-valued form of `g`. |
| `Bounty.globalUpper_cast_sum` | line 65926 | Moves the correction inside the sum. |
| `Bounty.tendsto_f_jumpDensity` | line 73975 | Density convergence from the finite formula and summability. |
| `Bounty.jumpDensity_eq_explicitDensity` | line 67601 | Identifies the limiting coefficient series. |
| `Bounty.target` | final declaration | Existing part (ii) target. |

[`Solutions/Erdos1062Full.lean`](../Solutions/Erdos1062Full.lean) exposes
`Erdos1062Full.exact_formula`, `part_i`, `density_converges`,
`density_irrational`, `part_ii`, and the combined `full_scope`. Its finite
formula follows by casting `f_eq_globalUpper`, applying `globalUpper_cast_sum`,
and identifying the explicitly defined arithmetic summand. Its public statements
contain no `answer` placeholder. Existence of these declarations in source is
distinct from a completed kernel check and full axiom audit.

## Service evidence, dates, and prior work

The [Conjectures.io record](https://conjectures.io/results/8d59a0af-6762-4606-93c9-72dd356a57bc)
specifically certifies part (ii). It reports acceptance on September 21, 2026 at
18:55:24.437579 UTC, production verification on September 21, an advisory review
decision on September 22, and public certification on September 23. The displayed
formal target is existence of an irrational limit, not the combined target in
this note. The record reports ordinary Lean kernel verification with permitted
axioms `propext`, `Quot.sound`, and `Classical.choice`; it does not report a
Nanoda run. These are service-reported results, not a new local replay.

The currently linked
[service exposition](https://conjectures.io/papers/erdos1062ii.pdf?v=20260922-authors)
is a different six-page document, titled *Erdős Problem 1062(ii): Irrationality
of a Divisibility Density* and dated September 22, 2026. Its Proposition 2.1
describes the exact finite formula and names `f_eq_globalUpper` and
`globalUpper_cast_sum`. It should not be labeled with the full manuscript's
different title. Both documents name Liam Kruer and Jensen Kohlmeyer.

Lebensold's earlier bounds `0.6725 n ≤ f(n) ≤ 0.6736 n` for large `n` remain
credited. D. Davis's [April 2026 paper](https://arxiv.org/abs/2604.17613)
establishes existence and effective computability of the density while leaving
irrationality open. Convergence alone is therefore not claimed as new. The
manuscript's internal date is not evidence of first public disclosure, and
neither this scope note nor the service record establishes exhaustive historical
priority.

## JSP catalog and policy boundary

The policy revision inspected was
[`16877004910734cecca83cc5af0fec2f5a4125b3`](https://github.com/TheJustinSunPrize/awards/commit/16877004910734cecca83cc5af0fec2f5a4125b3),
whose commit date is October 8, 2026. The relevant record is
[`problems/catalog-0801-0900.md#JSP-000882`](https://github.com/TheJustinSunPrize/awards/blob/16877004910734cecca83cc5af0fec2f5a4125b3/problems/catalog-0801-0900.md#JSP-000882),
titled *How large can an integer-interval subset be if no element divides two
other elements?* At that revision it is Open, with Lean proof No and eligibility
No.

The [contribution rules](https://github.com/TheJustinSunPrize/awards/blob/16877004910734cecca83cc5af0fec2f5a4125b3/CONTRIBUTING.md)
require a complete original-problem solution and original Lean repository,
branch, full commit SHA, statement/proof locations, reproduction instructions,
axiom audit, and attribution evidence. The mathematical solution must pass
review before Lean acceptance. Participant edits are limited to Current status
(including Proof contributors), Lean proof, Attribution basis, and Publication
details. Maintainers handle the index and eligibility fields. The existing
[PR #4905](https://github.com/TheJustinSunPrize/awards/pull/4905) should be updated
instead of duplicating the same contribution.

The [award process](https://github.com/TheJustinSunPrize/awards/blob/16877004910734cecca83cc5af0fec2f5a4125b3/docs/award-process.md)
separates mathematical review, Lean verification, merge, public candidate notice,
review period, identity checks, recipient confirmation, and award. A successful
build does not establish priority or award entitlement. Original authorship and
independently checkable public chronology must be preserved; an earlier PR or
an author-supplied Git timestamp alone does not establish priority.
