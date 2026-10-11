# Mathematical scope and proof for Erdős 354

Prepared by Jensen Kohlmeyer with Codex assistance, 10 October 2026.

For positive real numbers α, β and γ > 1, consider the two indexed sequences
floor(αγⁿ), floor(βγⁿ), for n ≥ 0. Completeness means that every sufficiently
large integer is a sum of finitely many distinct indexed occurrences. Equal
integer values at different indices remain separately available.

The package proves these three statements with those same definitions:

1. At γ = 2 the interleaving is complete whenever α/β is irrational.
2. Some fixed γ in (1,2) works for every positive α, β with irrational α/β.
3. It is false that every γ in (1,2) works for every such pair.

These are yes/no statements. No classification of all working bases is asserted.

## The first two statements and their sources

Statement 1 is Theorem 1.1 of Jensen Kohlmeyer and Liam Kruer's
[*Completeness of two floor-doubling sequences*](../../papers/erdos354-Kohlmeyer-Kruer.pdf).
Its complete Lean proof is `KohlmeyerKruerPartI.lean`; `Combined.lean` exposes
the endpoint `Erdos354Combined.part_i` without an admitted problem statement.

Statement 2 follows from Kenta Kitamura's stronger single-sequence result:
for γ equal to the square root of the golden ratio, floor(αγⁿ) alone is complete
for every α > 0. His [original proof and explanation](https://github.com/KitaKen1/erdos-354-part-ii/tree/5536b1874d734cfaac522a379722b8cd828dd343)
and Apache-2.0 Lean source are retained and credited. The imported proof's
mathematical argument is unchanged; only its dependency on the common definitions
was adapted. `Erdos354Combined.part_ii_exists` is the combined endpoint.

## An explicit construction for the third statement

The universal negative answer was previously obtained by Jesse Geneson,
[Corollary 12](https://arxiv.org/html/2609.25107v1#Thmtheorem12).
The construction below uses his parity mechanism with a different base and a
fully formalized elementary recurrence argument. The family of bases is related
to the discussion in Dubickas, *Even and odd integral parts of powers of a real
number*, Glasgow Mathematical Journal 48 (2006), page 332,
[DOI](https://doi.org/10.1017/S0017089506003090).
This does not establish a base below the golden ratio or all the stronger
properties in Geneson's result.

### 1. Choose an irrational base in (1,2)

Let

    p(x) = x⁶ − x⁵ − x⁴ − x³ − x² − x − 1.

Since p(1) = −5 and p(2) = 1, continuity supplies a real root γ in (1,2).
The monic rational-root theorem would make any rational root an integer.
There is no integer in (1,2), so γ is irrational.

Define

    cᵢ = γ⁻¹ + γ⁻² + ⋯ + γ⁻⁽ⁱ⁺¹⁾,       0 ≤ i ≤ 5.

The equation p(γ)=0 gives c₅=1. Thus

    0 < c₀ < c₁ < ⋯ < c₅ = 1,
    γc₀ = 1,     γcᵢ = 1 + cᵢ₋₁ (i ≥ 1).

Writing S=Σcᵢ and summing these identities gives (γ−1)S=5. Hence S>5.
Set wᵢ=1−cᵢ. These coefficients are nonnegative, and q=Σwᵢ=6−S satisfies
0 ≤ q < 1.

### 2. An integer recurrence with vanishing absolute error

Set U₀=⋯=U₅=1 and Uₙ₊₆=Uₙ+⋯+Uₙ₊₅. All Uₙ are integers congruent to 1
modulo 5: the induction step adds six residues equal to 1.

For any sequence u satisfying that recurrence, put

    Wₙ(u) = Σᵢ₌₀⁵ cᵢuₙ₊ᵢ.

Using the coefficient identities gives Wₙ₊₁(u)=γWₙ(u). In particular
Wₙ(U)=Sγⁿ. The geometric sequence uₙ=γⁿ satisfies the same recurrence,
and its initial weighted sum T=Σcᵢγⁱ is positive.

Let C=S/T>0 and eₙ=Uₙ−Cγⁿ. Its weighted sum is zero for every n. Subtracting
this weighted-sum identity from its six-term recurrence gives

    eₙ₊₆ = Σᵢ₌₀⁵ wᵢeₙ₊ᵢ.

This implies eₙ→0. Indeed, choose M bounding |e₀|,...,|e₅|. Nonnegativity
of the weights and Σwᵢ=q<1 first bound every term by M. More generally,
an induction shows |eₙ|≤Mqᵏ for every n≥6k: if all terms from 6k onward
have bound Mqᵏ, the displayed recurrence bounds each term from 6(k+1)
onward by Mqᵏ⁺¹. As k tends to infinity these bounds tend to zero.

### 3. Fractional parts stay in a small positive interval

Choose N sufficiently large that |Uₙ−Cγⁿ|<1/4 for every n≥N, and put
η=Cγᴺ/5>0. For every integer j≥1, write Uₙ=5k+1 with n=N+j. Then

    ηγʲ = k + 1/5 + (Cγⁿ−Uₙ)/5.

The last error has absolute value less than 1/20. Consequently

    3/20 < fract(ηγʲ) < 1/4     for every j≥1.

This is the unconditional parameter witness formalized in
`Erdos354Parameters.small_fractional_parts_exist`.

### 4. Both floor sequences are even

Set α=2ηγ and β=α(1+γ). Both are positive. Their ratio 1/(1+γ) is
irrational, since a rational value would make γ rational.

For any n≥0, let x=ηγⁿ⁺¹ and y=ηγⁿ⁺². Their fractional parts belong to
(3/20,1/4). Therefore floor(2x)=2floor(x), and
floor(2(x+y))=2(floor(x)+floor(y)), because
0<2(fract(x)+fract(y))<1.

These are precisely floor(αγⁿ) and floor(βγⁿ). Thus every term of their
interleaving is even, and every finite indexed sum is even. Arbitrarily
large odd integers cannot be represented, so the interleaving is incomplete.

The final unconditional witness is `Erdos354Parameters.universal_counterexample`.
`Erdos354Full.full_solution` combines it with statements 1 and 2. The Lean
source uses only Mathlib and the explicitly included common definitions;
no unproved parameter-existence hypothesis is imported.
