/-
The statement and its two definitions are from Google DeepMind's
FormalConjectures/OEIS/60841.lean (Apache License 2.0).
Source: https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/OEIS/60841.lean
-/
import Mathlib

/-!
# Wilson's A060841 integrality conjecture

Authors: Jensen Kohlmeyer and Liam Kruer.
Developed with AI assistance from OpenAI Codex.

The final theorem `OeisA60841.conjecture1` has exactly the type of the
integrality conjecture in Google DeepMind's source. Its matrix and exceptional
set definitions are reproduced below. This file imports only Mathlib.

Proof outline:
* Factor the gcd matrix through the divisibility matrix and Euler's totient.
* Deduce that the reciprocal determinant is (n!)² / ∏_{k=1}^n φ(k).
* Use the primes 3,5,7,11,13,17,19,23,29,31,37,41 to prove that its
  2-adic valuation is negative for every n ≥ 120.
* Check all remaining n by exact reduction in Lean's kernel.

Checked with Lean 4.33.1 and Mathlib commit
0df444a360eaa60ab8c11dca51a86af692955474.
The final axiom audit uses only propext, Classical.choice, and Quot.sound.
-/

namespace OeisA60841

/-- The matrix from the original conjecture. -/
def lcmMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun i j : Fin n ↦ 1 / ((Nat.lcm (i.val + 1) (j.val + 1) : ℚ))

/-- The exceptional set from the original conjecture. -/
def integerDetN : Set ℕ :=
  Set.Icc 1 34 ∪ {36, 38}

end OeisA60841

set_option maxHeartbeats 800000

open scoped BigOperators

namespace WilsonA060841

open Finset

private lemma sum_totient_shift (m n : ℕ) (hm : 0 < m) (hmn : m ≤ n) :
    (∑ d ∈ range n, if d + 1 ∣ m then (d + 1).totient else 0) = m := by
  let f : ℕ → ℕ := fun d => if d ∣ m then d.totient else 0
  have hzero : f 0 = 0 := by simp [f]
  have hext : (∑ d ∈ range (m + 1), f d) = ∑ d ∈ range (n + 1), f d := by
    apply sum_subset (range_mono (by omega))
    intro d hd hdm
    have hmd : m < d := by simpa using hdm
    have hnot : ¬ d ∣ m := fun h => (not_le_of_gt hmd) (Nat.le_of_dvd hm h)
    simp [f, hnot]
  calc
    (∑ d ∈ range n, if d + 1 ∣ m then (d + 1).totient else 0) =
        ∑ d ∈ range (n + 1), f d := by
      rw [sum_range_succ']
      simp [f, hzero]
    _ = ∑ d ∈ range (m + 1), f d := hext.symm
    _ = m := by simpa [f, sum_filter] using Nat.sum_totient' m

private def divisibilityMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => if j.val + 1 ∣ i.val + 1 then 1 else 0

private def gcdMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => Nat.gcd (i.val + 1) (j.val + 1)

private lemma divisibilityMatrix_det (n : ℕ) : (divisibilityMatrix n).det = 1 := by
  have htri : (divisibilityMatrix n).IsLowerTriangular := by
    intro i j hij
    have hlt : i.val < j.val := hij
    have hnot : ¬ j.val + 1 ∣ i.val + 1 := by
      intro h
      have := Nat.le_of_dvd (Nat.succ_pos i.val) h
      omega
    simp [divisibilityMatrix, hnot]
  rw [Matrix.det_of_isLowerTriangular _ htri]
  simp [divisibilityMatrix]

/-- The classical divisibility-matrix factorization of the gcd matrix. -/
private lemma gcdMatrix_factor (n : ℕ) :
    gcdMatrix n = divisibilityMatrix n *
      Matrix.diagonal (fun i : Fin n => ((i.val + 1).totient : ℚ)) *
      (divisibilityMatrix n).transpose := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
  change (Nat.gcd (i.val + 1) (j.val + 1) : ℚ) = _
  have hsum := sum_totient_shift (Nat.gcd (i.val + 1) (j.val + 1)) n
    (Nat.gcd_pos_of_pos_left _ (Nat.succ_pos _))
    (le_trans (Nat.gcd_le_left _ (Nat.succ_pos _)) (Nat.succ_le_of_lt i.isLt))
  have hsumQ : (∑ d ∈ range n,
      if d + 1 ∣ Nat.gcd (i.val + 1) (j.val + 1)
      then ((d + 1).totient : ℚ) else 0) = Nat.gcd (i.val + 1) (j.val + 1) := by
    exact_mod_cast hsum
  rw [← hsumQ, ← Fin.sum_univ_eq_sum_range]
  apply sum_congr rfl
  intro d hd
  simp only [divisibilityMatrix, Nat.dvd_gcd_iff]
  split_ifs <;> simp_all

private lemma gcdMatrix_det (n : ℕ) :
    (gcdMatrix n).det = ∏ i : Fin n, ((i.val + 1).totient : ℚ) := by
  rw [gcdMatrix_factor, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal,
    Matrix.det_transpose, divisibilityMatrix_det]
  simp

private def totientProduct (n : ℕ) : ℕ :=
  ∏ k ∈ range n, (k + 1).totient

private lemma totientProduct_pos (n : ℕ) : 0 < totientProduct n := by
  apply prod_pos
  intro k hk
  exact Nat.totient_pos.mpr (by omega)

private lemma determinant_formula (n : ℕ) :
    (OeisA60841.lcmMatrix n).det =
      (totientProduct n : ℚ) / (n.factorial : ℚ)^2 := by
  let D : Matrix (Fin n) (Fin n) ℚ := Matrix.diagonal (fun i => (i.val + 1 : ℕ))
  have hf : gcdMatrix n = D * OeisA60841.lcmMatrix n * D := by
    ext i j
    simp only [D, Matrix.mul_diagonal, Matrix.diagonal_mul]
    change (Nat.gcd (i.val + 1) (j.val + 1) : ℚ) =
      (i.val + 1 : ℕ) * (1 / (Nat.lcm (i.val + 1) (j.val + 1) : ℚ)) *
      (j.val + 1 : ℕ)
    have hn : (Nat.lcm (i.val + 1) (j.val + 1) : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.lcm_ne_zero (by omega) (by omega))
    have hg := Nat.gcd_mul_lcm (i.val + 1) (j.val + 1)
    have hgq : (Nat.gcd (i.val + 1) (j.val + 1) : ℚ) *
        Nat.lcm (i.val + 1) (j.val + 1) =
        (i.val + 1 : ℕ) * (j.val + 1 : ℕ) := by exact_mod_cast hg
    field_simp
    exact hgq
  have hD : D.det = (n.factorial : ℚ) := by
    simp only [D, Matrix.det_diagonal]
    rw [Fin.prod_univ_eq_prod_range (fun k => ((k + 1 : ℕ) : ℚ))]
    exact_mod_cast (Nat.factorial_eq_prod_range_add_one n).symm
  have ht : (gcdMatrix n).det = (totientProduct n : ℚ) := by
    rw [gcdMatrix_det, Fin.prod_univ_eq_prod_range (fun k => ((k + 1).totient : ℚ))]
    simp [totientProduct]
  have he := congrArg Matrix.det hf
  rw [Matrix.det_mul, Matrix.det_mul, hD, ht] at he
  have hn : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  apply (eq_div_iff (pow_ne_zero 2 hn)).mpr
  nlinarith [he]

private lemma reciprocal_formula (n : ℕ) :
    ((OeisA60841.lcmMatrix n).det)⁻¹ =
      (n.factorial : ℚ)^2 / (totientProduct n : ℚ) := by
  rw [determinant_formula, inv_div]

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private lemma val_prod {α : Type*} (s : Finset α) (f : α → ℕ)
    (h : ∀ i ∈ s, f i ≠ 0) :
    padicValNat 2 (∏ i ∈ s, f i) = ∑ i ∈ s, padicValNat 2 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [prod_insert ha, sum_insert ha, padicValNat.mul (h a (mem_insert_self _ _))]
    · rw [ih (by aesop)]
    · exact prod_ne_zero_iff.mpr (by aesop)

private lemma factorial_valuation (n : ℕ) :
    padicValNat 2 n.factorial = ∑ k ∈ range n, padicValNat 2 (k + 1) := by
  rw [Nat.factorial_eq_prod_range_add_one]
  apply val_prod
  intros
  omega

private lemma reciprocal_valuation (n : ℕ) :
    padicValRat 2 ((OeisA60841.lcmMatrix n).det)⁻¹ =
      2 * (padicValNat 2 n.factorial : ℤ) - padicValNat 2 (totientProduct n) := by
  rw [reciprocal_formula, padicValRat.div, padicValRat.pow]
  · simp
  · exact pow_ne_zero 2 (by exact_mod_cast Nat.factorial_ne_zero n)
  · exact_mod_cast (totientProduct_pos n).ne'

private def smallPrimes : Finset ℕ := {3,5,7,11,13,17,19,23,29,31,37,41}

private lemma smallPrimes_prime {p : ℕ} (hp : p ∈ smallPrimes) : p.Prime := by
  simp only [smallPrimes, mem_insert, mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num

private lemma prime_factors_valuation (m : ℕ) (hm : 0 < m) :
    (∑ p ∈ m.primeFactors, padicValNat 2 p) = if 2 ∣ m then 1 else 0 := by
  have he : (∑ p ∈ m.primeFactors, padicValNat 2 p) =
      ∑ p ∈ m.primeFactors, if p = 2 then 1 else 0 := by
    apply sum_congr rfl
    intro p hp
    by_cases h : p = 2
    · subst p; simp
    · have : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
      simp [h, padicValNat_primes (Ne.symm h)]
  rw [he]
  simp [Nat.mem_primeFactors, hm.ne', Nat.prime_two]

/-- Retaining just twelve odd primes gives a lower bound on v₂(φ(m)). -/
private lemma totient_valuation_bound (m : ℕ) (hm : 0 < m) :
    padicValNat 2 m +
      (∑ p ∈ smallPrimes, if p ∣ m then padicValNat 2 (p - 1) else 0) ≤
      padicValNat 2 m.totient + (if 2 ∣ m then 1 else 0) := by
  have hn : ∀ p ∈ m.primeFactors, p ≠ 0 := by
    intro p hp
    exact (Nat.pos_of_mem_primeFactors hp).ne'
  have hs : ∀ p ∈ m.primeFactors, p - 1 ≠ 0 := by
    intro p hp
    have := (Nat.prime_of_mem_primeFactors hp).two_le
    omega
  have he := congrArg (padicValNat 2) (Nat.totient_mul_prod_primeFactors m)
  rw [padicValNat.mul (Nat.totient_pos.mpr hm).ne' (prod_ne_zero_iff.mpr hn),
      padicValNat.mul hm.ne' (prod_ne_zero_iff.mpr hs), val_prod _ _ hn,
      val_prod _ _ hs, prime_factors_valuation m hm] at he
  rw [he]
  gcongr
  rw [← sum_filter]
  apply sum_le_sum_of_subset
  intro p hp
  rcases mem_filter.mp hp with ⟨hp, hd⟩
  exact Nat.mem_primeFactors.mpr ⟨smallPrimes_prime hp, hd, hm.ne'⟩

private lemma count_multiples_weighted (n p w : ℕ) :
    (∑ k ∈ range n, if p ∣ k + 1 then w else 0) = w * (n / p) := by
  calc
    _ = w * (∑ k ∈ range n, if p ∣ k + 1 then 1 else 0) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro k hk
      split_ifs <;> simp
    _ = _ := by rw [sum_boole, Nat.cast_id, Nat.card_multiples]

private lemma summed_valuation_bound (n : ℕ) :
    padicValNat 2 n.factorial +
      (∑ p ∈ smallPrimes, padicValNat 2 (p - 1) * (n / p)) ≤
      padicValNat 2 (totientProduct n) + n / 2 := by
  have h := sum_le_sum (s := range n) (fun k hk =>
    totient_valuation_bound (k + 1) (by omega))
  simp only [sum_add_distrib] at h
  rw [← factorial_valuation, sum_comm] at h
  simp only [count_multiples_weighted, one_mul] at h
  have ht : (∑ k ∈ range n, padicValNat 2 (k + 1).totient) =
      padicValNat 2 (totientProduct n) := by
    symm
    apply val_prod
    intro k hk
    exact (Nat.totient_pos.mpr (by omega)).ne'
  simpa only [ht] using h

private lemma fixed_prime_sum (n : ℕ) :
    (∑ p ∈ smallPrimes, padicValNat 2 (p - 1) * (n / p)) =
      n / 3 + 2 * (n / 5) + n / 7 + n / 11 + 2 * (n / 13) +
      4 * (n / 17) + n / 19 + n / 23 + 2 * (n / 29) + n / 31 +
      2 * (n / 37) + 3 * (n / 41) := by
  have h2 : padicValNat 2 2 = 1 := by decide +kernel
  have h4 : padicValNat 2 4 = 2 := by decide +kernel
  have h6 : padicValNat 2 6 = 1 := by decide +kernel
  have h10 : padicValNat 2 10 = 1 := by decide +kernel
  have h12 : padicValNat 2 12 = 2 := by decide +kernel
  have h16 : padicValNat 2 16 = 4 := by decide +kernel
  have h18 : padicValNat 2 18 = 1 := by decide +kernel
  have h22 : padicValNat 2 22 = 1 := by decide +kernel
  have h28 : padicValNat 2 28 = 2 := by decide +kernel
  have h30 : padicValNat 2 30 = 1 := by decide +kernel
  have h36 : padicValNat 2 36 = 2 := by decide +kernel
  have h40 : padicValNat 2 40 = 3 := by decide +kernel
  norm_num [smallPrimes, h2, h4, h6, h10, h12, h16, h18, h22, h28, h30, h36, h40]
  ring

private lemma floor_lower (n p : ℕ) (hp : 0 < p) :
    (n : ℚ) / p - 1 ≤ (n / p : ℕ) := by
  have h : (n : ℚ) < (p : ℚ) * ((n / p : ℕ) + 1) := by
    exact_mod_cast Nat.lt_mul_div_succ n hp
  have hpq : (0 : ℚ) < p := by exact_mod_cast hp
  have hh : (n : ℚ) / p < (n / p : ℕ) + 1 :=
    (div_lt_iff₀ hpq).mpr (by nlinarith [h])
  linarith

/-- The chosen weights sum to 21, and their weighted reciprocals exceed 3/2. -/
private lemma fixed_prime_sum_bound (n : ℕ) (hn : 120 ≤ n) :
    n + n / 2 ≤ ∑ p ∈ smallPrimes, padicValNat 2 (p - 1) * (n / p) := by
  rw [fixed_prime_sum]
  have h3 := floor_lower n 3 (by norm_num)
  have h5 := floor_lower n 5 (by norm_num)
  have h7 := floor_lower n 7 (by norm_num)
  have h11 := floor_lower n 11 (by norm_num)
  have h13 := floor_lower n 13 (by norm_num)
  have h17 := floor_lower n 17 (by norm_num)
  have h19 := floor_lower n 19 (by norm_num)
  have h23 := floor_lower n 23 (by norm_num)
  have h29 := floor_lower n 29 (by norm_num)
  have h31 := floor_lower n 31 (by norm_num)
  have h37 := floor_lower n 37 (by norm_num)
  have h41 := floor_lower n 41 (by norm_num)
  have hb : (255691624204897 / 152125131763605 : ℚ) * n - 21 ≤
      ((n / 3 : ℕ) : ℚ) + (2 : ℚ) * ((n / 5 : ℕ) : ℚ) + ((n / 7 : ℕ) : ℚ) + ((n / 11 : ℕ) : ℚ)
        + (2 : ℚ) * ((n / 13 : ℕ) : ℚ) + (4 : ℚ) * ((n / 17 : ℕ) : ℚ) + ((n / 19 : ℕ) : ℚ)
        + ((n / 23 : ℕ) : ℚ) + (2 : ℚ) * ((n / 29 : ℕ) : ℚ) + ((n / 31 : ℕ) : ℚ) + (2 : ℚ) * ((n / 37 : ℕ) : ℚ)
        + (3 : ℚ) * ((n / 41 : ℕ) : ℚ) := by
    linear_combination 1 * h3 + 2 * h5 + 1 * h7 + 1 * h11 + 2 * h13 + 4 * h17
      + 1 * h19 + 1 * h23 + 2 * h29 + 1 * h31 + 2 * h37 + 3 * h41
  have hh : ((n / 2 : ℕ) : ℚ) ≤ (n : ℚ) / 2 := Nat.cast_div_le
  have hnq : (120 : ℚ) ≤ n := by exact_mod_cast hn
  have he : (n : ℚ) + (n / 2 : ℕ) ≤
      ((n / 3 : ℕ) : ℚ) + (2 : ℚ) * ((n / 5 : ℕ) : ℚ) + ((n / 7 : ℕ) : ℚ) + ((n / 11 : ℕ) : ℚ)
        + (2 : ℚ) * ((n / 13 : ℕ) : ℚ) + (4 : ℚ) * ((n / 17 : ℕ) : ℚ) + ((n / 19 : ℕ) : ℚ)
        + ((n / 23 : ℕ) : ℚ) + (2 : ℚ) * ((n / 29 : ℕ) : ℚ) + ((n / 31 : ℕ) : ℚ) + (2 : ℚ) * ((n / 37 : ℕ) : ℚ)
        + (3 : ℚ) * ((n / 41 : ℕ) : ℚ) := by linarith
  exact_mod_cast he

private lemma large_valuation_negative (n : ℕ) (hn : 120 ≤ n) :
    padicValRat 2 ((OeisA60841.lcmMatrix n).det)⁻¹ < 0 := by
  have hs := summed_valuation_bound n
  have hf := fixed_prime_sum_bound n hn
  have hv := padicValNat_factorial_lt_of_ne_zero 2 (n := n) (by omega)
  rw [reciprocal_valuation]
  omega

private lemma large_nonintegral (n : ℕ) (hn : 120 ≤ n) :
    ((OeisA60841.lcmMatrix n).det)⁻¹.den ≠ 1 := by
  have hneg := large_valuation_negative n hn
  intro hden
  have hnonneg : 0 ≤ padicValRat 2 ((OeisA60841.lcmMatrix n).det)⁻¹ := by
    rw [← (Rat.den_eq_one_iff _).mp hden, padicValRat.of_int]
    positivity
  omega

set_option maxRecDepth 10000 in
/-- All 119 remaining cases are checked by kernel reduction, without native_decide. -/
private lemma small_cases : ∀ n : Fin 120, 1 ≤ n.val →
    (((n.val.factorial : ℚ)^2 / (totientProduct n.val : ℚ)).den = 1 ↔
      n.val ∈ OeisA60841.integerDetN) := by
  simp only [OeisA60841.integerDetN, Set.mem_union, Set.mem_Icc, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  decide +kernel

set_option maxRecDepth 10000 in
private lemma small_negative_valuation : ∀ n : Fin 120, 39 ≤ n.val →
    2 * padicValNat 2 n.val.factorial < padicValNat 2 (totientProduct n.val) := by
  decide +kernel

/-- The stronger denominator assertion stated in the companion paper:
the reciprocal determinant has negative 2-adic valuation for every n ≥ 39. -/
theorem two_adic_negative {n : ℕ} (hn : 39 ≤ n) :
    padicValRat 2 ((OeisA60841.lcmMatrix n).det)⁻¹ < 0 := by
  by_cases hsmall : n < 120
  · have hv := small_negative_valuation ⟨n, hsmall⟩ hn
    rw [reciprocal_valuation]
    change 2 * padicValNat 2 n.factorial < padicValNat 2 (totientProduct n) at hv
    omega
  · exact large_valuation_negative n (by omega)

/-- Wilson's A060841 integrality conjecture, with the exact matrix and
exceptional set from Google DeepMind's formal statement. -/
theorem wilson_integrality :
    ∀ n : ℕ, 1 ≤ n →
      (((OeisA60841.lcmMatrix n).det)⁻¹.den = 1 ↔ n ∈ OeisA60841.integerDetN) := by
  intro n hn
  by_cases hsmall : n < 120
  · rw [reciprocal_formula]
    exact small_cases ⟨n, hsmall⟩ hn
  · have hlarge : 120 ≤ n := by omega
    have hout : n ∉ OeisA60841.integerDetN := by
      simp only [OeisA60841.integerDetN, Set.mem_union, Set.mem_Icc, Set.mem_insert_iff,
        Set.mem_singleton_iff]
      omega
    exact iff_of_false (large_nonintegral n hlarge) hout

end WilsonA060841

namespace OeisA60841

/-- Robert G. Wilson V's integrality conjecture (OEIS A060841), in exactly
Google DeepMind's formulation. -/
theorem conjecture1 :
    ∀ n : ℕ, 1 ≤ n → (((lcmMatrix n).det)⁻¹.den = 1 ↔ n ∈ integerDetN) :=
  WilsonA060841.wilson_integrality

end OeisA60841

#print axioms OeisA60841.conjecture1

#print axioms WilsonA060841.two_adic_negative
