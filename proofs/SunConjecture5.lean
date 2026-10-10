/-
Copyright (c) 2026 Jensen Kohlmeyer and Liam Kruer.
Released under the Apache 2.0 license.
AI assistance: OpenAI Codex.
-/
import FormalConjectures.OEIS.«160324»
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Sun's A160324 Conjecture 5

An infinite counterexample family for orders 34, 35, 36.
The final theorem negates the exact type of the repository's conjecture.
-/

set_option maxHeartbeats 800000

namespace SunConjecture5

lemma bad_prime (a : ℕ) (ha : 0 < a) (ha8 : a % 8 = 7) :
    ∃ p : ℕ, p.Prime ∧ jacobiSym (-2) p = -1 ∧ Odd (a.factorization p) := by
  obtain ⟨s, r, hs, hr, heq, hsf⟩ := Nat.sq_mul_squarefree_of_pos ha
  have hs8 : s % 8 = 7 := by
    have hm := congrArg (fun n : ℕ => n % 8) heq
    rw [ha8] at hm
    have hr8 := Nat.mod_lt r (by decide : 0 < 8)
    interval_cases h₁ : r % 8 <;>
      norm_num [Nat.mul_mod, Nat.pow_mod, h₁] at hm <;> omega
  have hso : Odd s := by
    rw [Nat.odd_iff]
    omega
  have hjs : jacobiSym (-2) s = -1 := by
    rw [jacobiSym.at_neg_two hso, ZMod.χ₈'_nat_eq_if_mod_eight]
    have hs2 : s % 2 = 1 := by omega
    simp [hs2, hs8]
  obtain ⟨p, hp, hps, hjp⟩ := jacobiSym.eq_neg_one_at_prime_divisor_of_eq_neg_one hjs
  have hsp : s.factorization p = 1 := by
    have hlow := (hp.dvd_iff_one_le_factorization (by omega : s ≠ 0)).mp hps
    have hupp := hsf.natFactorization_le_one p
    omega
  refine ⟨p, hp, hjp, ?_⟩
  have hv : a.factorization p = 2 * r.factorization p + 1 := by
    rw [← heq, Nat.factorization_mul (pow_ne_zero _ (by omega)) (by omega),
      Nat.factorization_pow]
    simp [hsp]
  rw [hv]
  exact ⟨r.factorization p, by omega⟩

lemma norm_even_valuation (p : ℕ) (hp : p.Prime) (hjp : jacobiSym (-2) p = -1)
    (u v : ℤ) (hn : u ^ 2 + 2 * v ^ 2 ≠ 0) :
    Even ((u ^ 2 + 2 * v ^ 2).natAbs.factorization p) := by
  have hg : 0 < u.gcd v := by
    rw [Int.gcd_pos_iff]
    by_contra h
    push Not at h
    simp [h.1, h.2] at hn
  obtain ⟨g, u', v', hg, hcop, hu, hv⟩ := Int.exists_gcd_one' hg
  have hprim : ¬ p ∣ (u' ^ 2 + 2 * v' ^ 2).natAbs := by
    intro hd
    have hd' : (p : ℤ) ∣ u' ^ 2 - (-2) * v' ^ 2 := by
      convert Int.natCast_dvd.mpr hd using 1
      ring
    let : Fact p.Prime := ⟨hp⟩
    obtain ⟨hpu, hpv⟩ := jacobiSym.prime_dvd_of_eq_neg_one hjp hd'
    have hpg : p ∣ u'.gcd v' := Nat.dvd_gcd (Int.natCast_dvd.mp hpu)
      (Int.natCast_dvd.mp hpv)
    rw [hcop] at hpg
    exact hp.ne_one (Nat.dvd_one.mp hpg)
  have hsplit : u ^ 2 + 2 * v ^ 2 = (g : ℤ) ^ 2 * (u' ^ 2 + 2 * v' ^ 2) := by
    rw [hu, hv]
    ring
  have hprim0 : u' ^ 2 + 2 * v' ^ 2 ≠ 0 := by
    intro h
    simp [hsplit, h] at hn
  have hnat : (u ^ 2 + 2 * v ^ 2).natAbs = g ^ 2 * (u' ^ 2 + 2 * v' ^ 2).natAbs := by
    rw [hsplit, Int.natAbs_mul, Int.natAbs_pow]
    simp
  rw [hnat, Nat.factorization_mul (pow_ne_zero _ (by omega))
    (Int.natAbs_ne_zero.mpr hprim0), Nat.factorization_pow]
  simp [Nat.factorization_eq_zero_of_not_dvd hprim]

lemma jacobi_two : jacobiSym (-2) 2 = 0 := by
  apply jacobiSym.eq_zero_iff.mpr
  norm_num

lemma jacobi_seventeen : jacobiSym (-2) 17 = 1 := by
  rw [jacobiSym.at_neg_two (by decide : Odd 17), ZMod.χ₈'_nat_eq_if_mod_eight]
  norm_num

lemma jacobi_1019 : jacobiSym (-2) 1019 = 1 := by
  rw [jacobiSym.at_neg_two (by decide : Odd 1019), ZMod.χ₈'_nat_eq_if_mod_eight]
  norm_num

lemma bad_prime_not_dvd_constants (p : ℕ) (hp : p.Prime)
    (hjp : jacobiSym (-2) p = -1) : ¬ p ∣ 8 ∧ ¬ p ∣ 544 ∧ ¬ p ∣ 4 := by
  have hp2 : p ≠ 2 := by
    intro h
    rw [h, jacobi_two] at hjp
    norm_num at hjp
  have hp17 : p ≠ 17 := by
    intro h
    rw [h, jacobi_seventeen] at hjp
    norm_num at hjp
  have hn2 : ¬ p ∣ 2 := by
    intro h
    have he := (Nat.prime_two.dvd_iff_eq hp.ne_one).mp h
    exact hp2 he.symm
  have hn17 : ¬ p ∣ 17 := by
    intro h
    have he := ((by norm_num : Nat.Prime 17).dvd_iff_eq hp.ne_one).mp h
    exact hp17 he.symm
  have hn8 : ¬ p ∣ 8 := by
    intro h
    apply hn2
    exact hp.dvd_of_dvd_pow (show p ∣ (2 : ℕ) ^ 3 by norm_num; exact h)
  have hn32 : ¬ p ∣ 32 := by
    intro h
    apply hn2
    exact hp.dvd_of_dvd_pow (show p ∣ (2 : ℕ) ^ 5 by norm_num; exact h)
  have hn544 : ¬ p ∣ 544 := by
    intro h
    have hd : p ∣ 32 * 17 := by norm_num at h ⊢; exact h
    exact (hp.dvd_mul.mp hd).elim hn32 hn17
  have hn4 : ¬ p ∣ 4 := by
    intro h
    apply hn2
    exact hp.dvd_of_dvd_pow (show p ∣ (2 : ℕ) ^ 2 by norm_num; exact h)
  exact ⟨hn8, hn544, hn4⟩

lemma quadratic_obstruction (T X Y Z : ℤ)
    (hT : 0 < T) (hT32 : T % 32 = 27) (hX32 : X % 32 = 17)
    (hY2 : Y % 2 = 1)
    (hprimes : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ T → jacobiSym (-2) p ≠ -1)
    (hq : T ^ 2 = 561 * X ^ 2 + 136 * Y ^ 2 + 2112 * Z ^ 2) : False := by
  let A := 2 * T + 34 * X + 64 * Z
  let B := 2 * T - 34 * X - 64 * Z
  let N := Y ^ 2 + 2 * (X - 2 * Z) ^ 2
  have hY0 : Y ≠ 0 := by omega
  have hN : 0 < N := by
    dsimp [N]
    nlinarith [sq_pos_of_ne_zero hY0, sq_nonneg (X - 2 * Z)]
  have hAB : A * B = 544 * N := by
    dsimp [A, B, N]
    linear_combination 4 * hq
  have hsum : A + B = 4 * T := by dsimp [A, B]; ring
  have hABpos : 0 < A * B := by rw [hAB]; omega
  have hApos : 0 < A := by
    rcases mul_pos_iff.mp hABpos with h | h
    · exact h.1
    · omega
  have hBpos : 0 < B := by
    rcases mul_pos_iff.mp hABpos with h | h
    · exact h.2
    · omega
  have hA64 : A % 64 = 56 := by dsimp [A]; omega
  let a := (A / 8).toNat
  have hacast : (a : ℤ) = A / 8 := by
    exact Int.toNat_of_nonneg (by omega)
  have hAa : A = 8 * (a : ℤ) := by omega
  have ha : 0 < a := by omega
  have ha8 : a % 8 = 7 := by omega
  obtain ⟨p, hp, hjp, hodd⟩ := bad_prime a ha ha8
  obtain ⟨hn8, hn544, hn4⟩ := bad_prime_not_dvd_constants p hp hjp
  have hpa : p ∣ a := by
    apply (hp.dvd_iff_one_le_factorization (by omega)).mpr
    obtain ⟨r, hr⟩ := hodd
    omega
  have hpA : (p : ℤ) ∣ A := by
    rw [hAa]
    exact dvd_mul_of_dvd_right (Int.ofNat_dvd.mpr hpa) 8
  have hnB : ¬ p ∣ B.natAbs := by
    intro hd
    have hpB := Int.natCast_dvd.mpr hd
    have hpS : (p : ℤ) ∣ 4 * T := by
      rw [← hsum]
      exact dvd_add hpA hpB
    have hpS' : p ∣ 4 * T.natAbs := by
      simpa [Int.natAbs_mul] using Int.natCast_dvd.mp hpS
    rcases hp.dvd_mul.mp hpS' with h4 | hpT
    · exact hn4 h4
    · exact hprimes p hp (Int.natCast_dvd.mpr hpT) hjp
  have hAnat : A.natAbs = 8 * a := by
    rw [hAa, Int.natAbs_mul]
    simp
  have hAfac : A.natAbs.factorization p = a.factorization p := by
    rw [hAnat, Nat.factorization_mul (by decide) (by omega)]
    simp [Nat.factorization_eq_zero_of_not_dvd hn8]
  have hprod : A.natAbs * B.natAbs = 544 * N.natAbs := by
    simpa [Int.natAbs_mul] using congrArg Int.natAbs hAB
  have hval := congrArg (fun n : ℕ => n.factorization p) hprod
  rw [Nat.factorization_mul (Int.natAbs_ne_zero.mpr (ne_of_gt hApos))
      (Int.natAbs_ne_zero.mpr (ne_of_gt hBpos)),
    Nat.factorization_mul (by decide) (Int.natAbs_ne_zero.mpr (ne_of_gt hN))] at hval
  simp only [Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hnB,
    Nat.factorization_eq_zero_of_not_dvd hn544, add_zero, zero_add, hAfac] at hval
  have heven := norm_even_valuation p hp hjp Y (X - 2 * Z) (ne_of_gt hN)
  change Even (N.natAbs.factorization p) at heven
  obtain ⟨r, hr⟩ := hodd
  obtain ⟨s, hs⟩ := heven
  omega

/-- The prime power used in the explicit counterexample family. -/
def T (k : ℕ) : ℕ := 1019 ^ (80 * k + 1)

/-- The natural-number counterexamples; exact divisibility is proved below. -/
def counterexample (k : ℕ) : ℕ := (T k ^ 2 - 392089) / 35904

lemma T_mod (k : ℕ) : Nat.ModEq 35904 (T k) 1019 := by
  have hperiod : Nat.ModEq 35904 ((1019 : ℕ) ^ 80) 1 := by
    norm_num [Nat.ModEq]
  have hpow := hperiod.pow k
  simp only [one_pow] at hpow
  unfold T
  rw [pow_add, pow_mul, pow_one]
  simpa using hpow.mul (Nat.ModEq.refl 1019)

lemma T_growth (k : ℕ) : 1019 * (k + 1) ≤ T k := by
  have hsmall : ∀ j : ℕ, j + 1 ≤ (1019 : ℕ) ^ j := by
    intro j
    induction j with
    | zero => norm_num
    | succ j ih =>
      rw [pow_succ]
      nlinarith
  have hmono : (1019 : ℕ) ^ (k + 1) ≤ T k := by
    unfold T
    gcongr <;> omega
  have hmul : 1019 * (k + 1) ≤ (1019 : ℕ) ^ (k + 1) := by
    rw [pow_succ]
    nlinarith [hsmall k]
  exact hmul.trans hmono

lemma T_lower (k : ℕ) : 1019 ≤ T k := by
  have h := T_growth k
  nlinarith

lemma counterexample_identity (k : ℕ) :
    35904 * counterexample k + 392089 = T k ^ 2 := by
  have hsq : 392089 ≤ T k ^ 2 := by nlinarith [T_lower k]
  have hmod := (T_mod k).pow 2
  change (T k ^ 2) % 35904 = (1019 ^ 2) % 35904 at hmod
  norm_num at hmod
  unfold counterexample
  omega

lemma counterexample_positive (k : ℕ) : 0 < counterexample k := by
  have h := counterexample_identity k
  have ht := T_lower k
  nlinarith

lemma counterexample_large (k : ℕ) : k ≤ counterexample k := by
  have hmul := Nat.mul_le_mul (T_growth k) (T_lower k)
  have hi := counterexample_identity k
  nlinarith

lemma counterexample_zero : counterexample 0 = 18 := by
  norm_num [counterexample, T]

lemma T_mod_thirty_two (k : ℕ) : (T k : ℤ) % 32 = 27 := by
  have hm := T_mod k
  change T k % 35904 = 1019 % 35904 at hm
  norm_num at hm
  have hn : T k % 32 = 27 := by omega
  exact_mod_cast hn

lemma T_prime_divisors (k p : ℕ) (hp : p.Prime) (hd : (p : ℤ) ∣ (T k : ℤ)) :
    jacobiSym (-2) p ≠ -1 := by
  have hd' : p ∣ 1019 ^ (80 * k + 1) := Int.ofNat_dvd.mp hd
  have hp1019 : p ∣ 1019 := hp.dvd_of_dvd_pow hd'
  have heq : p = 1019 :=
    ((by norm_num : Nat.Prime 1019).dvd_iff_eq hp.ne_one).mp hp1019 |>.symm
  rw [heq, jacobi_1019]
  norm_num

lemma cast_triangle (x : ℕ) :
    2 * ((x * (x - 1) / 2 : ℕ) : ℤ) = (x : ℤ) * ((x : ℤ) - 1) := by
  have hd := Nat.mul_div_cancel' (Nat.two_dvd_mul_sub_one x)
  have hc : (2 : ℤ) * ((x * (x - 1) / 2 : ℕ) : ℤ) =
      ((x * (x - 1) : ℕ) : ℤ) := by exact_mod_cast hd
  rw [hc]
  by_cases hx : x = 0
  · simp [hx]
  · rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ x)]
    norm_num

lemma twice_polygonal (j x : ℕ) (hj : 2 ≤ j) :
    2 * (OeisA160324.polygonalNumber j x : ℤ) =
      ((j : ℤ) - 2) * (x : ℤ) * ((x : ℤ) - 1) + 2 * (x : ℤ) := by
  unfold OeisA160324.polygonalNumber
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hj]
  have htri := cast_triangle x
  change 2 * (((j : ℤ) - 2) * ((x * (x - 1) / 2 : ℕ) : ℤ) + (x : ℤ)) = _
  linear_combination ((j : ℤ) - 2) * htri

lemma completed_squares (x y z : ℕ) :
    35904 * ((OeisA160324.polygonalNumber 34 x : ℤ) +
      (OeisA160324.polygonalNumber 35 y : ℤ) +
      (OeisA160324.polygonalNumber 36 z : ℤ)) + 392089 =
      561 * (32 * (x : ℤ) - 15) ^ 2 + 136 * (66 * (y : ℤ) - 31) ^ 2 +
        2112 * (17 * (z : ℤ) - 8) ^ 2 := by
  have hx := twice_polygonal 34 x (by decide)
  have hy := twice_polygonal 35 y (by decide)
  have hz := twice_polygonal 36 z (by decide)
  norm_num at hx hy hz
  linear_combination 17952 * hx + 17952 * hy + 17952 * hz

theorem counterexample_not_representable (k : ℕ) :
    ¬ ∃ x y z : ℕ, counterexample k = OeisA160324.polygonalNumber 34 x +
      OeisA160324.polygonalNumber 35 y + OeisA160324.polygonalNumber 36 z := by
  rintro ⟨x, y, z, hrepr⟩
  have hnat := counterexample_identity k
  have hint : 35904 * (counterexample k : ℤ) + 392089 = (T k : ℤ) ^ 2 := by
    exact_mod_cast hnat
  have hrepr' : (counterexample k : ℤ) = (OeisA160324.polygonalNumber 34 x : ℤ) +
      (OeisA160324.polygonalNumber 35 y : ℤ) +
      (OeisA160324.polygonalNumber 36 z : ℤ) := by exact_mod_cast hrepr
  have hq : (T k : ℤ) ^ 2 = 561 * (32 * (x : ℤ) - 15) ^ 2 +
      136 * (66 * (y : ℤ) - 31) ^ 2 + 2112 * (17 * (z : ℤ) - 8) ^ 2 := by
    rw [← hint, hrepr']
    exact completed_squares x y z
  exact quadratic_obstruction (T k) (32 * (x : ℤ) - 15) (66 * (y : ℤ) - 31)
    (17 * (z : ℤ) - 8) (by exact_mod_cast (show 0 < T k by have := T_lower k; omega))
    (T_mod_thirty_two k) (by omega) (by omega) (T_prime_divisors k) hq

/-- The closed formula stated in the paper, with natural-number subtraction and division. -/
lemma counterexample_formula (k : ℕ) :
    counterexample k = (1019 ^ (160 * k + 2) - 392089) / 35904 := by
  unfold counterexample T
  rw [← pow_mul]
  have he : (80 * k + 1) * 2 = 160 * k + 2 := by omega
  rw [he]

/-- Polygonal numbers extended to arbitrary integer indices. -/
def integerPolygonal (j : ℕ) (x : ℤ) : ℤ :=
  ((j : ℤ) - 2) * (x * (x - 1) / 2) + x

lemma integer_triangle (x : ℤ) : 2 * (x * (x - 1) / 2) = x * (x - 1) := by
  have hm : (x * (x - 1)) % 2 = 0 := by
    rcases (show x % 2 = 0 ∨ x % 2 = 1 by omega) with hx | hx <;>
      norm_num [Int.mul_emod, Int.sub_emod, hx]
  omega

lemma twice_integer_polygonal (j : ℕ) (x : ℤ) :
    2 * integerPolygonal j x = ((j : ℤ) - 2) * x * (x - 1) + 2 * x := by
  unfold integerPolygonal
  linear_combination ((j : ℤ) - 2) * integer_triangle x

lemma integer_completed_squares (x y z : ℤ) :
    35904 * (integerPolygonal 34 x + integerPolygonal 35 y + integerPolygonal 36 z) +
      392089 = 561 * (32 * x - 15) ^ 2 + 136 * (66 * y - 31) ^ 2 +
      2112 * (17 * z - 8) ^ 2 := by
  have hx := twice_integer_polygonal 34 x
  have hy := twice_integer_polygonal 35 y
  have hz := twice_integer_polygonal 36 z
  norm_num at hx hy hz
  linear_combination 17952 * hx + 17952 * hy + 17952 * hz

theorem counterexample_not_representable_integer (k : ℕ) :
    ¬ ∃ x y z : ℤ, (counterexample k : ℤ) =
      integerPolygonal 34 x + integerPolygonal 35 y + integerPolygonal 36 z := by
  rintro ⟨x, y, z, hrepr⟩
  have hi : 35904 * (counterexample k : ℤ) + 392089 = (T k : ℤ) ^ 2 := by
    exact_mod_cast counterexample_identity k
  have hq : (T k : ℤ) ^ 2 = 561 * (32 * x - 15) ^ 2 +
      136 * (66 * y - 31) ^ 2 + 2112 * (17 * z - 8) ^ 2 := by
    rw [← hi, hrepr]
    exact integer_completed_squares x y z
  exact quadratic_obstruction (T k) (32 * x - 15) (66 * y - 31) (17 * z - 8)
    (by exact_mod_cast (show 0 < T k by have := T_lower k; omega))
    (T_mod_thirty_two k) (by omega) (by omega) (T_prime_divisors k) hq

theorem arbitrarily_large_counterexamples (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ ¬ ∃ x y z : ℕ, n = OeisA160324.polygonalNumber 34 x +
      OeisA160324.polygonalNumber 35 y + OeisA160324.polygonalNumber 36 z := by
  exact ⟨counterexample N, counterexample_large N, counterexample_not_representable N⟩

/-- The negation of the exact repository statement, without invoking its proof. -/
theorem sun_conjecture5_false : ¬ (type_of% OeisA160324.conjecture5) := by
  intro h
  have h33 := h 33 (by decide)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp h33
  obtain ⟨n, hn, hnot⟩ := arbitrarily_large_counterexamples N
  exact hnot (hN n hn)

#print axioms sun_conjecture5_false
#print axioms counterexample_not_representable_integer
#print axioms counterexample_formula

end SunConjecture5
