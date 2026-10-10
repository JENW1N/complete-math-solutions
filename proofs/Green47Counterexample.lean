-- Solved via Jensen Kohlmeyer and Liam Kruer.

/-!
# Counterexample to the exact-containment formulation of Green 47

The statement is displayed at
https://conjectures.io/problems/green47-green-47?mode=counterexample

This proof addresses exact containment of every element in a rational quadratic
image of the integers. It does not refute the formulation allowing finitely many
exceptions. The analytic step uses Mathlib's Dirichlet theorem and dyadic summation.
-/

open Finset

namespace Green47Counterexample

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def squares (F : Type*) [Field F] [Fintype F] [DecidableEq F] : Finset F :=
  univ.image (fun x : F => x ^ 2)

lemma mem_squares (a : F) : a ∈ squares F ↔ ∃ x : F, x ^ 2 = a := by
  simp [squares]

lemma zero_mem_squares : (0 : F) ∈ squares F := by
  exact (mem_squares 0).mpr ⟨0, by simp⟩

lemma roots_sq (x : F) :
    univ.filter (fun y : F => y ^ 2 = x ^ 2) = {x, -x} := by
  ext y
  simp [sq_eq_sq_iff_eq_or_eq_neg]

omit [Fintype F] [DecidableEq F] in
lemma ne_neg_of_ne_zero (h2 : (2 : F) ≠ 0) {x : F} (hx : x ≠ 0) : x ≠ -x := by
  intro h
  have h' : (2 : F) * x = 0 := by linear_combination h
  exact (mul_ne_zero h2 hx) h'

lemma square_fiber_card (h2 : (2 : F) ≠ 0) {r : F} (hr : r ∈ squares F) :
    (univ.filter (fun x : F => x ^ 2 = r)).card = if r = 0 then 1 else 2 := by
  obtain ⟨x, rfl⟩ := (mem_squares r).mp hr
  by_cases hx : x = 0
  · subst x
    have hz : univ.filter (fun y : F => y ^ 2 = 0 ^ 2) = {0} := by
      ext y
      simp
    rw [hz]
    simp
  · rw [if_neg (pow_ne_zero 2 hx), roots_sq x, card_pair (ne_neg_of_ne_zero h2 hx)]

lemma sum_square_fibers (h2 : (2 : F) ≠ 0) (g : F → F) :
    (∑ x : F, g (x ^ 2)) = 2 * (∑ r ∈ squares F, g r) - g 0 := by
  have hf := Finset.sum_fiberwise_of_maps_to
    (s := (univ : Finset F)) (t := squares F) (g := fun x : F => x ^ 2)
    (fun x _ => (mem_squares (x ^ 2)).mpr ⟨x, rfl⟩) (fun x : F => g (x ^ 2))
  have hf' : (∑ r ∈ squares F, (if r = 0 then 1 else 2 : ℕ) • g r) =
      ∑ x : F, g (x ^ 2) := by
    convert hf using 1
    apply sum_congr rfl
    intro r hr
    rw [← square_fiber_card h2 hr, ← sum_const]
    apply sum_congr rfl
    intro x hx
    rw [(mem_filter.mp hx).2]
  rw [← hf']
  have hid : ∀ r : F, (if r = 0 then 1 else 2 : ℕ) • g r =
      2 * g r - if r = 0 then g 0 else 0 := by
    intro r
    by_cases hr : r = 0 <;> simp [hr, two_smul] <;> ring
  simp_rw [hid]
  rw [sum_sub_distrib, ← mul_sum]
  simp [zero_mem_squares]

lemma card_squares (h2 : (2 : F) ≠ 0) :
    2 * (squares F).card = Fintype.card F + 1 := by
  have hc := Finset.card_eq_sum_card_image (fun x : F => x ^ 2) univ
  change Fintype.card F = ∑ r ∈ squares F, (univ.filter (fun x : F => x ^ 2 = r)).card at hc
  have hc' : Fintype.card F = ∑ r ∈ squares F, (if r = 0 then 1 else 2 : ℕ) := by
    rw [hc]
    exact sum_congr rfl (fun r hr => square_fiber_card h2 hr)
  have ht : (∑ r ∈ squares F, (if r = 0 then 1 else 2 : ℕ)) + 1 =
      2 * (squares F).card := by
    have hz : (∑ r ∈ squares F, (if r = 0 then 1 else 0 : ℕ)) = 1 := by
      simp [zero_mem_squares]
    conv_lhs => rhs; rw [← hz]
    rw [← sum_add_distrib]
    trans ∑ _r ∈ squares F, (2 : ℕ)
    · apply sum_congr rfl
      intro r _
      split_ifs <;> norm_num
    · simp [mul_comm]
  omega

lemma two_mul_card_squares (h2 : (2 : F) ≠ 0) :
    (2 : F) * (squares F).card = 1 := by
  have hc := congrArg (fun n : ℕ => (n : F)) (card_squares h2)
  simpa [FiniteField.cast_card_eq_zero] using hc

lemma sum_squares_eq_zero (h2 : (2 : F) ≠ 0) (hp : 5 < Fintype.card F) :
    (∑ r ∈ squares F, r) = 0 := by
  have hs := sum_square_fibers h2 (fun r : F => r)
  rw [FiniteField.sum_pow_lt_card_sub_one F 2 (by omega), sub_zero] at hs
  exact (mul_eq_zero.mp hs.symm).resolve_left h2

lemma sum_squares_sq_eq_zero (h2 : (2 : F) ≠ 0) (hp : 5 < Fintype.card F) :
    (∑ r ∈ squares F, r ^ 2) = 0 := by
  have hs := sum_square_fibers h2 (fun r : F => r ^ 2)
  simp only [← pow_mul, show 2 * 2 = 4 by rfl, zero_pow (by decide : 2 ≠ 0), sub_zero] at hs
  rw [FiniteField.sum_pow_lt_card_sub_one F 4 (by omega)] at hs
  exact (mul_eq_zero.mp hs.symm).resolve_left h2

def quadImage (a b c : F) : Finset F := univ.image (fun x : F => a * x ^ 2 + b * x + c)

lemma quadImage_eq (h2 : (2 : F) ≠ 0) {a : F} (ha : a ≠ 0) (b c : F) :
    quadImage a b c = (squares F).image (fun r => (c - b ^ 2 / (4 * a)) + a * r) := by
  have h4 : (4 : F) ≠ 0 := by simpa [show (4 : F) = 2 * 2 by ring] using mul_ne_zero h2 h2
  ext y
  simp only [quadImage, squares, mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨(x + b / (2 * a)) ^ 2, ⟨x + b / (2 * a), rfl⟩, ?_⟩
    field_simp
    ring
  · rintro ⟨r, ⟨x, rfl⟩, rfl⟩
    refine ⟨x - b / (2 * a), ?_⟩
    field_simp
    ring

omit [Fintype F] [DecidableEq F] in
lemma affine_injective {a : F} (ha : a ≠ 0) (v : F) :
    Function.Injective (fun r : F => v + a * r) := by
  intro x y h
  exact mul_left_cancel₀ ha (add_left_cancel h)

lemma card_quadImage (h2 : (2 : F) ≠ 0) {a : F} (ha : a ≠ 0) (b c : F) :
    (quadImage a b c).card = (squares F).card := by
  rw [quadImage_eq h2 ha b c, card_image_of_injective _ (affine_injective ha _)]

lemma quadratic_moment (h2 : (2 : F) ≠ 0) (hp : 5 < Fintype.card F)
    {a : F} (ha : a ≠ 0) (b c : F) :
    (∑ r ∈ quadImage a b c, r ^ 2) = 2 * (∑ r ∈ quadImage a b c, r) ^ 2 := by
  rw [quadImage_eq h2 ha b c]
  set v := c - b ^ 2 / (4 * a)
  rw [sum_image (fun _ _ _ _ h => affine_injective ha v h),
    sum_image (fun _ _ _ _ h => affine_injective ha v h)]
  have h1 : 2 * (∑ r ∈ squares F, (v + a * r)) = v := by
    rw [sum_add_distrib, sum_const, ← mul_sum, sum_squares_eq_zero h2 hp]
    simp only [mul_zero, add_zero, nsmul_eq_mul]
    linear_combination v * two_mul_card_squares h2
  have h2' : 2 * (∑ r ∈ squares F, (v + a * r) ^ 2) = v ^ 2 := by
    simp_rw [show ∀ r : F, (v + a * r) ^ 2 = v ^ 2 + (2 * v * a) * r + a ^ 2 * r ^ 2 by intro; ring]
    rw [sum_add_distrib, sum_add_distrib, sum_const, ← mul_sum, ← mul_sum,
      sum_squares_eq_zero h2 hp, sum_squares_sq_eq_zero h2 hp]
    simp only [mul_zero, add_zero, nsmul_eq_mul]
    linear_combination v ^ 2 * two_mul_card_squares h2
  apply mul_left_cancel₀ h2
  linear_combination h2' - (2 * (∑ r ∈ squares F, (v + a * r)) + v) * h1

def exceptionalImage (F : Type*) [Field F] [Fintype F] [DecidableEq F] : Finset F :=
  insert 2 ((squares F).erase 0)

lemma exceptionalImage_card (hns : (2 : F) ∉ squares F) :
    (exceptionalImage F).card = (squares F).card := by
  rw [exceptionalImage, card_insert_of_notMem (fun h => hns (mem_of_mem_erase h)),
    card_erase_of_mem zero_mem_squares]
  have : 0 < (squares F).card := card_pos.mpr ⟨0, zero_mem_squares⟩
  omega

lemma exceptionalImage_sum (h2 : (2 : F) ≠ 0) (hp : 5 < Fintype.card F)
    (hns : (2 : F) ∉ squares F) : (∑ r ∈ exceptionalImage F, r) = 2 := by
  rw [exceptionalImage, sum_insert (fun h => hns (mem_of_mem_erase h)),
    sum_erase_eq_sub zero_mem_squares, sum_squares_eq_zero h2 hp]
  ring

lemma exceptionalImage_sum_sq (h2 : (2 : F) ≠ 0) (hp : 5 < Fintype.card F)
    (hns : (2 : F) ∉ squares F) : (∑ r ∈ exceptionalImage F, r ^ 2) = 4 := by
  rw [exceptionalImage, sum_insert (fun h => hns (mem_of_mem_erase h)),
    sum_erase_eq_sub zero_mem_squares, sum_squares_sq_eq_zero h2 hp]
  ring

lemma exceptionalImage_not_subset_quadImage (h2 : (2 : F) ≠ 0) (hp : 5 < Fintype.card F)
    (hns : (2 : F) ∉ squares F) {a : F} (ha : a ≠ 0) (b c : F) :
    ¬ exceptionalImage F ⊆ quadImage a b c := by
  intro h
  have he : exceptionalImage F = quadImage a b c :=
    eq_of_subset_of_card_le h (by rw [exceptionalImage_card hns, card_quadImage h2 ha b c])
  have hm := quadratic_moment h2 hp ha b c
  rw [← he, exceptionalImage_sum h2 hp hns, exceptionalImage_sum_sq h2 hp hns] at hm
  have h4 : (2 : F) * 2 = 0 := by linear_combination -hm
  exact (mul_ne_zero h2 h2) h4

end Green47Counterexample

open Finset Filter

namespace Green47Counterexample

def goodPrime (q : ℕ) : Prop := q.Prime ∧ q % 8 = 1

def counterexample : Set ℕ := insert 2 ((fun q : ℕ => q ^ 2) '' {q | goodPrime q})

lemma mem_counterexample (n : ℕ) : n ∈ counterexample ↔
    n = 2 ∨ ∃ q, goodPrime q ∧ q ^ 2 = n := by
  simp [counterexample]

lemma mem_squares_iff_isSquare {p : ℕ} [Fact p.Prime] (x : ZMod p) :
    x ∈ squares (ZMod p) ↔ IsSquare x := by
  simp [mem_squares, isSquare_iff_exists_sq, eq_comm]

lemma two_ne_zero {p : ℕ} [Fact p.Prime] (hp : 2 < p) : (2 : ZMod p) ≠ 0 := by
  intro h
  have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
  have := Nat.le_of_dvd (by decide : 0 < 2) hd
  omega

lemma goodPrime_cast_ne_zero {p q : ℕ} [Fact p.Prime] (hp : 2 < p)
    (hns : (2 : ZMod p) ∉ squares (ZMod p)) (hq : goodPrime q) : (q : ZMod p) ≠ 0 := by
  intro hq0
  have hd : p ∣ q := (ZMod.natCast_eq_zero_iff q p).mp hq0
  have he : q = p := (hq.1.dvd_iff_eq (by omega : p ≠ 1)).mp hd
  apply hns
  rw [mem_squares_iff_isSquare, ZMod.exists_sq_eq_two_iff (by omega)]
  exact Or.inl (he ▸ hq.2)

lemma local_bound : ∀ᶠ p : ℕ in atTop, p.Prime →
    ((fun a : ℕ => (a : ZMod p)) '' counterexample).ncard ≤ (p + 1) / 2 := by
  filter_upwards [eventually_ge_atTop 3] with p hp hprime
  let : Fact p.Prime := ⟨hprime⟩
  have hp2 : 2 < p := by omega
  have hc : (squares (ZMod p)).card = (p + 1) / 2 := by
    have h := card_squares (two_ne_zero hp2)
    rw [ZMod.card] at h
    omega
  by_cases hs : (2 : ZMod p) ∈ squares (ZMod p)
  · have hsub : ((fun a : ℕ => (a : ZMod p)) '' counterexample) ⊆
        (squares (ZMod p) : Set (ZMod p)) := by
      rintro x ⟨a, ha, rfl⟩
      rcases (mem_counterexample a).mp ha with rfl | ⟨q, _, rfl⟩
      · exact hs
      · apply (mem_squares _).mpr
        exact ⟨q, by simp⟩
    exact (Set.ncard_le_ncard hsub (Finset.finite_toSet _)).trans (by simpa using hc.le)
  · have hsub : ((fun a : ℕ => (a : ZMod p)) '' counterexample) ⊆
        (exceptionalImage (ZMod p) : Set (ZMod p)) := by
      rintro x ⟨a, ha, rfl⟩
      rcases (mem_counterexample a).mp ha with rfl | ⟨q, hq, rfl⟩
      · exact mem_insert_self _ _
      · apply mem_insert_of_mem
        apply mem_erase.mpr
        constructor
        · simpa using pow_ne_zero 2 (goodPrime_cast_ne_zero hp2 hs hq)
        · exact (mem_squares _).mpr ⟨q, by simp⟩
    exact (Set.ncard_le_ncard hsub (Finset.finite_toSet _)).trans
      (by simpa [exceptionalImage_card hs] using hc.le)

lemma goodPrime_in_residue {p : ℕ} [Fact p.Prime] (hp : 2 < p)
    (u : ZMod p) (hu : u ≠ 0) : ∃ q, goodPrime q ∧ (q : ZMod p) = u := by
  have hprime : p.Prime := Fact.out
  have h8p : Nat.Coprime 8 p := by
    rw [show 8 = 2 ^ 3 by norm_num, Nat.coprime_pow_left_iff (by decide), Nat.coprime_comm,
      hprime.coprime_iff_not_dvd]
    exact fun hd => (not_le.mpr hp) (Nat.le_of_dvd (by decide) hd)
  let r := Nat.chineseRemainder h8p 1 u.val
  have hr8 : r.val.Coprime 8 := by
    change Nat.gcd r.val 8 = 1
    rw [r.property.1.gcd_eq]
    simp
  have hrp : r.val.Coprime p := by
    change Nat.gcd r.val p = 1
    rw [r.property.2.gcd_eq]
    obtain ⟨v, hv⟩ := isUnit_iff_ne_zero.mpr hu
    simpa [hv] using ZMod.val_coe_unit_coprime v
  obtain ⟨q, _, hq, hqr⟩ := Nat.forall_exists_prime_gt_and_modEq 0
    (by positivity : 8 * p ≠ 0) (hr8.mul_right hrp)
  refine ⟨q, ⟨hq, ?_⟩, ?_⟩
  · have hh := (hqr.of_dvd (dvd_mul_right 8 p)).trans r.property.1
    exact hh
  · have hh := (hqr.of_dvd (dvd_mul_left p 8)).trans r.property.2
    simpa only [ZMod.natCast_zmod_val] using (ZMod.natCast_eq_natCast_iff q u.val p).mpr hh

lemma exceptionalImage_subset_reduction {p : ℕ} [Fact p.Prime] (hp : 2 < p) :
    (exceptionalImage (ZMod p) : Set (ZMod p)) ⊆
      ((fun a : ℕ => (a : ZMod p)) '' counterexample) := by
  intro x hx
  rcases mem_insert.mp hx with rfl | hx
  · exact ⟨2, (mem_counterexample 2).mpr (Or.inl rfl), by simp⟩
  · obtain ⟨hx0, hxs⟩ := mem_erase.mp hx
    obtain ⟨u, rfl⟩ := (mem_squares x).mp hxs
    have hu : u ≠ 0 := by intro h; simp [h] at hx0
    obtain ⟨q, hq, hqu⟩ := goodPrime_in_residue hp u hu
    refine ⟨q ^ 2, (mem_counterexample _).mpr (Or.inr ⟨q, hq, rfl⟩), ?_⟩
    simp [hqu]

lemma intCast_ne_zero_of_abs_lt {p : ℕ} [Fact p.Prime] {a : ℤ}
    (ha : a ≠ 0) (hap : a.natAbs < p) : (a : ZMod p) ≠ 0 := by
  intro h
  have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp h
  have hn : p ∣ a.natAbs := by exact_mod_cast Int.natAbs_dvd_natAbs.mpr hd
  exact (not_le.mpr hap) (Nat.le_of_dvd (Int.natAbs_pos.mpr ha) hn)

lemma no_scaled_integer_quadratic (a b c d : ℤ) (ha : a ≠ 0) (hd : d ≠ 0) :
    ¬ (∀ n ∈ counterexample, ∃ z : ℤ, d * (n : ℤ) = a * z ^ 2 + b * z + c) := by
  intro h
  obtain ⟨p, hpl, hprime, hp3⟩ := Nat.forall_exists_prime_gt_and_modEq
    (max 5 (max a.natAbs d.natAbs)) (by decide : 8 ≠ 0) (by decide : Nat.Coprime 3 8)
  let : Fact p.Prime := ⟨hprime⟩
  have hp5 : 5 < p := lt_of_le_of_lt (le_max_left _ _) hpl
  have hap : a.natAbs < p := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hpl
  have hdp : d.natAbs < p := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hpl
  have had : (a : ZMod p) / d ≠ 0 := div_ne_zero (intCast_ne_zero_of_abs_lt ha hap)
    (intCast_ne_zero_of_abs_lt hd hdp)
  have hns : (2 : ZMod p) ∉ squares (ZMod p) := by
    rw [mem_squares_iff_isSquare, ZMod.exists_sq_eq_two_iff (by omega)]
    have hmod : p % 8 = 3 := hp3
    omega
  apply exceptionalImage_not_subset_quadImage (two_ne_zero (by omega))
    (by simpa using hp5) hns had ((b : ZMod p) / d) ((c : ZMod p) / d)
  intro x hx
  obtain ⟨n, hn, rfl⟩ := exceptionalImage_subset_reduction (by omega) hx
  obtain ⟨z, hz⟩ := h n hn
  apply mem_image.mpr
  refine ⟨(z : ZMod p), mem_univ _, ?_⟩
  have hz' : (d : ZMod p) * n = (a : ZMod p) * z ^ 2 + (b : ZMod p) * z + c := by
    simpa only [Int.cast_mul, Int.cast_add, Int.cast_pow, Int.cast_natCast] using
      congrArg (fun x : ℤ => (x : ZMod p)) hz
  field_simp [intCast_ne_zero_of_abs_lt hd hdp]
  linear_combination -hz'

lemma no_rational_quadratic : ¬ ∃ P : Polynomial ℚ, P.degree = 2 ∧
    ∀ n ∈ counterexample, ∃ z : ℤ, (n : ℚ) = P.eval (z : ℚ) := by
  rintro ⟨P, hP, h⟩
  have hdeg : P.natDegree = 2 := Polynomial.natDegree_eq_of_degree_eq_some hP
  have hP0 : P ≠ 0 := by intro he; simp [he] at hP
  let a := P.coeff 2
  let b := P.coeff 1
  let c := P.coeff 0
  have ha : a ≠ 0 := by
    change P.coeff 2 ≠ 0
    rw [← hdeg, Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hP0
  have hev (x : ℚ) : P.eval x = a * x ^ 2 + b * x + c := by
    rw [Polynomial.eval_eq_sum_range, hdeg]
    simp [sum_range_succ, a, b, c]
    ring
  have had : (a.den : ℤ) ≠ 0 := by exact_mod_cast a.den_ne_zero
  have hbd : (b.den : ℤ) ≠ 0 := by exact_mod_cast b.den_ne_zero
  have hcd : (c.den : ℤ) ≠ 0 := by exact_mod_cast c.den_ne_zero
  apply no_scaled_integer_quadratic (a.num * b.den * c.den) (b.num * a.den * c.den)
    (c.num * a.den * b.den) ((a.den : ℤ) * b.den * c.den)
    (mul_ne_zero (mul_ne_zero (Rat.num_ne_zero.mpr ha) hbd) hcd)
    (mul_ne_zero (mul_ne_zero had hbd) hcd)
  intro n hn
  obtain ⟨z, hz⟩ := h n hn
  rw [hev] at hz
  refine ⟨z, ?_⟩
  have he : ((a.den : ℚ) * b.den * c.den) * n =
      ((a.num : ℚ) * b.den * c.den) * (z : ℚ) ^ 2 +
      ((b.num : ℚ) * a.den * c.den) * z + (c.num : ℚ) * a.den * b.den := by
    have han : a * a.den = (a.num : ℚ) :=
      (eq_div_iff (by exact_mod_cast a.den_ne_zero)).mp a.num_div_den.symm
    have hbn : b * b.den = (b.num : ℚ) :=
      (eq_div_iff (by exact_mod_cast b.den_ne_zero)).mp b.num_div_den.symm
    have hcn : c * c.den = (c.num : ℚ) :=
      (eq_div_iff (by exact_mod_cast c.den_ne_zero)).mp c.num_div_den.symm
    linear_combination ((a.den : ℚ) * b.den * c.den) * hz +
      ((b.den : ℚ) * c.den * (z : ℚ) ^ 2) * han +
      ((a.den : ℚ) * c.den * z) * hbn + ((a.den : ℚ) * b.den) * hcn
  exact_mod_cast he

end Green47Counterexample

open Finset Filter Asymptotics

namespace Green47Counterexample


noncomputable def goodPrimes (N : ℕ) : Finset ℕ := by
  classical
  exact (range (N + 1)).filter goodPrime

lemma mem_goodPrimes (N q : ℕ) : q ∈ goodPrimes N ↔ q ≤ N ∧ goodPrime q := by
  classical
  simp [goodPrimes]

lemma primeCount_le_squareCount (N : ℕ) :
    (goodPrimes N).card ≤ (counterexample ∩ Set.Iic (N ^ 2)).ncard := by
  classical
  have hinj : Function.Injective (fun q : ℕ => q ^ 2) := by
    intro x y h
    nlinarith
  have hsub : ((goodPrimes N).image (fun q : ℕ => q ^ 2) : Set ℕ) ⊆
      counterexample ∩ Set.Iic (N ^ 2) := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hx
    obtain ⟨hqN, hq⟩ := (mem_goodPrimes N q).mp hq
    exact ⟨(mem_counterexample _).mpr (Or.inr ⟨q, hq, rfl⟩), Nat.pow_le_pow_left hqN 2⟩
  simpa only [Set.ncard_coe_finset, card_image_of_injective _ hinj] using
    Set.ncard_le_ncard hsub (Set.finite_Iic _ |>.subset Set.inter_subset_right)

lemma dyadicCount_of_small
    (h : (fun X : ℕ => ((counterexample ∩ Set.Iic X).ncard : ℝ)) =O[atTop]
      (fun X : ℕ => Real.sqrt (X : ℝ) / Real.log (X : ℝ) ^ 100)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ k : ℕ in atTop,
      ((goodPrimes (2 ^ k)).card : ℝ) ≤ C * (2 : ℝ) ^ k / (k : ℝ) ^ 100 := by
  obtain ⟨C, hC, hb⟩ := h.exists_pos
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨C / (2 * Real.log 2) ^ 100, by positivity, ?_⟩
  have ht : Tendsto (fun k : ℕ => (2 ^ k) ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by decide : 2 ≠ 0)).comp
      (tendsto_pow_atTop_atTop_of_one_lt (by decide : 1 < (2 : ℕ)))
  filter_upwards [ht.eventually hb.bound, eventually_ge_atTop 1] with k hk hk1
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  have hcnt : ((goodPrimes (2 ^ k)).card : ℝ) ≤
      ((counterexample ∩ Set.Iic ((2 ^ k) ^ 2)).ncard : ℝ) :=
    Nat.cast_le.mpr (primeCount_le_squareCount (2 ^ k))
  have he : Real.sqrt (((2 ^ k) ^ 2 : ℕ) : ℝ) /
      Real.log (((2 ^ k) ^ 2 : ℕ) : ℝ) ^ 100 =
      (2 : ℝ) ^ k / ((2 * Real.log 2) ^ 100 * (k : ℝ) ^ 100) := by
    simp only [Nat.cast_pow, Nat.cast_ofNat, Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ (2 : ℝ) ^ k), Real.log_pow]
    have hmul : (2 : ℝ) * ((k : ℝ) * Real.log 2) =
        (2 * Real.log 2) * (k : ℝ) := by ring
    rw [← mul_pow, hmul]
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (by positivity), he] at hk
  refine hcnt.trans (hk.trans_eq ?_)
  field_simp

noncomputable def primeWeight (n : ℕ) : ℝ := by
  classical
  exact if goodPrime n then Real.log (n : ℝ) / n else 0

lemma primeWeight_nonneg (n : ℕ) : 0 ≤ primeWeight n := by
  classical
  unfold primeWeight
  split_ifs with hn
  · exact div_nonneg (Real.log_nonneg (by exact_mod_cast hn.1.one_le)) (Nat.cast_nonneg n)
  · exact le_rfl

lemma primeWeight_not_summable : ¬ Summable primeWeight := by
  classical
  intro h
  apply ArithmeticFunction.vonMangoldt.not_summable_residueClass_prime_div
    (a := (1 : ZMod 8)) isUnit_one
  convert h using 1
  ext n
  have hm : (n : ZMod 8) = 1 ↔ n % 8 = 1 := ZMod.natCast_eq_natCast_iff' n 1 8
  by_cases hp : n.Prime
  · simp [primeWeight, goodPrime, hp, ArithmeticFunction.vonMangoldt.residueClass,
      ArithmeticFunction.vonMangoldt_apply_prime hp, Set.indicator,
      hm, ite_div]
  · simp [primeWeight, goodPrime, hp]

def dyadicBlock (k : ℕ) : Finset ℕ :=
  (range (2 ^ (k + 1))).filter (fun n => Nat.log 2 n = k)

lemma mem_dyadicBlock (k n : ℕ) : n ∈ dyadicBlock k ↔ Nat.log 2 n = k := by
  simp only [dyadicBlock, mem_filter, mem_range]
  constructor
  · exact And.right
  · intro hn
    exact ⟨hn ▸ Nat.lt_pow_succ_log_self (by decide : 1 < 2) n, hn⟩

lemma blockWeight_le (k : ℕ) :
    (∑ n ∈ dyadicBlock k, primeWeight n) ≤
      ((goodPrimes (2 ^ (k + 1))).card : ℝ) *
        (((k : ℝ) + 1) * Real.log 2 / (2 : ℝ) ^ k) := by
  classical
  have ht : (dyadicBlock k).filter goodPrime ⊆ goodPrimes (2 ^ (k + 1)) := by
    intro n hn
    obtain ⟨hnb, hng⟩ := mem_filter.mp hn
    exact (mem_goodPrimes _ n).mpr ⟨(mem_range.mp (mem_filter.mp hnb).1).le, hng⟩
  have hb : ∀ n ∈ (dyadicBlock k).filter goodPrime,
      Real.log (n : ℝ) / n ≤ ((k : ℝ) + 1) * Real.log 2 / (2 : ℝ) ^ k := by
    intro n hn
    obtain ⟨hnb, hng⟩ := mem_filter.mp hn
    have hn0 : 0 < (n : ℝ) := by exact_mod_cast hng.1.pos
    have hlow : (2 : ℝ) ^ k ≤ n := by
      have hh := Nat.pow_log_le_self 2 hng.1.ne_zero
      rw [(mem_dyadicBlock k n).mp hnb] at hh
      exact_mod_cast hh
    have hupp : (n : ℝ) ≤ (2 : ℝ) ^ (k + 1) := by
      exact_mod_cast (mem_range.mp (mem_filter.mp hnb).1).le
    calc
      Real.log (n : ℝ) / n ≤ Real.log ((2 : ℝ) ^ (k + 1)) / n :=
        div_le_div_of_nonneg_right (Real.log_le_log hn0 hupp) hn0.le
      _ ≤ Real.log ((2 : ℝ) ^ (k + 1)) / (2 : ℝ) ^ k :=
        div_le_div_of_nonneg_left (Real.log_nonneg (one_le_pow₀ (by norm_num)))
          (by positivity) hlow
      _ = _ := by simp [Real.log_pow]
  simp only [primeWeight, ← sum_filter]
  calc
    _ ≤ ∑ _n ∈ (dyadicBlock k).filter goodPrime,
        (((k : ℝ) + 1) * Real.log 2 / (2 : ℝ) ^ k) := sum_le_sum hb
    _ = (((dyadicBlock k).filter goodPrime).card : ℝ) *
        (((k : ℝ) + 1) * Real.log 2 / (2 : ℝ) ^ k) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (card_le_card ht))
      (by positivity)

lemma summable_of_dyadicCount {C : ℝ} (hC : 0 < C)
    (hcount : ∀ᶠ k : ℕ in atTop,
      ((goodPrimes (2 ^ k)).card : ℝ) ≤ C * (2 : ℝ) ^ k / (k : ℝ) ^ 100) :
    Summable primeWeight := by
  have hs : Summable (fun k : ℕ => ((k : ℝ) ^ 99)⁻¹) :=
    Real.summable_nat_pow_inv.mpr (by decide)
  have hs' : Summable (fun k : ℕ => (((k : ℝ) + 1) ^ 99)⁻¹) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      hs.comp_injective (fun a b (h : a + 1 = b + 1) => Nat.add_right_cancel h)
  have hs'' := hs'.mul_left (2 * C * Real.log 2)
  have hblocks : Summable (fun k : ℕ => ∑ n ∈ dyadicBlock k, primeWeight n) := by
    apply hs''.of_norm_bounded_eventually_nat
    filter_upwards [(tendsto_add_atTop_nat 1).eventually hcount] with k hk
    rw [Real.norm_of_nonneg (sum_nonneg (fun n _ => primeWeight_nonneg n))]
    refine (blockWeight_le k).trans ?_
    calc
      _ ≤ (C * (2 : ℝ) ^ (k + 1) / ((k : ℝ) + 1) ^ 100) *
          (((k : ℝ) + 1) * Real.log 2 / (2 : ℝ) ^ k) :=
        mul_le_mul_of_nonneg_right (by simpa only [Nat.cast_add, Nat.cast_one] using hk)
          (by positivity)
      _ = 2 * C * Real.log 2 * (((k : ℝ) + 1) ^ 99)⁻¹ := by
        rw [pow_succ]
        have hk0 : (k : ℝ) + 1 ≠ 0 := by positivity
        have htwo : (2 : ℝ) ^ k ≠ 0 := by positivity
        field_simp
  have hp : ∀ n : ℕ, ∃! k : ℕ, n ∈ (dyadicBlock k : Set ℕ) := by
    intro n
    refine ⟨Nat.log 2 n, (mem_dyadicBlock _ _).mpr rfl, ?_⟩
    intro k hk
    exact ((mem_dyadicBlock k n).mp hk).symm
  apply (summable_partition primeWeight_nonneg hp).mpr
  constructor
  · intro k
    exact summable_of_hasFiniteSupport (Set.toFinite _)
  · convert hblocks using 1
    funext k
    exact Finset.tsum_subtype (dyadicBlock k) primeWeight

lemma not_small : ¬ ((fun X : ℕ => ((counterexample ∩ Set.Iic X).ncard : ℝ)) =O[atTop]
      (fun X : ℕ => Real.sqrt (X : ℝ) / Real.log (X : ℝ) ^ 100)) := by
  intro h
  obtain ⟨C, hC, hc⟩ := dyadicCount_of_small h
  exact primeWeight_not_summable (summable_of_dyadicCount hC hc)

end Green47Counterexample


/-- Negation of the complete Green 47 statement displayed by conjectures.io.
The witness is `{2} ∪ {q² | q.Prime ∧ q % 8 = 1}`. -/
theorem target : ¬ (fcTypeOfName% "Green47.green_47") := by
  intro h
  have hA := h.mp trivial Green47Counterexample.counterexample Green47Counterexample.local_bound
  exact hA.elim Green47Counterexample.not_small Green47Counterexample.no_rational_quadratic

