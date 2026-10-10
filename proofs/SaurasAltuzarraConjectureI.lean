/-
Copyright 2026 Jensen Kohlmeyer and Liam Kruer.
Released under Apache 2.0 license.

The sequence definition and conjecture statement are reproduced from
Google DeepMind's Formal Conjectures repository (Apache 2.0):
commit 89294ea02bd7cd678d59984add52cb4baef3dbf4,
FormalConjectures/OEIS/46969.lean, OeisA46969.conjecture1.
The conjecture is due to Lorenzo Sauras Altuzarra (13 October 2020).
AI assistance: OpenAI Codex, for mathematical development, formalization,
and manuscript preparation. All proof dependencies are kernel checked.
-/
import Mathlib

/-!
# Sauras Altuzarra Conjecture I

For primes p > 3 with 2*p-1 prime, the exact denominator is 12*(2*p-1).
This single file contains the entire proof beyond Mathlib. It imports no
unproved conjecture. The definition `a` and final proposition reproduce
the pinned Formal Conjectures statement; a separate audit checked this
proof against the type read directly from the unchanged repository file.

Verified with Lean 4.33.1 and Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.
-/

set_option maxHeartbeats 1600000
set_option autoImplicit false

open Finset

namespace SaurasAltuzarra

private abbrev PInt (p : ℕ) [Fact p.Prime] (x : ℚ) : Prop :=
  Rat.padicValuation p x ≤ 1

private abbrev PZero (p : ℕ) [Fact p.Prime] (x : ℚ) : Prop :=
  PInt p (x / p)

private lemma pint_int (p : ℕ) [Fact p.Prime] (x : ℤ) : PInt p x :=
  Int.padicValuation_le_one p x

private lemma pint_nat (p : ℕ) [Fact p.Prime] (x : ℕ) : PInt p x := by
  exact_mod_cast pint_int p (x : ℤ)

private lemma pint_mul {p : ℕ} [Fact p.Prime] {x y : ℚ}
    (hx : PInt p x) (hy : PInt p y) : PInt p (x * y) :=
  ((Rat.padicValuation p).map_mul x y).trans_le (mul_le_one' hx hy)

private lemma pint_add {p : ℕ} [Fact p.Prime] {x y : ℚ}
    (hx : PInt p x) (hy : PInt p y) : PInt p (x + y) :=
  (Rat.padicValuation p).map_add_le hx hy

private lemma pint_sub {p : ℕ} [Fact p.Prime] {x y : ℚ}
    (hx : PInt p x) (hy : PInt p y) : PInt p (x - y) :=
  (Rat.padicValuation p).map_sub_le hx hy

private lemma pint_neg {p : ℕ} [Fact p.Prime] {x : ℚ}
    (hx : PInt p x) : PInt p (-x) := by
  change Rat.padicValuation p (-x) ≤ 1
  rw [Valuation.map_neg]
  exact hx

private lemma pint_inv_nat {p n : ℕ} [Fact p.Prime] (h : ¬ p ∣ n) :
    PInt p ((n : ℚ)⁻¹) := by
  apply Rat.padicValuation_le_one_iff.mpr
  have hn : 0 < n := Nat.pos_of_ne_zero (by intro hn; subst n; simp at h)
  simpa [Rat.inv_natCast_den_of_pos hn] using h

private lemma pint_div_nat {p n : ℕ} [Fact p.Prime] {x : ℚ}
    (hx : PInt p x) (hn : ¬ p ∣ n) : PInt p (x / n) := by
  exact pint_mul hx (pint_inv_nat hn)

private lemma pzero_zero (p : ℕ) [Fact p.Prime] : PZero p 0 := by simp [PZero, PInt]

private lemma pzero_add {p : ℕ} [Fact p.Prime] {x y : ℚ}
    (hx : PZero p x) (hy : PZero p y) : PZero p (x + y) := by
  simpa only [PZero, add_div] using pint_add hx hy

private lemma pzero_sub {p : ℕ} [Fact p.Prime] {x y : ℚ}
    (hx : PZero p x) (hy : PZero p y) : PZero p (x - y) := by
  simpa only [PZero, sub_div] using pint_sub hx hy

private lemma pzero_mul {p : ℕ} [Fact p.Prime] {x y : ℚ}
    (hx : PZero p x) (hy : PInt p y) : PZero p (x * y) := by
  simpa only [div_mul_eq_mul_div] using pint_mul hx hy

private lemma pzero_sum {p : ℕ} [Fact p.Prime] {ι : Type*} (s : Finset ι)
    (f : ι → ℚ) (h : ∀ i ∈ s, PZero p (f i)) : PZero p (∑ i ∈ s, f i) := by
  simpa only [PZero, sum_div] using (Rat.padicValuation p).map_sum_le h

private lemma pzero_prime_mul {p : ℕ} [Fact p.Prime] {x : ℚ}
    (hx : PInt p x) : PZero p ((p : ℚ) * x) := by
  have hp : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero Fact.out)
  simpa [PZero, mul_div_cancel_left₀ _ hp] using hx

private lemma pint_of_pzero {p : ℕ} [Fact p.Prime] {x : ℚ}
    (hx : PZero p x) : PInt p x := by
  have hp : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero Fact.out)
  simpa [div_mul_cancel₀ _ hp] using pint_mul hx (pint_nat p p)

private lemma pzero_int_iff {p : ℕ} [Fact p.Prime] (x : ℤ) :
    PZero p x ↔ (p : ℤ) ∣ x := by
  constructor
  · intro hx
    apply Int.padicValuation_lt_one_iff.mp
    have hlt : Rat.padicValuation p (p : ℚ) < 1 := by
      rw [Rat.padicValuation_self, ← WithZero.exp_zero, WithZero.exp_lt_exp]
      norm_num
    have hle : Rat.padicValuation p (x : ℚ) ≤ Rat.padicValuation p (p : ℚ) := by
      have hp : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero Fact.out)
      have h : Rat.padicValuation p ((x : ℚ) / p) * Rat.padicValuation p (p : ℚ) ≤
          1 * Rat.padicValuation p (p : ℚ) := by gcongr
      simpa only [← map_mul, div_mul_cancel₀ _ hp, one_mul] using h
    exact hle.trans_lt hlt
  · rintro ⟨t, ht⟩
    have hx : (x : ℚ) = (p : ℚ) * t := by exact_mod_cast ht
    rw [hx]
    exact pzero_prime_mul (pint_int p t)

private lemma pzero_nat_of_dvd {p n : ℕ} [Fact p.Prime] (h : p ∣ n) :
    PZero p (n : ℚ) := by
  exact (pzero_int_iff (n : ℤ)).mpr (Int.natCast_dvd_natCast.mpr h)

private lemma pint_bernoulli_mul_prime {p : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) (n : ℕ) : PInt p ((p : ℚ) * bernoulli n) := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | hn
  · have hn : n = 2 * k := by omega
    rw [hn]
    obtain ⟨t, ht⟩ := Bernoulli.vonStaudt_clausen k
    have hsum : PInt p (∑ r ∈ range (2 * k + 2) with r.Prime ∧ (r - 1) ∣ 2 * k,
        (p : ℚ) / r) := by
      refine (Rat.padicValuation p).map_sum_le fun r hr ↦ ?_
      have hrp := (mem_filter.mp hr).2.1
      by_cases h : r = p
      · subst r
        simp [Nat.Prime.ne_zero (Fact.out : p.Prime)]
      · exact pint_div_nat (pint_nat p p) ((Nat.dvd_prime hrp).not.mpr (by
          rintro (h1 | h2)
          · exact (Nat.Prime.ne_one Fact.out) h1
          · exact h h2.symm))
    have heq : (p : ℚ) * bernoulli (2 * k) = p * t -
        ∑ r ∈ range (2 * k + 2) with r.Prime ∧ (r - 1) ∣ 2 * k, (p : ℚ) / r := by
      have ht' : (t : ℚ) = bernoulli (2 * k) +
        ∑ r ∈ range (2 * k + 2) with r.Prime ∧ (r - 1) ∣ 2 * k, (1 : ℚ) / r := ht
      have hs : (∑ r ∈ range (2 * k + 2) with r.Prime ∧ (r - 1) ∣ 2 * k,
          (p : ℚ) / r) = p *
          ∑ r ∈ range (2 * k + 2) with r.Prime ∧ (r - 1) ∣ 2 * k, (1 : ℚ) / r := by
        rw [mul_sum]
        apply sum_congr rfl
        intro r hr
        ring
      rw [hs, ht']; ring
    rw [heq]
    exact pint_sub (pint_mul (pint_nat p p) (pint_int p t)) hsum
  · by_cases h : n = 1
    · subst n
      rw [bernoulli_one]
      exact pint_mul (pint_nat p p) (by
        apply Rat.padicValuation_le_one_iff.mpr
        norm_num
        exact Nat.not_dvd_of_pos_of_lt (by decide) (by omega))
    · rw [bernoulli_eq_zero_of_odd hn (by have := hn.pos; omega)]
      simp [PInt]

private lemma pint_bernoulli_of_not_dvd {p : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) {n : ℕ} (hnd : ¬ (p - 1) ∣ n) : PInt p (bernoulli n) := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | hn
  · have hn : n = 2 * k := by omega
    rw [hn] at hnd ⊢
    obtain ⟨t, ht⟩ := Bernoulli.vonStaudt_clausen k
    have hsum : PInt p (∑ r ∈ range (2 * k + 2) with r.Prime ∧ (r - 1) ∣ 2 * k,
        (1 : ℚ) / r) := by
      refine (Rat.padicValuation p).map_sum_le fun r hr ↦ ?_
      have hrp := (mem_filter.mp hr).2.1
      have hrne : r ≠ p := by intro h; subst r; exact hnd (mem_filter.mp hr).2.2
      exact pint_div_nat (by simp [PInt]) ((Nat.dvd_prime hrp).not.mpr (by
        rintro (h1 | h2)
        · exact (Nat.Prime.ne_one Fact.out) h1
        · exact hrne h2.symm))
    have heq : bernoulli (2 * k) = (t : ℚ) -
        ∑ r ∈ range (2 * k + 2) with r.Prime ∧ (r - 1) ∣ 2 * k, (1 : ℚ) / r := by
      linarith [ht]
    rw [heq]
    exact pint_sub (pint_int p t) hsum
  · by_cases h : n = 1
    · subst n
      rw [bernoulli_one]
      apply Rat.padicValuation_le_one_iff.mpr
      norm_num
      exact Nat.not_dvd_of_pos_of_lt (by decide) (by omega)
    · rw [bernoulli_eq_zero_of_odd hn (by have := hn.pos; omega)]
      simp [PInt]

private lemma pint_bernoulli_add_inv {p k : ℕ} [Fact p.Prime]
    (hk : 0 < k) (hd : (p - 1) ∣ 2 * k) :
    PInt p (bernoulli (2 * k) + 1 / p) := by
  let s := (range (2 * k + 2)).filter fun r ↦ r.Prime ∧ (r - 1) ∣ 2 * k
  have hp_mem : p ∈ s := by
    apply mem_filter.mpr
    refine ⟨mem_range.mpr ?_, Fact.out, hd⟩
    have := Nat.le_of_dvd (by omega : 0 < 2 * k) hd
    omega
  obtain ⟨t, ht⟩ := Bernoulli.vonStaudt_clausen k
  change (t : ℚ) = bernoulli (2 * k) + ∑ r ∈ s, (1 : ℚ) / r at ht
  rw [← add_sum_erase _ _ hp_mem] at ht
  have hsum : PInt p (∑ r ∈ s.erase p, (1 : ℚ) / r) := by
    refine (Rat.padicValuation p).map_sum_le fun r hr ↦ ?_
    have hrp := (mem_filter.mp (mem_erase.mp hr).2).2.1
    have hrne := (mem_erase.mp hr).1
    exact pint_div_nat (by simp [PInt]) ((Nat.dvd_prime hrp).not.mpr (by
      rintro (h1 | h2)
      · exact (Nat.Prime.ne_one Fact.out) h1
      · exact hrne h2.symm))
  have heq : bernoulli (2 * k) + 1 / p = (t : ℚ) -
      ∑ r ∈ s.erase p, (1 : ℚ) / r := by linarith [ht]
  rw [heq]
  exact pint_sub (pint_int p t) hsum

private lemma pzero_prime_mul_bernoulli_pred {p : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) : PZero p ((p : ℚ) * bernoulli (p - 1) + 1) := by
  have hpodd : p % 2 = 1 := ((Nat.Prime.eq_two_or_odd Fact.out).resolve_left (by omega))
  have heq : p - 1 = 2 * ((p - 1) / 2) := by omega
  have h := pint_bernoulli_add_inv (p := p) (k := (p - 1) / 2) (by omega)
    (by rw [← heq])
  rw [← heq] at h
  have hpne : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero Fact.out)
  convert pzero_prime_mul h using 1
  field_simp [hpne]

private lemma choose_two_rat (n : ℕ) :
    (n.choose 2 : ℚ) = (n : ℚ) * (n - 1 : ℕ) / 2 := by
  have h := Nat.choose_succ_right_eq n 1
  norm_num at h
  have hq : (n.choose 2 : ℚ) * 2 = (n : ℚ) * (n - 1 : ℕ) := by exact_mod_cast h
  linarith

private lemma choose_three_rat (n : ℕ) :
    (n.choose 3 : ℚ) = (n : ℚ) * (n - 1 : ℕ) * (n - 2 : ℕ) / 6 := by
  have hq : (n.choose 3 : ℚ) * 3 = (n.choose 2 : ℚ) * (n - 2 : ℕ) := by
    exact_mod_cast Nat.choose_succ_right_eq n 2
  rw [choose_two_rat] at hq
  linarith

/-- The first Bernoulli congruence above a prime, proved directly from its recurrence. -/
private theorem bernoulli_prime_add_one_congruence {p : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) : PZero p (bernoulli (p + 1) - 1 / 12) := by
  have hp2 : ¬ p ∣ 2 := Nat.not_dvd_of_pos_of_lt (by decide) (by omega)
  have hp6 : ¬ p ∣ 6 := by
    intro h
    have h : p ∣ 2 ∨ p ∣ 3 := (Nat.Prime.dvd_mul Fact.out).mp (by simpa using h)
    rcases h with h | h
    · exact hp2 h
    · exact (Nat.not_dvd_of_pos_of_lt (by decide) (by omega)) h
  have hhalf : PInt p (1 / 2) := pint_div_nat (by simp [PInt]) hp2
  have hsixth : PInt p (1 / 6) := pint_div_nat (by simp [PInt]) hp6
  have hB : PInt p (bernoulli (p + 1)) := by
    apply pint_bernoulli_of_not_dvd hp5
    intro hd
    have hd2 : (p - 1) ∣ 2 := by
      have h := Nat.dvd_sub hd (dvd_refl (p - 1))
      simpa [show p + 1 - (p - 1) = 2 by omega] using h
    have := Nat.le_of_dvd (by decide : 0 < 2) hd2
    omega
  let f : ℕ → ℚ := fun k ↦ ((p + 2).choose k : ℚ) * bernoulli k
  let g : ℕ → ℚ := fun k ↦ if k = 0 then 1 else if k = 1 then -1 else
    if k = 2 then 1 / 6 else if k = p - 1 then -1 / 3 else
    if k = p + 1 then 2 * bernoulli (p + 1) else 0
  have hterms : ∀ k ∈ range (p + 2), PZero p (f k - g k) := by
    intro k hk
    have hklt := mem_range.mp hk
    by_cases hk0 : k = 0
    · subst k
      simp [f, g]
    by_cases hk1 : k = 1
    · subst k
      have heq : f 1 - g 1 = (p : ℚ) * (-1 / 2) := by
        simp [f, g, bernoulli_one]; ring
      rw [heq]
      exact pzero_prime_mul (by simpa only [neg_div] using pint_neg hhalf)
    by_cases hk2 : k = 2
    · subst k
      have heq : f 2 - g 2 = (p : ℚ) * ((p + 3) / 12) := by
        simp [f, g, choose_two_rat, bernoulli_two]
        ring
      rw [heq]
      have hp12 : ¬ p ∣ 12 := by
        intro h
        rw [show 12 = 2 * 6 by decide] at h
        exact (not_or.mpr ⟨hp2, hp6⟩) ((Nat.Prime.dvd_mul Fact.out).mp h)
      exact pzero_prime_mul (pint_div_nat (by
        convert pint_nat p (p + 3) using 1
        push_cast
        ring) hp12)
    by_cases hkpred : k = p - 1
    · subst k
      have hchoose : ((p + 2).choose (p - 1) : ℚ) =
          (p : ℚ) * ((p + 1) * (p + 2) / 6) := by
        rw [← show p + 2 - 3 = p - 1 by omega, Nat.choose_symm (by omega), choose_three_rat]
        push_cast; ring
      let c : ℚ := ((p : ℚ) + 1) * (p + 2) / 6
      have hc : PInt p c := by
        exact pint_div_nat (pint_mul (by simpa using pint_nat p (p + 1))
          (by simpa using pint_nat p (p + 2))) hp6
      have hc0 : PZero p (c - 1 / 3) := by
        have heq : c - 1 / 3 = (p : ℚ) * ((p + 3) / 6) := by dsimp [c]; ring
        rw [heq]
        exact pzero_prime_mul (pint_div_nat (by simpa using pint_nat p (p + 3)) hp6)
      have hb0 := pzero_mul (pzero_prime_mul_bernoulli_pred hp5) hc
      have heq : f (p - 1) - g (p - 1) =
          ((p : ℚ) * bernoulli (p - 1) + 1) * c - (c - 1 / 3) := by
        simp [f, g, hchoose, c, show p - 1 ≠ 0 by omega,
          show p - 1 ≠ 1 by omega, show p - 1 ≠ 2 by omega]
        ring
      rw [heq]
      exact pzero_sub hb0 hc0
    by_cases hklast : k = p + 1
    · subst k
      have heq : f (p + 1) - g (p + 1) = (p : ℚ) * bernoulli (p + 1) := by
        simp [f, g, show p ≠ 0 by omega, show p + 1 ≠ 2 by omega, show p + 1 ≠ p - 1 by omega,
          show p + 2 = (p + 1) + 1 by omega]; ring
      rw [heq]
      exact pzero_prime_mul hB
    by_cases hkp : k = p
    · subst k
      have hodd : Odd p := Nat.Prime.odd_of_ne_two Fact.out (by omega)
      simp [f, g, hk0, hk1, hk2, hkpred,
        bernoulli_eq_zero_of_odd hodd (by omega)]
    · have hkr : 3 ≤ k ∧ k < p - 1 := by omega
      have hd : p ∣ (p + 2).choose k := Nat.Prime.dvd_choose Fact.out (by omega)
        (by omega) (by omega)
      have hBk : PInt p (bernoulli k) := by
        apply pint_bernoulli_of_not_dvd hp5
        intro hd
        have := Nat.le_of_dvd (by omega : 0 < k) hd
        omega
      simpa [f, g, hk0, hk1, hk2, hkpred, hklast] using
        pzero_mul (pzero_nat_of_dvd hd) hBk
  have hsum := pzero_sum (range (p + 2)) (fun k ↦ f k - g k) hterms
  have hf : ∑ k ∈ range (p + 2), f k = 0 := by
    simp only [f, sum_bernoulli, if_neg (by omega : p + 2 ≠ 1)]
  have hg : ∑ k ∈ range (p + 2), g k = 2 * bernoulli (p + 1) - 1 / 6 := by
    have hg' : g = fun k ↦ (if k = 0 then (1 : ℚ) else 0) +
        (if k = 1 then -1 else 0) + (if k = 2 then 1 / 6 else 0) +
        (if k = p - 1 then -1 / 3 else 0) +
        (if k = p + 1 then 2 * bernoulli (p + 1) else 0) := by
      funext k
      dsimp [g]
      split_ifs <;> first | omega | ring
    rw [hg']
    simp only [sum_add_distrib, sum_ite_eq', mem_range]
    simp [show 0 < p + 2 by omega, show 1 < p + 2 by omega, show 2 < p + 2 by omega,
      show p - 1 < p + 2 by omega, show p + 1 < p + 2 by omega]
    ring
  rw [sum_sub_distrib, hf, hg] at hsum
  have h := pzero_mul hsum hhalf
  convert pzero_sub (pzero_zero p) h using 1
  ring

private lemma prime_square_dvd_pow_sub {p : ℕ} (x y : ℤ)
    (hxy : (p : ℤ) ∣ x - y) : (p : ℤ) ^ 2 ∣ x ^ (2 * p) - y ^ (2 * p) := by
  obtain ⟨t, ht⟩ := hxy
  have hx : x = y + (p : ℤ) * t := by linarith
  rw [hx]
  have hsq : (p : ℤ) ^ 2 ∣ ((p : ℤ) * t) ^ 2 := by
    rw [mul_pow]
    exact dvd_mul_right _ _
  have hmain := hsq.trans (sq_dvd_add_pow_sub_sub ((p : ℤ) * t) y (2 * p))
  have hlin : (p : ℤ) ^ 2 ∣ y ^ (2 * p - 1) * ((p : ℤ) * t) * (2 * p : ℕ) := by
    refine ⟨2 * t * y ^ (2 * p - 1), ?_⟩
    push_cast
    ring
  have heq : (y + (p : ℤ) * t) ^ (2 * p) - y ^ (2 * p) =
      ((y + (p : ℤ) * t) ^ (2 * p) - y ^ (2 * p - 1) * ((p : ℤ) * t) * (2 * p : ℕ) -
        y ^ (2 * p)) + y ^ (2 * p - 1) * ((p : ℤ) * t) * (2 * p : ℕ) := by ring
  rw [heq]
  exact dvd_add hmain hlin

/-- Multiplication by two permutes the residues; exponent `2*p` lifts this
permutation to a congruence modulo `p^2`. -/
private lemma prime_square_dvd_power_sum {p : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) : (p : ℤ) ^ 2 ∣ ∑ r ∈ range p, (r : ℤ) ^ (2 * p) := by
  classical
  have hp2 : ¬ p ∣ 2 := Nat.not_dvd_of_pos_of_lt (by decide) (by omega)
  have htwo : (2 : ZMod p) ≠ 0 := by
    exact mt (ZMod.natCast_eq_zero_iff 2 p).mp hp2
  let f : ZMod p → ℤ := fun x ↦ (x.val : ℤ) ^ (2 * p)
  have hperm : ∑ x : ZMod p, f (2 * x) = ∑ x : ZMod p, f x :=
    Equiv.sum_comp (Equiv.mulLeft₀ (2 : ZMod p) htwo) f
  have hterm : ∀ x : ZMod p, (p : ℤ) ^ 2 ∣ f (2 * x) - 2 ^ (2 * p) * f x := by
    intro x
    have hxy : (p : ℤ) ∣ ((2 * x).val : ℤ) - 2 * (x.val : ℤ) := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      push_cast
      simp
    simpa [f, mul_pow] using prime_square_dvd_pow_sub (p := p)
      ((2 * x).val : ℤ) (2 * (x.val : ℤ)) hxy
  have hsum := Finset.dvd_sum fun x (_ : x ∈ (univ : Finset (ZMod p))) ↦ hterm x
  rw [sum_sub_distrib, ← mul_sum, hperm] at hsum
  have hsumeq : (∑ x : ZMod p, f x) - 2 ^ (2 * p) * (∑ x : ZMod p, f x) =
      (1 - 2 ^ (2 * p)) * (∑ x : ZMod p, f x) := by ring
  rw [hsumeq] at hsum
  have hnot : ¬ (p : ℤ) ∣ (1 - 2 ^ (2 * p) : ℤ) := by
    intro h
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h
    have hc : ((1 - 2 ^ (2 * p) : ℤ) : ZMod p) = -3 := by
      push_cast
      rw [mul_comm 2 p, pow_mul, ZMod.pow_card]
      norm_num
    rw [hc] at hz
    have h3 : p ∣ 3 := by
      apply (ZMod.natCast_eq_zero_iff 3 p).mp
      simpa using neg_eq_zero.mp hz
    exact (Nat.not_dvd_of_pos_of_lt (by decide) (by omega)) h3
  have hcop : IsCoprime (p : ℤ) (1 - 2 ^ (2 * p) : ℤ) := by
    rw [Int.isCoprime_iff_nat_coprime, Int.natAbs_natCast]
    apply (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr
    exact mt Int.natCast_dvd.mpr hnot
  have hdiv := hcop.pow_left.dvd_of_dvd_mul_left hsum
  have heq : (∑ r ∈ range p, (r : ℤ) ^ (2 * p)) = ∑ x : ZMod p, f x := by
    refine sum_bij' (fun r _ ↦ (r : ZMod p)) (fun x _ ↦ x.val)
      (fun _ _ ↦ mem_univ _) (fun x _ ↦ mem_range.mpr (ZMod.val_lt x))
      (fun r hr ↦ ZMod.val_cast_of_lt (mem_range.mp hr))
      (fun x _ ↦ ZMod.natCast_zmod_val x) ?_
    intro r hr
    change (r : ℤ) ^ (2 * p) = ((r : ZMod p).val : ℤ) ^ (2 * p)
    rw [ZMod.val_cast_of_lt (mem_range.mp hr)]
  rw [heq]
  exact hdiv

/-- At index `2*p`, the Bernoulli numerator is divisible by `p`. -/
private theorem bernoulli_two_mul_prime_divisible {p : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) : PZero p (bernoulli (2 * p)) := by
  have hpne : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero Fact.out)
  have hden : ¬ p ∣ 2 * p + 1 := by
    intro hd
    have h := Nat.dvd_sub hd (show p ∣ 2 * p by exact dvd_mul_left p 2)
    have h1 : p ∣ 1 := by simpa using h
    exact (Nat.Prime.not_dvd_one Fact.out) h1
  let R : ℚ := ∑ i ∈ range (2 * p), bernoulli i * ((2 * p + 1).choose i : ℚ) *
    (p : ℚ) ^ (2 * p + 1 - i) / (2 * p + 1)
  have hR : PInt p (R / (p : ℚ) ^ 2) := by
    dsimp [R]
    rw [sum_div]
    refine (Rat.padicValuation p).map_sum_le fun i hi ↦ ?_
    have hi' := mem_range.mp hi
    by_cases htop : i = 2 * p - 1
    · subst i
      have hodd : Odd (2 * p - 1) := ⟨p - 1, by omega⟩
      rw [bernoulli_eq_zero_of_odd hodd (by omega)]
      simp
    · have hil : i ≤ 2 * p - 2 := by omega
      have hexp : 2 * p + 1 - i = (2 * p - i - 2) + 3 := by omega
      have heq : (bernoulli i * ((2 * p + 1).choose i : ℚ) *
          (p : ℚ) ^ (2 * p + 1 - i) / (2 * p + 1)) / (p : ℚ) ^ 2 =
          ((p : ℚ) * bernoulli i) * ((2 * p + 1).choose i : ℚ) *
          (p : ℚ) ^ (2 * p - i - 2) / (2 * p + 1) := by
        rw [hexp, pow_add]
        field_simp
      rw [heq]
      have hmul := pint_mul (pint_mul (pint_bernoulli_mul_prime hp5 i)
        (pint_nat p ((2 * p + 1).choose i))) (by
          simpa only [Nat.cast_pow] using pint_nat p (p ^ (2 * p - i - 2)))
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using
        pint_div_nat hmul hden
  obtain ⟨t, ht⟩ := prime_square_dvd_power_sum hp5
  have hsum : PInt p ((∑ r ∈ range p, (r : ℚ) ^ (2 * p)) / (p : ℚ) ^ 2) := by
    have htq : (∑ r ∈ range p, (r : ℚ) ^ (2 * p)) = (p : ℚ) ^ 2 * t := by
      exact_mod_cast ht
    rw [htq, mul_div_cancel_left₀ _ (pow_ne_zero 2 hpne)]
    exact pint_int p t
  have hF : (∑ r ∈ range p, (r : ℚ) ^ (2 * p)) = R + p * bernoulli (2 * p) := by
    rw [sum_range_pow, sum_range_succ]
    simp only [Nat.choose_succ_self_right, show 2 * p + 1 - 2 * p = 1 by omega,
      pow_one, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    dsimp [R]
    congr 1
    field_simp
  have heq : bernoulli (2 * p) / p =
      (∑ r ∈ range p, (r : ℚ) ^ (2 * p)) / (p : ℚ) ^ 2 - R / (p : ℚ) ^ 2 := by
    rw [hF]
    field_simp
    ring
  change PInt p (bernoulli (2 * p) / p)
  rw [heq]
  exact pint_sub hsum hR

private lemma divisors_two_prime {p d : ℕ} (hp : p.Prime) (hd : d ∣ 2 * p) :
    d = 1 ∨ d = 2 ∨ d = p ∨ d = 2 * p := by
  by_cases hpd : p ∣ d
  · obtain ⟨t, ht⟩ := hpd
    obtain ⟨c, hc⟩ := hd
    have htc : 2 = t * c := by
      apply Nat.eq_of_mul_eq_mul_left hp.pos
      calc p * 2 = 2 * p := by ring
        _ = d * c := hc
        _ = (p * t) * c := by rw [ht]
        _ = p * (t * c) := by ring
    have ht2 : t ∣ 2 := ⟨c, htc⟩
    rcases (Nat.dvd_prime Nat.prime_two).mp ht2 with h | h
    · right; right; left; simpa [h] using ht
    · right; right; right; simpa [h, mul_comm] using ht
  · have hcop : d.Coprime p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpd).symm
    have hd2 : d ∣ 2 := hcop.dvd_of_dvd_mul_left (by simpa [mul_comm] using hd)
    rcases (Nat.dvd_prime Nat.prime_two).mp hd2 with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

private lemma primes_for_bernoulli_two_prime {p : ℕ} (hp : p.Prime)
    (hq : (2 * p - 1).Prime) (h3 : 3 < p) :
    (range (2 * p + 2)).filter (fun r ↦ r.Prime ∧ (r - 1) ∣ 2 * p) = {2, 3} := by
  have hpmod : p % 3 ≠ 0 := by
    intro h
    rcases (Nat.dvd_prime hp).mp (Nat.dvd_of_mod_eq_zero h) with h | h <;> omega
  have hqmod : (2 * p - 1) % 3 ≠ 0 := by
    intro h
    rcases (Nat.dvd_prime hq).mp (Nat.dvd_of_mod_eq_zero h) with h | h <;> omega
  have hp1 : p % 3 = 1 := by omega
  have hpodd : p % 2 = 1 := (hp.eq_two_or_odd).resolve_left (by omega)
  ext r
  simp only [mem_filter, mem_range, mem_insert, mem_singleton]
  constructor
  · rintro ⟨hrlt, hrp, hrd⟩
    rcases divisors_two_prime hp hrd with h | h | h | h
    · left; have := hrp.two_le; omega
    · right; have := hrp.two_le; omega
    · have hr : r = p + 1 := by have := hrp.two_le; omega
      have hd2 : 2 ∣ r := by apply Nat.dvd_of_mod_eq_zero; omega
      rcases (Nat.dvd_prime hrp).mp hd2 with h | h <;> omega
    · have hr : r = 2 * p + 1 := by have := hrp.two_le; omega
      have hd3 : 3 ∣ r := by apply Nat.dvd_of_mod_eq_zero; omega
      rcases (Nat.dvd_prime hrp).mp hd3 with h | h <;> omega
  · rintro (rfl | rfl)
    · exact ⟨by omega, Nat.prime_two, by simp⟩
    · exact ⟨by omega, Nat.prime_three, by norm_num⟩

end SaurasAltuzarra

namespace SaurasAltuzarraConjectureI

/-- The definition in `FormalConjectures/OEIS/46969.lean`, verbatim. -/
def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let m := 2 * n
    let k := m * (m - 1)
    (bernoulli m / (k : ℚ)).den

open SaurasAltuzarra

/-- An exact denominator formula, stronger than Conjecture I. -/
theorem exact_denominator (p : ℕ) (hp : p.Prime) (hq : (2 * p - 1).Prime)
    (h3 : 3 < p) : a p = 12 * (2 * p - 1) := by
  let : Fact p.Prime := ⟨hp⟩
  have hpodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left (by omega)
  have hp5 : 5 ≤ p := by omega
  have hpne : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  let q := 2 * p - 1
  have hq5 : 5 ≤ q := by dsimp [q]; omega
  have hqp : q.Prime := hq
  obtain ⟨t, ht⟩ := Bernoulli.vonStaudt_clausen p
  rw [primes_for_bernoulli_two_prime hp hq h3] at ht
  norm_num at ht
  let N : ℤ := 6 * t - 5
  have hBN : bernoulli (2 * p) = (N : ℚ) / 6 := by dsimp [N]; push_cast; linarith [ht]
  have hNz : PZero p (N : ℚ) := by
    have h := pzero_mul (bernoulli_two_mul_prime_divisible hp5) (pint_nat p 6)
    simpa [hBN] using h
  obtain ⟨M, hM⟩ := (pzero_int_iff N).mp hNz
  have hBM : bernoulli (2 * p) = (p : ℚ) * M / 6 := by rw [hBN, hM]; push_cast; rfl
  have hN2 : ¬ (2 : ℤ) ∣ N := by dsimp [N]; omega
  have hN3 : ¬ (3 : ℤ) ∣ N := by dsimp [N]; omega
  have hM2 : ¬ 2 ∣ M.natAbs := by
    intro hd
    apply hN2
    rw [hM]
    exact dvd_mul_of_dvd_right (Int.natCast_dvd.mpr hd) _
  have hM3 : ¬ 3 ∣ M.natAbs := by
    intro hd
    apply hN3
    rw [hM]
    exact dvd_mul_of_dvd_right (Int.natCast_dvd.mpr hd) _
  have hcop12 : M.natAbs.Coprime 12 := by
    have hc2 := ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hM2).symm
    have hc3 := ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hM3).symm
    convert (hc2.pow_right 2).mul_right hc3 using 1
  have hcopq : M.natAbs.Coprime q := by
    let : Fact q.Prime := ⟨hqp⟩
    apply ((Nat.Prime.coprime_iff_not_dvd hqp).mpr ?_).symm
    intro hd
    have hMz : PZero q (M : ℚ) := (pzero_int_iff M).mpr (Int.natCast_dvd.mpr hd)
    have hq6 : ¬ q ∣ 6 := by
      intro hd
      have hdiv : q ∣ 2 ∨ q ∣ 3 := (hqp.dvd_mul).mp (by simpa using hd)
      rcases hdiv with h | h
      · exact (Nat.not_dvd_of_pos_of_lt (by decide) (by omega)) h
      · exact (Nat.not_dvd_of_pos_of_lt (by decide) (by omega)) h
    have hBz : PZero q (bernoulli (2 * p)) := by
      rw [hBM, mul_comm (p : ℚ) (M : ℚ)]
      exact pzero_mul (pzero_mul hMz (pint_nat q p)) (pint_inv_nat hq6)
    have hcon : PZero q (bernoulli (2 * p) - 1 / 12) := by
      have h := bernoulli_prime_add_one_congruence (p := q) hq5
      simpa [show q + 1 = 2 * p by dsimp [q]; omega] using h
    have h1 : PZero q (1 : ℚ) := by
      have hz := pzero_sub hBz hcon
      have h := pzero_mul hz (pint_nat q 12)
      convert h using 1
      ring
    have hqd1 : (q : ℤ) ∣ 1 := (pzero_int_iff 1).mp h1
    have hqd1' : q ∣ 1 := Int.natCast_dvd_natCast.mp hqd1
    exact hqp.not_dvd_one hqd1'
  have hcoefficient : bernoulli (2 * p) / ((2 * p * (2 * p - 1) : ℕ) : ℚ) =
      (M : ℚ) / ((12 * q : ℕ) : ℚ) := by
    have hd : ((2 * p * (2 * p - 1) : ℕ) : ℚ) = 2 * (p : ℚ) * (q : ℚ) := by
      dsimp [q]
      push_cast
      ring
    have h12 : ((12 * q : ℕ) : ℚ) = 12 * (q : ℚ) := by push_cast; rfl
    rw [hBM]
    rw [hd, h12]
    field_simp
    ring
  have hden : ((M : ℚ) / ((12 * q : ℕ) : ℚ)).den = 12 * q := by
    have hr := Rat.den_div_eq_of_coprime (a := M) (b := (12 * q : ℕ))
      (by have := hqp.pos; positivity) (by simpa [Int.natAbs_mul] using hcop12.mul_right hcopq)
    exact_mod_cast hr
  simp only [a, if_neg (by omega : p ≠ 0)]
  rw [hcoefficient, hden]

/-- Sauras Altuzarra's Conjecture I, with exactly the current repository's type. -/
theorem conjecture1 (p : ℕ) (hp : p.Prime) (hp' : (2 * p - 1).Prime) (h3 : 3 < p) :
    (a p / 12).Prime := by
  rw [exact_denominator p hp hp' h3, Nat.mul_div_cancel_left _ (by decide : 0 < 12)]
  exact hp'

end SaurasAltuzarraConjectureI

#print axioms SaurasAltuzarraConjectureI.exact_denominator
#print axioms SaurasAltuzarraConjectureI.conjecture1
