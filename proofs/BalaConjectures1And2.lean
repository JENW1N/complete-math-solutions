import FormalConjectures.OEIS.«79727»
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Algebra.QuadraticAlgebra.Basic


/-!
# Peter Bala's Conjectures 1 and 2 (OEIS A079727)

Authors: Jensen Kohlmeyer (jenwin@purdue.edu) and Liam Kruer (kruerl@purdue.edu).
Developed with substantial AI assistance from OpenAI's Codex in mathematical
exploration, proof development, Lean implementation, and manuscript preparation.

The main results are `A79727Cubic.conjecture1` and
`A79727Cubic.conjecture2`. They have exactly the types of the corresponding
Google DeepMind Formal Conjectures statements, without extra hypotheses.
The commands at the end check both types and audit their axiom dependencies.

All auxiliary mathematics is included in this file. The prime-level proof
is reused from the workspace's Conjecture 4 formalization by Jensen Kohlmeyer
and Liam Kruer, developed with substantial assistance from OpenAI Codex.
The additional argument uses a second-order binomial recurrence, polynomial
conservation identities in characteristic p, and Vandermonde's identity.

Source statements:
https://github.com/google-deepmind/formal-conjectures/blob/8432eac998110a563e03df65a28c117e97c8c142/FormalConjectures/OEIS/79727.lean
Prime-level reference: https://arxiv.org/abs/1012.3898, Theorem 3.2.

Requires Lean 4.33.1 and the matching Formal Conjectures/mathlib environment.
Only the three imports above are needed; there are no local proof imports.
From /Users/jenwin/Documents/ChatGPT/erdos, run:
bash scripts/lake.sh env lean "/Users/jenwin/Desktop/Peter Bala's Conjectures 1 and 2.lean"
-/

set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false


namespace A79727Proof

open Finset

def c (k : ℕ) : ℕ := Nat.choose (2 * k) k

theorem repository_index (S : Finset ℕ) :
    (∏ p ∈ S, p - 1) / 2 = ((∏ p ∈ S, p) - 1) / 2 := rfl

theorem eligible_odd {p : ℕ} (hp : OeisA3625.A p) : Odd p := by
  have hp2 : p ≠ 2 := by
    rintro rfl
    norm_num [OeisA3625.A] at hp
  exact hp.1.odd_of_ne_two hp2

theorem upper_half_dvd {p : ℕ} (hp : p.Prime) (a b : ℕ)
    (hb : (p - 1) / 2 < b) (hbp : b < p) : p ∣ c (a * p + b) := by
  let _ : Fact p.Prime := ⟨hp⟩
  have hm : (a * p + b) % p = b := by
    simp [Nat.add_mod, Nat.mod_eq_of_lt hbp]
  have htwob : p ≤ 2 * b := by omega
  have hmod : (2 * (a * p + b)) % p = 2 * b - p := by
    calc
      (2 * (a * p + b)) % p = (2 * b) % p := by
        simp [Nat.mul_add, Nat.add_mod, Nat.mul_mod]
      _ = 2 * b - p := by
        rw [Nat.mod_eq_sub_mod htwob, Nat.mod_eq_of_lt (by omega)]
  have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat
    (n := 2 * (a * p + b)) (k := a * p + b) (p := p)
  rw [hm, hmod, Nat.choose_eq_zero_of_lt (show 2 * b - p < b by omega),
    zero_mul] at h
  exact Nat.dvd_of_mod_eq_zero h

theorem upper_half_cube_dvd {p : ℕ} (hp : p.Prime) (a b : ℕ)
    (hb : (p - 1) / 2 < b) (hbp : b < p) : p ^ 2 ∣ c (a * p + b) ^ 3 := by
  obtain ⟨t, ht⟩ := upper_half_dvd hp a b hb hbp
  rw [ht]
  refine ⟨p * t ^ 3, ?_⟩
  ring

theorem full_block_of_half {p : ℕ} (hp : p.Prime) (a : ℕ)
    (hh : p ^ 2 ∣ ∑ b ∈ range ((p - 1) / 2 + 1), c (a * p + b) ^ 3) :
    p ^ 2 ∣ ∑ b ∈ range p, c (a * p + b) ^ 3 := by
  have hlen : (p - 1) / 2 + 1 ≤ p := by have := hp.two_le; omega
  have heq : p = ((p - 1) / 2 + 1) + (p - ((p - 1) / 2 + 1)) := by omega
  have hsplit := sum_range_add (fun b => c (a * p + b) ^ 3)
    ((p - 1) / 2 + 1) (p - ((p - 1) / 2 + 1))
  rw [← heq] at hsplit
  rw [hsplit]
  apply dvd_add hh
  apply Finset.dvd_sum
  intro b hb
  apply upper_half_cube_dvd hp
  · omega
  · simp only [mem_range] at hb
    omega

theorem prefix_of_full_blocks {p d : ℕ} {f : ℕ → ℕ}
    (hb : ∀ a, d ∣ ∑ b ∈ range p, f (a * p + b)) (a : ℕ) :
    d ∣ ∑ k ∈ range (a * p), f k := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Nat.succ_mul, sum_range_add]
    exact dvd_add ih (hb a)

theorem odd_multiple_of_half_blocks {p n : ℕ} (hp : p.Prime)
    (hn : Odd n) (hpn : p ∣ n)
    (hh : ∀ a, p ^ 2 ∣ ∑ b ∈ range ((p - 1) / 2 + 1), c (a * p + b) ^ 3) :
    p ^ 2 ∣ OeisA79727.a ((n - 1) / 2) := by
  obtain ⟨q, rfl⟩ := hpn
  have hq : Odd q := (Nat.odd_mul.mp hn).2
  obtain ⟨a, rfl⟩ := hq
  have hpodd : Odd p := (Nat.odd_mul.mp hn).1
  obtain ⟨t, ht⟩ := hpodd
  have hend : (p * (2 * a + 1) - 1) / 2 = a * p + (p - 1) / 2 := by
    have hexpand : p * (2 * a + 1) = 2 * (a * p) + p := by ring
    rw [hexpand]
    omega
  rw [hend]
  unfold OeisA79727.a
  change p ^ 2 ∣ ∑ k ∈ range (a * p + (p - 1) / 2 + 1), c k ^ 3
  rw [Nat.add_assoc, sum_range_add]
  exact dvd_add (prefix_of_full_blocks (fun a => full_block_of_half hp a (hh a)) a) (hh a)

theorem product_square_dvd {S : Finset ℕ} {N : ℕ}
    (hprime : ∀ p ∈ S, p.Prime) (hdiv : ∀ p ∈ S, p ^ 2 ∣ N) :
    (∏ p ∈ S, p) ^ 2 ∣ N := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p S hpS ih =>
    rw [prod_insert hpS, mul_pow]
    have hp : p.Prime := hprime p (mem_insert_self _ _)
    have hrest : ∀ q ∈ S, q.Prime := fun q hq => hprime q (mem_insert_of_mem hq)
    have hc : Nat.Coprime p (∏ q ∈ S, q) := by
      apply Nat.Coprime.prod_right
      intro q hq
      exact (hp.coprime_iff_not_dvd).mpr (by
        intro hd
        have heq : p = q := (Nat.prime_dvd_prime_iff_eq hp (hrest q hq)).mp hd
        exact hpS (heq ▸ hq))
    exact (hc.pow 2 2).mul_dvd_of_dvd_of_dvd
      (hdiv p (mem_insert_self _ _))
      (ih hrest (fun q hq => hdiv q (mem_insert_of_mem hq)))

theorem eligible_product_odd (S : Finset ℕ)
    (hS : ∀ p ∈ S, OeisA3625.A p) : Odd (∏ p ∈ S, p) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p S hpS ih =>
    rw [prod_insert hpS]
    exact (eligible_odd (hS p (mem_insert_self _ _))).mul
      (ih (fun q hq => hS q (mem_insert_of_mem hq)))

/-- The exceptional prime 3 can be handled directly from the binomial recurrence. -/
theorem half_blocks_three (a : ℕ) :
    3 ^ 2 ∣ ∑ b ∈ range ((3 - 1) / 2 + 1), c (a * 3 + b) ^ 3 := by
  have h := Nat.succ_mul_centralBinom_succ (a * 3)
  change (a * 3 + 1) * c (a * 3 + 1) = 2 * (2 * (a * 3) + 1) * c (a * 3) at h
  have hz := congrArg (fun n : ℕ => (n : ZMod 9) ^ 3) h
  push_cast at hz
  ring_nf at hz
  have h9 : (9 : ZMod 9) = 0 := rfl
  have h27 : (27 : ZMod 9) = 0 := rfl
  have h144 : (144 : ZMod 9) = 0 := rfl
  have h864 : (864 : ZMod 9) = 0 := rfl
  have h1728 : (1728 : ZMod 9) = 0 := rfl
  simp only [h9, h27, h144, h864, h1728, mul_zero, zero_add] at hz
  norm_num [Finset.sum_range_succ]
  apply (ZMod.natCast_eq_zero_iff _ 9).mp
  push_cast
  rw [Nat.add_comm (a * 3) 1, hz]
  ring_nf
  simp only [h9, mul_zero]

theorem all_odd_multiples_of_three {n : ℕ} (hn : Odd n) (h3 : 3 ∣ n) :
    9 ∣ OeisA79727.a ((n - 1) / 2) := by
  exact odd_multiple_of_half_blocks (by norm_num) hn h3 half_blocks_three

/-- The first-order product expansion, valid whenever the perturbation squares to zero. -/
theorem prod_first_order {R ι : Type*} [CommRing R] (s : Finset ι) (f : ι → R)
    (e : R) (he : e ^ 2 = 0) :
    (∏ i ∈ s, (1 + e * f i)) = 1 + e * ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [prod_insert hi, sum_insert hi, ih]
    linear_combination f i * (∑ j ∈ s, f j) * he

def harmonic {R : Type*} [AddCommMonoid R] [NatCast R] [Inv R] (n : ℕ) : R :=
  ∑ j ∈ range n, ((j + 1 : ℕ) : R)⁻¹

def correction {R : Type*} [Ring R] [Inv R] (n : ℕ) : R :=
  ∑ j ∈ range n, (2 * ((2 * j + 1 : ℕ) : R)⁻¹ - ((j + 1 : ℕ) : R)⁻¹)

theorem nilpotent_shift_step {R : Type*} [CommRing R]
    (e r s u v ri si E C : R) (he : e ^ 2 = 0)
    (hr : r * ri = 1) (hs : s * si = 1) (hrec : r * v = 2 * s * u) :
    (e + r) * (C * v * (1 + e * (E + 2 * si - ri))) =
      2 * (2 * e + s) * (C * u * (1 + e * E)) := by
  linear_combination C * (1 + e * E + 2 * e * si) * hrec -
    C * e * v * hr + 4 * C * e * u * hs +
    C * (v * (E + 2 * si - ri) - 4 * u * E) * he

theorem prime_square_zero (p : ℕ) : (p : ZMod (p ^ 2)) ^ 2 = 0 := by
  rw [← Nat.cast_pow, ZMod.natCast_self]

theorem small_nat_unit {p n : ℕ} (hp : p.Prime) (hn : 0 < n) (hnp : n < p) :
    IsUnit (n : ZMod (p ^ 2)) := by
  apply (ZMod.isUnit_natCast_iff_not_dvd_pow hp (by norm_num : 0 < 2)).mpr
  intro hd
  exact (not_le.mpr hnp) (Nat.le_of_dvd hn hd)

theorem shifted_c_mod {p : ℕ} (hp : p.Prime) (a b : ℕ) (hb : b ≤ (p - 1) / 2) :
    (c (a * p + b) : ZMod (p ^ 2)) =
      (c (a * p) : ZMod (p ^ 2)) * (c b : ZMod (p ^ 2)) *
        (1 + (a * p : ℕ) * correction b) := by
  induction b with
  | zero => simp [c, correction]
  | succ b ih =>
    have ih := ih (by omega)
    let e : ZMod (p ^ 2) := (a * p : ℕ)
    let r : ZMod (p ^ 2) := (b + 1 : ℕ)
    let s : ZMod (p ^ 2) := (2 * b + 1 : ℕ)
    have he : e ^ 2 = 0 := by
      dsimp [e]
      rw [Nat.cast_mul, mul_pow, prime_square_zero, mul_zero]
    have hrunit : IsUnit r := small_nat_unit hp (by omega) (by omega)
    have hsunit : IsUnit s := small_nat_unit hp (by omega) (by omega)
    have herunit : IsUnit (e + r) :=
      (show IsNilpotent e from ⟨2, he⟩).isUnit_add_right_of_commute
        hrunit (Commute.all _ _)
    have hrec : r * (c (b + 1) : ZMod (p ^ 2)) =
        2 * s * (c b : ZMod (p ^ 2)) := by
      dsimp [r, s]
      have hbrec : (b + 1) * c (b + 1) = 2 * (2 * b + 1) * c b :=
        Nat.succ_mul_centralBinom_succ b
      simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using
        congrArg (fun n : ℕ => (n : ZMod (p ^ 2))) hbrec
    have hshift : (e + r) * (c (a * p + (b + 1)) : ZMod (p ^ 2)) =
        2 * (2 * e + s) * (c (a * p + b) : ZMod (p ^ 2)) := by
      have ht := congrArg (fun n : ℕ => (n : ZMod (p ^ 2)))
        (Nat.succ_mul_centralBinom_succ (a * p + b))
      change (((a * p + b + 1) * c (a * p + b + 1) : ℕ) : ZMod (p ^ 2)) =
        ((2 * (2 * (a * p + b) + 1) * c (a * p + b) : ℕ) : ZMod (p ^ 2)) at ht
      push_cast at ht
      dsimp [e, r, s]
      push_cast
      simp only [Nat.add_assoc] at ht
      linear_combination ht
    apply herunit.mul_left_cancel
    rw [hshift, ih]
    have hstep := nilpotent_shift_step e r s (c b : ZMod (p ^ 2))
      (c (b + 1) : ZMod (p ^ 2)) r⁻¹ s⁻¹ (correction b)
      (c (a * p) : ZMod (p ^ 2)) he
      (ZMod.mul_inv_of_unit _ hrunit) (ZMod.mul_inv_of_unit _ hsunit) hrec
    simpa only [correction, sum_range_succ, Nat.succ_eq_add_one,
      add_sub_assoc, e, r, s] using hstep.symm

theorem harmonic_succ {R : Type*} [AddCommMonoid R] [NatCast R] [Inv R] (n : ℕ) :
    (harmonic (n + 1) : R) = harmonic n + ((n + 1 : ℕ) : R)⁻¹ := by
  simp [harmonic, sum_range_succ]

theorem correction_succ {R : Type*} [Ring R] [Inv R] (n : ℕ) :
    (correction (n + 1) : R) = correction n +
      (2 * ((2 * n + 1 : ℕ) : R)⁻¹ - ((n + 1 : ℕ) : R)⁻¹) := by
  simp only [correction, sum_range_succ]

theorem correction_eq_twice_harmonic {p : ℕ} (hp : p.Prime) (b : ℕ)
    (hb : b ≤ (p - 1) / 2) :
    (correction b : ZMod (p ^ 2)) = 2 * (harmonic (2 * b) - harmonic b) := by
  induction b with
  | zero => simp [correction, harmonic]
  | succ b ih =>
    have ih := ih (by omega)
    have hr := small_nat_unit hp (n := b + 1) (by omega) (by omega)
    have htwo := small_nat_unit hp (n := 2 * (b + 1)) (by omega) (by omega)
    have hi : (2 : ZMod (p ^ 2)) * ((2 * (b + 1) : ℕ) : ZMod (p ^ 2))⁻¹ =
        ((b + 1 : ℕ) : ZMod (p ^ 2))⁻¹ := by
      apply hr.mul_left_cancel
      calc
        _ = ((2 * (b + 1) : ℕ) : ZMod (p ^ 2)) *
            ((2 * (b + 1) : ℕ) : ZMod (p ^ 2))⁻¹ := by push_cast; ring
        _ = 1 := ZMod.mul_inv_of_unit _ htwo
        _ = _ := (ZMod.mul_inv_of_unit _ hr).symm
    change (correction (b + 1) : ZMod (p ^ 2)) =
      2 * (harmonic (2 * (b + 1)) - harmonic (b + 1))
    rw [correction_succ, ih, show 2 * (b + 1) = (2 * b + 1) + 1 by omega]
    simp only [harmonic_succ]
    rw [show 2 * b + 1 + 1 = 2 * (b + 1) by omega]
    linear_combination -hi

theorem cube_first_order {R : Type*} [CommRing R] (e x : R) (he : e ^ 2 = 0) :
    (1 + e * x) ^ 3 = 1 + 3 * e * x := by
  linear_combination (e * x ^ 3 + 3 * x ^ 2) * he

/-- Full shifted-binomial expansion. Keeping `c (a*p)` removes the need for Babbage's theorem. -/
theorem shifted_cube_mod {p : ℕ} (hp : p.Prime) (a b : ℕ) (hb : b ≤ (p - 1) / 2) :
    (c (a * p + b) : ZMod (p ^ 2)) ^ 3 =
      (c (a * p) : ZMod (p ^ 2)) ^ 3 * (c b : ZMod (p ^ 2)) ^ 3 *
        (1 + 6 * (a : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) *
          (harmonic (2 * b) - harmonic b)) := by
  have he : ((a * p : ℕ) : ZMod (p ^ 2)) ^ 2 = 0 := by
    rw [Nat.cast_mul, mul_pow, prime_square_zero, mul_zero]
  rw [shifted_c_mod hp a b hb, mul_pow, mul_pow, cube_first_order _ _ he,
    correction_eq_twice_harmonic hp b hb]
  push_cast
  ring

section Gegenbauer

open Polynomial

variable {R : Type*} [CommRing R]

/-- The polynomial `n! * C_n^λ`, defined without divisions. -/
noncomputable def gegen (l : R) : ℕ → Polynomial R
  | 0 => 1
  | 1 => 2 * C l * X
  | n + 2 => 2 * ((n : Polynomial R) + 1 + C l) * X * gegen l (n + 1) -
      ((n : Polynomial R) + 1) * ((n : Polynomial R) + 2 * C l) * gegen l n

theorem gegen_zero (l : R) : gegen l 0 = 1 := rfl

theorem gegen_one (l : R) : gegen l 1 = 2 * C l * X := rfl

theorem gegen_step (l : R) (n : ℕ) :
    gegen l (n + 2) = 2 * ((n : Polynomial R) + 1 + C l) * X * gegen l (n + 1) -
      ((n : Polynomial R) + 1) * ((n : Polynomial R) + 2 * C l) * gegen l n := rfl

noncomputable def rising (z : R) (n : ℕ) : R := (ascPochhammer R n).eval z

theorem rising_zero (z : R) : rising z 0 = 1 := by simp [rising]

theorem rising_succ (z : R) (n : ℕ) : rising z (n + 1) = rising z n * (z + n) :=
  ascPochhammer_succ_eval n z

theorem rising_succ_left (z : R) (n : ℕ) :
    rising z (n + 1) = z * rising (z + 1) n := by
  simp [rising, ascPochhammer_succ_left, eval_comp]

theorem rising_shift_two (z : R) (n : ℕ) :
    (z + n + 1) * rising z (n + 1) = z * (z + 1) * rising (z + 2) n := by
  have hs := rising_succ z (n + 1)
  rw [rising_succ_left z (n + 1), rising_succ_left (z + 1) n] at hs
  push_cast at hs
  convert hs.symm using 1 <;> ring

theorem gegen_eval_one (l : R) (n : ℕ) : (gegen l n).eval 1 = rising (2 * l) n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [gegen_zero, rising_zero]
  | one => simp [gegen_one, rising, ascPochhammer_one]
  | more n ih0 ih1 =>
    rw [gegen_step]
    simp only [eval_sub, eval_mul, eval_add, eval_natCast, eval_one, eval_ofNat,
      eval_C, eval_X, mul_one, ih0, ih1]
    rw [rising_succ (2 * l) (n + 1), rising_succ (2 * l) n]
    push_cast
    ring

theorem gegen_comp_neg_X (l : R) (n : ℕ) :
    (gegen l n).comp (-X) = (-1) ^ n * gegen l n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [gegen_zero]
  | one => simp [gegen_one, mul_comp]
  | more n ih0 ih1 =>
    rw [gegen_step]
    simp only [sub_comp, mul_comp, add_comp, natCast_comp, one_comp,
      ofNat_comp, C_comp, X_comp, ih0, ih1]
    rw [pow_add, pow_add]
    norm_num
    ring

/-- The coefficient of `(1-X²)^k` in the denominator-free square identity. -/
noncomputable def gegenSquareCoeff (l : R) (n k : ℕ) : R :=
  (n.choose k : R) * (-4) ^ k * rising l k ^ 2 *
    rising (2 * l + k) (n - k) * rising (2 * l + 2 * k) (n - k)

theorem gegenSquareCoeff_zero (l : R) (n : ℕ) :
    gegenSquareCoeff l n 0 = rising (2 * l) n ^ 2 := by
  simp [gegenSquareCoeff, rising_zero, pow_two]

theorem gegenSquareCoeff_diag (l : R) (n : ℕ) :
    gegenSquareCoeff l n n = (-4) ^ n * rising l n ^ 2 := by
  simp [gegenSquareCoeff, rising_zero]

theorem gegenSquareCoeff_above (l : R) {n k : ℕ} (h : n < k) :
    gegenSquareCoeff l n k = 0 := by
  simp [gegenSquareCoeff, Nat.choose_eq_zero_of_lt h]

theorem gegenSquareCoeff_raise_n (l : R) (n k : ℕ) (hk : k ≤ n) :
    ((n + 1 - k : ℕ) : R) * gegenSquareCoeff l (n + 1) k =
      (n + 1 : R) * (2 * l + n) * (2 * l + n + k) * gegenSquareCoeff l n k := by
  have hc := congrArg (fun m : ℕ => (m : R)) (Nat.choose_mul_succ_eq n k)
  push_cast at hc
  unfold gegenSquareCoeff
  rw [show n + 1 - k = (n - k) + 1 by omega]
  rw [rising_succ, rising_succ]
  push_cast
  rw [Nat.cast_sub hk]
  have hnk : ((n + 1 - k : ℕ) : R) = (n : R) + 1 - k := by
    rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
  rw [hnk] at hc
  linear_combination -((-4 : R) ^ k * rising l k ^ 2 *
    rising (2 * l + k) (n - k) * rising (2 * l + 2 * k) (n - k) *
    (2 * l + n) * (2 * l + n + k)) * hc

/-- The hypergeometric coefficient recurrence, with all denominators cleared. -/
theorem gegenSquareCoeff_raise_k (l : R) (n k : ℕ) (hk : k < n) :
    (k + 1 : R) * (k + 2 * l) * (2 * k + 2 * l + 1) *
      gegenSquareCoeff l n (k + 1) =
      2 * ((k : R) - n) * (k + n + 2 * l) * (k + l) * gegenSquareCoeff l n k := by
  obtain ⟨d, hd⟩ : ∃ d, n = k + d + 1 := ⟨n - k - 1, by omega⟩
  subst n
  have hc := congrArg (fun m : ℕ => (m : R))
    (Nat.choose_succ_right_eq (k + d + 1) k)
  rw [show k + d + 1 - k = d + 1 by omega] at hc
  push_cast at hc
  have hr := rising_shift_two (2 * l + 2 * (k : R)) d
  have ha : (2 * l + 2 * (k : R) + 2) = 2 * l + 2 * ((k : R) + 1) := by ring
  rw [ha] at hr
  unfold gegenSquareCoeff
  rw [show k + d + 1 - (k + 1) = d by omega,
    show k + d + 1 - k = d + 1 by omega, rising_succ l k,
    rising_succ_left (2 * l + k) d, pow_succ]
  push_cast
  simp only [← add_assoc] at *
  linear_combination
    -4 * (-4 : R) ^ k * rising l k ^ 2 * (l + k) ^ 2 * (2 * l + k) *
      (2 * l + 2 * k + 1) * rising (2 * l + k + 1) d *
      rising (2 * l + 2 * (k + 1)) d * hc +
    2 * (d + 1 : R) * (k + l) * ((k + d + 1).choose k : R) *
      (-4 : R) ^ k * rising l k ^ 2 * (2 * l + k) *
      rising (2 * l + k + 1) d * hr

theorem gegenSquareCoeff_recurrence (l : R) (n k : ℕ) :
    (k + 1 : R) * (k + 2 * l) * (2 * k + 2 * l + 1) *
      gegenSquareCoeff l n (k + 1) =
      2 * ((k : R) - n) * (k + n + 2 * l) * (k + l) * gegenSquareCoeff l n k := by
  rcases lt_trichotomy k n with hk | rfl | hk
  · exact gegenSquareCoeff_raise_k l n k hk
  · rw [gegenSquareCoeff_above l (by omega)]
    ring
  · rw [gegenSquareCoeff_above l hk, gegenSquareCoeff_above l (by omega)]
    ring

noncomputable def gegenSquareSeries (l : R) (n : ℕ) : Polynomial R :=
  ∑ k ∈ range (n + 1), monomial k (gegenSquareCoeff l n k)

theorem coeff_gegenSquareSeries (l : R) (n k : ℕ) :
    (gegenSquareSeries l n).coeff k = gegenSquareCoeff l n k := by
  by_cases hk : k < n + 1
  · simp [gegenSquareSeries, finsetSum_coeff, coeff_monomial, hk]
  · have hnk : n < k := by omega
    simp [gegenSquareSeries, finsetSum_coeff, coeff_monomial, hk,
      gegenSquareCoeff_above l hnk]

noncomputable def theta (P : Polynomial R) : Polynomial R := X * derivative P

theorem coeff_theta (P : Polynomial R) (k : ℕ) :
    (theta P).coeff k = (k : R) * P.coeff k := by
  cases k with
  | zero => simp [theta]
  | succ k => simp [theta, coeff_X_mul, coeff_derivative, mul_comm]

noncomputable def thetaAdd (a : R) (P : Polynomial R) : Polynomial R :=
  theta P + C a * P

theorem coeff_thetaAdd (a : R) (P : Polynomial R) (k : ℕ) :
    (thetaAdd a P).coeff k = ((k : R) + a) * P.coeff k := by
  simp only [thetaAdd, coeff_add, coeff_theta, coeff_C_mul]
  ring

/-- The third-order hypergeometric equation for the square series. -/
theorem gegenSquareSeries_theta_equation (l : R) (n : ℕ) :
    theta (thetaAdd (2 * l - 1)
      (2 * theta (gegenSquareSeries l n) + C (2 * l - 1) * gegenSquareSeries l n)) =
    2 * X * thetaAdd (-(n : R))
      (thetaAdd ((n : R) + 2 * l) (thetaAdd l (gegenSquareSeries l n))) := by
  ext k
  cases k with
  | zero => simp only [coeff_theta, Nat.cast_zero, zero_mul, mul_assoc, coeff_X_mul_zero, coeff_ofNat_mul, mul_zero]
  | succ k =>
    have h := gegenSquareCoeff_recurrence l n k
    simp only [coeff_theta, coeff_thetaAdd, coeff_add, coeff_C_mul,
      coeff_gegenSquareSeries]
    rw [show (2 : Polynomial R) = C (2 : R) by rfl,
      show C (2 : R) * X * thetaAdd (-(n : R))
        (thetaAdd ((n : R) + 2 * l) (thetaAdd l (gegenSquareSeries l n))) =
        C (2 : R) * (X * thetaAdd (-(n : R))
          (thetaAdd ((n : R) + 2 * l) (thetaAdd l (gegenSquareSeries l n)))) by ring]
    simp only [coeff_C_mul, coeff_X_mul, coeff_thetaAdd, coeff_theta, coeff_gegenSquareSeries]
    push_cast
    linear_combination h

/-- Differential operator for the square series in the variable `1-x²`. -/
noncomputable def seriesOp (l q : R) (F : Polynomial R) : Polynomial R :=
  2 * X ^ 2 * (1 - X) * derivative (derivative (derivative F)) +
  (C (6 * l + 3) * X - C (6 * l + 6) * X ^ 2) * derivative (derivative F) +
  (C (2 * l * (2 * l + 1)) - C (2 * ((l + 1) * (2 * l + 1) - q)) * X) *
    derivative F + C (2 * l * q) * F

theorem seriesOp_theta (l : R) (n : ℕ) (F : Polynomial R) :
    X * seriesOp l ((n : R) * (n + 2 * l)) F =
    theta (thetaAdd (2 * l - 1) (2 * theta F + C (2 * l - 1) * F)) -
      2 * X * thetaAdd (-(n : R))
        (thetaAdd ((n : R) + 2 * l) (thetaAdd l F)) := by
  simp only [seriesOp, theta, thetaAdd, derivative_add, derivative_sub,
    derivative_mul, derivative_C, derivative_X, derivative_ofNat,
    map_add, map_sub, map_mul, map_neg, map_natCast, map_ofNat, map_one,
    zero_mul, mul_zero, zero_add, add_zero, one_mul, derivative_zero, derivative_one, derivative_natCast]
  ring

theorem gegenSquareSeries_differential_equation (l : R) (n : ℕ) :
    seriesOp l ((n : R) * (n + 2 * l)) (gegenSquareSeries l n) = 0 := by
  have h : X * seriesOp l ((n : R) * (n + 2 * l)) (gegenSquareSeries l n) = 0 := by
    rw [seriesOp_theta, gegenSquareSeries_theta_equation, sub_self]
  ext k
  have hk := congrArg (fun P : Polynomial R => P.coeff (k + 1)) h
  simpa only [coeff_X_mul, coeff_zero] using hk

/-- The symmetric square of the Gegenbauer differential operator. -/
noncomputable def squareOp (l q : R) (F : Polynomial R) : Polynomial R :=
  (1 - X ^ 2) ^ 2 * derivative (derivative (derivative F)) -
  C (3 * (2 * l + 1)) * X * (1 - X ^ 2) * derivative (derivative F) +
  (C (4 * q) * (1 - X ^ 2) - C (2 * l + 1) +
    C (2 * (2 * l + 1) ^ 2 - (2 * l + 1)) * X ^ 2) * derivative F -
  C (8 * l * q) * X * F

theorem squareOp_comp (l q : R) (F : Polynomial R) :
    squareOp l q (F.comp (1 - X ^ 2)) =
      -4 * X * (seriesOp l q F).comp (1 - X ^ 2) := by
  simp only [squareOp, seriesOp, derivative_comp, derivative_sub, derivative_pow,
    derivative_mul, derivative_C, derivative_X, derivative_one, derivative_ofNat,
    add_comp, sub_comp, mul_comp, pow_comp, C_comp, X_comp, one_comp, ofNat_comp,
    map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
    zero_mul, mul_zero, zero_add, add_zero, mul_one, one_mul, pow_one,
    derivative_zero, C_ofNat, C_1, C_0, map_natCast]
  norm_num
  ring

/-- Coupled derivative identities for the factorial-normalized Gegenbauer polynomials. -/
theorem gegen_derivative_pair (l : R) (n : ℕ) :
    derivative (gegen l (n + 1)) = ((n : Polynomial R) + 1) *
      (X * derivative (gegen l n) + ((n : Polynomial R) + 2 * C l) * gegen l n) ∧
    X * derivative (gegen l (n + 1)) - ((n : Polynomial R) + 1) * gegen l (n + 1) =
      ((n : Polynomial R) + 1) * derivative (gegen l n) := by
  induction n with
  | zero =>
    simp [gegen_zero, gegen_one, derivative_mul]
    ring
  | succ n ih =>
    have hd : derivative (gegen l (n + 2)) =
        2 * ((n : Polynomial R) + 1 + C l) *
          (gegen l (n + 1) + X * derivative (gegen l (n + 1))) -
        ((n : Polynomial R) + 1) * ((n : Polynomial R) + 2 * C l) *
          derivative (gegen l n) := by
      rw [gegen_step]
      simp only [derivative_sub, derivative_mul, derivative_add, derivative_natCast,
        derivative_one, derivative_ofNat, derivative_C, derivative_X,
        zero_add, add_zero, zero_mul, mul_zero, mul_one]
      ring
    have ha : derivative (gegen l (n + 2)) = ((n : Polynomial R) + 2) *
        (X * derivative (gegen l (n + 1)) +
          ((n : Polynomial R) + 1 + 2 * C l) * gegen l (n + 1)) := by
      linear_combination hd + ((n : Polynomial R) + 2 * C l) * ih.2
    constructor
    · simpa only [Nat.cast_add, Nat.cast_one, Nat.succ_eq_add_one, add_assoc,
        show (1 : Polynomial R) + 1 = 2 by ring] using ha
    · change X * derivative (gegen l (n + 2)) -
        (((n + 1 : ℕ) : Polynomial R) + 1) * gegen l (n + 2) =
        (((n + 1 : ℕ) : Polynomial R) + 1) * derivative (gegen l (n + 1))
      rw [ha, gegen_step]
      push_cast
      linear_combination ((n : Polynomial R) + 2) * X * ih.2 -
        ((n : Polynomial R) + 2) * ih.1

/-- The Gegenbauer differential equation, valid over every commutative ring. -/
theorem gegen_differential_equation (l : R) (n : ℕ) :
    (1 - X ^ 2) * derivative (derivative (gegen l n)) -
      (2 * C l + 1) * X * derivative (gegen l n) +
      (n : Polynomial R) * ((n : Polynomial R) + 2 * C l) * gegen l n = 0 := by
  cases n with
  | zero => simp [gegen_zero]
  | succ n =>
    have ha := (gegen_derivative_pair l n).1
    have hb := (gegen_derivative_pair l n).2
    have hda := congrArg derivative ha
    have hdb := congrArg derivative hb
    simp only [derivative_mul, derivative_add, derivative_sub, derivative_natCast,
      derivative_one, derivative_ofNat, derivative_C, derivative_X,
      zero_add, add_zero, zero_mul, mul_zero, one_mul] at hda hdb
    push_cast
    linear_combination hda - X * hdb - ((n : Polynomial R) + 1 + 2 * C l) * hb

theorem squareOp_of_equation (l q : R) (g : Polynomial R)
    (h : (1 - X ^ 2) * derivative (derivative g) -
      C (2 * l + 1) * X * derivative g + C q * g = 0) :
    squareOp l q (g ^ 2) = 0 := by
  have hd := congrArg derivative h
  simp only [derivative_sub, derivative_add, derivative_mul, derivative_pow,
    derivative_C, derivative_X, derivative_one, derivative_zero,
    zero_add, add_zero, zero_mul, mul_zero, mul_one, one_mul, pow_one,
    C_ofNat, C_1] at hd
  simp only [squareOp, pow_two, derivative_mul, derivative_add]
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, map_one, map_natCast] at h hd ⊢
  norm_num at h hd ⊢
  linear_combination 2 * (1 - X ^ 2) * g * hd +
    (6 * (1 - X ^ 2) * derivative g - 8 * C l * X * g) * h

theorem gegen_square_equation (l : R) (n : ℕ) :
    squareOp l ((n : R) * (n + 2 * l)) (gegen l n ^ 2) = 0 := by
  apply squareOp_of_equation
  simpa only [map_add, map_mul, map_natCast, map_ofNat, map_one] using
    gegen_differential_equation l n

noncomputable def shiftedSquareOp (l q : R) (F : Polynomial R) : Polynomial R :=
  (4 * X ^ 2 + 4 * X ^ 3 + X ^ 4) * derivative (derivative (derivative F)) +
  (C (6 * (2 * l + 1)) * X + C (9 * (2 * l + 1)) * X ^ 2 +
    C (3 * (2 * l + 1)) * X ^ 3) * derivative (derivative F) +
  (C (2 * (2 * l + 1) * (2 * l)) +
    C (4 * (2 * l + 1) ^ 2 - 2 * (2 * l + 1) - 8 * q) * X +
    C (2 * (2 * l + 1) ^ 2 - (2 * l + 1) - 4 * q) * X ^ 2) * derivative F -
  C (8 * l * q) * (1 + X) * F

theorem shiftedSquareOp_eq (l q : R) (F : Polynomial R) :
    shiftedSquareOp l q (F.comp (X + 1)) = (squareOp l q F).comp (X + 1) := by
  simp only [shiftedSquareOp, squareOp, derivative_comp, derivative_add,
    derivative_mul, derivative_X, derivative_one, derivative_zero,
    add_comp, sub_comp, mul_comp, pow_comp, C_comp, X_comp, one_comp,
    zero_add, add_zero, zero_mul, mul_zero, mul_one, one_mul,
    map_add, map_sub, map_mul, map_pow, map_ofNat, map_one, ofNat_comp]
  norm_num
  ring

theorem shiftedSquareOp_theta (l q : R) (F : Polynomial R) :
    shiftedSquareOp l q F =
    2 * thetaAdd (2 * l) (2 * theta (derivative F) + C (2 * l + 1) * derivative F) +
    (4 * theta (theta (theta F)) + C (18 * l - 3) * theta (theta F) +
      C (16 * l ^ 2 - 6 * l + 1 - 8 * q) * theta F - C (8 * l * q) * F) +
    X * (theta (theta (theta F)) + C (6 * l) * theta (theta F) +
      C (8 * l ^ 2 - 4 * q) * theta F - C (8 * l * q) * F) := by
  simp only [shiftedSquareOp, thetaAdd, theta, derivative_add, derivative_mul,
    derivative_X, derivative_C, derivative_zero, derivative_one,
    derivative_ofNat, zero_add, add_zero, zero_mul, mul_zero, mul_one, one_mul,
    map_add, map_sub, map_mul, map_pow, map_ofNat, map_one, ofNat_comp]
  norm_num
  ring

theorem coeff_shiftedSquareOp_of_vanishing (l q : R) (F : Polynomial R) (k : ℕ)
    (hz : ∀ j ≤ k, F.coeff j = 0) :
    (shiftedSquareOp l q F).coeff k =
      2 * ((k : R) + 1) * (k + 2 * l) * (2 * k + 2 * l + 1) * F.coeff (k + 1) := by
  rw [shiftedSquareOp_theta]
  cases k with
  | zero =>
    simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
      coeff_thetaAdd, coeff_theta, coeff_derivative, coeff_X_mul_zero,
      hz 0 (by omega), Nat.cast_zero, Nat.cast_one]
    ring
  | succ k =>
    simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
      coeff_thetaAdd, coeff_theta, coeff_derivative, coeff_X_mul,
      hz (k + 1) (by omega), hz k (by omega)]
    push_cast
    ring

theorem squareOp_unique [IsDomain R] (l q : R)
    (hnonzero : ∀ k : ℕ,
      2 * ((k : R) + 1) * (k + 2 * l) * (2 * k + 2 * l + 1) ≠ 0)
    (F : Polynomial R) (heq : squareOp l q F = 0) (hval : F.eval 1 = 0) : F = 0 := by
  have hs : shiftedSquareOp l q (F.comp (X + 1)) = 0 := by
    rw [shiftedSquareOp_eq, heq, zero_comp]
  suffices h : F.comp (X + 1) = 0 by
    exact (comp_X_add_C_eq_zero_iff (t := 1)).mp (by simpa using h)
  ext k
  change (F.comp (X + 1)).coeff k = 0
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero => simpa only [coeff_zero_eq_eval_zero, eval_comp,
        eval_add, eval_X, eval_one, zero_add] using hval
    | succ k =>
      have hh := congrArg (fun P : Polynomial R => P.coeff k) hs
      rw [coeff_shiftedSquareOp_of_vanishing l q _ k
        (fun j hj => ih j (by omega)), coeff_zero] at hh
      exact (mul_eq_zero.mp hh).resolve_left (hnonzero k)

theorem squareOp_sub (l q : R) (F G : Polynomial R) :
    squareOp l q (F - G) = squareOp l q F - squareOp l q G := by
  simp only [squareOp, derivative_sub]
  ring

theorem gegen_square_of_nondegenerate [IsDomain R] (l : R) (n : ℕ)
    (hnonzero : ∀ k : ℕ,
      2 * ((k : R) + 1) * (k + 2 * l) * (2 * k + 2 * l + 1) ≠ 0) :
    gegen l n ^ 2 = (gegenSquareSeries l n).comp (1 - X ^ 2) := by
  apply sub_eq_zero.mp
  apply squareOp_unique l ((n : R) * (n + 2 * l)) hnonzero
  · rw [squareOp_sub, gegen_square_equation, squareOp_comp,
      gegenSquareSeries_differential_equation, zero_comp, mul_zero, sub_self]
  · simp only [eval_sub, eval_pow, gegen_eval_one, eval_comp, eval_sub,
      eval_one, eval_pow, eval_X, one_pow, sub_self]
    rw [← coeff_zero_eq_eval_zero, coeff_gegenSquareSeries, gegenSquareCoeff_zero, sub_self]

theorem variable_nondegenerate (k : ℕ) :
    2 * ((k : Polynomial ℤ) + 1) * ((k : Polynomial ℤ) + 2 * X) *
      (2 * (k : Polynomial ℤ) + 2 * X + 1) ≠ 0 := by
  have hk : (k : Polynomial ℤ) + 1 ≠ 0 := by
    intro h
    have he := congrArg (fun P : Polynomial ℤ => P.eval 0) h
    simp only [eval_add, eval_natCast, eval_one, eval_zero] at he
    omega
  have h1 : (k : Polynomial ℤ) + 2 * X ≠ 0 := by
    intro h
    have := congrArg (fun P : Polynomial ℤ => P.coeff 1) h
    simp only [coeff_add, coeff_ofNat_mul, coeff_X, coeff_natCast_ite,
      coeff_one, coeff_zero] at this
    norm_num at this
  have h2 : 2 * (k : Polynomial ℤ) + 2 * X + 1 ≠ 0 := by
    intro h
    have := congrArg (fun P : Polynomial ℤ => P.coeff 1) h
    simp only [coeff_add, coeff_ofNat_mul, coeff_X, coeff_natCast_ite,
      coeff_one, coeff_zero] at this
    norm_num at this
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hk) h1) h2

theorem gegen_square_universal (n : ℕ) :
    gegen (X : Polynomial ℤ) n ^ 2 =
      (gegenSquareSeries (X : Polynomial ℤ) n).comp (1 - X ^ 2) :=
  gegen_square_of_nondegenerate X n variable_nondegenerate

theorem map_rising {S : Type*} [CommRing S] (f : R →+* S) (l : R) (n : ℕ) :
    f (rising l n) = rising (f l) n := by
  induction n with
  | zero => simp [rising_zero]
  | succ n ih => simp only [rising_succ, map_mul, map_add, map_natCast, ih]

theorem map_gegen {S : Type*} [CommRing S] (f : R →+* S) (l : R) (n : ℕ) :
    (gegen l n).map f = gegen (f l) n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [gegen_zero]
  | one => simp [gegen_one]
  | more n ih0 ih1 => simp [gegen_step, ih0, ih1]

theorem map_gegenSquareCoeff {S : Type*} [CommRing S] (f : R →+* S) (l : R) (n k : ℕ) :
    f (gegenSquareCoeff l n k) = gegenSquareCoeff (f l) n k := by
  simp only [gegenSquareCoeff, map_mul, map_pow, map_neg, map_ofNat, map_natCast,
    map_add, map_rising]

theorem map_gegenSquareSeries {S : Type*} [CommRing S] (f : R →+* S) (l : R) (n : ℕ) :
    (gegenSquareSeries l n).map f = gegenSquareSeries (f l) n := by
  ext k
  simp only [coeff_map, coeff_gegenSquareSeries, map_gegenSquareCoeff]

/-- The finite Gegenbauer square identity over any commutative ring. -/
theorem gegen_square (l : R) (n : ℕ) :
    gegen l n ^ 2 = (gegenSquareSeries l n).comp (1 - X ^ 2) := by
  let f : Polynomial ℤ →+* R := eval₂RingHom (Int.castRingHom R) l
  have h := congrArg (Polynomial.map f) (gegen_square_universal n)
  simpa only [Polynomial.map_pow, map_gegen, map_comp, map_gegenSquareSeries,
    Polynomial.map_sub, Polynomial.map_one, Polynomial.map_X,
    f, coe_eval₂RingHom, eval₂_X] using h

noncomputable def scaledGegenCoeff (l : R) (n k : ℕ) : R :=
  64 ^ k * gegenSquareCoeff l n k

theorem scaledGegenCoeff_zero (l : R) (n : ℕ) :
    scaledGegenCoeff l n 0 = rising (2 * l) n ^ 2 := by
  simp [scaledGegenCoeff, gegenSquareCoeff_zero]

theorem scaledGegenCoeff_recurrence (l : R) (n k : ℕ) :
    (k + 1 : R) * (k + 2 * l) * (2 * k + 2 * l + 1) *
      scaledGegenCoeff l n (k + 1) =
      128 * ((k : R) - n) * (k + n + 2 * l) * (k + l) * scaledGegenCoeff l n k := by
  unfold scaledGegenCoeff
  rw [pow_succ]
  linear_combination (64 : R) ^ (k + 1) * gegenSquareCoeff_recurrence l n k

theorem scaledGegenCoeff_square (u : R) (hu : u ^ 2 = -63) (n : ℕ) :
    ((gegen (X : Polynomial R) n).eval (C u)) ^ 2 =
      ∑ k ∈ range (n + 1), scaledGegenCoeff (X : Polynomial R) n k := by
  have h := congrArg (fun P : Polynomial (Polynomial R) => P.eval (C u))
    (gegen_square (X : Polynomial R) n)
  have hu' : (C u : Polynomial R) ^ 2 = -63 := by rw [← C_pow, hu]; simp only [map_neg]; rfl
  simp only [eval_pow, eval_comp, gegenSquareSeries, eval_finsetSum,
    eval_monomial, eval_sub, eval_one, eval_X, hu'] at h
  norm_num at h
  simpa only [scaledGegenCoeff, mul_comm] using h

section HalfParameter

variable {K : Type*} [Field K]

theorem scaledGegenCoeff_half_value_recurrence (n k : ℕ) (h2 : (2 : K) ≠ 0)
    (hn : (n : K) = -(1 / 2)) :
    2 * ((k : K) + 1) ^ 3 * (scaledGegenCoeff (X : Polynomial K) n (k + 1)).eval (1 / 2) =
      16 * (2 * (k : K) + 1) ^ 3 * (scaledGegenCoeff (X : Polynomial K) n k).eval (1 / 2) := by
  have h := congrArg (fun P : Polynomial K => P.eval (1 / 2))
    (scaledGegenCoeff_recurrence (X : Polynomial K) n k)
  simp only [eval_mul, eval_add, eval_sub, eval_natCast, eval_ofNat, eval_one, eval_X, hn] at h
  convert h using 1 <;> field_simp <;> ring

theorem scaledGegenCoeff_half_derivative_recurrence (n k : ℕ) (h2 : (2 : K) ≠ 0)
    (hn : (n : K) = -(1 / 2)) :
    2 * ((k : K) + 1) ^ 3 *
        (derivative (scaledGegenCoeff (X : Polynomial K) n (k + 1))).eval (1 / 2) +
      6 * ((k : K) + 1) ^ 2 * (scaledGegenCoeff (X : Polynomial K) n (k + 1)).eval (1 / 2) =
    16 * (2 * (k : K) + 1) ^ 3 *
        (derivative (scaledGegenCoeff (X : Polynomial K) n k)).eval (1 / 2) +
      96 * (2 * (k : K) + 1) ^ 2 * (scaledGegenCoeff (X : Polynomial K) n k).eval (1 / 2) := by
  have h := congrArg (fun P : Polynomial K => (derivative P).eval (1 / 2))
    (scaledGegenCoeff_recurrence (X : Polynomial K) n k)
  simp only [derivative_mul, derivative_add, derivative_sub, derivative_natCast,
    derivative_ofNat, derivative_one, derivative_X, eval_add, eval_sub, eval_mul,
    eval_natCast, eval_ofNat, eval_one, eval_X, eval_zero, hn, zero_add, add_zero,
    zero_mul, mul_zero, one_mul, mul_one] at h
  convert h using 1 <;> field_simp <;> ring

theorem central_cube_recurrence (k : ℕ) :
    ((k : K) + 1) ^ 3 * (c (k + 1) : K) ^ 3 =
      8 * (2 * (k : K) + 1) ^ 3 * (c k : K) ^ 3 := by
  have h := congrArg (fun n : ℕ => (n : K)) (Nat.succ_mul_centralBinom_succ k)
  change (((k + 1) * c (k + 1) : ℕ) : K) = ((2 * (2 * k + 1) * c k : ℕ) : K) at h
  push_cast at h
  have h3 := congrArg (fun x : K => x ^ 3) h
  convert h3 using 1 <;> ring

theorem half_choose_identity (n : ℕ) (h2 : (2 : K) ≠ 0)
    (hn : (n : K) = -(1 / 2))
    (hden : ∀ j : ℕ, 0 < j → j ≤ n → (j : K) ≠ 0) (k : ℕ) (hk : k ≤ n) :
    (n.choose k : K) * (-4) ^ k = (c k : K) := by
  induction k with
  | zero => simp [c]
  | succ k ih =>
    have hr : (k : K) + 1 ≠ 0 := by simpa using hden (k + 1) (by omega) hk
    have hch := congrArg (fun m : ℕ => (m : K)) (Nat.choose_succ_right_eq n k)
    push_cast at hch
    rw [Nat.cast_sub (by omega : k ≤ n)] at hch
    have hc := congrArg (fun m : ℕ => (m : K)) (Nat.succ_mul_centralBinom_succ k)
    change (((k + 1) * c (k + 1) : ℕ) : K) = ((2 * (2 * k + 1) * c k : ℕ) : K) at hc
    push_cast at hc
    apply mul_left_cancel₀ hr
    rw [pow_succ]
    calc
      _ = (-4 : K) ^ k * (-4) * ((n.choose k : K) * ((n : K) - k)) := by
        linear_combination (-4 : K) ^ k * (-4) * hch
      _ = 2 * (2 * (k : K) + 1) * ((n.choose k : K) * (-4) ^ k) := by
        rw [hn]
        field_simp
        ring
      _ = _ := by rw [ih (by omega)]; exact hc.symm

theorem harmonic_difference_succ (k : ℕ) (h2 : (2 : K) ≠ 0)
    (hr : (k : K) + 1 ≠ 0) :
    (harmonic (2 * (k + 1)) - harmonic (k + 1) : K) =
      (harmonic (2 * k) - harmonic k) + (2 * (k : K) + 1)⁻¹ -
        (2 * ((k : K) + 1))⁻¹ := by
  rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega]
  simp only [harmonic_succ]
  push_cast
  have hi : (2 * (k : K) + 1 + 1)⁻¹ = (2 * ((k : K) + 1))⁻¹ := by congr 1; ring
  rw [hi]
  have hj : ((k : K) + 1)⁻¹ = 2 * (2 * ((k : K) + 1))⁻¹ := by field_simp
  rw [hj]
  ring

theorem derivative_recurrence_step (r s a b d v z w : K)
    (h2 : (2 : K) ≠ 0) (hr : r ≠ 0) (hs : s ≠ 0)
    (hc : r ^ 3 * z = 8 * s ^ 3 * v)
    (hd : 2 * r ^ 3 * w + 6 * r ^ 2 * a * z =
      16 * s ^ 3 * (b * v + 6 * a * v * d) + 96 * s ^ 2 * a * v) :
    w = b * z + 6 * a * z * (d + s⁻¹ - (2 * r)⁻¹) := by
  apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero h2 (pow_ne_zero 3 hr)) hs)
  calc
    2 * r ^ 3 * s * w =
        (2 * b * s + 12 * a * d * s + 12 * a) * r ^ 3 * z -
          6 * r ^ 2 * a * z * s := by
      linear_combination s * hd - (2 * b * s + 12 * a * d * s + 12 * a) * hc
    _ = 2 * r ^ 3 * s * (b * z + 6 * a * z * (d + s⁻¹ - (2 * r)⁻¹)) := by
      field_simp
      ring

theorem scaledGegenCoeff_half_value (n : ℕ) (h2 : (2 : K) ≠ 0)
    (hn : (n : K) = -(1 / 2))
    (hden : ∀ j : ℕ, 0 < j → j ≤ n → (j : K) ≠ 0) (k : ℕ) (hk : k ≤ n) :
    (scaledGegenCoeff (X : Polynomial K) n k).eval (1 / 2) =
      (scaledGegenCoeff (X : Polynomial K) n 0).eval (1 / 2) * (c k : K) ^ 3 := by
  induction k with
  | zero => simp [c]
  | succ k ih =>
    have hr : (k : K) + 1 ≠ 0 := by simpa using hden (k + 1) (by omega) hk
    have hv := scaledGegenCoeff_half_value_recurrence n k h2 hn
    rw [ih (by omega)] at hv
    have hc := central_cube_recurrence (K := K) k
    apply mul_left_cancel₀ (mul_ne_zero h2 (pow_ne_zero 3 hr))
    linear_combination hv -
      2 * (scaledGegenCoeff (X : Polynomial K) n 0).eval (1 / 2) * hc

theorem scaledGegenCoeff_half_derivative (n : ℕ) (h2 : (2 : K) ≠ 0)
    (hn : (n : K) = -(1 / 2))
    (hden : ∀ j : ℕ, 0 < j → j ≤ n → (j : K) ≠ 0)
    (hodd : ∀ j : ℕ, j < n → 2 * (j : K) + 1 ≠ 0) (k : ℕ) (hk : k ≤ n) :
    (derivative (scaledGegenCoeff (X : Polynomial K) n k)).eval (1 / 2) =
      (derivative (scaledGegenCoeff (X : Polynomial K) n 0)).eval (1 / 2) * (c k : K) ^ 3 +
      6 * (scaledGegenCoeff (X : Polynomial K) n 0).eval (1 / 2) * (c k : K) ^ 3 *
        (harmonic (2 * k) - harmonic k) := by
  induction k with
  | zero => simp [c, harmonic]
  | succ k ih =>
    have hr : (k : K) + 1 ≠ 0 := by simpa using hden (k + 1) (by omega) hk
    have hd := scaledGegenCoeff_half_derivative_recurrence n k h2 hn
    rw [scaledGegenCoeff_half_value n h2 hn hden (k + 1) hk,
      scaledGegenCoeff_half_value n h2 hn hden k (by omega), ih (by omega)] at hd
    rw [harmonic_difference_succ k h2 hr]
    apply derivative_recurrence_step ((k : K) + 1) (2 * (k : K) + 1)
      _ _ _ _ _ _ h2 hr (hodd k (by omega)) (central_cube_recurrence k)
    convert hd using 1 <;> ring

theorem rising_one_ne_zero (n : ℕ)
    (hden : ∀ j : ℕ, 0 < j → j ≤ n → (j : K) ≠ 0) : rising (1 : K) n ≠ 0 := by
  induction n with
  | zero => simp [rising_zero]
  | succ n ih =>
    rw [rising_succ]
    apply mul_ne_zero (ih (fun j hj hjn => hden j hj (by omega)))
    have h := hden (n + 1) (by omega) (by omega)
    simpa only [Nat.cast_add, Nat.cast_one, add_comm] using h

theorem scaledGegenCoeff_initial_ne_zero (n : ℕ) (h2 : (2 : K) ≠ 0)
    (hden : ∀ j : ℕ, 0 < j → j ≤ n → (j : K) ≠ 0) :
    (scaledGegenCoeff (X : Polynomial K) n 0).eval (1 / 2) ≠ 0 := by
  have hm := map_rising (evalRingHom (1 / 2 : K)) (2 * (X : Polynomial K)) n
  simp only [coe_evalRingHom, eval_mul, eval_ofNat, eval_X] at hm
  have ht : (2 : K) * (1 / 2) = 1 := by field_simp
  rw [ht] at hm
  rw [scaledGegenCoeff_zero, eval_pow, hm]
  exact pow_ne_zero 2 (rising_one_ne_zero n hden)

/-- Concrete harmonic cancellation from the finite square identity. -/
theorem harmonic_cancellation_gegenbauer (n : ℕ) (h2 : (2 : K) ≠ 0)
    (h6 : (6 : K) ≠ 0) (hn : (n : K) = -(1 / 2))
    (hden : ∀ j : ℕ, 0 < j → j ≤ n → (j : K) ≠ 0)
    (hodd : ∀ j : ℕ, j < n → 2 * (j : K) + 1 ≠ 0)
    (u : K) (hu : u ^ 2 = -63)
    (hz : (∑ k ∈ range (n + 1), (c k : K) ^ 3) = 0) :
    (∑ k ∈ range (n + 1), (c k : K) ^ 3 * (harmonic (2 * k) - harmonic k)) = 0 := by
  let Q : Polynomial K := (gegen (X : Polynomial K) n).eval (C u)
  let a : K := (scaledGegenCoeff (X : Polynomial K) n 0).eval (1 / 2)
  let b : K := (derivative (scaledGegenCoeff (X : Polynomial K) n 0)).eval (1 / 2)
  have ha : a ≠ 0 := scaledGegenCoeff_initial_ne_zero n h2 hden
  have hsquare : Q ^ 2 = ∑ k ∈ range (n + 1), scaledGegenCoeff (X : Polynomial K) n k :=
    scaledGegenCoeff_square u hu n
  have hv : (Q ^ 2).eval (1 / 2) = 0 := by
    rw [hsquare, eval_finsetSum]
    calc
      _ = ∑ k ∈ range (n + 1), a * (c k : K) ^ 3 := by
        apply sum_congr rfl
        intro k hk
        exact scaledGegenCoeff_half_value n h2 hn hden k (by simpa using hk)
      _ = a * ∑ k ∈ range (n + 1), (c k : K) ^ 3 := (mul_sum ..).symm
      _ = 0 := by rw [hz, mul_zero]
  have hroot : Q.eval (1 / 2) = 0 := by
    simpa only [eval_pow, sq_eq_zero_iff] using hv
  have hd : (derivative (Q ^ 2)).eval (1 / 2) = 0 := by
    rw [pow_two, derivative_mul]
    simp only [eval_add, eval_mul, hroot, zero_mul, mul_zero, zero_add]
  rw [hsquare, derivative_sum, eval_finsetSum] at hd
  have he : (∑ k ∈ range (n + 1),
      (derivative (scaledGegenCoeff (X : Polynomial K) n k)).eval (1 / 2)) =
      b * (∑ k ∈ range (n + 1), (c k : K) ^ 3) +
      (6 * a) * (∑ k ∈ range (n + 1), (c k : K) ^ 3 *
        (harmonic (2 * k) - harmonic k)) := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro k hk
    have h := scaledGegenCoeff_half_derivative n h2 hn hden hodd k (by simpa using hk)
    dsimp [a, b]
    convert h using 1 <;> ring
  rw [he, hz, mul_zero, zero_add] at hd
  exact (mul_eq_zero.mp hd).resolve_left (mul_ne_zero h6 ha)

end HalfParameter

/-- The scalar square recurrence, after canceling the common formal factor `2X`
algebraically. No cancellation hypothesis on the coefficient ring is needed. -/
theorem gegen_square_recurrence (l : R) (n : ℕ) :
    ((n : Polynomial R) + 1 + C l) * gegen l (n + 3) ^ 2 =
      ((n : Polynomial R) + 2 + C l) *
        (4 * ((n : Polynomial R) + 2 + C l) * ((n : Polynomial R) + 1 + C l) * X ^ 2 -
          ((n : Polynomial R) + 2) * ((n : Polynomial R) + 1 + 2 * C l)) *
        gegen l (n + 2) ^ 2 -
      ((n : Polynomial R) + 1 + C l) * ((n : Polynomial R) + 2) *
        ((n : Polynomial R) + 1 + 2 * C l) *
        (4 * ((n : Polynomial R) + 2 + C l) * ((n : Polynomial R) + 1 + C l) * X ^ 2 -
          ((n : Polynomial R) + 2) * ((n : Polynomial R) + 1 + 2 * C l)) *
        gegen l (n + 1) ^ 2 +
      ((n : Polynomial R) + 2 + C l) * ((n : Polynomial R) + 2) *
        ((n : Polynomial R) + 1 + 2 * C l) * ((n : Polynomial R) + 1) ^ 2 *
        ((n : Polynomial R) + 2 * C l) ^ 2 * gegen l n ^ 2 := by
  rw [show n + 3 = (n + 1) + 2 by omega, gegen_step l (n + 1), gegen_step l n]
  push_cast
  ring

theorem coeff_quadratic_binomial (b : R) (n j : ℕ) :
    ((X ^ 2 + C b : Polynomial R) ^ n).coeff j =
      if 2 ∣ j then b ^ (n - j / 2) * (n.choose (j / 2) : R) else 0 := by
  have he : (X ^ 2 + C b : Polynomial R) ^ n = expand R 2 ((X + C b) ^ n) := by
    simp only [map_pow, map_add, expand_X, expand_C]
  rw [he, coeff_expand (by norm_num), coeff_X_add_C_pow]

theorem coeff_add_linear_power (F : Polynomial R) (a : R) (n : ℕ) :
    ((F + C a * X) ^ n).coeff n =
      ∑ j ∈ range (n + 1), (n.choose j : R) * a ^ (n - j) * (F ^ j).coeff j := by
  rw [add_pow, finsetSum_coeff]
  apply sum_congr rfl
  intro j hj
  have hjn : j ≤ n := by simpa using hj
  have he : F ^ j * (C a * X) ^ (n - j) * (n.choose j : Polynomial R) =
      C ((n.choose j : R) * a ^ (n - j)) * (F ^ j * X ^ (n - j)) := by
    simp only [mul_pow, map_mul, map_pow, map_natCast]
    ring
  rw [he, coeff_C_mul]
  congr 1
  conv_lhs => arg 2; rw [show n = j + (n - j) by omega]
  exact coeff_mul_X_pow (F ^ j) (n - j) j

theorem coeff_binomial_times (G : Polynomial R) (a : R) (n : ℕ) :
    (((X + C a) ^ n) * G).coeff (2 * n) =
      ∑ j ∈ range (n + 1), (n.choose j : R) * a ^ (n - j) * G.coeff (2 * n - j) := by
  rw [add_pow, sum_mul, finsetSum_coeff]
  apply sum_congr rfl
  intro j hj
  have hjn : j ≤ n := by simpa using hj
  have he : (X ^ j * C a ^ (n - j) * (n.choose j : Polynomial R)) * G =
      C ((n.choose j : R) * a ^ (n - j)) * (X ^ j * G) := by
    simp only [map_mul, map_pow, map_natCast]
    ring
  rw [he, coeff_C_mul]
  congr 1
  conv_lhs => arg 2; rw [show 2 * n = (2 * n - j) + j by omega]
  exact coeff_X_pow_mul G j (2 * n - j)

theorem quadratic_coefficient_reflection {K : Type*} [Field K]
    (n : ℕ) (h2 : (2 : K) ≠ 0) (hn : (n : K) = -(1 / 2))
    (hden : ∀ j : ℕ, 0 < j → j ≤ n → (j : K) ≠ 0)
    (b : K) (j : ℕ) (hj : j ≤ n) :
    ((X ^ 2 + C b : Polynomial K) ^ j).coeff j =
      ((X ^ 2 + C (-4 * b) : Polynomial K) ^ n).coeff (2 * n - j) := by
  rw [coeff_quadratic_binomial, coeff_quadratic_binomial]
  by_cases hd : 2 ∣ j
  · obtain ⟨r, rfl⟩ := hd
    have hr : r ≤ n := by omega
    have hmod : 2 ∣ 2 * n - 2 * r := ⟨n - r, by omega⟩
    rw [if_pos (dvd_mul_right 2 r), if_pos hmod]
    rw [show 2 * r / 2 = r by omega,
      show (2 * n - 2 * r) / 2 = n - r by omega,
      show 2 * r - r = r by omega, show n - (n - r) = r by omega,
      Nat.choose_symm hr]
    have hc := half_choose_identity n h2 hn hden r hr
    change b ^ r * (c r : K) = (-4 * b) ^ r * (n.choose r : K)
    rw [← hc, mul_pow]
    ring
  · have hmod : ¬ 2 ∣ 2 * n - j := by omega
    rw [if_neg hd, if_neg hmod]

/-- The coefficient identity underlying the degree-two isogeny transformation. -/
theorem quadratic_hasse_transform {K : Type*} [Field K]
    (n : ℕ) (h2 : (2 : K) ≠ 0) (hn : (n : K) = -(1 / 2))
    (hden : ∀ j : ℕ, 0 < j → j ≤ n → (j : K) ≠ 0) (a b : K) :
    ((X ^ 2 + C a * X + C b : Polynomial K) ^ n).coeff n =
      (((X + C a) * (X ^ 2 + C (-4 * b))) ^ n).coeff (2 * n) := by
  rw [show (X ^ 2 + C a * X + C b : Polynomial K) =
    (X ^ 2 + C b) + C a * X by ring, mul_pow,
    coeff_add_linear_power, coeff_binomial_times]
  apply sum_congr rfl
  intro j hj
  rw [quadratic_coefficient_reflection n h2 hn hden b j (by simpa using hj)]

/-- The binomial divisibility used to make the Hasse coefficient translation-invariant. -/
theorem choose_pred_prime_dvd {p m : ℕ} (hp : p.Prime)
    (hpm : p ≤ m) (hmp : m < 2 * p - 1) : p ∣ m.choose (p - 1) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hp2 := hp.two_le
  have hm : m % p = m - p := by
    rw [Nat.mod_eq_sub_mod hpm, Nat.mod_eq_of_lt (by omega)]
  have hb : (p - 1) % p = p - 1 := Nat.mod_eq_of_lt (by omega)
  have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat
    (n := m) (k := p - 1) (p := p)
  rw [hm, hb, Nat.choose_eq_zero_of_lt (by omega : m - p < p - 1), zero_mul] at h
  exact Nat.dvd_of_mod_eq_zero h

theorem hasseDeriv_pred_prime_constant {p : ℕ} (hp : p.Prime) [CharP R p]
    (F : Polynomial R) (hdeg : F.natDegree < 2 * p - 1) :
    hasseDeriv (p - 1) F = C (F.coeff (p - 1)) := by
  ext j
  rw [hasseDeriv_coeff]
  cases j with
  | zero => simp
  | succ j =>
    rw [coeff_C, if_neg (by omega)]
    by_cases hd : F.natDegree < j + 1 + (p - 1)
    · rw [coeff_eq_zero_of_natDegree_lt hd, mul_zero]
    · have hv : ((j + 1 + (p - 1)).choose (p - 1) : R) = 0 :=
        (CharP.cast_eq_zero_iff R p _).mpr
          (choose_pred_prime_dvd hp (by have := hp.two_le; omega) (by omega))
      rw [hv, zero_mul]

theorem hasse_coefficient_translate {p : ℕ} (hp : p.Prime) [CharP R p]
    (F : Polynomial R) (hdeg : F.natDegree < 2 * p - 1) (r : R) :
    (F.comp (X + C r)).coeff (p - 1) = F.coeff (p - 1) := by
  rw [← taylor_apply, taylor_coeff, hasseDeriv_pred_prime_constant hp F hdeg, eval_C]

noncomputable def cubic (a b c : R) : Polynomial R :=
  X ^ 3 + C a * X ^ 2 + C b * X + C c

noncomputable def cubicHasse (n : ℕ) (a b c : R) : R :=
  (cubic a b c ^ n).coeff (2 * n)

theorem cubic_natDegree (a b c : R) : (cubic a b c).natDegree ≤ 3 := by
  unfold cubic
  compute_degree!

theorem cubic_shift (a b c r : R) :
    (cubic a b c).comp (X + C r) =
      cubic (a + 3 * r) (b + 2 * a * r + 3 * r ^ 2)
        (c + b * r + a * r ^ 2 + r ^ 3) := by
  simp only [cubic, add_comp, mul_comp, pow_comp, C_comp, X_comp,
    map_add, map_mul, map_pow, map_ofNat]
  ring

theorem cubicHasse_shift {p : ℕ} (hp : p.Prime) [CharP R p]
    (n : ℕ) (hn : 2 * n + 1 = p) (a b c r : R) :
    cubicHasse n (a + 3 * r) (b + 2 * a * r + 3 * r ^ 2)
      (c + b * r + a * r ^ 2 + r ^ 3) = cubicHasse n a b c := by
  have hdeg : (cubic a b c ^ n).natDegree < 2 * p - 1 :=
    lt_of_le_of_lt (natDegree_pow_le_of_le n (cubic_natDegree a b c)) (by omega)
  have h := hasse_coefficient_translate hp (cubic a b c ^ n) hdeg r
  rw [pow_comp, cubic_shift] at h
  simpa only [show p - 1 = 2 * n by omega, cubicHasse] using h

theorem cubicHasse_root (n : ℕ) (a b : R) :
    cubicHasse n a b 0 = ((X ^ 2 + C a * X + C b : Polynomial R) ^ n).coeff n := by
  have he : cubic a b 0 = X * (X ^ 2 + C a * X + C b) := by
    simp only [cubic, map_zero]
    ring
  rw [cubicHasse, he, mul_pow, show 2 * n = n + n by omega, coeff_X_pow_mul]

/-- Equality of Hasse coefficients under the elementary degree-two transformation. -/
theorem cubicHasse_two_isogeny {K : Type*} [Field K] {p : ℕ} (hp : p.Prime) [CharP K p]
    (n : ℕ) (hn : 2 * n + 1 = p) (h2 : (2 : K) ≠ 0)
    (hnK : (n : K) = -(1 / 2))
    (hden : ∀ j : ℕ, 0 < j → j ≤ n → (j : K) ≠ 0) (a b : K) :
    cubicHasse n (-2 * a) (a ^ 2 - 4 * b) 0 = cubicHasse n a b 0 := by
  let G : Polynomial K := (X + C a) * (X ^ 2 + C (-4 * b))
  have hdeg : (G ^ n).natDegree < 2 * p - 1 := by
    have hg : G.natDegree ≤ 3 := by dsimp [G]; compute_degree!
    exact lt_of_le_of_lt (natDegree_pow_le_of_le n hg) (by omega)
  have h := hasse_coefficient_translate hp (G ^ n) hdeg (-a)
  have hg : G.comp (X + C (-a)) = cubic (-2 * a) (a ^ 2 - 4 * b) 0 := by
    simp only [G, cubic, add_comp, mul_comp, pow_comp, C_comp, X_comp,
      map_neg, map_mul, map_sub, map_pow, map_ofNat, map_zero, neg_comp, ofNat_comp]
    ring
  rw [pow_comp, hg, show p - 1 = 2 * n by omega] at h
  exact h.trans ((quadratic_hasse_transform n h2 hnK hden a b).symm.trans
    (cubicHasse_root n a b).symm)

theorem coeff_comp_scale (F : Polynomial R) (t : R) (k : ℕ) :
    (F.comp (C t * X)).coeff k = t ^ k * F.coeff k := by
  induction F using Polynomial.induction_on' with
  | add F G ihF ihG => simp only [add_comp, coeff_add, ihF, ihG]; ring
  | monomial j a =>
    simp only [monomial_comp, mul_pow, ← map_pow, ← map_mul, coeff_C_mul,
      coeff_X_pow, coeff_monomial]
    split_ifs <;> simp_all <;> ring

theorem cubicHasse_scale {K : Type*} [Field K] (n : ℕ) (a b c t : K) (ht : t ≠ 0) :
    cubicHasse n (a * t) (b * t ^ 2) (c * t ^ 3) = t ^ n * cubicHasse n a b c := by
  have he : (cubic (a * t) (b * t ^ 2) (c * t ^ 3)).comp (C t * X) =
      C (t ^ 3) * cubic a b c := by
    simp only [cubic, add_comp, mul_comp, pow_comp, C_comp, X_comp,
      map_mul, map_pow]
    ring
  have h := congrArg (fun F : Polynomial K => (F ^ n).coeff (2 * n)) he
  rw [← pow_comp, coeff_comp_scale, mul_pow, ← map_pow, coeff_C_mul] at h
  change t ^ (2 * n) * cubicHasse n (a * t) (b * t ^ 2) (c * t ^ 3) =
    (t ^ 3) ^ n * cubicHasse n a b c at h
  apply mul_left_cancel₀ (pow_ne_zero (2 * n) ht)
  rw [h]
  rw [← mul_assoc, ← pow_add, ← pow_mul]
  congr 2
  omega

/-- The CM parameter of discriminant `-7` gives an eigenvalue for the Hasse coefficient.
The proof uses only polynomial translations, scaling, and the degree-two identity. -/
theorem cubicHasse_cm7_eigenvalue {K : Type*} [Field K] {p : ℕ}
    (hp : p.Prime) [CharP K p] (n : ℕ) (hn : 2 * n + 1 = p)
    (h2 : (2 : K) ≠ 0) (hnK : (n : K) = -(1 / 2))
    (hden : ∀ j : ℕ, 0 < j → j ≤ n → (j : K) ≠ 0)
    (z : K) (hz : z ^ 2 - z + 2 = 0) :
    z ^ (2 * n) * cubicHasse n 0 (-35) (-98) = cubicHasse n 0 (-35) (-98) := by
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at hz
    have : (2 : K) = 0 := by simpa using hz
    exact h2 this
  let r := z - 4
  have hr : r ^ 3 - 35 * r - 98 = 0 := by
    dsimp [r]
    linear_combination (z - 11) * hz
  have hz4 : z ^ 4 = 2 - 3 * z := by
    linear_combination (z ^ 2 + z - 1) * hz
  have hz6 : z ^ 6 = 2 + 5 * z := by
    linear_combination (z ^ 4 + z ^ 3 - z ^ 2 - 3 * z - 1) * hz
  have h1 := cubicHasse_shift hp n hn (0 : K) (-35) (-98) r
  have hc1 : (-98 : K) + -35 * r + 0 * r ^ 2 + r ^ 3 = 0 := by
    linear_combination hr
  rw [hc1] at h1
  simp only [zero_mul, mul_zero, zero_add, add_zero] at h1
  have h2i := cubicHasse_two_isogeny hp n hn h2 hnK hden (3 * r) (-35 + 3 * r ^ 2)
  have ha2 : -2 * (3 * r) = -6 * r := by ring
  have hb2 : (3 * r) ^ 2 - 4 * (-35 + 3 * r ^ 2) = 140 - 3 * r ^ 2 := by ring
  rw [ha2, hb2] at h2i
  have h3 := cubicHasse_shift hp n hn (-6 * r) (140 - 3 * r ^ 2) (0 : K) (2 * r)
  have ha3 : -6 * r + 3 * (2 * r) = 0 := by ring
  have hb3 : 140 - 3 * r ^ 2 + 2 * (-6 * r) * (2 * r) + 3 * (2 * r) ^ 2 =
      -35 * z ^ 4 := by
    rw [hz4]
    dsimp [r]
    linear_combination -15 * hz
  have hc3 : 0 + (140 - 3 * r ^ 2) * (2 * r) + (-6 * r) * (2 * r) ^ 2 + (2 * r) ^ 3 =
      -98 * z ^ 6 := by
    rw [hz6]
    dsimp [r] at *
    linear_combination -22 * hr
  rw [ha3, hb3, hc3] at h3
  have hs := cubicHasse_scale n (0 : K) (-35) (-98) (z ^ 2) (pow_ne_zero 2 hz0)
  simp only [zero_mul, ← pow_mul] at hs
  norm_num at hs
  simp only [neg_mul] at h3 h2i h1
  exact hs.symm.trans (h3.trans (h2i.trans h1))

theorem cubicHasse_cm7_zero {K : Type*} [Field K] {p : ℕ}
    (hp : p.Prime) [CharP K p] (n : ℕ) (hn : 2 * n + 1 = p)
    (h2 : (2 : K) ≠ 0) (hnK : (n : K) = -(1 / 2))
    (hden : ∀ j : ℕ, 0 < j → j ≤ n → (j : K) ≠ 0)
    (z : K) (hz : z ^ 2 - z + 2 = 0) (hFrob : z ^ p ≠ z) :
    cubicHasse n (0 : K) (-35) (-98) = 0 := by
  have he := cubicHasse_cm7_eigenvalue hp n hn h2 hnK hden z hz
  have hpow : z ^ (2 * n) ≠ 1 := by
    intro h
    apply hFrob
    rw [← hn, pow_succ, h, one_mul]
  have hzero : (z ^ (2 * n) - 1) * cubicHasse n 0 (-35) (-98) = 0 := by
    linear_combination he
  exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hpow)

theorem neg_seven_legendre {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hres : p % 7 = 3 ∨ p % 7 = 5 ∨ p % 7 = 6) : legendreSym p (-7) = -1 := by
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hodd : p % 2 = 1 := Nat.odd_iff.mp ((Fact.out : p.Prime).odd_of_ne_two hp2)
  have hrec : legendreSym p 7 = (-1 : ℤ) ^ (3 * (p / 2)) * legendreSym 7 p := by
    simpa using (legendreSym.quadratic_reciprocity' (p := 7) (q := p) (by decide) hp2)
  have hsmall : legendreSym 7 (p : ℤ) = -1 := by
    rw [legendreSym.mod]
    change legendreSym 7 ((p : ℤ) % 7) = -1
    have hm : (p : ℤ) % 7 = ((p % 7 : ℕ) : ℤ) := by omega
    rw [hm]
    rcases hres with h | h | h <;> rw [h] <;> norm_num
  have hs : ((-1 : ℤ) ^ (p / 2)) ^ 2 = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  rw [legendreSym.at_neg hp2, hrec, ZMod.χ₄_eq_neg_one_pow hodd,
    show 3 * (p / 2) = (p / 2) * 3 by omega, pow_mul]
  calc
    _ = (((-1 : ℤ) ^ (p / 2)) ^ 2) ^ 2 * legendreSym 7 p := by ring
    _ = -1 := by rw [hs, hsmall]; norm_num

theorem cm7_parameter_not_fixed {K : Type*} [Field K] {p n : ℕ}
    (hp : p.Prime) [CharP K p] (hn : 2 * n + 1 = p) (h2 : (2 : K) ≠ 0)
    (hpow : (-7 : K) ^ n = -1) (z : K) (hz : z ^ 2 - z + 2 = 0) : z ^ p ≠ z := by
  letI : Fact p.Prime := ⟨hp⟩
  intro hf
  let d := 2 * z - 1
  have hd2 : d ^ 2 = -7 := by
    dsimp [d]
    linear_combination 4 * hz
  have htwo : (2 : K) ^ p = 2 := by
    exact map_ofNat (frobenius K p) 2
  have hfixed : d ^ p = d := by
    dsimp [d]
    rw [sub_pow_char, mul_pow, htwo, hf, one_pow]
  have hnegative : d ^ p = -d := by
    rw [← hn, pow_succ, pow_mul, hd2, hpow]
    ring
  have hd0 : d = 0 := by
    have he : (2 : K) * d = 0 := by linear_combination hnegative - hfixed
    exact (mul_eq_zero.mp he).resolve_left h2
  have hn0 : n ≠ 0 := by
    intro h
    subst n
    have := hp.two_le
    omega
  rw [← hd2, hd0, zero_pow (by decide : 2 ≠ 0), zero_pow hn0] at hpow
  exact neg_ne_zero.mpr one_ne_zero hpow.symm

noncomputable def generatingCoeff (n : ℕ) (x : R) (k : ℕ) : R :=
  ((1 - 2 * C x * X + X ^ 2 : Polynomial R) ^ n).coeff k

theorem derivative_power_identity (F : Polynomial R) (n : ℕ) :
    F * derivative (F ^ n) = (n : Polynomial R) * derivative F * F ^ n := by
  cases n with
  | zero => simp
  | succ n =>
    rw [derivative_pow]
    simp only [Nat.succ_sub_one, Nat.cast_succ, C_eq_natCast, map_add, map_one, map_natCast]
    rw [pow_succ]
    ring

theorem generating_equation (n : ℕ) (x : R) :
    let F : Polynomial R := (1 - 2 * C x * X + X ^ 2) ^ n
    derivative F - C (2 * x) * theta F + X * theta F =
      C (-2 * (n : R) * x) * F + C (2 * (n : R)) * (X * F) := by
  have h := derivative_power_identity (1 - 2 * C x * X + X ^ 2) n
  have hq : derivative (1 - 2 * C x * X + X ^ 2 : Polynomial R) = -2 * C x + 2 * X := by
    simp only [derivative_add, derivative_sub, derivative_mul, derivative_pow,
      derivative_one, derivative_ofNat, derivative_C, derivative_X,
      zero_mul, mul_zero, add_zero, zero_add, mul_one, one_mul,
      pow_one, map_natCast]
    norm_num
  rw [hq] at h
  dsimp only
  unfold theta
  simp only [map_mul, map_neg, map_ofNat, map_natCast]
  linear_combination h

theorem generatingCoeff_zero (n : ℕ) (x : R) : generatingCoeff n x 0 = 1 := by
  simp [generatingCoeff, coeff_zero_eq_eval_zero]

theorem generatingCoeff_one (n : ℕ) (x : R) :
    generatingCoeff n x 1 = -2 * (n : R) * x := by
  have h := congrArg (fun F : Polynomial R => F.coeff 0) (generating_equation n x)
  simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_neg, coeff_natCast_mul,
    coeff_C_mul, coeff_mul_C, coeff_theta, coeff_X_mul_zero, coeff_mul_X_zero,
    coeff_derivative, Nat.cast_zero, zero_mul, mul_zero, add_zero, zero_add, sub_zero,
    Nat.cast_one, mul_one] at h
  change generatingCoeff n x 1 = -2 * (n : R) * x * generatingCoeff n x 0 at h
  rw [generatingCoeff_zero, mul_one] at h
  exact h

theorem generatingCoeff_recurrence (n k : ℕ) (x : R) :
    ((k : R) + 2) * generatingCoeff n x (k + 2) =
      2 * ((k : R) + 1 - n) * x * generatingCoeff n x (k + 1) +
      (2 * (n : R) - k) * generatingCoeff n x k := by
  have h := congrArg (fun F : Polynomial R => F.coeff (k + 1)) (generating_equation n x)
  simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_neg, coeff_natCast_mul,
    coeff_C_mul, coeff_mul_C, coeff_theta, coeff_X_mul, coeff_mul_X,
    coeff_derivative] at h
  push_cast at h
  unfold generatingCoeff
  linear_combination h

theorem gegen_negative_nat_eval (n k : ℕ) (x : R) :
    (gegen (-(n : R)) k).eval x = (k.factorial : R) * generatingCoeff n x k := by
  induction k using Nat.twoStepInduction with
  | zero => simp [gegen_zero, generatingCoeff_zero]
  | one => simp [gegen_one, generatingCoeff_one]
  | more k ih0 ih1 =>
    rw [gegen_step]
    simp only [eval_sub, eval_mul, eval_add, eval_natCast, eval_one, eval_ofNat,
      eval_C, eval_X, ih0, ih1]
    rw [show k + 2 = (k + 1) + 1 by omega]
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    have h := generatingCoeff_recurrence n k x
    linear_combination -((k : R) + 1) * (k.factorial : R) * h

theorem gegen_half_cubicHasse {K : Type*} [Field K] (n : ℕ)
    (hn : (n : K) = -(1 / 2)) (x : K) :
    (gegen (1 / 2 : K) n).eval x = (n.factorial : K) * cubicHasse n (-2 * x) 1 0 := by
  have hn' : (1 / 2 : K) = -(n : K) := by rw [hn, neg_neg]
  have he : (1 - 2 * C x * X + X ^ 2 : Polynomial K) =
      X ^ 2 + C (-2 * x) * X + C (1 : K) := by
    simp only [map_mul, map_neg, map_ofNat, map_one]
    ring
  rw [hn', gegen_negative_nat_eval, cubicHasse_root]
  simp only [generatingCoeff, he]

theorem cast_ne_zero_below {p j : ℕ} [CharP R p] (hj : 0 < j) (hjp : j < p) :
    (j : R) ≠ 0 := by
  intro h
  have hd : p ∣ j := (CharP.cast_eq_zero_iff R p j).mp h
  exact (not_le.mpr hjp) (Nat.le_of_dvd hj hd)

theorem cm7_hasse_vanishing {p : ℕ} [Fact p.Prime] {K : Type*} [Field K]
    [CharP K p] [IsAlgClosed K] (f : ZMod p →+* K) (h5 : 5 ≤ p)
    (hres : p % 7 = 3 ∨ p % 7 = 5 ∨ p % 7 = 6) :
    cubicHasse ((p - 1) / 2) (0 : K) (-35) (-98) = 0 := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by omega
  have h2 : (2 : K) ≠ 0 := cast_ne_zero_below (p := p) (j := 2) (by omega) (by omega)
  let n := (p - 1) / 2
  have hn : 2 * n + 1 = p := by
    obtain ⟨m, hm⟩ := hp.odd_of_ne_two hp2
    dsimp [n]
    omega
  have hn0 : 2 * (n : K) + 1 = 0 := by
    have h := congrArg (fun j : ℕ => (j : K)) hn
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, CharP.cast_eq_zero K p] at h
    exact h
  have hnK : (n : K) = -(1 / 2) := by
    apply mul_left_cancel₀ h2
    calc
      2 * (n : K) = -1 := eq_neg_of_add_eq_zero_left hn0
      _ = 2 * -(1 / 2 : K) := by rw [one_div, mul_neg, mul_inv_cancel₀ h2]
  have hden (j : ℕ) (hj : 0 < j) (hjn : j ≤ n) : (j : K) ≠ 0 :=
    cast_ne_zero_below (p := p) hj (by omega)
  have hpow : (-7 : K) ^ n = -1 := by
    have he := legendreSym.eq_pow p (-7)
    rw [neg_seven_legendre hp2 hres] at he
    have ht := congrArg f he.symm
    simpa only [map_pow, map_intCast, map_neg, map_ofNat, map_one, Int.cast_neg, Int.cast_ofNat, Int.cast_one,
      show p / 2 = n by omega] using ht
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (-7 : K) (by norm_num : 0 < 2)
  let z : K := (1 + s) / 2
  have hz : z ^ 2 - z + 2 = 0 := by
    dsimp [z]
    field_simp
    linear_combination hs
  exact cubicHasse_cm7_zero hp n hn h2 hnK hden z hz
    (cm7_parameter_not_fixed hp hn h2 hpow z hz)

theorem cubicHasse_legendre_vanishing {K : Type*} [Field K] {p : ℕ}
    (hp : p.Prime) [CharP K p] (n : ℕ) (hn : 2 * n + 1 = p)
    (h2 : (2 : K) ≠ 0) (h7 : (7 : K) ≠ 0) (hnK : (n : K) = -(1 / 2))
    (hden : ∀ j : ℕ, 0 < j → j ≤ n → (j : K) ≠ 0)
    (hE : cubicHasse n (0 : K) (-35) (-98) = 0) (s : K) (hs : s ^ 2 = -7) :
    cubicHasse n (-2 * (3 * s)) 1 0 = 0 := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h, zero_pow (by decide : 2 ≠ 0)] at hs
    exact (neg_ne_zero.mpr h7) hs.symm
  have h4 : (4 : K) ≠ 0 := by convert mul_ne_zero h2 h2 using 1 <;> norm_num
  let t := 4 * s / 7
  have ht : t ≠ 0 := div_ne_zero (mul_ne_zero h4 hs0) h7
  have hscale := cubicHasse_scale n (0 : K) (-35) (-98) t ht
  have htb : -35 * t ^ 2 = 80 := by
    dsimp [t]
    rw [div_pow, mul_pow, hs]
    field_simp
    ring
  have htc : -98 * t ^ 3 = 128 * s := by
    dsimp [t]
    rw [div_pow, mul_pow, pow_succ s 2, hs]
    field_simp
    ring
  rw [zero_mul, htb, htc, hE, mul_zero] at hscale
  have hshift := cubicHasse_shift hp n hn (12 * s) (-256) (0 : K) (-4 * s)
  have ha : 12 * s + 3 * (-4 * s) = 0 := by ring
  have hb : -256 + 2 * (12 * s) * (-4 * s) + 3 * (-4 * s) ^ 2 = 80 := by
    linear_combination -48 * hs
  have hc : 0 + -256 * (-4 * s) + 12 * s * (-4 * s) ^ 2 + (-4 * s) ^ 3 = 128 * s := by
    linear_combination 128 * s * hs
  rw [ha, hb, hc] at hshift
  have hi := cubicHasse_two_isogeny hp n hn h2 hnK hden (-2 * (3 * s)) 1
  have hia : -2 * (-2 * (3 * s)) = 12 * s := by ring
  have hib : (-2 * (3 * s)) ^ 2 - 4 * 1 = -256 := by linear_combination 36 * hs
  rw [hia, hib] at hi
  exact hi.symm.trans (hshift.symm.trans hscale)

theorem gegen_inert_root_zero {p : ℕ} [Fact p.Prime] {K : Type*} [Field K]
    [CharP K p] [IsAlgClosed K] (f : ZMod p →+* K) (h5 : 5 ≤ p)
    (hres : p % 7 = 3 ∨ p % 7 = 5 ∨ p % 7 = 6)
    (n : ℕ) (hn : 2 * n + 1 = p) (h2 : (2 : K) ≠ 0) (h7 : (7 : K) ≠ 0)
    (hnK : (n : K) = -(1 / 2))
    (hden : ∀ j : ℕ, 0 < j → j ≤ n → (j : K) ≠ 0)
    (s : K) (hs : s ^ 2 = -7) : (gegen (1 / 2 : K) n).eval (3 * s) = 0 := by
  have hE := cm7_hasse_vanishing f h5 hres
  have hn' : n = (p - 1) / 2 := by omega
  rw [← hn'] at hE
  rw [gegen_half_cubicHasse n hnK, cubicHasse_legendre_vanishing
    (Fact.out : p.Prime) n hn h2 h7 hnK hden hE s hs, mul_zero]

theorem map_gegen_eval {S : Type*} [CommRing S] (f : R →+* S) (l x : R) (n : ℕ) :
    f ((gegen l n).eval x) = (gegen (f l) n).eval (f x) := by
  rw [← eval₂_at_apply, ← eval_map, map_gegen]

theorem gegen_eval_neg (l x : R) (n : ℕ) :
    (gegen l n).eval (-x) = (-1) ^ n * (gegen l n).eval x := by
  have h := congrArg (fun F : Polynomial R => F.eval x) (gegen_comp_neg_X l n)
  simpa only [eval_comp, eval_neg, eval_X, eval_mul, eval_pow, eval_one] using h

/-- The same recurrence works modulo a prime square: the correction is a multiple of `(2n+1)²`. -/
theorem scaledGegenCoeff_nilpotent_recurrence (l : R) (n k : ℕ)
    (hl : 2 * l = 1) (hn : (2 * (n : R) + 1) ^ 2 = 0) :
    2 * ((k : R) + 1) ^ 3 * scaledGegenCoeff l n (k + 1) =
      16 * (2 * (k : R) + 1) ^ 3 * scaledGegenCoeff l n k := by
  have h := scaledGegenCoeff_recurrence l n k
  rw [hl] at h
  have hs : 128 * ((k : R) + l) = 64 * (2 * (k : R) + 1) := by
    linear_combination 64 * hl
  have hprod : 128 * ((k : R) - n) * (k + n + 1) * (k + l) * scaledGegenCoeff l n k =
      16 * (2 * (k : R) + 1) ^ 3 * scaledGegenCoeff l n k := by
    calc
      _ = (128 * ((k : R) + l)) * ((k : R) - n) * (k + n + 1) * scaledGegenCoeff l n k := by ring
      _ = 64 * (2 * (k : R) + 1) * ((k : R) - n) * (k + n + 1) * scaledGegenCoeff l n k := by rw [hs]
      _ = _ := by linear_combination -16 * (2 * (k : R) + 1) * scaledGegenCoeff l n k * hn
  rw [hprod] at h
  convert h using 1 <;> ring

theorem central_cube_recurrence_ring (k : ℕ) :
    ((k : R) + 1) ^ 3 * (c (k + 1) : R) ^ 3 =
      8 * (2 * (k : R) + 1) ^ 3 * (c k : R) ^ 3 := by
  have h := congrArg (fun n : ℕ => (n : R)) (Nat.succ_mul_centralBinom_succ k)
  change (((k + 1) * c (k + 1) : ℕ) : R) = ((2 * (2 * k + 1) * c k : ℕ) : R) at h
  push_cast at h
  have h3 := congrArg (fun x : R => x ^ 3) h
  convert h3 using 1 <;> ring

theorem scaledGegenCoeff_nilpotent_value (l : R) (n : ℕ)
    (hl : 2 * l = 1) (hn : (2 * (n : R) + 1) ^ 2 = 0)
    (h2 : IsUnit (2 : R))
    (hden : ∀ j : ℕ, 0 < j → j ≤ n → IsUnit (j : R)) (k : ℕ) (hk : k ≤ n) :
    scaledGegenCoeff l n k = scaledGegenCoeff l n 0 * (c k : R) ^ 3 := by
  induction k with
  | zero => simp [c]
  | succ k ih =>
    have hr : IsUnit ((k : R) + 1) := by simpa using hden (k + 1) (by omega) hk
    have hv := scaledGegenCoeff_nilpotent_recurrence l n k hl hn
    rw [ih (by omega)] at hv
    have hc := central_cube_recurrence_ring (R := R) k
    apply (h2.mul (hr.pow 3)).mul_left_cancel
    linear_combination hv - 2 * scaledGegenCoeff l n 0 * hc

theorem gegen_square_eval (l u : R) (hu : u ^ 2 = -63) (n : ℕ) :
    (gegen l n).eval u ^ 2 = ∑ k ∈ range (n + 1), scaledGegenCoeff l n k := by
  have h := congrArg (fun F : Polynomial R => F.eval u) (gegen_square l n)
  simp only [eval_pow, eval_comp, gegenSquareSeries, eval_finsetSum,
    eval_monomial, eval_sub, eval_one, eval_X, hu] at h
  norm_num at h
  simpa only [scaledGegenCoeff, mul_comm] using h

theorem rising_one_unit (n : ℕ)
    (hden : ∀ j : ℕ, 0 < j → j ≤ n → IsUnit (j : R)) : IsUnit (rising (1 : R) n) := by
  induction n with
  | zero => simp [rising_zero]
  | succ n ih =>
    rw [rising_succ]
    apply (ih (fun j hj hjn => hden j hj (by omega))).mul
    have h := hden (n + 1) (by omega) (by omega)
    simpa only [Nat.cast_add, Nat.cast_one, add_comm] using h

theorem scaledGegenCoeff_initial_unit (l : R) (n : ℕ) (hl : 2 * l = 1)
    (hden : ∀ j : ℕ, 0 < j → j ≤ n → IsUnit (j : R)) : IsUnit (scaledGegenCoeff l n 0) := by
  rw [scaledGegenCoeff_zero, hl]
  exact (rising_one_unit n hden).pow 2

/-- Evaluation of a quadratic algebra at a root, allowing a change of coefficient ring. -/
def quadraticEval {S : Type*} [CommRing S] (f : R →+* S) (d : R) (u : S) (hu : u ^ 2 = f d) :
    QuadraticAlgebra R d 0 →+* S where
  toFun q := f q.re + f q.im * u
  map_zero' := by simp
  map_one' := by simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_add' q r := by simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, map_add]; ring
  map_mul' q r := by
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, map_add, map_mul,
      map_zero, zero_mul, add_zero]
    linear_combination -f q.im * f r.im * hu

theorem quadraticEval_omega {S : Type*} [CommRing S]
    (f : R →+* S) (d : R) (u : S) (hu : u ^ 2 = f d) :
    quadraticEval f d u hu QuadraticAlgebra.omega = u := by
  simp [quadraticEval, QuadraticAlgebra.omega]

theorem quadraticEval_algebraMap {S : Type*} [CommRing S]
    (f : R →+* S) (d : R) (u : S) (hu : u ^ 2 = f d) (r : R) :
    quadraticEval f d u hu (algebraMap R (QuadraticAlgebra R d 0) r) = f r := by
  simp [quadraticEval]

theorem quadraticEval_zero_components {K : Type*} [Field K]
    (f : R →+* K) (d : R) (u : K) (hu : u ^ 2 = f d)
    (hu' : (-u) ^ 2 = f d) (q : QuadraticAlgebra R d 0)
    (h2 : (2 : K) ≠ 0) (hu0 : u ≠ 0)
    (hplus : quadraticEval f d u hu q = 0)
    (hminus : quadraticEval f d (-u) hu' q = 0) : f q.re = 0 ∧ f q.im = 0 := by
  change f q.re + f q.im * u = 0 at hplus
  change f q.re + f q.im * (-u) = 0 at hminus
  constructor
  · have h : (2 : K) * f q.re = 0 := by linear_combination hplus + hminus
    exact (mul_eq_zero.mp h).resolve_left h2
  · have h : (2 * u) * f q.im = 0 := by linear_combination hplus - hminus
    exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero h2 hu0)

end Gegenbauer

/-- A root of a polynomial square is also a root of its derivative. -/
theorem square_derivative_at_root {K : Type*} [Field K]
    (Q : Polynomial K) (x : K) (hQ : (Q ^ 2).eval x = 0) :
    (Polynomial.derivative (Q ^ 2)).eval x = 0 := by
  have hz : Q.eval x = 0 := by
    simpa only [Polynomial.eval_pow, sq_eq_zero_iff] using hQ
  simp [Polynomial.derivative_pow, hz]

/-- The parameter-derivative mechanism. The finite square identity and its coefficient
calculations are explicit hypotheses, rather than unproved declarations. -/
theorem harmonic_cancellation_from_square {K : Type*} [Field K]
    (p : ℕ) (Q : Polynomial K) (T : ℕ → Polynomial K) (x : K)
    (hsix : (6 : K) ≠ 0)
    (hsquare : Q ^ 2 = ∑ k ∈ range ((p - 1) / 2 + 1), T k)
    (hvalue : ∀ k < (p - 1) / 2 + 1, (T k).eval x = (c k : K) ^ 3)
    (hderiv : ∀ k < (p - 1) / 2 + 1,
      (Polynomial.derivative (T k)).eval x =
        6 * ((c k : K) ^ 3 * (harmonic (2 * k) - harmonic k)))
    (hzero : (∑ k ∈ range ((p - 1) / 2 + 1), (c k : K) ^ 3) = 0) :
    (∑ k ∈ range ((p - 1) / 2 + 1),
      (c k : K) ^ 3 * (harmonic (2 * k) - harmonic k)) = 0 := by
  have hv : (Q ^ 2).eval x = 0 := by
    rw [hsquare, Polynomial.eval_finsetSum]
    convert hzero using 1
    apply sum_congr rfl
    intro k hk
    exact hvalue k (mem_range.mp hk)
  have hd := square_derivative_at_root Q x hv
  rw [hsquare, Polynomial.derivative_sum, Polynomial.eval_finsetSum] at hd
  have hsum : (∑ k ∈ range ((p - 1) / 2 + 1),
      (Polynomial.derivative (T k)).eval x) =
      6 * ∑ k ∈ range ((p - 1) / 2 + 1),
        (c k : K) ^ 3 * (harmonic (2 * k) - harmonic k) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro k hk
    exact hderiv k (mem_range.mp hk)
  rw [hsum] at hd
  exact (mul_eq_zero.mp hd).resolve_left hsix

/-- The exact repository conclusion follows from the required half-block theorem. -/
theorem conjecture4_of_half_blocks
    (half_blocks : ∀ p, OeisA3625.A p → ∀ a,
      p ^ 2 ∣ ∑ b ∈ range ((p - 1) / 2 + 1), c (a * p + b) ^ 3)
    (S : Finset ℕ) (hS : ∀ p ∈ S, OeisA3625.A p) :
    (∏ p ∈ S, p) ^ 2 ∣ OeisA79727.a ((∏ p ∈ S, p - 1) / 2) := by
  apply product_square_dvd (fun p hp => (hS p hp).1)
  intro p hp
  exact odd_multiple_of_half_blocks (hS p hp).1 (eligible_product_odd S hS)
    (dvd_prod_of_mem (fun q => q) hp) (half_blocks p (hS p hp))

def primeSum (p : ℕ) : ZMod (p ^ 2) :=
  ∑ k ∈ range ((p - 1) / 2 + 1), (c k : ZMod (p ^ 2)) ^ 3

def harmonicSum (p : ℕ) : ZMod (p ^ 2) :=
  ∑ k ∈ range ((p - 1) / 2 + 1),
    (c k : ZMod (p ^ 2)) ^ 3 * (harmonic (2 * k) - harmonic k)

def reducePrime (p : ℕ) : ZMod (p ^ 2) →+* ZMod p :=
  ZMod.castHom (dvd_pow_self p (by norm_num : 2 ≠ 0)) (ZMod p)

def primeSumField (p : ℕ) : ZMod p :=
  ∑ k ∈ range ((p - 1) / 2 + 1), (c k : ZMod p) ^ 3

def harmonicSumField (p : ℕ) : ZMod p :=
  ∑ k ∈ range ((p - 1) / 2 + 1),
    (c k : ZMod p) ^ 3 * (harmonic (2 * k) - harmonic k)

theorem reducePrime_zero_annihilates {p : ℕ} (hp : p.Prime)
    (x : ZMod (p ^ 2)) (hx : reducePrime p x = 0) : (p : ZMod (p ^ 2)) * x = 0 := by
  let _ : NeZero (p ^ 2) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hval : p ∣ x.val := by
    apply (ZMod.natCast_eq_zero_iff x.val p).mp
    calc
      (x.val : ZMod p) = reducePrime p (x.val : ZMod (p ^ 2)) :=
        (map_natCast (reducePrime p) x.val).symm
      _ = reducePrime p x := by rw [ZMod.natCast_zmod_val]
      _ = 0 := hx
  obtain ⟨t, ht⟩ := hval
  rw [← ZMod.natCast_zmod_val x, ht]
  push_cast
  calc
    (p : ZMod (p ^ 2)) * (p * t) = (p : ZMod (p ^ 2)) ^ 2 * t := by ring
    _ = 0 := by rw [prime_square_zero, zero_mul]

theorem reducePrime_mul_zero {p : ℕ} (hp : p.Prime)
    (x y : ZMod (p ^ 2)) (hx : reducePrime p x = 0) (hy : reducePrime p y = 0) : x * y = 0 := by
  let _ : NeZero (p ^ 2) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hval : p ∣ x.val := by
    apply (ZMod.natCast_eq_zero_iff x.val p).mp
    calc
      (x.val : ZMod p) = reducePrime p (x.val : ZMod (p ^ 2)) :=
        (map_natCast (reducePrime p) x.val).symm
      _ = reducePrime p x := by rw [ZMod.natCast_zmod_val]
      _ = 0 := hx
  obtain ⟨t, ht⟩ := hval
  have hpy := reducePrime_zero_annihilates hp y hy
  rw [← ZMod.natCast_zmod_val x, ht]
  push_cast
  calc
    (p : ZMod (p ^ 2)) * t * y = t * (p * y) := by ring
    _ = 0 := by rw [hpy, mul_zero]

theorem quadratic_square_zero {p : ℕ} (hp : p.Prime) (d : ZMod (p ^ 2))
    (q : QuadraticAlgebra (ZMod (p ^ 2)) d 0)
    (hr : reducePrime p q.re = 0) (hi : reducePrime p q.im = 0) : q ^ 2 = 0 := by
  have hrr := reducePrime_mul_zero hp q.re q.re hr hr
  have hii := reducePrime_mul_zero hp q.im q.im hi hi
  have hri := reducePrime_mul_zero hp q.re q.im hr hi
  apply QuadraticAlgebra.ext
  · simp only [pow_two, QuadraticAlgebra.re_mul, QuadraticAlgebra.re_zero,
      mul_assoc, hrr, hii, mul_zero, add_zero]
  · simp only [pow_two, QuadraticAlgebra.im_mul, QuadraticAlgebra.im_zero,
      zero_mul, add_zero, hri, mul_comm q.im q.re, zero_add]

theorem reducePrime_inv_unit {p : ℕ} (hp : p.Prime)
    (x : ZMod (p ^ 2)) (hx : IsUnit x) :
    reducePrime p x⁻¹ = (reducePrime p x)⁻¹ := by
  let _ : Fact p.Prime := ⟨hp⟩
  have hne : reducePrime p x ≠ 0 := (hx.map (reducePrime p)).ne_zero
  apply mul_left_cancel₀ hne
  rw [← map_mul, ZMod.mul_inv_of_unit _ hx, map_one, mul_inv_cancel₀ hne]

theorem reducePrime_harmonic {p : ℕ} (hp : p.Prime) (n : ℕ) (hn : n < p) :
    reducePrime p (harmonic n) = (harmonic n : ZMod p) := by
  unfold harmonic
  rw [map_sum]
  apply sum_congr rfl
  intro j hj
  rw [reducePrime_inv_unit hp _ (small_nat_unit hp (by omega)
    (by have := mem_range.mp hj; omega)), map_natCast]

theorem reducePrime_primeSum (p : ℕ) :
    reducePrime p (primeSum p) = primeSumField p := by
  simp [primeSum, primeSumField]

theorem reducePrime_harmonicSum {p : ℕ} (hp : p.Prime) :
    reducePrime p (harmonicSum p) = harmonicSumField p := by
  unfold harmonicSum harmonicSumField
  rw [map_sum]
  apply sum_congr rfl
  intro k hk
  have hk' := mem_range.mp hk
  have hp2 := hp.two_le
  rw [map_mul, map_pow, map_natCast, map_sub,
    reducePrime_harmonic hp _ (by omega), reducePrime_harmonic hp _ (by omega)]

theorem harmonicSum_annihilates_of_field_zero {p : ℕ} (hp : p.Prime)
    (h : harmonicSumField p = 0) : (p : ZMod (p ^ 2)) * harmonicSum p = 0 := by
  apply reducePrime_zero_annihilates hp
  rwa [reducePrime_harmonicSum hp]

/-- Harmonic sums commute with homomorphisms of fields. -/
theorem map_harmonic {K L : Type*} [Field K] [Field L] (f : K →+* L) (n : ℕ) :
    f (harmonic n) = (harmonic n : L) := by
  simp only [harmonic, map_sum, map_inv₀, map_natCast]

/-- The harmonic obstruction vanishes whenever the original prime sum vanishes modulo `p`. -/
theorem harmonicSumField_eq_zero {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (hz : primeSumField p = 0) : harmonicSumField p = 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  let K := AlgebraicClosure (ZMod p)
  let f : ZMod p →+* K := algebraMap (ZMod p) K
  have hsmall (j : ℕ) (hj : 0 < j) (hjp : j < p) : (j : K) ≠ 0 := by
    intro h
    have hd : p ∣ j := (CharP.cast_eq_zero_iff K p j).mp h
    exact (not_le.mpr hjp) (Nat.le_of_dvd hj hd)
  have h2 : (2 : K) ≠ 0 := hsmall 2 (by omega) (by omega)
  have h3 : (3 : K) ≠ 0 := hsmall 3 (by omega) (by omega)
  have h6 : (6 : K) ≠ 0 := by
    convert mul_ne_zero h2 h3 using 1 <;> norm_num
  let n := (p - 1) / 2
  have hnat : 2 * n + 1 = p := by
    have ho := hp.odd_of_ne_two (by omega)
    obtain ⟨m, hm⟩ := ho
    dsimp [n]
    omega
  have hn0 : 2 * (n : K) + 1 = 0 := by
    calc
      _ = ((2 * n + 1 : ℕ) : K) := by
        rw [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
      _ = (p : K) := congrArg (fun j : ℕ => (j : K)) hnat
      _ = 0 := CharP.cast_eq_zero K p
  have hn : (n : K) = -(1 / 2) := by
    apply mul_left_cancel₀ h2
    calc
      2 * (n : K) = -1 := eq_neg_of_add_eq_zero_left hn0
      _ = 2 * -(1 / 2 : K) := by
        rw [one_div, mul_neg, mul_inv_cancel₀ h2]
  have hden (j : ℕ) (hj : 0 < j) (hjn : j ≤ n) : (j : K) ≠ 0 :=
    hsmall j hj (by omega)
  have hodd (j : ℕ) (hjn : j < n) : 2 * (j : K) + 1 ≠ 0 := by
    have h := hsmall (2 * j + 1) (by omega) (by omega)
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at h
    exact h
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (-63 : K) (by norm_num : 0 < 2)
  have hsum : (∑ k ∈ range (n + 1), (c k : K) ^ 3) = 0 := by
    have h := congrArg f hz
    simpa only [primeSumField, map_sum, map_pow, map_natCast, map_zero, n] using h
  have hh := harmonic_cancellation_gegenbauer n h2 h6 hn hden hodd u hu hsum
  apply f.injective
  simpa only [harmonicSumField, map_sum, map_mul, map_pow, map_sub, map_harmonic,
    map_natCast, map_zero, n] using hh

open Polynomial in
/-- Sun's prime-level vanishing, proved here by finite polynomial identities and a nilpotent lift. -/
theorem prime_case_large {p : ℕ} (hp : OeisA3625.A p) (h5 : 5 ≤ p) : primeSum p = 0 := by
  letI : Fact p.Prime := ⟨hp.1⟩
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  let R := ZMod (p ^ 2)
  let K := AlgebraicClosure (ZMod p)
  let Q := QuadraticAlgebra R (-63) 0
  let j : R →+* Q := algebraMap R Q
  let f0 : ZMod p →+* K := algebraMap (ZMod p) K
  let f : R →+* K := f0.comp (reducePrime p)
  let n := (p - 1) / 2
  let l : R := (2 : R)⁻¹
  let lq : Q := j l
  let q : Q := (gegen lq n).eval QuadraticAlgebra.omega
  have hn : 2 * n + 1 = p := by
    obtain ⟨m, hm⟩ := eligible_odd hp
    dsimp [n]
    omega
  have hp7 : p ≠ 7 := by
    intro h
    have hh := hp.2
    rw [h] at hh
    norm_num at hh
  have h2K : (2 : K) ≠ 0 := cast_ne_zero_below (p := p) (j := 2) (by omega) (by omega)
  have h3K : (3 : K) ≠ 0 := cast_ne_zero_below (p := p) (j := 3) (by omega) (by omega)
  have h7K : (7 : K) ≠ 0 := by
    intro h
    have h7p : (7 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 7 hp7
    apply h7p
    apply f0.injective
    simpa only [map_ofNat, map_zero] using h
  have hnK0 : 2 * (n : K) + 1 = 0 := by
    have h := congrArg (fun m : ℕ => (m : K)) hn
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, CharP.cast_eq_zero K p] at h
    exact h
  have hnK : (n : K) = -(1 / 2) := by
    apply mul_left_cancel₀ h2K
    calc
      2 * (n : K) = -1 := eq_neg_of_add_eq_zero_left hnK0
      _ = 2 * -(1 / 2 : K) := by rw [one_div, mul_neg, mul_inv_cancel₀ h2K]
  have hdenK (m : ℕ) (hm : 0 < m) (hmn : m ≤ n) : (m : K) ≠ 0 :=
    cast_ne_zero_below (p := p) hm (by omega)
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (-7 : K) (by norm_num : 0 < 2)
  let u := 3 * s
  have hu : u ^ 2 = -63 := by dsimp [u]; linear_combination 9 * hs
  have hs0 : s ≠ 0 := by
    intro h
    rw [h, zero_pow (by decide : 2 ≠ 0)] at hs
    exact (neg_ne_zero.mpr h7K) hs.symm
  have hu0 : u ≠ 0 := mul_ne_zero h3K hs0
  have hroot : (gegen (1 / 2 : K) n).eval u = 0 :=
    gegen_inert_root_zero f0 h5 hp.2 n hn h2K h7K hnK hdenK s hs
  have h2R : IsUnit (2 : R) := small_nat_unit hp.1 (n := 2) (by omega) (by omega)
  have hl : (2 : R) * l = 1 := ZMod.mul_inv_of_unit _ h2R
  have hfl : f l = (1 / 2 : K) := by
    dsimp [f, l]
    rw [reducePrime_inv_unit hp.1 _ h2R]
    simp only [map_inv₀, map_ofNat, one_div]
  have huF : u ^ 2 = f (-63) := by simpa only [map_neg, map_ofNat] using hu
  have huF' : (-u) ^ 2 = f (-63) := by simpa only [neg_sq] using huF
  have hplus : quadraticEval f (-63) u huF q = 0 := by
    dsimp only [q, lq]
    rw [map_gegen_eval, quadraticEval_algebraMap, quadraticEval_omega, hfl]
    exact hroot
  have hminus : quadraticEval f (-63) (-u) huF' q = 0 := by
    dsimp only [q, lq]
    rw [map_gegen_eval, quadraticEval_algebraMap, quadraticEval_omega, hfl,
      gegen_eval_neg, hroot, mul_zero]
  have hparts := quadraticEval_zero_components f (-63) u huF huF' q h2K hu0 hplus hminus
  have hr : reducePrime p q.re = 0 := by
    apply f0.injective
    change f q.re = f0 0
    rw [hparts.1, map_zero]
  have hi : reducePrime p q.im = 0 := by
    apply f0.injective
    change f q.im = f0 0
    rw [hparts.2, map_zero]
  have hq0 : q ^ 2 = 0 := quadratic_square_zero hp.1 (-63) q hr hi
  have h2Q : IsUnit (2 : Q) := by simpa only [map_ofNat] using h2R.map j
  have hlQ : (2 : Q) * lq = 1 := by
    have h := congrArg j hl
    simpa only [map_mul, map_ofNat, map_one] using h
  have hdenR (m : ℕ) (hm : 0 < m) (hmn : m ≤ n) : IsUnit (m : R) :=
    small_nat_unit hp.1 hm (by omega)
  have hdenQ (m : ℕ) (hm : 0 < m) (hmn : m ≤ n) : IsUnit (m : Q) := by
    simpa only [map_natCast] using (hdenR m hm hmn).map j
  have hnR : 2 * (n : R) + 1 = (p : R) := by
    have h := congrArg (fun m : ℕ => (m : R)) hn
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at h
    exact h
  have hnR0 : (2 * (n : R) + 1) ^ 2 = 0 := by rw [hnR]; exact prime_square_zero p
  have hnQ : (2 * (n : Q) + 1) ^ 2 = 0 := by
    have h := congrArg j hnR0
    simpa only [map_pow, map_add, map_mul, map_ofNat, map_natCast, map_one, map_zero] using h
  have homega : (QuadraticAlgebra.omega : Q) ^ 2 = -63 := by
    calc
      _ = (QuadraticAlgebra.omega : Q) * QuadraticAlgebra.omega := pow_two _
      _ = j (-63) + j 0 * QuadraticAlgebra.omega :=
        QuadraticAlgebra.omega_mul_omega_eq_algebraMap
      _ = -63 := by rw [map_neg, map_ofNat, map_zero, zero_mul, add_zero]
  have hsum : q ^ 2 = scaledGegenCoeff lq n 0 *
      ∑ k ∈ range (n + 1), (c k : Q) ^ 3 := by
    rw [show q ^ 2 = ∑ k ∈ range (n + 1), scaledGegenCoeff lq n k from
      gegen_square_eval lq QuadraticAlgebra.omega homega n, mul_sum]
    apply sum_congr rfl
    intro k hk
    exact scaledGegenCoeff_nilpotent_value lq n hlQ hnQ h2Q hdenQ k (by simpa using hk)
  have hsum0 : (∑ k ∈ range (n + 1), (c k : Q) ^ 3) = 0 := by
    apply (scaledGegenCoeff_initial_unit lq n hlQ hdenQ).mul_left_cancel
    rw [mul_zero, ← hsum, hq0]
  apply QuadraticAlgebra.algebraMap_injective (R := R) (a := (-63 : R)) (b := (0 : R))
  change j (primeSum p) = j 0
  have hcast (m : ℕ) : j (m : R) = (m : Q) := map_natCast j m
  simpa only [primeSum, map_sum, map_pow, hcast, map_zero, n] using hsum0

def PrimeCase : Prop := ∀ p, OeisA3625.A p → primeSum p = 0

/-- The prime-level supercongruence, including the small prime `3`. -/
theorem prime_case : PrimeCase := by
  intro p hp
  by_cases hp3 : p = 3
  · subst p
    norm_num [primeSum, c, sum_range_succ]
    decide
  · apply prime_case_large hp
    have hp2 := hp.1.two_le
    obtain ⟨m, hm⟩ := eligible_odd hp
    omega

/-- The harmonic cancellation in the ring modulo `p²`. It is proved below from `PrimeCase`. -/
def HarmonicVanishing : Prop :=
  ∀ p, OeisA3625.A p → 5 ≤ p → (p : ZMod (p ^ 2)) * harmonicSum p = 0

theorem harmonicVanishing_of_primeCase (prime_case : PrimeCase) : HarmonicVanishing := by
  intro p hp h5
  apply harmonicSum_annihilates_of_field_zero hp.1
  apply harmonicSumField_eq_zero hp.1 h5
  have h := congrArg (reducePrime p) (prime_case p hp)
  simpa only [reducePrime_primeSum, map_zero] using h

theorem half_blocks_of_arithmetic_inputs
    (prime_case : PrimeCase) (harm : HarmonicVanishing)
    (p : ℕ) (hp : OeisA3625.A p) (a : ℕ) :
    p ^ 2 ∣ ∑ b ∈ range ((p - 1) / 2 + 1), c (a * p + b) ^ 3 := by
  by_cases hp3 : p = 3
  · subst p
    exact half_blocks_three a
  have hp5 : 5 ≤ p := by
    have hp2 := hp.1.two_le
    obtain ⟨t, ht⟩ := eligible_odd hp
    omega
  apply (ZMod.natCast_eq_zero_iff _ (p ^ 2)).mp
  push_cast
  have hs : (∑ b ∈ range ((p - 1) / 2 + 1),
      (c (a * p + b) : ZMod (p ^ 2)) ^ 3) =
      (c (a * p) : ZMod (p ^ 2)) ^ 3 *
        (primeSum p + (6 * (a : ZMod (p ^ 2))) *
          ((p : ZMod (p ^ 2)) * harmonicSum p)) := by
    unfold primeSum harmonicSum
    simp only [mul_add, mul_sum]
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro b hb
    rw [shifted_cube_mod hp.1 a b (by simpa using mem_range.mp hb)]
    ring
  rw [hs, prime_case p hp, harm p hp hp5]
  ring

/-- The stronger theorem: the other prime factors of the odd multiple are unrestricted. -/
theorem all_odd_multiples {p n : ℕ} (hp : OeisA3625.A p)
    (hn : Odd n) (hpn : p ∣ n) :
    p ^ 2 ∣ OeisA79727.a ((n - 1) / 2) := by
  exact odd_multiple_of_half_blocks hp.1 hn hpn
    (half_blocks_of_arithmetic_inputs prime_case
      (harmonicVanishing_of_primeCase prime_case) p hp)

/-- Modular assembly from the prime and harmonic inputs, both proved in this file. -/
theorem conjecture4_of_arithmetic_inputs
    (prime_case : PrimeCase) (harm : HarmonicVanishing)
    (S : Finset ℕ) (hS : ∀ p ∈ S, OeisA3625.A p) :
    (∏ p ∈ S, p) ^ 2 ∣ OeisA79727.a ((∏ p ∈ S, p - 1) / 2) := by
  exact conjecture4_of_half_blocks
    (half_blocks_of_arithmetic_inputs prime_case harm) S hS

/-- Reduction to the prime-level theorem, discharged by `prime_case`. -/
theorem conjecture4_of_primeCase (prime_case : PrimeCase)
    (S : Finset ℕ) (hS : ∀ p ∈ S, OeisA3625.A p) :
    (∏ p ∈ S, p) ^ 2 ∣ OeisA79727.a ((∏ p ∈ S, p - 1) / 2) := by
  exact conjecture4_of_arithmetic_inputs prime_case
    (harmonicVanishing_of_primeCase prime_case) S hS

/-- The exact Google DeepMind Formal Conjectures statement, with no extra hypotheses. -/
theorem conjecture4 (S : Finset ℕ) (hS : ∀ p ∈ S, OeisA3625.A p) :
    (∏ p ∈ S, p) ^ 2 ∣ OeisA79727.a ((∏ p ∈ S, p - 1) / 2) := by
  exact conjecture4_of_primeCase prime_case S hS

end A79727Proof



set_option maxHeartbeats 1600000

namespace A79727Cubic

open Polynomial Finset A79727Proof

section Coefficients

variable (R : Type*) [CommRing R]

def wCoeff (k : ℕ) : R := (c k : R) ^ 3

noncomputable def bCoeff : ℕ → R
  | 0 => 0
  | k + 1 => Ring.inverse (((k : R) + 1) ^ 3) *
      (8 * (2 * (k : R) + 1) ^ 3 * bCoeff k +
        48 * (2 * (k : R) + 1) ^ 2 * wCoeff R k -
        3 * ((k : R) + 1) ^ 2 * wCoeff R (k + 1))

noncomputable def qCoeff : ℕ → R
  | 0 => 0
  | k + 1 => Ring.inverse (((k : R) + 1) ^ 3) *
      (8 * (2 * (k : R) + 1) ^ 3 * qCoeff k +
        48 * (2 * (k : R) + 1) ^ 2 * bCoeff R k +
        96 * (2 * (k : R) + 1) * wCoeff R k -
        3 * ((k : R) + 1) ^ 2 * bCoeff R (k + 1) -
        3 * ((k : R) + 1) * wCoeff R (k + 1))

variable {R}

theorem wCoeff_recurrence (k : ℕ) :
    ((k : R) + 1) ^ 3 * wCoeff R (k + 1) =
      8 * (2 * (k : R) + 1) ^ 3 * wCoeff R k := by
  exact central_cube_recurrence_ring k

theorem bCoeff_recurrence (k : ℕ) (hr : IsUnit ((k : R) + 1)) :
    ((k : R) + 1) ^ 3 * bCoeff R (k + 1) +
      3 * ((k : R) + 1) ^ 2 * wCoeff R (k + 1) =
      8 * (2 * (k : R) + 1) ^ 3 * bCoeff R k +
        48 * (2 * (k : R) + 1) ^ 2 * wCoeff R k := by
  rw [bCoeff, Ring.mul_inverse_cancel_left _ _ (hr.pow 3)]
  ring

theorem qCoeff_recurrence (k : ℕ) (hr : IsUnit ((k : R) + 1)) :
    ((k : R) + 1) ^ 3 * qCoeff R (k + 1) +
      3 * ((k : R) + 1) ^ 2 * bCoeff R (k + 1) +
      3 * ((k : R) + 1) * wCoeff R (k + 1) =
      8 * (2 * (k : R) + 1) ^ 3 * qCoeff R k +
        48 * (2 * (k : R) + 1) ^ 2 * bCoeff R k +
        96 * (2 * (k : R) + 1) * wCoeff R k := by
  rw [qCoeff, Ring.mul_inverse_cancel_left _ _ (hr.pow 3)]
  ring

theorem map_ringInverse {S : Type*} [CommRing S] (j : R →+* S)
    {x : R} (hx : IsUnit x) : j (Ring.inverse x) = Ring.inverse (j x) := by
  apply (hx.map j).mul_left_cancel
  rw [← map_mul, Ring.mul_inverse_cancel _ hx, map_one,
    Ring.mul_inverse_cancel _ (hx.map j)]

theorem map_wCoeff {S : Type*} [CommRing S] (j : R →+* S) (k : ℕ) :
    j (wCoeff R k) = wCoeff S k := by simp [wCoeff]

theorem map_bCoeff {S : Type*} [CommRing S] (j : R →+* S) (n : ℕ)
    (hu : ∀ k < n, IsUnit ((k : R) + 1)) : j (bCoeff R n) = bCoeff S n := by
  induction n with
  | zero => simp [bCoeff]
  | succ n ih =>
    rw [bCoeff, map_mul, map_ringInverse j ((hu n (by omega)).pow 3)]
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, map_natCast,
      map_one, map_wCoeff, ih (fun k hk => hu k (by omega))]
    rfl

theorem map_qCoeff {S : Type*} [CommRing S] (j : R →+* S) (n : ℕ)
    (hu : ∀ k < n, IsUnit ((k : R) + 1)) : j (qCoeff R n) = qCoeff S n := by
  induction n with
  | zero => simp [qCoeff]
  | succ n ih =>
    rw [qCoeff, map_mul, map_ringInverse j ((hu n (by omega)).pow 3)]
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, map_natCast,
      map_one, map_wCoeff, ih (fun k hk => hu k (by omega)),
      map_bCoeff j n (fun k hk => hu k (by omega)), map_bCoeff j (n + 1) hu]
    rfl

theorem cube_shift_algebra (e r s w b q w' b' q' : R) (he : e ^ 3 = 0)
    (h0 : r ^ 3 * w' = 8 * s ^ 3 * w)
    (h1 : r ^ 3 * b' + 3 * r ^ 2 * w' = 8 * s ^ 3 * b + 48 * s ^ 2 * w)
    (h2 : r ^ 3 * q' + 3 * r ^ 2 * b' + 3 * r * w' =
      8 * s ^ 3 * q + 48 * s ^ 2 * b + 96 * s * w) :
    (e + r) ^ 3 * (w' + e * b' + e ^ 2 * q') =
      8 * (2 * e + s) ^ 3 * (w + e * b + e ^ 2 * q) := by
  linear_combination h0 + e * h1 + e ^ 2 * h2 +
    (3 * r ^ 2 * q' + 3 * r * b' + w' - 48 * s ^ 2 * q - 96 * s * b - 64 * w +
      e * (3 * r * q' + b' - 96 * s * q - 64 * b) + e ^ 2 * (q' - 64 * q)) * he

theorem cube_shift (a p b : ℕ) (he : ((a * p : ℕ) : R) ^ 3 = 0)
    (hu : ∀ k < b, IsUnit ((k : R) + 1)) :
    (c (a * p + b) : R) ^ 3 = (c (a * p) : R) ^ 3 *
      (wCoeff R b + ((a * p : ℕ) : R) * bCoeff R b +
        ((a * p : ℕ) : R) ^ 2 * qCoeff R b) := by
  induction b with
  | zero => simp [wCoeff, bCoeff, qCoeff, c]
  | succ b ih =>
    let e : R := ((a * p : ℕ) : R)
    let r : R := (b : R) + 1
    let s : R := 2 * (b : R) + 1
    have hr : IsUnit r := hu b (by omega)
    have her : IsUnit (e + r) :=
      (show IsNilpotent e from ⟨3, he⟩).isUnit_add_right_of_commute hr (Commute.all _ _)
    have ht := central_cube_recurrence_ring (R := R) (a * p + b)
    have hrec : (e + r) ^ 3 * (c (a * p + (b + 1)) : R) ^ 3 =
        8 * (2 * e + s) ^ 3 * (c (a * p + b) : R) ^ 3 := by
      simpa only [e, r, s, Nat.cast_add, Nat.add_assoc, mul_add, add_assoc] using ht
    apply (her.pow 3).mul_left_cancel
    rw [hrec, ih (fun k hk => hu k (by omega))]
    have ha := cube_shift_algebra e r s (wCoeff R b) (bCoeff R b) (qCoeff R b)
      (wCoeff R (b + 1)) (bCoeff R (b + 1)) (qCoeff R (b + 1)) he
      (wCoeff_recurrence b) (bCoeff_recurrence b hr) (qCoeff_recurrence b hr)
    linear_combination -(c (a * p) : R) ^ 3 * ha

end Coefficients

end A79727Cubic


set_option maxHeartbeats 1600000

namespace A79727Cubic

open Polynomial Finset A79727Proof

def reduce31 (p : ℕ) : ZMod (p ^ 3) →+* ZMod p :=
  ZMod.castHom (dvd_pow_self p (by norm_num : 3 ≠ 0)) (ZMod p)

def reduce32 (p : ℕ) : ZMod (p ^ 3) →+* ZMod (p ^ 2) :=
  ZMod.castHom (pow_dvd_pow p (by norm_num : 2 ≤ 3)) (ZMod (p ^ 2))

theorem p_cube_zero (p : ℕ) : (p : ZMod (p ^ 3)) ^ 3 = 0 := by
  rw [← Nat.cast_pow, ZMod.natCast_self]

theorem small_unit3 {p : ℕ} (hp : p.Prime) {n : ℕ} (hn : 0 < n) (hnp : n < p) :
    IsUnit (n : ZMod (p ^ 3)) := by
  apply (ZMod.isUnit_natCast_iff_not_dvd_pow hp (by norm_num : 0 < 3)).mpr
  intro hd
  exact (not_le.mpr hnp) (Nat.le_of_dvd hn hd)

theorem reduction_zero_value_dvd {p : ℕ} (hp : p.Prime)
    (x : ZMod (p ^ 3)) (hx : reduce31 p x = 0) : p ∣ x.val := by
  let _ : NeZero (p ^ 3) := ⟨pow_ne_zero _ hp.ne_zero⟩
  apply (ZMod.natCast_eq_zero_iff x.val p).mp
  calc
    (x.val : ZMod p) = reduce31 p (x.val : ZMod (p ^ 3)) :=
      (map_natCast (reduce31 p) x.val).symm
    _ = reduce31 p x := by rw [ZMod.natCast_zmod_val]
    _ = 0 := hx

theorem reduction32_zero_value_dvd {p : ℕ} (hp : p.Prime)
    (x : ZMod (p ^ 3)) (hx : reduce32 p x = 0) : p ^ 2 ∣ x.val := by
  let _ : NeZero (p ^ 3) := ⟨pow_ne_zero _ hp.ne_zero⟩
  apply (ZMod.natCast_eq_zero_iff x.val (p ^ 2)).mp
  calc
    (x.val : ZMod (p ^ 2)) = reduce32 p (x.val : ZMod (p ^ 3)) :=
      (map_natCast (reduce32 p) x.val).symm
    _ = reduce32 p x := by rw [ZMod.natCast_zmod_val]
    _ = 0 := hx

theorem p_sq_annihilates {p : ℕ} (hp : p.Prime)
    (x : ZMod (p ^ 3)) (hx : reduce31 p x = 0) : (p : ZMod (p ^ 3)) ^ 2 * x = 0 := by
  let _ : NeZero (p ^ 3) := ⟨pow_ne_zero _ hp.ne_zero⟩
  obtain ⟨t, ht⟩ := reduction_zero_value_dvd hp x hx
  rw [← ZMod.natCast_zmod_val x, ht]
  push_cast
  calc
    (p : ZMod (p ^ 3)) ^ 2 * (p * t) = (p : ZMod (p ^ 3)) ^ 3 * t := by ring
    _ = 0 := by rw [p_cube_zero, zero_mul]

theorem reduced_product_zero {p : ℕ} (hp : p.Prime)
    (x y : ZMod (p ^ 3)) (hx : reduce32 p x = 0) (hy : reduce31 p y = 0) : x * y = 0 := by
  let _ : NeZero (p ^ 3) := ⟨pow_ne_zero _ hp.ne_zero⟩
  obtain ⟨t, ht⟩ := reduction32_zero_value_dvd hp x hx
  obtain ⟨s, hs⟩ := reduction_zero_value_dvd hp y hy
  rw [← ZMod.natCast_zmod_val x, ← ZMod.natCast_zmod_val y, ht, hs]
  push_cast
  calc
    (p : ZMod (p ^ 3)) ^ 2 * t * (p * s) = (p : ZMod (p ^ 3)) ^ 3 * (t * s) := by ring
    _ = 0 := by rw [p_cube_zero, zero_mul]

theorem p_reduced_product_zero {p : ℕ} (hp : p.Prime)
    (x y : ZMod (p ^ 3)) (hx : reduce31 p x = 0) (hy : reduce31 p y = 0) :
    (p : ZMod (p ^ 3)) * x * y = 0 := by
  let _ : NeZero (p ^ 3) := ⟨pow_ne_zero _ hp.ne_zero⟩
  obtain ⟨t, ht⟩ := reduction_zero_value_dvd hp x hx
  obtain ⟨s, hs⟩ := reduction_zero_value_dvd hp y hy
  rw [← ZMod.natCast_zmod_val x, ← ZMod.natCast_zmod_val y, ht, hs]
  push_cast
  calc
    (p : ZMod (p ^ 3)) * (p * t) * (p * s) = (p : ZMod (p ^ 3)) ^ 3 * (t * s) := by ring
    _ = 0 := by rw [p_cube_zero, zero_mul]

theorem p_sq_mul_eq {p : ℕ} (hp : p.Prime) (x y : ZMod (p ^ 3))
    (hxy : reduce31 p x = reduce31 p y) :
    (p : ZMod (p ^ 3)) ^ 2 * x = (p : ZMod (p ^ 3)) ^ 2 * y := by
  have hz := p_sq_annihilates hp (x - y) (by rw [map_sub, hxy, sub_self])
  linear_combination hz

theorem shifted_cube3 {p : ℕ} (hp : p.Prime) (a b : ℕ) (hb : b < p) :
    (c (a * p + b) : ZMod (p ^ 3)) ^ 3 = (c (a * p) : ZMod (p ^ 3)) ^ 3 *
      (wCoeff (ZMod (p ^ 3)) b + (a : ZMod (p ^ 3)) * (p : ZMod (p ^ 3)) * bCoeff (ZMod (p ^ 3)) b +
        (a : ZMod (p ^ 3)) ^ 2 * (p : ZMod (p ^ 3)) ^ 2 * qCoeff (ZMod (p ^ 3)) b) := by
  have he : ((a * p : ℕ) : ZMod (p ^ 3)) ^ 3 = 0 := by
    rw [Nat.cast_mul, mul_pow, p_cube_zero, mul_zero]
  have hh := cube_shift (R := ZMod (p ^ 3)) a p b he (by
    intro k hk
    have hu := small_unit3 hp (n := k + 1) (by omega) (by omega)
    simpa only [Nat.cast_add, Nat.cast_one] using hu)
  convert hh using 1 <;> push_cast <;> ring

theorem cube_zero_of_dvd {p k : ℕ} (hpk : p ∣ c k) :
    (c k : ZMod (p ^ 3)) ^ 3 = 0 := by
  obtain ⟨t, ht⟩ := hpk
  rw [ht, Nat.cast_mul, mul_pow, p_cube_zero, zero_mul]

end A79727Cubic


set_option maxHeartbeats 1600000

namespace A79727Cubic

open Polynomial Finset A79727Proof

section Invariants

variable {R : Type*} [CommRing R]

noncomputable def op0 (f : R[X]) : R[X] :=
  8 * (X * X * X) * (1 - X) * derivative (derivative (derivative f)) +
  (24 * (X * X) - 36 * (X * X * X)) * derivative (derivative f) +
  (8 * X - 26 * (X * X)) * derivative f - X * f

noncomputable def op1 (f : R[X]) : R[X] :=
  24 * (X * X) * (1 - X) * derivative (derivative f) +
  (24 * X - 48 * (X * X)) * derivative f - 6 * X * f

noncomputable def op2 (f : R[X]) : R[X] :=
  24 * X * (1 - X) * derivative f - 12 * X * f

noncomputable def bracket (f g : R[X]) : R[X] :=
  4 * (X * X) * (1 - X) *
    (f * derivative (derivative g) + derivative (derivative f) * g -
      derivative f * derivative g) +
  (4 * X - 6 * (X * X)) * (f * derivative g + derivative f * g) - X * f * g

noncomputable def invA (f : R[X]) : R[X] := bracket f f

noncomputable def invK (f g : R[X]) : R[X] :=
  2 * bracket f g + 8 * X * (1 - X) * f * derivative f - 4 * X * (f * f)

noncomputable def invJ (f g q : R[X]) : R[X] :=
  2 * bracket f q + 8 * (1 - X) * (f * f) +
  16 * X * (1 - X) * f * derivative g -
  8 * X * (1 - X) * derivative f * g - 4 * X * f * g

theorem invA_derivative (f : R[X]) :
    X * derivative (invA f) = f * op0 f := by
  simp only [invA, bracket, op0, derivative_add, derivative_sub, derivative_mul,
    derivative_pow, derivative_X, derivative_one, derivative_ofNat, mul_one,
    one_mul, zero_mul, mul_zero, zero_add, add_zero, sub_zero, pow_one, C_ofNat]
  ring

theorem invK_derivative (f g : R[X]) :
    X * derivative (invK f g) + 2 * invA f =
      f * (op0 g + op1 f) + g * op0 f := by
  simp only [invA, invK, bracket, op0, op1, derivative_add, derivative_sub,
    derivative_mul, derivative_pow, derivative_X, derivative_one, derivative_ofNat,
    mul_one, one_mul, zero_mul, mul_zero, zero_add, add_zero, sub_zero, pow_one, C_ofNat]
  ring

theorem invJ_derivative (f g q : R[X]) :
    X * derivative (invJ f g q) + invK f g =
      f * (op0 q + op1 g + op2 f) + q * op0 f := by
  simp only [invJ, invK, bracket, op0, op1, op2, derivative_add, derivative_sub,
    derivative_mul, derivative_pow, derivative_X, derivative_one, derivative_ofNat,
    mul_one, one_mul, zero_mul, mul_zero, zero_add, add_zero, sub_zero, pow_one, C_ofNat]
  ring

end Invariants

section FieldInvariants

variable {K : Type*} [Field K]

theorem vanishing_of_system (A B J : K[X]) (h2 : (2 : K) ≠ 0)
    (ha : theta A = 0) (hb : theta B + 2 * A = 0)
    (hj : theta J + B = 0) : A = 0 ∧ B = 0 ∧ derivative J = 0 := by
  have hz : A = 0 ∧ B = 0 := by
    constructor <;> apply Polynomial.ext <;> intro n
    all_goals
      have han := congrArg (fun P : K[X] => P.coeff n) ha
      have hbn := congrArg (fun P : K[X] => P.coeff n) hb
      have hjn := congrArg (fun P : K[X] => P.coeff n) hj
      simp only [coeff_theta, coeff_add, coeff_ofNat_mul, coeff_zero] at han hbn hjn
      rw [coeff_zero]
      by_cases hn : (n : K) = 0
      · simp only [hn, zero_mul, zero_add] at han hbn hjn
        first | exact (mul_eq_zero.mp hbn).resolve_left h2 | exact hjn
      · have haz := (mul_eq_zero.mp han).resolve_left hn
        rw [haz, mul_zero, add_zero] at hbn
        first | exact haz | exact (mul_eq_zero.mp hbn).resolve_left hn
  refine ⟨hz.1, hz.2, ?_⟩
  have hh : theta J = 0 := by simpa only [hz.2, add_zero] using hj
  exact (mul_eq_zero.mp hh).resolve_left X_ne_zero

theorem invariant_zero (f g q : K[X]) (h2 : (2 : K) ≠ 0)
    (hf : op0 f = 0) (hg : op0 g + op1 f = 0)
    (hq : op0 q + op1 g + op2 f = 0) :
    invA f = 0 ∧ invK f g = 0 ∧ derivative (invJ f g q) = 0 := by
  apply vanishing_of_system (invA f) (invK f g) (invJ f g q) h2
  · have hh := invA_derivative f
    simpa only [theta, hf, mul_zero] using hh
  · have hh := invK_derivative f g
    simpa only [theta, hf, hg, mul_zero, zero_add] using hh
  · have hh := invJ_derivative f g q
    simpa only [theta, hf, hq, mul_zero, zero_add] using hh

end FieldInvariants

section SmallDerivative

variable {K : Type*} [Field K] {p : ℕ} [CharP K p]

theorem derivative_zero_degree_le (hp : 0 < p) (f : K[X])
    (hd : f.natDegree ≤ p) (hf : derivative f = 0) :
    f = C (f.coeff 0) + C (f.coeff p) * X ^ p := by
  ext n
  by_cases hn0 : n = 0
  · subst n
    simp only [coeff_add, coeff_C, coeff_C_mul, coeff_X_pow,
      if_pos rfl, if_neg (Nat.ne_of_gt hp), if_neg (Ne.symm (Nat.ne_of_gt hp)),
      ite_true, mul_zero, add_zero]
  by_cases hnp : n = p
  · subst n
    simp only [coeff_add, coeff_C, coeff_C_mul, coeff_X_pow,
      if_pos rfl, if_neg (Nat.ne_of_gt hp), if_neg (Ne.symm (Nat.ne_of_gt hp)),
      ite_true, mul_one, zero_add]
  have hzero : f.coeff n = 0 := by
    by_cases hnlt : n < p
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
      have hh := congrArg (fun P : K[X] => P.coeff m) hf
      rw [coeff_derivative, coeff_zero] at hh
      exact (mul_eq_zero.mp hh).resolve_right
        (by simpa only [Nat.cast_succ] using
          (cast_ne_zero_below (R := K) (Nat.succ_pos m) hnlt))
    · exact coeff_eq_zero_of_natDegree_lt (by omega)
  simp only [coeff_add, coeff_C, coeff_C_mul, coeff_X_pow, hzero,
    if_neg hn0, if_neg (Ne.symm hn0), if_neg hnp, if_neg (Ne.symm hnp),
    mul_zero, zero_add]

end SmallDerivative

end A79727Cubic


set_option maxHeartbeats 1600000

namespace A79727Cubic

open Polynomial Finset A79727Proof

section TopCoefficients

variable {R : Type*} [CommRing R]

noncomputable def quadCore (f q : R[X]) : R[X] :=
  f * theta (theta q) + theta (theta f) * q - theta f * theta q

noncomputable def bilinCore (f q : R[X]) : R[X] := f * theta q + theta f * q

noncomputable def crossCore (f g : R[X]) : R[X] :=
  16 * (f * theta g) - 8 * (theta f * g)

noncomputable def jLow (f g q : R[X]) : R[X] :=
  8 * quadCore f q + 8 * (f * f) + crossCore f g

noncomputable def jHigh (f g q : R[X]) : R[X] :=
  jLow f g q + 4 * bilinCore f q + 2 * (f * q) + 4 * (f * g)

theorem invJ_theta (f g q : R[X]) :
    invJ f g q = jLow f g q - X * jHigh f g q := by
  simp only [invJ, bracket, jLow, jHigh, quadCore, bilinCore, crossCore, theta,
    derivative_mul, derivative_X, one_mul]
  ring

theorem theta_degree {n : ℕ} {f : R[X]} (hf : f.natDegree ≤ n) :
    (theta f).natDegree ≤ n := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [coeff_theta, coeff_eq_zero_of_natDegree_lt (hf.trans_lt hk), mul_zero]

theorem const_mul_degree (a : ℕ) {n : ℕ} {f : R[X]} (hf : f.natDegree ≤ n) :
    ((a : R[X]) * f).natDegree ≤ n := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [coeff_natCast_mul, coeff_eq_zero_of_natDegree_lt (hf.trans_lt hk), mul_zero]

theorem mul_degree {n : ℕ} {f g : R[X]} (hf : f.natDegree ≤ n)
    (hg : g.natDegree ≤ n) : (f * g).natDegree ≤ 2 * n := by
  have := natDegree_mul_le_of_le hf hg
  omega

theorem quad_degree {n : ℕ} {f q : R[X]} (hf : f.natDegree ≤ n)
    (hq : q.natDegree ≤ n) : (quadCore f q).natDegree ≤ 2 * n := by
  apply (natDegree_sub_le _ _).trans
  apply max_le
  · exact natDegree_add_le_of_degree_le (mul_degree hf (theta_degree (theta_degree hq)))
      (mul_degree (theta_degree (theta_degree hf)) hq)
  · exact mul_degree (theta_degree hf) (theta_degree hq)

theorem bilin_degree {n : ℕ} {f q : R[X]} (hf : f.natDegree ≤ n)
    (hq : q.natDegree ≤ n) : (bilinCore f q).natDegree ≤ 2 * n :=
  natDegree_add_le_of_degree_le (mul_degree hf (theta_degree hq))
    (mul_degree (theta_degree hf) hq)

theorem cross_degree {n : ℕ} {f g : R[X]} (hf : f.natDegree ≤ n)
    (hg : g.natDegree ≤ n) : (crossCore f g).natDegree ≤ 2 * n := by
  apply (natDegree_sub_le _ _).trans
  exact max_le (const_mul_degree 16 (mul_degree hf (theta_degree hg)))
    (const_mul_degree 8 (mul_degree (theta_degree hf) hg))

theorem jLow_degree {n : ℕ} {f g q : R[X]} (hf : f.natDegree ≤ n)
    (hg : g.natDegree ≤ n) (hq : q.natDegree ≤ n) :
    (jLow f g q).natDegree ≤ 2 * n :=
  natDegree_add_le_of_degree_le
    (natDegree_add_le_of_degree_le (const_mul_degree 8 (quad_degree hf hq))
      (const_mul_degree 8 (mul_degree hf hf))) (cross_degree hf hg)

theorem jHigh_degree {n : ℕ} {f g q : R[X]} (hf : f.natDegree ≤ n)
    (hg : g.natDegree ≤ n) (hq : q.natDegree ≤ n) :
    (jHigh f g q).natDegree ≤ 2 * n :=
  natDegree_add_le_of_degree_le
    (natDegree_add_le_of_degree_le
      (natDegree_add_le_of_degree_le (jLow_degree hf hg hq)
        (const_mul_degree 4 (bilin_degree hf hq)))
      (const_mul_degree 2 (mul_degree hf hq))) (const_mul_degree 4 (mul_degree hf hg))

theorem invJ_degree {n : ℕ} {f g q : R[X]} (hf : f.natDegree ≤ n)
    (hg : g.natDegree ≤ n) (hq : q.natDegree ≤ n) :
    (invJ f g q).natDegree ≤ 2 * n + 1 := by
  rw [invJ_theta]
  apply (natDegree_sub_le _ _).trans
  apply max_le
  · exact (jLow_degree hf hg hq).trans (by omega)
  · have := natDegree_mul_le_of_le natDegree_X_le (jHigh_degree hf hg hq)
    omega

theorem quad_top {n : ℕ} {f q : R[X]} (hf : f.natDegree ≤ n)
    (hq : q.natDegree ≤ n) :
    (quadCore f q).coeff (2 * n) = (n : R) ^ 2 * f.coeff n * q.coeff n := by
  rw [show 2 * n = n + n by omega]
  simp only [quadCore, coeff_sub, coeff_add,
    coeff_mul_add_eq_of_natDegree_le hf (theta_degree (theta_degree hq)),
    coeff_mul_add_eq_of_natDegree_le (theta_degree (theta_degree hf)) hq,
    coeff_mul_add_eq_of_natDegree_le (theta_degree hf) (theta_degree hq), coeff_theta]
  ring

theorem bilin_top {n : ℕ} {f q : R[X]} (hf : f.natDegree ≤ n)
    (hq : q.natDegree ≤ n) :
    (bilinCore f q).coeff (2 * n) = 2 * n * f.coeff n * q.coeff n := by
  rw [show 2 * n = n + n by omega]
  simp only [bilinCore, coeff_add,
    coeff_mul_add_eq_of_natDegree_le hf (theta_degree hq),
    coeff_mul_add_eq_of_natDegree_le (theta_degree hf) hq, coeff_theta]
  ring

theorem cross_top {n : ℕ} {f g : R[X]} (hf : f.natDegree ≤ n)
    (hg : g.natDegree ≤ n) :
    (crossCore f g).coeff (2 * n) = 8 * n * f.coeff n * g.coeff n := by
  rw [show 2 * n = n + n by omega]
  simp only [crossCore, coeff_sub, coeff_ofNat_mul,
    coeff_mul_add_eq_of_natDegree_le hf (theta_degree hg),
    coeff_mul_add_eq_of_natDegree_le (theta_degree hf) hg, coeff_theta]
  ring

theorem invJ_top {n : ℕ} {f g q : R[X]} (hf : f.natDegree ≤ n)
    (hg : g.natDegree ≤ n) (hq : q.natDegree ≤ n) :
    (invJ f g q).coeff (2 * n + 1) =
      -(2 * (2 * (n : R) + 1) ^ 2 * f.coeff n * q.coeff n +
        4 * (2 * (n : R) + 1) * f.coeff n * g.coeff n + 8 * f.coeff n ^ 2) := by
  rw [invJ_theta, coeff_sub, coeff_X_mul,
    coeff_eq_zero_of_natDegree_lt ((jLow_degree hf hg hq).trans_lt (by omega))]
  simp only [jHigh, jLow, coeff_add, coeff_ofNat_mul, quad_top hf hq,
    bilin_top hf hq, cross_top hf hg]
  rw [show 2 * n = n + n by omega,
    coeff_mul_add_eq_of_natDegree_le hf hf,
    coeff_mul_add_eq_of_natDegree_le hf hq,
    coeff_mul_add_eq_of_natDegree_le hf hg]
  ring

theorem invJ_zero (f g q : R[X]) : (invJ f g q).coeff 0 = 8 * f.coeff 0 ^ 2 := by
  simp [invJ_theta, jLow, quadCore, crossCore, coeff_theta, pow_two]

end TopCoefficients

end A79727Cubic


set_option maxHeartbeats 1600000

namespace A79727Cubic

open Polynomial Finset A79727Proof

variable {K : Type*} [Field K]

theorem full_invariants {p n : ℕ} [CharP K p] (hp : 0 < p)
    (hpn : p = 2 * n + 1) (h2 : (2 : K) ≠ 0)
    {f g q : K[X]} (hf : f.natDegree ≤ n) (hg : g.natDegree ≤ n)
    (hq : q.natDegree ≤ n) (hf0 : f.coeff 0 = 1) (hfn : f.coeff n ^ 2 = 1)
    (ef : op0 f = 0) (eg : op0 g + op1 f = 0)
    (eq : op0 q + op1 g + op2 f = 0) :
    invA f = 0 ∧ invK f g = 0 ∧ invJ f g q = 8 * (1 - X ^ p) := by
  obtain ⟨ha, hk, hj⟩ := invariant_zero f g q h2 ef eg eq
  have hn : 2 * (n : K) + 1 = 0 := by
    have hh : (p : K) = 0 := CharP.cast_eq_zero K p
    simpa only [hpn, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hh
  have hd : (invJ f g q).natDegree ≤ p := by
    rw [hpn]
    exact invJ_degree hf hg hq
  have hzero : (invJ f g q).coeff 0 = 8 := by rw [invJ_zero, hf0]; ring
  have htop : (invJ f g q).coeff p = -8 := by
    rw [hpn, invJ_top hf hg hq, hn, hfn]
    ring
  have hh := derivative_zero_degree_le hp (invJ f g q) hd hj
  rw [hzero, htop] at hh
  refine ⟨ha, hk, ?_⟩
  rw [hh]
  rw [map_neg]
  change (8 : K[X]) + (-8) * X ^ p = 8 * (1 - X ^ p)
  ring

theorem root_of_invariants {p : ℕ} {f g q : K[X]} (h2 : (2 : K) ≠ 0)
    (ha : invA f = 0) (hk : invK f g = 0)
    (hj : invJ f g q = 8 * (1 - X ^ p))
    {t : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1) (htp : t ^ p = t)
    (hft : f.eval t = 0) :
    (derivative f).eval t = 0 ∧ g.eval t = 0 ∧
      q.eval t * (theta (theta f)).eval t = 1 := by
  have h4 : (4 : K) ≠ 0 := by convert pow_ne_zero 2 h2 using 1 <;> norm_num
  have h8 : (8 : K) ≠ 0 := by convert pow_ne_zero 3 h2 using 1 <;> norm_num
  have h1t : 1 - t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht1)
  have hea := congrArg (fun P : K[X] => P.eval t) ha
  have hek := congrArg (fun P : K[X] => P.eval t) hk
  have hej := congrArg (fun P : K[X] => P.eval t) hj
  simp only [invA, bracket, eval_add, eval_sub, eval_mul, eval_ofNat,
    eval_one, eval_X, eval_zero, hft, zero_mul, mul_zero, zero_add, add_zero] at hea
  have hdf : (derivative f).eval t = 0 := by
    have hsq : 4 * t ^ 2 * (1 - t) * ((derivative f).eval t) ^ 2 = 0 := by
      linear_combination -hea
    have hh := (mul_eq_zero.mp hsq).resolve_left
      (mul_ne_zero (mul_ne_zero h4 (pow_ne_zero 2 ht0)) h1t)
    by_contra hz
    exact pow_ne_zero 2 hz hh
  simp only [invK, bracket, eval_add, eval_sub, eval_mul, eval_ofNat,
    eval_one, eval_X, eval_zero, hft, hdf, zero_mul, mul_zero, zero_add, add_zero,
    sub_zero] at hek
  simp only [invJ, bracket, eval_add, eval_sub, eval_mul, eval_ofNat,
    eval_one, eval_X, eval_zero, eval_pow, hft, hdf, htp, zero_mul, mul_zero,
    zero_add, add_zero, sub_zero] at hej
  have hjval : 8 * t ^ 2 * (1 - t) * (derivative (derivative f)).eval t * q.eval t =
      8 * (1 - t) := by linear_combination hej
  have hddf : (derivative (derivative f)).eval t ≠ 0 := by
    intro hz
    rw [hz, mul_zero, zero_mul] at hjval
    exact (mul_ne_zero h8 h1t) hjval.symm
  have hgt : g.eval t = 0 := by
    have hz : 8 * t ^ 2 * (1 - t) * (derivative (derivative f)).eval t * g.eval t = 0 := by
      linear_combination hek
    exact (mul_eq_zero.mp hz).resolve_left
      (mul_ne_zero (mul_ne_zero (mul_ne_zero h8 (pow_ne_zero 2 ht0)) h1t) hddf)
  refine ⟨hdf, hgt, ?_⟩
  apply mul_left_cancel₀ (mul_ne_zero h8 h1t)
  simp only [theta, derivative_mul, derivative_X, one_mul, eval_mul, eval_add, eval_X, hdf,
    zero_add]
  linear_combination hjval

end A79727Cubic


set_option maxHeartbeats 1600000

namespace A79727Cubic

open Polynomial Finset A79727Proof

section Series

variable {K : Type*} [Field K]

noncomputable def pack (n : ℕ) (a : ℕ → K) : K[X] :=
  ∑ k ∈ range (n + 1), monomial k (a k / (64 : K) ^ k)

theorem coeff_pack (n k : ℕ) (a : ℕ → K) :
    (pack n a).coeff k = if k ≤ n then a k / (64 : K) ^ k else 0 := by
  classical
  simp [pack, finsetSum_coeff, coeff_monomial, Nat.lt_succ_iff]

theorem pack_degree (n : ℕ) (a : ℕ → K) : (pack n a).natDegree ≤ n := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [coeff_pack, if_neg (by omega)]

theorem pack_eval (n : ℕ) (a : ℕ → K) (h64 : (64 : K) ≠ 0) :
    (pack n a).eval 64 = ∑ k ∈ range (n + 1), a k := by
  simp [pack, eval_finset_sum, eval_monomial, div_mul_cancel₀, pow_ne_zero _ h64]

theorem theta_pack (n : ℕ) (a : ℕ → K) :
    theta (pack n a) = pack n (fun k => (k : K) * a k) := by
  ext k
  simp only [coeff_theta, coeff_pack]
  split_ifs <;> ring

theorem op0_theta (f : K[X]) :
    op0 f = 8 * theta (theta (theta f)) -
      X * (8 * theta (theta (theta f)) + 12 * theta (theta f) + 6 * theta f + f) := by
  simp only [op0, theta, derivative_mul, derivative_add, derivative_X, one_mul]
  ring

theorem op1_theta (f : K[X]) :
    op1 f = 24 * theta (theta f) -
      X * (24 * theta (theta f) + 24 * theta f + 6 * f) := by
  simp only [op1, theta, derivative_mul, derivative_X, one_mul]
  ring

theorem op2_theta (f : K[X]) :
    op2 f = 24 * theta f - X * (24 * theta f + 12 * f) := by
  simp only [op2, theta]
  ring

theorem coeff_op0 (f : K[X]) (k : ℕ) :
    (op0 f).coeff (k + 1) = 8 * ((k : K) + 1) ^ 3 * f.coeff (k + 1) -
      (2 * (k : K) + 1) ^ 3 * f.coeff k := by
  rw [op0_theta]
  simp only [coeff_sub, coeff_add, coeff_ofNat_mul, coeff_X_mul, coeff_theta,
    Nat.cast_add, Nat.cast_one]
  ring

theorem coeff_op1 (f : K[X]) (k : ℕ) :
    (op1 f).coeff (k + 1) = 24 * ((k : K) + 1) ^ 2 * f.coeff (k + 1) -
      6 * (2 * (k : K) + 1) ^ 2 * f.coeff k := by
  rw [op1_theta]
  simp only [coeff_sub, coeff_add, coeff_ofNat_mul, coeff_X_mul, coeff_theta,
    Nat.cast_add, Nat.cast_one]
  ring

theorem coeff_op2 (f : K[X]) (k : ℕ) :
    (op2 f).coeff (k + 1) = 24 * ((k : K) + 1) * f.coeff (k + 1) -
      12 * (2 * (k : K) + 1) * f.coeff k := by
  rw [op2_theta]
  simp only [coeff_sub, coeff_add, coeff_ofNat_mul, coeff_X_mul, coeff_theta,
    Nat.cast_add, Nat.cast_one]
  ring

theorem coeff_ops_zero (f : K[X]) :
    (op0 f).coeff 0 = 0 ∧ (op1 f).coeff 0 = 0 ∧ (op2 f).coeff 0 = 0 := by
  simp [op0_theta, op1_theta, op2_theta, coeff_theta]

theorem pack_ode {n : ℕ} (h64 : (64 : K) ≠ 0)
    (hn : 2 * (n : K) + 1 = 0)
    (hu : ∀ k < n, IsUnit ((k : K) + 1)) :
    op0 (pack n (wCoeff K)) = 0 ∧
      op0 (pack n (bCoeff K)) + op1 (pack n (wCoeff K)) = 0 ∧
      op0 (pack n (qCoeff K)) + op1 (pack n (bCoeff K)) +
        op2 (pack n (wCoeff K)) = 0 := by
  have h0 (k : ℕ) (hk : k < n) :
      8 * ((k : K) + 1) ^ 3 * (wCoeff K (k + 1) / (64 : K) ^ (k + 1)) -
        (2 * (k : K) + 1) ^ 3 * (wCoeff K k / (64 : K) ^ k) = 0 := by
    rw [pow_succ]
    field_simp
    linear_combination 8 * (64 : K) ^ k * wCoeff_recurrence (R := K) k
  have h1 (k : ℕ) (hk : k < n) :
      (8 * ((k : K) + 1) ^ 3 * (bCoeff K (k + 1) / (64 : K) ^ (k + 1)) -
        (2 * (k : K) + 1) ^ 3 * (bCoeff K k / (64 : K) ^ k)) +
      (24 * ((k : K) + 1) ^ 2 * (wCoeff K (k + 1) / (64 : K) ^ (k + 1)) -
        6 * (2 * (k : K) + 1) ^ 2 * (wCoeff K k / (64 : K) ^ k)) = 0 := by
    rw [pow_succ]
    field_simp
    linear_combination 8 * (64 : K) ^ k * bCoeff_recurrence k (hu k hk)
  have h2 (k : ℕ) (hk : k < n) :
      (8 * ((k : K) + 1) ^ 3 * (qCoeff K (k + 1) / (64 : K) ^ (k + 1)) -
        (2 * (k : K) + 1) ^ 3 * (qCoeff K k / (64 : K) ^ k)) +
      (24 * ((k : K) + 1) ^ 2 * (bCoeff K (k + 1) / (64 : K) ^ (k + 1)) -
        6 * (2 * (k : K) + 1) ^ 2 * (bCoeff K k / (64 : K) ^ k)) +
      (24 * ((k : K) + 1) * (wCoeff K (k + 1) / (64 : K) ^ (k + 1)) -
        12 * (2 * (k : K) + 1) * (wCoeff K k / (64 : K) ^ k)) = 0 := by
    rw [pow_succ]
    field_simp
    linear_combination 8 * (64 : K) ^ k * qCoeff_recurrence k (hu k hk)
  constructor
  · ext k
    cases k with
    | zero => exact (coeff_ops_zero _).1
    | succ k =>
      rw [coeff_op0]
      simp only [coeff_pack, coeff_zero]
      rcases lt_trichotomy k n with hk | rfl | hk
      · simpa only [if_pos (by omega : k + 1 ≤ n), if_pos (by omega : k ≤ n)] using h0 k hk
      · simp [hn]
      · simp [show ¬k + 1 ≤ n by omega, show ¬k ≤ n by omega]
  constructor
  · ext k
    cases k with
    | zero => simp [(coeff_ops_zero _).1, (coeff_ops_zero _).2.1]
    | succ k =>
      simp only [coeff_add, coeff_op0, coeff_op1, coeff_pack, coeff_zero]
      rcases lt_trichotomy k n with hk | rfl | hk
      · simpa only [if_pos (by omega : k + 1 ≤ n), if_pos (by omega : k ≤ n)] using h1 k hk
      · simp [hn]
      · simp [show ¬k + 1 ≤ n by omega, show ¬k ≤ n by omega]
  · ext k
    cases k with
    | zero => simp [(coeff_ops_zero _).1, (coeff_ops_zero _).2.1, (coeff_ops_zero _).2.2]
    | succ k =>
      simp only [coeff_add, coeff_op0, coeff_op1, coeff_op2, coeff_pack, coeff_zero]
      rcases lt_trichotomy k n with hk | rfl | hk
      · simpa only [if_pos (by omega : k + 1 ≤ n), if_pos (by omega : k ≤ n)] using h2 k hk
      · simp [hn]
      · simp [show ¬k + 1 ≤ n by omega, show ¬k ≤ n by omega]

end Series

end A79727Cubic


set_option maxHeartbeats 1600000

namespace A79727Cubic
open Polynomial Finset A79727Proof

theorem field_moments {p : ℕ} (hp : OeisA3625.A p) (h5 : 5 ≤ p) :
    (∑ k ∈ range ((p - 1) / 2 + 1), (k : ZMod p) * wCoeff (ZMod p) k) = 0 ∧
    (∑ k ∈ range ((p - 1) / 2 + 1), bCoeff (ZMod p) k) = 0 ∧
    (∑ k ∈ range ((p - 1) / 2 + 1), qCoeff (ZMod p) k) *
      (∑ k ∈ range ((p - 1) / 2 + 1), (k : ZMod p) ^ 2 * wCoeff (ZMod p) k) = 1 := by
  letI : Fact p.Prime := ⟨hp.1⟩
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  let n := (p - 1) / 2
  let f := pack n (wCoeff (ZMod p))
  let g := pack n (bCoeff (ZMod p))
  let q := pack n (qCoeff (ZMod p))
  have hn : p = 2 * n + 1 := by
    obtain ⟨m, hm⟩ := eligible_odd hp
    dsimp [n]
    omega
  have h2 : (2 : ZMod p) ≠ 0 := cast_ne_zero_below (p := p) (j := 2) (by omega) (by omega)
  have h3 : (3 : ZMod p) ≠ 0 := cast_ne_zero_below (p := p) (j := 3) (by omega) (by omega)
  have hp7 : p ≠ 7 := by
    intro he
    have hh := hp.2
    rw [he] at hh
    norm_num at hh
  have h7 : (7 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 7 hp7
  have h64 : (64 : ZMod p) ≠ 0 := by
    convert pow_ne_zero 6 h2 using 1 <;> norm_num
  have ht1 : (64 : ZMod p) ≠ 1 := by
    have h63 : (63 : ZMod p) ≠ 0 := by
      convert mul_ne_zero (pow_ne_zero 2 h3) h7 using 1 <;> norm_num
    intro he
    apply h63
    linear_combination he
  have hn0 : 2 * (n : ZMod p) + 1 = 0 := by
    have hh : (p : ZMod p) = 0 := ZMod.natCast_self p
    simpa only [hn, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hh
  have hnK : (n : ZMod p) = -(1 / 2) := by
    apply mul_left_cancel₀ h2
    calc
      2 * (n : ZMod p) = -1 := eq_neg_of_add_eq_zero_left hn0
      _ = 2 * -(1 / 2 : ZMod p) := by rw [one_div, mul_neg, mul_inv_cancel₀ h2]
  have hden (k : ℕ) (hk : 0 < k) (hkn : k ≤ n) : (k : ZMod p) ≠ 0 :=
    cast_ne_zero_below hk (by omega)
  have hu (k : ℕ) (hk : k < n) : IsUnit ((k : ZMod p) + 1) := by
    apply isUnit_iff_ne_zero.mpr
    simpa only [Nat.cast_add, Nat.cast_one] using hden (k + 1) (by omega) (by omega)
  have hf0 : f.coeff 0 = 1 := by simp [f, coeff_pack, wCoeff, c]
  have hfn : f.coeff n ^ 2 = 1 := by
    have hc : (c n : ZMod p) = (-4) ^ n := by
      have hh := half_choose_identity n h2 hnK hden n le_rfl
      simpa only [Nat.choose_self, Nat.cast_one, one_mul] using hh.symm
    have he : f.coeff n = (-1) ^ n := by
      dsimp [f]
      rw [coeff_pack, if_pos le_rfl, wCoeff, hc, ← pow_mul, mul_comm n 3, pow_mul,
        ← div_pow]
      congr 1
      apply (div_eq_iff h64).mpr
      ring
    rw [he, ← pow_mul, mul_comm n 2, pow_mul]
    simp
  obtain ⟨ef, eg, eq⟩ := pack_ode h64 hn0 hu
  obtain ⟨ha, hk, hj⟩ := full_invariants hp.1.pos hn h2
    (pack_degree n _) (pack_degree n _) (pack_degree n _) hf0 hfn ef eg eq
  have hft : f.eval 64 = 0 := by
    rw [show f = pack n (wCoeff (ZMod p)) from rfl, pack_eval n _ h64]
    have hh := congrArg (reducePrime p) (prime_case p hp)
    rw [reducePrime_primeSum, map_zero] at hh
    exact hh
  obtain ⟨hdf, hgt, hprod⟩ := root_of_invariants h2 ha hk hj h64 ht1 (ZMod.pow_card _) hft
  change (derivative f).eval 64 = 0 at hdf
  have hfirst : (theta f).eval 64 = 0 := by
    simp only [theta, eval_mul, eval_X, hdf, mul_zero]
  have hfirst' : (∑ k ∈ range (n + 1), (k : ZMod p) * wCoeff (ZMod p) k) = 0 := by
    simpa only [f, theta_pack, pack_eval n _ h64] using hfirst
  have hsecond : (∑ k ∈ range (n + 1), bCoeff (ZMod p) k) = 0 := by
    simpa only [g, pack_eval n _ h64] using hgt
  have hprod' : (∑ k ∈ range (n + 1), qCoeff (ZMod p) k) *
      (∑ k ∈ range (n + 1), (k : ZMod p) ^ 2 * wCoeff (ZMod p) k) = 1 := by
    simpa only [q, f, theta_pack, pack_eval n _ h64, pow_two, mul_assoc] using hprod
  exact ⟨hfirst', hsecond, hprod'⟩

end A79727Cubic


namespace A79727Cubic
open Finset A79727Proof

theorem sum_range_blocks {R : Type*} [AddCommMonoid R] (f : ℕ → R) (m p : ℕ) :
    ∑ k ∈ range (m * p), f k = ∑ a ∈ range m, ∑ b ∈ range p, f (a * p + b) := by
  induction m with
  | zero => simp
  | succ m ih => simp only [Nat.succ_mul, sum_range_add, ih, sum_range_succ]

theorem sum_range_zmod {R : Type*} [AddCommMonoid R] {p : ℕ} [NeZero p] (hp : 0 < p)
    (f : ZMod p → R) : ∑ k ∈ range p, f k = ∑ x : ZMod p, f x := by
  classical
  apply sum_bij (fun (k : ℕ) _ => (k : ZMod p))
  · intros; exact mem_univ _
  · intro a ha b hb he
    have hh := congrArg ZMod.val he
    simpa only [ZMod.val_natCast_of_lt (mem_range.mp ha),
      ZMod.val_natCast_of_lt (mem_range.mp hb)] using hh
  · intro x hx
    exact ⟨x.val, mem_range.mpr (ZMod.val_lt x), ZMod.natCast_zmod_val x⟩
  · intros; rfl

theorem inverse_sq_sum {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    (∑ k ∈ range p, ((k : ZMod p)⁻¹) ^ 2) = 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [sum_range_zmod hp.pos (fun x : ZMod p => (x⁻¹) ^ 2)]
  have he : (∑ x : ZMod p, (x⁻¹) ^ 2) = ∑ x : ZMod p, x ^ 2 := by
    apply sum_bij (fun x _ => x⁻¹)
    · intros; exact mem_univ _
    · intro a ha b hb he; exact inv_injective he
    · intro x hx; exact ⟨x⁻¹, mem_univ _, inv_inv x⟩
    · intros; rfl
  rw [he]
  exact FiniteField.sum_pow_lt_card_sub_one (ZMod p) 2 (by rw [ZMod.card]; omega)

end A79727Cubic


set_option maxHeartbeats 1600000

namespace A79727Cubic
open Finset A79727Proof

-- A binomial identity with positive lower index.
theorem choose_mul_index {N k : ℕ} (hN : 0 < N) (hk : 0 < k) :
    k * N.choose k = N * (N - 1).choose (k - 1) := by
  have hh := Nat.add_one_mul_choose_eq (N - 1) (k - 1)
  rw [Nat.sub_add_cancel hN, Nat.sub_add_cancel hk] at hh
  simpa only [Nat.mul_comm] using hh.symm

theorem choose_square_dvd {p k : ℕ} (hp : p.Prime)
    (hk : 0 < k) (hpk : ¬p ∣ k) : p ^ 2 ∣ (p ^ 2).choose k := by
  have hh := choose_mul_index (pow_pos hp.pos 2) hk
  have hc : (p ^ 2).Coprime k := (hp.coprime_iff_not_dvd.mpr hpk).pow_left 2
  apply hc.dvd_of_dvd_mul_left
  rw [hh]
  exact dvd_mul_right _ _

theorem choose_mul_prime {p a : ℕ} (hp : p.Prime) (ha : 0 < a) :
    a * (p ^ 2).choose (a * p) = p * (p ^ 2 - 1).choose (a * p - 1) := by
  have hh := choose_mul_index (pow_pos hp.pos 2)
    (Nat.mul_pos ha hp.pos)
  apply Nat.mul_left_cancel hp.pos
  simpa only [pow_two, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hh

theorem choose_pred_prime_field {p : ℕ} (hp : p.Prime) (k : ℕ) (hk : k < p) :
    ((p - 1).choose k : ZMod p) = (-1) ^ k := by
  letI : Fact p.Prime := ⟨hp⟩
  induction k with
  | zero => simp
  | succ k ih =>
    have ih := ih (by omega)
    have hh := congrArg (fun m : ℕ => (m : ZMod p))
      (Nat.choose_succ_right_eq (p - 1) k)
    have hpred : ((p - 1 - k : ℕ) : ZMod p) = -((k : ZMod p) + 1) := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub hp.one_le, ZMod.natCast_self]
      push_cast
      ring
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, ih, hpred] at hh
    apply mul_right_cancel₀ (show (k : ZMod p) + 1 ≠ 0 from by
      simpa only [Nat.cast_add, Nat.cast_one] using
        (cast_ne_zero_below (R := ZMod p) (by omega : 0 < k + 1) hk))
    rw [pow_succ]
    linear_combination hh

theorem choose_pred_square_field {p a : ℕ} (hp : p.Prime)
    (ha : 0 < a) (hap : a < p) :
    ((p ^ 2 - 1).choose (a * p - 1) : ZMod p) ^ 2 = 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hn : p ^ 2 - 1 = (p - 1) * p + (p - 1) := by
    have := hp.two_le
    have h := Nat.sub_add_cancel hp.one_le
    have hsq : 1 ≤ p ^ 2 := by nlinarith
    have h' := Nat.sub_add_cancel hsq
    nlinarith
  have hk : a * p - 1 = (a - 1) * p + (p - 1) := by
    have h := Nat.sub_add_cancel hp.one_le
    have h' := Nat.sub_add_cancel ha
    have h'' := Nat.sub_add_cancel (Nat.mul_pos ha hp.pos)
    nlinarith
  have hm := Choose.choose_modEq_choose_mod_mul_choose_div_nat
    (n := p ^ 2 - 1) (k := a * p - 1) (p := p)
  rw [hn, hk] at hm
  have hp1 : p - 1 < p := by omega
  have hmod (b : ℕ) : (b * p + (p - 1)) % p = p - 1 := by
    simp [Nat.add_mod, Nat.mod_eq_of_lt hp1]
  have hdiv (b : ℕ) : (b * p + (p - 1)) / p = b := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp.pos, Nat.div_eq_of_lt hp1, Nat.zero_add]
  rw [hmod, hmod, hdiv, hdiv, Nat.choose_self, one_mul] at hm
  rw [← hn, ← hk] at hm
  have he := (ZMod.natCast_eq_natCast_iff _ _ p).mpr hm
  rw [he, choose_pred_prime_field hp (a - 1) (by omega)]
  rw [← pow_mul, mul_comm (a - 1) 2, pow_mul]
  simp

end A79727Cubic


set_option maxHeartbeats 1600000

namespace A79727Cubic
open Finset A79727Proof

theorem choose_nondigit_square_zero {p a b : ℕ} (hp : p.Prime)
    (hb : 0 < b) (hbp : b < p) :
    ((p ^ 2).choose (a * p + b) : ZMod (p ^ 3)) ^ 2 = 0 := by
  have hpk : ¬p ∣ a * p + b := by
    intro hh
    have hm := Nat.mod_eq_zero_of_dvd hh
    have hmod : (a * p + b) % p = b := by simp [Nat.add_mod, Nat.mod_eq_of_lt hbp]
    rw [hmod] at hm
    omega
  obtain ⟨t, ht⟩ := choose_square_dvd hp (by omega : 0 < a * p + b) hpk
  rw [ht, Nat.cast_mul, Nat.cast_pow]
  calc
    ((p : ZMod (p ^ 3)) ^ 2 * t) ^ 2 = (p : ZMod (p ^ 3)) ^ 3 * (p * t ^ 2) := by ring
    _ = 0 := by rw [p_cube_zero, zero_mul]

theorem choose_digit_square {p a : ℕ} (hp : p.Prime) (ha : 0 < a) (hap : a < p) :
    ((p ^ 2).choose (a * p) : ZMod (p ^ 3)) ^ 2 =
      (p : ZMod (p ^ 3)) ^ 2 * Ring.inverse (a : ZMod (p ^ 3)) ^ 2 := by
  have hu := small_unit3 hp ha hap
  have hinv := Ring.mul_inverse_cancel (a : ZMod (p ^ 3)) hu
  have hh := congrArg (fun m : ℕ => (m : ZMod (p ^ 3))) (choose_mul_prime hp ha)
  simp only [Nat.cast_mul] at hh
  have hy := p_sq_mul_eq hp
    (((p ^ 2 - 1).choose (a * p - 1) : ZMod (p ^ 3)) ^ 2) 1
    (by simpa only [map_pow, map_natCast, map_one] using choose_pred_square_field hp ha hap)
  apply (hu.pow 2).mul_left_cancel
  have hh2 := congrArg (fun x : ZMod (p ^ 3) => x ^ 2) hh
  have hi2 := congrArg (fun x : ZMod (p ^ 3) => x ^ 2) hinv
  linear_combination hh2 + hy - (p : ZMod (p ^ 3)) ^ 2 * hi2

theorem endpoint_binomial {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    (c (p ^ 2) : ZMod (p ^ 3)) = 2 := by
  letI : Fact p.Prime := ⟨hp⟩
  let u : ℕ → ZMod (p ^ 3) := fun a => Ring.inverse (a : ZMod (p ^ 3)) ^ 2
  have hsum : (p : ZMod (p ^ 3)) ^ 2 * ∑ a ∈ range p, u a = 0 := by
    apply p_sq_annihilates hp
    rw [map_sum]
    have hm : ∀ a ∈ range p, reduce31 p (u a) = ((a : ZMod p)⁻¹) ^ 2 := by
      intro a ha
      by_cases ha0 : a = 0
      · subst a
        simp [u, Ring.inverse_zero]
      · have hu := small_unit3 hp (by omega : 0 < a) (mem_range.mp ha)
        dsimp [u]
        rw [map_pow, map_ringInverse _ hu, map_natCast, Ring.inverse_eq_inv]
    rw [sum_congr rfl hm]
    exact inverse_sq_sum hp h5
  have hb (a : ℕ) (ha : a < p) :
      ∑ b ∈ range p, ((p ^ 2).choose (a * p + b) : ZMod (p ^ 3)) ^ 2 =
        ((p ^ 2).choose (a * p) : ZMod (p ^ 3)) ^ 2 := by
    apply (sum_eq_single 0 ?_ ?_).trans
    · simp
    · intro b hb hb0
      exact choose_nondigit_square_zero hp (by omega) (mem_range.mp hb)
    · intro hh
      exact False.elim (hh (mem_range.mpr hp.pos))
  have hd (a : ℕ) (ha : a < p) :
      ((p ^ 2).choose (a * p) : ZMod (p ^ 3)) ^ 2 =
        (if a = 0 then 1 else 0) + (p : ZMod (p ^ 3)) ^ 2 * u a := by
    by_cases ha0 : a = 0
    · subst a
      simp [u, Ring.inverse_zero]
    · simp only [if_neg ha0, zero_add]
      exact choose_digit_square hp (by omega) ha
  have hv := congrArg (fun m : ℕ => (m : ZMod (p ^ 3))) (Nat.sum_range_choose_sq (p ^ 2))
  simp only [Nat.cast_sum, Nat.cast_pow] at hv
  change (∑ k ∈ range (p ^ 2 + 1), ((p ^ 2).choose k : ZMod (p ^ 3)) ^ 2) =
    (c (p ^ 2) : ZMod (p ^ 3)) at hv
  rw [← hv, sum_range_succ]
  rw [show p ^ 2 = p * p by ring, sum_range_blocks]
  have he : (∑ a ∈ range p, ∑ b ∈ range p,
      ((p * p).choose (a * p + b) : ZMod (p ^ 3)) ^ 2) =
      ∑ a ∈ range p, ((p ^ 2).choose (a * p) : ZMod (p ^ 3)) ^ 2 := by
    apply sum_congr rfl
    intro a ha
    simpa only [pow_two] using hb a (mem_range.mp ha)
  rw [he, sum_congr rfl (fun a ha => hd a (mem_range.mp ha)), sum_add_distrib,
    ← mul_sum, hsum]
  norm_num [hp.pos]

end A79727Cubic


set_option maxHeartbeats 1600000

namespace A79727Cubic
open Finset A79727Proof

noncomputable def halfSum {R : Type*} [AddCommMonoid R] (p : ℕ) (f : ℕ → R) : R :=
  ∑ k ∈ range ((p - 1) / 2 + 1), f k

noncomputable def moment (R : Type*) [CommRing R] (p j : ℕ) : R :=
  halfSum p (fun k => (k : R) ^ j * wCoeff R k)

noncomputable def outerMoment (p j : ℕ) : ZMod (p ^ 3) :=
  ∑ a ∈ range p, (a : ZMod (p ^ 3)) ^ j * (c (a * p) : ZMod (p ^ 3)) ^ 3

theorem central_lucas {p : ℕ} (hp : p.Prime) (a : ℕ) :
    (c (a * p) : ZMod p) = (c a : ZMod p) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hh := Choose.choose_mul_mul_modEq_choose_nat (a := 2 * a) (b := a) (p := p)
  apply (ZMod.natCast_eq_natCast_iff _ _ p).mpr
  simpa only [c, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hh

theorem halfSum_extend {R : Type*} [AddCommMonoid R] {p : ℕ} (hp : p.Prime)
    (f : ℕ → R) (hz : ∀ k, (p - 1) / 2 < k → k < p → f k = 0) :
    ∑ k ∈ range p, f k = halfSum p f := by
  unfold halfSum
  symm
  apply sum_subset (range_mono (by have := hp.two_le; omega))
  intro k hk hn
  apply hz k
  · simp only [mem_range] at hn
    omega
  · exact mem_range.mp hk

theorem outerMoment_reduce {p : ℕ} (hp : p.Prime) (j : ℕ) :
    reduce31 p (outerMoment p j) = moment (ZMod p) p j := by
  unfold outerMoment moment
  simp only [map_sum, map_mul, map_pow, map_natCast, central_lucas hp]
  apply halfSum_extend hp
  intro k hk hkp
  have hd := upper_half_dvd hp 0 k hk hkp
  simp only [zero_mul, zero_add] at hd
  have hz : (c k : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hd
  simp [wCoeff, hz]

theorem full_block3 {p : ℕ} (hp : p.Prime) (a : ℕ) :
    (∑ b ∈ range p, (c (a * p + b) : ZMod (p ^ 3)) ^ 3) =
      (c (a * p) : ZMod (p ^ 3)) ^ 3 *
      (halfSum p (wCoeff (ZMod (p ^ 3))) +
        (a : ZMod (p ^ 3)) * (p : ZMod (p ^ 3)) * halfSum p (bCoeff (ZMod (p ^ 3))) +
        (a : ZMod (p ^ 3)) ^ 2 * (p : ZMod (p ^ 3)) ^ 2 *
          halfSum p (qCoeff (ZMod (p ^ 3)))) := by
  rw [halfSum_extend hp _ (fun b hb hbp => cube_zero_of_dvd (upper_half_dvd hp a b hb hbp))]
  unfold halfSum
  rw [show (∑ k ∈ range ((p - 1) / 2 + 1), (c (a * p + k) : ZMod (p ^ 3)) ^ 3) =
      ∑ k ∈ range ((p - 1) / 2 + 1), (c (a * p) : ZMod (p ^ 3)) ^ 3 *
        (wCoeff (ZMod (p ^ 3)) k + (a : ZMod (p ^ 3)) * (p : ZMod (p ^ 3)) * bCoeff (ZMod (p ^ 3)) k +
          (a : ZMod (p ^ 3)) ^ 2 * (p : ZMod (p ^ 3)) ^ 2 * qCoeff (ZMod (p ^ 3)) k) by
    apply sum_congr rfl
    intro k hk
    apply shifted_cube3 hp
    have := hp.two_le
    simp only [mem_range] at hk
    omega]
  simp only [mul_add, sum_add_distrib, ← mul_sum]

theorem full_square_expansion {p : ℕ} (hp : p.Prime) :
    (∑ k ∈ range (p ^ 2), (c k : ZMod (p ^ 3)) ^ 3) =
      halfSum p (wCoeff (ZMod (p ^ 3))) * outerMoment p 0 +
      (p : ZMod (p ^ 3)) * halfSum p (bCoeff (ZMod (p ^ 3))) * outerMoment p 1 +
      (p : ZMod (p ^ 3)) ^ 2 *
        (halfSum p (qCoeff (ZMod (p ^ 3))) * outerMoment p 2) := by
  rw [show p ^ 2 = p * p by ring, sum_range_blocks]
  simp only [full_block3 hp]
  unfold outerMoment
  simp only [pow_zero, pow_one, one_mul, mul_add, sum_add_distrib, mul_sum]
  congr 2 <;> (first | apply sum_congr rfl | funext i) <;> intros <;> ring

theorem halfSum_w_reduce32 (p : ℕ) :
    reduce32 p (halfSum p (wCoeff (ZMod (p ^ 3)))) = primeSum p := by
  simp only [halfSum, wCoeff, primeSum, map_sum, map_pow, map_natCast]

theorem halfSum_b_reduce31 {p : ℕ} (hp : p.Prime) :
    reduce31 p (halfSum p (bCoeff (ZMod (p ^ 3)))) = halfSum p (bCoeff (ZMod p)) := by
  unfold halfSum
  rw [map_sum]
  apply sum_congr rfl
  intro k hk
  apply map_bCoeff
  intro j hj
  have := hp.two_le
  have hu := small_unit3 hp (n := j + 1) (by omega) (by simp only [mem_range] at hk; omega)
  simpa only [Nat.cast_add, Nat.cast_one] using hu

theorem halfSum_q_reduce31 {p : ℕ} (hp : p.Prime) :
    reduce31 p (halfSum p (qCoeff (ZMod (p ^ 3)))) = halfSum p (qCoeff (ZMod p)) := by
  unfold halfSum
  rw [map_sum]
  apply sum_congr rfl
  intro k hk
  apply map_qCoeff
  intro j hj
  have := hp.two_le
  have hu := small_unit3 hp (n := j + 1) (by omega) (by simp only [mem_range] at hk; omega)
  simpa only [Nat.cast_add, Nat.cast_one] using hu

end A79727Cubic


set_option maxHeartbeats 1600000

namespace A79727Cubic
open Finset A79727Proof

theorem suffix_zero {p : ℕ} (hp : p.Prime) (hpodd : Odd p) :
    ∀ k, p * (p - 1) ≤ k → k < p ^ 2 → (c k : ZMod (p ^ 3)) ^ 3 = 0 := by
  intro k hk hk2
  let a := p - 1
  let b := k - a * p
  have he : k = a * p + b := by
    have ha : a * p ≤ k := by simpa only [a, Nat.mul_comm] using hk
    dsimp [b]
    omega
  have hb : b < p := by
    have hp1 := Nat.sub_add_cancel hp.one_le
    have hprod : a * p + p = p ^ 2 := by dsimp [a]; nlinarith
    omega
  by_cases hbh : (p - 1) / 2 < b
  · rw [he]
    exact cube_zero_of_dvd (upper_half_dvd hp a b hbh hb)
  · have hlow : 2 * b < p := by
      obtain ⟨m, hm⟩ := hpodd
      omega
    letI : Fact p.Prime := ⟨hp⟩
    have hlucas := Choose.choose_modEq_choose_mod_mul_choose_div_nat
      (n := 2 * k) (k := k) (p := p)
    have hkmod : k % p = b := by rw [he]; simp [Nat.add_mod, Nat.mod_eq_of_lt hb]
    have hkdiv : k / p = a := by
      rw [he, Nat.add_comm, Nat.add_mul_div_right _ _ hp.pos, Nat.div_eq_of_lt hb, Nat.zero_add]
    have h2kdiv : 2 * k / p = 2 * a := by
      rw [he, show 2 * (a * p + b) = (2 * a) * p + 2 * b by ring,
        Nat.add_comm, Nat.add_mul_div_right _ _ hp.pos, Nat.div_eq_of_lt hlow, Nat.zero_add]
    have hd : p ∣ c a := by
      have ha : (p - 1) / 2 < a := by
        obtain ⟨m, hm⟩ := hpodd
        have := hp.two_le
        dsimp [a]
        omega
      simpa only [zero_mul, zero_add] using upper_half_dvd hp 0 a ha (by dsimp [a]; omega)
    have hz : (2 * a).choose a ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr hd
    rw [hkmod, hkdiv, h2kdiv] at hlucas
    have hc : p ∣ c k := by
      apply Nat.modEq_zero_iff_dvd.mp
      exact hlucas.trans ((Nat.ModEq.refl _).mul hz)
    exact cube_zero_of_dvd hc

end A79727Cubic


set_option maxHeartbeats 1600000

namespace A79727Cubic
open Finset A79727Proof

theorem auxiliary {p : ℕ} (hp : OeisA3625.A p) (h5 : 5 ≤ p) :
    (∑ k ∈ range (p ^ 2), (c k : ZMod (p ^ 3)) ^ 3) = (p : ZMod (p ^ 3)) ^ 2 := by
  obtain ⟨hm1, hb, hq⟩ := field_moments hp h5
  have hm0 : moment (ZMod p) p 0 = 0 := by
    have hh := congrArg (reducePrime p) (prime_case p hp)
    rw [reducePrime_primeSum, map_zero] at hh
    simpa only [moment, halfSum, wCoeff, pow_zero, one_mul, primeSumField] using hh
  have hm1' : moment (ZMod p) p 1 = 0 := by
    simpa only [moment, halfSum, pow_one] using hm1
  have ht0 := reduced_product_zero hp.1
    (halfSum p (wCoeff (ZMod (p ^ 3)))) (outerMoment p 0)
    (by rw [halfSum_w_reduce32, prime_case p hp])
    (by rw [outerMoment_reduce hp.1, hm0])
  have ht1 := p_reduced_product_zero hp.1
    (halfSum p (bCoeff (ZMod (p ^ 3)))) (outerMoment p 1)
    (by rw [halfSum_b_reduce31 hp.1]; exact hb)
    (by rw [outerMoment_reduce hp.1, hm1'])
  have ht2 := p_sq_mul_eq hp.1
    (halfSum p (qCoeff (ZMod (p ^ 3))) * outerMoment p 2) 1
    (by rw [map_mul, halfSum_q_reduce31 hp.1, outerMoment_reduce hp.1, map_one]; exact hq)
  rw [full_square_expansion hp.1, ht0, ht1, ht2]
  ring

theorem conjecture1_large {p : ℕ} (hp : OeisA3625.A p) (h5 : 5 ≤ p) :
    OeisA79727.a (p ^ 2) ≡ 8 + p ^ 2 [MOD p ^ 3] := by
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
  simp only [OeisA79727.a, Nat.cast_sum, Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat]
  change (∑ k ∈ range (p ^ 2 + 1), (c k : ZMod (p ^ 3)) ^ 3) = 8 + (p : ZMod (p ^ 3)) ^ 2
  rw [sum_range_succ, auxiliary hp h5, endpoint_binomial hp.1 h5]
  ring

theorem conjecture2_large {p : ℕ} (hp : OeisA3625.A p) (h5 : 5 ≤ p) :
    OeisA79727.a (p * (p - 1)) ≡ p ^ 2 [MOD p ^ 3] := by
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
  simp only [OeisA79727.a, Nat.cast_sum, Nat.cast_pow]
  change (∑ k ∈ range (p * (p - 1) + 1), (c k : ZMod (p ^ 3)) ^ 3) = (p : ZMod (p ^ 3)) ^ 2
  rw [← auxiliary hp h5]
  apply sum_subset (range_mono (by have := hp.1.one_le; nlinarith [Nat.sub_add_cancel this]))
  intro k hk hn
  apply suffix_zero hp.1 (eligible_odd hp) k
  · simp only [mem_range] at hn
    omega
  · exact mem_range.mp hk

/-- Peter Bala's first conjecture, with the exact hypotheses and conclusion of the source. -/
theorem conjecture1 (p : ℕ) (hp : OeisA3625.A p) :
    OeisA79727.a (p ^ 2) ≡ 8 + p ^ 2 [MOD p ^ 3] := by
  by_cases hp3 : p = 3
  · subst p
    norm_num [OeisA79727.a, sum_range_succ]
    decide
  · apply conjecture1_large hp
    have := hp.1.two_le
    obtain ⟨m, hm⟩ := eligible_odd hp
    omega

/-- Peter Bala's second conjecture, with the exact hypotheses and conclusion of the source. -/
theorem conjecture2 (p : ℕ) (hp : OeisA3625.A p) :
    OeisA79727.a (p * (p - 1)) ≡ p ^ 2 [MOD p ^ 3] := by
  by_cases hp3 : p = 3
  · subst p
    norm_num [OeisA79727.a, sum_range_succ]
    decide
  · apply conjecture2_large hp
    have := hp.1.two_le
    obtain ⟨m, hm⟩ := eligible_odd hp
    omega

end A79727Cubic



-- Compare declaration types only. No source conjecture is used as a proof.
open Lean Elab Command in
run_cmd do
  for (source, result) in [
      (``OeisA79727.conjecture1, ``A79727Cubic.conjecture1),
      (``OeisA79727.conjecture2, ``A79727Cubic.conjecture2)] do
    let original ← getConstInfo source
    let proved ← getConstInfo result
    let same ← liftTermElabM <| Meta.isDefEq proved.type original.type
    unless same do
      throwError "Type mismatch: {result} does not prove the exact statement of {source}."
    let axioms ← Lean.collectAxioms result
    for ax in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {result}."
    logInfo m!"Verified {result}: exact source type; only standard axioms."

#print axioms A79727Cubic.conjecture1
#print axioms A79727Cubic.conjecture2
