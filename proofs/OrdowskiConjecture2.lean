import Mathlib

/-!
# Ordowski's second question for OEIS A051903

A negative answer to Thomas Ordowski's question of December 2, 2019.

Sources:
* https://oeis.org/A051903
* https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/OEIS/51903.lean

The definition `OeisA51903.a` is copied exactly from the Formal Conjectures
statement. The final theorem is its `conjecture2`, with the requested answer
resolved to `False`. This file depends only on Mathlib.

Checked with Lean 4.33.1 and the Mathlib version in the accompanying project.
-/

set_option autoImplicit false

namespace OeisA51903

/-- Maximum exponent in the prime factorization of `n`; the original definition. -/
def a (n : ℕ) : ℕ :=
  (n.primeFactorsList.map (n.primeFactorsList.count ·)).foldr max 0

private theorem foldr_max_mem (l : List ℕ) (h : 0 < l.foldr max 0) :
    l.foldr max 0 ∈ l := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    simp only [List.foldr_cons] at h ⊢
    by_cases hx : xs.foldr max 0 ≤ x
    · simp [max_eq_left hx]
    · have hxt : x < xs.foldr max 0 := lt_of_not_ge hx
      rw [max_eq_right (le_of_lt hxt)]
      exact List.mem_cons_of_mem x (ih (lt_of_le_of_lt (Nat.zero_le x) hxt))

private theorem exponent_lt_prime_power {p e : ℕ} (hp : 3 ≤ p) (he : 2 ≤ e) :
    e < p ^ (e - 1) := by
  have h : ∀ k : ℕ, k + 2 < p ^ (k + 1) := by
    intro k
    induction k with
    | zero => simpa using (show 2 < p by omega)
    | succ k ih =>
      rw [Nat.succ_add, pow_succ]
      have hpos : 0 < p ^ (k + 1) := pow_pos (by omega) _
      nlinarith
  have hk := h (e - 2)
  have h1 : e - 2 + 2 = e := by omega
  have h2 : e - 2 + 1 = e - 1 := by omega
  simpa only [h1, h2] using hk

/-- The all-bases congruence forces the Carmichael exponent to divide `n - e`. -/
private theorem carmichael_dvd_sub {n e : ℕ} (hn : n ≠ 0) (he : e ≤ n)
    (h : ∀ b : ℕ, b ^ n ≡ b ^ e [MOD n]) :
    ArithmeticFunction.carmichael n ∣ n - e := by
  let : NeZero n := ⟨hn⟩
  rw [ArithmeticFunction.carmichael_eq_exponent hn]
  apply Monoid.exponent_dvd_of_forall_pow_eq_one
  intro u
  have hu : u ^ n = u ^ e := by
    apply Units.ext
    have hb := (ZMod.natCast_eq_natCast_iff _ _ n).mpr (h (u : ZMod n).val)
    simpa only [Nat.cast_pow, ZMod.natCast_zmod_val, Units.val_pow_eq_pow_val] using hb
  rw [pow_sub u he, hu, mul_inv_cancel]

/-- No odd integer with maximum prime-factor exponent greater than one has
the proposed congruence for every base. -/
theorem no_odd_solution :
    ¬ ∃ n : ℕ, Odd n ∧ 1 < a n ∧ ∀ b : ℕ, b ^ n ≡ b ^ (a n) [MOD n] := by
  rintro ⟨n, hn, he, hall⟩
  have hn0 : n ≠ 0 := by
    intro h
    subst n
    simp at hn
  have hmem : a n ∈ n.primeFactorsList.map (n.primeFactorsList.count ·) :=
    foldr_max_mem _ (lt_trans Nat.zero_lt_one he)
  obtain ⟨p, hp_mem, hp_eq⟩ := List.mem_map.mp hmem
  have hp : p.Prime := Nat.prime_of_mem_primeFactorsList hp_mem
  have hpdvd : p ∣ n := (Nat.mem_primeFactorsList hn0).mp hp_mem |>.2
  have hp_ne_two : p ≠ 2 := by
    intro h
    exact hn.not_two_dvd_nat (h ▸ hpdvd)
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  rw [Nat.primeFactorsList_count_eq] at hp_eq
  have hpow : p ^ a n ∣ n := by
    rw [← hp_eq]
    exact Nat.ordProj_dvd n p
  have hbound : a n < p ^ (a n - 1) := exponent_lt_prime_power hp3 (by omega)
  have hpred : p ^ (a n - 1) ∣ n :=
    (pow_dvd_pow p (Nat.sub_le (a n) 1)).trans hpow
  have he_le : a n ≤ n := le_trans (le_of_lt hbound) (Nat.le_of_dvd (by omega) hpred)
  have hlam : ArithmeticFunction.carmichael n ∣ n - a n :=
    carmichael_dvd_sub hn0 he_le hall
  have hlocal : p ^ (a n - 1) ∣ ArithmeticFunction.carmichael n := by
    have hc := ArithmeticFunction.carmichael_dvd hpow
    rw [ArithmeticFunction.carmichael_pow_of_prime_ne_two (a n) hp hp_ne_two,
      Nat.totient_prime_pow hp (by omega)] at hc
    exact (dvd_mul_right _ _).trans hc
  have hdiv : p ^ (a n - 1) ∣ a n := by
    have hd := Nat.dvd_sub hpred (hlocal.trans hlam)
    simpa only [Nat.sub_sub_self he_le] using hd
  exact (not_le_of_gt hbound) (Nat.le_of_dvd (by omega) hdiv)

/-- DeepMind's complete formal statement, with `answer(sorry)` resolved to `False`. -/
theorem conjecture2 :
    False ↔ ∃ n : ℕ, Odd n ∧ 1 < a n ∧ ∀ b : ℕ, b ^ n ≡ b ^ (a n) [MOD n] := by
  exact ⟨False.elim, no_odd_solution⟩

end OeisA51903

#print axioms OeisA51903.conjecture2
