/-
Copyright (c) 2026 Jensen Kohlmeyer and Liam Kruer.
Released under the Apache 2.0 license.
OpenAI Codex assisted with discovery, verification, formalization, and writing.
-/
import FormalConjectures.OEIS.«105720»

/-!
# A counterexample to the square conjecture for triangular matchstick prime sums

The sequence is OEIS A105720.
This single file imports the exact Formal Conjectures sequence definition and proves
`A105720.counterexample_value` and `A105720.conjecture_false`.

The witness is n = 111008771, with a(n) = 622112686^2.
The repository's unproved declaration `OeisA105720.conjecture` is not used.

Environment: Lean 4.33.1; Formal Conjectures revision
89294ea02bd7cd678d59984add52cb4baef3dbf4; Mathlib revision
0df444a360eaa60ab8c11dca51a86af692955474.

Four finite computations use `native_decide`: two grid-closure checks and two
sieve-table evaluations. In this Lean version those introduce generated evaluation
axioms, trusting the compiler/runtime. All generic correctness arguments are ordinary
Lean proofs. The concluding `#print axioms` commands expose the trust dependencies.
-/

set_option maxHeartbeats 0
set_option autoImplicit false

namespace A105720
open Finset

/-- Primes, together with composites whose least prime factor has not yet been removed. -/
def survivors (p v : ℕ) : Finset ℕ :=
  (Icc 2 v).filter (fun m => m.Prime ∨ p ≤ m.minFac)

lemma mem_survivors {p v m : ℕ} :
    m ∈ survivors p v ↔ 2 ≤ m ∧ m ≤ v ∧ (m.Prime ∨ p ≤ m.minFac) := by
  simp [survivors, and_assoc]

lemma survivors_mono_v {p v w : ℕ} (h : v ≤ w) :
    survivors p v ⊆ survivors p w := by
  intro m hm
  simp only [mem_survivors] at hm ⊢
  exact ⟨hm.1, hm.2.1.trans h, hm.2.2⟩

lemma survivors_mono_p {p v : ℕ} : survivors (p+1) v ⊆ survivors p v := by
  intro m hm
  simp only [mem_survivors] at hm ⊢
  exact ⟨hm.1, hm.2.1, hm.2.2.imp_right (by omega)⟩

lemma minFac_mul {p m : ℕ} (hp : p.Prime) (hm : p ≤ m.minFac) (hm2 : 2 ≤ m) :
    (p*m).minFac = p := by
  apply le_antisymm (Nat.minFac_le_of_dvd hp.two_le (dvd_mul_right p m))
  have hne : p*m ≠ 1 := by have := hp.two_le; nlinarith
  apply (Nat.le_minFac.mpr ?_).resolve_left hne
  intro q hq hd
  rcases hq.dvd_mul.mp hd with hd | hd
  · have := (Nat.prime_dvd_prime_iff_eq hq hp).mp hd
    omega
  · exact hm.trans (Nat.minFac_le_of_dvd hq.two_le hd)

lemma removed_iff {p v m : ℕ} :
    m ∈ survivors p v \ survivors (p+1) v ↔
      2 ≤ m ∧ m ≤ v ∧ ¬m.Prime ∧ m.minFac = p := by
  simp only [mem_sdiff, mem_survivors]
  constructor
  · rintro ⟨⟨h2, hv, hs⟩, hn⟩
    have hnp : ¬m.Prime := fun h => hn ⟨h2, hv, Or.inl h⟩
    have hl : p ≤ m.minFac := hs.resolve_left hnp
    have hu : ¬p+1 ≤ m.minFac := fun h => hn ⟨h2, hv, Or.inr h⟩
    exact ⟨h2, hv, hnp, by omega⟩
  · rintro ⟨h2, hv, hn, hf⟩
    exact ⟨⟨h2, hv, Or.inr (by omega)⟩,
      fun h => (h.2.2.elim hn (by omega))⟩

lemma multiplier_iff {p v m : ℕ} (hp : p.Prime) :
    m ∈ survivors p (v/p) \ survivors p (p-1) ↔
      p ≤ m ∧ m ≤ v/p ∧ p ≤ m.minFac := by
  simp only [mem_sdiff, mem_survivors]
  constructor
  · rintro ⟨⟨h2, hv, hs⟩, hn⟩
    have hl : p ≤ m := by
      by_contra h
      apply hn
      exact ⟨h2, by omega, hs⟩
    exact ⟨hl, hv, hs.elim (fun h => by simpa [h.minFac_eq] using hl) id⟩
  · rintro ⟨hl, hv, hf⟩
    exact ⟨⟨hp.two_le.trans hl, hv, Or.inr hf⟩, fun h => by omega⟩

/-- Multiplication by p identifies exactly the composites removed at the p-stage. -/
lemma removed_image {p v : ℕ} (hp : p.Prime) :
    survivors p v \ survivors (p+1) v =
      (survivors p (v/p) \ survivors p (p-1)).image (fun m => p*m) := by
  ext m
  rw [removed_iff, mem_image]
  constructor
  · rintro ⟨h2, hv, hn, hf⟩
    have hd : p ∣ m := hf ▸ Nat.minFac_dvd m
    obtain ⟨k, hk⟩ := hd
    have hl : p ≤ k := by
      have := Nat.minFac_le_div (by omega : 0 < m) hn
      rw [hf, hk, Nat.mul_div_cancel_left _ hp.pos] at this
      exact this
    have hk2 : 2 ≤ k := hp.two_le.trans hl
    have hfk : p ≤ k.minFac := by
      rw [← hf]
      apply Nat.minFac_le_of_dvd (Nat.minFac_prime (by omega)).two_le
      exact (Nat.minFac_dvd k).trans (hk ▸ dvd_mul_left k p)
    refine ⟨k, (multiplier_iff hp).mpr ⟨hl, ?_, hfk⟩, hk.symm⟩
    rw [Nat.le_div_iff_mul_le hp.pos]
    simpa [hk, Nat.mul_comm] using hv
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨hl, hv, hf⟩ := (multiplier_iff hp).mp hk
    have hk2 := hp.two_le.trans hl
    refine ⟨?_, ?_, ?_, minFac_mul hp hf hk2⟩
    · have := hp.two_le; nlinarith
    · have := (Nat.le_div_iff_mul_le hp.pos).mp hv
      simpa [Nat.mul_comm] using this
    · intro hprime
      have he' := (Nat.dvd_prime hprime).mp (dvd_mul_right p k)
      have := hp.two_le
      rcases he' with he' | he' <;> nlinarith

lemma survivors_no_change {p v : ℕ} (h : ¬p.Prime ∨ v < p*p) :
    survivors (p+1) v = survivors p v := by
  apply subset_antisymm survivors_mono_p
  intro m hm
  by_contra hn
  have hr := removed_iff.mp (mem_sdiff.mpr ⟨hm, hn⟩)
  rcases h with hp | hv
  · apply hp
    rw [← hr.2.2.2]
    exact Nat.minFac_prime (by omega)
  · have := Nat.minFac_sq_le_self (by omega : 0 < m) hr.2.2.1
    rw [hr.2.2.2] at this
    nlinarith [hr.2.1]

def weighted (w : ℕ → ℤ) (p v : ℕ) : ℤ := ∑ m ∈ survivors p v, w m

/-- A single recurrence covers both the count (weight 1) and the sum (weight m). -/
lemma weighted_step {p v : ℕ} (hp : p.Prime) (hv : p*p ≤ v)
    (w : ℕ → ℤ) (c : ℤ) (hw : ∀ m, w (p*m) = c*w m) :
    weighted w (p+1) v = weighted w p v -
      c*(weighted w p (v/p) - weighted w p (p-1)) := by
  have hsub : survivors p (p-1) ⊆ survivors p (v/p) := by
    apply survivors_mono_v
    have := (Nat.le_div_iff_mul_le hp.pos).mpr hv
    omega
  have hi : Function.Injective (fun m : ℕ => p*m) :=
    fun a b h => Nat.eq_of_mul_eq_mul_left hp.pos h
  have hr := sum_sdiff (f := w) (survivors_mono_p (p := p) (v := v))
  rw [removed_image hp, sum_image (fun _ _ _ _ h => hi h)] at hr
  simp only [hw, ← mul_sum] at hr
  have hs := sum_sdiff (f := w) hsub
  simp only [weighted]
  linear_combination hr - c * hs

/-- Beyond the square root, the survivor set is exactly the finite set of primes. -/
lemma survivors_final {p v : ℕ} (h : v < p*p) :
    survivors p v = Nat.primesLE v := by
  ext m
  simp only [mem_survivors, Nat.mem_primesLE]
  constructor
  · rintro ⟨h2, hv, hp | hf⟩
    · exact ⟨hv, hp⟩
    · refine ⟨hv, ?_⟩
      by_contra hn
      have := Nat.minFac_sq_le_self (by omega : 0 < m) hn
      nlinarith
  · rintro ⟨hv, hp⟩
    exact ⟨hp.two_le, hv, Or.inl hp⟩

def stats (p v : ℕ) : ℤ × ℤ :=
  (weighted (fun _ => 1) p v, weighted (fun m => (m : ℤ)) p v)

def initial (v : ℕ) : ℤ × ℤ := ((v : ℤ)-1, (v*(v+1)/2 : ℕ)-1)

lemma survivors_two (v : ℕ) : survivors 2 v = Icc 2 v := by
  ext m
  simp only [mem_survivors, mem_Icc]
  constructor
  · exact fun h => ⟨h.1, h.2.1⟩
  · rintro ⟨h2, hv⟩
    exact ⟨h2, hv, Or.inr (Nat.minFac_prime (by omega)).two_le⟩

lemma stats_initial {v : ℕ} (hv : 1 ≤ v) : stats 2 v = initial v := by
  apply Prod.ext
  · simp only [stats, weighted, survivors_two, sum_const, Nat.card_Icc,
      nsmul_eq_mul, mul_one, initial]
    omega
  · have he : Icc 2 v = Ico 2 (v+1) := by
      ext m
      simp only [mem_Icc, mem_Ico]
      omega
    simp only [stats, weighted, survivors_two, he, initial]
    rw [sum_Ico_eq_sub _ (by omega : 2 ≤ v+1)]
    have hs : (∑ m ∈ range (v+1), (m : ℤ)) = ((v+1)*v/2 : ℕ) := by
      rw [← Nat.cast_sum]
      congr 1
      simpa using sum_range_id (v+1)
    rw [hs]
    norm_num [Nat.mul_comm, sum_range_succ]

lemma stats_step {p v : ℕ} (hp : p.Prime) (hv : p*p ≤ v) :
    stats (p+1) v =
      ((stats p v).1 - ((stats p (v/p)).1 - (stats p (p-1)).1),
       (stats p v).2 - (p : ℤ)*((stats p (v/p)).2 - (stats p (p-1)).2)) := by
  apply Prod.ext
  · exact (weighted_step hp hv (fun _ => 1) 1 (by simp)).trans (by simp [stats])
  · exact weighted_step hp hv (fun m => (m : ℤ)) (p : ℤ) (by simp)

/-- Descending quotient coordinates followed by the small integer coordinates. -/
def label (x b i : ℕ) : ℕ := if i < b then x/(i+1) else 2*b-i
def index (x b v : ℕ) : ℕ := if v ≤ b then 2*b-v else x/v-1

/-- The length of the prefix on which the current sieve stage makes a change. -/
def active (x b p : ℕ) : ℕ := min b (x/(p*p)) + (b+1-p*p)

/-- The executable prefix length is equivalent to the mathematical cutoff v >= p^2. -/
lemma active_iff {x b p i : ℕ} (hxb : b*b ≤ x) (hp : 2 ≤ p) (hi : i < 2*b) :
    i < active x b p ↔ p*p ≤ label x b i := by
  have hq : 0 < p*p := by positivity
  by_cases hb : p*p ≤ b
  · have hd : b ≤ x/(p*p) := by
      apply (Nat.le_div_iff_mul_le hq).mpr
      nlinarith
    rw [active, min_eq_left hd]
    by_cases hib : i < b
    · have hv : p*p ≤ x/(i+1) := by
        apply (Nat.le_div_iff_mul_le (by omega : 0 < i+1)).mpr
        nlinarith
      simp only [label, if_pos hib]
      omega
    · simp only [label, if_neg hib]
      omega
  · have hz : b+1-p*p = 0 := by omega
    rw [active, hz, add_zero]
    by_cases hib : i < b
    · simp only [label, if_pos hib, lt_min_iff]
      have hd : p*p ≤ x/(i+1) ↔ i+1 ≤ x/(p*p) := by
        rw [Nat.le_div_iff_mul_le (by omega : 0 < i+1), Nat.le_div_iff_mul_le hq]
        simp [Nat.mul_comm]
      omega
    · simp only [label, if_neg hib, lt_min_iff]
      omega

lemma active_le {x b p : ℕ} (hp : 2 ≤ p) : active x b p ≤ 2*b := by
  have := Nat.min_le_left b (x/(p*p))
  have : 1 ≤ p*p := by nlinarith
  unfold active
  omega

/-- Write a prefix, using a function that can read the immutable preceding table. -/
def overwrite {α : Type} (a : Array α) (n : ℕ) (f : ℕ → α) : Array α :=
  (List.range n).foldl (fun a i => a.set! i (f i)) a

lemma overwrite_succ {α : Type} (a : Array α) (n : ℕ) (f : ℕ → α) :
    overwrite a (n+1) f = (overwrite a n f).set! n (f n) := by
  simp [overwrite, List.range_succ, List.foldl_append]

lemma overwrite_size {α : Type} (a : Array α) (n : ℕ) (f : ℕ → α) :
    (overwrite a n f).size = a.size := by
  induction n with
  | zero => simp [overwrite]
  | succ n ih => rw [overwrite_succ, Array.size_set!, ih]

lemma overwrite_get {α : Type} [Inhabited α] (a : Array α) (n : ℕ) (f : ℕ → α)
    (hn : n ≤ a.size) (i : ℕ) :
    (overwrite a n f)[i]! = if i < n then f i else a[i]! := by
  induction n with
  | zero => simp [overwrite]
  | succ n ih =>
    rw [overwrite_succ]
    by_cases hi : n = i
    · subst i
      rw [Array.getElem!_set!_self _ _ _ (by rw [overwrite_size]; omega)]
      simp
    · rw [Array.getElem!_set!_ne _ _ _ _ hi, ih (by omega)]
      by_cases hlt : i < n
      · simp [hlt, show i < n+1 by omega]
      · simp [hlt, show ¬i < n+1 by omega]

/-- Positivity and validity of every lookup needed by every active prime stage. -/
def GoodGrid (x b : ℕ) : Prop :=
  (∀ i : Fin (2*b), 1 ≤ label x b i) ∧
  ∀ p : Fin (b+1), 2 ≤ (p : ℕ) → Nat.Prime p →
    index x b (p-1) < 2*b ∧ label x b (index x b (p-1)) = p-1 ∧
    ∀ i : Fin (active x b p),
      index x b (label x b i / p) < 2*b ∧
      label x b (index x b (label x b i / p)) = label x b i / p

instance (x b : ℕ) : Decidable (GoodGrid x b) := inferInstanceAs (Decidable (_ ∧ _))

def initTable (x b : ℕ) : Array (ℤ × ℤ) :=
  Array.ofFn (fun i : Fin (2*b) => initial (label x b i))

def nextTable (x b p : ℕ) (a : Array (ℤ × ℤ)) : Array (ℤ × ℤ) :=
  if p.Prime then
    overwrite a (active x b p) (fun i : ℕ =>
      let v := label x b i
      let old := a[i]!
      let lo := a[index x b (v/p)]!
      let base := a[index x b (p-1)]!
      (old.1 - (lo.1-base.1), old.2 - (p : ℤ)*(lo.2-base.2)))
  else a

def table (x b : ℕ) : ℕ → Array (ℤ × ℤ)
  | 0 => initTable x b
  | k+1 => nextTable x b (k+2) (table x b k)

def Correct (x b p : ℕ) (a : Array (ℤ × ℤ)) : Prop :=
  a.size = 2*b ∧ ∀ i : Fin (2*b), a[(i : ℕ)]! = stats p (label x b i)

lemma ofFn_get {n : ℕ} {α : Type} [Inhabited α] (f : Fin n → α) (i : Fin n) :
    (Array.ofFn f)[(i : ℕ)]! = f i := by
  rw [getElem!_pos _ _ (by simp only [Array.size_ofFn]; exact i.isLt)]
  simp

lemma init_correct {x b : ℕ} (hg : GoodGrid x b) :
    Correct x b 2 (initTable x b) := by
  refine ⟨by simp [initTable], ?_⟩
  intro i
  rw [initTable, ofFn_get]
  exact (stats_initial (hg.1 i)).symm

lemma next_correct {x b p : ℕ} {a : Array (ℤ × ℤ)}
    (hg : GoodGrid x b) (hxb : b*b ≤ x) (hp2 : 2 ≤ p) (hpb : p ≤ b)
    (ha : Correct x b p a) :
    Correct x b (p+1) (nextTable x b p a) := by
  by_cases hp : p.Prime
  · refine ⟨by simpa [nextTable, hp, overwrite_size] using ha.1, ?_⟩
    intro i
    rw [nextTable, if_pos hp, overwrite_get _ _ _ (by rw [ha.1]; exact active_le hp2)]
    dsimp
    split_ifs with hi
    · have hv := (active_iff hxb hp2 i.isLt).mp hi
      obtain ⟨hk, hkv, hlookup⟩ := hg.2 ⟨p, by omega⟩ hp2 hp
      obtain ⟨hj, hjv⟩ := hlookup ⟨i, hi⟩
      have hlo := ha.2 ⟨index x b (label x b i / p), hj⟩
      have hbase := ha.2 ⟨index x b (p-1), hk⟩
      rw [hjv] at hlo
      rw [hkv] at hbase
      rw [ha.2 i, hlo, hbase]
      exact (stats_step hp hv).symm
    · rw [ha.2 i]
      have hv : label x b i < p*p := by
        have := (active_iff hxb hp2 i.isLt).not.mp hi
        omega
      simp [stats, weighted, survivors_no_change (Or.inr hv)]
  · rcases ha with ⟨hs, ha⟩
    refine ⟨by simpa [nextTable, hp] using hs, ?_⟩
    intro i
    simp only [nextTable, if_neg hp, ha i]
    simp [stats, weighted, survivors_no_change (Or.inl hp)]

/-- The table computes the mathematical survivor counts and sums after every stage. -/
lemma table_correct {x b : ℕ} (hg : GoodGrid x b) (hxb : b*b ≤ x) :
    ∀ k, k+1 ≤ b → Correct x b (k+2) (table x b k) := by
  intro k
  induction k with
  | zero => intro _; exact init_correct hg
  | succ k ih =>
    intro hk
    exact next_correct hg hxb (by omega) (by omega) (ih (by omega))

def result (x b : ℕ) : ℤ × ℤ := (table x b (b-1))[0]!

/-- The final table gives the exact prime count and prime sum, with no conjectural input. -/
lemma result_correct {x b : ℕ} (hb : 1 ≤ b) (hg : GoodGrid x b) (hxb : b*b ≤ x)
    (hx : x < (b+1)*(b+1)) :
    result x b = (((Nat.primesLE x).card : ℤ), ∑ m ∈ Nat.primesLE x, (m : ℤ)) := by
  have ht := (table_correct hg hxb (b-1) (by omega)).2 ⟨0, by omega⟩
  have hk : b-1+2 = b+1 := by omega
  simp only [label, if_pos (by omega : 0 < b), zero_add, Nat.div_one, hk] at ht
  rw [result, ht]
  simp only [stats, weighted, survivors_final hx, sum_const, nsmul_eq_mul, mul_one]

/-- Reconcile a finite prime set with Mathlib's zero-based prime enumeration. -/
lemma primes_image (x : ℕ) :
    (range ((Nat.primesLE x).card)).image (Nat.nth Nat.Prime) = Nat.primesLE x := by
  have hc : (Nat.primesLE x).card = Nat.count Nat.Prime (x+1) := by
    rw [Nat.primesLE_card_eq_primeCounting, Nat.primeCounting, Nat.primeCounting']
  ext m
  rw [mem_image, Nat.mem_primesLE]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨by have := Nat.nth_lt_of_lt_count (hc ▸ mem_range.mp hi); omega,
      Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime i⟩
  · rintro ⟨hm, hp⟩
    refine ⟨Nat.count Nat.Prime m, ?_, Nat.nth_count hp⟩
    rw [mem_range, hc]
    exact Nat.count_strict_mono hp (by omega)

lemma prime_prefix_sum (x : ℕ) :
    (∑ i ∈ range ((Nat.primesLE x).card), (Nat.nth Nat.Prime i : ℤ)) =
      ∑ m ∈ Nat.primesLE x, (m : ℤ) := by
  calc
    _ = ∑ m ∈ (range ((Nat.primesLE x).card)).image (Nat.nth Nat.Prime), (m : ℤ) :=
      (sum_image (fun _ _ _ _ h => Nat.nth_injective Nat.infinite_setOfPred_prime h)).symm
    _ = _ := by rw [primes_image x]

-- The four finite, compiler-trusted checks used by the final theorem.
lemma lower_grid : GoodGrid 2274652150 47693 := by native_decide
lemma lower_result : result 2274652150 47693 = (111008770, 123000804558174777) := by
  native_decide

lemma upper_grid : GoodGrid 4711447171 68639 := by native_decide
lemma upper_result : result 4711447171 68639 = (222017542, 510024998640309373) := by
  native_decide

-- Convert the evaluated tables to statements about Mathlib's actual finite prime sets.
lemma lower_stats :
    (((Nat.primesLE 2274652150).card : ℤ), ∑ m ∈ Nat.primesLE 2274652150, (m : ℤ)) =
      (111008770, 123000804558174777) := by
  rw [← result_correct (by decide : 1 ≤ 47693) lower_grid (by decide) (by decide)]
  exact lower_result

lemma upper_stats :
    (((Nat.primesLE 4711447171).card : ℤ), ∑ m ∈ Nat.primesLE 4711447171, (m : ℤ)) =
      (222017542, 510024998640309373) := by
  rw [← result_correct (by decide : 1 ≤ 68639) upper_grid (by decide) (by decide)]
  exact upper_result

lemma lower_count : (Nat.primesLE 2274652150).card = 111008770 := by
  have h := congrArg (fun z : ℤ × ℤ => z.1) lower_stats
  change ((Nat.primesLE 2274652150).card : ℤ) = (111008770 : ℕ) at h
  exact Int.ofNat.inj h

lemma upper_count : (Nat.primesLE 4711447171).card = 222017542 := by
  have h := congrArg (fun z : ℤ × ℤ => z.1) upper_stats
  change ((Nat.primesLE 4711447171).card : ℤ) = (222017542 : ℕ) at h
  exact Int.ofNat.inj h

lemma lower_sum : (∑ m ∈ Nat.primesLE 2274652150, (m : ℤ)) = 123000804558174777 := by
  have h := congrArg (fun z : ℤ × ℤ => z.2) lower_stats
  dsimp only at h
  exact h

lemma upper_sum : (∑ m ∈ Nat.primesLE 4711447171, (m : ℤ)) = 510024998640309373 := by
  have h := congrArg (fun z : ℤ × ℤ => z.2) upper_stats
  dsimp only at h
  exact h

-- Endpoint primality is supplementary; the rank-based sum proof does not require it.
set_option maxRecDepth 100000 in
theorem endpoints_prime : Nat.Prime 2274652151 ∧ Nat.Prime 4711447171 := by norm_num

/-- The explicit square term, using the repository's exact definition of a. -/
theorem counterexample_value : OeisA105720.a 111008771 = 622112686 ^ 2 := by
  have hl := prime_prefix_sum 2274652150
  have hu := prime_prefix_sum 4711447171
  rw [lower_count, lower_sum] at hl
  rw [upper_count, upper_sum] at hu
  have h : (OeisA105720.a 111008771 : ℤ) = (622112686 : ℤ)^2 := by
    rw [OeisA105720.a, if_neg (by decide), Nat.cast_sum]
    rw [sum_Ico_eq_sub _ (by decide)]
    change (∑ i ∈ range 222017542, (Nat.nth Nat.Prime i : ℤ)) -
      (∑ i ∈ range 111008770, (Nat.nth Nat.Prime i : ℤ)) = _
    rw [hu, hl]
    norm_num
  have h' : (OeisA105720.a 111008771 : ℤ) = ((622112686 ^ 2 : ℕ) : ℤ) :=
    h.trans (by norm_num)
  exact Int.ofNat.inj h'

theorem counterexample_isSquare : IsSquare (OeisA105720.a 111008771) := by
  rw [counterexample_value]
  exact ⟨622112686, by ring⟩

/-- Negation of the complete proposition asserted by `OeisA105720.conjecture`. -/
theorem conjecture_false :
    ¬ (∀ n : ℕ, 0 < n → (IsSquare (OeisA105720.a n) ↔
      (n = 3 ∨ n = 6 ∨ n = 4072))) := by
  intro h
  have hc := (h 111008771 (by decide)).mp counterexample_isSquare
  norm_num at hc

#print axioms endpoints_prime
#print axioms counterexample_value
#print axioms conjecture_false

end A105720
