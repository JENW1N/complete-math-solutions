import Erdos354Definitions

/-!
# Erdős Problem 354(ii): the Formal Conjectures target

This file proves the affirmative answer to `Erdos354.erdos_354.parts.ii`.
The common base is the square root of the golden ratio.  In fact, one floor
sequence is already complete for every positive scale, so the second sequence
and the irrational-ratio hypothesis are not needed for this base.

Part (i), where the base is fixed to `2`, is not proved here.
-/

open Finset Filter
open scoped Topology goldenRatio

namespace Erdos354PartIIProof

/-- Representations with distinct indices drawn from a prescribed support. -/
def Rep (a : ℕ → ℤ) (s : Set ℕ) (z : ℤ) : Prop :=
  ∃ t : Finset ℕ, (∀ i ∈ t, i ∈ s) ∧ ∑ i ∈ t, a i = z

lemma rep_mono {a : ℕ → ℤ} {s t : Set ℕ} {z : ℤ}
    (h : s ⊆ t) (hz : Rep a s z) : Rep a t z := by
  obtain ⟨u, hu, rfl⟩ := hz
  exact ⟨u, fun i hi ↦ h (hu i hi), rfl⟩

/-- A sequence whose successive terms at most double has bounded deficit. -/
lemma deficit_bound (b : ℕ → ℤ) (h : ∀ n, b (n + 1) ≤ 2 * b n) :
    ∀ n, b n ≤ b 0 + ∑ i ∈ range n, b i := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    have := h n
    omega

/-- Adding a sequence with bounded deficit extends an already represented interval. -/
lemma extend_interval (a : ℕ → ℤ) (c : Set ℕ) (b : ℕ → ℕ)
    (hb : Function.Injective b) (hbc : ∀ n, b n ∉ c) (L D : ℤ)
    (hinit : ∀ z, L ≤ z → z ≤ L + D → Rep a c z)
    (hgap : ∀ n, a (b n) ≤ D + 1 + ∑ j ∈ range n, a (b j)) :
    ∀ n z, L ≤ z → z ≤ L + D + ∑ j ∈ range n, a (b j) →
      Rep a (c ∪ b '' Set.Iio n) z := by
  classical
  intro n
  induction n with
  | zero =>
    intro z hz hz'
    simpa using hinit z hz (by simpa using hz')
  | succ n ih =>
    intro z hz hz'
    have hsub : c ∪ b '' Set.Iio n ⊆ c ∪ b '' Set.Iio (n + 1) := by
      intro i hi
      rcases hi with hi | ⟨j, hj, rfl⟩
      · exact Or.inl hi
      · exact Or.inr ⟨j, by simp only [Set.mem_Iio] at *; omega, rfl⟩
    by_cases hold : z ≤ L + D + ∑ j ∈ range n, a (b j)
    · exact rep_mono hsub (ih z hz hold)
    · have hlow : L ≤ z - a (b n) := by
        have := hgap n
        omega
      have hhigh : z - a (b n) ≤ L + D + ∑ j ∈ range n, a (b j) := by
        rw [sum_range_succ] at hz'
        omega
      obtain ⟨u, hu, hsum⟩ := ih (z - a (b n)) hlow hhigh
      have hn : b n ∉ u := by
        intro hn
        rcases hu _ hn with hn | ⟨j, hj, heq⟩
        · exact hbc n hn
        · have := hb heq
          simp only [Set.mem_Iio] at hj
          omega
      refine ⟨insert (b n) u, ?_, ?_⟩
      · intro i hi
        rcases mem_insert.mp hi with rfl | hi
        · exact Or.inr ⟨n, by simp, rfl⟩
        · exact hsub (hu i hi)
      · rw [sum_insert hn, hsum]
        omega

/-- The interval extension covers every integer above its starting point. -/
lemma complete_of_interval (a : ℕ → ℤ) (c : Set ℕ) (b : ℕ → ℕ)
    (hb : Function.Injective b) (hbc : ∀ n, b n ∉ c)
    (hpos : ∀ n, 1 ≤ a (b n)) (L D : ℤ) (hD : 0 ≤ D)
    (hinit : ∀ z, L ≤ z → z ≤ L + D → Rep a c z)
    (hgap : ∀ n, a (b n) ≤ D + 1 + ∑ j ∈ range n, a (b j)) :
    ∀ z ≥ L, ∃ t : Finset ℕ, ∑ i ∈ t, a i = z := by
  intro z hz
  obtain ⟨n, hn⟩ := exists_nat_ge (z - L)
  have hsum : (n : ℤ) ≤ ∑ j ∈ range n, a (b j) := by
    simpa using sum_le_sum (fun j (_ : j ∈ range n) ↦ hpos j)
  have hupper : z ≤ L + D + ∑ j ∈ range n, a (b j) := by
    calc
      z ≤ L + (n : ℤ) := by omega
      _ ≤ L + ∑ j ∈ range n, a (b j) := by
        simpa [add_comm] using add_le_add_left hsum L
      _ ≤ L + D + ∑ j ∈ range n, a (b j) := by omega
  obtain ⟨t, _, ht⟩ := extend_interval a c b hb hbc L D hinit hgap n z hz hupper
  exact ⟨t, ht⟩

/-- Arbitrarily late carry-one triples generate intervals of any finite length. -/
lemma intervals_of_carries (a : ℕ → ℤ)
    (h : ∀ N, ∃ n ≥ N, a (n + 2) = a n + a (n + 1) + 1) :
    ∀ D : ℕ, ∃ K : ℕ, ∃ L : ℤ, ∀ z : ℤ, L ≤ z → z ≤ L + D →
      ∃ t : Finset ℕ, t ⊆ range K ∧ ∑ i ∈ t, a i = z := by
  classical
  intro D
  induction D with
  | zero =>
    refine ⟨0, 0, ?_⟩
    intro z hz hz'
    have : z = 0 := by omega
    subst z
    exact ⟨∅, by simp, by simp⟩
  | succ D ih =>
    obtain ⟨K, L, ih⟩ := ih
    obtain ⟨n, hn, heq⟩ := h K
    refine ⟨n + 3, L + a n + a (n + 1), ?_⟩
    intro z hz hz'
    by_cases hold : z ≤ L + a n + a (n + 1) + D
    · obtain ⟨t, ht, hsum⟩ := ih (z - a n - a (n + 1)) (by omega) (by omega)
      have hnot : n ∉ t := fun hi ↦ by
        have := mem_range.mp (ht hi)
        omega
      have hnot' : n + 1 ∉ t := fun hi ↦ by
        have := mem_range.mp (ht hi)
        omega
      refine ⟨insert n (insert (n + 1) t), ?_, ?_⟩
      · intro i hi
        simp only [mem_insert] at hi
        rcases hi with rfl | rfl | hi
        · simp
        · simp
        · have := mem_range.mp (ht hi)
          simp only [mem_range]
          omega
      · rw [sum_insert (by simp [hnot]), sum_insert hnot', hsum]
        omega
    · obtain ⟨t, ht, hsum⟩ := ih (z - a (n + 2)) (by omega) (by omega)
      have hnot : n + 2 ∉ t := fun hi ↦ by
        have := mem_range.mp (ht hi)
        omega
      refine ⟨insert (n + 2) t, ?_, ?_⟩
      · intro i hi
        rcases mem_insert.mp hi with rfl | hi
        · simp
        · have := mem_range.mp (ht hi)
          simp only [mem_range]
          omega
      · rw [sum_insert hnot, hsum]
        omega

/-- A bounded nonnegative Fibonacci-type recurrence has zero second term. -/
lemma bounded_fib_second_zero (f : ℕ → ℝ) (h0 : ∀ n, 0 ≤ f n)
    (h1 : ∀ n, f n < 1) (hr : ∀ n, f (n + 2) = f n + f (n + 1)) : f 1 = 0 := by
  have hm : Monotone (fun n ↦ f (n + 1)) := by
    apply monotone_nat_of_le_succ
    intro n
    have := hr n
    have := h0 n
    linarith
  have hl : ∀ n : ℕ, (n : ℝ) * f 1 ≤ f (n + 2) := by
    intro n
    induction n with
    | zero => simpa using h0 2
    | succ n ih =>
      have ht : f 1 ≤ f (n + 1) := by simpa using hm (Nat.zero_le n)
      have he := hr (n + 1)
      push_cast
      nlinarith
  apply le_antisymm _ (h0 1)
  by_contra! hpos
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / f 1)
  have hn' : 1 < (n : ℝ) * f 1 := (div_lt_iff₀ hpos).mp hn
  have := hl n
  have := h1 (n + 2)
  linarith

/-- A bounded nonnegative Fibonacci-type recurrence is identically zero. -/
lemma bounded_fib_zero (f : ℕ → ℝ) (h0 : ∀ n, 0 ≤ f n)
    (h1 : ∀ n, f n < 1) (hr : ∀ n, f (n + 2) = f n + f (n + 1)) :
    ∀ n, f n = 0 := by
  have hs : ∀ n, f (n + 1) = 0 := by
    intro n
    exact bounded_fib_second_zero (fun j ↦ f (n + j)) (fun j ↦ h0 _) (fun j ↦ h1 _)
      (fun j ↦ by simpa [Nat.add_assoc] using hr (n + j))
  intro n
  cases n with
  | zero =>
    have := hr 0
    have := hs 0
    have := hs 1
    norm_num at *
    linarith
  | succ n => exact hs n

noncomputable def goldenFloor (u : ℝ) (n : ℕ) : ℤ := ⌊u * φ ^ n⌋

lemma real_recurrence (u : ℝ) (n : ℕ) :
    u * φ ^ (n + 2) = u * φ ^ n + u * φ ^ (n + 1) := by
  rw [pow_add, Real.goldenRatio_sq, pow_succ]
  ring

lemma floor_recurrence (u : ℝ) (n : ℕ) :
    goldenFloor u (n + 2) = goldenFloor u n + goldenFloor u (n + 1) ∨
    goldenFloor u (n + 2) = goldenFloor u n + goldenFloor u (n + 1) + 1 := by
  have hr := real_recurrence u n
  have h0 := Int.floor_le (u * φ ^ n)
  have h1 := Int.floor_le (u * φ ^ (n + 1))
  have h2 := Int.floor_le (u * φ ^ (n + 2))
  have h0' := Int.lt_floor_add_one (u * φ ^ n)
  have h1' := Int.lt_floor_add_one (u * φ ^ (n + 1))
  have h2' := Int.lt_floor_add_one (u * φ ^ (n + 2))
  have hl : goldenFloor u n + goldenFloor u (n + 1) ≤ goldenFloor u (n + 2) := by
    unfold goldenFloor
    have hh : (⌊u * φ ^ n⌋ : ℤ) + ⌊u * φ ^ (n + 1)⌋ < ⌊u * φ ^ (n + 2)⌋ + 1 := by
      exact_mod_cast (show (⌊u * φ ^ n⌋ : ℝ) + ⌊u * φ ^ (n + 1)⌋ <
        (⌊u * φ ^ (n + 2)⌋ : ℝ) + 1 by linarith)
    omega
  have hu : goldenFloor u (n + 2) < goldenFloor u n + goldenFloor u (n + 1) + 2 := by
    unfold goldenFloor
    exact_mod_cast (show (⌊u * φ ^ (n + 2)⌋ : ℝ) <
      (⌊u * φ ^ n⌋ : ℝ) + ⌊u * φ ^ (n + 1)⌋ + 2 by linarith)
  omega

/-- The carry-one alternative occurs arbitrarily far out. -/
lemma late_carries (u : ℝ) (hu : 0 < u) :
    ∀ N, ∃ n ≥ N,
      goldenFloor u (n + 2) = goldenFloor u n + goldenFloor u (n + 1) + 1 := by
  intro N
  by_contra! h
  have hr : ∀ n, N ≤ n →
      goldenFloor u (n + 2) = goldenFloor u n + goldenFloor u (n + 1) := by
    intro n hn
    exact (floor_recurrence u n).resolve_right (h n hn)
  let f : ℕ → ℝ := fun j ↦ u * φ ^ (N + j) - (goldenFloor u (N + j) : ℝ)
  have hf0 : ∀ j, 0 ≤ f j := fun j ↦ sub_nonneg.mpr (Int.floor_le _)
  have hf1 : ∀ j, f j < 1 := fun j ↦ Int.fract_lt_one _
  have hfr : ∀ j, f (j + 2) = f j + f (j + 1) := by
    intro j
    have hreal := real_recurrence u (N + j)
    have hint := hr (N + j) (by omega)
    have hc : (goldenFloor u (N + j + 2) : ℝ) =
        goldenFloor u (N + j) + goldenFloor u (N + j + 1) := by
      exact_mod_cast hint
    dsimp [f]
    simp only [← Nat.add_assoc]
    linarith
  have hz := bounded_fib_zero f hf0 hf1 hfr
  have hzero : u * φ ^ N = (goldenFloor u N : ℝ) := by
    have := hz 0
    dsimp [f] at this
    simpa using sub_eq_zero.mp this
  have hone : u * φ ^ (N + 1) = (goldenFloor u (N + 1) : ℝ) := by
    have := hz 1
    exact sub_eq_zero.mp this
  have hne : (goldenFloor u N : ℝ) ≠ 0 := by
    rw [← hzero]
    positivity
  apply Real.goldenRatio_irrational.ne_rational (goldenFloor u (N + 1)) (goldenFloor u N)
  apply (eq_div_iff hne).mpr
  rw [← hzero, ← hone, pow_succ]
  ring

/-- A positive golden-ratio floor sequence eventually has positive terms
and successive terms at most double. -/
lemma floor_tail (u : ℝ) (hu : 0 < u) :
    ∃ K : ℕ, ∀ n ≥ K,
      1 ≤ goldenFloor u n ∧ goldenFloor u (n + 1) ≤ 2 * goldenFloor u n := by
  have ht : Tendsto (fun n : ℕ ↦ u * φ ^ n) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt Real.one_lt_goldenRatio).const_mul_atTop hu
  have hd : 0 < 2 - φ := sub_pos.mpr Real.goldenRatio_lt_two
  obtain ⟨K, hK⟩ := eventually_atTop.mp
    ((ht.eventually_ge_atTop 1).and (ht.eventually_ge_atTop (2 / (2 - φ))))
  refine ⟨K, ?_⟩
  intro n hn
  obtain ⟨hlo, hbig⟩ := hK n hn
  refine ⟨Int.le_floor.mpr (by simpa using hlo), ?_⟩
  have hmul : 2 ≤ u * φ ^ n * (2 - φ) := (div_le_iff₀ hd).mp hbig
  have hb := Int.lt_floor_add_one (u * φ ^ n)
  have hnxt := Int.floor_le (u * φ ^ (n + 1))
  rw [pow_succ] at hnxt
  have hh : (goldenFloor u (n + 1) : ℝ) ≤ 2 * (goldenFloor u n : ℝ) := by
    unfold goldenFloor
    rw [pow_succ]
    nlinarith
  exact_mod_cast hh

/-- The common base used in the proof. -/
noncomputable def gamma : ℝ := Real.sqrt φ

lemma gamma_sq : gamma ^ 2 = φ := Real.sq_sqrt Real.goldenRatio_pos.le

lemma gamma_bounds : 1 < gamma ∧ gamma < 2 := by
  constructor
  · exact (Real.lt_sqrt (by norm_num)).mpr (by simpa using Real.one_lt_goldenRatio)
  · exact (Real.sqrt_lt' (by norm_num)).mpr (by
      have := Real.goldenRatio_lt_two
      norm_num
      linarith)

lemma floor_even (u : ℝ) (n : ℕ) : ⌊gamma ^ (2 * n) * u⌋ = goldenFloor u n := by
  rw [pow_mul, gamma_sq, mul_comm]
  rfl

lemma floor_odd (u : ℝ) (n : ℕ) :
    ⌊gamma ^ (2 * n + 1) * u⌋ = goldenFloor (u * gamma) n := by
  unfold goldenFloor
  congr 1
  rw [pow_add, pow_mul, gamma_sq, pow_one]
  ring

/-- For every positive scale, one square-root-golden-ratio floor sequence is complete. -/
theorem single_complete (u : ℝ) (hu : 0 < u) :
    ∃ L : ℤ, ∀ z ≥ L, ∃ t : Finset ℕ, ∑ i ∈ t, ⌊gamma ^ i * u⌋ = z := by
  classical
  have hg : 0 < gamma := lt_trans zero_lt_one gamma_bounds.1
  obtain ⟨K, hK⟩ := floor_tail (u * gamma) (mul_pos hu hg)
  let b : ℕ → ℕ := fun n ↦ 2 * (K + n) + 1
  let a : ℕ → ℤ := fun n ↦ ⌊gamma ^ n * u⌋
  let c : Set ℕ := {n | n % 2 = 0}
  let D : ℕ := (goldenFloor (u * gamma) K).toNat
  have hpos : ∀ n, 1 ≤ a (b n) := by
    intro n
    dsimp [a, b]
    rw [floor_odd]
    exact (hK (K + n) (by omega)).1
  have hD : (D : ℤ) = goldenFloor (u * gamma) K :=
    Int.toNat_of_nonneg (le_trans (by norm_num) (hK K le_rfl).1)
  obtain ⟨M, L, hL⟩ := intervals_of_carries (goldenFloor u) (late_carries u hu) D
  have hinit : ∀ z, L ≤ z → z ≤ L + (D : ℤ) → Rep a c z := by
    intro z hz hz'
    obtain ⟨t, _, ht⟩ := hL z hz hz'
    refine ⟨t.image (fun n ↦ 2 * n), ?_, ?_⟩
    · intro i hi
      obtain ⟨j, _, rfl⟩ := mem_image.mp hi
      simp [c]
    · rw [sum_image (by intro i _ j _ h; dsimp at h; omega)]
      simpa only [a, floor_even] using ht
  have hgap : ∀ n, a (b n) ≤ (D : ℤ) + 1 + ∑ j ∈ range n, a (b j) := by
    intro n
    have hr : ∀ j,
        goldenFloor (u * gamma) (K + (j + 1)) ≤ 2 * goldenFloor (u * gamma) (K + j) := by
      intro j
      simpa [Nat.add_assoc] using (hK (K + j) (by omega)).2
    have hd := deficit_bound (fun j ↦ goldenFloor (u * gamma) (K + j)) hr n
    dsimp [a, b]
    simp only [floor_odd, hD]
    simp only [Nat.add_zero] at hd
    omega
  refine ⟨L, complete_of_interval a c b ?_ ?_ hpos L D (by positivity) hinit hgap⟩
  · intro i j hij
    dsimp [b] at hij
    omega
  · intro n
    simp [b, c]

/-- Exact affirmative answer to the Formal Conjectures target
`Erdos354.erdos_354.parts.ii`. -/
theorem erdos_354_part_ii_solved : True ↔
    ∃ γ ∈ Set.Ioo (1 : ℝ) 2, ∀ᵉ (α > 0) (β > 0), Irrational (α / β) →
      IsAddCompleteNatSeq' (Erdos354.FloorMultiples.interleave α β γ) := by
  constructor
  · intro _
    refine ⟨gamma, gamma_bounds, ?_⟩
    intro α hα β _ _
    obtain ⟨L, hL⟩ := single_complete α hα
    unfold IsAddCompleteNatSeq' subseqSums'
    apply eventually_atTop.mpr
    refine ⟨L, ?_⟩
    intro z hz
    obtain ⟨t, ht⟩ := hL z hz
    classical
    refine ⟨t.image (fun n ↦ 2 * n), ?_⟩
    rw [sum_image (by intro i _ j _ hij; dsimp at hij; omega)]
    simpa [Erdos354.FloorMultiples.interleave, Erdos354.FloorMultiples] using ht.symm
  · intro _
    trivial

#print axioms erdos_354_part_ii_solved
#print axioms single_complete

end Erdos354PartIIProof
