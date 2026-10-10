/-
Erdos 272: the Szabo strong variant.

The final theorem is Bounty.target, with exactly the task's requested type.
All combinatorial reductions used in the proof are proved below.

Proof outline: private witnesses and progression matching give the bound for
common-point families and for families with a long common interval core.
Trace counts give a common point for the crooked members after a linear loss.
Straddling estimates and one-sided endpoint stability then give the required
long-core structure. The lower construction and upper bound yield the big-O
statement.

Pinned environment: Lean 4.33.1; FormalConjectures
8432eac998110a563e03df65a28c117e97c8c142; Mathlib
0df444a360eaa60ab8c11dca51a86af692955474.
-/


section
open Finset Filter Asymptotics

theorem arithInterSet_empty (N : ℕ) : Erdos272.IsArithInterSet N ∅ := by
  simp [Erdos272.IsArithInterSet]

theorem admissible_card_le_pow {N : ℕ} {A : Finset (Finset ℕ)}
    (hA : Erdos272.IsArithInterSet N A) : A.card ≤ 2 ^ N := by
  have h := Finset.card_le_card hA.1
  simpa using h

theorem admissible_cards_nonempty (N : ℕ) :
    {m : ℕ | ∃ A : Finset (Finset ℕ), ∃ (_ : Erdos272.IsArithInterSet N A), A.card = m}.Nonempty := by
  exact ⟨0, ∅, arithInterSet_empty N, rfl⟩

theorem admissible_cards_bddAbove (N : ℕ) :
    BddAbove {m : ℕ | ∃ A : Finset (Finset ℕ),
      ∃ (_ : Erdos272.IsArithInterSet N A), A.card = m} := by
  refine ⟨2 ^ N, ?_⟩
  rintro m ⟨A, hA, rfl⟩
  exact admissible_card_le_pow hA

theorem card_le_max {N : ℕ} {A : Finset (Finset ℕ)}
    (hA : Erdos272.IsArithInterSet N A) : A.card ≤ Erdos272.maxArithInterCard N := by
  exact le_csSup (admissible_cards_bddAbove N) ⟨A, hA, rfl⟩

theorem max_is_attained (N : ℕ) :
    ∃ A : Finset (Finset ℕ), Erdos272.IsArithInterSet N A ∧
      A.card = Erdos272.maxArithInterCard N := by
  obtain ⟨A, hA, heq⟩ := Nat.sSup_mem
    (admissible_cards_nonempty N) (admissible_cards_bddAbove N)
  exact ⟨A, hA, heq⟩

theorem nonempty_small_isAP {s : Finset ℕ} (hs : s.Nonempty) (hcard : s.card ≤ 2) :
    ∃ l > 0, (s : Set ℕ).IsAPOfLength l := by
  have hpos := Finset.card_pos.mpr hs
  by_cases h : s.card = 1
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h
    exact ⟨1, by norm_num, Set.IsAPOfLength.one.mpr ⟨a, by simp⟩⟩
  · have htwo : s.card = 2 := by omega
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp htwo
    refine ⟨2, by norm_num, ?_⟩
    rw [Finset.coe_pair]
    rcases lt_or_gt_of_ne hab with hab | hba
    · exact Nat.isAPOfLength_pair hab
    · rw [Set.pair_comm]
      exact Nat.isAPOfLength_pair hba

theorem small_star_admissible {N c : ℕ} {A : Finset (Finset ℕ)}
    (hsub : A ⊆ (Finset.Icc 1 N).powerset)
    (hc : ∀ s ∈ A, c ∈ s)
    (hsize : ∀ s ∈ A, s.card ≤ 3) : Erdos272.IsArithInterSet N A := by
  refine ⟨hsub, ?_⟩
  intro s hs t ht hst
  apply nonempty_small_isAP ⟨c, Finset.mem_inter.mpr ⟨hc s hs, hc t ht⟩⟩
  by_contra h
  have hthree : 3 ≤ (s ∩ t).card := by omega
  have heqs : s ∩ t = s := Finset.eq_of_subset_of_card_le
    Finset.inter_subset_left ((hsize s hs).trans hthree)
  have heqt : s ∩ t = t := Finset.eq_of_subset_of_card_le
    Finset.inter_subset_right ((hsize t ht).trans hthree)
  exact hst (heqs.symm.trans heqt)

theorem insert_injective_fixed_card {α : Type*} [DecidableEq α]
    {c : α} {s t : Finset α} (hcard : s.card = t.card)
    (h : insert c s = insert c t) : s = t := by
  by_cases hs : c ∈ s
  · have ht : c ∈ t := by
      by_contra ht
      have hh := congrArg Finset.card h
      simp [Finset.insert_eq_of_mem hs, Finset.card_insert_of_notMem ht] at hh
      omega
    simpa [Finset.insert_eq_of_mem hs, Finset.insert_eq_of_mem ht] using h
  · have ht : c ∉ t := by
      intro ht
      have hh := congrArg Finset.card h
      simp [Finset.insert_eq_of_mem ht, Finset.card_insert_of_notMem hs] at hh
      omega
    apply Finset.ext
    intro x
    have hh := Finset.ext_iff.mp h x
    by_cases hx : x = c
    · subst x
      simp [hs, ht]
    · simpa [hx] using hh

/-- Pairs in `[1,N]`, enlarged to contain 1, together with the singleton `{1}`. -/
def lowerFamily (N : ℕ) : Finset (Finset ℕ) :=
  insert {1} (((Finset.Icc 1 N).powersetCard 2).image (insert 1))

theorem lowerFamily_admissible {N : ℕ} (hN : 1 ≤ N) :
    Erdos272.IsArithInterSet N (lowerFamily N) := by
  apply small_star_admissible (c := 1)
  · intro s hs
    rcases Finset.mem_insert.mp hs with rfl | hs
    · simp [hN]
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
      exact Finset.mem_powerset.mpr (Finset.insert_subset
        (Finset.mem_Icc.mpr ⟨le_rfl, hN⟩) (Finset.mem_powersetCard.mp ht).1)
  · intro s hs
    rcases Finset.mem_insert.mp hs with rfl | hs
    · simp
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
      simp
  · intro s hs
    rcases Finset.mem_insert.mp hs with rfl | hs
    · simp
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
      have hh := Finset.card_insert_le 1 t
      rw [(Finset.mem_powersetCard.mp ht).2] at hh
      exact hh

theorem card_lowerFamily (N : ℕ) : (lowerFamily N).card = N.choose 2 + 1 := by
  have hinj : Set.InjOn (insert 1)
      (((Finset.Icc 1 N).powersetCard 2) : Set (Finset ℕ)) := by
    intro s hs t ht heq
    exact insert_injective_fixed_card
      ((Finset.mem_powersetCard.mp hs).2.trans (Finset.mem_powersetCard.mp ht).2.symm) heq
  have hnot : {1} ∉ (((Finset.Icc 1 N).powersetCard 2).image (insert 1)) := by
    intro h
    obtain ⟨s, hs, heq⟩ := Finset.mem_image.mp h
    have hh : s.card ≤ ({1} : Finset ℕ).card := by
      rw [← heq]
      exact Finset.card_le_card (Finset.subset_insert 1 s)
    simp [(Finset.mem_powersetCard.mp hs).2] at hh
  rw [lowerFamily, Finset.card_insert_of_notMem hnot,
    Finset.card_image_of_injOn hinj, Finset.card_powersetCard]
  simp

theorem lower_bound {N : ℕ} (hN : 1 ≤ N) :
    N.choose 2 + 1 ≤ Erdos272.maxArithInterCard N := by
  rw [← card_lowerFamily]
  exact card_le_max (lowerFamily_admissible hN)

theorem lower_bound_real {N : ℕ} (hN : 1 ≤ N) :
    (N : ℝ)^2 / 2 - (N : ℝ) / 2 + 1 ≤ (Erdos272.maxArithInterCard N : ℝ) := by
  have h : ((N.choose 2 + 1 : ℕ) : ℝ) ≤ (Erdos272.maxArithInterCard N : ℝ) :=
    Nat.cast_le.mpr (lower_bound hN)
  rw [Nat.cast_add, Nat.cast_one, Nat.cast_choose_two] at h
  nlinarith

/-- The finite upper bound still required to finish the proposed proof. -/
def FiniteUpperBound : Prop :=
  ∃ C : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ A : Finset (Finset ℕ), Erdos272.IsArithInterSet N A →
      (A.card : ℝ) ≤ (N : ℝ)^2 / 2 + C * (N : ℝ)

/-- A conditional reduction, not a proof of the requested unconditional theorem. -/
theorem target_of_finite_upper_bound (hupper : FiniteUpperBound) :
    fcTypeOfName% "Erdos272.erdos_272.variants.szabo_strong" := by
  rcases hupper with ⟨C, N₀, hupper⟩
  refine Asymptotics.IsBigO.of_bound (max |C| 1) ?_
  filter_upwards [Filter.eventually_ge_atTop (max N₀ 1)] with N hN
  have hN₀ : N₀ ≤ N := (le_max_left _ _).trans hN
  have hN₁ : 1 ≤ N := (le_max_right _ _).trans hN
  obtain ⟨A, hA, hcard⟩ := max_is_attained N
  have hupperN := hupper N hN₀ A hA
  rw [hcard] at hupperN
  have hlowerN := lower_bound_real hN₁
  have hC : C ≤ max |C| 1 := (le_abs_self C).trans (le_max_left _ _)
  have hone : (1 : ℝ) ≤ max |C| 1 := le_max_right _ _
  have hNnonneg : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  simp only [Real.norm_eq_abs, abs_of_nonneg hNnonneg]
  refine abs_le.mpr ⟨?_, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_right hone hNnonneg]
  · nlinarith [mul_le_mul_of_nonneg_right hC hNnonneg]

theorem finite_upper_bound_of_target
    (h : fcTypeOfName% "Erdos272.erdos_272.variants.szabo_strong") :
    FiniteUpperBound := by
  obtain ⟨C, hC⟩ := Asymptotics.isBigO_iff.mp h
  obtain ⟨N₀, hC⟩ := Filter.eventually_atTop.mp hC
  refine ⟨C, N₀, ?_⟩
  intro N hN A hA
  have hbound := hC N hN
  have hNnonneg : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  simp only [Real.norm_eq_abs, abs_of_nonneg hNnonneg] at hbound
  have hu := (abs_le.mp hbound).2
  have hcard : (A.card : ℝ) ≤ (Erdos272.maxArithInterCard N : ℝ) :=
    Nat.cast_le.mpr (card_le_max hA)
  linarith

theorem target_iff_finite_upper_bound :
    (fcTypeOfName% "Erdos272.erdos_272.variants.szabo_strong") ↔ FiniteUpperBound :=
  ⟨finite_upper_bound_of_target, target_of_finite_upper_bound⟩

end
section
open Finset

theorem range_image_isAP (a d k : ℕ) (hd : 0 < d) :
    (((Finset.range k).image (fun i => a + i * d) : Finset ℕ) : Set ℕ).IsAPOfLength k := by
  refine ⟨a, d, ?_, ?_⟩
  · have hinj : Function.Injective (fun i : ℕ => a + i * d) := by
      intro i j hij
      nlinarith
    simp [Finset.card_image_of_injective _ hinj]
  · ext x
    simp

theorem multiples_isAP {d M : ℕ} (hd : 0 < d) :
    (((Finset.Icc 0 M).filter (fun x => d ∣ x) : Finset ℕ) : Set ℕ).IsAPOfLength
      (↑(M / d + 1 : ℕ)) := by
  have heq : (Finset.Icc 0 M).filter (fun x => d ∣ x) =
      (Finset.range (M / d + 1)).image (fun i => 0 + i * d) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.zero_le, true_and,
      Finset.mem_image, Finset.mem_range, zero_add]
    constructor
    · rintro ⟨hx, hdvd⟩
      refine ⟨x / d, ?_, Nat.div_mul_cancel hdvd⟩
      exact Nat.lt_succ_of_le ((Nat.le_div_iff_mul_le hd).mpr
        (by simpa [Nat.div_mul_cancel hdvd] using hx))
    · rintro ⟨i, hi, rfl⟩
      exact ⟨(Nat.le_div_iff_mul_le hd).mp (Nat.le_of_lt_succ hi), dvd_mul_left d i⟩
  rw [heq]
  exact range_image_isAP 0 d (M / d + 1) hd

/-- The arithmetic hull of `0,a,b`, expressed by divisibility and an interval. -/
def hullZero (a b : ℕ) : Finset ℕ :=
  (Finset.Icc 0 (max a b)).filter (fun x => a.gcd b ∣ x)

theorem gcd_mem_hullZero {a : ℕ} (b : ℕ) (ha : 0 < a) : a.gcd b ∈ hullZero a b := by
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
    ⟨Nat.zero_le _, (Nat.gcd_le_left b ha).trans (le_max_left _ _)⟩, dvd_rfl⟩

/-- Closure under the hulls from a closest positive point forces a progression. -/
theorem hullZero_closed_isAP {s : Finset ℕ} {a : ℕ}
    (ha : a ∈ s) (hapos : 0 < a)
    (hmin : ∀ b ∈ s, 0 < b → a ≤ b)
    (hclosed : ∀ b ∈ s, hullZero a b ⊆ s) :
    ∃ l > 0, (s : Set ℕ).IsAPOfLength l := by
  have hne : s.Nonempty := ⟨a, ha⟩
  have hdvd : ∀ b ∈ s, a ∣ b := by
    intro b hb
    have hgmem : a.gcd b ∈ s := hclosed b hb (gcd_mem_hullZero b hapos)
    have hgpos : 0 < a.gcd b := Nat.gcd_pos_of_pos_left b hapos
    have heq : a.gcd b = a := le_antisymm (Nat.gcd_le_left b hapos)
      (hmin _ hgmem hgpos)
    rw [← heq]
    exact Nat.gcd_dvd_right a b
  let M := s.max' hne
  have hMmem : M ∈ s := Finset.max'_mem s hne
  have hgcd : a.gcd M = a := Nat.gcd_eq_left_iff_dvd.mpr (hdvd M hMmem)
  have heq : s = (Finset.Icc 0 M).filter (fun x => a ∣ x) := by
    apply Finset.Subset.antisymm
    · intro x hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
        ⟨Nat.zero_le _, Finset.le_max' s x hx⟩, hdvd x hx⟩
    · intro x hx
      apply hclosed M hMmem
      have haM : a ≤ M := Finset.le_max' s a ha
      simpa [hullZero, max_eq_right haM, hgcd] using hx
  refine ⟨(M / a + 1 : ℕ), by positivity, ?_⟩
  rw [heq]
  exact multiples_isAP hapos

/-- A non-progression has a failed gcd hull from every closest positive point. -/
theorem closest_positive_witness {s : Finset ℕ} {a : ℕ}
    (ha : a ∈ s) (hapos : 0 < a)
    (hmin : ∀ b ∈ s, 0 < b → a ≤ b)
    (hcrooked : ¬ ∃ l > 0, (s : Set ℕ).IsAPOfLength l) :
    ∃ b ∈ s, ¬ hullZero a b ⊆ s := by
  by_contra h
  push Not at h
  exact hcrooked (hullZero_closed_isAP ha hapos hmin h)

theorem finset_ap_representation {s : Finset ℕ} {l : ℕ∞}
    (h : (s : Set ℕ).IsAPOfLength l) :
    ∃ a d : ℕ, ∀ x : ℕ, x ∈ s ↔ ∃ i < s.card, a + i * d = x := by
  have hl : (s.card : ℕ∞) = l := by simpa using h.card
  obtain ⟨a, d, heq⟩ := h.eq
  refine ⟨a, d, ?_⟩
  intro x
  change x ∈ (s : Set ℕ) ↔ _
  rw [heq]
  simp [← hl]

/-- A progression containing the three points contains their gcd hull. -/
theorem hullZero_subset_of_isAP {s : Finset ℕ} {l : ℕ∞} {u v : ℕ}
    (hAP : (s : Set ℕ).IsAPOfLength l)
    (hzero : 0 ∈ s) (hu : u ∈ s) (hv : v ∈ s) (hupos : 0 < u) :
    hullZero u v ⊆ s := by
  obtain ⟨a, d, hrep⟩ := finset_ap_representation hAP
  obtain ⟨i₀, hi₀, h₀⟩ := (hrep 0).mp hzero
  have ha : a = 0 := by omega
  subst a
  obtain ⟨i, hi, hui⟩ := (hrep u).mp hu
  obtain ⟨j, hj, hvj⟩ := (hrep v).mp hv
  simp only [zero_add] at hui hvj hrep
  have hd : 0 < d := by nlinarith
  have hdu : d ∣ u := by rw [← hui]; exact dvd_mul_left d i
  have hdv : d ∣ v := by rw [← hvj]; exact dvd_mul_left d j
  intro x hx
  obtain ⟨hxrange, hxdiv⟩ := Finset.mem_filter.mp hx
  have hxmax : x ≤ max u v := (Finset.mem_Icc.mp hxrange).2
  have hdx : d ∣ x := (Nat.dvd_gcd hdu hdv).trans hxdiv
  have hdivmul : x / d * d = x := Nat.div_mul_cancel hdx
  have humax : u ≤ max i j * d := by nlinarith [le_max_left i j]
  have hvmax : v ≤ max i j * d := by nlinarith [le_max_right i j]
  have hxbound : x ≤ max i j * d := hxmax.trans (max_le humax hvmax)
  have hindex : x / d ≤ max i j :=
    Nat.le_of_mul_le_mul_right (by simpa [hdivmul] using hxbound) hd
  exact (hrep x).mpr ⟨x / d, hindex.trans_lt (max_lt_iff.mpr ⟨hi, hj⟩), hdivmul⟩

/-- A failed hull is private among progression-intersecting sets containing zero. -/
theorem hullZero_witness_private {F : Finset (Finset ℕ)}
    (hF : (F : Set (Finset ℕ)).Pairwise fun s t =>
      ∃ l > 0, ((s ∩ t : Finset ℕ) : Set ℕ).IsAPOfLength l)
    (hzero : ∀ s ∈ F, 0 ∈ s)
    {s t : Finset ℕ} (hs : s ∈ F) (ht : t ∈ F) {a b : ℕ}
    (ha : a ∈ s) (hb : b ∈ s) (hapos : 0 < a)
    (hfail : ¬ hullZero a b ⊆ s) (hat : a ∈ t) (hbt : b ∈ t) : t = s := by
  by_contra hne
  obtain ⟨l, hl, hAP⟩ := hF hs ht (fun hst => hne hst.symm)
  have hh := hullZero_subset_of_isAP hAP
    (Finset.mem_inter.mpr ⟨hzero s hs, hzero t ht⟩)
    (Finset.mem_inter.mpr ⟨ha, hat⟩) (Finset.mem_inter.mpr ⟨hb, hbt⟩) hapos
  exact hfail (hh.trans Finset.inter_subset_left)

end
section
open Finset

theorem prod_le_card_succ_mul_prod_pred (s : Finset ℕ) (hs : ∀ p ∈ s, 2 ≤ p) :
    (∏ p ∈ s, p) ≤ (s.card + 1) * ∏ p ∈ s, (p - 1) := by
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert a s hmax ih =>
    have hnot : a ∉ s := by
      intro ha
      exact (lt_irrefl a) (hmax a ha)
    have ha : 2 ≤ a := hs a (Finset.mem_insert_self _ _)
    have hs' : ∀ p ∈ s, 2 ≤ p := fun p hp => hs p (Finset.mem_insert_of_mem hp)
    have hsub : s ⊆ Finset.Icc 2 (a - 1) := by
      intro p hp
      exact Finset.mem_Icc.mpr ⟨hs' p hp, by have := hmax p hp; omega⟩
    have hcard := Finset.card_le_card hsub
    simp only [Nat.card_Icc] at hcard
    have hca : s.card + 2 ≤ a := by omega
    have hprod := Nat.mul_le_mul_left a (ih hs')
    have hcoef : a * (s.card + 1) ≤ (s.card + 2) * (a - 1) := by
      have hapred : a - 1 + 1 = a := by omega
      nlinarith
    have hprod' := Nat.mul_le_mul_right (∏ p ∈ s, (p - 1)) hcoef
    rw [Finset.prod_insert hnot, Finset.prod_insert hnot, Finset.card_insert_of_notMem hnot]
    nlinarith

theorem le_primeFactors_card_succ_mul_totient (n : ℕ) :
    n ≤ (n.primeFactors.card + 1) * n.totient := by
  have hprime : ∀ p ∈ n.primeFactors, 2 ≤ p :=
    fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
  have hprod := prod_le_card_succ_mul_prod_pred n.primeFactors hprime
  have hmult := Nat.mul_le_mul_left n.totient hprod
  have hidentity := Nat.totient_mul_prod_primeFactors n
  have hpos : 0 < ∏ p ∈ n.primeFactors, (p - 1) :=
    Finset.prod_pos (fun p hp => by have := hprime p hp; omega)
  have hineq : n * (∏ p ∈ n.primeFactors, (p - 1)) ≤
      ((n.primeFactors.card + 1) * n.totient) * (∏ p ∈ n.primeFactors, (p - 1)) := by
    nlinarith
  exact (mul_le_mul_iff_left₀ hpos).mp hineq

theorem primeFactors_card_le_log_two {n : ℕ} (hn : n ≠ 0) :
    n.primeFactors.card ≤ Nat.log 2 n := by
  apply (Nat.le_log_iff_pow_le (by decide) hn).mpr
  calc
    2 ^ n.primeFactors.card ≤ ∏ p ∈ n.primeFactors, p :=
      Finset.pow_card_le_prod _ _ _
        (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
    _ ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.prod_primeFactors_dvd n)

theorem le_log_succ_mul_totient (n : ℕ) :
    n ≤ (Nat.log 2 n + 1) * n.totient := by
  by_cases hn : n = 0
  · simp [hn]
  · exact (le_primeFactors_card_succ_mul_totient n).trans
      (Nat.mul_le_mul_right _ (Nat.add_le_add_right (primeFactors_card_le_log_two hn) 1))

theorem totient_ratio_le_log_succ {n : ℕ} (hn : 0 < n) :
    (n : ℝ) / (n.totient : ℝ) ≤ (Nat.log 2 n : ℝ) + 1 := by
  have hp : (0 : ℝ) < n.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hn)
  apply (div_le_iff₀ hp).mpr
  exact_mod_cast le_log_succ_mul_totient n

end
section
open Finset

theorem odd_reciprocal_sq_step {x : ℝ} (hx : 0 ≤ x) :
    1 / (2 * x + 5) ^ 2 ≤ 1 / (4 * x + 8) - 1 / (4 * x + 12) := by
  have h4 : 0 < 2 * x + 4 := by positivity
  have h6 : 0 < 2 * x + 6 := by positivity
  calc
    1 / (2 * x + 5) ^ 2 ≤ 1 / ((2 * x + 4) * (2 * x + 6)) :=
      one_div_le_one_div_of_le (mul_pos h4 h6) (by nlinarith)
    _ = 1 / (4 * x + 8) - 1 / (4 * x + 12) := by
      have h8 : 4 * x + 8 ≠ 0 := by positivity
      have h12 : 4 * x + 12 ≠ 0 := by positivity
      field_simp
      ring

theorem odd_reciprocal_sq_tail (N : ℕ) :
    (∑ k ∈ Finset.range N, 1 / (2 * (k : ℝ) + 5) ^ 2) ≤
      1 / 8 - 1 / (4 * (N : ℝ) + 8) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have hs := odd_reciprocal_sq_step (Nat.cast_nonneg N)
    calc
      _ ≤ (1 / 8 - 1 / (4 * (N : ℝ) + 8)) +
          (1 / (4 * (N : ℝ) + 8) - 1 / (4 * (N : ℝ) + 12)) := add_le_add ih hs
      _ = _ := by push_cast; ring

theorem odd_reciprocal_sq_sum (N : ℕ) :
    (∑ k ∈ Finset.range N, 1 / (2 * (k : ℝ) + 3) ^ 2) ≤ 17 / 72 := by
  cases N with
  | zero => norm_num
  | succ N =>
    rw [Finset.sum_range_succ']
    have heq : (∑ k ∈ Finset.range N, 1 / (2 * ((k + 1 : ℕ) : ℝ) + 3) ^ 2) =
        ∑ k ∈ Finset.range N, 1 / (2 * (k : ℝ) + 5) ^ 2 := by
      apply Finset.sum_congr rfl
      intro k hk
      push_cast
      congr 2; ring
    rw [heq]
    norm_num only [Nat.cast_zero, mul_zero, zero_add]
    have ht := odd_reciprocal_sq_tail N
    have hp : 0 ≤ 1 / (4 * (N : ℝ) + 8) := by positivity
    linarith

def positiveMultiples (N d : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun a => d ∣ a)

def divisorBlock (N d : ℕ) : Finset (ℕ × ℕ) :=
  positiveMultiples N d ×ˢ positiveMultiples N d

def coprimeSquare (N : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).filter (fun p => p.1.Coprime p.2)

def noncoprimeSquare (N : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).filter (fun p => ¬p.1.Coprime p.2)

theorem card_positiveMultiples_le (N : ℕ) {d : ℕ} (hd : 0 < d) :
    (positiveMultiples N d).card ≤ N / d := by
  have hmaps : Set.MapsTo (fun a : ℕ => a / d)
      (positiveMultiples N d : Set ℕ) (Finset.Icc 1 (N / d) : Set ℕ) := by
    intro a ha
    obtain ⟨haI, had⟩ := Finset.mem_filter.mp ha
    obtain ⟨ha1, haN⟩ := Finset.mem_Icc.mp haI
    exact Finset.mem_Icc.mpr
      ⟨Nat.div_pos (Nat.le_of_dvd ha1 had) hd, Nat.div_le_div_right haN⟩
  have hinj : Set.InjOn (fun a : ℕ => a / d) (positiveMultiples N d : Set ℕ) := by
    intro a ha b hb hab
    have hda := (Finset.mem_filter.mp ha).2
    have hdb := (Finset.mem_filter.mp hb).2
    calc
      a = a / d * d := (Nat.div_mul_cancel hda).symm
      _ = b / d * d := congrArg (fun k => k * d) hab
      _ = b := Nat.div_mul_cancel hdb
  simpa using Finset.card_le_card_of_injOn (fun a : ℕ => a / d) hmaps hinj

theorem card_divisorBlock_le (N : ℕ) {d : ℕ} (hd : 0 < d) :
    (divisorBlock N d).card ≤ (N / d) ^ 2 := by
  have hh := card_positiveMultiples_le N hd
  simp only [divisorBlock, Finset.card_product]
  nlinarith

theorem card_divisorBlock_real_le (N : ℕ) {d : ℕ} (hd : 0 < d) :
    ((divisorBlock N d).card : ℝ) ≤ (N : ℝ) ^ 2 / (d : ℝ) ^ 2 := by
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hquot : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / (d : ℝ) := by
    apply (le_div_iff₀ hdR).mpr
    exact_mod_cast Nat.div_mul_le_self N d
  have hsq := (sq_le_sq₀ (Nat.cast_nonneg (N / d))
    (div_nonneg (Nat.cast_nonneg N) hdR.le)).mpr hquot
  have hc : ((divisorBlock N d).card : ℝ) ≤ ((N / d : ℕ) : ℝ) ^ 2 :=
    by exact_mod_cast card_divisorBlock_le N hd
  exact hc.trans (by simpa [div_pow] using hsq)

theorem noncoprimeSquare_subset_blocks (N : ℕ) :
    noncoprimeSquare N ⊆ divisorBlock N 2 ∪
      (Finset.range N).biUnion (fun k => divisorBlock N (2 * k + 3)) := by
  rintro ⟨a, b⟩ hp
  obtain ⟨hpI, hcop⟩ := Finset.mem_filter.mp hp
  obtain ⟨haI, hbI⟩ := Finset.mem_product.mp hpI
  obtain ⟨ha1, haN⟩ := Finset.mem_Icc.mp haI
  obtain ⟨hb1, hbN⟩ := Finset.mem_Icc.mp hbI
  have hpos : 0 < a.gcd b := Nat.gcd_pos_of_pos_left b ha1
  have hne : a.gcd b ≠ 1 := hcop
  have hle : a.gcd b ≤ N := (Nat.gcd_le_left b ha1).trans haN
  have hblock (d : ℕ) (hd : d ∣ a.gcd b) : (a, b) ∈ divisorBlock N d := by
    exact Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr ⟨haI, hd.trans (Nat.gcd_dvd_left a b)⟩,
        Finset.mem_filter.mpr ⟨hbI, hd.trans (Nat.gcd_dvd_right a b)⟩⟩
  by_cases heven : 2 ∣ a.gcd b
  · exact Finset.mem_union_left _ (hblock 2 heven)
  · have hmod : a.gcd b % 2 = 1 := by
      have hnmod : a.gcd b % 2 ≠ 0 := by simpa [Nat.dvd_iff_mod_eq_zero] using heven
      have hm := Nat.mod_lt (a.gcd b) (by decide : 0 < 2)
      omega
    have hdiv := Nat.mod_add_div (a.gcd b) 2
    let k := a.gcd b / 2 - 1
    have hkg : 2 * k + 3 = a.gcd b := by dsimp [k]; omega
    have hkN : k < N := by dsimp [k]; omega
    apply Finset.mem_union_right
    apply Finset.mem_biUnion.mpr
    refine ⟨k, Finset.mem_range.mpr hkN, ?_⟩
    rw [hkg]
    exact hblock _ dvd_rfl

theorem card_noncoprimeSquare_le (N : ℕ) :
    (noncoprimeSquare N).card ≤ (divisorBlock N 2).card +
      ∑ k ∈ Finset.range N, (divisorBlock N (2 * k + 3)).card := by
  calc
    _ ≤ (divisorBlock N 2 ∪
        (Finset.range N).biUnion (fun k => divisorBlock N (2 * k + 3))).card :=
      Finset.card_le_card (noncoprimeSquare_subset_blocks N)
    _ ≤ (divisorBlock N 2).card +
        ((Finset.range N).biUnion (fun k => divisorBlock N (2 * k + 3))).card :=
      Finset.card_union_le _ _
    _ ≤ _ := Nat.add_le_add_left Finset.card_biUnion_le _

theorem card_noncoprimeSquare_real_le (N : ℕ) :
    ((noncoprimeSquare N).card : ℝ) ≤ 35 / 72 * (N : ℝ) ^ 2 := by
  have hcover : ((noncoprimeSquare N).card : ℝ) ≤ ((divisorBlock N 2).card : ℝ) +
      ∑ k ∈ Finset.range N, ((divisorBlock N (2 * k + 3)).card : ℝ) :=
    by exact_mod_cast card_noncoprimeSquare_le N
  have hblocks := Finset.sum_le_sum (s := Finset.range N)
    (fun k _ => card_divisorBlock_real_le N (by omega : 0 < 2 * k + 3))
  have htwo := card_divisorBlock_real_le N (by decide : 0 < 2)
  have hsum := odd_reciprocal_sq_sum N
  have hmain : ((noncoprimeSquare N).card : ℝ) ≤ (N : ℝ) ^ 2 / 4 +
      ∑ k ∈ Finset.range N, (N : ℝ) ^ 2 / (2 * (k : ℝ) + 3) ^ 2 := by
    have hh := hcover.trans (add_le_add htwo hblocks)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_mul, Nat.reducePow] at hh
    exact hh
  have hfactor : (∑ k ∈ Finset.range N, (N : ℝ) ^ 2 / (2 * (k : ℝ) + 3) ^ 2) =
      (N : ℝ) ^ 2 * ∑ k ∈ Finset.range N, 1 / (2 * (k : ℝ) + 3) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hfactor] at hmain
  nlinarith [mul_le_mul_of_nonneg_left hsum (sq_nonneg (N : ℝ))]

theorem coprimeSquare_card_lower (N : ℕ) :
    37 / 72 * (N : ℝ) ^ 2 ≤ ((coprimeSquare N).card : ℝ) := by
  have hp : (coprimeSquare N).card + (noncoprimeSquare N).card = N ^ 2 := by
    have hh := Finset.card_filter_add_card_filter_not
      (s := (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)) (p := fun p : ℕ × ℕ => p.1.Coprime p.2)
    simpa [coprimeSquare, noncoprimeSquare, pow_two] using hh
  have hpR : ((coprimeSquare N).card : ℝ) + ((noncoprimeSquare N).card : ℝ) = (N : ℝ) ^ 2 :=
    by exact_mod_cast hp
  have hh := card_noncoprimeSquare_real_le N
  linarith

def upperCoprime (N : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 N).sigma (fun b => (Finset.Icc 1 b).filter (fun a => b.Coprime a))).image
    (fun p : (Σ _ : ℕ, ℕ) => (p.2, p.1))

def summatoryTotient (N : ℕ) : ℕ := ∑ b ∈ Finset.Icc 1 N, b.totient

theorem mem_upperCoprime {N a b : ℕ} :
    (a, b) ∈ upperCoprime N ↔ b ∈ Finset.Icc 1 N ∧ a ∈ Finset.Icc 1 b ∧ b.Coprime a := by
  constructor
  · intro h
    obtain ⟨⟨b', a'⟩, hp, heq⟩ := Finset.mem_image.mp h
    have h₁ : a' = a := congrArg Prod.fst heq
    have h₂ : b' = b := congrArg Prod.snd heq
    subst a'
    subst b'
    simpa only [Finset.mem_sigma, Finset.mem_filter] using hp
  · rintro ⟨hb, ha, hcop⟩
    exact Finset.mem_image.mpr ⟨⟨b, a⟩,
      Finset.mem_sigma.mpr ⟨hb, Finset.mem_filter.mpr ⟨ha, hcop⟩⟩, rfl⟩

theorem card_coprime_Icc (b : ℕ) :
    ((Finset.Icc 1 b).filter (fun a => b.Coprime a)).card = b.totient := by
  have heq : Finset.Icc 1 b = Finset.Ico 1 (1 + b) := by
    ext a
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [heq]
  exact Nat.filter_coprime_Ico_eq_totient b 1

theorem card_upperCoprime (N : ℕ) : (upperCoprime N).card = summatoryTotient N := by
  have hinj : Function.Injective (fun p : (Σ _ : ℕ, ℕ) => (p.2, p.1)) := by
    rintro ⟨b, a⟩ ⟨d, c⟩ heq
    have h₁ : a = c := congrArg Prod.fst heq
    have h₂ : b = d := congrArg Prod.snd heq
    subst c
    subst d
    rfl
  rw [upperCoprime, Finset.card_image_of_injective _ hinj, Finset.card_sigma]
  exact Finset.sum_congr rfl (fun b _ => card_coprime_Icc b)

theorem coprimeSquare_subset_upper (N : ℕ) :
    coprimeSquare N ⊆ upperCoprime N ∪ (upperCoprime N).image Prod.swap := by
  rintro ⟨a, b⟩ hp
  obtain ⟨hpI, hcop⟩ := Finset.mem_filter.mp hp
  obtain ⟨haI, hbI⟩ := Finset.mem_product.mp hpI
  by_cases hab : a ≤ b
  · exact Finset.mem_union_left _ (mem_upperCoprime.mpr
      ⟨hbI, Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp haI).1, hab⟩, hcop.symm⟩)
  · apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    refine ⟨(b, a), mem_upperCoprime.mpr ?_, rfl⟩
    exact ⟨haI, Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hbI).1, by omega⟩, hcop⟩

theorem coprimeSquare_card_le_twice_totient (N : ℕ) :
    (coprimeSquare N).card ≤ 2 * summatoryTotient N := by
  have hcover := (Finset.card_le_card (coprimeSquare_subset_upper N)).trans
    (Finset.card_union_le _ _)
  have hsum := hcover.trans (Nat.add_le_add_left (Finset.card_image_le (f := Prod.swap)) _)
  simpa [card_upperCoprime, two_mul] using hsum

theorem summatoryTotient_lower (N : ℕ) :
    37 / 144 * (N : ℝ) ^ 2 ≤ (summatoryTotient N : ℝ) := by
  have hupper : ((coprimeSquare N).card : ℝ) ≤ 2 * (summatoryTotient N : ℝ) :=
    by exact_mod_cast coprimeSquare_card_le_twice_totient N
  have hlower := coprimeSquare_card_lower N
  linarith

/-- The prefix inequality required by the negative half of the matching. -/
theorem totient_matching_supply {m : ℕ} (hm : 108 ≤ m) :
    ((m : ℝ) ^ 2 + 3 * (m : ℝ)) / 2 ≤ 2 * (summatoryTotient m : ℝ) := by
  have hmR : (108 : ℝ) ≤ m := by exact_mod_cast hm
  have hquad := mul_nonneg (Nat.cast_nonneg m : (0 : ℝ) ≤ m) (sub_nonneg.mpr hmR)
  have hsum := summatoryTotient_lower m
  nlinarith

/-- Supply of primitive positive pairs after removing the two small exceptions. -/
theorem totient_corner_supply {m : ℕ} (hm : 128 ≤ m) :
    (m : ℝ) ^ 2 / 5 ≤ (summatoryTotient m : ℝ) - 2 := by
  have hmR : (128 : ℝ) ≤ m := by exact_mod_cast hm
  have hsum := summatoryTotient_lower m
  nlinarith

end
section
open Finset

def axisPairs (m : ℕ) : Finset (ℕ × ℕ) :=
  ((upperCoprime m).erase (1, 1)).erase (1, 2)

theorem mem_axisPairs {m a b : ℕ} :
    (a, b) ∈ axisPairs m ↔ 1 ≤ a ∧ a < b ∧ 3 ≤ b ∧ b ≤ m ∧ a.Coprime b := by
  simp only [axisPairs, Finset.mem_erase, mem_upperCoprime, Finset.mem_Icc]
  constructor
  · rintro ⟨hne12, hne11, ⟨hb1, hbm⟩, ⟨ha1, hab⟩, hcop⟩
    have hab' : a < b := by
      by_contra hlt
      have heq : a = b := by omega
      subst b
      have hone : a = 1 := by simpa using hcop
      exact hne11 (Prod.ext hone hone)
    have hb3 : 3 ≤ b := by
      by_contra hlt
      have hbeq : b = 2 := by omega
      have haeq : a = 1 := by omega
      exact hne12 (Prod.ext haeq hbeq)
    exact ⟨ha1, hab', hb3, hbm, hcop.symm⟩
  · rintro ⟨ha1, hab, hb3, hbm, hcop⟩
    refine ⟨?_, ?_, ⟨by omega, hbm⟩, ⟨ha1, hab.le⟩, hcop.symm⟩
    · intro heq
      have hb := congrArg Prod.snd heq
      change b = 2 at hb
      omega
    · intro heq
      have hb := congrArg Prod.snd heq
      change b = 1 at hb
      omega

theorem axisPairs_mono {m n : ℕ} (hmn : m ≤ n) : axisPairs m ⊆ axisPairs n := by
  rintro ⟨a, b⟩ hp
  rcases mem_axisPairs.mp hp with ⟨ha, hab, hb, hbm, hcop⟩
  exact mem_axisPairs.mpr ⟨ha, hab, hb, hbm.trans hmn, hcop⟩

theorem card_axisPairs_add_two {m : ℕ} (hm : 2 ≤ m) :
    (axisPairs m).card + 2 = summatoryTotient m := by
  have h11 : (1, 1) ∈ upperCoprime m :=
    mem_upperCoprime.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩,
      by simp, by decide⟩
  have h12 : (1, 2) ∈ (upperCoprime m).erase (1, 1) := by
    apply Finset.mem_erase.mpr
    exact ⟨by decide, mem_upperCoprime.mpr
      ⟨Finset.mem_Icc.mpr ⟨by decide, hm⟩, by simp, by decide⟩⟩
  have hc11 := Finset.card_erase_add_one h11
  have hc12 := Finset.card_erase_add_one h12
  rw [card_upperCoprime] at hc11
  change (((upperCoprime m).erase (1, 1)).erase (1, 2)).card + 2 = _
  omega

def triangleCells (m : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (m + 1)).sigma (fun l => Finset.range (l + 1))).image
    (fun p : (Σ _ : ℕ, ℕ) => (p.1, p.2))

def noncoprimeTriangle (m : ℕ) : Finset (ℕ × ℕ) :=
  (triangleCells m).filter (fun p => ¬p.1.Coprime p.2)

theorem mem_triangleCells {m l r : ℕ} :
    (l, r) ∈ triangleCells m ↔ l ≤ m ∧ r ≤ l := by
  constructor
  · intro h
    obtain ⟨⟨l', r'⟩, hp, heq⟩ := Finset.mem_image.mp h
    have h₁ : l' = l := congrArg Prod.fst heq
    have h₂ : r' = r := congrArg Prod.snd heq
    subst l'
    subst r'
    simpa only [Finset.mem_sigma, Finset.mem_range, Nat.lt_succ_iff] using hp
  · rintro ⟨hl, hr⟩
    refine Finset.mem_image.mpr ⟨⟨l, r⟩, ?_, rfl⟩
    simpa only [Finset.mem_sigma, Finset.mem_range, Nat.lt_succ_iff] using And.intro hl hr

theorem card_triangleCells (m : ℕ) :
    2 * (triangleCells m).card = (m + 1) * (m + 2) := by
  have hinj : Function.Injective (fun p : (Σ _ : ℕ, ℕ) => (p.1, p.2)) := by
    rintro ⟨a, b⟩ ⟨c, d⟩ heq
    have h₁ : a = c := congrArg Prod.fst heq
    have h₂ : b = d := congrArg Prod.snd heq
    subst c
    subst d
    rfl
  have hc : (triangleCells m).card = ∑ l ∈ Finset.range (m + 1), (l + 1) := by
    simp [triangleCells, Finset.card_image_of_injective _ hinj, Finset.card_sigma]
  rw [hc]
  clear hc hinj
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    nlinarith

theorem card_noncoprimeTriangle_add_totient_le (m : ℕ) :
    (noncoprimeTriangle m).card + summatoryTotient m ≤ (triangleCells m).card := by
  have hsub : noncoprimeTriangle m ∪ (upperCoprime m).image Prod.swap ⊆ triangleCells m := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact (Finset.mem_filter.mp hp).1
    · obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hp
      rcases mem_upperCoprime.mp hab with ⟨hbI, haI, hcop⟩
      exact mem_triangleCells.mpr ⟨(Finset.mem_Icc.mp hbI).2, (Finset.mem_Icc.mp haI).2⟩
  have hdisj : Disjoint (noncoprimeTriangle m) ((upperCoprime m).image Prod.swap) := by
    rw [Finset.disjoint_left]
    intro p hp hq
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hq
    exact (Finset.mem_filter.mp hp).2 (mem_upperCoprime.mp hab).2.2
  have hh := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ Prod.swap_injective, card_upperCoprime] at hh
  exact hh

theorem noncoprimeTriangle_le_axisPairs_large {m : ℕ} (hm : 128 ≤ m) :
    (noncoprimeTriangle m).card ≤ (axisPairs m).card := by
  have hcards := card_noncoprimeTriangle_add_totient_le m
  have htriangle := card_triangleCells m
  have haxis := card_axisPairs_add_two (by omega : 2 ≤ m)
  have hsum := summatoryTotient_lower m
  have hcR : ((noncoprimeTriangle m).card : ℝ) + (summatoryTotient m : ℝ) ≤
      ((triangleCells m).card : ℝ) := by exact_mod_cast hcards
  have htR : 2 * ((triangleCells m).card : ℝ) = ((m : ℝ) + 1) * ((m : ℝ) + 2) :=
    by exact_mod_cast htriangle
  have haR : ((axisPairs m).card : ℝ) + 2 = (summatoryTotient m : ℝ) :=
    by exact_mod_cast haxis
  have hmR : (128 : ℝ) ≤ m := by exact_mod_cast hm
  have hprod := mul_nonneg (Nat.cast_nonneg m : (0 : ℝ) ≤ m) (sub_nonneg.mpr hmR)
  apply Nat.cast_le (α := ℝ).mp
  nlinarith

theorem noncoprimeTriangle_prefix_bound (m : ℕ) :
    (noncoprimeTriangle m).card ≤ (axisPairs m).card + 10000 := by
  by_cases hm : 128 ≤ m
  · exact (noncoprimeTriangle_le_axisPairs_large hm).trans (Nat.le_add_right _ _)
  · have hsub : noncoprimeTriangle m ⊆ triangleCells m := Finset.filter_subset _ _
    have hcard := Finset.card_le_card hsub
    have htri := card_triangleCells m
    have hprod : (m + 1) * (m + 2) ≤ 128 * 129 := Nat.mul_le_mul (by omega) (by omega)
    omega

abbrev NoncoprimeCell := {p : ℕ × ℕ // p.2 ≤ p.1 ∧ ¬p.1.Coprime p.2}

abbrev AxisToken := (ℕ × ℕ) ⊕ Fin 10000

def axisNeighborhood (p : NoncoprimeCell) : Finset AxisToken :=
  (axisPairs p.val.1).disjSum Finset.univ

theorem axisNeighborhood_hall (S : Finset NoncoprimeCell) :
    S.card ≤ (S.biUnion axisNeighborhood).card := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp
  · obtain ⟨a, ha, hmax⟩ := Finset.exists_max_image S (fun p : NoncoprimeCell => p.val.1) hS
    have hmaps : Set.MapsTo (fun p : NoncoprimeCell => p.val)
        (S : Set NoncoprimeCell) (noncoprimeTriangle a.val.1 : Set (ℕ × ℕ)) := by
      intro p hp
      exact Finset.mem_filter.mpr
        ⟨mem_triangleCells.mpr ⟨hmax p hp, p.property.1⟩, p.property.2⟩
    have hc := Finset.card_le_card_of_injOn (fun p : NoncoprimeCell => p.val)
      hmaps Subtype.coe_injective.injOn
    calc
      S.card ≤ (noncoprimeTriangle a.val.1).card := hc
      _ ≤ (axisPairs a.val.1).card + 10000 := noncoprimeTriangle_prefix_bound _
      _ = (axisNeighborhood a).card := by simp [axisNeighborhood]
      _ ≤ (S.biUnion axisNeighborhood).card :=
        Finset.card_le_card (Finset.subset_biUnion_of_mem axisNeighborhood ha)

/-- One matching works simultaneously at every level, with at most 10000 dummy values. -/
theorem exists_axis_matching :
    ∃ f : NoncoprimeCell → AxisToken,
      Function.Injective f ∧ ∀ p, f p ∈ axisNeighborhood p := by
  classical
  exact (Finset.all_card_le_biUnion_card_iff_exists_injective axisNeighborhood).mp
    axisNeighborhood_hall

end
section
open Finset

abbrev ProgressionCell := {p : ℕ × ℕ // 3 ≤ p.1 + p.2}

abbrev ClassifiedCell := (ℕ × ℕ) ⊕ (NoncoprimeCell ⊕ NoncoprimeCell)

abbrev IntervalRawToken := (ℕ × ℕ) ⊕ (AxisToken ⊕ AxisToken)

def classifyCell (p : ProgressionCell) : ClassifiedCell :=
  if hc : p.val.1.Coprime p.val.2 then Sum.inl p.val
  else if hh : p.val.2 ≤ p.val.1 then
    Sum.inr (Sum.inl ⟨p.val, hh, hc⟩)
  else Sum.inr (Sum.inr ⟨p.val.swap, by simpa using (Nat.le_of_lt (lt_of_not_ge hh)),
    fun h => hc h.symm⟩)

def unclassifyCell : ClassifiedCell → ℕ × ℕ
  | Sum.inl p => p
  | Sum.inr (Sum.inl p) => p.val
  | Sum.inr (Sum.inr p) => p.val.swap

theorem unclassify_classify (p : ProgressionCell) : unclassifyCell (classifyCell p) = p.val := by
  unfold classifyCell
  split_ifs <;> simp [unclassifyCell]

theorem classifyCell_injective : Function.Injective classifyCell := by
  intro p q hpq
  apply Subtype.ext
  have hh := congrArg unclassifyCell hpq
  simpa only [unclassify_classify] using hh

def RawTokenValid (p : ProgressionCell) : IntervalRawToken → Prop
  | Sum.inl q => q = p.val ∧ q.1.Coprime q.2
  | Sum.inr (Sum.inl q) => q ∈ (axisPairs p.val.1).disjSum (Finset.univ : Finset (Fin 10000))
  | Sum.inr (Sum.inr q) => q ∈ (axisPairs p.val.2).disjSum (Finset.univ : Finset (Fin 10000))

theorem exists_interval_raw_matching :
    ∃ f : ProgressionCell → IntervalRawToken,
      Function.Injective f ∧ ∀ p, RawTokenValid p (f p) := by
  obtain ⟨g, hg, hmem⟩ := exists_axis_matching
  let f : ProgressionCell → IntervalRawToken :=
    Sum.map id (Sum.map g g) ∘ classifyCell
  refine ⟨f, ?_, ?_⟩
  · have hmap : Function.Injective (Sum.map (id : ℕ × ℕ → ℕ × ℕ) (Sum.map g g)) :=
      Sum.map_injective.mpr ⟨Function.injective_id, Sum.map_injective.mpr ⟨hg, hg⟩⟩
    exact hmap.comp classifyCell_injective
  · intro p
    dsimp [f, Function.comp_def]
    unfold classifyCell
    split_ifs with hc hh
    · exact ⟨rfl, hc⟩
    · exact hmem ⟨p.val, hh, hc⟩
    · exact hmem ⟨p.val.swap, by simpa using (Nat.le_of_lt (lt_of_not_ge hh)),
        fun h => hc h.symm⟩

def rawPair : IntervalRawToken → Option (ℤ × ℤ)
  | Sum.inl (l, r) => some (-(l : ℤ), (r : ℤ))
  | Sum.inr (Sum.inl (Sum.inl (a, b))) => some (-(b : ℤ), -(a : ℤ))
  | Sum.inr (Sum.inr (Sum.inl (a, b))) => some ((a : ℤ), (b : ℤ))
  | Sum.inr (Sum.inl (Sum.inr _)) => none
  | Sum.inr (Sum.inr (Sum.inr _)) => none

def encodeIntervalDummy : (Fin 10000 ⊕ Fin 10000) → IntervalRawToken
  | Sum.inl i => Sum.inr (Sum.inl (Sum.inr i))
  | Sum.inr i => Sum.inr (Sum.inr (Sum.inr i))

def intervalDummyTokens : Finset IntervalRawToken :=
  Finset.univ.image encodeIntervalDummy

theorem encodeIntervalDummy_injective : Function.Injective encodeIntervalDummy := by
  intro a b h
  cases a <;> cases b <;> simp_all [encodeIntervalDummy]

theorem card_intervalDummyTokens : intervalDummyTokens.card = 20000 := by
  simp [intervalDummyTokens, Finset.card_image_of_injective _ encodeIntervalDummy_injective]

theorem rawPair_eq_none_iff (t : IntervalRawToken) :
    rawPair t = none ↔ t ∈ intervalDummyTokens := by
  rcases t with ⟨l, r⟩ | (⟨a, b⟩ | i) | (⟨a, b⟩ | i) <;>
    simp [rawPair, intervalDummyTokens, encodeIntervalDummy, Sum.exists]

theorem coprime_cell_positive {p : ProgressionCell} (hc : p.val.1.Coprime p.val.2) :
    0 < p.val.1 ∧ 0 < p.val.2 ∧ p.val.1 ≠ p.val.2 := by
  have hsize := p.property
  have hl : 0 < p.val.1 := by
    by_contra h
    have heq : p.val.1 = 0 := by omega
    have hr : p.val.2 = 1 := by simpa [heq] using hc
    omega
  have hr : 0 < p.val.2 := by
    by_contra h
    have heq : p.val.2 = 0 := by omega
    have hl' : p.val.1 = 1 := by simpa [heq] using hc
    omega
  refine ⟨hl, hr, ?_⟩
  intro heq
  have h1 : p.val.2 = 1 := by simpa [heq] using hc
  omega

def PositiveRawToken : IntervalRawToken → Prop
  | Sum.inl (l, r) => 0 < l ∧ 0 < r
  | Sum.inr (Sum.inl (Sum.inl (a, b))) => 0 < a ∧ 0 < b
  | Sum.inr (Sum.inr (Sum.inl (a, b))) => 0 < a ∧ 0 < b
  | Sum.inr (Sum.inl (Sum.inr _)) => True
  | Sum.inr (Sum.inr (Sum.inr _)) => True

theorem rawTokenValid_positive {p : ProgressionCell} {t : IntervalRawToken}
    (h : RawTokenValid p t) : PositiveRawToken t := by
  rcases t with ⟨l, r⟩ | (⟨a, b⟩ | i) | (⟨a, b⟩ | i)
  · obtain ⟨heq, hc⟩ := h
    have hpos := coprime_cell_positive (p := p) (by simpa [← heq] using hc)
    simpa only [PositiveRawToken, ← heq] using And.intro hpos.1 hpos.2.1
  · have hp := mem_axisPairs.mp (Finset.inl_mem_disjSum.mp h)
    exact ⟨hp.1, by omega⟩
  · trivial
  · have hp := mem_axisPairs.mp (Finset.inl_mem_disjSum.mp h)
    exact ⟨hp.1, by omega⟩
  · trivial

theorem rawPair_some_injective {t s : IntervalRawToken}
    (ht : PositiveRawToken t) (hs : PositiveRawToken s)
    (hne : rawPair t ≠ none) (heq : rawPair t = rawPair s) : t = s := by
  rcases t with ⟨l, r⟩ | (⟨a, b⟩ | i) | (⟨a, b⟩ | i) <;>
    rcases s with ⟨l', r'⟩ | (⟨a', b'⟩ | i') | (⟨a', b'⟩ | i') <;>
    simp_all [PositiveRawToken, rawPair]

/-- A contained primitive pair which forms no three-term progression with zero. -/
def PrimitiveBadPair (p : ProgressionCell) (q : ℤ × ℤ) : Prop :=
  -(p.val.1 : ℤ) ≤ q.1 ∧ q.1 < q.2 ∧ q.2 ≤ (p.val.2 : ℤ) ∧
    q.1 ≠ 0 ∧ q.2 ≠ 0 ∧ q.1.natAbs.Coprime q.2.natAbs ∧
      q.1 + q.2 ≠ 0 ∧ 2 * q.1 ≠ q.2 ∧ q.1 ≠ 2 * q.2

theorem axis_pair_not_twice {m a b : ℕ} (h : (a, b) ∈ axisPairs m) : b ≠ 2 * a := by
  rcases mem_axisPairs.mp h with ⟨ha, hab, hb, hbm, hc⟩
  intro heq
  have hd : a ∣ b := by rw [heq]; exact dvd_mul_left a 2
  have hg := Nat.gcd_eq_left_iff_dvd.mpr hd
  have hg1 : a.gcd b = 1 := hc
  have ha1 : a = 1 := by omega
  omega

theorem primitiveBadPair_mixed {p : ProgressionCell} (hc : p.val.1.Coprime p.val.2) :
    PrimitiveBadPair p (-(p.val.1 : ℤ), (p.val.2 : ℤ)) := by
  have hpos := coprime_cell_positive hc
  refine ⟨le_rfl, by omega, le_rfl, by omega, by omega, ?_, by omega, by omega, by omega⟩
  simpa using hc

theorem primitiveBadPair_negative {p : ProgressionCell} {a b : ℕ}
    (h : (a, b) ∈ axisPairs p.val.1) : PrimitiveBadPair p (-(b : ℤ), -(a : ℤ)) := by
  have hn := axis_pair_not_twice h
  rcases mem_axisPairs.mp h with ⟨ha, hab, hb, hbm, hc⟩
  refine ⟨by omega, by omega, by omega, by omega, by omega, ?_, by omega, by omega, by omega⟩
  simpa using hc.symm

theorem primitiveBadPair_positive {p : ProgressionCell} {a b : ℕ}
    (h : (a, b) ∈ axisPairs p.val.2) : PrimitiveBadPair p ((a : ℤ), (b : ℤ)) := by
  have hn := axis_pair_not_twice h
  rcases mem_axisPairs.mp h with ⟨ha, hab, hb, hbm, hc⟩
  refine ⟨by omega, by omega, by omega, by omega, by omega, ?_, by omega, by omega, by omega⟩
  simpa using hc

theorem rawTokenValid_pair {p : ProgressionCell} {t : IntervalRawToken} {q : ℤ × ℤ}
    (h : RawTokenValid p t) (hq : rawPair t = some q) : PrimitiveBadPair p q := by
  rcases t with ⟨l, r⟩ | (⟨a, b⟩ | i) | (⟨a, b⟩ | i)
  · obtain ⟨heq, hc⟩ := h
    have hpair : (-(l : ℤ), (r : ℤ)) = q := Option.some.inj hq
    rw [← hpair]
    have hcop : p.val.1.Coprime p.val.2 := by simpa [← heq] using hc
    simpa only [← heq] using primitiveBadPair_mixed hcop
  · have hpair : (-(b : ℤ), -(a : ℤ)) = q := Option.some.inj hq
    rw [← hpair]
    exact primitiveBadPair_negative (Finset.inl_mem_disjSum.mp h)
  · cases hq
  · have hpair : ((a : ℤ), (b : ℤ)) = q := Option.some.inj hq
    rw [← hpair]
    exact primitiveBadPair_positive (Finset.inl_mem_disjSum.mp h)
  · cases hq

theorem not_isAP_triple_of_relations {u v : ℤ}
    (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v)
    (hadd : u + v ≠ 0) (hdu : 2 * u ≠ v) (hdv : u ≠ 2 * v) :
    ¬ ∃ l : ℕ∞, (({0, u, v} : Finset ℤ) : Set ℤ).IsAPOfLength l := by
  rintro ⟨l, hAP⟩
  have hcard : ({0, u, v} : Finset ℤ).card = 3 := by simp [hu.symm, hv.symm, huv]
  have hl : (3 : ℕ∞) = l := by simpa [hcard] using hAP.card
  obtain ⟨a, d, hset⟩ := hAP.eq
  have hrep (x : ℤ) : x ∈ ({0, u, v} : Finset ℤ) ↔
      ∃ i : ℕ, i < 3 ∧ a + (i : ℤ) * d = x := by
    change x ∈ (({0, u, v} : Finset ℤ) : Set ℤ) ↔ _
    rw [hset]
    simp [← hl]
  have ha : a = 0 ∨ a = u ∨ a = v := by
    have hh := (hrep a).mpr ⟨0, by decide, by simp⟩
    simpa using hh
  have hb : a + d = 0 ∨ a + d = u ∨ a + d = v := by
    have hh := (hrep (a + d)).mpr ⟨1, by decide, by simp⟩
    simpa using hh
  have hc : a + 2 * d = 0 ∨ a + 2 * d = u ∨ a + 2 * d = v := by
    have hh := (hrep (a + 2 * d)).mpr ⟨2, by decide, by simp⟩
    simpa using hh
  have hd : d ≠ 0 := by
    intro hd
    obtain ⟨i, hi, hui⟩ := (hrep u).mp (by simp)
    obtain ⟨j, hj, hvj⟩ := (hrep v).mp (by simp)
    simp only [hd, mul_zero, add_zero] at hui hvj
    exact huv (hui.symm.trans hvj)
  rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb <;>
    rcases hc with hc | hc | hc <;> omega

theorem primitiveBadPair_not_isAP {p : ProgressionCell} {q : ℤ × ℤ}
    (h : PrimitiveBadPair p q) :
    ¬ ∃ l : ℕ∞, (({0, q.1, q.2} : Finset ℤ) : Set ℤ).IsAPOfLength l := by
  rcases h with ⟨hleft, hlt, hright, hu, hv, hcop, hadd, hdu, hdv⟩
  exact not_isAP_triple_of_relations hu hv hlt.ne hadd hdu hdv

/-- Normalized form of the draft's progression matching lemma. -/
theorem exists_progression_pair_matching :
    ∃ f : ProgressionCell → Option (ℤ × ℤ),
      (∀ p q, f p = some q → PrimitiveBadPair p q) ∧
      (∀ p p' q, f p = some q → f p' = some q → p = p') ∧
      (∀ S : Finset ProgressionCell, (S.filter (fun p => f p = none)).card ≤ 20000) := by
  classical
  obtain ⟨g, hg, hvalid⟩ := exists_interval_raw_matching
  refine ⟨rawPair ∘ g, ?_, ?_, ?_⟩
  · intro p q hpq
    exact rawTokenValid_pair (hvalid p) hpq
  · intro p p' q hp hp'
    apply hg
    apply rawPair_some_injective (rawTokenValid_positive (hvalid p))
      (rawTokenValid_positive (hvalid p'))
    · change rawPair (g p) = some q at hp
      rw [hp]
      simp
    · exact hp.trans hp'.symm
  · intro S
    have hmaps : Set.MapsTo g
        ((S.filter (fun p => (rawPair ∘ g) p = none)) : Set ProgressionCell)
        (intervalDummyTokens : Set IntervalRawToken) := by
      intro p hp
      exact (rawPair_eq_none_iff (g p)).mp (Finset.mem_filter.mp hp).2
    have hc := Finset.card_le_card_of_injOn g hmaps hg.injOn
    simpa only [card_intervalDummyTokens] using hc

end
section
open Finset

def natAP (a d k : ℕ) : Finset ℕ :=
  (Finset.range k).image (fun i => a + i * d)

theorem mem_natAP {a d k x : ℕ} :
    x ∈ natAP a d k ↔ ∃ i < k, a + i * d = x := by
  simp [natAP]

theorem natAP_isAP {a d k : ℕ} (hd : 0 < d) :
    (natAP a d k : Set ℕ).IsAPOfLength k := range_image_isAP a d k hd

theorem nat_ap_representation_pos {S : Finset ℕ} {l : ℕ∞}
    (hAP : (S : Set ℕ).IsAPOfLength l) (hcard : 2 ≤ S.card) :
    ∃ a d : ℕ, 0 < d ∧ ∀ x : ℕ, x ∈ S ↔ ∃ i < S.card, a + i * d = x := by
  obtain ⟨a, d, hrep⟩ := finset_ap_representation hAP
  refine ⟨a, d, ?_, hrep⟩
  by_contra hd
  have hd0 : d = 0 := by omega
  have hsmall : S.card ≤ 1 := Finset.card_le_one.mpr (by
    intro x hx y hy
    obtain ⟨i, hi, hxi⟩ := (hrep x).mp hx
    obtain ⟨j, hj, hyj⟩ := (hrep y).mp hy
    simp only [hd0, mul_zero, add_zero] at hxi hyj
    exact hxi.symm.trans hyj)
  omega

theorem nat_ap_eq_natAP {S : Finset ℕ} {l : ℕ∞}
    (hAP : (S : Set ℕ).IsAPOfLength l) (hcard : 2 ≤ S.card) :
    ∃ a d : ℕ, 0 < d ∧ S = natAP a d S.card := by
  obtain ⟨a, d, hd, hrep⟩ := nat_ap_representation_pos hAP hcard
  refine ⟨a, d, hd, ?_⟩
  ext x
  exact (hrep x).trans mem_natAP.symm

def ConsecutiveIn (S : Finset ℕ) (u v : ℕ) : Prop :=
  u ∈ S ∧ v ∈ S ∧ u < v ∧ ∀ x ∈ S, ¬ (u < x ∧ x < v)

theorem ConsecutiveIn.card_ge_two {S : Finset ℕ} {u v : ℕ}
    (h : ConsecutiveIn S u v) : 2 ≤ S.card := by
  have hsub : {u, v} ⊆ S := by simp [Finset.insert_subset_iff, h.1, h.2.1]
  have hh := Finset.card_le_card hsub
  simpa [h.2.2.1.ne] using hh

theorem ConsecutiveIn.inter {S T : Finset ℕ} {u v : ℕ}
    (hS : ConsecutiveIn S u v) (huT : u ∈ T) (hvT : v ∈ T) :
    ConsecutiveIn (S ∩ T) u v := by
  exact ⟨Finset.mem_inter.mpr ⟨hS.1, huT⟩, Finset.mem_inter.mpr ⟨hS.2.1, hvT⟩,
    hS.2.2.1, fun x hx => hS.2.2.2 x (Finset.mem_inter.mp hx).1⟩

theorem ConsecutiveIn.union {S T : Finset ℕ} {u v : ℕ}
    (hS : ConsecutiveIn S u v) (hT : ConsecutiveIn T u v) :
    ConsecutiveIn (S ∪ T) u v := by
  refine ⟨Finset.mem_union_left _ hS.1, Finset.mem_union_left _ hS.2.1, hS.2.2.1, ?_⟩
  intro x hx
  rcases Finset.mem_union.mp hx with hx | hx
  · exact hS.2.2.2 x hx
  · exact hT.2.2.2 x hx

theorem natAP_step_of_consecutive {a d k u v : ℕ} (hd : 0 < d)
    (h : ConsecutiveIn (natAP a d k) u v) : d = v - u := by
  obtain ⟨i, hi, hui⟩ := mem_natAP.mp h.1
  obtain ⟨j, hj, hvj⟩ := mem_natAP.mp h.2.1
  have huv := h.2.2.1
  have hij : i < j := by
    by_contra hh
    have hmul := Nat.mul_le_mul_right d (Nat.le_of_not_gt hh)
    omega
  have hnext : j = i + 1 := by
    by_contra hh
    have hgap : i + 1 < j := by omega
    have hx : a + (i + 1) * d ∈ natAP a d k := mem_natAP.mpr
      ⟨i + 1, hgap.trans hj, rfl⟩
    have hleft : u < a + (i + 1) * d := by nlinarith
    have hright : a + (i + 1) * d < v := by
      have hmul := Nat.mul_lt_mul_of_pos_right hgap hd
      omega
    exact h.2.2.2 _ hx ⟨hleft, hright⟩
  have hv : v = u + d := by rw [hnext] at hvj; nlinarith
  omega

theorem nat_ap_eq_with_consecutive_gap {S : Finset ℕ} {l : ℕ∞} {u v : ℕ}
    (hAP : (S : Set ℕ).IsAPOfLength l) (hcon : ConsecutiveIn S u v) :
    ∃ a : ℕ, S = natAP a (v - u) S.card := by
  obtain ⟨a, d, hd, heq⟩ := nat_ap_eq_natAP hAP hcon.card_ge_two
  have hgap := natAP_step_of_consecutive hd (heq ▸ hcon)
  exact ⟨a, by simpa [hgap] using heq⟩

theorem natAP_union_overlap (a d k t m : ℕ) (ht : t < k) :
    natAP a d k ∪ natAP (a + t * d) d m = natAP a d (max k (t + m)) := by
  ext x
  simp only [Finset.mem_union, mem_natAP]
  constructor
  · rintro (⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩)
    · exact ⟨i, hi.trans_le (le_max_left _ _), rfl⟩
    · refine ⟨t + j, (Nat.add_lt_add_left hj t).trans_le (le_max_right _ _), ?_⟩
      ring
  · rintro ⟨i, hi, rfl⟩
    by_cases hik : i < k
    · exact Or.inl ⟨i, hik, rfl⟩
    · have hit : t ≤ i := by omega
      have him : i - t < m := by omega
      refine Or.inr ⟨i - t, him, ?_⟩
      have hei : t + (i - t) = i := Nat.add_sub_of_le hit
      nlinarith

theorem natAP_union_isAP_of_common_point {a b d k m u : ℕ}
    (hd : 0 < d) (huS : u ∈ natAP a d k) (huT : u ∈ natAP b d m) :
    ∃ l : ℕ∞, ((natAP a d k ∪ natAP b d m : Finset ℕ) : Set ℕ).IsAPOfLength l := by
  suffices ∀ a b k m, a ≤ b → u ∈ natAP a d k → u ∈ natAP b d m →
      ∃ l : ℕ∞, ((natAP a d k ∪ natAP b d m : Finset ℕ) : Set ℕ).IsAPOfLength l by
    rcases le_total a b with hab | hba
    · exact this a b k m hab huS huT
    · simpa only [Finset.union_comm] using this b a m k hba huT huS
  intro a b k m hab huS huT
  obtain ⟨i, hi, hui⟩ := mem_natAP.mp huS
  obtain ⟨j, hj, huj⟩ := mem_natAP.mp huT
  have hji : j ≤ i := by
    by_contra hh
    have hmul := Nat.mul_lt_mul_of_pos_right (Nat.lt_of_not_ge hh) hd
    omega
  have hb : b = a + (i - j) * d := by
    have hsub : j + (i - j) = i := Nat.add_sub_of_le hji
    nlinarith
  have ht : i - j < k := by omega
  rw [hb, natAP_union_overlap a d k (i - j) m ht]
  exact ⟨_, natAP_isAP hd⟩

theorem isAP_union_of_consecutive {S T : Finset ℕ} {u v : ℕ}
    (hS : ∃ l : ℕ∞, (S : Set ℕ).IsAPOfLength l)
    (hT : ∃ l : ℕ∞, (T : Set ℕ).IsAPOfLength l)
    (hconS : ConsecutiveIn S u v) (hconT : ConsecutiveIn T u v) :
    ∃ l : ℕ∞, ((S ∪ T : Finset ℕ) : Set ℕ).IsAPOfLength l := by
  obtain ⟨lS, hS⟩ := hS
  obtain ⟨lT, hT⟩ := hT
  obtain ⟨a, hSa⟩ := nat_ap_eq_with_consecutive_gap hS hconS
  obtain ⟨b, hTb⟩ := nat_ap_eq_with_consecutive_gap hT hconT
  have hd : 0 < v - u := Nat.sub_pos_of_lt hconS.2.2.1
  rw [hSa, hTb]
  exact natAP_union_isAP_of_common_point hd (hSa ▸ hconS.1) (hTb ▸ hconT.1)

end
section
open Finset

def IsCrooked (S : Finset ℕ) : Prop :=
  ¬ ∃ l : ℕ∞, (S : Set ℕ).IsAPOfLength l

def FixedGapAP (u v : ℕ) (S : Finset ℕ) : Prop :=
  S = ∅ ∨ ((∃ l : ℕ∞, (S : Set ℕ).IsAPOfLength l) ∧ ConsecutiveIn S u v)

theorem fixedGapAP_empty (u v : ℕ) : FixedGapAP u v ∅ := Or.inl rfl

theorem fixedGapAP_union {u v : ℕ} {S T : Finset ℕ}
    (hS : FixedGapAP u v S) (hT : FixedGapAP u v T) : FixedGapAP u v (S ∪ T) := by
  rcases hS with rfl | ⟨hAPs, hcons⟩
  · simpa using hT
  rcases hT with rfl | ⟨hAPt, hcont⟩
  · simpa [FixedGapAP] using Or.inr (And.intro hAPs hcons)
  · exact Or.inr ⟨isAP_union_of_consecutive hAPs hAPt hcons hcont, hcons.union hcont⟩

theorem union_closed_biUnion {α β : Type*} [DecidableEq α] {C : Finset α → Prop}
    (hzero : C ∅) (hunion : ∀ S T, C S → C T → C (S ∪ T))
    (B : Finset β) (f : β → Finset α) (hf : ∀ b ∈ B, C (f b)) : C (B.biUnion f) := by
  classical
  induction B using Finset.induction_on with
  | empty => simpa using hzero
  | @insert b B hb ih =>
    rw [Finset.biUnion_insert]
    exact hunion _ _ (hf b (Finset.mem_insert_self _ _))
      (ih (fun c hc => hf c (Finset.mem_insert_of_mem hc)))

theorem private_points_of_union_closed {α : Type*} [DecidableEq α]
    {F : Finset (Finset α)} {C : Finset α → Prop}
    (hzero : C ∅) (hunion : ∀ S T, C S → C T → C (S ∪ T))
    (hnot : ∀ S ∈ F, ¬ C S)
    (hinter : (F : Set (Finset α)).Pairwise (fun S T => C (S ∩ T))) :
    ∀ S ∈ F, ∃ x ∈ S, ∀ T ∈ F, x ∈ T → T = S := by
  classical
  intro S hS
  let U := (F.erase S).biUnion (fun T => S ∩ T)
  have hUC : C U := union_closed_biUnion hzero hunion _ _ (by
    intro T hT
    obtain ⟨hne, hTF⟩ := Finset.mem_erase.mp hT
    exact hinter hS hTF (fun hST => hne hST.symm))
  have hUsub : U ⊆ S := by
    intro x hx
    obtain ⟨T, hT, hxST⟩ := Finset.mem_biUnion.mp hx
    exact (Finset.mem_inter.mp hxST).1
  have hnotSub : ¬ S ⊆ U := by
    intro hSU
    have heq : S = U := Finset.Subset.antisymm hSU hUsub
    exact hnot S hS (heq.symm ▸ hUC)
  obtain ⟨x, hxS, hxU⟩ := Finset.not_subset.mp hnotSub
  refine ⟨x, hxS, ?_⟩
  intro T hT hxT
  by_contra hne
  apply hxU
  exact Finset.mem_biUnion.mpr ⟨T, Finset.mem_erase.mpr ⟨hne, hT⟩,
    Finset.mem_inter.mpr ⟨hxS, hxT⟩⟩

theorem card_le_of_private_points {α : Type*} [DecidableEq α]
    {F : Finset (Finset α)} {U : Finset α}
    (hsub : ∀ S ∈ F, S ⊆ U)
    (hprivate : ∀ S ∈ F, ∃ x ∈ S, ∀ T ∈ F, x ∈ T → T = S) : F.card ≤ U.card := by
  classical
  choose x hx hpriv using (fun S : {S // S ∈ F} => hprivate S.val S.property)
  have hmaps : Set.MapsTo x
      ((Finset.univ : Finset {S // S ∈ F}) : Set {S // S ∈ F}) (U : Set α) := by
    intro S hS
    exact hsub S.val S.property (hx S)
  have hinj : Function.Injective x := by
    intro S T heq
    apply Subtype.ext
    exact (hpriv S T.val T.property (by simpa only [heq] using hx T)).symm
  have hc := Finset.card_le_card_of_injOn x hmaps hinj.injOn
  simpa using hc

theorem arithInterSet_mono {N : ℕ} {F G : Finset (Finset ℕ)}
    (hF : Erdos272.IsArithInterSet N F) (hGF : G ⊆ F) : Erdos272.IsArithInterSet N G := by
  refine ⟨hGF.trans hF.1, ?_⟩
  intro S hS T hT hne
  exact hF.2 (hGF hS) (hGF hT) hne

/-- At most `N` crooked members can have one specified consecutive pair. -/
theorem crooked_consecutive_card_le {N u v : ℕ} {F : Finset (Finset ℕ)}
    (hF : Erdos272.IsArithInterSet N F)
    (hcrooked : ∀ S ∈ F, IsCrooked S)
    (hconsecutive : ∀ S ∈ F, ConsecutiveIn S u v) : F.card ≤ N := by
  have hprivate : ∀ S ∈ F, ∃ x ∈ S, ∀ T ∈ F, x ∈ T → T = S := by
    apply private_points_of_union_closed (C := FixedGapAP u v) (fixedGapAP_empty u v)
      (fun S T hS hT => fixedGapAP_union hS hT)
    · intro S hS hclass
      rcases hclass with heq | ⟨hAP, hcon⟩
      · have hu := (hconsecutive S hS).1
        simp [heq] at hu
      · exact hcrooked S hS hAP
    · intro S hS T hT hne
      obtain ⟨l, hl, hAP⟩ := hF.2 hS hT hne
      exact Or.inr ⟨⟨l, hAP⟩,
        (hconsecutive S hS).inter (hconsecutive T hT).1 (hconsecutive T hT).2.1⟩
  have hc := card_le_of_private_points
    (fun S hS => Finset.mem_powerset.mp (hF.1 hS)) hprivate
  simpa using hc

end
section
open Finset

noncomputable def blockMinima (S : Finset ℕ) : Finset ℕ := by
  classical
  exact S.filter (fun x => ∀ y ∈ S, y / 32 = x / 32 → x ≤ y)

def ShortConsecutive (S : Finset ℕ) (p : ℕ × ℕ) : Prop :=
  ConsecutiveIn S p.1 p.2 ∧ p.2 - p.1 ≤ 32

noncomputable def shortPairs (S : Finset ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact (S ×ˢ S).filter (ShortConsecutive S)

theorem card_blockMinima_le {N : ℕ} {S : Finset ℕ} (hsub : S ⊆ Finset.Icc 1 N) :
    (blockMinima S).card ≤ N / 32 + 1 := by
  classical
  have hmaps : Set.MapsTo (fun x : ℕ => x / 32) (blockMinima S : Set ℕ)
      (Finset.Icc 0 (N / 32) : Set ℕ) := by
    intro x hx
    have hxS := (Finset.mem_filter.mp hx).1
    have hxN := (Finset.mem_Icc.mp (hsub hxS)).2
    exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, Nat.div_le_div_right hxN⟩
  have hinj : Set.InjOn (fun x : ℕ => x / 32) (blockMinima S : Set ℕ) := by
    intro x hx y hy hxy
    obtain ⟨hxS, hxMin⟩ := Finset.mem_filter.mp hx
    obtain ⟨hyS, hyMin⟩ := Finset.mem_filter.mp hy
    exact le_antisymm (hxMin y hyS hxy.symm) (hyMin x hxS hxy)
  simpa using Finset.card_le_card_of_injOn (fun x : ℕ => x / 32) hmaps hinj

theorem short_pair_ending_at_nonminimum {S : Finset ℕ} {x : ℕ}
    (hxS : x ∈ S) (hxMin : x ∉ blockMinima S) : ∃ z, (z, x) ∈ shortPairs S := by
  classical
  have hnot : ¬ ∀ y ∈ S, y / 32 = x / 32 → x ≤ y := by
    intro h
    exact hxMin (Finset.mem_filter.mpr ⟨hxS, h⟩)
  push Not at hnot
  obtain ⟨y, hyS, hquot, hyx⟩ := hnot
  let B := S.filter (fun z => z < x)
  have hyB : y ∈ B := Finset.mem_filter.mpr ⟨hyS, hyx⟩
  have hB : B.Nonempty := ⟨y, hyB⟩
  let z := B.max' hB
  have hzB : z ∈ B := Finset.max'_mem B hB
  obtain ⟨hzS, hzx⟩ := Finset.mem_filter.mp hzB
  have hyz : y ≤ z := Finset.le_max' B y hyB
  have hcon : ConsecutiveIn S z x := by
    refine ⟨hzS, hxS, hzx, ?_⟩
    intro w hw hbetween
    have hwB : w ∈ B := Finset.mem_filter.mpr ⟨hw, hbetween.2⟩
    have hwz : w ≤ z := Finset.le_max' B w hwB
    omega
  have hxmod := Nat.mod_add_div x 32
  have hmodlt := Nat.mod_lt x (by decide : 0 < 32)
  have hydiv := Nat.div_mul_le_self y 32
  have hgap : x - z ≤ 32 := by omega
  exact ⟨z, Finset.mem_filter.mpr
    ⟨Finset.mem_product.mpr ⟨hzS, hxS⟩, hcon, hgap⟩⟩

theorem card_nonminima_le_shortPairs (S : Finset ℕ) :
    (S \ blockMinima S).card ≤ (shortPairs S).card := by
  classical
  choose z hz using (fun x : {x // x ∈ S \ blockMinima S} =>
    short_pair_ending_at_nonminimum (Finset.mem_sdiff.mp x.property).1
      (Finset.mem_sdiff.mp x.property).2)
  have hmaps : Set.MapsTo (fun x : {x // x ∈ S \ blockMinima S} => (z x, x.val))
      ((Finset.univ : Finset {x // x ∈ S \ blockMinima S}) : Set {x // x ∈ S \ blockMinima S})
      (shortPairs S : Set (ℕ × ℕ)) := by
    intro x hx
    exact hz x
  have hinj : Function.Injective (fun x : {x // x ∈ S \ blockMinima S} => (z x, x.val)) := by
    intro x y hxy
    exact Subtype.ext (congrArg Prod.snd hxy)
  simpa using Finset.card_le_card_of_injOn _ hmaps hinj.injOn

theorem card_le_shortPairs_add_blocks {N : ℕ} {S : Finset ℕ}
    (hsub : S ⊆ Finset.Icc 1 N) : S.card ≤ (shortPairs S).card + (N / 32 + 1) := by
  classical
  have hminsub : blockMinima S ⊆ S := Finset.filter_subset _ _
  have hcard := Finset.card_sdiff_add_card_eq_card hminsub
  have hnon := card_nonminima_le_shortPairs S
  have hmin := card_blockMinima_le hsub
  omega

theorem dense_set_many_short_pairs {N : ℕ} {S : Finset ℕ}
    (hN : 64 ≤ N) (hsub : S ⊆ Finset.Icc 1 N) (hsize : N < 16 * S.card) :
    N ≤ 64 * (shortPairs S).card := by
  have hcard := card_le_shortPairs_add_blocks hsub
  have hdiv := Nat.div_mul_le_self N 32
  omega

def shortPairUniverse (N : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 32)).image (fun p => (p.1, p.1 + p.2))

theorem card_shortPairUniverse (N : ℕ) : (shortPairUniverse N).card = 32 * N := by
  have hinj : Function.Injective (fun p : ℕ × ℕ => (p.1, p.1 + p.2)) := by
    rintro ⟨a, d⟩ ⟨b, e⟩ heq
    have h₁ : a = b := congrArg Prod.fst heq
    have h₂ : a + d = b + e := congrArg Prod.snd heq
    exact Prod.ext h₁ (by omega)
  simp [shortPairUniverse, Finset.card_image_of_injective _ hinj, Nat.mul_comm]

theorem shortConsecutive_mem_universe {N : ℕ} {S : Finset ℕ} {p : ℕ × ℕ}
    (hsub : S ⊆ Finset.Icc 1 N) (hp : ShortConsecutive S p) : p ∈ shortPairUniverse N := by
  rcases p with ⟨u, v⟩
  have huI := hsub hp.1.1
  have huv := hp.1.2.2.1
  have hgap := hp.2
  exact Finset.mem_image.mpr ⟨(u, v - u), Finset.mem_product.mpr
    ⟨huI, Finset.mem_Icc.mpr ⟨by omega, hgap⟩⟩, Prod.ext rfl (by omega)⟩

theorem shortPairs_eq_bipartiteAbove {N : ℕ} {S : Finset ℕ}
    (hsub : S ⊆ Finset.Icc 1 N) :
    (by
      classical
      exact shortPairs S = Finset.bipartiteAbove ShortConsecutive (shortPairUniverse N) S) := by
  classical
  ext p
  simp only [shortPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_bipartiteAbove]
  constructor
  · rintro ⟨hmem, hrel⟩
    exact ⟨shortConsecutive_mem_universe hsub hrel, hrel⟩
  · rintro ⟨hU, hrel⟩
    exact ⟨⟨hrel.1.1, hrel.1.2.1⟩, hrel⟩

/-- The dense crooked members contribute only a linear number of sets. -/
theorem dense_crooked_card_le {N : ℕ} {F : Finset (Finset ℕ)}
    (hN : 64 ≤ N) (hF : Erdos272.IsArithInterSet N F)
    (hcrooked : ∀ S ∈ F, IsCrooked S)
    (hsize : ∀ S ∈ F, N < 16 * S.card) : F.card ≤ 2048 * N := by
  classical
  have hsub : ∀ S ∈ F, S ⊆ Finset.Icc 1 N :=
    fun S hS => Finset.mem_powerset.mp (hF.1 hS)
  have hlow : F.card * N ≤ 64 * ∑ S ∈ F, (shortPairs S).card := by
    have hh := Finset.sum_le_sum (s := F)
      (fun S hS => dense_set_many_short_pairs hN (hsub S hS) (hsize S hS))
    simpa [← Finset.mul_sum] using hh
  have hdouble : (∑ S ∈ F, (shortPairs S).card) =
      ∑ p ∈ shortPairUniverse N, (Finset.bipartiteBelow ShortConsecutive F p).card := by
    calc
      _ = ∑ S ∈ F, (Finset.bipartiteAbove ShortConsecutive (shortPairUniverse N) S).card :=
        Finset.sum_congr rfl (fun S hS => congrArg Finset.card (shortPairs_eq_bipartiteAbove (hsub S hS)))
      _ = _ := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow ShortConsecutive
  have hbelow : ∀ p ∈ shortPairUniverse N,
      (Finset.bipartiteBelow ShortConsecutive F p).card ≤ N := by
    intro p hp
    have hBF : Finset.bipartiteBelow ShortConsecutive F p ⊆ F := Finset.filter_subset _ _
    apply crooked_consecutive_card_le (u := p.1) (v := p.2) (arithInterSet_mono hF hBF)
    · intro S hS
      exact hcrooked S (hBF hS)
    · intro S hS
      exact ((Finset.mem_bipartiteBelow ShortConsecutive).mp hS).2.1
  have hupp : (∑ p ∈ shortPairUniverse N,
      (Finset.bipartiteBelow ShortConsecutive F p).card) ≤ (shortPairUniverse N).card * N := by
    simpa using Finset.sum_le_sum hbelow
  rw [hdouble] at hlow
  rw [card_shortPairUniverse] at hupp
  have hfinal : F.card * N ≤ (2048 * N) * N := by nlinarith
  exact Nat.le_of_mul_le_mul_right hfinal (by omega)

end
section
open Finset

theorem finset_ap_image_of_map_progressions {α β : Type*}
    [AddCommMonoid α] [AddCommMonoid β] [DecidableEq α] [DecidableEq β]
    {S : Finset α} {l : ℕ∞} (f g : α → β) (hinj : Function.Injective f)
    (hmap : ∀ (a d : α) (n : ℕ), f (a + n • d) = f a + n • g d)
    (hAP : (S : Set α).IsAPOfLength l) :
    ((S.image f : Finset β) : Set β).IsAPOfLength l := by
  obtain ⟨a, d, hAP⟩ := hAP
  refine ⟨f a, g d, ?_, ?_⟩
  · simpa [Finset.card_image_of_injective _ hinj] using hAP.card
  · ext y
    rw [Finset.coe_image]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [hAP.eq] at hx
      obtain ⟨n, hn, rfl⟩ := hx
      exact ⟨n, hn, (hmap a d n).symm⟩
    · rintro ⟨n, hn, hy⟩
      refine ⟨a + n • d, ?_, ?_⟩
      · rw [hAP.eq]
        exact ⟨n, hn, rfl⟩
      · exact (hmap a d n).trans hy

theorem nat_ap_cast_int {S : Finset ℕ} {l : ℕ∞} (hAP : (S : Set ℕ).IsAPOfLength l) :
    (((S.image (fun x : ℕ => (x : ℤ))) : Finset ℤ) : Set ℤ).IsAPOfLength l := by
  apply finset_ap_image_of_map_progressions
    (fun x : ℕ => (x : ℤ)) (fun x : ℕ => (x : ℤ)) Nat.cast_injective
    (fun a d n => by simp) hAP

theorem int_ap_affine_image {S : Finset ℤ} {l : ℕ∞} {c d : ℤ}
    (hd : d ≠ 0) (hAP : (S : Set ℤ).IsAPOfLength l) :
    (((S.image (fun x => c + d * x)) : Finset ℤ) : Set ℤ).IsAPOfLength l := by
  apply finset_ap_image_of_map_progressions (fun x => c + d * x) (fun x => d * x)
    (fun x y hxy => mul_left_cancel₀ hd (add_left_cancel hxy))
    (fun a b n => by simp only [nsmul_eq_mul]; ring) hAP

theorem natAP_cast_eq_affine_interval (a d k i : ℕ) (hi : i < k) :
    (natAP a d k).image (fun x : ℕ => (x : ℤ)) =
      (Finset.Icc (-(i : ℤ)) ((k - 1 - i : ℕ) : ℤ)).image
        (fun z => ((a + i * d : ℕ) : ℤ) + (d : ℤ) * z) := by
  have hr : (k - 1 - i) + i + 1 = k := by omega
  have hrI : ((k - 1 - i : ℕ) : ℤ) + (i : ℤ) + 1 = (k : ℤ) := by exact_mod_cast hr
  ext x
  constructor
  · intro hx
    obtain ⟨n, hn, hnx⟩ := Finset.mem_image.mp hx
    obtain ⟨j, hj, hnj⟩ := mem_natAP.mp hn
    refine Finset.mem_image.mpr ⟨(j : ℤ) - (i : ℤ), Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
    rw [← hnx, ← hnj]
    push_cast
    ring
  · intro hx
    obtain ⟨z, hz, hzx⟩ := Finset.mem_image.mp hx
    obtain ⟨hzlo, hzhi⟩ := Finset.mem_Icc.mp hz
    have hznonneg : 0 ≤ z + (i : ℤ) := by omega
    let j := (z + (i : ℤ)).toNat
    have hji : (j : ℤ) = z + (i : ℤ) := Int.toNat_of_nonneg hznonneg
    have hj : j < k := by omega
    refine Finset.mem_image.mpr ⟨a + j * d, mem_natAP.mpr ⟨j, hj, rfl⟩, ?_⟩
    rw [← hzx]
    push_cast
    rw [hji]
    ring

def IsCenteredModel (c d : ℕ) (p : ProgressionCell) (S : Finset ℕ) : Prop :=
  S.image (fun x : ℕ => (x : ℤ)) =
    (Finset.Icc (-(p.val.1 : ℤ)) (p.val.2 : ℤ)).image (fun z => (c : ℤ) + (d : ℤ) * z)

theorem exists_centered_model {S : Finset ℕ} {l : ℕ∞} {c : ℕ}
    (hAP : (S : Set ℕ).IsAPOfLength l) (hcard : 4 ≤ S.card) (hc : c ∈ S) :
    ∃ d : ℕ, 0 < d ∧ ∃ p : ProgressionCell, IsCenteredModel c d p S := by
  obtain ⟨a, d, hd, heq⟩ := nat_ap_eq_natAP hAP (by omega)
  obtain ⟨i, hi, hci⟩ := mem_natAP.mp (heq ▸ hc)
  refine ⟨d, hd, ⟨(i, S.card - 1 - i), by omega⟩, ?_⟩
  change S.image (fun x : ℕ => (x : ℤ)) = _
  have hcast := congrArg (fun T : Finset ℕ => T.image (fun x : ℕ => (x : ℤ))) heq
  exact hcast.trans (by simpa only [hci] using natAP_cast_eq_affine_interval a d S.card i hi)

theorem exists_centered_model_bounded {N : ℕ} {S : Finset ℕ} {l : ℕ∞} {c : ℕ}
    (hsub : S ⊆ Finset.Icc 1 N) (hAP : (S : Set ℕ).IsAPOfLength l)
    (hcard : 4 ≤ S.card) (hc : c ∈ S) :
    ∃ d : ℕ, 0 < d ∧ d ≤ N ∧ ∃ p : ProgressionCell, IsCenteredModel c d p S := by
  obtain ⟨a, d, hd, heq⟩ := nat_ap_eq_natAP hAP (by omega)
  have hstep : a + d ∈ S := by
    rw [heq]
    exact mem_natAP.mpr ⟨1, by omega, by simp⟩
  have hdN : d ≤ N := by have hh := (Finset.mem_Icc.mp (hsub hstep)).2; omega
  obtain ⟨i, hi, hci⟩ := mem_natAP.mp (heq ▸ hc)
  refine ⟨d, hd, hdN, ⟨(i, S.card - 1 - i), by omega⟩, ?_⟩
  change S.image (fun x : ℕ => (x : ℤ)) = _
  have hcast := congrArg (fun T : Finset ℕ => T.image (fun x : ℕ => (x : ℤ))) heq
  exact hcast.trans (by simpa only [hci] using natAP_cast_eq_affine_interval a d S.card i hi)

theorem centered_model_determines_set {c d : ℕ} {p : ProgressionCell} {S T : Finset ℕ}
    (hS : IsCenteredModel c d p S) (hT : IsCenteredModel c d p T) : S = T := by
  have heq : S.image (fun x : ℕ => (x : ℤ)) = T.image (fun x : ℕ => (x : ℤ)) := hS.trans hT.symm
  exact (Finset.image_injective (f := fun x : ℕ => (x : ℤ)) Nat.cast_injective) heq

end
section
open Finset

def liftPair (c d : ℕ) (q : ℤ × ℤ) : ℕ × ℕ :=
  (((c : ℤ) + (d : ℤ) * q.1).toNat, ((c : ℤ) + (d : ℤ) * q.2).toNat)

theorem centered_point_mem {c d : ℕ} {p : ProgressionCell} {S : Finset ℕ}
    (hmodel : IsCenteredModel c d p S) {z : ℤ}
    (hz : z ∈ Finset.Icc (-(p.val.1 : ℤ)) (p.val.2 : ℤ)) :
    ((c : ℤ) + (d : ℤ) * z).toNat ∈ S ∧
      (((c : ℤ) + (d : ℤ) * z).toNat : ℤ) = (c : ℤ) + (d : ℤ) * z := by
  have himage : (c : ℤ) + (d : ℤ) * z ∈ S.image (fun x : ℕ => (x : ℤ)) := by
    rw [hmodel]
    exact Finset.mem_image.mpr ⟨z, hz, rfl⟩
  obtain ⟨x, hx, heq⟩ := Finset.mem_image.mp himage
  constructor
  · simpa only [← heq, Int.toNat_natCast] using hx
  · simp only [← heq, Int.toNat_natCast]

theorem primitive_pair_coordinates {p : ProgressionCell} {q : ℤ × ℤ}
    (h : PrimitiveBadPair p q) :
    q.1 ∈ Finset.Icc (-(p.val.1 : ℤ)) (p.val.2 : ℤ) ∧
      q.2 ∈ Finset.Icc (-(p.val.1 : ℤ)) (p.val.2 : ℤ) := by
  exact ⟨Finset.mem_Icc.mpr ⟨h.1, h.2.1.le.trans h.2.2.1⟩,
    Finset.mem_Icc.mpr ⟨h.1.trans h.2.1.le, h.2.2.1⟩⟩

theorem scaled_primitive_triple_not_isAP {p : ProgressionCell} {q : ℤ × ℤ}
    (h : PrimitiveBadPair p q) {d : ℤ} (hd : d ≠ 0) :
    ¬ ∃ l : ℕ∞, (({0, d * q.1, d * q.2} : Finset ℤ) : Set ℤ).IsAPOfLength l := by
  rcases h with ⟨hleft, hlt, hright, hu, hv, hcop, hadd, hdu, hdv⟩
  apply not_isAP_triple_of_relations (mul_ne_zero hd hu) (mul_ne_zero hd hv)
    (fun heq => hlt.ne (mul_left_cancel₀ hd heq))
  · rw [← mul_add]
    exact mul_ne_zero hd hadd
  · intro heq
    apply hdu
    apply mul_left_cancel₀ hd
    calc
      d * (2 * q.1) = 2 * (d * q.1) := by ring
      _ = d * q.2 := heq
  · intro heq
    apply hdv
    apply mul_left_cancel₀ hd
    calc
      d * q.1 = 2 * (d * q.2) := heq
      _ = d * (2 * q.2) := by ring

def NaturalMatchedPair (c d : ℕ) (S : Finset ℕ) (q : ℕ × ℕ) : Prop :=
  q.1 ∈ S ∧ q.2 ∈ S ∧ q.1 < q.2 ∧ q.1 ≠ c ∧ q.2 ≠ c ∧
    Int.gcd ((q.1 : ℤ) - (c : ℤ)) ((q.2 : ℤ) - (c : ℤ)) = d ∧
      ¬ ∃ l : ℕ∞, (({c, q.1, q.2} : Finset ℕ) : Set ℕ).IsAPOfLength l

theorem liftPair_spec {c d : ℕ} {S : Finset ℕ} {p : ProgressionCell} {q : ℤ × ℤ}
    (hd : 0 < d) (hmodel : IsCenteredModel c d p S) (hpair : PrimitiveBadPair p q) :
    NaturalMatchedPair c d S (liftPair c d q) := by
  have hcoords := primitive_pair_coordinates hpair
  obtain ⟨hxS, hxcast⟩ := centered_point_mem hmodel hcoords.1
  obtain ⟨hyS, hycast⟩ := centered_point_mem hmodel hcoords.2
  have hdI : (0 : ℤ) < d := by exact_mod_cast hd
  have hdi : (d : ℤ) ≠ 0 := hdI.ne'
  rcases hpair with ⟨hleft, hlt, hright, hu, hv, hcop, hadd, hdu, hdv⟩
  have hxy : ((c : ℤ) + (d : ℤ) * q.1).toNat <
      ((c : ℤ) + (d : ℤ) * q.2).toNat := by
    have hmul := mul_lt_mul_of_pos_left hlt hdI
    omega
  have hxc : ((c : ℤ) + (d : ℤ) * q.1).toNat ≠ c := by
    intro heq
    have hzero : (d : ℤ) * q.1 = 0 := by omega
    exact hu ((mul_eq_zero.mp hzero).resolve_left hdi)
  have hyc : ((c : ℤ) + (d : ℤ) * q.2).toNat ≠ c := by
    intro heq
    have hzero : (d : ℤ) * q.2 = 0 := by omega
    exact hv ((mul_eq_zero.mp hzero).resolve_left hdi)
  have hdiffx : (((c : ℤ) + (d : ℤ) * q.1).toNat : ℤ) - (c : ℤ) = (d : ℤ) * q.1 := by omega
  have hdiffy : (((c : ℤ) + (d : ℤ) * q.2).toNat : ℤ) - (c : ℤ) = (d : ℤ) * q.2 := by omega
  refine ⟨hxS, hyS, hxy, hxc, hyc, ?_, ?_⟩
  · dsimp only [liftPair]
    rw [hdiffx, hdiffy, Int.gcd_mul_left, Int.natAbs_natCast, Int.gcd_def]
    have hg : q.1.natAbs.gcd q.2.natAbs = 1 := hcop
    rw [hg, Nat.mul_one]
  · rintro ⟨l, hAP⟩
    have hcast := nat_ap_cast_int hAP
    have hshift := int_ap_affine_image (c := -(c : ℤ)) (d := 1) (by decide) hcast
    have hscaled : (({0, (d : ℤ) * q.1, (d : ℤ) * q.2} : Finset ℤ) : Set ℤ).IsAPOfLength l := by
      simpa [liftPair, hxcast, hycast] using hshift
    exact scaled_primitive_triple_not_isAP
      ⟨hleft, hlt, hright, hu, hv, hcop, hadd, hdu, hdv⟩ hdi ⟨l, hscaled⟩

theorem liftPair_injective_on_models {c d : ℕ} {S T : Finset ℕ}
    {p p' : ProgressionCell} {q q' : ℤ × ℤ}
    (hd : 0 < d) (hS : IsCenteredModel c d p S) (hT : IsCenteredModel c d p' T)
    (hq : PrimitiveBadPair p q) (hq' : PrimitiveBadPair p' q')
    (heq : liftPair c d q = liftPair c d q') : q = q' := by
  have hcs := primitive_pair_coordinates hq
  have hct := primitive_pair_coordinates hq'
  have hx := (centered_point_mem hS hcs.1).2
  have hy := (centered_point_mem hS hcs.2).2
  have hx' := (centered_point_mem hT hct.1).2
  have hy' := (centered_point_mem hT hct.2).2
  have hfst := congrArg (fun r : ℕ × ℕ => (r.1 : ℤ)) heq
  have hsnd := congrArg (fun r : ℕ × ℕ => (r.2 : ℤ)) heq
  change (((c : ℤ) + (d : ℤ) * q.1).toNat : ℤ) =
    (((c : ℤ) + (d : ℤ) * q'.1).toNat : ℤ) at hfst
  change (((c : ℤ) + (d : ℤ) * q.2).toNat : ℤ) =
    (((c : ℤ) + (d : ℤ) * q'.2).toNat : ℤ) at hsnd
  rw [hx, hx'] at hfst
  rw [hy, hy'] at hsnd
  have hdI : (d : ℤ) ≠ 0 := by exact_mod_cast hd.ne'
  exact Prod.ext (mul_left_cancel₀ hdI (add_left_cancel hfst))
    (mul_left_cancel₀ hdI (add_left_cancel hsnd))

end
section
open Finset

theorem exists_natural_progression_pair_matching {N c : ℕ} {F : Finset (Finset ℕ)}
    (hsub : ∀ S ∈ F, S ⊆ Finset.Icc 1 N)
    (hAP : ∀ S ∈ F, ∃ l : ℕ∞, (S : Set ℕ).IsAPOfLength l)
    (hcard : ∀ S ∈ F, 4 ≤ S.card) (hcenter : ∀ S ∈ F, c ∈ S) :
    ∃ f : {S // S ∈ F} → Option (ℕ × ℕ),
      (∀ S q, f S = some q → ∃ d : ℕ, 0 < d ∧ d ≤ N ∧ NaturalMatchedPair c d S.val q) ∧
      (∀ S T q, f S = some q → f T = some q → S = T) ∧
      ((Finset.univ.filter (fun S => f S = none)).card ≤ 20000 * N) := by
  classical
  let A := {S : Finset ℕ // S ∈ F}
  have hparam : ∀ S : A, ∃ d : ℕ, 0 < d ∧ d ≤ N ∧
      ∃ p : ProgressionCell, IsCenteredModel c d p S.val := by
    intro S
    obtain ⟨l, hAPs⟩ := hAP S.val S.property
    exact exists_centered_model_bounded (hsub S.val S.property) hAPs
      (hcard S.val S.property) (hcenter S.val S.property)
  choose d hd hdN p hmodel using hparam
  obtain ⟨f, hreal, hrealinj, hexcept⟩ := exists_progression_pair_matching
  let g : A → Option (ℕ × ℕ) := fun S => (f (p S)).map (liftPair c (d S))
  have hvalid : ∀ S q, g S = some q → NaturalMatchedPair c (d S) S.val q := by
    intro S q hq
    obtain ⟨r, hr, hrq⟩ := Option.map_eq_some_iff.mp hq
    rw [← hrq]
    exact liftPair_spec (hd S) (hmodel S) (hreal (p S) r hr)
  refine ⟨g, ?_, ?_, ?_⟩
  · intro S q hq
    exact ⟨d S, hd S, hdN S, hvalid S q hq⟩
  · intro S T q hSq hTq
    have hSvalid := hvalid S q hSq
    have hTvalid := hvalid T q hTq
    have hdST : d S = d T := hSvalid.2.2.2.2.2.1.symm.trans hTvalid.2.2.2.2.2.1
    obtain ⟨r, hr, hrq⟩ := Option.map_eq_some_iff.mp hSq
    obtain ⟨r', hr', hr'q⟩ := Option.map_eq_some_iff.mp hTq
    have hlifts : liftPair c (d T) r = liftPair c (d T) r' := by
      simpa only [hdST] using hrq.trans hr'q.symm
    have hrr' : r = r' := liftPair_injective_on_models (hd T)
      (by simpa only [hdST] using hmodel S) (hmodel T)
      (hreal (p S) r hr) (hreal (p T) r' hr') hlifts
    have hpST : p S = p T := hrealinj (p S) (p T) r hr (by simpa only [hrr'] using hr')
    apply Subtype.ext
    exact centered_model_determines_set
      (by simpa only [hdST, hpST] using hmodel S) (hmodel T)
  · let B : Finset A := Finset.univ.filter (fun S => g S = none)
    have hmaps : Set.MapsTo d (B : Set A) (Finset.Icc 1 N : Set ℕ) := by
      intro S hS
      exact Finset.mem_Icc.mpr ⟨hd S, hdN S⟩
    have hfiber : ∀ k ∈ Finset.Icc 1 N, (B.filter (fun S => d S = k)).card ≤ 20000 := by
      intro k hk
      let C := B.filter (fun S => d S = k)
      have hpinj : Set.InjOn p (C : Set A) := by
        intro S hS T hT hpST
        have hdSk : d S = k := (Finset.mem_filter.mp hS).2
        have hdTk : d T = k := (Finset.mem_filter.mp hT).2
        apply Subtype.ext
        exact centered_model_determines_set
          (by simpa only [hdSk] using hmodel S)
          (by simpa only [hdTk, ← hpST] using hmodel T)
      have hfilter : (C.image p).filter (fun q => f q = none) = C.image p := by
        apply Finset.filter_eq_self.mpr
        intro q hq
        obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hq
        have hSB : S ∈ B := (Finset.mem_filter.mp hS).1
        have hnone : g S = none := (Finset.mem_filter.mp hSB).2
        exact Option.map_eq_none_iff.mp hnone
      have hh := hexcept (C.image p)
      rw [hfilter, Finset.card_image_of_injOn hpinj] at hh
      exact hh
    change B.card ≤ 20000 * N
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    calc
      _ ≤ ∑ k ∈ Finset.Icc 1 N, 20000 := Finset.sum_le_sum hfiber
      _ = 20000 * N := by simp [Nat.mul_comm]

end
section
open Finset

def HasAPCover (S T : Finset ℕ) : Prop :=
  ∃ A : Finset ℕ, A ⊆ S ∧ (∃ l : ℕ∞, (A : Set ℕ).IsAPOfLength l) ∧ T ⊆ A

def IsWitnessPair (S : Finset ℕ) (c : ℕ) (P : Finset ℕ) : Prop :=
  P.card = 2 ∧ P ⊆ S.erase c ∧ ¬ HasAPCover S (insert c P)

theorem ConsecutiveIn.subset {S T : Finset ℕ} {u v : ℕ}
    (h : ConsecutiveIn S u v) (hTS : T ⊆ S) (hu : u ∈ T) (hv : v ∈ T) :
    ConsecutiveIn T u v :=
  ⟨hu, hv, h.2.2.1, fun x hx => h.2.2.2 x (hTS hx)⟩

/-- An adjacent pair has a third point which no contained progression can cover. -/
theorem consecutive_has_missing_cover {S : Finset ℕ} {u v : ℕ}
    (hcrooked : IsCrooked S) (hcon : ConsecutiveIn S u v) :
    ∃ b ∈ S, b ≠ u ∧ b ≠ v ∧ ¬ HasAPCover S {u, v, b} := by
  classical
  let D : Finset (Finset ℕ) := S.powerset.filter
    (fun T : Finset ℕ => (∃ l : ℕ∞, (T : Set ℕ).IsAPOfLength l) ∧ u ∈ T ∧ v ∈ T)
  let U : Finset ℕ := D.biUnion id
  have hpairS : {u, v} ⊆ S := by simp [Finset.insert_subset_iff, hcon.1, hcon.2.1]
  have hpairAP : (({u, v} : Finset ℕ) : Set ℕ).IsAPOfLength 2 :=
    by simpa using Nat.isAPOfLength_pair hcon.2.2.1
  have hpairD : {u, v} ∈ D := Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr hpairS, ⟨2, hpairAP⟩, by simp, by simp⟩
  have huU : u ∈ U := Finset.mem_biUnion.mpr ⟨{u, v}, hpairD, by simp⟩
  have hvU : v ∈ U := Finset.mem_biUnion.mpr ⟨{u, v}, hpairD, by simp⟩
  have hUclass : FixedGapAP u v U := union_closed_biUnion (fixedGapAP_empty u v)
      (fun S T hS hT => fixedGapAP_union hS hT) D id (by
    intro T hT
    obtain ⟨hTS, hAP, huT, hvT⟩ := Finset.mem_filter.mp hT
    exact Or.inr ⟨hAP, hcon.subset (Finset.mem_powerset.mp hTS) huT hvT⟩)
  have hUAP : ∃ l : ℕ∞, (U : Set ℕ).IsAPOfLength l := by
    rcases hUclass with heq | h
    · simp [heq] at huU
    · exact h.1
  have hUsub : U ⊆ S := by
    intro x hx
    obtain ⟨T, hT, hxT⟩ := Finset.mem_biUnion.mp hx
    exact Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1 hxT
  have hnotSub : ¬ S ⊆ U := by
    intro hSU
    have heq : S = U := Finset.Subset.antisymm hSU hUsub
    exact hcrooked (heq.symm ▸ hUAP)
  obtain ⟨b, hbS, hbU⟩ := Finset.not_subset.mp hnotSub
  refine ⟨b, hbS, ?_, ?_, ?_⟩
  · intro heq
    subst b
    exact hbU huU
  · intro heq
    subst b
    exact hbU hvU
  · rintro ⟨T, hTS, hAP, hcover⟩
    have hTD : T ∈ D := Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr hTS, hAP, hcover (by simp), hcover (by simp)⟩
    exact hbU (Finset.mem_biUnion.mpr ⟨T, hTD, hcover (by simp)⟩)

theorem exists_consecutive_at_mem {S : Finset ℕ} {c : ℕ}
    (hc : c ∈ S) (hcard : 2 ≤ S.card) :
    ∃ a, ConsecutiveIn S a c ∨ ConsecutiveIn S c a := by
  classical
  have herase : (S.erase c).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_erase_of_mem hc]
    omega
  obtain ⟨a, ha⟩ := herase
  obtain ⟨hac, haS⟩ := Finset.mem_erase.mp ha
  rcases lt_or_gt_of_ne hac with hac | hca
  · let B := S.filter (fun x => x < c)
    have haB : a ∈ B := Finset.mem_filter.mpr ⟨haS, hac⟩
    have hB : B.Nonempty := ⟨a, haB⟩
    let b := B.max' hB
    have hbB : b ∈ B := Finset.max'_mem B hB
    obtain ⟨hbS, hbc⟩ := Finset.mem_filter.mp hbB
    refine ⟨b, Or.inl ⟨hbS, hc, hbc, ?_⟩⟩
    intro x hx hbetween
    have hxB : x ∈ B := Finset.mem_filter.mpr ⟨hx, hbetween.2⟩
    have hxb : x ≤ b := Finset.le_max' B x hxB
    omega
  · let B := S.filter (fun x => c < x)
    have haB : a ∈ B := Finset.mem_filter.mpr ⟨haS, hca⟩
    have hB : B.Nonempty := ⟨a, haB⟩
    let b := B.min' hB
    have hbB : b ∈ B := Finset.min'_mem B hB
    obtain ⟨hbS, hcb⟩ := Finset.mem_filter.mp hbB
    refine ⟨b, Or.inr ⟨hc, hbS, hcb, ?_⟩⟩
    intro x hx hbetween
    have hxB : x ∈ B := Finset.mem_filter.mpr ⟨hx, hbetween.1⟩
    have hbx : b ≤ x := Finset.min'_le B x hxB
    omega

theorem crooked_card_ge_two {S : Finset ℕ} {c : ℕ}
    (hcrooked : IsCrooked S) (hc : c ∈ S) : 2 ≤ S.card := by
  by_contra hcard
  have hsmall : S.card ≤ 1 := by omega
  have heq : S = {c} := by
    ext x
    simp only [Finset.mem_singleton]
    exact ⟨fun hx => Finset.card_le_one.mp hsmall x hx c hc, fun hxc => hxc.symm ▸ hc⟩
  apply hcrooked
  refine ⟨1, Set.IsAPOfLength.one.mpr ⟨c, ?_⟩⟩
  simp [heq]

theorem witness_pair_of_right_neighbor {S : Finset ℕ} {c a : ℕ}
    (hcrooked : IsCrooked S) (hcon : ConsecutiveIn S c a) :
    ∃ b, IsWitnessPair S c {a, b} := by
  obtain ⟨b, hbS, hbc, hba, hcover⟩ := consecutive_has_missing_cover hcrooked hcon
  refine ⟨b, ?_⟩
  refine ⟨by simp [hba.symm], ?_, hcover⟩
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact Finset.mem_erase.mpr ⟨hcon.2.2.1.ne', hcon.2.1⟩
  · exact Finset.mem_erase.mpr ⟨hbc, hbS⟩

theorem witness_pair_of_left_neighbor {S : Finset ℕ} {c a : ℕ}
    (hcrooked : IsCrooked S) (hcon : ConsecutiveIn S a c) :
    ∃ b, IsWitnessPair S c {a, b} := by
  obtain ⟨b, hbS, hba, hbc, hcover⟩ := consecutive_has_missing_cover hcrooked hcon
  refine ⟨b, ?_⟩
  have hperm : ({a, c, b} : Finset ℕ) = insert c {a, b} := by
    ext x
    simp [or_left_comm]
  refine ⟨by simp [hba.symm], ?_, by simpa only [hperm] using hcover⟩
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact Finset.mem_erase.mpr ⟨hcon.2.2.1.ne, hcon.1⟩
  · exact Finset.mem_erase.mpr ⟨hbc, hbS⟩

theorem exists_witness_pair {S : Finset ℕ} {c : ℕ}
    (hcrooked : IsCrooked S) (hc : c ∈ S) : ∃ P : Finset ℕ, IsWitnessPair S c P := by
  obtain ⟨a, hcon | hcon⟩ := exists_consecutive_at_mem hc (crooked_card_ge_two hcrooked hc)
  · obtain ⟨b, hb⟩ := witness_pair_of_left_neighbor hcrooked hcon
    exact ⟨{a, b}, hb⟩
  · obtain ⟨b, hb⟩ := witness_pair_of_right_neighbor hcrooked hcon
    exact ⟨{a, b}, hb⟩

theorem witness_pair_private {N c : ℕ} {F : Finset (Finset ℕ)} {S T P : Finset ℕ}
    (hF : Erdos272.IsArithInterSet N F) (hS : S ∈ F) (hT : T ∈ F)
    (hcS : c ∈ S) (hcT : c ∈ T) (hW : IsWitnessPair S c P) (hPT : P ⊆ T) : T = S := by
  by_contra hne
  obtain ⟨l, hl, hAP⟩ := hF.2 hS hT (fun hST => hne hST.symm)
  apply hW.2.2
  refine ⟨S ∩ T, Finset.inter_subset_left, ⟨l, hAP⟩, ?_⟩
  apply Finset.insert_subset
  · exact Finset.mem_inter.mpr ⟨hcS, hcT⟩
  · intro x hx
    exact Finset.mem_inter.mpr ⟨Finset.mem_of_mem_erase (hW.2.1 hx), hPT hx⟩

theorem witness_pair_not_isAP {c : ℕ} {S P : Finset ℕ}
    (hc : c ∈ S) (hW : IsWitnessPair S c P) :
    ¬ ∃ l : ℕ∞, ((insert c P : Finset ℕ) : Set ℕ).IsAPOfLength l := by
  intro hAP
  apply hW.2.2
  refine ⟨insert c P, ?_, hAP, Finset.Subset.refl _⟩
  exact Finset.insert_subset hc (hW.2.1.trans (Finset.erase_subset _ _))

end
section
open Finset

theorem sorted_pair_finset_injective {a b x y : ℕ} (hab : a < b) (hxy : x < y)
    (heq : ({a, b} : Finset ℕ) = {x, y}) : (a, b) = (x, y) := by
  have ha' : a ∈ ({x, y} : Finset ℕ) := by rw [← heq]; simp
  have hb' : b ∈ ({x, y} : Finset ℕ) := by rw [← heq]; simp
  have ha : a = x ∨ a = y := by simpa only [Finset.mem_insert,
    Finset.mem_singleton] using ha'
  have hb : b = x ∨ b = y := by simpa only [Finset.mem_insert,
    Finset.mem_singleton] using hb'
  have hax : a = x := by omega
  have hby : b = y := by omega
  exact Prod.ext hax hby

theorem small_common_point_card_le {α : Type*} [DecidableEq α]
    {F : Finset (Finset α)} {U : Finset α} {c : α}
    (hsub : ∀ S ∈ F, S ⊆ U) (hc : ∀ S ∈ F, c ∈ S)
    (hsmall : ∀ S ∈ F, S.card ≤ 2) : F.card ≤ U.card := by
  have hcover : F ⊆ U.image (fun x => {c, x}) := by
    intro S hS
    have hcS := hc S hS
    have hcard : (S.erase c).card ≤ 1 := by
      rw [Finset.card_erase_of_mem hcS]
      have hh := hsmall S hS
      omega
    rcases (S.erase c).eq_empty_or_nonempty with hempty | hne
    · have hSsing : S = {c} := by
        rw [← Finset.insert_erase hcS, hempty]
        rfl
      refine Finset.mem_image.mpr ⟨c, hsub S hS hcS, ?_⟩
      simp [hSsing]
    · have hone : (S.erase c).card = 1 := by
        have hh := Finset.card_pos.mpr hne
        omega
      obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hone
      have hxerase : x ∈ S.erase c := by rw [hx]; simp
      have hxS : x ∈ S := (Finset.mem_erase.mp hxerase).2
      refine Finset.mem_image.mpr ⟨x, hsub S hS hxS, ?_⟩
      rw [← Finset.insert_erase hcS, hx]
  exact (Finset.card_le_card hcover).trans (Finset.card_image_le)

theorem partial_matching_card_le {α β : Type*} [Fintype α] [DecidableEq β]
    [Inhabited β] {B : Finset β} {M : ℕ} (f : α → Option β)
    (hvalid : ∀ a b, f a = some b → b ∈ B)
    (hinj : ∀ a a' b, f a = some b → f a' = some b → a = a')
    (hmiss : (Finset.univ.filter (fun a => f a = none)).card ≤ M) :
    Fintype.card α ≤ B.card + M := by
  classical
  let R : Finset α := Finset.univ.filter (fun a => f a ≠ none)
  let g : α → β := fun a => (f a).getD default
  have hsome : ∀ a ∈ R, f a = some (g a) := by
    intro a ha
    obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp (Finset.mem_filter.mp ha).2
    simp [g, hb]
  have hRcard : R.card ≤ B.card := Finset.card_le_card_of_injOn g
    (fun a ha => hvalid a (g a) (hsome a ha)) (by
      intro a ha a' ha' heq
      exact hinj a a' (g a) (hsome a ha) (by simpa only [heq] using hsome a' ha'))
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset α)) (fun a => f a = none)
  simp only [Finset.card_univ] at hpartition
  change (Finset.univ.filter (fun a => f a = none)).card + R.card = Fintype.card α
    at hpartition
  omega

theorem extend_partial_matching {α β : Type*} [DecidableEq α] {Q : Finset α}
    {P : α → β → Prop} {M : ℕ} (f : {a // a ∈ Q} → Option β)
    (hvalid : ∀ a b, f a = some b → P a.val b)
    (hinj : ∀ a a' b, f a = some b → f a' = some b → a = a')
    (hmiss : (Finset.univ.filter (fun a => f a = none)).card ≤ M) :
    ∃ g : α → Option β,
      (∀ a b, g a = some b → P a b) ∧
      (∀ a a' b, g a = some b → g a' = some b → a = a') ∧
      (∀ S : Finset α, S ⊆ Q → (S.filter (fun a => g a = none)).card ≤ M) := by
  classical
  let g : α → Option β := fun a => if h : a ∈ Q then f ⟨a, h⟩ else none
  have hsome {a : α} {b : β} (h : g a = some b) :
      ∃ ha : a ∈ Q, f ⟨a, ha⟩ = some b := by
    by_cases ha : a ∈ Q
    · exact ⟨ha, by simpa only [g, dif_pos ha] using h⟩
    · simp [g, ha] at h
  refine ⟨g, ?_, ?_, ?_⟩
  · intro a b hab
    obtain ⟨ha, hf⟩ := hsome hab
    exact hvalid ⟨a, ha⟩ b hf
  · intro a a' b hab ha'b
    obtain ⟨ha, hf⟩ := hsome hab
    obtain ⟨ha', hf'⟩ := hsome ha'b
    exact congrArg (fun x : {a // a ∈ Q} => x.val) (hinj ⟨a, ha⟩ ⟨a', ha'⟩ b hf hf')
  · intro S hSQ
    let E := S.filter (fun a => g a = none)
    let e : {a // a ∈ E} → {a // a ∈ Q} :=
      fun a => ⟨a.val, hSQ (Finset.mem_filter.mp a.property).1⟩
    have heinj : Function.Injective e := by
      intro a a' heq
      exact Subtype.ext (congrArg (fun x : {a // a ∈ Q} => x.val) heq)
    have hemaps : Set.MapsTo e
        ((Finset.univ : Finset {a // a ∈ E}) : Set {a // a ∈ E})
        ((Finset.univ.filter (fun a => f a = none)) : Set {a // a ∈ Q}) := by
      intro a ha
      have haQ : a.val ∈ Q := hSQ (Finset.mem_filter.mp a.property).1
      have hh : g a.val = none := (Finset.mem_filter.mp a.property).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        by simpa only [g, dif_pos haQ, e] using hh⟩
    have hEcard := Finset.card_le_card_of_injOn e hemaps heinj.injOn
    simpa only [Finset.card_univ, Fintype.card_coe] using hEcard.trans hmiss

end
section
open Finset

theorem exists_common_point_pair_matching_allowed {N c : ℕ} {F : Finset (Finset ℕ)}
    {Allowed : Finset ℕ → Prop}
    (hF : Erdos272.IsArithInterSet N F) (hc : ∀ S ∈ F, c ∈ S)
    (hcard : ∀ S ∈ F, 3 ≤ S.card)
    (hWitness : ∀ S ∈ F, IsCrooked S → ∃ P, IsWitnessPair S c P ∧ Allowed P)
    (hTriple : ∀ S ∈ F, S.card = 3 → Allowed (S.erase c))
    (hMatch : ∀ G : Finset (Finset ℕ), G ⊆ F →
      (∀ S ∈ G, ∃ l : ℕ∞, (S : Set ℕ).IsAPOfLength l) →
      (∀ S ∈ G, 4 ≤ S.card) → ∃ g : {S // S ∈ G} → Option (ℕ × ℕ),
        (∀ S q, g S = some q → ∃ d : ℕ, 0 < d ∧ d ≤ N ∧
          NaturalMatchedPair c d S.val q ∧ Allowed {q.1, q.2}) ∧
        (∀ S T q, g S = some q → g T = some q → S = T) ∧
        (Finset.univ.filter (fun S => g S = none)).card ≤ 20000 * N) :
    ∃ f : {S // S ∈ F} → Option (Finset ℕ),
      (∀ S P, f S = some P → P.card = 2 ∧ P ⊆ S.val.erase c) ∧
      (∀ S P, f S = some P → Allowed P) ∧
      (∀ S T P, f S = some P → f T = some P → S = T) ∧
      (Finset.univ.filter (fun S => f S = none)).card ≤ 20000 * N := by
  classical
  let A := {S : Finset ℕ // S ∈ F}
  let L := F.filter (fun S => ¬ IsCrooked S ∧ 4 ≤ S.card)
  obtain ⟨g, hgvalid, hginj, hgmiss⟩ := hMatch L (Finset.filter_subset _ _)
    (fun S hS => of_not_not (Finset.mem_filter.mp hS).2.1)
    (fun S hS => (Finset.mem_filter.mp hS).2.2)
  let large (S : A) (hn : ¬ IsCrooked S.val) (ht : S.val.card ≠ 3) : {T // T ∈ L} :=
    ⟨S.val, Finset.mem_filter.mpr ⟨S.property, hn, by have hh := hcard S.val S.property; omega⟩⟩
  let w (S : A) (h : IsCrooked S.val) : Finset ℕ :=
    Classical.choose (hWitness S.val S.property h)
  have hw (S : A) (h : IsCrooked S.val) : IsWitnessPair S.val c (w S h) ∧ Allowed (w S h) :=
    Classical.choose_spec (hWitness S.val S.property h)
  let f : A → Option (Finset ℕ) := fun S =>
    if h : IsCrooked S.val then some (w S h)
    else if ht : S.val.card = 3 then some (S.val.erase c)
    else (g (large S h ht)).map (fun q => {q.1, q.2})
  have hcrook (S : A) {P : Finset ℕ} (hP : f S = some P) (h : IsCrooked S.val) :
      IsWitnessPair S.val c P := by
    have heq : w S h = P := by simpa only [f, dif_pos h, Option.some.injEq] using hP
    exact heq ▸ (hw S h).1
  have hthree (S : A) {P : Finset ℕ} (hP : f S = some P)
      (hn : ¬ IsCrooked S.val) (ht : S.val.card = 3) : P = S.val.erase c := by
    have heq : S.val.erase c = P := by
      simpa only [f, dif_neg hn, dif_pos ht, Option.some.injEq] using hP
    exact heq.symm
  have hlarge (S : A) {P : Finset ℕ} (hP : f S = some P)
      (hn : ¬ IsCrooked S.val) (ht : S.val.card ≠ 3) :
      ∃ r : ℕ × ℕ, g (large S hn ht) = some r ∧ P = {r.1, r.2} ∧
        ∃ d : ℕ, NaturalMatchedPair c d S.val r := by
    have hm : (g (large S hn ht)).map (fun q => ({q.1, q.2} : Finset ℕ)) = some P := by
      simpa only [f, dif_neg hn, dif_neg ht] using hP
    obtain ⟨r, hr, hrP⟩ := Option.map_eq_some_iff.mp hm
    obtain ⟨d, hd, hdN, hnat, hAllowed⟩ := hgvalid (large S hn ht) r hr
    exact ⟨r, hr, hrP.symm, d, hnat⟩
  have hvalid (S : A) (P : Finset ℕ) (hP : f S = some P) :
      P.card = 2 ∧ P ⊆ S.val.erase c := by
    by_cases hn : IsCrooked S.val
    · exact ⟨(hcrook S hP hn).1, (hcrook S hP hn).2.1⟩
    by_cases ht : S.val.card = 3
    · rw [hthree S hP hn ht]
      exact ⟨by rw [Finset.card_erase_of_mem (hc S.val S.property), ht], Finset.Subset.refl _⟩
    obtain ⟨r, hr, rfl, d, hnat⟩ := hlarge S hP hn ht
    refine ⟨by simp [hnat.2.2.1.ne], ?_⟩
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_erase.mpr ⟨hnat.2.2.2.1, hnat.1⟩
    · exact Finset.mem_erase.mpr ⟨hnat.2.2.2.2.1, hnat.2.1⟩
  have hallowed (S : A) (P : Finset ℕ) (hP : f S = some P) : Allowed P := by
    by_cases hn : IsCrooked S.val
    · have heq : w S hn = P := by simpa only [f, dif_pos hn, Option.some.injEq] using hP
      exact heq ▸ (hw S hn).2
    by_cases ht : S.val.card = 3
    · rw [hthree S hP hn ht]
      exact hTriple S.val S.property ht
    obtain ⟨r, hr, hrP, d, hnat⟩ := hlarge S hP hn ht
    obtain ⟨e, he, heN, hnat', hAllowed⟩ := hgvalid (large S hn ht) r hr
    exact hrP.symm ▸ hAllowed
  refine ⟨f, hvalid, hallowed, ?_, ?_⟩
  · intro S T P hS hT
    by_cases hSc : IsCrooked S.val
    · apply Subtype.ext
      exact (witness_pair_private hF S.property T.property (hc S.val S.property)
        (hc T.val T.property) (hcrook S hS hSc)
        ((hvalid T P hT).2.trans (Finset.erase_subset _ _))).symm
    by_cases hTc : IsCrooked T.val
    · apply Subtype.ext
      exact witness_pair_private hF T.property S.property (hc T.val T.property)
        (hc S.val S.property) (hcrook T hT hTc)
        ((hvalid S P hS).2.trans (Finset.erase_subset _ _))
    have hS_AP : ∃ l : ℕ∞, (S.val : Set ℕ).IsAPOfLength l := of_not_not hSc
    have hT_AP : ∃ l : ℕ∞, (T.val : Set ℕ).IsAPOfLength l := of_not_not hTc
    by_cases hS3 : S.val.card = 3
    · have hSP : S.val = insert c P := by
        rw [hthree S hS hSc hS3, Finset.insert_erase (hc S.val S.property)]
      by_cases hT3 : T.val.card = 3
      · apply Subtype.ext
        rw [hSP, hthree T hT hTc hT3, Finset.insert_erase (hc T.val T.property)]
      · obtain ⟨r, hr, hrP, d, hnat⟩ := hlarge T hT hTc hT3
        exact False.elim (hnat.2.2.2.2.2.2 (by simpa only [hSP, hrP] using hS_AP))
    · by_cases hT3 : T.val.card = 3
      · have hTP : T.val = insert c P := by
          rw [hthree T hT hTc hT3, Finset.insert_erase (hc T.val T.property)]
        obtain ⟨r, hr, hrP, d, hnat⟩ := hlarge S hS hSc hS3
        exact False.elim (hnat.2.2.2.2.2.2 (by simpa only [hTP, hrP] using hT_AP))
      · obtain ⟨r, hr, hrP, d, hnat⟩ := hlarge S hS hSc hS3
        obtain ⟨s, hs, hsP, e, hnat'⟩ := hlarge T hT hTc hT3
        have hrs : r = s := sorted_pair_finset_injective hnat.2.2.1 hnat'.2.2.1
          (hrP.symm.trans hsP)
        have hST := hginj (large S hSc hS3) (large T hTc hT3) r hr
          (by simpa only [hrs] using hs)
        exact Subtype.ext (congrArg (fun U : {T // T ∈ L} => U.val) hST)
  · let E : Finset A := Finset.univ.filter (fun S => f S = none)
    have hex : ∀ S : {S // S ∈ E}, ∃ T : {T // T ∈ L}, T.val = S.val.val ∧ g T = none := by
      intro S
      have hfnone : f S.val = none := (Finset.mem_filter.mp S.property).2
      by_cases hn : IsCrooked S.val.val
      · simp only [f, dif_pos hn, Option.some_ne_none] at hfnone
      by_cases ht : S.val.val.card = 3
      · simp only [f, dif_neg hn, dif_pos ht, Option.some_ne_none] at hfnone
      refine ⟨large S.val hn ht, rfl, ?_⟩
      have hm : (g (large S.val hn ht)).map (fun q => ({q.1, q.2} : Finset ℕ)) = none := by
        simpa only [f, dif_neg hn, dif_neg ht] using hfnone
      exact Option.map_eq_none_iff.mp hm
    choose e he henone using hex
    have heinj : Function.Injective e := by
      intro S T heq
      apply Subtype.ext
      apply Subtype.ext
      exact (he S).symm.trans ((congrArg Subtype.val heq).trans (he T))
    have hemaps : Set.MapsTo e
        ((Finset.univ : Finset {S // S ∈ E}) : Set {S // S ∈ E})
        ((Finset.univ.filter (fun T => g T = none)) : Set {T // T ∈ L}) := by
      intro S hS
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, henone S⟩
    have hEcard := Finset.card_le_card_of_injOn e hemaps heinj.injOn
    have hh := hEcard.trans hgmiss
    simpa only [Finset.card_univ, Fintype.card_coe] using hh

theorem exists_common_point_pair_matching {N c : ℕ} {F : Finset (Finset ℕ)}
    (hF : Erdos272.IsArithInterSet N F) (hc : ∀ S ∈ F, c ∈ S)
    (hcard : ∀ S ∈ F, 3 ≤ S.card) :
    ∃ f : {S // S ∈ F} → Option (Finset ℕ),
      (∀ S P, f S = some P → P.card = 2 ∧ P ⊆ S.val.erase c) ∧
      (∀ S T P, f S = some P → f T = some P → S = T) ∧
      (Finset.univ.filter (fun S => f S = none)).card ≤ 20000 * N := by
  have hMatch : ∀ G : Finset (Finset ℕ), G ⊆ F →
      (∀ S ∈ G, ∃ l : ℕ∞, (S : Set ℕ).IsAPOfLength l) →
      (∀ S ∈ G, 4 ≤ S.card) → ∃ g : {S // S ∈ G} → Option (ℕ × ℕ),
        (∀ S q, g S = some q → ∃ d : ℕ, 0 < d ∧ d ≤ N ∧
          NaturalMatchedPair c d S.val q ∧ True) ∧
        (∀ S T q, g S = some q → g T = some q → S = T) ∧
        (Finset.univ.filter (fun S => g S = none)).card ≤ 20000 * N := by
    intro G hGF hAP hcard
    obtain ⟨g, hvalid, hinj, hmiss⟩ := exists_natural_progression_pair_matching
      (fun S hS => Finset.mem_powerset.mp (hF.1 (hGF hS))) hAP hcard
      (fun S hS => hc S (hGF hS))
    refine ⟨g, ?_, hinj, hmiss⟩
    intro S q hq
    obtain ⟨d, hd, hdN, hnat⟩ := hvalid S q hq
    exact ⟨d, hd, hdN, hnat, trivial⟩
  obtain ⟨f, hvalid, hAllowed, hinj, hmiss⟩ := exists_common_point_pair_matching_allowed
    (Allowed := fun _ => True) hF hc hcard
    (fun S hS hcrooked => by
      obtain ⟨P, hP⟩ := exists_witness_pair hcrooked (hc S hS)
      exact ⟨P, hP, trivial⟩)
    (fun S hS h3 => trivial) hMatch
  exact ⟨f, hvalid, hinj, hmiss⟩

theorem common_point_large_card_le {N c : ℕ} {F : Finset (Finset ℕ)}
    (hF : Erdos272.IsArithInterSet N F) (hc : ∀ S ∈ F, c ∈ S)
    (hcard : ∀ S ∈ F, 3 ≤ S.card) : F.card ≤ N.choose 2 + 20000 * N := by
  classical
  obtain ⟨f, hvalid, hinj, hmiss⟩ := exists_common_point_pair_matching hF hc hcard
  have hm := partial_matching_card_le (B := (Finset.Icc 1 N).powersetCard 2) f
    (fun S P hP => Finset.mem_powersetCard.mpr ⟨(hvalid S P hP).2.trans
      ((Finset.erase_subset c S.val).trans (Finset.mem_powerset.mp (hF.1 S.property))),
      (hvalid S P hP).1⟩) hinj hmiss
  simpa using hm

theorem common_point_card_le {N c : ℕ} {F : Finset (Finset ℕ)}
    (hF : Erdos272.IsArithInterSet N F) (hc : ∀ S ∈ F, c ∈ S) :
    F.card ≤ N.choose 2 + 20001 * N := by
  classical
  let B := F.filter (fun S => S.card ≤ 2)
  let G := F.filter (fun S => ¬ S.card ≤ 2)
  have hB : B.card ≤ N := by
    have hh := small_common_point_card_le (F := B) (U := Finset.Icc 1 N) (c := c)
      (fun S hS => Finset.mem_powerset.mp (hF.1 (Finset.mem_filter.mp hS).1))
      (fun S hS => hc S (Finset.mem_filter.mp hS).1)
      (fun S hS => (Finset.mem_filter.mp hS).2)
    simpa using hh
  have hG : G.card ≤ N.choose 2 + 20000 * N := common_point_large_card_le
    (arithInterSet_mono hF (Finset.filter_subset _ _))
    (fun S hS => hc S (Finset.mem_filter.mp hS).1)
    (fun S hS => by have hh := (Finset.mem_filter.mp hS).2; omega)
  have hpartition := Finset.card_filter_add_card_filter_not (s := F) (fun S => S.card ≤ 2)
  change B.card + G.card = F.card at hpartition
  omega

theorem common_point_card_le_real {N c : ℕ} {F : Finset (Finset ℕ)}
    (hF : Erdos272.IsArithInterSet N F) (hc : ∀ S ∈ F, c ∈ S) :
    (F.card : ℝ) ≤ (N : ℝ)^2 / 2 + 20001 * (N : ℝ) := by
  have hh : (F.card : ℝ) ≤ (N.choose 2 : ℝ) + 20001 * (N : ℝ) :=
    by exact_mod_cast common_point_card_le hF hc
  rw [Nat.cast_choose_two] at hh
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  nlinarith

end
section
open Finset

theorem coprime_row_tail_card {A r : ℕ} :
    r.totient ≤ (((Finset.Icc 1 r).filter (fun a => r.Coprime a)).filter
      (fun a => A ≤ a)).card + A := by
  let D := (Finset.Icc 1 r).filter (fun a => r.Coprime a)
  have hsmall : (D.filter (fun a => ¬ A ≤ a)).card ≤ A := by
    have hsub : D.filter (fun a => ¬ A ≤ a) ⊆ Finset.range A := by
      intro a ha
      exact Finset.mem_range.mpr (Nat.lt_of_not_ge (Finset.mem_filter.mp ha).2)
    simpa using Finset.card_le_card hsub
  have hpart := Finset.card_filter_add_card_filter_not (s := D) (fun a => A ≤ a)
  have hD : D.card = r.totient := card_coprime_Icc r
  change r.totient ≤ (D.filter (fun a => A ≤ a)).card + A
  omega

theorem exists_axis_row_assignment {A C r : ℕ} (hr : 3 ≤ r)
    (hsupply : A + C + 1 ≤ r.totient) :
    ∃ g : Fin (C + 1) → ℕ, Function.Injective g ∧
      ∀ i, (g i, r) ∈ axisPairs r ∧ A ≤ g i := by
  let D := ((Finset.Icc 1 r).filter (fun a => r.Coprime a)).filter (fun a => A ≤ a)
  have hcard : C + 1 ≤ D.card := by
    have hh := coprime_row_tail_card (A := A) (r := r)
    change r.totient ≤ D.card + A at hh
    omega
  let e : Fin (C + 1) → Fin D.card := fun i => ⟨i.val, lt_of_lt_of_le i.isLt hcard⟩
  let g : Fin (C + 1) → ℕ := fun i => (D.orderEmbOfFin rfl) (e i)
  refine ⟨g, ?_, ?_⟩
  · intro i j hij
    have he : e i = e j := (D.orderEmbOfFin rfl).injective hij
    exact Fin.ext (congrArg (fun i : Fin D.card => i.val) he)
  · intro i
    have hiD : g i ∈ D := D.orderEmbOfFin_mem rfl (e i)
    obtain ⟨hirow, hiA⟩ := Finset.mem_filter.mp hiD
    obtain ⟨hiI, hcop⟩ := Finset.mem_filter.mp hirow
    obtain ⟨hi1, hir⟩ := Finset.mem_Icc.mp hiI
    have hir' : g i < r := by
      by_contra hh
      have heq : g i = r := by omega
      have hone : r = 1 := by simpa only [heq, Nat.coprime_self] using hcop
      omega
    exact ⟨mem_axisPairs.mpr ⟨hi1, hir', hr, le_rfl, hcop.symm⟩, hiA⟩

theorem exists_corner_pair_matching {A B C M : ℕ} (hB : 2 ≤ B)
    (hsupply : ∀ r : ℕ, B < r → r ≤ M → A + C + 1 ≤ r.totient)
    (Q : Finset ProgressionCell)
    (hleft : ∀ p ∈ Q, p.val.1 ≤ C) (hright : ∀ p ∈ Q, p.val.2 ≤ M) :
    ∃ f : {p // p ∈ Q} → Option (ℤ × ℤ),
      (∀ p q, f p = some q → PrimitiveBadPair p.val q ∧
        (q.2 ≤ (B : ℤ) ∨ (A : ℤ) ≤ q.1)) ∧
      (∀ p p' q, f p = some q → f p' = some q → p = p') ∧
      (Finset.univ.filter (fun p => f p = none)).card ≤ 20000 := by
  classical
  let R := {r : ℕ // B < r ∧ r ≤ M}
  have hrows : ∀ r : R, ∃ g : Fin (C + 1) → ℕ, Function.Injective g ∧
      ∀ i, (g i, r.val) ∈ axisPairs r.val ∧ A ≤ g i := by
    intro r
    exact exists_axis_row_assignment (by have hh := r.property.1; omega)
      (hsupply r.val r.property.1 r.property.2)
  choose a hainj haspec using hrows
  obtain ⟨g, hgvalid, hginj, hgmiss⟩ := exists_progression_pair_matching
  let ri (p : {p // p ∈ Q}) (hr : B < p.val.val.2) : R :=
    ⟨p.val.val.2, hr, hright p.val p.property⟩
  let li (p : {p // p ∈ Q}) : Fin (C + 1) :=
    ⟨p.val.val.1, Nat.lt_succ_of_le (hleft p.val p.property)⟩
  let f : {p // p ∈ Q} → Option (ℤ × ℤ) := fun p =>
    if hr : B < p.val.val.2 then some ((a (ri p hr) (li p) : ℤ), (p.val.val.2 : ℤ))
    else g p.val
  have hlong (p : {p // p ∈ Q}) {q : ℤ × ℤ} (hq : f p = some q)
      (hr : B < p.val.val.2) : ((a (ri p hr) (li p) : ℤ), (p.val.val.2 : ℤ)) = q := by
    exact Option.some.inj (by simpa only [f, dif_pos hr] using hq)
  have hshort (p : {p // p ∈ Q}) {q : ℤ × ℤ} (hq : f p = some q)
      (hr : ¬ B < p.val.val.2) : g p.val = some q := by
    simpa only [f, dif_neg hr] using hq
  refine ⟨f, ?_, ?_, ?_⟩
  · intro p q hq
    by_cases hr : B < p.val.val.2
    · rw [← hlong p hq hr]
      exact ⟨primitiveBadPair_positive (haspec (ri p hr) (li p)).1,
        Or.inr (by
          change (A : ℤ) ≤ (a (ri p hr) (li p) : ℤ)
          exact_mod_cast (haspec (ri p hr) (li p)).2)⟩
    · have hp := hgvalid p.val q (hshort p hq hr)
      exact ⟨hp, Or.inl (by have hh := hp.2.2.1; omega)⟩
  · intro p p' q hp hp'
    by_cases hr : B < p.val.val.2
    · have heq := hlong p hp hr
      by_cases hr' : B < p'.val.val.2
      · have heq' := hlong p' hp' hr'
        have hrI := congrArg Prod.snd (heq.trans heq'.symm)
        change (p.val.val.2 : ℤ) = (p'.val.val.2 : ℤ) at hrI
        have hrr : p.val.val.2 = p'.val.val.2 := by exact_mod_cast hrI
        have hri : ri p hr = ri p' hr' := Subtype.ext hrr
        have hfst := congrArg Prod.fst (heq.trans heq'.symm)
        change (a (ri p hr) (li p) : ℤ) = (a (ri p' hr') (li p') : ℤ) at hfst
        rw [hri] at hfst
        have hl : li p = li p' := hainj (ri p' hr') (by exact_mod_cast hfst)
        apply Subtype.ext
        apply Subtype.ext
        exact Prod.ext (congrArg Fin.val hl) hrr
      · have hbound := (hgvalid p'.val q (hshort p' hp' hr')).2.2.1
        have hsnd := congrArg Prod.snd heq
        change (p.val.val.2 : ℤ) = q.2 at hsnd
        omega
    · by_cases hr' : B < p'.val.val.2
      · have hbound := (hgvalid p.val q (hshort p hp hr)).2.2.1
        have hsnd := congrArg Prod.snd (hlong p' hp' hr')
        change (p'.val.val.2 : ℤ) = q.2 at hsnd
        omega
      · exact Subtype.ext (hginj p.val p'.val q (hshort p hp hr) (hshort p' hp' hr'))
  · have hmaps : Set.MapsTo (fun p : {p // p ∈ Q} => p.val)
        ((Finset.univ.filter (fun p => f p = none)) : Set {p // p ∈ Q})
        ((Q.filter (fun p => g p = none)) : Set ProgressionCell) := by
      intro p hp
      have hnone : f p = none := (Finset.mem_filter.mp hp).2
      have hr : ¬ B < p.val.val.2 := by
        intro hr
        simp only [f, dif_pos hr, Option.some_ne_none] at hnone
      have hg : g p.val = none := by simpa only [f, dif_neg hr] using hnone
      exact Finset.mem_filter.mpr ⟨p.property, hg⟩
    exact (Finset.card_le_card_of_injOn (fun p : {p // p ∈ Q} => p.val)
      hmaps Subtype.coe_injective.injOn).trans (hgmiss Q)

def boundedProgressionCells (C M : ℕ) : Finset ProgressionCell :=
  ((Finset.range (C + 1)).product (Finset.range (M + 1))).subtype
    (fun p => 3 ≤ p.1 + p.2)

theorem mem_boundedProgressionCells {C M : ℕ} {p : ProgressionCell} :
    p ∈ boundedProgressionCells C M ↔ p.val.1 ≤ C ∧ p.val.2 ≤ M := by
  simp [boundedProgressionCells]

theorem exists_bounded_corner_matching {A B C M : ℕ} (hB : 2 ≤ B)
    (hsupply : ∀ r : ℕ, B < r → r ≤ M → A + C + 1 ≤ r.totient) :
    ∃ f : ProgressionCell → Option (ℤ × ℤ),
      (∀ p q, f p = some q → PrimitiveBadPair p q ∧
        (q.2 ≤ (B : ℤ) ∨ (A : ℤ) ≤ q.1)) ∧
      (∀ p p' q, f p = some q → f p' = some q → p = p') ∧
      (∀ S : Finset ProgressionCell, S ⊆ boundedProgressionCells C M →
        (S.filter (fun p => f p = none)).card ≤ 20000) := by
  obtain ⟨f, hvalid, hinj, hmiss⟩ := exists_corner_pair_matching hB hsupply
    (boundedProgressionCells C M)
    (fun p hp => (mem_boundedProgressionCells.mp hp).1)
    (fun p hp => (mem_boundedProgressionCells.mp hp).2)
  exact extend_partial_matching f hvalid hinj hmiss

end
section
theorem corner_totient_row_supply {N c L R d r : ℕ}
    (hcL : c < L) (hLR : L ≤ R) (hRN : R ≤ N)
    (hd : 0 < d) (hdt : d ≤ L + N - R)
    (hN : 256 * (L + N - R) * (Nat.log 2 N + 1) ≤ N)
    (hr : (R - c) / d < r) (hrN : r ≤ N / d) :
    ((L - c) / d + 1) + c / d + 1 ≤ r.totient := by
  let t := L + N - R
  let K := Nat.log 2 N + 1
  have hLt : L ≤ t := by dsimp [t]; omega
  have hct : c ≤ t := hcL.le.trans hLt
  have htp : 0 < t := by omega
  have hNt : N + L = t + R := by dsimp [t]; omega
  have hRc : R - c + c = R := Nat.sub_add_cancel (hcL.le.trans hLR)
  have hLc : L - c + c = L := Nat.sub_add_cancel hcL.le
  have hrN' : r ≤ N := hrN.trans (Nat.div_le_self N d)
  have hlog : Nat.log 2 r + 1 ≤ K := Nat.add_le_add_right (Nat.log_mono_right hrN') 1
  have hrphi : r ≤ K * r.totient := (le_log_succ_mul_totient r).trans
    (Nat.mul_le_mul_right r.totient hlog)
  have hRr : R - c < r * d := (Nat.div_lt_iff_lt_mul hd).mp hr
  by_contra hphi
  have hphi' : r.totient ≤ (L - c) / d + c / d + 1 := by omega
  have hmul : d * r.totient ≤ 2 * t := by
    have hdivL := Nat.mul_div_le (L - c) d
    have hdivc := Nat.mul_div_le c d
    have hh := Nat.mul_le_mul_left d hphi'
    nlinarith
  have hupper : d * r ≤ K * (2 * t) := by
    calc
      d * r ≤ d * (K * r.totient) := Nat.mul_le_mul_left d hrphi
      _ = K * (d * r.totient) := by ring
      _ ≤ K * (2 * t) := Nat.mul_le_mul_left K hmul
  have hK : 1 ≤ K := by dsimp [K]; omega
  change 256 * t * K ≤ N at hN
  have hprod : t ≤ t * K := by nlinarith
  nlinarith

theorem corner_normalized_threshold {N c L R d : ℕ}
    (hcL : c < L) (hLR : L ≤ R) (hRN : R ≤ N)
    (hd : 0 < d) (hdt : d ≤ L + N - R)
    (hN : 256 * (L + N - R) * (Nat.log 2 N + 1) ≤ N) :
    2 ≤ (R - c) / d := by
  apply (Nat.le_div_iff_mul_le hd).mpr
  have ht : L ≤ L + N - R := by omega
  have hc : c ≤ L + N - R := by omega
  have hmul : 256 * (L + N - R) ≤ 256 * (L + N - R) * (Nat.log 2 N + 1) := by
    exact Nat.le_mul_of_pos_right _ (by omega)
  omega

end
section
open Finset

theorem centered_model_cell_bounds {N c d : ℕ} {p : ProgressionCell} {S : Finset ℕ}
    (hd : 0 < d) (hmodel : IsCenteredModel c d p S) (hsub : S ⊆ Finset.Icc 1 N) :
    p.val.1 ≤ c / d ∧ p.val.2 ≤ N / d := by
  have hl := centered_point_mem hmodel
    (Finset.mem_Icc.mpr ⟨le_rfl, (by omega : -(p.val.1 : ℤ) ≤ (p.val.2 : ℤ))⟩)
  have hr := centered_point_mem hmodel
    (Finset.mem_Icc.mpr ⟨(by omega : -(p.val.1 : ℤ) ≤ (p.val.2 : ℤ)), le_rfl⟩)
  have hlI := Finset.mem_Icc.mp (hsub hl.1)
  have hrI := Finset.mem_Icc.mp (hsub hr.1)
  have hleftI : (p.val.1 : ℤ) * (d : ℤ) ≤ c := by nlinarith [hl.2]
  have hrightI : (p.val.2 : ℤ) * (d : ℤ) ≤ N := by nlinarith [hr.2]
  exact ⟨(Nat.le_div_iff_mul_le hd).mpr (by exact_mod_cast hleftI),
    (Nat.le_div_iff_mul_le hd).mpr (by exact_mod_cast hrightI)⟩

theorem exists_natural_progression_pair_matching_constrained
    {N c : ℕ} {F : Finset (Finset ℕ)} {P : (ℕ × ℕ) → Prop}
    (hsub : ∀ S ∈ F, S ⊆ Finset.Icc 1 N)
    (hAP : ∀ S ∈ F, ∃ l : ℕ∞, (S : Set ℕ).IsAPOfLength l)
    (hcard : ∀ S ∈ F, 4 ≤ S.card) (hcenter : ∀ S ∈ F, c ∈ S)
    (hmatch : ∀ d : ℕ, 0 < d → d ≤ N → ∃ f : ProgressionCell → Option (ℤ × ℤ),
      (∀ p q, f p = some q → PrimitiveBadPair p q ∧
        ∀ S : Finset ℕ, IsCenteredModel c d p S → P (liftPair c d q)) ∧
      (∀ p p' q, f p = some q → f p' = some q → p = p') ∧
      (∀ Q : Finset ProgressionCell,
        (∀ p ∈ Q, p.val.1 ≤ c / d ∧ p.val.2 ≤ N / d) →
        (Q.filter (fun p => f p = none)).card ≤ 20000)) :
    ∃ f : {S // S ∈ F} → Option (ℕ × ℕ),
      (∀ S q, f S = some q → ∃ d : ℕ, 0 < d ∧ d ≤ N ∧
        NaturalMatchedPair c d S.val q ∧ P q) ∧
      (∀ S T q, f S = some q → f T = some q → S = T) ∧
      (Finset.univ.filter (fun S => f S = none)).card ≤ 20000 * N := by
  classical
  let A := {S : Finset ℕ // S ∈ F}
  let D := {k : ℕ // 0 < k ∧ k ≤ N}
  have hparam : ∀ S : A, ∃ d : ℕ, 0 < d ∧ d ≤ N ∧
      ∃ p : ProgressionCell, IsCenteredModel c d p S.val := by
    intro S
    obtain ⟨l, hAPs⟩ := hAP S.val S.property
    exact exists_centered_model_bounded (hsub S.val S.property) hAPs
      (hcard S.val S.property) (hcenter S.val S.property)
  choose d hd hdN p hmodel using hparam
  let k : A → D := fun S => ⟨d S, hd S, hdN S⟩
  choose f hfvalid hfinj hfmiss using (fun k : D => hmatch k.val k.property.1 k.property.2)
  let g : A → Option (ℕ × ℕ) := fun S => (f (k S) (p S)).map (liftPair c (d S))
  have hvalid : ∀ S q, g S = some q → NaturalMatchedPair c (d S) S.val q ∧ P q := by
    intro S q hq
    obtain ⟨r, hr, hrq⟩ := Option.map_eq_some_iff.mp hq
    rw [← hrq]
    have hv := hfvalid (k S) (p S) r hr
    exact ⟨liftPair_spec (hd S) (hmodel S) hv.1, hv.2 S.val (hmodel S)⟩
  refine ⟨g, ?_, ?_, ?_⟩
  · intro S q hq
    exact ⟨d S, hd S, hdN S, hvalid S q hq⟩
  · intro S T q hSq hTq
    have hSvalid := (hvalid S q hSq).1
    have hTvalid := (hvalid T q hTq).1
    have hdST : d S = d T := hSvalid.2.2.2.2.2.1.symm.trans hTvalid.2.2.2.2.2.1
    have hkST : k S = k T := Subtype.ext hdST
    obtain ⟨r, hr, hrq⟩ := Option.map_eq_some_iff.mp hSq
    obtain ⟨r', hr', hr'q⟩ := Option.map_eq_some_iff.mp hTq
    have hlifts : liftPair c (d T) r = liftPair c (d T) r' := by
      simpa only [hdST] using hrq.trans hr'q.symm
    have hrr' : r = r' := liftPair_injective_on_models (hd T)
      (by simpa only [hdST] using hmodel S) (hmodel T)
      (hfvalid (k S) (p S) r hr).1 (hfvalid (k T) (p T) r' hr').1 hlifts
    have hpST : p S = p T := hfinj (k T) (p S) (p T) r
      (by simpa only [hkST] using hr) (by simpa only [hrr'] using hr')
    apply Subtype.ext
    exact centered_model_determines_set
      (by simpa only [hdST, hpST] using hmodel S) (hmodel T)
  · let B : Finset A := Finset.univ.filter (fun S => g S = none)
    have hmaps : Set.MapsTo d (B : Set A) (Finset.Icc 1 N : Set ℕ) := by
      intro S hS
      exact Finset.mem_Icc.mpr ⟨hd S, hdN S⟩
    have hfiber : ∀ j ∈ Finset.Icc 1 N, (B.filter (fun S => d S = j)).card ≤ 20000 := by
      intro j hj
      let C := B.filter (fun S => d S = j)
      let kj : D := ⟨j, (Finset.mem_Icc.mp hj).1, (Finset.mem_Icc.mp hj).2⟩
      have hdj : ∀ S ∈ C, d S = j := fun S hS => (Finset.mem_filter.mp hS).2
      have hkj : ∀ S ∈ C, k S = kj := fun S hS => Subtype.ext (hdj S hS)
      have hpinj : Set.InjOn p (C : Set A) := by
        intro S hS T hT hpST
        apply Subtype.ext
        exact centered_model_determines_set
          (by simpa only [hdj S hS] using hmodel S)
          (by simpa only [hdj T hT, ← hpST] using hmodel T)
      have hfilter : (C.image p).filter (fun q => f kj q = none) = C.image p := by
        apply Finset.filter_eq_self.mpr
        intro q hq
        obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hq
        have hSB : S ∈ B := (Finset.mem_filter.mp hS).1
        have hnone : g S = none := (Finset.mem_filter.mp hSB).2
        have hh := Option.map_eq_none_iff.mp hnone
        simpa only [hkj S hS] using hh
      have hbounds : ∀ q ∈ C.image p, q.val.1 ≤ c / kj.val ∧ q.val.2 ≤ N / kj.val := by
        intro q hq
        obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hq
        have hh := centered_model_cell_bounds (hd S) (hmodel S) (hsub S.val S.property)
        simpa only [hdj S hS] using hh
      have hh := hfmiss kj (C.image p) hbounds
      rw [hfilter, Finset.card_image_of_injOn hpinj] at hh
      exact hh
    change B.card ≤ 20000 * N
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    calc
      _ ≤ ∑ j ∈ Finset.Icc 1 N, 20000 := Finset.sum_le_sum hfiber
      _ = 20000 * N := by simp [Nat.mul_comm]

end
section
def AffineAvoidsCorner (c L R d : ℕ) (q : ℤ × ℤ) : Prop :=
  ¬ ((c : ℤ) < (c : ℤ) + (d : ℤ) * q.1 ∧
    (c : ℤ) + (d : ℤ) * q.1 < (L : ℤ) ∧
    (R : ℤ) < (c : ℤ) + (d : ℤ) * q.2)

theorem large_step_affine_avoids_corner {c L R d : ℕ} (hLd : L ≤ c + d)
    (q : ℤ × ℤ) : AffineAvoidsCorner c L R d q := by
  rintro ⟨hc, hL, hR⟩
  have hd : (0 : ℤ) ≤ d := Nat.cast_nonneg d
  rcases le_or_gt q.1 0 with hq | hq
  · have hprod := mul_nonpos_of_nonneg_of_nonpos hd hq
    omega
  · have hq1 : (1 : ℤ) ≤ q.1 := by omega
    have hprod := mul_le_mul_of_nonneg_left hq1 hd
    have hLdI : (L : ℤ) ≤ (c : ℤ) + (d : ℤ) := by exact_mod_cast hLd
    nlinarith

theorem normalized_bounds_avoid_corner {c L R d : ℕ} {q : ℤ × ℤ}
    (hcL : c < L) (hLR : L ≤ R) (hd : 0 < d)
    (hq : q.2 ≤ (((R - c) / d : ℕ) : ℤ) ∨
      ((((L - c) / d + 1 : ℕ) : ℤ) ≤ q.1)) : AffineAvoidsCorner c L R d q := by
  rintro ⟨hc, hL, hR⟩
  have hdI : (0 : ℤ) ≤ d := Nat.cast_nonneg d
  have hRc : R - c + c = R := Nat.sub_add_cancel (hcL.le.trans hLR)
  have hLc : L - c + c = L := Nat.sub_add_cancel hcL.le
  rcases hq with hq | hq
  · have hbase : c + d * ((R - c) / d) ≤ R := by
      have hh := Nat.mul_div_le (R - c) d
      nlinarith
    have hbaseI : (c : ℤ) + (d : ℤ) * (((R - c) / d : ℕ) : ℤ) ≤ R := by
      exact_mod_cast hbase
    have hprod := mul_le_mul_of_nonneg_left hq hdI
    linarith
  · have hbase : L < c + d * ((L - c) / d + 1) := by
      have hh : L - c < ((L - c) / d + 1) * d :=
        (Nat.div_lt_iff_lt_mul hd).mp (by omega)
      nlinarith
    have hbaseI : (L : ℤ) < (c : ℤ) + (d : ℤ) * (((L - c) / d + 1 : ℕ) : ℤ) := by
      exact_mod_cast hbase
    have hprod := mul_le_mul_of_nonneg_left hq hdI
    linarith

theorem liftPair_avoids_corner {c L R d : ℕ} {q : ℤ × ℤ}
    {p : ProgressionCell} {S : Finset ℕ} (hmodel : IsCenteredModel c d p S)
    (hp : PrimitiveBadPair p q) (havoid : AffineAvoidsCorner c L R d q) :
    ¬ (c < (liftPair c d q).1 ∧ (liftPair c d q).1 < L ∧ R < (liftPair c d q).2) := by
  rintro ⟨hc, hL, hR⟩
  have hcoords := primitive_pair_coordinates hp
  have hx : ((liftPair c d q).1 : ℤ) = (c : ℤ) + (d : ℤ) * q.1 :=
    (centered_point_mem hmodel hcoords.1).2
  have hy : ((liftPair c d q).2 : ℤ) = (c : ℤ) + (d : ℤ) * q.2 :=
    (centered_point_mem hmodel hcoords.2).2
  apply havoid
  have hcI : (c : ℤ) < ((liftPair c d q).1 : ℤ) := by exact_mod_cast hc
  have hLI : ((liftPair c d q).1 : ℤ) < (L : ℤ) := by exact_mod_cast hL
  have hRI : (R : ℤ) < ((liftPair c d q).2 : ℤ) := by exact_mod_cast hR
  exact ⟨by simpa only [hx] using hcI, by simpa only [hx] using hLI,
    by simpa only [hy] using hRI⟩

theorem exists_normalized_corner_matching {N c L R d : ℕ}
    (hcL : c < L) (hLR : L ≤ R) (hRN : R ≤ N) (hd : 0 < d)
    (hN : 256 * (L + N - R) * (Nat.log 2 N + 1) ≤ N) :
    ∃ f : ProgressionCell → Option (ℤ × ℤ),
      (∀ p q, f p = some q → PrimitiveBadPair p q ∧ AffineAvoidsCorner c L R d q) ∧
      (∀ p p' q, f p = some q → f p' = some q → p = p') ∧
      (∀ Q : Finset ProgressionCell,
        (∀ p ∈ Q, p.val.1 ≤ c / d ∧ p.val.2 ≤ N / d) →
        (Q.filter (fun p => f p = none)).card ≤ 20000) := by
  by_cases hdt : d ≤ L + N - R
  · obtain ⟨f, hvalid, hinj, hmiss⟩ := exists_bounded_corner_matching
      (A := (L - c) / d + 1) (B := (R - c) / d) (C := c / d) (M := N / d)
      (corner_normalized_threshold hcL hLR hRN hd hdt hN)
      (fun r hr hrN => corner_totient_row_supply hcL hLR hRN hd hdt hN hr hrN)
    refine ⟨f, ?_, hinj, ?_⟩
    · intro p q hpq
      have hh := hvalid p q hpq
      exact ⟨hh.1, normalized_bounds_avoid_corner hcL hLR hd hh.2⟩
    · intro Q hQ
      exact hmiss Q (fun p hp => mem_boundedProgressionCells.mpr (hQ p hp))
  · obtain ⟨f, hvalid, hinj, hmiss⟩ := exists_progression_pair_matching
    refine ⟨f, ?_, hinj, fun Q _ => hmiss Q⟩
    intro p q hpq
    have hLd : L ≤ c + d := by omega
    exact ⟨hvalid p q hpq, large_step_affine_avoids_corner hLd q⟩

theorem exists_natural_corner_pair_matching {N c L R : ℕ} {F : Finset (Finset ℕ)}
    (hcL : c < L) (hLR : L ≤ R) (hRN : R ≤ N)
    (hN : 256 * (L + N - R) * (Nat.log 2 N + 1) ≤ N)
    (hsub : ∀ S ∈ F, S ⊆ Finset.Icc 1 N)
    (hAP : ∀ S ∈ F, ∃ l : ℕ∞, (S : Set ℕ).IsAPOfLength l)
    (hcard : ∀ S ∈ F, 4 ≤ S.card) (hcenter : ∀ S ∈ F, c ∈ S) :
    ∃ f : {S // S ∈ F} → Option (ℕ × ℕ),
      (∀ S q, f S = some q → ∃ d : ℕ, 0 < d ∧ d ≤ N ∧
        NaturalMatchedPair c d S.val q ∧ ¬ (c < q.1 ∧ q.1 < L ∧ R < q.2)) ∧
      (∀ S T q, f S = some q → f T = some q → S = T) ∧
      (Finset.univ.filter (fun S => f S = none)).card ≤ 20000 * N := by
  apply exists_natural_progression_pair_matching_constrained hsub hAP hcard hcenter
  intro d hd hdN
  obtain ⟨f, hvalid, hinj, hmiss⟩ := exists_normalized_corner_matching hcL hLR hRN hd hN
  refine ⟨f, ?_, hinj, hmiss⟩
  intro p q hpq
  have hh := hvalid p q hpq
  exact ⟨hh.1, fun S hS => liftPair_avoids_corner hS hh.1 hh.2⟩

end
section
open Finset

theorem exists_consecutive_left_of_mem {S : Finset ℕ} {x c : ℕ}
    (hx : x ∈ S) (hc : c ∈ S) (hxc : x < c) : ∃ a, ConsecutiveIn S a c := by
  let B := S.filter (fun a => a < c)
  have hB : B.Nonempty := ⟨x, Finset.mem_filter.mpr ⟨hx, hxc⟩⟩
  let a := B.max' hB
  have haB : a ∈ B := Finset.max'_mem B hB
  obtain ⟨haS, hac⟩ := Finset.mem_filter.mp haB
  refine ⟨a, haS, hc, hac, ?_⟩
  intro y hy hbetween
  have hyB : y ∈ B := Finset.mem_filter.mpr ⟨hy, hbetween.2⟩
  have hya : y ≤ a := Finset.le_max' B y hyB
  omega

theorem exists_consecutive_right_of_mem {S : Finset ℕ} {c x : ℕ}
    (hc : c ∈ S) (hx : x ∈ S) (hcx : c < x) : ∃ a, ConsecutiveIn S c a := by
  let B := S.filter (fun a => c < a)
  have hB : B.Nonempty := ⟨x, Finset.mem_filter.mpr ⟨hx, hcx⟩⟩
  let a := B.min' hB
  have haB : a ∈ B := Finset.min'_mem B hB
  obtain ⟨haS, hca⟩ := Finset.mem_filter.mp haB
  refine ⟨a, hc, haS, hca, ?_⟩
  intro y hy hbetween
  have hyB : y ∈ B := Finset.mem_filter.mpr ⟨hy, hbetween.1⟩
  have hay : a ≤ y := Finset.min'_le B y hyB
  omega

theorem consecutive_AP_core {S : Finset ℕ} {u v : ℕ} (hcon : ConsecutiveIn S u v) :
    ∃ U : Finset ℕ, U ⊆ S ∧ (∃ l : ℕ∞, (U : Set ℕ).IsAPOfLength l) ∧
      u ∈ U ∧ v ∈ U ∧ ∀ x : ℕ, HasAPCover S {u, v, x} ↔ x ∈ U := by
  classical
  let D : Finset (Finset ℕ) := S.powerset.filter
    (fun T : Finset ℕ => (∃ l : ℕ∞, (T : Set ℕ).IsAPOfLength l) ∧ u ∈ T ∧ v ∈ T)
  let U : Finset ℕ := D.biUnion id
  have hpairS : {u, v} ⊆ S := by simp [Finset.insert_subset_iff, hcon.1, hcon.2.1]
  have hpairAP : (({u, v} : Finset ℕ) : Set ℕ).IsAPOfLength 2 :=
    by simpa using Nat.isAPOfLength_pair hcon.2.2.1
  have hpairD : {u, v} ∈ D := Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr hpairS, ⟨2, hpairAP⟩, by simp, by simp⟩
  have huU : u ∈ U := Finset.mem_biUnion.mpr ⟨{u, v}, hpairD, by simp⟩
  have hvU : v ∈ U := Finset.mem_biUnion.mpr ⟨{u, v}, hpairD, by simp⟩
  have hUclass : FixedGapAP u v U := union_closed_biUnion (fixedGapAP_empty u v)
      (fun S T hS hT => fixedGapAP_union hS hT) D id (by
    intro T hT
    obtain ⟨hTS, hAP, huT, hvT⟩ := Finset.mem_filter.mp hT
    exact Or.inr ⟨hAP, hcon.subset (Finset.mem_powerset.mp hTS) huT hvT⟩)
  have hUAP : ∃ l : ℕ∞, (U : Set ℕ).IsAPOfLength l := by
    rcases hUclass with heq | h
    · simp [heq] at huU
    · exact h.1
  have hUsub : U ⊆ S := by
    intro x hx
    obtain ⟨T, hT, hxT⟩ := Finset.mem_biUnion.mp hx
    exact Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1 hxT
  refine ⟨U, hUsub, hUAP, huU, hvU, ?_⟩
  intro x
  constructor
  · rintro ⟨T, hTS, hAP, hcover⟩
    have hTD : T ∈ D := Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr hTS, hAP, hcover (by simp), hcover (by simp)⟩
    exact Finset.mem_biUnion.mpr ⟨T, hTD, hcover (by simp)⟩
  · intro hx
    exact ⟨U, hUsub, hUAP, by simp [Finset.insert_subset_iff, huU, hvU, hx]⟩

theorem natAP_first_eq_of_min {a c d k : ℕ} (hc : c ∈ natAP a d k)
    (hmin : ∀ x ∈ natAP a d k, c ≤ x) : a = c := by
  obtain ⟨i, hi, hci⟩ := mem_natAP.mp hc
  have ha : a ∈ natAP a d k := mem_natAP.mpr ⟨0, by omega, by simp⟩
  have hca := hmin a ha
  omega

theorem nat_ap_eq_at_min {S : Finset ℕ} {c : ℕ}
    (hAP : ∃ l : ℕ∞, (S : Set ℕ).IsAPOfLength l) (hcard : 2 ≤ S.card)
    (hc : c ∈ S) (hmin : ∀ x ∈ S, c ≤ x) :
    ∃ d : ℕ, 0 < d ∧ S = natAP c d S.card := by
  obtain ⟨l, hAP⟩ := hAP
  obtain ⟨a, d, hd, heq⟩ := nat_ap_eq_natAP hAP hcard
  have hac : a = c := natAP_first_eq_of_min (heq ▸ hc)
    (fun x hx => hmin x (heq.symm ▸ hx))
  exact ⟨d, hd, by simpa only [hac] using heq⟩

theorem natAP_filter_le {a d k R : ℕ} (hd : 0 < d) (haR : a ≤ R) :
    (natAP a d k).filter (fun x => x ≤ R) = natAP a d (min k ((R - a) / d + 1)) := by
  ext x
  simp only [Finset.mem_filter, mem_natAP]
  constructor
  · rintro ⟨⟨i, hi, heq⟩, hxR⟩
    refine ⟨i, lt_min hi ?_, heq⟩
    apply Nat.lt_succ_of_le
    apply (Nat.le_div_iff_mul_le hd).mpr
    omega
  · rintro ⟨i, hi, heq⟩
    obtain ⟨hik, hiR⟩ := lt_min_iff.mp hi
    refine ⟨⟨i, hik, heq⟩, ?_⟩
    have hh : i * d ≤ R - a := (Nat.le_div_iff_mul_le hd).mp (by omega : i ≤ (R - a) / d)
    omega

theorem hasAPCover_of_not_witness {S P : Finset ℕ} {c : ℕ}
    (hcard : P.card = 2) (hsub : P ⊆ S.erase c) (hnot : ¬ IsWitnessPair S c P) :
    HasAPCover S (insert c P) := by
  by_contra hcover
  exact hnot ⟨hcard, hsub, hcover⟩

theorem hasAPCover_at_min {S : Finset ℕ} {c x y : ℕ}
    (hmin : ∀ z ∈ S, c ≤ z) (hcx : c < x) (hcover : HasAPCover S {c, x, y}) :
    ∃ d k : ℕ, 0 < d ∧ 2 ≤ k ∧ natAP c d k ⊆ S ∧
      x ∈ natAP c d k ∧ y ∈ natAP c d k := by
  obtain ⟨U, hUS, hUAP, hUcover⟩ := hcover
  have hcU : c ∈ U := hUcover (by simp)
  have hxU : x ∈ U := hUcover (by simp)
  have hyU : y ∈ U := hUcover (by simp)
  have hUcard : 2 ≤ U.card := by
    have hsub : {c, x} ⊆ U := by simp [Finset.insert_subset_iff, hcU, hxU]
    simpa [hcx.ne] using Finset.card_le_card hsub
  obtain ⟨d, hd, heq⟩ := nat_ap_eq_at_min hUAP hUcard hcU (fun z hz => hmin z (hUS hz))
  exact ⟨d, U.card, hd, hUcard, heq ▸ hUS, heq ▸ hxU, heq ▸ hyU⟩

end
section
open Finset

def InExteriorCorner (c L R : ℕ) (P : Finset ℕ) : Prop :=
  ∃ u v : ℕ, c < u ∧ u < L ∧ R < v ∧ P = {u, v}

theorem exterior_corner_pair_iff {c L R u v : ℕ} (hLR : L ≤ R) (huv : u < v) :
    InExteriorCorner c L R {u, v} ↔ c < u ∧ u < L ∧ R < v := by
  constructor
  · rintro ⟨a, b, hca, haL, hRb, heq⟩
    have hab : a < b := by omega
    have hpair := sorted_pair_finset_injective huv hab heq
    have hua : u = a := congrArg Prod.fst hpair
    have hvb : v = b := congrArg Prod.snd hpair
    exact ⟨by omega, by omega, by omega⟩
  · rintro ⟨hcu, huL, hRv⟩
    exact ⟨u, v, hcu, huL, hRv, rfl⟩

theorem exterior_corner_mem_gt {c L R x : ℕ} {P : Finset ℕ}
    (hLR : L ≤ R) (hP : InExteriorCorner c L R P) (hx : x ∈ P) : c < x := by
  obtain ⟨u, v, hcu, huL, hRv, rfl⟩ := hP
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  omega

theorem exterior_witness_min {S : Finset ℕ} {c L R : ℕ}
    (hcrooked : IsCrooked S) (hc : c ∈ S) (hLR : L ≤ R)
    (hcorner : ∀ P, IsWitnessPair S c P → InExteriorCorner c L R P) :
    ∀ x ∈ S, c ≤ x := by
  intro x hx
  by_contra hcx
  obtain ⟨a, ha⟩ := exists_consecutive_left_of_mem hx hc (by omega)
  obtain ⟨b, hb⟩ := witness_pair_of_left_neighbor hcrooked ha
  have hca := exterior_corner_mem_gt hLR (hcorner {a, b} hb) (by simp : a ∈ ({a, b} : Finset ℕ))
  have hac := ha.2.2.1
  omega

theorem exterior_witness_neighbor {S : Finset ℕ} {c L R : ℕ}
    (hcrooked : IsCrooked S) (hc : c ∈ S) (hLR : L ≤ R)
    (hcorner : ∀ P, IsWitnessPair S c P → InExteriorCorner c L R P) :
    ∃ a : ℕ, ConsecutiveIn S c a ∧ a < L := by
  have hmin := exterior_witness_min hcrooked hc hLR hcorner
  obtain ⟨a, ha | ha⟩ := exists_consecutive_at_mem hc (crooked_card_ge_two hcrooked hc)
  · have hh := hmin a ha.1
    have hlt := ha.2.2.1
    omega
  · obtain ⟨b, hb⟩ := witness_pair_of_right_neighbor hcrooked ha
    obtain ⟨u, v, hcu, huL, hRv, hpair⟩ := hcorner {a, b} hb
    have haPair : a = u ∨ a = v := by
      have hh : a ∈ ({u, v} : Finset ℕ) := by rw [← hpair]; simp
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hh
    refine ⟨a, ha, ?_⟩
    rcases haPair with rfl | rfl
    · exact huL
    · have huS : u ∈ S := Finset.mem_of_mem_erase
        (hb.2.1 (by rw [hpair]; simp))
      exact False.elim (ha.2.2.2 u huS ⟨hcu, by omega⟩)

theorem exterior_witness_prefix {S : Finset ℕ} {c L R : ℕ}
    (hcrooked : IsCrooked S) (hc : c ∈ S) (hLR : L ≤ R)
    (hcorner : ∀ P, IsWitnessPair S c P → InExteriorCorner c L R P) :
    ∃ d h : ℕ, 0 < d ∧ d < L - c ∧ 1 ≤ h ∧
      (∀ x ∈ S, c ≤ x) ∧ S.filter (fun x => x ≤ R) = natAP c d (h + 1) ∧
      c + h * d ≤ R ∧ ∃ v ∈ S, R < v := by
  have hmin := exterior_witness_min hcrooked hc hLR hcorner
  obtain ⟨a, hcon, haL⟩ := exterior_witness_neighbor hcrooked hc hLR hcorner
  have hca := hcon.2.2.1
  have hcR : c ≤ R := by omega
  obtain ⟨U, hUS, hUAP, hcU, haU, hcover⟩ := consecutive_AP_core hcon
  have hconU := hcon.subset hUS hcU haU
  have hUcard := hconU.card_ge_two
  obtain ⟨d, hd, heq⟩ := nat_ap_eq_at_min hUAP hUcard hcU (fun x hx => hmin x (hUS hx))
  have hgap : d = a - c := natAP_step_of_consecutive hd (heq ▸ hconU)
  have hcad : c + d = a := by omega
  have hprefix : S.filter (fun x => x ≤ R) = U.filter (fun x => x ≤ R) := by
    ext x
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hxS, hxR⟩
      refine ⟨?_, hxR⟩
      by_cases hxc : x = c
      · simpa only [hxc] using hcU
      by_cases hxa : x = a
      · simpa only [hxa] using haU
      apply (hcover x).mp
      apply hasAPCover_of_not_witness (by simp [Ne.symm hxa])
      · intro y hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl
        · exact Finset.mem_erase.mpr ⟨hca.ne', hcon.2.1⟩
        · exact Finset.mem_erase.mpr ⟨hxc, hxS⟩
      · intro hW
        obtain ⟨u, v, hcu, huL, hRv, he⟩ := hcorner {a, x} hW
        have hv : v = a ∨ v = x := by
          have hh : v ∈ ({a, x} : Finset ℕ) := by rw [he]; simp
          simpa only [Finset.mem_insert, Finset.mem_singleton] using hh
        omega
    · rintro ⟨hxU, hxR⟩
      exact ⟨hUS hxU, hxR⟩
  rw [heq, natAP_filter_le hd hcR] at hprefix
  let k := min U.card ((R - c) / d + 1)
  have hk : 2 ≤ k := by
    apply le_min hUcard
    have hdiv : 1 ≤ (R - c) / d := (Nat.le_div_iff_mul_le hd).mpr (by omega)
    omega
  let h := k - 1
  have hkh : k = h + 1 := by dsimp [h]; omega
  have hprefix' : S.filter (fun x => x ≤ R) = natAP c d (h + 1) := by
    change S.filter (fun x => x ≤ R) = natAP c d k at hprefix
    simpa only [hkh] using hprefix
  have htop : c + h * d ∈ S.filter (fun x => x ≤ R) := by
    rw [hprefix']
    exact mem_natAP.mpr ⟨h, by omega, rfl⟩
  have htail : ∃ v ∈ S, R < v := by
    by_contra! hh
    have hfilter : S.filter (fun x => x ≤ R) = S := Finset.filter_eq_self.mpr hh
    apply hcrooked
    refine ⟨(h + 1 : ℕ), ?_⟩
    rw [← hfilter, hprefix']
    exact natAP_isAP hd
  exact ⟨d, h, hd, by omega, by dsimp [h]; omega, hmin, hprefix',
    (Finset.mem_filter.mp htop).2, htail⟩

end
section
open Finset

theorem totient_le_of_no_coprime_middle {m a h : ℕ}
    (hgap : ∀ j : ℕ, a ≤ j → j ≤ h → ¬ j.Coprime m) :
    m.totient ≤ 2 * a + (m - 2 * h) := by
  let D := (Finset.Icc 1 m).filter (fun j => m.Coprime j)
  let U := Finset.range a ∪ (Finset.range a).image (fun j => m - j) ∪ Finset.Ioo h (m - h)
  have hcover : D ⊆ U := by
    intro j hj
    obtain ⟨hjI, hcop⟩ := Finset.mem_filter.mp hj
    have hjm := (Finset.mem_Icc.mp hjI).2
    by_cases hja : j < a
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_range.mpr hja))
    by_cases hjh : j ≤ h
    · exact False.elim (hgap j (by omega) hjh hcop.symm)
    by_cases hma : m - j < a
    · apply Finset.mem_union_left
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨m - j, Finset.mem_range.mpr hma, by omega⟩
    by_cases hmh : m - j ≤ h
    · have hcop' : (m - j).Coprime m := (Nat.coprime_self_sub_left hjm).mpr hcop.symm
      exact False.elim (hgap (m - j) (by omega) hmh hcop')
    · exact Finset.mem_union_right _ (Finset.mem_Ioo.mpr ⟨by omega, by omega⟩)
  have hmid : (Finset.Ioo h (m - h)).card ≤ m - 2 * h := by
    simp only [Nat.card_Ioo]
    omega
  have himage : ((Finset.range a).image (fun j => m - j)).card ≤ a := by
    simpa using Finset.card_image_le (s := Finset.range a) (f := fun j => m - j)
  have hUcard : U.card ≤ 2 * a + (m - 2 * h) := by
    have h1 := Finset.card_union_le (Finset.range a) ((Finset.range a).image (fun j => m - j))
    have h2 := Finset.card_union_le
      (Finset.range a ∪ (Finset.range a).image (fun j => m - j)) (Finset.Ioo h (m - h))
    simp only [Finset.card_range] at h1
    change U.card ≤ _ at h2
    omega
  have hD : D.card = m.totient := card_coprime_Icc m
  rw [← hD]
  exact (Finset.card_le_card hcover).trans hUcard

theorem exists_coprime_middle {m a h : ℕ}
    (hlarge : (2 * a + (m - 2 * h)) * (Nat.log 2 m + 1) < m) :
    ∃ j : ℕ, a ≤ j ∧ j ≤ h ∧ j.Coprime m := by
  by_contra hnone
  have hphi : m.totient ≤ 2 * a + (m - 2 * h) := totient_le_of_no_coprime_middle
    (fun j haj hjh hjcop => hnone ⟨j, haj, hjh, hjcop⟩)
  have hh := (le_log_succ_mul_totient m).trans
    (Nat.mul_le_mul_left (Nat.log 2 m + 1) hphi)
  nlinarith

theorem exists_coprime_in_prefix_core {N c L R d h m : ℕ}
    (hcL : c < L) (hLR : L ≤ R) (hRN : R ≤ N) (hd : 0 < d) (hdL : d ≤ L)
    (hN : 256 * (L + N - R) * (Nat.log 2 N + 1) ≤ N)
    (hmR : R < c + m * d) (hmN : c + m * d ≤ N)
    (hhalf : R + c < 2 * (c + h * d)) :
    ∃ j : ℕ, L ≤ c + j * d ∧ j ≤ h ∧ j.Coprime m := by
  let t := L + N - R
  let a := (L - c) / d + 1
  let q := 2 * a + (m - 2 * h)
  let K := Nat.log 2 N + 1
  have hLt : L ≤ t := by dsimp [t]; omega
  have hct : c ≤ t := hcL.le.trans hLt
  have htp : 0 < t := by omega
  have htR : t + R = L + N := by dsimp [t]; omega
  have hNR : N - R + R = N := Nat.sub_add_cancel hRN
  have hLc : L - c + c = L := Nat.sub_add_cancel hcL.le
  have hmN' : m ≤ N := by
    have hmul : m ≤ m * d := Nat.le_mul_of_pos_right m hd
    omega
  have ha : d * a ≤ L - c + d := by
    have hh := Nat.mul_div_le (L - c) d
    dsimp [a]
    nlinarith
  have hmid : d * (m - 2 * h) ≤ N - R := by
    by_cases hmh : 2 * h ≤ m
    · have heq : m - 2 * h + 2 * h = m := Nat.sub_add_cancel hmh
      nlinarith
    · have heq : m - 2 * h = 0 := by omega
      simp [heq]
  have hq : d * q ≤ 4 * t := by
    dsimp [q]
    nlinarith
  have hK : 1 ≤ K := by dsimp [K]; omega
  have hlog : Nat.log 2 m + 1 ≤ K := Nat.add_le_add_right (Nat.log_mono_right hmN') 1
  have hlarge : q * (Nat.log 2 m + 1) < m := by
    by_contra hh
    have hm : m ≤ q * K := (by omega : m ≤ q * (Nat.log 2 m + 1)).trans
      (Nat.mul_le_mul_left q hlog)
    have hbound : d * m ≤ 4 * t * K := by
      calc
        d * m ≤ d * (q * K) := Nat.mul_le_mul_left d hm
        _ = (d * q) * K := by ring
        _ ≤ (4 * t) * K := Nat.mul_le_mul_right K hq
    change 256 * t * K ≤ N at hN
    have hprod : t ≤ t * K := by nlinarith
    nlinarith
  obtain ⟨j, haj, hjh, hjcop⟩ := exists_coprime_middle hlarge
  refine ⟨j, ?_, hjh, hjcop⟩
  have hj : (L - c) / d < j := by change (L - c) / d + 1 ≤ j at haj; omega
  have hmul : L - c < j * d := (Nat.div_lt_iff_lt_mul hd).mp hj
  omega

end
section
open Finset

theorem prefix_top_mem {S : Finset ℕ} {c d h R : ℕ}
    (hprefix : S.filter (fun x => x ≤ R) = natAP c d (h + 1)) :
    c + h * d ∈ S := by
  have hh : c + h * d ∈ S.filter (fun x => x ≤ R) := by
    rw [hprefix]
    exact mem_natAP.mpr ⟨h, by omega, rfl⟩
  exact (Finset.mem_filter.mp hh).1

theorem prefix_le_top {S : Finset ℕ} {c d h R x : ℕ}
    (hprefix : S.filter (fun y => y ≤ R) = natAP c d (h + 1))
    (hx : x ∈ S) (hxR : x ≤ R) : x ≤ c + h * d := by
  have hh : x ∈ natAP c d (h + 1) := hprefix ▸ Finset.mem_filter.mpr ⟨hx, hxR⟩
  obtain ⟨i, hi, hxi⟩ := mem_natAP.mp hh
  have hmul := Nat.mul_le_mul_right d (by omega : i ≤ h)
  omega

theorem prefix_dvd_offset {S : Finset ℕ} {c d h R x : ℕ}
    (hprefix : S.filter (fun y => y ≤ R) = natAP c d (h + 1))
    (hx : x ∈ S) (hxR : x ≤ R) : d ∣ x - c := by
  have hh : x ∈ natAP c d (h + 1) := hprefix ▸ Finset.mem_filter.mpr ⟨hx, hxR⟩
  obtain ⟨i, hi, hxi⟩ := mem_natAP.mp hh
  refine ⟨i, ?_⟩
  rw [← hxi, Nat.add_sub_cancel_left, Nat.mul_comm]

theorem prefix_step_divides_cover_step {S : Finset ℕ} {c d h R e k x : ℕ}
    (hprefix : S.filter (fun y => y ≤ R) = natAP c d (h + 1))
    (_he : 0 < e) (hcover : natAP c e k ⊆ S) (hcx : c < x)
    (hx : x ∈ natAP c e k) (hxR : x ≤ R) : d ∣ e := by
  obtain ⟨i, hi, hxi⟩ := mem_natAP.mp hx
  have hi1 : 1 ≤ i := by
    by_contra hh
    have hi0 : i = 0 := by omega
    simp only [hi0, zero_mul, add_zero] at hxi
    omega
  have hstep : c + e ∈ S := hcover (mem_natAP.mpr ⟨1, by omega, by simp⟩)
  have hmul := Nat.mul_le_mul_right e hi1
  have hstepR : c + e ≤ R := by omega
  simpa only [Nat.add_sub_cancel_left] using prefix_dvd_offset hprefix hstep hstepR

theorem distant_consecutive_witness {S : Finset ℕ} {c x y : ℕ}
    (hmin : ∀ z ∈ S, c ≤ z) (hcx : c < x)
    (hcon : ConsecutiveIn S x y) (hgap : 2 * x < c + y) :
    IsWitnessPair S c {x, y} := by
  refine ⟨by simp [hcon.2.2.1.ne], ?_, ?_⟩
  · intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact Finset.mem_erase.mpr ⟨hcx.ne', hcon.1⟩
    · exact Finset.mem_erase.mpr ⟨by have hh := hcon.2.2.1; omega, hcon.2.1⟩
  · intro hcover
    obtain ⟨e, k, he, hk, hAS, hxA, hyA⟩ := hasAPCover_at_min hmin hcx hcover
    have hconA := hcon.subset hAS hxA hyA
    have hstep : e = y - x := natAP_step_of_consecutive he hconA
    obtain ⟨i, hi, hxi⟩ := mem_natAP.mp hxA
    have hi1 : 1 ≤ i := by
      by_contra hh
      have hi0 : i = 0 := by omega
      simp only [hi0, zero_mul, add_zero] at hxi
      omega
    have hmul := Nat.mul_le_mul_right e hi1
    have hxy := hcon.2.2.1
    omega

theorem prefix_top_cover_analysis {S : Finset ℕ} {c d h R v : ℕ}
    (hd : 0 < d) (hh : 1 ≤ h)
    (hprefix : S.filter (fun x => x ≤ R) = natAP c d (h + 1))
    (hmin : ∀ x ∈ S, c ≤ x) (htopR : c + h * d ≤ R) (hvR : R < v)
    (hcover : HasAPCover S {c, c + h * d, v}) :
    d ∣ v - c ∧ R + c < 2 * (c + h * d) := by
  let z := c + h * d
  have hcz : c < z := by
    have hpos : 0 < h * d := Nat.mul_pos (by omega) hd
    dsimp [z]
    omega
  obtain ⟨e, k, he, hk, hAS, hzA, hvA⟩ := hasAPCover_at_min hmin hcz hcover
  have hde : d ∣ e := prefix_step_divides_cover_step hprefix he hAS hcz hzA htopR
  obtain ⟨i, hi, hzi⟩ := mem_natAP.mp hzA
  obtain ⟨j, hj, hvj⟩ := mem_natAP.mp hvA
  have hi1 : 1 ≤ i := by
    by_contra hlt
    have hi0 : i = 0 := by omega
    simp only [hi0, zero_mul, add_zero] at hzi
    omega
  have hij : i < j := by
    by_contra hlt
    have hmul := Nat.mul_le_mul_right e (by omega : j ≤ i)
    dsimp [z] at hzi
    omega
  have hzstep : z + e ∈ S := hAS (mem_natAP.mpr ⟨i + 1, by omega, by nlinarith⟩)
  have hzstepR : R < z + e := by
    by_contra hle
    have hbound := prefix_le_top hprefix hzstep (by omega : z + e ≤ R)
    change z + e ≤ z at hbound
    omega
  constructor
  · have hev : e ∣ v - c := by
      refine ⟨j, ?_⟩
      rw [← hvj, Nat.add_sub_cancel_left, Nat.mul_comm]
    exact hde.trans hev
  · have hmul := Nat.mul_le_mul_right e hi1
    change R + c < 2 * z
    omega

theorem prefix_reaches_core {S : Finset ℕ} {c L R d h : ℕ}
    (hd : 0 < d) (hh : 1 ≤ h)
    (hprefix : S.filter (fun x => x ≤ R) = natAP c d (h + 1))
    (hmin : ∀ x ∈ S, c ≤ x) (htopR : c + h * d ≤ R)
    (htail : ∃ v ∈ S, R < v) (hwide : 2 * L ≤ R + c)
    (hbetween : ∀ u v : ℕ, u < v → IsWitnessPair S c {u, v} →
      ∃ x ∈ S, u < x ∧ x < v) : L ≤ c + h * d := by
  let z := c + h * d
  by_contra hzL
  let B := S.filter (fun v => R < v)
  have hB : B.Nonempty := by
    obtain ⟨v, hvS, hRv⟩ := htail
    exact ⟨v, Finset.mem_filter.mpr ⟨hvS, hRv⟩⟩
  let v := B.min' hB
  obtain ⟨hvS, hRv⟩ := Finset.mem_filter.mp (Finset.min'_mem B hB)
  have hzS : z ∈ S := prefix_top_mem hprefix
  have hcz : c < z := by
    have hpos : 0 < h * d := Nat.mul_pos (by omega) hd
    dsimp [z]
    omega
  have hcon : ConsecutiveIn S z v := by
    refine ⟨hzS, hvS, by dsimp [z]; omega, ?_⟩
    intro x hx hzxv
    by_cases hxR : x ≤ R
    · have hh := prefix_le_top hprefix hx hxR
      change x ≤ z at hh
      omega
    · have hxB : x ∈ B := Finset.mem_filter.mpr ⟨hx, by omega⟩
      have hvx : v ≤ x := Finset.min'_le B x hxB
      omega
  have hgap : 2 * z < c + v := by omega
  have hW := distant_consecutive_witness hmin hcz hcon hgap
  obtain ⟨x, hxS, hzx, hxv⟩ := hbetween z v hcon.2.2.1 hW
  exact hcon.2.2.2 x hxS ⟨hzx, hxv⟩

end
section
open Finset

theorem exterior_witness_contradiction {N c L R : ℕ} {S : Finset ℕ}
    (hcL : c < L) (hLR : L ≤ R) (hRN : R ≤ N)
    (hN : 256 * (L + N - R) * (Nat.log 2 N + 1) ≤ N)
    (hsub : S ⊆ Finset.Icc 1 N) (hcrooked : IsCrooked S) (hc : c ∈ S)
    (hcorner : ∀ P, IsWitnessPair S c P → InExteriorCorner c L R P)
    (hbetween : ∀ u v : ℕ, u < v → IsWitnessPair S c {u, v} →
      ∃ x ∈ S, u < x ∧ x < v) : False := by
  obtain ⟨d, h, hd, hdL, hh, hmin, hprefix, htopR, htail⟩ :=
    exterior_witness_prefix hcrooked hc hLR hcorner
  let z := c + h * d
  have hzS : z ∈ S := prefix_top_mem hprefix
  have hcz : c < z := by
    have hpos := Nat.mul_pos (by omega : 0 < h) hd
    dsimp [z]
    omega
  have hwide : 2 * L ≤ R + c := by
    have hmul : 256 * (L + N - R) ≤ 256 * (L + N - R) * (Nat.log 2 N + 1) :=
      Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hzL : L ≤ z := prefix_reaches_core hd hh hprefix hmin htopR htail hwide hbetween
  have htopCover : ∀ v ∈ S, R < v → HasAPCover S {c, z, v} := by
    intro v hvS hRv
    have hzv : z < v := by dsimp [z]; omega
    apply hasAPCover_of_not_witness (by simp [hzv.ne])
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact Finset.mem_erase.mpr ⟨hcz.ne', hzS⟩
      · exact Finset.mem_erase.mpr ⟨by omega, hvS⟩
    · intro hW
      have hbad := (exterior_corner_pair_iff hLR hzv).mp (hcorner {z, v} hW)
      omega
  have hgrid : ∀ x ∈ S, d ∣ x - c := by
    intro x hx
    by_cases hxR : x ≤ R
    · exact prefix_dvd_offset hprefix hx hxR
    · exact (prefix_top_cover_analysis hd hh hprefix hmin htopR (by omega)
        (htopCover x hx (by omega))).1
  have hSnonempty : S.Nonempty := ⟨c, hc⟩
  let v := S.max' hSnonempty
  have hvS : v ∈ S := Finset.max'_mem S hSnonempty
  have hmax : ∀ x ∈ S, x ≤ v := fun x hx => Finset.le_max' S x hx
  have hRv : R < v := by
    obtain ⟨w, hwS, hRw⟩ := htail
    have hwv := hmax w hwS
    omega
  have hcv : c ≤ v := hmin v hvS
  have hvN : v ≤ N := (Finset.mem_Icc.mp (hsub hvS)).2
  obtain ⟨m, hm⟩ := hgrid v hvS
  have hvm : v = c + m * d := by
    have hvsub := Nat.sub_add_cancel hcv
    nlinarith only [hm, hvsub]
  have hhalf : R + c < 2 * (c + h * d) :=
    (prefix_top_cover_analysis hd hh hprefix hmin htopR hRv (htopCover v hvS hRv)).2
  obtain ⟨j, hjL, hjh, hjcop⟩ := exists_coprime_in_prefix_core hcL hLR hRN hd
    (by omega : d ≤ L) hN (by simpa only [hvm] using hRv)
    (by simpa only [hvm] using hvN) hhalf
  let u := c + j * d
  have huR : u ≤ R := by
    have hmul := Nat.mul_le_mul_right d hjh
    dsimp [u]
    omega
  have huS : u ∈ S := by
    have hu : u ∈ S.filter (fun x => x ≤ R) := by
      rw [hprefix]
      exact mem_natAP.mpr ⟨j, by omega, rfl⟩
    exact (Finset.mem_filter.mp hu).1
  have hcu : c < u := by dsimp [u]; omega
  have huv : u < v := by omega
  have huCover : HasAPCover S {c, u, v} := by
    apply hasAPCover_of_not_witness (by simp [huv.ne])
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact Finset.mem_erase.mpr ⟨hcu.ne', huS⟩
      · exact Finset.mem_erase.mpr ⟨by omega, hvS⟩
    · intro hW
      have hbad := (exterior_corner_pair_iff hLR huv).mp (hcorner {u, v} hW)
      dsimp [u] at hbad
      omega
  obtain ⟨e, k, he, hk, hAS, huA, hvA⟩ := hasAPCover_at_min hmin hcu huCover
  have hde : d ∣ e := prefix_step_divides_cover_step hprefix he hAS hcu huA huR
  obtain ⟨i, hi, hui⟩ := mem_natAP.mp huA
  obtain ⟨i', hi', hvi'⟩ := mem_natAP.mp hvA
  have hejd : e ∣ j * d := by
    refine ⟨i, ?_⟩
    dsimp [u] at hui
    nlinarith only [hui]
  have hemd : e ∣ m * d := by
    refine ⟨i', ?_⟩
    rw [hvm] at hvi'
    nlinarith only [hvi']
  have hed : e ∣ d := by
    have hdiv := Nat.dvd_gcd hejd hemd
    have hgcd : (j * d).gcd (m * d) = d := by
      rw [Nat.gcd_mul_right, hjcop.gcd_eq_one, Nat.one_mul]
    simpa only [hgcd] using hdiv
  have hedEq : e = d := Nat.dvd_antisymm hed hde
  have hvA' : v ∈ natAP c d k := by simpa only [hedEq] using hvA
  have hAS' : natAP c d k ⊆ S := by simpa only [hedEq] using hAS
  have hSA : S ⊆ natAP c d k := by
    obtain ⟨b, hb, hvb⟩ := mem_natAP.mp hvA'
    intro x hx
    obtain ⟨a, ha⟩ := hgrid x hx
    have hcx : c ≤ x := hmin x hx
    have hxa : x = c + a * d := by
      have hsubx := Nat.sub_add_cancel hcx
      nlinarith only [hsubx, ha]
    have hxab : a ≤ b := by
      have hxv := hmax x hx
      by_contra hab
      have hmul := Nat.mul_lt_mul_of_pos_right (by omega : b < a) hd
      omega
    exact mem_natAP.mpr ⟨a, lt_of_le_of_lt hxab hb, hxa.symm⟩
  have hS_eq : S = natAP c d k := Finset.Subset.antisymm hSA hAS'
  exact hcrooked ⟨k, hS_eq.symm ▸ natAP_isAP hd⟩

theorem exists_witness_outside_exterior_pairs {N c L R : ℕ}
    {S : Finset ℕ} {W : Finset (Finset ℕ)}
    (hcL : c < L) (hLR : L ≤ R) (hRN : R ≤ N)
    (hN : 256 * (L + N - R) * (Nat.log 2 N + 1) ≤ N)
    (hsub : S ⊆ Finset.Icc 1 N) (hcrooked : IsCrooked S) (hc : c ∈ S)
    (hW : ∀ P ∈ W, InExteriorCorner c L R P)
    (hbetween : ∀ u v : ℕ, u < v → ({u, v} : Finset ℕ) ∈ W →
      ∃ x ∈ S, u < x ∧ x < v) :
    ∃ P : Finset ℕ, IsWitnessPair S c P ∧ P ∉ W := by
  by_contra hnone
  have hinW : ∀ P, IsWitnessPair S c P → P ∈ W := by
    intro P hP
    by_contra hPW
    exact hnone ⟨P, hP, hPW⟩
  exact exterior_witness_contradiction hcL hLR hRN hN hsub hcrooked hc
    (fun P hP => hW P (hinW P hP))
    (fun u v huv hP => hbetween u v huv (hinW {u, v} hP))

end
section
open Finset

theorem erase_not_mem_exterior_pairs {c L R : ℕ} {S : Finset ℕ} {W : Finset (Finset ℕ)}
    (hc : c ∈ S) (hLR : L ≤ R) (hW : ∀ P ∈ W, InExteriorCorner c L R P)
    (hbetween : ∀ u v : ℕ, u < v → ({u, v} : Finset ℕ) ∈ W →
      ∃ x ∈ S, u < x ∧ x < v) : S.erase c ∉ W := by
  intro hPW
  obtain ⟨u, v, hcu, huL, hRv, heq⟩ := hW (S.erase c) hPW
  have huv : u < v := by omega
  obtain ⟨x, hxS, hux, hxv⟩ := hbetween u v huv (by simpa only [heq] using hPW)
  have hS : S = insert c {u, v} := by rw [← heq, Finset.insert_erase hc]
  have hx : x = c ∨ x = u ∨ x = v := by
    simpa only [hS, Finset.mem_insert, Finset.mem_singleton] using hxS
  omega

theorem exists_star_matching_outside_exterior_pairs {N c L R : ℕ}
    {F : Finset (Finset ℕ)} {W : Finset (Finset ℕ)}
    (hcL : c < L) (hLR : L ≤ R) (hRN : R ≤ N)
    (hN : 256 * (L + N - R) * (Nat.log 2 N + 1) ≤ N)
    (hF : Erdos272.IsArithInterSet N F) (hc : ∀ S ∈ F, c ∈ S)
    (hcard : ∀ S ∈ F, 3 ≤ S.card)
    (hW : ∀ P ∈ W, InExteriorCorner c L R P)
    (hbetween : ∀ S ∈ F, ∀ u v : ℕ, u < v → ({u, v} : Finset ℕ) ∈ W →
      ∃ x ∈ S, u < x ∧ x < v) :
    ∃ f : {S // S ∈ F} → Option (Finset ℕ),
      (∀ S P, f S = some P → P.card = 2 ∧ P ⊆ S.val.erase c) ∧
      (∀ S P, f S = some P → P ∉ W) ∧
      (∀ S T P, f S = some P → f T = some P → S = T) ∧
      (Finset.univ.filter (fun S => f S = none)).card ≤ 20000 * N := by
  apply exists_common_point_pair_matching_allowed hF hc hcard
  · intro S hS hcrooked
    exact exists_witness_outside_exterior_pairs hcL hLR hRN hN
      (Finset.mem_powerset.mp (hF.1 hS)) hcrooked (hc S hS) hW (hbetween S hS)
  · intro S hS h3
    exact erase_not_mem_exterior_pairs (hc S hS) hLR hW (hbetween S hS)
  · intro G hGF hAP h4
    obtain ⟨g, hvalid, hinj, hmiss⟩ := exists_natural_corner_pair_matching hcL hLR hRN hN
      (fun S hS => Finset.mem_powerset.mp (hF.1 (hGF hS))) hAP h4
      (fun S hS => hc S (hGF hS))
    refine ⟨g, ?_, hinj, hmiss⟩
    intro S q hq
    obtain ⟨d, hd, hdN, hnat, havoid⟩ := hvalid S q hq
    refine ⟨d, hd, hdN, hnat, ?_⟩
    intro hPW
    exact havoid ((exterior_corner_pair_iff hLR hnat.2.2.1).mp (hW _ hPW))

theorem star_card_le_with_reserved_pairs {N c L R : ℕ}
    {F : Finset (Finset ℕ)} {W : Finset (Finset ℕ)}
    (hcL : c < L) (hLR : L ≤ R) (hRN : R ≤ N)
    (hN : 256 * (L + N - R) * (Nat.log 2 N + 1) ≤ N)
    (hF : Erdos272.IsArithInterSet N F) (hc : ∀ S ∈ F, c ∈ S)
    (hW : ∀ P ∈ W, InExteriorCorner c L R P)
    (hbetween : ∀ S ∈ F, ∀ u v : ℕ, u < v → ({u, v} : Finset ℕ) ∈ W →
      ∃ x ∈ S, u < x ∧ x < v) :
    F.card ≤ (((Finset.Icc 1 N).powersetCard 2) \ W).card + 20001 * N := by
  classical
  let B := F.filter (fun S => S.card ≤ 2)
  let G := F.filter (fun S => ¬ S.card ≤ 2)
  have hB : B.card ≤ N := by
    have hh := small_common_point_card_le (F := B) (U := Finset.Icc 1 N) (c := c)
      (fun S hS => Finset.mem_powerset.mp (hF.1 (Finset.mem_filter.mp hS).1))
      (fun S hS => hc S (Finset.mem_filter.mp hS).1)
      (fun S hS => (Finset.mem_filter.mp hS).2)
    simpa using hh
  have hGF : G ⊆ F := Finset.filter_subset _ _
  obtain ⟨f, hvalid, hAllowed, hinj, hmiss⟩ := exists_star_matching_outside_exterior_pairs
    hcL hLR hRN hN (arithInterSet_mono hF hGF) (fun S hS => hc S (hGF hS))
    (fun S hS => by have hh := (Finset.mem_filter.mp hS).2; omega) hW
    (fun S hS => hbetween S (hGF hS))
  have hG : G.card ≤ (((Finset.Icc 1 N).powersetCard 2) \ W).card + 20000 * N := by
    have hh := partial_matching_card_le (B := ((Finset.Icc 1 N).powersetCard 2) \ W) f
      (fun S P hP => Finset.mem_sdiff.mpr ⟨Finset.mem_powersetCard.mpr
        ⟨(hvalid S P hP).2.trans ((Finset.erase_subset _ _).trans
          (Finset.mem_powerset.mp (hF.1 (hGF S.property)))), (hvalid S P hP).1⟩,
        hAllowed S P hP⟩) hinj hmiss
    simpa using hh
  have hpartition := Finset.card_filter_add_card_filter_not (s := F) (fun S => S.card ≤ 2)
  change B.card + G.card = F.card at hpartition
  omega

end
section
open Finset

theorem arithInter_nonempty {N : ℕ} {F : Finset (Finset ℕ)} {S T : Finset ℕ}
    (hF : Erdos272.IsArithInterSet N F) (hS : S ∈ F) (hT : T ∈ F) (hne : S ≠ T) :
    (S ∩ T).Nonempty := by
  obtain ⟨l, hl, hAP⟩ := hF.2 hS hT hne
  apply Finset.nonempty_iff_ne_empty.mpr
  intro hzero
  exact Set.not_isAPOfLength_empty hl (by simpa only [hzero, Finset.coe_empty] using hAP)

theorem exists_exterior_interval_pairs {N c L R : ℕ} {I : Finset (Finset ℕ)}
    (hLR : L ≤ R)
    (hI : ∀ S ∈ I, ∃ a b : ℕ, c + 1 < a ∧ a ≤ L ∧ R ≤ b ∧ b < N ∧ S = Finset.Icc a b) :
    ∃ W : Finset (Finset ℕ), W.card = I.card ∧ W ⊆ (Finset.Icc 1 N).powersetCard 2 ∧
      (∀ P ∈ W, InExteriorCorner c L R P) ∧
      (∀ u v : ℕ, u < v → ({u, v} : Finset ℕ) ∈ W →
        ∃ T ∈ I, T = Finset.Icc (u + 1) (v - 1)) := by
  classical
  let A := {S : Finset ℕ // S ∈ I}
  choose a b hca haL hRb hbN hset using (fun S : A => hI S.val S.property)
  let f : A → Finset ℕ := fun S => {a S - 1, b S + 1}
  let W : Finset (Finset ℕ) := Finset.univ.image f
  have hlt : ∀ S : A, a S - 1 < b S + 1 := by
    intro S
    have h1 := haL S
    have h2 := hRb S
    omega
  have hinj : Function.Injective f := by
    intro S T hST
    have heq := sorted_pair_finset_injective (hlt S) (hlt T) hST
    have ha := congrArg Prod.fst heq
    have hb := congrArg Prod.snd heq
    have haST : a S = a T := by have h1 := hca S; have h2 := hca T; omega
    have hbST : b S = b T := by omega
    apply Subtype.ext
    rw [hset S, hset T, haST, hbST]
  refine ⟨W, ?_, ?_, ?_, ?_⟩
  · simp only [W, Finset.card_image_of_injective _ hinj, Finset.card_univ, A, Fintype.card_coe]
  · intro P hP
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hP
    apply Finset.mem_powersetCard.mpr
    refine ⟨?_, by simp [f, (hlt S).ne]⟩
    intro x hx
    simp only [f, Finset.mem_insert, Finset.mem_singleton] at hx
    have h1 := hca S
    have h2 := haL S
    have h3 := hRb S
    have h4 := hbN S
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro P hP
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hP
    have h1 := hca S
    have h2 := haL S
    have h3 := hRb S
    exact ⟨a S - 1, b S + 1, by omega, by omega, by omega, rfl⟩
  · intro u v huv hP
    obtain ⟨S, hS, hfS⟩ := Finset.mem_image.mp hP
    have heq := sorted_pair_finset_injective (hlt S) huv hfS
    have hu := congrArg Prod.fst heq
    have hv := congrArg Prod.snd heq
    have haeq : a S = u + 1 := by have hh := hca S; omega
    have hbeq : b S = v - 1 := by omega
    exact ⟨S.val, S.property, by rw [hset S, haeq, hbeq]⟩

def boundaryIntervals (c N : ℕ) : Finset (Finset ℕ) :=
  ((Finset.Icc 1 N).image (fun b => Finset.Icc (c + 1) b)) ∪
    ((Finset.Icc 1 N).image (fun a => Finset.Icc a N))

theorem card_boundaryIntervals_le (c N : ℕ) : (boundaryIntervals c N).card ≤ 2 * N := by
  have hcard := Finset.card_union_le
    ((Finset.Icc 1 N).image (fun b => Finset.Icc (c + 1) b))
    ((Finset.Icc 1 N).image (fun a => Finset.Icc a N))
  have hleft := Finset.card_image_le (s := Finset.Icc 1 N) (f := fun b => Finset.Icc (c + 1) b)
  have hright := Finset.card_image_le (s := Finset.Icc 1 N) (f := fun a => Finset.Icc a N)
  simp only [Nat.card_Icc] at hleft hright
  change (boundaryIntervals c N).card ≤ _ at hcard
  omega

theorem long_core_family_card_le {N c L R : ℕ} {F : Finset (Finset ℕ)}
    (hcL : c < L) (hLR : L ≤ R) (hRN : R ≤ N)
    (hN : 256 * (L + N - R) * (Nat.log 2 N + 1) ≤ N)
    (hF : Erdos272.IsArithInterSet N F)
    (hinterval : ∀ S ∈ F, c ∉ S → ∃ a b : ℕ,
      c < a ∧ a ≤ L ∧ R ≤ b ∧ b ≤ N ∧ S = Finset.Icc a b) :
    F.card ≤ N.choose 2 + 20003 * N := by
  classical
  let H := F.filter (fun S => c ∈ S)
  let J := F.filter (fun S => c ∉ S)
  let B := J.filter (fun S => S ∈ boundaryIntervals c N)
  let I := J.filter (fun S => S ∉ boundaryIntervals c N)
  have hHF : H ⊆ F := Finset.filter_subset _ _
  have hJF : J ⊆ F := Finset.filter_subset _ _
  have hIJ : I ⊆ J := Finset.filter_subset _ _
  have hIF : I ⊆ F := hIJ.trans hJF
  have hHc : ∀ S ∈ H, c ∈ S := fun S hS => (Finset.mem_filter.mp hS).2
  have hJc : ∀ S ∈ J, c ∉ S := fun S hS => (Finset.mem_filter.mp hS).2
  have hIgood : ∀ S ∈ I, ∃ a b : ℕ,
      c + 1 < a ∧ a ≤ L ∧ R ≤ b ∧ b < N ∧ S = Finset.Icc a b := by
    intro S hS
    obtain ⟨a, b, hca, haL, hRb, hbN, hSab⟩ := hinterval S (hIF hS) (hJc S (hIJ hS))
    have hnot : S ∉ boundaryIntervals c N := (Finset.mem_filter.mp hS).2
    have ha1 : 1 ≤ a := by omega
    have hb1 : 1 ≤ b := by omega
    have haN : a ≤ N := by omega
    have hane : a ≠ c + 1 := by
      intro heq
      apply hnot
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨b, Finset.mem_Icc.mpr ⟨hb1, hbN⟩, by rw [hSab, heq]⟩
    have hbne : b ≠ N := by
      intro heq
      apply hnot
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨a, Finset.mem_Icc.mpr ⟨ha1, haN⟩, by rw [hSab, heq]⟩
    exact ⟨a, b, by omega, haL, hRb, by omega, hSab⟩
  obtain ⟨W, hWcard, hWsub, hWcorner, hWdecode⟩ := exists_exterior_interval_pairs hLR hIgood
  have hbetween : ∀ S ∈ H, ∀ u v : ℕ, u < v → ({u, v} : Finset ℕ) ∈ W →
      ∃ x ∈ S, u < x ∧ x < v := by
    intro S hS u v huv hW
    obtain ⟨T, hT, hTuv⟩ := hWdecode u v huv hW
    have hne : S ≠ T := by
      intro heq
      exact hJc T (hIJ hT) (heq ▸ hHc S hS)
    obtain ⟨x, hx⟩ := arithInter_nonempty hF (hHF hS) (hIF hT) hne
    obtain ⟨hxS, hxT⟩ := Finset.mem_inter.mp hx
    rw [hTuv] at hxT
    have hbounds := Finset.mem_Icc.mp hxT
    exact ⟨x, hxS, by omega, by omega⟩
  have hH := star_card_le_with_reserved_pairs hcL hLR hRN hN
    (arithInterSet_mono hF hHF) hHc hWcorner hbetween
  have hB : B.card ≤ 2 * N := by
    have hBsub : B ⊆ boundaryIntervals c N := fun S hS => (Finset.mem_filter.mp hS).2
    exact (Finset.card_le_card hBsub).trans (card_boundaryIntervals_le c N)
  have hpool := Finset.card_sdiff_add_card_eq_card hWsub
  simp only [Finset.card_powersetCard, Nat.card_Icc, Nat.add_sub_cancel] at hpool
  have hFpart := Finset.card_filter_add_card_filter_not (s := F) (fun S => c ∈ S)
  change H.card + J.card = F.card at hFpart
  have hJpart := Finset.card_filter_add_card_filter_not (s := J)
    (fun S => S ∈ boundaryIntervals c N)
  change B.card + I.card = J.card at hJpart
  omega

end
section
open Finset

def apSegment (u v d : ℕ) : Finset ℕ := (Finset.Icc u v).filter (fun x => d ∣ x - u)

def apTrace (c p d : ℕ) : Finset ℕ := apSegment (min c p) (max c p) d

theorem apSegment_eq_natAP {u v d : ℕ} (huv : u ≤ v) (hd : 0 < d) :
    apSegment u v d = natAP u d ((v - u) / d + 1) := by
  ext x
  simp only [apSegment, Finset.mem_filter, Finset.mem_Icc, mem_natAP]
  constructor
  · rintro ⟨⟨hux, hxv⟩, hdiv⟩
    refine ⟨(x - u) / d, ?_, ?_⟩
    · apply Nat.lt_succ_of_le
      exact Nat.div_le_div_right (by omega : x - u ≤ v - u)
    · rw [Nat.div_mul_cancel hdiv]
      omega
  · rintro ⟨i, hi, hxi⟩
    have hib : i * d ≤ v - u := (Nat.le_div_iff_mul_le hd).mp (by omega)
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    refine ⟨i, ?_⟩
    rw [← hxi, Nat.add_sub_cancel_left, Nat.mul_comm]

theorem apSegment_isAP {u v d : ℕ} (huv : u ≤ v) (hd : 0 < d) :
    ∃ l : ℕ∞, (apSegment u v d : Set ℕ).IsAPOfLength l := by
  rw [apSegment_eq_natAP huv hd]
  exact ⟨((v - u) / d + 1 : ℕ), natAP_isAP hd⟩

theorem apTrace_isAP {c p d : ℕ} (hd : 0 < d) :
    ∃ l : ℕ∞, (apTrace c p d : Set ℕ).IsAPOfLength l :=
  apSegment_isAP min_le_max hd

theorem natAP_inter_Icc_eq_segment {a d k u v : ℕ} (hd : 0 < d)
    (hu : u ∈ natAP a d k) (hv : v ∈ natAP a d k) (_huv : u ≤ v) :
    natAP a d k ∩ Finset.Icc u v = apSegment u v d := by
  obtain ⟨i, hi, hui⟩ := mem_natAP.mp hu
  obtain ⟨j, hj, hvj⟩ := mem_natAP.mp hv
  ext x
  simp only [Finset.mem_inter, apSegment, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨hxA, hux, hxv⟩
    obtain ⟨b, hb, hxb⟩ := mem_natAP.mp hxA
    refine ⟨⟨hux, hxv⟩, ?_⟩
    rw [← hxb, ← hui, Nat.add_sub_add_left, ← Nat.sub_mul]
    exact dvd_mul_left d (b - i)
  · rintro ⟨⟨hux, hxv⟩, hdx⟩
    obtain ⟨t, ht⟩ := hdx
    have hxt : x = a + (i + t) * d := by
      have hsub := Nat.sub_add_cancel hux
      nlinarith only [hui, ht, hsub]
    have hij : i + t ≤ j := by
      by_contra hle
      have hmul := Nat.mul_lt_mul_of_pos_right (by omega : j < i + t) hd
      omega
    exact ⟨mem_natAP.mpr ⟨i + t, hij.trans_lt hj, hxt.symm⟩, hux, hxv⟩

theorem ap_inter_Icc_endpoints {S : Finset ℕ} {u v : ℕ}
    (hAP : ∃ l : ℕ∞, (S : Set ℕ).IsAPOfLength l)
    (hu : u ∈ S) (hv : v ∈ S) (huv : u < v) :
    ∃ d : ℕ, 0 < d ∧ d ∣ v - u ∧ S ∩ Finset.Icc u v = apSegment u v d := by
  have hcard : 2 ≤ S.card := by
    have hsub : {u, v} ⊆ S := by simp [Finset.insert_subset_iff, hu, hv]
    simpa [huv.ne] using Finset.card_le_card hsub
  obtain ⟨l, hAP⟩ := hAP
  obtain ⟨a, d, hd, hS⟩ := nat_ap_eq_natAP hAP hcard
  have hslice := natAP_inter_Icc_eq_segment hd (hS ▸ hu) (hS ▸ hv) huv.le
  have hvseg : v ∈ apSegment u v d := hslice ▸ Finset.mem_inter.mpr
    ⟨hS ▸ hv, Finset.mem_Icc.mpr ⟨huv.le, le_rfl⟩⟩
  exact ⟨d, hd, (Finset.mem_filter.mp hvseg).2,
    (congrArg (fun T : Finset ℕ => T ∩ Finset.Icc u v) hS).trans hslice⟩

theorem ap_inter_Icc {S : Finset ℕ} {u v : ℕ}
    (hAP : ∃ l : ℕ∞, (S : Set ℕ).IsAPOfLength l) :
    ∃ l : ℕ∞, ((S ∩ Finset.Icc u v : Finset ℕ) : Set ℕ).IsAPOfLength l := by
  let T := S ∩ Finset.Icc u v
  rcases T.eq_empty_or_nonempty with hzero | hT
  · refine ⟨0, Set.IsAPOfLength.zero.mpr ?_⟩
    change (T : Set ℕ) = ∅
    simp [hzero]
  · let a := T.min' hT
    let b := T.max' hT
    have haT : a ∈ T := Finset.min'_mem T hT
    have hbT : b ∈ T := Finset.max'_mem T hT
    have hab : a ≤ b := Finset.min'_le T b hbT
    by_cases heq : a = b
    · have hTsmall : T.card ≤ 1 := Finset.card_le_one.mpr (by
        intro x hx y hy
        have hax : a ≤ x := Finset.min'_le T x hx
        have hxb : x ≤ b := Finset.le_max' T x hx
        have hay : a ≤ y := Finset.min'_le T y hy
        have hyb : y ≤ b := Finset.le_max' T y hy
        omega)
      obtain ⟨l, hl, hTl⟩ := nonempty_small_isAP hT (by omega : T.card ≤ 2)
      exact ⟨l, hTl⟩
    · obtain ⟨d, hd, hdiv, hslice⟩ := ap_inter_Icc_endpoints hAP
        (Finset.mem_inter.mp haT).1 (Finset.mem_inter.mp hbT).1 (by omega)
      have hT_eq : T = S ∩ Finset.Icc a b := by
        ext x
        constructor
        · intro hx
          exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).1,
            Finset.mem_Icc.mpr ⟨Finset.min'_le T x hx, Finset.le_max' T x hx⟩⟩
        · intro hx
          obtain ⟨hxS, hxI⟩ := Finset.mem_inter.mp hx
          have habounds := Finset.mem_Icc.mp (Finset.mem_inter.mp haT).2
          have hbbounds := Finset.mem_Icc.mp (Finset.mem_inter.mp hbT).2
          have hxbounds := Finset.mem_Icc.mp hxI
          exact Finset.mem_inter.mpr ⟨hxS, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩
      change ∃ l : ℕ∞, (T : Set ℕ).IsAPOfLength l
      rw [hT_eq, hslice]
      exact apSegment_isAP hab hd

theorem ap_trace_endpoints {S : Finset ℕ} {c p : ℕ}
    (hAP : ∃ l : ℕ∞, (S : Set ℕ).IsAPOfLength l) (hc : c ∈ S) (hp : p ∈ S) (hcp : c ≠ p) :
    ∃ d : ℕ, 0 < d ∧ d ∣ max c p - min c p ∧
      S ∩ Finset.Icc (min c p) (max c p) = apTrace c p d := by
  have hmin : min c p ∈ S := by
    rcases le_total c p with h | h
    · simpa only [min_eq_left h] using hc
    · simpa only [min_eq_right h] using hp
  have hmax : max c p ∈ S := by
    rcases le_total c p with h | h
    · simpa only [max_eq_right h] using hp
    · simpa only [max_eq_left h] using hc
  have hlt : min c p < max c p := by omega
  exact ap_inter_Icc_endpoints hAP hmin hmax hlt

theorem hasAPCover_inter_Icc {S T : Finset ℕ} {u v : ℕ}
    (hT : T ⊆ Finset.Icc u v) (hcover : HasAPCover S T) :
    HasAPCover (S ∩ Finset.Icc u v) T := by
  obtain ⟨A, hAS, hAP, hTA⟩ := hcover
  refine ⟨A ∩ Finset.Icc u v, ?_, ap_inter_Icc hAP, ?_⟩
  · intro x hx
    obtain ⟨hxA, hxI⟩ := Finset.mem_inter.mp hx
    exact Finset.mem_inter.mpr ⟨hAS hxA, hxI⟩
  · exact Finset.subset_inter hTA hT

theorem witness_pair_of_inter_Icc {S P : Finset ℕ} {c u v : ℕ}
    (hc : c ∈ Finset.Icc u v) (hW : IsWitnessPair (S ∩ Finset.Icc u v) c P) :
    IsWitnessPair S c P := by
  refine ⟨hW.1, ?_, ?_⟩
  · intro x hx
    obtain ⟨hxc, hxSI⟩ := Finset.mem_erase.mp (hW.2.1 hx)
    exact Finset.mem_erase.mpr ⟨hxc, (Finset.mem_inter.mp hxSI).1⟩
  · intro hcover
    apply hW.2.2
    apply hasAPCover_inter_Icc (Finset.insert_subset hc ?_) hcover
    intro x hx
    exact (Finset.mem_inter.mp (Finset.mem_of_mem_erase (hW.2.1 hx))).2

end
section
open Finset

def anchorDistance (c p : ℕ) : ℕ := max c p - min c p

def traceAt (S : Finset ℕ) (c p : ℕ) : Finset ℕ :=
  S ∩ Finset.Icc (min c p) (max c p)

def AllTriplesCovered (S : Finset ℕ) (c p : ℕ) : Prop :=
  ∀ x ∈ S, HasAPCover S {c, p, x}

def HasWitnessAt (S : Finset ℕ) (c p : ℕ) : Prop := ∃ x, IsWitnessPair S c {p, x}

theorem anchorDistance_pos {c p : ℕ} (hcp : c ≠ p) : 0 < anchorDistance c p := by
  dsimp [anchorDistance]
  omega

theorem allTriplesCovered_of_no_witnessAt {S : Finset ℕ} {c p : ℕ}
    (hc : c ∈ S) (hp : p ∈ S.erase c) (hno : ¬ HasWitnessAt S c p) :
    AllTriplesCovered S c p := by
  have hpne := (Finset.mem_erase.mp hp).1
  have hpS := (Finset.mem_erase.mp hp).2
  have hpairCover : HasAPCover S {c, p} := by
    obtain ⟨l, hl, hAP⟩ := nonempty_small_isAP (s := {c, p}) (by simp) (by simp [hpne.symm])
    exact ⟨{c, p}, by simp [Finset.insert_subset_iff, hc, hpS], ⟨l, hAP⟩, Finset.Subset.refl _⟩
  intro x hx
  by_cases hxc : x = c
  · subst x
    have heq : ({c, p, c} : Finset ℕ) = {c, p} := by ext z; simp [or_comm]
    rw [heq]
    exact hpairCover
  by_cases hxp : x = p
  · subst x
    simpa using hpairCover
  apply hasAPCover_of_not_witness (by simp [Ne.symm hxp])
  · intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    · exact hp
    · exact Finset.mem_erase.mpr ⟨hxc, hx⟩
  · exact fun hW => hno ⟨x, hW⟩

def IncompatibleTraceCode (S : Finset ℕ) (c p d e : ℕ) : Prop :=
  apTrace c p d ⊆ S ∧ apTrace c p e ⊆ S ∧
    ¬ HasAPCover S (apTrace c p d ∪ apTrace c p e)

theorem exists_incompatible_trace_code {S : Finset ℕ} {c p : ℕ}
    (hc : c ∈ S) (hcp : c ≠ p) (hcover : AllTriplesCovered S c p)
    (hcrooked : IsCrooked (traceAt S c p)) :
    ∃ d e : ℕ, 0 < d ∧ 0 < e ∧ d ∣ anchorDistance c p ∧ e ∣ anchorDistance c p ∧
      IncompatibleTraceCode S c p d e := by
  have hcI : c ∈ Finset.Icc (min c p) (max c p) :=
    Finset.mem_Icc.mpr ⟨min_le_left _ _, le_max_left _ _⟩
  have hcT : c ∈ traceAt S c p := Finset.mem_inter.mpr ⟨hc, hcI⟩
  obtain ⟨P, hP⟩ := exists_witness_pair hcrooked hcT
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hP.1
  have hPS : IsWitnessPair S c {x, y} := witness_pair_of_inter_Icc hcI hP
  have hxT : x ∈ traceAt S c p := Finset.mem_of_mem_erase (hP.2.1 (by simp))
  have hyT : y ∈ traceAt S c p := Finset.mem_of_mem_erase (hP.2.1 (by simp))
  obtain ⟨A, hAS, hAAP, hAx⟩ := hcover x (Finset.mem_inter.mp hxT).1
  obtain ⟨B, hBS, hBAP, hBy⟩ := hcover y (Finset.mem_inter.mp hyT).1
  obtain ⟨d, hd, hddiv, hAtrace⟩ := ap_trace_endpoints hAAP (hAx (by simp)) (hAx (by simp)) hcp
  obtain ⟨e, he, hediv, hBtrace⟩ := ap_trace_endpoints hBAP (hBy (by simp)) (hBy (by simp)) hcp
  have hTdS : apTrace c p d ⊆ S := by
    rw [← hAtrace]
    exact Finset.inter_subset_left.trans hAS
  have hTeS : apTrace c p e ⊆ S := by
    rw [← hBtrace]
    exact Finset.inter_subset_left.trans hBS
  have hcTd : c ∈ apTrace c p d := hAtrace ▸ Finset.mem_inter.mpr ⟨hAx (by simp), hcI⟩
  have hxTd : x ∈ apTrace c p d := hAtrace ▸ Finset.mem_inter.mpr
    ⟨hAx (by simp), (Finset.mem_inter.mp hxT).2⟩
  have hyTe : y ∈ apTrace c p e := hBtrace ▸ Finset.mem_inter.mpr
    ⟨hBy (by simp), (Finset.mem_inter.mp hyT).2⟩
  refine ⟨d, e, hd, he, hddiv, hediv, hTdS, hTeS, ?_⟩
  rintro ⟨C, hCS, hCAP, hUC⟩
  apply hPS.2.2
  refine ⟨C, hCS, hCAP, ?_⟩
  have hcC := hUC (Finset.mem_union_left _ hcTd)
  have hxC := hUC (Finset.mem_union_left _ hxTd)
  have hyC := hUC (Finset.mem_union_right _ hyTe)
  simp [Finset.insert_subset_iff, hcC, hxC, hyC]

theorem trace_code_private {N c p d e : ℕ} {F : Finset (Finset ℕ)} {S T : Finset ℕ}
    (hF : Erdos272.IsArithInterSet N F) (hS : S ∈ F) (hT : T ∈ F)
    (hcode : IncompatibleTraceCode S c p d e)
    (hTd : apTrace c p d ⊆ T) (hTe : apTrace c p e ⊆ T) : T = S := by
  by_contra hne
  obtain ⟨l, hl, hAP⟩ := hF.2 hS hT (fun hST => hne hST.symm)
  apply hcode.2.2
  refine ⟨S ∩ T, Finset.inter_subset_left, ⟨l, hAP⟩, ?_⟩
  exact Finset.subset_inter (Finset.union_subset hcode.1 hcode.2.1)
    (Finset.union_subset hTd hTe)

theorem crooked_trace_family_card_le {N c : ℕ} {F : Finset (Finset ℕ)}
    (hF : Erdos272.IsArithInterSet N F) (hc : ∀ S ∈ F, c ∈ S)
    (p : {S // S ∈ F} → ℕ)
    (hp : ∀ S, p S ∈ S.val ∧ c ≠ p S)
    (hcover : ∀ S, AllTriplesCovered S.val c (p S))
    (hcrooked : ∀ S, IsCrooked (traceAt S.val c (p S))) :
    F.card ≤ ∑ q ∈ Finset.Icc 1 N, ((anchorDistance c q).divisors.card)^2 := by
  classical
  let A := {S : Finset ℕ // S ∈ F}
  have hex : ∀ S : A, ∃ d e : ℕ, 0 < d ∧ 0 < e ∧
      d ∣ anchorDistance c (p S) ∧ e ∣ anchorDistance c (p S) ∧
      IncompatibleTraceCode S.val c (p S) d e := by
    intro S
    exact exists_incompatible_trace_code (hc S.val S.property) (hp S).2 (hcover S) (hcrooked S)
  choose d e hd he hddiv hediv hcode using hex
  let U : Finset (Σ _ : ℕ, ℕ × ℕ) := (Finset.Icc 1 N).sigma (fun q =>
    ((anchorDistance c q).divisors).product ((anchorDistance c q).divisors))
  let f : A → (Σ _ : ℕ, ℕ × ℕ) := fun S => ⟨p S, d S, e S⟩
  have hmaps : Set.MapsTo f ((Finset.univ : Finset A) : Set A) (U : Set (Σ _ : ℕ, ℕ × ℕ)) := by
    intro S hS
    have hpI : p S ∈ Finset.Icc 1 N := Finset.mem_powerset.mp (hF.1 S.property) (hp S).1
    have hdist : anchorDistance c (p S) ≠ 0 := (anchorDistance_pos (hp S).2).ne'
    exact Finset.mem_sigma.mpr ⟨hpI, Finset.mem_product.mpr
      ⟨Nat.mem_divisors.mpr ⟨hddiv S, hdist⟩, Nat.mem_divisors.mpr ⟨hediv S, hdist⟩⟩⟩
  have hinj : Function.Injective f := by
    intro S T hf
    have hpST : p S = p T := congrArg Sigma.fst hf
    have hdST : d S = d T := congrArg (fun q : (Σ _ : ℕ, ℕ × ℕ) => q.2.1) hf
    have heST : e S = e T := congrArg (fun q : (Σ _ : ℕ, ℕ × ℕ) => q.2.2) hf
    apply Subtype.ext
    exact (trace_code_private hF S.property T.property (hcode S)
      (by simpa only [hpST, hdST] using (hcode T).1)
      (by simpa only [hpST, heST] using (hcode T).2.1)).symm
  have hcard := Finset.card_le_card_of_injOn f hmaps hinj.injOn
  simpa [A, U, Finset.card_sigma, Finset.card_product, pow_two] using hcard

end
section
open Finset

theorem natAP_dvd_anchorDistance {a d k c x : ℕ}
    (hc : c ∈ natAP a d k) (hx : x ∈ natAP a d k) : d ∣ anchorDistance c x := by
  obtain ⟨i, hi, hci⟩ := mem_natAP.mp hc
  obtain ⟨j, hj, hxj⟩ := mem_natAP.mp hx
  rcases le_total c x with hcx | hxc
  · rw [anchorDistance, min_eq_left hcx, max_eq_right hcx, ← hxj, ← hci,
      Nat.add_sub_add_left, ← Nat.sub_mul]
    exact dvd_mul_left d (j - i)
  · rw [anchorDistance, min_eq_right hxc, max_eq_left hxc, ← hci, ← hxj,
      Nat.add_sub_add_left, ← Nat.sub_mul]
    exact dvd_mul_left d (i - j)

theorem apTrace_step_dvd_of_subset {c p d e : ℕ} (hcp : c ≠ p)
    (hediv : e ∣ anchorDistance c p) (hsub : apTrace c p e ⊆ apTrace c p d) : d ∣ e := by
  have heD : e ≤ anchorDistance c p := Nat.le_of_dvd (anchorDistance_pos hcp) hediv
  have hpoint : min c p + e ∈ apTrace c p e := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨by omega, ?_⟩, ?_⟩
    · dsimp [anchorDistance] at heD
      omega
    · simp
  have hh := (Finset.mem_filter.mp (hsub hpoint)).2
  simpa only [Nat.add_sub_cancel_left] using hh

theorem natAP_consecutive {a d k i : ℕ} (hd : 0 < d) (hi : i + 1 < k) :
    ConsecutiveIn (natAP a d k) (a + i * d) (a + (i + 1) * d) := by
  refine ⟨mem_natAP.mpr ⟨i, by omega, rfl⟩, mem_natAP.mpr ⟨i + 1, hi, rfl⟩,
    by nlinarith only [hd], ?_⟩
  intro x hx hbetween
  obtain ⟨j, hj, hxj⟩ := mem_natAP.mp hx
  have hij : i < j := by
    by_contra hh
    have hmul := Nat.mul_le_mul_right d (by omega : j ≤ i)
    omega
  have hji : j < i + 1 := by
    by_contra hh
    have hmul := Nat.mul_le_mul_right d (by omega : i + 1 ≤ j)
    omega
  omega

theorem consecutive_of_inter_Icc {S : Finset ℕ} {u v a b : ℕ}
    (hcon : ConsecutiveIn (S ∩ Finset.Icc u v) a b) : ConsecutiveIn S a b := by
  have ha := Finset.mem_inter.mp hcon.1
  have hb := Finset.mem_inter.mp hcon.2.1
  refine ⟨ha.1, hb.1, hcon.2.2.1, ?_⟩
  intro x hx hbetween
  apply hcon.2.2.2 x (Finset.mem_inter.mpr ⟨hx, ?_⟩) hbetween
  have haI := Finset.mem_Icc.mp ha.2
  have hbI := Finset.mem_Icc.mp hb.2
  exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩

theorem apTrace_neighbor {S : Finset ℕ} {c p d : ℕ} (hcp : c ≠ p)
    (hd : 0 < d) (hddiv : d ∣ anchorDistance c p)
    (htrace : traceAt S c p = apTrace c p d) :
    ∃ a : ℕ, (ConsecutiveIn S c a ∨ ConsecutiveIn S a c) ∧ anchorDistance c a = d := by
  let u := min c p
  let v := max c p
  let q := (v - u) / d
  have hDpos : 0 < v - u := anchorDistance_pos hcp
  have hqd : q * d = v - u := Nat.div_mul_cancel hddiv
  have hq : 1 ≤ q := by
    by_contra hlt
    have hq0 : q = 0 := Nat.eq_zero_of_not_pos hlt
    rw [hq0, zero_mul] at hqd
    omega
  have hvq : v = u + q * d := by omega
  have hrep : traceAt S c p = natAP u d (q + 1) := by
    rw [htrace]
    exact apSegment_eq_natAP min_le_max hd
  rcases le_total c p with hcp' | hpc
  · have hu : u = c := min_eq_left hcp'
    have hcon : ConsecutiveIn S c (c + d) := by
      apply consecutive_of_inter_Icc (u := min c p) (v := max c p)
      change ConsecutiveIn (traceAt S c p) c (c + d)
      rw [hrep, hu]
      simpa only [zero_mul, zero_add, add_zero, one_mul] using
        (natAP_consecutive (a := c) (d := d) (k := q + 1) (i := 0) hd (by omega))
    refine ⟨c + d, Or.inl hcon, ?_⟩
    dsimp [anchorDistance]
    omega
  · have hv : v = c := max_eq_left hpc
    let a := u + (q - 1) * d
    have had : a + d = c := by
      have hh : q - 1 + 1 = q := by omega
      dsimp [a]
      nlinarith only [hvq, hv, hh]
    have hcon : ConsecutiveIn S a c := by
      apply consecutive_of_inter_Icc (u := min c p) (v := max c p)
      change ConsecutiveIn (traceAt S c p) a c
      rw [hrep]
      have hh := natAP_consecutive (a := u) (d := d) (k := q + 1) (i := q - 1) hd (by omega)
      have heq : u + (q - 1 + 1) * d = c := by rw [show q - 1 + 1 = q by omega, ← hvq, hv]
      simpa only [heq] using hh
    refine ⟨a, Or.inr hcon, ?_⟩
    dsimp [anchorDistance]
    omega

theorem allTriplesCovered_grid_of_APtrace {S : Finset ℕ} {c p : ℕ}
    (hc : c ∈ S) (hp : p ∈ S) (hcp : c ≠ p) (hcover : AllTriplesCovered S c p)
    (hTAP : ∃ l : ℕ∞, (traceAt S c p : Set ℕ).IsAPOfLength l) :
    ∃ d : ℕ, 0 < d ∧ d ∣ anchorDistance c p ∧
      traceAt S c p = apTrace c p d ∧ ∀ x ∈ S, d ∣ anchorDistance c x := by
  let I := Finset.Icc (min c p) (max c p)
  have hcI : c ∈ I := Finset.mem_Icc.mpr ⟨min_le_left _ _, le_max_left _ _⟩
  have hpI : p ∈ I := Finset.mem_Icc.mpr ⟨min_le_right _ _, le_max_right _ _⟩
  have hcT : c ∈ traceAt S c p := Finset.mem_inter.mpr ⟨hc, hcI⟩
  have hpT : p ∈ traceAt S c p := Finset.mem_inter.mpr ⟨hp, hpI⟩
  obtain ⟨d, hd, hddiv, htrace⟩ := ap_trace_endpoints hTAP hcT hpT hcp
  have hTI : traceAt S c p ∩ I = traceAt S c p := Finset.inter_eq_left.mpr Finset.inter_subset_right
  have hT_eq : traceAt S c p = apTrace c p d := hTI.symm.trans htrace
  refine ⟨d, hd, hddiv, hT_eq, ?_⟩
  intro x hx
  obtain ⟨A, hAS, ⟨l, hAP⟩, hCA⟩ := hcover x hx
  have hcA : c ∈ A := hCA (by simp)
  have hpA : p ∈ A := hCA (by simp)
  have hxA : x ∈ A := hCA (by simp)
  have hAcard : 2 ≤ A.card := by
    have hsub : {c, p} ⊆ A := by simp [Finset.insert_subset_iff, hcA, hpA]
    simpa [hcp] using Finset.card_le_card hsub
  obtain ⟨a, e, he, hArep⟩ := nat_ap_eq_natAP hAP hAcard
  have hediv : e ∣ anchorDistance c p := natAP_dvd_anchorDistance (hArep ▸ hcA) (hArep ▸ hpA)
  have hminA : min c p ∈ A := by
    rcases le_total c p with h | h
    · simpa only [min_eq_left h] using hcA
    · simpa only [min_eq_right h] using hpA
  have hmaxA : max c p ∈ A := by
    rcases le_total c p with h | h
    · simpa only [max_eq_right h] using hpA
    · simpa only [max_eq_left h] using hcA
  have hAslice : A ∩ I = apTrace c p e :=
    (congrArg (fun T : Finset ℕ => T ∩ I) hArep).trans
      (natAP_inter_Icc_eq_segment he (hArep ▸ hminA) (hArep ▸ hmaxA) min_le_max)
  have hsubTrace : apTrace c p e ⊆ apTrace c p d := by
    rw [← hAslice, ← hT_eq]
    intro y hy
    obtain ⟨hyA, hyI⟩ := Finset.mem_inter.mp hy
    exact Finset.mem_inter.mpr ⟨hAS hyA, hyI⟩
  exact (apTrace_step_dvd_of_subset hcp hediv hsubTrace).trans
    (natAP_dvd_anchorDistance (hArep ▸ hcA) (hArep ▸ hxA))

theorem APtrace_witness_divisor_code {S : Finset ℕ} {c p : ℕ}
    (hcrooked : IsCrooked S) (hc : c ∈ S) (hp : p ∈ S) (hcp : c ≠ p)
    (hcover : AllTriplesCovered S c p)
    (hTAP : ∃ l : ℕ∞, (traceAt S c p : Set ℕ).IsAPOfLength l) :
    ∃ a z : ℕ, IsWitnessPair S c {a, z} ∧ anchorDistance c a ∣ anchorDistance c z := by
  obtain ⟨d, hd, hddiv, htrace, hgrid⟩ := allTriplesCovered_grid_of_APtrace hc hp hcp hcover hTAP
  obtain ⟨a, hcon, had⟩ := apTrace_neighbor hcp hd hddiv htrace
  obtain ⟨z, hW⟩ : ∃ z, IsWitnessPair S c {a, z} := by
    rcases hcon with hcon | hcon
    · exact witness_pair_of_right_neighbor hcrooked hcon
    · exact witness_pair_of_left_neighbor hcrooked hcon
  have hzS : z ∈ S := Finset.mem_of_mem_erase (hW.2.1 (by simp))
  exact ⟨a, z, hW, by simpa only [had] using hgrid z hzS⟩

end
section
open Finset

theorem anchorDistance_inj_of_side {c a b : ℕ}
    (hdist : anchorDistance c a = anchorDistance c b)
    (hside : decide (c ≤ a) = decide (c ≤ b)) : a = b := by
  dsimp [anchorDistance] at hdist
  by_cases hca : c ≤ a
  · have hcb : c ≤ b := by by_contra hh; simp [hca, hh] at hside
    rw [max_eq_right hca, min_eq_left hca, max_eq_right hcb, min_eq_left hcb] at hdist
    omega
  · have hcb : ¬ c ≤ b := by intro hh; simp [hca, hh] at hside
    have hac : a ≤ c := by omega
    have hbc : b ≤ c := by omega
    rw [max_eq_left hac, min_eq_right hac, max_eq_left hbc, min_eq_right hbc] at hdist
    omega

theorem APtrace_family_card_le {N c : ℕ} {F : Finset (Finset ℕ)}
    (hF : Erdos272.IsArithInterSet N F) (hc : ∀ S ∈ F, c ∈ S)
    (hcrooked : ∀ S ∈ F, IsCrooked S)
    (p : {S // S ∈ F} → ℕ)
    (hp : ∀ S, p S ∈ S.val ∧ c ≠ p S)
    (hcover : ∀ S, AllTriplesCovered S.val c (p S))
    (hAP : ∀ S, ∃ l : ℕ∞, (traceAt S.val c (p S) : Set ℕ).IsAPOfLength l) :
    F.card ≤ 2 * ∑ q ∈ Finset.Icc 1 N, (anchorDistance c q).divisors.card := by
  classical
  let A := {S : Finset ℕ // S ∈ F}
  have hex : ∀ S : A, ∃ a z : ℕ, IsWitnessPair S.val c {a, z} ∧
      anchorDistance c a ∣ anchorDistance c z := by
    intro S
    exact APtrace_witness_divisor_code (hcrooked S.val S.property) (hc S.val S.property)
      (hp S).1 (hp S).2 (hcover S) (hAP S)
  choose a z hW hdiv using hex
  let U : Finset (Σ _ : ℕ, Bool × ℕ) := (Finset.Icc 1 N).sigma (fun q =>
    (Finset.univ : Finset Bool).product (anchorDistance c q).divisors)
  let f : A → (Σ _ : ℕ, Bool × ℕ) := fun S => ⟨z S, decide (c ≤ a S), anchorDistance c (a S)⟩
  have hmaps : Set.MapsTo f ((Finset.univ : Finset A) : Set A)
      (U : Set (Σ _ : ℕ, Bool × ℕ)) := by
    intro S hS
    have hz : z S ∈ S.val.erase c := (hW S).2.1 (by simp)
    have hzI : z S ∈ Finset.Icc 1 N :=
      Finset.mem_powerset.mp (hF.1 S.property) (Finset.mem_of_mem_erase hz)
    have hdist : anchorDistance c (z S) ≠ 0 :=
      (anchorDistance_pos (Ne.symm (Finset.mem_erase.mp hz).1)).ne'
    exact Finset.mem_sigma.mpr ⟨hzI, Finset.mem_product.mpr
      ⟨Finset.mem_univ _, Nat.mem_divisors.mpr ⟨hdiv S, hdist⟩⟩⟩
  have hinj : Function.Injective f := by
    intro S T hf
    have hz : z S = z T := congrArg Sigma.fst hf
    have hside : decide (c ≤ a S) = decide (c ≤ a T) :=
      congrArg (fun q : (Σ _ : ℕ, Bool × ℕ) => q.2.1) hf
    have hdist : anchorDistance c (a S) = anchorDistance c (a T) :=
      congrArg (fun q : (Σ _ : ℕ, Bool × ℕ) => q.2.2) hf
    have ha : a S = a T := anchorDistance_inj_of_side hdist hside
    apply Subtype.ext
    exact (witness_pair_private hF S.property T.property (hc S.val S.property)
      (hc T.val T.property) (hW S) (by
        rw [ha, hz]
        exact (hW T).2.1.trans (Finset.erase_subset _ _))).symm
  have hcard := Finset.card_le_card_of_injOn f hmaps hinj.injOn
  simpa [A, U, Finset.card_sigma, Finset.card_product, Finset.mul_sum] using hcard

end
section
open Finset

def witnessExceptionBound (N c : ℕ) : ℕ :=
  (∑ q ∈ Finset.Icc 1 N, ((anchorDistance c q).divisors.card)^2) +
    2 * ∑ q ∈ Finset.Icc 1 N, (anchorDistance c q).divisors.card

theorem noWitnessAt_family_card_le {N c : ℕ} {F : Finset (Finset ℕ)}
    (hF : Erdos272.IsArithInterSet N F) (hc : ∀ S ∈ F, c ∈ S)
    (hcrooked : ∀ S ∈ F, IsCrooked S) (p : Finset ℕ → ℕ)
    (hp : ∀ S ∈ F, p S ∈ S.erase c)
    (hno : ∀ S ∈ F, ¬ HasWitnessAt S c (p S)) :
    F.card ≤ witnessExceptionBound N c := by
  classical
  let C := F.filter (fun S => IsCrooked (traceAt S c (p S)))
  let A := F.filter (fun S => ¬ IsCrooked (traceAt S c (p S)))
  have hCF : C ⊆ F := Finset.filter_subset _ _
  have hAF : A ⊆ F := Finset.filter_subset _ _
  have hcover : ∀ S ∈ F, AllTriplesCovered S c (p S) :=
    fun S hS => allTriplesCovered_of_no_witnessAt (hc S hS) (hp S hS) (hno S hS)
  have hC := crooked_trace_family_card_le (arithInterSet_mono hF hCF)
    (fun S hS => hc S (hCF hS)) (fun S => p S.val)
    (fun S => ⟨Finset.mem_of_mem_erase (hp S.val (hCF S.property)),
      Ne.symm (Finset.mem_erase.mp (hp S.val (hCF S.property))).1⟩)
    (fun S => hcover S.val (hCF S.property))
    (fun S => (Finset.mem_filter.mp S.property).2)
  have hA := APtrace_family_card_le (arithInterSet_mono hF hAF)
    (fun S hS => hc S (hAF hS)) (fun S hS => hcrooked S (hAF hS)) (fun S => p S.val)
    (fun S => ⟨Finset.mem_of_mem_erase (hp S.val (hAF S.property)),
      Ne.symm (Finset.mem_erase.mp (hp S.val (hAF S.property))).1⟩)
    (fun S => hcover S.val (hAF S.property)) (fun S => by
      simpa only [IsCrooked, not_not] using (Finset.mem_filter.mp S.property).2)
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := F) (fun S => IsCrooked (traceAt S c (p S)))
  change C.card + A.card = F.card at hpartition
  dsimp [witnessExceptionBound]
  omega

theorem restricted_witness_bad_family_card_le {N c : ℕ} {F : Finset (Finset ℕ)}
    {P : Finset ℕ}
    (hF : Erdos272.IsArithInterSet N F) (hc : ∀ S ∈ F, c ∈ S)
    (hcrooked : ∀ S ∈ F, IsCrooked S)
    (hmet : ∀ S ∈ F, (S.erase c ∩ P).Nonempty)
    (hbad : ∀ S ∈ F, ∀ Q, IsWitnessPair S c Q → Disjoint Q P) :
    F.card ≤ witnessExceptionBound N c := by
  classical
  have hex : ∀ S : {S // S ∈ F}, ∃ p, p ∈ S.val.erase c ∩ P :=
    fun S => hmet S.val S.property
  choose p₀ hp₀ using hex
  let p : Finset ℕ → ℕ := fun S => if h : S ∈ F then p₀ ⟨S, h⟩ else 0
  have hp : ∀ S ∈ F, p S ∈ S.erase c ∩ P := by
    intro S hS
    simpa only [p, dif_pos hS] using hp₀ ⟨S, hS⟩
  apply noWitnessAt_family_card_le hF hc hcrooked p
    (fun S hS => (Finset.mem_inter.mp (hp S hS)).1)
  intro S hS hW
  obtain ⟨x, hx⟩ := hW
  exact Finset.disjoint_left.mp (hbad S hS {p S, x} hx) (by simp)
    (Finset.mem_inter.mp (hp S hS)).2

def meetingPairPool (N c : ℕ) (P : Finset ℕ) : Finset (Finset ℕ) :=
  (((Finset.Icc 1 N).erase c).powersetCard 2).filter (fun Q => ¬ Disjoint Q P)

theorem witness_meeting_family_card_le {N c : ℕ} {F : Finset (Finset ℕ)} {P : Finset ℕ}
    (hF : Erdos272.IsArithInterSet N F) (hc : ∀ S ∈ F, c ∈ S)
    (hgood : ∀ S ∈ F, ∃ Q, IsWitnessPair S c Q ∧ ¬ Disjoint Q P) :
    F.card ≤ (meetingPairPool N c P).card := by
  classical
  let A := {S : Finset ℕ // S ∈ F}
  have hex : ∀ S : A, ∃ Q, IsWitnessPair S.val c Q ∧ ¬ Disjoint Q P :=
    fun S => hgood S.val S.property
  choose Q hW hQP using hex
  have hmaps : Set.MapsTo Q ((Finset.univ : Finset A) : Set A)
      (meetingPairPool N c P : Set (Finset ℕ)) := by
    intro S hS
    refine Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨?_, (hW S).1⟩, hQP S⟩
    intro x hx
    obtain ⟨hxc, hxS⟩ := Finset.mem_erase.mp ((hW S).2.1 hx)
    exact Finset.mem_erase.mpr ⟨hxc, Finset.mem_powerset.mp (hF.1 S.property) hxS⟩
  have hinj : Function.Injective Q := by
    intro S T hQ
    apply Subtype.ext
    exact (witness_pair_private hF S.property T.property (hc S.val S.property)
      (hc T.val T.property) (hW S) (by
        rw [hQ]
        exact (hW T).2.1.trans (Finset.erase_subset _ _))).symm
  simpa only [Finset.card_univ, A, Fintype.card_coe] using
    Finset.card_le_card_of_injOn Q hmaps hinj.injOn

theorem crooked_meeting_set_card_le {N c : ℕ} {F : Finset (Finset ℕ)} {P : Finset ℕ}
    (hF : Erdos272.IsArithInterSet N F) (hc : ∀ S ∈ F, c ∈ S)
    (hcrooked : ∀ S ∈ F, IsCrooked S)
    (hmet : ∀ S ∈ F, (S.erase c ∩ P).Nonempty) :
    F.card ≤ (meetingPairPool N c P).card + witnessExceptionBound N c := by
  classical
  let G := F.filter (fun S => ∃ Q, IsWitnessPair S c Q ∧ ¬ Disjoint Q P)
  let B := F.filter (fun S => ¬ ∃ Q, IsWitnessPair S c Q ∧ ¬ Disjoint Q P)
  have hGF : G ⊆ F := Finset.filter_subset _ _
  have hBF : B ⊆ F := Finset.filter_subset _ _
  have hG := witness_meeting_family_card_le (arithInterSet_mono hF hGF)
    (fun S hS => hc S (hGF hS)) (fun S hS => (Finset.mem_filter.mp hS).2)
  have hB := restricted_witness_bad_family_card_le (arithInterSet_mono hF hBF)
    (fun S hS => hc S (hBF hS)) (fun S hS => hcrooked S (hBF hS))
    (fun S hS => hmet S (hBF hS)) (fun S hS Q hQ => by
      by_contra hdis
      exact (Finset.mem_filter.mp hS).2 ⟨Q, hQ, hdis⟩)
  have hpartition := Finset.card_filter_add_card_filter_not (s := F)
    (fun S => ∃ Q, IsWitnessPair S c Q ∧ ¬ Disjoint Q P)
  change G.card + B.card = F.card at hpartition
  omega

end
section
open Finset

noncomputable def reciprocalSum (N : ℕ) : ℝ := ∑ a ∈ Finset.Icc 1 N, (a : ℝ)⁻¹

def factorQuadPool (N : ℕ) : Finset (Σ _ : ℕ, Σ _ : ℕ, Σ _ : ℕ, ℕ) :=
  (Finset.Icc 1 N).sigma (fun g => (Finset.Icc 1 N).sigma (fun a =>
    (Finset.Icc 1 N).sigma (fun b => Finset.Icc 1 (N / (g * a * b)))))

theorem exists_divisor_pair_factors {n d e : ℕ} (hn : 0 < n)
    (hd : d ∈ n.divisors) (he : e ∈ n.divisors) :
    ∃ g a b t : ℕ, 0 < g ∧ 0 < a ∧ 0 < b ∧ 0 < t ∧
      d = g * a ∧ e = g * b ∧ n = g * a * b * t := by
  have hdpos := Nat.pos_of_mem_divisors hd
  have hepos := Nat.pos_of_mem_divisors he
  let g := Nat.gcd d e
  have hg : 0 < g := Nat.gcd_pos_of_pos_left e hdpos
  obtain ⟨a, b, hab, hda, heb⟩ := Nat.exists_coprime d e
  have hD : d = g * a := by simpa only [Nat.mul_comm, g] using hda
  have hE : e = g * b := by simpa only [Nat.mul_comm, g] using heb
  have ha : 0 < a := Nat.pos_of_mul_pos_left (hD ▸ hdpos)
  have hb : 0 < b := Nat.pos_of_mul_pos_left (hE ▸ hepos)
  have hlcm : Nat.lcm d e = g * a * b := by
    rw [hD, hE, Nat.lcm_mul_left, hab.lcm_eq_mul, Nat.mul_assoc]
  have hdiv : g * a * b ∣ n := hlcm ▸ Nat.lcm_dvd (Nat.mem_divisors.mp hd).1
    (Nat.mem_divisors.mp he).1
  obtain ⟨t, ht⟩ := hdiv
  have htpos : 0 < t := by
    by_contra hh
    have ht0 : t = 0 := Nat.eq_zero_of_not_pos hh
    simp [ht0] at ht
    omega
  exact ⟨g, a, b, t, hg, ha, hb, htpos, hD, hE, ht⟩

theorem divisor_second_moment_le_factorQuadPool (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, n.divisors.card ^ 2) ≤ (factorQuadPool N).card := by
  classical
  let U : Finset (Σ _ : ℕ, ℕ × ℕ) := (Finset.Icc 1 N).sigma
    (fun n => n.divisors.product n.divisors)
  let A := {u // u ∈ U}
  have hex : ∀ u : A, ∃ g a b t : ℕ, 0 < g ∧ 0 < a ∧ 0 < b ∧ 0 < t ∧
      u.val.2.1 = g * a ∧ u.val.2.2 = g * b ∧ u.val.1 = g * a * b * t := by
    intro u
    obtain ⟨hn, hde⟩ := Finset.mem_sigma.mp u.property
    obtain ⟨hd, he⟩ := Finset.mem_product.mp hde
    exact exists_divisor_pair_factors (Finset.mem_Icc.mp hn).1 hd he
  choose g a b t hg ha hb ht hd he hn using hex
  let f : A → (Σ _ : ℕ, Σ _ : ℕ, Σ _ : ℕ, ℕ) := fun u => ⟨g u, a u, b u, t u⟩
  have hmaps : Set.MapsTo f ((Finset.univ : Finset A) : Set A)
      (factorQuadPool N : Set (Σ _ : ℕ, Σ _ : ℕ, Σ _ : ℕ, ℕ)) := by
    intro u hu
    have hnN : u.val.1 ≤ N := (Finset.mem_Icc.mp (Finset.mem_sigma.mp u.property).1).2
    have hprod : g u * a u * b u * t u ≤ N := by rwa [← hn u]
    have hga : g u * a u ≤ g u * a u * b u := Nat.le_mul_of_pos_right _ (hb u)
    have hgab : g u * a u * b u ≤ g u * a u * b u * t u := Nat.le_mul_of_pos_right _ (ht u)
    have hgN : g u ≤ N := (Nat.le_mul_of_pos_right _ (ha u)).trans (hga.trans (hgab.trans hprod))
    have haN : a u ≤ N := (Nat.le_mul_of_pos_left _ (hg u)).trans (hga.trans (hgab.trans hprod))
    have hbN : b u ≤ N := (Nat.le_mul_of_pos_left _ (Nat.mul_pos (hg u) (ha u))).trans
      (hgab.trans hprod)
    have hden : 0 < g u * a u * b u := Nat.mul_pos (Nat.mul_pos (hg u) (ha u)) (hb u)
    refine Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr ⟨hg u, hgN⟩, ?_⟩
    refine Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr ⟨ha u, haN⟩, ?_⟩
    refine Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr ⟨hb u, hbN⟩, ?_⟩
    exact Finset.mem_Icc.mpr ⟨ht u, (Nat.le_div_iff_mul_le hden).mpr
      (by simpa only [f, Nat.mul_comm (t u)] using hprod)⟩
  let decode : (Σ _ : ℕ, Σ _ : ℕ, Σ _ : ℕ, ℕ) → (Σ _ : ℕ, ℕ × ℕ) :=
    fun q => ⟨q.1 * q.2.1 * q.2.2.1 * q.2.2.2, q.1 * q.2.1, q.1 * q.2.2.1⟩
  have hrec : ∀ u : A, decode (f u) = u.val := by
    intro u
    dsimp only [decode, f]
    rw [← hn u, ← hd u, ← he u]
  have hinj : Function.Injective f := by
    intro u v huv
    apply Subtype.ext
    rw [← hrec u, ← hrec v, huv]
  simpa [A, U, Finset.card_sigma, Finset.card_product, pow_two] using
    Finset.card_le_card_of_injOn f hmaps hinj.injOn

theorem factorQuadPool_card_le (N : ℕ) :
    ((factorQuadPool N).card : ℝ) ≤ (N : ℝ) * reciprocalSum N ^ 3 := by
  calc
    ((factorQuadPool N).card : ℝ) =
        ∑ g ∈ Finset.Icc 1 N, ∑ a ∈ Finset.Icc 1 N,
          ∑ b ∈ Finset.Icc 1 N, ((N / (g * a * b) : ℕ) : ℝ) := by
      simp [factorQuadPool, Finset.card_sigma, Nat.cast_sum]
    _ ≤ ∑ g ∈ Finset.Icc 1 N, ∑ a ∈ Finset.Icc 1 N,
        ∑ b ∈ Finset.Icc 1 N, (N : ℝ) * (g : ℝ)⁻¹ * (a : ℝ)⁻¹ * (b : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro g hg
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      simpa [Nat.cast_mul, div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_left_comm, mul_comm]
        using (Nat.cast_div_le (α := ℝ) (m := N) (n := g * a * b))
    _ = (N : ℝ) * reciprocalSum N ^ 3 := by
      simp only [← Finset.mul_sum, ← Finset.sum_mul, reciprocalSum]
      ring

theorem divisor_second_moment_le_reciprocalSum (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ)^2) ≤ (N : ℝ) * reciprocalSum N ^ 3 := by
  have h : ((∑ n ∈ Finset.Icc 1 N, n.divisors.card ^ 2 : ℕ) : ℝ) ≤
      ((factorQuadPool N).card : ℝ) := by exact_mod_cast divisor_second_moment_le_factorQuadPool N
  simpa only [Nat.cast_sum, Nat.cast_pow] using h.trans (factorQuadPool_card_le N)

end
section
open Finset

theorem reciprocalSum_eq_harmonic (N : ℕ) : reciprocalSum N = (harmonic N : ℝ) := by
  simp only [reciprocalSum, harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]

theorem reciprocalSum_nonneg (N : ℕ) : 0 ≤ reciprocalSum N :=
  Finset.sum_nonneg (fun a _ha => inv_nonneg.mpr (Nat.cast_nonneg a))

theorem reciprocalSum_le_log (N : ℕ) : reciprocalSum N ≤ 1 + Real.log N := by
  rw [reciprocalSum_eq_harmonic]
  exact harmonic_le_one_add_log N

theorem reciprocalSum_le_natLog (N : ℕ) :
    reciprocalSum N ≤ 2 * ((Nat.log 2 N : ℝ) + 1) := by
  by_cases hN : N = 0
  · simp [hN, reciprocalSum]
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
  have hpow : (N : ℝ) < (2 : ℝ) ^ (Nat.log 2 N + 1) := by
    exact_mod_cast Nat.lt_pow_succ_log_self (b := 2) (by decide) N
  have hlog := Real.log_le_log hNpos hpow.le
  rw [Real.log_pow] at hlog
  have htwo : Real.log 2 ≤ (1 : ℝ) := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh ⊢
    exact hh
  have hmul := mul_le_mul_of_nonneg_left htwo (Nat.cast_nonneg (Nat.log 2 N + 1) :
    (0 : ℝ) ≤ (Nat.log 2 N + 1 : ℕ))
  have hH := reciprocalSum_le_log N
  push_cast at hlog hmul
  nlinarith only [hH, hlog, hmul, Nat.cast_nonneg (α := ℝ) (Nat.log 2 N)]

theorem anchorDistance_le_of_mem {N c q : ℕ} (hc : c ∈ Finset.Icc 1 N)
    (hq : q ∈ Finset.Icc 1 N) : anchorDistance c q ≤ N := by
  have hcc := Finset.mem_Icc.mp hc
  have hqq := Finset.mem_Icc.mp hq
  dsimp [anchorDistance]
  omega

theorem sum_anchorDistance_le_twice {N c : ℕ} (hc : c ∈ Finset.Icc 1 N)
    (f : ℕ → ℕ) (hzero : f 0 = 0) :
    (∑ q ∈ Finset.Icc 1 N, f (anchorDistance c q)) ≤
      2 * ∑ m ∈ Finset.Icc 1 N, f m := by
  classical
  let U := (Finset.Icc 1 N).erase c
  let V := (Finset.Icc 1 N).product (Finset.univ : Finset Bool)
  let g : ℕ → ℕ × Bool := fun q => (anchorDistance c q, decide (c ≤ q))
  have hmaps : U.image g ⊆ V := by
    intro z hz
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hqc, hqI⟩ := Finset.mem_erase.mp hq
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr
      ⟨anchorDistance_pos (Ne.symm hqc), anchorDistance_le_of_mem hc hqI⟩, Finset.mem_univ _⟩
  have hinj : Set.InjOn g (U : Set ℕ) := by
    intro q hq r hr hqr
    exact anchorDistance_inj_of_side (congrArg Prod.fst hqr) (congrArg Prod.snd hqr)
  have hsum : (∑ q ∈ U, f (anchorDistance c q)) ≤ ∑ z ∈ V, f z.1 := by
    calc
      _ = ∑ z ∈ U.image g, f z.1 := by rw [Finset.sum_image hinj]
      _ ≤ _ := Finset.sum_le_sum_of_subset hmaps
  have hsame : (∑ q ∈ Finset.Icc 1 N, f (anchorDistance c q)) =
      ∑ q ∈ U, f (anchorDistance c q) := by
    have hh := Finset.sum_erase_add (Finset.Icc 1 N) (fun q => f (anchorDistance c q)) hc
    simpa only [anchorDistance, max_self, min_self, Nat.sub_self, hzero, add_zero] using hh.symm
  rw [hsame]
  simpa [V, Finset.sum_product, Finset.sum_mul, Finset.mul_sum, mul_comm] using hsum

theorem witnessExceptionBound_le_second_moment {N c : ℕ}
    (hc : c ∈ Finset.Icc 1 N) :
    witnessExceptionBound N c ≤ 6 * ∑ n ∈ Finset.Icc 1 N, n.divisors.card ^ 2 := by
  have hfirst : (∑ q ∈ Finset.Icc 1 N, (anchorDistance c q).divisors.card) ≤
      ∑ q ∈ Finset.Icc 1 N, (anchorDistance c q).divisors.card ^ 2 := by
    apply Finset.sum_le_sum
    intro q hq
    have hh := (anchorDistance c q).divisors.card
    nlinarith
  have hsecond := sum_anchorDistance_le_twice hc (fun n => n.divisors.card ^ 2) (by simp)
  dsimp [witnessExceptionBound]
  omega

theorem witnessExceptionBound_le_reciprocalSum {N c : ℕ}
    (hc : c ∈ Finset.Icc 1 N) :
    (witnessExceptionBound N c : ℝ) ≤ 6 * (N : ℝ) * reciprocalSum N ^ 3 := by
  have hnat : (witnessExceptionBound N c : ℝ) ≤
      6 * ∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ)^2 := by
    exact_mod_cast witnessExceptionBound_le_second_moment hc
  have hmoment := divisor_second_moment_le_reciprocalSum N
  nlinarith only [hnat, hmoment]

theorem witnessExceptionBound_le_natLog {N c : ℕ} (hc : c ∈ Finset.Icc 1 N) :
    witnessExceptionBound N c ≤ 48 * N * (Nat.log 2 N + 1)^3 := by
  have hbase := reciprocalSum_le_natLog N
  have hpow := pow_le_pow_left₀ (reciprocalSum_nonneg N) hbase 3
  have hmul := mul_le_mul_of_nonneg_left hpow (by positivity : (0 : ℝ) ≤ 6 * (N : ℝ))
  have hbound := (witnessExceptionBound_le_reciprocalSum hc).trans hmul
  have heq : 6 * (N : ℝ) * (2 * ((Nat.log 2 N : ℝ) + 1))^3 =
      ((48 * N * (Nat.log 2 N + 1)^3 : ℕ) : ℝ) := by push_cast; ring
  rw [heq] at hbound
  exact_mod_cast hbound

end
section
open Finset

theorem card_meeting_pairs_add {α : Type*} [DecidableEq α] (U P : Finset α) :
    ((U.powersetCard 2).filter (fun Q => ¬ Disjoint Q P)).card +
      (U \ P).card.choose 2 = U.card.choose 2 := by
  classical
  have heq : (U.powersetCard 2).filter (fun Q => Disjoint Q P) = (U \ P).powersetCard 2 := by
    ext Q
    simp only [Finset.mem_filter, Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨hQU, hcard⟩, hdis⟩
      refine ⟨?_, hcard⟩
      intro x hx
      exact Finset.mem_sdiff.mpr ⟨hQU hx, fun hxP => Finset.disjoint_left.mp hdis hx hxP⟩
    · rintro ⟨hQ, hcard⟩
      refine ⟨⟨fun x hx => (Finset.mem_sdiff.mp (hQ hx)).1, hcard⟩, ?_⟩
      exact Finset.disjoint_left.mpr (fun x hx hxP => (Finset.mem_sdiff.mp (hQ hx)).2 hxP)
  have hh := Finset.card_filter_add_card_filter_not (s := U.powersetCard 2)
    (fun Q => Disjoint Q P)
  rw [heq, Finset.card_powersetCard, Finset.card_powersetCard] at hh
  omega

theorem card_meeting_pairs_real {α : Type*} [DecidableEq α] {U P : Finset α} (hP : P ⊆ U) :
    (((U.powersetCard 2).filter (fun Q => ¬ Disjoint Q P)).card : ℝ) =
      (P.card : ℝ) * U.card - (P.card : ℝ)^2 / 2 - (P.card : ℝ) / 2 := by
  classical
  have hcard := card_meeting_pairs_add U P
  have hsub : (U \ P).card + P.card = U.card := Finset.card_sdiff_add_card_eq_card hP
  have hreal : (((U.powersetCard 2).filter (fun Q => ¬ Disjoint Q P)).card : ℝ) +
      ((U \ P).card : ℝ) * ((U \ P).card - 1) / 2 = (U.card : ℝ) * (U.card - 1) / 2 := by
    have hh : (((U.powersetCard 2).filter (fun Q => ¬ Disjoint Q P)).card : ℝ) +
        (((U \ P).card.choose 2 : ℕ) : ℝ) = ((U.card.choose 2 : ℕ) : ℝ) := by exact_mod_cast hcard
    simpa only [Nat.cast_choose_two] using hh
  have hsubreal : ((U \ P).card : ℝ) + (P.card : ℝ) = U.card := by exact_mod_cast hsub
  nlinarith only [hreal, hsubreal]

theorem meetingPairPool_card_real {N c : ℕ} {P : Finset ℕ}
    (hP : P ⊆ Finset.Icc 1 N) (hcP : c ∉ P) :
    ((meetingPairPool N c P).card : ℝ) ≤
      (P.card : ℝ) * N - (P.card : ℝ)^2 / 2 := by
  have hPU : P ⊆ (Finset.Icc 1 N).erase c := by
    intro p hp
    exact Finset.mem_erase.mpr ⟨fun hpc => hcP (hpc ▸ hp), hP hp⟩
  have hcount := card_meeting_pairs_real hPU
  have hU : ((Finset.Icc 1 N).erase c).card ≤ N := by
    have hh := Finset.card_le_card (Finset.erase_subset (s := Finset.Icc 1 N) c)
    simpa only [Nat.card_Icc, Nat.add_sub_cancel] using hh
  have hUR : (((Finset.Icc 1 N).erase c).card : ℝ) ≤ N := by exact_mod_cast hU
  have hmul := mul_le_mul_of_nonneg_left hUR (Nat.cast_nonneg P.card : (0 : ℝ) ≤ P.card)
  change ((meetingPairPool N c P).card : ℝ) = _ at hcount
  nlinarith only [hcount, hmul, Nat.cast_nonneg (α := ℝ) P.card]

theorem meetingPairPool_card_add_choose_le {N c : ℕ} {P : Finset ℕ}
    (hP : P ⊆ Finset.Icc 1 N) (hcP : c ∉ P) :
    (meetingPairPool N c P).card + P.card.choose 2 ≤ P.card * N := by
  have hbound := meetingPairPool_card_real hP hcP
  have hh : ((meetingPairPool N c P).card : ℝ) + ((P.card.choose 2 : ℕ) : ℝ) ≤
      (P.card : ℝ) * N := by
    rw [Nat.cast_choose_two]
    nlinarith only [hbound, Nat.cast_nonneg (α := ℝ) P.card]
  exact_mod_cast hh

theorem crooked_meeting_set_card_le_natLog {N c : ℕ} {F : Finset (Finset ℕ)} {P : Finset ℕ}
    (hF : Erdos272.IsArithInterSet N F) (hc : ∀ S ∈ F, c ∈ S)
    (hcI : c ∈ Finset.Icc 1 N) (hcrooked : ∀ S ∈ F, IsCrooked S)
    (hP : P ⊆ Finset.Icc 1 N) (hcP : c ∉ P)
    (hmet : ∀ S ∈ F, (S.erase c ∩ P).Nonempty) :
    F.card + P.card.choose 2 ≤ P.card * N + 48 * N * (Nat.log 2 N + 1)^3 := by
  have hfamily := crooked_meeting_set_card_le hF hc hcrooked hmet
  have hpairs := meetingPairPool_card_add_choose_le hP hcP
  have hexception := witnessExceptionBound_le_natLog hcI
  omega

end
section
open Finset

theorem IsCrooked.card_three_le {S : Finset ℕ} (hS : IsCrooked S) : 3 ≤ S.card := by
  by_contra hcard
  have hsmall : S.card ≤ 2 := by omega
  rcases S.eq_empty_or_nonempty with hzero | hne
  · apply hS
    subst S
    exact ⟨0, by simp⟩
  · obtain ⟨l, hl, hAP⟩ := nonempty_small_isAP hne hsmall
    exact hS ⟨l, hAP⟩

theorem arithInter_inter_nonempty {N : ℕ} {F : Finset (Finset ℕ)} {S T : Finset ℕ}
    (hF : Erdos272.IsArithInterSet N F) (hS : S ∈ F) (hT : T ∈ F)
    (hSnonempty : S.Nonempty) : (S ∩ T).Nonempty := by
  by_cases hST : S = T
  · simpa only [hST, Finset.inter_self] using hST ▸ hSnonempty
  obtain ⟨l, hl, hAP⟩ := hF.2 hS hT hST
  by_contra hnot
  have heq : S ∩ T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnot
  rw [heq] at hAP
  exact Set.not_isAPOfLength_empty hl (by simpa using hAP)

theorem crooked_two_point_cover_card_le {N : ℕ} {F : Finset (Finset ℕ)} {H : Finset ℕ}
    (hF : Erdos272.IsArithInterSet N F) (hcrooked : ∀ S ∈ F, IsCrooked S)
    (hH : H ⊆ Finset.Icc 1 N) (hmet : ∀ S ∈ F, 2 ≤ (S ∩ H).card) :
    F.card ≤ H.card * (H.card * N + 48 * N * (Nat.log 2 N + 1)^3) := by
  classical
  let D : ℕ → Finset (Finset ℕ) := fun c => F.filter (fun S => c ∈ S)
  have hDsub : ∀ c, D c ⊆ F := fun c => Finset.filter_subset _ _
  have hDc : ∀ c ∈ H, (D c).card ≤ H.card * N + 48 * N * (Nat.log 2 N + 1)^3 := by
    intro c hcH
    have hhit : ∀ S ∈ D c, (S.erase c ∩ H.erase c).Nonempty := by
      intro S hS
      have hSF := hDsub c hS
      have hcount := hmet S hSF
      have hne : ((S ∩ H).erase c).Nonempty := by
        apply Finset.card_pos.mp
        have hh := Finset.card_erase_add_one (Finset.mem_inter.mpr
          ⟨(Finset.mem_filter.mp hS).2, hcH⟩)
        omega
      obtain ⟨x, hx⟩ := hne
      obtain ⟨hxc, hxSH⟩ := Finset.mem_erase.mp hx
      obtain ⟨hxS, hxH⟩ := Finset.mem_inter.mp hxSH
      exact ⟨x, Finset.mem_inter.mpr
        ⟨Finset.mem_erase.mpr ⟨hxc, hxS⟩, Finset.mem_erase.mpr ⟨hxc, hxH⟩⟩⟩
    have hh := crooked_meeting_set_card_le_natLog (arithInterSet_mono hF (hDsub c))
      (fun S hS => (Finset.mem_filter.mp hS).2) (hH hcH)
      (fun S hS => hcrooked S (hDsub c hS)) ((Finset.erase_subset _ _).trans hH)
      (Finset.notMem_erase _ _) hhit
    have hpc := Nat.mul_le_mul_right N (Finset.card_erase_le (s := H) (a := c))
    omega
  have hcover : F ⊆ H.biUnion D := by
    intro S hS
    have hne : (S ∩ H).Nonempty := Finset.card_pos.mp (by have := hmet S hS; omega)
    obtain ⟨c, hc⟩ := hne
    exact Finset.mem_biUnion.mpr ⟨c, (Finset.mem_inter.mp hc).2,
      Finset.mem_filter.mpr ⟨hS, (Finset.mem_inter.mp hc).1⟩⟩
  calc
    F.card ≤ (H.biUnion D).card := Finset.card_le_card hcover
    _ ≤ ∑ c ∈ H, (D c).card := Finset.card_biUnion_le
    _ ≤ ∑ c ∈ H, (H.card * N + 48 * N * (Nat.log 2 N + 1)^3) := Finset.sum_le_sum hDc
    _ = _ := by simp

theorem crooked_anchored_with_avoider_card_le {N c : ℕ} {F D : Finset (Finset ℕ)}
    {T : Finset ℕ} (hF : Erdos272.IsArithInterSet N F) (hDF : D ⊆ F)
    (hc : ∀ S ∈ D, c ∈ S) (hcI : c ∈ Finset.Icc 1 N)
    (hcrooked : ∀ S ∈ D, IsCrooked S) (hT : T ∈ F) (hcT : c ∉ T) :
    D.card ≤ T.card * N + 48 * N * (Nat.log 2 N + 1)^3 := by
  have hhit : ∀ S ∈ D, (S.erase c ∩ T).Nonempty := by
    intro S hS
    obtain ⟨x, hx⟩ := arithInter_inter_nonempty hF (hDF hS) hT ⟨c, hc S hS⟩
    obtain ⟨hxS, hxT⟩ := Finset.mem_inter.mp hx
    exact ⟨x, Finset.mem_inter.mpr ⟨Finset.mem_erase.mpr
      ⟨fun hxc => hcT (hxc ▸ hxT), hxS⟩, hxT⟩⟩
  have hh := crooked_meeting_set_card_le_natLog (arithInterSet_mono hF hDF) hc hcI
    hcrooked (Finset.mem_powerset.mp (hF.1 hT)) hcT hhit
  omega

theorem two_points_in_union_of_singleton_inter {S T A : Finset ℕ} {c : ℕ}
    (hST : S ∩ T = {c}) (hcA : c ∉ A)
    (hAS : (A ∩ S).Nonempty) (hAT : (A ∩ T).Nonempty) :
    2 ≤ (A ∩ (S ∪ T).erase c).card := by
  obtain ⟨x, hx⟩ := hAS
  obtain ⟨y, hy⟩ := hAT
  obtain ⟨hxA, hxS⟩ := Finset.mem_inter.mp hx
  obtain ⟨hyA, hyT⟩ := Finset.mem_inter.mp hy
  have hxc : x ≠ c := fun hh => hcA (hh ▸ hxA)
  have hyc : y ≠ c := fun hh => hcA (hh ▸ hyA)
  have hxy : x ≠ y := by
    intro hh
    have hxT : x ∈ T := hh ▸ hyT
    have hhmem : x ∈ ({c} : Finset ℕ) := hST ▸ Finset.mem_inter.mpr ⟨hxS, hxT⟩
    exact hxc (Finset.mem_singleton.mp hhmem)
  have hxH : x ∈ A ∩ (S ∪ T).erase c := Finset.mem_inter.mpr
    ⟨hxA, Finset.mem_erase.mpr ⟨hxc, Finset.mem_union_left _ hxS⟩⟩
  have hyH : y ∈ A ∩ (S ∪ T).erase c := Finset.mem_inter.mpr
    ⟨hyA, Finset.mem_erase.mpr ⟨hyc, Finset.mem_union_right _ hyT⟩⟩
  have hsub : {x, y} ⊆ A ∩ (S ∪ T).erase c := by simp [Finset.insert_subset_iff, hxH, hyH]
  simpa only [Finset.card_pair hxy] using Finset.card_le_card hsub

theorem small_crooked_no_common_point_card_le {N k s : ℕ} {F K : Finset (Finset ℕ)}
    (hF : Erdos272.IsArithInterSet N F) (hKF : K ⊆ F)
    (hcrooked : ∀ S ∈ K, IsCrooked S) (hsmall : ∀ S ∈ K, S.card ≤ k)
    (hbound : ∀ S ∈ F, S.card ≤ s)
    (hno : ∀ c ∈ Finset.Icc 1 N, ∃ T ∈ F, c ∉ T) :
    K.card ≤ s * N + 4 * k^2 * N + (2 * k + 1) * (48 * N * (Nat.log 2 N + 1)^3) := by
  classical
  let E := 48 * N * (Nat.log 2 N + 1)^3
  rcases K.eq_empty_or_nonempty with hKzero | hKne
  · simp [hKzero]
  by_cases hsingle : ∃ S ∈ K, ∃ T ∈ K, (S ∩ T).card = 1
  · obtain ⟨S, hS, T, hT, hcard⟩ := hsingle
    obtain ⟨c, hST⟩ := Finset.card_eq_one.mp hcard
    have hcS : c ∈ S := (Finset.mem_inter.mp (hST.symm ▸ Finset.mem_singleton_self c)).1
    have hcI : c ∈ Finset.Icc 1 N := Finset.mem_powerset.mp (hF.1 (hKF hS)) hcS
    obtain ⟨V, hV, hcV⟩ := hno c hcI
    let D := K.filter (fun A => c ∈ A)
    let B := K.filter (fun A => c ∉ A)
    have hDK : D ⊆ K := Finset.filter_subset _ _
    have hBK : B ⊆ K := Finset.filter_subset _ _
    have hD := crooked_anchored_with_avoider_card_le hF (hDK.trans hKF)
      (fun A hA => (Finset.mem_filter.mp hA).2) hcI
      (fun A hA => hcrooked A (hDK hA)) hV hcV
    have hVN := Nat.mul_le_mul_right N (hbound V hV)
    have hhit : ∀ A ∈ B, 2 ≤ (A ∩ (S ∪ T).erase c).card := by
      intro A hA
      have hAne : A.Nonempty := Finset.card_pos.mp (by
        have := (hcrooked A (hBK hA)).card_three_le
        omega)
      exact two_points_in_union_of_singleton_inter hST (Finset.mem_filter.mp hA).2
        (arithInter_inter_nonempty hF (hKF (hBK hA)) (hKF hS) hAne)
        (arithInter_inter_nonempty hF (hKF (hBK hA)) (hKF hT) hAne)
    have hHsub : (S ∪ T).erase c ⊆ Finset.Icc 1 N :=
      (Finset.erase_subset _ _).trans (Finset.union_subset
        (Finset.mem_powerset.mp (hF.1 (hKF hS))) (Finset.mem_powerset.mp (hF.1 (hKF hT))))
    have hB := crooked_two_point_cover_card_le (arithInterSet_mono hF (hBK.trans hKF))
      (fun A hA => hcrooked A (hBK hA)) hHsub hhit
    have hHcard : ((S ∪ T).erase c).card ≤ 2 * k := by
      have hh := (Finset.card_erase_le (s := S ∪ T) (a := c)).trans (Finset.card_union_le S T)
      have hs := hsmall S hS
      have ht := hsmall T hT
      omega
    have hBlim : B.card ≤ (2 * k) * (2 * k * N + E) := hB.trans
      (Nat.mul_le_mul hHcard (Nat.add_le_add_right (Nat.mul_le_mul_right N hHcard) E))
    have hpartition := Finset.card_filter_add_card_filter_not (s := K) (fun A => c ∈ A)
    change D.card + B.card = K.card at hpartition
    change D.card ≤ V.card * N + E at hD
    change K.card ≤ s * N + 4 * k^2 * N + (2 * k + 1) * E
    nlinarith only [hD, hVN, hBlim, hpartition]
  · obtain ⟨H, hH⟩ := hKne
    have hhit : ∀ A ∈ K, 2 ≤ (A ∩ H).card := by
      intro A hA
      have hAne : A.Nonempty := Finset.card_pos.mp (by
        have := (hcrooked A hA).card_three_le
        omega)
      have hne := arithInter_inter_nonempty hF (hKF hA) (hKF hH) hAne
      have hpos := Finset.card_pos.mpr hne
      have hnot : (A ∩ H).card ≠ 1 := fun hh => hsingle ⟨A, hA, H, hH, hh⟩
      omega
    have hh := crooked_two_point_cover_card_le (arithInterSet_mono hF hKF) hcrooked
      (Finset.mem_powerset.mp (hF.1 (hKF hH))) hhit
    have hhk := hsmall H hH
    have hlim : K.card ≤ k * (k * N + E) := hh.trans
      (Nat.mul_le_mul hhk (Nat.add_le_add_right (Nat.mul_le_mul_right N hhk) E))
    change K.card ≤ s * N + 4 * k^2 * N + (2 * k + 1) * E
    nlinarith only [hlim, Nat.zero_le (s * N), Nat.zero_le (k^2 * N), Nat.zero_le (k * E), Nat.zero_le E]

end
section
open Finset

theorem factorization_le_log_two {n p : ℕ} (hn : n ≠ 0) (hp : p ∈ n.primeFactors) :
    n.factorization p ≤ Nat.log 2 n := by
  apply (Nat.le_log_iff_pow_le (by decide) hn).mpr
  calc
    2 ^ n.factorization p ≤ p ^ n.factorization p :=
      Nat.pow_le_pow_left (Nat.prime_of_mem_primeFactors hp).two_le _
    _ ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.ordProj_dvd n p)

theorem divisor_card_pow_le_log_power {n : ℕ} (hn : n ≠ 0) (k : ℕ) :
    n.divisors.card ^ k ≤ n * (Nat.log 2 n + 1)^(k * 2^k) := by
  classical
  let L := Nat.log 2 n + 1
  let S := n.primeFactors.filter (fun p => p < 2^k)
  have hL : 1 ≤ L := by dsimp [L]; omega
  have hScard : S.card ≤ 2^k := by
    have hsub : S ⊆ Finset.range (2^k) := fun p hp =>
      Finset.mem_range.mpr (Finset.mem_filter.mp hp).2
    simpa only [Finset.card_range] using Finset.card_le_card hsub
  have hfactor : ∀ p ∈ n.primeFactors, (n.factorization p + 1)^k ≤
      (if p < 2^k then L^k else 1) * p ^ n.factorization p := by
    intro p hp
    by_cases hpk : p < 2^k
    · rw [if_pos hpk]
      have he : n.factorization p + 1 ≤ L := Nat.add_le_add_right (factorization_le_log_two hn hp) 1
      have hp1 : 1 ≤ p ^ n.factorization p := Nat.one_le_pow _ _ (Nat.prime_of_mem_primeFactors hp).pos
      exact (Nat.pow_le_pow_left he k).trans (Nat.le_mul_of_pos_right _ hp1)
    · rw [if_neg hpk, one_mul]
      calc
        (n.factorization p + 1)^k ≤ (2 ^ n.factorization p)^k :=
          Nat.pow_le_pow_left (Nat.succ_le_of_lt Nat.lt_two_pow_self) k
        _ = (2^k) ^ n.factorization p := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
        _ ≤ p ^ n.factorization p := Nat.pow_le_pow_left (by omega) _
  have hprod : n.divisors.card ^ k ≤
      (∏ p ∈ n.primeFactors, if p < 2^k then L^k else 1) * n := by
    rw [Nat.card_divisors hn, ← Finset.prod_pow]
    calc
      _ ≤ ∏ p ∈ n.primeFactors, ((if p < 2^k then L^k else 1) * p ^ n.factorization p) :=
        Finset.prod_le_prod' hfactor
      _ = _ := by rw [Finset.prod_mul_distrib, ← Nat.prod_primeFactors_pow_factorization hn]
  have hprodEq : (∏ p ∈ n.primeFactors, if p < 2^k then L^k else 1) = L^(k * S.card) := by
    simp [Finset.prod_ite, S, pow_mul]
  rw [hprodEq] at hprod
  have hpower : L^(k * S.card) ≤ L^(k * 2^k) :=
    Nat.pow_le_pow_right hL (Nat.mul_le_mul_left k hScard)
  exact hprod.trans (by simpa only [Nat.mul_comm] using Nat.mul_le_mul_right n hpower)

end
section
open Finset Filter

theorem eventually_natLog_pow_le (k : ℕ) :
    ∀ᶠ n : ℕ in Filter.atTop, (Nat.log 2 n + 1)^k ≤ n := by
  have ho := (Real.isLittleO_pow_logb_id_atTop (b := (2 : ℝ)) (n := k)).bound
    (by positivity : (0 : ℝ) < ((2 : ℝ)^k)⁻¹)
  have hnat : ∀ᶠ n : ℕ in Filter.atTop,
      ‖Real.logb 2 (n : ℝ)^k‖ ≤ ((2 : ℝ)^k)⁻¹ * ‖(n : ℝ)‖ :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).eventually ho
  filter_upwards [hnat, Filter.eventually_ge_atTop 2] with n hn hn2
  have hlogn : 1 ≤ Nat.log 2 n :=
    (Nat.le_log_iff_pow_le (by decide) (by omega)).mpr (by simpa using hn2)
  have hcast : (1 : ℝ) ≤ Nat.log 2 n := by exact_mod_cast hlogn
  have hle : (Nat.log 2 n : ℝ) ≤ Real.logb 2 n := by
    simpa only [Nat.cast_ofNat] using Real.natLog_le_logb n 2
  have hlogpos : (0 : ℝ) ≤ Real.logb 2 n := by linarith
  have hbase : (Nat.log 2 n : ℝ) + 1 ≤ 2 * Real.logb 2 n := by linarith
  have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (Nat.log 2 n : ℝ) + 1) hbase k
  simp only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hlogpos k),
    abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)] at hn
  have hmul := mul_le_mul_of_nonneg_left hn (by positivity : (0 : ℝ) ≤ (2 : ℝ)^k)
  have htwo : (2 : ℝ)^k ≠ 0 := by positivity
  simp only [← mul_assoc, mul_inv_cancel₀ htwo, one_mul] at hmul
  rw [mul_pow] at hpow
  have hresult : (((Nat.log 2 n + 1)^k : ℕ) : ℝ) ≤ n := by
    push_cast
    exact hpow.trans hmul
  exact_mod_cast hresult

theorem eventually_divisor_card_pow_le (k : ℕ) :
    ∀ᶠ n : ℕ in Filter.atTop, n.divisors.card^k ≤ n := by
  filter_upwards [eventually_natLog_pow_le ((2 * k) * 2^(2 * k)),
    Filter.eventually_ge_atTop 1] with n hn hn1
  have hdiv := divisor_card_pow_le_log_power (by omega : n ≠ 0) (2 * k)
  have hmul := Nat.mul_le_mul_left n hn
  have hsq : (n.divisors.card^k)^2 ≤ n^2 := by
    have hh := hdiv.trans hmul
    simpa only [pow_mul, Nat.mul_comm 2 k, pow_two] using hh
  nlinarith only [hsq]

theorem eventually_uniform_divisor_card_pow_le (k : ℕ) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ n ≤ N, n.divisors.card^k ≤ N := by
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.mp (eventually_divisor_card_pow_le k)
  filter_upwards [Filter.eventually_ge_atTop (n₀^k)] with N hN n hnN
  by_cases hn : n₀ ≤ n
  · exact (hn₀ n hn).trans hnN
  · have hcard : n.divisors.card ≤ n₀ := (Nat.card_divisors_le_self n).trans (by omega)
    exact (Nat.pow_le_pow_left hcard k).trans hN

end
section
open Finset

def coprimePrefix (m K : ℕ) : ℕ := ((Finset.Icc 1 K).filter (fun j => m.Coprime j)).card

theorem moebius_divisor_indicator (n : ℕ) :
    (∑ d ∈ n.divisors, ArithmeticFunction.moebius d) = if n = 1 then 1 else 0 := by
  rw [← ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.moebius_mul_coe_zeta,
    ArithmeticFunction.one_apply]

theorem coprime_moebius_indicator {m : ℕ} (hm : 0 < m) (j : ℕ) :
    (∑ d ∈ m.divisors, if d ∣ j then ArithmeticFunction.moebius d else 0) =
      if m.Coprime j then 1 else 0 := by
  have hg : Nat.gcd m j ≠ 0 := (Nat.gcd_pos_of_pos_left j hm).ne'
  have hfilter : m.divisors.filter (fun d => d ∣ j) = (Nat.gcd m j).divisors := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hdm, _⟩, hdj⟩
      exact ⟨Nat.dvd_gcd hdm hdj, hg⟩
    · rintro ⟨hdg, _⟩
      exact ⟨⟨hdg.trans (Nat.gcd_dvd_left m j), hm.ne'⟩,
        hdg.trans (Nat.gcd_dvd_right m j)⟩
  rw [← Finset.sum_filter, hfilter, moebius_divisor_indicator]

theorem card_multiples_Icc (K d : ℕ) : ((Finset.Icc 1 K).filter (fun j => d ∣ j)).card = K / d := by
  have hset : (Finset.range (K + 1)).filter (fun j => j ≠ 0 ∧ d ∣ j) =
      (Finset.Icc 1 K).filter (fun j => d ∣ j) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    omega
  rw [← hset]
  exact Nat.card_multiples' K d

theorem coprimePrefix_moebius {m : ℕ} (hm : 0 < m) (K : ℕ) :
    (coprimePrefix m K : ℤ) =
      ∑ d ∈ m.divisors, ArithmeticFunction.moebius d * ((K / d : ℕ) : ℤ) := by
  calc
    (coprimePrefix m K : ℤ) = ∑ j ∈ Finset.Icc 1 K, if m.Coprime j then (1 : ℤ) else 0 := by
      simp [coprimePrefix]
    _ = ∑ j ∈ Finset.Icc 1 K, ∑ d ∈ m.divisors,
        if d ∣ j then ArithmeticFunction.moebius d else 0 := by
      exact Finset.sum_congr rfl (fun j hj => (coprime_moebius_indicator hm j).symm)
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d hd
      rw [← Finset.sum_filter]
      simp [Finset.sum_const, card_multiples_Icc, mul_comm]

theorem coprimePrefix_moebius_real {m : ℕ} (hm : 0 < m) (K : ℕ) :
    (coprimePrefix m K : ℝ) =
      ∑ d ∈ m.divisors, (ArithmeticFunction.moebius d : ℝ) * ((K / d : ℕ) : ℝ) := by
  have hh := congrArg (fun z : ℤ => (z : ℝ)) (coprimePrefix_moebius hm K)
  simpa only [Int.cast_natCast, Int.cast_sum, Int.cast_mul] using hh

theorem nat_div_error_le_one {K d : ℕ} (hd : 0 < d) :
    |((K / d : ℕ) : ℝ) - (K : ℝ) / d| ≤ 1 := by
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hupper := Nat.cast_div_le (α := ℝ) (m := K) (n := d)
  have hlt : K < (K / d + 1) * d := by
    have hmod := Nat.mod_lt K hd
    have heq := Nat.mod_add_div K d
    nlinarith only [hmod, heq]
  have hlower : (K : ℝ) / d < ((K / d : ℕ) : ℝ) + 1 := by
    apply (div_lt_iff₀ hdR).mpr
    exact_mod_cast hlt
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem moebius_reciprocal_totient {m : ℕ} (hm : 0 < m) :
    (∑ d ∈ m.divisors, (ArithmeticFunction.moebius d : ℝ) / d) = (m.totient : ℝ) / m := by
  have hprefix : coprimePrefix m m = m.totient := card_coprime_Icc m
  have hsum := coprimePrefix_moebius_real hm m
  rw [hprefix] at hsum
  have heq : (∑ d ∈ m.divisors, (ArithmeticFunction.moebius d : ℝ) / d) * (m : ℝ) =
      m.totient := by
    rw [Finset.sum_mul, hsum]
    apply Finset.sum_congr rfl
    intro d hd
    have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr (Nat.pos_of_mem_divisors hd)
    have hdiv : ((m / d : ℕ) : ℝ) = (m : ℝ) / d := by
      apply (eq_div_iff hdpos.ne').mpr
      exact_mod_cast Nat.div_mul_cancel (Nat.mem_divisors.mp hd).1
    rw [hdiv]
    ring
  exact (eq_div_iff (Nat.cast_ne_zero.mpr hm.ne')).mpr heq

theorem coprimePrefix_error_le {m : ℕ} (hm : 0 < m) (K : ℕ) :
    |(coprimePrefix m K : ℝ) - (K : ℝ) * m.totient / m| ≤ m.divisors.card := by
  have heq : (coprimePrefix m K : ℝ) - (K : ℝ) * m.totient / m =
      ∑ d ∈ m.divisors, (ArithmeticFunction.moebius d : ℝ) *
        (((K / d : ℕ) : ℝ) - (K : ℝ) / d) := by
    have hphi : (K : ℝ) * m.totient / m =
        (K : ℝ) * ∑ d ∈ m.divisors, (ArithmeticFunction.moebius d : ℝ) / d := by
      rw [moebius_reciprocal_totient hm]
      ring
    rw [coprimePrefix_moebius_real hm, hphi, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    ring
  rw [heq]
  calc
    _ ≤ ∑ d ∈ m.divisors, |(ArithmeticFunction.moebius d : ℝ) *
        (((K / d : ℕ) : ℝ) - (K : ℝ) / d)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ m.divisors, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      rw [abs_mul]
      have hmu : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
      exact (mul_le_mul hmu (nat_div_error_le_one (Nat.pos_of_mem_divisors hd))
        (abs_nonneg _) (by norm_num)).trans (by norm_num)
    _ = _ := by simp

theorem coprimeInterval_error_le {m A B : ℕ} (hm : 0 < m) (hAB : A ≤ B) :
    |(((Finset.Ioc A B).filter (fun j => m.Coprime j)).card : ℝ) -
      ((B : ℝ) - A) * m.totient / m| ≤ 2 * (m.divisors.card : ℝ) := by
  have hpartition : ((Finset.Ioc A B).filter (fun j => m.Coprime j)).card +
      coprimePrefix m A = coprimePrefix m B := by
    have hdis : Disjoint (Finset.Icc 1 A) (Finset.Ioc A B) := by
      apply Finset.disjoint_left.mpr
      intro j hjA hjB
      have ha := Finset.mem_Icc.mp hjA
      have hb := Finset.mem_Ioc.mp hjB
      omega
    have hunion : Finset.Icc 1 A ∪ Finset.Ioc A B = Finset.Icc 1 B := by
      ext j
      simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
      omega
    have hdis' : Disjoint ((Finset.Icc 1 A).filter (fun j => m.Coprime j))
        ((Finset.Ioc A B).filter (fun j => m.Coprime j)) :=
      Finset.disjoint_filter_filter hdis
    have hh := Finset.card_union_of_disjoint hdis'
    rw [← Finset.filter_union, hunion] at hh
    dsimp [coprimePrefix]
    omega
  have hpartR : (((Finset.Ioc A B).filter (fun j => m.Coprime j)).card : ℝ) +
      (coprimePrefix m A : ℝ) = coprimePrefix m B := by exact_mod_cast hpartition
  have hA := abs_le.mp (coprimePrefix_error_le hm A)
  have hB := abs_le.mp (coprimePrefix_error_le hm B)
  rw [sub_mul, sub_div]
  apply abs_le.mpr
  constructor <;> nlinarith only [hpartR, hA.1, hA.2, hB.1, hB.2]

theorem coprimeInterval_log_lower {m A B : ℕ} (hm : 0 < m) (hAB : A ≤ B) :
    B - A ≤ (((Finset.Ioc A B).filter (fun j => m.Coprime j)).card +
      2 * m.divisors.card) * (Nat.log 2 m + 1) := by
  let C := ((Finset.Ioc A B).filter (fun j => m.Coprime j)).card
  let L := Nat.log 2 m + 1
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hratio : (1 : ℝ) ≤ (L : ℝ) * m.totient / m := by
    apply (le_div_iff₀ hmR).mpr
    rw [one_mul]
    exact_mod_cast le_log_succ_mul_totient m
  have herror := (abs_le.mp (coprimeInterval_error_le hm hAB)).1
  have hc : ((B : ℝ) - A) * m.totient / m ≤ (C : ℝ) + 2 * m.divisors.card := by
    dsimp [C]
    linarith only [herror]
  have hlen : (0 : ℝ) ≤ (B : ℝ) - A := sub_nonneg.mpr (by exact_mod_cast hAB)
  have hreal : (B : ℝ) - A ≤ ((C : ℝ) + 2 * m.divisors.card) * L := by
    calc
      _ = ((B : ℝ) - A) * 1 := by ring
      _ ≤ ((B : ℝ) - A) * ((L : ℝ) * m.totient / m) :=
        mul_le_mul_of_nonneg_left hratio hlen
      _ = (L : ℝ) * (((B : ℝ) - A) * m.totient / m) := by ring
      _ ≤ (L : ℝ) * ((C : ℝ) + 2 * m.divisors.card) :=
        mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg L)
      _ = _ := by ring
  have hcast : ((B - A : ℕ) : ℝ) ≤ (((C + 2 * m.divisors.card) * L : ℕ) : ℝ) := by
    simpa only [Nat.cast_sub hAB, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] using hreal
  exact_mod_cast hcast

theorem coprimeInterval_log_density {m A B : ℕ} (hm : 0 < m) (hAB : A ≤ B)
    (hlength : 4 * m.divisors.card * (Nat.log 2 m + 1) ≤ B - A) :
    B - A ≤ 2 * ((Finset.Ioc A B).filter (fun j => m.Coprime j)).card * (Nat.log 2 m + 1) := by
  have hh := coprimeInterval_log_lower hm hAB
  nlinarith only [hh, hlength]

end
section
open Finset

theorem fixedGap_core {S : Finset ℕ} {u v : ℕ} (huv : u < v) (hu : u ∈ S) (hv : v ∈ S) :
    ∃ U : Finset ℕ, U ⊆ S ∧ (∃ l : ℕ∞, (U : Set ℕ).IsAPOfLength l) ∧
      ConsecutiveIn U u v ∧ ∀ T ⊆ S, FixedGapAP u v T → T ⊆ U := by
  classical
  let D := S.powerset.filter (fun T => FixedGapAP u v T)
  let U := D.biUnion id
  have hpairCon : ConsecutiveIn {u, v} u v := by
    refine ⟨by simp, by simp, huv, ?_⟩
    intro x hx hbetween
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    omega
  have hpairAP : (({u, v} : Finset ℕ) : Set ℕ).IsAPOfLength 2 :=
    by simpa using Nat.isAPOfLength_pair huv
  have hpairD : {u, v} ∈ D := Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (by simp [Finset.insert_subset_iff, hu, hv]),
      Or.inr ⟨⟨2, hpairAP⟩, hpairCon⟩⟩
  have huU : u ∈ U := Finset.mem_biUnion.mpr ⟨{u, v}, hpairD, by simp⟩
  have hclass : FixedGapAP u v U := union_closed_biUnion (fixedGapAP_empty u v)
    (fun T V hT hV => fixedGapAP_union hT hV) D id (fun T hT => (Finset.mem_filter.mp hT).2)
  have hUP : (∃ l : ℕ∞, (U : Set ℕ).IsAPOfLength l) ∧ ConsecutiveIn U u v := by
    rcases hclass with hzero | hclass
    · simp [hzero] at huU
    · exact hclass
  refine ⟨U, ?_, hUP.1, hUP.2, ?_⟩
  · intro x hx
    obtain ⟨T, hT, hxT⟩ := Finset.mem_biUnion.mp hx
    exact Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1 hxT
  · intro T hTS hT x hx
    exact Finset.mem_biUnion.mpr ⟨T, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hTS, hT⟩, hx⟩

theorem natAP_prefix_subset_of_endpoints {a d k u v t : ℕ} (hd : 0 < d)
    (hu : u ∈ natAP a d k) (hv : v ∈ natAP a d k) (ht : u + t * d ≤ v) :
    natAP u d (t + 1) ⊆ natAP a d k := by
  have huv : u ≤ v := by omega
  have hslice := natAP_inter_Icc_eq_segment hd hu hv huv
  intro x hx
  obtain ⟨i, hi, hxi⟩ := mem_natAP.mp hx
  have hit : i * d ≤ t * d := Nat.mul_le_mul_right d (by omega : i ≤ t)
  have hxseg : x ∈ apSegment u v d := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
    rw [← hxi, Nat.add_sub_cancel_left]
    exact dvd_mul_left d i
  exact (Finset.mem_inter.mp (hslice.symm ▸ hxseg)).1

theorem natAP_consecutive_of_neighbor {a d k u : ℕ} (hd : 0 < d)
    (hu : u ∈ natAP a d k) (hv : u + d ∈ natAP a d k) :
    ConsecutiveIn (natAP a d k) u (u + d) := by
  refine ⟨hu, hv, by omega, ?_⟩
  intro x hx hbetween
  have hdiv := natAP_dvd_anchorDistance hu hx
  have hux : u ≤ x := by omega
  rw [anchorDistance, max_eq_right hux, min_eq_left hux] at hdiv
  have hle := Nat.le_of_dvd (by omega : 0 < x - u) hdiv
  omega

theorem proper_divisor_double_le {e d : ℕ} (he : 0 < e) (hed : e ∣ d) (hlt : e < d) :
    2 * e ≤ d := by
  obtain ⟨q, hq⟩ := hed
  have hq2 : 2 ≤ q := by nlinarith only [he, hlt, hq]
  nlinarith only [hq2, hq, he]

theorem minimal_prefix_witness_core {S : Finset ℕ} {c d K : ℕ} (hd : 0 < d) (hK : 1 ≤ K)
    (hprefix : natAP c d (K + 1) ⊆ S)
    (hmin : ∀ e : ℕ, 0 < e → natAP c e (K + 1) ⊆ S → d ≤ e) :
    ∃ U : Finset ℕ, U ⊆ S ∧ (∃ l : ℕ∞, (U : Set ℕ).IsAPOfLength l) ∧
      natAP c d (K + 1) ⊆ U ∧
      ∀ z ∈ S, z ∉ U → ∀ p : ℕ, 0 < p → p ≤ K → K ≤ 2 * p →
        p.Coprime (anchorDistance c z) → IsWitnessPair S c {c + p * d, z} := by
  have hcP : c ∈ natAP c d (K + 1) := mem_natAP.mpr ⟨0, by omega, by simp⟩
  have hvP : c + d ∈ natAP c d (K + 1) := mem_natAP.mpr ⟨1, by omega, by simp⟩
  obtain ⟨U, hUS, hUAP, hUcon, hmax⟩ := fixedGap_core (by omega : c < c + d)
    (hprefix hcP) (hprefix hvP)
  have hPU : natAP c d (K + 1) ⊆ U := hmax _ hprefix
    (Or.inr ⟨⟨K + 1, natAP_isAP hd⟩, natAP_consecutive_of_neighbor hd hcP hvP⟩)
  refine ⟨U, hUS, hUAP, hPU, ?_⟩
  intro z hz hzU p hp hpK hKp hcop
  let y := c + p * d
  have hyP : y ∈ natAP c d (K + 1) := mem_natAP.mpr ⟨p, by omega, rfl⟩
  have hyU : y ∈ U := hPU hyP
  have hyS : y ∈ S := hUS hyU
  have hcy : c < y := by dsimp [y]; nlinarith only [hp, hd]
  have hzc : z ≠ c := fun heq => hzU (heq.symm ▸ hPU hcP)
  have hyz : y ≠ z := fun heq => hzU (heq ▸ hyU)
  refine ⟨Finset.card_pair hyz, ?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_erase.mpr ⟨hcy.ne', hyS⟩
    · exact Finset.mem_erase.mpr ⟨hzc, hz⟩
  · rintro ⟨A, hAS, ⟨l, hAAP⟩, hCA⟩
    have hcA : c ∈ A := hCA (by simp)
    have hyA : y ∈ A := hCA (by simp [y])
    have hzA : z ∈ A := hCA (by simp)
    have hcardA : 2 ≤ A.card := by
      have hsub : {c, y} ⊆ A := by simp [Finset.insert_subset_iff, hcA, hyA]
      simpa [hcy.ne] using Finset.card_le_card hsub
    obtain ⟨a, e, he, hArep⟩ := nat_ap_eq_natAP hAAP hcardA
    have hep : e ∣ p * d := by
      have hh := natAP_dvd_anchorDistance (hArep ▸ hcA) (hArep ▸ hyA)
      have hdist : anchorDistance c y = p * d := by dsimp [anchorDistance, y]; omega
      simpa only [hdist] using hh
    have hez : e ∣ anchorDistance c z := natAP_dvd_anchorDistance (hArep ▸ hcA) (hArep ▸ hzA)
    have hecop : e.Coprime p := (hcop.of_dvd_right hez).symm
    have hed : e ∣ d := hecop.dvd_of_dvd_mul_left hep
    have heD : e ≤ d := Nat.le_of_dvd hd hed
    by_cases heq : e = d
    · have hvA : c + d ∈ A := by
        have hsub := natAP_prefix_subset_of_endpoints he (hArep ▸ hcA) (hArep ▸ hyA)
          (t := 1) (by dsimp [y] at hcy ⊢; nlinarith only [hp, heq])
        apply hArep.symm ▸ (hsub ?_)
        exact mem_natAP.mpr ⟨1, by omega, by simpa only [one_mul, heq]⟩
      have hcon : ConsecutiveIn A c (c + d) := by
        have hvAe : c + e ∈ A := by simpa only [heq] using hvA
        have hh := natAP_consecutive_of_neighbor he (hArep ▸ hcA) (hArep ▸ hvAe)
        have hhA : ConsecutiveIn A c (c + e) := hArep.symm ▸ hh
        simpa only [heq] using hhA
      exact hzU (hmax A hAS (Or.inr ⟨⟨l, hAAP⟩, hcon⟩) hzA)
    · have hdouble : 2 * e ≤ d := proper_divisor_double_le he hed (by omega)
      have hKe : c + K * e ≤ y := by dsimp [y]; nlinarith only [hdouble, hKp]
      have hsmallPrefix : natAP c e (K + 1) ⊆ S :=
        (natAP_prefix_subset_of_endpoints he (hArep ▸ hcA) (hArep ▸ hyA) hKe).trans
          (hArep ▸ hAS)
      have hh := hmin e he hsmallPrefix
      omega

end
section
open Finset

noncomputable def structuralWitnessPairs (S : Finset ℕ) (c : ℕ) : Finset (Finset ℕ) := by
  classical
  exact ((S.erase c).powersetCard 2).filter (fun Q => IsWitnessPair S c Q)

theorem mem_structuralWitnessPairs {S Q : Finset ℕ} {c : ℕ} :
    Q ∈ structuralWitnessPairs S c ↔ IsWitnessPair S c Q := by
  classical
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    exact Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨h.2.1, h.1⟩, h⟩

theorem sum_structuralWitnessPairs_card_le {N c : ℕ} {F : Finset (Finset ℕ)}
    (hF : Erdos272.IsArithInterSet N F) (hc : ∀ S ∈ F, c ∈ S) :
    (∑ S ∈ F, (structuralWitnessPairs S c).card) ≤ N.choose 2 := by
  classical
  let U := F.sigma (fun S => structuralWitnessPairs S c)
  have hmaps : Set.MapsTo (fun q : (Σ _ : Finset ℕ, Finset ℕ) => q.2)
      (U : Set (Σ _ : Finset ℕ, Finset ℕ)) ((Finset.Icc 1 N).powersetCard 2 : Set (Finset ℕ)) := by
    intro q hq
    obtain ⟨hS, hQ⟩ := Finset.mem_sigma.mp hq
    have hW := mem_structuralWitnessPairs.mp hQ
    refine Finset.mem_powersetCard.mpr ⟨?_, hW.1⟩
    exact hW.2.1.trans ((Finset.erase_subset _ _).trans (Finset.mem_powerset.mp (hF.1 hS)))
  have hinj : Set.InjOn (fun q : (Σ _ : Finset ℕ, Finset ℕ) => q.2) (U : Set (Σ _ : Finset ℕ, Finset ℕ)) := by
    rintro ⟨S, Q⟩ hu ⟨T, R⟩ hv hQR
    change Q = R at hQR
    obtain ⟨hS, hQ⟩ := Finset.mem_sigma.mp hu
    obtain ⟨hT, hR⟩ := Finset.mem_sigma.mp hv
    have hWQ := mem_structuralWitnessPairs.mp hQ
    have hWR := mem_structuralWitnessPairs.mp hR
    have hTS : T = S := witness_pair_private hF hS hT (hc S hS) (hc T hT) hWQ
      (by simpa only [hQR] using hWR.2.1.trans (Finset.erase_subset _ _))
    cases hTS
    cases hQR
    rfl
  simpa only [U, Finset.card_sigma, Finset.card_powersetCard, Nat.card_Icc, Nat.add_sub_cancel] using
    Finset.card_le_card_of_injOn _ hmaps hinj

theorem minimal_prefix_witnesses_count {S U : Finset ℕ} {c d K : ℕ}
    (hd : 0 < d) (hPU : natAP c d (K + 1) ⊆ U)
    (hW : ∀ z ∈ S, z ∉ U → ∀ p : ℕ, 0 < p → p ≤ K → K ≤ 2 * p →
      p.Coprime (anchorDistance c z) → IsWitnessPair S c {c + p * d, z}) :
    (∑ z ∈ S \ U, ((Finset.Ioc (K / 2) K).filter
      (fun p => (anchorDistance c z).Coprime p)).card) ≤ (structuralWitnessPairs S c).card := by
  classical
  let V := (S \ U).sigma (fun z => (Finset.Ioc (K / 2) K).filter
    (fun p => (anchorDistance c z).Coprime p))
  let f : (Σ _ : ℕ, ℕ) → Finset ℕ := fun q => {c + q.2 * d, q.1}
  have hspec : ∀ q ∈ V, c + q.2 * d ∈ U ∧ q.1 ∉ U ∧ IsWitnessPair S c (f q) := by
    intro q hq
    obtain ⟨hz, hp⟩ := Finset.mem_sigma.mp hq
    obtain ⟨hzS, hzU⟩ := Finset.mem_sdiff.mp hz
    obtain ⟨hpI, hcop⟩ := Finset.mem_filter.mp hp
    obtain ⟨hphalf, hpK⟩ := Finset.mem_Ioc.mp hpI
    have hppos : 0 < q.2 := by omega
    have hKp : K ≤ 2 * q.2 := by omega
    refine ⟨hPU (mem_natAP.mpr ⟨q.2, by omega, rfl⟩), hzU, ?_⟩
    exact hW q.1 hzS hzU q.2 hppos hpK hKp hcop.symm
  have hmaps : Set.MapsTo f (V : Set (Σ _ : ℕ, ℕ))
      (structuralWitnessPairs S c : Set (Finset ℕ)) :=
    fun q hq => mem_structuralWitnessPairs.mpr (hspec q hq).2.2
  have hinj : Set.InjOn f (V : Set (Σ _ : ℕ, ℕ)) := by
    rintro ⟨z, p⟩ hp ⟨w, q⟩ hq heq
    change ({c + p * d, z} : Finset ℕ) = {c + q * d, w} at heq
    have hpS := hspec ⟨z, p⟩ hp
    have hqS := hspec ⟨w, q⟩ hq
    have hzmem : z ∈ ({c + q * d, w} : Finset ℕ) := by rw [← heq]; simp
    have hz : z = w := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hzmem
      rcases hzmem with hbad | hzw
      · exact False.elim (hpS.2.1 (hbad.symm ▸ hqS.1))
      · exact hzw
    have hymem : c + p * d ∈ ({c + q * d, w} : Finset ℕ) := by rw [← heq]; simp
    have hy : c + p * d = c + q * d := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hymem
      rcases hymem with hy | hbad
      · exact hy
      · exact False.elim (hqS.2.1 (hbad ▸ hpS.1))
    have hpq : p = q := by nlinarith only [hy, hd]
    cases hz
    cases hpq
    rfl
  simpa only [V, Finset.card_sigma] using Finset.card_le_card_of_injOn f hmaps hinj

theorem minimal_prefix_many_witnesses {N D c d K : ℕ} {S : Finset ℕ}
    (hS : S ⊆ Finset.Icc 1 N) (hd : 0 < d) (hK : 1 ≤ K)
    (hprefix : natAP c d (K + 1) ⊆ S)
    (hmin : ∀ e : ℕ, 0 < e → natAP c e (K + 1) ⊆ S → d ≤ e)
    (hdivisor : ∀ n ≤ N, n.divisors.card ≤ D)
    (hlength : 8 * D * (Nat.log 2 N + 1) ≤ K) :
    ∃ U : Finset ℕ, U ⊆ S ∧ (∃ l : ℕ∞, (U : Set ℕ).IsAPOfLength l) ∧
      (S \ U).card * K ≤ 4 * (Nat.log 2 N + 1) * (structuralWitnessPairs S c).card := by
  obtain ⟨U, hUS, hUAP, hPU, hW⟩ := minimal_prefix_witness_core hd hK hprefix hmin
  refine ⟨U, hUS, hUAP, ?_⟩
  have hcP : c ∈ natAP c d (K + 1) := mem_natAP.mpr ⟨0, by omega, by simp⟩
  have hcI : c ∈ Finset.Icc 1 N := hS (hprefix hcP)
  have hrow : ∀ z ∈ S \ U, K ≤ 4 * (Nat.log 2 N + 1) *
      ((Finset.Ioc (K / 2) K).filter (fun p => (anchorDistance c z).Coprime p)).card := by
    intro z hz
    obtain ⟨hzS, hzU⟩ := Finset.mem_sdiff.mp hz
    have hcz : c ≠ z := fun heq => hzU (heq ▸ hPU hcP)
    have hm : 0 < anchorDistance c z := anchorDistance_pos hcz
    have hmN : anchorDistance c z ≤ N := anchorDistance_le_of_mem hcI (hS hzS)
    have htau := hdivisor (anchorDistance c z) hmN
    have hlog : Nat.log 2 (anchorDistance c z) + 1 ≤ Nat.log 2 N + 1 :=
      Nat.add_le_add_right (Nat.log_mono_right hmN) 1
    have hcoef := Nat.mul_le_mul htau hlog
    have hlen : 4 * (anchorDistance c z).divisors.card *
        (Nat.log 2 (anchorDistance c z) + 1) ≤ K - K / 2 := by
      have hhalf : K ≤ 2 * (K - K / 2) := by omega
      nlinarith only [hcoef, hlength, hhalf]
    have hcount := coprimeInterval_log_density hm (Nat.div_le_self K 2) hlen
    have hcount' := hcount.trans (Nat.mul_le_mul_left
      (2 * ((Finset.Ioc (K / 2) K).filter (fun p => (anchorDistance c z).Coprime p)).card) hlog)
    have hhalf : K ≤ 2 * (K - K / 2) := by omega
    nlinarith only [hcount', hhalf]
  have hsum := Finset.sum_le_sum hrow
  have hcount := minimal_prefix_witnesses_count hd hPU hW
  have hbound := Nat.mul_le_mul_left (4 * (Nat.log 2 N + 1)) hcount
  simp only [Finset.sum_const, smul_eq_mul, ← Finset.mul_sum] at hsum
  omega

end
section
open Finset

theorem apSegment_mono_step {u v d e : ℕ} (hed : e ∣ d) :
    apSegment u v d ⊆ apSegment u v e := by
  intro x hx
  obtain ⟨hxI, hdx⟩ := Finset.mem_filter.mp hx
  exact Finset.mem_filter.mpr ⟨hxI, hed.trans hdx⟩

theorem exists_divisor_minimal_trace {S : Finset ℕ} {c p d : ℕ}
    (hd : 0 < d) (htrace : apSegment c p d ⊆ S) :
    ∃ e : ℕ, 0 < e ∧ e ∣ d ∧ apSegment c p e ⊆ S ∧
      ∀ f : ℕ, 0 < f → f ∣ e → apSegment c p f ⊆ S → e ≤ f := by
  let D := d.divisors.filter (fun e => apSegment c p e ⊆ S)
  have hdD : d ∈ D := Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨dvd_refl d, hd.ne'⟩, htrace⟩
  have hD : D.Nonempty := ⟨d, hdD⟩
  let e := D.min' hD
  have heD : e ∈ D := Finset.min'_mem D hD
  have hediv := Nat.mem_divisors.mp (Finset.mem_filter.mp heD).1
  refine ⟨e, Nat.pos_of_mem_divisors (Finset.mem_filter.mp heD).1, hediv.1,
    (Finset.mem_filter.mp heD).2, ?_⟩
  intro f hf hfe hfS
  exact Finset.min'_le D f (Finset.mem_filter.mpr
    ⟨Nat.mem_divisors.mpr ⟨hfe.trans hediv.1, hd.ne'⟩, hfS⟩)

theorem minimal_trace_witness_core {S : Finset ℕ} {c p d : ℕ}
    (hcp : c < p) (hd : 0 < d) (hddiv : d ∣ p - c)
    (htrace : apSegment c p d ⊆ S)
    (hmin : ∀ e : ℕ, 0 < e → e ∣ d → apSegment c p e ⊆ S → d ≤ e) :
    ∃ U : Finset ℕ, U ⊆ S ∧ (∃ l : ℕ∞, (U : Set ℕ).IsAPOfLength l) ∧
      apSegment c p d ⊆ U ∧
      ∀ z ∈ S, p ≤ z → z ∉ U → ∀ i : ℕ, 0 < i → c + i * d ∈ U →
        i.Coprime (anchorDistance c z) → IsWitnessPair S c {c + i * d, z} := by
  have hdlen : d ≤ p - c := Nat.le_of_dvd (by omega) hddiv
  have hcT : c ∈ apSegment c p d := Finset.mem_filter.mpr
    ⟨Finset.mem_Icc.mpr ⟨le_rfl, hcp.le⟩, by simp⟩
  have hvT : c + d ∈ apSegment c p d := Finset.mem_filter.mpr
    ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by simp⟩
  have hrep := apSegment_eq_natAP hcp.le hd
  have hTcon : ConsecutiveIn (apSegment c p d) c (c + d) :=
    hrep.symm ▸ natAP_consecutive_of_neighbor hd (hrep ▸ hcT) (hrep ▸ hvT)
  obtain ⟨U, hUS, hUAP, hUcon, hmax⟩ := fixedGap_core (by omega : c < c + d)
    (htrace hcT) (htrace hvT)
  have hTU : apSegment c p d ⊆ U := hmax _ htrace
    (Or.inr ⟨apSegment_isAP hcp.le hd, hTcon⟩)
  refine ⟨U, hUS, hUAP, hTU, ?_⟩
  intro z hz hpz hzU i hi hyU hcop
  let y := c + i * d
  have hcy : c < y := by dsimp [y]; nlinarith only [hi, hd]
  have hzc : z ≠ c := by omega
  have hyz : y ≠ z := fun heq => hzU (heq ▸ hyU)
  refine ⟨Finset.card_pair hyz, ?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_erase.mpr ⟨hcy.ne', hUS hyU⟩
    · exact Finset.mem_erase.mpr ⟨hzc, hz⟩
  · rintro ⟨A, hAS, ⟨l, hAAP⟩, hCA⟩
    have hcA : c ∈ A := hCA (by simp)
    have hyA : y ∈ A := hCA (by simp [y])
    have hzA : z ∈ A := hCA (by simp)
    have hcard : 2 ≤ A.card := by
      have hsub : {c, y} ⊆ A := by simp [Finset.insert_subset_iff, hcA, hyA]
      simpa [hcy.ne] using Finset.card_le_card hsub
    obtain ⟨a, e, he, hArep⟩ := nat_ap_eq_natAP hAAP hcard
    have heid : e ∣ i * d := by
      have hh := natAP_dvd_anchorDistance (hArep ▸ hcA) (hArep ▸ hyA)
      have hdist : anchorDistance c y = i * d := by dsimp [anchorDistance, y]; omega
      simpa only [hdist] using hh
    have hez : e ∣ anchorDistance c z := natAP_dvd_anchorDistance (hArep ▸ hcA) (hArep ▸ hzA)
    have hed : e ∣ d := ((hcop.of_dvd_right hez).symm).dvd_of_dvd_mul_left heid
    have hediv : e ∣ p - c := hed.trans hddiv
    have hTeA : apSegment c p e ⊆ A := by
      rw [apSegment_eq_natAP hcp.le he]
      have hlast : c + ((p - c) / e) * e ≤ z := by
        rw [Nat.div_mul_cancel hediv]
        omega
      exact (natAP_prefix_subset_of_endpoints he (hArep ▸ hcA) (hArep ▸ hzA) hlast).trans
        (by rw [← hArep])
    have hde : d ≤ e := hmin e he hed (hTeA.trans hAS)
    have hed' : e ≤ d := Nat.le_of_dvd hd hed
    have heq : e = d := by omega
    have hvAe : c + e ∈ A := hTeA (by simpa only [heq] using hvT)
    have hcon : ConsecutiveIn A c (c + d) := by
      have hh := natAP_consecutive_of_neighbor he (hArep ▸ hcA) (hArep ▸ hvAe)
      have hhA : ConsecutiveIn A c (c + e) := hArep.symm ▸ hh
      simpa only [heq] using hhA
    exact hzU (hmax A hAS (Or.inr ⟨⟨l, hAAP⟩, hcon⟩) hzA)

theorem coprime_index_recovers_divisor {D d e i j : ℕ}
    (hd : d ∣ D) (he : e ∣ D) (hi : i.Coprime D) (hj : j.Coprime D)
    (hcode : i * d = j * e) : d = e := by
  have hleft : Nat.gcd (i * d) D = d := by rw [hi.gcd_mul_left_cancel, Nat.gcd_eq_left hd]
  have hright : Nat.gcd (j * e) D = e := by rw [hj.gcd_mul_left_cancel, Nat.gcd_eq_left he]
  exact hleft.symm.trans ((congrArg (fun n => Nat.gcd n D) hcode).trans hright)

end
section
theorem quadratic_deficit {L w k : ℝ} (hL : 0 ≤ L) (hw : 0 ≤ w)
    (hk : k ≤ 5 / 3) :
    (L ^ 2 + w ^ 2) / 100 ≤ L ^ 2 / 2 + w ^ 2 / 4 - (k - 1) * L * w := by
  have hkw := mul_le_mul_of_nonneg_right hk (mul_nonneg hL hw)
  nlinarith [sq_nonneg (7 * L - 5 * w), sq_nonneg L, sq_nonneg w]

theorem retained_deficit {n q c r x s k : ℝ}
    (hq : 0 ≤ q) (hc : 0 ≤ c) (hx : 0 ≤ x) (hsr : s ≤ r)
    (hk0 : 0 ≤ k) (hk : k ≤ 5 / 3) (hn : n = q + c + r + x) :
    k * x * (q + c) + r * x + k * c * (r - s) + s * (q + c + r) - s ^ 2 / 2 ≤
      n ^ 2 / 2 - ((q + c) ^ 2 + x ^ 2) / 100 := by
  let L := q + c
  let w := x + r - s
  have hL : 0 ≤ L := add_nonneg hq hc
  have hw : 0 ≤ w := by dsimp [w]; linarith
  have hxw : x ≤ w := by dsimp [w]; linarith
  have hkw := quadratic_deficit hL hw hk
  have hmain :
      k * x * (q + c) + r * x + k * c * (r - s) + s * (q + c + r) - s ^ 2 / 2 ≤
        k * L * w + w ^ 2 / 4 + s * (L + w) + s ^ 2 / 2 := by
    have hprod := mul_nonneg (mul_nonneg hk0 hq) (sub_nonneg.mpr hsr)
    dsimp [L, w]
    nlinarith [sq_nonneg (x - (r - s))]
  have hidentity :
      n ^ 2 / 2 - (k * L * w + w ^ 2 / 4 + s * (L + w) + s ^ 2 / 2) =
        L ^ 2 / 2 + w ^ 2 / 4 - (k - 1) * L * w := by
    rw [hn]
    dsimp [L, w]
    ring
  have hsq : x ^ 2 ≤ w ^ 2 := sq_le_sq₀ hx hw |>.mpr hxw
  dsimp [L] at hidentity hmain hkw
  linarith

end
section
/-- The alternatives after the structural reduction, including possible reflection. -/
def ReducedFamilyStructure (N : ℕ) (G : Finset (Finset ℕ)) : Prop :=
  (∃ c : ℕ, ∀ S ∈ G, c ∈ S) ∨
  (∃ c L R : ℕ, c < L ∧ L ≤ R ∧ R ≤ N ∧
    256 * (L + N - R) * (Nat.log 2 N + 1) ≤ N ∧
    ∀ S ∈ G, c ∉ S → ∃ a b : ℕ,
      c < a ∧ a ≤ L ∧ R ≤ b ∧ b ≤ N ∧ S = Finset.Icc a b)

/-- The structural statement proved below by `structural_reduction`. -/
def StructuralReduction : Prop :=
  ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ F : Finset (Finset ℕ),
    Erdos272.IsArithInterSet N F → (N : ℝ)^2 / 2 ≤ (F.card : ℝ) →
    ∃ G : Finset (Finset ℕ), Erdos272.IsArithInterSet N G ∧
      F.card ≤ G.card + 2048 * N ∧ ReducedFamilyStructure N G

theorem reduced_family_card_le {N : ℕ} {G : Finset (Finset ℕ)}
    (hG : Erdos272.IsArithInterSet N G) (hstructure : ReducedFamilyStructure N G) :
    G.card ≤ N.choose 2 + 20003 * N := by
  rcases hstructure with ⟨c, hc⟩ | ⟨c, L, R, hcL, hLR, hRN, hN, hinterval⟩
  · have hh := common_point_card_le hG hc
    omega
  · exact long_core_family_card_le hcL hLR hRN hN hG hinterval

theorem finite_upper_bound_of_structural_reduction (hstructure : StructuralReduction) :
    FiniteUpperBound := by
  obtain ⟨N₀, hreduce⟩ := hstructure
  refine ⟨30000, N₀, ?_⟩
  intro N hN F hF
  have hNnonneg : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  by_cases hlarge : (N : ℝ)^2 / 2 ≤ (F.card : ℝ)
  · obtain ⟨G, hG, hFG, hstruct⟩ := hreduce N hN F hF hlarge
    have hcardG := reduced_family_card_le hG hstruct
    have hcardF : F.card ≤ N.choose 2 + 22051 * N := by omega
    have hreal : (F.card : ℝ) ≤ (N.choose 2 : ℝ) + 22051 * (N : ℝ) := by exact_mod_cast hcardF
    rw [Nat.cast_choose_two] at hreal
    nlinarith only [hreal, hNnonneg]
  · nlinarith only [hlarge, hNnonneg]

/-- Conditional on the explicit structural reduction; this is not an unconditional target proof. -/
theorem target_of_structural_reduction (hstructure : StructuralReduction) :
    fcTypeOfName% "Erdos272.erdos_272.variants.szabo_strong" :=
  target_of_finite_upper_bound (finite_upper_bound_of_structural_reduction hstructure)

end
/- Midpoint -/

/- The explicit coprime index from the third supplied proof. -/

section
theorem exists_coprime_near_half (m : ℕ) (hm : 6 ≤ m) :
    ∃ j : ℕ, 0 < j ∧ 2 * j ≤ m ∧ m ≤ 2 * j + 4 ∧ Nat.Coprime j m := by
  by_cases hodd : m % 2 = 1
  · refine ⟨m / 2, by omega, by omega, by omega, ?_⟩
    have heq : m = 2 * (m / 2) + 1 := by omega
    have hcop : Nat.Coprime (m / 2) (2 * (m / 2) + 1) := by simp
    simpa only [← heq] using hcop
  · have heq : m = 2 * (m / 2) := by omega
    by_cases heven : (m / 2) % 2 = 0
    · refine ⟨m / 2 - 1, by omega, by omega, by omega, ?_⟩
      have hcop : Nat.Coprime (m / 2 - 1) (m / 2) := by
        have hh : m / 2 - 1 + 1 = m / 2 := by omega
        rw [← hh]
        simp
      have hcop2 : Nat.Coprime (m / 2 - 1) 2 :=
        Nat.coprime_two_right.mpr (Nat.odd_iff.mpr (by omega))
      simpa only [← heq] using hcop2.mul_right hcop
    · refine ⟨m / 2 - 2, by omega, by omega, by omega, ?_⟩
      have hjodd : (m / 2 - 2) % 2 = 1 := by omega
      have hcop2 : Nat.Coprime (m / 2 - 2) 2 :=
        Nat.coprime_two_right.mpr (Nat.odd_iff.mpr hjodd)
      have hcop : Nat.Coprime (m / 2 - 2) (m / 2) := by
        have hh : m / 2 = (m / 2 - 2) + 2 := by omega
        have hp : Nat.Coprime (m / 2 - 2) ((m / 2 - 2) + 2) := by
          simpa only [Nat.coprime_self_add_right] using hcop2
        simpa only [← hh] using hp
      simpa only [← heq] using hcop2.mul_right hcop

end
/- LinearExterior -/

/- A midpoint argument removes the logarithmic factor from the exterior-witness lemma. -/

section
open Finset

theorem prefix_top_cover_half {S : Finset ℕ} {c d h R v : ℕ}
    (hd : 0 < d) (hh : 1 ≤ h)
    (hprefix : S.filter (fun x => x ≤ R) = natAP c d (h + 1))
    (hmin : ∀ x ∈ S, c ≤ x)
    (hwide : 3 * v + c ≤ 4 * R)
    (hcover : HasAPCover S {c, c + h * d, v}) :
    v + c ≤ 2 * (c + h * d) := by
  let z := c + h * d
  have hcz : c < z := by
    have hpos : 0 < h * d := Nat.mul_pos (by omega) hd
    dsimp [z]
    omega
  change v + c ≤ 2 * z
  by_contra hhalf
  obtain ⟨e, k, he, hk, hAS, hzA, hvA⟩ := hasAPCover_at_min hmin hcz hcover
  obtain ⟨i, hi, hzi⟩ := mem_natAP.mp hzA
  obtain ⟨j, hj, hvj⟩ := mem_natAP.mp hvA
  have hi1 : 1 ≤ i := by
    by_contra hlt
    have hi0 : i = 0 := by omega
    simp only [hi0, zero_mul, add_zero] at hzi
    omega
  have hij : i + 1 < j := by
    by_contra hlt
    have hmul := Nat.mul_le_mul_right e (by omega : j ≤ i + 1)
    have hew := Nat.mul_le_mul_right e hi1
    nlinarith only [hmul, hew, hzi, hvj, hhalf]
  have hnext : c + (i + 1) * e ∈ S :=
    hAS (mem_natAP.mpr ⟨i + 1, by omega, rfl⟩)
  have hnextR : R < c + (i + 1) * e := by
    by_contra hle
    have hbound := prefix_le_top hprefix hnext (by omega)
    change c + (i + 1) * e ≤ z at hbound
    nlinarith only [he, hbound, hzi]
  have hpred : c + (j - 1) * e ∈ S :=
    hAS (mem_natAP.mpr ⟨j - 1, by omega, rfl⟩)
  have hpredz : z < c + (j - 1) * e := by
    have hmul := Nat.mul_lt_mul_of_pos_right (by omega : i < j - 1) he
    omega
  have hpredR : R < c + (j - 1) * e := by
    by_contra hle
    have hbound := prefix_le_top hprefix hpred (by omega)
    change c + (j - 1) * e ≤ z at hbound
    omega
  have hnext_eq : c + (i + 1) * e = z + e := by nlinarith only [hzi]
  have hjsub : j - 1 + 1 = j := by omega
  have hpred_eq : c + (j - 1) * e + e = v := by
    calc
      c + (j - 1) * e + e = c + (j - 1 + 1) * e := by ring
      _ = v := by rw [hjsub]; exact hvj
  omega

theorem exists_coprime_in_prefix_core_linear {N c L R d h m : ℕ}
    (hcL : c < L) (hRN : R ≤ N) (hd : 0 < d) (hdL : d ≤ L)
    (hN : 16 * (L + N - R) ≤ N)
    (hRm : R < c + m * d)
    (hhalf : c + m * d + c ≤ 2 * (c + h * d)) :
    ∃ j : ℕ, L ≤ c + j * d ∧ j ≤ h ∧ Nat.Coprime j m := by
  have hRL : 16 * L ≤ R := by omega
  have hm6 : 6 ≤ m := by
    by_contra hlt
    have hmul := Nat.mul_le_mul_right d (by omega : m ≤ 5)
    omega
  obtain ⟨j, hjpos, hjm, hmj, hcop⟩ := exists_coprime_near_half m hm6
  have hjh : j ≤ h := by
    by_contra hlt
    have hmul := Nat.mul_lt_mul_of_pos_right (by omega : 2 * h < m) hd
    nlinarith only [hmul, hhalf]
  have hjL : L ≤ c + j * d := by
    have hmul := Nat.mul_le_mul_right d hmj
    nlinarith only [hmul, hRm, hRL, hdL, hcL]
  exact ⟨j, hjL, hjh, hcop⟩

theorem exterior_witness_contradiction_linear {N c L R : ℕ} {S : Finset ℕ}
    (hcL : c < L) (hLR : L ≤ R) (hRN : R ≤ N)
    (hN : 16 * (L + N - R) ≤ N)
    (hsub : S ⊆ Finset.Icc 1 N) (hcrooked : IsCrooked S) (hc : c ∈ S)
    (hcorner : ∀ P, IsWitnessPair S c P → InExteriorCorner c L R P)
    (hbetween : ∀ u v : ℕ, u < v → IsWitnessPair S c {u, v} →
      ∃ x ∈ S, u < x ∧ x < v) : False := by
  obtain ⟨d, h, hd, hdL, hh, hmin, hprefix, htopR, htail⟩ :=
    exterior_witness_prefix hcrooked hc hLR hcorner
  let z := c + h * d
  have hzS : z ∈ S := prefix_top_mem hprefix
  have hcz : c < z := by
    have hpos := Nat.mul_pos (by omega : 0 < h) hd
    dsimp [z]
    omega
  have hwide : 2 * L ≤ R + c := by omega
  have hzL : L ≤ z := prefix_reaches_core hd hh hprefix hmin htopR htail hwide hbetween
  have htopCover : ∀ v ∈ S, R < v → HasAPCover S {c, z, v} := by
    intro v hvS hRv
    have hzv : z < v := by dsimp [z]; omega
    apply hasAPCover_of_not_witness (by simp [hzv.ne])
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact Finset.mem_erase.mpr ⟨hcz.ne', hzS⟩
      · exact Finset.mem_erase.mpr ⟨by omega, hvS⟩
    · intro hW
      have hbad := (exterior_corner_pair_iff hLR hzv).mp (hcorner {z, v} hW)
      omega
  have hgrid : ∀ x ∈ S, d ∣ x - c := by
    intro x hx
    by_cases hxR : x ≤ R
    · exact prefix_dvd_offset hprefix hx hxR
    · exact (prefix_top_cover_analysis hd hh hprefix hmin htopR (by omega)
        (htopCover x hx (by omega))).1
  have hSnonempty : S.Nonempty := ⟨c, hc⟩
  let v := S.max' hSnonempty
  have hvS : v ∈ S := Finset.max'_mem S hSnonempty
  have hmax : ∀ x ∈ S, x ≤ v := fun x hx => Finset.le_max' S x hx
  have hRv : R < v := by
    obtain ⟨w, hwS, hRw⟩ := htail
    have hwv := hmax w hwS
    omega
  have hcv : c ≤ v := hmin v hvS
  have hvN : v ≤ N := (Finset.mem_Icc.mp (hsub hvS)).2
  obtain ⟨m, hm⟩ := hgrid v hvS
  have hvm : v = c + m * d := by
    have hvsub := Nat.sub_add_cancel hcv
    nlinarith only [hm, hvsub]
  have hwideTail : 3 * v + c ≤ 4 * R := by omega
  have hhalf : v + c ≤ 2 * (c + h * d) :=
    prefix_top_cover_half hd hh hprefix hmin hwideTail (htopCover v hvS hRv)
  obtain ⟨j, hjL, hjh, hjcop⟩ := exists_coprime_in_prefix_core_linear hcL hRN hd
    (by omega : d ≤ L) hN (by simpa only [hvm] using hRv)
    (by simpa only [hvm] using hhalf)
  let u := c + j * d
  have huR : u ≤ R := by
    have hmul := Nat.mul_le_mul_right d hjh
    dsimp [u]
    omega
  have huS : u ∈ S := by
    have hu : u ∈ S.filter (fun x => x ≤ R) := by
      rw [hprefix]
      exact mem_natAP.mpr ⟨j, by omega, rfl⟩
    exact (Finset.mem_filter.mp hu).1
  have hcu : c < u := by dsimp [u]; omega
  have huv : u < v := by omega
  have huCover : HasAPCover S {c, u, v} := by
    apply hasAPCover_of_not_witness (by simp [huv.ne])
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact Finset.mem_erase.mpr ⟨hcu.ne', huS⟩
      · exact Finset.mem_erase.mpr ⟨by omega, hvS⟩
    · intro hW
      have hbad := (exterior_corner_pair_iff hLR huv).mp (hcorner {u, v} hW)
      dsimp [u] at hbad
      omega
  obtain ⟨e, k, he, hk, hAS, huA, hvA⟩ := hasAPCover_at_min hmin hcu huCover
  have hde : d ∣ e := prefix_step_divides_cover_step hprefix he hAS hcu huA huR
  obtain ⟨i, hi, hui⟩ := mem_natAP.mp huA
  obtain ⟨i', hi', hvi'⟩ := mem_natAP.mp hvA
  have hejd : e ∣ j * d := by
    refine ⟨i, ?_⟩
    dsimp [u] at hui
    nlinarith only [hui]
  have hemd : e ∣ m * d := by
    refine ⟨i', ?_⟩
    rw [hvm] at hvi'
    nlinarith only [hvi']
  have hed : e ∣ d := by
    have hdiv := Nat.dvd_gcd hejd hemd
    have hgcd : (j * d).gcd (m * d) = d := by
      rw [Nat.gcd_mul_right, hjcop.gcd_eq_one, Nat.one_mul]
    simpa only [hgcd] using hdiv
  have hedEq : e = d := Nat.dvd_antisymm hed hde
  have hvA' : v ∈ natAP c d k := by simpa only [hedEq] using hvA
  have hAS' : natAP c d k ⊆ S := by simpa only [hedEq] using hAS
  have hSA : S ⊆ natAP c d k := by
    obtain ⟨b, hb, hvb⟩ := mem_natAP.mp hvA'
    intro x hx
    obtain ⟨a, ha⟩ := hgrid x hx
    have hcx : c ≤ x := hmin x hx
    have hxa : x = c + a * d := by
      have hsubx := Nat.sub_add_cancel hcx
      nlinarith only [hsubx, ha]
    have hxab : a ≤ b := by
      have hxv := hmax x hx
      by_contra hab
      have hmul := Nat.mul_lt_mul_of_pos_right (by omega : b < a) hd
      omega
    exact mem_natAP.mpr ⟨a, lt_of_le_of_lt hxab hb, hxa.symm⟩
  have hS_eq : S = natAP c d k := Finset.Subset.antisymm hSA hAS'
  exact hcrooked ⟨k, hS_eq.symm ▸ natAP_isAP hd⟩

theorem exists_witness_outside_exterior_pairs_linear {N c L R : ℕ}
    {S : Finset ℕ} {W : Finset (Finset ℕ)}
    (hcL : c < L) (hLR : L ≤ R) (hRN : R ≤ N)
    (hN : 16 * (L + N - R) ≤ N)
    (hsub : S ⊆ Finset.Icc 1 N) (hcrooked : IsCrooked S) (hc : c ∈ S)
    (hW : ∀ P ∈ W, InExteriorCorner c L R P)
    (hbetween : ∀ u v : ℕ, u < v → ({u, v} : Finset ℕ) ∈ W →
      ∃ x ∈ S, u < x ∧ x < v) :
    ∃ P : Finset ℕ, IsWitnessPair S c P ∧ P ∉ W := by
  by_contra hnone
  have hinW : ∀ P, IsWitnessPair S c P → P ∈ W := by
    intro P hP
    by_contra hPW
    exact hnone ⟨P, hP, hPW⟩
  exact exterior_witness_contradiction_linear hcL hLR hRN hN hsub hcrooked hc
    (fun P hP => hW P (hinW P hP))
    (fun u v huv hP => hbetween u v huv (hinW {u, v} hP))

end
/- ProgressionCount -/

/- Counting intersecting arithmetic progressions by their common difference. -/

section
open Finset

theorem start_mem_same_step_of_inter {a b d k m x : ℕ}
    (hd : 0 < d) (hba : b ≤ a)
    (hx : x ∈ natAP a d k) (hx' : x ∈ natAP b d m) :
    a ∈ natAP b d m := by
  obtain ⟨i, hi, hxi⟩ := mem_natAP.mp hx
  obtain ⟨j, hj, hxj⟩ := mem_natAP.mp hx'
  have hij : i ≤ j := by
    by_contra hlt
    have hmul := Nat.mul_lt_mul_of_pos_right (by omega : j < i) hd
    omega
  have hsub : i + (j - i) = j := Nat.add_sub_of_le hij
  refine mem_natAP.mpr ⟨j - i, by omega, ?_⟩
  nlinarith only [hxi, hxj, hsub]

theorem same_step_common_point {N d : ℕ} {F : Finset (Finset ℕ)}
    (hd : 0 < d) (hF : Erdos272.IsArithInterSet N F) (hne : F.Nonempty)
    (hcard : ∀ S ∈ F, 0 < S.card)
    (hrep : ∀ S ∈ F, ∃ a : ℕ, S = natAP a d S.card) :
    ∃ c : ℕ, c ∈ Finset.Icc 1 N ∧ ∀ S ∈ F, c ∈ S := by
  classical
  let X := {S // S ∈ F}
  have hex : ∀ S : X, ∃ a : ℕ, S.val = natAP a d S.val.card :=
    fun S => hrep S.val S.property
  choose a ha using hex
  have hX : (Finset.univ : Finset X).Nonempty := by
    obtain ⟨S, hS⟩ := hne
    exact ⟨⟨S, hS⟩, Finset.mem_univ _⟩
  obtain ⟨S₀, hS₀, hmax⟩ := Finset.exists_max_image Finset.univ a hX
  have hc₀ : a S₀ ∈ S₀.val := by
    rw [ha S₀]
    exact mem_natAP.mpr ⟨0, hcard S₀.val S₀.property, by simp⟩
  refine ⟨a S₀, (Finset.mem_powerset.mp (hF.1 S₀.property)) hc₀, ?_⟩
  intro S hS
  let T : X := ⟨S, hS⟩
  obtain ⟨x, hx⟩ := arithInter_inter_nonempty hF S₀.property hS ⟨a S₀, hc₀⟩
  obtain ⟨hx₀, hxS⟩ := Finset.mem_inter.mp hx
  rw [ha S₀] at hx₀
  have hxT : x ∈ natAP (a T) d T.val.card := by simpa only [← ha T] using hxS
  have hh := start_mem_same_step_of_inter hd (hmax T (Finset.mem_univ _)) hx₀ hxT
  simpa only [← ha T] using hh

theorem centered_model_sharp_bounds {N c d : ℕ} {p : ProgressionCell} {S : Finset ℕ}
    (hd : 0 < d) (hmodel : IsCenteredModel c d p S) (hsub : S ⊆ Finset.Icc 1 N) :
    p.val.1 ≤ (c - 1) / d ∧ p.val.2 ≤ (N - c) / d := by
  have hl := centered_point_mem hmodel
    (Finset.mem_Icc.mpr ⟨le_rfl, (by omega : -(p.val.1 : ℤ) ≤ (p.val.2 : ℤ))⟩)
  have hr := centered_point_mem hmodel
    (Finset.mem_Icc.mpr ⟨(by omega : -(p.val.1 : ℤ) ≤ (p.val.2 : ℤ)), le_rfl⟩)
  have hlI := Finset.mem_Icc.mp (hsub hl.1)
  have hrI := Finset.mem_Icc.mp (hsub hr.1)
  have hleftI : (p.val.1 : ℤ) * (d : ℤ) + 1 ≤ c := by nlinarith only [hl.2, hlI.1]
  have hrightI : (p.val.2 : ℤ) * (d : ℤ) + c ≤ N := by nlinarith only [hr.2, hrI.2]
  have hleft : p.val.1 * d + 1 ≤ c := by exact_mod_cast hleftI
  have hright : p.val.2 * d + c ≤ N := by exact_mod_cast hrightI
  exact ⟨(Nat.le_div_iff_mul_le hd).mpr (by omega),
    (Nat.le_div_iff_mul_le hd).mpr (by omega)⟩

theorem centered_family_card_le_rectangle {N c d : ℕ} {F : Finset (Finset ℕ)}
    (hd : 0 < d) (hsub : ∀ S ∈ F, S ⊆ Finset.Icc 1 N)
    (hmodel : ∀ S ∈ F, ∃ p : ProgressionCell, IsCenteredModel c d p S) :
    F.card ≤ ((c - 1) / d + 1) * ((N - c) / d + 1) := by
  classical
  let X := {S // S ∈ F}
  have hex : ∀ S : X, ∃ p : ProgressionCell, IsCenteredModel c d p S.val :=
    fun S => hmodel S.val S.property
  choose p hp using hex
  let f : X → ℕ × ℕ := fun S => (p S).val
  have hinj : Function.Injective f := by
    intro S T hST
    have hpST : p S = p T := Subtype.ext hST
    apply Subtype.ext
    exact centered_model_determines_set (hp S) (by simpa only [hpST] using hp T)
  have hmaps : Set.MapsTo f ((Finset.univ : Finset X) : Set X)
      (((Finset.range ((c - 1) / d + 1)).product
        (Finset.range ((N - c) / d + 1))) : Set (ℕ × ℕ)) := by
    intro S hS
    have hb := centered_model_sharp_bounds hd (hp S) (hsub S.val S.property)
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by dsimp [f]; omega),
      Finset.mem_range.mpr (by dsimp [f]; omega)⟩
  simpa [X] using Finset.card_le_card_of_injOn f hmaps hinj.injOn

theorem same_step_family_card_le {N d : ℕ} {F : Finset (Finset ℕ)}
    (hd : 0 < d) (hF : Erdos272.IsArithInterSet N F)
    (hcard : ∀ S ∈ F, 4 ≤ S.card)
    (hrep : ∀ S ∈ F, ∃ a : ℕ, S = natAP a d S.card) :
    (F.card : ℝ) ≤ (N : ℝ) ^ 2 / (4 * (d : ℝ) ^ 2) + (N : ℝ) / d + 1 := by
  classical
  by_cases hne : F.Nonempty
  · obtain ⟨c, hcN, hc⟩ := same_step_common_point hd hF hne (fun S hS => by
      have hh := hcard S hS; omega) hrep
    have hmodels : ∀ S ∈ F, ∃ p : ProgressionCell, IsCenteredModel c d p S := by
      intro S hS
      obtain ⟨a, heq⟩ := hrep S hS
      obtain ⟨i, hi, hci⟩ := mem_natAP.mp (heq ▸ hc S hS)
      refine ⟨⟨(i, S.card - 1 - i), by have hh := hcard S hS; omega⟩, ?_⟩
      change S.image (fun x : ℕ => (x : ℤ)) = _
      have hcast := congrArg (fun T : Finset ℕ => T.image (fun x : ℕ => (x : ℤ))) heq
      exact hcast.trans (by simpa only [hci] using natAP_cast_eq_affine_interval a d S.card i hi)
    have hbound := centered_family_card_le_rectangle hd
      (fun S hS => Finset.mem_powerset.mp (hF.1 hS)) hmodels
    let C := (c - 1) / d
    let M := (N - c) / d
    have hCM : (C + M) * d ≤ N := by
      have hC := Nat.div_mul_le_self (c - 1) d
      have hM := Nat.div_mul_le_self (N - c) d
      obtain ⟨hc1, hcN'⟩ := Finset.mem_Icc.mp hcN
      dsimp [C, M]
      nlinarith only [hC, hM, Nat.sub_add_cancel hc1, Nat.sub_add_cancel hcN']
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd
    have hsum : (C : ℝ) + M ≤ (N : ℝ) / d := by
      apply (le_div_iff₀ hdR).mpr
      exact_mod_cast hCM
    have hboundR : (F.card : ℝ) ≤ ((C : ℝ) + 1) * ((M : ℝ) + 1) := by
      exact_mod_cast hbound
    have hsq : ((C : ℝ) + M + 2) ^ 2 ≤ ((N : ℝ) / d + 2) ^ 2 :=
      (sq_le_sq₀ (by positivity) (by positivity)).mpr (by linarith only [hsum])
    have hid : ((N : ℝ) / d + 2) ^ 2 / 4 =
        (N : ℝ) ^ 2 / (4 * (d : ℝ) ^ 2) + (N : ℝ) / d + 1 := by
      field_simp
      ring
    nlinarith only [hboundR, hsq, hid, sq_nonneg ((C : ℝ) - M)]
  · have hF0 : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    rw [hF0]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity

theorem reciprocal_square_sum_le (N : ℕ) :
    (∑ i ∈ Finset.Icc 1 N, ((i : ℝ) ^ 2)⁻¹) ≤ 5 / 3 := by
  have hsmall : (∑ i ∈ Finset.Icc (1 : ℕ) 5, ((i : ℝ) ^ 2)⁻¹) = 5269 / 3600 := by
    norm_num [Finset.sum_Icc_succ_top]
  by_cases hN : 5 ≤ N
  · have hsplit : Finset.Icc 1 N = Finset.Icc 1 5 ∪ Finset.Ioc 5 N := by
      ext i
      simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
      omega
    have hdisj : Disjoint (Finset.Icc 1 5) (Finset.Ioc 5 N) := by
      apply Finset.disjoint_left.mpr
      intro i hi hi'
      simp only [Finset.mem_Icc, Finset.mem_Ioc] at hi hi'
      omega
    rw [hsplit, Finset.sum_union hdisj, hsmall]
    have htail := sum_Ioc_inv_sq_le_sub (α := ℝ) (k := 5) (by decide) hN
    have hpos : 0 ≤ (N : ℝ)⁻¹ := by positivity
    norm_num only at htail
    linarith only [htail, hpos]
  · calc
      _ ≤ ∑ i ∈ Finset.Icc (1 : ℕ) 5, ((i : ℝ) ^ 2)⁻¹ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro i hi
          obtain ⟨hi1, hiN⟩ := Finset.mem_Icc.mp hi
          exact Finset.mem_Icc.mpr ⟨hi1, by omega⟩
        · intro i hi hi'
          positivity
      _ ≤ 5 / 3 := by rw [hsmall]; norm_num

theorem progression_family_large_card_le {N : ℕ} {F : Finset (Finset ℕ)}
    (hF : Erdos272.IsArithInterSet N F)
    (hAP : ∀ S ∈ F, ∃ l : ℕ∞, (S : Set ℕ).IsAPOfLength l)
    (hcard : ∀ S ∈ F, 4 ≤ S.card) :
    (F.card : ℝ) ≤ 5 * (N : ℝ) ^ 2 / 12 + (N : ℝ) * reciprocalSum N + N := by
  classical
  have hparam : ∀ S : Finset ℕ, ∃ a d : ℕ,
      S ∈ F → 0 < d ∧ d ≤ N ∧ S = natAP a d S.card := by
    intro S
    by_cases hS : S ∈ F
    · obtain ⟨l, hl⟩ := hAP S hS
      obtain ⟨a, d, hd, hrep⟩ := nat_ap_eq_natAP hl (by have hh := hcard S hS; omega)
      have hstep : a + d ∈ S := by
        rw [hrep]
        exact mem_natAP.mpr ⟨1, by have hh := hcard S hS; omega, by simp⟩
      have hdN : d ≤ N := by
        have hh := (Finset.mem_Icc.mp ((Finset.mem_powerset.mp (hF.1 hS)) hstep)).2
        omega
      exact ⟨a, d, fun _ => ⟨hd, hdN, hrep⟩⟩
    · exact ⟨0, 1, fun h => False.elim (hS h)⟩
  choose a d hspec using hparam
  have hmaps : Set.MapsTo d (F : Set (Finset ℕ)) (Finset.Icc 1 N : Set ℕ) := by
    intro S hS
    exact Finset.mem_Icc.mpr ⟨(hspec S hS).1, (hspec S hS).2.1⟩
  have hsumCard : (F.card : ℝ) =
      ∑ k ∈ Finset.Icc 1 N, ((F.filter (fun S => d S = k)).card : ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_fiberwise hmaps
  have hbound : ∀ k ∈ Finset.Icc 1 N,
      ((F.filter (fun S => d S = k)).card : ℝ) ≤
        (N : ℝ) ^ 2 / (4 * (k : ℝ) ^ 2) + (N : ℝ) / k + 1 := by
    intro k hk
    apply same_step_family_card_le (Finset.mem_Icc.mp hk).1
    · exact ⟨fun S hS => hF.1 (Finset.mem_filter.mp hS).1,
        fun S hS T hT hST => hF.2 (Finset.mem_filter.mp hS).1 (Finset.mem_filter.mp hT).1 hST⟩
    · intro S hS
      exact hcard S (Finset.mem_filter.mp hS).1
    · intro S hS
      obtain ⟨hSF, hdk⟩ := Finset.mem_filter.mp hS
      exact ⟨a S, by simpa only [hdk] using (hspec S hSF).2.2⟩
  calc
    (F.card : ℝ) ≤ ∑ k ∈ Finset.Icc 1 N,
        ((N : ℝ) ^ 2 / (4 * (k : ℝ) ^ 2) + (N : ℝ) / k + 1) := by
      rw [hsumCard]
      exact Finset.sum_le_sum hbound
    _ = (N : ℝ) ^ 2 / 4 * (∑ k ∈ Finset.Icc 1 N, ((k : ℝ) ^ 2)⁻¹) +
        (N : ℝ) * reciprocalSum N + N := by
      calc
        _ = ∑ k ∈ Finset.Icc 1 N,
            ((N : ℝ) ^ 2 / 4 * ((k : ℝ) ^ 2)⁻¹ + (N : ℝ) * (k : ℝ)⁻¹ + 1) := by
          apply Finset.sum_congr rfl
          intro k hk
          simp only [div_eq_mul_inv, mul_inv_rev]
          ring
        _ = _ := by simp [reciprocalSum, Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ 5 * (N : ℝ) ^ 2 / 12 + (N : ℝ) * reciprocalSum N + N := by
      have hh := mul_le_mul_of_nonneg_left (reciprocal_square_sum_le N)
        (by positivity : 0 ≤ (N : ℝ) ^ 2 / 4)
      nlinarith only [hh]

theorem progression_family_large_card_le_log {N : ℕ} {F : Finset (Finset ℕ)}
    (hF : Erdos272.IsArithInterSet N F)
    (hAP : ∀ S ∈ F, ∃ l : ℕ∞, (S : Set ℕ).IsAPOfLength l)
    (hcard : ∀ S ∈ F, 4 ≤ S.card) :
    (F.card : ℝ) ≤ 5 * (N : ℝ) ^ 2 / 12 + (N : ℝ) * Real.log N + 2 * N := by
  have h := progression_family_large_card_le hF hAP hcard
  have hlog := mul_le_mul_of_nonneg_left (reciprocalSum_le_log N) (Nat.cast_nonneg N)
  nlinarith only [h, hlog]

end
/- SmallProgressionCount -/

/- Small progression members contribute only a linear error to the progression count. -/

section
open Finset

theorem admissible_subfamily {N : ℕ} {F G : Finset (Finset ℕ)}
    (hF : Erdos272.IsArithInterSet N F) (hGF : G ⊆ F) :
    Erdos272.IsArithInterSet N G :=
  ⟨fun _S hS => hF.1 (hGF hS), fun _S hS _T hT hST => hF.2 (hGF hS) (hGF hT) hST⟩

theorem short_progressions_rooted_card_le {N c : ℕ} {F : Finset (Finset ℕ)}
    (hsub : ∀ S ∈ F, S ⊆ Finset.Icc 1 N)
    (hAP : ∀ S ∈ F, ∃ l : ℕ∞, (S : Set ℕ).IsAPOfLength l)
    (hcard : ∀ S ∈ F, 2 ≤ S.card ∧ S.card ≤ 3)
    (hc : ∀ S ∈ F, c ∈ S) : F.card ≤ 6 * N := by
  classical
  let X := {S // S ∈ F}
  have hparam : ∀ S : X, ∃ d i : ℕ,
      0 < d ∧ d ≤ N ∧ i < S.val.card ∧
      S.val = natAP (c - i * d) d S.val.card := by
    intro S
    obtain ⟨l, hl⟩ := hAP S.val S.property
    obtain ⟨a, d, hd, hrep⟩ := nat_ap_eq_natAP hl (hcard S.val S.property).1
    obtain ⟨i, hi, hci⟩ := mem_natAP.mp (hrep ▸ hc S.val S.property)
    have ha : a = c - i * d := by omega
    have hstep : a + d ∈ S.val := by
      rw [hrep]
      exact mem_natAP.mpr ⟨1, (hcard S.val S.property).1, by simp⟩
    have hdN : d ≤ N := by
      have hh := (Finset.mem_Icc.mp (hsub S.val S.property hstep)).2
      omega
    exact ⟨d, i, hd, hdN, hi, by simpa only [ha] using hrep⟩
  choose d i hd hdN hi hrep using hparam
  let f : X → ℕ × ℕ × ℕ := fun S => (S.val.card, i S, d S)
  have hinj : Function.Injective f := by
    intro S T hST
    have hk : S.val.card = T.val.card := congrArg Prod.fst hST
    have hiST : i S = i T := congrArg (fun q : ℕ × ℕ × ℕ => q.2.1) hST
    have hdST : d S = d T := congrArg (fun q : ℕ × ℕ × ℕ => q.2.2) hST
    apply Subtype.ext
    rw [hrep S, hrep T, hk, hiST, hdST]
  have hmaps : Set.MapsTo f ((Finset.univ : Finset X) : Set X)
      (((Finset.Icc 2 3).product ((Finset.range 3).product (Finset.Icc 1 N))) :
        Set (ℕ × ℕ × ℕ)) := by
    intro S hS
    have hsize := hcard S.val S.property
    dsimp only [f]
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr hsize,
      Finset.mem_product.mpr ⟨Finset.mem_range.mpr (show i S < 3 by have hh := hi S; omega),
        Finset.mem_Icc.mpr ⟨hd S, hdN S⟩⟩⟩
  have hh := Finset.card_le_card_of_injOn f hmaps hinj.injOn
  norm_num [X, Finset.card_product] at hh
  omega

theorem singleton_of_member_card_le_one {S : Finset ℕ} {c : ℕ}
    (hc : c ∈ S) (hcard : S.card ≤ 1) : S = {c} := by
  apply Finset.Subset.antisymm
  · intro x hx
    exact Finset.mem_singleton.mpr (Finset.card_le_one.mp hcard x hx c hc)
  · simpa only [Finset.singleton_subset_iff] using hc

theorem small_progressions_rooted_card_le {N c : ℕ} {F : Finset (Finset ℕ)}
    (hsub : ∀ S ∈ F, S ⊆ Finset.Icc 1 N)
    (hAP : ∀ S ∈ F, ∃ l : ℕ∞, (S : Set ℕ).IsAPOfLength l)
    (hcard : ∀ S ∈ F, S.card ≤ 3)
    (hc : ∀ S ∈ F, c ∈ S) : F.card ≤ 6 * N + 1 := by
  classical
  have hlarge : (F.filter (fun S => 2 ≤ S.card)).card ≤ 6 * N := by
    apply short_progressions_rooted_card_le
    · intro S hS
      exact hsub S (Finset.mem_filter.mp hS).1
    · intro S hS
      exact hAP S (Finset.mem_filter.mp hS).1
    · intro S hS
      obtain ⟨hSF, hsize⟩ := Finset.mem_filter.mp hS
      exact ⟨hsize, hcard S hSF⟩
    · intro S hS
      exact hc S (Finset.mem_filter.mp hS).1
  have hsmall : (F.filter (fun S => ¬2 ≤ S.card)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro S hS T hT
    obtain ⟨hSF, hsizeS⟩ := Finset.mem_filter.mp hS
    obtain ⟨hTF, hsizeT⟩ := Finset.mem_filter.mp hT
    rw [singleton_of_member_card_le_one (hc S hSF) (by omega),
      singleton_of_member_card_le_one (hc T hTF) (by omega)]
  have hpart := Finset.card_filter_add_card_filter_not (s := F) (fun S => 2 ≤ S.card)
  omega

theorem progression_family_small_card_le {N : ℕ} {F : Finset (Finset ℕ)}
    (hF : Erdos272.IsArithInterSet N F)
    (hAP : ∀ S ∈ F, ∃ l : ℕ∞, (S : Set ℕ).IsAPOfLength l)
    (hcard : ∀ S ∈ F, S.card ≤ 3) : F.card ≤ 18 * N + 3 := by
  classical
  by_cases hne : ∃ S ∈ F, S.Nonempty
  · obtain ⟨S₀, hS₀, hne₀⟩ := hne
    let D (c : ℕ) := F.filter (fun S => c ∈ S)
    have hcover : F ⊆ S₀.biUnion D := by
      intro S hS
      obtain ⟨c, hc⟩ := arithInter_inter_nonempty hF hS₀ hS hne₀
      obtain ⟨hc₀, hcS⟩ := Finset.mem_inter.mp hc
      exact Finset.mem_biUnion.mpr ⟨c, hc₀, Finset.mem_filter.mpr ⟨hS, hcS⟩⟩
    have hD : ∀ c ∈ S₀, (D c).card ≤ 6 * N + 1 := by
      intro c hc
      apply small_progressions_rooted_card_le
      · intro S hS
        exact Finset.mem_powerset.mp (hF.1 (Finset.mem_filter.mp hS).1)
      · intro S hS
        exact hAP S (Finset.mem_filter.mp hS).1
      · intro S hS
        exact hcard S (Finset.mem_filter.mp hS).1
      · intro S hS
        exact (Finset.mem_filter.mp hS).2
    calc
      F.card ≤ (S₀.biUnion D).card := Finset.card_le_card hcover
      _ ≤ ∑ c ∈ S₀, (D c).card := Finset.card_biUnion_le
      _ ≤ ∑ c ∈ S₀, (6 * N + 1) := Finset.sum_le_sum hD
      _ = S₀.card * (6 * N + 1) := by simp
      _ ≤ 18 * N + 3 := by
        have hh := Nat.mul_le_mul_right (6 * N + 1) (hcard S₀ hS₀)
        omega
  · have hsmall : F.card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro S hS T hT
      have hS0 : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp (fun hh => hne ⟨S, hS, hh⟩)
      have hT0 : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp (fun hh => hne ⟨T, hT, hh⟩)
      rw [hS0, hT0]
    omega

theorem progression_family_card_le {N : ℕ} {F : Finset (Finset ℕ)}
    (hF : Erdos272.IsArithInterSet N F)
    (hAP : ∀ S ∈ F, ∃ l : ℕ∞, (S : Set ℕ).IsAPOfLength l) :
    (F.card : ℝ) ≤ 5 * (N : ℝ) ^ 2 / 12 + (N : ℝ) * Real.log N + 20 * N + 3 := by
  classical
  have hbig : ((F.filter (fun S => 4 ≤ S.card)).card : ℝ) ≤
      5 * (N : ℝ) ^ 2 / 12 + (N : ℝ) * Real.log N + 2 * N := by
    apply progression_family_large_card_le_log
    · exact admissible_subfamily hF (Finset.filter_subset _ _)
    · intro S hS
      exact hAP S (Finset.mem_filter.mp hS).1
    · intro S hS
      exact (Finset.mem_filter.mp hS).2
  have hsmall : (F.filter (fun S => ¬4 ≤ S.card)).card ≤ 18 * N + 3 := by
    apply progression_family_small_card_le
    · exact admissible_subfamily hF (Finset.filter_subset _ _)
    · intro S hS
      exact hAP S (Finset.mem_filter.mp hS).1
    · intro S hS
      have hh := (Finset.mem_filter.mp hS).2
      omega
  have hpart : ((F.filter (fun S => 4 ≤ S.card)).card : ℝ) +
      ((F.filter (fun S => ¬4 ≤ S.card)).card : ℝ) = F.card := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := F) (fun S => 4 ≤ S.card)
  have hsmallR : ((F.filter (fun S => ¬4 ≤ S.card)).card : ℝ) ≤ 18 * (N : ℝ) + 3 := by
    exact_mod_cast hsmall
  linarith only [hbig, hsmallR, hpart]

end
/- ProgressionAsymptotic -/

/- Uniform asymptotic consequences of the progression-family count. -/

section
open Finset Filter

noncomputable def crookedMembers (F : Finset (Finset ℕ)) : Finset (Finset ℕ) := by
  classical
  exact F.filter IsCrooked

theorem eventually_progression_family_quadratic_gap :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ F : Finset (Finset ℕ),
      Erdos272.IsArithInterSet N F →
      (∀ S ∈ F, ∃ l : ℕ∞, (S : Set ℕ).IsAPOfLength l) →
      (F.card : ℝ) ≤ 17 / 40 * (N : ℝ) ^ 2 := by
  have hlog := Real.isLittleO_log_id_atTop.bound (by norm_num : (0 : ℝ) < 1 / 240)
  have hnat : ∀ᶠ N : ℕ in atTop, ‖Real.log (N : ℝ)‖ ≤ (1 / 240 : ℝ) * ‖(N : ℝ)‖ :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop).eventually hlog
  filter_upwards [hnat, Filter.eventually_ge_atTop 10000] with N hlogN hN F hF hAP
  have hcount := progression_family_card_le hF hAP
  have hNR : (10000 : ℝ) ≤ N := by exact_mod_cast hN
  have hnonneg : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hln : Real.log (N : ℝ) ≤ (1 / 240 : ℝ) * N := by
    simp only [Real.norm_eq_abs, abs_of_nonneg hnonneg] at hlogN
    exact (le_abs_self _).trans hlogN
  have hlnmul := mul_le_mul_of_nonneg_left hln hnonneg
  have hNsq := mul_le_mul_of_nonneg_left hNR hnonneg
  nlinarith only [hcount, hlnmul, hNsq, hNR]

theorem eventually_many_crooked_members :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ F : Finset (Finset ℕ),
      Erdos272.IsArithInterSet N F → (N : ℝ) ^ 2 / 2 ≤ (F.card : ℝ) →
      3 / 40 * (N : ℝ) ^ 2 ≤ ((crookedMembers F).card : ℝ) := by
  classical
  filter_upwards [eventually_progression_family_quadratic_gap] with N hN F hF hsize
  have hAP : ∀ S ∈ F.filter (fun S => ¬IsCrooked S),
      ∃ l : ℕ∞, (S : Set ℕ).IsAPOfLength l := by
    intro S hS
    simpa only [IsCrooked, not_not] using (Finset.mem_filter.mp hS).2
  have hcount := hN _ (admissible_subfamily hF (Finset.filter_subset _ _)) hAP
  have hpart : ((F.filter IsCrooked).card : ℝ) +
      ((F.filter (fun S => ¬IsCrooked S)).card : ℝ) = F.card := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := F) IsCrooked
  change 3 / 40 * (N : ℝ) ^ 2 ≤ ((F.filter IsCrooked).card : ℝ)
  linarith only [hcount, hpart, hsize]

noncomputable def sparseCrookedMembers (N : ℕ) (F : Finset (Finset ℕ)) :
    Finset (Finset ℕ) := by
  classical
  exact (crookedMembers F).filter (fun S => 16 * S.card ≤ N)

theorem eventually_many_sparse_crooked_members :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ F : Finset (Finset ℕ),
      Erdos272.IsArithInterSet N F → (N : ℝ) ^ 2 / 2 ≤ (F.card : ℝ) →
      (N : ℝ) ^ 2 / 14 ≤ ((sparseCrookedMembers N F).card : ℝ) := by
  classical
  filter_upwards [eventually_many_crooked_members, Filter.eventually_ge_atTop 1000000]
    with N hN hlarge F hF hsize
  let C := crookedMembers F
  let D := C.filter (fun S => ¬16 * S.card ≤ N)
  have hcount : 3 / 40 * (N : ℝ) ^ 2 ≤ (C.card : ℝ) := hN F hF hsize
  have hDF : D ⊆ F := by
    intro S hS
    have hSC : S ∈ C := (Finset.mem_filter.mp hS).1
    exact (Finset.mem_filter.mp hSC).1
  have hdense : D.card ≤ 2048 * N := by
    apply dense_crooked_card_le (by omega) (admissible_subfamily hF hDF)
    · intro S hS
      have hSC : S ∈ C := (Finset.mem_filter.mp hS).1
      exact (Finset.mem_filter.mp hSC).2
    · intro S hS
      have hh := (Finset.mem_filter.mp hS).2
      omega
  have hpart : ((sparseCrookedMembers N F).card : ℝ) + (D.card : ℝ) = C.card := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := C) (fun S => 16 * S.card ≤ N)
  have hdenseR : (D.card : ℝ) ≤ 2048 * (N : ℝ) := by exact_mod_cast hdense
  have hNR : (1000000 : ℝ) ≤ N := by exact_mod_cast hlarge
  have hproduct := mul_le_mul_of_nonneg_left hNR (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  nlinarith only [hcount, hdenseR, hpart, hproduct]

end
/- TracePreparation -/

/- Divisor-minimal traces, their prefixes, and simultaneous witness counts. -/

section
open Finset


theorem minimal_trace_witness_core_consecutive {S : Finset ℕ} {c p d : ℕ}
    (hcp : c < p) (hd : 0 < d) (hddiv : d ∣ p - c)
    (htrace : apSegment c p d ⊆ S)
    (hmin : ∀ e : ℕ, 0 < e → e ∣ d → apSegment c p e ⊆ S → d ≤ e) :
    ∃ U : Finset ℕ, U ⊆ S ∧ (∃ l : ℕ∞, (U : Set ℕ).IsAPOfLength l) ∧
      ConsecutiveIn U c (c + d) ∧ apSegment c p d ⊆ U ∧
      ∀ z ∈ S, p ≤ z → z ∉ U → ∀ i : ℕ, 0 < i → c + i * d ∈ U →
        i.Coprime (anchorDistance c z) → IsWitnessPair S c {c + i * d, z} := by
  have hdlen : d ≤ p - c := Nat.le_of_dvd (by omega) hddiv
  have hcT : c ∈ apSegment c p d := Finset.mem_filter.mpr
    ⟨Finset.mem_Icc.mpr ⟨le_rfl, hcp.le⟩, by simp⟩
  have hvT : c + d ∈ apSegment c p d := Finset.mem_filter.mpr
    ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by simp⟩
  have hrep := apSegment_eq_natAP hcp.le hd
  have hTcon : ConsecutiveIn (apSegment c p d) c (c + d) :=
    hrep.symm ▸ natAP_consecutive_of_neighbor hd (hrep ▸ hcT) (hrep ▸ hvT)
  obtain ⟨U, hUS, hUAP, hUcon, hmax⟩ := fixedGap_core (by omega : c < c + d)
    (htrace hcT) (htrace hvT)
  have hTU : apSegment c p d ⊆ U := hmax _ htrace
    (Or.inr ⟨apSegment_isAP hcp.le hd, hTcon⟩)
  refine ⟨U, hUS, hUAP, hUcon, hTU, ?_⟩
  intro z hz hpz hzU i hi hyU hcop
  let y := c + i * d
  have hcy : c < y := by dsimp [y]; nlinarith only [hi, hd]
  have hzc : z ≠ c := by omega
  have hyz : y ≠ z := fun heq => hzU (heq ▸ hyU)
  refine ⟨Finset.card_pair hyz, ?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_erase.mpr ⟨hcy.ne', hUS hyU⟩
    · exact Finset.mem_erase.mpr ⟨hzc, hz⟩
  · rintro ⟨A, hAS, ⟨l, hAAP⟩, hCA⟩
    have hcA : c ∈ A := hCA (by simp)
    have hyA : y ∈ A := hCA (by simp [y])
    have hzA : z ∈ A := hCA (by simp)
    have hcard : 2 ≤ A.card := by
      have hsub : {c, y} ⊆ A := by simp [Finset.insert_subset_iff, hcA, hyA]
      simpa [hcy.ne] using Finset.card_le_card hsub
    obtain ⟨a, e, he, hArep⟩ := nat_ap_eq_natAP hAAP hcard
    have heid : e ∣ i * d := by
      have hh := natAP_dvd_anchorDistance (hArep ▸ hcA) (hArep ▸ hyA)
      have hdist : anchorDistance c y = i * d := by dsimp [anchorDistance, y]; omega
      simpa only [hdist] using hh
    have hez : e ∣ anchorDistance c z := natAP_dvd_anchorDistance (hArep ▸ hcA) (hArep ▸ hzA)
    have hed : e ∣ d := ((hcop.of_dvd_right hez).symm).dvd_of_dvd_mul_left heid
    have hediv : e ∣ p - c := hed.trans hddiv
    have hTeA : apSegment c p e ⊆ A := by
      rw [apSegment_eq_natAP hcp.le he]
      have hlast : c + ((p - c) / e) * e ≤ z := by
        rw [Nat.div_mul_cancel hediv]
        omega
      exact (natAP_prefix_subset_of_endpoints he (hArep ▸ hcA) (hArep ▸ hzA) hlast).trans
        (by rw [← hArep])
    have hde : d ≤ e := hmin e he hed (hTeA.trans hAS)
    have hed' : e ≤ d := Nat.le_of_dvd hd hed
    have heq : e = d := by omega
    have hvAe : c + e ∈ A := hTeA (by simpa only [heq] using hvT)
    have hcon : ConsecutiveIn A c (c + d) := by
      have hh := natAP_consecutive_of_neighbor he (hArep ▸ hcA) (hArep ▸ hvAe)
      have hhA : ConsecutiveIn A c (c + e) := hArep.symm ▸ hh
      simpa only [heq] using hhA
    exact hzU (hmax A hAS (Or.inr ⟨⟨l, hAAP⟩, hcon⟩) hzA)


end
/- Exact right-hand prefixes of finite arithmetic progressions through a fixed gap. -/

section
open Finset

theorem card_natAP {a d k : ℕ} (hd : 0 < d) : (natAP a d k).card = k := by
  have hinj : Function.Injective (fun i : ℕ => a + i * d) := by
    intro i j hij
    nlinarith only [hij, hd]
  rw [natAP, Finset.card_image_of_injective _ hinj, Finset.card_range]

theorem ap_right_prefix_of_consecutive {U : Finset ℕ} {c d : ℕ}
    (hd : 0 < d) (hAP : ∃ l : ℕ∞, (U : Set ℕ).IsAPOfLength l)
    (hcon : ConsecutiveIn U c (c + d)) :
    ∃ k : ℕ, 1 ≤ k ∧ U.filter (fun x => c ≤ x) = natAP c d (k + 1) := by
  obtain ⟨l, hl⟩ := hAP
  obtain ⟨a, hU⟩ := nat_ap_eq_with_consecutive_gap hl hcon
  simp only [Nat.add_sub_cancel_left] at hU
  have hne : U.Nonempty := ⟨c, hcon.1⟩
  let v := U.max' hne
  have hvU : v ∈ U := Finset.max'_mem U hne
  have hcv : c ≤ v := Finset.le_max' U c hcon.1
  have hvd : c + d ≤ v := Finset.le_max' U (c + d) hcon.2.1
  have hfilter : U.filter (fun x => c ≤ x) = U ∩ Finset.Icc c v := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_inter, Finset.mem_Icc]
    constructor
    · rintro ⟨hx, hcx⟩
      exact ⟨hx, hcx, Finset.le_max' U x hx⟩
    · rintro ⟨hx, hcx, _⟩
      exact ⟨hx, hcx⟩
  have hslice : U ∩ Finset.Icc c v = apSegment c v d :=
    (congrArg (fun T : Finset ℕ => T ∩ Finset.Icc c v) hU).trans
      (natAP_inter_Icc_eq_segment hd (hU ▸ hcon.1) (hU ▸ hvU) hcv)
  refine ⟨(v - c) / d, ?_, ?_⟩
  · apply (Nat.le_div_iff_mul_le hd).mpr
    omega
  · rw [hfilter, hslice, apSegment_eq_natAP hcv hd]

theorem right_prefix_card_le_of_no_long_prefix {S U : Finset ℕ} {c d K : ℕ}
    (hd : 0 < d) (hUS : U ⊆ S) (hAP : ∃ l : ℕ∞, (U : Set ℕ).IsAPOfLength l)
    (hcon : ConsecutiveIn U c (c + d))
    (hno : ∀ e : ℕ, 0 < e → ¬ natAP c e (K + 1) ⊆ S) :
    (U.filter (fun x => c ≤ x)).card ≤ K := by
  obtain ⟨k, hk, hprefix⟩ := ap_right_prefix_of_consecutive hd hAP hcon
  have hkK : k < K := by
    by_contra hnot
    have hKk : K ≤ k := by omega
    apply hno d hd
    have hsub : natAP c d (K + 1) ⊆ natAP c d (k + 1) := by
      intro x hx
      obtain ⟨i, hi, hxi⟩ := mem_natAP.mp hx
      exact mem_natAP.mpr ⟨i, by omega, hxi⟩
    exact hsub.trans (hprefix ▸ (Finset.filter_subset _ _).trans hUS)
  rw [hprefix, card_natAP hd]
  omega

end
/- Arithmetic bounds for products of two anchor distances. -/

section
open Filter

theorem eventually_uniform_divisor_card_pow_le_square (k : ℕ) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ m ≤ N^2, m.divisors.card^k ≤ N := by
  have ht : Tendsto (fun N : ℕ => N^2) atTop atTop := by
    apply Filter.tendsto_atTop.mpr
    intro b
    filter_upwards [Filter.eventually_ge_atTop b] with N hN
    nlinarith only [hN]
  have hh := ht.eventually (eventually_uniform_divisor_card_pow_le (2*k))
  filter_upwards [hh] with N hN m hm
  have hsq : (m.divisors.card^k)^2 ≤ N^2 := by
    simpa only [pow_mul, Nat.mul_comm 2 k] using hN m hm
  nlinarith only [hsq]

theorem natLog_succ_le_twice_of_le_square {m N : ℕ} (hm : m ≤ N^2) :
    Nat.log 2 m + 1 ≤ 2 * (Nat.log 2 N + 1) := by
  let L := Nat.log 2 N + 1
  have hL : 1 ≤ L := by dsimp [L]; omega
  have hN : N < 2^L := Nat.lt_pow_succ_log_self (b := 2) (by decide) N
  have hsq : N^2 < (2^L)^2 := by nlinarith only [hN]
  have heq : (2^L)^2 = 2^(2*L) := by rw [← pow_mul, Nat.mul_comm L 2]
  rw [heq] at hsq
  have hlog := Nat.log_lt_of_lt_pow' (b := 2) (by omega : 2*L ≠ 0) (hm.trans_lt hsq)
  omega

end
/- Divisor-minimal endpoint traces cover every point except structural witness neighbors. -/

section
open Finset

noncomputable def witnessNeighbors (S : Finset ℕ) (c p : ℕ) : Finset ℕ := by
  classical
  exact S.filter (fun x => IsWitnessPair S c {p, x})

def traceSteps (S : Finset ℕ) (c p : ℕ) : Finset ℕ :=
  (p - c).divisors.filter (fun d => apSegment c p d ⊆ S)

noncomputable def minimalTraceSteps (S : Finset ℕ) (c p : ℕ) : Finset ℕ := by
  classical
  exact (traceSteps S c p).filter (fun d =>
    ∀ e : ℕ, 0 < e → e ∣ d → apSegment c p e ⊆ S → d ≤ e)

theorem minimalTraceSteps_card_le (S : Finset ℕ) (c p : ℕ) :
    (minimalTraceSteps S c p).card ≤ (p - c).divisors.card := by
  classical
  exact Finset.card_le_card ((Finset.filter_subset _ _).trans (Finset.filter_subset _ _))

theorem minimal_trace_union_subset (S : Finset ℕ) (c p : ℕ) :
    (minimalTraceSteps S c p).biUnion (apSegment c p) ⊆ S := by
  classical
  intro x hx
  obtain ⟨d, hd, hxd⟩ := Finset.mem_biUnion.mp hx
  exact (Finset.mem_filter.mp (Finset.mem_filter.mp hd).1).2 hxd

theorem trace_union_subset_minimal (S : Finset ℕ) {c p : ℕ} (hcp : c < p) :
    (traceSteps S c p).biUnion (apSegment c p) ⊆
      (minimalTraceSteps S c p).biUnion (apSegment c p) := by
  classical
  intro x hx
  obtain ⟨d, hd, hxd⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨hddiv, hdS⟩ := Finset.mem_filter.mp hd
  obtain ⟨e, he, hed, heS, hmin⟩ := exists_divisor_minimal_trace (Nat.pos_of_mem_divisors hddiv) hdS
  have heM : e ∈ minimalTraceSteps S c p := Finset.mem_filter.mpr
    ⟨Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr
      ⟨hed.trans (Nat.mem_divisors.mp hddiv).1, by omega⟩, heS⟩, hmin⟩
  exact Finset.mem_biUnion.mpr ⟨e, heM, apSegment_mono_step hed hxd⟩

theorem hasAPCover_triple_of_not_witness {S : Finset ℕ} {c p x : ℕ}
    (hcp : c < p) (hc : c ∈ S) (hp : p ∈ S) (hx : x ∈ S)
    (hnot : ¬ IsWitnessPair S c {p, x}) : HasAPCover S {c, p, x} := by
  by_cases hxc : x = c
  · subst x
    refine ⟨{c, p}, by simp [Finset.insert_subset_iff, hc, hp],
      ⟨2, by simpa using Nat.isAPOfLength_pair hcp⟩, ?_⟩
    simp [Finset.insert_subset_iff]
  by_cases hxp : x = p
  · subst x
    refine ⟨{c, p}, by simp [Finset.insert_subset_iff, hc, hp],
      ⟨2, by simpa using Nat.isAPOfLength_pair hcp⟩, ?_⟩
    simp
  apply hasAPCover_of_not_witness (Finset.card_pair (Ne.symm hxp))
  · intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    · exact Finset.mem_erase.mpr ⟨hcp.ne', hp⟩
    · exact Finset.mem_erase.mpr ⟨hxc, hx⟩
  · exact hnot

theorem covered_point_mem_trace_union {S : Finset ℕ} {c p x : ℕ}
    (hcp : c < p) (hx : x ∈ Finset.Icc c p) (hcover : HasAPCover S {c, p, x}) :
    x ∈ (traceSteps S c p).biUnion (apSegment c p) := by
  obtain ⟨A, hAS, hAP, hCA⟩ := hcover
  obtain ⟨d, hd, hddiv, htrace⟩ := ap_inter_Icc_endpoints hAP (hCA (by simp)) (hCA (by simp)) hcp
  have hdS : apSegment c p d ⊆ S := by
    rw [← htrace]
    exact Finset.inter_subset_left.trans hAS
  have hdD : d ∈ traceSteps S c p := Finset.mem_filter.mpr
    ⟨Nat.mem_divisors.mpr ⟨hddiv, by omega⟩, hdS⟩
  exact Finset.mem_biUnion.mpr ⟨d, hdD, htrace ▸ Finset.mem_inter.mpr ⟨hCA (by simp), hx⟩⟩

theorem trace_cover_by_minimal_and_neighbors {S : Finset ℕ} {c p : ℕ}
    (hcp : c < p) (hc : c ∈ S) (hp : p ∈ S) :
    S ∩ Finset.Icc c p ⊆ (minimalTraceSteps S c p).biUnion (apSegment c p) ∪
      witnessNeighbors S c p := by
  classical
  intro x hx
  obtain ⟨hxS, hxI⟩ := Finset.mem_inter.mp hx
  by_cases hW : IsWitnessPair S c {p, x}
  · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hxS, hW⟩)
  · exact Finset.mem_union_left _ (trace_union_subset_minimal S hcp
      (covered_point_mem_trace_union hcp hxI (hasAPCover_triple_of_not_witness hcp hc hp hxS hW)))

theorem trace_card_le_minimal_union_add_neighbors {S : Finset ℕ} {c p : ℕ}
    (hcp : c < p) (hc : c ∈ S) (hp : p ∈ S) :
    (S ∩ Finset.Icc c p).card ≤
      ((minimalTraceSteps S c p).biUnion (apSegment c p)).card + (witnessNeighbors S c p).card :=
  (Finset.card_le_card (trace_cover_by_minimal_and_neighbors hcp hc hp)).trans (Finset.card_union_le _ _)

end
/- Right-hand prefix extensions of every divisor-minimal trace. -/

section
open Finset

theorem minimal_trace_prefix_family {S : Finset ℕ} {c p : ℕ} (hcp : c < p) :
    ∃ k : ℕ → ℕ, ∀ d ∈ minimalTraceSteps S c p,
      1 ≤ k d ∧ natAP c d (k d + 1) ⊆ S ∧ apSegment c p d ⊆ natAP c d (k d + 1) ∧
      ∀ z ∈ S, p ≤ z → z ∉ natAP c d (k d + 1) → ∀ i : ℕ, 0 < i → i ≤ k d →
        i.Coprime (anchorDistance c z) → IsWitnessPair S c {c + i*d, z} := by
  classical
  have hex : ∀ d : ℕ, ∃ k : ℕ, d ∈ minimalTraceSteps S c p →
      1 ≤ k ∧ natAP c d (k + 1) ⊆ S ∧ apSegment c p d ⊆ natAP c d (k + 1) ∧
      ∀ z ∈ S, p ≤ z → z ∉ natAP c d (k + 1) → ∀ i : ℕ, 0 < i → i ≤ k →
        i.Coprime (anchorDistance c z) → IsWitnessPair S c {c + i*d, z} := by
    intro d
    by_cases hdJ : d ∈ minimalTraceSteps S c p
    · obtain ⟨hdT, hmin⟩ := Finset.mem_filter.mp hdJ
      obtain ⟨hdD, hdS⟩ := Finset.mem_filter.mp hdT
      have hd : 0 < d := Nat.pos_of_mem_divisors hdD
      obtain ⟨U, hUS, hAP, hcon, hTU, hW⟩ := minimal_trace_witness_core_consecutive hcp hd
        (Nat.mem_divisors.mp hdD).1 hdS hmin
      obtain ⟨k, hk, hright⟩ := ap_right_prefix_of_consecutive hd hAP hcon
      refine ⟨k, fun _ => ⟨hk, ?_, ?_, ?_⟩⟩
      · rw [← hright]
        exact (Finset.filter_subset _ _).trans hUS
      · intro x hx
        rw [← hright]
        exact Finset.mem_filter.mpr ⟨hTU hx, (Finset.mem_Icc.mp (Finset.mem_filter.mp hx).1).1⟩
      · intro z hz hpz hzP i hi hik hcop
        have hzU : z ∉ U := by
          intro hzU
          apply hzP
          rw [← hright]
          exact Finset.mem_filter.mpr ⟨hzU, by omega⟩
        apply hW z hz hpz hzU i hi
        · have hy : c + i*d ∈ natAP c d (k+1) := mem_natAP.mpr ⟨i, by omega, rfl⟩
          rw [← hright] at hy
          exact (Finset.mem_filter.mp hy).1
        · exact hcop
    · exact ⟨0, fun hh => False.elim (hdJ hh)⟩
  choose k hk using hex
  exact ⟨k, hk⟩

theorem exists_biUnion_card_between {α β : Type*} [DecidableEq β]
    (J : Finset α) (R : α → Finset β) {K : ℕ} (hK : 0 < K)
    (hsmall : ∀ d ∈ J, (R d).card ≤ K) (hlarge : K ≤ (J.biUnion R).card) :
    ∃ I : Finset α, I ⊆ J ∧ K ≤ (I.biUnion R).card ∧ (I.biUnion R).card ≤ 2*K := by
  classical
  revert hsmall hlarge
  induction J using Finset.induction_on with
  | empty =>
    intro hsmall hlarge
    simp only [Finset.biUnion_empty, Finset.card_empty] at hlarge
    omega
  | @insert a J ha ih =>
    intro hsmall hlarge
    by_cases hJ : K ≤ (J.biUnion R).card
    · obtain ⟨I, hIJ, hlo, hhi⟩ := ih (fun d hd => hsmall d (Finset.mem_insert_of_mem hd)) hJ
      exact ⟨I, hIJ.trans (Finset.subset_insert _ _), hlo, hhi⟩
    · refine ⟨insert a J, Finset.Subset.refl _, hlarge, ?_⟩
      rw [Finset.biUnion_insert]
      have hh := Finset.card_union_le (R a) (J.biUnion R)
      have haK := hsmall a (Finset.mem_insert_self _ _)
      omega

end
/- Simultaneous witness counting across distinct divisor-minimal trace steps. -/

section
open Finset

theorem coprimePrefix_log_lower {m : ℕ} (hm : 0 < m) (K : ℕ) :
    K ≤ (coprimePrefix m K + 2 * m.divisors.card) * (Nat.log 2 m + 1) := by
  have hI : Finset.Ioc 0 K = Finset.Icc 1 K := by
    ext i
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  have hh := coprimeInterval_log_lower hm (Nat.zero_le K)
  simpa only [Nat.sub_zero, hI, coprimePrefix] using hh

theorem trace_witness_codes_card_le {S H J Z : Finset ℕ} {c p : ℕ} (k : ℕ → ℕ)
    (hJ : J ⊆ (p - c).divisors)
    (hprefix : ∀ d ∈ J, natAP c d (k d + 1) ⊆ H)
    (houtside : Disjoint Z H)
    (hW : ∀ z ∈ Z, ∀ d ∈ J, ∀ i : ℕ, 0 < i → i ≤ k d →
      i.Coprime (anchorDistance c z) → IsWitnessPair S c {c + i * d, z}) :
    (∑ z ∈ Z, ∑ d ∈ J, coprimePrefix ((p - c) * anchorDistance c z) (k d)) ≤
      (structuralWitnessPairs S c).card := by
  classical
  let V : Finset (Σ _ : ℕ, Σ _ : ℕ, ℕ) := Z.sigma (fun z => J.sigma (fun d =>
    (Finset.Icc 1 (k d)).filter (fun i => ((p - c) * anchorDistance c z).Coprime i)))
  let f : (Σ _ : ℕ, Σ _ : ℕ, ℕ) → Finset ℕ := fun q => {c + q.2.2 * q.2.1, q.1}
  have hspec : ∀ q ∈ V, q.1 ∈ Z ∧ q.2.1 ∈ J ∧
      c + q.2.2 * q.2.1 ∈ H ∧ q.2.2.Coprime (p - c) ∧ IsWitnessPair S c (f q) := by
    intro q hq
    obtain ⟨hz, hd, hi⟩ := Finset.mem_sigma.mp hq |>.imp_right Finset.mem_sigma.mp
    obtain ⟨hiI, hcop⟩ := Finset.mem_filter.mp hi
    obtain ⟨hi1, hik⟩ := Finset.mem_Icc.mp hiI
    have hcops := Nat.coprime_mul_iff_left.mp hcop
    refine ⟨hz, hd, hprefix q.2.1 hd (mem_natAP.mpr ⟨q.2.2, by omega, rfl⟩), hcops.1.symm, ?_⟩
    exact hW q.1 hz q.2.1 hd q.2.2 hi1 hik hcops.2.symm
  have hmaps : Set.MapsTo f (V : Set (Σ _ : ℕ, Σ _ : ℕ, ℕ))
      (structuralWitnessPairs S c : Set (Finset ℕ)) :=
    fun q hq => mem_structuralWitnessPairs.mpr (hspec q hq).2.2.2.2
  have hinj : Set.InjOn f (V : Set (Σ _ : ℕ, Σ _ : ℕ, ℕ)) := by
    rintro ⟨z, d, i⟩ hz ⟨w, e, j⟩ hw heq
    change ({c + i*d, z} : Finset ℕ) = {c + j*e, w} at heq
    have hzS := hspec ⟨z, d, i⟩ hz
    have hwS := hspec ⟨w, e, j⟩ hw
    have hzNot : z ∉ H := fun hzH => Finset.disjoint_left.mp houtside hzS.1 hzH
    have hwNot : w ∉ H := fun hwH => Finset.disjoint_left.mp houtside hwS.1 hwH
    have hzmem : z ∈ ({c + j*e, w} : Finset ℕ) := by rw [← heq]; simp
    have hzw : z = w := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hzmem
      rcases hzmem with hh | hh
      · exact False.elim (hzNot (hh.symm ▸ hwS.2.2.1))
      · exact hh
    have hymem : c + i*d ∈ ({c + j*e, w} : Finset ℕ) := by rw [← heq]; simp
    have hy : c + i*d = c + j*e := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hymem
      rcases hymem with hh | hh
      · exact hh
      · exact False.elim (hwNot (hh ▸ hzS.2.2.1))
    have hde : d = e := coprime_index_recovers_divisor
      (Nat.mem_divisors.mp (hJ hzS.2.1)).1 (Nat.mem_divisors.mp (hJ hwS.2.1)).1
      hzS.2.2.2.1 hwS.2.2.2.1 (by change i*d = j*e; exact Nat.add_left_cancel hy)
    have hdpos : 0 < d := Nat.pos_of_mem_divisors (hJ hzS.2.1)
    have hij : i = j := by rw [← hde] at hy; nlinarith only [hy, hdpos]
    cases hzw
    cases hde
    cases hij
    rfl
  simpa [V, Finset.card_sigma, coprimePrefix] using Finset.card_le_card_of_injOn f hmaps hinj

theorem trace_row_coprime_count {N D c p z : ℕ} {J : Finset ℕ} (k : ℕ → ℕ)
    (hc : c ∈ Finset.Icc 1 N) (hp : p ∈ Finset.Icc 1 N)
    (hcp : c < p) (hz : z ∈ Finset.Icc 1 N) (hpz : p ≤ z)
    (hdivisor : ∀ m ≤ N^2, m.divisors.card ≤ D) :
    (∑ d ∈ J, k d) ≤ 2 * (Nat.log 2 N + 1) *
      ((∑ d ∈ J, coprimePrefix ((p - c) * anchorDistance c z) (k d)) + 2 * J.card * D) := by
  let m := (p - c) * anchorDistance c z
  have hdist : 0 < anchorDistance c z := anchorDistance_pos (by omega)
  have hm : 0 < m := Nat.mul_pos (by omega) hdist
  have hpN : p - c ≤ N := by have := Finset.mem_Icc.mp hp; omega
  have hmN : m ≤ N^2 := by
    simpa only [m, pow_two] using Nat.mul_le_mul hpN (anchorDistance_le_of_mem hc hz)
  have htau := hdivisor m hmN
  have hlog := natLog_succ_le_twice_of_le_square hmN
  have hrow : ∀ d ∈ J, k d ≤
      2 * (Nat.log 2 N + 1) * (coprimePrefix m (k d) + 2 * D) := by
    intro d hd
    have hfirst := coprimePrefix_log_lower hm (k d)
    have hcoef := Nat.add_le_add_left (Nat.mul_le_mul_left 2 htau) (coprimePrefix m (k d))
    exact hfirst.trans (by simpa only [Nat.mul_comm] using Nat.mul_le_mul hcoef hlog)
  have hsum := Finset.sum_le_sum hrow
  rw [← Finset.mul_sum, Finset.sum_add_distrib] at hsum
  simp only [Finset.sum_const, smul_eq_mul] at hsum
  simpa only [m, Nat.mul_assoc, Nat.mul_left_comm J.card 2] using hsum

theorem many_witnesses_from_traces {N D c p : ℕ} {S H J Z : Finset ℕ} (k : ℕ → ℕ)
    (hc : c ∈ Finset.Icc 1 N) (hp : p ∈ Finset.Icc 1 N) (hcp : c < p)
    (hZ : Z ⊆ Finset.Icc 1 N) (htail : ∀ z ∈ Z, p ≤ z)
    (hJ : J ⊆ (p - c).divisors) (hprefix : ∀ d ∈ J, natAP c d (k d + 1) ⊆ H)
    (houtside : Disjoint Z H)
    (hW : ∀ z ∈ Z, ∀ d ∈ J, ∀ i : ℕ, 0 < i → i ≤ k d →
      i.Coprime (anchorDistance c z) → IsWitnessPair S c {c + i * d, z})
    (hdivisor : ∀ m ≤ N^2, m.divisors.card ≤ D)
    (hsize : 8 * (Nat.log 2 N + 1) * J.card * D ≤ ∑ d ∈ J, k d) :
    Z.card * (∑ d ∈ J, k d) ≤ 4 * (Nat.log 2 N + 1) * (structuralWitnessPairs S c).card := by
  have hrow : ∀ z ∈ Z, (∑ d ∈ J, k d) ≤ 4 * (Nat.log 2 N + 1) *
      ∑ d ∈ J, coprimePrefix ((p - c) * anchorDistance c z) (k d) := by
    intro z hz
    have hh := trace_row_coprime_count (J := J) k hc hp hcp (hZ hz) (htail z hz) hdivisor
    nlinarith only [hh, hsize]
  have hsum := Finset.sum_le_sum hrow
  have hcount := trace_witness_codes_card_le k hJ hprefix houtside hW
  have hmul := Nat.mul_le_mul_left (4 * (Nat.log 2 N + 1)) hcount
  simp only [Finset.sum_const, smul_eq_mul, ← Finset.mul_sum] at hsum
  omega

end
/- ShortTrace -/

/- The short-prefix case supplies quadratically many structural witnesses. -/

section
open Finset

theorem short_prefix_many_witnesses {N D c p K : ℕ} {S : Finset ℕ}
    (hS : S ⊆ Finset.Icc 1 N) (hc : c ∈ S) (hp : p ∈ S) (hcp : c < p)
    (hK : 0 < K)
    (hhead : 2*K ≤ (S ∩ Finset.Icc c p).card)
    (htail : 4*K ≤ (S.filter (fun z => p ≤ z)).card)
    (hneighbors : (witnessNeighbors S c p).card ≤ K)
    (hno : ∀ d : ℕ, 0 < d → ¬ natAP c d (K + 1) ⊆ S)
    (hdivisor : ∀ m ≤ N^2, m.divisors.card ≤ D)
    (hsize : 16 * (Nat.log 2 N + 1) * D^2 + D ≤ K) :
    K^2 ≤ 4 * (Nat.log 2 N + 1) * (structuralWitnessPairs S c).card := by
  classical
  obtain ⟨k, hk⟩ := minimal_trace_prefix_family (S := S) hcp
  let J := minimalTraceSteps S c p
  let R : ℕ → Finset ℕ := fun d => natAP c d (k d + 1)
  have hJD : J ⊆ (p - c).divisors :=
    (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  have hsmall : ∀ d ∈ J, (R d).card ≤ K := by
    intro d hdJ
    have hd := Nat.pos_of_mem_divisors (hJD hdJ)
    have hdK : k d < K := by
      by_contra hn
      apply hno d hd
      intro x hx
      obtain ⟨i, hi, hxi⟩ := mem_natAP.mp hx
      exact (hk d hdJ).2.1 (mem_natAP.mpr ⟨i, by omega, hxi⟩)
    simpa only [R, card_natAP hd] using (by omega : k d + 1 ≤ K)
  have htraceSub : J.biUnion (apSegment c p) ⊆ J.biUnion R := by
    intro x hx
    obtain ⟨d, hd, hxd⟩ := Finset.mem_biUnion.mp hx
    exact Finset.mem_biUnion.mpr ⟨d, hd, (hk d hd).2.2.1 hxd⟩
  have hlarge : K ≤ (J.biUnion R).card := by
    have hh := trace_card_le_minimal_union_add_neighbors hcp hc hp
    have htr := Finset.card_le_card htraceSub
    change (J.biUnion (apSegment c p)).card ≤ _ at htr
    change (S ∩ Finset.Icc c p).card ≤ (J.biUnion (apSegment c p)).card + _ at hh
    omega
  obtain ⟨I, hIJ, hIlow, hIhigh⟩ := exists_biUnion_card_between J R hK hsmall hlarge
  let H := I.biUnion R
  let Z := (S.filter (fun z => p ≤ z)) \ H
  have hID : I ⊆ (p - c).divisors := hIJ.trans hJD
  have hpN : p - c ≤ N := by have := Finset.mem_Icc.mp (hS hp); omega
  have hNN : N ≤ N^2 := by nlinarith only [Nat.zero_le N]
  have hD : I.card ≤ D :=
    (Finset.card_le_card hID).trans (hdivisor (p - c) (hpN.trans hNN))
  have hsum : H.card ≤ (∑ d ∈ I, k d) + I.card := by
    have hh := Finset.card_biUnion_le (s := I) (t := R)
    have hcards : (∑ d ∈ I, (R d).card) = (∑ d ∈ I, k d) + I.card := by
      calc
        (∑ d ∈ I, (R d).card) = ∑ d ∈ I, (k d + 1) := Finset.sum_congr rfl
          (fun d hd => card_natAP (Nat.pos_of_mem_divisors (hID hd)))
        _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
    exact hh.trans_eq hcards
  have hlog : 1 ≤ Nat.log 2 N + 1 := by omega
  have hDD : D ≤ D^2 := by nlinarith only [Nat.zero_le D]
  have htwice : 2*D ≤ K := by
    have hh := Nat.mul_le_mul_right (D^2) hlog
    nlinarith only [hsize, hDD, hh]
  have hsumK : K ≤ 2 * (∑ d ∈ I, k d) := by
    change K ≤ H.card at hIlow
    omega
  have hsumSize : 8 * (Nat.log 2 N + 1) * I.card * D ≤ ∑ d ∈ I, k d := by
    have hh := Nat.mul_le_mul_right (8 * (Nat.log 2 N + 1) * D) hD
    change K ≤ H.card at hIlow
    nlinarith only [hsize, hsum, hIlow, hD, hh]
  have hZcard : 2*K ≤ Z.card := by
    have hh := Finset.card_le_card_sdiff_add_card (s := S.filter (fun z => p ≤ z)) (t := H)
    change (S.filter (fun z => p ≤ z)).card ≤ Z.card + H.card at hh
    change H.card ≤ 2*K at hIhigh
    omega
  have hcount := many_witnesses_from_traces (S := S) (H := H) (J := I) (Z := Z) k
    (hS hc) (hS hp) hcp
    (fun z hz => hS (Finset.mem_filter.mp (Finset.mem_sdiff.mp hz).1).1)
    (fun z hz => (Finset.mem_filter.mp (Finset.mem_sdiff.mp hz).1).2)
    hID (fun d hd x hx => Finset.mem_biUnion.mpr ⟨d, hd, hx⟩)
    (Finset.disjoint_left.mpr (fun z hz hzH => (Finset.mem_sdiff.mp hz).2 hzH))
    (by
      intro z hz d hd i hi hik hcop
      have hzS := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hz).1).1
      have hpz := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hz).1).2
      have hzR : z ∉ R d := fun hzr => (Finset.mem_sdiff.mp hz).2
        (Finset.mem_biUnion.mpr ⟨d, hd, hzr⟩)
      exact (hk d (hIJ hd)).2.2.2 z hzS hpz hzR i hi hik hcop)
    hdivisor hsumSize
  have hprod1 := Nat.mul_le_mul_right (∑ d ∈ I, k d) hZcard
  have hprod2 := Nat.mul_le_mul_left K hsumK
  nlinarith only [hcount, hprod1, hprod2]

end
/- WitnessSelection -/

/- Middle-point selection and incidence bounds for private witness pairs. -/

section
open Finset

theorem exists_middle_block {T : Finset ℕ} {K : ℕ} (hcard : 8*K ≤ T.card) :
    ∃ M : Finset ℕ, M ⊆ T ∧ M.card = K ∧ ∀ p ∈ M,
      2*K ≤ (T.filter (fun x => x ≤ p)).card ∧
      4*K ≤ (T.filter (fun x => p ≤ x)).card := by
  classical
  let f := T.orderEmbOfFin rfl
  let mid : Fin K → ℕ := fun i => f ⟨2*K + i.val, by omega⟩
  have hinj : Function.Injective mid := by
    intro i j hij
    have hh := f.injective hij
    have hv := congrArg Fin.val hh
    apply Fin.ext
    change 2*K + i.val = 2*K + j.val at hv
    omega
  refine ⟨Finset.univ.image mid, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    exact T.orderEmbOfFin_mem rfl _
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  · intro p hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    constructor
    · let lo : Fin (2*K) → ℕ := fun j => f ⟨j.val, by omega⟩
      have hlo : Function.Injective lo := by
        intro a b hab
        have hh := congrArg Fin.val (f.injective hab)
        exact Fin.ext hh
      have hmaps : Set.MapsTo lo (↑(Finset.univ : Finset (Fin (2*K))) : Set (Fin (2*K)))
          (T.filter (fun x => x ≤ mid i) : Set ℕ) := by
        intro j hj
        refine Finset.mem_filter.mpr ⟨T.orderEmbOfFin_mem rfl _, ?_⟩
        apply f.monotone
        change j.val ≤ 2*K + i.val
        omega
      simpa only [Finset.card_univ, Fintype.card_fin] using
        Finset.card_le_card_of_injOn lo hmaps hlo.injOn
    · let hi : Fin (4*K) → ℕ := fun j => f ⟨4*K + j.val, by omega⟩
      have hhi : Function.Injective hi := by
        intro a b hab
        have hh := congrArg Fin.val (f.injective hab)
        apply Fin.ext
        change 4*K + a.val = 4*K + b.val at hh
        omega
      have hmaps : Set.MapsTo hi (↑(Finset.univ : Finset (Fin (4*K))) : Set (Fin (4*K)))
          (T.filter (fun x => mid i ≤ x) : Set ℕ) := by
        intro j hj
        refine Finset.mem_filter.mpr ⟨T.orderEmbOfFin_mem rfl _, ?_⟩
        apply f.monotone
        change 2*K + i.val ≤ 4*K + j.val
        omega
      simpa only [Finset.card_univ, Fintype.card_fin] using
        Finset.card_le_card_of_injOn hi hmaps hhi.injOn

theorem sum_witnessNeighbors_card_le (S M : Finset ℕ) (c : ℕ) :
    (∑ p ∈ M, (witnessNeighbors S c p).card) ≤
      2 * (structuralWitnessPairs S c).card := by
  classical
  let A := M.sigma (witnessNeighbors S c)
  let B := (structuralWitnessPairs S c).sigma (fun Q => Q)
  let f : (Σ _ : ℕ, ℕ) → (Σ _ : Finset ℕ, ℕ) := fun q => ⟨{q.1, q.2}, q.1⟩
  have hspec : ∀ q ∈ A, IsWitnessPair S c {q.1, q.2} := by
    intro q hq
    exact (Finset.mem_filter.mp (Finset.mem_sigma.mp hq).2).2
  have hmaps : Set.MapsTo f (A : Set (Σ _ : ℕ, ℕ)) (B : Set (Σ _ : Finset ℕ, ℕ)) := by
    intro q hq
    exact Finset.mem_sigma.mpr ⟨mem_structuralWitnessPairs.mpr (hspec q hq), by simp [f]⟩
  have hinj : Set.InjOn f (A : Set (Σ _ : ℕ, ℕ)) := by
    rintro ⟨p, x⟩ hx ⟨q, y⟩ hy heq
    have hpq : p = q := congrArg (fun z : (Σ _ : Finset ℕ, ℕ) => z.2) heq
    subst q
    have hpair : ({p, x} : Finset ℕ) = {p, y} := congrArg Sigma.fst heq
    have hpx : p ≠ x := by
      intro hh
      have hc := (hspec ⟨p, x⟩ hx).1
      simp [hh] at hc
    have hxmem : x ∈ ({p, y} : Finset ℕ) := by rw [← hpair]; simp
    have hxy : x = y := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxmem
      exact hxmem.resolve_left hpx.symm
    subst y
    rfl
  have hB : B.card = 2 * (structuralWitnessPairs S c).card := by
    rw [Finset.card_sigma]
    have hh : (∑ Q ∈ structuralWitnessPairs S c, Q.card) =
        ∑ _Q ∈ structuralWitnessPairs S c, 2 :=
      Finset.sum_congr rfl (fun Q hQ => (mem_structuralWitnessPairs.mp hQ).1)
    simpa only [Finset.sum_const, smul_eq_mul, Nat.mul_comm] using hh
  have hbound := (Finset.card_le_card_of_injOn f hmaps hinj).trans_eq hB
  simpa only [A, Finset.card_sigma] using hbound

end
/- LongPrefix -/

/- Preserve the anchored prefix in the long-prefix witness estimate. -/

section
open Finset

theorem minimal_prefix_many_witnesses_anchored {N D c d K : ℕ} {S : Finset ℕ}
    (hS : S ⊆ Finset.Icc 1 N) (hd : 0 < d) (hK : 1 ≤ K)
    (hprefix : natAP c d (K + 1) ⊆ S)
    (hmin : ∀ e : ℕ, 0 < e → natAP c e (K + 1) ⊆ S → d ≤ e)
    (hdivisor : ∀ n ≤ N, n.divisors.card ≤ D)
    (hlength : 8 * D * (Nat.log 2 N + 1) ≤ K) :
    ∃ U : Finset ℕ, U ⊆ S ∧ (∃ l : ℕ∞, (U : Set ℕ).IsAPOfLength l) ∧
      natAP c d (K + 1) ⊆ U ∧
      (S \ U).card * K ≤ 4 * (Nat.log 2 N + 1) * (structuralWitnessPairs S c).card := by
  obtain ⟨U, hUS, hUAP, hPU, hW⟩ := minimal_prefix_witness_core hd hK hprefix hmin
  refine ⟨U, hUS, hUAP, hPU, ?_⟩
  have hcP : c ∈ natAP c d (K + 1) := mem_natAP.mpr ⟨0, by omega, by simp⟩
  have hcI : c ∈ Finset.Icc 1 N := hS (hprefix hcP)
  have hrow : ∀ z ∈ S \ U, K ≤ 4 * (Nat.log 2 N + 1) *
      ((Finset.Ioc (K / 2) K).filter (fun p => (anchorDistance c z).Coprime p)).card := by
    intro z hz
    obtain ⟨hzS, hzU⟩ := Finset.mem_sdiff.mp hz
    have hcz : c ≠ z := fun heq => hzU (heq ▸ hPU hcP)
    have hm : 0 < anchorDistance c z := anchorDistance_pos hcz
    have hmN : anchorDistance c z ≤ N := anchorDistance_le_of_mem hcI (hS hzS)
    have htau := hdivisor (anchorDistance c z) hmN
    have hlog : Nat.log 2 (anchorDistance c z) + 1 ≤ Nat.log 2 N + 1 :=
      Nat.add_le_add_right (Nat.log_mono_right hmN) 1
    have hcoef := Nat.mul_le_mul htau hlog
    have hlen : 4 * (anchorDistance c z).divisors.card *
        (Nat.log 2 (anchorDistance c z) + 1) ≤ K - K / 2 := by
      have hhalf : K ≤ 2 * (K - K / 2) := by omega
      nlinarith only [hcoef, hlength, hhalf]
    have hcount := coprimeInterval_log_density hm (Nat.div_le_self K 2) hlen
    have hcount' := hcount.trans (Nat.mul_le_mul_left
      (2 * ((Finset.Ioc (K / 2) K).filter (fun p => (anchorDistance c z).Coprime p)).card) hlog)
    have hhalf : K ≤ 2 * (K - K / 2) := by omega
    nlinarith only [hcount', hhalf]
  have hsum := Finset.sum_le_sum hrow
  have hcount := minimal_prefix_witnesses_count hd hPU hW
  have hbound := Nat.mul_le_mul_left (4 * (Nat.log 2 N + 1)) hcount
  simp only [Finset.sum_const, smul_eq_mul, ← Finset.mul_sum] at hsum
  omega


end
/- RightCoreAlternative -/

/- A right-hand witness/core alternative for a single finite set. -/

section
open Finset

theorem no_long_right_prefix_many_witnesses {N D c K : ℕ} {S : Finset ℕ}
    (hS : S ⊆ Finset.Icc 1 N) (hc : c ∈ S) (hK : 0 < K)
    (hright : 8*K ≤ (S.filter (fun x => c < x)).card)
    (hno : ∀ d : ℕ, 0 < d → ¬ natAP c d (K + 1) ⊆ S)
    (hdivisor : ∀ m ≤ N^2, m.divisors.card ≤ D)
    (hsize : 16 * (Nat.log 2 N + 1) * D^2 + D ≤ K) :
    K^2 ≤ 4 * (Nat.log 2 N + 1) * (structuralWitnessPairs S c).card := by
  classical
  let T := S.filter (fun x => c < x)
  obtain ⟨M, hMT, hMcard, hmiddle⟩ := exists_middle_block hright
  by_cases hsome : ∃ p ∈ M, (witnessNeighbors S c p).card ≤ K
  · obtain ⟨p, hpM, hneigh⟩ := hsome
    have hpT := hMT hpM
    obtain ⟨hpS, hcp⟩ := Finset.mem_filter.mp hpT
    have hhead : 2*K ≤ (S ∩ Finset.Icc c p).card :=
      (hmiddle p hpM).1.trans (Finset.card_le_card (by
        intro x hx
        obtain ⟨hxT, hxp⟩ := Finset.mem_filter.mp hx
        obtain ⟨hxS, hcx⟩ := Finset.mem_filter.mp hxT
        exact Finset.mem_inter.mpr ⟨hxS, Finset.mem_Icc.mpr ⟨hcx.le, hxp⟩⟩))
    have htail : 4*K ≤ (S.filter (fun x => p ≤ x)).card :=
      (hmiddle p hpM).2.trans (Finset.card_le_card (by
        intro x hx
        obtain ⟨hxT, hpx⟩ := Finset.mem_filter.mp hx
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hxT).1, hpx⟩))
    exact short_prefix_many_witnesses hS hc hpS hcp hK hhead htail hneigh hno hdivisor hsize
  · have hneigh : ∀ p ∈ M, K ≤ (witnessNeighbors S c p).card := by
      intro p hp
      have hh : ¬ (witnessNeighbors S c p).card ≤ K := fun hn => hsome ⟨p, hp, hn⟩
      omega
    have hlow := Finset.sum_le_sum hneigh
    simp only [Finset.sum_const, smul_eq_mul, hMcard] at hlow
    have hupp := sum_witnessNeighbors_card_le S M c
    have hlog : 1 ≤ Nat.log 2 N + 1 := by omega
    have hm := Nat.mul_le_mul_right (4 * (structuralWitnessPairs S c).card) hlog
    nlinarith only [hlow, hupp, hm]

theorem right_witness_or_AP_core {N D c K : ℕ} {S : Finset ℕ}
    (hS : S ⊆ Finset.Icc 1 N) (hc : c ∈ S) (hK : 0 < K)
    (hright : 8*K ≤ (S.filter (fun x => c < x)).card)
    (hdivisor : ∀ m ≤ N^2, m.divisors.card ≤ D)
    (hsize : 16 * (Nat.log 2 N + 1) * D^2 + D ≤ K) :
    K^2 ≤ 4 * (Nat.log 2 N + 1) * (structuralWitnessPairs S c).card ∨
      ∃ U : Finset ℕ, U ⊆ S ∧ (∃ l : ℕ∞, (U : Set ℕ).IsAPOfLength l) ∧ c ∈ U ∧
        (S \ U).card * K ≤ 4 * (Nat.log 2 N + 1) * (structuralWitnessPairs S c).card := by
  classical
  by_cases hex : ∃ d : ℕ, 0 < d ∧ natAP c d (K + 1) ⊆ S
  · let d := Nat.find hex
    have hd := (Nat.find_spec hex).1
    have hprefix := (Nat.find_spec hex).2
    have hmin : ∀ e : ℕ, 0 < e → natAP c e (K + 1) ⊆ S → d ≤ e :=
      fun e he hpre => Nat.find_min' hex ⟨he, hpre⟩
    have hdivN : ∀ n ≤ N, n.divisors.card ≤ D := by
      intro n hn
      exact hdivisor n (hn.trans (by nlinarith only [Nat.zero_le N]))
    have hlength : 8 * D * (Nat.log 2 N + 1) ≤ K := by
      have hDD : D ≤ D^2 := by nlinarith only [Nat.zero_le D]
      have hm := Nat.mul_le_mul_left (16 * (Nat.log 2 N + 1)) hDD
      nlinarith only [hsize, hm, Nat.zero_le (D * (Nat.log 2 N + 1))]
    obtain ⟨U, hUS, hAP, hPU, hbound⟩ := minimal_prefix_many_witnesses_anchored
      hS hd hK hprefix hmin hdivN hlength
    exact Or.inr ⟨U, hUS, hAP, hPU (mem_natAP.mpr ⟨0, by omega, by simp⟩), hbound⟩
  · apply Or.inl
    apply no_long_right_prefix_many_witnesses hS hc hK hright _ hdivisor hsize
    exact fun d hd hpre => hex ⟨d, hd, hpre⟩

end
/- Reflection -/

/- Reflection of bounded sets, arithmetic progressions, and intrinsic witnesses. -/

section
open Finset

def reflectPoint (N x : ℕ) : ℕ := N + 1 - x

def reflectSet (N : ℕ) (S : Finset ℕ) : Finset ℕ := S.image (reflectPoint N)

theorem reflectPoint_mem {N x : ℕ} (hx : x ∈ Finset.Icc 1 N) :
    reflectPoint N x ∈ Finset.Icc 1 N := by
  simp only [reflectPoint, Finset.mem_Icc] at *
  omega

theorem reflectPoint_involutive {N x : ℕ} (hx : x ≤ N+1) :
    reflectPoint N (reflectPoint N x) = x := by
  dsimp [reflectPoint]
  omega

theorem reflectPoint_injOn (N : ℕ) :
    Set.InjOn (reflectPoint N) (Finset.Icc 1 N : Set ℕ) := by
  intro x hx y hy hxy
  have hxN := (Finset.mem_Icc.mp hx).2
  have hyN := (Finset.mem_Icc.mp hy).2
  dsimp [reflectPoint] at hxy
  omega

theorem reflectSet_subset {N : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.Icc 1 N) :
    reflectSet N S ⊆ Finset.Icc 1 N := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
  exact reflectPoint_mem (hS hy)

theorem reflectSet_mono {N : ℕ} {S T : Finset ℕ} (h : S ⊆ T) :
    reflectSet N S ⊆ reflectSet N T := Finset.image_subset_image h

theorem reflectSet_involutive {N : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.Icc 1 N) :
    reflectSet N (reflectSet N S) = S := by
  dsimp [reflectSet]
  rw [Finset.image_image]
  calc
    S.image (fun x => reflectPoint N (reflectPoint N x)) = S.image id := by
      apply Finset.image_congr
      intro x hx
      exact reflectPoint_involutive (by have := Finset.mem_Icc.mp (hS hx); omega)
    _ = S := Finset.image_id

theorem reflectSet_card {N : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.Icc 1 N) :
    (reflectSet N S).card = S.card := by
  exact Finset.card_image_of_injOn ((reflectPoint_injOn N).mono hS)

theorem reflectSet_sdiff {N : ℕ} {S T : Finset ℕ}
    (hS : S ⊆ Finset.Icc 1 N) (hTS : T ⊆ S) :
    reflectSet N (S \ T) = reflectSet N S \ reflectSet N T := by
  exact Finset.image_sdiff_of_injOn ((reflectPoint_injOn N).mono hS) hTS

theorem reflectSet_natAP {N a d k : ℕ} (hk : 0 < k)
    (htop : a + (k-1)*d ≤ N+1) :
    reflectSet N (natAP a d k) = natAP (N+1 - (a+(k-1)*d)) d k := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hx
    obtain ⟨i, hi, rfl⟩ := mem_natAP.mp hy
    refine mem_natAP.mpr ⟨k-1-i, by omega, ?_⟩
    have heq : i*d + (k-1-i)*d = (k-1)*d := by
      rw [← Nat.add_mul]
      congr 1
      omega
    have hsub : a+(k-1)*d + (N+1 - (a+(k-1)*d)) = N+1 := Nat.add_sub_of_le htop
    dsimp [reflectPoint] at hyx
    omega
  · intro hx
    obtain ⟨j, hj, rfl⟩ := mem_natAP.mp hx
    refine Finset.mem_image.mpr ⟨a + (k-1-j)*d,
      mem_natAP.mpr ⟨k-1-j, by omega, rfl⟩, ?_⟩
    have heq : j*d + (k-1-j)*d = (k-1)*d := by
      rw [← Nat.add_mul]
      congr 1
      omega
    have hsub : a+(k-1)*d + (N+1 - (a+(k-1)*d)) = N+1 := Nat.add_sub_of_le htop
    dsimp [reflectPoint]
    omega

theorem reflectSet_isAP {N : ℕ} {S : Finset ℕ}
    (hS : S ⊆ Finset.Icc 1 N) (hAP : ∃ l : ℕ∞, (S : Set ℕ).IsAPOfLength l) :
    ∃ l : ℕ∞, (reflectSet N S : Set ℕ).IsAPOfLength l := by
  rcases S.eq_empty_or_nonempty with hzero | hne
  · simpa [hzero, reflectSet] using hAP
  by_cases hsmall : S.card ≤ 2
  · obtain ⟨l, hl, hAP'⟩ := nonempty_small_isAP (hne.image (reflectPoint N))
      (by change (reflectSet N S).card ≤ 2; rw [reflectSet_card hS]; exact hsmall)
    exact ⟨l, hAP'⟩
  · obtain ⟨l, hl⟩ := hAP
    obtain ⟨a, d, hd, hrep⟩ := nat_ap_eq_natAP hl (by omega)
    have hk : 0 < S.card := Finset.card_pos.mpr hne
    have hlast : a + (S.card-1)*d ∈ S := by
      have hh : a + (S.card-1)*d ∈ natAP a d S.card :=
        mem_natAP.mpr ⟨S.card-1, by omega, rfl⟩
      rwa [← hrep] at hh
    have htop : a + (S.card-1)*d ≤ N+1 := by
      have := Finset.mem_Icc.mp (hS hlast)
      omega
    rw [hrep, reflectSet_natAP hk htop]
    exact ⟨_, natAP_isAP hd⟩

theorem reflectSet_AP_cover {N : ℕ} {S T : Finset ℕ}
    (hS : S ⊆ Finset.Icc 1 N) (hcover : HasAPCover S T) :
    HasAPCover (reflectSet N S) (reflectSet N T) := by
  obtain ⟨U, hUS, hAP, hTU⟩ := hcover
  exact ⟨reflectSet N U, reflectSet_mono hUS,
    reflectSet_isAP (hUS.trans hS) hAP, reflectSet_mono hTU⟩

theorem reflectSet_witness_pair {N c : ℕ} {S Q : Finset ℕ}
    (hS : S ⊆ Finset.Icc 1 N) (hc : c ∈ S) (hW : IsWitnessPair S c Q) :
    IsWitnessPair (reflectSet N S) (reflectPoint N c) (reflectSet N Q) := by
  have hQS : Q ⊆ S := hW.2.1.trans (Finset.erase_subset _ _)
  have hQ := hQS.trans hS
  refine ⟨(reflectSet_card hQ).trans hW.1, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_image.mpr ⟨y, hQS hy, rfl⟩⟩
    intro heq
    exact (Finset.mem_erase.mp (hW.2.1 hy)).1
      (reflectPoint_injOn N (hQ hy) (hS hc) heq)
  · intro hcover
    have hh := reflectSet_AP_cover (reflectSet_subset hS) hcover
    have heq : reflectSet N (insert (reflectPoint N c) (reflectSet N Q)) = insert c Q := by
      change (insert (reflectPoint N c) (reflectSet N Q)).image (reflectPoint N) = _
      rw [Finset.image_insert, reflectPoint_involutive
        (by have := Finset.mem_Icc.mp (hS hc); omega)]
      exact congrArg (insert c) (reflectSet_involutive hQ)
    rw [reflectSet_involutive hS, heq] at hh
    exact hW.2.2 hh

theorem reflectSet_witness_count {N c : ℕ} {S : Finset ℕ}
    (hS : S ⊆ Finset.Icc 1 N) (hc : c ∈ S) :
    (structuralWitnessPairs (reflectSet N S) (reflectPoint N c)).card =
      (structuralWitnessPairs S c).card := by
  classical
  have hle : ∀ {T : Finset ℕ} {b : ℕ}, T ⊆ Finset.Icc 1 N → b ∈ T →
      (structuralWitnessPairs T b).card ≤
        (structuralWitnessPairs (reflectSet N T) (reflectPoint N b)).card := by
    intro T b hT hb
    apply Finset.card_le_card_of_injOn (reflectSet N)
    · intro Q hQ
      exact mem_structuralWitnessPairs.mpr (reflectSet_witness_pair hT hb (mem_structuralWitnessPairs.mp hQ))
    · intro Q hQ R hR heq
      have hQT : Q ⊆ Finset.Icc 1 N :=
        (mem_structuralWitnessPairs.mp hQ).2.1.trans ((Finset.erase_subset _ _).trans hT)
      have hRT : R ⊆ Finset.Icc 1 N :=
        (mem_structuralWitnessPairs.mp hR).2.1.trans ((Finset.erase_subset _ _).trans hT)
      have hh := congrArg (reflectSet N) heq
      simpa only [reflectSet_involutive hQT, reflectSet_involutive hRT] using hh
  have hlo := hle hS hc
  have hhi := hle (reflectSet_subset hS) (Finset.mem_image.mpr ⟨c, hc, rfl⟩)
  rw [reflectSet_involutive hS, reflectPoint_involutive
    (by have := Finset.mem_Icc.mp (hS hc); omega)] at hhi
  exact Nat.le_antisymm hhi hlo

theorem reflectSet_filter_lt {N c : ℕ} {S : Finset ℕ}
    (hS : S ⊆ Finset.Icc 1 N) (hc : c ∈ S) :
    reflectSet N (S.filter (fun x => x < c)) =
      (reflectSet N S).filter (fun y => reflectPoint N c < y) := by
  have hcN := Finset.mem_Icc.mp (hS hc)
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hxS, hxc⟩ := Finset.mem_filter.mp hx
    have hxN := Finset.mem_Icc.mp (hS hxS)
    refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨x, hxS, rfl⟩, ?_⟩
    dsimp [reflectPoint]
    omega
  · intro hy
    obtain ⟨hyS, hcy⟩ := Finset.mem_filter.mp hy
    obtain ⟨x, hxS, rfl⟩ := Finset.mem_image.mp hyS
    have hxN := Finset.mem_Icc.mp (hS hxS)
    refine Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hxS, ?_⟩, rfl⟩
    dsimp [reflectPoint] at hcy
    omega

end
/- WitnessCoreAlternative -/

/- The witness/core alternative at an arbitrary anchor, in either orientation. -/

section
open Finset

theorem card_sides_add_one {S : Finset ℕ} {c : ℕ} (hc : c ∈ S) :
    (S.filter (fun x => x < c)).card + (S.filter (fun x => c < x)).card + 1 = S.card := by
  have hunion : S.filter (fun x => x < c) ∪ S.filter (fun x => c < x) = S.erase c := by
    ext x
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro (⟨hx, hxc⟩ | ⟨hx, hcx⟩)
      · exact ⟨hxc.ne, hx⟩
      · exact ⟨hcx.ne', hx⟩
    · rintro ⟨hne, hx⟩
      rcases lt_or_gt_of_ne hne with hh | hh
      · exact Or.inl ⟨hx, hh⟩
      · exact Or.inr ⟨hx, hh⟩
  have hdisj : Disjoint (S.filter (fun x => x < c)) (S.filter (fun x => c < x)) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have := (Finset.mem_filter.mp hx).2
    have := (Finset.mem_filter.mp hy).2
    omega
  have hh := Finset.card_union_of_disjoint hdisj
  rw [hunion, Finset.card_erase_of_mem hc] at hh
  have hpos := Finset.card_pos.mpr (show S.Nonempty from ⟨c, hc⟩)
  omega

theorem witness_or_AP_core {N D c K : ℕ} {S : Finset ℕ}
    (hS : S ⊆ Finset.Icc 1 N) (hc : c ∈ S) (hK : 0 < K)
    (hcard : 16*K + 1 ≤ S.card)
    (hdivisor : ∀ m ≤ N^2, m.divisors.card ≤ D)
    (hsize : 16 * (Nat.log 2 N + 1) * D^2 + D ≤ K) :
    K^2 ≤ 4 * (Nat.log 2 N + 1) * (structuralWitnessPairs S c).card ∨
      ∃ U : Finset ℕ, U ⊆ S ∧ (∃ l : ℕ∞, (U : Set ℕ).IsAPOfLength l) ∧ c ∈ U ∧
        (S \ U).card * K ≤ 4 * (Nat.log 2 N + 1) * (structuralWitnessPairs S c).card := by
  by_cases hright : 8*K ≤ (S.filter (fun x => c < x)).card
  · exact right_witness_or_AP_core hS hc hK hright hdivisor hsize
  have hleft : 8*K ≤ (S.filter (fun x => x < c)).card := by
    have hh := card_sides_add_one hc
    omega
  have hright' : 8*K ≤ ((reflectSet N S).filter (fun y => reflectPoint N c < y)).card := by
    rw [← reflectSet_filter_lt hS hc,
      reflectSet_card ((Finset.filter_subset _ _).trans hS)]
    exact hleft
  have hc' : reflectPoint N c ∈ reflectSet N S := Finset.mem_image.mpr ⟨c, hc, rfl⟩
  rcases right_witness_or_AP_core (reflectSet_subset hS) hc' hK hright' hdivisor hsize with hmany | hcore
  · exact Or.inl (by simpa only [reflectSet_witness_count hS hc] using hmany)
  · obtain ⟨V, hVS, hAP, hcV, hcount⟩ := hcore
    have hV : V ⊆ Finset.Icc 1 N := hVS.trans (reflectSet_subset hS)
    have hUS : reflectSet N V ⊆ S := by
      have hh := reflectSet_mono (N := N) hVS
      rwa [reflectSet_involutive hS] at hh
    refine Or.inr ⟨reflectSet N V, hUS, reflectSet_isAP hV hAP, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨reflectPoint N c, hcV, reflectPoint_involutive
        (by have := Finset.mem_Icc.mp (hS hc); omega)⟩
    · have hdiff : (S \ reflectSet N V).card = (reflectSet N S \ V).card := by
        have hh := reflectSet_card (N := N) (S := reflectSet N S \ V)
          (Finset.sdiff_subset.trans (reflectSet_subset hS))
        rw [reflectSet_sdiff (reflectSet_subset hS) hVS, reflectSet_involutive hS] at hh
        exact hh
      simpa only [hdiff, reflectSet_witness_count hS hc] using hcount

theorem AP_core_of_few_witnesses {N D c K t : ℕ} {S : Finset ℕ}
    (hS : S ⊆ Finset.Icc 1 N) (hc : c ∈ S) (hK : 0 < K)
    (hcard : 16*K + 1 ≤ S.card)
    (hdivisor : ∀ m ≤ N^2, m.divisors.card ≤ D)
    (hsize : 16 * (Nat.log 2 N + 1) * D^2 + D ≤ K)
    (ht : t ≤ K)
    (hfew : 4 * (Nat.log 2 N + 1) * (structuralWitnessPairs S c).card < t*K) :
    ∃ U : Finset ℕ, U ⊆ S ∧ (∃ l : ℕ∞, (U : Set ℕ).IsAPOfLength l) ∧
      c ∈ U ∧ (S \ U).card < t := by
  rcases witness_or_AP_core hS hc hK hcard hdivisor hsize with hmany | hcore
  · have hh := Nat.mul_le_mul_right K ht
    nlinarith only [hmany, hfew, hh]
  · obtain ⟨U, hUS, hAP, hcU, hbound⟩ := hcore
    refine ⟨U, hUS, hAP, hcU, ?_⟩
    exact Nat.lt_of_mul_lt_mul_right (hbound.trans_lt hfew)

end
/- CoreAsymptotic -/

/- Uniform applicability of the witness/core alternative above the cube-root scale. -/

section
open Finset Filter

def squareDivisorBound (N : ℕ) : ℕ :=
  (Finset.range (N^2+1)).sup (fun m => m.divisors.card)

theorem divisor_card_le_squareDivisorBound {m N : ℕ} (hm : m ≤ N^2) :
    m.divisors.card ≤ squareDivisorBound N :=
  Finset.le_sup (s := Finset.range (N^2+1)) (f := fun n : ℕ => n.divisors.card)
    (b := m) (Finset.mem_range.mpr (by omega))

theorem squareDivisorBound_pos {N : ℕ} (hN : 1 ≤ N) : 1 ≤ squareDivisorBound N := by
  have hh := divisor_card_le_squareDivisorBound (m := 1) (by nlinarith only [hN])
  simpa only [Nat.divisors_one, Finset.card_singleton] using hh

theorem eventually_squareDivisorBound_pow_le (k : ℕ) :
    ∀ᶠ N : ℕ in atTop, (squareDivisorBound N)^k ≤ N := by
  filter_upwards [eventually_uniform_divisor_card_pow_le_square k] with N hN
  obtain ⟨m, hm, heq⟩ := Finset.exists_mem_eq_sup (Finset.range (N^2+1))
    ⟨0, by simp⟩ (fun m => m.divisors.card)
  change squareDivisorBound N = m.divisors.card at heq
  rw [heq]
  exact hN m (by have := Finset.mem_range.mp hm; omega)

theorem core_threshold_cubed_le {L D N : ℕ}
    (hL : 1 ≤ L) (hD : 1 ≤ D) (hLpow : L^12 ≤ N) (hDpow : D^24 ≤ N)
    (hN : 273^6 ≤ N) :
    (16 * (16*L*D^2 + D) + 1)^3 ≤ N := by
  let B := 16 * (16*L*D^2 + D) + 1
  have hDD : D ≤ D^2 := by nlinarith only [Nat.zero_le D]
  have hmul := Nat.mul_le_mul_right (D^2) hL
  have hmul1 : 1 ≤ L*D^2 := by nlinarith only [hD, hDD, hmul]
  have hB : B ≤ 273*L*D^2 := by
    dsimp [B]
    nlinarith only [hDD, hmul, hmul1]
  have hpow : B^12 ≤ 273^12 * N^2 := by
    calc
      B^12 ≤ (273*L*D^2)^12 := Nat.pow_le_pow_left hB 12
      _ = 273^12 * (L^12 * D^24) := by ring
      _ ≤ 273^12 * (N*N) := Nat.mul_le_mul_left _ (Nat.mul_le_mul hLpow hDpow)
      _ = _ := by ring
  have hconst : 273^12 ≤ N^2 := by
    have hh := Nat.pow_le_pow_left hN 2
    simpa only [← pow_mul] using hh
  have hbound : (B^3)^4 ≤ N^4 := by
    calc
      (B^3)^4 = B^12 := by ring
      _ ≤ 273^12*N^2 := hpow
      _ ≤ N^2*N^2 := Nat.mul_le_mul_right _ hconst
      _ = N^4 := by ring
  exact (Nat.pow_le_pow_iff_left (by decide : 4 ≠ 0)).mp hbound

theorem eventually_core_threshold :
    ∀ᶠ N : ℕ in atTop,
      (16 * (16 * (Nat.log 2 N + 1) * (squareDivisorBound N)^2 + squareDivisorBound N) + 1)^3 ≤ N := by
  filter_upwards [eventually_natLog_pow_le 12, eventually_squareDivisorBound_pow_le 24,
    Filter.eventually_ge_atTop (273^6), Filter.eventually_ge_atTop 1] with N hL hD hN hN1
  exact core_threshold_cubed_le (by omega) (squareDivisorBound_pos hN1) hL hD hN

theorem eventually_witness_or_AP_core :
    ∀ᶠ N : ℕ in atTop, ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 N → N ≤ S.card^3 →
      ∀ c ∈ S,
        ((S.card-1)/16)^2 ≤ 4 * (Nat.log 2 N + 1) * (structuralWitnessPairs S c).card ∨
        ∃ U : Finset ℕ, U ⊆ S ∧ (∃ l : ℕ∞, (U : Set ℕ).IsAPOfLength l) ∧ c ∈ U ∧
          (S \ U).card * ((S.card-1)/16) ≤
            4 * (Nat.log 2 N + 1) * (structuralWitnessPairs S c).card := by
  filter_upwards [eventually_core_threshold, Filter.eventually_ge_atTop (17^3)] with N hthreshold hN
  intro S hS hScube c hc
  have h17 : 17 ≤ S.card :=
    (Nat.pow_le_pow_iff_left (by decide : 3 ≠ 0)).mp (hN.trans hScube)
  have hcard : 16 * ((S.card-1)/16) + 1 ≤ S.card := by omega
  have hbound : 16 * (16 * (Nat.log 2 N + 1) * (squareDivisorBound N)^2 + squareDivisorBound N) + 1 ≤
      S.card := (Nat.pow_le_pow_iff_left (by decide : 3 ≠ 0)).mp (hthreshold.trans hScube)
  apply witness_or_AP_core hS hc (by omega) hcard
    (fun m hm => divisor_card_le_squareDivisorBound hm)
  omega

end
/- VariableAnchorCount -/

/- Private witness pairs can be summed over anchors in a fixed transversal. -/

section
open Finset

theorem sum_variable_anchor_witnesses_le {N : ℕ} {F : Finset (Finset ℕ)} {H : Finset ℕ}
    (hF : Erdos272.IsArithInterSet N F) (anchor : Finset ℕ → ℕ)
    (hanchor : ∀ S ∈ F, anchor S ∈ S ∧ anchor S ∈ H) :
    (∑ S ∈ F, (structuralWitnessPairs S (anchor S)).card) ≤ H.card * N.choose 2 := by
  classical
  let A := F.sigma (fun S => structuralWitnessPairs S (anchor S))
  let B := H ×ˢ (Finset.Icc 1 N).powersetCard 2
  let f : (Σ _ : Finset ℕ, Finset ℕ) → ℕ × Finset ℕ := fun q => (anchor q.1, q.2)
  have hmaps : Set.MapsTo f (A : Set (Σ _ : Finset ℕ, Finset ℕ)) (B : Set (ℕ × Finset ℕ)) := by
    intro q hq
    obtain ⟨hS, hQ⟩ := Finset.mem_sigma.mp hq
    have hW := mem_structuralWitnessPairs.mp hQ
    refine Finset.mem_product.mpr ⟨(hanchor q.1 hS).2, Finset.mem_powersetCard.mpr ⟨?_, hW.1⟩⟩
    exact hW.2.1.trans ((Finset.erase_subset _ _).trans (Finset.mem_powerset.mp (hF.1 hS)))
  have hinj : Set.InjOn f (A : Set (Σ _ : Finset ℕ, Finset ℕ)) := by
    rintro ⟨S, Q⟩ hSQ ⟨T, R⟩ hTR heq
    obtain ⟨hS, hQ⟩ := Finset.mem_sigma.mp hSQ
    obtain ⟨hT, hR⟩ := Finset.mem_sigma.mp hTR
    have hc : anchor S = anchor T := congrArg Prod.fst heq
    have hQR : Q = R := congrArg Prod.snd heq
    have hWQ := mem_structuralWitnessPairs.mp hQ
    have hWR := mem_structuralWitnessPairs.mp hR
    have hTS : T = S := witness_pair_private hF hS hT (hanchor S hS).1
      (by rw [hc]; exact (hanchor T hT).1) hWQ
      (by rw [hQR]; exact hWR.2.1.trans (Finset.erase_subset _ _))
    subst T
    subst R
    rfl
  have hh := Finset.card_le_card_of_injOn f hmaps hinj
  simpa only [A, B, Finset.card_sigma, Finset.card_product, Finset.card_powersetCard,
    Nat.card_Icc, Nat.add_sub_cancel] using hh

theorem witness_rich_family_card_le {N q C : ℕ} {F : Finset (Finset ℕ)} {H : Finset ℕ}
    (hF : Erdos272.IsArithInterSet N F)
    (hwitness : ∀ S ∈ F, ∃ c ∈ S, c ∈ H ∧ q ≤ C * (structuralWitnessPairs S c).card) :
    F.card * q ≤ C * H.card * N.choose 2 := by
  classical
  have hex : ∀ S : Finset ℕ, ∃ c, S ∈ F →
      c ∈ S ∧ c ∈ H ∧ q ≤ C * (structuralWitnessPairs S c).card := by
    intro S
    by_cases hS : S ∈ F
    · obtain ⟨c, hc, hcH, hb⟩ := hwitness S hS
      exact ⟨c, fun _ => ⟨hc, hcH, hb⟩⟩
    · exact ⟨0, fun hh => False.elim (hS hh)⟩
  choose anchor hanchor using hex
  have hsum := Finset.sum_le_sum (s := F) (fun S hS => (hanchor S hS).2.2)
  simp only [Finset.sum_const, smul_eq_mul, ← Finset.mul_sum] at hsum
  have hbound := sum_variable_anchor_witnesses_le hF anchor
    (fun S hS => ⟨(hanchor S hS).1, (hanchor S hS).2.1⟩)
  have hh := hsum.trans (Nat.mul_le_mul_left C hbound)
  simpa only [Nat.mul_assoc] using hh

end
/- FarFromAP -/

/- Families far from arithmetic progressions are controlled by their private witnesses. -/

section
open Finset

theorem far_from_AP_witness_lower {N D c K t : ℕ} {S : Finset ℕ}
    (hS : S ⊆ Finset.Icc 1 N) (hc : c ∈ S) (hK : 0 < K)
    (hcard : 16*K + 1 ≤ S.card)
    (hdivisor : ∀ m ≤ N^2, m.divisors.card ≤ D)
    (hsize : 16 * (Nat.log 2 N + 1) * D^2 + D ≤ K)
    (ht : t ≤ K)
    (hfar : ∀ U ⊆ S, (∃ l : ℕ∞, (U : Set ℕ).IsAPOfLength l) → c ∈ U → t ≤ (S \ U).card) :
    t*K ≤ 4 * (Nat.log 2 N + 1) * (structuralWitnessPairs S c).card := by
  rcases witness_or_AP_core hS hc hK hcard hdivisor hsize with hmany | hcore
  · have hh : t*K ≤ K^2 := by simpa only [pow_two] using Nat.mul_le_mul_right K ht
    exact hh.trans hmany
  · obtain ⟨U, hUS, hAP, hcU, hb⟩ := hcore
    exact (Nat.mul_le_mul_right K (hfar U hUS hAP hcU)).trans hb

theorem far_from_AP_family_card_le {N D K t : ℕ} {F : Finset (Finset ℕ)} {H : Finset ℕ}
    (hF : Erdos272.IsArithInterSet N F) (hK : 0 < K)
    (hcard : ∀ S ∈ F, 16*K + 1 ≤ S.card)
    (hdivisor : ∀ m ≤ N^2, m.divisors.card ≤ D)
    (hsize : 16 * (Nat.log 2 N + 1) * D^2 + D ≤ K)
    (ht : t ≤ K) (hhit : ∀ S ∈ F, (S ∩ H).Nonempty)
    (hfar : ∀ S ∈ F, ∀ U ⊆ S, (∃ l : ℕ∞, (U : Set ℕ).IsAPOfLength l) → t ≤ (S \ U).card) :
    F.card * (t*K) ≤ 4 * (Nat.log 2 N + 1) * H.card * N.choose 2 := by
  apply witness_rich_family_card_le hF
  intro S hS
  obtain ⟨c, hc⟩ := hhit S hS
  obtain ⟨hcS, hcH⟩ := Finset.mem_inter.mp hc
  exact ⟨c, hcS, hcH, far_from_AP_witness_lower (Finset.mem_powerset.mp (hF.1 hS)) hcS
    hK (hcard S hS) hdivisor hsize ht (fun U hUS hAP _ => hfar S hS U hUS hAP)⟩

theorem exists_maximal_AP_extension {S U : Finset ℕ}
    (hUS : U ⊆ S) (hAP : ∃ l : ℕ∞, (U : Set ℕ).IsAPOfLength l) :
    ∃ P : Finset ℕ, U ⊆ P ∧ P ⊆ S ∧ (∃ l : ℕ∞, (P : Set ℕ).IsAPOfLength l) ∧
      ∀ Q : Finset ℕ, P ⊆ Q → Q ⊆ S → (∃ l : ℕ∞, (Q : Set ℕ).IsAPOfLength l) → Q = P := by
  classical
  let A := S.powerset.filter (fun P => U ⊆ P ∧ ∃ l : ℕ∞, (P : Set ℕ).IsAPOfLength l)
  have hUA : U ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hUS, Finset.Subset.refl _, hAP⟩
  obtain ⟨P, hP, hmax⟩ := Finset.exists_max_image A Finset.card ⟨U, hUA⟩
  obtain ⟨hPS, hUP, hPAP⟩ := Finset.mem_filter.mp hP
  refine ⟨P, hUP, Finset.mem_powerset.mp hPS, hPAP, ?_⟩
  intro Q hPQ hQS hQAP
  have hQA : Q ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hQS, hUP.trans hPQ, hQAP⟩
  exact (Finset.eq_of_subset_of_card_le hPQ (hmax Q hQA)).symm

theorem maximal_AP_core_of_few_witnesses {N D c K t : ℕ} {S : Finset ℕ}
    (hS : S ⊆ Finset.Icc 1 N) (hc : c ∈ S) (hK : 0 < K)
    (hcard : 16*K + 1 ≤ S.card)
    (hdivisor : ∀ m ≤ N^2, m.divisors.card ≤ D)
    (hsize : 16 * (Nat.log 2 N + 1) * D^2 + D ≤ K)
    (ht : t ≤ K)
    (hfew : 4 * (Nat.log 2 N + 1) * (structuralWitnessPairs S c).card < t*K) :
    ∃ P : Finset ℕ, P ⊆ S ∧ (∃ l : ℕ∞, (P : Set ℕ).IsAPOfLength l) ∧
      c ∈ P ∧ (S \ P).card < t ∧
      ∀ Q : Finset ℕ, P ⊆ Q → Q ⊆ S → (∃ l : ℕ∞, (Q : Set ℕ).IsAPOfLength l) → Q = P := by
  obtain ⟨U, hUS, hAP, hcU, hsmall⟩ := AP_core_of_few_witnesses hS hc hK hcard hdivisor hsize ht hfew
  obtain ⟨P, hUP, hPS, hPAP, hmax⟩ := exists_maximal_AP_extension hUS hAP
  refine ⟨P, hPS, hPAP, hUP hcU, ?_, hmax⟩
  have hdiff : S \ P ⊆ S \ U := by
    intro x hx
    obtain ⟨hxS, hxP⟩ := Finset.mem_sdiff.mp hx
    exact Finset.mem_sdiff.mpr ⟨hxS, fun hxU => hxP (hUP hxU)⟩
  exact (Finset.card_le_card hdiff).trans_lt hsmall

end
/- CorePoolCount -/

/- Counting disjoint remainders, and an intersection constraint on large core classes. -/

section
open Finset

theorem disjoint_pieces_hit_bound {α ι : Type*} [DecidableEq α]
    (I : Finset ι) (piece : ι → Finset α) (U : Finset α)
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (piece i) (piece j))
    (hhit : ∀ i ∈ I, (piece i ∩ U).Nonempty) : I.card ≤ U.card := by
  classical
  choose x hx using (fun i : {i // i ∈ I} => hhit i.val i.property)
  have hmaps : Set.MapsTo x
      ((Finset.univ : Finset {i // i ∈ I}) : Set {i // i ∈ I}) (U : Set α) := by
    intro i hi
    exact (Finset.mem_inter.mp (hx i)).2
  have hinj : Function.Injective x := by
    intro i j hij
    apply Subtype.ext
    by_contra hne
    have hd := hdisj i.val i.property j.val j.property hne
    exact Finset.disjoint_left.mp hd (Finset.mem_inter.mp (hx i)).1
      (by simpa only [hij] using (Finset.mem_inter.mp (hx j)).1)
  simpa only [Finset.card_univ, Fintype.card_coe] using
    Finset.card_le_card_of_injOn x hmaps hinj.injOn

theorem exists_piece_disjoint_of_card_lt {α ι : Type*} [DecidableEq α]
    (I : Finset ι) (piece : ι → Finset α) (U : Finset α)
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (piece i) (piece j))
    (hcard : U.card < I.card) : ∃ i ∈ I, Disjoint (piece i) U := by
  classical
  by_contra hn
  have hhit : ∀ i ∈ I, (piece i ∩ U).Nonempty := by
    intro i hi
    by_contra hempty
    apply hn
    refine ⟨i, hi, Finset.disjoint_left.mpr ?_⟩
    intro x hx hU
    exact hempty ⟨x, Finset.mem_inter.mpr ⟨hx, hU⟩⟩
  have hh := disjoint_pieces_hit_bound I piece U hdisj hhit
  omega

theorem heavy_core_pools_intersect {α : Type*} [DecidableEq α]
    {F G : Finset (Finset α)} {U V : Finset α} {s : ℕ} (core : Finset α → Finset α)
    (hFU : ∀ S ∈ F, core S ⊆ U) (hGV : ∀ T ∈ G, core T ⊆ V)
    (hFdisj : ∀ S ∈ F, ∀ T ∈ F, S ≠ T → Disjoint (S \ core S) (T \ core T))
    (hGdisj : ∀ S ∈ G, ∀ T ∈ G, S ≠ T → Disjoint (S \ core S) (T \ core T))
    (hcross : ∀ S ∈ F, ∀ T ∈ G, (S ∩ T).Nonempty)
    (hsmall : ∀ T ∈ G, T.card ≤ s)
    (hFlarge : s < F.card) (hGlarge : U.card < G.card) : (U ∩ V).Nonempty := by
  classical
  by_contra hempty
  have hUV : Disjoint U V := Finset.disjoint_left.mpr
    (fun x hx hy => hempty ⟨x, Finset.mem_inter.mpr ⟨hx, hy⟩⟩)
  obtain ⟨T, hT, hTU⟩ := exists_piece_disjoint_of_card_lt G (fun T => T \ core T) U hGdisj hGlarge
  have hTfull : Disjoint T U := by
    apply Finset.disjoint_left.mpr
    intro x hxT hxU
    by_cases hxcore : x ∈ core T
    · exact Finset.disjoint_left.mp hUV hxU (hGV T hT hxcore)
    · exact Finset.disjoint_left.mp hTU (Finset.mem_sdiff.mpr ⟨hxT, hxcore⟩) hxU
  have hhit : ∀ S ∈ F, ((S \ core S) ∩ T).Nonempty := by
    intro S hS
    obtain ⟨x, hx⟩ := hcross S hS T hT
    obtain ⟨hxS, hxT⟩ := Finset.mem_inter.mp hx
    refine ⟨x, Finset.mem_inter.mpr ⟨Finset.mem_sdiff.mpr ⟨hxS, ?_⟩, hxT⟩⟩
    intro hxcore
    exact Finset.disjoint_left.mp hTfull hxT (hFU S hS hxcore)
  have hh := (disjoint_pieces_hit_bound F (fun S => S \ core S) T hFdisj hhit).trans (hsmall T hT)
  omega

end
/- CoreOverlap -/

/- Long overlap forces an AP intersection to stay inside a nearly full maximal core. -/

section
open Finset

theorem AP_subset_core_of_long_overlap {S P Q : Finset ℕ} {a b d k K : ℕ}
    (hd : 0 < d) (hPform : P = natAP b d k) (hPS : P ⊆ S) (hQS : Q ⊆ S)
    (hQAP : ∃ l : ℕ∞, (Q : Set ℕ).IsAPOfLength l)
    (hlong : natAP a d (K+1) ⊆ P ∩ Q) (hsmall : (S \ P).card < K)
    (hmax : ∀ U : Finset ℕ, P ⊆ U → U ⊆ S →
      (∃ l : ℕ∞, (U : Set ℕ).IsAPOfLength l) → U = P) : Q ⊆ P := by
  have hK : 0 < K := by omega
  have ha : a ∈ P ∩ Q := hlong (mem_natAP.mpr ⟨0, by omega, by simp⟩)
  have hv : a+d ∈ P ∩ Q := hlong (mem_natAP.mpr ⟨1, by omega, by simp⟩)
  have hlast : a+K*d ∈ P ∩ Q := hlong (mem_natAP.mpr ⟨K, by omega, rfl⟩)
  have haQ := (Finset.mem_inter.mp ha).2
  have hvQ := (Finset.mem_inter.mp hv).2
  have hlastQ := (Finset.mem_inter.mp hlast).2
  have hQcard : 2 ≤ Q.card := by
    have hh : {a, a+d} ⊆ Q := by simp [Finset.insert_subset_iff, haQ, hvQ]
    simpa only [Finset.card_pair (by omega : a ≠ a+d)] using Finset.card_le_card hh
  obtain ⟨l, hl⟩ := hQAP
  obtain ⟨q, e, he, hQform⟩ := nat_ap_eq_natAP hl hQcard
  have hediv : e ∣ d := by
    have hh := natAP_dvd_anchorDistance (hQform ▸ haQ) (hQform ▸ hvQ)
    simpa only [anchorDistance, Nat.min_eq_left (by omega : a ≤ a+d),
      Nat.max_eq_right (by omega : a ≤ a+d), Nat.add_sub_cancel_left] using hh
  have hed : e ≤ d := Nat.le_of_dvd hd hediv
  have heq : e = d := by
    by_contra hne
    have hlt : e < d := by omega
    have hseg : Q ∩ Finset.Icc a (a+K*d) = apSegment a (a+K*d) e := by
      have hh := natAP_inter_Icc_eq_segment he (hQform ▸ haQ) (hQform ▸ hlastQ)
        (by omega : a ≤ a+K*d)
      rw [← hQform] at hh
      exact hh
    let f : ℕ → ℕ := fun i => a+i*d+e
    have hmaps : Set.MapsTo f (Finset.range K : Set ℕ) ((S \ P : Finset ℕ) : Set ℕ) := by
      intro i hi
      have hiK := Finset.mem_range.mp hi
      have hyQ : f i ∈ Q := by
        have hySeg : f i ∈ apSegment a (a+K*d) e := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by dsimp [f]; omega, ?_⟩, ?_⟩
          · dsimp [f]
            nlinarith only [hiK, hed]
          · have hh : e ∣ i*d+e := dvd_add (dvd_mul_of_dvd_right hediv i) (dvd_refl e)
            simpa only [f, Nat.add_assoc, Nat.add_sub_cancel_left] using hh
        rw [← hseg] at hySeg
        exact (Finset.mem_inter.mp hySeg).1
      refine Finset.mem_sdiff.mpr ⟨hQS hyQ, ?_⟩
      intro hyP
      have haP := (Finset.mem_inter.mp ha).1
      have hh := natAP_dvd_anchorDistance (hPform ▸ haP) (hPform ▸ hyP)
      have hdist : anchorDistance a (f i) = i*d+e := by dsimp [anchorDistance, f]; omega
      rw [hdist] at hh
      have hdive : d ∣ e := by
        have hh' := Nat.dvd_sub hh (dvd_mul_left d i)
        simpa only [Nat.add_sub_cancel_left] using hh'
      have hde := Nat.le_of_dvd he hdive
      omega
    have hinj : Function.Injective f := by
      intro i j hij
      dsimp [f] at hij
      nlinarith only [hij, hd]
    have hcount := Finset.card_le_card_of_injOn f hmaps hinj.injOn
    rw [Finset.card_range] at hcount
    omega
  have haP := (Finset.mem_inter.mp ha).1
  have hvP := (Finset.mem_inter.mp hv).1
  have hconP : ConsecutiveIn P a (a+d) := by
    have hh := natAP_consecutive_of_neighbor hd (hPform ▸ haP) (hPform ▸ hvP)
    rwa [← hPform] at hh
  have hconQ : ConsecutiveIn Q a (a+d) := by
    have hvQ' : a+e ∈ Q := by simpa only [heq] using hvQ
    have hh := natAP_consecutive_of_neighbor he (hQform ▸ haQ) (hQform ▸ hvQ')
    rw [← hQform, heq] at hh
    exact hh
  have hPAP : ∃ l : ℕ∞, (P : Set ℕ).IsAPOfLength l := by
    rw [hPform]
    exact ⟨_, natAP_isAP hd⟩
  have hunion := isAP_union_of_consecutive hPAP ⟨l, hl⟩ hconP hconQ
  have heqUnion := hmax (P ∪ Q) (Finset.subset_union_left) (Finset.union_subset hPS hQS) hunion
  exact heqUnion ▸ Finset.subset_union_right

theorem core_remainder_private_of_long_overlap {N a b d k K : ℕ}
    {F : Finset (Finset ℕ)} {S T P : Finset ℕ}
    (hF : Erdos272.IsArithInterSet N F) (hS : S ∈ F) (hT : T ∈ F) (hne : S ≠ T)
    (hd : 0 < d) (hPform : P = natAP b d k) (hPS : P ⊆ S)
    (hlongP : natAP a d (K+1) ⊆ P) (hlongT : natAP a d (K+1) ⊆ T)
    (hsmall : (S \ P).card < K)
    (hmax : ∀ U : Finset ℕ, P ⊆ U → U ⊆ S →
      (∃ l : ℕ∞, (U : Set ℕ).IsAPOfLength l) → U = P) :
    Disjoint (S \ P) T := by
  obtain ⟨l, hl, hAP⟩ := hF.2 hS hT hne
  have hlong : natAP a d (K+1) ⊆ P ∩ (S ∩ T) := by
    intro x hx
    exact Finset.mem_inter.mpr ⟨hlongP hx, Finset.mem_inter.mpr ⟨hPS (hlongP hx), hlongT hx⟩⟩
  have hsub := AP_subset_core_of_long_overlap hd hPform hPS Finset.inter_subset_left
    ⟨l, hAP⟩ hlong hsmall hmax
  exact Finset.disjoint_left.mpr (fun x hxS hxT =>
    (Finset.mem_sdiff.mp hxS).2 (hsub (Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp hxS).1, hxT⟩)))

theorem common_prefix_remainders_disjoint {N a d K : ℕ} {F : Finset (Finset ℕ)}
    (hF : Erdos272.IsArithInterSet N F) (hd : 0 < d) (core : Finset ℕ → Finset ℕ)
    (hform : ∀ S ∈ F, ∃ b k, core S = natAP b d k)
    (hsub : ∀ S ∈ F, core S ⊆ S)
    (hprefix : ∀ S ∈ F, natAP a d (K+1) ⊆ core S)
    (hsmall : ∀ S ∈ F, (S \ core S).card < K)
    (hmax : ∀ S ∈ F, ∀ U : Finset ℕ, core S ⊆ U → U ⊆ S →
      (∃ l : ℕ∞, (U : Set ℕ).IsAPOfLength l) → U = core S) :
    ∀ S ∈ F, ∀ T ∈ F, S ≠ T → Disjoint (S \ core S) (T \ core T) := by
  intro S hS T hT hne
  obtain ⟨b, k, hcore⟩ := hform S hS
  have hh := core_remainder_private_of_long_overlap hF hS hT hne hd hcore (hsub S hS)
    (hprefix S hS) ((hprefix T hT).trans (hsub T hT)) (hsmall S hS) (hmax S hS)
  exact Finset.disjoint_left.mpr (fun x hx hy =>
    Finset.disjoint_left.mp hh hx (Finset.mem_sdiff.mp hy).1)

theorem crooked_disjoint_remainders_card_le {N : ℕ} {F : Finset (Finset ℕ)}
    (hF : Erdos272.IsArithInterSet N F) (core : Finset ℕ → Finset ℕ)
    (hcrooked : ∀ S ∈ F, IsCrooked S)
    (hAP : ∀ S ∈ F, ∃ l : ℕ∞, (core S : Set ℕ).IsAPOfLength l)
    (hsub : ∀ S ∈ F, core S ⊆ S)
    (hdisj : ∀ S ∈ F, ∀ T ∈ F, S ≠ T → Disjoint (S \ core S) (T \ core T)) :
    F.card ≤ N := by
  have hhit : ∀ S ∈ F, ((S \ core S) ∩ Finset.Icc 1 N).Nonempty := by
    intro S hS
    have hne : (S \ core S).Nonempty := by
      by_contra hn
      have hSP : S ⊆ core S := by
        intro x hx
        by_contra hxp
        exact hn ⟨x, Finset.mem_sdiff.mpr ⟨hx, hxp⟩⟩
      have heq := Finset.Subset.antisymm hSP (hsub S hS)
      exact hcrooked S hS (by rw [heq]; exact hAP S hS)
    obtain ⟨x, hx⟩ := hne
    exact ⟨x, Finset.mem_inter.mpr ⟨hx, Finset.mem_powerset.mp (hF.1 hS) (Finset.mem_sdiff.mp hx).1⟩⟩
  simpa only [Nat.card_Icc, Nat.add_sub_cancel] using
    disjoint_pieces_hit_bound F (fun S => S \ core S) (Finset.Icc 1 N) hdisj hhit

end
/- CoreWindows -/

/- Uniform lattice windows for nearly full AP cores with nearby starting points. -/

section
open Finset

def apStartCode (d K a : ℕ) : ℕ × ℕ := (a % d, (a / d) / K)

def coreWindow (d K : ℕ) (q : ℕ × ℕ) : Finset ℕ :=
  natAP (q.1 + q.2*K*d) d (65*K)

def coreWindowPrefix (d K : ℕ) (q : ℕ × ℕ) : Finset ℕ :=
  natAP (q.1 + (q.2+1)*K*d) d (K+1)

theorem ap_start_decomposition {d K a : ℕ} (hK : 0 < K) :
    ∃ j < K, a = (apStartCode d K a).1 + ((apStartCode d K a).2*K+j)*d := by
  refine ⟨(a/d)%K, Nat.mod_lt _ hK, ?_⟩
  have h1 := Nat.mod_add_div a d
  have h2 := Nat.mod_add_div (a/d) K
  dsimp [apStartCode]
  nlinarith only [h1, congrArg (fun n => n*d) h2]

theorem natAP_subset_coreWindow {a d k K : ℕ} (hK : 0 < K) (hk : k ≤ 64*K) :
    natAP a d k ⊆ coreWindow d K (apStartCode d K a) := by
  obtain ⟨j, hj, ha⟩ := ap_start_decomposition (a := a) (d := d) hK
  intro x hx
  obtain ⟨i, hi, rfl⟩ := mem_natAP.mp hx
  apply mem_natAP.mpr
  refine ⟨j+i, by omega, ?_⟩
  nlinarith only [ha]

theorem coreWindowPrefix_subset_natAP {a d k K : ℕ} (hK : 0 < K) (hk : 2*K+1 ≤ k) :
    coreWindowPrefix d K (apStartCode d K a) ⊆ natAP a d k := by
  obtain ⟨j, hj, ha⟩ := ap_start_decomposition (a := a) (d := d) hK
  intro x hx
  obtain ⟨i, hi, rfl⟩ := mem_natAP.mp hx
  apply mem_natAP.mpr
  refine ⟨K-j+i, by omega, ?_⟩
  have hsum : K-j+j = K := by omega
  nlinarith only [ha, congrArg (fun n => n*d) hsum]

theorem card_coreWindow {d K : ℕ} (hd : 0 < d) (q : ℕ × ℕ) :
    (coreWindow d K q).card = 65*K := card_natAP hd

theorem coreWindow_inter_code_bounds {d K : ℕ} {q r : ℕ × ℕ}
    (hd : 0 < d) (hK : 0 < K) (hq : q.1 < d) (hr : r.1 < d)
    (hinter : (coreWindow d K q ∩ coreWindow d K r).Nonempty) :
    q.1 = r.1 ∧ q.2 ≤ r.2+65 ∧ r.2 ≤ q.2+65 := by
  obtain ⟨x, hx⟩ := hinter
  obtain ⟨hxq, hxr⟩ := Finset.mem_inter.mp hx
  obtain ⟨i, hi, hix⟩ := mem_natAP.mp hxq
  obtain ⟨j, hj, hjx⟩ := mem_natAP.mp hxr
  change q.1 + q.2*K*d + i*d = x at hix
  change r.1 + r.2*K*d + j*d = x at hjx
  have hres : q.1 = r.1 := by
    have hmod := congrArg (fun n => n % d) (hix.trans hjx.symm)
    simpa only [Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt hq, Nat.mod_eq_of_lt hr] using hmod
  have hindex : q.2*K+i = r.2*K+j := by
    rw [hres] at hix
    nlinarith only [hix, hjx, hd]
  refine ⟨hres, ?_, ?_⟩
  · by_contra hn
    have hh : r.2+65 < q.2 := by omega
    have hm := Nat.mul_le_mul_right K (by omega : r.2+66 ≤ q.2)
    nlinarith only [hm, hindex, hj, hK]
  · by_contra hn
    have hm := Nat.mul_le_mul_right K (by omega : q.2+66 ≤ r.2)
    nlinarith only [hm, hindex, hi, hK]

def startCodePool (N d K : ℕ) : Finset (ℕ × ℕ) :=
  Finset.range d ×ˢ Finset.range (N/(K*d)+1)

theorem apStartCode_mem_pool {N d K a : ℕ} (hd : 0 < d) (hK : 0 < K) (ha : a ≤ N) :
    apStartCode d K a ∈ startCodePool N d K := by
  refine Finset.mem_product.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ hd), ?_⟩
  apply Finset.mem_range.mpr
  change (a/d)/K < N/(K*d)+1
  rw [Nat.div_div_eq_div_mul]
  simpa only [Nat.mul_comm d K] using Nat.lt_succ_of_le (Nat.div_le_div_right ha)

theorem startCodePool_card_mul_le {N d K : ℕ} (hd : 0 < d) (hK : 0 < K) (hdN : d*K ≤ N) :
    (startCodePool N d K).card * K ≤ 2*N := by
  have hh := Nat.div_mul_le_self N (K*d)
  simp only [startCodePool, Finset.card_product, Finset.card_range]
  nlinarith only [hh, hdN]

end
/- WindowClassCount -/

/- Only a bounded number of lattice-window classes can be large. -/

section
open Finset

theorem window_class_sum_card_le {N d K : ℕ} {B : Finset (ℕ × ℕ)}
    (hd : 0 < d) (hK : 0 < K) (hdN : d*K ≤ N)
    (hB : B ⊆ startCodePool N d K)
    (family : (ℕ × ℕ) → Finset (Finset ℕ)) (core : Finset ℕ → Finset ℕ)
    (hcore : ∀ q ∈ B, ∀ S ∈ family q, core S ⊆ coreWindow d K q)
    (hdisj : ∀ q ∈ B, ∀ S ∈ family q, ∀ T ∈ family q,
      S ≠ T → Disjoint (S \ core S) (T \ core T))
    (hcross : ∀ q ∈ B, ∀ r ∈ B, ∀ S ∈ family q, ∀ T ∈ family r, (S ∩ T).Nonempty)
    (hsmall : ∀ q ∈ B, ∀ S ∈ family q, S.card ≤ 64*K)
    (hlinear : ∀ q ∈ B, (family q).card ≤ N) :
    (∑ q ∈ B, (family q).card) ≤ 261*N := by
  classical
  let H := B.filter (fun q => 65*K < (family q).card)
  have hHB : H ⊆ B := Finset.filter_subset _ _
  have hHcard : H.card ≤ 131 := by
    rcases H.eq_empty_or_nonempty with hzero | hne
    · simp [hzero]
    obtain ⟨q₀, hq₀⟩ := hne
    have hq₀B := hHB hq₀
    have hq₀large := (Finset.mem_filter.mp hq₀).2
    have hbound : ∀ q ∈ H, q.1 = q₀.1 ∧ q.2 ≤ q₀.2+65 ∧ q₀.2 ≤ q.2+65 := by
      intro q hq
      have hqB := hHB hq
      have hqLarge := (Finset.mem_filter.mp hq).2
      have hinter := heavy_core_pools_intersect core (hcore q hqB) (hcore q₀ hq₀B)
        (hdisj q hqB) (hdisj q₀ hq₀B) (hcross q hqB q₀ hq₀B) (hsmall q₀ hq₀B)
        (by omega : 64*K < (family q).card)
        (by simpa only [card_coreWindow hd] using hq₀large)
      exact coreWindow_inter_code_bounds hd hK
        (Finset.mem_range.mp (Finset.mem_product.mp (hB hqB)).1)
        (Finset.mem_range.mp (Finset.mem_product.mp (hB hq₀B)).1) hinter
    have hmaps : Set.MapsTo Prod.snd (H : Set (ℕ × ℕ))
        (Finset.Icc (q₀.2-65) (q₀.2+65) : Set ℕ) := by
      intro q hq
      have hh := hbound q hq
      exact Finset.mem_Icc.mpr ⟨by omega, hh.2.1⟩
    have hinj : Set.InjOn Prod.snd (H : Set (ℕ × ℕ)) := by
      intro q hq r hr heq
      exact Prod.ext ((hbound q hq).1.trans (hbound r hr).1.symm) heq
    have hh := Finset.card_le_card_of_injOn Prod.snd hmaps hinj
    rw [Nat.card_Icc] at hh
    omega
  have hlight : ∑ q ∈ B \ H, (family q).card ≤ B.card * (65*K) := by
    have hh : ∑ q ∈ B \ H, (family q).card ≤ (B \ H).card * (65*K) := by
      have hpoint : ∀ q ∈ B \ H, (family q).card ≤ 65*K := by
        intro q hq
        obtain ⟨hqB, hqH⟩ := Finset.mem_sdiff.mp hq
        have hnot : ¬ 65*K < (family q).card := fun hn => hqH (Finset.mem_filter.mpr ⟨hqB, hn⟩)
        omega
      simpa only [Finset.sum_const, smul_eq_mul] using Finset.sum_le_sum hpoint
    exact hh.trans (Nat.mul_le_mul_right _ (Finset.card_le_card Finset.sdiff_subset))
  have hheavy : ∑ q ∈ H, (family q).card ≤ 131*N := by
    have hh : ∑ q ∈ H, (family q).card ≤ H.card*N := by
      simpa only [Finset.sum_const, smul_eq_mul] using
        Finset.sum_le_sum (fun q hq => hlinear q (hHB hq))
    exact hh.trans (Nat.mul_le_mul_right N hHcard)
  have hpartition := Finset.sum_sdiff hHB (f := fun q => (family q).card)
  have hpool := startCodePool_card_mul_le hd hK hdN
  have hBsize := (Nat.mul_le_mul_right K (Finset.card_le_card hB)).trans hpool
  have hlight' : ∑ q ∈ B \ H, (family q).card ≤ 130*N := by
    have hh := Nat.mul_le_mul_left 65 hBsize
    nlinarith only [hlight, hh]
  omega

end
/- NearAPCount -/

/- A linear bound per common difference for families with nearly full maximal AP cores. -/

section
open Finset

theorem nearAP_same_step_card_le {N d K : ℕ} {F : Finset (Finset ℕ)}
    (hF : Erdos272.IsArithInterSet N F) (hd : 0 < d) (hK : 0 < K)
    (start length : Finset ℕ → ℕ)
    (hcrooked : ∀ S ∈ F, IsCrooked S)
    (hcard : ∀ S ∈ F, S.card ≤ 64*K)
    (hsub : ∀ S ∈ F, natAP (start S) d (length S) ⊆ S)
    (hlow : ∀ S ∈ F, 2*K+1 ≤ length S)
    (hhigh : ∀ S ∈ F, length S ≤ 64*K)
    (hsmall : ∀ S ∈ F, (S \ natAP (start S) d (length S)).card < K)
    (hmax : ∀ S ∈ F, ∀ U : Finset ℕ, natAP (start S) d (length S) ⊆ U → U ⊆ S →
      (∃ l : ℕ∞, (U : Set ℕ).IsAPOfLength l) → U = natAP (start S) d (length S)) :
    F.card ≤ 261*N := by
  classical
  rcases F.eq_empty_or_nonempty with hzero | hne
  · simp [hzero]
  let core : Finset ℕ → Finset ℕ := fun S => natAP (start S) d (length S)
  let code : Finset ℕ → ℕ × ℕ := fun S => apStartCode d K (start S)
  let B := startCodePool N d K
  let family : (ℕ × ℕ) → Finset (Finset ℕ) := fun q => F.filter (fun S => code S = q)
  have hstartN : ∀ S ∈ F, start S ≤ N := by
    intro S hS
    have hlen := hlow S hS
    have ha : start S ∈ S := hsub S hS (mem_natAP.mpr ⟨0, by omega, by simp⟩)
    exact (Finset.mem_Icc.mp (Finset.mem_powerset.mp (hF.1 hS) ha)).2
  have hdN : d*K ≤ N := by
    obtain ⟨S, hS⟩ := hne
    have hlen := hlow S hS
    have hx : start S + K*d ∈ S := hsub S hS (mem_natAP.mpr ⟨K, by omega, rfl⟩)
    have hh := (Finset.mem_Icc.mp (Finset.mem_powerset.mp (hF.1 hS) hx)).2
    nlinarith only [hh]
  have hfamilySub : ∀ q, family q ⊆ F := fun q => Finset.filter_subset _ _
  have hprefix : ∀ q, ∀ S ∈ family q, coreWindowPrefix d K q ⊆ core S := by
    intro q S hS
    have hSF := hfamilySub q hS
    have heq := (Finset.mem_filter.mp hS).2
    have hh := coreWindowPrefix_subset_natAP (a := start S) (d := d) hK (hlow S hSF)
    change code S = q at heq
    change coreWindowPrefix d K (code S) ⊆ core S at hh
    simpa only [heq] using hh
  have hdisj : ∀ q, ∀ S ∈ family q, ∀ T ∈ family q,
      S ≠ T → Disjoint (S \ core S) (T \ core T) := by
    intro q
    apply common_prefix_remainders_disjoint (arithInterSet_mono hF (hfamilySub q)) hd core
      (fun S _ => ⟨start S, length S, rfl⟩)
      (fun S hS => hsub S (hfamilySub q hS))
      (hprefix q) (fun S hS => hsmall S (hfamilySub q hS))
      (fun S hS => hmax S (hfamilySub q hS))
  have hlinear : ∀ q, (family q).card ≤ N := by
    intro q
    exact crooked_disjoint_remainders_card_le (arithInterSet_mono hF (hfamilySub q)) core
      (fun S hS => hcrooked S (hfamilySub q hS))
      (fun S _ => ⟨_, natAP_isAP hd⟩)
      (fun S hS => hsub S (hfamilySub q hS)) (hdisj q)
  have hsum := window_class_sum_card_le (B := B) hd hK hdN (Finset.Subset.refl _)
    family core
    (by
      intro q hq S hS
      have hh := natAP_subset_coreWindow (a := start S) (d := d) hK (hhigh S (hfamilySub q hS))
      have heq := (Finset.mem_filter.mp hS).2
      change code S = q at heq
      change core S ⊆ coreWindow d K (code S) at hh
      simpa only [heq] using hh)
    (fun q _ => hdisj q)
    (by
      intro q hq r hr S hS T hT
      have hSF := hfamilySub q hS
      have hTF := hfamilySub r hT
      have hSne : S.Nonempty := Finset.card_pos.mp (by
        have hh := (hcrooked S hSF).card_three_le
        omega)
      exact arithInter_inter_nonempty hF hSF hTF hSne)
    (fun q _ S hS => hcard S (hfamilySub q hS)) (fun q _ => hlinear q)
  have hmaps : ∀ S ∈ F, code S ∈ B := fun S hS => apStartCode_mem_pool hd hK (hstartN S hS)
  have hpartition : F.card = ∑ q ∈ B, (family q).card := Finset.card_eq_sum_card_fiberwise hmaps
  rw [hpartition]
  exact hsum

theorem nearAP_family_card_mul_le {N K : ℕ} {F : Finset (Finset ℕ)}
    (hF : Erdos272.IsArithInterSet N F) (hK : 0 < K)
    (start step length : Finset ℕ → ℕ)
    (hcrooked : ∀ S ∈ F, IsCrooked S)
    (hcard : ∀ S ∈ F, S.card ≤ 64*K)
    (hstep : ∀ S ∈ F, 0 < step S)
    (hsub : ∀ S ∈ F, natAP (start S) (step S) (length S) ⊆ S)
    (hlow : ∀ S ∈ F, 2*K+1 ≤ length S)
    (hhigh : ∀ S ∈ F, length S ≤ 64*K)
    (hsmall : ∀ S ∈ F, (S \ natAP (start S) (step S) (length S)).card < K)
    (hmax : ∀ S ∈ F, ∀ U : Finset ℕ, natAP (start S) (step S) (length S) ⊆ U → U ⊆ S →
      (∃ l : ℕ∞, (U : Set ℕ).IsAPOfLength l) → U = natAP (start S) (step S) (length S)) :
    F.card*K ≤ 261*N^2 := by
  classical
  let family : ℕ → Finset (Finset ℕ) := fun d => F.filter (fun S => step S = d)
  have hfamilySub : ∀ d, family d ⊆ F := fun d => Finset.filter_subset _ _
  have hmaps : ∀ S ∈ F, step S ∈ Finset.Icc 1 (N/K) := by
    intro S hS
    have hlen := hlow S hS
    have hx : start S + K*step S ∈ S := hsub S hS (mem_natAP.mpr ⟨K, by omega, rfl⟩)
    have hxN := (Finset.mem_Icc.mp (Finset.mem_powerset.mp (hF.1 hS) hx)).2
    refine Finset.mem_Icc.mpr ⟨hstep S hS, (Nat.le_div_iff_mul_le hK).mpr ?_⟩
    nlinarith only [hxN]
  have hbound : ∀ d ∈ Finset.Icc 1 (N/K), (family d).card ≤ 261*N := by
    intro d hd
    apply nearAP_same_step_card_le (arithInterSet_mono hF (hfamilySub d))
      (Finset.mem_Icc.mp hd).1 hK start length
      (fun S hS => hcrooked S (hfamilySub d hS))
      (fun S hS => hcard S (hfamilySub d hS))
    · intro S hS
      have hh := hsub S (hfamilySub d hS)
      simpa only [(Finset.mem_filter.mp hS).2] using hh
    · exact fun S hS => hlow S (hfamilySub d hS)
    · exact fun S hS => hhigh S (hfamilySub d hS)
    · intro S hS
      have hh := hsmall S (hfamilySub d hS)
      simpa only [(Finset.mem_filter.mp hS).2] using hh
    · intro S hS
      have hh := hmax S (hfamilySub d hS)
      simpa only [(Finset.mem_filter.mp hS).2] using hh
  have hsum := Finset.sum_le_sum hbound
  simp only [Finset.sum_const, smul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel] at hsum
  have hpartition : F.card = ∑ d ∈ Finset.Icc 1 (N/K), (family d).card :=
    Finset.card_eq_sum_card_fiberwise hmaps
  rw [← hpartition] at hsum
  have hm := Nat.mul_le_mul_right K hsum
  have hdiv := Nat.mul_le_mul_left (261*N) (Nat.div_mul_le_self N K)
  nlinarith only [hm, hdiv]

end
/- MediumCrooked -/

/- A quantitative bound for crooked members in one size band. -/

section
open Finset

def HasNearAPCore (K : ℕ) (S : Finset ℕ) : Prop :=
  ∃ P : Finset ℕ, P ⊆ S ∧ (∃ l : ℕ∞, (P : Set ℕ).IsAPOfLength l) ∧
    2*K+1 ≤ P.card ∧ (S \ P).card < K ∧
    ∀ U : Finset ℕ, P ⊆ U → U ⊆ S → (∃ l : ℕ∞, (U : Set ℕ).IsAPOfLength l) → U = P

theorem hasNearAPCore_of_approximation {K : ℕ} {S U : Finset ℕ}
    (hcard : 16*K+1 ≤ S.card) (hUS : U ⊆ S)
    (hAP : ∃ l : ℕ∞, (U : Set ℕ).IsAPOfLength l) (hsmall : (S \ U).card < K) :
    HasNearAPCore K S := by
  obtain ⟨P, hUP, hPS, hPAP, hmax⟩ := exists_maximal_AP_extension hUS hAP
  have hdiff : S \ P ⊆ S \ U := by
    intro x hx
    obtain ⟨hxS, hxP⟩ := Finset.mem_sdiff.mp hx
    exact Finset.mem_sdiff.mpr ⟨hxS, fun hxU => hxP (hUP hxU)⟩
  have hPsmall := (Finset.card_le_card hdiff).trans_lt hsmall
  refine ⟨P, hPS, hPAP, ?_, hPsmall, hmax⟩
  have hh := Finset.card_sdiff_add_card_eq_card hPS
  omega

theorem nearAP_core_family_card_mul_le {N K : ℕ} {F : Finset (Finset ℕ)}
    (hF : Erdos272.IsArithInterSet N F) (hK : 0 < K)
    (hcrooked : ∀ S ∈ F, IsCrooked S) (hcard : ∀ S ∈ F, S.card ≤ 64*K)
    (hnear : ∀ S ∈ F, HasNearAPCore K S) : F.card*K ≤ 261*N^2 := by
  classical
  have hex : ∀ S : Finset ℕ, ∃ a d k : ℕ, S ∈ F →
      0 < d ∧ natAP a d k ⊆ S ∧ 2*K+1 ≤ k ∧ k ≤ 64*K ∧ (S \ natAP a d k).card < K ∧
      ∀ U : Finset ℕ, natAP a d k ⊆ U → U ⊆ S →
        (∃ l : ℕ∞, (U : Set ℕ).IsAPOfLength l) → U = natAP a d k := by
    intro S
    by_cases hS : S ∈ F
    · obtain ⟨P, hPS, ⟨l, hl⟩, hPlow, hPsmall, hPmax⟩ := hnear S hS
      obtain ⟨a, d, hd, hrep⟩ := nat_ap_eq_natAP hl (by omega)
      refine ⟨a, d, P.card, fun _ => ⟨hd, ?_, hPlow,
        (Finset.card_le_card hPS).trans (hcard S hS), ?_, ?_⟩⟩
      · simpa only [← hrep] using hPS
      · simpa only [← hrep] using hPsmall
      · simpa only [← hrep] using hPmax
    · exact ⟨0, 1, 0, fun hh => False.elim (hS hh)⟩
  choose start step length hspec using hex
  exact nearAP_family_card_mul_le hF hK start step length hcrooked hcard
    (fun S hS => (hspec S hS).1)
    (fun S hS => (hspec S hS).2.1)
    (fun S hS => (hspec S hS).2.2.1)
    (fun S hS => (hspec S hS).2.2.2.1)
    (fun S hS => (hspec S hS).2.2.2.2.1)
    (fun S hS => (hspec S hS).2.2.2.2.2)

theorem crooked_size_band_card_mul_le {N D K : ℕ} {F : Finset (Finset ℕ)}
    (hF : Erdos272.IsArithInterSet N F) (hK : 0 < K)
    (hcrooked : ∀ S ∈ F, IsCrooked S)
    (hlow : ∀ S ∈ F, 16*K+1 ≤ S.card)
    (hhigh : ∀ S ∈ F, S.card ≤ 64*K)
    (hdivisor : ∀ m ≤ N^2, m.divisors.card ≤ D)
    (hsize : 16 * (Nat.log 2 N + 1) * D^2 + D ≤ K) :
    F.card*K ≤ 600 * (Nat.log 2 N + 1) * N^2 := by
  classical
  rcases F.eq_empty_or_nonempty with hzero | hne
  · simp [hzero]
  obtain ⟨R, hR⟩ := hne
  let A := F.filter (HasNearAPCore K)
  let B := F.filter (fun S => ¬ HasNearAPCore K S)
  have hAF : A ⊆ F := Finset.filter_subset _ _
  have hBF : B ⊆ F := Finset.filter_subset _ _
  have hnear := nearAP_core_family_card_mul_le (arithInterSet_mono hF hAF) hK
    (fun S hS => hcrooked S (hAF hS)) (fun S hS => hhigh S (hAF hS))
    (fun S hS => (Finset.mem_filter.mp hS).2)
  have hfar : ∀ S ∈ B, ∀ U ⊆ S, (∃ l : ℕ∞, (U : Set ℕ).IsAPOfLength l) → K ≤ (S \ U).card := by
    intro S hS U hUS hAP
    by_contra hn
    exact (Finset.mem_filter.mp hS).2
      (hasNearAPCore_of_approximation (hlow S (hBF hS)) hUS hAP (by omega))
  have hhit : ∀ S ∈ B, (S ∩ R).Nonempty := by
    intro S hS
    have hSne : S.Nonempty := Finset.card_pos.mp (by
      have hh := (hcrooked S (hBF hS)).card_three_le
      omega)
    exact arithInter_inter_nonempty hF (hBF hS) hR hSne
  have hfarBound := far_from_AP_family_card_le (arithInterSet_mono hF hBF) hK
    (fun S hS => hlow S (hBF hS)) hdivisor hsize (Nat.le_refl K) hhit hfar
  have hRcard := hhigh R hR
  have hchoose : N.choose 2 ≤ N^2 := Nat.choose_le_pow N 2
  have hprod := Nat.mul_le_mul hRcard hchoose
  have hmul := Nat.mul_le_mul_left (4 * (Nat.log 2 N + 1)) hprod
  have hfarFull : (B.card*K)*K ≤ (256 * (Nat.log 2 N + 1) * N^2)*K := by
    nlinarith only [hfarBound, hmul]
  have hfarFinal := Nat.le_of_mul_le_mul_right hfarFull hK
  have hpartition := Finset.card_filter_add_card_filter_not (s := F) (HasNearAPCore K)
  change A.card + B.card = F.card at hpartition
  have hsum : A.card*K + B.card*K = F.card*K := by rw [← Nat.add_mul, hpartition]
  have hlog : 1 ≤ Nat.log 2 N + 1 := by omega
  have hm := Nat.mul_le_mul_right (261*N^2) hlog
  nlinarith only [hnear, hfarFinal, hsum, hm, Nat.zero_le ((Nat.log 2 N + 1) * N^2)]

end
/- LargeCrooked -/

/- Summing size bands bounds every crooked member above a fixed cutoff. -/

section
open Finset

theorem large_crooked_card_mul_le_reciprocal {N D K : ℕ} {F : Finset (Finset ℕ)}
    (hF : Erdos272.IsArithInterSet N F) (hK : 0 < K)
    (hcrooked : ∀ S ∈ F, IsCrooked S)
    (hlow : ∀ S ∈ F, 16*K+1 ≤ S.card)
    (hdivisor : ∀ m ≤ N^2, m.divisors.card ≤ D)
    (hsize : 16 * (Nat.log 2 N + 1) * D^2 + D ≤ K) :
    (F.card : ℝ)*K ≤ 600 * (Nat.log 2 N + 1 : ℕ) * (N : ℝ)^2 * reciprocalSum N := by
  classical
  let level : Finset ℕ → ℕ := fun S => (S.card-1)/(16*K)
  let family : ℕ → Finset (Finset ℕ) := fun j => F.filter (fun S => level S = j)
  have hfamilySub : ∀ j, family j ⊆ F := fun j => Finset.filter_subset _ _
  have hmaps : ∀ S ∈ F, level S ∈ Finset.Icc 1 N := by
    intro S hS
    have hmin := hlow S hS
    have hScard : S.card ≤ N := by
      simpa only [Nat.card_Icc, Nat.add_sub_cancel] using
        Finset.card_le_card (Finset.mem_powerset.mp (hF.1 hS))
    refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
    · dsimp [level]
      apply (Nat.le_div_iff_mul_le (by positivity : 0 < 16*K)).mpr
      omega
    · exact (Nat.div_le_self _ _).trans (by omega)
  have hband : ∀ j ∈ Finset.Icc 1 N,
      (family j).card * (j*K) ≤ 600 * (Nat.log 2 N + 1) * N^2 := by
    intro j hj
    have hj1 := (Finset.mem_Icc.mp hj).1
    have hscale : K ≤ j*K := by nlinarith only [hj1]
    apply crooked_size_band_card_mul_le (arithInterSet_mono hF (hfamilySub j))
      (by positivity) (fun S hS => hcrooked S (hfamilySub j hS))
    · intro S hS
      have hlevel : level S = j := (Finset.mem_filter.mp hS).2
      have hprod := Nat.div_mul_le_self (S.card-1) (16*K)
      change level S * (16*K) ≤ S.card-1 at hprod
      rw [hlevel] at hprod
      have hpos := hlow S (hfamilySub j hS)
      have hsubeq : S.card-1+1 = S.card := by omega
      nlinarith only [hprod, hsubeq]
    · intro S hS
      have hlevel : level S = j := (Finset.mem_filter.mp hS).2
      have hquot : (S.card-1)/(16*K) < j+1 := by change level S < j+1; omega
      have hupper := (Nat.div_lt_iff_lt_mul (by positivity : 0 < 16*K)).mp hquot
      have hpos := hlow S (hfamilySub j hS)
      have hsubeq : S.card-1+1 = S.card := by omega
      nlinarith only [hupper, hscale, hsubeq]
    · exact hdivisor
    · exact hsize.trans hscale
  have hrow : ∀ j ∈ Finset.Icc 1 N,
      ((family j).card : ℝ)*K ≤
        (600 * (Nat.log 2 N + 1 : ℕ) * (N : ℝ)^2) * (j : ℝ)⁻¹ := by
    intro j hj
    have hjpos : (0 : ℝ) < j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
    have hh : ((family j).card : ℝ) * ((j : ℝ)*K) ≤
        600 * (Nat.log 2 N + 1 : ℕ) * (N : ℝ)^2 := by exact_mod_cast hband j hj
    rw [← div_eq_mul_inv]
    apply (le_div_iff₀ hjpos).mpr
    nlinarith only [hh]
  have hpartition : F.card = ∑ j ∈ Finset.Icc 1 N, (family j).card :=
    Finset.card_eq_sum_card_fiberwise hmaps
  have hsum := Finset.sum_le_sum hrow
  have hleft : (∑ j ∈ Finset.Icc 1 N, ((family j).card : ℝ)*K) = (F.card : ℝ)*K := by
    rw [← Finset.sum_mul, ← Nat.cast_sum, ← hpartition]
  rw [hleft, ← Finset.mul_sum] at hsum
  exact hsum

theorem large_crooked_card_mul_le {N D K : ℕ} {F : Finset (Finset ℕ)}
    (hF : Erdos272.IsArithInterSet N F) (hK : 0 < K)
    (hcrooked : ∀ S ∈ F, IsCrooked S)
    (hlow : ∀ S ∈ F, 16*K+1 ≤ S.card)
    (hdivisor : ∀ m ≤ N^2, m.divisors.card ≤ D)
    (hsize : 16 * (Nat.log 2 N + 1) * D^2 + D ≤ K) :
    F.card*K ≤ 1200 * (Nat.log 2 N + 1)^2 * N^2 := by
  have hh := large_crooked_card_mul_le_reciprocal hF hK hcrooked hlow hdivisor hsize
  have hrec := reciprocalSum_le_natLog N
  have hm := mul_le_mul_of_nonneg_left hrec
    (by positivity : (0 : ℝ) ≤ 600 * (Nat.log 2 N + 1 : ℕ) * (N : ℝ)^2)
  have hb : (F.card : ℝ)*K ≤ 1200 * ((Nat.log 2 N + 1 : ℕ) : ℝ)^2 * (N : ℝ)^2 := by
    push_cast at hh hm ⊢
    nlinarith only [hh, hm]
  exact_mod_cast hb

theorem crooked_no_common_point_card_mul_le {N D K s : ℕ} {F : Finset (Finset ℕ)}
    (hF : Erdos272.IsArithInterSet N F) (hK : 0 < K)
    (hcrooked : ∀ S ∈ F, IsCrooked S) (hbound : ∀ S ∈ F, S.card ≤ s)
    (hno : ∀ c ∈ Finset.Icc 1 N, ∃ T ∈ F, c ∉ T)
    (hdivisor : ∀ m ≤ N^2, m.divisors.card ≤ D)
    (hsize : 16 * (Nat.log 2 N + 1) * D^2 + D ≤ K) :
    F.card*K ≤
      (s*N + 4*(16*K)^2*N + (32*K+1)*(48*N*(Nat.log 2 N + 1)^3))*K +
        1200 * (Nat.log 2 N + 1)^2 * N^2 := by
  classical
  let A := F.filter (fun S => S.card ≤ 16*K)
  let B := F.filter (fun S => ¬ S.card ≤ 16*K)
  have hAF : A ⊆ F := Finset.filter_subset _ _
  have hBF : B ⊆ F := Finset.filter_subset _ _
  have hsmall := small_crooked_no_common_point_card_le hF hAF
    (fun S hS => hcrooked S (hAF hS)) (fun S hS => (Finset.mem_filter.mp hS).2) hbound hno
  have hsmall' := Nat.mul_le_mul_right K hsmall
  have hlarge := large_crooked_card_mul_le (arithInterSet_mono hF hBF) hK
    (fun S hS => hcrooked S (hBF hS))
    (fun S hS => by have hh := (Finset.mem_filter.mp hS).2; omega) hdivisor hsize
  have hpartition := Finset.card_filter_add_card_filter_not (s := F) (fun S => S.card ≤ 16*K)
  change A.card + B.card = F.card at hpartition
  have hmul : A.card*K + B.card*K = F.card*K := by rw [← Nat.add_mul, hpartition]
  nlinarith only [hsmall', hlarge, hmul]

end
/- StructuralCutoff -/

/- A fourth-root cutoff makes every structural error subquadratic. -/

section
open Finset Filter

def structuralCutoff (N : ℕ) : ℕ := Nat.sqrt (Nat.sqrt N)

theorem structuralCutoff_fourth_le (N : ℕ) : (structuralCutoff N)^4 ≤ N := by
  have h1 := Nat.sqrt_le' (Nat.sqrt N)
  have h2 := Nat.sqrt_le' N
  have hh := (Nat.pow_le_pow_left h1 2).trans h2
  simpa only [structuralCutoff, ← pow_mul] using hh

theorem le_structuralCutoff_of_fourth_le {a N : ℕ} (ha : a^4 ≤ N) : a ≤ structuralCutoff N := by
  apply Nat.le_sqrt'.mpr
  apply Nat.le_sqrt'.mpr
  simpa only [← pow_mul] using ha

theorem eventually_log_cube_le_structuralCutoff (C : ℕ) :
    ∀ᶠ N : ℕ in atTop, C*(Nat.log 2 N + 1)^3 ≤ structuralCutoff N := by
  filter_upwards [eventually_natLog_pow_le 24, Filter.eventually_ge_atTop (C^8)] with N hlog hN
  have hpow : (C*(Nat.log 2 N + 1)^3)^8 ≤ N^2 := by
    calc
      (C*(Nat.log 2 N + 1)^3)^8 = C^8 * (Nat.log 2 N + 1)^24 := by ring
      _ ≤ C^8*N := Nat.mul_le_mul_left _ hlog
      _ ≤ N*N := Nat.mul_le_mul_right _ hN
      _ = N^2 := by ring
  have hfourth : (C*(Nat.log 2 N + 1)^3)^4 ≤ N := by
    apply (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp
    simpa only [← pow_mul] using hpow
  exact le_structuralCutoff_of_fourth_le hfourth

theorem eventually_trace_threshold_le_structuralCutoff :
    ∀ᶠ N : ℕ in atTop,
      16*(Nat.log 2 N + 1)*(squareDivisorBound N)^2 + squareDivisorBound N ≤ structuralCutoff N := by
  filter_upwards [eventually_natLog_pow_le 16, eventually_squareDivisorBound_pow_le 32,
    Filter.eventually_ge_atTop (17^8)] with N hlog hdiv hN
  let L := Nat.log 2 N + 1
  let D := squareDivisorBound N
  let A := 16*L*D^2+D
  have hD : D ≤ D^2 := by nlinarith only [Nat.zero_le D]
  have hL : 1 ≤ L := by dsimp [L]; omega
  have hmul := Nat.mul_le_mul_right (D^2) hL
  have hA : A ≤ 17*L*D^2 := by dsimp [A]; nlinarith only [hD, hmul]
  have hpow : A^16 ≤ N^4 := by
    calc
      A^16 ≤ (17*L*D^2)^16 := Nat.pow_le_pow_left hA 16
      _ = 17^16 * (L^16 * D^32) := by ring
      _ ≤ 17^16 * (N*N) := Nat.mul_le_mul_left _ (Nat.mul_le_mul hlog hdiv)
      _ ≤ N^2 * (N*N) := Nat.mul_le_mul_right _ (by
        have hh := Nat.pow_le_pow_left hN 2
        simpa only [← pow_mul] using hh)
      _ = N^4 := by ring
  have hfourth : A^4 ≤ N := by
    apply (Nat.pow_le_pow_iff_left (by decide : 4 ≠ 0)).mp
    simpa only [← pow_mul] using hpow
  exact le_structuralCutoff_of_fourth_le hfourth

end
/- CrookedCommonPoint -/

/- The common-point reduction for a quadratically large sparse crooked family. -/

section
open Finset Filter

theorem structural_error_small {L K N : ℕ} (hL : 1 ≤ L)
    (hlog : 1000000000*L^3 ≤ K) (hroot : K^4 ≤ N) :
    4000 * (1024*K^3*N + (32*K+1)*48*K*N*L^3 + 1200*L^2*N^2) ≤ 3*N^2*K := by
  have hLcube : 1 ≤ L^3 := by simpa only [one_pow] using Nat.pow_le_pow_left hL 3
  have hKlarge : 1000000000 ≤ K := by
    have hh := Nat.mul_le_mul_left 1000000000 hLcube
    omega
  have hK : 1 ≤ K := by omega
  have hLL : L^2 ≤ L^3 := by
    have hh := Nat.mul_le_mul_left (L^2) hL
    nlinarith only [hh]
  have hKK : K^2 ≤ N := by
    have hk2 : 1 ≤ K^2 := by nlinarith only [hK]
    have hh := Nat.mul_le_mul_left (K^2) hk2
    nlinarith only [hh, hroot]
  have hfirstCoef : 4096000*K^2 ≤ N := by
    have hk2 : 4096000 ≤ K^2 := by nlinarith only [hKlarge]
    have hh := Nat.mul_le_mul_right (K^2) hk2
    nlinarith only [hh, hroot]
  have hsecondCoef : 6336000*L^3 ≤ K := by
    nlinarith only [hlog, Nat.zero_le (L^3)]
  have hthirdCoef : 4800000*L^2 ≤ K := by
    have hh := Nat.mul_le_mul_left 1000000000 hLL
    nlinarith only [hlog, hh, Nat.zero_le (L^2)]
  have hfirst : 4000*(1024*K^3*N) ≤ N^2*K := by
    have hh := Nat.mul_le_mul_right (K*N) hfirstCoef
    nlinarith only [hh]
  have hsecond : 4000*((32*K+1)*48*K*N*L^3) ≤ N^2*K := by
    have hrow : 32*K+1 ≤ 33*K := by omega
    have h1 := Nat.mul_le_mul_right (4000*48*K*N*L^3) hrow
    have h2 := Nat.mul_le_mul_right (K^2*N) hsecondCoef
    have h3 := Nat.mul_le_mul_right (K*N) hKK
    nlinarith only [h1, h2, h3]
  have hthird : 4000*(1200*L^2*N^2) ≤ N^2*K := by
    have hh := Nat.mul_le_mul_right (N^2) hthirdCoef
    nlinarith only [hh]
  nlinarith only [hfirst, hsecond, hthird]

theorem sparse_crooked_common_point {N D K : ℕ} {F : Finset (Finset ℕ)}
    (hN : 0 < N) (hF : Erdos272.IsArithInterSet N F)
    (hcrooked : ∀ S ∈ F, IsCrooked S)
    (hsparse : ∀ S ∈ F, 16*S.card ≤ N)
    (hlarge : N^2 ≤ 14*F.card)
    (hdivisor : ∀ m ≤ N^2, m.divisors.card ≤ D)
    (hsize : 16*(Nat.log 2 N + 1)*D^2+D ≤ K)
    (hlog : 1000000000*(Nat.log 2 N + 1)^3 ≤ K) (hroot : K^4 ≤ N) :
    ∃ c ∈ Finset.Icc 1 N, ∀ S ∈ F, c ∈ S := by
  classical
  by_contra hcommon
  push_neg at hcommon
  have hK : 0 < K := by
    have hL : 1 ≤ (Nat.log 2 N + 1)^3 := by
      simpa only [one_pow] using Nat.pow_le_pow_left (by omega : 1 ≤ Nat.log 2 N + 1) 3
    have hh := Nat.mul_le_mul_left 1000000000 hL
    omega
  have hbound : ∀ S ∈ F, S.card ≤ N/16 := by
    intro S hS
    apply (Nat.le_div_iff_mul_le (by decide : 0 < 16)).mpr
    simpa only [Nat.mul_comm S.card 16] using hsparse S hS
  have hupper := crooked_no_common_point_card_mul_le hF hK hcrooked hbound hcommon hdivisor hsize
  let L := Nat.log 2 N + 1
  let E := 1024*K^3*N + (32*K+1)*48*K*N*L^3 + 1200*L^2*N^2
  have herror : 4000*E ≤ 3*N^2*K := structural_error_small (by dsimp [L]; omega) hlog hroot
  have hupper' : F.card*K ≤ (N/16)*N*K + E := by
    dsimp [E, L]
    nlinarith only [hupper]
  have hbase : 16*((N/16)*N*K) ≤ N^2*K := by
    have hh := Nat.mul_le_mul_right (N*K) (Nat.div_mul_le_self N 16)
    nlinarith only [hh]
  have hlarge' := Nat.mul_le_mul_right K hlarge
  have hpos : 0 < N^2*K := by positivity
  nlinarith only [hupper', hbase, hlarge', herror, hpos]

theorem eventually_sparse_crooked_common_point :
    ∀ᶠ N : ℕ in atTop, ∀ F : Finset (Finset ℕ),
      Erdos272.IsArithInterSet N F → (∀ S ∈ F, IsCrooked S) →
      (∀ S ∈ F, 16*S.card ≤ N) → N^2 ≤ 14*F.card →
      ∃ c ∈ Finset.Icc 1 N, ∀ S ∈ F, c ∈ S := by
  filter_upwards [eventually_trace_threshold_le_structuralCutoff,
    eventually_log_cube_le_structuralCutoff 1000000000, Filter.eventually_ge_atTop 1] with N hsize hlog hN
  intro F hF hcrooked hsparse hlarge
  exact sparse_crooked_common_point hN hF hcrooked hsparse hlarge
    (fun m hm => divisor_card_le_squareDivisorBound hm) hsize hlog (structuralCutoff_fourth_le N)

end
/- CommonPointReduction -/

/- Removing linearly many dense crooked members leaves a common crooked root. -/

section
open Finset Filter

theorem common_crooked_reduction_of_sparse_root {N c : ℕ} {F : Finset (Finset ℕ)}
    (hN : 64 ≤ N) (hF : Erdos272.IsArithInterSet N F)
    (hroot : ∀ S ∈ sparseCrookedMembers N F, c ∈ S) :
    ∃ G : Finset (Finset ℕ), G ⊆ F ∧ Erdos272.IsArithInterSet N G ∧
      F.card ≤ G.card + 2048*N ∧ (∀ S ∈ G, IsCrooked S → c ∈ S) := by
  classical
  let D := (crookedMembers F).filter (fun S => ¬16*S.card ≤ N)
  let G := F \ D
  have hDF : D ⊆ F := by
    intro S hS
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).1
  have hdense : D.card ≤ 2048*N := by
    apply dense_crooked_card_le hN (admissible_subfamily hF hDF)
    · intro S hS
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).2
    · intro S hS
      have hh := (Finset.mem_filter.mp hS).2
      omega
  refine ⟨G, Finset.sdiff_subset, admissible_subfamily hF Finset.sdiff_subset, ?_, ?_⟩
  · exact (Finset.card_le_card_sdiff_add_card (s := F) (t := D)).trans
      (Nat.add_le_add_left hdense G.card)
  · intro S hS hcrooked
    obtain ⟨hSF, hSD⟩ := Finset.mem_sdiff.mp hS
    apply hroot S
    have hsparse : 16*S.card ≤ N := by
      by_contra hn
      exact hSD (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hSF, hcrooked⟩, hn⟩)
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hSF, hcrooked⟩, hsparse⟩

theorem eventually_common_crooked_reduction :
    ∀ᶠ N : ℕ in atTop, ∀ F : Finset (Finset ℕ),
      Erdos272.IsArithInterSet N F → (N : ℝ)^2/2 ≤ (F.card : ℝ) →
      ∃ G : Finset (Finset ℕ), G ⊆ F ∧ Erdos272.IsArithInterSet N G ∧
        F.card ≤ G.card + 2048*N ∧
        ∃ c ∈ Finset.Icc 1 N, ∀ S ∈ G, IsCrooked S → c ∈ S := by
  classical
  filter_upwards [eventually_many_sparse_crooked_members,
    eventually_sparse_crooked_common_point, Filter.eventually_ge_atTop 64]
    with N hmany hcommon hN F hF hsize
  let C := sparseCrookedMembers N F
  have hCF : C ⊆ F := by
    intro S hS
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).1
  have hcrooked : ∀ S ∈ C, IsCrooked S := by
    intro S hS
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).2
  have hsparse : ∀ S ∈ C, 16*S.card ≤ N := by
    intro S hS
    exact (Finset.mem_filter.mp hS).2
  have hlargeR : (N : ℝ)^2 ≤ 14*(C.card : ℝ) := by
    have hh := hmany F hF hsize
    change (N : ℝ)^2/14 ≤ (C.card : ℝ) at hh
    linarith only [hh]
  have hlarge : N^2 ≤ 14*C.card := by exact_mod_cast hlargeR
  obtain ⟨c, hc, hroot⟩ := hcommon C (admissible_subfamily hF hCF) hcrooked hsparse hlarge
  obtain ⟨G, hGF, hG, hcard, hGc⟩ := common_crooked_reduction_of_sparse_root hN hF hroot
  exact ⟨G, hGF, hG, hcard, c, hc, hGc⟩

end
/- MatchingModels -/

/- Progression matching retaining the progression model used in the proof. -/

section
open Finset

theorem exists_natural_progression_pair_matching_with_models {N c : ℕ} {F : Finset (Finset ℕ)}
    (hsub : ∀ S ∈ F, S ⊆ Finset.Icc 1 N)
    (hAP : ∀ S ∈ F, ∃ l : ℕ∞, (S : Set ℕ).IsAPOfLength l)
    (hcard : ∀ S ∈ F, 4 ≤ S.card) (hcenter : ∀ S ∈ F, c ∈ S) :
    ∃ f : {S // S ∈ F} → Option (ℕ × ℕ),
      (∀ S q, f S = some q → ∃ d : ℕ, 0 < d ∧ d ≤ N ∧ NaturalMatchedPair c d S.val q ∧
        ∃ p : ProgressionCell, IsCenteredModel c d p S.val) ∧
      (∀ S T q, f S = some q → f T = some q → S = T) ∧
      ((Finset.univ.filter (fun S => f S = none)).card ≤ 20000 * N) := by
  classical
  let A := {S : Finset ℕ // S ∈ F}
  have hparam : ∀ S : A, ∃ d : ℕ, 0 < d ∧ d ≤ N ∧
      ∃ p : ProgressionCell, IsCenteredModel c d p S.val := by
    intro S
    obtain ⟨l, hAPs⟩ := hAP S.val S.property
    exact exists_centered_model_bounded (hsub S.val S.property) hAPs
      (hcard S.val S.property) (hcenter S.val S.property)
  choose d hd hdN p hmodel using hparam
  obtain ⟨f, hreal, hrealinj, hexcept⟩ := exists_progression_pair_matching
  let g : A → Option (ℕ × ℕ) := fun S => (f (p S)).map (liftPair c (d S))
  have hvalid : ∀ S q, g S = some q → NaturalMatchedPair c (d S) S.val q := by
    intro S q hq
    obtain ⟨r, hr, hrq⟩ := Option.map_eq_some_iff.mp hq
    rw [← hrq]
    exact liftPair_spec (hd S) (hmodel S) (hreal (p S) r hr)
  refine ⟨g, ?_, ?_, ?_⟩
  · intro S q hq
    exact ⟨d S, hd S, hdN S, hvalid S q hq, p S, hmodel S⟩
  · intro S T q hSq hTq
    have hSvalid := hvalid S q hSq
    have hTvalid := hvalid T q hTq
    have hdST : d S = d T := hSvalid.2.2.2.2.2.1.symm.trans hTvalid.2.2.2.2.2.1
    obtain ⟨r, hr, hrq⟩ := Option.map_eq_some_iff.mp hSq
    obtain ⟨r', hr', hr'q⟩ := Option.map_eq_some_iff.mp hTq
    have hlifts : liftPair c (d T) r = liftPair c (d T) r' := by
      simpa only [hdST] using hrq.trans hr'q.symm
    have hrr' : r = r' := liftPair_injective_on_models (hd T)
      (by simpa only [hdST] using hmodel S) (hmodel T)
      (hreal (p S) r hr) (hreal (p T) r' hr') hlifts
    have hpST : p S = p T := hrealinj (p S) (p T) r hr (by simpa only [hrr'] using hr')
    apply Subtype.ext
    exact centered_model_determines_set
      (by simpa only [hdST, hpST] using hmodel S) (hmodel T)
  · let B : Finset A := Finset.univ.filter (fun S => g S = none)
    have hmaps : Set.MapsTo d (B : Set A) (Finset.Icc 1 N : Set ℕ) := by
      intro S hS
      exact Finset.mem_Icc.mpr ⟨hd S, hdN S⟩
    have hfiber : ∀ k ∈ Finset.Icc 1 N, (B.filter (fun S => d S = k)).card ≤ 20000 := by
      intro k hk
      let C := B.filter (fun S => d S = k)
      have hpinj : Set.InjOn p (C : Set A) := by
        intro S hS T hT hpST
        have hdSk : d S = k := (Finset.mem_filter.mp hS).2
        have hdTk : d T = k := (Finset.mem_filter.mp hT).2
        apply Subtype.ext
        exact centered_model_determines_set
          (by simpa only [hdSk] using hmodel S)
          (by simpa only [hdTk, ← hpST] using hmodel T)
      have hfilter : (C.image p).filter (fun q => f q = none) = C.image p := by
        apply Finset.filter_eq_self.mpr
        intro q hq
        obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hq
        have hSB : S ∈ B := (Finset.mem_filter.mp hS).1
        have hnone : g S = none := (Finset.mem_filter.mp hSB).2
        exact Option.map_eq_none_iff.mp hnone
      have hh := hexcept (C.image p)
      rw [hfilter, Finset.card_image_of_injOn hpinj] at hh
      exact hh
    change B.card ≤ 20000 * N
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    calc
      _ ≤ ∑ k ∈ Finset.Icc 1 N, 20000 := Finset.sum_le_sum hfiber
      _ = 20000 * N := by simp [Nat.mul_comm]

end
/- ModularMatching -/

/- Matching a rooted family into pairs leaving the root's residue class. -/

section
open Finset

def outsideRootResidue (N c k : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun x => ¬ Nat.ModEq k c x)

theorem centered_model_step_dvd_offset {c d x : ℕ} {p : ProgressionCell} {S : Finset ℕ}
    (hmodel : IsCenteredModel c d p S) (hx : x ∈ S) :
    (d : ℤ) ∣ (x : ℤ) - c := by
  have hxI : (x : ℤ) ∈ S.image (fun y : ℕ => (y : ℤ)) := Finset.mem_image.mpr ⟨x, hx, rfl⟩
  rw [hmodel] at hxI
  obtain ⟨z, _hz, heq⟩ := Finset.mem_image.mp hxI
  exact ⟨z, by linarith only [heq]⟩

theorem natural_matched_pair_meets_residue_complement {N c d k : ℕ}
    {p : ProgressionCell} {S : Finset ℕ} {q : ℕ × ℕ}
    (hsub : S ⊆ Finset.Icc 1 N) (hmodel : IsCenteredModel c d p S)
    (hq : NaturalMatchedPair c d S q) (hmet : (S ∩ outsideRootResidue N c k).Nonempty) :
    ¬ Disjoint ({q.1, q.2} : Finset ℕ) (outsideRootResidue N c k) := by
  intro hdis
  have hxmod : Nat.ModEq k c q.1 := by
    by_contra hh
    exact Finset.disjoint_left.mp hdis (by simp)
      (Finset.mem_filter.mpr ⟨hsub hq.1, hh⟩)
  have hymod : Nat.ModEq k c q.2 := by
    by_contra hh
    exact Finset.disjoint_left.mp hdis (by simp)
      (Finset.mem_filter.mpr ⟨hsub hq.2.1, hh⟩)
  have hkd : k ∣ d := by
    rw [← hq.2.2.2.2.2.1]
    exact Int.dvd_gcd hxmod.dvd hymod.dvd
  obtain ⟨x, hx⟩ := hmet
  obtain ⟨hxS, hxP⟩ := Finset.mem_inter.mp hx
  apply (Finset.mem_filter.mp hxP).2
  exact Nat.modEq_of_dvd ((Int.natCast_dvd_natCast.mpr hkd).trans
    (centered_model_step_dvd_offset hmodel hxS))

theorem rooted_residue_good_large_card_le {N c k : ℕ} {F : Finset (Finset ℕ)}
    (hF : Erdos272.IsArithInterSet N F) (hc : ∀ S ∈ F, c ∈ S)
    (hcard : ∀ S ∈ F, 3 ≤ S.card)
    (hmet : ∀ S ∈ F, (S ∩ outsideRootResidue N c k).Nonempty)
    (hgood : ∀ S ∈ F, IsCrooked S →
      ∃ Q, IsWitnessPair S c Q ∧ ¬ Disjoint Q (outsideRootResidue N c k)) :
    F.card ≤ (meetingPairPool N c (outsideRootResidue N c k)).card + 20000*N := by
  classical
  have hsub : ∀ S ∈ F, S ⊆ Finset.Icc 1 N :=
    fun S hS => Finset.mem_powerset.mp (hF.1 hS)
  have htriple : ∀ S ∈ F, S.card = 3 →
      ¬ Disjoint (S.erase c) (outsideRootResidue N c k) := by
    intro S hS _hcard hdis
    obtain ⟨x, hx⟩ := hmet S hS
    obtain ⟨hxS, hxP⟩ := Finset.mem_inter.mp hx
    have hxc : x ≠ c := by
      intro heq
      apply (Finset.mem_filter.mp hxP).2
      subst x
      rfl
    exact Finset.disjoint_left.mp hdis (Finset.mem_erase.mpr ⟨hxc, hxS⟩) hxP
  have hmatch : ∀ G : Finset (Finset ℕ), G ⊆ F →
      (∀ S ∈ G, ∃ l : ℕ∞, (S : Set ℕ).IsAPOfLength l) →
      (∀ S ∈ G, 4 ≤ S.card) → ∃ g : {S // S ∈ G} → Option (ℕ × ℕ),
        (∀ S q, g S = some q → ∃ d : ℕ, 0 < d ∧ d ≤ N ∧
          NaturalMatchedPair c d S.val q ∧
          ¬ Disjoint ({q.1, q.2} : Finset ℕ) (outsideRootResidue N c k)) ∧
        (∀ S T q, g S = some q → g T = some q → S = T) ∧
        (Finset.univ.filter (fun S => g S = none)).card ≤ 20000*N := by
    intro G hGF hAP hsize
    obtain ⟨g, hg, hinj, hmiss⟩ := exists_natural_progression_pair_matching_with_models
      (fun S hS => hsub S (hGF hS)) hAP hsize (fun S hS => hc S (hGF hS))
    refine ⟨g, ?_, hinj, hmiss⟩
    intro S q hq
    obtain ⟨d, hd, hdN, hnat, p, hmodel⟩ := hg S q hq
    exact ⟨d, hd, hdN, hnat, natural_matched_pair_meets_residue_complement
      (hsub S.val (hGF S.property)) hmodel hnat (hmet S.val (hGF S.property))⟩
  obtain ⟨f, hvalid, hallowed, hinj, hmiss⟩ := exists_common_point_pair_matching_allowed
    hF hc hcard hgood htriple hmatch
  have hm := partial_matching_card_le
    (B := meetingPairPool N c (outsideRootResidue N c k)) f
    (fun S Q hQ => Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨?_, (hvalid S Q hQ).1⟩,
      hallowed S Q hQ⟩) hinj hmiss
  · simpa only [Fintype.card_coe] using hm
  · intro x hx
    obtain ⟨hxc, hxS⟩ := Finset.mem_erase.mp ((hvalid S Q hQ).2 hx)
    exact Finset.mem_erase.mpr ⟨hxc, hsub S.val S.property hxS⟩

theorem rooted_residue_card_le {N c k : ℕ} {F : Finset (Finset ℕ)}
    (hF : Erdos272.IsArithInterSet N F) (hc : ∀ S ∈ F, c ∈ S)
    (hmet : ∀ S ∈ F, (S ∩ outsideRootResidue N c k).Nonempty) :
    F.card ≤ (meetingPairPool N c (outsideRootResidue N c k)).card +
      20001*N + witnessExceptionBound N c := by
  classical
  let P := outsideRootResidue N c k
  let Bad (S : Finset ℕ) := IsCrooked S ∧ ∀ Q, IsWitnessPair S c Q → Disjoint Q P
  let B := F.filter Bad
  let G := F.filter (fun S => ¬Bad S)
  have hBF : B ⊆ F := Finset.filter_subset _ _
  have hGF : G ⊆ F := Finset.filter_subset _ _
  have hB : B.card ≤ witnessExceptionBound N c := by
    apply restricted_witness_bad_family_card_le (arithInterSet_mono hF hBF)
      (fun S hS => hc S (hBF hS))
      (fun S hS => (Finset.mem_filter.mp hS).2.1)
    · intro S hS
      obtain ⟨x, hx⟩ := hmet S (hBF hS)
      obtain ⟨hxS, hxP⟩ := Finset.mem_inter.mp hx
      have hxc : x ≠ c := by
        intro heq
        apply (Finset.mem_filter.mp hxP).2
        subst x
        rfl
      exact ⟨x, Finset.mem_inter.mpr ⟨Finset.mem_erase.mpr ⟨hxc, hxS⟩, hxP⟩⟩
    · intro S hS
      exact (Finset.mem_filter.mp hS).2.2
  let T := G.filter (fun S => S.card ≤ 2)
  let H := G.filter (fun S => ¬S.card ≤ 2)
  have hTG : T ⊆ G := Finset.filter_subset _ _
  have hHG : H ⊆ G := Finset.filter_subset _ _
  have hT : T.card ≤ N := by
    have hh := small_common_point_card_le (F := T) (U := Finset.Icc 1 N) (c := c)
      (fun S hS => Finset.mem_powerset.mp (hF.1 (hGF (hTG hS))))
      (fun S hS => hc S (hGF (hTG hS))) (fun S hS => (Finset.mem_filter.mp hS).2)
    simpa using hh
  have hH : H.card ≤ (meetingPairPool N c P).card + 20000*N := by
    apply rooted_residue_good_large_card_le (arithInterSet_mono hF (hHG.trans hGF))
      (fun S hS => hc S (hGF (hHG hS)))
    · intro S hS
      have hh := (Finset.mem_filter.mp hS).2
      omega
    · intro S hS
      exact hmet S (hGF (hHG hS))
    · intro S hS hcrooked
      by_contra hbad
      apply (Finset.mem_filter.mp (hHG hS)).2
      refine ⟨hcrooked, ?_⟩
      intro Q hQ
      by_contra hn
      exact hbad ⟨Q, hQ, hn⟩
  have hpart := Finset.card_filter_add_card_filter_not (s := F) Bad
  have hpartG := Finset.card_filter_add_card_filter_not (s := G) (fun S => S.card ≤ 2)
  change B.card + G.card = F.card at hpart
  change T.card + H.card = G.card at hpartG
  change F.card ≤ (meetingPairPool N c P).card + 20001*N + witnessExceptionBound N c
  omega

end
/- ResidueCounting -/

/- Finite counts for a parity-restricted rooted family and a fixed-step family. -/

section
open Finset

theorem outsideRootResidue_two_card_le (N c : ℕ) :
    2*(outsideRootResidue N c 2).card ≤ N+1 := by
  have hmaps : Set.MapsTo (fun x : ℕ => (x-1)/2)
      (outsideRootResidue N c 2 : Set ℕ) (Finset.range ((N+1)/2) : Set ℕ) := by
    intro x hx
    obtain ⟨hxI, _hxmod⟩ := Finset.mem_filter.mp hx
    obtain ⟨hx1, hxN⟩ := Finset.mem_Icc.mp hxI
    apply Finset.mem_range.mpr
    change (x-1)/2 < (N+1)/2
    omega
  have hinj : Set.InjOn (fun x : ℕ => (x-1)/2) (outsideRootResidue N c 2 : Set ℕ) := by
    intro x hx y hy heq
    obtain ⟨hxI, hxmod⟩ := Finset.mem_filter.mp hx
    obtain ⟨hyI, hymod⟩ := Finset.mem_filter.mp hy
    obtain ⟨hx1, hxN⟩ := Finset.mem_Icc.mp hxI
    obtain ⟨hy1, hyN⟩ := Finset.mem_Icc.mp hyI
    change ¬c%2 = x%2 at hxmod
    change ¬c%2 = y%2 at hymod
    change (x-1)/2 = (y-1)/2 at heq
    omega
  have hh := Finset.card_le_card_of_injOn _ hmaps hinj
  simp only [Finset.card_range] at hh
  omega

theorem parity_meeting_pair_pool_card_le {N c : ℕ} (hN : 1 ≤ N) :
    ((meetingPairPool N c (outsideRootResidue N c 2)).card : ℝ) ≤
      3*(N : ℝ)^2/8 + N + 1 := by
  have hP : outsideRootResidue N c 2 ⊆ Finset.Icc 1 N := Finset.filter_subset _ _
  have hcP : c ∉ outsideRootResidue N c 2 := by
    intro hc
    exact (Finset.mem_filter.mp hc).2 rfl
  have hcount := meetingPairPool_card_real hP hcP
  have hPcount : 2*((outsideRootResidue N c 2).card : ℝ) ≤ (N : ℝ)+1 := by
    exact_mod_cast outsideRootResidue_two_card_le N c
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hprod := mul_nonneg
    (show 0 ≤ (N : ℝ)+1-2*(outsideRootResidue N c 2).card by linarith only [hPcount])
    (show 0 ≤ 3*(N : ℝ)-1-2*(outsideRootResidue N c 2).card by linarith only [hPcount, hNR])
  nlinarith only [hcount, hprod, hNR]

theorem rooted_parity_card_le {N c : ℕ} {F : Finset (Finset ℕ)}
    (hcI : c ∈ Finset.Icc 1 N) (hF : Erdos272.IsArithInterSet N F)
    (hc : ∀ S ∈ F, c ∈ S)
    (hmet : ∀ S ∈ F, (S ∩ outsideRootResidue N c 2).Nonempty) :
    (F.card : ℝ) ≤ 3*(N : ℝ)^2/8 + 20002*N + 1 +
      48*N*((Nat.log 2 N + 1 : ℕ) : ℝ)^3 := by
  have hNat := rooted_residue_card_le hF hc hmet
  have hcount : (F.card : ℝ) ≤ (meetingPairPool N c (outsideRootResidue N c 2)).card +
      20001*(N : ℝ) + witnessExceptionBound N c := by exact_mod_cast hNat
  have hN : 1 ≤ N := by have hh := Finset.mem_Icc.mp hcI; omega
  have hpairs := parity_meeting_pair_pool_card_le (c := c) hN
  have herr : (witnessExceptionBound N c : ℝ) ≤
      48*(N : ℝ)*((Nat.log 2 N + 1 : ℕ) : ℝ)^3 := by
    exact_mod_cast witnessExceptionBound_le_natLog hcI
  linarith only [hcount, hpairs, herr]

theorem natAP_mem_of_bounds_modEq {a d m x : ℕ} (hd : 0 < d) (hm : 0 < m)
    (hax : a ≤ x) (hxm : x ≤ a+(m-1)*d) (hmod : Nat.ModEq d a x) :
    x ∈ natAP a d m := by
  have hdiv : d ∣ x-a := (Nat.modEq_iff_dvd' hax).mp hmod
  let i := (x-a)/d
  have hid : i*d = x-a := Nat.div_mul_cancel hdiv
  have hrep : a+i*d = x := by omega
  have himul : i*d < m*d := by
    have hmsub : m-1+1 = m := by omega
    nlinarith only [hrep, hxm, hd, hmsub]
  have hi : i < m := Nat.lt_of_mul_lt_mul_right himul
  exact mem_natAP.mpr ⟨i, hi, hrep⟩

theorem natAP_avoiding_internal_root_subset_residue_complement {N c a d m : ℕ}
    (hd : 0 < d) (hm : 0 < m) (hsub : natAP a d m ⊆ Finset.Icc 1 N)
    (hac : a ≤ c) (hctop : c ≤ a+(m-1)*d) (hc : c ∉ natAP a d m) :
    natAP a d m ⊆ outsideRootResidue N c d := by
  intro x hx
  refine Finset.mem_filter.mpr ⟨hsub hx, ?_⟩
  intro hcx
  have hax : Nat.ModEq d a x := by
    obtain ⟨i, _hi, rfl⟩ := mem_natAP.mp hx
    change a%d = (a+i*d)%d
    simp only [Nat.add_mul_mod_self_right]
  have hacmod : Nat.ModEq d a c := hax.trans hcx.symm
  exact hc (natAP_mem_of_bounds_modEq hd hm hac hctop hacmod)

theorem same_step_family_full_card_le {N d : ℕ} {F : Finset (Finset ℕ)}
    (hd : 0 < d) (hF : Erdos272.IsArithInterSet N F)
    (hrep : ∀ S ∈ F, ∃ a : ℕ, S = natAP a d S.card) :
    (F.card : ℝ) ≤ (N : ℝ)^2/(4*(d : ℝ)^2) + (N : ℝ)/d + 18*N + 4 := by
  classical
  let A := F.filter (fun S => 4 ≤ S.card)
  let B := F.filter (fun S => ¬4 ≤ S.card)
  have hA : (A.card : ℝ) ≤ (N : ℝ)^2/(4*(d : ℝ)^2) + (N : ℝ)/d + 1 := by
    apply same_step_family_card_le hd (admissible_subfamily hF (Finset.filter_subset _ _))
    · intro S hS
      exact (Finset.mem_filter.mp hS).2
    · intro S hS
      exact hrep S (Finset.mem_filter.mp hS).1
  have hB : B.card ≤ 18*N+3 := by
    apply progression_family_small_card_le (admissible_subfamily hF (Finset.filter_subset _ _))
    · intro S hS
      obtain ⟨a, heq⟩ := hrep S (Finset.mem_filter.mp hS).1
      rw [heq]
      exact ⟨S.card, natAP_isAP hd⟩
    · intro S hS
      have hh := (Finset.mem_filter.mp hS).2
      omega
  have hBR : (B.card : ℝ) ≤ 18*(N : ℝ)+3 := by exact_mod_cast hB
  have hpart : (A.card : ℝ)+(B.card : ℝ) = F.card := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := F) (fun S => 4 ≤ S.card)
  linarith only [hA, hBR, hpart]

end
/- TwoStepStraddling -/

/- A quadratic gap when the progressions avoiding the root have step two. -/

section
open Finset Filter

def StraddlesRoot (c : ℕ) (S : Finset ℕ) : Prop :=
  (∃ x ∈ S, x < c) ∧ ∃ y ∈ S, c < y

theorem natAP_bounds_of_mem {a d m x : ℕ} (hx : x ∈ natAP a d m) :
    a ≤ x ∧ x ≤ a+(m-1)*d := by
  obtain ⟨i, hi, rfl⟩ := mem_natAP.mp hx
  have hii : i ≤ m-1 := by omega
  have hmul := Nat.mul_le_mul_right d hii
  omega

theorem straddling_natAP_subset_residue_complement {N c a d : ℕ} {S : Finset ℕ}
    (hd : 0 < d) (hrep : S = natAP a d S.card) (hsub : S ⊆ Finset.Icc 1 N)
    (hstraddle : StraddlesRoot c S) (hc : c ∉ S) : S ⊆ outsideRootResidue N c d := by
  obtain ⟨⟨x, hx, hxc⟩, y, hy, hcy⟩ := hstraddle
  have hm : 0 < S.card := Finset.card_pos.mpr ⟨x, hx⟩
  have hleft := (natAP_bounds_of_mem (hrep ▸ hx)).1
  have hright := (natAP_bounds_of_mem (hrep ▸ hy)).2
  have hh := natAP_avoiding_internal_root_subset_residue_complement hd hm
    (by simpa only [← hrep] using hsub) (by omega : a ≤ c)
    (by omega : c ≤ a+(S.card-1)*d) (by simpa only [← hrep] using hc)
  simpa only [← hrep] using hh

theorem two_step_straddling_family_card_le {N c : ℕ} {F : Finset (Finset ℕ)}
    (hcI : c ∈ Finset.Icc 1 N) (hF : Erdos272.IsArithInterSet N F)
    (hrep : ∀ S ∈ F, c ∉ S → ∃ a, S = natAP a 2 S.card)
    (houtside : ∃ P ∈ F, c ∉ P ∧ StraddlesRoot c P) :
    (F.card : ℝ) ≤ 7*(N : ℝ)^2/16 + 20021*N + 5 +
      48*N*((Nat.log 2 N+1 : ℕ) : ℝ)^3 := by
  classical
  obtain ⟨P, hPF, hcP, hstraddle⟩ := houtside
  obtain ⟨a, hPa⟩ := hrep P hPF hcP
  have hPsub : P ⊆ outsideRootResidue N c 2 :=
    straddling_natAP_subset_residue_complement (by decide) hPa
      (Finset.mem_powerset.mp (hF.1 hPF)) hstraddle hcP
  have hPne : P.Nonempty := by obtain ⟨x, hx, _hxc⟩ := hstraddle.1; exact ⟨x, hx⟩
  let R := F.filter (fun S => c ∈ S)
  let O := F.filter (fun S => c ∉ S)
  have hR : (R.card : ℝ) ≤ 3*(N : ℝ)^2/8 + 20002*N + 1 +
      48*N*((Nat.log 2 N+1 : ℕ) : ℝ)^3 := by
    apply rooted_parity_card_le hcI (admissible_subfamily hF (Finset.filter_subset _ _))
      (fun S hS => (Finset.mem_filter.mp hS).2)
    intro S hS
    obtain ⟨x, hx⟩ := arithInter_inter_nonempty hF hPF (Finset.mem_filter.mp hS).1 hPne
    obtain ⟨hxP, hxS⟩ := Finset.mem_inter.mp hx
    exact ⟨x, Finset.mem_inter.mpr ⟨hxS, hPsub hxP⟩⟩
  have hO : (O.card : ℝ) ≤ (N : ℝ)^2/16 + (N : ℝ)/2 + 18*N + 4 := by
    have hh := same_step_family_full_card_le (by decide : 0 < 2)
      (admissible_subfamily hF (show O ⊆ F from Finset.filter_subset _ _))
      (fun S hS => hrep S (Finset.mem_filter.mp hS).1 (Finset.mem_filter.mp hS).2)
    norm_num only [Nat.cast_ofNat, show (4 : ℝ)*2^2 = 16 by norm_num] at hh
    exact hh
  have hpart : (R.card : ℝ)+(O.card : ℝ) = F.card := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := F) (fun S => c ∈ S)
  nlinarith only [hR, hO, hpart, Nat.cast_nonneg (α := ℝ) N]

theorem eventually_const_mul_natLog_pow_le (C k : ℕ) :
    ∀ᶠ N : ℕ in atTop, C*(Nat.log 2 N+1)^k ≤ N := by
  filter_upwards [eventually_natLog_pow_le (2*k), Filter.eventually_ge_atTop (C^2)]
    with N hlog hN
  have hsq : (C*(Nat.log 2 N+1)^k)^2 ≤ N^2 := by
    calc
      (C*(Nat.log 2 N+1)^k)^2 = C^2*(Nat.log 2 N+1)^(2*k) := by ring
      _ ≤ C^2*N := Nat.mul_le_mul_left _ hlog
      _ ≤ N*N := Nat.mul_le_mul_right _ hN
      _ = N^2 := by ring
  exact (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp hsq

theorem eventually_two_step_straddling_gap :
    ∀ᶠ N : ℕ in atTop, ∀ (F : Finset (Finset ℕ)) (c : ℕ),
      c ∈ Finset.Icc 1 N → Erdos272.IsArithInterSet N F →
      (∀ S ∈ F, c ∉ S → ∃ a, S = natAP a 2 S.card) →
      (∃ P ∈ F, c ∉ P ∧ StraddlesRoot c P) →
      (F.card : ℝ) ≤ 15*(N : ℝ)^2/32 := by
  filter_upwards [eventually_const_mul_natLog_pow_le 3072 3,
    Filter.eventually_ge_atTop 2000000] with N hlog hN F c hcI hF hrep houtside
  have hbound := two_step_straddling_family_card_le hcI hF hrep houtside
  have hlogR : 3072*((Nat.log 2 N+1 : ℕ) : ℝ)^3 ≤ (N : ℝ) := by exact_mod_cast hlog
  have hNR : (2000000 : ℝ) ≤ N := by exact_mod_cast hN
  have hlogmul := mul_le_mul_of_nonneg_right hlogR (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  have hNmul := mul_le_mul_of_nonneg_right hNR (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  nlinarith only [hbound, hlogmul, hNmul, hNR]

end
/- OutsidePairCount -/

/- Counting meeting pairs with at least one endpoint outside an inner set. -/

section
open Finset

def meetingOutsidePairs {α : Type*} [DecidableEq α]
    (U B P : Finset α) : Finset (Finset α) :=
  (U.powersetCard 2).filter (fun Q => ¬Disjoint Q P ∧ ¬Q ⊆ B)

theorem meetingOutsidePairs_card_add {α : Type*} [DecidableEq α]
    {U B : Finset α} (hBU : B ⊆ U) (P : Finset α) :
    (meetingOutsidePairs U B P).card +
      ((B.powersetCard 2).filter (fun Q => ¬Disjoint Q (P ∩ B))).card =
      ((U.powersetCard 2).filter (fun Q => ¬Disjoint Q P)).card := by
  classical
  let M := (U.powersetCard 2).filter (fun Q => ¬Disjoint Q P)
  have hinside : M.filter (fun Q => Q ⊆ B) =
      (B.powersetCard 2).filter (fun Q => ¬Disjoint Q (P ∩ B)) := by
    ext Q
    constructor
    · intro hQ
      obtain ⟨hQM, hQB⟩ := Finset.mem_filter.mp hQ
      obtain ⟨hQU, hQP⟩ := Finset.mem_filter.mp hQM
      refine Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr
        ⟨hQB, (Finset.mem_powersetCard.mp hQU).2⟩, ?_⟩
      intro hdis
      apply hQP
      exact Finset.disjoint_left.mpr (fun x hxQ hxP =>
        Finset.disjoint_left.mp hdis hxQ (Finset.mem_inter.mpr ⟨hxP, hQB hxQ⟩))
    · intro hQ
      obtain ⟨hQB, hQP⟩ := Finset.mem_filter.mp hQ
      obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hQB
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_powersetCard.mpr ⟨hsub.trans hBU, hcard⟩, ?_⟩, hsub⟩
      intro hdis
      apply hQP
      exact Finset.disjoint_left.mpr (fun x hxQ hxPB =>
        Finset.disjoint_left.mp hdis hxQ (Finset.mem_inter.mp hxPB).1)
  have houtside : M.filter (fun Q => ¬Q ⊆ B) = meetingOutsidePairs U B P := by
    simp only [M, meetingOutsidePairs, Finset.filter_filter]
  have hh := Finset.card_filter_add_card_filter_not (s := M) (fun Q => Q ⊆ B)
  rw [hinside, houtside] at hh
  dsimp only [M] at hh
  omega

theorem meetingOutsidePairs_card_real {α : Type*} [DecidableEq α]
    {U B P : Finset α} (hBU : B ⊆ U) (hPU : P ⊆ U) :
    ((meetingOutsidePairs U B P).card : ℝ) =
      ((P \ B).card : ℝ)*U.card - ((P \ B).card : ℝ)^2/2 - ((P \ B).card : ℝ)/2 +
        ((P ∩ B).card : ℝ)*((U \ B).card - ((P \ B).card : ℝ)) := by
  have hsum : ((meetingOutsidePairs U B P).card : ℝ) +
      (((B.powersetCard 2).filter (fun Q => ¬Disjoint Q (P ∩ B))).card : ℝ) =
      (((U.powersetCard 2).filter (fun Q => ¬Disjoint Q P)).card : ℝ) := by
    exact_mod_cast meetingOutsidePairs_card_add hBU P
  rw [card_meeting_pairs_real hPU, card_meeting_pairs_real Finset.inter_subset_right] at hsum
  have hPpart : (P.card : ℝ) = ((P \ B).card : ℝ) + (P ∩ B).card := by
    exact_mod_cast (Finset.card_sdiff_add_card_inter P B).symm
  have hBpart : (U.card : ℝ) = ((U \ B).card : ℝ) + B.card := by
    exact_mod_cast (Finset.card_sdiff_add_card_eq_card hBU).symm
  rw [hPpart, hBpart] at hsum
  rw [hBpart]
  nlinarith only [hsum]

theorem meetingOutsidePairs_card_le {α : Type*} [DecidableEq α]
    {U B P : Finset α} (hBU : B ⊆ U) (hPU : P ⊆ U) :
    ((meetingOutsidePairs U B P).card : ℝ) ≤
      ((P \ B).card : ℝ)*U.card - ((P \ B).card : ℝ)^2/2 +
        ((P ∩ B).card : ℝ)*((U \ B).card - ((P \ B).card : ℝ)) := by
  rw [meetingOutsidePairs_card_real hBU hPU]
  linarith only [Nat.cast_nonneg (α := ℝ) (P \ B).card]

def crossPairPool {α : Type*} [DecidableEq α] (L R : Finset α) : Finset (Finset α) :=
  (L.product R).image (fun p => {p.1, p.2})

theorem crossPairPool_card_le {α : Type*} [DecidableEq α] (L R : Finset α) :
    (crossPairPool L R).card ≤ L.card*R.card := by
  exact (Finset.card_image_le).trans_eq (Finset.card_product L R)

end
/- IntervalWitnessPool -/

/- Rooted interval endpoints and intrinsic witnesses share a controlled pair pool. -/

section
open Finset

theorem witness_pair_not_subset_AP_member {N c : ℕ} {F : Finset (Finset ℕ)}
    {S T Q : Finset ℕ} (hF : Erdos272.IsArithInterSet N F) (hS : S ∈ F) (hT : T ∈ F)
    (hcS : c ∈ S) (hcT : c ∈ T) (hcrooked : IsCrooked S)
    (hAP : ∃ l : ℕ∞, (T : Set ℕ).IsAPOfLength l) (hQ : IsWitnessPair S c Q) : ¬Q ⊆ T := by
  intro hQT
  have hTS := witness_pair_private hF hS hT hcS hcT hQ hQT
  exact hcrooked (by simpa only [hTS] using hAP)

theorem root_pair_in_cross_of_inner {c u v : ℕ} {Q : Finset ℕ}
    (hcard : Q.card = 2) (hc : c ∉ Q) (hinner : Q ⊆ Finset.Icc u v)
    (hleft : ¬Q ⊆ Finset.Icc u c) (hright : ¬Q ⊆ Finset.Icc c v) :
    Q ∈ crossPairPool (Finset.Ico u c) (Finset.Ioc c v) := by
  obtain ⟨x, y, _hxy, rfl⟩ := Finset.card_eq_two.mp hcard
  have hx := Finset.mem_Icc.mp (hinner (by simp : x ∈ ({x, y} : Finset ℕ)))
  have hy := Finset.mem_Icc.mp (hinner (by simp : y ∈ ({x, y} : Finset ℕ)))
  have hxc : x ≠ c := by intro heq; apply hc; simp [heq]
  have hyc : y ≠ c := by intro heq; apply hc; simp [heq]
  by_cases hxlt : x < c
  · have hcy : c < y := by
      by_contra hn
      apply hleft
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl <;> exact Finset.mem_Icc.mpr (by omega)
    exact Finset.mem_image.mpr ⟨(x,y), Finset.mem_product.mpr
      ⟨Finset.mem_Ico.mpr ⟨hx.1, hxlt⟩, Finset.mem_Ioc.mpr ⟨hcy, hy.2⟩⟩, rfl⟩
  · have hylt : y < c := by
      by_contra hn
      apply hright
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl <;> exact Finset.mem_Icc.mpr (by omega)
    exact Finset.mem_image.mpr ⟨(y,x), Finset.mem_product.mpr
      ⟨Finset.mem_Ico.mpr ⟨hy.1, hylt⟩, Finset.mem_Ioc.mpr ⟨by omega, hx.2⟩⟩,
        by simp only [Finset.pair_comm]⟩

theorem crooked_witness_in_interval_pool {N c u v : ℕ} {F : Finset (Finset ℕ)}
    {S Q P : Finset ℕ} (hF : Erdos272.IsArithInterSet N F) (hS : S ∈ F)
    (huc : u ≤ c) (hcv : c ≤ v) (hcS : c ∈ S) (hcrooked : IsCrooked S)
    (hleft : u = c ∨ ∃ T ∈ F, (∃ l : ℕ∞, (T : Set ℕ).IsAPOfLength l) ∧ Finset.Icc u c ⊆ T)
    (hright : v = c ∨ ∃ T ∈ F, (∃ l : ℕ∞, (T : Set ℕ).IsAPOfLength l) ∧ Finset.Icc c v ⊆ T)
    (hQ : IsWitnessPair S c Q) (hmet : ¬Disjoint Q P) :
    Q ∈ crossPairPool (Finset.Ico u c) (Finset.Ioc c v) ∪
      meetingOutsidePairs ((Finset.Icc 1 N).erase c) ((Finset.Icc u v).erase c) P := by
  have hcQ : c ∉ Q := by
    intro hc
    exact (Finset.mem_erase.mp (hQ.2.1 hc)).1 rfl
  have hnotleft : ¬Q ⊆ Finset.Icc u c := by
    intro hsub
    rcases hleft with heq | ⟨T, hT, hAP, hcover⟩
    · have hh := Finset.card_le_card hsub
      simp only [heq, Finset.Icc_self, Finset.card_singleton, hQ.1] at hh
      omega
    exact witness_pair_not_subset_AP_member hF hS hT hcS
      (hcover (Finset.mem_Icc.mpr ⟨huc, le_rfl⟩)) hcrooked hAP hQ (hsub.trans hcover)
  have hnotright : ¬Q ⊆ Finset.Icc c v := by
    intro hsub
    rcases hright with heq | ⟨T, hT, hAP, hcover⟩
    · have hh := Finset.card_le_card hsub
      simp only [heq, Finset.Icc_self, Finset.card_singleton, hQ.1] at hh
      omega
    exact witness_pair_not_subset_AP_member hF hS hT hcS
      (hcover (Finset.mem_Icc.mpr ⟨le_rfl, hcv⟩)) hcrooked hAP hQ (hsub.trans hcover)
  by_cases hinner : Q ⊆ Finset.Icc u v
  · exact Finset.mem_union_left _ (root_pair_in_cross_of_inner hQ.1 hcQ hinner hnotleft hnotright)
  · apply Finset.mem_union_right
    refine Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨?_, hQ.1⟩,
      hmet, fun hh => hinner (hh.trans (Finset.erase_subset _ _))⟩
    intro x hx
    obtain ⟨hxc, hxS⟩ := Finset.mem_erase.mp (hQ.2.1 hx)
    exact Finset.mem_erase.mpr ⟨hxc, Finset.mem_powerset.mp (hF.1 hS) hxS⟩

theorem interval_isAP {a b : ℕ} (hab : a ≤ b) :
    ∃ l : ℕ∞, ((Finset.Icc a b : Finset ℕ) : Set ℕ).IsAPOfLength l := by
  simpa [apSegment] using apSegment_isAP hab (by decide : 0 < 1)

theorem private_pairs_and_intervals_card_le {N c : ℕ} {F C E : Finset (Finset ℕ)}
    {Pool : Finset (Finset ℕ)} (hF : Erdos272.IsArithInterSet N F)
    (hCF : C ⊆ F) (hEF : E ⊆ F) (hc : ∀ S ∈ C, c ∈ S)
    (hcrooked : ∀ S ∈ C, IsCrooked S)
    (hW : ∀ S ∈ C, ∃ Q, IsWitnessPair S c Q ∧ Q ∈ Pool)
    (hE : ∀ S ∈ E, ∃ a b : ℕ,
      a < c ∧ c < b ∧ S = Finset.Icc a b ∧ ({a,b} : Finset ℕ) ∈ Pool) :
    C.card + E.card ≤ Pool.card := by
  classical
  let X := {S // S ∈ C}
  let Y := {S // S ∈ E}
  have hparamC : ∀ S : X, ∃ Q, IsWitnessPair S.val c Q ∧ Q ∈ Pool :=
    fun S => hW S.val S.property
  choose Q hQ hQPool using hparamC
  have hparamE : ∀ T : Y, ∃ a b : ℕ,
      a < c ∧ c < b ∧ T.val = Finset.Icc a b ∧ ({a,b} : Finset ℕ) ∈ Pool :=
    fun T => hE T.val T.property
  choose a b hac hcb hrep hPairPool using hparamE
  let e : Y → Finset ℕ := fun T => {a T, b T}
  have hQinj : Function.Injective Q := by
    intro S T heq
    apply Subtype.ext
    exact (witness_pair_private hF (hCF S.property) (hCF T.property)
      (hc S.val S.property) (hc T.val T.property) (hQ S) (by
        rw [heq]
        exact (hQ T).2.1.trans (Finset.erase_subset _ _))).symm
  have heinj : Function.Injective e := by
    intro S T heq
    have hST := sorted_pair_finset_injective (lt_trans (hac S) (hcb S))
      (lt_trans (hac T) (hcb T)) heq
    have haST := congrArg Prod.fst hST
    have hbST := congrArg Prod.snd hST
    change a S = a T at haST
    change b S = b T at hbST
    apply Subtype.ext
    rw [hrep S, hrep T, haST, hbST]
  have hdis : Disjoint ((Finset.univ : Finset X).image Q) ((Finset.univ : Finset Y).image e) := by
    apply Finset.disjoint_left.mpr
    intro W hWC hWE
    obtain ⟨S, _hS, rfl⟩ := Finset.mem_image.mp hWC
    obtain ⟨T, _hT, hTeq⟩ := Finset.mem_image.mp hWE
    have hTab : a T ≤ b T := le_of_lt (lt_trans (hac T) (hcb T))
    have hAP : ∃ l : ℕ∞, (T.val : Set ℕ).IsAPOfLength l := by
      rw [hrep T]
      exact interval_isAP hTab
    have hcT : c ∈ T.val := by rw [hrep T]; exact Finset.mem_Icc.mpr ⟨(hac T).le, (hcb T).le⟩
    apply witness_pair_not_subset_AP_member hF (hCF S.property) (hEF T.property)
      (hc S.val S.property) hcT (hcrooked S.val S.property) hAP (hQ S)
    rw [← hTeq, hrep T]
    intro x hx
    simp only [e, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_Icc.mpr ⟨le_rfl, hTab⟩
    · exact Finset.mem_Icc.mpr ⟨hTab, le_rfl⟩
  have hsub : ((Finset.univ : Finset X).image Q) ∪ ((Finset.univ : Finset Y).image e) ⊆ Pool := by
    intro W hW
    rcases Finset.mem_union.mp hW with hWC | hWE
    · obtain ⟨S, _hS, rfl⟩ := Finset.mem_image.mp hWC
      exact hQPool S
    · obtain ⟨T, _hT, rfl⟩ := Finset.mem_image.mp hWE
      exact hPairPool T
  have hh := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdis, Finset.card_image_of_injective _ hQinj,
    Finset.card_image_of_injective _ heinj] at hh
  simpa only [Finset.card_univ, X, Y, Fintype.card_coe] using hh

end
/- StraddlingAlgebra -/

/- The finite quadratic optimization in the straddling case with step at least three. -/

section
theorem large_step_straddling_polynomial {n l w h j : ℝ}
    (hn : 6 ≤ n) (hl : 0 ≤ l) (hw : 0 ≤ w) (hlen : l+w ≤ n)
    (hhw : h ≤ w) (hh : 3*h ≤ w+6) (hj : 3*j ≤ l+6) :
    l^2/4 + h*n - h^2/2 + j*(w-h) ≤ 5*n^2/18 + 3*n := by
  let A := w/3+2
  let B := l/3+2
  have hA : h ≤ A := by dsimp [A]; linarith only [hh]
  have hB : j ≤ B := by dsimp [B]; linarith only [hj]
  have hAB : A+B ≤ n := by dsimp [A, B]; linarith only [hlen, hn]
  have hfirst := mul_le_mul_of_nonneg_right hB (sub_nonneg.mpr hhw)
  have hsecond := mul_nonneg (sub_nonneg.mpr hA)
    (show 0 ≤ n-B-(h+A)/2 by linarith only [hA, hAB])
  have hcount : l^2/4 + h*n-h^2/2+j*(w-h) ≤
      l^2/4+A*n-A^2/2+B*(w-A) := by
    nlinarith only [hfirst, hsecond]
  have hprod := mul_nonneg (show 0 ≤ n-l-w by linarith only [hlen])
    (show 0 ≤ 5*n+5*l-w by linarith only [hlen, hl, hw])
  have hmain : l^2/4+w*n/3-w^2/18+2*l*w/9 ≤ 5*n^2/18 := by
    nlinarith only [hprod, sq_nonneg l]
  dsimp only [A, B] at hcount
  nlinarith only [hcount, hmain, hlen, hl, hn]

end
/- ResidueSpacing -/

/- Spacing estimates for a residue class in one interval and its two exterior intervals. -/

section
open Finset

theorem spaced_residue_card_mul_le {a k u v : ℕ} {S : Finset ℕ}
    (hk : 3 ≤ k) (hsub : S ⊆ Finset.Icc u v)
    (hmod : ∀ x ∈ S, Nat.ModEq k a x) :
    3*S.card ≤ (Finset.Icc u v).card+3 := by
  by_cases huv : u ≤ v
  · have hmaps : Set.MapsTo (fun x : ℕ => (x-u)/3) (S : Set ℕ)
        (Finset.range ((v-u)/3+1) : Set ℕ) := by
      intro x hx
      obtain ⟨hux, hxv⟩ := Finset.mem_Icc.mp (hsub hx)
      apply Finset.mem_range.mpr
      change (x-u)/3 < (v-u)/3+1
      omega
    have hinj : Set.InjOn (fun x : ℕ => (x-u)/3) (S : Set ℕ) := by
      intro x hx y hy heq
      obtain ⟨hux, hxv⟩ := Finset.mem_Icc.mp (hsub hx)
      obtain ⟨huy, hyv⟩ := Finset.mem_Icc.mp (hsub hy)
      change (x-u)/3 = (y-u)/3 at heq
      have hxy : Nat.ModEq k x y := (hmod x hx).symm.trans (hmod y hy)
      by_cases hle : x ≤ y
      · have hd : k ∣ y-x := (Nat.modEq_iff_dvd' hle).mp hxy
        have hlt : y-x < k := by omega
        have hz := Nat.eq_zero_of_dvd_of_lt hd hlt
        omega
      · have hd : k ∣ x-y := (Nat.modEq_iff_dvd' (by omega : y ≤ x)).mp hxy.symm
        have hlt : x-y < k := by omega
        have hz := Nat.eq_zero_of_dvd_of_lt hd hlt
        omega
    have hh := Finset.card_le_card_of_injOn _ hmaps hinj
    simp only [Finset.card_range] at hh
    rw [Nat.card_Icc]
    omega
  · have hS : S = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      rintro ⟨x, hx⟩
      have hh := Finset.mem_Icc.mp (hsub hx)
      omega
    rw [hS]
    simp only [Finset.card_empty, Nat.mul_zero, Nat.zero_le]

theorem straddling_residue_parts_card_le {N c a k u v : ℕ} {P : Finset ℕ}
    (hk : 3 ≤ k) (hu : 1 ≤ u) (huc : u ≤ c) (hcv : c ≤ v) (hvN : v ≤ N)
    (hP : P ⊆ Finset.Icc 1 N) (hcP : c ∉ P)
    (hmod : ∀ x ∈ P, Nat.ModEq k a x) :
    3*(P \ (Finset.Icc u v).erase c).card ≤
        ((Finset.Icc 1 N).erase c \ (Finset.Icc u v).erase c).card+6 ∧
      3*(P ∩ (Finset.Icc u v).erase c).card ≤ ((Finset.Icc u v).erase c).card+4 := by
  let U := (Finset.Icc 1 N).erase c
  let B := (Finset.Icc u v).erase c
  let O := P \ B
  let L := O.filter (fun x => x < u)
  let R := O.filter (fun x => ¬x < u)
  have hL : 3*L.card ≤ (Finset.Icc 1 (u-1)).card+3 := by
    apply spaced_residue_card_mul_le hk
    · intro x hx
      obtain ⟨hxO, hxu⟩ := Finset.mem_filter.mp hx
      have hxP := (Finset.mem_sdiff.mp hxO).1
      have hxN := Finset.mem_Icc.mp (hP hxP)
      exact Finset.mem_Icc.mpr ⟨hxN.1, by omega⟩
    · intro x hx
      exact hmod x (Finset.mem_sdiff.mp (Finset.mem_filter.mp hx).1).1
  have hR : 3*R.card ≤ (Finset.Icc (v+1) N).card+3 := by
    apply spaced_residue_card_mul_le hk
    · intro x hx
      obtain ⟨hxO, hxu⟩ := Finset.mem_filter.mp hx
      obtain ⟨hxP, hxB⟩ := Finset.mem_sdiff.mp hxO
      have hxN := Finset.mem_Icc.mp (hP hxP)
      have hxc : x ≠ c := by intro heq; exact hcP (heq ▸ hxP)
      have hvx : v < x := by
        by_contra hn
        exact hxB (Finset.mem_erase.mpr ⟨hxc, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩)
      exact Finset.mem_Icc.mpr ⟨by omega, hxN.2⟩
    · intro x hx
      exact hmod x (Finset.mem_sdiff.mp (Finset.mem_filter.mp hx).1).1
  have hJ : 3*(P ∩ B).card ≤ (Finset.Icc u v).card+3 := by
    apply spaced_residue_card_mul_le hk
    · intro x hx
      exact Finset.mem_of_mem_erase (Finset.mem_inter.mp hx).2
    · intro x hx
      exact hmod x (Finset.mem_inter.mp hx).1
  have hBU : B ⊆ U := by
    intro x hx
    obtain ⟨hxc, hxI⟩ := Finset.mem_erase.mp hx
    have hx := Finset.mem_Icc.mp hxI
    exact Finset.mem_erase.mpr ⟨hxc, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩
  have hcU : c ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hcB : c ∈ Finset.Icc u v := Finset.mem_Icc.mpr ⟨huc, hcv⟩
  have hUcard : U.card = N-1 := by simp only [U, Finset.card_erase_of_mem hcU, Nat.card_Icc]; omega
  have hBcard : B.card = v-u := by simp only [B, Finset.card_erase_of_mem hcB, Nat.card_Icc]; omega
  have hOpart := Finset.card_filter_add_card_filter_not (s := O) (fun x => x < u)
  change L.card+R.card = O.card at hOpart
  have hUdiff := Finset.card_sdiff_add_card_eq_card hBU
  rw [hUcard, hBcard] at hUdiff
  simp only [Nat.card_Icc] at hL hR hJ
  change 3*O.card ≤ (U \ B).card+6 ∧ 3*(P ∩ B).card ≤ B.card+4
  constructor <;> omega

end
/- IntervalPoolBound -/

/- The interval and witness pool has a uniform quadratic gap for spacing at least three. -/

section
open Finset

theorem interval_witness_pool_card_le {N c a k u v : ℕ} {P : Finset ℕ}
    (hN : 6 ≤ N) (hk : 3 ≤ k) (hu : 1 ≤ u) (huc : u ≤ c) (hcv : c ≤ v) (hvN : v ≤ N)
    (hP : P ⊆ Finset.Icc 1 N) (hcP : c ∉ P) (hmod : ∀ x ∈ P, Nat.ModEq k a x) :
    ((crossPairPool (Finset.Ico u c) (Finset.Ioc c v) ∪
      meetingOutsidePairs ((Finset.Icc 1 N).erase c) ((Finset.Icc u v).erase c) P).card : ℝ) ≤
      5*(N : ℝ)^2/18+3*N := by
  let U := (Finset.Icc 1 N).erase c
  let B := (Finset.Icc u v).erase c
  let X := crossPairPool (Finset.Ico u c) (Finset.Ioc c v)
  let M := meetingOutsidePairs U B P
  have hBU : B ⊆ U := by
    intro x hx
    obtain ⟨hxc, hxI⟩ := Finset.mem_erase.mp hx
    have hh := Finset.mem_Icc.mp hxI
    exact Finset.mem_erase.mpr ⟨hxc, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩
  have hPU : P ⊆ U := by
    intro x hx
    exact Finset.mem_erase.mpr ⟨fun heq => hcP (heq ▸ hx), hP hx⟩
  have hUcard : U.card ≤ N := by
    have hh := Finset.card_le_card (Finset.erase_subset (s := Finset.Icc 1 N) c)
    simpa only [Nat.card_Icc, Nat.add_sub_cancel] using hh
  have hcB : c ∈ Finset.Icc u v := Finset.mem_Icc.mpr ⟨huc, hcv⟩
  have hBcard : B.card = v-u := by
    simp only [B, Finset.card_erase_of_mem hcB, Nat.card_Icc]
    omega
  have hLR : ((Finset.Ico u c).card : ℝ)+(Finset.Ioc c v).card = B.card := by
    exact_mod_cast (show (Finset.Ico u c).card+(Finset.Ioc c v).card = B.card by
      simp only [Nat.card_Ico, Nat.card_Ioc, hBcard]
      omega)
  have hXcard : (X.card : ℝ) ≤ (B.card : ℝ)^2/4 := by
    have hx : (X.card : ℝ) ≤ ((Finset.Ico u c).card : ℝ)*(Finset.Ioc c v).card := by
      exact_mod_cast crossPairPool_card_le (Finset.Ico u c) (Finset.Ioc c v)
    nlinarith only [hx, hLR, sq_nonneg (((Finset.Ico u c).card : ℝ)-(Finset.Ioc c v).card)]
  have hUcardR : (U.card : ℝ) ≤ N := by exact_mod_cast hUcard
  have hMN := mul_le_mul_of_nonneg_left hUcardR (Nat.cast_nonneg (P \ B).card : (0 : ℝ) ≤ (P \ B).card)
  have hMcard : (M.card : ℝ) ≤ ((P \ B).card : ℝ)*N - ((P \ B).card : ℝ)^2/2 +
      ((P ∩ B).card : ℝ)*((U \ B).card - ((P \ B).card : ℝ)) := by
    have hh := meetingOutsidePairs_card_le hBU hPU
    change (M.card : ℝ) ≤ _ at hh
    linarith only [hh, hMN]
  have hparts := straddling_residue_parts_card_le hk hu huc hcv hvN hP hcP hmod
  have hh : 3*((P \ B).card : ℝ) ≤ ((U \ B).card : ℝ)+6 := by exact_mod_cast hparts.1
  have hj4 : 3*((P ∩ B).card : ℝ) ≤ (B.card : ℝ)+4 := by exact_mod_cast hparts.2
  have hlen : (B.card : ℝ)+(U \ B).card ≤ (N : ℝ) := by
    have hh := Finset.card_sdiff_add_card_eq_card hBU
    have hnat : B.card+(U \ B).card ≤ N := by omega
    exact_mod_cast hnat
  have hhw : ((P \ B).card : ℝ) ≤ (U \ B).card := by
    exact_mod_cast Finset.card_le_card (show P \ B ⊆ U \ B by
      intro x hx
      obtain ⟨hxP, hxB⟩ := Finset.mem_sdiff.mp hx
      exact Finset.mem_sdiff.mpr ⟨hPU hxP, hxB⟩)
  have hpoly := large_step_straddling_polynomial (by exact_mod_cast hN)
    (Nat.cast_nonneg B.card) (Nat.cast_nonneg (U \ B).card) hlen hhw hh
    (show 3*((P ∩ B).card : ℝ) ≤ (B.card : ℝ)+6 by linarith only [hj4])
  have hUnion : ((X ∪ M).card : ℝ) ≤ (X.card : ℝ)+(M.card : ℝ) := by
    exact_mod_cast Finset.card_union_le X M
  change ((X ∪ M).card : ℝ) ≤ _
  linarith only [hUnion, hXcard, hMcard, hpoly]

end
/- IntervalEnvelope -/

/- Extremal endpoints and boundary members in a family of rooted intervals. -/

section
open Finset

theorem rooted_interval_envelope {N c : ℕ} {E : Finset (Finset ℕ)}
    (hcI : c ∈ Finset.Icc 1 N) (hsub : ∀ S ∈ E, S ⊆ Finset.Icc 1 N)
    (hc : ∀ S ∈ E, c ∈ S) (hinterval : ∀ S ∈ E, ∃ a b : ℕ, S = Finset.Icc a b) :
    ∃ u v : ℕ, 1 ≤ u ∧ u ≤ c ∧ c ≤ v ∧ v ≤ N ∧
      (u = c ∨ ∃ T ∈ E, (∃ l : ℕ∞, (T : Set ℕ).IsAPOfLength l) ∧ Finset.Icc u c ⊆ T) ∧
      (v = c ∨ ∃ T ∈ E, (∃ l : ℕ∞, (T : Set ℕ).IsAPOfLength l) ∧ Finset.Icc c v ⊆ T) ∧
      ∀ S ∈ E, ∃ a b : ℕ, u ≤ a ∧ a ≤ c ∧ c ≤ b ∧ b ≤ v ∧ S = Finset.Icc a b := by
  classical
  by_cases hne : E.Nonempty
  · let X := {S // S ∈ E}
    have hparam : ∀ S : X, ∃ a b : ℕ, S.val = Finset.Icc a b :=
      fun S => hinterval S.val S.property
    choose a b hrep using hparam
    have hab : ∀ S : X, a S ≤ c ∧ c ≤ b S := by
      intro S
      exact Finset.mem_Icc.mp (hrep S ▸ hc S.val S.property)
    have hbounds : ∀ S : X, 1 ≤ a S ∧ b S ≤ N := by
      intro S
      have hAS : a S ∈ S.val := by rw [hrep S]; exact Finset.mem_Icc.mpr ⟨le_rfl, (hab S).1.trans (hab S).2⟩
      have hBS : b S ∈ S.val := by rw [hrep S]; exact Finset.mem_Icc.mpr ⟨(hab S).1.trans (hab S).2, le_rfl⟩
      exact ⟨(Finset.mem_Icc.mp (hsub S.val S.property hAS)).1,
        (Finset.mem_Icc.mp (hsub S.val S.property hBS)).2⟩
    have hX : (Finset.univ : Finset X).Nonempty := by
      obtain ⟨S, hS⟩ := hne
      exact ⟨⟨S, hS⟩, Finset.mem_univ _⟩
    obtain ⟨L, _hL, hmin⟩ := Finset.exists_min_image Finset.univ a hX
    obtain ⟨R, _hR, hmax⟩ := Finset.exists_max_image Finset.univ b hX
    refine ⟨a L, b R, (hbounds L).1, (hab L).1, (hab R).2, (hbounds R).2, ?_, ?_, ?_⟩
    · apply Or.inr
      refine ⟨L.val, L.property, ?_, ?_⟩
      · rw [hrep L]
        exact interval_isAP ((hab L).1.trans (hab L).2)
      · intro x hx
        rw [hrep L]
        have hh := Finset.mem_Icc.mp hx
        exact Finset.mem_Icc.mpr ⟨hh.1, hh.2.trans (hab L).2⟩
    · apply Or.inr
      refine ⟨R.val, R.property, ?_, ?_⟩
      · rw [hrep R]
        exact interval_isAP ((hab R).1.trans (hab R).2)
      · intro x hx
        rw [hrep R]
        have hh := Finset.mem_Icc.mp hx
        exact Finset.mem_Icc.mpr ⟨(hab R).1.trans hh.1, hh.2⟩
    · intro S hS
      let T : X := ⟨S, hS⟩
      exact ⟨a T, b T, hmin T (Finset.mem_univ _), (hab T).1, (hab T).2,
        hmax T (Finset.mem_univ _), hrep T⟩
  · refine ⟨c, c, (Finset.mem_Icc.mp hcI).1, le_rfl, le_rfl,
      (Finset.mem_Icc.mp hcI).2, Or.inl rfl, Or.inl rfl, ?_⟩
    intro S hS
    exact False.elim (hne ⟨S, hS⟩)

theorem rooted_boundary_intervals_card_le {N c : ℕ} {E : Finset (Finset ℕ)}
    (hsub : ∀ S ∈ E, S ⊆ Finset.Icc 1 N) (hc : ∀ S ∈ E, c ∈ S)
    (hinterval : ∀ S ∈ E, ∃ a b : ℕ, S = Finset.Icc a b)
    (hboundary : ∀ S ∈ E, ¬StraddlesRoot c S) : E.card ≤ 2*N := by
  let L := (Finset.Icc 1 N).image (fun a => Finset.Icc a c)
  let R := (Finset.Icc 1 N).image (fun b => Finset.Icc c b)
  have hcover : E ⊆ L ∪ R := by
    intro S hS
    obtain ⟨a, b, hrep⟩ := hinterval S hS
    have hcb := Finset.mem_Icc.mp (hrep ▸ hc S hS)
    have haS : a ∈ S := by rw [hrep]; exact Finset.mem_Icc.mpr ⟨le_rfl, hcb.1.trans hcb.2⟩
    have hbS : b ∈ S := by rw [hrep]; exact Finset.mem_Icc.mpr ⟨hcb.1.trans hcb.2, le_rfl⟩
    by_cases ha : a = c
    · apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨b, hsub S hS hbS, by simpa only [ha] using hrep.symm⟩
    · have hb : b = c := by
        by_contra hn
        exact hboundary S hS ⟨⟨a, haS, by omega⟩, b, hbS, by omega⟩
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨a, hsub S hS haS, by simpa only [hb] using hrep.symm⟩
  have hL : L.card ≤ N := by
    have hh := Finset.card_image_le (s := Finset.Icc 1 N) (f := fun a => Finset.Icc a c)
    simpa only [Nat.card_Icc, Nat.add_sub_cancel] using hh
  have hR : R.card ≤ N := by
    have hh := Finset.card_image_le (s := Finset.Icc 1 N) (f := fun b => Finset.Icc c b)
    simpa only [Nat.card_Icc, Nat.add_sub_cancel] using hh
  have hh := (Finset.card_le_card hcover).trans (Finset.card_union_le L R)
  omega

end
/- LargeStepRooted -/

/- A joint bound for crooked members and rooted intervals meeting a sparse residue class. -/

section
open Finset

theorem crooked_and_intervals_meeting_sparse_residue_card_le {N c a k : ℕ}
    {F C E : Finset (Finset ℕ)} {P : Finset ℕ}
    (hN : 6 ≤ N) (hk : 3 ≤ k) (hcI : c ∈ Finset.Icc 1 N)
    (hF : Erdos272.IsArithInterSet N F) (hCF : C ⊆ F) (hEF : E ⊆ F)
    (hcC : ∀ S ∈ C, c ∈ S) (hC : ∀ S ∈ C, IsCrooked S)
    (hcE : ∀ S ∈ E, c ∈ S) (hE : ∀ S ∈ E, ∃ a b : ℕ, S = Finset.Icc a b)
    (hP : P ⊆ Finset.Icc 1 N) (hcP : c ∉ P) (hmod : ∀ x ∈ P, Nat.ModEq k a x)
    (hmet : ∀ S ∈ C, (S.erase c ∩ P).Nonempty) :
    (C.card : ℝ)+(E.card : ℝ) ≤ 5*(N : ℝ)^2/18+5*N+witnessExceptionBound N c := by
  classical
  let Good (S : Finset ℕ) := ∃ Q, IsWitnessPair S c Q ∧ ¬Disjoint Q P
  let G := C.filter Good
  let B := C.filter (fun S => ¬Good S)
  let D := E.filter (StraddlesRoot c)
  let J := E.filter (fun S => ¬StraddlesRoot c S)
  have hGC : G ⊆ C := Finset.filter_subset _ _
  have hBC : B ⊆ C := Finset.filter_subset _ _
  have hDE : D ⊆ E := Finset.filter_subset _ _
  have hJE : J ⊆ E := Finset.filter_subset _ _
  have hB : B.card ≤ witnessExceptionBound N c := by
    apply restricted_witness_bad_family_card_le (arithInterSet_mono hF (hBC.trans hCF))
      (fun S hS => hcC S (hBC hS)) (fun S hS => hC S (hBC hS))
      (fun S hS => hmet S (hBC hS))
    intro S hS Q hQ
    by_contra hn
    exact (Finset.mem_filter.mp hS).2 ⟨Q, hQ, hn⟩
  have hJ : J.card ≤ 2*N := rooted_boundary_intervals_card_le
    (fun S hS => Finset.mem_powerset.mp (hF.1 (hEF (hJE hS))))
    (fun S hS => hcE S (hJE hS)) (fun S hS => hE S (hJE hS))
    (fun S hS => (Finset.mem_filter.mp hS).2)
  obtain ⟨u, v, hu, huc, hcv, hvN, hleft, hright, henvelope⟩ := rooted_interval_envelope hcI
    (fun S hS => Finset.mem_powerset.mp (hF.1 (hEF hS))) hcE hE
  let Pool := crossPairPool (Finset.Ico u c) (Finset.Ioc c v) ∪
    meetingOutsidePairs ((Finset.Icc 1 N).erase c) ((Finset.Icc u v).erase c) P
  have hleftF : u = c ∨ ∃ T ∈ F, (∃ l : ℕ∞, (T : Set ℕ).IsAPOfLength l) ∧ Finset.Icc u c ⊆ T := by
    rcases hleft with hh | ⟨T, hT, hAP, hcover⟩
    · exact Or.inl hh
    · exact Or.inr ⟨T, hEF hT, hAP, hcover⟩
  have hrightF : v = c ∨ ∃ T ∈ F, (∃ l : ℕ∞, (T : Set ℕ).IsAPOfLength l) ∧ Finset.Icc c v ⊆ T := by
    rcases hright with hh | ⟨T, hT, hAP, hcover⟩
    · exact Or.inl hh
    · exact Or.inr ⟨T, hEF hT, hAP, hcover⟩
  have hGD : G.card+D.card ≤ Pool.card := by
    apply private_pairs_and_intervals_card_le hF (hGC.trans hCF) (hDE.trans hEF)
      (fun S hS => hcC S (hGC hS)) (fun S hS => hC S (hGC hS))
    · intro S hS
      obtain ⟨Q, hQ, hQP⟩ := (Finset.mem_filter.mp hS).2
      exact ⟨Q, hQ, crooked_witness_in_interval_pool hF (hCF (hGC hS)) huc hcv
        (hcC S (hGC hS)) (hC S (hGC hS)) hleftF hrightF hQ hQP⟩
    · intro S hS
      obtain ⟨l, r, hul, hlc, hcr, hrv, hrep⟩ := henvelope S (hDE hS)
      obtain ⟨⟨x, hx, hxc⟩, y, hy, hcy⟩ := (Finset.mem_filter.mp hS).2
      have hxI := Finset.mem_Icc.mp (hrep ▸ hx)
      have hyI := Finset.mem_Icc.mp (hrep ▸ hy)
      have hlc' : l < c := by omega
      have hcr' : c < r := by omega
      refine ⟨l, r, hlc', hcr', hrep, ?_⟩
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨(l,r), Finset.mem_product.mpr
        ⟨Finset.mem_Ico.mpr ⟨hul, hlc'⟩, Finset.mem_Ioc.mpr ⟨hcr', hrv⟩⟩, rfl⟩
  have hPool : (Pool.card : ℝ) ≤ 5*(N : ℝ)^2/18+3*N :=
    interval_witness_pool_card_le hN hk hu huc hcv hvN hP hcP hmod
  have hGDR : (G.card : ℝ)+(D.card : ℝ) ≤ Pool.card := by exact_mod_cast hGD
  have hBR : (B.card : ℝ) ≤ witnessExceptionBound N c := by exact_mod_cast hB
  have hJR : (J.card : ℝ) ≤ 2*(N : ℝ) := by exact_mod_cast hJ
  have hCpart : (G.card : ℝ)+(B.card : ℝ) = C.card := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := C) Good
  have hEpart : (D.card : ℝ)+(J.card : ℝ) = E.card := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := E) (StraddlesRoot c)
  linarith only [hGDR, hBR, hJR, hCpart, hEpart, hPool]

end
/- NonintervalProgressionCount -/

/- The progression count with ordinary intervals omitted. -/

section
open Finset

def IsInterval (S : Finset ℕ) : Prop := ∃ a b : ℕ, S = Finset.Icc a b

theorem natAP_step_one_isInterval (a m : ℕ) : IsInterval (natAP a 1 m) := by
  by_cases hm : m = 0
  · refine ⟨1, 0, ?_⟩
    simp [hm, natAP]
  · refine ⟨a, a+(m-1), ?_⟩
    ext x
    constructor
    · intro hx
      have hh := natAP_bounds_of_mem hx
      exact Finset.mem_Icc.mpr (by simpa only [Nat.mul_one] using hh)
    · intro hx
      obtain ⟨hax, hxtop⟩ := Finset.mem_Icc.mp hx
      exact mem_natAP.mpr ⟨x-a, by omega, by omega⟩

theorem reciprocal_square_tail_two_le (N : ℕ) :
    (∑ i ∈ Finset.Icc 2 N, ((i : ℝ)^2)⁻¹) ≤ 2/3 := by
  by_cases hN : 1 ≤ N
  · have hsplit : Finset.Icc 1 N = insert 1 (Finset.Icc 2 N) := by
      ext i
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hh := reciprocal_square_sum_le N
    rw [hsplit, Finset.sum_insert (by simp)] at hh
    norm_num only [Nat.cast_one, one_pow, inv_one] at hh
    linarith only [hh]
  · have hzero : N = 0 := by omega
    norm_num [hzero]

theorem progression_family_large_steps_card_le {N : ℕ} {F : Finset (Finset ℕ)}
    (hF : Erdos272.IsArithInterSet N F) (hcard : ∀ S ∈ F, 4 ≤ S.card)
    (hparam : ∀ S ∈ F, ∃ a d : ℕ, 2 ≤ d ∧ d ≤ N ∧ S = natAP a d S.card) :
    (F.card : ℝ) ≤ (N : ℝ)^2/6 + (N : ℝ)*reciprocalSum N + N := by
  classical
  have hparam' : ∀ S : Finset ℕ, ∃ a d : ℕ,
      S ∈ F → 2 ≤ d ∧ d ≤ N ∧ S = natAP a d S.card := by
    intro S
    by_cases hS : S ∈ F
    · obtain ⟨a,d,hd,hdN,hrep⟩ := hparam S hS
      exact ⟨a,d,fun _ => ⟨hd,hdN,hrep⟩⟩
    · exact ⟨0,2,fun hh => False.elim (hS hh)⟩
  choose a d hspec using hparam'
  have hmaps : Set.MapsTo d (F : Set (Finset ℕ)) (Finset.Icc 2 N : Set ℕ) := by
    intro S hS
    exact Finset.mem_Icc.mpr ⟨(hspec S hS).1, (hspec S hS).2.1⟩
  have hsumCard : (F.card : ℝ) =
      ∑ k ∈ Finset.Icc 2 N, ((F.filter (fun S => d S = k)).card : ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_fiberwise hmaps
  have hbound : ∀ k ∈ Finset.Icc 2 N,
      ((F.filter (fun S => d S = k)).card : ℝ) ≤
        (N : ℝ)^2/(4*(k : ℝ)^2)+(N : ℝ)/k+1 := by
    intro k hk
    apply same_step_family_card_le (by have hh := Finset.mem_Icc.mp hk; omega)
      (admissible_subfamily hF (Finset.filter_subset _ _))
    · intro S hS
      exact hcard S (Finset.mem_filter.mp hS).1
    · intro S hS
      obtain ⟨hSF, hdk⟩ := Finset.mem_filter.mp hS
      exact ⟨a S, by simpa only [hdk] using (hspec S hSF).2.2⟩
  have hinv : (∑ k ∈ Finset.Icc 2 N, (k : ℝ)⁻¹) ≤ reciprocalSum N := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro k hk
      have hh := Finset.mem_Icc.mp hk
      exact Finset.mem_Icc.mpr ⟨by omega, hh.2⟩
    · intro k _hk _hk'
      positivity
  have hcardI : ((Finset.Icc 2 N).card : ℝ) ≤ N := by
    exact_mod_cast (show (Finset.Icc 2 N).card ≤ N by rw [Nat.card_Icc]; omega)
  have hsum : (F.card : ℝ) ≤ (N : ℝ)^2/4*(∑ k ∈ Finset.Icc 2 N, ((k : ℝ)^2)⁻¹) +
      (N : ℝ)*(∑ k ∈ Finset.Icc 2 N, (k : ℝ)⁻¹)+(Finset.Icc 2 N).card := by
    calc
      (F.card : ℝ) ≤ ∑ k ∈ Finset.Icc 2 N,
          ((N : ℝ)^2/(4*(k : ℝ)^2)+(N : ℝ)/k+1) := by
        rw [hsumCard]
        exact Finset.sum_le_sum hbound
      _ = _ := by
        calc
          _ = ∑ k ∈ Finset.Icc 2 N,
              ((N : ℝ)^2/4*((k : ℝ)^2)⁻¹+(N : ℝ)*(k : ℝ)⁻¹+1) := by
            apply Finset.sum_congr rfl
            intro k _hk
            simp only [div_eq_mul_inv, mul_inv_rev]
            ring
          _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
            Finset.sum_const, nsmul_eq_mul, mul_one]
  have hquad := mul_le_mul_of_nonneg_left (reciprocal_square_tail_two_le N)
    (show 0 ≤ (N : ℝ)^2/4 by positivity)
  have hharm := mul_le_mul_of_nonneg_left hinv (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  linarith only [hsum, hquad, hharm, hcardI]

theorem noninterval_progression_family_card_le {N : ℕ} {F : Finset (Finset ℕ)}
    (hF : Erdos272.IsArithInterSet N F)
    (hAP : ∀ S ∈ F, ∃ l : ℕ∞, (S : Set ℕ).IsAPOfLength l)
    (hno : ∀ S ∈ F, ¬IsInterval S) :
    (F.card : ℝ) ≤ (N : ℝ)^2/6+(N : ℝ)*reciprocalSum N+19*N+3 := by
  classical
  let A := F.filter (fun S => 4 ≤ S.card)
  let B := F.filter (fun S => ¬4 ≤ S.card)
  have hA : (A.card : ℝ) ≤ (N : ℝ)^2/6+(N : ℝ)*reciprocalSum N+N := by
    apply progression_family_large_steps_card_le (admissible_subfamily hF (Finset.filter_subset _ _))
      (fun S hS => (Finset.mem_filter.mp hS).2)
    intro S hS
    obtain ⟨hSF, hsize⟩ := Finset.mem_filter.mp hS
    obtain ⟨l, hl⟩ := hAP S hSF
    obtain ⟨a,d,hd,hrep⟩ := nat_ap_eq_natAP hl (by omega : 2 ≤ S.card)
    have hd2 : 2 ≤ d := by
      by_contra hn
      have hd1 : d = 1 := by omega
      apply hno S hSF
      rw [hrep, hd1]
      exact natAP_step_one_isInterval _ _
    have hstep : a+d ∈ S := by
      rw [hrep]
      exact mem_natAP.mpr ⟨1, by omega, by simp⟩
    have hdN : d ≤ N := by
      have hh := Finset.mem_Icc.mp (Finset.mem_powerset.mp (hF.1 hSF) hstep)
      omega
    exact ⟨a,d,hd2,hdN,hrep⟩
  have hB : B.card ≤ 18*N+3 := by
    apply progression_family_small_card_le (admissible_subfamily hF (Finset.filter_subset _ _))
      (fun S hS => hAP S (Finset.mem_filter.mp hS).1)
    intro S hS
    have hh := (Finset.mem_filter.mp hS).2
    omega
  have hBR : (B.card : ℝ) ≤ 18*(N : ℝ)+3 := by exact_mod_cast hB
  have hpart : (A.card : ℝ)+(B.card : ℝ) = F.card := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := F) (fun S => 4 ≤ S.card)
  linarith only [hA, hBR, hpart]

end
/- LargeStepStraddling -/

/- The straddling gap when some avoiding progression has step at least three. -/

section
open Finset Filter

theorem interval_contains_straddled_root {c : ℕ} {S : Finset ℕ}
    (hinterval : IsInterval S) (hstraddle : StraddlesRoot c S) : c ∈ S := by
  obtain ⟨a,b,hrep⟩ := hinterval
  obtain ⟨⟨x,hx,hxc⟩,y,hy,hcy⟩ := hstraddle
  have hxI := Finset.mem_Icc.mp (hrep ▸ hx)
  have hyI := Finset.mem_Icc.mp (hrep ▸ hy)
  rw [hrep]
  exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩

theorem large_step_straddling_family_card_le {N c : ℕ} {F : Finset (Finset ℕ)}
    (hN : 6 ≤ N) (hcI : c ∈ Finset.Icc 1 N) (hF : Erdos272.IsArithInterSet N F)
    (hcC : ∀ S ∈ F, IsCrooked S → c ∈ S)
    (hstraddle : ∀ S ∈ F, c ∉ S → StraddlesRoot c S)
    (hlarge : ∃ P ∈ F, c ∉ P ∧ ∃ a k : ℕ, 3 ≤ k ∧ P = natAP a k P.card) :
    (F.card : ℝ) ≤ 4*(N : ℝ)^2/9+(N : ℝ)*reciprocalSum N+24*N+3+
      48*N*((Nat.log 2 N+1 : ℕ) : ℝ)^3 := by
  classical
  obtain ⟨P,hPF,hcP,a,k,hk,hrepP⟩ := hlarge
  let C := F.filter IsCrooked
  let H := F.filter (fun S => ¬IsCrooked S)
  let E := H.filter IsInterval
  let A := H.filter (fun S => ¬IsInterval S)
  have hCF : C ⊆ F := Finset.filter_subset _ _
  have hHF : H ⊆ F := Finset.filter_subset _ _
  have hEH : E ⊆ H := Finset.filter_subset _ _
  have hAH : A ⊆ H := Finset.filter_subset _ _
  have hCroot : ∀ S ∈ C, c ∈ S :=
    fun S hS => hcC S (hCF hS) (Finset.mem_filter.mp hS).2
  have hEroot : ∀ S ∈ E, c ∈ S := by
    intro S hS
    by_contra hc
    exact hc (interval_contains_straddled_root (Finset.mem_filter.mp hS).2
      (hstraddle S (hHF (hEH hS)) hc))
  have hPne : P.Nonempty := by
    obtain ⟨x,hx,_hxc⟩ := (hstraddle P hPF hcP).1
    exact ⟨x,hx⟩
  have hPmod : ∀ x ∈ P, Nat.ModEq k a x := by
    intro x hx
    obtain ⟨i,_hi,rfl⟩ := mem_natAP.mp (hrepP ▸ hx)
    change a%k = (a+i*k)%k
    simp only [Nat.add_mul_mod_self_right]
  have hmet : ∀ S ∈ C, (S.erase c ∩ P).Nonempty := by
    intro S hS
    obtain ⟨x,hx⟩ := arithInter_inter_nonempty hF hPF (hCF hS) hPne
    obtain ⟨hxP,hxS⟩ := Finset.mem_inter.mp hx
    have hxc : x ≠ c := by intro heq; exact hcP (heq ▸ hxP)
    exact ⟨x,Finset.mem_inter.mpr ⟨Finset.mem_erase.mpr ⟨hxc,hxS⟩,hxP⟩⟩
  have hCE := crooked_and_intervals_meeting_sparse_residue_card_le hN hk hcI hF hCF
    (hEH.trans hHF) hCroot (fun S hS => (Finset.mem_filter.mp hS).2) hEroot
    (fun S hS => (Finset.mem_filter.mp hS).2) (Finset.mem_powerset.mp (hF.1 hPF)) hcP hPmod hmet
  have hA := noninterval_progression_family_card_le (admissible_subfamily hF (hAH.trans hHF))
    (fun S hS => of_not_not (Finset.mem_filter.mp (hAH hS)).2)
    (fun S hS => (Finset.mem_filter.mp hS).2)
  have hCpart : (C.card : ℝ)+(H.card : ℝ) = F.card := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := F) IsCrooked
  have hHpart : (E.card : ℝ)+(A.card : ℝ) = H.card := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := H) IsInterval
  have herr : (witnessExceptionBound N c : ℝ) ≤ 48*(N : ℝ)*((Nat.log 2 N+1 : ℕ) : ℝ)^3 := by
    exact_mod_cast witnessExceptionBound_le_natLog hcI
  linarith only [hCE,hA,hCpart,hHpart,herr]

theorem eventually_large_step_straddling_gap :
    ∀ᶠ N : ℕ in atTop, ∀ (F : Finset (Finset ℕ)) (c : ℕ),
      c ∈ Finset.Icc 1 N → Erdos272.IsArithInterSet N F →
      (∀ S ∈ F, IsCrooked S → c ∈ S) →
      (∀ S ∈ F, c ∉ S → StraddlesRoot c S) →
      (∃ P ∈ F, c ∉ P ∧ ∃ a k : ℕ, 3 ≤ k ∧ P = natAP a k P.card) →
      (F.card : ℝ) ≤ 17*(N : ℝ)^2/36 := by
  filter_upwards [eventually_const_mul_natLog_pow_le 7200 3,
    Filter.eventually_ge_atTop 1000000] with N hlog hN F c hcI hF hcC hstraddle hlarge
  have hbound := large_step_straddling_family_card_le (by omega) hcI hF hcC hstraddle hlarge
  let L := Nat.log 2 N+1
  have hL : 1 ≤ L := by dsimp [L]; omega
  have hLL : L ≤ L^3 := by
    have hLsq : 1 ≤ L^2 := by nlinarith only [hL]
    have hh := Nat.mul_le_mul_left L hLsq
    nlinarith only [hh]
  have hLLR : (L : ℝ) ≤ (L : ℝ)^3 := by exact_mod_cast hLL
  have hrecip : reciprocalSum N ≤ 2*(L : ℝ) := by
    simpa only [L, Nat.cast_add, Nat.cast_one] using reciprocalSum_le_natLog N
  have hrecipmul := mul_le_mul_of_nonneg_left hrecip (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  have hLLmul := mul_le_mul_of_nonneg_left hLLR (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  have hlogR : 7200*(L : ℝ)^3 ≤ (N : ℝ) := by exact_mod_cast hlog
  have hlogmul := mul_le_mul_of_nonneg_left hlogR (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  have hNR : (1000000 : ℝ) ≤ N := by exact_mod_cast hN
  have hNmul := mul_le_mul_of_nonneg_left hNR (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  change (F.card : ℝ) ≤ 4*(N : ℝ)^2/9+(N : ℝ)*reciprocalSum N+24*N+3+48*N*(L : ℝ)^3 at hbound
  nlinarith only [hbound,hrecipmul,hLLmul,hlogmul,hNR,hNmul]

end
/- StraddlingReduction -/

/- Reduction of a near-extremal mixed family to a one-sided avoiding progression. -/

section
open Finset Filter

theorem straddling_AP_has_step_two_le {c : ℕ} {S : Finset ℕ}
    (hc : c ∉ S) (hstraddle : StraddlesRoot c S)
    (hAP : ∃ l : ℕ∞, (S : Set ℕ).IsAPOfLength l) :
    ∃ a d : ℕ, 2 ≤ d ∧ S = natAP a d S.card := by
  have hcard : 2 ≤ S.card := by
    by_contra hn
    obtain ⟨⟨x,hx,hxc⟩,y,hy,hcy⟩ := hstraddle
    have hxy := Finset.card_le_one.mp (by omega : S.card ≤ 1) x hx y hy
    omega
  obtain ⟨l,hl⟩ := hAP
  obtain ⟨a,d,hd,hrep⟩ := nat_ap_eq_natAP hl hcard
  have hd2 : 2 ≤ d := by
    by_contra hn
    have hd1 : d = 1 := by omega
    apply hc
    apply interval_contains_straddled_root (S := S) ?_ hstraddle
    rw [hrep,hd1]
    exact natAP_step_one_isInterval _ _
  exact ⟨a,d,hd2,hrep⟩

theorem eventually_straddling_gap :
    ∀ᶠ N : ℕ in atTop, ∀ (F : Finset (Finset ℕ)) (c : ℕ),
      c ∈ Finset.Icc 1 N → Erdos272.IsArithInterSet N F →
      (∀ S ∈ F, IsCrooked S → c ∈ S) →
      (∀ S ∈ F, c ∉ S → StraddlesRoot c S) →
      (∃ P ∈ F, c ∉ P) → (F.card : ℝ) ≤ 17*(N : ℝ)^2/36 := by
  classical
  filter_upwards [eventually_large_step_straddling_gap, eventually_two_step_straddling_gap]
    with N hlarge htwo F c hcI hF hcC hstraddle houtside
  by_cases hbig : ∃ P ∈ F, c ∉ P ∧ ∃ a k : ℕ, 3 ≤ k ∧ P = natAP a k P.card
  · exact hlarge F c hcI hF hcC hstraddle hbig
  · have hrep : ∀ S ∈ F, c ∉ S → ∃ a, S = natAP a 2 S.card := by
      intro S hS hcS
      have hAP : ∃ l : ℕ∞, (S : Set ℕ).IsAPOfLength l := by
        by_contra hnot
        exact hcS (hcC S hS hnot)
      obtain ⟨a,d,hd,hSd⟩ := straddling_AP_has_step_two_le hcS (hstraddle S hS hcS) hAP
      have hd2 : d = 2 := by
        by_contra hn
        exact hbig ⟨S,hS,hcS,a,d,by omega,hSd⟩
      exact ⟨a,by simpa only [hd2] using hSd⟩
    have htwobound := htwo F c hcI hF hrep (by
      obtain ⟨P,hP,hcP⟩ := houtside
      exact ⟨P,hP,hcP,hstraddle P hP hcP⟩)
    nlinarith only [htwobound,sq_nonneg (N : ℝ)]

theorem not_straddling_one_sided {c : ℕ} {S : Finset ℕ}
    (hc : c ∉ S) (hnot : ¬StraddlesRoot c S) :
    (∀ x ∈ S, x < c) ∨ ∀ x ∈ S, c < x := by
  by_cases hleft : ∃ x ∈ S, x < c
  · apply Or.inl
    intro y hy
    have hcy : y ≠ c := by intro heq; exact hc (heq ▸ hy)
    by_contra hn
    exact hnot ⟨hleft,y,hy,by omega⟩
  · apply Or.inr
    intro x hx
    have hxc : x ≠ c := by intro heq; exact hc (heq ▸ hx)
    by_contra hn
    exact hleft ⟨x,hx,by omega⟩

theorem eventually_near_extremal_one_sided_reduction :
    ∀ᶠ N : ℕ in atTop, ∀ (F : Finset (Finset ℕ)) (c : ℕ),
      c ∈ Finset.Icc 1 N → Erdos272.IsArithInterSet N F →
      (∀ S ∈ F, IsCrooked S → c ∈ S) →
      (N : ℝ)^2/2 ≤ (F.card : ℝ)+2048*N →
      (∀ S ∈ F, c ∈ S) ∨
        ∃ P ∈ F, c ∉ P ∧ ((∀ x ∈ P, x < c) ∨ ∀ x ∈ P, c < x) := by
  classical
  filter_upwards [eventually_straddling_gap,Filter.eventually_ge_atTop 1000000]
    with N hgap hN F c hcI hF hcC hlarge
  by_cases hcommon : ∀ S ∈ F, c ∈ S
  · exact Or.inl hcommon
  · apply Or.inr
    by_contra hno
    have hstraddle : ∀ S ∈ F, c ∉ S → StraddlesRoot c S := by
      intro S hS hcS
      by_contra hn
      exact hno ⟨S,hS,hcS,not_straddling_one_sided hcS hn⟩
    have houtside : ∃ P ∈ F, c ∉ P := by
      push Not at hcommon
      exact hcommon
    have hbound := hgap F c hcI hF hcC hstraddle houtside
    have hNR : (1000000 : ℝ) ≤ N := by exact_mod_cast hN
    have hNmul := mul_le_mul_of_nonneg_left hNR (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
    nlinarith only [hbound,hlarge,hNR,hNmul]

theorem eventually_one_sided_crooked_reduction :
    ∀ᶠ N : ℕ in atTop, ∀ F : Finset (Finset ℕ),
      Erdos272.IsArithInterSet N F → (N : ℝ)^2/2 ≤ (F.card : ℝ) →
      ∃ G : Finset (Finset ℕ), G ⊆ F ∧ Erdos272.IsArithInterSet N G ∧
        F.card ≤ G.card+2048*N ∧ ∃ c ∈ Finset.Icc 1 N,
        (∀ S ∈ G, IsCrooked S → c ∈ S) ∧
        ((∀ S ∈ G, c ∈ S) ∨ ∃ P ∈ G, c ∉ P ∧
          ((∀ x ∈ P, x < c) ∨ ∀ x ∈ P, c < x)) := by
  filter_upwards [eventually_common_crooked_reduction,eventually_near_extremal_one_sided_reduction]
    with N hcommon hside F hF hlarge
  obtain ⟨G,hGF,hG,hcard,c,hcI,hcG⟩ := hcommon F hF hlarge
  have hlargeG : (N : ℝ)^2/2 ≤ (G.card : ℝ)+2048*N := by
    have hcardR : (F.card : ℝ) ≤ (G.card : ℝ)+2048*N := by exact_mod_cast hcard
    exact hlarge.trans hcardR
  exact ⟨G,hGF,hG,hcard,c,hcI,hcG,hside G c hcI hG hcG hlargeG⟩

end
/- WitnessRedirect -/

/- Redirecting intrinsic witnesses through a neighbor of the root. -/

section
open Finset

theorem cover_union_of_shared_consecutive {S A B : Finset ℕ} {u v : ℕ}
    (hcon : ConsecutiveIn S u v) (hA : HasAPCover S A) (hB : HasAPCover S B)
    (huA : u ∈ A) (hvA : v ∈ A) (huB : u ∈ B) (hvB : v ∈ B) :
    HasAPCover S (A ∪ B) := by
  obtain ⟨U,hUS,hU,hAU⟩ := hA
  obtain ⟨V,hVS,hV,hBV⟩ := hB
  exact ⟨U ∪ V,Finset.union_subset hUS hVS,
    isAP_union_of_consecutive hU hV (hcon.subset hUS (hAU huA) (hAU hvA))
      (hcon.subset hVS (hBV huB) (hBV hvB)), Finset.union_subset_union hAU hBV⟩

theorem hasAPCover_mono {S A B : Finset ℕ} (hcover : HasAPCover S B) (hAB : A ⊆ B) :
    HasAPCover S A := by
  obtain ⟨U,hUS,hAP,hBU⟩ := hcover
  exact ⟨U,hUS,hAP,hAB.trans hBU⟩

theorem witness_pair_redirect_neighbor {S : Finset ℕ} {c z x y : ℕ}
    (hneighbor : ConsecutiveIn S c z ∨ ConsecutiveIn S z c)
    (hW : IsWitnessPair S c {x,y}) :
    IsWitnessPair S c {z,x} ∨ IsWitnessPair S c {z,y} := by
  classical
  by_cases hzx : z = x
  · exact Or.inr (by simpa only [hzx] using hW)
  by_cases hzy : z = y
  · exact Or.inl (by simpa only [hzy,Finset.pair_comm] using hW)
  have hz : z ∈ S.erase c := by
    rcases hneighbor with hcz | hzc
    · exact Finset.mem_erase.mpr ⟨hcz.2.2.1.ne',hcz.2.1⟩
    · exact Finset.mem_erase.mpr ⟨hzc.2.2.1.ne,hzc.1⟩
  have hx : x ∈ S.erase c := hW.2.1 (by simp)
  have hy : y ∈ S.erase c := hW.2.1 (by simp)
  by_contra hnot
  have hxnot : ¬IsWitnessPair S c {z,x} := fun hh => hnot (Or.inl hh)
  have hynot : ¬IsWitnessPair S c {z,y} := fun hh => hnot (Or.inr hh)
  have hX := hasAPCover_of_not_witness (by simp [hzx] : ({z,x} : Finset ℕ).card = 2)
    (show ({z,x} : Finset ℕ) ⊆ S.erase c by
      simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff]
      exact ⟨hz,hx⟩) hxnot
  have hY := hasAPCover_of_not_witness (by simp [hzy] : ({z,y} : Finset ℕ).card = 2)
    (show ({z,y} : Finset ℕ) ⊆ S.erase c by
      simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff]
      exact ⟨hz,hy⟩) hynot
  have hcover : HasAPCover S ((insert c {z,x}) ∪ (insert c {z,y})) := by
    rcases hneighbor with hcz | hzc
    · exact cover_union_of_shared_consecutive hcz hX hY (by simp) (by simp) (by simp) (by simp)
    · exact cover_union_of_shared_consecutive hzc hX hY (by simp) (by simp) (by simp) (by simp)
  apply hW.2.2
  apply hasAPCover_mono hcover
  intro t ht
  simp only [Finset.mem_insert,Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl <;> simp

theorem exists_root_neighbor_le {S : Finset ℕ} {c t R : ℕ}
    (hc : c ∈ S) (ht : t ∈ S) (htc : t ≠ c) (hcR : c ≤ R) (htR : t ≤ R) :
    ∃ z, z ≤ R ∧ (ConsecutiveIn S c z ∨ ConsecutiveIn S z c) := by
  rcases lt_or_gt_of_ne htc with htc | hct
  · obtain ⟨z,hzc⟩ := exists_consecutive_left_of_mem ht hc htc
    exact ⟨z,hzc.2.2.1.le.trans hcR,Or.inr hzc⟩
  · obtain ⟨z,hcz⟩ := exists_consecutive_right_of_mem hc ht hct
    have hzt : z ≤ t := by
      by_contra hn
      exact hcz.2.2.2 t ht ⟨hct,by omega⟩
    exact ⟨z,hzt.trans htR,Or.inl hcz⟩

theorem witness_meeting_right_can_reach_left {S Q : Finset ℕ} {c t L R : ℕ}
    (hc : c ∈ S) (ht : t ∈ S) (htc : t ≠ c) (hcR : c ≤ R) (htR : t ≤ R) (hLR : L ≤ R)
    (hW : IsWitnessPair S c Q) (hhigh : ∃ x ∈ Q, L ≤ x) :
    ∃ W, IsWitnessPair S c W ∧ (∃ x ∈ W, L ≤ x) ∧ ∃ y ∈ W, y ≤ R := by
  classical
  by_cases hlow : ∃ y ∈ Q, y ≤ R
  · exact ⟨Q,hW,hhigh,hlow⟩
  · obtain ⟨x,y,_hxy,hQrep⟩ := Finset.card_eq_two.mp hW.1
    have hRx : R < x := by
      by_contra hn
      apply hlow
      exact ⟨x,by simp [hQrep],by omega⟩
    have hRy : R < y := by
      by_contra hn
      apply hlow
      exact ⟨y,by simp [hQrep],by omega⟩
    obtain ⟨z,hzR,hneighbor⟩ := exists_root_neighbor_le hc ht htc hcR htR
    have hpair : IsWitnessPair S c {x,y} := by simpa only [hQrep] using hW
    rcases witness_pair_redirect_neighbor hneighbor hpair with hzx | hzy
    · exact ⟨{z,x},hzx,⟨x,by simp,hLR.trans hRx.le⟩,z,by simp,hzR⟩
    · exact ⟨{z,y},hzy,⟨y,by simp,hLR.trans hRy.le⟩,z,by simp,hzR⟩

end
/- FamilyReflection -/

/- Reflection preserves admissible families and their common crooked root. -/

section
open Finset

theorem reflectSet_inter {N : ℕ} {S T : Finset ℕ}
    (hS : S ⊆ Finset.Icc 1 N) (hT : T ⊆ Finset.Icc 1 N) :
    reflectSet N (S ∩ T) = reflectSet N S ∩ reflectSet N T := by
  ext x
  constructor
  · intro hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hyS,hyT⟩ := Finset.mem_inter.mp hy
    exact Finset.mem_inter.mpr ⟨Finset.mem_image.mpr ⟨y,hyS,rfl⟩,
      Finset.mem_image.mpr ⟨y,hyT,rfl⟩⟩
  · intro hx
    obtain ⟨hxS,hxT⟩ := Finset.mem_inter.mp hx
    obtain ⟨y,hy,hyx⟩ := Finset.mem_image.mp hxS
    obtain ⟨z,hz,hzx⟩ := Finset.mem_image.mp hxT
    have hyz : y = z := reflectPoint_injOn N (hS hy) (hT hz) (hyx.trans hzx.symm)
    exact Finset.mem_image.mpr ⟨y,Finset.mem_inter.mpr ⟨hy,hyz.symm ▸ hz⟩,hyx⟩

theorem reflectSet_isCrooked_iff {N : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.Icc 1 N) :
    IsCrooked (reflectSet N S) ↔ IsCrooked S := by
  constructor
  · intro hnot hAP
    exact hnot (reflectSet_isAP hS hAP)
  · intro hnot hAP
    have hh := reflectSet_isAP (reflectSet_subset hS) hAP
    rw [reflectSet_involutive hS] at hh
    exact hnot hh

def reflectFamily (N : ℕ) (F : Finset (Finset ℕ)) : Finset (Finset ℕ) := F.image (reflectSet N)

theorem reflectFamily_card {N : ℕ} {F : Finset (Finset ℕ)}
    (hsub : ∀ S ∈ F, S ⊆ Finset.Icc 1 N) : (reflectFamily N F).card = F.card := by
  apply Finset.card_image_of_injOn
  intro S hS T hT heq
  have hh := congrArg (reflectSet N) heq
  simpa only [reflectSet_involutive (hsub S hS), reflectSet_involutive (hsub T hT)] using hh

theorem reflectFamily_admissible {N : ℕ} {F : Finset (Finset ℕ)}
    (hF : Erdos272.IsArithInterSet N F) : Erdos272.IsArithInterSet N (reflectFamily N F) := by
  have hsub : ∀ S ∈ F, S ⊆ Finset.Icc 1 N := fun S hS => Finset.mem_powerset.mp (hF.1 hS)
  constructor
  · intro S hS
    obtain ⟨T,hT,rfl⟩ := Finset.mem_image.mp hS
    exact Finset.mem_powerset.mpr (reflectSet_subset (hsub T hT))
  · intro S hS T hT hST
    obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hS
    obtain ⟨B,hB,rfl⟩ := Finset.mem_image.mp hT
    have hAB : A ≠ B := by intro heq; apply hST; rw [heq]
    obtain ⟨l,hl,hAP⟩ := hF.2 hA hB hAB
    obtain ⟨m,hm⟩ := reflectSet_isAP (Finset.inter_subset_left.trans (hsub A hA)) ⟨l,hAP⟩
    have hne : (reflectSet N (A ∩ B)).Nonempty := (arithInter_nonempty hF hA hB hAB).image (reflectPoint N)
    have hmpos : 0 < m := by
      by_contra hn
      have hmzero : m = 0 := le_antisymm (le_of_not_gt hn) bot_le
      have hz := Set.IsAPOfLength.zero.mp (hmzero ▸ hm)
      obtain ⟨x,hx⟩ := hne
      have hxSet : x ∈ (reflectSet N (A ∩ B) : Set ℕ) := hx
      rw [hz] at hxSet
      exact hxSet
    refine ⟨m,hmpos,?_⟩
    simpa only [reflectSet_inter (hsub A hA) (hsub B hB)] using hm

theorem reflectFamily_crooked_root {N c : ℕ} {F : Finset (Finset ℕ)}
    (hsub : ∀ S ∈ F, S ⊆ Finset.Icc 1 N) (hc : ∀ S ∈ F, IsCrooked S → c ∈ S) :
    ∀ S ∈ reflectFamily N F, IsCrooked S → reflectPoint N c ∈ S := by
  intro S hS hcrooked
  obtain ⟨T,hT,rfl⟩ := Finset.mem_image.mp hS
  exact Finset.mem_image.mpr ⟨c,hc T hT ((reflectSet_isCrooked_iff (hsub T hT)).mp hcrooked),rfl⟩

theorem reflect_left_avoider {N c : ℕ} {S : Finset ℕ}
    (hsub : S ⊆ Finset.Icc 1 N) (hcI : c ∈ Finset.Icc 1 N)
    (hleft : ∀ x ∈ S, x < c) : ∀ x ∈ reflectSet N S, reflectPoint N c < x := by
  intro x hx
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
  have hcy := hleft y hy
  have hyN := Finset.mem_Icc.mp (hsub hy)
  have hcN := Finset.mem_Icc.mp hcI
  dsimp only [reflectPoint]
  omega

end
/- RightAvoiderReduction -/

/- Orienting the remaining structural case so an avoiding progression lies to the right. -/

section
open Finset Filter

theorem right_avoider_reduction_of_one_sided {N c : ℕ} {F : Finset (Finset ℕ)}
    (hcI : c ∈ Finset.Icc 1 N) (hF : Erdos272.IsArithInterSet N F)
    (hcC : ∀ S ∈ F, IsCrooked S → c ∈ S)
    (hcase : (∀ S ∈ F, c ∈ S) ∨
      ∃ P ∈ F, c ∉ P ∧ ((∀ x ∈ P, x < c) ∨ ∀ x ∈ P, c < x)) :
    ∃ G : Finset (Finset ℕ), Erdos272.IsArithInterSet N G ∧ G.card = F.card ∧
      ∃ d ∈ Finset.Icc 1 N, (∀ S ∈ G, IsCrooked S → d ∈ S) ∧
        ((∀ S ∈ G, d ∈ S) ∨ ∃ P ∈ G, ∀ x ∈ P, d < x) := by
  have hsub : ∀ S ∈ F, S ⊆ Finset.Icc 1 N := fun S hS => Finset.mem_powerset.mp (hF.1 hS)
  rcases hcase with hcommon | ⟨P,hP,_hcP,hleft | hright⟩
  · exact ⟨F,hF,rfl,c,hcI,hcC,Or.inl hcommon⟩
  · refine ⟨reflectFamily N F,reflectFamily_admissible hF,reflectFamily_card hsub,
      reflectPoint N c,reflectPoint_mem hcI,reflectFamily_crooked_root hsub hcC,Or.inr ?_⟩
    exact ⟨reflectSet N P,Finset.mem_image.mpr ⟨P,hP,rfl⟩,
      reflect_left_avoider (hsub P hP) hcI hleft⟩
  · exact ⟨F,hF,rfl,c,hcI,hcC,Or.inr ⟨P,hP,hright⟩⟩

theorem eventually_right_avoider_crooked_reduction :
    ∀ᶠ N : ℕ in atTop, ∀ F : Finset (Finset ℕ),
      Erdos272.IsArithInterSet N F → (N : ℝ)^2/2 ≤ (F.card : ℝ) →
      ∃ G : Finset (Finset ℕ), Erdos272.IsArithInterSet N G ∧
        F.card ≤ G.card+2048*N ∧ ∃ c ∈ Finset.Icc 1 N,
        (∀ S ∈ G, IsCrooked S → c ∈ S) ∧
        ((∀ S ∈ G, c ∈ S) ∨ ∃ P ∈ G, ∀ x ∈ P, c < x) := by
  filter_upwards [eventually_one_sided_crooked_reduction] with N hreduce F hF hlarge
  obtain ⟨G,_hGF,hG,hcard,c,hcI,hcG,hcase⟩ := hreduce F hF hlarge
  obtain ⟨H,hH,hHcard,d,hdI,hdH,hHcase⟩ := right_avoider_reduction_of_one_sided hcI hG hcG hcase
  refine ⟨H,hH,?_,d,hdI,hdH,hHcase⟩
  simpa only [hHcard] using hcard

end
/- OutsideEnvelope -/

/- Extremal endpoints for the avoiding family in the remaining one-sided case. -/

section
open Finset

theorem admissible_member_nonempty_of_card_two_le {N : ℕ} {F : Finset (Finset ℕ)}
    (hF : Erdos272.IsArithInterSet N F) (hcard : 2 ≤ F.card) : ∀ S ∈ F, S.Nonempty := by
  intro S hS
  have hpos : 0 < (F.erase S).card := by rw [Finset.card_erase_of_mem hS]; omega
  obtain ⟨T,hT⟩ := Finset.card_pos.mp hpos
  obtain ⟨hTS,hTF⟩ := Finset.mem_erase.mp hT
  exact (arithInter_nonempty hF hS hTF hTS.symm).mono Finset.inter_subset_left

theorem near_extremal_card_two_le {N : ℕ} {F : Finset (Finset ℕ)}
    (hN : 10000 ≤ N) (hlarge : (N : ℝ)^2/2 ≤ (F.card : ℝ)+2048*N) : 2 ≤ F.card := by
  by_contra hn
  have hcard : (F.card : ℝ) ≤ 1 := by exact_mod_cast (show F.card ≤ 1 by omega)
  have hNR : (10000 : ℝ) ≤ N := by exact_mod_cast hN
  have hNmul := mul_le_mul_of_nonneg_left hNR (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  nlinarith only [hcard,hNR,hNmul,hlarge]

theorem outside_member_envelope {N c : ℕ} {F : Finset (Finset ℕ)}
    (hF : Erdos272.IsArithInterSet N F) (hNonempty : ∀ S ∈ F, S.Nonempty)
    (hHasRight : ∃ P ∈ F, ∀ x ∈ P, c < x) :
    ∃ L R : ℕ, c < L ∧ L ≤ R ∧ R ≤ N ∧
      (∃ P ∈ F, c ∉ P ∧ ∀ x ∈ P, L ≤ x) ∧
      (∃ T ∈ F, c ∉ T ∧ ∀ x ∈ T, x ≤ R) ∧
      ∀ S ∈ F, c ∉ S →
        (∃ a ∈ S, a ≤ L ∧ ∀ x ∈ S, a ≤ x) ∧
        ∃ b ∈ S, R ≤ b ∧ ∀ x ∈ S, x ≤ b := by
  classical
  let A := F.filter (fun S => c ∉ S)
  let X := {S // S ∈ A}
  have hXF : ∀ S : X, S.val ∈ F := fun S => (Finset.mem_filter.mp S.property).1
  let a (S : X) := S.val.min' (hNonempty S.val (hXF S))
  let b (S : X) := S.val.max' (hNonempty S.val (hXF S))
  have ha : ∀ S : X, a S ∈ S.val := fun S => Finset.min'_mem _ _
  have hb : ∀ S : X, b S ∈ S.val := fun S => Finset.max'_mem _ _
  have hamin : ∀ S : X, ∀ x ∈ S.val, a S ≤ x := fun S x hx => Finset.min'_le _ _ hx
  have hbmax : ∀ S : X, ∀ x ∈ S.val, x ≤ b S := fun S x hx => Finset.le_max' _ _ hx
  obtain ⟨P,hPF,hRight⟩ := hHasRight
  have hcP : c ∉ P := by intro hh; exact (lt_irrefl c) (hRight c hh)
  let P₀ : X := ⟨P,Finset.mem_filter.mpr ⟨hPF,hcP⟩⟩
  have hX : (Finset.univ : Finset X).Nonempty := ⟨P₀,Finset.mem_univ _⟩
  obtain ⟨PL,_hPL,hmaxa⟩ := Finset.exists_max_image Finset.univ a hX
  obtain ⟨PR,_hPR,hminb⟩ := Finset.exists_min_image Finset.univ b hX
  have hcL : c < a PL := (hRight (a P₀) (ha P₀)).trans_le (hmaxa P₀ (Finset.mem_univ _))
  obtain ⟨x,hx⟩ := arithInter_inter_nonempty hF (hXF PL) (hXF PR) (hNonempty PL.val (hXF PL))
  obtain ⟨hxPL,hxPR⟩ := Finset.mem_inter.mp hx
  have hLR : a PL ≤ b PR := (hamin PL x hxPL).trans (hbmax PR x hxPR)
  have hRN : b PR ≤ N := (Finset.mem_Icc.mp (Finset.mem_powerset.mp (hF.1 (hXF PR)) (hb PR))).2
  refine ⟨a PL,b PR,hcL,hLR,hRN,?_,?_,?_⟩
  · exact ⟨PL.val,hXF PL,(Finset.mem_filter.mp PL.property).2,hamin PL⟩
  · exact ⟨PR.val,hXF PR,(Finset.mem_filter.mp PR.property).2,hbmax PR⟩
  · intro S hS hcS
    let T : X := ⟨S,Finset.mem_filter.mpr ⟨hS,hcS⟩⟩
    exact ⟨⟨a T,ha T,hmaxa T (Finset.mem_univ _),hamin T⟩,
      b T,hb T,hminb T (Finset.mem_univ _),hbmax T⟩

theorem witness_reaches_avoider_endpoint {N c L R : ℕ} {F : Finset (Finset ℕ)}
    {S T Q : Finset ℕ} (hF : Erdos272.IsArithInterSet N F) (hS : S ∈ F) (hT : T ∈ F)
    (hcS : c ∈ S) (hcT : c ∉ T) (hTbound : ∀ x ∈ T, x ≤ R)
    (hcR : c ≤ R) (hLR : L ≤ R) (hQ : IsWitnessPair S c Q) (hhigh : ∃ x ∈ Q, L ≤ x) :
    ∃ W, IsWitnessPair S c W ∧ (∃ x ∈ W, L ≤ x) ∧ ∃ y ∈ W, y ≤ R := by
  obtain ⟨t,ht⟩ := arithInter_inter_nonempty hF hS hT ⟨c,hcS⟩
  obtain ⟨htS,htT⟩ := Finset.mem_inter.mp ht
  have htc : t ≠ c := by intro heq; exact hcT (heq ▸ htT)
  exact witness_meeting_right_can_reach_left hcS htS htc hcR (hTbound t htT) hLR hQ hhigh

end
/- WitnessPreference -/

/- Choosing a middle witness first, then a shortest exterior witness. -/

section
open Finset

def HasMiddleWitness (S : Finset ℕ) (c L R : ℕ) : Prop :=
  ∃ Q, IsWitnessPair S c Q ∧ ∃ z ∈ Q, L ≤ z ∧ z ≤ R

theorem pair_eq_of_card_two_of_mem {Q : Finset ℕ} {x y : ℕ}
    (hcard : Q.card = 2) (hx : x ∈ Q) (hy : y ∈ Q) (hxy : x ≠ y) : Q = {x,y} := by
  have hsub : ({x,y} : Finset ℕ) ⊆ Q := by
    simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff]
    exact ⟨hx,hy⟩
  exact (Finset.eq_of_subset_of_card_le hsub (by simp [hcard,hxy])).symm

theorem preferred_one_sided_witness {S : Finset ℕ} {c L R : ℕ} (hLR : L ≤ R)
    (hreach : ∃ W, IsWitnessPair S c W ∧ (∃ x ∈ W, L ≤ x) ∧ ∃ y ∈ W, y ≤ R) :
    ∃ x p : ℕ, IsWitnessPair S c {x,p} ∧ L ≤ p ∧
      (p ≤ R ∨ (x < L ∧ R < p ∧ ¬HasMiddleWitness S c L R ∧
        ∀ u v : ℕ, u < L → R < v → IsWitnessPair S c {u,v} → p-x ≤ v-u)) := by
  classical
  by_cases hmiddle : HasMiddleWitness S c L R
  · obtain ⟨Q,hQ,p,hp,hLp,hpR⟩ := hmiddle
    obtain ⟨a,b,_hab,hrep⟩ := Finset.card_eq_two.mp hQ.1
    rw [hrep] at hp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hp
    rcases hp with hpa | hpb
    · exact ⟨b,p,by simpa only [hrep,hpa,Finset.pair_comm] using hQ,hLp,Or.inl hpR⟩
    · exact ⟨a,p,by simpa only [hrep,hpb] using hQ,hLp,Or.inl hpR⟩
  · obtain ⟨W,hW,⟨p,hp,hLp⟩,x,hx,hxR⟩ := hreach
    have hRp : R < p := by
      by_contra hn
      exact hmiddle ⟨W,hW,p,hp,hLp,by omega⟩
    have hxL : x < L := by
      by_contra hn
      exact hmiddle ⟨W,hW,x,hx,by omega,hxR⟩
    have hWrep : W = {x,p} := pair_eq_of_card_two_of_mem hW.1 hx hp (by omega)
    have hpair : IsWitnessPair S c {x,p} := by simpa only [hWrep] using hW
    let Candidate (d : ℕ) := ∃ u v : ℕ,
      u < L ∧ R < v ∧ IsWitnessPair S c {u,v} ∧ v-u = d
    have hex : ∃ d, Candidate d := ⟨p-x,x,p,hxL,hRp,hpair,rfl⟩
    obtain ⟨u,v,huL,hRv,hUV,hd⟩ := Nat.find_spec hex
    refine ⟨u,v,hUV,hLR.trans hRv.le,Or.inr ⟨huL,hRv,hmiddle,?_⟩⟩
    intro a b haL hRb hAB
    rw [hd]
    exact Nat.find_min' hex ⟨a,b,haL,hRb,hAB,rfl⟩

end
/- CornerCrop -/

/- A shortest preferred corner witness has a two-point or crooked interval trace. -/

section
open Finset

theorem exists_consecutive_across_cut {S : Finset ℕ} {R x y : ℕ}
    (hx : x ∈ S) (hy : y ∈ S) (hxR : x ≤ R) (hRy : R < y) :
    ∃ b a, ConsecutiveIn S b a ∧ x ≤ b ∧ b ≤ R ∧ R < a ∧ a ≤ y := by
  let B := S.filter (fun z => z ≤ R)
  let A := S.filter (fun z => R < z)
  have hxB : x ∈ B := Finset.mem_filter.mpr ⟨hx,hxR⟩
  have hyA : y ∈ A := Finset.mem_filter.mpr ⟨hy,hRy⟩
  have hB : B.Nonempty := ⟨x,hxB⟩
  have hA : A.Nonempty := ⟨y,hyA⟩
  let b := B.max' hB
  let a := A.min' hA
  have hbB : b ∈ B := Finset.max'_mem B hB
  have haA : a ∈ A := Finset.min'_mem A hA
  obtain ⟨hbS,hbR⟩ := Finset.mem_filter.mp hbB
  obtain ⟨haS,hRa⟩ := Finset.mem_filter.mp haA
  refine ⟨b,a,⟨hbS,haS,by omega,?_⟩,Finset.le_max' B x hxB,hbR,hRa,
    Finset.min'_le A y hyA⟩
  intro z hz hbetween
  by_cases hzR : z ≤ R
  · have hzB : z ∈ B := Finset.mem_filter.mpr ⟨hz,hzR⟩
    have hzb : z ≤ b := Finset.le_max' B z hzB
    omega
  · have hzA : z ∈ A := Finset.mem_filter.mpr ⟨hz,by omega⟩
    have haz : a ≤ z := Finset.min'_le A z hzA
    omega

theorem card_inter_Icc_le_two_of_consecutive {S : Finset ℕ} {x y : ℕ}
    (hcon : ConsecutiveIn S x y) : (S ∩ Finset.Icc x y).card ≤ 2 := by
  have hsub : S ∩ Finset.Icc x y ⊆ ({x,y} : Finset ℕ) := by
    intro z hz
    obtain ⟨hzS,hzI⟩ := Finset.mem_inter.mp hz
    obtain ⟨hxz,hzy⟩ := Finset.mem_Icc.mp hzI
    by_cases hzx : z = x
    · simp [hzx]
    by_cases hzy' : z = y
    · simp [hzy']
    exact False.elim (hcon.2.2.2 z hzS ⟨by omega,by omega⟩)
  have hh := Finset.card_le_card hsub
  simpa only [Finset.card_pair hcon.2.2.1.ne] using hh

theorem preferred_corner_crop_AP_card_le_two {S : Finset ℕ} {c x p L R : ℕ}
    (hcx : c < x) (hxL : x < L) (hLR : L ≤ R) (hRp : R < p)
    (hW : IsWitnessPair S c {x,p}) (hnoMiddle : ¬HasMiddleWitness S c L R)
    (hminimum : ∀ u v : ℕ, u < L → R < v → IsWitnessPair S c {u,v} → p-x ≤ v-u)
    (hAP : ∃ l : ℕ∞, ((S ∩ Finset.Icc x p : Finset ℕ) : Set ℕ).IsAPOfLength l) :
    (S ∩ Finset.Icc x p).card ≤ 2 := by
  by_contra hsize
  have hxS : x ∈ S := Finset.mem_of_mem_erase (hW.2.1 (by simp))
  have hpS : p ∈ S := Finset.mem_of_mem_erase (hW.2.1 (by simp))
  obtain ⟨b,a,hcon,hxb,hbR,hRa,hap⟩ := exists_consecutive_across_cut hxS hpS
    (hxL.le.trans hLR) hRp
  have hends : b ≠ x ∨ a ≠ p := by
    by_contra hn
    have hb : b = x := by by_contra hh; exact hn (Or.inl hh)
    have ha : a = p := by by_contra hh; exact hn (Or.inr hh)
    exact hsize (card_inter_Icc_le_two_of_consecutive (by simpa only [hb,ha] using hcon))
  have hshort : a-b < p-x := by
    rcases hends with hb | ha <;> omega
  have hnoBA : ¬IsWitnessPair S c {b,a} := by
    intro hBA
    by_cases hLb : L ≤ b
    · exact hnoMiddle ⟨{b,a},hBA,b,by simp,hLb,hbR⟩
    · have hh := hminimum b a (by omega) hRa hBA
      omega
  have hbSc : b ∈ S.erase c := Finset.mem_erase.mpr ⟨by omega,hcon.1⟩
  have haSc : a ∈ S.erase c := Finset.mem_erase.mpr ⟨by omega,hcon.2.1⟩
  have hcover := hasAPCover_of_not_witness
    (by simp [hcon.2.2.1.ne] : ({b,a} : Finset ℕ).card = 2)
    (show ({b,a} : Finset ℕ) ⊆ S.erase c by
      simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff]
      exact ⟨hbSc,haSc⟩) hnoBA
  obtain ⟨U,hUS,hUAP,hCU⟩ := hcover
  let C := S ∩ Finset.Icc x p
  have hbC : b ∈ C := Finset.mem_inter.mpr ⟨hcon.1,Finset.mem_Icc.mpr ⟨hxb,by omega⟩⟩
  have haC : a ∈ C := Finset.mem_inter.mpr ⟨hcon.2.1,Finset.mem_Icc.mpr ⟨by omega,hap⟩⟩
  have hAPunion : ∃ l : ℕ∞, ((U ∪ C : Finset ℕ) : Set ℕ).IsAPOfLength l :=
    isAP_union_of_consecutive hUAP hAP
      (hcon.subset hUS (hCU (by simp)) (hCU (by simp)))
      (hcon.subset Finset.inter_subset_left hbC haC)
  apply hW.2.2
  refine ⟨U ∪ C,Finset.union_subset hUS Finset.inter_subset_left,hAPunion,?_⟩
  intro z hz
  simp only [Finset.mem_insert,Finset.mem_singleton] at hz
  rcases hz with rfl | rfl | rfl
  · exact Finset.mem_union_left _ (hCU (by simp))
  · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hxS,Finset.mem_Icc.mpr ⟨le_rfl,by omega⟩⟩)
  · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hpS,Finset.mem_Icc.mpr ⟨by omega,le_rfl⟩⟩)

theorem preferred_corner_crop_dichotomy {S : Finset ℕ} {c x p L R : ℕ}
    (hcx : c < x) (hxL : x < L) (hLR : L ≤ R) (hRp : R < p)
    (hW : IsWitnessPair S c {x,p}) (hnoMiddle : ¬HasMiddleWitness S c L R)
    (hminimum : ∀ u v : ℕ, u < L → R < v → IsWitnessPair S c {u,v} → p-x ≤ v-u) :
    S ∩ Finset.Icc x p = {x,p} ∨ IsCrooked (S ∩ Finset.Icc x p) := by
  by_cases hcrooked : IsCrooked (S ∩ Finset.Icc x p)
  · exact Or.inr hcrooked
  · apply Or.inl
    have hcard := preferred_corner_crop_AP_card_le_two hcx hxL hLR hRp hW hnoMiddle hminimum
      (of_not_not hcrooked)
    have hxS : x ∈ S := Finset.mem_of_mem_erase (hW.2.1 (by simp))
    have hpS : p ∈ S := Finset.mem_of_mem_erase (hW.2.1 (by simp))
    have hsub : ({x,p} : Finset ℕ) ⊆ S ∩ Finset.Icc x p := by
      simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff]
      exact ⟨Finset.mem_inter.mpr ⟨hxS,Finset.mem_Icc.mpr ⟨le_rfl,by omega⟩⟩,
        Finset.mem_inter.mpr ⟨hpS,Finset.mem_Icc.mpr ⟨by omega,le_rfl⟩⟩⟩
    exact (Finset.eq_of_subset_of_card_le hsub (by
      simpa only [Finset.card_pair (show x ≠ p by omega)] using hcard)).symm

end
/- OrderedRowCount -/

/- The shift between successive occupied rows in the one-sided interval count. -/

section
open Finset

theorem ordered_row_sum_le_max_tail (A : Finset ℕ) (H J : ℕ → ℕ) (X : ℕ) :
    (∀ i ∈ A, J i ≤ X+1) →
    (∀ i ∈ A, ∀ j ∈ A, i < j → H i+J j ≤ X+1) →
    ∀ t ∈ A, (∀ i ∈ A, i ≤ t) →
      (∑ i ∈ A, (H i+J i)) ≤ A.card*(X+1)+H t := by
  induction A using Finset.induction_on_max with
  | empty => simp
  | @insert a A hmax ih =>
    intro hJ hcross t ht htop
    have haA : a ∉ A := by intro ha; exact (lt_irrefl a) (hmax a ha)
    have hat : a ≤ t := htop a (Finset.mem_insert_self _ _)
    have hta : t = a := by
      rcases Finset.mem_insert.mp ht with heq | htA
      · exact heq
      · have hlt := hmax t htA
        omega
    subst t
    by_cases hne : A.Nonempty
    · let m := A.max' hne
      have hmA : m ∈ A := Finset.max'_mem A hne
      have hmmax : ∀ i ∈ A, i ≤ m := fun i hi => Finset.le_max' A i hi
      have hih := ih (fun i hi => hJ i (Finset.mem_insert_of_mem hi))
        (fun i hi j hj hij => hcross i (Finset.mem_insert_of_mem hi) j
          (Finset.mem_insert_of_mem hj) hij) m hmA hmmax
      have hstep := hcross m (Finset.mem_insert_of_mem hmA) a
        (Finset.mem_insert_self _ _) (hmax m hmA)
      rw [Finset.sum_insert haA,Finset.card_insert_of_notMem haA]
      nlinarith only [hih,hstep]
    · have hAempty : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      have hJa := hJ a (Finset.mem_insert_self _ _)
      simpa [hAempty,Nat.add_comm] using Nat.add_le_add_left hJa (H a)

theorem ordered_row_sum_le (A : Finset ℕ) (H J : ℕ → ℕ) (X : ℕ)
    (hH : ∀ i ∈ A, H i ≤ X) (hJ : ∀ i ∈ A, J i ≤ X)
    (hcross : ∀ i ∈ A, ∀ j ∈ A, i < j → H i+J j ≤ X+1) :
    (∑ i ∈ A, (H i+J i)) ≤ A.card*(X+1)+X := by
  by_cases hne : A.Nonempty
  · let t := A.max' hne
    have ht : t ∈ A := Finset.max'_mem A hne
    have hh := ordered_row_sum_le_max_tail A H J X
      (fun i hi => (hJ i hi).trans (Nat.le_succ X)) hcross t ht
      (fun i hi => Finset.le_max' A i hi)
    exact hh.trans (Nat.add_le_add_left (hH t ht) _)
  · have hz : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp only [hz,Finset.sum_empty,Finset.card_empty,Nat.zero_mul,Nat.zero_add,Nat.zero_le]

theorem ordered_row_total_le {I A : Finset ℕ} (hAI : A ⊆ I) (H J : ℕ → ℕ) (X : ℕ)
    (hH : ∀ i ∈ A, H i ≤ X) (hJ : ∀ i ∈ A, J i ≤ X)
    (hcross : ∀ i ∈ A, ∀ j ∈ A, i < j → H i+J j ≤ X+1)
    (hinactive : ∀ i ∈ I \ A, H i+J i ≤ X) :
    (∑ i ∈ I, (H i+J i)) ≤ I.card*X+I.card+X := by
  have hactive := ordered_row_sum_le A H J X hH hJ hcross
  have hrest : (∑ i ∈ I \ A, (H i+J i)) ≤ (I \ A).card*X := by
    simpa using Finset.sum_le_sum hinactive
  have hsum := Finset.sum_sdiff hAI (f := fun i => H i+J i)
  have hcards := Finset.card_sdiff_add_card_eq_card hAI
  have hAcard := Finset.card_le_card hAI
  nlinarith only [hactive,hrest,hsum,hcards,hAcard]

end
/- IntervalRowLemmas -/

/- Endpoint constraints and private-coordinate counts for the one-sided rows. -/

section
open Finset

theorem pair_crop_meets_later_interval {S : Finset ℕ} {i p j l : ℕ}
    (hcrop : S ∩ Finset.Icc i p = {i,p}) (hmet : (S ∩ Finset.Icc j l).Nonempty)
    (hij : i < j) : p ≤ l := by
  by_contra hn
  obtain ⟨z,hz⟩ := hmet
  obtain ⟨hzS,hzI⟩ := Finset.mem_inter.mp hz
  obtain ⟨hjz,hzl⟩ := Finset.mem_Icc.mp hzI
  have hzCrop : z ∈ S ∩ Finset.Icc i p :=
    Finset.mem_inter.mpr ⟨hzS,Finset.mem_Icc.mpr ⟨by omega,by omega⟩⟩
  rw [hcrop] at hzCrop
  simp only [Finset.mem_insert,Finset.mem_singleton] at hzCrop
  omega

theorem crooked_crop_forces_interval_end_lt {S : Finset ℕ} {i p f : ℕ}
    (hcrooked : IsCrooked (S ∩ Finset.Icc i p))
    (hAP : ∃ l : ℕ∞, ((S ∩ Finset.Icc i f : Finset ℕ) : Set ℕ).IsAPOfLength l) : f < p := by
  by_contra hn
  have hh := ap_inter_Icc hAP (u := i) (v := p)
  have heq : (S ∩ Finset.Icc i f) ∩ Finset.Icc i p = S ∩ Finset.Icc i p := by
    ext x
    simp only [Finset.mem_inter,Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hxS,hix,_hxf⟩,_hix',hxp⟩
      exact ⟨hxS,hix,hxp⟩
    · rintro ⟨hxS,hix,hxp⟩
      exact ⟨⟨hxS,hix,by omega⟩,hix,hxp⟩
  rw [heq] at hh
  exact hcrooked hh

theorem witness_row_card_le_interval {N c i u v : ℕ} {F H : Finset (Finset ℕ)}
    (hF : Erdos272.IsArithInterSet N F) (hHF : H ⊆ F) (hc : ∀ S ∈ H, c ∈ S)
    (p : {S // S ∈ H} → ℕ) (hW : ∀ S, IsWitnessPair S.val c {i,p S})
    (hp : ∀ S, p S ∈ Finset.Icc u v) : H.card ≤ (Finset.Icc u v).card := by
  have hinj : Function.Injective p := by
    intro S T heq
    apply Subtype.ext
    exact (witness_pair_private hF (hHF S.property) (hHF T.property)
      (hc S.val S.property) (hc T.val T.property) (hW S) (by
        rw [heq]
        exact (hW T).2.1.trans (Finset.erase_subset _ _))).symm
  have hh := Finset.card_le_card_of_injOn p
    (show Set.MapsTo p ((Finset.univ : Finset {S // S ∈ H}) : Set {S // S ∈ H})
      (Finset.Icc u v : Set ℕ) from fun S _hS => hp S) hinj.injOn
  simpa only [Finset.card_univ,Fintype.card_coe] using hh

theorem interval_row_card_le {i u v : ℕ} {E : Finset (Finset ℕ)}
    (hrep : ∀ S ∈ E, ∃ q ∈ Finset.Icc u v, S = Finset.Icc i q) :
    E.card ≤ (Finset.Icc u v).card := by
  have hsub : E ⊆ (Finset.Icc u v).image (fun q => Finset.Icc i q) := by
    intro S hS
    obtain ⟨q,hq,hS⟩ := hrep S hS
    exact Finset.mem_image.mpr ⟨q,hq,hS.symm⟩
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

theorem three_row_blocks_card_le {A B E N R l m : ℕ}
    (hRl : R ≤ l) (hlm : l ≤ m) (hmN : m ≤ N+1)
    (hA : A ≤ l-R) (hE : E ≤ m-l) (hB : B ≤ N+1-m) :
    A+E+B ≤ N-R+1 := by omega

end
/- IntervalRowCut -/

/- A row of outside intervals and crooked traces has one common endpoint cutoff. -/

section
open Finset

theorem bar_and_interval_row_cut {N c j R : ℕ} {F C E : Finset (Finset ℕ)}
    (hcj : c < j) (hF : Erdos272.IsArithInterSet N F) (hCF : C ⊆ F) (hEF : E ⊆ F)
    (hc : ∀ S ∈ C, c ∈ S) (p : {S // S ∈ C} → ℕ)
    (hW : ∀ S, IsWitnessPair S.val c {j,p S})
    (hp : ∀ S, R < p S ∧ p S ≤ N)
    (hCrop : ∀ S, IsCrooked (S.val ∩ Finset.Icc j (p S)))
    (hrep : ∀ I ∈ E, ∃ f : ℕ, R < f ∧ f ≤ N ∧ I = Finset.Icc j f)
    (hEne : E.Nonempty) :
    ∃ l : ℕ, R < l ∧ l ≤ N ∧ (∃ I ∈ E, I = Finset.Icc j l) ∧
      C.card+E.card ≤ N-l+1 := by
  classical
  let Y := {I // I ∈ E}
  have hparam : ∀ I : Y, ∃ f : ℕ, R < f ∧ f ≤ N ∧ I.val = Finset.Icc j f :=
    fun I => hrep I.val I.property
  choose q hRq hqN hqrep using hparam
  have hY : (Finset.univ : Finset Y).Nonempty := by
    obtain ⟨I,hI⟩ := hEne
    exact ⟨⟨I,hI⟩,Finset.mem_univ _⟩
  obtain ⟨I₀,_hI₀,hminq⟩ := Finset.exists_min_image Finset.univ q hY
  let l := q I₀
  refine ⟨l,hRq I₀,hqN I₀,⟨I₀.val,I₀.property,hqrep I₀⟩,?_⟩
  by_cases hCne : C.Nonempty
  · have hX : (Finset.univ : Finset {S // S ∈ C}).Nonempty := by
      obtain ⟨S,hS⟩ := hCne
      exact ⟨⟨S,hS⟩,Finset.mem_univ _⟩
    obtain ⟨K,_hK,hminp⟩ := Finset.exists_min_image Finset.univ p hX
    let m := p K
    have hqm : ∀ I : Y, q I < m := by
      intro I
      have hcI : c ∉ I.val := by
        rw [hqrep I]
        intro hh
        have hcj' := (Finset.mem_Icc.mp hh).1
        omega
      have hKI : K.val ≠ I.val := by
        intro heq
        exact hcI (heq ▸ hc K.val K.property)
      obtain ⟨t,_ht,hAP⟩ := hF.2 (hCF K.property) (hEF I.property) hKI
      apply crooked_crop_forces_interval_end_lt (hCrop K)
      refine ⟨t,?_⟩
      simpa only [hqrep I] using hAP
    have hlm : l < m := hqm I₀
    have hmN : m ≤ N := (hp K).2
    have hCcard : C.card ≤ (Finset.Icc m N).card :=
      witness_row_card_le_interval hF hCF hc p hW (fun S => Finset.mem_Icc.mpr
        ⟨hminp S (Finset.mem_univ _),(hp S).2⟩)
    have hEcard : E.card ≤ (Finset.Icc l (m-1)).card := by
      apply interval_row_card_le
      intro I hI
      let T : Y := ⟨I,hI⟩
      exact ⟨q T,Finset.mem_Icc.mpr ⟨hminq T (Finset.mem_univ _),by have hh := hqm T; omega⟩,
        hqrep T⟩
    simp only [Nat.card_Icc] at hCcard hEcard
    omega
  · have hCzero : C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hCne
    have hEcard : E.card ≤ (Finset.Icc l N).card := by
      apply interval_row_card_le
      intro I hI
      let T : Y := ⟨I,hI⟩
      exact ⟨q T,Finset.mem_Icc.mpr ⟨hminq T (Finset.mem_univ _),hqN T⟩,hqrep T⟩
    have hlN : l ≤ N := hqN I₀
    simp only [hCzero,Finset.card_empty,Nat.zero_add]
    simp only [Nat.card_Icc] at hEcard
    omega

end
/- OneSidedRowCount -/

/- The rectangle bound for the right-hand corner witnesses and outside intervals. -/

section
open Finset

theorem corner_witnesses_and_intervals_card_le {N c L R : ℕ} {F C E : Finset (Finset ℕ)}
    (hLR : L ≤ R) (hRN : R ≤ N) (hF : Erdos272.IsArithInterSet N F)
    (hCF : C ⊆ F) (hEF : E ⊆ F) (hc : ∀ S ∈ C, c ∈ S)
    (x p j q : Finset ℕ → ℕ)
    (hC : ∀ S ∈ C, c < x S ∧ x S < L ∧ R < p S ∧ p S ≤ N ∧
      IsWitnessPair S c {x S,p S} ∧
      (S ∩ Finset.Icc (x S) (p S) = {x S,p S} ∨ IsCrooked (S ∩ Finset.Icc (x S) (p S))))
    (hE : ∀ S ∈ E, c < j S ∧ j S ≤ L ∧ R < q S ∧ q S ≤ N ∧ S = Finset.Icc (j S) (q S)) :
    C.card+E.card ≤ (L-c)*(N-R)+2*N := by
  classical
  let I := Finset.Ioc c L
  let HC (i : ℕ) := C.filter (fun S => x S = i)
  let Hat (i : ℕ) := (HC i).filter (fun S => S ∩ Finset.Icc (x S) (p S) = {x S,p S})
  let Bar (i : ℕ) := (HC i).filter (fun S => ¬S ∩ Finset.Icc (x S) (p S) = {x S,p S})
  let ER (i : ℕ) := E.filter (fun S => j S = i)
  let Active := I.filter (fun i => (ER i).Nonempty)
  have hHCC : ∀ i, HC i ⊆ C := fun i => Finset.filter_subset _ _
  have hHatHC : ∀ i, Hat i ⊆ HC i := fun i => Finset.filter_subset _ _
  have hBarHC : ∀ i, Bar i ⊆ HC i := fun i => Finset.filter_subset _ _
  have hERE : ∀ i, ER i ⊆ E := fun i => Finset.filter_subset _ _
  have hHCspec : ∀ i, ∀ S ∈ HC i, R < p S ∧ p S ≤ N ∧ IsWitnessPair S c {i,p S} := by
    intro i S hS
    obtain ⟨hSC,hxi⟩ := Finset.mem_filter.mp hS
    have hh := hC S hSC
    exact ⟨hh.2.2.1,hh.2.2.2.1,by simpa only [hxi] using hh.2.2.2.2.1⟩
  have hHCcard : ∀ i, (HC i).card ≤ N-R := by
    intro i
    have hh := witness_row_card_le_interval hF ((hHCC i).trans hCF)
      (fun S hS => hc S (hHCC i hS)) (fun S => p S.val)
      (fun S => (hHCspec i S.val S.property).2.2)
      (fun S => Finset.mem_Icc.mpr
        ⟨(hHCspec i S.val S.property).1,(hHCspec i S.val S.property).2.1⟩)
    simpa only [Nat.card_Icc,Nat.succ_eq_add_one,Nat.add_sub_add_right] using hh
  have hpartition : ∀ i, (Hat i).card+(Bar i).card = (HC i).card := by
    intro i
    exact Finset.card_filter_add_card_filter_not (s := HC i)
      (fun S => S ∩ Finset.Icc (x S) (p S) = {x S,p S})
  have hcuts : ∀ i ∈ Active, ∃ l, R < l ∧ l ≤ N ∧
      (∃ T ∈ ER i, T = Finset.Icc i l) ∧ (Bar i).card+(ER i).card ≤ N-l+1 := by
    intro i hi
    obtain ⟨hiI,hne⟩ := Finset.mem_filter.mp hi
    have hci : c < i := (Finset.mem_Ioc.mp hiI).1
    apply bar_and_interval_row_cut hci hF (((hBarHC i).trans (hHCC i)).trans hCF)
      ((hERE i).trans hEF) (fun S hS => hc S (hHCC i (hBarHC i hS))) (fun S => p S.val)
      (fun S => (hHCspec i S.val (hBarHC i S.property)).2.2)
      (fun S => ⟨(hHCspec i S.val (hBarHC i S.property)).1,
        (hHCspec i S.val (hBarHC i S.property)).2.1⟩) ?_ ?_ hne
    · intro S
      have hSi := hBarHC i S.property
      have hxi := (Finset.mem_filter.mp hSi).2
      have hcases := (hC S.val (hHCC i hSi)).2.2.2.2.2
      have hcrooked := hcases.resolve_left (Finset.mem_filter.mp S.property).2
      simpa only [hxi] using hcrooked
    · intro S hS
      obtain ⟨hSE,hji⟩ := Finset.mem_filter.mp hS
      have hh := hE S hSE
      exact ⟨q S,hh.2.2.1,hh.2.2.2.1,by simpa only [hji] using hh.2.2.2.2⟩
  have hHat : ∀ i ∈ Active, (Hat i).card ≤ N-R := by
    intro i _hi
    exact (Finset.card_le_card (hHatHC i)).trans (hHCcard i)
  have hBarE : ∀ i ∈ Active, (Bar i).card+(ER i).card ≤ N-R := by
    intro i hi
    obtain ⟨l,hRl,hlN,_hT,hcut⟩ := hcuts i hi
    omega
  have hcross : ∀ u ∈ Active, ∀ v ∈ Active, u < v →
      (Hat u).card+((Bar v).card+(ER v).card) ≤ (N-R)+1 := by
    intro u _hu v hv huv
    obtain ⟨l,hRl,hlN,⟨T,hT,hTrep⟩,hcut⟩ := hcuts v hv
    have hHatBound : (Hat u).card ≤ (Finset.Icc (R+1) l).card := by
      apply witness_row_card_le_interval hF (((hHatHC u).trans (hHCC u)).trans hCF)
        (fun S hS => hc S (hHCC u (hHatHC u hS))) (fun S => p S.val)
        (fun S => (hHCspec u S.val (hHatHC u S.property)).2.2)
      intro S
      have hSC := hHCC u (hHatHC u S.property)
      have hxu := (Finset.mem_filter.mp (hHatHC u S.property)).2
      have hcrop : S.val ∩ Finset.Icc u (p S.val) = {u,p S.val} := by
        simpa only [hxu] using (Finset.mem_filter.mp S.property).2
      have hmet : (S.val ∩ Finset.Icc v l).Nonempty := by
        have hh := arithInter_inter_nonempty hF (hCF hSC) (hEF (hERE v hT)) ⟨c,hc S.val hSC⟩
        simpa only [hTrep] using hh
      have hpl := pair_crop_meets_later_interval hcrop hmet huv
      exact Finset.mem_Icc.mpr ⟨(hHCspec u S.val (hHatHC u S.property)).1,hpl⟩
    simp only [Nat.card_Icc,Nat.add_sub_add_right] at hHatBound
    omega
  have hinactive : ∀ i ∈ I \ Active, (Hat i).card+((Bar i).card+(ER i).card) ≤ N-R := by
    intro i hi
    obtain ⟨hiI,hiA⟩ := Finset.mem_sdiff.mp hi
    have hnone : ¬(ER i).Nonempty := by
      intro hn
      exact hiA (Finset.mem_filter.mpr ⟨hiI,hn⟩)
    have hz : ER i = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnone
    have hpart := hpartition i
    have hbound := hHCcard i
    simp only [hz,Finset.card_empty]
    omega
  have hCmaps : Set.MapsTo x (C : Set (Finset ℕ)) (I : Set ℕ) := by
    intro S hS
    have hh := hC S hS
    exact Finset.mem_Ioc.mpr ⟨hh.1,hh.2.1.le⟩
  have hEmaps : Set.MapsTo j (E : Set (Finset ℕ)) (I : Set ℕ) := by
    intro S hS
    have hh := hE S hS
    exact Finset.mem_Ioc.mpr ⟨hh.1,hh.2.1⟩
  have hCcount : C.card = ∑ i ∈ I, (HC i).card := Finset.card_eq_sum_card_fiberwise hCmaps
  have hEcount : E.card = ∑ i ∈ I, (ER i).card := Finset.card_eq_sum_card_fiberwise hEmaps
  have hsum : (∑ i ∈ I, ((Hat i).card+((Bar i).card+(ER i).card))) = C.card+E.card := by
    calc
      _ = ∑ i ∈ I, ((HC i).card+(ER i).card) := by
        apply Finset.sum_congr rfl
        intro i _hi
        have hh := hpartition i
        omega
      _ = (∑ i ∈ I, (HC i).card)+(∑ i ∈ I, (ER i).card) := Finset.sum_add_distrib
      _ = C.card+E.card := by rw [← hCcount,← hEcount]
  have htotal := ordered_row_total_le (show Active ⊆ I from Finset.filter_subset _ _)
    (fun i => (Hat i).card) (fun i => (Bar i).card+(ER i).card) (N-R) hHat hBarE hcross hinactive
  rw [hsum] at htotal
  have hIcard : I.card = L-c := Nat.card_Ioc c L
  rw [hIcard] at htotal
  omega

end
/- ResidueIntervalCount -/

/- The exact spacing bound for a residue class in an interval. -/

section
open Finset

theorem residue_interval_card_le {a d u v : ℕ} {S : Finset ℕ}
    (hsub : S ⊆ Finset.Icc u v) (hmod : ∀ x ∈ S, Nat.ModEq d a x) :
    S.card ≤ (v-u)/d+1 := by
  have hmaps : Set.MapsTo (fun x : ℕ => (x-u)/d) (S : Set ℕ)
      (Finset.range ((v-u)/d+1) : Set ℕ) := by
    intro x hx
    have hxv := (Finset.mem_Icc.mp (hsub hx)).2
    apply Finset.mem_range.mpr
    exact Nat.lt_succ_of_le (Nat.div_le_div_right (Nat.sub_le_sub_right hxv u))
  have hinj : Set.InjOn (fun x : ℕ => (x-u)/d) (S : Set ℕ) := by
    intro x hx y hy heq
    have hux := (Finset.mem_Icc.mp (hsub hx)).1
    have huy := (Finset.mem_Icc.mp (hsub hy)).1
    have hxy := (hmod x hx).symm.trans (hmod y hy)
    have hmodsub : Nat.ModEq d (x-u) (y-u) := Nat.ModEq.sub_right hux huy hxy
    change (x-u)%d = (y-u)%d at hmodsub
    change (x-u)/d = (y-u)/d at heq
    have hnx := Nat.mod_add_div (x-u) d
    have hny := Nat.mod_add_div (y-u) d
    rw [heq,hmodsub] at hnx
    omega
  simpa only [Finset.card_range] using Finset.card_le_card_of_injOn _ hmaps hinj

end
/- APEndpointRectangle -/

/- Counting a fixed-step progression family by restricted first and last endpoints. -/

section
open Finset

theorem same_step_endpoint_rectangle_card_le {N L R d : ℕ} {F : Finset (Finset ℕ)}
    (hd : 0 < d) (hF : Erdos272.IsArithInterSet N F) (hcard : ∀ S ∈ F, 0 < S.card)
    (hparam : ∀ S ∈ F, ∃ a : ℕ,
      S = natAP a d S.card ∧ a ≤ L ∧ R ≤ a+(S.card-1)*d) :
    F.card ≤ (L/d+1)*((N-R)/d+1) := by
  classical
  by_cases hne : F.Nonempty
  · obtain ⟨z,_hzI,hz⟩ := same_step_common_point hd hF hne hcard
      (fun S hS => by obtain ⟨a,hrep,_ha,_hb⟩ := hparam S hS; exact ⟨a,hrep⟩)
    let X := {S // S ∈ F}
    have hp : ∀ S : X, ∃ a : ℕ,
        S.val = natAP a d S.val.card ∧ a ≤ L ∧ R ≤ a+(S.val.card-1)*d :=
      fun S => hparam S.val S.property
    choose a hrep haL hRb using hp
    let b (S : X) := a S+(S.val.card-1)*d
    have haS : ∀ S : X, a S ∈ S.val := by
      intro S
      rw [hrep S]
      exact mem_natAP.mpr ⟨0,hcard S.val S.property,by simp⟩
    have hbS : ∀ S : X, b S ∈ S.val := by
      intro S
      rw [hrep S]
      exact mem_natAP.mpr ⟨S.val.card-1,by have hh := hcard S.val S.property; omega,rfl⟩
    have hamod : ∀ S : X, Nat.ModEq d z (a S) := by
      intro S
      obtain ⟨i,_hi,hzi⟩ := mem_natAP.mp (hrep S ▸ hz S.val S.property)
      change z%d = (a S)%d
      rw [← hzi]
      simp only [Nat.add_mul_mod_self_right]
    have hbmod : ∀ S : X, Nat.ModEq d z (b S) := by
      intro S
      apply (hamod S).trans
      change (a S)%d = (a S+(S.val.card-1)*d)%d
      simp only [Nat.add_mul_mod_self_right]
    let A := (Finset.univ : Finset X).image a
    let B := (Finset.univ : Finset X).image b
    have hAcard : A.card ≤ L/d+1 := by
      have hh : A.card ≤ (L-1)/d+1 := by
        apply residue_interval_card_le
        · intro t ht
          obtain ⟨S,_hS,rfl⟩ := Finset.mem_image.mp ht
          have hbnd := Finset.mem_Icc.mp (Finset.mem_powerset.mp (hF.1 S.property) (haS S))
          exact Finset.mem_Icc.mpr ⟨hbnd.1,haL S⟩
        · intro t ht
          obtain ⟨S,_hS,rfl⟩ := Finset.mem_image.mp ht
          exact hamod S
      have hdiv : (L-1)/d ≤ L/d := Nat.div_le_div_right (Nat.sub_le L 1)
      omega
    have hBcard : B.card ≤ (N-R)/d+1 := by
      apply residue_interval_card_le
      · intro t ht
        obtain ⟨S,_hS,rfl⟩ := Finset.mem_image.mp ht
        have hbnd := Finset.mem_Icc.mp (Finset.mem_powerset.mp (hF.1 S.property) (hbS S))
        exact Finset.mem_Icc.mpr ⟨hRb S,hbnd.2⟩
      · intro t ht
        obtain ⟨S,_hS,rfl⟩ := Finset.mem_image.mp ht
        exact hbmod S
    let f (S : X) := (a S,b S)
    have hinj : Function.Injective f := by
      intro S T heq
      have ha := congrArg Prod.fst heq
      have hb := congrArg Prod.snd heq
      change a S = a T at ha
      change b S = b T at hb
      dsimp only [b] at hb
      rw [ha] at hb
      have hmul : (S.val.card-1)*d = (T.val.card-1)*d := Nat.add_left_cancel hb
      have hst := Nat.le_of_mul_le_mul_right hmul.le hd
      have hts := Nat.le_of_mul_le_mul_right hmul.ge hd
      have hs := hcard S.val S.property
      have ht := hcard T.val T.property
      have hcards : S.val.card = T.val.card := by omega
      apply Subtype.ext
      rw [hrep S,hrep T,ha,hcards]
    have hmaps : Set.MapsTo f ((Finset.univ : Finset X) : Set X) (A.product B : Set (ℕ × ℕ)) := by
      intro S _hS
      exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨S,Finset.mem_univ _,rfl⟩,
        Finset.mem_image.mpr ⟨S,Finset.mem_univ _,rfl⟩⟩
    have hcount : F.card ≤ A.card*B.card := by
      have hh : F.card ≤ (A.product B).card := by
        simpa only [Finset.card_univ,X,Fintype.card_coe] using
          Finset.card_le_card_of_injOn f hmaps hinj.injOn
      exact hh.trans_eq (Finset.card_product A B)
    exact hcount.trans (Nat.mul_le_mul hAcard hBcard)
  · have hz : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp only [hz,Finset.card_empty,Nat.zero_le]

end
/- APRectangleSum -/

/- The endpoint-rectangle estimate summed over all steps greater than one. -/

section
open Finset

theorem same_step_endpoint_rectangle_real_le {N L R d : ℕ} {F : Finset (Finset ℕ)}
    (hLN : L ≤ N) (hRN : R ≤ N) (hd : 0 < d)
    (hF : Erdos272.IsArithInterSet N F) (hcard : ∀ S ∈ F, 0 < S.card)
    (hparam : ∀ S ∈ F, ∃ a : ℕ,
      S = natAP a d S.card ∧ a ≤ L ∧ R ≤ a+(S.card-1)*d) :
    (F.card : ℝ) ≤ (L : ℝ)*(N-R)/((d : ℝ)^2)+2*N/d+1 := by
  have hh := same_step_endpoint_rectangle_card_le hd hF hcard hparam
  have hhR : (F.card : ℝ) ≤ ((L/d : ℕ)+1 : ℝ)*(((N-R)/d : ℕ)+1 : ℝ) := by
    exact_mod_cast hh
  have ha := Nat.cast_div_le (α := ℝ) (m := L) (n := d)
  have hb := Nat.cast_div_le (α := ℝ) (m := N-R) (n := d)
  rw [Nat.cast_sub hRN] at hb
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hRN' : (R : ℝ) ≤ N := by exact_mod_cast hRN
  have hprod : (F.card : ℝ) ≤ ((L : ℝ)/d+1)*(((N : ℝ)-R)/d+1) :=
    hhR.trans (mul_le_mul (by linarith only [ha]) (by linarith only [hb])
      (by positivity) (by positivity))
  have hLN' : (L : ℝ) ≤ N := by exact_mod_cast hLN
  have hsum : ((L : ℝ)+(N-R))/d ≤ 2*N/d :=
    (div_le_div_iff_of_pos_right hdR).mpr (by have := Nat.cast_nonneg (α := ℝ) R; linarith)
  have hid : ((L : ℝ)/d+1)*(((N : ℝ)-R)/d+1) =
      (L : ℝ)*(N-R)/((d : ℝ)^2)+((L : ℝ)+(N-R))/d+1 := by ring
  linarith only [hprod,hsum,hid]

theorem large_step_endpoint_rectangle_card_le {N L R : ℕ} {F : Finset (Finset ℕ)}
    (hLN : L ≤ N) (hRN : R ≤ N) (hF : Erdos272.IsArithInterSet N F)
    (hcard : ∀ S ∈ F, 0 < S.card)
    (hparam : ∀ S ∈ F, ∃ a d : ℕ, 2 ≤ d ∧ d ≤ N ∧
      S = natAP a d S.card ∧ a ≤ L ∧ R ≤ a+(S.card-1)*d) :
    (F.card : ℝ) ≤ (2/3)*(L : ℝ)*(N-R)+2*N*reciprocalSum N+N := by
  classical
  have hparam' : ∀ S : Finset ℕ, ∃ a d : ℕ, S ∈ F → 2 ≤ d ∧ d ≤ N ∧
      S = natAP a d S.card ∧ a ≤ L ∧ R ≤ a+(S.card-1)*d := by
    intro S
    by_cases hS : S ∈ F
    · obtain ⟨a,d,hd,hdN,hrep,ha,hb⟩ := hparam S hS
      exact ⟨a,d,fun _ => ⟨hd,hdN,hrep,ha,hb⟩⟩
    · exact ⟨0,2,fun hh => False.elim (hS hh)⟩
  choose a d hspec using hparam'
  have hmaps : Set.MapsTo d (F : Set (Finset ℕ)) (Finset.Icc 2 N : Set ℕ) := by
    intro S hS
    exact Finset.mem_Icc.mpr ⟨(hspec S hS).1,(hspec S hS).2.1⟩
  have hsumCard : (F.card : ℝ) =
      ∑ k ∈ Finset.Icc 2 N, ((F.filter (fun S => d S = k)).card : ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_fiberwise hmaps
  have hbound : ∀ k ∈ Finset.Icc 2 N,
      ((F.filter (fun S => d S = k)).card : ℝ) ≤
        (L : ℝ)*(N-R)/((k : ℝ)^2)+2*N/k+1 := by
    intro k hk
    apply same_step_endpoint_rectangle_real_le hLN hRN
      (by have hh := Finset.mem_Icc.mp hk; omega)
      (admissible_subfamily hF (Finset.filter_subset _ _))
      (fun S hS => hcard S (Finset.mem_filter.mp hS).1)
    intro S hS
    obtain ⟨hSF,hdk⟩ := Finset.mem_filter.mp hS
    exact ⟨a S,by simpa only [hdk] using (hspec S hSF).2.2⟩
  have hinv : (∑ k ∈ Finset.Icc 2 N, (k : ℝ)⁻¹) ≤ reciprocalSum N := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro k hk
      have hh := Finset.mem_Icc.mp hk
      exact Finset.mem_Icc.mpr ⟨by omega,hh.2⟩
    · intro k _hk _hk'; positivity
  have hcardI : ((Finset.Icc 2 N).card : ℝ) ≤ N := by
    exact_mod_cast (show (Finset.Icc 2 N).card ≤ N by rw [Nat.card_Icc]; omega)
  have hsum : (F.card : ℝ) ≤ (L : ℝ)*(N-R)*(∑ k ∈ Finset.Icc 2 N, ((k : ℝ)^2)⁻¹)+
      2*N*(∑ k ∈ Finset.Icc 2 N, (k : ℝ)⁻¹)+(Finset.Icc 2 N).card := by
    calc
      (F.card : ℝ) ≤ ∑ k ∈ Finset.Icc 2 N,
          ((L : ℝ)*(N-R)/((k : ℝ)^2)+2*N/k+1) := by
        rw [hsumCard]
        exact Finset.sum_le_sum hbound
      _ = _ := by
        simp only [div_eq_mul_inv,Finset.sum_add_distrib,← Finset.mul_sum,
          Finset.sum_const,nsmul_eq_mul,mul_one]
  have hRN' : (R : ℝ) ≤ N := by exact_mod_cast hRN
  have hquad := mul_le_mul_of_nonneg_left (reciprocal_square_tail_two_le N)
    (show 0 ≤ (L : ℝ)*(N-R) by positivity)
  have hharm := mul_le_mul_of_nonneg_left hinv (show (0 : ℝ) ≤ 2*N by positivity)
  linarith only [hsum,hquad,hharm,hcardI]

end
/- FiniteDensityConvolution -/

/- A finite Dirichlet-convolution identity for the coprime-pair density. -/

section
open Finset

noncomputable def reciprocalSquareSum (N : ℕ) : ℝ := ∑ d ∈ Finset.Icc 1 N, ((d : ℝ)^2)⁻¹

noncomputable def moebiusSquareSum (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℝ)/((d : ℝ)^2)

theorem reciprocalSquareSum_bounds {N : ℕ} (hN : 1 ≤ N) :
    1 ≤ reciprocalSquareSum N ∧ reciprocalSquareSum N ≤ 5/3 := by
  refine ⟨?_,reciprocal_square_sum_le N⟩
  have hh := Finset.single_le_sum (f := fun d : ℕ => ((d : ℝ)^2)⁻¹)
    (s := Finset.Icc 1 N) (fun d _hd => by positivity)
    (show 1 ∈ Finset.Icc 1 N from Finset.mem_Icc.mpr ⟨le_rfl,hN⟩)
  simpa only [reciprocalSquareSum,Nat.cast_one,one_pow,inv_one] using hh

theorem truncated_product_fiber {N n : ℕ} (hn : n ∈ Finset.Icc 1 N) :
    (((Finset.Icc 1 N).product (Finset.Icc 1 N)).filter
      (fun p : ℕ × ℕ => p.1*p.2 ≤ N)).filter (fun p => p.1*p.2 = n) =
        n.divisorsAntidiagonal := by
  have hn1 := (Finset.mem_Icc.mp hn).1
  have hnN := (Finset.mem_Icc.mp hn).2
  ext p
  simp only [Finset.product_eq_sprod,Finset.mem_filter,Finset.mem_product,Finset.mem_Icc,
    Nat.mem_divisorsAntidiagonal]
  constructor
  · rintro ⟨⟨⟨hp,hq⟩,_hprod⟩,heq⟩
    exact ⟨heq,by omega⟩
  · rintro ⟨heq,_hn0⟩
    have hp : 0 < p.1 := by nlinarith only [heq,hn1]
    have hq : 0 < p.2 := by nlinarith only [heq,hn1]
    have hpN : p.1 ≤ N := (Nat.le_mul_of_pos_right p.1 hq).trans (heq ▸ hnN)
    have hqN : p.2 ≤ N := (Nat.le_mul_of_pos_left p.2 hp).trans (heq ▸ hnN)
    exact ⟨⟨⟨⟨hp,hpN⟩,⟨hq,hqN⟩⟩,heq ▸ hnN⟩,heq⟩

theorem moebius_antidiagonal_weight (n : ℕ) :
    (∑ p ∈ n.divisorsAntidiagonal,
      (ArithmeticFunction.moebius p.1 : ℝ)/(((p.1 : ℝ)*p.2)^2)) =
      if n = 1 then 1 else 0 := by
  calc
    _ = ∑ p ∈ n.divisorsAntidiagonal,
        (ArithmeticFunction.moebius p.1 : ℝ)/((n : ℝ)^2) := by
      apply Finset.sum_congr rfl
      intro p hp
      have heq : (p.1 : ℝ)*p.2 = n := by
        exact_mod_cast (Nat.mem_divisorsAntidiagonal.mp hp).1
      rw [heq]
    _ = (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ))/((n : ℝ)^2) := by
      rw [Nat.sum_divisorsAntidiagonal (fun d _k =>
        (ArithmeticFunction.moebius d : ℝ)/((n : ℝ)^2)),Finset.sum_div]
    _ = _ := by
      have hh : (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ)) =
          if n = 1 then 1 else 0 := by
        exact_mod_cast moebius_divisor_indicator n
      rw [hh]
      split_ifs with hn
      · subst n; norm_num
      · simp

theorem truncated_moebius_product_sum {N : ℕ} (hN : 1 ≤ N) :
    (∑ p ∈ ((Finset.Icc 1 N).product (Finset.Icc 1 N)).filter
      (fun p : ℕ × ℕ => p.1*p.2 ≤ N),
      (ArithmeticFunction.moebius p.1 : ℝ)/(((p.1 : ℝ)*p.2)^2)) = 1 := by
  let P := ((Finset.Icc 1 N).product (Finset.Icc 1 N)).filter
    (fun p : ℕ × ℕ => p.1*p.2 ≤ N)
  have hmaps : ∀ p ∈ P, p.1*p.2 ∈ Finset.Icc 1 N := by
    intro p hp
    obtain ⟨hpI,hprod⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpi,hqi⟩ := Finset.mem_product.mp hpI
    exact Finset.mem_Icc.mpr ⟨Nat.mul_pos (Finset.mem_Icc.mp hpi).1
      (Finset.mem_Icc.mp hqi).1,hprod⟩
  have hsum := Finset.sum_fiberwise_of_maps_to hmaps
    (fun p : ℕ × ℕ => (ArithmeticFunction.moebius p.1 : ℝ)/(((p.1 : ℝ)*p.2)^2))
  calc
    _ = ∑ n ∈ Finset.Icc 1 N, ∑ p ∈ P.filter (fun p => p.1*p.2 = n),
        (ArithmeticFunction.moebius p.1 : ℝ)/(((p.1 : ℝ)*p.2)^2) := hsum.symm
    _ = ∑ n ∈ Finset.Icc 1 N, if n = 1 then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [show P.filter (fun p => p.1*p.2 = n) = n.divisorsAntidiagonal from
        truncated_product_fiber hn,moebius_antidiagonal_weight]
    _ = 1 := by simp [hN]

theorem moebius_product_full_sum (N : ℕ) :
    (∑ p ∈ (Finset.Icc 1 N).product (Finset.Icc 1 N),
      (ArithmeticFunction.moebius p.1 : ℝ)/(((p.1 : ℝ)*p.2)^2)) =
      moebiusSquareSum N*reciprocalSquareSum N := by
  rw [Finset.product_eq_sprod,Finset.sum_product,moebiusSquareSum,reciprocalSquareSum,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d _hd
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  simp only [mul_pow,div_eq_mul_inv,mul_inv_rev]
  ring

end
/- CoprimeRectangleSieve -/

/- Finite Moebius inversion for coprime pairs in a rectangle. -/

section
open Finset

def coprimeRectangle (A B : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 A).product (Finset.Icc 1 B)).filter (fun p => p.1.Coprime p.2)

theorem divisors_eq_filter_Icc {m N : ℕ} (hm : 0 < m) (hmN : m ≤ N) :
    (Finset.Icc 1 N).filter (fun d => d ∣ m) = m.divisors := by
  ext d
  simp only [Finset.mem_filter,Finset.mem_Icc,Nat.mem_divisors]
  constructor
  · rintro ⟨_hdI,hdm⟩
    exact ⟨hdm,hm.ne'⟩
  · rintro ⟨hdm,_hm0⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos hdm hm,(Nat.le_of_dvd hm hdm).trans hmN⟩,hdm⟩

theorem coprime_moebius_full_indicator {m N : ℕ} (hm : 0 < m) (hmN : m ≤ N) (j : ℕ) :
    (∑ d ∈ Finset.Icc 1 N,
      if d ∣ m ∧ d ∣ j then (ArithmeticFunction.moebius d : ℝ) else 0) =
        if m.Coprime j then 1 else 0 := by
  calc
    _ = ∑ d ∈ (Finset.Icc 1 N).filter (fun d => d ∣ m),
        if d ∣ j then (ArithmeticFunction.moebius d : ℝ) else 0 := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro d _hd
      by_cases hdm : d ∣ m <;> simp [hdm]
    _ = ∑ d ∈ m.divisors, if d ∣ j then (ArithmeticFunction.moebius d : ℝ) else 0 := by
      rw [divisors_eq_filter_Icc hm hmN]
    _ = _ := by exact_mod_cast coprime_moebius_indicator hm j

theorem coprimeRectangle_card_moebius {N A B : ℕ} (hAN : A ≤ N) :
    ((coprimeRectangle A B).card : ℝ) = ∑ d ∈ Finset.Icc 1 N,
      (ArithmeticFunction.moebius d : ℝ)*(A/d : ℕ)*(B/d : ℕ) := by
  calc
    _ = ∑ p ∈ (Finset.Icc 1 A).product (Finset.Icc 1 B),
        if p.1.Coprime p.2 then (1 : ℝ) else 0 := by simp [coprimeRectangle]
    _ = ∑ p ∈ (Finset.Icc 1 A).product (Finset.Icc 1 B), ∑ d ∈ Finset.Icc 1 N,
        if d ∣ p.1 ∧ d ∣ p.2 then (ArithmeticFunction.moebius d : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      have ha := Finset.mem_Icc.mp (Finset.mem_product.mp hp).1
      exact (coprime_moebius_full_indicator ha.1 (ha.2.trans hAN) p.2).symm
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d _hd
      have hprod : ((Finset.Icc 1 A).product (Finset.Icc 1 B)).filter
          (fun p : ℕ × ℕ => d ∣ p.1 ∧ d ∣ p.2) =
          ((Finset.Icc 1 A).filter (fun a => d ∣ a)).product
            ((Finset.Icc 1 B).filter (fun b => d ∣ b)) := by
        ext p
        simp only [Finset.product_eq_sprod,Finset.mem_filter,Finset.mem_product]
        tauto
      rw [← Finset.sum_filter,hprod]
      simp only [Finset.product_eq_sprod,Finset.sum_const,nsmul_eq_mul,Finset.card_product,
        card_multiples_Icc,Nat.cast_mul]
      ring

theorem nat_div_product_error {A B d : ℕ} (hd : 0 < d) :
    |((A/d : ℕ) : ℝ)*(B/d : ℕ)-(A : ℝ)*B/((d : ℝ)^2)| ≤ ((A : ℝ)+B)/d := by
  have ha := nat_div_error_le_one (K := A) hd
  have hb := nat_div_error_le_one (K := B) hd
  have ha0 : (0 : ℝ) ≤ (A/d : ℕ) := Nat.cast_nonneg _
  have hb0 : (0 : ℝ) ≤ (B/d : ℕ) := Nat.cast_nonneg _
  have hau := Nat.cast_div_le (α := ℝ) (m := A) (n := d)
  have hbu := Nat.cast_div_le (α := ℝ) (m := B) (n := d)
  have hda : (0 : ℝ) ≤ (A : ℝ)/d := by positivity
  have hdb : (0 : ℝ) ≤ (B : ℝ)/d := by positivity
  have hid : (A : ℝ)*B/((d : ℝ)^2) = ((A : ℝ)/d)*((B : ℝ)/d) := by ring
  have hsum : ((A : ℝ)+B)/d = (A : ℝ)/d+(B : ℝ)/d := by ring
  rw [hid,hsum]
  apply abs_le.mpr
  have hap := (abs_le.mp ha).1
  have hbp := (abs_le.mp hb).1
  have hprod := mul_le_mul hau hbu hb0 hda
  constructor
  · nlinarith only [hap,hbp,hau,hbu,ha0,hb0,hda,hdb]
  · nlinarith only [hprod,hda,hdb]

end
/- FiniteDensityNormalization -/

/- Normalizing the finite coprime density, with an explicit convolution-tail error. -/

section
open Finset

noncomputable def finiteCoprimeDensity (N : ℕ) : ℝ := (reciprocalSquareSum N)⁻¹

theorem reciprocal_product_row_tail {N a : ℕ} (ha : a ∈ Finset.Icc 1 N) :
    (∑ k ∈ (Finset.Icc 1 N).filter (fun k => ¬a*k ≤ N), ((k : ℝ)^2)⁻¹) ≤
      2*a/N := by
  obtain ⟨ha1,haN⟩ := Finset.mem_Icc.mp ha
  have hN : 0 < N := lt_of_lt_of_le ha1 haN
  have hdiv : 0 < N/a := Nat.div_pos haN ha1
  have hdivN : N/a ≤ N := Nat.div_le_self _ _
  have hset : (Finset.Icc 1 N).filter (fun k => ¬a*k ≤ N) = Finset.Ioc (N/a) N := by
    ext k
    simp only [Finset.mem_filter,Finset.mem_Icc,Finset.mem_Ioc]
    have hiff : N/a < k ↔ N < k*a := Nat.div_lt_iff_lt_mul ha1
    constructor
    · rintro ⟨⟨_hk1,hkN⟩,hprod⟩
      exact ⟨hiff.mpr (by nlinarith only [hprod]),hkN⟩
    · rintro ⟨hk,hkN⟩
      exact ⟨⟨by omega,hkN⟩,by have hh := hiff.mp hk; nlinarith only [hh]⟩
  rw [hset]
  have htail := sum_Ioc_inv_sq_le_sub (α := ℝ) (k := N/a) hdiv.ne' hdivN
  have hrem := Nat.mod_lt N ha1
  have hquot := Nat.mod_add_div N a
  have hmul : N ≤ 2*a*(N/a) := by nlinarith only [hrem,hquot,hdiv]
  have hmulR : (N : ℝ) ≤ 2*a*(N/a : ℕ) := by exact_mod_cast hmul
  have hquotR : (0 : ℝ) < (N/a : ℕ) := Nat.cast_pos.mpr hdiv
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hinv : ((N/a : ℕ) : ℝ)⁻¹ ≤ 2*a/N := by
    rw [inv_eq_one_div]
    apply (div_le_div_iff₀ hquotR hNR).mpr
    simpa only [one_mul] using hmulR
  have hnonneg : (0 : ℝ) ≤ (N : ℝ)⁻¹ := by positivity
  linarith only [htail,hinv,hnonneg]

theorem reciprocal_product_tail_le {N : ℕ} (hN : 1 ≤ N) :
    (∑ p ∈ ((Finset.Icc 1 N).product (Finset.Icc 1 N)).filter
      (fun p : ℕ × ℕ => ¬p.1*p.2 ≤ N),
      ((p.1 : ℝ)^2)⁻¹*((p.2 : ℝ)^2)⁻¹) ≤ 2*reciprocalSum N/N := by
  have hsplit : (∑ p ∈ ((Finset.Icc 1 N).product (Finset.Icc 1 N)).filter
      (fun p : ℕ × ℕ => ¬p.1*p.2 ≤ N),
      ((p.1 : ℝ)^2)⁻¹*((p.2 : ℝ)^2)⁻¹) =
      ∑ a ∈ Finset.Icc 1 N, ((a : ℝ)^2)⁻¹*
        (∑ k ∈ (Finset.Icc 1 N).filter (fun k => ¬a*k ≤ N), ((k : ℝ)^2)⁻¹) := by
    rw [Finset.sum_filter,Finset.product_eq_sprod,Finset.sum_product]
    apply Finset.sum_congr rfl
    intro a _ha
    simp only [Finset.sum_filter,Finset.mul_sum,mul_ite,mul_zero]
  rw [hsplit]
  calc
    _ ≤ ∑ a ∈ Finset.Icc 1 N, ((a : ℝ)^2)⁻¹*(2*a/N) := by
      apply Finset.sum_le_sum
      intro a ha
      exact mul_le_mul_of_nonneg_left (reciprocal_product_row_tail ha) (by positivity)
    _ = 2*reciprocalSum N/N := by
      calc
        _ = ∑ a ∈ Finset.Icc 1 N, (2/N)*(a : ℝ)⁻¹ := by
          apply Finset.sum_congr rfl
          intro a ha
          have ha0 : (a : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by
            have hh := (Finset.mem_Icc.mp ha).1; omega)
          have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
          field_simp
          <;> ring
        _ = _ := by rw [← Finset.mul_sum]; unfold reciprocalSum; ring

theorem moebiusSquareSum_normalization_error {N : ℕ} (hN : 1 ≤ N) :
    |moebiusSquareSum N*reciprocalSquareSum N-1| ≤ 2*reciprocalSum N/N := by
  let I := (Finset.Icc 1 N).product (Finset.Icc 1 N)
  let f (p : ℕ × ℕ) : ℝ :=
    (ArithmeticFunction.moebius p.1 : ℝ)/(((p.1 : ℝ)*p.2)^2)
  have hgood : (∑ p ∈ I.filter (fun p => p.1*p.2 ≤ N), f p) = 1 :=
    truncated_moebius_product_sum hN
  have hfull : (∑ p ∈ I, f p) = moebiusSquareSum N*reciprocalSquareSum N :=
    moebius_product_full_sum N
  have hpart := Finset.sum_filter_add_sum_filter_not I (fun p => p.1*p.2 ≤ N) f
  have heq : moebiusSquareSum N*reciprocalSquareSum N-1 =
      ∑ p ∈ I.filter (fun p => ¬p.1*p.2 ≤ N), f p := by linarith only [hpart,hgood,hfull]
  rw [heq]
  calc
    _ ≤ ∑ p ∈ I.filter (fun p => ¬p.1*p.2 ≤ N), |f p| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ I.filter (fun p => ¬p.1*p.2 ≤ N),
        ((p.1 : ℝ)^2)⁻¹*((p.2 : ℝ)^2)⁻¹ := by
      apply Finset.sum_le_sum
      intro p _hp
      have hmu : |(ArithmeticFunction.moebius p.1 : ℝ)| ≤ 1 := by
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := p.1)
      dsimp only [f]
      rw [abs_div,abs_of_nonneg (sq_nonneg ((p.1 : ℝ)*p.2))]
      calc
        _ ≤ 1/(((p.1 : ℝ)*p.2)^2) := div_le_div_of_nonneg_right hmu (sq_nonneg _)
        _ = _ := by simp only [mul_pow,one_div,mul_inv_rev]; ring
    _ ≤ 2*reciprocalSum N/N := reciprocal_product_tail_le hN

theorem finiteCoprimeDensity_bounds {N : ℕ} (hN : 1 ≤ N) :
    0 < finiteCoprimeDensity N ∧ finiteCoprimeDensity N ≤ 1 := by
  have hH := (reciprocalSquareSum_bounds hN).1
  have hHpos : 0 < reciprocalSquareSum N := by linarith only [hH]
  refine ⟨inv_pos.mpr hHpos,?_⟩
  change (reciprocalSquareSum N)⁻¹ ≤ 1
  exact (inv_le_one₀ hHpos).mpr hH

theorem moebiusSquareSum_density_error {N : ℕ} (hN : 1 ≤ N) :
    |moebiusSquareSum N-finiteCoprimeDensity N| ≤ 2*reciprocalSum N/N := by
  have hH := (reciprocalSquareSum_bounds hN).1
  have hHpos : 0 < reciprocalSquareSum N := by linarith only [hH]
  have hh := moebiusSquareSum_normalization_error hN
  have hid : |moebiusSquareSum N-finiteCoprimeDensity N| * reciprocalSquareSum N =
      |moebiusSquareSum N*reciprocalSquareSum N-1| := by
    rw [← abs_of_pos hHpos,← abs_mul]
    congr 1
    rw [sub_mul]
    simp only [finiteCoprimeDensity,inv_mul_cancel₀ hHpos.ne',abs_of_pos hHpos]
  have hnonneg := abs_nonneg (moebiusSquareSum N-finiteCoprimeDensity N)
  nlinarith only [hh,hid,hH,hnonneg]

theorem finiteCoprimeDensity_weights_sum {N : ℕ} (hN : 1 ≤ N) :
    (∑ d ∈ Finset.Icc 1 N, finiteCoprimeDensity N/((d : ℝ)^2)) = 1 := by
  rw [show (∑ d ∈ Finset.Icc 1 N, finiteCoprimeDensity N/((d : ℝ)^2)) =
    finiteCoprimeDensity N*reciprocalSquareSum N by
      simp only [div_eq_mul_inv,← Finset.mul_sum,reciprocalSquareSum]]
  have hH := (reciprocalSquareSum_bounds hN).1
  exact inv_mul_cancel₀ (by linarith : reciprocalSquareSum N ≠ 0)

end
/- CoprimeRectangleBounds -/

/- Uniform coprime-rectangle estimates using weights whose finite sum is exactly one. -/

section
open Finset

theorem coprimeRectangle_moebius_error {N A B : ℕ} (hAN : A ≤ N) :
    |((coprimeRectangle A B).card : ℝ)-moebiusSquareSum N*A*B| ≤
      ((A : ℝ)+B)*reciprocalSum N := by
  have hmain : moebiusSquareSum N*A*B = ∑ d ∈ Finset.Icc 1 N,
      (ArithmeticFunction.moebius d : ℝ)*((A : ℝ)*B/((d : ℝ)^2)) := by
    simp only [moebiusSquareSum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d _hd
    ring
  have heq : ((coprimeRectangle A B).card : ℝ)-moebiusSquareSum N*A*B =
      ∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℝ)*
        (((A/d : ℕ) : ℝ)*(B/d : ℕ)-(A : ℝ)*B/((d : ℝ)^2)) := by
    rw [coprimeRectangle_card_moebius hAN,hmain,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d _hd
    ring
  rw [heq]
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 N, |(ArithmeticFunction.moebius d : ℝ)*
        (((A/d : ℕ) : ℝ)*(B/d : ℕ)-(A : ℝ)*B/((d : ℝ)^2))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Finset.Icc 1 N, ((A : ℝ)+B)/d := by
      apply Finset.sum_le_sum
      intro d hd
      rw [abs_mul]
      have hmu : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
      have herr := nat_div_product_error (A := A) (B := B) (Finset.mem_Icc.mp hd).1
      exact (mul_le_mul hmu herr (abs_nonneg _) (by norm_num)).trans (by simp)
    _ = _ := by simp only [div_eq_mul_inv,← Finset.mul_sum,reciprocalSum]

theorem coprimeRectangle_density_error {N A B : ℕ} (hN : 1 ≤ N)
    (hAN : A ≤ N) (hBN : B ≤ N) :
    |((coprimeRectangle A B).card : ℝ)-finiteCoprimeDensity N*A*B| ≤
      2*((A : ℝ)+B)*reciprocalSum N := by
  have hfirst := coprimeRectangle_moebius_error (B := B) hAN
  have hnormal := moebiusSquareSum_density_error hN
  have hAN' : (A : ℝ) ≤ N := by exact_mod_cast hAN
  have hBN' : (B : ℝ) ≤ N := by exact_mod_cast hBN
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have harea : 2*(A : ℝ)*B ≤ ((A : ℝ)+B)*N := by
    have ha := mul_nonneg (sub_nonneg.mpr hAN') (Nat.cast_nonneg (α := ℝ) B)
    have hb := mul_nonneg (sub_nonneg.mpr hBN') (Nat.cast_nonneg (α := ℝ) A)
    nlinarith only [ha,hb]
  have hareaDiv : 2*(A : ℝ)*B/N ≤ (A : ℝ)+B := (div_le_iff₀ hNpos).mpr harea
  have hHnonneg : 0 ≤ reciprocalSum N := Finset.sum_nonneg (fun d _hd => by positivity)
  have herrorArea : (2*reciprocalSum N/N)*(A : ℝ)*B ≤ ((A : ℝ)+B)*reciprocalSum N := by
    have hh := mul_le_mul_of_nonneg_right hareaDiv hHnonneg
    calc
      _ = (2*(A : ℝ)*B/N)*reciprocalSum N := by ring
      _ ≤ _ := hh
  have hsecond : |moebiusSquareSum N*A*B-finiteCoprimeDensity N*A*B| ≤
      ((A : ℝ)+B)*reciprocalSum N := by
    calc
      _ = |moebiusSquareSum N-finiteCoprimeDensity N| * (A : ℝ)*B := by
        rw [show moebiusSquareSum N*A*B-finiteCoprimeDensity N*A*B =
          (moebiusSquareSum N-finiteCoprimeDensity N)*A*B by ring]
        simp only [abs_mul,Nat.abs_cast]
      _ ≤ (2*reciprocalSum N/N)*(A : ℝ)*B := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hnormal
          (Nat.cast_nonneg A)) (Nat.cast_nonneg B)
      _ ≤ _ := herrorArea
  have hh := abs_sub_le ((coprimeRectangle A B).card : ℝ)
    (moebiusSquareSum N*A*B) (finiteCoprimeDensity N*A*B)
  linarith only [hh,hfirst,hsecond]

def coprimeBox (A₀ A₁ B₀ B₁ : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Ioc A₀ A₁).product (Finset.Ioc B₀ B₁)).filter (fun p => p.1.Coprime p.2)

theorem coprimeBox_card_identity {A₀ A₁ B₀ B₁ : ℕ} (hA : A₀ ≤ A₁) (hB : B₀ ≤ B₁) :
    (coprimeBox A₀ A₁ B₀ B₁).card+(coprimeRectangle A₀ B₁).card+
      (coprimeRectangle A₁ B₀).card =
      (coprimeRectangle A₁ B₁).card+(coprimeRectangle A₀ B₀).card := by
  let S := (coprimeRectangle A₁ B₁).filter (fun p => ¬p.1 ≤ A₀)
  let T := (coprimeRectangle A₁ B₀).filter (fun p => ¬p.1 ≤ A₀)
  have hf₁ : (coprimeRectangle A₁ B₁).filter (fun p => p.1 ≤ A₀) =
      coprimeRectangle A₀ B₁ := by
    ext p
    simp only [coprimeRectangle,Finset.product_eq_sprod,Finset.mem_filter,
      Finset.mem_product,Finset.mem_Icc]
    omega
  have hf₀ : (coprimeRectangle A₁ B₀).filter (fun p => p.1 ≤ A₀) =
      coprimeRectangle A₀ B₀ := by
    ext p
    simp only [coprimeRectangle,Finset.product_eq_sprod,Finset.mem_filter,
      Finset.mem_product,Finset.mem_Icc]
    omega
  have hg₀ : S.filter (fun p => p.2 ≤ B₀) = T := by
    ext p
    simp only [S,T,coprimeRectangle,Finset.product_eq_sprod,Finset.mem_filter,
      Finset.mem_product,Finset.mem_Icc]
    omega
  have hg₁ : S.filter (fun p => ¬p.2 ≤ B₀) = coprimeBox A₀ A₁ B₀ B₁ := by
    ext p
    simp only [S,coprimeRectangle,coprimeBox,Finset.product_eq_sprod,Finset.mem_filter,
      Finset.mem_product,Finset.mem_Icc,Finset.mem_Ioc]
    omega
  have hp₁ := Finset.card_filter_add_card_filter_not (s := coprimeRectangle A₁ B₁)
    (fun p => p.1 ≤ A₀)
  have hp₀ := Finset.card_filter_add_card_filter_not (s := coprimeRectangle A₁ B₀)
    (fun p => p.1 ≤ A₀)
  have hpS := Finset.card_filter_add_card_filter_not (s := S) (fun p => p.2 ≤ B₀)
  rw [hf₁] at hp₁
  rw [hf₀] at hp₀
  rw [hg₀,hg₁] at hpS
  change (coprimeRectangle A₀ B₁).card+S.card = _ at hp₁
  change (coprimeRectangle A₀ B₀).card+T.card = _ at hp₀
  omega

theorem coprimeBox_density_error {N A₀ A₁ B₀ B₁ : ℕ} (hN : 1 ≤ N)
    (hA : A₀ ≤ A₁) (hAN : A₁ ≤ N) (hB : B₀ ≤ B₁) (hBN : B₁ ≤ N) :
    |((coprimeBox A₀ A₁ B₀ B₁).card : ℝ)-
      finiteCoprimeDensity N*((A₁ : ℝ)-A₀)*((B₁ : ℝ)-B₀)| ≤
      8*((A₁ : ℝ)+B₁)*reciprocalSum N := by
  have h₁₁ := coprimeRectangle_density_error hN hAN hBN
  have h₀₁ := coprimeRectangle_density_error hN (hA.trans hAN) hBN
  have h₁₀ := coprimeRectangle_density_error hN hAN (hB.trans hBN)
  have h₀₀ := coprimeRectangle_density_error hN (hA.trans hAN) (hB.trans hBN)
  have hcard : ((coprimeBox A₀ A₁ B₀ B₁).card : ℝ)+(coprimeRectangle A₀ B₁).card+
      (coprimeRectangle A₁ B₀).card =
      (coprimeRectangle A₁ B₁).card+(coprimeRectangle A₀ B₀).card := by
    exact_mod_cast coprimeBox_card_identity hA hB
  have hAR : (A₀ : ℝ) ≤ A₁ := by exact_mod_cast hA
  have hBR : (B₀ : ℝ) ≤ B₁ := by exact_mod_cast hB
  have hHnonneg : 0 ≤ reciprocalSum N := Finset.sum_nonneg (fun d _hd => by positivity)
  have hAH := mul_le_mul_of_nonneg_right hAR hHnonneg
  have hBH := mul_le_mul_of_nonneg_right hBR hHnonneg
  obtain ⟨h₁₁l,h₁₁u⟩ := abs_le.mp h₁₁
  obtain ⟨h₀₁l,h₀₁u⟩ := abs_le.mp h₀₁
  obtain ⟨h₁₀l,h₁₀u⟩ := abs_le.mp h₁₀
  obtain ⟨h₀₀l,h₀₀u⟩ := abs_le.mp h₀₀
  apply abs_le.mpr
  constructor <;> nlinarith only [hcard,h₁₁l,h₁₁u,h₀₁l,h₀₁u,h₁₀l,h₁₀u,
    h₀₀l,h₀₀u,hAH,hBH]

end
/- PrimitiveTriangleCount -/

/- Counting one orientation of coprime pairs in an interval. -/

section
open Finset

def coprimeUpperTriangle (A B : ℕ) : Finset (ℕ × ℕ) :=
  (coprimeBox A B A B).filter (fun p => p.1 < p.2)

theorem twice_coprimeUpperTriangle_card_le (A B : ℕ) :
    2*(coprimeUpperTriangle A B).card ≤ (coprimeBox A B A B).card := by
  classical
  let T := coprimeUpperTriangle A B
  have hinj : Function.Injective (Prod.swap : ℕ × ℕ → ℕ × ℕ) := Prod.swap_injective
  have hdis : Disjoint T (T.image Prod.swap) := by
    apply Finset.disjoint_left.mpr
    intro p hp hp'
    obtain ⟨q,hq,hqp⟩ := Finset.mem_image.mp hp'
    have hltp := (Finset.mem_filter.mp hp).2
    have hltq := (Finset.mem_filter.mp hq).2
    have hfst := congrArg Prod.fst hqp
    have hsnd := congrArg Prod.snd hqp
    change q.2 = p.1 at hfst
    change q.1 = p.2 at hsnd
    omega
  have hsub : T ∪ T.image Prod.swap ⊆ coprimeBox A B A B := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact (Finset.mem_filter.mp hp).1
    · obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨hqi,hcop⟩ := Finset.mem_filter.mp (Finset.mem_filter.mp hq).1
      have hqI := Finset.mem_product.mp hqi
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hqI.2,hqI.1⟩,hcop.symm⟩
  have hh := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdis,Finset.card_image_of_injective _ hinj] at hh
  dsimp only [T] at hh
  omega

theorem coprimeUpperTriangle_card_le {N A B : ℕ} (hN : 1 ≤ N)
    (hAB : A ≤ B) (hBN : B ≤ N) :
    ((coprimeUpperTriangle A B).card : ℝ) ≤
      finiteCoprimeDensity N*((B : ℝ)-A)^2/2+8*B*reciprocalSum N := by
  have htwice : 2*((coprimeUpperTriangle A B).card : ℝ) ≤ (coprimeBox A B A B).card := by
    exact_mod_cast twice_coprimeUpperTriangle_card_le A B
  have hbox := (abs_le.mp (coprimeBox_density_error hN hAB hBN hAB hBN)).2
  nlinarith only [htwice,hbox]

end
/- AbstractMiddleCount -/

/- A progression-endpoint rectangle and primitive witnesses in the middle region. -/

section
open Finset

theorem middle_coordinate_pools_card_le {N C A e M : ℕ} {E Wm Wp : Finset (ℕ × ℕ)}
    (hN : 1 ≤ N) (hCN : C ≤ N) (hAe : A ≤ e) (heM : e ≤ M) (hMN : M ≤ N)
    (hE : E ⊆ (Finset.Icc 1 C).product (Finset.Ioc A e))
    (hWm : Wm ⊆ coprimeBox 0 C A M) (hdis : Disjoint E Wm)
    (hWp : ∀ p ∈ Wp, 1 ≤ p.1 ∧ p.1 < p.2 ∧ e < p.2 ∧ p.2 ≤ M ∧ p.1.Coprime p.2) :
    (E.card : ℝ)+Wm.card+Wp.card ≤ (C : ℝ)*((e : ℝ)-A)+
      finiteCoprimeDensity N*(((M : ℝ)-e)*(C+M)-((M : ℝ)-e)^2/2)+
      40*((C : ℝ)+M)*reciprocalSum N := by
  classical
  let W₀ := Wm.filter (fun p => p.2 ≤ e)
  let W₁ := Wm.filter (fun p => ¬p.2 ≤ e)
  let V₀ := Wp.filter (fun p => p.1 ≤ e)
  let V₁ := Wp.filter (fun p => ¬p.1 ≤ e)
  have hW₀ : W₀ ⊆ (Finset.Icc 1 C).product (Finset.Ioc A e) := by
    intro p hp
    obtain ⟨hpW,hpe⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpI,_hcop⟩ := Finset.mem_filter.mp (hWm hpW)
    obtain ⟨hp₁,hp₂⟩ := Finset.mem_product.mp hpI
    obtain ⟨hp₁0,hp₁C⟩ := Finset.mem_Ioc.mp hp₁
    obtain ⟨hp₂A,_hp₂M⟩ := Finset.mem_Ioc.mp hp₂
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hp₁0,hp₁C⟩,
      Finset.mem_Ioc.mpr ⟨hp₂A,hpe⟩⟩
  have hW₁ : W₁ ⊆ coprimeBox 0 C e M := by
    intro p hp
    obtain ⟨hpW,hpe⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpI,hcop⟩ := Finset.mem_filter.mp (hWm hpW)
    obtain ⟨hp₁,hp₂⟩ := Finset.mem_product.mp hpI
    have hp₂M := (Finset.mem_Ioc.mp hp₂).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hp₁,
      Finset.mem_Ioc.mpr ⟨by omega,hp₂M⟩⟩,hcop⟩
  have hV₀ : V₀ ⊆ coprimeBox 0 e e M := by
    intro p hp
    obtain ⟨hpV,hpe⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp₁,hlt,hp₂e,hp₂M,hcop⟩ := hWp p hpV
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_Ioc.mpr ⟨hp₁,hpe⟩,Finset.mem_Ioc.mpr ⟨hp₂e,hp₂M⟩⟩,hcop⟩
  have hV₁ : V₁ ⊆ coprimeUpperTriangle e M := by
    intro p hp
    obtain ⟨hpV,hpe⟩ := Finset.mem_filter.mp hp
    obtain ⟨_hp₁,hlt,hp₂e,hp₂M,hcop⟩ := hWp p hpV
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_Ioc.mpr ⟨by omega,by omega⟩,Finset.mem_Ioc.mpr ⟨hp₂e,hp₂M⟩⟩,hcop⟩,hlt⟩
  have hrect : (E.card : ℝ)+W₀.card ≤ (C : ℝ)*((e : ℝ)-A) := by
    have hdis₀ : Disjoint E W₀ := hdis.mono_right (Finset.filter_subset _ _)
    have hsub := Finset.union_subset hE hW₀
    have hh := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdis₀] at hh
    have hh' : E.card+W₀.card ≤ C*(e-A) := by
      simpa only [Finset.product_eq_sprod,Finset.card_product,Nat.card_Icc,
        Nat.card_Ioc,Nat.add_sub_cancel] using hh
    have hhR : (E.card : ℝ)+W₀.card ≤ (C : ℝ)*(e-A : ℕ) := by exact_mod_cast hh'
    simpa only [Nat.cast_sub hAe] using hhR
  have hwm : (W₁.card : ℝ) ≤ finiteCoprimeDensity N*C*((M : ℝ)-e)+
      8*((C : ℝ)+M)*reciprocalSum N := by
    have hcard : (W₁.card : ℝ) ≤ (coprimeBox 0 C e M).card := by
      exact_mod_cast Finset.card_le_card hW₁
    have hh := (abs_le.mp (coprimeBox_density_error hN (Nat.zero_le C) hCN heM hMN)).2
    norm_num only [Nat.cast_zero,sub_zero] at hh
    linarith only [hcard,hh]
  have hv₀ : (V₀.card : ℝ) ≤ finiteCoprimeDensity N*e*((M : ℝ)-e)+
      8*((e : ℝ)+M)*reciprocalSum N := by
    have hcard : (V₀.card : ℝ) ≤ (coprimeBox 0 e e M).card := by
      exact_mod_cast Finset.card_le_card hV₀
    have hh := (abs_le.mp (coprimeBox_density_error hN (Nat.zero_le e) (heM.trans hMN) heM hMN)).2
    norm_num only [Nat.cast_zero,sub_zero] at hh
    linarith only [hcard,hh]
  have hv₁ : (V₁.card : ℝ) ≤ finiteCoprimeDensity N*((M : ℝ)-e)^2/2+
      8*M*reciprocalSum N := by
    have hcard : (V₁.card : ℝ) ≤ (coprimeUpperTriangle e M).card := by
      exact_mod_cast Finset.card_le_card hV₁
    exact hcard.trans (coprimeUpperTriangle_card_le hN heM hMN)
  have hwpart : (W₀.card : ℝ)+W₁.card = Wm.card := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := Wm) (fun p => p.2 ≤ e)
  have hvpart : (V₀.card : ℝ)+V₁.card = Wp.card := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := Wp) (fun p => p.1 ≤ e)
  have hH : 0 ≤ reciprocalSum N := Finset.sum_nonneg (fun d _hd => by positivity)
  have heR : (e : ℝ) ≤ M := by exact_mod_cast heM
  have heH := mul_le_mul_of_nonneg_right heR hH
  have hCH := mul_nonneg (Nat.cast_nonneg (α := ℝ) C) hH
  have hMH := mul_nonneg (Nat.cast_nonneg (α := ℝ) M) hH
  nlinarith only [hrect,hwm,hv₀,hv₁,hwpart,hvpart,heH,hCH,hMH]

end
/- CenteredEndpointMembership -/

/- Natural-coordinate endpoints and internal points of a centered progression. -/

section
open Finset

theorem centered_model_positive_mem {c d k : ℕ} {p : ProgressionCell} {S : Finset ℕ}
    (hmodel : IsCenteredModel c d p S) (hk : k ≤ p.val.2) : c+k*d ∈ S := by
  have hh := (centered_point_mem hmodel (z := (k : ℤ))
    (Finset.mem_Icc.mpr ⟨by omega,by exact_mod_cast hk⟩)).1
  have heq : ((c : ℤ)+(d : ℤ)*k).toNat = c+k*d := by
    rw [show (c : ℤ)+(d : ℤ)*k = ((c+k*d : ℕ) : ℤ) by push_cast; ring]
    exact Int.toNat_natCast _
  simpa only [heq] using hh

theorem centered_model_negative_mem {c d k : ℕ} {p : ProgressionCell} {S : Finset ℕ}
    (hmodel : IsCenteredModel c d p S) (hk : k ≤ p.val.1) : c-k*d ∈ S := by
  have hh := (centered_point_mem hmodel (z := -(k : ℤ))
    (Finset.mem_Icc.mpr ⟨by omega,by omega⟩)).1
  have heq : ((c : ℤ)+(d : ℤ)*(-(k : ℤ))).toNat = c-k*d := by
    rw [show (c : ℤ)+(d : ℤ)*(-(k : ℤ)) = (c : ℤ)-(k*d : ℕ) by push_cast; ring]
    omega
  simpa only [heq] using hh

theorem centered_model_root_mem {c d : ℕ} {p : ProgressionCell} {S : Finset ℕ}
    (hmodel : IsCenteredModel c d p S) : c ∈ S := by
  simpa only [Nat.zero_mul,Nat.add_zero] using
    centered_model_positive_mem hmodel (Nat.zero_le p.val.2)

end
/- MiddleStepCoordinates -/

/- The middle-region estimate for one progression step, in centered integer coordinates. -/

section
open Finset

theorem middle_step_coordinate_bound {N c d C A M : ℕ} {F Cm Cp E : Finset (Finset ℕ)}
    (hN : 1 ≤ N) (hCN : C ≤ N) (hAM : A ≤ M) (hMN : M ≤ N)
    (hF : Erdos272.IsArithInterSet N F) (hMF : Cm ⊆ F) (hPF : Cp ⊆ F) (hEF : E ⊆ F)
    (hcM : ∀ S ∈ Cm, c ∈ S) (hcP : ∀ S ∈ Cp, c ∈ S)
    (hcrookedM : ∀ S ∈ Cm, IsCrooked S) (hcrookedP : ∀ S ∈ Cp, IsCrooked S)
    (m : {S // S ∈ Cm} → ℕ × ℕ) (p : {S // S ∈ Cp} → ℕ × ℕ)
    (model : {S // S ∈ E} → ProgressionCell)
    (hm : ∀ S, 1 ≤ (m S).1 ∧ (m S).1 ≤ C ∧ A < (m S).2 ∧ (m S).2 ≤ M ∧
      (m S).1.Coprime (m S).2 ∧ IsWitnessPair S.val c {c-(m S).1*d,c+(m S).2*d})
    (hp : ∀ S, 1 ≤ (p S).1 ∧ (p S).1 < (p S).2 ∧ A < (p S).2 ∧ (p S).2 ≤ M ∧
      (p S).1.Coprime (p S).2 ∧ IsWitnessPair S.val c {c+(p S).1*d,c+(p S).2*d})
    (hmodel : ∀ T, IsCenteredModel c d (model T) T.val ∧ 1 ≤ (model T).val.1 ∧
      (model T).val.1 ≤ C ∧ A < (model T).val.2 ∧ (model T).val.2 ≤ M ∧
      ∃ l : ℕ∞, (T.val : Set ℕ).IsAPOfLength l) :
    ∃ e : ℕ, A ≤ e ∧ e ≤ M ∧
      (Cm.card : ℝ)+Cp.card+E.card ≤ (C : ℝ)*((e : ℝ)-A)+
        finiteCoprimeDensity N*(((M : ℝ)-e)*(C+M)-((M : ℝ)-e)^2/2)+
        40*((C : ℝ)+M)*reciprocalSum N := by
  classical
  let X := {S // S ∈ Cm}
  let Y := {S // S ∈ Cp}
  let Z := {S // S ∈ E}
  let fE (T : Z) := (model T).val
  let Wm := (Finset.univ : Finset X).image m
  let Wp := (Finset.univ : Finset Y).image p
  let EE := (Finset.univ : Finset Z).image fE
  have hm_inj : Function.Injective m := by
    intro S T heq
    apply Subtype.ext
    have hwS := (hm S).2.2.2.2.2
    have hwT := (hm T).2.2.2.2.2
    exact (witness_pair_private hF (hMF S.property) (hMF T.property)
      (hcM S.val S.property) (hcM T.val T.property) hwS (by
        rw [heq]
        exact hwT.2.1.trans (Finset.erase_subset _ _))).symm
  have hp_inj : Function.Injective p := by
    intro S T heq
    apply Subtype.ext
    have hwS := (hp S).2.2.2.2.2
    have hwT := (hp T).2.2.2.2.2
    exact (witness_pair_private hF (hPF S.property) (hPF T.property)
      (hcP S.val S.property) (hcP T.val T.property) hwS (by
        rw [heq]
        exact hwT.2.1.trans (Finset.erase_subset _ _))).symm
  have he_inj : Function.Injective fE := by
    intro S T heq
    have hmod : model S = model T := Subtype.ext heq
    apply Subtype.ext
    exact centered_model_determines_set (hmodel S).1
      (by simpa only [hmod] using (hmodel T).1)
  have hwm_card : Wm.card = Cm.card := by
    simp only [Wm,Finset.card_image_of_injective _ hm_inj,Finset.card_univ,X,Fintype.card_coe]
  have hwp_card : Wp.card = Cp.card := by
    simp only [Wp,Finset.card_image_of_injective _ hp_inj,Finset.card_univ,Y,Fintype.card_coe]
  have he_card : EE.card = E.card := by
    simp only [EE,Finset.card_image_of_injective _ he_inj,Finset.card_univ,Z,Fintype.card_coe]
  have he_exists : ∃ e : ℕ, A ≤ e ∧ e ≤ M ∧ (∀ T : Z, (model T).val.2 ≤ e) ∧
      (e = A ∨ ∃ T : Z, (model T).val.2 = e) := by
    by_cases hne : E.Nonempty
    · have hz : (Finset.univ : Finset Z).Nonempty := by
        obtain ⟨T,hT⟩ := hne
        exact ⟨⟨T,hT⟩,Finset.mem_univ _⟩
      obtain ⟨T,_hT,hmax⟩ := Finset.exists_max_image Finset.univ
        (fun T : Z => (model T).val.2) hz
      refine ⟨(model T).val.2,(hmodel T).2.2.2.1.le,(hmodel T).2.2.2.2.1,
        fun S => hmax S (Finset.mem_univ _),Or.inr ⟨T,rfl⟩⟩
    · refine ⟨A,le_rfl,hAM,?_,Or.inl rfl⟩
      intro T
      exact False.elim (hne ⟨T.val,T.property⟩)
  obtain ⟨e,hAe,heM,hmax,hewitness⟩ := he_exists
  have hErect : EE ⊆ (Finset.Icc 1 C).product (Finset.Ioc A e) := by
    intro q hq
    obtain ⟨T,_hT,rfl⟩ := Finset.mem_image.mp hq
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr
      ⟨(hmodel T).2.1,(hmodel T).2.2.1⟩,
      Finset.mem_Ioc.mpr ⟨(hmodel T).2.2.2.1,hmax T⟩⟩
  have hWmBox : Wm ⊆ coprimeBox 0 C A M := by
    intro q hq
    obtain ⟨S,_hS,rfl⟩ := Finset.mem_image.mp hq
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_Ioc.mpr ⟨(hm S).1,(hm S).2.1⟩,
        Finset.mem_Ioc.mpr ⟨(hm S).2.2.1,(hm S).2.2.2.1⟩⟩,(hm S).2.2.2.2.1⟩
  have hdis : Disjoint EE Wm := by
    apply Finset.disjoint_left.mpr
    intro q hqE hqW
    obtain ⟨T,_hT,rfl⟩ := Finset.mem_image.mp hqE
    obtain ⟨S,_hS,hcoords⟩ := Finset.mem_image.mp hqW
    have hmT := (hmodel T).1
    apply witness_pair_not_subset_AP_member hF (hMF S.property) (hEF T.property)
      (hcM S.val S.property) (centered_model_root_mem hmT)
      (hcrookedM S.val S.property) (hmodel T).2.2.2.2.2 (hm S).2.2.2.2.2
    change m S = (model T).val at hcoords
    rw [hcoords]
    exact Finset.insert_subset_iff.mpr ⟨centered_model_negative_mem hmT le_rfl,
      Finset.singleton_subset_iff.mpr (centered_model_positive_mem hmT le_rfl)⟩
  have hWpAbove : ∀ q ∈ Wp,
      1 ≤ q.1 ∧ q.1 < q.2 ∧ e < q.2 ∧ q.2 ≤ M ∧ q.1.Coprime q.2 := by
    intro q hq
    obtain ⟨S,_hS,rfl⟩ := Finset.mem_image.mp hq
    refine ⟨(hp S).1,(hp S).2.1,?_,(hp S).2.2.2.1,(hp S).2.2.2.2.1⟩
    by_contra hn
    have hbe : (p S).2 ≤ e := by omega
    rcases hewitness with he | ⟨T,hTe⟩
    · have hh := (hp S).2.2.1
      omega
    · have hmT := (hmodel T).1
      have ha : (p S).1 ≤ (model T).val.2 := by
        have hab := (hp S).2.1
        omega
      have hb : (p S).2 ≤ (model T).val.2 := by omega
      apply witness_pair_not_subset_AP_member hF (hPF S.property) (hEF T.property)
        (hcP S.val S.property) (centered_model_root_mem hmT)
        (hcrookedP S.val S.property) (hmodel T).2.2.2.2.2 (hp S).2.2.2.2.2
      exact Finset.insert_subset_iff.mpr ⟨centered_model_positive_mem hmT ha,
        Finset.singleton_subset_iff.mpr (centered_model_positive_mem hmT hb)⟩
  have hh := middle_coordinate_pools_card_le hN hCN hAe heM hMN hErect hWmBox hdis hWpAbove
  rw [hwm_card,hwp_card,he_card] at hh
  exact ⟨e,hAe,heM,by linarith only [hh]⟩

end
/- MiddleScalingAlgebra -/

/- Converting the centered-grid estimate to physical endpoint lengths. -/

section
theorem middle_grid_scaling {n c r R d C A M e ρ H K : ℝ}
    (hn : 0 ≤ n) (hc : 0 ≤ c) (hcN : c ≤ n) (hr : 0 ≤ r) (hR : 0 ≤ R) (hRN : R ≤ n)
    (hd : 0 < d) (hC : 0 ≤ C) (hA : 0 ≤ A) (hAe : A ≤ e) (heM : e ≤ M)
    (hCd : C*d ≤ c) (hCMd : (C+M)*d ≤ R) (hwidth : (M-A)*d ≤ r+d)
    (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hH : 0 ≤ H)
    (hK : K ≤ C*(e-A)+ρ*((M-e)*(C+M)-(M-e)^2/2)+40*(C+M)*H) :
    ∃ s : ℝ, 0 ≤ s ∧ s ≤ r ∧
      K ≤ (c*(r-s)+ρ*(s*R-s^2/2))/d^2+(40*H+2)*n/d := by
  let u := (M-e)*d
  let s := min r u
  have hu : 0 ≤ u := mul_nonneg (sub_nonneg.mpr heM) hd.le
  have hs : 0 ≤ s := le_min hr hu
  have hsr : s ≤ r := min_le_left _ _
  have hsu : s ≤ u := min_le_right _ _
  have huwidth : u ≤ r+d := by dsimp only [u]; nlinarith only [hwidth,hAe,hd]
  have hdelta : u-s ≤ d := by
    dsimp only [s]
    rcases le_total r u with hru | hur
    · rw [min_eq_left hru]; linarith only [huwidth]
    · rw [min_eq_right hur]; linarith only [hd]
  have hstart0 : 0 ≤ (e-A)*d := mul_nonneg (sub_nonneg.mpr hAe) hd.le
  have hstart : (e-A)*d ≤ r-s+d := by
    have hsum : (e-A)*d+u = (M-A)*d := by dsimp only [u]; ring
    linarith only [hwidth,hsum,hsu]
  have hfirst : (C*d)*((e-A)*d) ≤ c*(r-s+d) := by
    exact (mul_le_mul_of_nonneg_right hCd hstart0).trans
      (mul_le_mul_of_nonneg_left hstart hc)
  have hright : u*((C+M)*d) ≤ u*R := mul_le_mul_of_nonneg_left hCMd hu
  have htail₁ : ρ*(u*((C+M)*d)-u^2/2) ≤ ρ*(u*R-u^2/2) :=
    mul_le_mul_of_nonneg_left (by linarith only [hright]) hρ
  have hdeltaR := mul_le_mul_of_nonneg_right hdelta hR
  have hdeltaSum : 0 ≤ (u-s)*(u+s) := mul_nonneg (sub_nonneg.mpr hsu) (add_nonneg hu hs)
  have htail₂ : u*R-u^2/2 ≤ s*R-s^2/2+d*R := by
    nlinarith only [hdeltaR,hdeltaSum]
  have hρdR := mul_le_mul_of_nonneg_right hρ1 (mul_nonneg hd.le hR)
  have htail₃ : ρ*(u*R-u^2/2) ≤ ρ*(s*R-s^2/2)+d*R := by
    have hh := mul_le_mul_of_nonneg_left htail₂ hρ
    nlinarith only [hh,hρdR]
  have hgrid : (C*(e-A)+ρ*((M-e)*(C+M)-(M-e)^2/2))*d^2 ≤
      c*(r-s)+ρ*(s*R-s^2/2)+d*(c+R) := by
    dsimp only [u] at htail₁ htail₃
    nlinarith only [hfirst,htail₁,htail₃]
  have hCMN : (C+M)*d ≤ n := hCMd.trans hRN
  have herr := mul_le_mul_of_nonneg_right hCMN (show 0 ≤ 40*H*d by positivity)
  have hends := mul_le_mul_of_nonneg_left (add_le_add hcN hRN) hd.le
  have hKd := mul_le_mul_of_nonneg_right hK (sq_nonneg d)
  have hscaled : K*d^2 ≤ c*(r-s)+ρ*(s*R-s^2/2)+(40*H+2)*n*d := by
    nlinarith only [hKd,hgrid,herr,hends]
  refine ⟨s,hs,hsr,?_⟩
  have hid : ((c*(r-s)+ρ*(s*R-s^2/2))/d^2+(40*H+2)*n/d)*d^2 =
      c*(r-s)+ρ*(s*R-s^2/2)+(40*H+2)*n*d := by
    field_simp
    <;> ring
  exact (mul_le_mul_iff_of_pos_right (sq_pos_of_pos hd)).mp (by
    rw [hid]
    exact hscaled)

theorem middle_nat_grid_bounds {N c L R d : ℕ} (hcL : c ≤ L) (hLR : L ≤ R)
    (hd : 0 < d) :
    ((c/d : ℕ) : ℝ)*d ≤ c ∧
      (((c/d : ℕ) : ℝ)+( (R-c)/d : ℕ))*d ≤ R ∧
      ((( (R-c)/d : ℕ) : ℝ)-((L-c)/d : ℕ))*d ≤ ((R : ℝ)-L)+d := by
  have hcR : c ≤ R := hcL.trans hLR
  have hcdiv := Nat.div_mul_le_self c d
  have hRdiv := Nat.div_mul_le_self (R-c) d
  have hLmod := Nat.mod_lt (L-c) hd
  have hLquot := Nat.mod_add_div (L-c) d
  have hLdiv : L-c ≤ ((L-c)/d+1)*d := by nlinarith only [hLmod,hLquot]
  have hcdivR : ((c/d : ℕ) : ℝ)*d ≤ c := by exact_mod_cast hcdiv
  have hRdivR : (((R-c)/d : ℕ) : ℝ)*d ≤ (R : ℝ)-c := by
    exact_mod_cast hRdiv
  have hLdivR : (L : ℝ)-c ≤ (((L-c)/d : ℕ)+1 : ℝ)*d := by
    exact_mod_cast hLdiv
  exact ⟨hcdivR,by nlinarith only [hcdivR,hRdivR],by nlinarith only [hRdivR,hLdivR]⟩

theorem middle_nat_grid_scale {N c L R d e : ℕ} {K : ℝ}
    (hN : 1 ≤ N) (hcL : c ≤ L) (hLR : L ≤ R) (hRN : R ≤ N) (hd : 0 < d)
    (hAe : (L-c)/d ≤ e) (heM : e ≤ (R-c)/d)
    (hK : K ≤ ((c/d : ℕ) : ℝ)*((e : ℝ)-((L-c)/d : ℕ))+
      finiteCoprimeDensity N*((((R-c)/d : ℕ)-(e : ℝ))*((c/d : ℕ)+((R-c)/d : ℕ) : ℝ)-
        (((R-c)/d : ℕ)-(e : ℝ))^2/2)+
      40*((c/d : ℕ)+((R-c)/d : ℕ) : ℝ)*reciprocalSum N) :
    ∃ s : ℝ, 0 ≤ s ∧ s ≤ (R : ℝ)-L ∧
      K ≤ ((c : ℝ)*((R : ℝ)-L-s)+finiteCoprimeDensity N*(s*R-s^2/2))/((d : ℝ)^2)+
        (40*reciprocalSum N+2)*N/d := by
  have hcN : c ≤ N := hcL.trans (hLR.trans hRN)
  have hb := middle_nat_grid_bounds (N := N) hcL hLR hd
  apply middle_grid_scaling (Nat.cast_nonneg N) (Nat.cast_nonneg c)
    (by exact_mod_cast hcN) (sub_nonneg.mpr (by exact_mod_cast hLR))
    (Nat.cast_nonneg R) (by exact_mod_cast hRN) (Nat.cast_pos.mpr hd)
    (Nat.cast_nonneg (c/d)) (Nat.cast_nonneg ((L-c)/d))
    (by exact_mod_cast hAe) (by exact_mod_cast heM) hb.1 hb.2.1 hb.2.2
    (finiteCoprimeDensity_bounds hN).1.le (finiteCoprimeDensity_bounds hN).2
    (Finset.sum_nonneg (fun d _hd => by positivity)) hK

end
/- WeightedMiddleDeficit -/

/- Summing the normalized middle-region estimates while retaining the endpoint deficit. -/

section
open Finset

theorem finiteCoprimeDensity_mul_five_thirds {N : ℕ} (hN : 1 ≤ N) :
    1 ≤ finiteCoprimeDensity N*(5/3) := by
  have hH := reciprocalSquareSum_bounds hN
  have hρ := (finiteCoprimeDensity_bounds hN).1
  have hid : finiteCoprimeDensity N*reciprocalSquareSum N = 1 :=
    inv_mul_cancel₀ (by linarith only [hH.1] : reciprocalSquareSum N ≠ 0)
  have hh := mul_le_mul_of_nonneg_left hH.2 hρ.le
  linarith only [hid,hh]

theorem weighted_middle_deficit {N c L R : ℕ}
    (hN : 1 ≤ N) (hcL : c ≤ L) (hLR : L ≤ R) (hRN : R ≤ N)
    (s : ℕ → ℝ) (hs : ∀ d ∈ Finset.Icc 1 N, 0 ≤ s d ∧ s d ≤ (R : ℝ)-L) :
    (5/3)*(L : ℝ)*(N-R)+((R : ℝ)-L)*(N-R)+
      (∑ d ∈ Finset.Icc 1 N,
        ((c : ℝ)*((R : ℝ)-L-s d)+finiteCoprimeDensity N*(s d*R-(s d)^2/2))/((d : ℝ)^2)) ≤
      (N : ℝ)^2/2-((L : ℝ)^2+((N : ℝ)-R)^2)/100 := by
  let Outer := (5/3)*(L : ℝ)*(N-R)+((R : ℝ)-L)*(N-R)
  let Bound := (N : ℝ)^2/2-((L : ℝ)^2+((N : ℝ)-R)^2)/100
  let w (d : ℕ) := finiteCoprimeDensity N/((d : ℝ)^2)
  let f (d : ℕ) := ((c : ℝ)*((R : ℝ)-L-s d)+
    finiteCoprimeDensity N*(s d*R-(s d)^2/2))/((d : ℝ)^2)
  have hρ := (finiteCoprimeDensity_bounds hN).1
  have hρk := finiteCoprimeDensity_mul_five_thirds hN
  have hcLR : (c : ℝ) ≤ L := by exact_mod_cast hcL
  have hRNR : (R : ℝ) ≤ N := by exact_mod_cast hRN
  have hterms : ∀ d ∈ Finset.Icc 1 N, w d*Outer+f d ≤ w d*Bound := by
    intro d hd
    have hsd := (hs d hd).2
    have hretained := retained_deficit (n := (N : ℝ)) (q := (L : ℝ)-c)
      (c := (c : ℝ)) (r := (R : ℝ)-L) (x := (N : ℝ)-R) (s := s d) (k := 5/3)
      (sub_nonneg.mpr hcLR) (Nat.cast_nonneg c) (sub_nonneg.mpr hRNR) hsd
      (by norm_num) le_rfl (by ring)
    have hweighted := mul_le_mul_of_nonneg_left hretained hρ.le
    have hcz : 0 ≤ (c : ℝ)*((R : ℝ)-L-s d) :=
      mul_nonneg (Nat.cast_nonneg c) (sub_nonneg.mpr hsd)
    have hczweighted := mul_le_mul_of_nonneg_right hρk hcz
    have hraw : finiteCoprimeDensity N*Outer+(c : ℝ)*((R : ℝ)-L-s d)+
        finiteCoprimeDensity N*(s d*R-(s d)^2/2) ≤ finiteCoprimeDensity N*Bound := by
      dsimp only [Outer,Bound]
      nlinarith only [hweighted,hczweighted]
    calc
      w d*Outer+f d = (finiteCoprimeDensity N*Outer+(c : ℝ)*((R : ℝ)-L-s d)+
          finiteCoprimeDensity N*(s d*R-(s d)^2/2))/((d : ℝ)^2) := by
        dsimp only [w,f]
        ring
      _ ≤ (finiteCoprimeDensity N*Bound)/((d : ℝ)^2) :=
        div_le_div_of_nonneg_right hraw (sq_nonneg _)
      _ = w d*Bound := by dsimp only [w]; ring
  have hsum := Finset.sum_le_sum hterms
  have hwSum : (∑ d ∈ Finset.Icc 1 N, w d) = 1 := finiteCoprimeDensity_weights_sum hN
  rw [Finset.sum_add_distrib,← Finset.sum_mul,← Finset.sum_mul,hwSum,one_mul,one_mul] at hsum
  exact hsum

end
/- OrderedOneSidedWitness -/

/- Ordered preferred witnesses and the linear cost of a witness on a division point. -/

section
open Finset

theorem ordered_one_sided_witness {S : Finset ℕ} {c L R : ℕ} (hLR : L ≤ R)
    (hreach : ∃ W, IsWitnessPair S c W ∧ (∃ x ∈ W, L ≤ x) ∧ ∃ y ∈ W, y ≤ R)
    (hnoL : ∀ W, IsWitnessPair S c W → L ∉ W) :
    ∃ x p : ℕ, IsWitnessPair S c {x,p} ∧ x < p ∧ x ≤ R ∧ L < p ∧
      (c < x → x < L → R < p →
        S ∩ Finset.Icc x p = {x,p} ∨ IsCrooked (S ∩ Finset.Icc x p)) := by
  obtain ⟨x,p,hW,hLp,hcases⟩ := preferred_one_sided_witness hLR hreach
  have hxp : x ≠ p := by
    intro heq
    have hh := hW.1
    simp only [heq,Finset.insert_eq_of_mem (Finset.mem_singleton_self p),Finset.card_singleton] at hh
    omega
  have hpL : L < p := by
    have hneq : p ≠ L := by intro heq; apply hnoL {x,p} hW; simp [heq]
    omega
  rcases hcases with hpR | ⟨hxL,hRp,hnoMiddle,hmin⟩
  · by_cases hlt : x < p
    · exact ⟨x,p,hW,hlt,hlt.le.trans hpR,hpL,by intro _hcx _hxL hRp; omega⟩
    · refine ⟨p,x,by simpa only [Finset.pair_comm] using hW,by omega,hpR,by omega,?_⟩
      intro _hcp hpL' _hRx
      omega
  · exact ⟨x,p,hW,by omega,hxL.le.trans hLR,hpL,
      fun hcx _hxL _hRp => preferred_corner_crop_dichotomy hcx hxL hLR hRp hW hnoMiddle hmin⟩

theorem division_point_witness_family_card_le {N c L : ℕ} {F C : Finset (Finset ℕ)}
    (hF : Erdos272.IsArithInterSet N F) (hCF : C ⊆ F) (hc : ∀ S ∈ C, c ∈ S)
    (hL : ∀ S ∈ C, ∃ W, IsWitnessPair S c W ∧ L ∈ W) : C.card ≤ N := by
  classical
  let X := {S // S ∈ C}
  have hex : ∀ S : X, ∃ x : ℕ, IsWitnessPair S.val c {L,x} := by
    intro S
    obtain ⟨W,hW,hLW⟩ := hL S.val S.property
    obtain ⟨a,b,_hab,hrep⟩ := Finset.card_eq_two.mp hW.1
    rw [hrep] at hLW
    simp only [Finset.mem_insert,Finset.mem_singleton] at hLW
    rcases hLW with hLa | hLb
    · exact ⟨b,by simpa only [hrep,← hLa] using hW⟩
    · exact ⟨a,by simpa only [hrep,← hLb,Finset.pair_comm] using hW⟩
  choose x hx using hex
  have hh := witness_row_card_le_interval hF hCF hc x hx (fun S => by
    have hxS : x S ∈ S.val := Finset.mem_of_mem_erase ((hx S).2.1 (by simp))
    exact Finset.mem_powerset.mp (hF.1 (hCF S.property)) hxS)
  simpa only [Nat.card_Icc,Nat.add_sub_cancel] using hh

end
/- PrimitiveWitnessCoordinates -/

/- Reducing a rooted witness pair to coprime coordinates and its common step. -/

section
theorem primitive_scale_of_pos {u v : ℕ} (hu : 0 < u) (hv : 0 < v) :
    ∃ d a b : ℕ, 0 < d ∧ d ≤ v ∧ 1 ≤ a ∧ 1 ≤ b ∧ a.Coprime b ∧
      u = a*d ∧ v = b*d := by
  let d := u.gcd v
  have hd : 0 < d := Nat.gcd_pos_of_pos_left v hu
  have hdu : d ≤ u := Nat.gcd_le_left v hu
  have hdv : d ≤ v := Nat.gcd_le_right u hv
  exact ⟨d,u/d,v/d,hd,hdv,Nat.div_pos hdu hd,Nat.div_pos hdv hd,
    Nat.coprime_div_gcd_div_gcd hd,
    (Nat.div_mul_cancel (Nat.gcd_dvd_left u v)).symm,
    (Nat.div_mul_cancel (Nat.gcd_dvd_right u v)).symm⟩

theorem negative_middle_witness_coordinates {N c L R x p : ℕ} {S : Finset ℕ}
    (hcx : x < c) (hcL : c ≤ L) (hLp : L < p) (hpR : p ≤ R) (hRN : R ≤ N)
    (hW : IsWitnessPair S c {x,p}) :
    ∃ d a b : ℕ, 0 < d ∧ d ≤ N ∧ 1 ≤ a ∧ a ≤ c/d ∧ (L-c)/d < b ∧ b ≤ (R-c)/d ∧
      a.Coprime b ∧ IsWitnessPair S c {c-a*d,c+b*d} := by
  have hcp : c < p := hcL.trans_lt hLp
  obtain ⟨d,a,b,hd,hdv,ha,hb,hcop,hua,hvb⟩ :=
    primitive_scale_of_pos (by omega : 0 < c-x) (by omega : 0 < p-c)
  have hdN : d ≤ N := hdv.trans ((Nat.sub_le p c).trans (hpR.trans hRN))
  have hadec : a*d ≤ c := by omega
  have hbdec : b*d ≤ R-c := by omega
  have hlb : (L-c)/d < b := (Nat.div_lt_iff_lt_mul hd).mpr (by omega)
  have hxeq : x = c-a*d := by omega
  have hpeq : p = c+b*d := by omega
  exact ⟨d,a,b,hd,hdN,ha,(Nat.le_div_iff_mul_le hd).mpr hadec,hlb,
    (Nat.le_div_iff_mul_le hd).mpr hbdec,hcop,by simpa only [← hxeq,← hpeq] using hW⟩

theorem positive_middle_witness_coordinates {N c L R x p : ℕ} {S : Finset ℕ}
    (hcx : c < x) (hxp : x < p) (hcL : c ≤ L) (hLp : L < p) (hpR : p ≤ R) (hRN : R ≤ N)
    (hW : IsWitnessPair S c {x,p}) :
    ∃ d a b : ℕ, 0 < d ∧ d ≤ N ∧ 1 ≤ a ∧ a < b ∧ (L-c)/d < b ∧ b ≤ (R-c)/d ∧
      a.Coprime b ∧ IsWitnessPair S c {c+a*d,c+b*d} := by
  have hcp : c < p := hcx.trans hxp
  obtain ⟨d,a,b,hd,hdv,ha,_hb,hcop,hua,hvb⟩ :=
    primitive_scale_of_pos (by omega : 0 < x-c) (by omega : 0 < p-c)
  have hdN : d ≤ N := hdv.trans ((Nat.sub_le p c).trans (hpR.trans hRN))
  have hbdec : b*d ≤ R-c := by omega
  have hlb : (L-c)/d < b := (Nat.div_lt_iff_lt_mul hd).mpr (by omega)
  have hab : a < b := by
    by_contra hn
    have hmul := Nat.mul_le_mul_right d (show b ≤ a by omega)
    omega
  have hxeq : x = c+a*d := by omega
  have hpeq : p = c+b*d := by omega
  exact ⟨d,a,b,hd,hdN,ha,hab,hlb,(Nat.le_div_iff_mul_le hd).mpr hbdec,hcop,
    by simpa only [← hxeq,← hpeq] using hW⟩

end
/- MiddleFamilySum -/

/- Summing the middle-region family estimates over their primitive steps. -/

section
open Finset

theorem middle_family_sum_bound {N c L R : ℕ} {F Cm Cp E : Finset (Finset ℕ)}
    (hN : 1 ≤ N) (hcL : c ≤ L) (hLR : L ≤ R) (hRN : R ≤ N)
    (hF : Erdos272.IsArithInterSet N F) (hMF : Cm ⊆ F) (hPF : Cp ⊆ F) (hEF : E ⊆ F)
    (hcM : ∀ S ∈ Cm, c ∈ S) (hcP : ∀ S ∈ Cp, c ∈ S)
    (hcrookedM : ∀ S ∈ Cm, IsCrooked S) (hcrookedP : ∀ S ∈ Cp, IsCrooked S)
    (dm dp de : Finset ℕ → ℕ) (m p : Finset ℕ → ℕ × ℕ) (model : Finset ℕ → ProgressionCell)
    (hm : ∀ S ∈ Cm, 0 < dm S ∧ dm S ≤ N ∧ 1 ≤ (m S).1 ∧ (m S).1 ≤ c/dm S ∧
      (L-c)/dm S < (m S).2 ∧ (m S).2 ≤ (R-c)/dm S ∧ (m S).1.Coprime (m S).2 ∧
      IsWitnessPair S c {c-(m S).1*dm S,c+(m S).2*dm S})
    (hp : ∀ S ∈ Cp, 0 < dp S ∧ dp S ≤ N ∧ 1 ≤ (p S).1 ∧ (p S).1 < (p S).2 ∧
      (L-c)/dp S < (p S).2 ∧ (p S).2 ≤ (R-c)/dp S ∧ (p S).1.Coprime (p S).2 ∧
      IsWitnessPair S c {c+(p S).1*dp S,c+(p S).2*dp S})
    (he : ∀ S ∈ E, 0 < de S ∧ de S ≤ N ∧ IsCenteredModel c (de S) (model S) S ∧
      1 ≤ (model S).val.1 ∧ (model S).val.1 ≤ c/de S ∧ (L-c)/de S < (model S).val.2 ∧
      (model S).val.2 ≤ (R-c)/de S ∧ ∃ l : ℕ∞, (S : Set ℕ).IsAPOfLength l) :
    (5/3)*(L : ℝ)*(N-R)+((R : ℝ)-L)*(N-R)+(Cm.card : ℝ)+Cp.card+E.card ≤
      (N : ℝ)^2/2-((L : ℝ)^2+((N : ℝ)-R)^2)/100+
        (40*reciprocalSum N+2)*N*reciprocalSum N := by
  classical
  let I := Finset.Icc 1 N
  let CM (k : ℕ) := Cm.filter (fun S => dm S = k)
  let CP (k : ℕ) := Cp.filter (fun S => dp S = k)
  let EP (k : ℕ) := E.filter (fun S => de S = k)
  have hterms : ∀ k ∈ I, ∃ s : ℝ, 0 ≤ s ∧ s ≤ (R : ℝ)-L ∧
      ((CM k).card : ℝ)+(CP k).card+(EP k).card ≤
        ((c : ℝ)*((R : ℝ)-L-s)+finiteCoprimeDensity N*(s*R-s^2/2))/((k : ℝ)^2)+
          (40*reciprocalSum N+2)*N/k := by
    intro k hk
    have hkpos : 0 < k := (Finset.mem_Icc.mp hk).1
    have hcN : c ≤ N := hcL.trans (hLR.trans hRN)
    have hCN : c/k ≤ N := (Nat.div_le_self c k).trans hcN
    have hAM : (L-c)/k ≤ (R-c)/k := Nat.div_le_div_right (Nat.sub_le_sub_right hLR c)
    have hMN : (R-c)/k ≤ N := (Nat.div_le_self (R-c) k).trans ((Nat.sub_le R c).trans hRN)
    obtain ⟨e,hAe,heM,hbound⟩ := middle_step_coordinate_bound hN hCN hAM hMN hF
      ((Finset.filter_subset _ _).trans hMF) ((Finset.filter_subset _ _).trans hPF)
      ((Finset.filter_subset _ _).trans hEF)
      (fun S hS => hcM S (Finset.mem_filter.mp hS).1)
      (fun S hS => hcP S (Finset.mem_filter.mp hS).1)
      (fun S hS => hcrookedM S (Finset.mem_filter.mp hS).1)
      (fun S hS => hcrookedP S (Finset.mem_filter.mp hS).1)
      (fun S : {S // S ∈ CM k} => m S.val) (fun S : {S // S ∈ CP k} => p S.val)
      (fun S : {S // S ∈ EP k} => model S.val)
      (by
        intro S
        obtain ⟨hSC,hdk⟩ := Finset.mem_filter.mp S.property
        simpa only [hdk] using (hm S.val hSC).2.2)
      (by
        intro S
        obtain ⟨hSC,hdk⟩ := Finset.mem_filter.mp S.property
        simpa only [hdk] using (hp S.val hSC).2.2)
      (by
        intro S
        obtain ⟨hSC,hdk⟩ := Finset.mem_filter.mp S.property
        simpa only [hdk] using (he S.val hSC).2.2)
    exact middle_nat_grid_scale hN hcL hLR hRN hkpos hAe heM hbound
  have hchoices : ∀ k : ℕ, ∃ s : ℝ, k ∈ I → 0 ≤ s ∧ s ≤ (R : ℝ)-L ∧
      ((CM k).card : ℝ)+(CP k).card+(EP k).card ≤
        ((c : ℝ)*((R : ℝ)-L-s)+finiteCoprimeDensity N*(s*R-s^2/2))/((k : ℝ)^2)+
          (40*reciprocalSum N+2)*N/k := by
    intro k
    by_cases hk : k ∈ I
    · obtain ⟨s,hs⟩ := hterms k hk
      exact ⟨s,fun _ => hs⟩
    · exact ⟨0,fun hh => False.elim (hk hh)⟩
  choose s hs using hchoices
  have hMpart : (Cm.card : ℝ) = ∑ k ∈ I, ((CM k).card : ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_fiberwise (show Set.MapsTo dm
      (Cm : Set (Finset ℕ)) (I : Set ℕ) from fun S hS => Finset.mem_Icc.mpr
        ⟨(hm S hS).1,(hm S hS).2.1⟩)
  have hPpart : (Cp.card : ℝ) = ∑ k ∈ I, ((CP k).card : ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_fiberwise (show Set.MapsTo dp
      (Cp : Set (Finset ℕ)) (I : Set ℕ) from fun S hS => Finset.mem_Icc.mpr
        ⟨(hp S hS).1,(hp S hS).2.1⟩)
  have hEpart : (E.card : ℝ) = ∑ k ∈ I, ((EP k).card : ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_fiberwise (show Set.MapsTo de
      (E : Set (Finset ℕ)) (I : Set ℕ) from fun S hS => Finset.mem_Icc.mpr
        ⟨(he S hS).1,(he S hS).2.1⟩)
  have hsum := Finset.sum_le_sum (fun k hk => (hs k hk).2.2)
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,Finset.sum_add_distrib,
    ← hMpart,← hPpart,← hEpart] at hsum
  have herr : (∑ k ∈ I, (40*reciprocalSum N+2)*N/(k : ℝ)) =
      (40*reciprocalSum N+2)*N*reciprocalSum N := by
    simp only [div_eq_mul_inv,← Finset.mul_sum,I,reciprocalSum]
  rw [herr] at hsum
  have hdef := weighted_middle_deficit hN hcL hLR hRN s (fun k hk =>
    ⟨(hs k hk).1,(hs k hk).2.1⟩)
  linarith only [hsum,hdef]

end
/- MiddleProgressionModels -/

/- Centered models with a last endpoint in the middle region. -/

section
open Finset

theorem middle_progression_centered_model {N c L R a d : ℕ} {S : Finset ℕ}
    (hsub : S ⊆ Finset.Icc 1 N) (hd : 0 < d) (hcard : 4 ≤ S.card)
    (hrep : S = natAP a d S.card) (hcS : c ∈ S) (hac : a < c)
    (hcL : c ≤ L) (hLb : L < a+(S.card-1)*d) (hbR : a+(S.card-1)*d ≤ R) :
    ∃ p : ProgressionCell, IsCenteredModel c d p S ∧ 1 ≤ p.val.1 ∧ p.val.1 ≤ c/d ∧
      (L-c)/d < p.val.2 ∧ p.val.2 ≤ (R-c)/d := by
  obtain ⟨i,hi,hci⟩ := mem_natAP.mp (hrep ▸ hcS)
  let p : ProgressionCell := ⟨(i,S.card-1-i),by omega⟩
  have hp : IsCenteredModel c d p S := by
    change S.image (fun x : ℕ => (x : ℤ)) = _
    have hcast := congrArg (fun T : Finset ℕ => T.image (fun x : ℕ => (x : ℤ))) hrep
    exact hcast.trans (by simpa only [hci] using natAP_cast_eq_affine_interval a d S.card i hi)
  have hi1 : 1 ≤ i := by nlinarith only [hci,hac]
  have hiC : i ≤ c/d := (Nat.le_div_iff_mul_le hd).mpr (by omega)
  have hlast : c+p.val.2*d = a+(S.card-1)*d := by
    have hsumi : i+(S.card-1-i) = S.card-1 := by omega
    dsimp only [p]
    nlinarith only [hci,hsumi]
  have hlow : (L-c)/d < p.val.2 := (Nat.div_lt_iff_lt_mul hd).mpr (by omega)
  have hupp : p.val.2 ≤ (R-c)/d := (Nat.le_div_iff_mul_le hd).mpr (by omega)
  exact ⟨p,hp,hi1,hiC,hlow,hupp⟩

end
/- OneSidedOuterRectangles -/

/- The remaining two rectangle bounds for one-sided intrinsic witnesses. -/

section
open Finset

theorem crooked_witness_rectangle_card_le {N c : ℕ} {F C : Finset (Finset ℕ)} {A B : Finset ℕ}
    (hF : Erdos272.IsArithInterSet N F) (hCF : C ⊆ F) (hc : ∀ S ∈ C, c ∈ S)
    (hcrooked : ∀ S ∈ C, IsCrooked S)
    (hW : ∀ S ∈ C, ∃ x ∈ A, ∃ p ∈ B, IsWitnessPair S c {x,p}) : C.card ≤ A.card*B.card := by
  have hh := private_pairs_and_intervals_card_le (E := ∅) (Pool := crossPairPool A B) hF hCF
    (Finset.empty_subset _) hc hcrooked
    (by
      intro S hS
      obtain ⟨x,hx,p,hp,hW⟩ := hW S hS
      exact ⟨{x,p},hW,Finset.mem_image.mpr ⟨(x,p),Finset.mem_product.mpr ⟨hx,hp⟩,rfl⟩⟩)
    (by intro S hS; simp only [Finset.notMem_empty] at hS)
  have hpool := crossPairPool_card_le A B
  simp only [Finset.card_empty,Nat.add_zero] at hh
  exact hh.trans hpool

theorem middle_far_witnesses_card_le {N c L R : ℕ} {F C : Finset (Finset ℕ)}
    (hF : Erdos272.IsArithInterSet N F) (hCF : C ⊆ F) (hc : ∀ S ∈ C, c ∈ S)
    (hcrooked : ∀ S ∈ C, IsCrooked S) (x p : Finset ℕ → ℕ)
    (hW : ∀ S ∈ C, L < x S ∧ x S ≤ R ∧ R < p S ∧ IsWitnessPair S c {x S,p S}) :
    C.card ≤ (R-L)*(N-R) := by
  have hh := crooked_witness_rectangle_card_le (A := Finset.Ioc L R) (B := Finset.Ioc R N)
    hF hCF hc hcrooked (by
      intro S hS
      obtain ⟨hxL,hxR,hRp,hW⟩ := hW S hS
      have hpS : p S ∈ S := Finset.mem_of_mem_erase (hW.2.1 (by simp))
      have hpN := (Finset.mem_Icc.mp (Finset.mem_powerset.mp (hF.1 (hCF hS)) hpS)).2
      exact ⟨x S,Finset.mem_Ioc.mpr ⟨hxL,hxR⟩,p S,Finset.mem_Ioc.mpr ⟨hRp,hpN⟩,hW⟩)
  simpa only [Nat.card_Ioc] using hh

theorem left_corner_and_intervals_card_le {N c R : ℕ} {F C E : Finset (Finset ℕ)}
    (hcR : c ≤ R) (hF : Erdos272.IsArithInterSet N F) (hCF : C ⊆ F) (hEF : E ⊆ F)
    (hc : ∀ S ∈ C, c ∈ S) (hcrooked : ∀ S ∈ C, IsCrooked S)
    (x p : Finset ℕ → ℕ)
    (hW : ∀ S ∈ C, x S < c ∧ R < p S ∧ IsWitnessPair S c {x S,p S})
    (hE : ∀ S ∈ E, ∃ a b : ℕ, a < c ∧ R < b ∧ S = Finset.Icc a b) :
    C.card+E.card ≤ c*(N-R) := by
  let Pool := crossPairPool (Finset.Icc 1 c) (Finset.Ioc R N)
  have hh : C.card+E.card ≤ Pool.card := by
    apply private_pairs_and_intervals_card_le hF hCF hEF hc hcrooked
    · intro S hS
      obtain ⟨hxc,hRp,hW⟩ := hW S hS
      have hxS : x S ∈ S := Finset.mem_of_mem_erase (hW.2.1 (by simp))
      have hpS : p S ∈ S := Finset.mem_of_mem_erase (hW.2.1 (by simp))
      have hx1 := (Finset.mem_Icc.mp (Finset.mem_powerset.mp (hF.1 (hCF hS)) hxS)).1
      have hpN := (Finset.mem_Icc.mp (Finset.mem_powerset.mp (hF.1 (hCF hS)) hpS)).2
      exact ⟨{x S,p S},hW,Finset.mem_image.mpr ⟨(x S,p S),Finset.mem_product.mpr
        ⟨Finset.mem_Icc.mpr ⟨hx1,hxc.le⟩,Finset.mem_Ioc.mpr ⟨hRp,hpN⟩⟩,rfl⟩⟩
    · intro S hS
      obtain ⟨a,b,hac,hRb,hrep⟩ := hE S hS
      have hab : a ≤ b := hac.le.trans (hcR.trans hRb.le)
      have haS : a ∈ S := by rw [hrep]; exact Finset.mem_Icc.mpr ⟨le_rfl,hab⟩
      have hbS : b ∈ S := by rw [hrep]; exact Finset.mem_Icc.mpr ⟨hab,le_rfl⟩
      have ha1 := (Finset.mem_Icc.mp (Finset.mem_powerset.mp (hF.1 (hEF hS)) haS)).1
      have hbN := (Finset.mem_Icc.mp (Finset.mem_powerset.mp (hF.1 (hEF hS)) hbS)).2
      exact ⟨a,b,hac,hcR.trans_lt hRb,hrep,Finset.mem_image.mpr ⟨(a,b),Finset.mem_product.mpr
        ⟨Finset.mem_Icc.mpr ⟨ha1,hac.le⟩,Finset.mem_Ioc.mpr ⟨hRb,hbN⟩⟩,rfl⟩⟩
  have hpool : Pool.card ≤ c*(N-R) := by
    simpa only [Nat.card_Icc,Nat.add_sub_cancel,Nat.card_Ioc] using
      crossPairPool_card_le (Finset.Icc 1 c) (Finset.Ioc R N)
  exact hh.trans hpool

end
/- MiddlePreparedFamily -/

/- Applying the middle-region estimate directly to selected natural witness pairs. -/

section
open Finset

theorem middle_prepared_family_bound {N c L R : ℕ} {F C E : Finset (Finset ℕ)}
    (hN : 1 ≤ N) (hcL : c ≤ L) (hLR : L ≤ R) (hRN : R ≤ N)
    (hF : Erdos272.IsArithInterSet N F) (hCF : C ⊆ F) (hEF : E ⊆ F)
    (hcC : ∀ S ∈ C, c ∈ S) (hcrooked : ∀ S ∈ C, IsCrooked S)
    (x p a d : Finset ℕ → ℕ)
    (hW : ∀ S ∈ C, IsWitnessPair S c {x S,p S} ∧ x S < p S ∧ L < p S ∧ p S ≤ R)
    (hE : ∀ S ∈ E, 0 < d S ∧ d S ≤ N ∧ 4 ≤ S.card ∧ S = natAP (a S) (d S) S.card ∧
      c ∈ S ∧ a S < c ∧ L < a S+(S.card-1)*d S ∧ a S+(S.card-1)*d S ≤ R) :
    (5/3)*(L : ℝ)*(N-R)+((R : ℝ)-L)*(N-R)+(C.card : ℝ)+E.card ≤
      (N : ℝ)^2/2-((L : ℝ)^2+((N : ℝ)-R)^2)/100+
        (40*reciprocalSum N+2)*N*reciprocalSum N := by
  classical
  let Cm := C.filter (fun S => x S < c)
  let Cp := C.filter (fun S => ¬x S < c)
  have hCm : Cm ⊆ C := Finset.filter_subset _ _
  have hCp : Cp ⊆ C := Finset.filter_subset _ _
  have hneg : ∀ S : Finset ℕ, ∃ dm am bm : ℕ, S ∈ Cm →
      0 < dm ∧ dm ≤ N ∧ 1 ≤ am ∧ am ≤ c/dm ∧ (L-c)/dm < bm ∧ bm ≤ (R-c)/dm ∧
      am.Coprime bm ∧ IsWitnessPair S c {c-am*dm,c+bm*dm} := by
    intro S
    by_cases hS : S ∈ Cm
    · have hw := hW S (hCm hS)
      obtain ⟨dm,am,bm,hh⟩ := negative_middle_witness_coordinates
        (Finset.mem_filter.mp hS).2 hcL hw.2.2.1 hw.2.2.2 hRN hw.1
      exact ⟨dm,am,bm,fun _ => hh⟩
    · exact ⟨1,1,1,fun hh => False.elim (hS hh)⟩
  have hpos : ∀ S : Finset ℕ, ∃ dp ap bp : ℕ, S ∈ Cp →
      0 < dp ∧ dp ≤ N ∧ 1 ≤ ap ∧ ap < bp ∧ (L-c)/dp < bp ∧ bp ≤ (R-c)/dp ∧
      ap.Coprime bp ∧ IsWitnessPair S c {c+ap*dp,c+bp*dp} := by
    intro S
    by_cases hS : S ∈ Cp
    · have hw := hW S (hCp hS)
      have hxc : x S ≠ c := (Finset.mem_erase.mp (hw.1.2.1 (by simp))).1
      have hcx : c < x S := by have hn := (Finset.mem_filter.mp hS).2; omega
      obtain ⟨dp,ap,bp,hh⟩ := positive_middle_witness_coordinates hcx hw.2.1 hcL
        hw.2.2.1 hw.2.2.2 hRN hw.1
      exact ⟨dp,ap,bp,fun _ => hh⟩
    · exact ⟨1,1,2,fun hh => False.elim (hS hh)⟩
  have hemodel : ∀ S : Finset ℕ, ∃ model : ProgressionCell, S ∈ E →
      IsCenteredModel c (d S) model S ∧ 1 ≤ model.val.1 ∧ model.val.1 ≤ c/d S ∧
        (L-c)/d S < model.val.2 ∧ model.val.2 ≤ (R-c)/d S := by
    intro S
    by_cases hS : S ∈ E
    · obtain ⟨hd,_hdN,hcard,hrep,hc,hac,hLb,hbR⟩ := hE S hS
      obtain ⟨model,hh⟩ := middle_progression_centered_model
        (Finset.mem_powerset.mp (hF.1 (hEF hS))) hd hcard hrep hc hac hcL hLb hbR
      exact ⟨model,fun _ => hh⟩
    · exact ⟨⟨(0,3),by decide⟩,fun hh => False.elim (hS hh)⟩
  choose dm am bm hm using hneg
  choose dp ap bp hp using hpos
  choose model hmodel using hemodel
  have hh := middle_family_sum_bound hN hcL hLR hRN hF (hCm.trans hCF) (hCp.trans hCF) hEF
    (fun S hS => hcC S (hCm hS)) (fun S hS => hcC S (hCp hS))
    (fun S hS => hcrooked S (hCm hS)) (fun S hS => hcrooked S (hCp hS))
    dm dp d (fun S => (am S,bm S)) (fun S => (ap S,bp S)) model hm hp
    (by
      intro S hS
      have heS := hE S hS
      have hmS := hmodel S hS
      refine ⟨heS.1,heS.2.1,hmS.1,hmS.2.1,hmS.2.2.1,hmS.2.2.2.1,hmS.2.2.2.2,?_⟩
      rw [heS.2.2.2.1]
      exact ⟨(S.card : ℕ∞),natAP_isAP heS.1⟩)
  have hpart : (Cm.card : ℝ)+Cp.card = C.card := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := C) (fun S => x S < c)
  linarith only [hh,hpart]

end
/- PreparedPartitionLemmas -/

/- Elementary interval and finite-partition identities used in the one-sided assembly. -/

section
open Finset

theorem natAP_one_eq_Icc {a k : ℕ} (hk : 0 < k) : natAP a 1 k = Finset.Icc a (a+(k-1)) := by
  ext x
  constructor
  · intro hx
    have hh := natAP_bounds_of_mem hx
    exact Finset.mem_Icc.mpr (by simpa only [Nat.mul_one] using hh)
  · intro hx
    obtain ⟨hax,hxend⟩ := Finset.mem_Icc.mp hx
    exact mem_natAP.mpr ⟨x-a,by omega,by omega⟩

theorem card_le_four_of_cover {α : Type*} [DecidableEq α] {S A B C D : Finset α}
    (hcover : S ⊆ A ∪ B ∪ C ∪ D) : S.card ≤ A.card+B.card+C.card+D.card := by
  have hh := Finset.card_le_card hcover
  have h₁ := Finset.card_union_le A B
  have h₂ := Finset.card_union_le (A ∪ B) C
  have h₃ := Finset.card_union_le (A ∪ B ∪ C) D
  omega

theorem card_le_five_of_cover {α : Type*} [DecidableEq α] {S A B C D E : Finset α}
    (hcover : S ⊆ A ∪ B ∪ C ∪ D ∪ E) : S.card ≤ A.card+B.card+C.card+D.card+E.card := by
  have hh := Finset.card_le_card hcover
  have h₁ := card_le_four_of_cover (Finset.Subset.refl (A ∪ B ∪ C ∪ D))
  have h₂ := Finset.card_union_le (A ∪ B ∪ C ∪ D) E
  omega

end
/- OneSidedPreparedBound -/

/- Assembly of the prepared one-sided family estimate, with a retained endpoint deficit. -/

section
open Finset

theorem one_sided_prepared_card_le {N c L R : ℕ} {F C E : Finset (Finset ℕ)}
    (hN : 1 ≤ N) (hcL : c ≤ L) (hLR : L ≤ R) (hRN : R ≤ N)
    (hF : Erdos272.IsArithInterSet N F) (hCF : C ⊆ F) (hEF : E ⊆ F)
    (hcC : ∀ S ∈ C, c ∈ S) (hcrooked : ∀ S ∈ C, IsCrooked S)
    (x p a d : Finset ℕ → ℕ)
    (hW : ∀ S ∈ C, IsWitnessPair S c {x S,p S} ∧ x S < p S ∧ x S ≤ R ∧ L < p S ∧
      x S ≠ L ∧ (c < x S → x S < L → R < p S →
        S ∩ Finset.Icc (x S) (p S) = {x S,p S} ∨ IsCrooked (S ∩ Finset.Icc (x S) (p S))))
    (hE : ∀ S ∈ E, 0 < d S ∧ d S ≤ N ∧ 4 ≤ S.card ∧ S = natAP (a S) (d S) S.card ∧
      (c ∈ S → a S < c ∧ L < a S+(S.card-1)*d S) ∧
      (c ∉ S → a S ≤ L ∧ R ≤ a S+(S.card-1)*d S)) :
    (C.card : ℝ)+E.card ≤ (N : ℝ)^2/2-((L : ℝ)^2+((N : ℝ)-R)^2)/100+
      (40*reciprocalSum N+4)*N*reciprocalSum N+4*N := by
  classical
  let b (S : Finset ℕ) := a S+(S.card-1)*d S
  let CM := C.filter (fun S => p S ≤ R)
  let CL := C.filter (fun S => R < p S ∧ x S < c)
  let CQ := C.filter (fun S => R < p S ∧ c < x S ∧ x S < L)
  let CX := C.filter (fun S => R < p S ∧ L < x S)
  let EM := E.filter (fun S => c ∈ S ∧ b S ≤ R)
  let EX := E.filter (fun S => 2 ≤ d S ∧ R ≤ b S)
  let EI := E.filter (fun S => c ∈ S ∧ d S = 1 ∧ R < b S)
  let EP := E.filter (fun S => c ∉ S ∧ d S = 1 ∧ R < b S)
  let EB := E.filter (fun S => c ∉ S ∧ d S = 1 ∧ b S = R)
  have hCMM : CM ⊆ C := Finset.filter_subset _ _
  have hCLM : CL ⊆ C := Finset.filter_subset _ _
  have hCQM : CQ ⊆ C := Finset.filter_subset _ _
  have hCXM : CX ⊆ C := Finset.filter_subset _ _
  have hEME : EM ⊆ E := Finset.filter_subset _ _
  have hEXE : EX ⊆ E := Finset.filter_subset _ _
  have hEIE : EI ⊆ E := Finset.filter_subset _ _
  have hEPE : EP ⊆ E := Finset.filter_subset _ _
  have hEBE : EB ⊆ E := Finset.filter_subset _ _
  have hCcover : C ⊆ CM ∪ CL ∪ CQ ∪ CX := by
    intro S hS
    have hw := hW S hS
    have hxc : x S ≠ c := (Finset.mem_erase.mp (hw.1.2.1 (by simp))).1
    have hxL := hw.2.2.2.2.1
    simp only [CM,CL,CQ,CX,Finset.mem_union,Finset.mem_filter,hS,true_and]
    omega
  have hEcover : E ⊆ EM ∪ EX ∪ EI ∪ EP ∪ EB := by
    intro S hS
    have heS := hE S hS
    have hdpos := heS.1
    by_cases hcS : c ∈ S
    · have hh := heS.2.2.2.2.1 hcS
      simp only [EM,EX,EI,EP,EB,Finset.mem_union,Finset.mem_filter,hS,true_and,hcS,
        not_true_eq_false,false_and,or_false]
      omega
    · have hh := heS.2.2.2.2.2 hcS
      change a S ≤ L ∧ R ≤ b S at hh
      simp only [EM,EX,EI,EP,EB,Finset.mem_union,Finset.mem_filter,hS,true_and,hcS,
        not_false_eq_true,false_and,false_or]
      omega
  have hCcount : (C.card : ℝ) ≤ CM.card+CL.card+CQ.card+CX.card := by
    exact_mod_cast card_le_four_of_cover hCcover
  have hEcount : (E.card : ℝ) ≤ EM.card+EX.card+EI.card+EP.card+EB.card := by
    exact_mod_cast card_le_five_of_cover hEcover
  have hinterval : ∀ S ∈ E, d S = 1 → S = Finset.Icc (a S) (b S) := by
    intro S hS hd1
    have heS := hE S hS
    calc
      S = natAP (a S) (d S) S.card := heS.2.2.2.1
      _ = Finset.Icc (a S) (b S) := by
        rw [hd1,natAP_one_eq_Icc (by omega : 0 < S.card)]
        simp only [b,hd1,Nat.mul_one]
  have hbN : ∀ S ∈ E, b S ≤ N := by
    intro S hS
    have heS := hE S hS
    have hbS : b S ∈ S := by
      have hh : b S ∈ natAP (a S) (d S) S.card :=
        mem_natAP.mpr ⟨S.card-1,by have hh := heS.2.2.1; omega,rfl⟩
      simpa only [← heS.2.2.2.1] using hh
    exact (Finset.mem_Icc.mp (Finset.mem_powerset.mp (hF.1 (hEF hS)) hbS)).2
  have hmiddle := middle_prepared_family_bound hN hcL hLR hRN hF (hCMM.trans hCF) (hEME.trans hEF)
    (fun S hS => hcC S (hCMM hS)) (fun S hS => hcrooked S (hCMM hS)) x p a d
    (by
      intro S hS
      have hw := hW S (hCMM hS)
      exact ⟨hw.1,hw.2.1,hw.2.2.2.1,(Finset.mem_filter.mp hS).2⟩)
    (by
      intro S hS
      obtain ⟨hSE,hcS,hbR⟩ := Finset.mem_filter.mp hS
      have heS := hE S hSE
      obtain ⟨hac,hLb⟩ := heS.2.2.2.2.1 hcS
      exact ⟨heS.1,heS.2.1,heS.2.2.1,heS.2.2.2.1,hcS,hac,hLb,hbR⟩)
  have hleftNat := left_corner_and_intervals_card_le (hcL.trans hLR) hF (hCLM.trans hCF)
    (hEIE.trans hEF) (fun S hS => hcC S (hCLM hS)) (fun S hS => hcrooked S (hCLM hS)) x p
    (by
      intro S hS
      obtain ⟨hSC,hRp,hxc⟩ := Finset.mem_filter.mp hS
      exact ⟨hxc,hRp,(hW S hSC).1⟩)
    (by
      intro S hS
      obtain ⟨hSE,hcS,hd1,hRb⟩ := Finset.mem_filter.mp hS
      exact ⟨a S,b S,((hE S hSE).2.2.2.2.1 hcS).1,hRb,hinterval S hSE hd1⟩)
  have hleft : (CL.card : ℝ)+EI.card ≤ (c : ℝ)*((N : ℝ)-R) := by
    exact_mod_cast hleftNat
  have hrightNat := corner_witnesses_and_intervals_card_le hLR hRN hF (hCQM.trans hCF)
    (hEPE.trans hEF) (fun S hS => hcC S (hCQM hS)) x p a b
    (by
      intro S hS
      obtain ⟨hSC,hRp,hcx,hxL⟩ := Finset.mem_filter.mp hS
      have hw := hW S hSC
      have hpS : p S ∈ S := Finset.mem_of_mem_erase (hw.1.2.1 (by simp))
      have hpN := (Finset.mem_Icc.mp (Finset.mem_powerset.mp (hF.1 (hCF hSC)) hpS)).2
      exact ⟨hcx,hxL,hRp,hpN,hw.1,hw.2.2.2.2.2 hcx hxL hRp⟩)
    (by
      intro S hS
      obtain ⟨hSE,hcS,hd1,hRb⟩ := Finset.mem_filter.mp hS
      have heS := hE S hSE
      have hrep := hinterval S hSE hd1
      have hca : c < a S := by
        by_contra hn
        apply hcS
        rw [hrep]
        exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
      exact ⟨hca,(heS.2.2.2.2.2 hcS).1,hRb,hbN S hSE,hrep⟩)
  have hright : (CQ.card : ℝ)+EP.card ≤ ((L : ℝ)-c)*((N : ℝ)-R)+2*N := by
    exact_mod_cast hrightNat
  have hfarNat := middle_far_witnesses_card_le hF (hCXM.trans hCF)
    (fun S hS => hcC S (hCXM hS)) (fun S hS => hcrooked S (hCXM hS)) x p
    (by
      intro S hS
      obtain ⟨hSC,hRp,hLx⟩ := Finset.mem_filter.mp hS
      have hw := hW S hSC
      exact ⟨hLx,hw.2.2.1,hRp,hw.1⟩)
  have hfar : (CX.card : ℝ) ≤ ((R : ℝ)-L)*((N : ℝ)-R) := by exact_mod_cast hfarNat
  have hlarge := large_step_endpoint_rectangle_card_le (hLR.trans hRN) hRN
    (admissible_subfamily hF (hEXE.trans hEF))
    (fun S hS => by have hh := (hE S (hEXE hS)).2.2.1; omega)
    (by
      intro S hS
      obtain ⟨hSE,hd2,hRb⟩ := Finset.mem_filter.mp hS
      have heS := hE S hSE
      have haL : a S ≤ L := by
        by_cases hcS : c ∈ S
        · exact ((heS.2.2.2.2.1 hcS).1.le).trans hcL
        · exact (heS.2.2.2.2.2 hcS).1
      exact ⟨a S,d S,hd2,heS.2.1,heS.2.2.2.1,haL,hRb⟩)
  have hboundaryNat : EB.card ≤ N := by
    have hcover : EB ⊆ (Finset.Icc 1 N).image (fun a => Finset.Icc a R) := by
      intro S hS
      obtain ⟨hSE,_hcS,hd1,hbR⟩ := Finset.mem_filter.mp hS
      have hrep := hinterval S hSE hd1
      have haS : a S ∈ S := by
        have hh : a S ∈ natAP (a S) (d S) S.card :=
          mem_natAP.mpr ⟨0,by have hh := (hE S hSE).2.2.1; omega,by simp⟩
        simpa only [← (hE S hSE).2.2.2.1] using hh
      exact Finset.mem_image.mpr ⟨a S,Finset.mem_powerset.mp (hF.1 (hEF hSE)) haS,
        by simpa only [hbR] using hrep.symm⟩
    have hh := (Finset.card_le_card hcover).trans (Finset.card_image_le)
    simpa only [Nat.card_Icc,Nat.add_sub_cancel] using hh
  have hboundary : (EB.card : ℝ) ≤ N := by exact_mod_cast hboundaryNat
  nlinarith only [hCcount,hEcount,hmiddle,hleft,hright,hfar,hlarge,hboundary]

end
/- ProgressionBoundaryCount -/

/- Linear-harmonic bounds for progressions with a prescribed endpoint. -/

section
open Finset

theorem same_step_fixed_endpoint_card_le {N d q : ℕ} {F : Finset (Finset ℕ)} (first : Bool)
    (hd : 0 < d) (hsub : ∀ S ∈ F, S ⊆ Finset.Icc 1 N) (hcard : ∀ S ∈ F, 0 < S.card)
    (hparam : ∀ S ∈ F, ∃ a : ℕ, S = natAP a d S.card ∧
      (if first then a else a+(S.card-1)*d) = q) : F.card ≤ N/d+1 := by
  classical
  let X := {S // S ∈ F}
  have hp : ∀ S : X, ∃ a : ℕ, S.val = natAP a d S.val.card ∧
      (if first then a else a+(S.val.card-1)*d) = q := fun S => hparam S.val S.property
  choose a hrep hend using hp
  let f (S : X) := S.val.card-1
  have hlen : ∀ S : X, f S ≤ N/d := by
    intro S
    have hbS : a S+(S.val.card-1)*d ∈ S.val := by
      have hh : a S+(S.val.card-1)*d ∈ natAP (a S) d S.val.card :=
        mem_natAP.mpr ⟨S.val.card-1,by have hh := hcard S.val S.property; omega,rfl⟩
      simpa only [← hrep S] using hh
    have hbN := (Finset.mem_Icc.mp (hsub S.val S.property hbS)).2
    exact (Nat.le_div_iff_mul_le hd).mpr (by dsimp only [f]; omega)
  have hinj : Function.Injective f := by
    intro S T heq
    have hSC := hcard S.val S.property
    have hTC := hcard T.val T.property
    have hcards : S.val.card = T.val.card := by dsimp only [f] at heq; omega
    have haeq : a S = a T := by
      have hSe := hend S
      have hTe := hend T
      cases first <;> simp only [Bool.false_eq_true,↓reduceIte] at hSe hTe
      · rw [hcards] at hSe
        omega
      · omega
    apply Subtype.ext
    rw [hrep S,hrep T,hcards,haeq]
  have hmaps : Set.MapsTo f ((Finset.univ : Finset X) : Set X) (Finset.range (N/d+1) : Set ℕ) := by
    intro S _hS
    exact Finset.mem_range.mpr (by have hh := hlen S; omega)
  simpa only [Finset.card_univ,Finset.card_range,X,Fintype.card_coe] using
    Finset.card_le_card_of_injOn f hmaps hinj.injOn

theorem progression_fixed_endpoint_card_le {N q : ℕ} {F : Finset (Finset ℕ)} (first : Bool)
    (hsub : ∀ S ∈ F, S ⊆ Finset.Icc 1 N) (hcard : ∀ S ∈ F, 0 < S.card)
    (hparam : ∀ S ∈ F, ∃ a d : ℕ, 0 < d ∧ d ≤ N ∧ S = natAP a d S.card ∧
      (if first then a else a+(S.card-1)*d) = q) :
    (F.card : ℝ) ≤ (N : ℝ)*reciprocalSum N+N := by
  classical
  have hp : ∀ S : Finset ℕ, ∃ a d : ℕ, S ∈ F → 0 < d ∧ d ≤ N ∧ S = natAP a d S.card ∧
      (if first then a else a+(S.card-1)*d) = q := by
    intro S
    by_cases hS : S ∈ F
    · obtain ⟨a,d,hh⟩ := hparam S hS
      exact ⟨a,d,fun _ => hh⟩
    · exact ⟨0,1,fun hh => False.elim (hS hh)⟩
  choose a d hspec using hp
  have hpart : (F.card : ℝ) = ∑ k ∈ Finset.Icc 1 N,
      ((F.filter (fun S => d S = k)).card : ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_fiberwise (show Set.MapsTo d
      (F : Set (Finset ℕ)) (Finset.Icc 1 N : Set ℕ) from fun S hS =>
        Finset.mem_Icc.mpr ⟨(hspec S hS).1,(hspec S hS).2.1⟩)
  have hbound : ∀ k ∈ Finset.Icc 1 N,
      ((F.filter (fun S => d S = k)).card : ℝ) ≤ (N : ℝ)/k+1 := by
    intro k hk
    have hh := same_step_fixed_endpoint_card_le (F := F.filter (fun S => d S = k))
      first (Finset.mem_Icc.mp hk).1
      (fun S hS => hsub S (Finset.mem_filter.mp hS).1)
      (fun S hS => hcard S (Finset.mem_filter.mp hS).1)
      (by
        intro S hS
        obtain ⟨hSF,hdk⟩ := Finset.mem_filter.mp hS
        exact ⟨a S,by simpa only [hdk] using (hspec S hSF).2.2⟩)
    have hhR : ((F.filter (fun S => d S = k)).card : ℝ) ≤ ((N/k : ℕ)+1 : ℝ) := by
      exact_mod_cast hh
    have hdiv := Nat.cast_div_le (α := ℝ) (m := N) (n := k)
    linarith only [hhR,hdiv]
  rw [hpart]
  calc
    _ ≤ ∑ k ∈ Finset.Icc 1 N, ((N : ℝ)/k+1) := Finset.sum_le_sum hbound
    _ = _ := by simp [div_eq_mul_inv,Finset.sum_add_distrib,← Finset.mul_sum,reciprocalSum]

end
/- CrookedOneSidedPreparation -/

/- Preparing all but a controlled number of crooked members for the one-sided count. -/

section
open Finset

theorem prepare_one_sided_crooked {N c L R : ℕ} {F C : Finset (Finset ℕ)} {P T : Finset ℕ}
    (hcL : c ≤ L) (hLR : L ≤ R) (hF : Erdos272.IsArithInterSet N F) (hCF : C ⊆ F)
    (hcC : ∀ S ∈ C, c ∈ S) (hcrooked : ∀ S ∈ C, IsCrooked S)
    (hP : P ∈ F) (hcP : c ∉ P) (hLP : ∀ x ∈ P, L ≤ x)
    (hT : T ∈ F) (hcT : c ∉ T) (hTR : ∀ x ∈ T, x ≤ R) :
    ∃ G : Finset (Finset ℕ), G ⊆ C ∧ C.card ≤ G.card+N+witnessExceptionBound N c ∧
      ∃ x p : Finset ℕ → ℕ, ∀ S ∈ G, IsWitnessPair S c {x S,p S} ∧
        x S < p S ∧ x S ≤ R ∧ L < p S ∧ x S ≠ L ∧
        (c < x S → x S < L → R < p S →
          S ∩ Finset.Icc (x S) (p S) = {x S,p S} ∨ IsCrooked (S ∩ Finset.Icc (x S) (p S))) := by
  classical
  let High (S : Finset ℕ) := ∃ W, IsWitnessPair S c W ∧ ∃ x ∈ W, L ≤ x
  let Boundary (S : Finset ℕ) := ∃ W, IsWitnessPair S c W ∧ L ∈ W
  let A := C.filter High
  let B := C.filter (fun S => ¬High S)
  let G := A.filter (fun S => ¬Boundary S)
  let D := A.filter Boundary
  have hAC : A ⊆ C := Finset.filter_subset _ _
  have hBC : B ⊆ C := Finset.filter_subset _ _
  have hGA : G ⊆ A := Finset.filter_subset _ _
  have hDA : D ⊆ A := Finset.filter_subset _ _
  have hGC : G ⊆ C := hGA.trans hAC
  have hB : B.card ≤ witnessExceptionBound N c := by
    apply restricted_witness_bad_family_card_le (admissible_subfamily hF (hBC.trans hCF))
      (fun S hS => hcC S (hBC hS)) (fun S hS => hcrooked S (hBC hS))
    · intro S hS
      obtain ⟨z,hz⟩ := arithInter_inter_nonempty hF (hCF (hBC hS)) hP ⟨c,hcC S (hBC hS)⟩
      obtain ⟨hzS,hzP⟩ := Finset.mem_inter.mp hz
      exact ⟨z,Finset.mem_inter.mpr ⟨Finset.mem_erase.mpr
        ⟨fun heq => hcP (heq ▸ hzP),hzS⟩,hzP⟩⟩
    · intro S hS W hW
      apply Finset.disjoint_left.mpr
      intro z hzW hzP
      exact (Finset.mem_filter.mp hS).2 ⟨W,hW,z,hzW,hLP z hzP⟩
  have hD : D.card ≤ N := division_point_witness_family_card_le hF
    ((hDA.trans hAC).trans hCF) (fun S hS => hcC S (hAC (hDA hS)))
    (fun S hS => (Finset.mem_filter.mp hS).2)
  have hpart : A.card+B.card = C.card := Finset.card_filter_add_card_filter_not (s := C) High
  have hpartA : D.card+G.card = A.card := Finset.card_filter_add_card_filter_not (s := A) Boundary
  refine ⟨G,hGC,by omega,?_⟩
  have hchoice : ∀ S : Finset ℕ, ∃ x p : ℕ, S ∈ G → IsWitnessPair S c {x,p} ∧
      x < p ∧ x ≤ R ∧ L < p ∧ x ≠ L ∧ (c < x → x < L → R < p →
        S ∩ Finset.Icc x p = {x,p} ∨ IsCrooked (S ∩ Finset.Icc x p)) := by
    intro S
    by_cases hS : S ∈ G
    · have hAS := hGA hS
      obtain ⟨W,hW,hhigh⟩ := (Finset.mem_filter.mp hAS).2
      have hnoL : ∀ W, IsWitnessPair S c W → L ∉ W := by
        intro W hW hLW
        exact (Finset.mem_filter.mp hS).2 ⟨W,hW,hLW⟩
      obtain ⟨x,p,hxp,hlt,hxR,hLp,hcrop⟩ := ordered_one_sided_witness hLR
        (witness_reaches_avoider_endpoint hF (hCF (hGC hS)) hT (hcC S (hGC hS)) hcT hTR
          (hcL.trans hLR) hLR hW hhigh) hnoL
      have hxL : x ≠ L := by intro heq; exact hnoL {x,p} hxp (by simp [heq])
      exact ⟨x,p,fun _ => ⟨hxp,hlt,hxR,hLp,hxL,hcrop⟩⟩
    · exact ⟨0,0,fun hh => False.elim (hS hh)⟩
  choose x p hspec using hchoice
  exact ⟨x,p,hspec⟩

end
/- ProgressionOneSidedPreparation -/

/- Preparing progression endpoints for the one-sided estimate. -/

section
open Finset

theorem prepare_one_sided_progressions {N c L R : ℕ} {F A : Finset (Finset ℕ)} {P : Finset ℕ}
    (hF : Erdos272.IsArithInterSet N F) (hAF : A ⊆ F)
    (hAP : ∀ S ∈ A, ∃ l : ℕ∞, (S : Set ℕ).IsAPOfLength l)
    (hP : P ∈ F) (hLP : ∀ x ∈ P, L ≤ x)
    (houtside : ∀ S ∈ A, c ∉ S → (∃ u ∈ S, u ≤ L) ∧ ∃ v ∈ S, R ≤ v) :
    ∃ E : Finset (Finset ℕ), E ⊆ A ∧
      (A.card : ℝ) ≤ E.card+2*N*reciprocalSum N+20*N+3 ∧
      ∃ a d : Finset ℕ → ℕ, ∀ S ∈ E, 0 < d S ∧ d S ≤ N ∧ 4 ≤ S.card ∧
        S = natAP (a S) (d S) S.card ∧
        (c ∈ S → a S < c ∧ L < a S+(S.card-1)*d S) ∧
        (c ∉ S → a S ≤ L ∧ R ≤ a S+(S.card-1)*d S) := by
  classical
  let B := A.filter (fun S => 4 ≤ S.card)
  let Small := A.filter (fun S => ¬4 ≤ S.card)
  have hBA : B ⊆ A := Finset.filter_subset _ _
  have hSA : Small ⊆ A := Finset.filter_subset _ _
  have hsmall : Small.card ≤ 18*N+3 := progression_family_small_card_le
    (admissible_subfamily hF (hSA.trans hAF)) (fun S hS => hAP S (hSA hS))
    (fun S hS => by have hh := (Finset.mem_filter.mp hS).2; omega)
  have hparam : ∀ S : Finset ℕ, ∃ a d : ℕ, S ∈ B → 0 < d ∧ d ≤ N ∧ S = natAP a d S.card := by
    intro S
    by_cases hS : S ∈ B
    · have hsize := (Finset.mem_filter.mp hS).2
      obtain ⟨l,hl⟩ := hAP S (hBA hS)
      obtain ⟨a,d,hd,hrep⟩ := nat_ap_eq_natAP hl (by omega : 2 ≤ S.card)
      have hstep : a+d ∈ S := by
        have hh : a+d ∈ natAP a d S.card := mem_natAP.mpr ⟨1,by omega,by simp⟩
        simpa only [← hrep] using hh
      have hdN : d ≤ N := by
        have hh := (Finset.mem_Icc.mp (Finset.mem_powerset.mp (hF.1 (hAF (hBA hS))) hstep)).2
        omega
      exact ⟨a,d,fun _ => ⟨hd,hdN,hrep⟩⟩
    · exact ⟨0,1,fun hh => False.elim (hS hh)⟩
  choose a d hspec using hparam
  let b (S : Finset ℕ) := a S+(S.card-1)*d S
  let D := B.filter (fun S => a S = c)
  let Q := B.filter (fun S => ¬a S = c)
  let J := Q.filter (fun S => b S = L)
  let E := Q.filter (fun S => ¬b S = L)
  have hDB : D ⊆ B := Finset.filter_subset _ _
  have hQB : Q ⊆ B := Finset.filter_subset _ _
  have hJQ : J ⊆ Q := Finset.filter_subset _ _
  have hEQ : E ⊆ Q := Finset.filter_subset _ _
  have hJB : J ⊆ B := hJQ.trans hQB
  have hEB : E ⊆ B := hEQ.trans hQB
  have hD : (D.card : ℝ) ≤ (N : ℝ)*reciprocalSum N+N := by
    apply progression_fixed_endpoint_card_le true
      (fun S hS => Finset.mem_powerset.mp (hF.1 (hAF (hBA (hDB hS)))))
      (fun S hS => by have hh := (Finset.mem_filter.mp (hDB hS)).2; omega)
    intro S hS
    have hh := hspec S (hDB hS)
    exact ⟨a S,d S,hh.1,hh.2.1,hh.2.2,by simpa using (Finset.mem_filter.mp hS).2⟩
  have hJ : (J.card : ℝ) ≤ (N : ℝ)*reciprocalSum N+N := by
    apply progression_fixed_endpoint_card_le false
      (fun S hS => Finset.mem_powerset.mp (hF.1 (hAF (hBA (hJB hS)))))
      (fun S hS => by have hh := (Finset.mem_filter.mp (hJB hS)).2; omega)
    intro S hS
    have hh := hspec S (hJB hS)
    exact ⟨a S,d S,hh.1,hh.2.1,hh.2.2,by simpa only [Bool.false_eq_true,↓reduceIte]
      using (Finset.mem_filter.mp hS).2⟩
  have hpartA : (B.card : ℝ)+Small.card = A.card := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := A) (fun S => 4 ≤ S.card)
  have hpartB : (D.card : ℝ)+Q.card = B.card := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := B) (fun S => a S = c)
  have hpartQ : (J.card : ℝ)+E.card = Q.card := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := Q) (fun S => b S = L)
  have hsmallR : (Small.card : ℝ) ≤ 18*(N : ℝ)+3 := by exact_mod_cast hsmall
  refine ⟨E,hEB.trans hBA,by linarith only [hD,hJ,hpartA,hpartB,hpartQ,hsmallR],a,d,?_⟩
  intro S hS
  have hSB := hEB hS
  have hsize := (Finset.mem_filter.mp hSB).2
  have hSp := hspec S hSB
  refine ⟨hSp.1,hSp.2.1,hsize,hSp.2.2,?_,?_⟩
  · intro hcS
    have hac := (natAP_bounds_of_mem (hSp.2.2 ▸ hcS)).1
    have haNe := (Finset.mem_filter.mp (hEQ hS)).2
    obtain ⟨z,hz⟩ := arithInter_inter_nonempty hF (hAF (hBA hSB)) hP ⟨c,hcS⟩
    obtain ⟨hzS,hzP⟩ := Finset.mem_inter.mp hz
    have hzb := (natAP_bounds_of_mem (hSp.2.2 ▸ hzS)).2
    have hLz := hLP z hzP
    have hbNe := (Finset.mem_filter.mp hS).2
    dsimp only [b] at hbNe
    exact ⟨by omega,by omega⟩
  · intro hcS
    obtain ⟨⟨u,hu,huL⟩,v,hv,hRv⟩ := houtside S (hBA hSB) hcS
    have hau := (natAP_bounds_of_mem (hSp.2.2 ▸ hu)).1
    have hvb := (natAP_bounds_of_mem (hSp.2.2 ▸ hv)).2
    exact ⟨hau.trans huL,hRv.trans hvb⟩

end
/- OneSidedFiniteBound -/

/- The full finite one-sided estimate, including witness and endpoint preparation costs. -/

section
open Finset

theorem one_sided_family_finite_bound {N c L R : ℕ} {F : Finset (Finset ℕ)} {P T : Finset ℕ}
    (hN : 1 ≤ N) (hcL : c ≤ L) (hLR : L ≤ R) (hRN : R ≤ N)
    (hF : Erdos272.IsArithInterSet N F) (hc : ∀ S ∈ F, IsCrooked S → c ∈ S)
    (hP : P ∈ F) (hcP : c ∉ P) (hLP : ∀ x ∈ P, L ≤ x)
    (hT : T ∈ F) (hcT : c ∉ T) (hTR : ∀ x ∈ T, x ≤ R)
    (houtside : ∀ S ∈ F, c ∉ S → (∃ u ∈ S, u ≤ L) ∧ ∃ v ∈ S, R ≤ v) :
    (F.card : ℝ) ≤ (N : ℝ)^2/2-((L : ℝ)^2+((N : ℝ)-R)^2)/100+
      (40*reciprocalSum N+6)*N*reciprocalSum N+25*N+3+witnessExceptionBound N c := by
  classical
  let C := F.filter IsCrooked
  let A := F.filter (fun S => ¬IsCrooked S)
  have hCF : C ⊆ F := Finset.filter_subset _ _
  have hAF : A ⊆ F := Finset.filter_subset _ _
  have hcC : ∀ S ∈ C, c ∈ S := fun S hS => hc S (hCF hS) (Finset.mem_filter.mp hS).2
  have hC : ∀ S ∈ C, IsCrooked S := fun S hS => (Finset.mem_filter.mp hS).2
  have hA : ∀ S ∈ A, ∃ l : ℕ∞, (S : Set ℕ).IsAPOfLength l := by
    intro S hS
    exact of_not_not (Finset.mem_filter.mp hS).2
  obtain ⟨G,hGC,hCG,x,p,hW⟩ := prepare_one_sided_crooked hcL hLR hF hCF hcC hC
    hP hcP hLP hT hcT hTR
  obtain ⟨E,hEA,hAE,a,d,hE⟩ := prepare_one_sided_progressions hF hAF hA hP hLP
    (fun S hS hcS => houtside S (hAF hS) hcS)
  have hprepared := one_sided_prepared_card_le hN hcL hLR hRN hF (hGC.trans hCF) (hEA.trans hAF)
    (fun S hS => hcC S (hGC hS)) (fun S hS => hC S (hGC hS)) x p a d hW hE
  have hCGR : (C.card : ℝ) ≤ G.card+N+witnessExceptionBound N c := by exact_mod_cast hCG
  have hpart : (C.card : ℝ)+A.card = F.card := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := F) IsCrooked
  nlinarith only [hprepared,hCGR,hAE,hpart]

theorem one_sided_error_le_natLog {N c : ℕ} (hcI : c ∈ Finset.Icc 1 N) :
    (40*reciprocalSum N+6)*N*reciprocalSum N+25*N+3+witnessExceptionBound N c ≤
      512*(N : ℝ)*((Nat.log 2 N : ℝ)+1)^3 := by
  let J : ℝ := (Nat.log 2 N : ℝ)+1
  have hJ : 1 ≤ J := by
    dsimp only [J]
    have hh := Nat.cast_nonneg (α := ℝ) (Nat.log 2 N)
    linarith only [hh]
  have hJ0 : 0 ≤ J := by linarith only [hJ]
  have hH0 := reciprocalSum_nonneg N
  have hH : reciprocalSum N ≤ 2*J := reciprocalSum_le_natLog N
  have hNs : 1 ≤ N := (Finset.mem_Icc.mp hcI).1.trans (Finset.mem_Icc.mp hcI).2
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast hNs
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hJ2 : J ≤ J^2 := by nlinarith only [mul_nonneg hJ0 (sub_nonneg.mpr hJ)]
  have hJ3 : J^2 ≤ J^3 := by nlinarith only [mul_nonneg (sq_nonneg J) (sub_nonneg.mpr hJ)]
  have hJ13 : 1 ≤ J^3 := hJ.trans (hJ2.trans hJ3)
  have hHsq : (reciprocalSum N)^2 ≤ 4*J^3 := by
    have hh := (sq_le_sq₀ hH0 (by positivity : 0 ≤ 2*J)).mpr hH
    nlinarith only [hh,hJ3]
  have hH3 : reciprocalSum N ≤ 2*J^3 := by linarith only [hH,hJ2,hJ3]
  have hNH2 := mul_le_mul_of_nonneg_left hHsq hN0
  have hNH := mul_le_mul_of_nonneg_left hH3 hN0
  have hNsmall := mul_le_mul_of_nonneg_left hJ13 hN0
  have hW : (witnessExceptionBound N c : ℝ) ≤ 48*(N : ℝ)*J^3 := by
    dsimp only [J]
    exact_mod_cast witnessExceptionBound_le_natLog hcI
  change _ ≤ 512*(N : ℝ)*J^3
  nlinarith only [hNH2,hNH,hNsmall,hN,hW]

theorem one_sided_family_natLog_bound {N c L R : ℕ} {F : Finset (Finset ℕ)} {P T : Finset ℕ}
    (hcI : c ∈ Finset.Icc 1 N) (hcL : c ≤ L) (hLR : L ≤ R) (hRN : R ≤ N)
    (hF : Erdos272.IsArithInterSet N F) (hc : ∀ S ∈ F, IsCrooked S → c ∈ S)
    (hP : P ∈ F) (hcP : c ∉ P) (hLP : ∀ x ∈ P, L ≤ x)
    (hT : T ∈ F) (hcT : c ∉ T) (hTR : ∀ x ∈ T, x ≤ R)
    (houtside : ∀ S ∈ F, c ∉ S → (∃ u ∈ S, u ≤ L) ∧ ∃ v ∈ S, R ≤ v) :
    (F.card : ℝ) ≤ (N : ℝ)^2/2-((L : ℝ)^2+((N : ℝ)-R)^2)/100+
      512*(N : ℝ)*((Nat.log 2 N : ℝ)+1)^3 := by
  have hN : 1 ≤ N := (Finset.mem_Icc.mp hcI).1.trans (Finset.mem_Icc.mp hcI).2
  have hh := one_sided_family_finite_bound hN hcL hLR hRN hF hc hP hcP hLP hT hcT hTR houtside
  have herr := one_sided_error_le_natLog hcI
  linarith only [hh,herr]

end
/- OneSidedEndpointStability -/

/- Quantitative endpoint stability for near-extremal one-sided families. -/

section
open Finset Filter

theorem one_sided_endpoint_square_le {N c L R : ℕ} {F : Finset (Finset ℕ)} {P T : Finset ℕ}
    (hcI : c ∈ Finset.Icc 1 N) (hcL : c ≤ L) (hLR : L ≤ R) (hRN : R ≤ N)
    (hF : Erdos272.IsArithInterSet N F) (hc : ∀ S ∈ F, IsCrooked S → c ∈ S)
    (hlarge : (N : ℝ)^2/2 ≤ (F.card : ℝ)+2048*N)
    (hP : P ∈ F) (hcP : c ∉ P) (hLP : ∀ x ∈ P, L ≤ x)
    (hT : T ∈ F) (hcT : c ∉ T) (hTR : ∀ x ∈ T, x ≤ R)
    (houtside : ∀ S ∈ F, c ∉ S → (∃ u ∈ S, u ≤ L) ∧ ∃ v ∈ S, R ≤ v) :
    (L+N-R)^2 ≤ 512000*N*(Nat.log 2 N+1)^3 := by
  have hh := one_sided_family_natLog_bound hcI hcL hLR hRN hF hc hP hcP hLP hT hcT hTR houtside
  have hNlog : N ≤ N*(Nat.log 2 N+1)^3 := Nat.le_mul_of_pos_right N (by positivity)
  have hNlogR : (N : ℝ) ≤ (N : ℝ)*((Nat.log 2 N : ℝ)+1)^3 := by exact_mod_cast hNlog
  have hsquare : ((L : ℝ)+(N-R))^2 ≤ 512000*(N : ℝ)*((Nat.log 2 N : ℝ)+1)^3 := by
    nlinarith only [hh,hlarge,hNlogR,sq_nonneg ((L : ℝ)-((N : ℝ)-R))]
  have hsub : ((L+N-R : ℕ) : ℝ) = (L : ℝ)+(N-R) := by
    rw [Nat.cast_sub (by omega : R ≤ L+N),Nat.cast_add]
    ring
  have hcast : (((L+N-R)^2 : ℕ) : ℝ) ≤ ((512000*N*(Nat.log 2 N+1)^3 : ℕ) : ℝ) := by
    simpa only [Nat.cast_pow,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one,hsub] using hsquare
  exact_mod_cast hcast

theorem eventually_one_sided_endpoint_stability (K : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ (F : Finset (Finset ℕ)) (c L R : ℕ) (P T : Finset ℕ),
      c ∈ Finset.Icc 1 N → c ≤ L → L ≤ R → R ≤ N → Erdos272.IsArithInterSet N F →
      (∀ S ∈ F, IsCrooked S → c ∈ S) → (N : ℝ)^2/2 ≤ (F.card : ℝ)+2048*N →
      P ∈ F → c ∉ P → (∀ x ∈ P, L ≤ x) →
      T ∈ F → c ∉ T → (∀ x ∈ T, x ≤ R) →
      (∀ S ∈ F, c ∉ S → (∃ u ∈ S, u ≤ L) ∧ ∃ v ∈ S, R ≤ v) →
      K*(L+N-R)*(Nat.log 2 N+1) ≤ N := by
  filter_upwards [eventually_const_mul_natLog_pow_le (512000*K^2) 5]
    with N hlog F c L R P T hcI hcL hLR hRN hF hc hlarge hP hcP hLP hT hcT hTR houtside
  have hsquare := one_sided_endpoint_square_le hcI hcL hLR hRN hF hc hlarge
    hP hcP hLP hT hcT hTR houtside
  have hsq : (K*(L+N-R)*(Nat.log 2 N+1))^2 ≤ N^2 := by
    calc
      (K*(L+N-R)*(Nat.log 2 N+1))^2 = K^2*(Nat.log 2 N+1)^2*(L+N-R)^2 := by ring
      _ ≤ K^2*(Nat.log 2 N+1)^2*(512000*N*(Nat.log 2 N+1)^3) :=
        Nat.mul_le_mul_left _ hsquare
      _ = N*((512000*K^2)*(Nat.log 2 N+1)^5) := by ring
      _ ≤ N*N := Nat.mul_le_mul_left N hlog
      _ = N^2 := by ring
  exact (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp hsq

end
/- HalfSizeAvoider -/

/- A progression avoiding the root and having a nonunit step limits crooked members. -/

section
open Finset

theorem noninterval_card_two_le {S : Finset ℕ} (hno : ¬IsInterval S) : 2 ≤ S.card := by
  by_contra hn
  by_cases hne : S.Nonempty
  · have hcard : S.card = 1 := by have hh := Finset.card_pos.mpr hne; omega
    obtain ⟨a,ha⟩ := Finset.card_eq_one.mp hcard
    exact hno ⟨a,a,by simpa only [Finset.Icc_self] using ha⟩
  · have hS : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    exact hno ⟨1,0,by simpa using hS⟩

theorem noninterval_progression_card_le_half {N : ℕ} {S : Finset ℕ}
    (hsub : S ⊆ Finset.Icc 1 N) (hAP : ∃ l : ℕ∞, (S : Set ℕ).IsAPOfLength l)
    (hno : ¬IsInterval S) : (S.card : ℝ) ≤ (N : ℝ)/2+1 := by
  have hcard := noninterval_card_two_le hno
  obtain ⟨l,hl⟩ := hAP
  obtain ⟨a,d,hd,hrep⟩ := nat_ap_eq_natAP hl hcard
  have hd2 : 2 ≤ d := by
    by_contra hn
    have hd1 : d = 1 := by omega
    apply hno
    rw [hrep,hd1]
    exact natAP_step_one_isInterval _ _
  have hbS : a+(S.card-1)*d ∈ S := by
    have hh : a+(S.card-1)*d ∈ natAP a d S.card := mem_natAP.mpr ⟨S.card-1,by omega,rfl⟩
    simpa only [← hrep] using hh
  have hbN := (Finset.mem_Icc.mp (hsub hbS)).2
  have hmul := Nat.mul_le_mul_left (S.card-1) hd2
  have hsubadd : S.card-1+1 = S.card := by omega
  have hsize : 2*S.card ≤ N+2 := by nlinarith only [hmul,hbN,hsubadd]
  have hsizeR : 2*(S.card : ℝ) ≤ (N : ℝ)+2 := by exact_mod_cast hsize
  linarith only [hsizeR]

theorem meeting_half_set_pairs_card_le {N : ℕ} {P : Finset ℕ} (hN : 2 ≤ N)
    (hP : P ⊆ Finset.Icc 1 N) (hsize : (P.card : ℝ) ≤ (N : ℝ)/2+1) :
    ((((Finset.Icc 1 N).powersetCard 2).filter (fun Q => ¬Disjoint Q P)).card : ℝ) ≤
      3*(N : ℝ)^2/8+N := by
  let Q := Finset.Icc 1 N \ P
  have hpart : P.card+Q.card = N := by
    have hh := Finset.card_sdiff_add_card_eq_card hP
    rw [Nat.card_Icc,Nat.add_sub_cancel] at hh
    change Q.card+P.card = N at hh
    omega
  have hpartR : (P.card : ℝ)+Q.card = N := by exact_mod_cast hpart
  have hqN : (Q.card : ℝ) ≤ N := by have hh := Nat.cast_nonneg (α := ℝ) P.card; linarith only [hh,hpartR]
  have hq : (N : ℝ)/2-1 ≤ Q.card := by linarith only [hpartR,hsize]
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hqSq : ((N : ℝ)/2-1)^2 ≤ (Q.card : ℝ)^2 :=
    (sq_le_sq₀ (by linarith only [hN']) (Nat.cast_nonneg _)).mpr hq
  have hcount := card_meeting_pairs_add (Finset.Icc 1 N) P
  rw [Nat.card_Icc,Nat.add_sub_cancel] at hcount
  have hcountR : ((((Finset.Icc 1 N).powersetCard 2).filter (fun Q => ¬Disjoint Q P)).card : ℝ)+
      (Q.card.choose 2 : ℝ) = (N.choose 2 : ℝ) := by exact_mod_cast hcount
  rw [Nat.cast_choose_two,Nat.cast_choose_two] at hcountR
  nlinarith only [hcountR,hqSq,hqN,hN']

theorem crooked_with_half_size_avoider_card_le {N c : ℕ} {F C : Finset (Finset ℕ)} {P : Finset ℕ}
    (hN : 2 ≤ N) (hF : Erdos272.IsArithInterSet N F) (hCF : C ⊆ F)
    (hc : ∀ S ∈ C, c ∈ S) (hcrooked : ∀ S ∈ C, IsCrooked S)
    (hP : P ∈ F) (hcP : c ∉ P) (hsize : (P.card : ℝ) ≤ (N : ℝ)/2+1) :
    (C.card : ℝ) ≤ 3*(N : ℝ)^2/8+N+witnessExceptionBound N c := by
  classical
  let Good (S : Finset ℕ) := ∃ Q, IsWitnessPair S c Q ∧ ¬Disjoint Q P
  let G := C.filter Good
  let B := C.filter (fun S => ¬Good S)
  let Pool := ((Finset.Icc 1 N).powersetCard 2).filter (fun Q => ¬Disjoint Q P)
  have hGC : G ⊆ C := Finset.filter_subset _ _
  have hBC : B ⊆ C := Finset.filter_subset _ _
  have hB : B.card ≤ witnessExceptionBound N c := by
    apply restricted_witness_bad_family_card_le (admissible_subfamily hF (hBC.trans hCF))
      (fun S hS => hc S (hBC hS)) (fun S hS => hcrooked S (hBC hS))
    · intro S hS
      obtain ⟨z,hz⟩ := arithInter_inter_nonempty hF (hCF (hBC hS)) hP ⟨c,hc S (hBC hS)⟩
      obtain ⟨hzS,hzP⟩ := Finset.mem_inter.mp hz
      exact ⟨z,Finset.mem_inter.mpr ⟨Finset.mem_erase.mpr
        ⟨fun heq => hcP (heq ▸ hzP),hzS⟩,hzP⟩⟩
    · intro S hS Q hQ
      by_contra hn
      exact (Finset.mem_filter.mp hS).2 ⟨Q,hQ,hn⟩
  have hG : G.card ≤ Pool.card := by
    have hh := private_pairs_and_intervals_card_le (E := ∅) (Pool := Pool) hF (hGC.trans hCF)
      (Finset.empty_subset _) (fun S hS => hc S (hGC hS)) (fun S hS => hcrooked S (hGC hS))
      (by
        intro S hS
        obtain ⟨Q,hQ,hQP⟩ := (Finset.mem_filter.mp hS).2
        have hQS : Q ⊆ Finset.Icc 1 N := hQ.2.1.trans ((Finset.erase_subset _ _).trans
          (Finset.mem_powerset.mp (hF.1 (hCF (hGC hS)))))
        exact ⟨Q,hQ,Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr
          ⟨hQS,hQ.1⟩,hQP⟩⟩)
      (by intro S hS; simp only [Finset.notMem_empty] at hS)
    simpa only [Finset.card_empty,Nat.add_zero] using hh
  have hpool := meeting_half_set_pairs_card_le hN (Finset.mem_powerset.mp (hF.1 hP)) hsize
  have hGR : (G.card : ℝ) ≤ Pool.card := by exact_mod_cast hG
  have hBR : (B.card : ℝ) ≤ witnessExceptionBound N c := by exact_mod_cast hB
  have hpart : (G.card : ℝ)+B.card = C.card := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := C) Good
  linarith only [hGR,hBR,hpart,hpool]

end
/- LowStartProgressionCount -/

/- Counting progression families all of whose first endpoints are small. -/

section
open Finset

theorem large_progressions_starting_low_card_le {N L : ℕ} {F : Finset (Finset ℕ)}
    (hLN : L ≤ N) (hF : Erdos272.IsArithInterSet N F) (hcard : ∀ S ∈ F, 0 < S.card)
    (hparam : ∀ S ∈ F, ∃ a d : ℕ, 0 < d ∧ d ≤ N ∧ S = natAP a d S.card ∧ a ≤ L) :
    (F.card : ℝ) ≤ (5/3)*(L : ℝ)*N+2*N*reciprocalSum N+N := by
  classical
  have hp : ∀ S : Finset ℕ, ∃ a d : ℕ, S ∈ F → 0 < d ∧ d ≤ N ∧ S = natAP a d S.card ∧ a ≤ L := by
    intro S
    by_cases hS : S ∈ F
    · obtain ⟨a,d,hh⟩ := hparam S hS
      exact ⟨a,d,fun _ => hh⟩
    · exact ⟨0,1,fun hh => False.elim (hS hh)⟩
  choose a d hspec using hp
  let I := F.filter (fun S => d S = 1)
  let B := F.filter (fun S => ¬d S = 1)
  have hIF : I ⊆ F := Finset.filter_subset _ _
  have hBF : B ⊆ F := Finset.filter_subset _ _
  have hI : I.card ≤ L*N := by
    have hcover : I ⊆ ((Finset.Icc 1 L).product (Finset.Icc 1 N)).image
        (fun p : ℕ × ℕ => Finset.Icc p.1 p.2) := by
      intro S hS
      obtain ⟨hSF,hd1⟩ := Finset.mem_filter.mp hS
      obtain ⟨_hd,_hdN,hrep,haL⟩ := hspec S hSF
      have hinterval : S = Finset.Icc (a S) (a S+(S.card-1)) := by
        calc
          S = natAP (a S) (d S) S.card := hrep
          _ = _ := by rw [hd1,natAP_one_eq_Icc (hcard S hSF)]
      have hab : a S ≤ a S+(S.card-1) := Nat.le_add_right _ _
      have haS : a S ∈ S := by
        have hh : a S ∈ Finset.Icc (a S) (a S+(S.card-1)) := Finset.mem_Icc.mpr ⟨le_rfl,hab⟩
        simpa only [← hinterval] using hh
      have hbS : a S+(S.card-1) ∈ S := by
        have hh : a S+(S.card-1) ∈ Finset.Icc (a S) (a S+(S.card-1)) := Finset.mem_Icc.mpr ⟨hab,le_rfl⟩
        simpa only [← hinterval] using hh
      have ha1 := (Finset.mem_Icc.mp (Finset.mem_powerset.mp (hF.1 hSF) haS)).1
      have hbI := Finset.mem_powerset.mp (hF.1 hSF) hbS
      exact Finset.mem_image.mpr ⟨(a S,a S+(S.card-1)),Finset.mem_product.mpr
        ⟨Finset.mem_Icc.mpr ⟨ha1,haL⟩,hbI⟩,hinterval.symm⟩
    have hh := (Finset.card_le_card hcover).trans Finset.card_image_le
    simpa only [Finset.product_eq_sprod,Finset.card_product,Nat.card_Icc,Nat.add_sub_cancel] using hh
  have hB := large_step_endpoint_rectangle_card_le (R := 0) hLN (Nat.zero_le N)
    (admissible_subfamily hF hBF) (fun S hS => hcard S (hBF hS))
    (by
      intro S hS
      obtain ⟨hSF,hd1⟩ := Finset.mem_filter.mp hS
      obtain ⟨hd,hdN,hrep,haL⟩ := hspec S hSF
      exact ⟨a S,d S,by omega,hdN,hrep,haL,Nat.zero_le _⟩)
  have hIR : (I.card : ℝ) ≤ (L : ℝ)*N := by exact_mod_cast hI
  have hpart : (I.card : ℝ)+B.card = F.card := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := F) (fun S => d S = 1)
  norm_num only [Nat.cast_zero,sub_zero] at hB
  linarith only [hB,hIR,hpart]

theorem progressions_starting_low_card_le {N L : ℕ} {F : Finset (Finset ℕ)}
    (hLN : L ≤ N) (hF : Erdos272.IsArithInterSet N F)
    (hAP : ∀ S ∈ F, ∃ l : ℕ∞, (S : Set ℕ).IsAPOfLength l)
    (hlow : ∀ S ∈ F, ∃ u ∈ S, u ≤ L) :
    (F.card : ℝ) ≤ (5/3)*(L : ℝ)*N+2*N*reciprocalSum N+19*N+3 := by
  classical
  let A := F.filter (fun S => 4 ≤ S.card)
  let B := F.filter (fun S => ¬4 ≤ S.card)
  have hAF : A ⊆ F := Finset.filter_subset _ _
  have hBF : B ⊆ F := Finset.filter_subset _ _
  have hA := large_progressions_starting_low_card_le hLN (admissible_subfamily hF hAF)
    (fun S hS => by have hh := (Finset.mem_filter.mp hS).2; omega)
    (by
      intro S hS
      have hsize := (Finset.mem_filter.mp hS).2
      obtain ⟨l,hl⟩ := hAP S (hAF hS)
      obtain ⟨a,d,hd,hrep⟩ := nat_ap_eq_natAP hl (by omega : 2 ≤ S.card)
      have hstep : a+d ∈ S := by
        have hh : a+d ∈ natAP a d S.card := mem_natAP.mpr ⟨1,by omega,by simp⟩
        simpa only [← hrep] using hh
      have hdN : d ≤ N := by
        have hh := (Finset.mem_Icc.mp (Finset.mem_powerset.mp (hF.1 (hAF hS)) hstep)).2
        omega
      obtain ⟨u,hu,huL⟩ := hlow S (hAF hS)
      have hau := (natAP_bounds_of_mem (hrep ▸ hu)).1
      exact ⟨a,d,hd,hdN,hrep,hau.trans huL⟩)
  have hB := progression_family_small_card_le (admissible_subfamily hF hBF)
    (fun S hS => hAP S (hBF hS)) (fun S hS => by have hh := (Finset.mem_filter.mp hS).2; omega)
  have hBR : (B.card : ℝ) ≤ 18*(N : ℝ)+3 := by exact_mod_cast hB
  have hpart : (A.card : ℝ)+B.card = F.card := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := F) (fun S => 4 ≤ S.card)
  linarith only [hA,hBR,hpart]

end
/- LowStartIntervalReduction -/

/- Small first endpoints force avoiding progressions to be ordinary intervals. -/

section
open Finset Filter

theorem noninterval_avoider_low_start_finite_bound {N c L : ℕ} {F : Finset (Finset ℕ)}
    {P : Finset ℕ} (hN : 2 ≤ N) (hLN : L ≤ N) (hF : Erdos272.IsArithInterSet N F)
    (hc : ∀ S ∈ F, IsCrooked S → c ∈ S) (hlow : ∀ S ∈ F, ∃ u ∈ S, u ≤ L)
    (hP : P ∈ F) (hcP : c ∉ P) (hno : ¬IsInterval P) :
    (F.card : ℝ) ≤ 3*(N : ℝ)^2/8+(5/3)*(L : ℝ)*N+
      2*N*reciprocalSum N+20*N+3+witnessExceptionBound N c := by
  classical
  let C := F.filter IsCrooked
  let A := F.filter (fun S => ¬IsCrooked S)
  have hCF : C ⊆ F := Finset.filter_subset _ _
  have hAF : A ⊆ F := Finset.filter_subset _ _
  have hPAP : ∃ l : ℕ∞, (P : Set ℕ).IsAPOfLength l := by
    by_contra hn
    exact hcP (hc P hP hn)
  have hsize := noninterval_progression_card_le_half (Finset.mem_powerset.mp (hF.1 hP)) hPAP hno
  have hC := crooked_with_half_size_avoider_card_le hN hF hCF
    (fun S hS => hc S (hCF hS) (Finset.mem_filter.mp hS).2)
    (fun S hS => (Finset.mem_filter.mp hS).2) hP hcP hsize
  have hA := progressions_starting_low_card_le hLN (admissible_subfamily hF hAF)
    (fun S hS => of_not_not (Finset.mem_filter.mp hS).2) (fun S hS => hlow S (hAF hS))
  have hpart : (C.card : ℝ)+A.card = F.card := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := F) IsCrooked
  linarith only [hC,hA,hpart]

theorem eventually_low_start_interval_avoiders :
    ∀ᶠ N : ℕ in atTop, ∀ (F : Finset (Finset ℕ)) (c L : ℕ),
      c ∈ Finset.Icc 1 N → 256*L ≤ N → Erdos272.IsArithInterSet N F →
      (∀ S ∈ F, IsCrooked S → c ∈ S) → (∀ S ∈ F, ∃ u ∈ S, u ≤ L) →
      (N : ℝ)^2/2 ≤ (F.card : ℝ)+2048*N → ∀ P ∈ F, c ∉ P → IsInterval P := by
  filter_upwards [eventually_const_mul_natLog_pow_le 16384 3,Filter.eventually_ge_atTop 65536]
    with N hlog hN F c L hcI hsmall hF hc hlow hlarge P hP hcP
  by_contra hno
  have hLN : L ≤ N := by omega
  have hh := noninterval_avoider_low_start_finite_bound (by omega : 2 ≤ N) hLN hF hc hlow hP hcP hno
  have herr := one_sided_error_le_natLog hcI
  have hH := reciprocalSum_nonneg N
  have hN0 := Nat.cast_nonneg (α := ℝ) N
  have hNH := mul_nonneg hN0 hH
  have hNH2 := mul_nonneg hN0 (sq_nonneg (reciprocalSum N))
  have hbound : (F.card : ℝ) ≤ 3*(N : ℝ)^2/8+(5/3)*(L : ℝ)*N+
      512*(N : ℝ)*((Nat.log 2 N : ℝ)+1)^3 := by
    nlinarith only [hh,herr,hNH,hNH2,hN0]
  have hsmallR : 256*(L : ℝ) ≤ N := by exact_mod_cast hsmall
  have hsmallMul := mul_le_mul_of_nonneg_right hsmallR hN0
  have hlogR : 16384*((Nat.log 2 N : ℝ)+1)^3 ≤ (N : ℝ) := by exact_mod_cast hlog
  have hlogMul := mul_le_mul_of_nonneg_right hlogR hN0
  have hgap : (F.card : ℝ) ≤ 7*(N : ℝ)^2/16 := by
    nlinarith only [hbound,hsmallMul,hlogMul,sq_nonneg (N : ℝ)]
  have hNR : (65536 : ℝ) ≤ N := by exact_mod_cast hN
  have hNmul := mul_le_mul_of_nonneg_right hNR hN0
  nlinarith only [hgap,hlarge,hNR,hNmul]

end
/- StructuralReductionComplete -/

/- Completion of the structural reduction and the exact Szabo-strong target. -/

section
open Finset Filter

theorem eventually_structural_reduction :
    ∀ᶠ N : ℕ in atTop, ∀ F : Finset (Finset ℕ),
      Erdos272.IsArithInterSet N F → (N : ℝ)^2/2 ≤ (F.card : ℝ) →
      ∃ G : Finset (Finset ℕ), Erdos272.IsArithInterSet N G ∧
        F.card ≤ G.card+2048*N ∧ ReducedFamilyStructure N G := by
  classical
  filter_upwards [eventually_right_avoider_crooked_reduction,
    eventually_one_sided_endpoint_stability 256,eventually_low_start_interval_avoiders,
    Filter.eventually_ge_atTop 10000] with N hreduce hstable hinterval hN F hF hlarge
  obtain ⟨G,hG,hFG,c,hcI,hcG,hcase⟩ := hreduce F hF hlarge
  have hFGR : (F.card : ℝ) ≤ G.card+2048*N := by exact_mod_cast hFG
  have hlargeG : (N : ℝ)^2/2 ≤ (G.card : ℝ)+2048*N := hlarge.trans hFGR
  refine ⟨G,hG,hFG,?_⟩
  rcases hcase with hcommon | hright
  · exact Or.inl ⟨c,hcommon⟩
  · have hnonempty := admissible_member_nonempty_of_card_two_le hG (near_extremal_card_two_le hN hlargeG)
    obtain ⟨L,R,hcL,hLR,hRN,⟨P,hP,hcP,hLP⟩,⟨T,hT,hcT,hTR⟩,hend⟩ :=
      outside_member_envelope hG hnonempty hright
    have houtside : ∀ S ∈ G, c ∉ S → (∃ u ∈ S, u ≤ L) ∧ ∃ v ∈ S, R ≤ v := by
      intro S hS hcS
      obtain ⟨⟨u,hu,huL,_humin⟩,v,hv,hRv,_hvmax⟩ := hend S hS hcS
      exact ⟨⟨u,hu,huL⟩,v,hv,hRv⟩
    have hsmall := hstable G c L R P T hcI hcL.le hLR hRN hG hcG hlargeG
      hP hcP hLP hT hcT hTR houtside
    have hLsmall : 256*L ≤ N := by
      have hbase : 256*(L+N-R) ≤ 256*(L+N-R)*(Nat.log 2 N+1) :=
        Nat.le_mul_of_pos_right _ (by omega)
      exact (Nat.mul_le_mul_left 256 (show L ≤ L+N-R by omega)).trans (hbase.trans hsmall)
    have hlow : ∀ S ∈ G, ∃ u ∈ S, u ≤ L := by
      intro S hS
      by_cases hcS : c ∈ S
      · exact ⟨c,hcS,hcL.le⟩
      · exact (houtside S hS hcS).1
    have hallInterval := hinterval G c L hcI hLsmall hG hcG hlow hlargeG
    refine Or.inr ⟨c,L,R,hcL,hLR,hRN,hsmall,?_⟩
    intro S hS hcS
    obtain ⟨a,b,hrep⟩ := hallInterval S hS hcS
    obtain ⟨⟨u,hu,huL⟩,v,hv,hRv⟩ := houtside S hS hcS
    have huI := Finset.mem_Icc.mp (hrep ▸ hu)
    have hvI := Finset.mem_Icc.mp (hrep ▸ hv)
    have haL : a ≤ L := huI.1.trans huL
    have hRb : R ≤ b := hRv.trans hvI.2
    have hab : a ≤ b := haL.trans (hLR.trans hRb)
    have hca : c < a := by
      by_contra hn
      apply hcS
      rw [hrep]
      exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
    have hbS : b ∈ S := by rw [hrep]; exact Finset.mem_Icc.mpr ⟨hab,le_rfl⟩
    have hbN := (Finset.mem_Icc.mp (Finset.mem_powerset.mp (hG.1 hS) hbS)).2
    exact ⟨a,b,hca,haL,hRb,hbN,hrep⟩

theorem structural_reduction : StructuralReduction := by
  obtain ⟨N₀,hN₀⟩ := Filter.eventually_atTop.mp eventually_structural_reduction
  exact ⟨N₀,hN₀⟩

theorem target : fcTypeOfName% "Erdos272.erdos_272.variants.szabo_strong" := by
  exact target_of_structural_reduction structural_reduction

end
