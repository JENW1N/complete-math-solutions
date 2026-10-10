
open Finset Filter

theorem exact_target_type :
    (fcTypeOfName% "Erdos18.erdos_18b") =
      (True ↔ ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in Filter.atTop,
        (Erdos18.practicalH n.factorial : ℝ) < (n : ℝ) ^ ε) := by
  rfl

def HasShortDivisorSum (N R k : ℕ) : Prop :=
  ∃ D : Finset ℕ, D ⊆ N.divisors ∧ D.sum id = R ∧ D.card ≤ k

theorem short_sum_zero (N k : ℕ) : HasShortDivisorSum N 0 k := by
  refine ⟨∅, ?_, ?_, ?_⟩ <;> simp

theorem short_sum_mono_count {N R k l : ℕ}
    (h : HasShortDivisorSum N R k) (hkl : k ≤ l) :
    HasShortDivisorSum N R l := by
  obtain ⟨D, hD, hsum, hcard⟩ := h
  exact ⟨D, hD, hsum, hcard.trans hkl⟩

theorem short_sum_mono_host {N M R k : ℕ}
    (hNM : N ∣ M) (hM : M ≠ 0) (h : HasShortDivisorSum N R k) :
    HasShortDivisorSum M R k := by
  obtain ⟨D, hD, hsum, hcard⟩ := h
  exact ⟨D, hD.trans (Nat.divisors_subset_of_dvd hM hNM), hsum, hcard⟩

theorem practicalH_le_of_short_sums (N k : ℕ)
    (h : ∀ R ∈ Finset.Icc 1 N, HasShortDivisorSum N R k) :
    Erdos18.practicalH N ≤ k := by
  classical
  unfold Erdos18.practicalH
  apply Finset.sup_le
  intro R hR
  obtain ⟨D, hD, hsum, hcard⟩ := h R hR
  apply le_trans ?_ hcard
  apply Nat.sInf_le
  exact ⟨D, hD, rfl, D, Set.Subset.rfl, hsum.symm⟩

theorem short_sum_of_practicalH {N R : ℕ}
    (hN : Nat.IsPractical N) (hR : R ≤ N) :
    HasShortDivisorSum N R (Erdos18.practicalH N) := by
  classical
  by_cases hzero : R = 0
  · subst R
    exact short_sum_zero _ _
  have hRmem : R ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨by omega, hR⟩
  have hne : {k | ∃ D : Finset ℕ,
      D ⊆ N.divisors ∧ D.card = k ∧ R ∈ subsetSums D}.Nonempty :=
    ⟨N.divisors.card, N.divisors, Finset.Subset.refl _, rfl, hN R hR⟩
  obtain ⟨D, hD, hcard, E, hED, hsum⟩ := Nat.sInf_mem hne
  have hsub : E ⊆ D := Finset.coe_subset.mp hED
  refine ⟨E, hsub.trans hD, hsum.symm, ?_⟩
  calc
    E.card ≤ D.card := Finset.card_le_card hsub
    _ = sInf {k | ∃ D : Finset ℕ,
        D ⊆ N.divisors ∧ D.card = k ∧ R ∈ subsetSums D} := hcard
    _ ≤ Erdos18.practicalH N := by
      exact Finset.le_sup (f := fun m => sInf {k | ∃ D : Finset ℕ,
        D ⊆ N.divisors ∧ D.card = k ∧ m ∈ subsetSums D}) hRmem

theorem short_sum_radix {M q a r k l : ℕ}
    (hM : 0 < M) (hq : 0 < q) (hrq : r < q)
    (ha : HasShortDivisorSum M a k)
    (hr : HasShortDivisorSum (q * M) r l) :
    HasShortDivisorSum (q * M) (q * a + r) (k + l) := by
  classical
  obtain ⟨A, hA, hAsum, hAcard⟩ := ha
  obtain ⟨B, hB, hBsum, hBcard⟩ := hr
  have hinj : Function.Injective (fun d : ℕ => q * d) :=
    fun _ _ h => mul_left_cancel₀ (ne_of_gt hq) h
  have hdisj : Disjoint (A.image (fun d => q * d)) B := by
    apply Finset.disjoint_left.mpr
    intro x hx hxB
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos
      (Nat.dvd_of_mem_divisors (hA hd)) hM
    have hlow : q ≤ q * d := by nlinarith
    have hhigh : q * d ≤ r := by
      rw [← hBsum]
      exact Finset.single_le_sum (f := id) (fun _ _ => Nat.zero_le _) hxB
    omega
  refine ⟨A.image (fun d => q * d) ∪ B, ?_, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
      exact Nat.mem_divisors.mpr
        ⟨mul_dvd_mul_left q (Nat.dvd_of_mem_divisors (hA hd)),
          ne_of_gt (Nat.mul_pos hq hM)⟩
    · exact hB hx
  · rw [Finset.sum_union hdisj, Finset.sum_image
      (fun x _ y _ h => hinj h)]
    change (∑ x ∈ A, q * x) + B.sum id = q * a + r
    rw [← Finset.mul_sum, show (∑ x ∈ A, x) = a from hAsum, hBsum]
  · rw [Finset.card_union_of_disjoint hdisj,
      Finset.card_image_of_injective A hinj]
    omega

theorem practicalH_radix {M q l : ℕ}
    (hM : Nat.IsPractical M) (hMpos : 0 < M) (hq : 0 < q)
    (hlocal : ∀ r < q, HasShortDivisorSum (q * M) r l) :
    Erdos18.practicalH (q * M) ≤ Erdos18.practicalH M + l := by
  apply practicalH_le_of_short_sums
  intro R hR
  have hquot : R / q ≤ M :=
    Nat.div_le_of_le_mul (Finset.mem_Icc.mp hR).2
  have hrep := short_sum_radix hMpos hq (Nat.mod_lt R hq)
    (short_sum_of_practicalH hM hquot) (hlocal (R % q) (Nat.mod_lt R hq))
  simpa only [Nat.div_add_mod] using hrep

theorem factorial_radix_recurrence {n m l : ℕ} (hmn : m ≤ n)
    (hlocal : ∀ r < n.factorial / m.factorial,
      HasShortDivisorSum n.factorial r l) :
    Erdos18.practicalH n.factorial ≤ Erdos18.practicalH m.factorial + l := by
  have hdiv : m.factorial ∣ n.factorial := Nat.factorial_dvd_factorial hmn
  have heq : n.factorial / m.factorial * m.factorial = n.factorial :=
    Nat.div_mul_cancel hdiv
  have hq : 0 < n.factorial / m.factorial :=
    Nat.div_pos (Nat.le_of_dvd (Nat.factorial_pos n) hdiv) (Nat.factorial_pos m)
  have h := practicalH_radix (Erdos18.factorial_isPractical m)
    (Nat.factorial_pos m) hq (by simpa only [heq] using hlocal)
  simpa only [heq] using h

theorem positive_quotient_of_dvd {R S q : ℕ}
    (hq : 0 < q) (hSR : S < R) (hdvd : q ∣ R - S) :
    ∃ t : ℕ, 0 < t ∧ R = S + q * t ∧ t ≤ R / q := by
  refine ⟨(R - S) / q, ?_, ?_, ?_⟩
  · exact Nat.div_pos (Nat.le_of_dvd (Nat.sub_pos_of_lt hSR) hdvd) hq
  · rw [Nat.mul_div_cancel' hdvd]
    exact (Nat.add_sub_of_le hSR.le).symm
  · exact Nat.div_le_div_right (Nat.sub_le R S)

theorem polynomial_height_below_target {R S q D : ℕ}
    (hq : 2 ≤ q) (hR : q ^ (D + 1) ≤ R) (hS : S ≤ q ^ D) :
    S < R ∧ 2 * S ≤ R := by
  have hpow : 0 < q ^ D := pow_pos (by omega) D
  rw [pow_succ] at hR
  constructor <;> nlinarith

theorem positive_lifting_of_polynomial_height {R S q D : ℕ}
    (hq : 2 ≤ q) (hR : q ^ (D + 1) ≤ R) (hS : S ≤ q ^ D)
    (hdvd : q ∣ R - S) :
    ∃ t : ℕ, 0 < t ∧ R = S + q * t ∧ t ≤ R / q := by
  exact positive_quotient_of_dvd (by omega)
    (polynomial_height_below_target hq hR hS).1 hdvd

theorem positive_lifting_of_congruence {R S q D : ℕ}
    (hq : 2 ≤ q) (hR : q ^ (D + 1) ≤ R) (hS : S ≤ q ^ D)
    (hmod : Nat.ModEq q S R) :
    ∃ t : ℕ, 0 < t ∧ R = S + q * t ∧ t ≤ R / q := by
  exact positive_lifting_of_polynomial_height hq hR hS hmod.dvd'

theorem factorial_power_dvd (m r : ℕ) :
    m.factorial ^ r ∣ (r * m).factorial := by
  simpa using Nat.prod_factorial_dvd_factorial_sum (Finset.range r) (fun _ => m)

theorem factorial_binary_reserve (m k : ℕ) :
    2 ^ k * m.factorial ∣ (m + 2 * k).factorial := by
  have hpow : 2 ^ k ∣ (2 * k).factorial := by
    simpa [Nat.factorial, Nat.mul_comm] using factorial_power_dvd 2 k
  exact (mul_dvd_mul hpow (dvd_refl m.factorial)).trans
    (by simpa [Nat.add_comm] using
      Nat.factorial_mul_factorial_dvd_factorial_add (2 * k) m)

theorem shifted_divisor_dvd_factorial {m k b d : ℕ}
    (hd : d ∣ m.factorial) (hb : b ≤ k) :
    2 ^ b * d ∣ (m + 2 * k).factorial := by
  exact (mul_dvd_mul (pow_dvd_pow 2 hb) hd).trans (factorial_binary_reserve m k)

theorem product_divisors_dvd_factorial_sum {ι : Type*}
    (I : Finset ι) (d a : ι → ℕ)
    (h : ∀ i ∈ I, d i ∣ (a i).factorial) :
    (∏ i ∈ I, d i) ∣ (∑ i ∈ I, a i).factorial := by
  exact (Finset.prod_dvd_prod_of_dvd d (fun i => (a i).factorial) h).trans
    (Nat.prod_factorial_dvd_factorial_sum I a)

theorem distinctify_divisor_multiset (s : Multiset ℕ) {N : ℕ}
    (hN : N ≠ 0) (hs : ∀ d ∈ s, d ∣ N) :
    HasShortDivisorSum (2 ^ s.card * N) s.sum s.card := by
  classical
  have aux : ∀ k : ℕ, ∀ t : Multiset ℕ, t.card = k →
      ∀ M : ℕ, M ≠ 0 → (∀ d ∈ t, d ∣ M) →
      HasShortDivisorSum (2 ^ k * M) t.sum k := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro t hk M hM ht
      by_cases hn : t.Nodup
      · refine ⟨t.toFinset, ?_, ?_, ?_⟩
        · intro d hd
          exact Nat.mem_divisors.mpr
            ⟨dvd_mul_of_dvd_right (ht d (Multiset.mem_toFinset.mp hd)) (2 ^ k),
              mul_ne_zero (pow_ne_zero _ (by decide)) hM⟩
        · change (t.toFinset.val.map id).sum = t.sum
          simp [hn.dedup]
        · exact le_of_eq ((Multiset.toFinset_card_of_nodup hn).trans hk)
      · rw [Multiset.nodup_iff_ne_cons_cons] at hn
        push Not at hn
        obtain ⟨a, u, rfl⟩ := hn
        have hc : (2 * a ::ₘ u).card < k := by
          simp only [Multiset.card_cons] at hk ⊢
          omega
        have hnew : ∀ d ∈ (2 * a ::ₘ u), d ∣ 2 * M := by
          intro d hd
          rcases Multiset.mem_cons.mp hd with rfl | hd
          · exact mul_dvd_mul_left 2 (ht a (by simp))
          · exact dvd_mul_of_dvd_right (ht d (by simp [hd])) 2
        have hrep := ih _ hc (2 * a ::ₘ u) rfl (2 * M)
          (mul_ne_zero (by decide) hM) hnew
        have hhost : 2 ^ (2 * a ::ₘ u).card * (2 * M) = 2 ^ k * M := by
          rw [← hk]
          simp only [Multiset.card_cons, pow_succ]
          ring
        have hsum : (2 * a ::ₘ u).sum = (a ::ₘ a ::ₘ u).sum := by
          simp [two_mul, add_assoc]
        have hrep' := short_sum_mono_count hrep hc.le
        simpa only [hhost, hsum] using hrep'
  exact aux s.card s rfl N hN hs

theorem distinctify_factorial_divisors (s : Multiset ℕ) (F : ℕ)
    (hs : ∀ d ∈ s, d ∣ F.factorial) :
    HasShortDivisorSum (F + 2 * s.card).factorial s.sum s.card := by
  exact short_sum_mono_host (factorial_binary_reserve F s.card)
    (Nat.factorial_ne_zero _) (distinctify_divisor_multiset s (Nat.factorial_ne_zero F) hs)

def HasFactorialDivisorMultiset (F R u : ℕ) : Prop :=
  ∃ s : Multiset ℕ, (∀ d ∈ s, d ∣ F.factorial) ∧ s.sum = R ∧ s.card ≤ u

theorem factorial_multiset_zero (F u : ℕ) : HasFactorialDivisorMultiset F 0 u := by
  exact ⟨0, by simp, by simp, by simp⟩

theorem factorial_multiset_singleton {F R : ℕ} (hR : R ∣ F.factorial) :
    HasFactorialDivisorMultiset F R 1 := by
  exact ⟨{R}, by simpa using hR, by simp, by simp⟩

theorem factorial_multiset_mono {F G R u v : ℕ}
    (h : HasFactorialDivisorMultiset F R u) (hFG : F ≤ G) (huv : u ≤ v) :
    HasFactorialDivisorMultiset G R v := by
  obtain ⟨s, hs, hsum, hcard⟩ := h
  exact ⟨s, fun d hd => (hs d hd).trans (Nat.factorial_dvd_factorial hFG),
    hsum, hcard.trans huv⟩

theorem factorial_multiset_to_distinct {F R u : ℕ}
    (h : HasFactorialDivisorMultiset F R u) :
    HasShortDivisorSum (F + 2 * u).factorial R u := by
  obtain ⟨s, hs, hsum, hcard⟩ := h
  have hrep := distinctify_factorial_divisors s F hs
  rw [hsum] at hrep
  exact short_sum_mono_count
    (short_sum_mono_host (Nat.factorial_dvd_factorial (by omega))
      (Nat.factorial_ne_zero (F + 2 * u)) hrep) hcard

theorem factorial_multiset_add {F R S u v : ℕ}
    (hR : HasFactorialDivisorMultiset F R u)
    (hS : HasFactorialDivisorMultiset F S v) :
    HasFactorialDivisorMultiset F (R + S) (u + v) := by
  obtain ⟨s, hs, hsum, hcard⟩ := hR
  obtain ⟨t, ht, htsum, htcard⟩ := hS
  refine ⟨s + t, ?_, ?_, ?_⟩
  · intro d hd
    rcases Multiset.mem_add.mp hd with hd | hd
    · exact hs d hd
    · exact ht d hd
  · simp only [Multiset.sum_add, hsum, htsum]
  · simpa only [Multiset.card_add] using Nat.add_le_add hcard htcard

theorem factorial_multiset_scale {F G q R u : ℕ}
    (hq : q ∣ F.factorial) (h : HasFactorialDivisorMultiset G R u) :
    HasFactorialDivisorMultiset (F + G) (q * R) u := by
  obtain ⟨s, hs, hsum, hcard⟩ := h
  refine ⟨s.map (fun d => q * d), ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨d, hd, rfl⟩ := Multiset.mem_map.mp hx
    exact (mul_dvd_mul hq (hs d hd)).trans
      (Nat.factorial_mul_factorial_dvd_factorial_add F G)
  · have hmul := Multiset.sum_map_mul_left (s := s) (a := q) (f := id)
    simpa [hsum] using hmul
  · simpa only [Multiset.card_map] using hcard

theorem multiset_sum_expansion (s t : Multiset ℕ) :
    ((s ×ˢ t).map (fun p => p.1 * p.2)).sum = s.sum * t.sum := by
  refine Multiset.induction_on s (by simp) fun a s ih => ?_
  have hmul := Multiset.sum_map_mul_left (s := t) (a := a) (f := id)
  simp only [Multiset.cons_product, Multiset.map_add, Multiset.map_map,
    Multiset.sum_add, Multiset.sum_cons, ih]
  simpa [Function.comp_def, add_mul] using congrArg (fun x => x + s.sum * t.sum) hmul

theorem factorial_multiset_mul {F G R S u v : ℕ}
    (hR : HasFactorialDivisorMultiset F R u)
    (hS : HasFactorialDivisorMultiset G S v) :
    HasFactorialDivisorMultiset (F + G) (R * S) (u * v) := by
  obtain ⟨s, hs, hsum, hcard⟩ := hR
  obtain ⟨t, ht, htsum, htcard⟩ := hS
  refine ⟨(s ×ˢ t).map (fun p => p.1 * p.2), ?_, ?_, ?_⟩
  · intro d hd
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := Multiset.mem_map.mp hd
    obtain ⟨ha, hb⟩ := Multiset.mem_product.mp hab
    exact (mul_dvd_mul (hs a ha) (ht b hb)).trans
      (Nat.factorial_mul_factorial_dvd_factorial_add F G)
  · simp only [multiset_sum_expansion, hsum, htsum]
  · simpa only [Multiset.card_map, Multiset.card_product] using
      Nat.mul_le_mul hcard htcard

theorem factorial_multiset_lift {F G q R S T u v : ℕ}
    (hq : q ∣ F.factorial) (hR : R = S + q * T)
    (hS : HasFactorialDivisorMultiset F S u)
    (hT : HasFactorialDivisorMultiset G T v) :
    HasFactorialDivisorMultiset (F + G) R (u + v) := by
  rw [hR]
  exact factorial_multiset_add (factorial_multiset_mono hS (by omega) le_rfl)
    (factorial_multiset_scale hq hT)

def HasBoundedModularRepresentatives (q F u D : ℕ) : Prop :=
  ∀ R : ℕ, ∃ S : ℕ, S ≤ q ^ D ∧ Nat.ModEq q S R ∧
    HasFactorialDivisorMultiset F S u

theorem positive_modular_lifting_step {q F G u v D R : ℕ}
    (hq : 2 ≤ q) (hdiv : q ∣ F.factorial) (hR : q ^ (D + 1) ≤ R)
    (hmod : HasBoundedModularRepresentatives q F u D)
    (hchild : ∀ T : ℕ, 0 < T → T ≤ R / q → HasFactorialDivisorMultiset G T v) :
    HasFactorialDivisorMultiset (F + G) R (u + v) := by
  obtain ⟨S, hS, hcongr, hrep⟩ := hmod R
  obtain ⟨T, hTpos, hidentity, hTbound⟩ :=
    positive_lifting_of_congruence hq hR hS hcongr
  exact factorial_multiset_lift hdiv hidentity hrep (hchild T hTpos hTbound)

theorem positive_modular_lifting_step_distinct {q F G u v D R : ℕ}
    (hq : 2 ≤ q) (hdiv : q ∣ F.factorial) (hR : q ^ (D + 1) ≤ R)
    (hmod : HasBoundedModularRepresentatives q F u D)
    (hchild : ∀ T : ℕ, 0 < T → T ≤ R / q → HasFactorialDivisorMultiset G T v) :
    HasShortDivisorSum (F + G + 2 * (u + v)).factorial R (u + v) := by
  exact factorial_multiset_to_distinct
    (positive_modular_lifting_step hq hdiv hR hmod hchild)

theorem recursive_modular_lifting
    (indexBudget countBudget : ℕ → ℕ) (threshold : ℕ)
    (hbase : ∀ R < threshold,
      HasFactorialDivisorMultiset (indexBudget R) R (countBudget R))
    (hstep : ∀ R, threshold ≤ R → ∃ q F u D : ℕ,
      2 ≤ q ∧ q ∣ F.factorial ∧ q ^ (D + 1) ≤ R ∧
      HasBoundedModularRepresentatives q F u D ∧
      ∀ T : ℕ, 0 < T → T ≤ R / q →
        F + indexBudget T ≤ indexBudget R ∧
        u + countBudget T ≤ countBudget R) :
    ∀ R : ℕ, HasFactorialDivisorMultiset (indexBudget R) R (countBudget R) := by
  intro R
  induction R using Nat.strong_induction_on with
  | h R ih =>
    by_cases hsmall : R < threshold
    · exact hbase R hsmall
    obtain ⟨q, F, u, D, hq, hdiv, hheight, hmod, hbudget⟩ :=
      hstep R (by omega)
    obtain ⟨S, hS, hcongr, hrep⟩ := hmod R
    obtain ⟨T, hTpos, hidentity, hTbound⟩ :=
      positive_lifting_of_congruence hq hheight hS hcongr
    have hRpos : 0 < R := lt_of_lt_of_le (pow_pos (by omega) _) hheight
    have hTlt : T < R := hTbound.trans_lt (Nat.div_lt_self hRpos (by omega))
    have hchild := ih T hTlt
    obtain ⟨hF, hu⟩ := hbudget T hTpos hTbound
    exact factorial_multiset_mono
      (factorial_multiset_lift hdiv hidentity hrep hchild) hF hu

theorem bounded_recursive_modular_lifting
    (φ ψ : ℕ → ℝ) (threshold : ℕ) (C E A B ρ σ : ℝ)
    (hφ : ∀ R : ℕ, 0 < R → 1 ≤ φ R)
    (hψ : ∀ R : ℕ, 0 < R → 1 ≤ ψ R)
    (hC : (threshold : ℝ) ≤ C) (hCpos : 0 ≤ C)
    (hE : 1 ≤ E)
    (hindex : A + C * ρ ≤ C) (hcount : B + E * σ ≤ E)
    (hstep : ∀ R : ℕ, 0 < R → threshold ≤ R → ∃ q F u D : ℕ,
      2 ≤ q ∧ q ∣ F.factorial ∧ q ^ (D + 1) ≤ R ∧
      HasBoundedModularRepresentatives q F u D ∧
      (F : ℝ) ≤ A * φ R ∧ (u : ℝ) ≤ B * ψ R ∧
      ∀ T : ℕ, 0 < T → T ≤ R / q →
        φ T ≤ ρ * φ R ∧ ψ T ≤ σ * ψ R) :
    ∀ R : ℕ, 0 < R → ∃ F u : ℕ,
      HasFactorialDivisorMultiset F R u ∧
      (F : ℝ) ≤ C * φ R ∧ (u : ℝ) ≤ E * ψ R := by
  have hEpos : 0 ≤ E := by linarith
  intro R
  induction R using Nat.strong_induction_on with
  | h R ih =>
    intro hRpos
    by_cases hsmall : R < threshold
    · refine ⟨R, 1, factorial_multiset_singleton (Nat.dvd_factorial hRpos le_rfl), ?_, ?_⟩
      · have hRle : (R : ℝ) ≤ threshold := by exact_mod_cast hsmall.le
        have hprod : C ≤ C * φ R := by nlinarith [hφ R hRpos]
        exact hRle.trans (hC.trans hprod)
      · have hprod : E ≤ E * ψ R := by nlinarith [hψ R hRpos]
        simpa only [Nat.cast_one] using hE.trans hprod
    obtain ⟨q, F, u, D, hq, hdiv, hheight, hmod, hF, hu, hshrink⟩ :=
      hstep R hRpos (by omega)
    obtain ⟨S, hS, hcongr, hrep⟩ := hmod R
    obtain ⟨T, hTpos, hidentity, hTbound⟩ :=
      positive_lifting_of_congruence hq hheight hS hcongr
    have hTlt : T < R := hTbound.trans_lt (Nat.div_lt_self hRpos (by omega))
    obtain ⟨G, v, hchild, hG, hv⟩ := ih T hTlt hTpos
    obtain ⟨hφT, hψT⟩ := hshrink T hTpos hTbound
    refine ⟨F + G, u + v, factorial_multiset_lift hdiv hidentity hrep hchild, ?_, ?_⟩
    · calc
        ((F + G : ℕ) : ℝ) = (F : ℝ) + G := Nat.cast_add _ _
        _ ≤ A * φ R + C * φ T := add_le_add hF hG
        _ ≤ A * φ R + C * (ρ * φ R) := by gcongr
        _ = (A + C * ρ) * φ R := by ring
        _ ≤ C * φ R := mul_le_mul_of_nonneg_right hindex (by linarith [hφ R hRpos])
    · calc
        ((u + v : ℕ) : ℝ) = (u : ℝ) + v := Nat.cast_add _ _
        _ ≤ B * ψ R + E * ψ T := add_le_add hu hv
        _ ≤ B * ψ R + E * (σ * ψ R) := by gcongr
        _ = (B + E * σ) * ψ R := by ring
        _ ≤ E * ψ R := mul_le_mul_of_nonneg_right hcount (by linarith [hψ R hRpos])

def binaryLength (R : ℕ) : ℕ := Nat.log 2 R + 1

def liftingBits (R D : ℕ) : ℕ := Nat.log 2 R / (D + 1)

theorem binaryLength_pos (R : ℕ) : 0 < binaryLength R := by
  simp [binaryLength]

theorem lifting_modulus_height {R D : ℕ} (hR : 0 < R) :
    (2 ^ liftingBits R D) ^ (D + 1) ≤ R := by
  unfold liftingBits
  rw [← pow_mul]
  exact (Nat.pow_le_pow_right (by decide : 0 < 2)
    (Nat.div_mul_le_self (Nat.log 2 R) (D + 1))).trans
    (Nat.pow_log_le_self 2 hR.ne')

theorem liftingBits_pos {R D : ℕ} (hR : D + 1 ≤ Nat.log 2 R) :
    0 < liftingBits R D := by
  exact Nat.div_pos hR (by omega)

theorem lifting_modulus_ge_two {R D : ℕ} (hR : D + 1 ≤ Nat.log 2 R) :
    2 ≤ 2 ^ liftingBits R D := by
  simpa using Nat.pow_le_pow_right (by decide : 0 < 2) (liftingBits_pos hR)

theorem liftingBits_le_binaryLength (R D : ℕ) :
    liftingBits R D ≤ binaryLength R := by
  exact (Nat.div_le_self _ _).trans (Nat.le_succ _)

noncomputable def liftingRatio (D : ℕ) : ℝ := 1 - 1 / (2 * ((D : ℝ) + 1))

theorem liftingRatio_pos (D : ℕ) : 0 < liftingRatio D := by
  have hD : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  unfold liftingRatio
  have : 1 / (2 * ((D : ℝ) + 1)) < 1 :=
    (div_lt_one (by positivity)).mpr (by linarith)
  linarith

theorem liftingRatio_lt_one (D : ℕ) : liftingRatio D < 1 := by
  unfold liftingRatio
  have : 0 < 1 / (2 * ((D : ℝ) + 1)) := by positivity
  linarith

theorem binaryLength_quotient_shrink {R T D : ℕ}
    (hR : D + 1 ≤ Nat.log 2 R) (hT : T ≤ R / 2 ^ liftingBits R D) :
    (binaryLength T : ℝ) ≤ liftingRatio D * (binaryLength R : ℝ) := by
  have hkpos : 0 < liftingBits R D := liftingBits_pos hR
  have hk : liftingBits R D ≤ Nat.log 2 R := Nat.div_le_self _ _
  have hlog : Nat.log 2 T ≤ Nat.log 2 R - liftingBits R D := by
    calc
      Nat.log 2 T ≤ Nat.log 2 (R / 2 ^ liftingBits R D) := Nat.log_mono_right hT
      _ = Nat.log 2 R - liftingBits R D := Nat.log_div_base_pow 2 R _
  have hsplit : Nat.log 2 T + liftingBits R D ≤ Nat.log 2 R := by omega
  have hdiv : Nat.log 2 R < (D + 1) * (liftingBits R D + 1) :=
    Nat.lt_mul_div_succ _ (by omega)
  have hgap : binaryLength R ≤ 2 * (D + 1) * liftingBits R D := by
    unfold binaryLength
    nlinarith
  have hsplitR : (binaryLength T : ℝ) + (liftingBits R D : ℝ) ≤ binaryLength R := by
    exact_mod_cast (show binaryLength T + liftingBits R D ≤ binaryLength R by
      unfold binaryLength
      omega)
  have hgapR : (binaryLength R : ℝ) ≤
      (2 * ((D : ℝ) + 1)) * (liftingBits R D : ℝ) := by exact_mod_cast hgap
  have hden : (0 : ℝ) < 2 * ((D : ℝ) + 1) := by positivity
  have hquot : (binaryLength R : ℝ) / (2 * ((D : ℝ) + 1)) ≤ liftingBits R D :=
    (div_le_iff₀ hden).mpr (by nlinarith [hgapR])
  unfold liftingRatio
  have hid : (1 - 1 / (2 * ((D : ℝ) + 1))) * (binaryLength R : ℝ) =
      (binaryLength R : ℝ) - (binaryLength R : ℝ) / (2 * ((D : ℝ) + 1)) := by ring
  rw [hid]
  linarith

theorem binaryLength_rpow_quotient_shrink {R T D : ℕ} {a : ℝ}
    (ha : 0 ≤ a) (hR : D + 1 ≤ Nat.log 2 R)
    (hT : T ≤ R / 2 ^ liftingBits R D) :
    (binaryLength T : ℝ) ^ a ≤ liftingRatio D ^ a * (binaryLength R : ℝ) ^ a := by
  have h := Real.rpow_le_rpow (Nat.cast_nonneg (binaryLength T))
    (binaryLength_quotient_shrink hR hT) ha
  simpa only [Real.mul_rpow (liftingRatio_pos D).le (Nat.cast_nonneg _)] using h

def DyadicModularBounds (a b : ℝ) : Prop :=
  ∃ D k₀ : ℕ, ∃ A B : ℝ, 0 < A ∧ 0 < B ∧
    ∀ k : ℕ, k₀ ≤ k → ∃ F u : ℕ,
      2 ^ k ∣ F.factorial ∧ HasBoundedModularRepresentatives (2 ^ k) F u D ∧
      (F : ℝ) ≤ A * (k : ℝ) ^ a ∧ (u : ℝ) ≤ B * (k : ℝ) ^ b

theorem dyadic_modular_bounds_give_local_multisets {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (h : DyadicModularBounds a b) :
    ∃ C E : ℝ, 0 < C ∧ 0 < E ∧ ∀ R : ℕ, 0 < R → ∃ F u : ℕ,
      HasFactorialDivisorMultiset F R u ∧
      (F : ℝ) ≤ C * (binaryLength R : ℝ) ^ a ∧
      (u : ℝ) ≤ E * (binaryLength R : ℝ) ^ b := by
  obtain ⟨D, k₀, A, B, hA, hB, hmod⟩ := h
  let threshold : ℕ := 2 ^ ((D + 1) * (k₀ + 1))
  let ρ : ℝ := liftingRatio D ^ a
  let σ : ℝ := liftingRatio D ^ b
  have hρ : ρ < 1 := Real.rpow_lt_one (liftingRatio_pos D).le (liftingRatio_lt_one D) ha
  have hσ : σ < 1 := Real.rpow_lt_one (liftingRatio_pos D).le (liftingRatio_lt_one D) hb
  let C : ℝ := max (threshold : ℝ) (A / (1 - ρ))
  let E : ℝ := max 1 (B / (1 - σ))
  have hC : (threshold : ℝ) ≤ C := le_max_left _ _
  have hE : 1 ≤ E := le_max_left _ _
  have hCA : A / (1 - ρ) ≤ C := le_max_right _ _
  have hEB : B / (1 - σ) ≤ E := le_max_right _ _
  have hCpos : 0 < C := (div_pos hA (by linarith)).trans_le hCA
  have hEpos : 0 < E := lt_of_lt_of_le zero_lt_one hE
  have hindex : A + C * ρ ≤ C := by
    have := (div_le_iff₀ (by linarith : 0 < 1 - ρ)).mp hCA
    nlinarith
  have hcount : B + E * σ ≤ E := by
    have := (div_le_iff₀ (by linarith : 0 < 1 - σ)).mp hEB
    nlinarith
  refine ⟨C, E, hCpos, hEpos, ?_⟩
  refine bounded_recursive_modular_lifting
    (fun R => (binaryLength R : ℝ) ^ a) (fun R => (binaryLength R : ℝ) ^ b)
    threshold C E A B ρ σ
    (fun R _ => Real.one_le_rpow (by exact_mod_cast binaryLength_pos R) ha.le)
    (fun R _ => Real.one_le_rpow (by exact_mod_cast binaryLength_pos R) hb.le)
    hC hCpos.le hE hindex hcount ?_
  intro R hR hlarge
  have hlog : (D + 1) * (k₀ + 1) ≤ Nat.log 2 R :=
    (Nat.le_log_iff_pow_le (by decide : 1 < 2) hR.ne').mpr hlarge
  have hD : D + 1 ≤ Nat.log 2 R := by nlinarith
  have hk₀ : k₀ ≤ liftingBits R D := by
    apply (Nat.le_div_iff_mul_le (by omega : 0 < D + 1)).mpr
    nlinarith
  obtain ⟨F, u, hdiv, hrep, hF, hu⟩ := hmod (liftingBits R D) hk₀
  refine ⟨2 ^ liftingBits R D, F, u, D, lifting_modulus_ge_two hD, hdiv,
    lifting_modulus_height hR, hrep, ?_, ?_, ?_⟩
  · exact hF.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast liftingBits_le_binaryLength R D)
        ha.le) hA.le)
  · exact hu.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast liftingBits_le_binaryLength R D)
        hb.le) hB.le)
  · intro T _ hT
    exact ⟨binaryLength_rpow_quotient_shrink ha.le hD hT,
      binaryLength_rpow_quotient_shrink hb.le hD hT⟩

def LocalFactorialBounds (a b : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ R : ℕ, 0 < R → ∃ F u : ℕ,
    HasShortDivisorSum F.factorial R u ∧
    (F : ℝ) ≤ C * (binaryLength R : ℝ) ^ a ∧
    (u : ℝ) ≤ C * (binaryLength R : ℝ) ^ b

theorem dyadic_modular_bounds_give_local_bounds {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a) (h : DyadicModularBounds a b) :
    LocalFactorialBounds a b := by
  obtain ⟨C, E, hC, hE, hlocal⟩ := dyadic_modular_bounds_give_local_multisets ha hb h
  refine ⟨C + 2 * E, by linarith, ?_⟩
  intro R hR
  obtain ⟨F, u, hrep, hF, hu⟩ := hlocal R hR
  refine ⟨F + 2 * u, u, factorial_multiset_to_distinct hrep, ?_, ?_⟩
  · have hpow : (binaryLength R : ℝ) ^ b ≤ (binaryLength R : ℝ) ^ a :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast binaryLength_pos R) hba
    have htwice := mul_le_mul_of_nonneg_left hpow (by linarith : 0 ≤ 2 * E)
    push_cast
    nlinarith
  · have hpow : 0 ≤ (binaryLength R : ℝ) ^ b := Real.rpow_nonneg (by positivity) _
    nlinarith

theorem binaryLength_mono {R S : ℕ} (h : R ≤ S) : binaryLength R ≤ binaryLength S := by
  exact Nat.add_le_add_right (Nat.log_mono_right h) 1

theorem local_bounds_uniform_remainders {a b C : ℝ} {n Q : ℕ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hC : 0 ≤ C)
    (hlocal : ∀ R : ℕ, 0 < R → ∃ F u : ℕ,
      HasShortDivisorSum F.factorial R u ∧
      (F : ℝ) ≤ C * (binaryLength R : ℝ) ^ a ∧
      (u : ℝ) ≤ C * (binaryLength R : ℝ) ^ b)
    (hhost : C * (binaryLength Q : ℝ) ^ a ≤ n) :
    ∀ R < Q, HasShortDivisorSum n.factorial R ⌊C * (binaryLength Q : ℝ) ^ b⌋₊ := by
  intro R hRQ
  by_cases hzero : R = 0
  · subst R
    exact short_sum_zero _ _
  obtain ⟨F, u, hrep, hF, hu⟩ := hlocal R (by omega)
  have hlen : (binaryLength R : ℝ) ≤ binaryLength Q := by
    exact_mod_cast binaryLength_mono hRQ.le
  have hF' : (F : ℝ) ≤ n := hF.trans
    ((mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) hlen ha) hC).trans hhost)
  have hu' : (u : ℝ) ≤ C * (binaryLength Q : ℝ) ^ b := hu.trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) hlen hb) hC)
  exact short_sum_mono_count
    (short_sum_mono_host (Nat.factorial_dvd_factorial (by exact_mod_cast hF'))
      (Nat.factorial_ne_zero n) hrep) (Nat.le_floor hu')

theorem local_bounds_radix_recurrence {a b C : ℝ} {n m : ℕ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hC : 0 ≤ C) (hmn : m ≤ n)
    (hlocal : ∀ R : ℕ, 0 < R → ∃ F u : ℕ,
      HasShortDivisorSum F.factorial R u ∧
      (F : ℝ) ≤ C * (binaryLength R : ℝ) ^ a ∧
      (u : ℝ) ≤ C * (binaryLength R : ℝ) ^ b)
    (hhost : C * (binaryLength (n.factorial / m.factorial) : ℝ) ^ a ≤ n) :
    Erdos18.practicalH n.factorial ≤ Erdos18.practicalH m.factorial +
      ⌊C * (binaryLength (n.factorial / m.factorial) : ℝ) ^ b⌋₊ := by
  exact factorial_radix_recurrence hmn (local_bounds_uniform_remainders ha hb hC hlocal hhost)

theorem binaryLength_le_of_le_pow {R w : ℕ} (h : R ≤ 2 ^ w) :
    binaryLength R ≤ w + 1 := by
  have hlog := Nat.log_mono_right h (b := 2)
  rw [Nat.log_pow (by decide : 1 < 2)] at hlog
  exact Nat.add_le_add_right hlog 1

theorem binaryLength_pow_le (n w : ℕ) : binaryLength (n ^ w) ≤ w * binaryLength n + 1 := by
  apply binaryLength_le_of_le_pow
  calc
    n ^ w ≤ (2 ^ binaryLength n) ^ w :=
      Nat.pow_le_pow_left (Nat.lt_pow_succ_log_self (by decide : 1 < 2) n).le w
    _ = 2 ^ (w * binaryLength n) := by rw [← pow_mul, Nat.mul_comm]

theorem factorial_quotient_le_pow {n w : ℕ} (hw : w ≤ n) :
    n.factorial / (n - w).factorial ≤ n ^ w := by
  rw [← Nat.descFactorial_eq_div hw]
  exact Nat.descFactorial_le_pow n w

theorem binaryLength_factorial_quotient_le {n w : ℕ} (hw : w ≤ n) :
    binaryLength (n.factorial / (n - w).factorial) ≤ w * binaryLength n + 1 := by
  exact (binaryLength_mono (factorial_quotient_le_pow hw)).trans (binaryLength_pow_le n w)

theorem rpow_difference_lower_bound {x y p : ℝ}
    (hx : 0 < x) (hy : 0 ≤ y) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    p * (x - y) * x ^ (p - 1) ≤ x ^ p - y ^ p := by
  have hB := rpow_one_add_le_one_add_mul_self
    (s := y / x - 1) (by have := div_nonneg hy hx.le; linarith) hp hp1
  have hB' : y ^ p / x ^ p ≤ 1 + p * (y / x - 1) := by
    simpa only [show 1 + (y / x - 1) = y / x by ring,
      Real.div_rpow hy hx.le] using hB
  have hpX : 0 < x ^ p := Real.rpow_pos_of_pos hx p
  have hmul := (div_le_iff₀ hpX).mp hB'
  have hid : (1 + p * (y / x - 1)) * x ^ p =
      x ^ p - p * (x - y) * x ^ (p - 1) := by
    rw [Real.rpow_sub hx, Real.rpow_one]
    field_simp
    ring
  rw [hid] at hmul
  linarith

theorem eventually_const_mul_rpow_le {a b C E : ℝ} (hab : a < b) (hE : 0 < E) :
    ∀ᶠ n : ℕ in Filter.atTop, C * (n : ℝ) ^ a ≤ E * (n : ℝ) ^ b := by
  have h := (tendsto_rpow_atTop (sub_pos.mpr hab)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [h.eventually_ge_atTop (C / E), eventually_ge_atTop (1 : ℕ)] with n hn hn1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hC : C ≤ E * (n : ℝ) ^ (b - a) := by
    change C / E ≤ (n : ℝ) ^ (b - a) at hn
    simpa only [mul_comm] using (div_le_iff₀ hE).mp hn
  calc
    C * (n : ℝ) ^ a ≤ (E * (n : ℝ) ^ (b - a)) * (n : ℝ) ^ a :=
      mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg (Nat.cast_nonneg n) a)
    _ = E * (n : ℝ) ^ b := by
      rw [mul_assoc, ← Real.rpow_add hnpos, sub_add_cancel]

theorem eventually_binaryLength_le_rpow {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop, (binaryLength n : ℝ) ≤ (n : ℝ) ^ ε := by
  have hlog := ((isLittleO_log_rpow_atTop hε).const_mul_left (1 / Real.log 2)).comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hconst := eventually_const_mul_rpow_le (C := 1) (E := 1 / 2) hε (by norm_num)
  filter_upwards [hlog.def (by norm_num : (0 : ℝ) < 1 / 2), hconst] with n hn hc
  have hl : (Nat.log 2 n : ℝ) ≤ (1 / Real.log 2) * Real.log (n : ℝ) := by
    simpa only [Real.logb, Nat.cast_ofNat, div_eq_mul_inv, one_mul, mul_comm]
      using Real.natLog_le_logb n 2
  have hn' : (1 / Real.log 2) * Real.log (n : ℝ) ≤ (1 / 2) * (n : ℝ) ^ ε := by
    have habs : |(1 / Real.log 2) * Real.log (n : ℝ)| ≤ (1 / 2) * (n : ℝ) ^ ε := by
      simpa only [Function.comp_apply, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) ε)] using hn
    exact (le_abs_self _).trans habs
  have hc' : 1 ≤ (1 / 2) * (n : ℝ) ^ ε := by simpa using hc
  change ((Nat.log 2 n + 1 : ℕ) : ℝ) ≤ (n : ℝ) ^ ε
  rw [Nat.cast_add, Nat.cast_one]
  calc
    (Nat.log 2 n : ℝ) + 1 ≤ (1 / 2) * (n : ℝ) ^ ε + (1 / 2) * (n : ℝ) ^ ε :=
      add_le_add (hl.trans hn') hc'
    _ = (n : ℝ) ^ ε := by ring

noncomputable def radixWidth (n : ℕ) (θ : ℝ) : ℕ := ⌊(n : ℝ) ^ θ⌋₊

theorem eventually_radix_width_bounds {θ γ : ℝ}
    (hθ : 0 < θ) (hθ1 : θ < 1) (hγ : 0 < γ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      0 < radixWidth n θ ∧ radixWidth n θ < n ∧
      (n : ℝ) ^ θ / 2 ≤ (radixWidth n θ : ℝ) ∧
      (binaryLength (n.factorial / (n - radixWidth n θ).factorial) : ℝ) ≤
        2 * (n : ℝ) ^ (θ + γ) := by
  have hlarge := ((tendsto_rpow_atTop hθ).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 2
  have hsmall := eventually_const_mul_rpow_le (C := 1) (E := 1 / 2) hθ1 (by norm_num)
  filter_upwards [hlarge, hsmall, eventually_binaryLength_le_rpow hγ,
    eventually_ge_atTop (1 : ℕ)] with n hlarge hsmall hlen hn1
  change (2 : ℝ) ≤ (n : ℝ) ^ θ at hlarge
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hfloor : (radixWidth n θ : ℝ) ≤ (n : ℝ) ^ θ :=
    Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg n) θ)
  have hfloorlt : (n : ℝ) ^ θ < (radixWidth n θ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hwpos : 0 < radixWidth n θ := by
    apply Nat.le_floor
    norm_num only [Nat.cast_succ, Nat.cast_zero, zero_add]
    exact (by norm_num : (1 : ℝ) ≤ 2).trans hlarge
  have hwlt : radixWidth n θ < n := by
    have hsmall' : (n : ℝ) ^ θ ≤ (n : ℝ) / 2 := by
      simpa [div_eq_mul_inv, mul_comm] using hsmall
    exact_mod_cast hfloor.trans_lt (hsmall'.trans_lt (half_lt_self hnpos))
  refine ⟨hwpos, hwlt, by linarith only [hlarge, hfloorlt], ?_⟩
  have hlenQ : (binaryLength (n.factorial / (n - radixWidth n θ).factorial) : ℝ) ≤
      (radixWidth n θ : ℝ) * (binaryLength n : ℝ) + 1 := by
    exact_mod_cast binaryLength_factorial_quotient_le hwlt.le
  have hprod := mul_le_mul hfloor hlen (Nat.cast_nonneg (binaryLength n))
    (Real.rpow_nonneg (Nat.cast_nonneg n) θ)
  have hpowone : 1 ≤ (n : ℝ) ^ (θ + γ) :=
    Real.one_le_rpow (by exact_mod_cast hn1) (by linarith)
  rw [← Real.rpow_add hnpos] at hprod
  calc
    (binaryLength (n.factorial / (n - radixWidth n θ).factorial) : ℝ) ≤
        (radixWidth n θ : ℝ) * (binaryLength n : ℝ) + 1 := hlenQ
    _ ≤ (n : ℝ) ^ (θ + γ) + 1 := add_le_add hprod (le_refl (1 : ℝ))
    _ ≤ 2 * (n : ℝ) ^ (θ + γ) := by linarith only [hpowone]

theorem bounded_of_eventual_potential_decrease (f P : ℕ → ℝ)
    (hP : ∀ n : ℕ, 0 ≤ P n)
    (hstep : ∀ᶠ n : ℕ in Filter.atTop, ∃ m : ℕ, m < n ∧
      f n ≤ f m + P n - P m) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, f n ≤ K + P n := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hstep
  let K : ℝ := ∑ i ∈ Finset.range N, max 0 (f i)
  refine ⟨K, Finset.sum_nonneg (fun _ _ => le_max_left _ _), ?_⟩
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < N
    · have hf : f n ≤ K := (le_max_right 0 (f n)).trans
        (Finset.single_le_sum (f := fun i => max 0 (f i))
          (fun _ _ => le_max_left _ _) (Finset.mem_range.mpr hn))
      linarith [hP n]
    · obtain ⟨m, hmn, hfm⟩ := hN n (by omega)
      linarith [ih m hmn]

theorem eventual_factorial_potential_decrease {a b p θ γ C : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hp : 0 < p) (hp1 : p ≤ 1)
    (hθ : 0 < θ) (hθ1 : θ < 1) (hγ : 0 < γ) (hC : 0 ≤ C)
    (hindex : (θ + γ) * a < 1) (hcount : (θ + γ) * b < θ + p - 1)
    (hlocal : ∀ R : ℕ, 0 < R → ∃ F u : ℕ,
      HasShortDivisorSum F.factorial R u ∧
      (F : ℝ) ≤ C * (binaryLength R : ℝ) ^ a ∧
      (u : ℝ) ≤ C * (binaryLength R : ℝ) ^ b) :
    ∀ᶠ n : ℕ in Filter.atTop, ∃ m : ℕ, m < n ∧
      (Erdos18.practicalH n.factorial : ℝ) ≤
        (Erdos18.practicalH m.factorial : ℝ) + (n : ℝ) ^ p - (m : ℝ) ^ p := by
  have hhost := eventually_const_mul_rpow_le (C := C * (2 : ℝ) ^ a) (E := 1)
    hindex zero_lt_one
  have hcost := eventually_const_mul_rpow_le (C := C * (2 : ℝ) ^ b) (E := p / 2)
    hcount (half_pos hp)
  filter_upwards [eventually_radix_width_bounds hθ hθ1 hγ, hhost, hcost,
    eventually_ge_atTop (1 : ℕ)] with n hw hhost hcost hn1
  obtain ⟨hwpos, hwlt, hwhalf, hlen⟩ := hw
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  let m := n - radixWidth n θ
  let Q := n.factorial / m.factorial
  have hpow (t : ℝ) (ht : 0 ≤ t) :
      C * (binaryLength Q : ℝ) ^ t ≤
        (C * (2 : ℝ) ^ t) * (n : ℝ) ^ ((θ + γ) * t) := by
    calc
      C * (binaryLength Q : ℝ) ^ t ≤ C * (2 * (n : ℝ) ^ (θ + γ)) ^ t :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) hlen ht) hC
      _ = (C * (2 : ℝ) ^ t) * (n : ℝ) ^ ((θ + γ) * t) := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2)
          (Real.rpow_nonneg (Nat.cast_nonneg n) _), ← Real.rpow_mul (Nat.cast_nonneg n)]
        ring
  have hhost' : C * (binaryLength Q : ℝ) ^ a ≤ n :=
    (hpow a ha).trans (by simpa only [Real.rpow_one, one_mul] using hhost)
  have hrec := local_bounds_radix_recurrence ha hb hC (Nat.sub_le n (radixWidth n θ))
    hlocal hhost'
  have hcost' : (⌊C * (binaryLength Q : ℝ) ^ b⌋₊ : ℝ) ≤
      (p / 2) * (n : ℝ) ^ (θ + p - 1) :=
    (Nat.floor_le (mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg _) b))).trans
      ((hpow b hb).trans hcost)
  have hdiff := rpow_difference_lower_bound hnpos (Nat.cast_nonneg m) hp.le hp1
  have hnm : (n : ℝ) - (m : ℝ) = (radixWidth n θ : ℝ) := by
    dsimp [m]
    rw [Nat.cast_sub hwlt.le]
    ring
  rw [hnm] at hdiff
  have hpoweq : (n : ℝ) ^ θ * (n : ℝ) ^ (p - 1) = (n : ℝ) ^ (θ + p - 1) := by
    rw [← Real.rpow_add hnpos]
    congr 1
    ring
  have hgap : (p / 2) * (n : ℝ) ^ (θ + p - 1) ≤
      (n : ℝ) ^ p - (m : ℝ) ^ p := by
    calc
      (p / 2) * (n : ℝ) ^ (θ + p - 1) =
          (p * ((n : ℝ) ^ θ / 2)) * (n : ℝ) ^ (p - 1) := by rw [← hpoweq]; ring
      _ ≤ (p * (radixWidth n θ : ℝ)) * (n : ℝ) ^ (p - 1) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hwhalf hp.le)
          (Real.rpow_nonneg (Nat.cast_nonneg n) _)
      _ ≤ (n : ℝ) ^ p - (m : ℝ) ^ p := hdiff
  have hrec' : (Erdos18.practicalH n.factorial : ℝ) ≤
      (Erdos18.practicalH m.factorial : ℝ) + (⌊C * (binaryLength Q : ℝ) ^ b⌋₊ : ℝ) := by
    exact_mod_cast hrec
  refine ⟨m, Nat.sub_lt (by omega) hwpos, ?_⟩
  linarith

theorem local_bounds_give_power_bound {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1)
    (hlocal : LocalFactorialBounds (1 + p / 16) (p / 4)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ,
      (Erdos18.practicalH n.factorial : ℝ) ≤ K + (n : ℝ) ^ p := by
  obtain ⟨C, hC, hlocal⟩ := hlocal
  apply bounded_of_eventual_potential_decrease
    (fun n => (Erdos18.practicalH n.factorial : ℝ)) (fun n => (n : ℝ) ^ p)
    (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) p)
  exact eventual_factorial_potential_decrease (a := 1 + p / 16) (b := p / 4)
    (θ := 1 - p / 4) (γ := p / 8)
    (by linarith) (by linarith) hp hp1 (by linarith) (by linarith) (by linarith)
    hC.le (by nlinarith [sq_nonneg p]) (by nlinarith [sq_nonneg p]) hlocal

/- This intermediate conditional theorem verifies the
entire subsequent deduction, including both recursions and the strict bound. -/
theorem erdos18b_of_dyadic_modular_bounds
    (h : ∀ a b : ℝ, 1 < a → 0 < b → DyadicModularBounds a b) :
    fcTypeOfName% "Erdos18.erdos_18b" := by
  constructor
  · intro _ δ hδ
    let p : ℝ := min (δ / 2) (1 / 2)
    have hp : 0 < p := lt_min (half_pos hδ) (by norm_num)
    have hp1 : p ≤ 1 := (min_le_right _ _).trans (by norm_num)
    have hpδ : p < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
    have ha : 0 < 1 + p / 16 := by linarith
    have hb : 0 < p / 4 := by linarith
    have hba : p / 4 ≤ 1 + p / 16 := by linarith
    have hmod := h (1 + p / 16) (p / 4) (by linarith) hb
    have hlocal := dyadic_modular_bounds_give_local_bounds ha hb hba hmod
    obtain ⟨K, _, hbound⟩ := local_bounds_give_power_bound hp hp1 hlocal
    have hpow := eventually_const_mul_rpow_le (C := 1) (E := 1 / 3) hpδ (by norm_num)
    have hconst := eventually_const_mul_rpow_le (C := K) (E := 1 / 3) hδ (by norm_num)
    filter_upwards [hpow, hconst, eventually_ge_atTop (1 : ℕ)] with n hn hK hn1
    have hn' : (n : ℝ) ^ p ≤ (1 / 3) * (n : ℝ) ^ δ := by simpa using hn
    have hK' : K ≤ (1 / 3) * (n : ℝ) ^ δ := by simpa using hK
    have hpos : 0 < (n : ℝ) ^ δ := Real.rpow_pos_of_pos
      (by exact_mod_cast (show 0 < n by omega)) δ
    calc
      (Erdos18.practicalH n.factorial : ℝ) ≤ K + (n : ℝ) ^ p := hbound n
      _ ≤ (1 / 3) * (n : ℝ) ^ δ + (1 / 3) * (n : ℝ) ^ δ := add_le_add hK' hn'
      _ < (n : ℝ) ^ δ := by nlinarith only [hpos]
  · intro _
    trivial

theorem subpolynomial_of_power_log_bounds (f : ℕ → ℝ)
    (h : ∀ ε : ℝ, 0 < ε → ∃ C K : ℝ, ∀ᶠ n : ℕ in Filter.atTop,
      f n ≤ C * (n : ℝ) ^ ε * (Real.log (n : ℝ)) ^ K) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in Filter.atTop, f n < (n : ℝ) ^ δ := by
  intro δ hδ
  have hhalf : 0 < δ / 2 := half_pos hδ
  obtain ⟨C, K, hbound⟩ := h (δ / 2) hhalf
  have hsmall := ((isLittleO_log_rpow_rpow_atTop K hhalf).const_mul_left C).comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hevent := hsmall.def (by norm_num : (0 : ℝ) < 1 / 2)
  filter_upwards [hbound, hevent, eventually_ge_atTop (1 : ℕ)] with n hn he hn1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hp : 0 < (n : ℝ) ^ (δ / 2) := Real.rpow_pos_of_pos hnpos _
  have hlog : C * (Real.log (n : ℝ)) ^ K < (n : ℝ) ^ (δ / 2) := by
    have he' : |C * (Real.log (n : ℝ)) ^ K| ≤ (1 / 2) * (n : ℝ) ^ (δ / 2) := by
      simpa only [Function.comp_apply, Real.norm_eq_abs, abs_of_pos hp] using he
    have hle := le_abs_self (C * (Real.log (n : ℝ)) ^ K)
    linarith
  calc
    f n ≤ C * (n : ℝ) ^ (δ / 2) * (Real.log (n : ℝ)) ^ K := hn
    _ = (n : ℝ) ^ (δ / 2) * (C * (Real.log (n : ℝ)) ^ K) := by ring
    _ < (n : ℝ) ^ (δ / 2) * (n : ℝ) ^ (δ / 2) :=
      mul_lt_mul_of_pos_left hlog hp
    _ = (n : ℝ) ^ δ := by
      rw [← Real.rpow_add hnpos]
      congr 1
      ring

/- Final asymptotic deduction from the intermediate modular hypothesis. -/
theorem erdos18b_of_power_log_bounds
    (h : ∀ ε : ℝ, 0 < ε → ∃ C K : ℝ, ∀ᶠ n : ℕ in Filter.atTop,
      (Erdos18.practicalH n.factorial : ℝ) ≤
        C * (n : ℝ) ^ ε * (Real.log (n : ℝ)) ^ K) :
    fcTypeOfName% "Erdos18.erdos_18b" := by
  constructor
  · intro _
    exact subpolynomial_of_power_log_bounds _ h
  · intro _
    trivial

noncomputable def cyclicConvolution {q : ℕ} [NeZero q]
    (f g : ZMod q → ℂ) (x : ZMod q) : ℂ := ∑ y, f y * g (x - y)

theorem dft_cyclicConvolution {q : ℕ} [NeZero q]
    (f g : ZMod q → ℂ) (k : ZMod q) :
    ZMod.dft (cyclicConvolution f g) k = ZMod.dft f k * ZMod.dft g k := by
  classical
  simp only [ZMod.dft_apply, smul_eq_mul, cyclicConvolution]
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  refine Fintype.sum_equiv (Equiv.subRight y) _ _ ?_
  intro x
  simp only [Equiv.subRight_apply]
  have hchar : ZMod.stdAddChar (-(x * k)) =
      ZMod.stdAddChar (-(y * k)) * ZMod.stdAddChar (-((x - y) * k)) := by
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  rw [hchar]
  ring

noncomputable def cyclicConvolutionPow {q : ℕ} [NeZero q]
    (f : ZMod q → ℂ) : ℕ → ZMod q → ℂ
  | 0 => fun x => if x = 0 then 1 else 0
  | s + 1 => cyclicConvolution f (cyclicConvolutionPow f s)

theorem dft_cyclicConvolutionPow {q : ℕ} [NeZero q]
    (f : ZMod q → ℂ) (s : ℕ) (k : ZMod q) :
    ZMod.dft (cyclicConvolutionPow f s) k = (ZMod.dft f k) ^ s := by
  classical
  induction s with
  | zero => simp [cyclicConvolutionPow, ZMod.dft_apply]
  | succ s ih =>
    rw [cyclicConvolutionPow, dft_cyclicConvolution, ih, pow_succ]
    ring

theorem nonzero_of_fourier_norm_sum_lt_one {q : ℕ} [NeZero q]
    (f : ZMod q → ℂ) (hzero : ZMod.dft f 0 = 1)
    (hsmall : ∑ k ∈ (Finset.univ : Finset (ZMod q)).erase 0, ‖ZMod.dft f k‖ < 1) :
    ∀ x : ZMod q, f x ≠ 0 := by
  classical
  intro x hx
  have hsum := congrFun (ZMod.dft_dft f) (-x)
  rw [ZMod.dft_apply] at hsum
  simp only [mul_neg, neg_neg, hx, smul_eq_mul, mul_zero] at hsum
  have hsplit := Finset.sum_erase_add (Finset.univ : Finset (ZMod q))
    (fun k => ZMod.stdAddChar (k * x) * ZMod.dft f k) (Finset.mem_univ 0)
  have hrest : (∑ k ∈ (Finset.univ : Finset (ZMod q)).erase 0,
      ZMod.stdAddChar (k * x) * ZMod.dft f k) = -1 := by
    have hz : ZMod.stdAddChar (0 * x) * ZMod.dft f 0 = 1 := by simp [hzero]
    rw [hz, hsum] at hsplit
    exact eq_neg_of_add_eq_zero_left hsplit
  have hnorm : ‖∑ k ∈ (Finset.univ : Finset (ZMod q)).erase 0,
      ZMod.stdAddChar (k * x) * ZMod.dft f k‖ ≤
      ∑ k ∈ (Finset.univ : Finset (ZMod q)).erase 0, ‖ZMod.dft f k‖ := by
    calc
      _ ≤ ∑ k ∈ (Finset.univ : Finset (ZMod q)).erase 0,
          ‖ZMod.stdAddChar (k * x) * ZMod.dft f k‖ := norm_sum_le _ _
      _ = _ := by simp only [norm_mul, ZMod.stdAddChar_apply, Circle.norm_coe, one_mul]
  rw [hrest] at hnorm
  norm_num only [norm_neg, norm_one] at hnorm
  exact (hnorm.trans_lt hsmall).false

theorem convolution_pow_nonzero_of_fourier_bound {q : ℕ} [NeZero q]
    (f : ZMod q → ℂ) (s : ℕ) (hzero : ZMod.dft f 0 = 1)
    (hsmall : ∑ k ∈ (Finset.univ : Finset (ZMod q)).erase 0, ‖ZMod.dft f k‖ ^ s < 1) :
    ∀ x : ZMod q, cyclicConvolutionPow f s x ≠ 0 := by
  apply nonzero_of_fourier_norm_sum_lt_one
  · rw [dft_cyclicConvolutionPow, hzero, one_pow]
  · simpa only [dft_cyclicConvolutionPow, norm_pow] using hsmall

theorem convolution_pow_support_representatives {q : ℕ} [NeZero q]
    (f : ZMod q → ℂ) (F u H : ℕ)
    (hsupport : ∀ x : ZMod q, f x ≠ 0 → ∃ S : ℕ,
      S ≤ H ∧ (S : ZMod q) = x ∧ HasFactorialDivisorMultiset F S u) :
    ∀ s : ℕ, ∀ x : ZMod q, cyclicConvolutionPow f s x ≠ 0 → ∃ S : ℕ,
      S ≤ s * H ∧ (S : ZMod q) = x ∧ HasFactorialDivisorMultiset F S (s * u) := by
  classical
  intro s
  induction s with
  | zero =>
    intro x hx
    have hxzero : x = 0 := by
      by_contra hne
      simp only [cyclicConvolutionPow, if_neg hne] at hx
      exact hx rfl
    subst x
    exact ⟨0, by simp, by simp, by simpa using factorial_multiset_zero F 0⟩
  | succ s ih =>
    intro x hx
    change (∑ y : ZMod q, f y * cyclicConvolutionPow f s (x - y)) ≠ 0 at hx
    obtain ⟨y, _, hy⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
    obtain ⟨hfy, hgs⟩ := mul_ne_zero_iff.mp hy
    obtain ⟨A, hA, hAcast, hArep⟩ := hsupport y hfy
    obtain ⟨B, hB, hBcast, hBrep⟩ := ih (x - y) hgs
    refine ⟨A + B, ?_, ?_, ?_⟩
    · calc
        A + B ≤ H + s * H := Nat.add_le_add hA hB
        _ = (s + 1) * H := by ring
    · rw [Nat.cast_add, hAcast, hBcast]
      abel
    · simpa only [Nat.succ_mul, Nat.add_comm] using factorial_multiset_add hArep hBrep

theorem bounded_modular_representatives_of_fourier {q F u H D s : ℕ} [NeZero q]
    (f : ZMod q → ℂ) (hzero : ZMod.dft f 0 = 1)
    (hsmall : ∑ k ∈ (Finset.univ : Finset (ZMod q)).erase 0, ‖ZMod.dft f k‖ ^ s < 1)
    (hsupport : ∀ x : ZMod q, f x ≠ 0 → ∃ S : ℕ,
      S ≤ H ∧ (S : ZMod q) = x ∧ HasFactorialDivisorMultiset F S u)
    (hheight : s * H ≤ q ^ D) :
    HasBoundedModularRepresentatives q F (s * u) D := by
  intro R
  obtain ⟨S, hS, hScast, hrep⟩ := convolution_pow_support_representatives f F u H hsupport s
    (R : ZMod q) (convolution_pow_nonzero_of_fourier_bound f s hzero hsmall (R : ZMod q))
  exact ⟨S, hS.trans hheight, (ZMod.natCast_eq_natCast_iff S R q).mp hScast, hrep⟩

noncomputable def dyadicConductorLevel {K : ℕ} (x : ZMod (2 ^ K)) : ℕ :=
  Nat.log 2 (addOrderOf x)

theorem dyadic_conductor_spec {K : ℕ} (x : ZMod (2 ^ K)) :
    dyadicConductorLevel x ≤ K ∧ addOrderOf x = 2 ^ dyadicConductorLevel x := by
  have hdvd : addOrderOf x ∣ 2 ^ K := by
    simpa only [ZMod.card] using addOrderOf_dvd_card (x := x)
  obtain ⟨j, hj, heq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hlevel : dyadicConductorLevel x = j := by
    simp only [dyadicConductorLevel, heq, Nat.log_pow (by decide : 1 < 2)]
  exact ⟨hlevel ▸ hj, by rw [hlevel, heq]⟩

theorem dyadic_conductor_pos {K : ℕ} {x : ZMod (2 ^ K)} (hx : x ≠ 0) :
    0 < dyadicConductorLevel x := by
  by_contra h
  have hz : dyadicConductorLevel x = 0 := by omega
  have horder : addOrderOf x = 1 := by simpa only [hz, pow_zero] using (dyadic_conductor_spec x).2
  exact hx (AddMonoid.addOrderOf_eq_one_iff.mp horder)

theorem dyadic_conductor_fiber_card_le {K j : ℕ} (hj : j ≤ K) :
    (((Finset.univ : Finset (ZMod (2 ^ K))).erase 0).filter
      (fun x => dyadicConductorLevel x = j)).card ≤ 2 ^ j := by
  classical
  have hsub : (((Finset.univ : Finset (ZMod (2 ^ K))).erase 0).filter
      (fun x => dyadicConductorLevel x = j)) ⊆
      (Finset.univ.filter (fun x : ZMod (2 ^ K) => addOrderOf x = 2 ^ j)) := by
    intro x hx
    obtain ⟨_, heq⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [← heq]; exact (dyadic_conductor_spec x).2⟩
  calc
    _ ≤ (Finset.univ.filter (fun x : ZMod (2 ^ K) => addOrderOf x = 2 ^ j)).card :=
      Finset.card_le_card hsub
    _ = Nat.totient (2 ^ j) := IsAddCyclic.card_addOrderOf_eq_totient
      (by simpa only [ZMod.card] using pow_dvd_pow 2 hj)
    _ ≤ 2 ^ j := Nat.totient_le _

theorem dyadic_geometric_sum (K : ℕ) :
    (∑ j ∈ Finset.Icc 1 K, (1 / 2 : ℝ) ^ j) = 1 - (1 / 2 : ℝ) ^ K := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ K + 1), ih, pow_succ]
    ring

theorem dyadic_fourier_norm_sum_lt_one {K s : ℕ} (f : ZMod (2 ^ K) → ℂ)
    (hdecay : ∀ x : ZMod (2 ^ K), x ≠ 0 →
      ‖ZMod.dft f x‖ ^ s ≤ (1 / 4 : ℝ) ^ dyadicConductorLevel x) :
    ∑ x ∈ (Finset.univ : Finset (ZMod (2 ^ K))).erase 0, ‖ZMod.dft f x‖ ^ s < 1 := by
  classical
  have hmaps : ∀ x ∈ (Finset.univ : Finset (ZMod (2 ^ K))).erase 0,
      dyadicConductorLevel x ∈ Finset.Icc 1 K := by
    intro x hx
    exact Finset.mem_Icc.mpr ⟨dyadic_conductor_pos (Finset.mem_erase.mp hx).1,
      (dyadic_conductor_spec x).1⟩
  have hbound :
      (∑ x ∈ (Finset.univ : Finset (ZMod (2 ^ K))).erase 0, ‖ZMod.dft f x‖ ^ s) ≤
      ∑ j ∈ Finset.Icc 1 K, (1 / 2 : ℝ) ^ j := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun x => ‖ZMod.dft f x‖ ^ s)]
    apply Finset.sum_le_sum
    intro j hj
    have hcard :
        ((((Finset.univ : Finset (ZMod (2 ^ K))).erase 0).filter
          (fun x => dyadicConductorLevel x = j)).card : ℝ) ≤ (2 : ℝ) ^ j := by
      exact_mod_cast dyadic_conductor_fiber_card_le (Finset.mem_Icc.mp hj).2
    calc
      _ ≤ ∑ x ∈ (((Finset.univ : Finset (ZMod (2 ^ K))).erase 0).filter
          (fun x => dyadicConductorLevel x = j)), (1 / 4 : ℝ) ^ j := by
        apply Finset.sum_le_sum
        intro x hx
        obtain ⟨hx, hlevel⟩ := Finset.mem_filter.mp hx
        simpa only [hlevel] using hdecay x (Finset.mem_erase.mp hx).1
      _ = ((((Finset.univ : Finset (ZMod (2 ^ K))).erase 0).filter
          (fun x => dyadicConductorLevel x = j)).card : ℝ) * (1 / 4 : ℝ) ^ j := by simp
      _ ≤ (2 : ℝ) ^ j * (1 / 4 : ℝ) ^ j :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = (1 / 2 : ℝ) ^ j := by rw [← mul_pow]; norm_num
  rw [dyadic_geometric_sum] at hbound
  have hpos : 0 < (1 / 2 : ℝ) ^ K := pow_pos (by norm_num) _
  exact hbound.trans_lt (by linarith)

theorem powered_dyadic_decay_le {v t : ℝ} {s j : ℕ} (hv : 0 ≤ v)
    (hdecay : v ≤ (2 : ℝ) ^ (-t * (j : ℝ))) (hs : 2 ≤ t * (s : ℝ)) :
    v ^ s ≤ (1 / 4 : ℝ) ^ j := by
  calc
    v ^ s ≤ ((2 : ℝ) ^ (-t * (j : ℝ))) ^ s := pow_le_pow_left₀ hv hdecay s
    _ = (2 : ℝ) ^ ((-t * (j : ℝ)) * (s : ℝ)) :=
      (Real.rpow_mul_natCast (by norm_num) _ _).symm
    _ ≤ (2 : ℝ) ^ ((-2 : ℝ) * (j : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      nlinarith [mul_le_mul_of_nonneg_right hs (Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    _ = (1 / 4 : ℝ) ^ j := by
      rw [Real.rpow_mul_natCast (by norm_num)]
      norm_num [Real.rpow_neg, Real.rpow_ofNat]

theorem exists_convolution_power_for_dyadic_decay {t : ℝ} (ht : 0 < t) :
    ∃ s : ℕ, 0 < s ∧ ∀ K : ℕ, ∀ f : ZMod (2 ^ K) → ℂ,
      (∀ x : ZMod (2 ^ K), x ≠ 0 →
        ‖ZMod.dft f x‖ ≤ (2 : ℝ) ^ (-t * (dyadicConductorLevel x : ℝ))) →
      ∑ x ∈ (Finset.univ : Finset (ZMod (2 ^ K))).erase 0, ‖ZMod.dft f x‖ ^ s < 1 := by
  obtain ⟨s, hs⟩ := exists_nat_ge (2 / t)
  have hts : 2 ≤ t * (s : ℝ) := by
    have := (div_le_iff₀ ht).mp hs
    nlinarith
  have hspos : 0 < s := by
    by_contra h
    have : s = 0 := by omega
    simp only [this, Nat.cast_zero, mul_zero] at hts
    norm_num at hts
  refine ⟨s, hspos, ?_⟩
  intro K f hdecay
  apply dyadic_fourier_norm_sum_lt_one
  intro x hx
  exact powered_dyadic_decay_le (norm_nonneg _) (hdecay x hx) hts

noncomputable def cyclicPushforward {α : Type*} [Fintype α] {q : ℕ} [NeZero q]
    (w : α → ℂ) (T : α → ZMod q) (x : ZMod q) : ℂ :=
  ∑ a, if T a = x then w a else 0

theorem dft_cyclicPushforward {α : Type*} [Fintype α] {q : ℕ} [NeZero q]
    (w : α → ℂ) (T : α → ZMod q) (k : ZMod q) :
    ZMod.dft (cyclicPushforward w T) k = ∑ a, ZMod.stdAddChar (-(T a * k)) * w a := by
  classical
  simp only [ZMod.dft_apply, cyclicPushforward, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp only [mul_ite, mul_zero]
  simp

theorem cyclicPushforward_support {α : Type*} [Fintype α] {q : ℕ} [NeZero q]
    (w : α → ℂ) (T : α → ZMod q) {x : ZMod q}
    (hx : cyclicPushforward w T x ≠ 0) : ∃ a : α, T a = x ∧ w a ≠ 0 := by
  classical
  obtain ⟨a, _, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
  by_cases h : T a = x
  · exact ⟨a, h, by simpa only [h, if_true] using ha⟩
  · simp only [h, if_false, ne_eq, not_true_eq_false] at ha

theorem dft_translate {q : ℕ} [NeZero q] (f : ZMod q → ℂ) (a k : ZMod q) :
    ZMod.dft (fun x => f (x - a)) k = ZMod.stdAddChar (-(a * k)) * ZMod.dft f k := by
  classical
  simp only [ZMod.dft_apply, smul_eq_mul, Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.subRight a) _ _ ?_
  intro x
  simp only [Equiv.subRight_apply]
  rw [← mul_assoc, ← AddChar.map_add_eq_mul]
  congr 2
  ring

noncomputable def cyclicBernoulliSmooth {q : ℕ} [NeZero q]
    (f : ZMod q → ℂ) (x : ZMod q) : ℂ := (f x + f (x - 1)) / 2

theorem dft_cyclicBernoulliSmooth {q : ℕ} [NeZero q]
    (f : ZMod q → ℂ) (k : ZMod q) :
    ZMod.dft (cyclicBernoulliSmooth f) k =
      ZMod.dft f k * ((1 + ZMod.stdAddChar (-k)) / 2) := by
  have heq : cyclicBernoulliSmooth f =
      (fun x => f x + f (x - 1)) * (fun _ => (2 : ℂ)⁻¹) := by
    ext x
    simp [cyclicBernoulliSmooth, div_eq_mul_inv]
  rw [heq]
  change ZMod.dft (fun x => (f x + f (x - 1)) * (2 : ℂ)⁻¹) k = _
  rw [ZMod.dft_mul_const]
  change ZMod.dft (fun x => f x + f (x - 1)) k * (2 : ℂ)⁻¹ = _
  have hadd : ZMod.dft (fun x => f x + f (x - 1)) k =
      ZMod.dft f k + ZMod.dft (fun x => f (x - 1)) k := by
    exact congrFun (map_add ZMod.dft f (fun x => f (x - 1))) k
  rw [hadd, dft_translate]
  simp only [one_mul]
  ring

theorem norm_dft_cyclicBernoulliSmooth_le {q : ℕ} [NeZero q]
    (f : ZMod q → ℂ) (k : ZMod q) :
    ‖ZMod.dft (cyclicBernoulliSmooth f) k‖ ≤ ‖ZMod.dft f k‖ := by
  have hnorm : ‖(1 + ZMod.stdAddChar (-k)) / (2 : ℂ)‖ ≤ 1 := by
    rw [norm_div]
    have ht := norm_add_le (1 : ℂ) (ZMod.stdAddChar (-k))
    norm_num only [norm_one, ZMod.stdAddChar_apply, Circle.norm_coe, Complex.norm_ofNat] at *
    linarith
  rw [dft_cyclicBernoulliSmooth, norm_mul]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)

theorem dft_cyclicBernoulliSmooth_zero {q : ℕ} [NeZero q]
    (f : ZMod q → ℂ) {k : ZMod q} (hk : k ≠ 0) (h2 : (2 : ZMod q) * k = 0) :
    ZMod.dft (cyclicBernoulliSmooth f) k = 0 := by
  have hsq : ZMod.stdAddChar (-k) ^ 2 = (1 : ℂ) := by
    rw [← AddChar.map_nsmul_eq_pow]
    have hz : 2 • (-k) = 0 := by
      norm_num only [nsmul_eq_mul, Nat.cast_ofNat, mul_neg, h2, neg_zero]
    rw [hz, AddChar.map_zero_eq_one]
  have hne : ZMod.stdAddChar (-k) ≠ (1 : ℂ) := by
    intro h
    have hzero : ZMod.stdAddChar (-k) = ZMod.stdAddChar (0 : ZMod q) := by simpa using h
    exact hk (neg_eq_zero.mp (ZMod.injective_stdAddChar hzero))
  have hchar := (sq_eq_one_iff.mp hsq).resolve_left hne
  rw [dft_cyclicBernoulliSmooth, hchar]
  simp

theorem sum_addChar_progression_eq_zero {q : ℕ} [NeZero q]
    (ψ : AddChar (ZMod q) ℂ) (a b : ZMod q) (n : ℕ)
    (hb : ψ b ≠ 1) (hn : ψ (n • b) = 1) :
    ∑ i ∈ Finset.range n, ψ (a + i • b) = 0 := by
  have hpow : (ψ b) ^ n = 1 := by rw [← AddChar.map_nsmul_eq_pow, hn]
  have hgeom := geom_sum_mul (ψ b) n
  rw [hpow, sub_self] at hgeom
  have hsum : (∑ i ∈ Finset.range n, (ψ b) ^ i) = 0 :=
    (mul_eq_zero.mp hgeom).resolve_right (sub_ne_zero.mpr hb)
  simp_rw [AddChar.map_add_eq_mul, AddChar.map_nsmul_eq_pow]
  rw [← Finset.mul_sum, hsum, mul_zero]

theorem dyadic_conductor_twice_ne_zero {K : ℕ} {x : ZMod (2 ^ K)}
    (hx : 2 ≤ dyadicConductorLevel x) : (2 : ZMod (2 ^ K)) * x ≠ 0 := by
  intro hzero
  have hsmul : 2 • x = 0 := by simpa only [nsmul_eq_mul, Nat.cast_ofNat] using hzero
  have hdvd : addOrderOf x ∣ 2 := addOrderOf_dvd_iff_nsmul_eq_zero.mpr hsmul
  rw [(dyadic_conductor_spec x).2] at hdvd
  have hle := Nat.le_of_dvd (by decide : 0 < 2) hdvd
  have hfour : 4 ≤ 2 ^ dyadicConductorLevel x := by
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hx
  omega

theorem dyadic_conductor_power_nsmul_eq_zero {K b : ℕ} {x : ZMod (2 ^ K)}
    (hx : dyadicConductorLevel x ≤ b) : (2 ^ b) • x = 0 := by
  apply addOrderOf_dvd_iff_nsmul_eq_zero.mp
  rw [(dyadic_conductor_spec x).2]
  exact pow_dvd_pow 2 hx

noncomputable def cyclicOddDigit {K : ℕ} (b : ℕ) : ZMod (2 ^ K) → ℂ :=
  cyclicPushforward (fun _ : Fin (2 ^ (b - 1)) => ((2 ^ (b - 1) : ℕ) : ℂ)⁻¹)
    (fun i => ((2 * i.val + 1 : ℕ) : ZMod (2 ^ K)))

theorem dft_cyclicOddDigit_zero {K b : ℕ} {k : ZMod (2 ^ K)}
    (hklo : 2 ≤ dyadicConductorLevel k) (hkhi : dyadicConductorLevel k ≤ b) :
    ZMod.dft (cyclicOddDigit b) k = 0 := by
  have hbpos : 0 < b := by omega
  have hp : 2 ^ (b - 1) * 2 = 2 ^ b := by
    rw [← pow_succ, Nat.sub_add_cancel hbpos]
  have hchar : ZMod.stdAddChar (-(2 * k)) ≠ (1 : ℂ) := by
    intro h
    have hh : ZMod.stdAddChar (-(2 * k)) = ZMod.stdAddChar (0 : ZMod (2 ^ K)) := by
      simpa using h
    exact dyadic_conductor_twice_ne_zero hklo (neg_eq_zero.mp (ZMod.injective_stdAddChar hh))
  have hperiod : ZMod.stdAddChar ((2 ^ (b - 1)) • (-(2 * k))) = (1 : ℂ) := by
    have heq : ((2 ^ (b - 1) : ℕ) • (-(2 * k)) : ZMod (2 ^ K)) =
        -((2 ^ b : ℕ) • k) := by
      simp only [nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat, mul_neg]
      rw [← mul_assoc]
      congr 2
      simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
        congrArg (fun n : ℕ => (n : ZMod (2 ^ K))) hp
    rw [heq, dyadic_conductor_power_nsmul_eq_zero hkhi, neg_zero, AddChar.map_zero_eq_one]
  have hsum := sum_addChar_progression_eq_zero ZMod.stdAddChar (-k) (-(2 * k))
    (2 ^ (b - 1)) hchar hperiod
  have hrewrite : ∀ i : ℕ,
      ZMod.stdAddChar (-(((2 * i + 1 : ℕ) : ZMod (2 ^ K)) * k)) =
        ZMod.stdAddChar (-k + i • (-(2 * k))) := by
    intro i
    congr 1
    push_cast
    simp only [nsmul_eq_mul]
    ring
  rw [cyclicOddDigit, dft_cyclicPushforward, ← Finset.sum_mul]
  have hfin : (∑ i : Fin (2 ^ (b - 1)),
      ZMod.stdAddChar (-(((2 * i.val + 1 : ℕ) : ZMod (2 ^ K)) * k))) = 0 := by
    simpa only [hrewrite] using
      (Fin.sum_univ_eq_sum_range
        (fun i : ℕ => ZMod.stdAddChar (-k + i • (-(2 * k)))) (2 ^ (b - 1))).trans hsum
  rw [hfin, zero_mul]

theorem dyadic_conductor_mul_unit {K : ℕ} (x y : ZMod (2 ^ K)) (hy : IsUnit y) :
    dyadicConductorLevel (y * x) = dyadicConductorLevel x := by
  obtain ⟨u, rfl⟩ := hy
  have horder : addOrderOf ((u : ZMod (2 ^ K)) * x) = addOrderOf x :=
    addOrderOf_injective (AddMonoidHom.mulLeft (u : ZMod (2 ^ K)))
      (Units.mulLeft u).injective x
  simp only [dyadicConductorLevel, horder]

noncomputable def cyclicMultiplicativeConvolution {q : ℕ} [NeZero q]
    (f g : ZMod q → ℂ) : ZMod q → ℂ :=
  cyclicPushforward (fun p : ZMod q × ZMod q => f p.1 * g p.2) (fun p => p.1 * p.2)

theorem dft_cyclicMultiplicativeConvolution {q : ℕ} [NeZero q]
    (f g : ZMod q → ℂ) (k : ZMod q) :
    ZMod.dft (cyclicMultiplicativeConvolution f g) k =
      ∑ y : ZMod q, g y * ZMod.dft f (y * k) := by
  classical
  rw [cyclicMultiplicativeConvolution, dft_cyclicPushforward]
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  simp only [ZMod.dft_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem cyclicMultiplicativeConvolution_support_units {q : ℕ} [NeZero q]
    (f g : ZMod q → ℂ) (hf : ∀ x, f x ≠ 0 → IsUnit x)
    (hg : ∀ x, g x ≠ 0 → IsUnit x) :
    ∀ x, cyclicMultiplicativeConvolution f g x ≠ 0 → IsUnit x := by
  intro x hx
  obtain ⟨⟨a, b⟩, hab, hw⟩ := cyclicPushforward_support
    (fun p : ZMod q × ZMod q => f p.1 * g p.2) (fun p => p.1 * p.2) hx
  obtain ⟨ha, hb⟩ := mul_ne_zero_iff.mp hw
  rw [← hab]
  exact (hf a ha).mul (hg b hb)

theorem cyclicMultiplicativeConvolution_support_representatives {q F G u v H J : ℕ}
    [NeZero q] (f g : ZMod q → ℂ)
    (hf : ∀ x, f x ≠ 0 → ∃ S : ℕ,
      S ≤ H ∧ (S : ZMod q) = x ∧ HasFactorialDivisorMultiset F S u)
    (hg : ∀ x, g x ≠ 0 → ∃ S : ℕ,
      S ≤ J ∧ (S : ZMod q) = x ∧ HasFactorialDivisorMultiset G S v) :
    ∀ x, cyclicMultiplicativeConvolution f g x ≠ 0 → ∃ S : ℕ,
      S ≤ H * J ∧ (S : ZMod q) = x ∧ HasFactorialDivisorMultiset (F + G) S (u * v) := by
  intro x hx
  obtain ⟨⟨a, b⟩, hab, hw⟩ := cyclicPushforward_support
    (fun p : ZMod q × ZMod q => f p.1 * g p.2) (fun p => p.1 * p.2) hx
  obtain ⟨ha, hb⟩ := mul_ne_zero_iff.mp hw
  obtain ⟨A, hA, hAcast, hArep⟩ := hf a ha
  obtain ⟨B, hB, hBcast, hBrep⟩ := hg b hb
  exact ⟨A * B, Nat.mul_le_mul hA hB, by simpa only [Nat.cast_mul, hAcast, hBcast] using hab,
    factorial_multiset_mul hArep hBrep⟩

theorem dft_cyclicMultiplicativeConvolution_zero {K lo hi : ℕ}
    (f g : ZMod (2 ^ K) → ℂ)
    (hf : ∀ x, lo ≤ dyadicConductorLevel x → dyadicConductorLevel x ≤ hi → ZMod.dft f x = 0)
    (hg : ∀ x, g x ≠ 0 → IsUnit x) {k : ZMod (2 ^ K)}
    (hklo : lo ≤ dyadicConductorLevel k) (hkhi : dyadicConductorLevel k ≤ hi) :
    ZMod.dft (cyclicMultiplicativeConvolution f g) k = 0 := by
  rw [dft_cyclicMultiplicativeConvolution]
  apply Finset.sum_eq_zero
  intro y _
  by_cases hy : g y = 0
  · simp only [hy, zero_mul]
  · have hlevel := dyadic_conductor_mul_unit k y (hg y hy)
    rw [hf (y * k) (by rwa [hlevel]) (by rwa [hlevel]), mul_zero]

noncomputable def cyclicProductPow {q : ℕ} [NeZero q]
    (f : ZMod q → ℂ) : ℕ → ZMod q → ℂ
  | 0 => fun x => if x = 1 then 1 else 0
  | r + 1 => cyclicMultiplicativeConvolution f (cyclicProductPow f r)

theorem cyclicProductPow_support_units {q : ℕ} [NeZero q]
    (f : ZMod q → ℂ) (hf : ∀ x, f x ≠ 0 → IsUnit x) :
    ∀ r : ℕ, ∀ x, cyclicProductPow f r x ≠ 0 → IsUnit x := by
  intro r
  induction r with
  | zero =>
    intro x hx
    have hxeq : x = 1 := by
      by_contra h
      simp only [cyclicProductPow, if_neg h, ne_eq, not_true_eq_false] at hx
    rw [hxeq]
    exact isUnit_one
  | succ r ih =>
    exact cyclicMultiplicativeConvolution_support_units f _ hf ih

theorem cyclicProductPow_support_representatives {q F u H : ℕ} [NeZero q]
    (f : ZMod q → ℂ)
    (hf : ∀ x, f x ≠ 0 → ∃ S : ℕ,
      S ≤ H ∧ (S : ZMod q) = x ∧ HasFactorialDivisorMultiset F S u) :
    ∀ r : ℕ, ∀ x, cyclicProductPow f r x ≠ 0 → ∃ S : ℕ,
      S ≤ H ^ r ∧ (S : ZMod q) = x ∧ HasFactorialDivisorMultiset (r * F) S (u ^ r) := by
  intro r
  induction r with
  | zero =>
    intro x hx
    have hxeq : x = 1 := by
      by_contra h
      simp only [cyclicProductPow, if_neg h, ne_eq, not_true_eq_false] at hx
    refine ⟨1, by simp, by simp [hxeq], ?_⟩
    simpa using factorial_multiset_singleton (F := 0) (R := 1) (one_dvd _)
  | succ r ih =>
    intro x hx
    have hrep := cyclicMultiplicativeConvolution_support_representatives f _ hf ih x hx
    simpa only [Nat.succ_mul, pow_succ, Nat.add_comm, Nat.mul_comm] using hrep

theorem dft_cyclicProductPow_zero {K lo hi r : ℕ}
    (f : ZMod (2 ^ K) → ℂ) (hr : 0 < r)
    (hu : ∀ x, f x ≠ 0 → IsUnit x)
    (hf : ∀ x, lo ≤ dyadicConductorLevel x → dyadicConductorLevel x ≤ hi → ZMod.dft f x = 0)
    {k : ZMod (2 ^ K)} (hklo : lo ≤ dyadicConductorLevel k)
    (hkhi : dyadicConductorLevel k ≤ hi) :
    ZMod.dft (cyclicProductPow f r) k = 0 := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  exact dft_cyclicMultiplicativeConvolution_zero f _ hf
    (cyclicProductPow_support_units f hu r) hklo hkhi

theorem dft_cyclicOddDigit_at_zero {K : ℕ} (b : ℕ) :
    ZMod.dft (cyclicOddDigit (K := K) b) 0 = 1 := by
  rw [cyclicOddDigit, dft_cyclicPushforward]
  simp

theorem cyclicOddDigit_support_units {K b : ℕ} :
    ∀ x, cyclicOddDigit (K := K) b x ≠ 0 → IsUnit x := by
  intro x hx
  obtain ⟨i, hi, _⟩ := cyclicPushforward_support
    (fun _ : Fin (2 ^ (b - 1)) => ((2 ^ (b - 1) : ℕ) : ℂ)⁻¹)
    (fun i => ((2 * i.val + 1 : ℕ) : ZMod (2 ^ K))) hx
  rw [← hi]
  apply (ZMod.isUnit_iff_coprime _ _).mpr
  have hc : Nat.Coprime (2 * i.val + 1) 2 := by
    rw [Nat.coprime_comm, Nat.prime_two.coprime_iff_not_dvd]
    omega
  exact hc.pow_right K

theorem cyclicOddDigit_support_representatives {K b F : ℕ} (hb : 0 < b) (hF : 2 ^ b ≤ F) :
    ∀ x, cyclicOddDigit (K := K) b x ≠ 0 → ∃ S : ℕ,
      S ≤ 2 ^ b ∧ (S : ZMod (2 ^ K)) = x ∧ HasFactorialDivisorMultiset F S 1 := by
  intro x hx
  obtain ⟨i, hi, _⟩ := cyclicPushforward_support
    (fun _ : Fin (2 ^ (b - 1)) => ((2 ^ (b - 1) : ℕ) : ℂ)⁻¹)
    (fun i => ((2 * i.val + 1 : ℕ) : ZMod (2 ^ K))) hx
  have hp : 2 ^ b = 2 * 2 ^ (b - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hb]
  have hS : 2 * i.val + 1 ≤ 2 ^ b := by rw [hp]; omega
  exact ⟨2 * i.val + 1, hS, hi,
    factorial_multiset_singleton (Nat.dvd_factorial (by omega) (hS.trans hF))⟩

theorem dft_cyclicMultiplicativeConvolution_at_zero {q : ℕ} [NeZero q]
    (f g : ZMod q → ℂ) :
    ZMod.dft (cyclicMultiplicativeConvolution f g) 0 = ZMod.dft f 0 * ZMod.dft g 0 := by
  rw [dft_cyclicMultiplicativeConvolution]
  simp only [mul_zero, ← Finset.sum_mul, ZMod.dft_apply_zero]
  ring

theorem dft_cyclicProductPow_at_zero {q : ℕ} [NeZero q]
    (f : ZMod q → ℂ) (r : ℕ) : ZMod.dft (cyclicProductPow f r) 0 = (ZMod.dft f 0) ^ r := by
  induction r with
  | zero => simp [cyclicProductPow, ZMod.dft_apply_zero]
  | succ r ih =>
    rw [cyclicProductPow, dft_cyclicMultiplicativeConvolution_at_zero, ih, pow_succ]
    ring

theorem dft_cyclicBernoulliSmooth_at_zero {q : ℕ} [NeZero q] (f : ZMod q → ℂ) :
    ZMod.dft (cyclicBernoulliSmooth f) 0 = ZMod.dft f 0 := by
  rw [dft_cyclicBernoulliSmooth]
  simp

theorem cyclicBernoulliSmooth_support_representatives {q F u H : ℕ} [NeZero q]
    (f : ZMod q → ℂ)
    (hf : ∀ x, f x ≠ 0 → ∃ S : ℕ,
      S ≤ H ∧ (S : ZMod q) = x ∧ HasFactorialDivisorMultiset F S u) :
    ∀ x, cyclicBernoulliSmooth f x ≠ 0 → ∃ S : ℕ,
      S ≤ H + 1 ∧ (S : ZMod q) = x ∧ HasFactorialDivisorMultiset F S (u + 1) := by
  intro x hx
  by_cases hfx : f x = 0
  · have hother : f (x - 1) ≠ 0 := by
      intro h
      simp only [cyclicBernoulliSmooth, hfx, h, add_zero, zero_div, ne_eq, not_true_eq_false] at hx
    obtain ⟨S, hS, hScast, hrep⟩ := hf (x - 1) hother
    refine ⟨S + 1, Nat.add_le_add_right hS 1, ?_, ?_⟩
    · rw [Nat.cast_add, Nat.cast_one, hScast, sub_add_cancel]
    · exact factorial_multiset_add hrep (factorial_multiset_singleton (one_dvd _))
  · obtain ⟨S, hS, hScast, hrep⟩ := hf x hfx
    exact ⟨S, by omega, hScast, factorial_multiset_mono hrep le_rfl (by omega)⟩

theorem dft_smooth_product_zero_at_low_conductor {K b r : ℕ}
    (f : ZMod (2 ^ K) → ℂ) (hr : 0 < r)
    (hu : ∀ x, f x ≠ 0 → IsUnit x)
    (hf : ∀ x, 2 ≤ dyadicConductorLevel x → dyadicConductorLevel x ≤ b → ZMod.dft f x = 0)
    {k : ZMod (2 ^ K)} (hk : k ≠ 0) (hkhi : dyadicConductorLevel k ≤ b) :
    ZMod.dft (cyclicBernoulliSmooth (cyclicProductPow f r)) k = 0 := by
  by_cases hklo : 2 ≤ dyadicConductorLevel k
  · rw [dft_cyclicBernoulliSmooth, dft_cyclicProductPow_zero f hr hu hf hklo hkhi, zero_mul]
  · have hlevel : dyadicConductorLevel k = 1 := by
      have := dyadic_conductor_pos hk
      omega
    apply dft_cyclicBernoulliSmooth_zero _ hk
    have horder : addOrderOf k = 2 := by simpa only [hlevel, pow_one] using (dyadic_conductor_spec k).2
    simpa only [horder, nsmul_eq_mul, Nat.cast_ofNat] using addOrderOf_nsmul_eq_zero k

theorem exists_power_modular_representatives_of_product_decay {t : ℝ} (ht : 0 < t) :
    ∃ s : ℕ, 0 < s ∧ ∀ K b r F u : ℕ, 0 < r →
      ∀ f : ZMod (2 ^ K) → ℂ,
      ZMod.dft f 0 = 1 →
      (∀ x, f x ≠ 0 → IsUnit x) →
      (∀ x, 2 ≤ dyadicConductorLevel x → dyadicConductorLevel x ≤ b → ZMod.dft f x = 0) →
      (∀ x, b < dyadicConductorLevel x →
        ‖ZMod.dft (cyclicProductPow f r) x‖ ≤ (2 : ℝ) ^ (-t * (dyadicConductorLevel x : ℝ))) →
      (∀ x, f x ≠ 0 → ∃ S : ℕ,
        S ≤ 2 ^ K ∧ (S : ZMod (2 ^ K)) = x ∧ HasFactorialDivisorMultiset F S u) →
      2 * s ≤ 2 ^ K →
      HasBoundedModularRepresentatives (2 ^ K) (r * F) (s * (u ^ r + 1)) (r + 1) := by
  obtain ⟨s, hspos, hspower⟩ := exists_convolution_power_for_dyadic_decay ht
  refine ⟨s, hspos, ?_⟩
  intro K b r F u hr f hzero hunits hlow hhigh hsupport hheight
  let g := cyclicBernoulliSmooth (cyclicProductPow f r)
  have hdecay : ∀ x : ZMod (2 ^ K), x ≠ 0 →
      ‖ZMod.dft g x‖ ≤ (2 : ℝ) ^ (-t * (dyadicConductorLevel x : ℝ)) := by
    intro x hx
    by_cases hxlo : dyadicConductorLevel x ≤ b
    · have hz := dft_smooth_product_zero_at_low_conductor f hr hunits hlow hx hxlo
      change ‖ZMod.dft (cyclicBernoulliSmooth (cyclicProductPow f r)) x‖ ≤ _
      rw [hz, norm_zero]
      positivity
    · exact (norm_dft_cyclicBernoulliSmooth_le _ x).trans (hhigh x (by omega))
  have hgzero : ZMod.dft g 0 = 1 := by
    change ZMod.dft (cyclicBernoulliSmooth (cyclicProductPow f r)) 0 = 1
    rw [dft_cyclicBernoulliSmooth_at_zero, dft_cyclicProductPow_at_zero, hzero, one_pow]
  have hgsupport := cyclicBernoulliSmooth_support_representatives (cyclicProductPow f r)
    (cyclicProductPow_support_representatives f hsupport r)
  apply bounded_modular_representatives_of_fourier g hgzero (hspower K g hdecay) hgsupport
  have hqpow : 1 ≤ (2 ^ K) ^ r := Nat.one_le_pow r (2 ^ K) (by positivity)
  calc
    s * ((2 ^ K) ^ r + 1) ≤ s * (2 * (2 ^ K) ^ r) := Nat.mul_le_mul_left s (by omega)
    _ = (2 * s) * (2 ^ K) ^ r := by ring
    _ ≤ (2 ^ K) * (2 ^ K) ^ r := Nat.mul_le_mul_right _ hheight
    _ = (2 ^ K) ^ (r + 1) := (pow_succ' _ _).symm

def shortFactorialDigits (F l : ℕ) : Finset ℕ :=
  insert 0 (F.factorial.divisors.filter (fun d => d < 2 ^ l))

theorem mem_shortFactorialDigits {F l d : ℕ} :
    d ∈ shortFactorialDigits F l ↔ d < 2 ^ l ∧ (d = 0 ∨ d ∣ F.factorial) := by
  constructor
  · intro h
    rcases Finset.mem_insert.mp h with hz | hd
    · exact ⟨by rw [hz]; positivity, Or.inl hz⟩
    · obtain ⟨hdiv, hlt⟩ := Finset.mem_filter.mp hd
      exact ⟨hlt, Or.inr (Nat.dvd_of_mem_divisors hdiv)⟩
  · rintro ⟨hlt, hz | hdvd⟩
    · exact Finset.mem_insert.mpr (Or.inl hz)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr
        ⟨Nat.mem_divisors.mpr ⟨hdvd, Nat.factorial_ne_zero F⟩, hlt⟩))

theorem shortFactorialDigits_small_integers {F l : ℕ} :
    min (F + 1) (2 ^ l) ≤ (shortFactorialDigits F l).card := by
  have hsub : Finset.range (min (F + 1) (2 ^ l)) ⊆ shortFactorialDigits F l := by
    intro d hd
    have hdlt := Finset.mem_range.mp hd
    apply mem_shortFactorialDigits.mpr
    refine ⟨lt_of_lt_of_le hdlt (min_le_right _ _), ?_⟩
    by_cases hz : d = 0
    · exact Or.inl hz
    · exact Or.inr (Nat.dvd_factorial (by omega)
        (by have := min_le_left (F + 1) (2 ^ l); omega))
  simpa only [Finset.card_range] using Finset.card_le_card hsub

theorem prime_dvd_prime_product_iff {p : ℕ} (hp : Nat.Prime p)
    (s : Finset ℕ) (hs : ∀ q ∈ s, Nat.Prime q) :
    p ∣ s.prod id ↔ p ∈ s := by
  constructor
  · intro h
    obtain ⟨q, hq, hpq⟩ := (hp.prime.dvd_finsetProd_iff id).mp h
    have heq : q = p := (hs q hq).dvd_iff_eq hp.ne_one |>.mp hpq
    exact heq ▸ hq
  · exact Finset.dvd_prod_of_mem id

theorem prime_products_injective {s t : Finset ℕ}
    (hs : ∀ p ∈ s, Nat.Prime p) (ht : ∀ p ∈ t, Nat.Prime p)
    (heq : s.prod id = t.prod id) : s = t := by
  apply Finset.Subset.antisymm
  · intro p hp
    apply (prime_dvd_prime_product_iff (hs p hp) t ht).mp
    rw [← heq]
    exact Finset.dvd_prod_of_mem id hp
  · intro p hp
    apply (prime_dvd_prime_product_iff (ht p hp) s hs).mp
    rw [heq]
    exact Finset.dvd_prod_of_mem id hp

theorem prime_subset_product_dvd_factorial {F : ℕ} {s : Finset ℕ}
    (hs : s ⊆ Nat.primesLE F) : s.prod id ∣ F.factorial := by
  rw [← Finset.prod_Ico_id_eq_factorial F]
  apply Finset.prod_dvd_prod_of_subset s (Finset.Ico 1 (F + 1)) id
  intro p hp
  obtain ⟨hpF, hprime⟩ := Nat.mem_primesLE.mp (hs hp)
  exact Finset.mem_Ico.mpr ⟨by have := hprime.two_le; omega, by omega⟩

theorem shortFactorialDigits_choose_lower {F l v : ℕ} (hheight : F ^ v < 2 ^ l) :
    (Nat.primeCounting F).choose v ≤ (shortFactorialDigits F l).card := by
  have hmap : Set.MapsTo (fun s : Finset ℕ => s.prod id)
      ((Nat.primesLE F).powersetCard v) (shortFactorialDigits F l) := by
    intro s hs
    obtain ⟨hs, hcard⟩ := Finset.mem_powersetCard.mp hs
    apply mem_shortFactorialDigits.mpr
    refine ⟨?_, Or.inr (prime_subset_product_dvd_factorial hs)⟩
    have hprod : s.prod id ≤ F ^ v := by
      calc
        s.prod id ≤ ∏ _ ∈ s, F := Finset.prod_le_prod' (fun p hp => Nat.le_of_mem_primesLE (hs hp))
        _ = F ^ v := by rw [Finset.prod_const, hcard]
    exact hprod.trans_lt hheight
  have hinj : Set.InjOn (fun s : Finset ℕ => s.prod id) ((Nat.primesLE F).powersetCard v) := by
    intro s hs t ht heq
    apply prime_products_injective _ _ heq
    · intro p hp
      exact Nat.prime_of_mem_primesLE ((Finset.mem_powersetCard.mp hs).1 hp)
    · intro p hp
      exact Nat.prime_of_mem_primesLE ((Finset.mem_powersetCard.mp ht).1 hp)
  simpa only [Finset.card_powersetCard, Nat.primesLE_card_eq_primeCounting] using
    Finset.card_le_card_of_injOn _ hmap hinj

theorem choose_lower_half_ratio {n v : ℕ} (hv : 0 < v) (hvn : 2 * v ≤ n) :
    ((n : ℝ) / 2 / (v : ℝ)) ^ v ≤ (n.choose v : ℝ) := by
  have hvpos : (0 : ℝ) < v := by exact_mod_cast hv
  have hnsub : (n : ℝ) / 2 ≤ ((n + 1 - v : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : v ≤ n + 1), Nat.cast_add, Nat.cast_one]
    have hh : (2 : ℝ) * v ≤ n := by exact_mod_cast hvn
    linarith
  have hfac : (v.factorial : ℝ) ≤ (v : ℝ) ^ v := by exact_mod_cast Nat.factorial_le_pow v
  calc
    ((n : ℝ) / 2 / (v : ℝ)) ^ v = ((n : ℝ) / 2) ^ v / (v : ℝ) ^ v := div_pow _ _ _
    _ ≤ (((n + 1 - v : ℕ) : ℝ) ^ v) / (v : ℝ) ^ v := by
      exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (by positivity) hnsub v) (by positivity)
    _ ≤ (((n + 1 - v : ℕ) : ℝ) ^ v) / (v.factorial : ℝ) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hfac
    _ ≤ (n.choose v : ℝ) := Nat.pow_le_choose v n

theorem eventually_primeCounting_ge_rpow {σ : ℝ} (hσ : σ < 1) :
    ∀ᶠ n : ℕ in Filter.atTop, (n : ℝ) ^ σ ≤ (Nat.primeCounting n : ℝ) := by
  have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog := (isLittleO_log_rpow_atTop (sub_pos.mpr hσ)).comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp
    (Real.isLittleO_log_id_atTop.def (by positivity : (0 : ℝ) < Real.log 2 / 4))
  filter_upwards [hlog.def (by positivity : (0 : ℝ) < Real.log 2 / 2),
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop M,
    eventually_ge_atTop (2 : ℕ)] with n hn hnM hn2
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hlogn : Real.log (n : ℝ) ≤ (Real.log 2 / 2) * (n : ℝ) ^ (1 - σ) := by
    have hh : |Real.log (n : ℝ)| ≤ (Real.log 2 / 2) * (n : ℝ) ^ (1 - σ) := by
      simpa only [Function.comp_apply, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) (1 - σ))] using hn
    exact (le_abs_self _).trans hh
  have hlognext : Real.log ((n : ℝ) + 1) ≤ (Real.log 2 / 2) * n := by
    have hh := hM ((n : ℝ) + 1) (by linarith)
    have hh' : |Real.log ((n : ℝ) + 1)| ≤ (Real.log 2 / 4) * ((n : ℝ) + 1) := by
      simpa only [id_eq, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ n + 1)] using hh
    have hle := (le_abs_self _).trans hh'
    nlinarith
  have hpi := Chebyshev.pi_ge n
  have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
  have hmain := (div_le_iff₀ hlogpos).mp hpi
  apply (mul_le_mul_iff_left₀
    (show 0 < (Real.log 2 / 2) * (n : ℝ) ^ (1 - σ) by positivity)).mp
  calc
    (n : ℝ) ^ σ * ((Real.log 2 / 2) * (n : ℝ) ^ (1 - σ)) = (Real.log 2 / 2) * n := by
      rw [mul_comm ((n : ℝ) ^ σ)]
      rw [mul_assoc, ← Real.rpow_add hnpos, sub_add_cancel, Real.rpow_one]
    _ ≤ (Nat.primeCounting n : ℝ) * Real.log (n : ℝ) := by linarith
    _ ≤ (Nat.primeCounting n : ℝ) * ((Real.log 2 / 2) * (n : ℝ) ^ (1 - σ)) :=
      mul_le_mul_of_nonneg_left hlogn (Nat.cast_nonneg _)

theorem half_binaryLength_rpow_le {F : ℕ} (hF : 2 ≤ F) :
    (2 : ℝ) ^ ((binaryLength F : ℝ) / 2) ≤ (F : ℝ) := by
  have hlog : 1 ≤ Nat.log 2 F := Nat.le_log_of_pow_le (by decide) (by simpa using hF)
  have hlen : (binaryLength F : ℝ) / 2 ≤ (Nat.log 2 F : ℝ) := by
    simp only [binaryLength, Nat.cast_add, Nat.cast_one]
    have hh : (1 : ℝ) ≤ Nat.log 2 F := by exact_mod_cast hlog
    linarith
  calc
    (2 : ℝ) ^ ((binaryLength F : ℝ) / 2) ≤ (2 : ℝ) ^ (Nat.log 2 F : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hlen
    _ = ((2 ^ Nat.log 2 F : ℕ) : ℝ) := by simp
    _ ≤ (F : ℝ) := by exact_mod_cast Nat.pow_log_le_self 2 (by omega : F ≠ 0)

theorem shortFactorialDigits_uniform_lower {F k : ℕ} {δ : ℝ}
    (hF : 2 ≤ F) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hprimes : (2 * (k : ℝ)) * (F : ℝ) ^ δ ≤ (Nat.primeCounting F : ℝ)) :
    ∀ l : ℕ, 1 ≤ l → l ≤ k →
      (2 : ℝ) ^ (δ * (l : ℝ) / 8) ≤ (shortFactorialDigits F l).card := by
  intro l hlpos hlk
  let a := binaryLength F
  have ha : 0 < a := binaryLength_pos F
  have hFa : (2 : ℝ) ^ ((a : ℝ) / 2) ≤ (F : ℝ) := half_binaryLength_rpow_le hF
  by_cases hsmall : l ≤ 4 * a
  · have hsmallreal : (l : ℝ) ≤ 4 * (a : ℝ) := by exact_mod_cast hsmall
    have hfirst : (2 : ℝ) ^ (δ * (l : ℝ) / 8) ≤ (F + 1 : ℕ) := by
      calc
        (2 : ℝ) ^ (δ * (l : ℝ) / 8) ≤ (2 : ℝ) ^ ((a : ℝ) / 2) := by
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
          nlinarith [mul_le_mul_of_nonneg_right hδ1 (Nat.cast_nonneg l : (0 : ℝ) ≤ l)]
        _ ≤ (F : ℝ) := hFa
        _ ≤ (F + 1 : ℕ) := by exact_mod_cast Nat.le_succ F
    have hsecond : (2 : ℝ) ^ (δ * (l : ℝ) / 8) ≤ ((2 ^ l : ℕ) : ℝ) := by
      rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      nlinarith [mul_le_mul_of_nonneg_right hδ1 (Nat.cast_nonneg l : (0 : ℝ) ≤ l)]
    have hmin : (2 : ℝ) ^ (δ * (l : ℝ) / 8) ≤ (min (F + 1) (2 ^ l) : ℕ) := by
      rw [Nat.cast_min]
      exact le_min hfirst hsecond
    exact hmin.trans (by exact_mod_cast shortFactorialDigits_small_integers (F := F) (l := l))
  · let v := l / (2 * a)
    have hvpos : 0 < v := Nat.div_pos (by omega) (by omega)
    have hvle : v ≤ k := (Nat.div_le_self l (2 * a)).trans hlk
    have hmul : 2 * a * v ≤ l := Nat.mul_div_le l (2 * a)
    have hupper : l < 2 * a * (v + 1) := Nat.lt_mul_div_succ l (by omega)
    have halower : l ≤ 4 * a * v := by nlinarith
    have hheight : F ^ v < 2 ^ l := by
      calc
        F ^ v ≤ (2 ^ a) ^ v := Nat.pow_le_pow_left
          (Nat.lt_pow_succ_log_self (by decide : 1 < 2) F).le v
        _ = 2 ^ (a * v) := (pow_mul _ _ _).symm
        _ < 2 ^ l := Nat.pow_lt_pow_right (by decide : 1 < 2) (by nlinarith)
    have hFpow : 1 ≤ (F : ℝ) ^ δ := Real.one_le_rpow (by exact_mod_cast (show 1 ≤ F by omega)) hδ.le
    have htwov : 2 * v ≤ Nat.primeCounting F := by
      have hkr : (v : ℝ) ≤ k := by exact_mod_cast hvle
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      have hreal : 2 * (v : ℝ) ≤ (Nat.primeCounting F : ℝ) := by nlinarith
      exact_mod_cast hreal
    have hratio : (F : ℝ) ^ δ ≤ (Nat.primeCounting F : ℝ) / 2 / (v : ℝ) := by
      apply (le_div_iff₀ (by exact_mod_cast hvpos : (0 : ℝ) < v)).mpr
      apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
      have hkr : (v : ℝ) ≤ k := by exact_mod_cast hvle
      have hF0 : 0 ≤ (F : ℝ) ^ δ := by positivity
      nlinarith [mul_le_mul_of_nonneg_right hkr hF0]
    have halowerreal : (l : ℝ) ≤ 4 * (a : ℝ) * (v : ℝ) := by exact_mod_cast halower
    calc
      (2 : ℝ) ^ (δ * (l : ℝ) / 8) ≤ (2 : ℝ) ^ (((a : ℝ) / 2 * δ) * (v : ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        nlinarith [mul_le_mul_of_nonneg_left halowerreal hδ.le]
      _ = (((2 : ℝ) ^ ((a : ℝ) / 2)) ^ δ) ^ v := by
        rw [Real.rpow_mul_natCast (by norm_num), Real.rpow_mul (by norm_num)]
      _ ≤ ((F : ℝ) ^ δ) ^ v :=
        pow_le_pow_left₀ (by positivity) (Real.rpow_le_rpow (by positivity) hFa hδ.le) v
      _ ≤ ((Nat.primeCounting F : ℝ) / 2 / (v : ℝ)) ^ v :=
        pow_le_pow_left₀ (by positivity) hratio v
      _ ≤ ((Nat.primeCounting F).choose v : ℝ) := choose_lower_half_ratio hvpos htwov
      _ ≤ (shortFactorialDigits F l).card := by exact_mod_cast shortFactorialDigits_choose_lower hheight

noncomputable def factorialDigitHost (a : ℝ) (k : ℕ) : ℕ := ⌈(k : ℝ) ^ a⌉₊

theorem factorialDigitHost_tendsto {a : ℝ} (ha : 0 < a) :
    Filter.Tendsto (factorialDigitHost a) Filter.atTop Filter.atTop := by
  have hp := (tendsto_rpow_atTop ha).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  apply Filter.tendsto_atTop.mpr
  intro M
  filter_upwards [hp.eventually_ge_atTop (M : ℝ)] with k hk
  have hh : (M : ℝ) ≤ (k : ℝ) ^ a := hk
  exact_mod_cast hh.trans (Nat.le_ceil _)

theorem factorialDigitHost_le {a : ℝ} {k : ℕ} (ha : 0 ≤ a) (hk : 1 ≤ k) :
    (factorialDigitHost a k : ℝ) ≤ 2 * (k : ℝ) ^ a := by
  have hone : 1 ≤ (k : ℝ) ^ a := Real.one_le_rpow (by exact_mod_cast hk) ha
  have hceil := Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg k) a)
  change (⌈(k : ℝ) ^ a⌉₊ : ℝ) ≤ _
  linarith

theorem shortFactorialDigits_uniform_asymptotic {a : ℝ} (ha : 1 < a) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ k : ℕ in Filter.atTop,
      (factorialDigitHost a k : ℝ) ≤ 2 * (k : ℝ) ^ a ∧
      ∀ l : ℕ, 1 ≤ l → l ≤ k →
        (2 : ℝ) ^ (c * (l : ℝ)) ≤ (shortFactorialDigits (factorialDigitHost a k) l).card := by
  let δ : ℝ := (a - 1) / (4 * a)
  let σ : ℝ := 1 - δ
  have hapos : 0 < a := by linarith
  have hδ : 0 < δ := div_pos (by linarith) (by positivity)
  have hδquarter : δ ≤ 1 / 4 := by
    dsimp [δ]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * a)).mpr
    linarith
  have hδeq : 4 * a * δ = a - 1 := by
    dsimp [δ]
    field_simp
  have hσ : σ < 1 := by dsimp [σ]; linarith
  have hgap : 0 < σ - δ := by dsimp [σ]; linarith
  have hexponent : 1 < a * (σ - δ) := by
    dsimp [σ]
    nlinarith
  have hhost := factorialDigitHost_tendsto hapos
  have hprime := hhost.eventually (eventually_primeCounting_ge_rpow hσ)
  have hpower := eventually_const_mul_rpow_le (C := 2) (E := 1) hexponent (by norm_num)
  refine ⟨δ / 8, by positivity, ?_⟩
  filter_upwards [hprime, hpower, hhost.eventually_ge_atTop 2, eventually_ge_atTop (1 : ℕ)]
    with k hkprime hkpower hkhost hkone
  refine ⟨factorialDigitHost_le hapos.le hkone, ?_⟩
  have hFpos : (0 : ℝ) < factorialDigitHost a k := by exact_mod_cast (show 0 < factorialDigitHost a k by omega)
  have h2k : 2 * (k : ℝ) ≤ (factorialDigitHost a k : ℝ) ^ (σ - δ) := by
    calc
      2 * (k : ℝ) ≤ (k : ℝ) ^ (a * (σ - δ)) := by
        simpa only [Real.rpow_one, one_mul] using hkpower
      _ = ((k : ℝ) ^ a) ^ (σ - δ) := Real.rpow_mul (Nat.cast_nonneg k) _ _
      _ ≤ (factorialDigitHost a k : ℝ) ^ (σ - δ) :=
        Real.rpow_le_rpow (by positivity) (Nat.le_ceil _) hgap.le
  have hprimes : (2 * (k : ℝ)) * (factorialDigitHost a k : ℝ) ^ δ ≤
      (Nat.primeCounting (factorialDigitHost a k) : ℝ) := by
    calc
      _ ≤ (factorialDigitHost a k : ℝ) ^ (σ - δ) * (factorialDigitHost a k : ℝ) ^ δ :=
        mul_le_mul_of_nonneg_right h2k (by positivity)
      _ = (factorialDigitHost a k : ℝ) ^ σ := by rw [← Real.rpow_add hFpos, sub_add_cancel]
      _ ≤ _ := hkprime
  intro l hl hlk
  have hh := shortFactorialDigits_uniform_lower hkhost hδ (by linarith : δ ≤ 1) hprimes l hl hlk
  convert hh using 1
  congr 1
  ring

def binaryAppend (A D : Finset ℕ) (b : ℕ) : Finset ℕ :=
  (A ×ˢ D).image (fun p => p.1 + 2 ^ b * p.2)

def natResidueFiber (A : Finset ℕ) (q r : ℕ) : Finset ℕ :=
  A.filter (fun x => Nat.ModEq q x r)

noncomputable def natResidueMass (A : Finset ℕ) (q r : ℕ) : ℝ :=
  ((natResidueFiber A q r).card : ℝ) / (A.card : ℝ)

theorem binary_append_injective {A D : Finset ℕ} {b : ℕ}
    (hA : ∀ x ∈ A, x < 2 ^ b) :
    Set.InjOn (fun p : ℕ × ℕ => p.1 + 2 ^ b * p.2) (A ×ˢ D : Finset (ℕ × ℕ)) := by
  intro p hp s hs heq
  change p.1 + 2 ^ b * p.2 = s.1 + 2 ^ b * s.2 at heq
  have hpA := hA p.1 (Finset.mem_product.mp hp).1
  have hsA := hA s.1 (Finset.mem_product.mp hs).1
  have hmod := congrArg (fun n => n % (2 ^ b)) heq
  simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hpA, Nat.mod_eq_of_lt hsA] at hmod
  have hmul : 2 ^ b * p.2 = 2 ^ b * s.2 := by omega
  have hright := Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2 ^ b) hmul
  exact Prod.ext hmod hright

theorem binary_append_card {A D : Finset ℕ} {b : ℕ}
    (hA : ∀ x ∈ A, x < 2 ^ b) : (binaryAppend A D b).card = A.card * D.card := by
  rw [binaryAppend, Finset.card_image_of_injOn (binary_append_injective hA), Finset.card_product]

theorem binary_append_nonempty {A D : Finset ℕ} {b : ℕ}
    (hA : A.Nonempty) (hD : D.Nonempty) : (binaryAppend A D b).Nonempty := by
  exact (hA.product hD).image _

theorem binary_append_lt {A D : Finset ℕ} {b l : ℕ}
    (hA : ∀ x ∈ A, x < 2 ^ b) (hD : ∀ d ∈ D, d < 2 ^ l) :
    ∀ x ∈ binaryAppend A D b, x < 2 ^ (b + l) := by
  intro x hx
  obtain ⟨⟨a, d⟩, had, rfl⟩ := Finset.mem_image.mp hx
  have ha := hA a (Finset.mem_product.mp had).1
  have hd := hD d (Finset.mem_product.mp had).2
  rw [pow_add]
  nlinarith [mul_le_mul_of_nonneg_left (show d + 1 ≤ 2 ^ l by omega) (Nat.zero_le (2 ^ b))]

theorem nat_residue_fiber_mono_modulus {A : Finset ℕ} {q Q r : ℕ} (hq : q ∣ Q) :
    natResidueFiber A Q r ⊆ natResidueFiber A q r := by
  intro x hx
  obtain ⟨hx, hmod⟩ := Finset.mem_filter.mp hx
  exact Finset.mem_filter.mpr ⟨hx, hmod.of_dvd hq⟩

theorem nat_residue_fiber_card_le_one {A : Finset ℕ} {q r : ℕ}
    (hA : ∀ x ∈ A, x < q) : (natResidueFiber A q r).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro x hx y hy
  obtain ⟨hxA, hxmod⟩ := Finset.mem_filter.mp hx
  obtain ⟨hyA, hymod⟩ := Finset.mem_filter.mp hy
  have hxy := hxmod.trans hymod.symm
  simpa only [Nat.ModEq, Nat.mod_eq_of_lt (hA x hxA), Nat.mod_eq_of_lt (hA y hyA)] using hxy

theorem binary_append_residue_fiber {A D : Finset ℕ} {b q r : ℕ} (hq : q ∣ 2 ^ b) :
    natResidueFiber (binaryAppend A D b) q r = binaryAppend (natResidueFiber A q r) D b := by
  have hequiv (a d : ℕ) : Nat.ModEq q (a + 2 ^ b * d) r ↔ Nat.ModEq q a r := by
    have hh : Nat.ModEq q (a + 2 ^ b * d) a := by
      simpa only [add_zero] using (Nat.ModEq.refl a).add ((hq.trans (dvd_mul_right _ _)).modEq_zero_nat)
    exact ⟨fun h => hh.symm.trans h, fun h => hh.trans h⟩
  ext x
  constructor
  · intro hx
    obtain ⟨hx, hm⟩ := Finset.mem_filter.mp hx
    obtain ⟨⟨a, d⟩, had, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr ⟨(a, d), Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr ⟨(Finset.mem_product.mp had).1, (hequiv a d).mp hm⟩,
        (Finset.mem_product.mp had).2⟩, rfl⟩
  · intro hx
    obtain ⟨⟨a, d⟩, had, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨ha, hd⟩ := Finset.mem_product.mp had
    obtain ⟨ha, hm⟩ := Finset.mem_filter.mp ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨(a, d), Finset.mem_product.mpr ⟨ha, hd⟩, rfl⟩,
      (hequiv a d).mpr hm⟩

theorem binary_append_residue_fiber_card {A D : Finset ℕ} {b q r : ℕ}
    (hA : ∀ x ∈ A, x < 2 ^ b) (hq : q ∣ 2 ^ b) :
    (natResidueFiber (binaryAppend A D b) q r).card = (natResidueFiber A q r).card * D.card := by
  rw [binary_append_residue_fiber hq]
  exact binary_append_card (fun x hx => hA x (Finset.mem_filter.mp hx).1)

theorem binary_append_residue_mass {A D : Finset ℕ} {b q r : ℕ}
    (hA : ∀ x ∈ A, x < 2 ^ b) (hD : D.Nonempty) (hq : q ∣ 2 ^ b) :
    natResidueMass (binaryAppend A D b) q r = natResidueMass A q r := by
  have hDc : (D.card : ℝ) ≠ 0 := by exact_mod_cast Finset.card_ne_zero.mpr hD
  unfold natResidueMass
  rw [binary_append_residue_fiber_card hA hq, binary_append_card hA, Nat.cast_mul, Nat.cast_mul]
  exact mul_div_mul_right _ _ hDc

theorem binary_append_residue_mass_high {A D : Finset ℕ} {b j r : ℕ}
    (hA : ∀ x ∈ A, x < 2 ^ b) (hne : A.Nonempty) (hD : D.Nonempty) (hj : b ≤ j) :
    natResidueMass (binaryAppend A D b) (2 ^ j) r ≤ 1 / (A.card : ℝ) := by
  have hAc : (0 : ℝ) < A.card := by exact_mod_cast Finset.card_pos.mpr hne
  calc
    natResidueMass (binaryAppend A D b) (2 ^ j) r ≤
        natResidueMass (binaryAppend A D b) (2 ^ b) r := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact_mod_cast Finset.card_le_card (nat_residue_fiber_mono_modulus (pow_dvd_pow 2 hj))
    _ = natResidueMass A (2 ^ b) r := binary_append_residue_mass hA hD (dvd_refl _)
    _ ≤ 1 / (A.card : ℝ) := by
      apply div_le_div_of_nonneg_right _ hAc.le
      exact_mod_cast nat_residue_fiber_card_le_one hA

theorem nat_residue_fiber_range_card_le {q N r : ℕ} (hq : 0 < q) :
    (natResidueFiber (Finset.range (q * N)) q r).card ≤ N := by
  have hmap : Set.MapsTo (fun x : ℕ => x / q)
      (natResidueFiber (Finset.range (q * N)) q r) (Finset.range N) := by
    intro x hx
    have hxlt := Finset.mem_range.mp (Finset.mem_filter.mp hx).1
    exact Finset.mem_range.mpr ((Nat.div_lt_iff_lt_mul hq).mpr (by simpa only [mul_comm] using hxlt))
  have hinj : Set.InjOn (fun x : ℕ => x / q)
      (natResidueFiber (Finset.range (q * N)) q r) := by
    intro x hx y hy heq
    change x / q = y / q at heq
    have hmod := (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm
    change x % q = y % q at hmod
    have hxdiv := Nat.mod_add_div x q
    have hydiv := Nat.mod_add_div y q
    rw [heq, hmod] at hxdiv
    omega
  simpa only [Finset.card_range] using Finset.card_le_card_of_injOn _ hmap hinj

theorem nat_residue_fiber_bounded_card_le {A : Finset ℕ} {b j r : ℕ}
    (hA : ∀ x ∈ A, x < 2 ^ b) (hj : j ≤ b) :
    (natResidueFiber A (2 ^ j) r).card ≤ 2 ^ (b - j) := by
  have hpow : 2 ^ b = 2 ^ j * 2 ^ (b - j) := by rw [← pow_add, Nat.add_sub_of_le hj]
  have hsub : natResidueFiber A (2 ^ j) r ⊆ natResidueFiber (Finset.range (2 ^ b)) (2 ^ j) r := by
    intro x hx
    obtain ⟨hxA, hmod⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hA x hxA), hmod⟩
  refine (Finset.card_le_card hsub).trans ?_
  rw [hpow]
  exact nat_residue_fiber_range_card_le (by positivity)

def initialOddDigits (b : ℕ) : Finset ℕ :=
  (Finset.range (2 ^ (b - 1))).image (fun i => 2 * i + 1)

theorem initial_odd_digits_card (b : ℕ) : (initialOddDigits b).card = 2 ^ (b - 1) := by
  rw [initialOddDigits, Finset.card_image_of_injective]
  · exact Finset.card_range _
  · intro x y h
    change 2 * x + 1 = 2 * y + 1 at h
    omega

theorem initial_odd_digits_nonempty (b : ℕ) : (initialOddDigits b).Nonempty := by
  apply Finset.card_pos.mp
  rw [initial_odd_digits_card]
  positivity

theorem initial_odd_digits_lt {b : ℕ} (hb : 0 < b) :
    ∀ x ∈ initialOddDigits b, x < 2 ^ b := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
  have hi := Finset.mem_range.mp hi
  have hp : 2 ^ b = 2 * 2 ^ (b - 1) := by rw [← pow_succ', Nat.sub_add_cancel hb]
  rw [hp]
  omega

theorem initial_odd_digits_odd {b x : ℕ} (hx : x ∈ initialOddDigits b) : Odd x := by
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
  exact ⟨i, by ring⟩

theorem initial_odd_digits_entropy {b : ℕ} {c : ℝ} (hb : 2 ≤ b) (hc : c ≤ 1 / 2) :
    (2 : ℝ) ^ (c * (b : ℝ)) ≤ (initialOddDigits b).card := by
  rw [initial_odd_digits_card, Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  rw [Nat.cast_sub (by omega : 1 ≤ b), Nat.cast_one]
  have hbr : (2 : ℝ) ≤ b := by exact_mod_cast hb
  nlinarith [mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg b : (0 : ℝ) ≤ b)]

theorem initial_odd_digits_spread {b j r : ℕ} {c : ℝ}
    (hb : 2 ≤ b) (hj : 2 ≤ j) (hjb : j ≤ b) (hc : c ≤ 1) :
    natResidueMass (initialOddDigits b) (2 ^ j) r ≤ (2 : ℝ) ^ (-(c / 2) * (j : ℝ)) := by
  have hcard := nat_residue_fiber_bounded_card_le (r := r)
    (initial_odd_digits_lt (by omega : 0 < b)) hjb
  unfold natResidueMass
  rw [initial_odd_digits_card]
  calc
    ((natResidueFiber (initialOddDigits b) (2 ^ j) r).card : ℝ) / ((2 ^ (b - 1) : ℕ) : ℝ) ≤
        ((2 ^ (b - j) : ℕ) : ℝ) / ((2 ^ (b - 1) : ℕ) : ℝ) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast hcard
    _ = (2 : ℝ) ^ (1 - (j : ℝ)) := by
      simp only [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast,
        ← Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Nat.cast_sub hjb,
        Nat.cast_sub (by omega : 1 ≤ b), Nat.cast_one]
      congr 1
      ring
    _ ≤ (2 : ℝ) ^ (-(c / 2) * (j : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have hjr : (2 : ℝ) ≤ j := by exact_mod_cast hj
      nlinarith [mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg j : (0 : ℝ) ≤ j)]

theorem binary_append_entropy {A D : Finset ℕ} {b l : ℕ} {c : ℝ}
    (hA : ∀ x ∈ A, x < 2 ^ b)
    (hcA : (2 : ℝ) ^ (c * (b : ℝ)) ≤ A.card)
    (hcD : (2 : ℝ) ^ (c * (l : ℝ)) ≤ D.card) :
    (2 : ℝ) ^ (c * ((b + l : ℕ) : ℝ)) ≤ (binaryAppend A D b).card := by
  rw [binary_append_card hA, Nat.cast_mul, Nat.cast_add, mul_add, Real.rpow_add (by norm_num)]
  exact mul_le_mul hcA hcD (by positivity) (Nat.cast_nonneg _)

theorem binary_append_spread {A D : Finset ℕ} {b l : ℕ} {c : ℝ}
    (hA : ∀ x ∈ A, x < 2 ^ b) (hne : A.Nonempty) (hD : D.Nonempty)
    (hl : l ≤ b) (hc : 0 ≤ c)
    (hcA : (2 : ℝ) ^ (c * (b : ℝ)) ≤ A.card)
    (hspread : ∀ j : ℕ, 2 ≤ j → j ≤ b → ∀ r : ℕ,
      natResidueMass A (2 ^ j) r ≤ (2 : ℝ) ^ (-(c / 2) * (j : ℝ))) :
    ∀ j : ℕ, 2 ≤ j → j ≤ b + l → ∀ r : ℕ,
      natResidueMass (binaryAppend A D b) (2 ^ j) r ≤ (2 : ℝ) ^ (-(c / 2) * (j : ℝ)) := by
  intro j hj hjbl r
  by_cases hjb : j ≤ b
  · rw [binary_append_residue_mass hA hD (pow_dvd_pow 2 hjb)]
    exact hspread j hj hjb r
  · calc
      natResidueMass (binaryAppend A D b) (2 ^ j) r ≤ 1 / (A.card : ℝ) :=
        binary_append_residue_mass_high hA hne hD (by omega)
      _ ≤ 1 / (2 : ℝ) ^ (c * (b : ℝ)) :=
        one_div_le_one_div_of_le (by positivity) hcA
      _ = (2 : ℝ) ^ (-(c * (b : ℝ))) := by rw [Real.rpow_neg (by norm_num), one_div]
      _ ≤ (2 : ℝ) ^ (-(c / 2) * (j : ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        have hltwo : (j : ℝ) ≤ 2 * (b : ℝ) := by exact_mod_cast (show j ≤ 2 * b by omega)
        nlinarith [mul_le_mul_of_nonneg_left hltwo hc]

theorem short_factorial_digits_nonempty (F l : ℕ) : (shortFactorialDigits F l).Nonempty := by
  exact ⟨0, Finset.mem_insert_self _ _⟩

theorem short_factorial_digits_entropy {F K : ℕ} {c : ℝ}
    (h : ∀ l : ℕ, 1 ≤ l → l ≤ K → (2 : ℝ) ^ (c * (l : ℝ)) ≤ (shortFactorialDigits F l).card)
    {l : ℕ} (hl : l ≤ K) : (2 : ℝ) ^ (c * (l : ℝ)) ≤ (shortFactorialDigits F l).card := by
  by_cases hz : l = 0
  · subst l
    simp only [Nat.cast_zero, mul_zero, Real.rpow_zero]
    exact_mod_cast Finset.card_pos.mpr (short_factorial_digits_nonempty F 0)
  · exact h l (by omega) hl

theorem binary_append_odd {A D : Finset ℕ} {b : ℕ} (hb : 0 < b)
    (hA : ∀ x ∈ A, Odd x) : ∀ x ∈ binaryAppend A D b, Odd x := by
  intro x hx
  obtain ⟨⟨a, d⟩, had, rfl⟩ := Finset.mem_image.mp hx
  exact (hA a (Finset.mem_product.mp had).1).add_even
    ((even_two.pow_of_ne_zero (Nat.ne_of_gt hb)).mul_right d)

theorem binary_append_representations {A : Finset ℕ} {F K b l u : ℕ} (hb : b ≤ K)
    (hA : ∀ x ∈ A, HasFactorialDivisorMultiset (F + 2 * K) x u) :
    ∀ x ∈ binaryAppend A (shortFactorialDigits F l) b,
      HasFactorialDivisorMultiset (F + 2 * K) x (u + 1) := by
  intro x hx
  obtain ⟨⟨a, d⟩, had, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨ha, hd⟩ := Finset.mem_product.mp had
  apply factorial_multiset_add (hA a ha)
  rcases (mem_shortFactorialDigits.mp hd).2 with hz | hdiv
  · rw [hz, mul_zero]
    exact factorial_multiset_zero _ _
  · exact factorial_multiset_singleton (shifted_divisor_dvd_factorial hdiv hb)

structure BinaryBlockProfile (F K b u : ℕ) (c : ℝ) (A : Finset ℕ) : Prop where
  nonempty : A.Nonempty
  bounded : ∀ x ∈ A, x < 2 ^ b
  odd : ∀ x ∈ A, Odd x
  representatives : ∀ x ∈ A, HasFactorialDivisorMultiset (F + 2 * K) x u
  entropy : (2 : ℝ) ^ (c * (b : ℝ)) ≤ A.card
  spread : ∀ j : ℕ, 2 ≤ j → j ≤ b → ∀ r : ℕ,
    natResidueMass A (2 ^ j) r ≤ (2 : ℝ) ^ (-(c / 2) * (j : ℝ))

theorem initial_odd_digits_profile {F K b : ℕ} {c : ℝ}
    (hb : 2 ≤ b) (hF : 2 ^ b ≤ F) (hc : c ≤ 1 / 2) :
    BinaryBlockProfile F K b 1 c (initialOddDigits b) := by
  refine ⟨initial_odd_digits_nonempty b, initial_odd_digits_lt (by omega),
    fun _ hx => initial_odd_digits_odd hx, ?_, initial_odd_digits_entropy hb hc, ?_⟩
  · intro x hx
    have hodd := initial_odd_digits_odd hx
    have hpos : 0 < x := by obtain ⟨t, ht⟩ := hodd; omega
    exact factorial_multiset_singleton (Nat.dvd_factorial hpos
      (by have := initial_odd_digits_lt (by omega : 0 < b) x hx; omega))
  · intro j hj hjb r
    exact initial_odd_digits_spread hb hj hjb (by linarith)

theorem binary_append_profile {F K b l u : ℕ} {c : ℝ} {A : Finset ℕ}
    (hA : BinaryBlockProfile F K b u c A) (hb : 0 < b) (hbK : b ≤ K) (hl : l ≤ b) (hc : 0 ≤ c)
    (hD : (2 : ℝ) ^ (c * (l : ℝ)) ≤ (shortFactorialDigits F l).card) :
    BinaryBlockProfile F K (b + l) (u + 1) c (binaryAppend A (shortFactorialDigits F l) b) := by
  refine ⟨binary_append_nonempty hA.nonempty (short_factorial_digits_nonempty F l),
    binary_append_lt hA.bounded (fun _ hd => (mem_shortFactorialDigits.mp hd).1),
    binary_append_odd hb hA.odd, binary_append_representations hbK hA.representatives,
    binary_append_entropy hA.bounded hA.entropy hD, ?_⟩
  exact binary_append_spread hA.bounded hA.nonempty (short_factorial_digits_nonempty F l)
    hl hc hA.entropy hA.spread

def binaryBlockEndpoint (K b₀ i : ℕ) : ℕ := min K (2 ^ i * b₀)

def binaryBlockWidth (K b₀ i : ℕ) : ℕ := binaryBlockEndpoint K b₀ (i + 1) - binaryBlockEndpoint K b₀ i

def binaryBlockSet (F K b₀ : ℕ) : ℕ → Finset ℕ
  | 0 => initialOddDigits b₀
  | i + 1 => binaryAppend (binaryBlockSet F K b₀ i)
      (shortFactorialDigits F (binaryBlockWidth K b₀ i)) (binaryBlockEndpoint K b₀ i)

theorem binary_block_endpoint_zero {K b₀ : ℕ} (hb : b₀ ≤ K) : binaryBlockEndpoint K b₀ 0 = b₀ := by
  simp only [binaryBlockEndpoint, pow_zero, one_mul, min_eq_right hb]

theorem binary_block_endpoint_bounds {K b₀ : ℕ} (hb : b₀ ≤ K) (i : ℕ) :
    b₀ ≤ binaryBlockEndpoint K b₀ i ∧ binaryBlockEndpoint K b₀ i ≤ K := by
  refine ⟨le_min hb ?_, min_le_left _ _⟩
  nlinarith [show 1 ≤ 2 ^ i from Nat.one_le_two_pow]

theorem binary_block_endpoint_mono (K b₀ i : ℕ) :
    binaryBlockEndpoint K b₀ i ≤ binaryBlockEndpoint K b₀ (i + 1) := by
  apply min_le_min_left
  exact Nat.mul_le_mul_right b₀ (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))

theorem binary_block_endpoint_succ_le_twice (K b₀ i : ℕ) :
    binaryBlockEndpoint K b₀ (i + 1) ≤ 2 * binaryBlockEndpoint K b₀ i := by
  unfold binaryBlockEndpoint
  by_cases h : 2 ^ i * b₀ ≤ K
  · rw [min_eq_right h]
    calc
      min K (2 ^ (i + 1) * b₀) ≤ 2 ^ (i + 1) * b₀ := min_le_right _ _
      _ = 2 * (2 ^ i * b₀) := by rw [pow_succ]; ring
  · rw [min_eq_left (by omega : K ≤ 2 ^ i * b₀)]
    exact (min_le_left _ _).trans (by omega)

theorem binary_block_width_add (K b₀ i : ℕ) :
    binaryBlockEndpoint K b₀ i + binaryBlockWidth K b₀ i = binaryBlockEndpoint K b₀ (i + 1) := by
  exact Nat.add_sub_of_le (binary_block_endpoint_mono K b₀ i)

theorem binary_block_width_le (K b₀ i : ℕ) :
    binaryBlockWidth K b₀ i ≤ binaryBlockEndpoint K b₀ i := by
  have := binary_block_endpoint_succ_le_twice K b₀ i
  unfold binaryBlockWidth
  omega

theorem binary_block_endpoint_top {K b₀ : ℕ} (hb : 1 ≤ b₀) :
    binaryBlockEndpoint K b₀ (binaryLength K) = K := by
  apply min_eq_left
  have hK : K < 2 ^ binaryLength K := Nat.lt_pow_succ_log_self (by decide : 1 < 2) K
  nlinarith

theorem binary_block_set_profile {F K b₀ : ℕ} {c : ℝ}
    (hb : 2 ≤ b₀) (hbK : b₀ ≤ K) (hF : 2 ^ b₀ ≤ F) (hc : 0 ≤ c) (hcsmall : c ≤ 1 / 2)
    (hD : ∀ l : ℕ, 1 ≤ l → l ≤ K → (2 : ℝ) ^ (c * (l : ℝ)) ≤ (shortFactorialDigits F l).card) :
    ∀ i : ℕ, BinaryBlockProfile F K (binaryBlockEndpoint K b₀ i) (i + 1) c (binaryBlockSet F K b₀ i) := by
  intro i
  induction i with
  | zero =>
    rw [binary_block_endpoint_zero hbK]
    exact initial_odd_digits_profile hb hF hcsmall
  | succ i ih =>
    have hbds := binary_block_endpoint_bounds hbK i
    have hw := binary_block_width_le K b₀ i
    have hstep := binary_append_profile ih (by omega) hbds.2 hw hc
      (short_factorial_digits_entropy hD (hw.trans hbds.2))
    rw [binary_block_width_add] at hstep
    exact hstep

theorem binary_block_set_profile_top {F K b₀ : ℕ} {c : ℝ}
    (hb : 2 ≤ b₀) (hbK : b₀ ≤ K) (hF : 2 ^ b₀ ≤ F) (hc : 0 ≤ c) (hcsmall : c ≤ 1 / 2)
    (hD : ∀ l : ℕ, 1 ≤ l → l ≤ K → (2 : ℝ) ^ (c * (l : ℝ)) ≤ (shortFactorialDigits F l).card) :
    BinaryBlockProfile F K K (binaryLength K + 1) c (binaryBlockSet F K b₀ (binaryLength K)) := by
  have h := binary_block_set_profile hb hbK hF hc hcsmall hD (binaryLength K)
  rwa [binary_block_endpoint_top (by omega : 1 ≤ b₀)] at h

noncomputable def cyclicUniformNatSet {q : ℕ} [NeZero q] (A : Finset ℕ) : ZMod q → ℂ :=
  cyclicPushforward (fun _ : A => (A.card : ℂ)⁻¹) (fun n => (n.val : ZMod q))

theorem dft_cyclicUniformNatSet {q : ℕ} [NeZero q] (A : Finset ℕ) (k : ZMod q) :
    ZMod.dft (cyclicUniformNatSet A) k =
      (∑ n ∈ A, ZMod.stdAddChar (-((n : ZMod q) * k))) * (A.card : ℂ)⁻¹ := by
  rw [cyclicUniformNatSet, dft_cyclicPushforward, ← Finset.sum_mul]
  congr 1
  exact Finset.sum_coe_sort A (fun n => ZMod.stdAddChar (-((n : ZMod q) * k)))

theorem dft_cyclicUniformNatSet_at_zero {q : ℕ} [NeZero q] {A : Finset ℕ} (hA : A.Nonempty) :
    ZMod.dft (cyclicUniformNatSet (q := q) A) 0 = 1 := by
  rw [dft_cyclicUniformNatSet]
  have hcard : (A.card : ℂ) ≠ 0 := by exact_mod_cast Finset.card_ne_zero.mpr hA
  simp [hcard]

theorem cyclicUniformNatSet_support {q : ℕ} [NeZero q] (A : Finset ℕ) {x : ZMod q}
    (hx : cyclicUniformNatSet A x ≠ 0) : ∃ n ∈ A, (n : ZMod q) = x := by
  obtain ⟨n, hn, _⟩ := cyclicPushforward_support (fun _ : A => (A.card : ℂ)⁻¹)
    (fun n => (n.val : ZMod q)) hx
  exact ⟨n.val, n.property, hn⟩

theorem dft_binary_append {q b : ℕ} [NeZero q] {A D : Finset ℕ}
    (hA : ∀ x ∈ A, x < 2 ^ b) (k : ZMod q) :
    ZMod.dft (cyclicUniformNatSet (binaryAppend A D b)) k =
      ZMod.dft (cyclicUniformNatSet A) k *
      ((∑ d ∈ D, ZMod.stdAddChar (-(((2 ^ b * d : ℕ) : ZMod q) * k))) * (D.card : ℂ)⁻¹) := by
  classical
  rw [dft_cyclicUniformNatSet, binary_append_card hA, Nat.cast_mul, mul_inv_rev,
    dft_cyclicUniformNatSet]
  unfold binaryAppend
  rw [Finset.sum_image (binary_append_injective hA), Finset.sum_product]
  have hchar (a d : ℕ) : ZMod.stdAddChar (-(((a + 2 ^ b * d : ℕ) : ZMod q) * k)) =
      ZMod.stdAddChar (-((a : ZMod q) * k)) * ZMod.stdAddChar (-(((2 ^ b * d : ℕ) : ZMod q) * k)) := by
    rw [← AddChar.map_add_eq_mul]
    congr 1
    push_cast
    ring
  simp_rw [hchar, ← Finset.mul_sum, ← Finset.sum_mul]
  ring

theorem dft_initialOddDigits {K b : ℕ} (k : ZMod (2 ^ K)) :
    ZMod.dft (cyclicUniformNatSet (initialOddDigits b)) k = ZMod.dft (cyclicOddDigit b) k := by
  rw [dft_cyclicUniformNatSet, initial_odd_digits_card, cyclicOddDigit, dft_cyclicPushforward,
    ← Finset.sum_mul]
  congr 1
  unfold initialOddDigits
  rw [Finset.sum_image (by intro x hx y hy h; change 2 * x + 1 = 2 * y + 1 at h; omega)]
  exact (Fin.sum_univ_eq_sum_range
    (fun i : ℕ => ZMod.stdAddChar (-(((2 * i + 1 : ℕ) : ZMod (2 ^ K)) * k))) _).symm

theorem dft_binary_block_set_low {F K b₀ : ℕ} {c : ℝ}
    (hb : 2 ≤ b₀) (hbK : b₀ ≤ K) (hF : 2 ^ b₀ ≤ F) (hc : 0 ≤ c) (hcsmall : c ≤ 1 / 2)
    (hD : ∀ l : ℕ, 1 ≤ l → l ≤ K → (2 : ℝ) ^ (c * (l : ℝ)) ≤ (shortFactorialDigits F l).card)
    {k : ZMod (2 ^ K)} (hklo : 2 ≤ dyadicConductorLevel k) (hkhi : dyadicConductorLevel k ≤ b₀) :
    ∀ i : ℕ, ZMod.dft (cyclicUniformNatSet (binaryBlockSet F K b₀ i)) k = 0 := by
  intro i
  induction i with
  | zero =>
    rw [binaryBlockSet, dft_initialOddDigits]
    exact dft_cyclicOddDigit_zero hklo hkhi
  | succ i ih =>
    rw [binaryBlockSet, dft_binary_append (binary_block_set_profile hb hbK hF hc hcsmall hD i).bounded,
      ih, zero_mul]

theorem cyclicUniformNatSet_eq_residue_mass {q : ℕ} [NeZero q] (A : Finset ℕ) (x : ZMod q) :
    cyclicUniformNatSet A x = (natResidueMass A q x.val : ℂ) := by
  classical
  have hpred (n : ℕ) : ((n : ZMod q) = x) ↔ Nat.ModEq q n x.val := by
    simpa only [ZMod.natCast_zmod_val] using (ZMod.natCast_eq_natCast_iff n x.val q)
  unfold cyclicUniformNatSet cyclicPushforward
  rw [Finset.sum_coe_sort A (fun n => if (n : ZMod q) = x then (A.card : ℂ)⁻¹ else 0)]
  simp_rw [hpred]
  rw [← Finset.sum_filter]
  simp [natResidueMass, natResidueFiber, div_eq_mul_inv]

theorem norm_cyclicUniformNatSet {q : ℕ} [NeZero q] (A : Finset ℕ) (x : ZMod q) :
    ‖cyclicUniformNatSet A x‖ = natResidueMass A q x.val := by
  rw [cyclicUniformNatSet_eq_residue_mass]
  apply Complex.norm_of_nonneg
  unfold natResidueMass
  positivity

theorem cyclicUniformNatSet_probability {q : ℕ} [NeZero q] {A : Finset ℕ} (hA : A.Nonempty) :
    (∀ x : ZMod q, 0 ≤ (cyclicUniformNatSet A x).re ∧ (cyclicUniformNatSet A x).im = 0) ∧
      ZMod.dft (cyclicUniformNatSet (q := q) A) 0 = 1 := by
  refine ⟨?_, dft_cyclicUniformNatSet_at_zero hA⟩
  intro x
  rw [cyclicUniformNatSet_eq_residue_mass]
  simp only [Complex.ofReal_re, Complex.ofReal_im, and_true]
  unfold natResidueMass
  positivity

theorem binary_block_profile_law {F K u : ℕ} {c : ℝ} {A : Finset ℕ}
    (hA : BinaryBlockProfile F K K u c A) :
    (∀ x : ZMod (2 ^ K), cyclicUniformNatSet A x ≠ 0 → IsUnit x) ∧
    (∀ x : ZMod (2 ^ K), cyclicUniformNatSet A x ≠ 0 → ∃ S : ℕ,
      S ≤ 2 ^ K ∧ (S : ZMod (2 ^ K)) = x ∧ HasFactorialDivisorMultiset (F + 2 * K) S u) ∧
    (∀ j : ℕ, 2 ≤ j → j ≤ K → ∀ x : ZMod (2 ^ j),
      ‖cyclicUniformNatSet A x‖ ≤ (2 : ℝ) ^ (-(c / 2) * (j : ℝ))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨n, hn, hcast⟩ := cyclicUniformNatSet_support A hx
    rw [← hcast]
    apply (ZMod.isUnit_iff_coprime _ _).mpr
    have hnodd := hA.odd n hn
    have hcop : Nat.Coprime n 2 := by
      rw [Nat.coprime_comm, Nat.prime_two.coprime_iff_not_dvd]
      obtain ⟨t, ht⟩ := hnodd
      omega
    exact hcop.pow_right K
  · intro x hx
    obtain ⟨n, hn, hcast⟩ := cyclicUniformNatSet_support A hx
    exact ⟨n, (hA.bounded n hn).le, hcast, hA.representatives n hn⟩
  · intro j hj hjK x
    rw [norm_cyclicUniformNatSet]
    exact hA.spread j hj hjK x.val

noncomputable def factorialDigitBase (a : ℝ) (K : ℕ) : ℕ := Nat.log 2 (factorialDigitHost a K)

noncomputable def factorialBlockSet (a : ℝ) (K : ℕ) : Finset ℕ :=
  binaryBlockSet (factorialDigitHost a K) K (factorialDigitBase a K) (binaryLength K)

noncomputable def factorialBlockLaw (a : ℝ) (K : ℕ) : ZMod (2 ^ K) → ℂ :=
  cyclicUniformNatSet (factorialBlockSet a K)

theorem factorialDigitBase_tendsto {a : ℝ} (ha : 0 < a) :
    Filter.Tendsto (factorialDigitBase a) Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop.mpr
  intro M
  filter_upwards [(factorialDigitHost_tendsto ha).eventually_ge_atTop (2 ^ M)] with K hK
  exact Nat.le_log_of_pow_le (by decide) hK

theorem eventually_factorialDigitBase_bounds {a : ℝ} (ha : 0 < a) :
    ∀ᶠ K : ℕ in Filter.atTop, 2 ≤ factorialDigitBase a K ∧ factorialDigitBase a K ≤ K ∧
      2 ^ factorialDigitBase a K ≤ factorialDigitHost a K := by
  let ε : ℝ := 1 / (2 * a)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have haε : a * ε = 1 / 2 := by dsimp [ε]; field_simp
  have hhost := factorialDigitHost_tendsto ha
  have hbit := hhost.eventually (eventually_binaryLength_le_rpow hε)
  have hpower := eventually_const_mul_rpow_le (a := 1 / 2) (b := 1) (C := (2 : ℝ) ^ ε)
    (E := 1) (by norm_num) (by norm_num)
  filter_upwards [hbit, hpower, (factorialDigitBase_tendsto ha).eventually_ge_atTop 2,
    hhost.eventually_ge_atTop 1, eventually_ge_atTop (1 : ℕ)] with K hKbit hKpower hKbase hKhost hKone
  refine ⟨hKbase, ?_, Nat.pow_log_le_self 2 (by omega)⟩
  have hlen : (binaryLength (factorialDigitHost a K) : ℝ) ≤ (K : ℝ) := by
    calc
      (binaryLength (factorialDigitHost a K) : ℝ) ≤ (factorialDigitHost a K : ℝ) ^ ε := hKbit
      _ ≤ (2 * (K : ℝ) ^ a) ^ ε := Real.rpow_le_rpow (Nat.cast_nonneg _)
        (factorialDigitHost_le ha.le hKone) hε.le
      _ = (2 : ℝ) ^ ε * (K : ℝ) ^ (1 / 2 : ℝ) := by
        rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul (Nat.cast_nonneg K), haε]
      _ ≤ (K : ℝ) := by simpa only [one_mul, Real.rpow_one] using hKpower
  have hbitle : factorialDigitBase a K ≤ binaryLength (factorialDigitHost a K) := Nat.le_succ _
  exact_mod_cast (show (factorialDigitBase a K : ℝ) ≤ (K : ℝ) from
    (by exact_mod_cast hbitle : (factorialDigitBase a K : ℝ) ≤ binaryLength (factorialDigitHost a K)).trans hlen)

theorem factorial_block_set_profiles {a : ℝ} (ha : 1 < a) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 / 2 ∧ ∀ᶠ K : ℕ in Filter.atTop,
      BinaryBlockProfile (factorialDigitHost a K) K K (binaryLength K + 1) c (factorialBlockSet a K) ∧
      (∀ x : ZMod (2 ^ K), 2 ≤ dyadicConductorLevel x →
        dyadicConductorLevel x ≤ factorialDigitBase a K → ZMod.dft (factorialBlockLaw a K) x = 0) := by
  obtain ⟨c₀, hc₀, hshort⟩ := shortFactorialDigits_uniform_asymptotic ha
  let c := min c₀ (1 / 2)
  have hc : 0 < c := lt_min hc₀ (by norm_num)
  have hcc : c ≤ c₀ := min_le_left _ _
  have hchalf : c ≤ 1 / 2 := min_le_right _ _
  refine ⟨c, hc, hchalf, ?_⟩
  filter_upwards [hshort, eventually_factorialDigitBase_bounds (by linarith : 0 < a)]
    with K hKshort hKb
  obtain ⟨hblo, hbK, hF⟩ := hKb
  have hD : ∀ l : ℕ, 1 ≤ l → l ≤ K →
      (2 : ℝ) ^ (c * (l : ℝ)) ≤ (shortFactorialDigits (factorialDigitHost a K) l).card := by
    intro l hl hlK
    exact (Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (mul_le_mul_of_nonneg_right hcc (Nat.cast_nonneg l))).trans (hKshort.2 l hl hlK)
  refine ⟨binary_block_set_profile_top hblo hbK hF hc.le hchalf hD, ?_⟩
  intro x hxlo hxhi
  exact dft_binary_block_set_low hblo hbK hF hc.le hchalf hD hxlo hxhi (binaryLength K)

theorem factorial_block_laws {a : ℝ} (ha : 1 < a) :
    ∃ g : ℝ, 0 < g ∧ g ≤ 1 / 2 ∧ ∀ᶠ K : ℕ in Filter.atTop,
      ZMod.dft (factorialBlockLaw a K) 0 = 1 ∧
      (∀ x : ZMod (2 ^ K), 0 ≤ (factorialBlockLaw a K x).re ∧ (factorialBlockLaw a K x).im = 0) ∧
      (∀ x : ZMod (2 ^ K), factorialBlockLaw a K x ≠ 0 → IsUnit x) ∧
      (∀ x : ZMod (2 ^ K), factorialBlockLaw a K x ≠ 0 → ∃ S : ℕ,
        S ≤ 2 ^ K ∧ (S : ZMod (2 ^ K)) = x ∧
          HasFactorialDivisorMultiset (factorialDigitHost a K + 2 * K) S (binaryLength K + 1)) ∧
      (∀ x : ZMod (2 ^ K), 2 ≤ dyadicConductorLevel x → dyadicConductorLevel x ≤ factorialDigitBase a K →
        ZMod.dft (factorialBlockLaw a K) x = 0) ∧
      (∀ j : ℕ, 2 ≤ j → j ≤ K → ∀ x : ZMod (2 ^ j),
        ‖cyclicUniformNatSet (factorialBlockSet a K) x‖ ≤ (2 : ℝ) ^ (-g * (j : ℝ))) := by
  obtain ⟨c, hc, hchalf, hprofiles⟩ := factorial_block_set_profiles ha
  refine ⟨c / 2, by positivity, by linarith, ?_⟩
  filter_upwards [hprofiles] with K hK
  obtain ⟨hprofile, hlow⟩ := hK
  obtain ⟨hprob, hzero⟩ := cyclicUniformNatSet_probability (q := 2 ^ K) hprofile.nonempty
  obtain ⟨hunit, hrep, hspread⟩ := binary_block_profile_law hprofile
  exact ⟨hzero, hprob, hunit, hrep, hlow, hspread⟩

theorem dyadic_frequency_factor {K : ℕ} {x : ZMod (2 ^ K)} (hx : x ≠ 0) :
    ∃ a : ℕ, Odd a ∧ x = ((2 ^ (K - dyadicConductorLevel x) * a : ℕ) : ZMod (2 ^ K)) := by
  let j := dyadicConductorLevel x
  have hj : 0 < j := dyadic_conductor_pos hx
  have hjK : j ≤ K := (dyadic_conductor_spec x).1
  have horder : addOrderOf x = 2 ^ j := (dyadic_conductor_spec x).2
  have hperiod : ((2 ^ j * x.val : ℕ) : ZMod (2 ^ K)) = 0 := by
    have hh := addOrderOf_nsmul_eq_zero x
    rw [horder] at hh
    simpa only [nsmul_eq_mul, Nat.cast_mul, ZMod.natCast_zmod_val] using hh
  have hdiv := (ZMod.natCast_eq_zero_iff _ _).mp hperiod
  have hQ : 2 ^ K = 2 ^ j * 2 ^ (K - j) := by rw [← pow_add, Nat.add_sub_of_le hjK]
  have hdiv' : 2 ^ j * 2 ^ (K - j) ∣ 2 ^ j * x.val := hQ.symm.dvd.trans hdiv
  have hfactor := Nat.dvd_of_mul_dvd_mul_left (by positivity : 0 < 2 ^ j) hdiv'
  obtain ⟨a, ha⟩ := hfactor
  have hxa : x = ((2 ^ (K - j) * a : ℕ) : ZMod (2 ^ K)) := by
    rw [← ha, ZMod.natCast_zmod_val]
  refine ⟨a, ?_, hxa⟩
  by_contra hodd
  have heven : Even a := Nat.not_odd_iff_even.mp hodd
  obtain ⟨t, ht⟩ := heven
  have hnat : 2 ^ (j - 1) * (2 ^ (K - j) * a) = 2 ^ K * t := by
    rw [ht, hQ]
    have hp : 2 ^ j = 2 ^ (j - 1) * 2 := by rw [← pow_succ, Nat.sub_add_cancel hj]
    rw [hp]
    ring
  have hsmul : (2 ^ (j - 1)) • x = 0 := by
    rw [hxa, nsmul_eq_mul, ← Nat.cast_mul, hnat]
    exact (ZMod.natCast_eq_zero_iff _ _).mpr (dvd_mul_right _ _)
  have hdvd : 2 ^ j ∣ 2 ^ (j - 1) := by
    rw [← horder]
    exact addOrderOf_dvd_iff_nsmul_eq_zero.mpr hsmul
  have hle := (Nat.pow_dvd_pow_iff_le_right (by decide : 1 < 2)).mp hdvd
  omega

theorem stdAddChar_scaled_modulus {Q q d : ℕ} [NeZero Q] [NeZero q]
    (hQ : Q = d * q) (m : ℤ) :
    ZMod.stdAddChar (((d : ℤ) * m : ℤ) : ZMod Q) = ZMod.stdAddChar (m : ZMod q) := by
  have hd : d ≠ 0 := by
    intro h
    have := NeZero.ne Q
    simp [hQ, h] at this
  rw [ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  congr 1
  rw [hQ]
  push_cast
  have hdc : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  have hqc : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  field_simp

theorem dyadic_frequency_phase {K j a : ℕ} (hj : j ≤ K)
    {x : ZMod (2 ^ K)} (hx : x = ((2 ^ (K - j) * a : ℕ) : ZMod (2 ^ K))) (n : ℕ) :
    ZMod.stdAddChar (-((n : ZMod (2 ^ K)) * x)) =
      ZMod.stdAddChar (-((n : ZMod (2 ^ j)) * (a : ZMod (2 ^ j)))) := by
  have hQ : 2 ^ K = 2 ^ (K - j) * 2 ^ j := by rw [← pow_add, Nat.sub_add_cancel hj]
  have hphase := stdAddChar_scaled_modulus hQ (-((n : ℤ) * (a : ℤ)))
  rw [hx]
  convert hphase using 1
  · push_cast
    congr 1
    ring
  · push_cast
    rfl

theorem dft_product_uniform_succ {q : ℕ} [NeZero q]
    (A : Finset ℕ) (r : ℕ) (k : ZMod q) :
    ZMod.dft (cyclicProductPow (cyclicUniformNatSet A) (r + 1)) k =
      (∑ a ∈ A, ZMod.dft (cyclicProductPow (cyclicUniformNatSet A) r) ((a : ZMod q) * k)) *
        (A.card : ℂ)⁻¹ := by
  classical
  rw [cyclicProductPow, dft_cyclicMultiplicativeConvolution]
  simp_rw [dft_cyclicUniformNatSet, ← mul_assoc, Finset.mul_sum]
  rw [← Finset.sum_mul, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [ZMod.dft_apply]
  apply Finset.sum_congr rfl
  intro y _
  simp only [smul_eq_mul]
  rw [show (a : ZMod q) * y * k = y * ((a : ZMod q) * k) by ring]
  ring

theorem dft_product_uniform_transfer {Q q : ℕ} [NeZero Q] [NeZero q]
    (A : Finset ℕ) : ∀ r : ℕ, ∀ x : ZMod Q, ∀ y : ZMod q,
      (∀ n : ℕ, ZMod.stdAddChar (-((n : ZMod Q) * x)) = ZMod.stdAddChar (-((n : ZMod q) * y))) →
      ZMod.dft (cyclicProductPow (cyclicUniformNatSet A) r) x =
        ZMod.dft (cyclicProductPow (cyclicUniformNatSet A) r) y := by
  intro r
  induction r with
  | zero =>
    intro x y hphase
    simpa [cyclicProductPow, ZMod.dft_apply] using hphase 1
  | succ r ih =>
    intro x y hphase
    rw [dft_product_uniform_succ, dft_product_uniform_succ]
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    apply ih
    intro n
    simpa only [Nat.cast_mul, mul_assoc] using hphase (n * a)

/-- The odd-law mixing property proved below by `weighted_dyadic_mixing`. -/
def WeightedDyadicMixing : Prop :=
  ∀ g : ℝ, 0 < g → g ≤ 1 / 2 → ∃ r : ℕ, ∃ t : ℝ, ∃ J₀ : ℕ,
    0 < r ∧ 0 < t ∧ ∀ J : ℕ, J₀ ≤ J → ∀ A : Finset ℕ,
      A.Nonempty → (∀ n ∈ A, Odd n) →
      (∀ l : ℕ, 2 ≤ l → l ≤ J → ∀ x : ZMod (2 ^ l),
        ‖cyclicUniformNatSet A x‖ ≤ (2 : ℝ) ^ (-g * (l : ℝ))) →
      ∀ a : ℕ, Odd a →
        ‖ZMod.dft (cyclicProductPow (cyclicUniformNatSet A) r) (a : ZMod (2 ^ J))‖ ≤
          (2 : ℝ) ^ (-t * (J : ℝ))

theorem block_product_decay_of_weighted_mixing {a : ℝ} (ha : 1 < a) (hmix : WeightedDyadicMixing) :
    ∃ r : ℕ, ∃ t : ℝ, 0 < r ∧ 0 < t ∧ ∀ᶠ K : ℕ in Filter.atTop,
      ∀ x : ZMod (2 ^ K), factorialDigitBase a K < dyadicConductorLevel x →
        ‖ZMod.dft (cyclicProductPow (factorialBlockLaw a K) r) x‖ ≤
          (2 : ℝ) ^ (-t * (dyadicConductorLevel x : ℝ)) := by
  obtain ⟨c, hc, hchalf, hprofiles⟩ := factorial_block_set_profiles ha
  obtain ⟨r, t, J₀, hr, ht, hmix⟩ := hmix (c / 2) (by positivity) (by linarith)
  refine ⟨r, t, hr, ht, ?_⟩
  filter_upwards [hprofiles, (factorialDigitBase_tendsto (by linarith : 0 < a)).eventually_ge_atTop J₀]
    with K hK hKbase
  intro x hx
  have hxne : x ≠ 0 := by
    intro hzero
    subst x
    simp [dyadicConductorLevel] at hx
  obtain ⟨m, hm, hfactor⟩ := dyadic_frequency_factor hxne
  have hjK := (dyadic_conductor_spec x).1
  have hspread := (binary_block_profile_law hK.1).2.2
  have hbound := hmix (dyadicConductorLevel x) (by omega) (factorialBlockSet a K)
    hK.1.nonempty hK.1.odd (fun l hl hlj => hspread l hl (hlj.trans hjK)) m hm
  have htransfer := dft_product_uniform_transfer (factorialBlockSet a K) r x
    (m : ZMod (2 ^ dyadicConductorLevel x)) (fun n => dyadic_frequency_phase hjK hfactor n)
  change ‖ZMod.dft (cyclicProductPow (cyclicUniformNatSet (factorialBlockSet a K)) r) x‖ ≤ _
  rw [htransfer]
  exact hbound

theorem block_product_host_bound {a : ℝ} {K r : ℕ} (ha : 1 ≤ a) (hK : 1 ≤ K) :
    ((r * (factorialDigitHost a K + 2 * K) : ℕ) : ℝ) ≤
      (4 * (r : ℝ)) * (K : ℝ) ^ a := by
  have hhost := factorialDigitHost_le (by linarith : 0 ≤ a) hK
  have hKpow : (K : ℝ) ≤ (K : ℝ) ^ a := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hK : (1 : ℝ) ≤ K) ha
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
  calc
    (r : ℝ) * ((factorialDigitHost a K : ℝ) + 2 * K) ≤ (r : ℝ) * (4 * (K : ℝ) ^ a) :=
      mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg r)
    _ = (4 * (r : ℝ)) * (K : ℝ) ^ a := by ring

theorem eventually_block_sum_count_bound {b : ℝ} {r : ℕ} (hb : 0 < b) (hr : 0 < r) (s : ℕ) :
    ∀ᶠ K : ℕ in Filter.atTop,
      ((s * ((binaryLength K + 1) ^ r + 1) : ℕ) : ℝ) ≤
        ((s : ℝ) * ((2 : ℝ) ^ r + 1)) * (K : ℝ) ^ b := by
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  have hε : 0 < b / (r : ℝ) := div_pos hb hrpos
  filter_upwards [eventually_binaryLength_le_rpow hε, eventually_ge_atTop (1 : ℕ)] with K hK hKone
  have hlenone : (1 : ℝ) ≤ binaryLength K := by exact_mod_cast binaryLength_pos K
  have hlen : ((binaryLength K + 1 : ℕ) : ℝ) ≤ 2 * (K : ℝ) ^ (b / (r : ℝ)) := by
    rw [Nat.cast_add, Nat.cast_one]
    linarith
  have hpow : (((binaryLength K + 1 : ℕ) : ℝ) ^ r) ≤ (2 : ℝ) ^ r * (K : ℝ) ^ b := by
    calc
      _ ≤ (2 * (K : ℝ) ^ (b / (r : ℝ))) ^ r := pow_le_pow_left₀ (by positivity) hlen r
      _ = (2 : ℝ) ^ r * (K : ℝ) ^ b := by
        rw [mul_pow, ← Real.rpow_mul_natCast (Nat.cast_nonneg K), div_mul_cancel₀ b hrpos.ne']
  have hKpow : 1 ≤ (K : ℝ) ^ b := Real.one_le_rpow (by exact_mod_cast hKone) hb.le
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_one]
  calc
    (s : ℝ) * (((binaryLength K : ℝ) + 1) ^ r + 1) ≤
        (s : ℝ) * (((2 : ℝ) ^ r + 1) * (K : ℝ) ^ b) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg s)
      push_cast at hpow
      nlinarith
    _ = ((s : ℝ) * ((2 : ℝ) ^ r + 1)) * (K : ℝ) ^ b := by ring

theorem dyadic_modular_bounds_of_block_product_decay {a b : ℝ}
    (ha : 1 < a) (hb : 0 < b)
    (hdecay : ∃ r : ℕ, ∃ t : ℝ, 0 < r ∧ 0 < t ∧ ∀ᶠ K : ℕ in Filter.atTop,
      ∀ x : ZMod (2 ^ K), factorialDigitBase a K < dyadicConductorLevel x →
        ‖ZMod.dft (cyclicProductPow (factorialBlockLaw a K) r) x‖ ≤
          (2 : ℝ) ^ (-t * (dyadicConductorLevel x : ℝ))) : DyadicModularBounds a b := by
  obtain ⟨r, t, hr, ht, hdecay⟩ := hdecay
  obtain ⟨s, hs, hmod⟩ := exists_power_modular_representatives_of_product_decay ht
  obtain ⟨g, hg, hghalf, hlaws⟩ := factorial_block_laws ha
  have hevent : ∀ᶠ K : ℕ in Filter.atTop, ∃ F u : ℕ,
      2 ^ K ∣ F.factorial ∧ HasBoundedModularRepresentatives (2 ^ K) F u (r + 1) ∧
      (F : ℝ) ≤ (4 * (r : ℝ)) * (K : ℝ) ^ a ∧
      (u : ℝ) ≤ ((s : ℝ) * ((2 : ℝ) ^ r + 1)) * (K : ℝ) ^ b := by
    filter_upwards [hdecay, hlaws, eventually_block_sum_count_bound hb hr s,
      eventually_ge_atTop (2 * s), eventually_ge_atTop (1 : ℕ)] with K hKdecay hKlaw hKcount hKs hKone
    obtain ⟨hzero, _, hunit, hrep, hlow, _⟩ := hKlaw
    have hheight : 2 * s ≤ 2 ^ K := hKs.trans (Nat.lt_two_pow_self : K < 2 ^ K).le
    have hmodK := hmod K (factorialDigitBase a K) r (factorialDigitHost a K + 2 * K)
      (binaryLength K + 1) hr (factorialBlockLaw a K) hzero hunit hlow hKdecay hrep hheight
    refine ⟨r * (factorialDigitHost a K + 2 * K), s * ((binaryLength K + 1) ^ r + 1),
      ?_, hmodK, block_product_host_bound ha.le hKone, hKcount⟩
    have hreserve : 2 ^ K ∣ (factorialDigitHost a K + 2 * K).factorial :=
      (dvd_mul_right (2 ^ K) (factorialDigitHost a K).factorial).trans
        (factorial_binary_reserve (factorialDigitHost a K) K)
    exact hreserve.trans (Nat.factorial_dvd_factorial (by nlinarith))
  obtain ⟨K₀, hK₀⟩ := Filter.eventually_atTop.mp hevent
  refine ⟨r + 1, K₀, 4 * (r : ℝ), (s : ℝ) * ((2 : ℝ) ^ r + 1), ?_, ?_, hK₀⟩ <;>
    positivity

theorem dyadic_modular_bounds_of_weighted_dyadic_mixing {a b : ℝ}
    (ha : 1 < a) (hb : 0 < b) (hmix : WeightedDyadicMixing) : DyadicModularBounds a b := by
  exact dyadic_modular_bounds_of_block_product_decay ha hb (block_product_decay_of_weighted_mixing ha hmix)

theorem erdos18b_of_weighted_dyadic_mixing (hmix : WeightedDyadicMixing) :
    fcTypeOfName% "Erdos18.erdos_18b" := by
  exact erdos18b_of_dyadic_modular_bounds
    (fun _ _ ha hb => dyadic_modular_bounds_of_weighted_dyadic_mixing ha hb hmix)

theorem binary_block_profile_spread_extended {F K b u J : ℕ} {c : ℝ} {A : Finset ℕ}
    (hA : BinaryBlockProfile F K b u c A) (hc : 0 ≤ c) (hJ : J ≤ 2 * b) :
    ∀ l : ℕ, 2 ≤ l → l ≤ J → ∀ r : ℕ,
      natResidueMass A (2 ^ l) r ≤ (2 : ℝ) ^ (-(c / 2) * (l : ℝ)) := by
  intro l hl hlJ r
  by_cases hlb : l ≤ b
  · exact hA.spread l hl hlb r
  · have hbound : ∀ x ∈ A, x < 2 ^ l := by
      intro x hx
      exact (hA.bounded x hx).trans_le (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))
    calc
      natResidueMass A (2 ^ l) r ≤ 1 / (A.card : ℝ) := by
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
        exact_mod_cast nat_residue_fiber_card_le_one hbound
      _ ≤ 1 / (2 : ℝ) ^ (c * (b : ℝ)) := one_div_le_one_div_of_le (by positivity) hA.entropy
      _ = (2 : ℝ) ^ (-(c * (b : ℝ))) := by rw [Real.rpow_neg (by norm_num), one_div]
      _ ≤ (2 : ℝ) ^ (-(c / 2) * (l : ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        have hh : (l : ℝ) ≤ 2 * (b : ℝ) := by exact_mod_cast hlJ.trans hJ
        nlinarith [mul_le_mul_of_nonneg_left hh hc]

def natTranslate (A : Finset ℕ) (c : ℕ) : Finset ℕ := A.image (fun n => n + c)

theorem nat_translate_card (A : Finset ℕ) (c : ℕ) : (natTranslate A c).card = A.card := by
  apply Finset.card_image_of_injective
  intro x y h
  exact Nat.add_right_cancel h

theorem nat_translate_nonempty {A : Finset ℕ} (hA : A.Nonempty) (c : ℕ) : (natTranslate A c).Nonempty :=
  hA.image _

theorem nat_translate_residue_mass {q : ℕ} [NeZero q] (A : Finset ℕ) (c r : ℕ) :
    natResidueMass (natTranslate A c) q r = natResidueMass A q ((r : ZMod q) - (c : ZMod q)).val := by
  let z : ZMod q := (r : ZMod q) - (c : ZMod q)
  have hpred (n : ℕ) : Nat.ModEq q (n + c) r ↔ Nat.ModEq q n z.val := by
    rw [← ZMod.natCast_eq_natCast_iff, ← ZMod.natCast_eq_natCast_iff]
    simp only [Nat.cast_add, ZMod.natCast_zmod_val, z]
    exact eq_sub_iff_add_eq.symm
  have hfiber : natResidueFiber (natTranslate A c) q r = natTranslate (natResidueFiber A q z.val) c := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxA, hxmod⟩ := Finset.mem_filter.mp hx
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hxA
      exact Finset.mem_image.mpr ⟨n, Finset.mem_filter.mpr ⟨hn, (hpred n).mp hxmod⟩, rfl⟩
    · intro hx
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨hnA, hnmod⟩ := Finset.mem_filter.mp hn
      exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨n, hnA, rfl⟩, (hpred n).mpr hnmod⟩
  unfold natResidueMass
  rw [hfiber, nat_translate_card, nat_translate_card]

theorem bounded_nat_set_cast_injective {q : ℕ} {A : Finset ℕ} (hA : ∀ n ∈ A, n < q) :
    Set.InjOn (fun n : ℕ => (n : ZMod q)) A := by
  intro n hn m hm h
  have heq := (ZMod.natCast_eq_natCast_iff n m q).mp h
  simpa only [Nat.ModEq, Nat.mod_eq_of_lt (hA n hn), Nat.mod_eq_of_lt (hA m hm)] using heq

theorem translated_nat_set_cast_injective {q : ℕ} {A : Finset ℕ}
    (hA : Set.InjOn (fun n : ℕ => (n : ZMod q)) A) (c : ℕ) :
    Set.InjOn (fun n : ℕ => (n : ZMod q)) (natTranslate A c) := by
  intro n hn m hm h
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hm
  have hab : (a : ZMod q) = (b : ZMod q) := by
    change ((a + c : ℕ) : ZMod q) = ((b + c : ℕ) : ZMod q) at h
    simpa only [Nat.cast_add, add_left_inj] using h
  rw [hA ha hb hab]

theorem translated_binary_prefix_spread {F K b u J : ℕ} {c : ℝ} {A : Finset ℕ}
    (hA : BinaryBlockProfile F K b u c A) (hc : 0 ≤ c) (hbJ : b ≤ J) (hJ : J ≤ 2 * b)
    (d : ℕ) :
    (natTranslate A d).Nonempty ∧
      Set.InjOn (fun n : ℕ => (n : ZMod (2 ^ J))) (natTranslate A d) ∧
      ∀ l : ℕ, 2 ≤ l → l ≤ J → ∀ x : ZMod (2 ^ l),
        ‖cyclicUniformNatSet (natTranslate A d) x‖ ≤ (2 : ℝ) ^ (-(c / 2) * (l : ℝ)) := by
  refine ⟨nat_translate_nonempty hA.nonempty d, ?_, ?_⟩
  · apply translated_nat_set_cast_injective
    apply bounded_nat_set_cast_injective
    intro n hn
    exact (hA.bounded n hn).trans_le (Nat.pow_le_pow_right (by decide : 0 < 2) hbJ)
  · intro l hl hlJ x
    rw [norm_cyclicUniformNatSet, nat_translate_residue_mass]
    exact binary_block_profile_spread_extended hA hc hJ l hl hlJ _

theorem binary_block_endpoint_monotone (K b₀ : ℕ) : Monotone (binaryBlockEndpoint K b₀) := by
  exact monotone_nat_of_le_succ (binary_block_endpoint_mono K b₀)

theorem binary_block_prefix_at_level {K b₀ J : ℕ}
    (hb : 1 ≤ b₀) (hbJ : b₀ < J) (hJK : J ≤ K) :
    ∃ i : ℕ, i ≤ binaryLength K ∧ binaryBlockEndpoint K b₀ i ≤ J ∧
      J ≤ 2 * binaryBlockEndpoint K b₀ i := by
  have hex : ∃ i : ℕ, J ≤ binaryBlockEndpoint K b₀ i := by
    refine ⟨binaryLength K, ?_⟩
    rwa [binary_block_endpoint_top hb]
  let m := Nat.find hex
  have hm : J ≤ binaryBlockEndpoint K b₀ m := Nat.find_spec hex
  have hmN : m ≤ binaryLength K := Nat.find_min' hex (by rwa [binary_block_endpoint_top hb])
  have hmpos : 0 < m := by
    by_contra h
    have hmzero : m = 0 := by omega
    rw [hmzero, binary_block_endpoint_zero (by omega)] at hm
    omega
  have hprev : binaryBlockEndpoint K b₀ (m - 1) < J := by
    exact Nat.lt_of_not_ge (Nat.find_min hex (by change m - 1 < m; omega))
  refine ⟨m - 1, by omega, hprev.le, ?_⟩
  have hnext := binary_block_endpoint_succ_le_twice K b₀ (m - 1)
  rw [Nat.sub_add_cancel hmpos] at hnext
  exact hm.trans hnext

theorem binary_append_singleton_zero (A : Finset ℕ) (b : ℕ) : binaryAppend A {0} b = A := by
  ext x
  simp [binaryAppend]

theorem binary_append_assoc (A D E : Finset ℕ) (b l : ℕ) :
    binaryAppend (binaryAppend A D b) E (b + l) = binaryAppend A (binaryAppend D E l) b := by
  ext x
  constructor
  · intro hx
    obtain ⟨⟨ad, e⟩, hade, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨had, he⟩ := Finset.mem_product.mp hade
    obtain ⟨⟨a, d⟩, hapair, rfl⟩ := Finset.mem_image.mp had
    obtain ⟨ha, hd⟩ := Finset.mem_product.mp hapair
    refine Finset.mem_image.mpr ⟨(a, d + 2 ^ l * e), Finset.mem_product.mpr ⟨ha, ?_⟩, ?_⟩
    · exact Finset.mem_image.mpr ⟨(d, e), Finset.mem_product.mpr ⟨hd, he⟩, rfl⟩
    · simp only [pow_add]
      ring
  · intro hx
    obtain ⟨⟨a, de⟩, hade, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨ha, hde⟩ := Finset.mem_product.mp hade
    obtain ⟨⟨d, e⟩, hdepair, rfl⟩ := Finset.mem_image.mp hde
    obtain ⟨hd, he⟩ := Finset.mem_product.mp hdepair
    refine Finset.mem_image.mpr ⟨(a + 2 ^ b * d, e), Finset.mem_product.mpr ⟨?_, he⟩, ?_⟩
    · exact Finset.mem_image.mpr ⟨(a, d), Finset.mem_product.mpr ⟨ha, hd⟩, rfl⟩
    · simp only [pow_add]
      ring

theorem binary_block_set_factors_at_prefix (F K b₀ i N : ℕ) (hiN : i ≤ N) :
    ∃ D : Finset ℕ, D.Nonempty ∧ binaryBlockSet F K b₀ N =
      binaryAppend (binaryBlockSet F K b₀ i) D (binaryBlockEndpoint K b₀ i) := by
  induction N, hiN using Nat.le_induction with
  | base =>
    exact ⟨{0}, Finset.singleton_nonempty 0, (binary_append_singleton_zero _ _).symm⟩
  | succ N hiN ih =>
    obtain ⟨D, hD, hfactor⟩ := ih
    have hbN := binary_block_endpoint_monotone K b₀ hiN
    have hsplit : binaryBlockEndpoint K b₀ N = binaryBlockEndpoint K b₀ i +
        (binaryBlockEndpoint K b₀ N - binaryBlockEndpoint K b₀ i) := by omega
    refine ⟨binaryAppend D (shortFactorialDigits F (binaryBlockWidth K b₀ N))
      (binaryBlockEndpoint K b₀ N - binaryBlockEndpoint K b₀ i),
      binary_append_nonempty hD (short_factorial_digits_nonempty _ _), ?_⟩
    rw [binaryBlockSet, hfactor, hsplit, binary_append_assoc]
    simp only [Nat.add_sub_cancel_left]

noncomputable def natProductAverage : List (Finset ℕ) → (ℕ → ℂ) → ℂ
  | [], f => f 1
  | A :: L, f => (∑ n ∈ A, natProductAverage L (fun m => f (n * m))) * (A.card : ℂ)⁻¹

theorem nat_product_average_congr (L : List (Finset ℕ)) {f g : ℕ → ℂ}
    (h : ∀ n, f n = g n) : natProductAverage L f = natProductAverage L g := by
  congr 1
  exact funext h

theorem nat_product_average_binary_append_head {A D : Finset ℕ} {b : ℕ}
    (hA : ∀ n ∈ A, n < 2 ^ b) (L : List (Finset ℕ)) (f : ℕ → ℂ) :
    natProductAverage (binaryAppend A D b :: L) f =
      (∑ d ∈ D, natProductAverage (natTranslate A (2 ^ b * d) :: L) f) * (D.card : ℂ)⁻¹ := by
  simp only [natProductAverage, binary_append_card hA, Nat.cast_mul, mul_inv_rev,
    nat_translate_card]
  rw [binaryAppend, Finset.sum_image (binary_append_injective hA), Finset.sum_product,
    Finset.sum_comm]
  simp only [natTranslate, Finset.sum_image (fun _ _ _ _ h => Nat.add_right_cancel h)]
  rw [← Finset.sum_mul]
  ring

theorem nat_product_average_binary_append {A D : Finset ℕ} {b : ℕ}
    (hA : ∀ n ∈ A, n < 2 ^ b) (P L : List (Finset ℕ)) (f : ℕ → ℂ) :
    natProductAverage (P ++ binaryAppend A D b :: L) f =
      (∑ d ∈ D, natProductAverage (P ++ natTranslate A (2 ^ b * d) :: L) f) * (D.card : ℂ)⁻¹ := by
  induction P generalizing f with
  | nil => exact nat_product_average_binary_append_head hA L f
  | cons B P ih =>
    simp only [List.cons_append, natProductAverage]
    simp_rw [ih]
    simp only [← Finset.sum_mul]
    rw [Finset.sum_comm]
    ring

theorem norm_finset_average_le {D : Finset ℕ} (hD : D.Nonempty) {f : ℕ → ℂ} {B : ℝ}
    (h : ∀ d ∈ D, ‖f d‖ ≤ B) : ‖(∑ d ∈ D, f d) * (D.card : ℂ)⁻¹‖ ≤ B := by
  have hDc : (0 : ℝ) < D.card := by exact_mod_cast Finset.card_pos.mpr hD
  have hsum : ‖∑ d ∈ D, f d‖ ≤ (D.card : ℝ) * B := by
    calc
      _ ≤ ∑ d ∈ D, ‖f d‖ := norm_sum_le _ _
      _ ≤ ∑ _d ∈ D, B := Finset.sum_le_sum h
      _ = (D.card : ℝ) * B := by simp
  calc
    ‖(∑ d ∈ D, f d) * (D.card : ℂ)⁻¹‖ = ‖∑ d ∈ D, f d‖ / (D.card : ℝ) := by
      rw [norm_mul, norm_inv, Complex.norm_natCast, div_eq_mul_inv]
    _ ≤ ((D.card : ℝ) * B) / (D.card : ℝ) := div_le_div_of_nonneg_right hsum hDc.le
    _ = B := by field_simp

theorem norm_product_average_binary_append_le {A D : Finset ℕ} {b r : ℕ}
    (hA : ∀ n ∈ A, n < 2 ^ b) (hD : D.Nonempty) (f : ℕ → ℂ) (M : ℝ)
    (hbound : ∀ L : List (Finset ℕ), L.length = r →
      (∀ B ∈ L, ∃ d ∈ D, B = natTranslate A (2 ^ b * d)) → ‖natProductAverage L f‖ ≤ M) :
    ‖natProductAverage (List.replicate r (binaryAppend A D b)) f‖ ≤ M := by
  have haux : ∀ k : ℕ, ∀ P : List (Finset ℕ), P.length + k = r →
      (∀ B ∈ P, ∃ d ∈ D, B = natTranslate A (2 ^ b * d)) →
      ‖natProductAverage (P ++ List.replicate k (binaryAppend A D b)) f‖ ≤ M := by
    intro k
    induction k with
    | zero =>
      intro P hlen hP
      simp only [List.replicate_zero, List.append_nil]
      apply hbound P (by simpa using hlen) hP
    | succ k ih =>
      intro P hlen hP
      rw [List.replicate_succ, nat_product_average_binary_append hA]
      apply norm_finset_average_le hD
      intro d hd
      have heq : P ++ natTranslate A (2 ^ b * d) :: List.replicate k (binaryAppend A D b) =
          (P ++ [natTranslate A (2 ^ b * d)]) ++ List.replicate k (binaryAppend A D b) := by simp
      rw [heq]
      apply ih
      · simp only [List.length_append, List.length_singleton]
        omega
      · intro B hB
        rcases List.mem_append.mp hB with hBP | hBd
        · exact hP B hBP
        · exact ⟨d, hd, List.mem_singleton.mp hBd⟩
  exact haux r [] (by simp) (by simp)

theorem nat_product_average_replicate_dft {q : ℕ} [NeZero q] (A : Finset ℕ) (r : ℕ) :
    ∀ k : ZMod q,
      natProductAverage (List.replicate r A) (fun n => ZMod.stdAddChar (-((n : ZMod q) * k))) =
        ZMod.dft (cyclicProductPow (cyclicUniformNatSet A) r) k := by
  induction r with
  | zero =>
    intro k
    simp [natProductAverage, cyclicProductPow, ZMod.dft_apply]
  | succ r ih =>
    intro k
    rw [List.replicate_succ, natProductAverage, dft_product_uniform_succ]
    congr 1
    apply Finset.sum_congr rfl
    intro n _
    have heq : (fun m : ℕ => ZMod.stdAddChar (-(((n * m : ℕ) : ZMod q) * k))) =
        (fun m : ℕ => ZMod.stdAddChar (-((m : ZMod q) * ((n : ZMod q) * k)))) := by
      funext m
      rw [Nat.cast_mul]
      congr 2
      ring
    rw [heq]
    exact ih _

def DyadicSetAdmissible (g : ℝ) (J : ℕ) (A : Finset ℕ) : Prop :=
  A.Nonempty ∧ Set.InjOn (fun n : ℕ => (n : ZMod (2 ^ J))) A ∧
    ∀ l : ℕ, 2 ≤ l → l ≤ J → ∀ x : ZMod (2 ^ l),
      ‖cyclicUniformNatSet A x‖ ≤ (2 : ℝ) ^ (-g * (l : ℝ))

/-- A set-valued analytic input. This proposition is not asserted as a theorem. -/
def DyadicSetMixing : Prop :=
  ∀ g : ℝ, 0 < g → g ≤ 1 / 2 → ∃ r : ℕ, ∃ t : ℝ, ∃ J₀ : ℕ,
    0 < r ∧ 0 < t ∧ ∀ J : ℕ, J₀ ≤ J → ∀ L : List (Finset ℕ),
      L.length = r → (∀ A ∈ L, DyadicSetAdmissible g J A) → ∀ a : ℕ, Odd a →
        ‖natProductAverage L (fun n => ZMod.stdAddChar (-((n : ZMod (2 ^ J)) * (a : ZMod (2 ^ J)))))‖ ≤
          (2 : ℝ) ^ (-t * (J : ℝ))

theorem factorial_block_all_profiles {a : ℝ} (ha : 1 < a) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 / 2 ∧ ∀ᶠ K : ℕ in Filter.atTop,
      2 ≤ factorialDigitBase a K ∧ factorialDigitBase a K ≤ K ∧
      ∀ i : ℕ, BinaryBlockProfile (factorialDigitHost a K) K
        (binaryBlockEndpoint K (factorialDigitBase a K) i) (i + 1) c
        (binaryBlockSet (factorialDigitHost a K) K (factorialDigitBase a K) i) := by
  obtain ⟨c₀, hc₀, hshort⟩ := shortFactorialDigits_uniform_asymptotic ha
  let c := min c₀ (1 / 2)
  have hc : 0 < c := lt_min hc₀ (by norm_num)
  have hcc : c ≤ c₀ := min_le_left _ _
  have hchalf : c ≤ 1 / 2 := min_le_right _ _
  refine ⟨c, hc, hchalf, ?_⟩
  filter_upwards [hshort, eventually_factorialDigitBase_bounds (by linarith : 0 < a)]
    with K hKshort hKb
  obtain ⟨hblo, hbK, hF⟩ := hKb
  have hD : ∀ l : ℕ, 1 ≤ l → l ≤ K →
      (2 : ℝ) ^ (c * (l : ℝ)) ≤ (shortFactorialDigits (factorialDigitHost a K) l).card := by
    intro l hl hlK
    exact (Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (mul_le_mul_of_nonneg_right hcc (Nat.cast_nonneg l))).trans (hKshort.2 l hl hlK)
  exact ⟨hblo, hbK, binary_block_set_profile hblo hbK hF hc.le hchalf hD⟩

theorem block_product_decay_of_set_mixing {a : ℝ} (ha : 1 < a) (hmix : DyadicSetMixing) :
    ∃ r : ℕ, ∃ t : ℝ, 0 < r ∧ 0 < t ∧ ∀ᶠ K : ℕ in Filter.atTop,
      ∀ x : ZMod (2 ^ K), factorialDigitBase a K < dyadicConductorLevel x →
        ‖ZMod.dft (cyclicProductPow (factorialBlockLaw a K) r) x‖ ≤
          (2 : ℝ) ^ (-t * (dyadicConductorLevel x : ℝ)) := by
  obtain ⟨c, hc, hchalf, hprofiles⟩ := factorial_block_all_profiles ha
  obtain ⟨r, t, J₀, hr, ht, hmix⟩ := hmix (c / 2) (by positivity) (by linarith)
  refine ⟨r, t, hr, ht, ?_⟩
  filter_upwards [hprofiles, (factorialDigitBase_tendsto (by linarith : 0 < a)).eventually_ge_atTop J₀]
    with K hK hKbase
  intro x hx
  have hxne : x ≠ 0 := by
    intro hzero
    subst x
    simp [dyadicConductorLevel] at hx
  obtain ⟨m, hm, hfrequency⟩ := dyadic_frequency_factor hxne
  have hjK := (dyadic_conductor_spec x).1
  obtain ⟨i, hi, hbi, hjb⟩ := binary_block_prefix_at_level (by omega : 1 ≤ factorialDigitBase a K) hx hjK
  have hprefix := hK.2.2 i
  obtain ⟨D, hD, hfactor⟩ := binary_block_set_factors_at_prefix (factorialDigitHost a K) K
    (factorialDigitBase a K) i (binaryLength K) hi
  have hfactor' : factorialBlockSet a K = binaryAppend
      (binaryBlockSet (factorialDigitHost a K) K (factorialDigitBase a K) i) D
      (binaryBlockEndpoint K (factorialDigitBase a K) i) := hfactor
  have hbound : ‖natProductAverage (List.replicate r (factorialBlockSet a K))
      (fun n => ZMod.stdAddChar (-((n : ZMod (2 ^ dyadicConductorLevel x)) *
        (m : ZMod (2 ^ dyadicConductorLevel x)))))‖ ≤
          (2 : ℝ) ^ (-t * (dyadicConductorLevel x : ℝ)) := by
    rw [hfactor']
    apply norm_product_average_binary_append_le hprefix.bounded hD
    intro L hlen hL
    apply hmix (dyadicConductorLevel x) (by omega) L hlen _ m hm
    intro B hB
    obtain ⟨d, _, rfl⟩ := hL B hB
    exact translated_binary_prefix_spread hprefix hc.le hbi hjb _
  have htransfer := dft_product_uniform_transfer (factorialBlockSet a K) r x
    (m : ZMod (2 ^ dyadicConductorLevel x)) (fun n => dyadic_frequency_phase hjK hfrequency n)
  change ‖ZMod.dft (cyclicProductPow (cyclicUniformNatSet (factorialBlockSet a K)) r) x‖ ≤ _
  rw [htransfer, ← nat_product_average_replicate_dft]
  exact hbound

theorem dyadic_modular_bounds_of_dyadic_set_mixing {a b : ℝ}
    (ha : 1 < a) (hb : 0 < b) (hmix : DyadicSetMixing) : DyadicModularBounds a b := by
  exact dyadic_modular_bounds_of_block_product_decay ha hb (block_product_decay_of_set_mixing ha hmix)

theorem erdos18b_of_dyadic_set_mixing (hmix : DyadicSetMixing) :
    fcTypeOfName% "Erdos18.erdos_18b" := by
  exact erdos18b_of_dyadic_modular_bounds
    (fun _ _ ha hb => dyadic_modular_bounds_of_dyadic_set_mixing ha hb hmix)

theorem nat_residue_mass_mod (A : Finset ℕ) (q y : ℕ) :
    natResidueMass A q (y % q) = natResidueMass A q y := by
  unfold natResidueMass natResidueFiber
  simp only [Nat.ModEq, Nat.mod_mod]
  rfl

theorem nat_residue_mass_lt_iff {A : Finset ℕ} (hA : A.Nonempty) (q y : ℕ) (z : ℝ) :
    natResidueMass A q y < z ↔ ((natResidueFiber A q y).card : ℝ) < z * (A.card : ℝ) := by
  have hcard : (0 : ℝ) < A.card := by exact_mod_cast Finset.card_pos.mpr hA
  exact div_lt_iff₀ hcard

theorem dyadic_large_divisor_iff (ε : ℝ) (J l : ℕ) :
    (((2 ^ J : ℕ) : ℝ) ^ ε < ((2 ^ l : ℕ) : ℝ)) ↔ ε * (J : ℝ) < (l : ℝ) := by
  simp only [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast]
  rw [← Real.rpow_mul (by norm_num), Real.rpow_lt_rpow_left_iff (by norm_num)]
  rw [mul_comm]

/-- The dyadic specialization of the set estimate in Bourgain (2007), Theorem 2.
The casts are injective so that the natural-number sets represent uniform sets
modulo the full modulus. Only sufficiently large divisors have a fiber hypothesis.
This stronger optional proposition is not used by the final proof of `target`. -/
def BourgainDyadicSetEstimate : Prop :=
  ∀ γ : ℝ, 0 < γ → ∃ ε t : ℝ, ∃ r J₀ : ℕ,
    0 < ε ∧ 0 < t ∧ 0 < r ∧ ∀ J : ℕ, J₀ ≤ J → ∀ L : List (Finset ℕ),
      L.length = r →
      (∀ A ∈ L, A.Nonempty ∧ Set.InjOn (fun n : ℕ => (n : ZMod (2 ^ J))) A ∧
        ∀ l : ℕ, l ≤ J → ε * (J : ℝ) < (l : ℝ) → ∀ y : ℕ,
          natResidueMass A (2 ^ l) y < (2 : ℝ) ^ (-γ * (l : ℝ))) →
      ∀ a : ℕ, Odd a →
        ‖natProductAverage L (fun n => ZMod.stdAddChar (-((n : ZMod (2 ^ J)) * (a : ZMod (2 ^ J)))))‖ <
          (2 : ℝ) ^ (-t * (J : ℝ))

theorem dyadic_set_mixing_of_bourgain_dyadic_set_estimate
    (hB : BourgainDyadicSetEstimate) : DyadicSetMixing := by
  intro g hg _
  obtain ⟨ε, t, r, J₀, hε, ht, hr, hB⟩ := hB (g / 2) (by positivity)
  refine ⟨r, t, max J₀ ⌈2 / ε⌉₊, hr, ht, ?_⟩
  intro J hJ L hlen hL a ha
  have hJ₀ : J₀ ≤ J := (le_max_left _ _).trans hJ
  have hJceil : ⌈2 / ε⌉₊ ≤ J := (le_max_right _ _).trans hJ
  have hJeps : 2 ≤ ε * (J : ℝ) := by
    have hcast : (2 / ε : ℝ) ≤ J := (Nat.le_ceil _).trans (by exact_mod_cast hJceil)
    have hprod := (div_le_iff₀ hε).mp hcast
    simpa only [mul_comm] using hprod
  apply le_of_lt (hB J hJ₀ L hlen _ a ha)
  intro A hA
  obtain ⟨hne, hinj, hspread⟩ := hL A hA
  refine ⟨hne, hinj, ?_⟩
  intro l hlJ hlε y
  have hlreal : (2 : ℝ) < l := hJeps.trans_lt hlε
  have hl : 2 ≤ l := by exact_mod_cast hlreal.le
  have hmass : natResidueMass A (2 ^ l) y ≤ (2 : ℝ) ^ (-g * (l : ℝ)) := by
    simpa only [norm_cyclicUniformNatSet, ZMod.val_natCast, nat_residue_mass_mod]
      using hspread l hl hlJ (y : ZMod (2 ^ l))
  refine hmass.trans_lt (Real.rpow_lt_rpow_of_exponent_lt (by norm_num) ?_)
  nlinarith [mul_pos hg (show (0 : ℝ) < l by linarith)]

theorem erdos18b_of_bourgain_dyadic_set_estimate (hB : BourgainDyadicSetEstimate) :
    fcTypeOfName% "Erdos18.erdos_18b" := by
  exact erdos18b_of_dyadic_set_mixing (dyadic_set_mixing_of_bourgain_dyadic_set_estimate hB)

/- Elementary Fourier estimates used in the fixed-prime analytic argument. -/

theorem conjugate_stdAddChar {q : ℕ} [NeZero q] (x : ZMod q) :
    starRingEnd ℂ (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  rw [ZMod.stdAddChar_apply, ZMod.stdAddChar_apply, AddChar.map_neg_eq_inv,
    Circle.coe_inv_eq_conj]

theorem dft_conjugate {q : ℕ} [NeZero q] (f : ZMod q → ℂ) (k : ZMod q) :
    ZMod.dft (fun x => starRingEnd ℂ (f x)) k = starRingEnd ℂ (ZMod.dft f (-k)) := by
  simp only [ZMod.dft_apply, smul_eq_mul, map_sum, map_mul, mul_neg, neg_neg,
    conjugate_stdAddChar]

theorem dft_bilinear_pairing {q : ℕ} [NeZero q] (f g : ZMod q → ℂ) :
    (∑ k : ZMod q, ZMod.dft f k * g k) = ∑ x : ZMod q, f x * ZMod.dft g x := by
  simp only [ZMod.dft_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro k _
  rw [mul_comm k x]
  ring

theorem dft_parseval {q : ℕ} [NeZero q] (f : ZMod q → ℂ) :
    (∑ k : ZMod q, ‖ZMod.dft f k‖ ^ 2) = (q : ℝ) * ∑ x : ZMod q, ‖f x‖ ^ 2 := by
  have hpair := dft_bilinear_pairing f (fun k => starRingEnd ℂ (ZMod.dft f k))
  simp_rw [dft_conjugate] at hpair
  simp only [ZMod.dft_dft, neg_neg, smul_eq_mul, map_mul, map_natCast] at hpair
  have hcomplex : (∑ k : ZMod q, ZMod.dft f k * starRingEnd ℂ (ZMod.dft f k)) =
      (q : ℂ) * ∑ x : ZMod q, f x * starRingEnd ℂ (f x) := by
    rw [hpair, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  simp only [Complex.mul_conj'] at hcomplex
  apply Complex.ofReal_injective
  push_cast
  exact hcomplex

theorem norm_dft_mulconv_sq_le {q : ℕ} [NeZero q]
    (f g : ZMod q → ℂ) {k : ZMod q} (hk : IsUnit k) :
    ‖ZMod.dft (cyclicMultiplicativeConvolution f g) k‖ ^ 2 ≤
      (∑ x : ZMod q, ‖g x‖ ^ 2) * ((q : ℝ) * ∑ x : ZMod q, ‖f x‖ ^ 2) := by
  obtain ⟨u, rfl⟩ := hk
  have hperm : (∑ x : ZMod q, ‖ZMod.dft f (x * (u : ZMod q))‖ ^ 2) =
      ∑ x : ZMod q, ‖ZMod.dft f x‖ ^ 2 := by
    exact Fintype.sum_equiv u.mulRight _ _ (fun _ => rfl)
  rw [dft_cyclicMultiplicativeConvolution]
  calc
    ‖∑ x : ZMod q, g x * ZMod.dft f (x * (u : ZMod q))‖ ^ 2 ≤
        (∑ x : ZMod q, ‖g x‖ * ‖ZMod.dft f (x * (u : ZMod q))‖) ^ 2 := by
      apply pow_le_pow_left₀ (norm_nonneg _) _ 2
      simpa only [norm_mul] using norm_sum_le Finset.univ
        (fun x : ZMod q => g x * ZMod.dft f (x * (u : ZMod q)))
    _ ≤ (∑ x : ZMod q, ‖g x‖ ^ 2) *
        ∑ x : ZMod q, ‖ZMod.dft f (x * (u : ZMod q))‖ ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ = _ := by rw [hperm, dft_parseval]

theorem sum_norm_cyclicUniformNatSet {q : ℕ} [NeZero q] {A : Finset ℕ} (hA : A.Nonempty) :
    (∑ x : ZMod q, ‖cyclicUniformNatSet A x‖) = 1 := by
  have hsum := dft_cyclicUniformNatSet_at_zero (q := q) hA
  rw [ZMod.dft_apply_zero] at hsum
  have hre := congrArg Complex.re hsum
  simp only [norm_cyclicUniformNatSet]
  simpa only [Complex.re_sum, cyclicUniformNatSet_eq_residue_mass, Complex.ofReal_re,
    Complex.one_re] using hre

theorem sum_sq_norm_cyclicUniformNatSet_le {q : ℕ} [NeZero q]
    {A : Finset ℕ} (hA : A.Nonempty) {M : ℝ}
    (hM : ∀ x : ZMod q, ‖cyclicUniformNatSet A x‖ ≤ M) :
    (∑ x : ZMod q, ‖cyclicUniformNatSet A x‖ ^ 2) ≤ M := by
  calc
    _ ≤ ∑ x : ZMod q, M * ‖cyclicUniformNatSet A x‖ := by
      apply Finset.sum_le_sum
      intro x _
      simpa only [pow_two] using mul_le_mul_of_nonneg_right (hM x) (norm_nonneg _)
    _ = M := by rw [← Finset.mul_sum, sum_norm_cyclicUniformNatSet hA, mul_one]

theorem norm_dft_mulconv_uniform_sq_le {q : ℕ} [NeZero q]
    {A B : Finset ℕ} (hA : A.Nonempty) (hB : B.Nonempty) {M₁ M₂ : ℝ}
    (hM₁ : ∀ x : ZMod q, ‖cyclicUniformNatSet A x‖ ≤ M₁)
    (hM₂ : ∀ x : ZMod q, ‖cyclicUniformNatSet B x‖ ≤ M₂)
    {k : ZMod q} (hk : IsUnit k) :
    ‖ZMod.dft (cyclicMultiplicativeConvolution (cyclicUniformNatSet A)
      (cyclicUniformNatSet B)) k‖ ^ 2 ≤ (q : ℝ) * M₁ * M₂ := by
  have hM₂pos : 0 ≤ M₂ := (norm_nonneg (cyclicUniformNatSet B (0 : ZMod q))).trans (hM₂ 0)
  calc
    _ ≤ (∑ x : ZMod q, ‖cyclicUniformNatSet B x‖ ^ 2) *
        ((q : ℝ) * ∑ x : ZMod q, ‖cyclicUniformNatSet A x‖ ^ 2) :=
      norm_dft_mulconv_sq_le _ _ hk
    _ ≤ M₂ * ((q : ℝ) * M₁) := by
      apply mul_le_mul (sum_sq_norm_cyclicUniformNatSet_le hB hM₂)
        (mul_le_mul_of_nonneg_left (sum_sq_norm_cyclicUniformNatSet_le hA hM₁)
          (Nat.cast_nonneg q))
      · positivity
      · exact hM₂pos
    _ = _ := by ring

theorem norm_dft_mulconv_uniform_dyadic_le {J : ℕ} {A B : Finset ℕ}
    (hA : A.Nonempty) (hB : B.Nonempty) {g₁ g₂ : ℝ}
    (hM₁ : ∀ x : ZMod (2 ^ J), ‖cyclicUniformNatSet A x‖ ≤ (2 : ℝ) ^ (-g₁ * (J : ℝ)))
    (hM₂ : ∀ x : ZMod (2 ^ J), ‖cyclicUniformNatSet B x‖ ≤ (2 : ℝ) ^ (-g₂ * (J : ℝ)))
    {k : ZMod (2 ^ J)} (hk : IsUnit k) :
    ‖ZMod.dft (cyclicMultiplicativeConvolution (cyclicUniformNatSet A)
      (cyclicUniformNatSet B)) k‖ ≤ (2 : ℝ) ^ (-((g₁ + g₂ - 1) / 2) * (J : ℝ)) := by
  have hs := norm_dft_mulconv_uniform_sq_le hA hB hM₁ hM₂ hk
  have heq : ((2 ^ J : ℕ) : ℝ) * (2 : ℝ) ^ (-g₁ * (J : ℝ)) *
      (2 : ℝ) ^ (-g₂ * (J : ℝ)) =
      ((2 : ℝ) ^ (-((g₁ + g₂ - 1) / 2) * (J : ℝ))) ^ 2 := by
    rw [show ((2 ^ J : ℕ) : ℝ) = (2 : ℝ) ^ (J : ℝ) by simp,
      ← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num),
      ← Real.rpow_mul_natCast (by norm_num)]
    congr 1
    push_cast
    ring
  rw [heq] at hs
  have hp : 0 < (2 : ℝ) ^ (-((g₁ + g₂ - 1) / 2) * (J : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  nlinarith [norm_nonneg (ZMod.dft (cyclicMultiplicativeConvolution
    (cyclicUniformNatSet A) (cyclicUniformNatSet B)) k)]

theorem sum_uniformNatSet_mul {q : ℕ} [NeZero q] (A : Finset ℕ) (F : ZMod q → ℂ) :
    (∑ x : ZMod q, cyclicUniformNatSet A x * F x) =
      (∑ n ∈ A, F (n : ZMod q)) * (A.card : ℂ)⁻¹ := by
  classical
  unfold cyclicUniformNatSet cyclicPushforward
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [ite_mul, zero_mul]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.sum_coe_sort A (fun n : ℕ => (A.card : ℂ)⁻¹ * F (n : ZMod q))]
  apply Finset.sum_congr rfl
  intro n _
  ring

theorem dft_mulconv_uniform {q : ℕ} [NeZero q] (A B : Finset ℕ) (k : ZMod q) :
    ZMod.dft (cyclicMultiplicativeConvolution (cyclicUniformNatSet A)
      (cyclicUniformNatSet B)) k =
      (∑ b ∈ B, ZMod.dft (cyclicUniformNatSet A) ((b : ZMod q) * k)) * (B.card : ℂ)⁻¹ := by
  rw [dft_cyclicMultiplicativeConvolution, sum_uniformNatSet_mul]

theorem dft_mulconv_uniform_transfer {Q q : ℕ} [NeZero Q] [NeZero q]
    (A B : Finset ℕ) (x : ZMod Q) (y : ZMod q)
    (hphase : ∀ n : ℕ, ZMod.stdAddChar (-((n : ZMod Q) * x)) =
      ZMod.stdAddChar (-((n : ZMod q) * y))) :
    ZMod.dft (cyclicMultiplicativeConvolution (cyclicUniformNatSet A)
      (cyclicUniformNatSet B)) x =
      ZMod.dft (cyclicMultiplicativeConvolution (cyclicUniformNatSet A)
        (cyclicUniformNatSet B)) y := by
  rw [dft_mulconv_uniform, dft_mulconv_uniform]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  rw [dft_cyclicUniformNatSet, dft_cyclicUniformNatSet]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  simpa only [Nat.cast_mul, mul_assoc] using hphase (a * b)

theorem odd_natCast_isUnit_dyadic (J : ℕ) {m : ℕ} (hm : Odd m) :
    IsUnit (m : ZMod (2 ^ J)) := by
  apply (ZMod.isUnit_iff_coprime _ _).mpr
  have hcop : Nat.Coprime m 2 := by
    rw [Nat.coprime_comm, Nat.prime_two.coprime_iff_not_dvd]
    obtain ⟨t, ht⟩ := hm
    omega
  exact hcop.pow_right J

theorem norm_dft_mulconv_uniform_conductor_le {K : ℕ} {A B : Finset ℕ}
    (hA : A.Nonempty) (hB : B.Nonempty) {g₁ g₂ : ℝ}
    (hM₁ : ∀ j : ℕ, 1 ≤ j → j ≤ K → ∀ x : ZMod (2 ^ j),
      ‖cyclicUniformNatSet A x‖ ≤ (2 : ℝ) ^ (-g₁ * (j : ℝ)))
    (hM₂ : ∀ j : ℕ, 1 ≤ j → j ≤ K → ∀ x : ZMod (2 ^ j),
      ‖cyclicUniformNatSet B x‖ ≤ (2 : ℝ) ^ (-g₂ * (j : ℝ)))
    {x : ZMod (2 ^ K)} (hx : x ≠ 0) :
    ‖ZMod.dft (cyclicMultiplicativeConvolution (cyclicUniformNatSet A)
      (cyclicUniformNatSet B)) x‖ ≤
      (2 : ℝ) ^ (-((g₁ + g₂ - 1) / 2) * (dyadicConductorLevel x : ℝ)) := by
  have hj : 1 ≤ dyadicConductorLevel x := dyadic_conductor_pos hx
  have hjK : dyadicConductorLevel x ≤ K := (dyadic_conductor_spec x).1
  obtain ⟨m, hm, hfactor⟩ := dyadic_frequency_factor hx
  rw [dft_mulconv_uniform_transfer A B x (m : ZMod (2 ^ dyadicConductorLevel x))
    (fun n => dyadic_frequency_phase hjK hfactor n)]
  exact norm_dft_mulconv_uniform_dyadic_le hA hB (hM₁ _ hj hjK) (hM₂ _ hj hjK)
    (odd_natCast_isUnit_dyadic _ hm)

theorem exists_power_mulconv_uniform_nonzero {g₁ g₂ : ℝ} (hg : 1 < g₁ + g₂) :
    ∃ s : ℕ, 0 < s ∧ ∀ K : ℕ, ∀ A B : Finset ℕ, A.Nonempty → B.Nonempty →
      (∀ j : ℕ, 1 ≤ j → j ≤ K → ∀ x : ZMod (2 ^ j),
        ‖cyclicUniformNatSet A x‖ ≤ (2 : ℝ) ^ (-g₁ * (j : ℝ))) →
      (∀ j : ℕ, 1 ≤ j → j ≤ K → ∀ x : ZMod (2 ^ j),
        ‖cyclicUniformNatSet B x‖ ≤ (2 : ℝ) ^ (-g₂ * (j : ℝ))) →
      ∀ x : ZMod (2 ^ K), cyclicConvolutionPow
        (cyclicMultiplicativeConvolution (cyclicUniformNatSet A) (cyclicUniformNatSet B)) s x ≠ 0 := by
  obtain ⟨s, hs, hsum⟩ := exists_convolution_power_for_dyadic_decay
    (show 0 < (g₁ + g₂ - 1) / 2 by linarith)
  refine ⟨s, hs, ?_⟩
  intro K A B hA hB hM₁ hM₂
  apply convolution_pow_nonzero_of_fourier_bound
  · rw [dft_cyclicMultiplicativeConvolution_at_zero, dft_cyclicUniformNatSet_at_zero hA,
      dft_cyclicUniformNatSet_at_zero hB, mul_one]
  · apply hsum
    intro x hx
    exact norm_dft_mulconv_uniform_conductor_le hA hB hM₁ hM₂ hx

theorem exists_subset_with_prescribed_fiber_card {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (f : α → β) (P : Finset β) (k : ℕ)
    (hk : ∀ b ∈ P, k ≤ (S.filter (fun a => f a = b)).card) :
    ∃ U : Finset α, U ⊆ S ∧ U.image f ⊆ P ∧
      (∀ b ∈ P, (U.filter (fun a => f a = b)).card = k) ∧ U.card = P.card * k := by
  classical
  have hchoose : ∀ b : β, ∃ V : Finset α,
      V ⊆ S.filter (fun a => f a = b) ∧ (b ∈ P → V.card = k) := by
    intro b
    by_cases hb : b ∈ P
    · obtain ⟨V, hV, hcard⟩ := Finset.exists_subset_card_eq (hk b hb)
      exact ⟨V, hV, fun _ => hcard⟩
    · exact ⟨∅, Finset.empty_subset _, by simp [hb]⟩
  choose V hV hcard using hchoose
  let U := P.biUnion V
  have hU : U ⊆ S := by
    intro a ha
    obtain ⟨b, hb, hab⟩ := Finset.mem_biUnion.mp ha
    exact (Finset.mem_filter.mp (hV b hab)).1
  have himage : U.image f ⊆ P := by
    intro b hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨c, hc, hac⟩ := Finset.mem_biUnion.mp ha
    exact (Finset.mem_filter.mp (hV c hac)).2.symm ▸ hc
  have hfiber : ∀ b ∈ P, U.filter (fun a => f a = b) = V b := by
    intro b hb
    ext a
    constructor
    · intro ha
      obtain ⟨haU, hab⟩ := Finset.mem_filter.mp ha
      obtain ⟨c, hc, hac⟩ := Finset.mem_biUnion.mp haU
      have hcb : c = b := (Finset.mem_filter.mp (hV c hac)).2.symm.trans hab
      exact hcb ▸ hac
    · intro ha
      exact Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨b, hb, ha⟩,
        (Finset.mem_filter.mp (hV b ha)).2⟩
  have hdisjoint : (P : Set β).PairwiseDisjoint V := by
    intro b hb c hc hbc
    apply Finset.disjoint_left.mpr
    intro a hab hac
    exact hbc ((Finset.mem_filter.mp (hV b hab)).2.symm.trans (Finset.mem_filter.mp (hV c hac)).2)
  refine ⟨U, hU, himage, ?_, ?_⟩
  · intro b hb
    rw [hfiber b hb, hcard b hb]
  · change (P.biUnion V).card = _
    rw [Finset.card_biUnion hdisjoint]
    calc
      ∑ b ∈ P, (V b).card = ∑ _b ∈ P, k := Finset.sum_congr rfl hcard
      _ = _ := by simp

theorem exists_dyadic_uniform_fibers {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (f : α → β) (T : ℕ)
    (hbound : ∀ b ∈ S.image f, (S.filter (fun a => f a = b)).card ≤ 2 ^ T) :
    ∃ k : ℕ, k ≤ T ∧ ∃ U : Finset α, U ⊆ S ∧
      S.card ≤ 2 * (T + 1) * U.card ∧
      ∀ b ∈ U.image f, (U.filter (fun a => f a = b)).card = 2 ^ k := by
  classical
  let P := S.image f
  let c : β → ℕ := fun b => (S.filter (fun a => f a = b)).card
  let bucket : ℕ → Finset β := fun k => P.filter (fun b => Nat.log 2 (c b) = k)
  let w : ℕ → ℕ := fun k => ∑ b ∈ bucket k, c b
  have hcpos : ∀ b ∈ P, c b ≠ 0 := by
    intro b hb
    obtain ⟨a, ha, hab⟩ := Finset.mem_image.mp hb
    exact Finset.card_ne_zero.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, hab⟩⟩
  have hmaps : ∀ b ∈ P, Nat.log 2 (c b) ∈ Finset.range (T + 1) := by
    intro b hb
    apply Finset.mem_range.mpr
    have hlog := Nat.log_monotone (b := 2) (hbound b hb)
    rw [Nat.log_pow (by decide : 1 < 2)] at hlog
    change Nat.log 2 (c b) ≤ T at hlog
    omega
  have hsum : (∑ k ∈ Finset.range (T + 1), w k) = S.card := by
    change (∑ k ∈ Finset.range (T + 1), ∑ b ∈ P.filter (fun b => Nat.log 2 (c b) = k), c b) = _
    rw [Finset.sum_fiberwise_of_maps_to hmaps]
    exact (Finset.card_eq_sum_card_image f S).symm
  obtain ⟨k, hk, hmax⟩ := Finset.exists_max_image (Finset.range (T + 1)) w
    (Finset.nonempty_range_iff.mpr (by omega))
  have hbig : S.card ≤ (T + 1) * w k := by
    rw [← hsum]
    calc
      _ ≤ ∑ _i ∈ Finset.range (T + 1), w k := Finset.sum_le_sum hmax
      _ = _ := by simp
  have hlo : ∀ b ∈ bucket k, 2 ^ k ≤ c b := by
    intro b hb
    obtain ⟨hbP, hlog⟩ := Finset.mem_filter.mp hb
    rw [← hlog]
    exact Nat.pow_log_le_self 2 (hcpos b hbP)
  have hhi : ∀ b ∈ bucket k, c b ≤ 2 * 2 ^ k := by
    intro b hb
    have hlog := (Finset.mem_filter.mp hb).2
    have hpow := (Nat.lt_pow_succ_log_self (by decide : 1 < 2) (c b)).le
    simpa only [hlog, Nat.succ_eq_add_one, pow_succ, Nat.mul_comm] using hpow
  obtain ⟨U, hUS, hUP, hfiber, hcard⟩ :=
    exists_subset_with_prescribed_fiber_card S f (bucket k) (2 ^ k) hlo
  have hw : w k ≤ 2 * U.card := by
    change (∑ b ∈ bucket k, c b) ≤ _
    calc
      _ ≤ ∑ _b ∈ bucket k, 2 * 2 ^ k := Finset.sum_le_sum hhi
      _ = 2 * U.card := by simp only [Finset.sum_const, smul_eq_mul, hcard]; ring
  refine ⟨k, by have := Finset.mem_range.mp hk; omega, U, hUS, ?_, ?_⟩
  · calc
      S.card ≤ (T + 1) * w k := hbig
      _ ≤ (T + 1) * (2 * U.card) := Nat.mul_le_mul_left _ hw
      _ = _ := by ring
  · intro b hb
    exact hfiber b (hUP hb)

theorem exists_dyadic_first_split {A : Finset ℕ} {b e : ℕ}
    (hcard : 1 < A.card) (hbound : ∀ x ∈ A, x < 2 ^ e)
    (hbase : ∀ x ∈ A, ∀ y ∈ A, x % 2 ^ b = y % 2 ^ b) :
    ∃ m : ℕ, b ≤ m ∧ m < e ∧
      (∀ x ∈ A, ∀ y ∈ A, x % 2 ^ m = y % 2 ^ m) ∧
      ∃ x ∈ A, ∃ y ∈ A, x % 2 ^ (m + 1) ≠ y % 2 ^ (m + 1) := by
  classical
  let P : ℕ → Prop := fun l => ∃ x ∈ A, ∃ y ∈ A, x % 2 ^ l ≠ y % 2 ^ l
  have hPe : P e := by
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hcard
    refine ⟨x, hx, y, hy, ?_⟩
    simpa only [Nat.mod_eq_of_lt (hbound x hx), Nat.mod_eq_of_lt (hbound y hy)] using hxy
  have hex : ∃ l, P l := ⟨e, hPe⟩
  let l := Nat.find hex
  have hl : P l := Nat.find_spec hex
  have hle : l ≤ e := Nat.find_min' hex hPe
  have hbl : b < l := by
    by_contra hn
    have hlb : l ≤ b := by omega
    obtain ⟨x, hx, y, hy, hxy⟩ := hl
    have hmod : Nat.ModEq (2 ^ b) x y := hbase x hx y hy
    exact hxy (hmod.of_dvd (pow_dvd_pow 2 hlb))
  refine ⟨l - 1, by omega, by omega, ?_, ?_⟩
  · intro x hx y hy
    by_contra hxy
    exact (Nat.find_min hex (show l - 1 < l by omega)) ⟨x, hx, y, hy, hxy⟩
  · simpa only [Nat.sub_add_cancel (show 1 ≤ l by omega)] using hl

theorem dyadic_residue_fiber_card_le {A : Finset ℕ} {b T : ℕ}
    (hbound : ∀ x ∈ A, x < 2 ^ (b + T)) (r : ℕ) :
    (A.filter (fun x => x % 2 ^ b = r)).card ≤ 2 ^ T := by
  classical
  let S := A.filter (fun x => x % 2 ^ b = r)
  have hinj : Set.InjOn (fun x : ℕ => x / 2 ^ b) S := by
    intro x hx y hy hdiv
    have hmod : x % 2 ^ b = y % 2 ^ b :=
      (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm
    change x / 2 ^ b = y / 2 ^ b at hdiv
    calc
      x = x % 2 ^ b + 2 ^ b * (x / 2 ^ b) := (Nat.mod_add_div x (2 ^ b)).symm
      _ = y % 2 ^ b + 2 ^ b * (y / 2 ^ b) := by rw [hmod, hdiv]
      _ = y := Nat.mod_add_div y (2 ^ b)
  have himage : S.image (fun x => x / 2 ^ b) ⊆ Finset.range (2 ^ T) := by
    intro n hn
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hn
    apply Finset.mem_range.mpr
    apply (Nat.div_lt_iff_lt_mul (by positivity : 0 < 2 ^ b)).mpr
    simpa only [pow_add, Nat.mul_comm] using hbound x (Finset.mem_filter.mp hx).1
  calc
    _ = (S.image (fun x => x / 2 ^ b)).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.range (2 ^ T)).card := Finset.card_le_card himage
    _ = _ := Finset.card_range _

theorem exists_large_fiber {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (f : α → β) (P : Finset β) (hP : P.Nonempty)
    (hmaps : ∀ a ∈ S, f a ∈ P) :
    ∃ b ∈ P, S.card ≤ P.card * (S.filter (fun a => f a = b)).card := by
  classical
  obtain ⟨b, hb, hmax⟩ := Finset.exists_max_image P
    (fun b => (S.filter (fun a => f a = b)).card) hP
  refine ⟨b, hb, ?_⟩
  calc
    S.card = ∑ c ∈ P, (S.filter (fun a => f a = c)).card :=
      Finset.card_eq_sum_card_fiberwise hmaps
    _ ≤ ∑ _c ∈ P, (S.filter (fun a => f a = b)).card := Finset.sum_le_sum hmax
    _ = _ := by simp

-- The auxiliary choice of a level is intentionally unconstrained outside the image of S.
theorem exists_dyadic_regular_block {A : Finset ℕ} {b T : ℕ} (hT : 0 < T)
    (hbound : ∀ x ∈ A, x < 2 ^ (b + T)) :
    ∃ U : Finset ℕ, U ⊆ A ∧ ∃ m k : ℕ, b ≤ m ∧ m < b + T ∧ k ≤ T ∧
      A.card ≤ 2 * (T + 1) ^ 2 * U.card ∧
      (∀ x ∈ U, ∀ y ∈ U, x % 2 ^ b = y % 2 ^ b → x % 2 ^ m = y % 2 ^ m) ∧
      ∀ r ∈ U.image (fun x => x % 2 ^ m),
        (U.filter (fun x => x % 2 ^ m = r)).card = 2 ^ k ∧
        (0 < k → ∃ x ∈ U.filter (fun x => x % 2 ^ m = r),
          ∃ y ∈ U.filter (fun x => x % 2 ^ m = r), x % 2 ^ (m + 1) ≠ y % 2 ^ (m + 1)) := by
  classical
  obtain ⟨k, hkT, S, hSA, hsize, hcard⟩ := exists_dyadic_uniform_fibers A
    (fun x => x % 2 ^ b) T (fun r _ => dyadic_residue_fiber_card_le hbound r)
  by_cases hk : k = 0
  · refine ⟨S, hSA, b, k, le_rfl, by omega, hkT, ?_, ?_, ?_⟩
    · exact hsize.trans (Nat.mul_le_mul_right S.card (by nlinarith))
    · intro x hx y hy hxy
      exact hxy
    · intro r hr
      exact ⟨hcard r hr, by simp [hk]⟩
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk
  let P := S.image (fun x => x % 2 ^ b)
  let F : ℕ → Finset ℕ := fun r => S.filter (fun x => x % 2 ^ b = r)
  have hchoose : ∀ r : ℕ, ∃ m : ℕ, r ∈ P → b ≤ m ∧ m < b + T ∧
      (∀ x ∈ F r, ∀ y ∈ F r, x % 2 ^ m = y % 2 ^ m) ∧
      ∃ x ∈ F r, ∃ y ∈ F r, x % 2 ^ (m + 1) ≠ y % 2 ^ (m + 1) := by
    intro r
    by_cases hr : r ∈ P
    · have hFr : 1 < (F r).card := by
        rw [show (F r).card = 2 ^ k from hcard r hr]
        exact one_lt_pow₀ (by decide : 1 < (2 : ℕ)) hkpos.ne'
      obtain ⟨m, hm⟩ := exists_dyadic_first_split hFr
        (fun x hx => hbound x (hSA (Finset.mem_filter.mp hx).1))
        (fun x hx y hy => (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm)
      exact ⟨m, fun _ => hm⟩
    · exact ⟨b, fun h => (hr h).elim⟩
  choose level hlevel using hchoose
  have hmaps : ∀ x ∈ S, level (x % 2 ^ b) ∈ Finset.Ico b (b + T) := by
    intro x hx
    have hh := hlevel (x % 2 ^ b) (Finset.mem_image_of_mem _ hx)
    exact Finset.mem_Ico.mpr ⟨hh.1, hh.2.1⟩
  obtain ⟨m, hm, hlarge⟩ := exists_large_fiber S (fun x => level (x % 2 ^ b))
    (Finset.Ico b (b + T)) (Finset.nonempty_Ico.mpr (by omega)) hmaps
  have hbm : b ≤ m := (Finset.mem_Ico.mp hm).1
  have hme : m < b + T := (Finset.mem_Ico.mp hm).2
  let U := S.filter (fun x => level (x % 2 ^ b) = m)
  have hUS : U ⊆ S := Finset.filter_subset _ _
  have hlarge' : S.card ≤ T * U.card := by simpa only [Nat.card_Ico, Nat.add_sub_cancel_left] using hlarge
  have hcommon : ∀ x ∈ U, ∀ y ∈ U, x % 2 ^ b = y % 2 ^ b → x % 2 ^ m = y % 2 ^ m := by
    intro x hx y hy hxy
    have hxS : x ∈ S := hUS hx
    have hh := hlevel (x % 2 ^ b) (Finset.mem_image_of_mem _ hxS)
    have hxm : level (x % 2 ^ b) = m := (Finset.mem_filter.mp hx).2
    rw [hxm] at hh
    exact hh.2.2.1 x (Finset.mem_filter.mpr ⟨hxS, rfl⟩) y
      (Finset.mem_filter.mpr ⟨hUS hy, hxy.symm⟩)
  refine ⟨U, hUS.trans hSA, m, k, hbm, hme, hkT, ?_, hcommon, ?_⟩
  · calc
      A.card ≤ 2 * (T + 1) * S.card := hsize
      _ ≤ 2 * (T + 1) * (T * U.card) := Nat.mul_le_mul_left _ hlarge'
      _ = (2 * (T + 1) * T) * U.card := by ring
      _ ≤ 2 * (T + 1) ^ 2 * U.card := Nat.mul_le_mul_right _ (by nlinarith)
  · intro r hr
    obtain ⟨a, haU, har⟩ := Finset.mem_image.mp hr
    have haS := hUS haU
    have habP : a % 2 ^ b ∈ P := Finset.mem_image_of_mem _ haS
    have hla : level (a % 2 ^ b) = m := (Finset.mem_filter.mp haU).2
    have hh := hlevel (a % 2 ^ b) habP
    rw [hla] at hh
    have hfiber : U.filter (fun x => x % 2 ^ m = r) = F (a % 2 ^ b) := by
      ext x
      constructor
      · intro hx
        obtain ⟨hxU, hxr⟩ := Finset.mem_filter.mp hx
        have hxm : Nat.ModEq (2 ^ m) x a := hxr.trans har.symm
        exact Finset.mem_filter.mpr ⟨hUS hxU, hxm.of_dvd (pow_dvd_pow 2 hbm)⟩
      · intro hx
        obtain ⟨hxS, hxb⟩ := Finset.mem_filter.mp hx
        have hxU : x ∈ U := Finset.mem_filter.mpr ⟨hxS, by rw [hxb, hla]⟩
        have hxa := hh.2.2.1 x (Finset.mem_filter.mpr ⟨hxS, hxb⟩) a
          (Finset.mem_filter.mpr ⟨haS, rfl⟩)
        exact Finset.mem_filter.mpr ⟨hxU, hxa.trans har⟩
    refine ⟨?_, fun _ => ?_⟩
    · rw [hfiber]
      exact hcard _ habP
    · rw [hfiber]
      exact hh.2.2.2

def dyadicProjection (A : Finset ℕ) (j : ℕ) : Finset ℕ :=
  A.image (fun x => x % 2 ^ j)

def dyadicLift (A : Finset ℕ) (j : ℕ) (P : Finset ℕ) : Finset ℕ :=
  A.filter (fun x => x % 2 ^ j ∈ P)

theorem dyadic_projection_bounded (A : Finset ℕ) (j : ℕ) :
    ∀ x ∈ dyadicProjection A j, x < 2 ^ j := by
  intro x hx
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  exact Nat.mod_lt _ (by positivity)

theorem dyadic_projection_self {A : Finset ℕ} {j : ℕ}
    (hA : ∀ x ∈ A, x < 2 ^ j) : dyadicProjection A j = A := by
  ext x
  constructor
  · intro hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    simpa only [Nat.mod_eq_of_lt (hA a ha)] using ha
  · intro hx
    exact Finset.mem_image.mpr ⟨x, hx, Nat.mod_eq_of_lt (hA x hx)⟩

theorem dyadic_projection_trans (A : Finset ℕ) {j k : ℕ} (hjk : j ≤ k) :
    dyadicProjection (dyadicProjection A k) j = dyadicProjection A j := by
  unfold dyadicProjection
  rw [Finset.image_image]
  apply Finset.image_congr
  intro x hx
  exact Nat.mod_mod_of_dvd x (pow_dvd_pow 2 hjk)

theorem dyadic_lift_subset (A : Finset ℕ) (j : ℕ) (P : Finset ℕ) :
    dyadicLift A j P ⊆ A := Finset.filter_subset _ _

theorem dyadic_projection_lift {A P : Finset ℕ} {j : ℕ}
    (hP : P ⊆ dyadicProjection A j) : dyadicProjection (dyadicLift A j P) j = P := by
  ext r
  constructor
  · intro hr
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hr
    exact (Finset.mem_filter.mp ha).2
  · intro hr
    obtain ⟨a, ha, har⟩ := Finset.mem_image.mp (hP hr)
    exact Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, har.symm ▸ hr⟩, har⟩

theorem dyadic_lift_fiber {A P : Finset ℕ} {j r : ℕ} (hr : r ∈ P) :
    (dyadicLift A j P).filter (fun x => x % 2 ^ j = r) =
      A.filter (fun x => x % 2 ^ j = r) := by
  ext x
  constructor
  · intro hx
    obtain ⟨hx, hxr⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1, hxr⟩
  · intro hx
    obtain ⟨hx, hxr⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hx, hxr.symm ▸ hr⟩, hxr⟩

theorem dyadic_lift_card {A P : Finset ℕ} {j v : ℕ}
    (hcard : ∀ r ∈ P, (A.filter (fun x => x % 2 ^ j = r)).card = v) :
    (dyadicLift A j P).card = P.card * v := by
  have hmaps : ∀ x ∈ dyadicLift A j P, x % 2 ^ j ∈ P := by
    intro x hx
    exact (Finset.mem_filter.mp hx).2
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  calc
    _ = ∑ _r ∈ P, v := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [dyadic_lift_fiber hr, hcard r hr]
    _ = _ := by simp

structure DyadicTreeBlock (A : Finset ℕ) (b T m k : ℕ) : Prop where
  base_le : b ≤ m
  split_lt : m < b + T
  count_le : k ≤ T
  common : ∀ x ∈ A, ∀ y ∈ A, x % 2 ^ b = y % 2 ^ b → x % 2 ^ m = y % 2 ^ m
  fiber_card : ∀ r ∈ dyadicProjection A m,
    (A.filter (fun x => x % 2 ^ m = r)).card = 2 ^ k
  splits : ∀ r ∈ dyadicProjection A m, 0 < k →
    ∃ x ∈ A.filter (fun x => x % 2 ^ m = r),
      ∃ y ∈ A.filter (fun x => x % 2 ^ m = r), x % 2 ^ (m + 1) ≠ y % 2 ^ (m + 1)

theorem exists_dyadic_tree_block {A : Finset ℕ} {b T : ℕ} (hT : 0 < T)
    (hbound : ∀ x ∈ A, x < 2 ^ (b + T)) :
    ∃ U : Finset ℕ, U ⊆ A ∧ ∃ m k : ℕ,
      DyadicTreeBlock U b T m k ∧ A.card ≤ 2 * (T + 1) ^ 2 * U.card := by
  obtain ⟨U, hUA, m, k, hbm, hme, hk, hsize, hcommon, hfiber⟩ :=
    exists_dyadic_regular_block hT hbound
  exact ⟨U, hUA, m, k, ⟨hbm, hme, hk, hcommon,
    fun r hr => (hfiber r hr).1, fun r hr => (hfiber r hr).2⟩, hsize⟩

theorem dyadic_tree_block_base_fiber {A : Finset ℕ} {b T m k a : ℕ}
    (hA : DyadicTreeBlock A b T m k) (ha : a ∈ A) :
    A.filter (fun x => x % 2 ^ b = a % 2 ^ b) =
      A.filter (fun x => x % 2 ^ m = a % 2 ^ m) := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxA, hxb⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hxA, hA.common x hxA a ha hxb⟩
  · intro hx
    obtain ⟨hxA, hxm⟩ := Finset.mem_filter.mp hx
    have hmod : Nat.ModEq (2 ^ m) x a := hxm
    exact Finset.mem_filter.mpr ⟨hxA, hmod.of_dvd (pow_dvd_pow 2 hA.base_le)⟩

theorem dyadic_tree_block_base_card {A : Finset ℕ} {b T m k : ℕ}
    (hA : DyadicTreeBlock A b T m k) :
    ∀ r ∈ dyadicProjection A b, (A.filter (fun x => x % 2 ^ b = r)).card = 2 ^ k := by
  intro r hr
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hr
  rw [dyadic_tree_block_base_fiber hA ha]
  exact hA.fiber_card _ (Finset.mem_image_of_mem _ ha)

theorem dyadic_tree_block_card {A : Finset ℕ} {b T m k : ℕ}
    (hA : DyadicTreeBlock A b T m k) : A.card = (dyadicProjection A b).card * 2 ^ k := by
  rw [Finset.card_eq_sum_card_image (fun x => x % 2 ^ b) A]
  calc
    _ = ∑ _r ∈ dyadicProjection A b, 2 ^ k :=
      Finset.sum_congr rfl (dyadic_tree_block_base_card hA)
    _ = _ := by simp

theorem dyadic_tree_block_lift {A : Finset ℕ} {b T m k : ℕ}
    (hA : DyadicTreeBlock A b T m k) (P : Finset ℕ) :
    DyadicTreeBlock (dyadicLift A b P) b T m k := by
  have hsub := dyadic_lift_subset A b P
  have hfiber : ∀ r ∈ dyadicProjection (dyadicLift A b P) m,
      (dyadicLift A b P).filter (fun x => x % 2 ^ m = r) =
        A.filter (fun x => x % 2 ^ m = r) := by
    intro r hr
    obtain ⟨a, ha, har⟩ := Finset.mem_image.mp hr
    have haP : a % 2 ^ b ∈ P := (Finset.mem_filter.mp ha).2
    ext x
    constructor
    · intro hx
      obtain ⟨hx, hxr⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr ⟨hsub hx, hxr⟩
    · intro hx
      obtain ⟨hxA, hxr⟩ := Finset.mem_filter.mp hx
      have hmod : Nat.ModEq (2 ^ m) x a := hxr.trans har.symm
      have hxb : x % 2 ^ b = a % 2 ^ b := hmod.of_dvd (pow_dvd_pow 2 hA.base_le)
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hxA, hxb.symm ▸ haP⟩, hxr⟩
  have hproj : dyadicProjection (dyadicLift A b P) m ⊆ dyadicProjection A m :=
    Finset.image_subset_image hsub
  refine ⟨hA.base_le, hA.split_lt, hA.count_le, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    exact hA.common x (hsub hx) y (hsub hy) hxy
  · intro r hr
    rw [hfiber r hr]
    exact hA.fiber_card r (hproj hr)
  · intro r hr hk
    rw [hfiber r hr]
    exact hA.splits r (hproj hr) hk

def DyadicRegularTree (A : Finset ℕ) (T N : ℕ) : Prop :=
  ∀ i : ℕ, i < N → ∃ m k : ℕ,
    DyadicTreeBlock (dyadicProjection A (T * (i + 1))) (T * i) T m k

theorem exists_dyadic_regular_tree (T : ℕ) (hT : 0 < T) :
    ∀ N : ℕ, ∀ A : Finset ℕ, (∀ x ∈ A, x < 2 ^ (T * N)) →
      ∃ B : Finset ℕ, B ⊆ A ∧ DyadicRegularTree B T N ∧
        A.card ≤ (2 * (T + 1) ^ 2) ^ N * B.card := by
  intro N
  induction N with
  | zero =>
    intro A hA
    exact ⟨A, Finset.Subset.refl _, by intro i hi; omega, by simp⟩
  | succ N ih =>
    intro A hA
    have hA' : ∀ x ∈ A, x < 2 ^ (T * N + T) := by
      simpa only [Nat.mul_add, Nat.mul_one] using hA
    obtain ⟨U, hUA, m, k, hblock, hsize⟩ := exists_dyadic_tree_block hT hA'
    obtain ⟨B, hBP, htree, hBsize⟩ := ih (dyadicProjection U (T * N))
      (dyadic_projection_bounded U (T * N))
    let V := dyadicLift U (T * N) B
    have hVU : V ⊆ U := dyadic_lift_subset _ _ _
    have hVA : V ⊆ A := hVU.trans hUA
    have hVB : dyadicProjection V (T * N) = B := dyadic_projection_lift hBP
    have hVcard : V.card = B.card * 2 ^ k :=
      dyadic_lift_card (fun r hr => dyadic_tree_block_base_card hblock r (hBP hr))
    refine ⟨V, hVA, ?_, ?_⟩
    · intro i hi
      by_cases hiN : i < N
      · obtain ⟨mi, ki, hBi⟩ := htree i hiN
        have hle : T * (i + 1) ≤ T * N := Nat.mul_le_mul_left T (by omega)
        have hproj : dyadicProjection V (T * (i + 1)) = dyadicProjection B (T * (i + 1)) := by
          rw [← hVB]
          exact (dyadic_projection_trans V hle).symm
        exact ⟨mi, ki, hproj.symm ▸ hBi⟩
      · have hiEq : i = N := by omega
        subst i
        refine ⟨m, k, ?_⟩
        rw [dyadic_projection_self (fun x hx => hA x (hVA hx))]
        exact dyadic_tree_block_lift hblock B
    · calc
        A.card ≤ 2 * (T + 1) ^ 2 * U.card := hsize
        _ = (2 * (T + 1) ^ 2) * ((dyadicProjection U (T * N)).card * 2 ^ k) := by
          rw [dyadic_tree_block_card hblock]
        _ ≤ (2 * (T + 1) ^ 2) * (((2 * (T + 1) ^ 2) ^ N * B.card) * 2 ^ k) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hBsize)
        _ = (2 * (T + 1) ^ 2) ^ (N + 1) * V.card := by rw [hVcard, pow_succ]; ring

theorem eventually_dyadic_regularization_cost_le {η : ℝ} (hη : 0 < η) :
    ∀ᶠ T : ℕ in Filter.atTop,
      (2 : ℝ) * ((T : ℝ) + 1) ^ 2 ≤ (2 : ℝ) ^ (η * (T : ℝ)) := by
  have hb : 0 < Real.log 2 * η := mul_pos (Real.log_pos (by norm_num)) hη
  have hsmall := ((isLittleO_pow_exp_pos_mul_atTop 2 hb).const_mul_left (8 : ℝ)).comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [hsmall.def (by norm_num : (0 : ℝ) < 1), eventually_ge_atTop (1 : ℕ)] with T hT hTpos
  have hTreal : (1 : ℝ) ≤ T := by exact_mod_cast hTpos
  have hexp : 8 * (T : ℝ) ^ 2 ≤ Real.exp ((Real.log 2 * η) * (T : ℝ)) := by
    simpa only [Function.comp_apply, Real.norm_eq_abs, one_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 8 * (T : ℝ) ^ 2),
      abs_of_pos (Real.exp_pos _)] using hT
  calc
    (2 : ℝ) * ((T : ℝ) + 1) ^ 2 ≤ 8 * (T : ℝ) ^ 2 := by nlinarith
    _ ≤ Real.exp ((Real.log 2 * η) * (T : ℝ)) := hexp
    _ = (2 : ℝ) ^ (η * (T : ℝ)) := by rw [Real.rpow_def_of_pos (by norm_num), mul_assoc]

theorem exists_dyadic_regular_tree_small_loss {η : ℝ} (hη : 0 < η) :
    ∃ T : ℕ, 0 < T ∧ ∀ N : ℕ, ∀ A : Finset ℕ, (∀ x ∈ A, x < 2 ^ (T * N)) →
      ∃ B : Finset ℕ, B ⊆ A ∧ DyadicRegularTree B T N ∧
        (A.card : ℝ) ≤ (2 : ℝ) ^ (η * ((T * N : ℕ) : ℝ)) * (B.card : ℝ) := by
  obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.mp (eventually_dyadic_regularization_cost_le hη)
  let T := max T₀ 1
  have hT : 0 < T := lt_of_lt_of_le (by decide : 0 < 1) (le_max_right _ _)
  have hcost : (2 : ℝ) * ((T : ℝ) + 1) ^ 2 ≤ (2 : ℝ) ^ (η * (T : ℝ)) :=
    hT₀ T (le_max_left _ _)
  refine ⟨T, hT, ?_⟩
  intro N A hA
  obtain ⟨B, hBA, htree, hsize⟩ := exists_dyadic_regular_tree T hT N A hA
  refine ⟨B, hBA, htree, ?_⟩
  have hsize' : (A.card : ℝ) ≤ ((2 : ℝ) * ((T : ℝ) + 1) ^ 2) ^ N * (B.card : ℝ) := by
    exact_mod_cast hsize
  calc
    (A.card : ℝ) ≤ ((2 : ℝ) * ((T : ℝ) + 1) ^ 2) ^ N * (B.card : ℝ) := hsize'
    _ ≤ ((2 : ℝ) ^ (η * (T : ℝ))) ^ N * (B.card : ℝ) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hcost N) (Nat.cast_nonneg _)
    _ = (2 : ℝ) ^ (η * ((T * N : ℕ) : ℝ)) * (B.card : ℝ) := by
      rw [← Real.rpow_mul_natCast (by norm_num), Nat.cast_mul, mul_assoc]

theorem dyadic_projection_fiber_self {A : Finset ℕ} {j r : ℕ}
    (hr : r ∈ dyadicProjection A j) :
    (dyadicProjection A j).filter (fun x => x % 2 ^ j = r) = {r} := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxP, hxr⟩ := Finset.mem_filter.mp hx
    have hxlt := dyadic_projection_bounded A j x hxP
    rw [Nat.mod_eq_of_lt hxlt] at hxr
    exact Finset.mem_singleton.mpr hxr
  · intro hx
    have hxr := Finset.mem_singleton.mp hx
    subst x
    exact Finset.mem_filter.mpr ⟨hr, Nat.mod_eq_of_lt (dyadic_projection_bounded A j r hr)⟩

theorem dyadic_lift_coarse_fiber (A : Finset ℕ) {b e : ℕ} (hbe : b ≤ e) (r : ℕ) :
    dyadicLift A e ((dyadicProjection A e).filter (fun y => y % 2 ^ b = r)) =
      A.filter (fun x => x % 2 ^ b = r) := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxA, hxf⟩ := Finset.mem_filter.mp hx
    have hmod := (Finset.mem_filter.mp hxf).2
    rw [Nat.mod_mod_of_dvd x (pow_dvd_pow 2 hbe)] at hmod
    exact Finset.mem_filter.mpr ⟨hxA, hmod⟩
  · intro hx
    obtain ⟨hxA, hxr⟩ := Finset.mem_filter.mp hx
    refine Finset.mem_filter.mpr ⟨hxA, Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ hxA, ?_⟩⟩
    rwa [Nat.mod_mod_of_dvd x (pow_dvd_pow 2 hbe)]

theorem dyadic_fiber_card_mul (A : Finset ℕ) {b e v : ℕ} (hbe : b ≤ e)
    (hcard : ∀ s ∈ dyadicProjection A e, (A.filter (fun x => x % 2 ^ e = s)).card = v) (r : ℕ) :
    (A.filter (fun x => x % 2 ^ b = r)).card =
      ((dyadicProjection A e).filter (fun x => x % 2 ^ b = r)).card * v := by
  rw [← dyadic_lift_coarse_fiber A hbe r]
  exact dyadic_lift_card (fun s hs => hcard s (Finset.mem_filter.mp hs).1)

theorem dyadic_regular_tree_uniform_fibers {A : Finset ℕ} {T N : ℕ}
    (htree : DyadicRegularTree A T N) : ∀ j : ℕ, j ≤ N → ∀ i : ℕ, i ≤ j →
      ∃ v : ℕ, 0 < v ∧ ∀ r ∈ dyadicProjection A (T * i),
        ((dyadicProjection A (T * j)).filter (fun x => x % 2 ^ (T * i) = r)).card = v := by
  intro j
  induction j with
  | zero =>
    intro hj i hi
    have hi0 : i = 0 := by omega
    subst i
    refine ⟨1, by decide, ?_⟩
    intro r hr
    rw [dyadic_projection_fiber_self hr, Finset.card_singleton]
  | succ j ih =>
    intro hj i hi
    by_cases hij : i = j + 1
    · subst i
      refine ⟨1, by decide, ?_⟩
      intro r hr
      rw [dyadic_projection_fiber_self hr, Finset.card_singleton]
    have hij' : i ≤ j := by omega
    obtain ⟨v, hv, hvc⟩ := ih (by omega) i hij'
    obtain ⟨m, k, hblock⟩ := htree j (by omega)
    refine ⟨v * 2 ^ k, by positivity, ?_⟩
    intro r hr
    rw [dyadic_fiber_card_mul _ (Nat.mul_le_mul_left T hij')
      (dyadic_tree_block_base_card hblock) r]
    rw [dyadic_projection_trans A (Nat.mul_le_mul_left T (show j ≤ j + 1 by omega)), hvc r hr]

theorem dyadic_regular_tree_residue_mass {A : Finset ℕ} {T N i r : ℕ}
    (htree : DyadicRegularTree A T N) (hbound : ∀ x ∈ A, x < 2 ^ (T * N))
    (hi : i ≤ N) (hr : r ∈ dyadicProjection A (T * i)) :
    natResidueMass A (2 ^ (T * i)) r = 1 / ((dyadicProjection A (T * i)).card : ℝ) := by
  obtain ⟨v, hv, hvc⟩ := dyadic_regular_tree_uniform_fibers htree N le_rfl i hi
  rw [dyadic_projection_self hbound] at hvc
  have hcard : A.card = (dyadicProjection A (T * i)).card * v := by
    rw [Finset.card_eq_sum_card_image (fun x => x % 2 ^ (T * i)) A]
    calc
      _ = ∑ _s ∈ dyadicProjection A (T * i), v := Finset.sum_congr rfl hvc
      _ = _ := by simp
  have hfiber : (natResidueFiber A (2 ^ (T * i)) r).card = v := by
    simpa only [natResidueFiber, Nat.ModEq,
      Nat.mod_eq_of_lt (dyadic_projection_bounded A (T * i) r hr)] using hvc r hr
  have hvR : (v : ℝ) ≠ 0 := by exact_mod_cast hv.ne'
  have hcR : ((dyadicProjection A (T * i)).card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr ⟨r, hr⟩
  unfold natResidueMass
  rw [hfiber, hcard, Nat.cast_mul]
  field_simp

theorem nat_sumset_card_ge_projection_mul_fiber (A B : Finset ℕ) (q : ℕ)
    (hB : ∀ x ∈ B, ∀ y ∈ B, x % q = y % q) :
    (A.image (fun x => x % q)).card * B.card ≤
      ((A ×ˢ B).image (fun p => p.1 + p.2)).card := by
  classical
  have hnonempty : ∀ r ∈ A.image (fun x => x % q),
      1 ≤ (A.filter (fun x => x % q = r)).card := by
    intro r hr
    obtain ⟨x, hx, hxr⟩ := Finset.mem_image.mp hr
    exact Finset.card_pos.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, hxr⟩⟩
  obtain ⟨R, hRA, hRP, hfiber, hRcard⟩ := exists_subset_with_prescribed_fiber_card A
    (fun x => x % q) (A.image (fun x => x % q)) 1 hnonempty
  have hRinj : Set.InjOn (fun x : ℕ => x % q) R := by
    intro x hx y hy hxy
    have hcard : (R.filter (fun z => z % q = x % q)).card ≤ 1 := by
      rw [hfiber _ (Finset.mem_image_of_mem _ (hRA hx))]
    exact Finset.card_le_one.mp hcard x (Finset.mem_filter.mpr ⟨hx, rfl⟩) y
      (Finset.mem_filter.mpr ⟨hy, hxy.symm⟩)
  have hinj : Set.InjOn (fun p : ℕ × ℕ => p.1 + p.2) (R ×ˢ B : Finset (ℕ × ℕ)) := by
    intro p hp s hs hsum
    change p.1 + p.2 = s.1 + s.2 at hsum
    obtain ⟨hpR, hpB⟩ := Finset.mem_product.mp hp
    obtain ⟨hsR, hsB⟩ := Finset.mem_product.mp hs
    have hmodB : Nat.ModEq q p.2 s.2 := hB _ hpB _ hsB
    have hmodsum : Nat.ModEq q (p.1 + p.2) (s.1 + s.2) := by rw [hsum]
    have hfst : p.1 = s.1 := hRinj hpR hsR (hmodB.add_right_cancel hmodsum)
    have hsnd : p.2 = s.2 := by omega
    exact Prod.ext hfst hsnd
  calc
    _ = R.card * B.card := by rw [hRcard, mul_one]
    _ = (R ×ˢ B).card := (Finset.card_product R B).symm
    _ = ((R ×ˢ B).image (fun p => p.1 + p.2)).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ _ := Finset.card_le_card (Finset.image_subset_image
      (Finset.product_subset_product hRA (Finset.Subset.refl B)))

theorem dyadic_projection_zero {A : Finset ℕ} (hA : A.Nonempty) : dyadicProjection A 0 = {0} := by
  simpa only [dyadicProjection, pow_zero, Nat.mod_one] using Finset.image_const hA (0 : ℕ)

theorem exists_dyadic_prefix_growth {A : Finset ℕ} (hA : A.Nonempty) (T N : ℕ) (δ : ℝ) :
    ∃ i : ℕ, i ≤ N ∧ ((dyadicProjection A (T * i)).card : ℝ) ≤ (2 : ℝ) ^ (δ * ((T * i : ℕ) : ℝ)) ∧
      ∀ j : ℕ, i ≤ j → j ≤ N →
        ((dyadicProjection A (T * i)).card : ℝ) * (2 : ℝ) ^ (δ * ((T * (j - i) : ℕ) : ℝ)) ≤
          ((dyadicProjection A (T * j)).card : ℝ) := by
  classical
  let w : ℕ → ℝ := fun i => ((dyadicProjection A (T * i)).card : ℝ) /
    (2 : ℝ) ^ (δ * ((T * i : ℕ) : ℝ))
  obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image (Finset.range (N + 1)) w
    (Finset.nonempty_range_iff.mpr (by omega))
  have hpow (j : ℕ) : 0 < (2 : ℝ) ^ (δ * ((T * j : ℕ) : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hzero : w 0 = 1 := by
    simp only [w, dyadic_projection_zero hA, Finset.card_singleton,
      Nat.cast_one, Nat.cast_zero, mul_zero, Real.rpow_zero, div_one]
  have hiupper : ((dyadicProjection A (T * i)).card : ℝ) ≤ (2 : ℝ) ^ (δ * ((T * i : ℕ) : ℝ)) := by
    have hh := hmin 0 (Finset.mem_range.mpr (by omega : 0 < N + 1))
    rw [hzero] at hh
    exact (div_le_one (hpow i)).mp hh
  refine ⟨i, by have := Finset.mem_range.mp hi; omega, hiupper, ?_⟩
  intro j hij hjN
  have hh : ((dyadicProjection A (T * i)).card : ℝ) / (2 : ℝ) ^ (δ * ((T * i : ℕ) : ℝ)) ≤
      ((dyadicProjection A (T * j)).card : ℝ) / (2 : ℝ) ^ (δ * ((T * j : ℕ) : ℝ)) :=
    hmin j (Finset.mem_range.mpr (by omega))
  have hcross := (div_le_div_iff₀ (hpow i) (hpow j)).mp hh
  have hfactor : (2 : ℝ) ^ (δ * ((T * j : ℕ) : ℝ)) =
      (2 : ℝ) ^ (δ * ((T * i : ℕ) : ℝ)) * (2 : ℝ) ^ (δ * ((T * (j - i) : ℕ) : ℝ)) := by
    rw [← Real.rpow_add (by norm_num)]
    congr 1
    simp only [Nat.cast_mul, Nat.cast_sub hij]
    ring
  rw [hfactor] at hcross
  apply (mul_le_mul_iff_left₀ (hpow i)).mp
  convert hcross using 1
  ring

theorem dyadic_regular_tree_projection_growth_bound {A B : Finset ℕ} {T N i : ℕ}
    (hBA : B ⊆ A) (hB : B.Nonempty) (htree : DyadicRegularTree B T N)
    (hbound : ∀ x ∈ B, x < 2 ^ (T * N)) (hi : i ≤ N) :
    (dyadicProjection A (T * i)).card * B.card ≤
      (dyadicProjection B (T * i)).card * ((A ×ˢ A).image (fun p => p.1 + p.2)).card := by
  obtain ⟨v, hv, hvc⟩ := dyadic_regular_tree_uniform_fibers htree N le_rfl i hi
  rw [dyadic_projection_self hbound] at hvc
  obtain ⟨a, ha⟩ := hB
  let r := a % 2 ^ (T * i)
  have hr : r ∈ dyadicProjection B (T * i) := Finset.mem_image_of_mem _ ha
  let C := B.filter (fun x => x % 2 ^ (T * i) = r)
  have hCB : C ⊆ B := Finset.filter_subset _ _
  have hCA : C ⊆ A := hCB.trans hBA
  have hCcard : C.card = v := hvc r hr
  have hBcard : B.card = (dyadicProjection B (T * i)).card * v := by
    rw [Finset.card_eq_sum_card_image (fun x => x % 2 ^ (T * i)) B]
    calc
      _ = ∑ _s ∈ dyadicProjection B (T * i), v := Finset.sum_congr rfl hvc
      _ = _ := by simp
  have hsum : (dyadicProjection A (T * i)).card * v ≤
      ((A ×ˢ A).image (fun p => p.1 + p.2)).card := by
    rw [← hCcard]
    calc
      _ ≤ ((A ×ˢ C).image (fun p => p.1 + p.2)).card :=
        nat_sumset_card_ge_projection_mul_fiber A C (2 ^ (T * i))
          (fun x hx y hy => (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm)
      _ ≤ _ := Finset.card_le_card (Finset.image_subset_image
        (Finset.product_subset_product (Finset.Subset.refl A) hCA))
  rw [hBcard]
  calc
    _ = (dyadicProjection B (T * i)).card * ((dyadicProjection A (T * i)).card * v) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ hsum

theorem nat_modular_sumset_card_ge_projection_mul_fiber (A B : Finset ℕ) {q Q : ℕ}
    (hq : q ∣ Q) (hbound : ∀ x ∈ B, x < Q)
    (hB : ∀ x ∈ B, ∀ y ∈ B, x % q = y % q) :
    (A.image (fun x => x % q)).card * B.card ≤
      ((A ×ˢ B).image (fun p => (p.1 + p.2) % Q)).card := by
  classical
  have hnonempty : ∀ r ∈ A.image (fun x => x % q),
      1 ≤ (A.filter (fun x => x % q = r)).card := by
    intro r hr
    obtain ⟨x, hx, hxr⟩ := Finset.mem_image.mp hr
    exact Finset.card_pos.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, hxr⟩⟩
  obtain ⟨R, hRA, hRP, hfiber, hRcard⟩ := exists_subset_with_prescribed_fiber_card A
    (fun x => x % q) (A.image (fun x => x % q)) 1 hnonempty
  have hRinj : Set.InjOn (fun x : ℕ => x % q) R := by
    intro x hx y hy hxy
    have hcard : (R.filter (fun z => z % q = x % q)).card ≤ 1 := by
      rw [hfiber _ (Finset.mem_image_of_mem _ (hRA hx))]
    exact Finset.card_le_one.mp hcard x (Finset.mem_filter.mpr ⟨hx, rfl⟩) y
      (Finset.mem_filter.mpr ⟨hy, hxy.symm⟩)
  have hinj : Set.InjOn (fun p : ℕ × ℕ => (p.1 + p.2) % Q) (R ×ˢ B : Finset (ℕ × ℕ)) := by
    intro p hp s hs hsum
    change (p.1 + p.2) % Q = (s.1 + s.2) % Q at hsum
    obtain ⟨hpR, hpB⟩ := Finset.mem_product.mp hp
    obtain ⟨hsR, hsB⟩ := Finset.mem_product.mp hs
    have hmodB : Nat.ModEq q p.2 s.2 := hB _ hpB _ hsB
    have hmodsum : Nat.ModEq Q (p.1 + p.2) (s.1 + s.2) := hsum
    have hfst : p.1 = s.1 := hRinj hpR hsR (hmodB.add_right_cancel (hmodsum.of_dvd hq))
    have hmodsnd : Nat.ModEq Q p.2 s.2 := by
      rw [hfst] at hmodsum
      exact (Nat.ModEq.refl s.1).add_left_cancel hmodsum
    have hsnd : p.2 = s.2 := by
      simpa only [Nat.ModEq, Nat.mod_eq_of_lt (hbound _ hpB), Nat.mod_eq_of_lt (hbound _ hsB)] using hmodsnd
    exact Prod.ext hfst hsnd
  calc
    _ = R.card * B.card := by rw [hRcard, mul_one]
    _ = (R ×ˢ B).card := (Finset.card_product R B).symm
    _ = ((R ×ˢ B).image (fun p => (p.1 + p.2) % Q)).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ _ := Finset.card_le_card (Finset.image_subset_image
      (Finset.product_subset_product hRA (Finset.Subset.refl B)))

theorem dyadic_regular_tree_modular_growth_bound {A B : Finset ℕ} {T N i : ℕ}
    (hBA : B ⊆ A) (hB : B.Nonempty) (htree : DyadicRegularTree B T N)
    (hbound : ∀ x ∈ B, x < 2 ^ (T * N)) (hi : i ≤ N) :
    (dyadicProjection A (T * i)).card * B.card ≤
      (dyadicProjection B (T * i)).card *
        ((A ×ˢ A).image (fun p => (p.1 + p.2) % 2 ^ (T * N))).card := by
  obtain ⟨v, hv, hvc⟩ := dyadic_regular_tree_uniform_fibers htree N le_rfl i hi
  rw [dyadic_projection_self hbound] at hvc
  obtain ⟨a, ha⟩ := hB
  let r := a % 2 ^ (T * i)
  have hr : r ∈ dyadicProjection B (T * i) := Finset.mem_image_of_mem _ ha
  let C := B.filter (fun x => x % 2 ^ (T * i) = r)
  have hCB : C ⊆ B := Finset.filter_subset _ _
  have hCA : C ⊆ A := hCB.trans hBA
  have hCcard : C.card = v := hvc r hr
  have hBcard : B.card = (dyadicProjection B (T * i)).card * v := by
    rw [Finset.card_eq_sum_card_image (fun x => x % 2 ^ (T * i)) B]
    calc
      _ = ∑ _s ∈ dyadicProjection B (T * i), v := Finset.sum_congr rfl hvc
      _ = _ := by simp
  have hsum : (dyadicProjection A (T * i)).card * v ≤
      ((A ×ˢ A).image (fun p => (p.1 + p.2) % 2 ^ (T * N))).card := by
    rw [← hCcard]
    calc
      _ ≤ ((A ×ˢ C).image (fun p => (p.1 + p.2) % 2 ^ (T * N))).card :=
        nat_modular_sumset_card_ge_projection_mul_fiber A C (pow_dvd_pow 2 (Nat.mul_le_mul_left T hi))
          (fun x hx => hbound x (hCB hx))
          (fun x hx y hy => (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm)
      _ ≤ _ := Finset.card_le_card (Finset.image_subset_image
        (Finset.product_subset_product (Finset.Subset.refl A) hCA))
  rw [hBcard]
  calc
    _ = (dyadicProjection B (T * i)).card * ((dyadicProjection A (T * i)).card * v) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ hsum

theorem dyadic_projection_card_of_common {A : Finset ℕ} {b m : ℕ} (hbm : b ≤ m)
    (hcommon : ∀ x ∈ A, ∀ y ∈ A, x % 2 ^ b = y % 2 ^ b → x % 2 ^ m = y % 2 ^ m) :
    (dyadicProjection A m).card = (dyadicProjection A b).card := by
  have hinj : Set.InjOn (fun x : ℕ => x % 2 ^ b) (dyadicProjection A m) := by
    intro x hx y hy hxy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hy
    have hac : a % 2 ^ b = c % 2 ^ b := by
      simpa only [Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 hbm)] using hxy
    exact hcommon a ha c hc hac
  calc
    _ = (dyadicProjection (dyadicProjection A m) b).card := (Finset.card_image_of_injOn hinj).symm
    _ = _ := by rw [dyadic_projection_trans A hbm]

theorem exists_regular_tree_dense_tail {A B : Finset ℕ} {T N : ℕ}
    (hT : 0 < T) (hBA : B ⊆ A) (hB : B.Nonempty) (htree : DyadicRegularTree B T N)
    (hbound : ∀ x ∈ B, x < 2 ^ (T * N)) {γ δ ε η κ : ℝ}
    (hgap : δ < γ) (hbudget : κ + η ≤ ε * (γ - δ))
    (hlarge : (A.card : ℝ) ≤ (2 : ℝ) ^ (η * ((T * N : ℕ) : ℝ)) * (B.card : ℝ))
    (hsmall : (((A ×ˢ A).image (fun p => (p.1 + p.2) % 2 ^ (T * N))).card : ℝ) ≤
      (2 : ℝ) ^ (κ * ((T * N : ℕ) : ℝ)) * (A.card : ℝ))
    (hprojection : ∀ j : ℕ, j ≤ N → ε * (N : ℝ) < (j : ℝ) →
      (2 : ℝ) ^ (γ * ((T * j : ℕ) : ℝ)) ≤ ((dyadicProjection A (T * j)).card : ℝ)) :
    ∃ i : ℕ, i ≤ N ∧ (i : ℝ) ≤ ε * (N : ℝ) ∧
      ((dyadicProjection B (T * i)).card : ℝ) ≤ (2 : ℝ) ^ (δ * ((T * i : ℕ) : ℝ)) ∧
      ∀ j : ℕ, i ≤ j → j ≤ N →
        ((dyadicProjection B (T * i)).card : ℝ) * (2 : ℝ) ^ (δ * ((T * (j - i) : ℕ) : ℝ)) ≤
          ((dyadicProjection B (T * j)).card : ℝ) := by
  obtain ⟨i, hiN, hPi, htail⟩ := exists_dyadic_prefix_growth hB T N δ
  refine ⟨i, hiN, ?_, hPi, htail⟩
  by_contra hi
  have hiε : ε * (N : ℝ) < (i : ℝ) := lt_of_not_ge hi
  have hPA := hprojection i hiN hiε
  have hgrowth : ((dyadicProjection A (T * i)).card : ℝ) * (B.card : ℝ) ≤
      ((dyadicProjection B (T * i)).card : ℝ) *
        (((A ×ˢ A).image (fun p => (p.1 + p.2) % 2 ^ (T * N))).card : ℝ) := by
    exact_mod_cast dyadic_regular_tree_modular_growth_bound hBA hB htree hbound hiN
  have hprod : (2 : ℝ) ^ (γ * ((T * i : ℕ) : ℝ)) * (B.card : ℝ) ≤
      (2 : ℝ) ^ (δ * ((T * i : ℕ) : ℝ) + (κ + η) * ((T * N : ℕ) : ℝ)) * (B.card : ℝ) := by
    calc
      _ ≤ ((dyadicProjection A (T * i)).card : ℝ) * (B.card : ℝ) :=
        mul_le_mul_of_nonneg_right hPA (Nat.cast_nonneg _)
      _ ≤ _ := hgrowth
      _ ≤ (2 : ℝ) ^ (δ * ((T * i : ℕ) : ℝ)) *
          ((2 : ℝ) ^ (κ * ((T * N : ℕ) : ℝ)) * (A.card : ℝ)) :=
        mul_le_mul hPi hsmall (Nat.cast_nonneg _) (Real.rpow_nonneg (by norm_num) _)
      _ ≤ (2 : ℝ) ^ (δ * ((T * i : ℕ) : ℝ)) *
          ((2 : ℝ) ^ (κ * ((T * N : ℕ) : ℝ)) *
            ((2 : ℝ) ^ (η * ((T * N : ℕ) : ℝ)) * (B.card : ℝ))) := by
        apply mul_le_mul_of_nonneg_left
        · exact mul_le_mul_of_nonneg_left hlarge (Real.rpow_nonneg (by norm_num) _)
        · exact Real.rpow_nonneg (by norm_num) _
      _ = _ := by
        simp only [← mul_assoc]
        rw [← Real.rpow_add (show (0 : ℝ) < 2 by norm_num),
          ← Real.rpow_add (show (0 : ℝ) < 2 by norm_num)]
        congr 2
        ring
  have hBpos : (0 : ℝ) < B.card := by exact_mod_cast Finset.card_pos.mpr hB
  have hpow := (mul_le_mul_iff_of_pos_right hBpos).mp hprod
  have hexp := (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mp hpow
  simp only [Nat.cast_mul] at hexp
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have htailbound : (γ - δ) * (i : ℝ) ≤ (κ + η) * (N : ℝ) := by
    apply (mul_le_mul_iff_of_pos_left hTpos).mp
    nlinarith [hexp]
  have hbudgetN := mul_le_mul_of_nonneg_right hbudget (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  have hcancel : (γ - δ) * (i : ℝ) ≤ (γ - δ) * (ε * (N : ℝ)) := by nlinarith
  exact hi ((mul_le_mul_iff_of_pos_left (sub_pos.mpr hgap)).mp hcancel)

def dyadicZoom (A : Finset ℕ) (b r : ℕ) : Finset ℕ :=
  (A.filter (fun x => x % 2 ^ b = r)).image (fun x => x / 2 ^ b)

theorem dyadic_zoom_card (A : Finset ℕ) (b r : ℕ) :
    (dyadicZoom A b r).card = (A.filter (fun x => x % 2 ^ b = r)).card := by
  apply Finset.card_image_of_injOn
  intro x hx y hy hdiv
  change x / 2 ^ b = y / 2 ^ b at hdiv
  have hmod : x % 2 ^ b = y % 2 ^ b :=
    (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm
  calc
    x = x % 2 ^ b + 2 ^ b * (x / 2 ^ b) := (Nat.mod_add_div x (2 ^ b)).symm
    _ = y % 2 ^ b + 2 ^ b * (y / 2 ^ b) := by rw [hmod, hdiv]
    _ = y := Nat.mod_add_div y (2 ^ b)

theorem dyadic_zoom_nonempty {A : Finset ℕ} {b r : ℕ} (hr : r ∈ dyadicProjection A b) :
    (dyadicZoom A b r).Nonempty := by
  obtain ⟨a, ha, har⟩ := Finset.mem_image.mp hr
  exact (show (A.filter (fun x => x % 2 ^ b = r)).Nonempty from
    ⟨a, Finset.mem_filter.mpr ⟨ha, har⟩⟩).image _

theorem dyadic_zoom_bounded {A : Finset ℕ} {b e : ℕ}
    (hA : ∀ x ∈ A, x < 2 ^ (b + e)) (r : ℕ) :
    ∀ x ∈ dyadicZoom A b r, x < 2 ^ e := by
  intro x hx
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  apply (Nat.div_lt_iff_lt_mul (by positivity : 0 < 2 ^ b)).mpr
  simpa only [pow_add, Nat.mul_comm] using hA a (Finset.mem_filter.mp ha).1

theorem dyadic_projection_zoom (A : Finset ℕ) (b r l : ℕ) :
    dyadicProjection (dyadicZoom A b r) l = dyadicZoom (dyadicProjection A (b + l)) b r := by
  have hmod (a : ℕ) : a % 2 ^ (b + l) % 2 ^ b = a % 2 ^ b :=
    Nat.mod_mod_of_dvd a (pow_dvd_pow 2 (by omega))
  have hdiv (a : ℕ) : a % 2 ^ (b + l) / 2 ^ b = a / 2 ^ b % 2 ^ l := by
    rw [pow_add]
    exact Nat.mod_mul_right_div_self _ _ _
  ext z
  constructor
  · intro hz
    obtain ⟨y, hy, hyz⟩ := Finset.mem_image.mp hz
    obtain ⟨a, ha, hay⟩ := Finset.mem_image.mp hy
    obtain ⟨haA, har⟩ := Finset.mem_filter.mp ha
    refine Finset.mem_image.mpr ⟨a % 2 ^ (b + l), ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ haA, (hmod a).trans har⟩
    · rw [hdiv a, hay, hyz]
  · intro hz
    obtain ⟨y, hy, hyz⟩ := Finset.mem_image.mp hz
    obtain ⟨hyP, hyr⟩ := Finset.mem_filter.mp hy
    obtain ⟨a, haA, hay⟩ := Finset.mem_image.mp hyP
    have har : a % 2 ^ b = r := by rw [← hmod a, hay, hyr]
    refine Finset.mem_image.mpr ⟨a / 2 ^ b, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨haA, har⟩, rfl⟩
    · rw [← hdiv a, hay, hyz]

theorem dyadic_regular_tree_zoom_projection_card {A : Finset ℕ} {T N i j r : ℕ}
    (htree : DyadicRegularTree A T N) (hij : i + j ≤ N)
    (hr : r ∈ dyadicProjection A (T * i)) :
    (dyadicProjection A (T * i)).card *
      (dyadicProjection (dyadicZoom A (T * i) r) (T * j)).card =
      (dyadicProjection A (T * (i + j))).card := by
  have hlevel : T * i ≤ T * (i + j) := Nat.mul_le_mul_left T (by omega)
  obtain ⟨v, hv, hvc⟩ := dyadic_regular_tree_uniform_fibers htree (i + j) hij i (by omega)
  have hcard : (dyadicProjection A (T * (i + j))).card = (dyadicProjection A (T * i)).card * v := by
    rw [Finset.card_eq_sum_card_image (fun x => x % 2 ^ (T * i)) (dyadicProjection A (T * (i + j)))]
    change (∑ s ∈ dyadicProjection (dyadicProjection A (T * (i + j))) (T * i), _) = _
    rw [dyadic_projection_trans A hlevel]
    calc
      _ = ∑ _s ∈ dyadicProjection A (T * i), v := Finset.sum_congr rfl hvc
      _ = _ := by simp
  rw [dyadic_projection_zoom, ← Nat.mul_add, dyadic_zoom_card, hvc r hr, hcard]

theorem dyadic_regular_tree_zoom_card {A : Finset ℕ} {T N i r : ℕ}
    (htree : DyadicRegularTree A T N) (hbound : ∀ x ∈ A, x < 2 ^ (T * N)) (hi : i ≤ N)
    (hr : r ∈ dyadicProjection A (T * i)) :
    (dyadicProjection A (T * i)).card * (dyadicZoom A (T * i) r).card = A.card := by
  have hzoom := dyadic_zoom_bounded (b := T * i) (e := T * (N - i))
    (by simpa only [← Nat.mul_add, Nat.add_sub_of_le hi] using hbound) r
  have hh := dyadic_regular_tree_zoom_projection_card (j := N - i) htree (by omega) hr
  simpa only [dyadic_projection_self hzoom, Nat.add_sub_of_le hi, dyadic_projection_self hbound] using hh

theorem dyadic_regular_tree_zoom_growth {A : Finset ℕ} {T N i r : ℕ} {δ : ℝ}
    (htree : DyadicRegularTree A T N) (hr : r ∈ dyadicProjection A (T * i))
    (hgrowth : ∀ j : ℕ, i ≤ j → j ≤ N →
      ((dyadicProjection A (T * i)).card : ℝ) * (2 : ℝ) ^ (δ * ((T * (j - i) : ℕ) : ℝ)) ≤
        ((dyadicProjection A (T * j)).card : ℝ)) :
    ∀ j : ℕ, i + j ≤ N → (2 : ℝ) ^ (δ * ((T * j : ℕ) : ℝ)) ≤
      ((dyadicProjection (dyadicZoom A (T * i) r) (T * j)).card : ℝ) := by
  intro j hj
  have hpos : (0 : ℝ) < (dyadicProjection A (T * i)).card := by
    exact_mod_cast Finset.card_pos.mpr ⟨r, hr⟩
  have hh := hgrowth (i + j) (by omega) hj
  rw [Nat.add_sub_cancel_left] at hh
  have heq : ((dyadicProjection A (T * i)).card : ℝ) *
      ((dyadicProjection (dyadicZoom A (T * i) r) (T * j)).card : ℝ) =
      ((dyadicProjection A (T * (i + j))).card : ℝ) := by
    exact_mod_cast dyadic_regular_tree_zoom_projection_card htree hj hr
  rw [← heq] at hh
  exact (mul_le_mul_iff_of_pos_left hpos).mp hh

theorem dyadic_join_injective (d r : ℕ) :
    Function.Injective (fun x : ℕ => r + 2 ^ d * x) := by
  intro x y hxy
  exact Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2 ^ d) (Nat.add_left_cancel hxy)

theorem dyadic_join_div {d r : ℕ} (hr : r < 2 ^ d) (x : ℕ) :
    (r + 2 ^ d * x) / 2 ^ d = x := by
  rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hr, zero_add]

theorem dyadic_join_mod {d r : ℕ} (hr : r < 2 ^ d) (l x : ℕ) :
    (r + 2 ^ d * x) % 2 ^ (d + l) = r + 2 ^ d * (x % 2 ^ l) := by
  have hx : x % 2 ^ l < 2 ^ l := Nat.mod_lt _ (by positivity)
  have hbound : r + 2 ^ d * (x % 2 ^ l) < 2 ^ (d + l) := by
    rw [pow_add]
    have hmul := Nat.mul_le_mul_left (2 ^ d) (show x % 2 ^ l + 1 ≤ 2 ^ l by omega)
    nlinarith
  have hdecomp : r + 2 ^ d * x =
      (r + 2 ^ d * (x % 2 ^ l)) + 2 ^ (d + l) * (x / 2 ^ l) := by
    calc
      _ = r + 2 ^ d * (x % 2 ^ l + 2 ^ l * (x / 2 ^ l)) := by rw [Nat.mod_add_div]
      _ = _ := by rw [pow_add]; ring
  rw [hdecomp, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hbound]

theorem dyadic_join_mod_eq_iff {d r : ℕ} (hr : r < 2 ^ d) (l x y : ℕ) :
    (r + 2 ^ d * x) % 2 ^ (d + l) = (r + 2 ^ d * y) % 2 ^ (d + l) ↔
      x % 2 ^ l = y % 2 ^ l := by
  rw [dyadic_join_mod hr, dyadic_join_mod hr]
  exact (dyadic_join_injective d r).eq_iff

theorem dyadic_zoom_mem {A : Finset ℕ} {d r x : ℕ} (hr : r < 2 ^ d) :
    x ∈ dyadicZoom A d r ↔ r + 2 ^ d * x ∈ A := by
  constructor
  · intro hx
    obtain ⟨a, ha, hax⟩ := Finset.mem_image.mp hx
    obtain ⟨haA, har⟩ := Finset.mem_filter.mp ha
    have hjoin : r + 2 ^ d * x = a := by rw [← hax, ← har, Nat.mod_add_div]
    rwa [hjoin]
  · intro hx
    refine Finset.mem_image.mpr ⟨r + 2 ^ d * x, ?_, dyadic_join_div hr x⟩
    exact Finset.mem_filter.mpr ⟨hx, by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]⟩

theorem dyadic_projection_zoom_mem_iff {A : Finset ℕ} {d r l s : ℕ} (hr : r < 2 ^ d) :
    s ∈ dyadicProjection (dyadicZoom A d r) l ↔
      r + 2 ^ d * s ∈ dyadicProjection A (d + l) := by
  rw [dyadic_projection_zoom, dyadic_zoom_mem hr]

theorem dyadic_zoom_fiber_image (A : Finset ℕ) {d r : ℕ} (hr : r < 2 ^ d) (l s : ℕ) :
    (((dyadicZoom A d r).filter (fun x => x % 2 ^ l = s)).image (fun x => r + 2 ^ d * x)) =
      A.filter (fun y => y % 2 ^ (d + l) = r + 2 ^ d * s) := by
  ext a
  constructor
  · intro ha
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨hxZ, hxs⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨(dyadic_zoom_mem hr).mp hxZ,
      by rw [dyadic_join_mod hr, hxs]⟩
  · intro ha
    obtain ⟨haA, har⟩ := Finset.mem_filter.mp ha
    have hlow : a % 2 ^ d = r := by
      calc
        _ = (a % 2 ^ (d + l)) % 2 ^ d := (Nat.mod_mod_of_dvd a (pow_dvd_pow 2 (by omega))).symm
        _ = (r + 2 ^ d * s) % 2 ^ d := by rw [har]
        _ = r := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
    have hjoin : r + 2 ^ d * (a / 2 ^ d) = a := by rw [← hlow, Nat.mod_add_div]
    have hhigh : a / 2 ^ d % 2 ^ l = s := by
      have hh := congrArg (fun n => n / 2 ^ d) har
      simpa only [pow_add, Nat.mod_mul_right_div_self, dyadic_join_div hr] using hh
    refine Finset.mem_image.mpr ⟨a / 2 ^ d, Finset.mem_filter.mpr ⟨?_, hhigh⟩, hjoin⟩
    exact (dyadic_zoom_mem hr).mpr (hjoin.symm ▸ haA)

theorem dyadic_zoom_fiber_card (A : Finset ℕ) {d r : ℕ} (hr : r < 2 ^ d) (l s : ℕ) :
    ((dyadicZoom A d r).filter (fun x => x % 2 ^ l = s)).card =
      (A.filter (fun y => y % 2 ^ (d + l) = r + 2 ^ d * s)).card := by
  rw [← dyadic_zoom_fiber_image A hr l s,
    Finset.card_image_of_injective _ (dyadic_join_injective d r)]

theorem dyadic_tree_block_zoom {A : Finset ℕ} {b T m k d r : ℕ}
    (hA : DyadicTreeBlock A b T m k) (hdb : d ≤ b) (hr : r < 2 ^ d) :
    DyadicTreeBlock (dyadicZoom A d r) (b - d) T (m - d) k := by
  have hdm : d ≤ m := hdb.trans hA.base_le
  have hproj : ∀ s ∈ dyadicProjection (dyadicZoom A d r) (m - d),
      r + 2 ^ d * s ∈ dyadicProjection A m := by
    intro s hs
    simpa only [Nat.add_sub_of_le hdm] using (dyadic_projection_zoom_mem_iff hr).mp hs
  refine ⟨by have := hA.base_le; omega, by have := hA.split_lt; omega, hA.count_le, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    have hxyA : (r + 2 ^ d * x) % 2 ^ b = (r + 2 ^ d * y) % 2 ^ b := by
      simpa only [Nat.add_sub_of_le hdb] using (dyadic_join_mod_eq_iff hr (b - d) x y).mpr hxy
    have hxyM := hA.common _ ((dyadic_zoom_mem hr).mp hx) _ ((dyadic_zoom_mem hr).mp hy) hxyA
    apply (dyadic_join_mod_eq_iff hr (m - d) x y).mp
    simpa only [Nat.add_sub_of_le hdm] using hxyM
  · intro s hs
    rw [dyadic_zoom_fiber_card A hr, Nat.add_sub_of_le hdm]
    exact hA.fiber_card _ (hproj s hs)
  · intro s hs hk
    obtain ⟨a, ha, c, hc, hac⟩ := hA.splits _ (hproj s hs) hk
    have himage : (((dyadicZoom A d r).filter (fun x => x % 2 ^ (m - d) = s)).image
        (fun x => r + 2 ^ d * x)) = A.filter (fun y => y % 2 ^ m = r + 2 ^ d * s) := by
      simpa only [Nat.add_sub_of_le hdm] using dyadic_zoom_fiber_image A hr (m - d) s
    rw [← himage] at ha hc
    obtain ⟨x, hx, hxa⟩ := Finset.mem_image.mp ha
    obtain ⟨y, hy, hyc⟩ := Finset.mem_image.mp hc
    refine ⟨x, hx, y, hy, ?_⟩
    intro hxy
    have hjoined := (dyadic_join_mod_eq_iff hr (m - d + 1) x y).mpr hxy
    have hindex : d + (m - d + 1) = m + 1 := by omega
    rw [hindex, hxa, hyc] at hjoined
    exact hac hjoined

theorem dyadic_regular_tree_zoom {A : Finset ℕ} {T N i r : ℕ}
    (htree : DyadicRegularTree A T N) (hi : i ≤ N) (hr : r < 2 ^ (T * i)) :
    DyadicRegularTree (dyadicZoom A (T * i) r) T (N - i) := by
  intro j hj
  obtain ⟨m, k, hblock⟩ := htree (i + j) (by omega)
  have hdi : T * i ≤ T * (i + j) := Nat.mul_le_mul_left T (by omega)
  have hzoom := dyadic_tree_block_zoom hblock hdi hr
  have hbase : T * (i + j) - T * i = T * j := by rw [Nat.mul_add, Nat.add_sub_cancel_left]
  have hend : T * i + T * (j + 1) = T * (i + j + 1) := by ring
  refine ⟨m - T * i, k, ?_⟩
  rw [dyadic_projection_zoom, hend]
  simpa only [hbase] using hzoom

def branchPrefix (c : ℕ → ℕ) (n : ℕ) : ℕ := ∑ i ∈ Finset.range n, c i

theorem branch_prefix_zero (c : ℕ → ℕ) : branchPrefix c 0 = 0 := by simp [branchPrefix]

theorem branch_prefix_succ (c : ℕ → ℕ) (n : ℕ) :
    branchPrefix c (n + 1) = branchPrefix c n + c n := Finset.sum_range_succ c n

theorem branch_prefix_mono (c : ℕ → ℕ) : Monotone (branchPrefix c) := by
  intro a b hab
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hab)
    (fun _ _ _ => Nat.zero_le _)

theorem branch_prefix_add_interval (c : ℕ → ℕ) {a b : ℕ} (hab : a ≤ b) :
    branchPrefix c a + (∑ i ∈ Finset.Ico a b, c i) = branchPrefix c b :=
  Finset.sum_range_add_sum_Ico c hab

theorem branch_prefix_sub_eq_sum (c : ℕ → ℕ) {a b : ℕ} (hab : a ≤ b) :
    branchPrefix c b - branchPrefix c a = ∑ i ∈ Finset.Ico a b, c i := by
  have hh := branch_prefix_add_interval c hab
  omega

theorem branch_prefix_sub_le (c : ℕ → ℕ) {a b T : ℕ} (hab : a ≤ b)
    (hcap : ∀ i : ℕ, a ≤ i → i < b → c i ≤ T) :
    branchPrefix c b - branchPrefix c a ≤ T * (b - a) := by
  rw [branch_prefix_sub_eq_sum c hab]
  calc
    _ ≤ ∑ _i ∈ Finset.Ico a b, T := by
      apply Finset.sum_le_sum
      intro i hi
      exact hcap i (Finset.mem_Ico.mp hi).1 (Finset.mem_Ico.mp hi).2
    _ = _ := by simp [Nat.mul_comm]

theorem branch_prefix_eq_of_zero (c : ℕ → ℕ) {a b : ℕ} (hab : a ≤ b)
    (hzero : ∀ i : ℕ, a ≤ i → i < b → c i = 0) : branchPrefix c b = branchPrefix c a := by
  have hh := branch_prefix_add_interval c hab
  have hsum : (∑ i ∈ Finset.Ico a b, c i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    exact hzero i (Finset.mem_Ico.mp hi).1 (Finset.mem_Ico.mp hi).2
  rw [hsum, add_zero] at hh
  exact hh.symm

theorem dyadic_regular_tree_profile {A : Finset ℕ} {T N : ℕ}
    (hA : A.Nonempty) (htree : DyadicRegularTree A T N) :
    ∃ m c : ℕ → ℕ,
      (∀ i : ℕ, i < N → DyadicTreeBlock (dyadicProjection A (T * (i + 1))) (T * i) T (m i) (c i)) ∧
      ∀ j : ℕ, j ≤ N → (dyadicProjection A (T * j)).card = 2 ^ branchPrefix c j := by
  classical
  unfold DyadicRegularTree at htree
  choose! m c hmc using htree
  refine ⟨m, c, hmc, ?_⟩
  intro j
  induction j with
  | zero =>
    intro hj
    simp only [Nat.mul_zero, dyadic_projection_zero hA, Finset.card_singleton, branch_prefix_zero, pow_zero]
  | succ j ih =>
    intro hj
    have hblock := hmc j (by omega)
    rw [branch_prefix_succ, pow_add, ← ih (by omega)]
    have hc := dyadic_tree_block_card hblock
    simpa only [dyadic_projection_trans A (Nat.mul_le_mul_left T (show j ≤ j + 1 by omega))] using hc

structure BranchingInterval (c : ℕ → ℕ) (T N R : ℕ) (α : ℝ) (a b : ℕ) : Prop where
  width : a + R ≤ b
  end_le : b ≤ N
  branching : 0 < c a
  sparse : ((branchPrefix c b - branchPrefix c a : ℕ) : ℝ) < α * (T : ℝ) * ((b - a : ℕ) : ℝ)
  dense : ∀ j : ℕ, a + R ≤ j → j < b →
    α * (T : ℝ) * ((j - a : ℕ) : ℝ) ≤ ((branchPrefix c j - branchPrefix c a : ℕ) : ℝ)

def BranchingIntervalChain (c : ℕ → ℕ) (T N R : ℕ) (α : ℝ) :
    ℕ → List (ℕ × ℕ) → ℕ → Prop
  | z, [], w => w = z
  | z, (a, b) :: L, w => z ≤ a ∧ branchPrefix c a = branchPrefix c z ∧
      BranchingInterval c T N R α a b ∧ BranchingIntervalChain c T N R α b L w

def BranchingIntervalTerminal (c : ℕ → ℕ) (T N R : ℕ) (α : ℝ) (z : ℕ) : Prop :=
  branchPrefix c N - branchPrefix c z ≤ T * R ∨
    ∃ a : ℕ, z ≤ a ∧ a + R ≤ N ∧ branchPrefix c a = branchPrefix c z ∧
      α * (T : ℝ) * ((N - a : ℕ) : ℝ) ≤ ((branchPrefix c N - branchPrefix c a : ℕ) : ℝ)

theorem exists_branching_interval_chain (c : ℕ → ℕ) (T N R : ℕ) (α : ℝ)
    (hR : 0 < R) (hcap : ∀ i : ℕ, i < N → c i ≤ T) :
    ∀ z : ℕ, z ≤ N → ∃ L : List (ℕ × ℕ), ∃ w : ℕ,
      z ≤ w ∧ w ≤ N ∧ BranchingIntervalChain c T N R α z L w ∧
        BranchingIntervalTerminal c T N R α w := by
  have aux : ∀ d : ℕ, ∀ z : ℕ, N - z = d → z ≤ N →
      ∃ L : List (ℕ × ℕ), ∃ w : ℕ,
        z ≤ w ∧ w ≤ N ∧ BranchingIntervalChain c T N R α z L w ∧
          BranchingIntervalTerminal c T N R α w := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro z hdz hzN
      by_cases hex : ∃ a : ℕ, z ≤ a ∧ a < N ∧ 0 < c a
      · let a := Nat.find hex
        obtain ⟨hza, haN, hac⟩ := Nat.find_spec hex
        have hgap : branchPrefix c a = branchPrefix c z := by
          apply branch_prefix_eq_of_zero c hza
          intro i hzi hia
          by_contra hi
          exact (Nat.find_min hex hia) ⟨hzi, by omega, Nat.pos_of_ne_zero hi⟩
        by_cases haR : a + R ≤ N
        · let Q : ℕ → Prop := fun b => a + R ≤ b ∧ b ≤ N ∧
            ((branchPrefix c b - branchPrefix c a : ℕ) : ℝ) < α * (T : ℝ) * ((b - a : ℕ) : ℝ)
          by_cases hdrop : ∃ b, Q b
          · let b := Nat.find hdrop
            obtain ⟨hab, hbN, hstop⟩ := Nat.find_spec hdrop
            have hzb : z < b := by omega
            have hinterval : BranchingInterval c T N R α a b := by
              refine ⟨hab, hbN, hac, hstop, ?_⟩
              intro j hjR hjb
              by_contra hj
              exact (Nat.find_min hdrop hjb) ⟨hjR, by omega, lt_of_not_ge hj⟩
            obtain ⟨L, w, hbw, hwN, hchain, hterminal⟩ := ih (N - b) (by omega) b rfl hbN
            refine ⟨(a, b) :: L, w, hzb.le.trans hbw, hwN, ?_, hterminal⟩
            exact ⟨hza, hgap, hinterval, hchain⟩
          · refine ⟨[], z, le_rfl, hzN, rfl, Or.inr ⟨a, hza, haR, hgap, ?_⟩⟩
            apply le_of_not_gt
            intro hfail
            exact hdrop ⟨N, haR, le_rfl, hfail⟩
        · refine ⟨[], z, le_rfl, hzN, rfl, Or.inl ?_⟩
          rw [← hgap]
          exact (branch_prefix_sub_le c (le_of_lt haN) (fun i _ hiN => hcap i hiN)).trans
            (Nat.mul_le_mul_left T (by omega))
      · have hgap : branchPrefix c N = branchPrefix c z := by
          apply branch_prefix_eq_of_zero c hzN
          intro i hzi hiN
          by_contra hi
          exact hex ⟨i, hzi, hiN, Nat.pos_of_ne_zero hi⟩
        exact ⟨[], z, le_rfl, hzN, rfl, Or.inl (by rw [hgap, Nat.sub_self]; omega)⟩
  intro z hzN
  exact aux (N - z) z rfl hzN

theorem branching_interval_chain_le {c : ℕ → ℕ} {T N R : ℕ} {α : ℝ}
    {z w : ℕ} {L : List (ℕ × ℕ)} (hchain : BranchingIntervalChain c T N R α z L w) :
    z ≤ w := by
  induction L generalizing z with
  | nil =>
    change w = z at hchain
    omega
  | cons p L ih =>
    rcases p with ⟨a, b⟩
    obtain ⟨hza, _, hblock, htail⟩ := hchain
    have hab := hblock.width
    have hbw := ih htail
    omega

theorem branching_interval_chain_length {c : ℕ → ℕ} {T N R : ℕ} {α : ℝ}
    {z w : ℕ} {L : List (ℕ × ℕ)} (hchain : BranchingIntervalChain c T N R α z L w) :
    L.length * R ≤ w - z := by
  induction L generalizing z with
  | nil => simp
  | cons p L ih =>
    rcases p with ⟨a, b⟩
    obtain ⟨hza, _, hblock, htail⟩ := hchain
    have hab := hblock.width
    have hbw := branching_interval_chain_le htail
    have hlen := ih htail
    simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

theorem branching_interval_chain_entropy {c : ℕ → ℕ} {T N R : ℕ} {α : ℝ}
    {z w : ℕ} {L : List (ℕ × ℕ)} (hchain : BranchingIntervalChain c T N R α z L w) :
    (L.map (fun p => branchPrefix c p.2 - branchPrefix c p.1)).sum =
      branchPrefix c w - branchPrefix c z := by
  induction L generalizing z with
  | nil =>
    change w = z at hchain
    simp [hchain]
  | cons p L ih =>
    rcases p with ⟨a, b⟩
    obtain ⟨hza, hgap, hblock, htail⟩ := hchain
    have hab : a ≤ b := by have := hblock.width; omega
    have hbw := branching_interval_chain_le htail
    have hEab := branch_prefix_mono c hab
    have hEbw := branch_prefix_mono c hbw
    simp only [List.map_cons, List.sum_cons]
    rw [ih htail, hgap] at *
    omega

theorem branching_interval_chain_mem {c : ℕ → ℕ} {T N R : ℕ} {α : ℝ}
    {z w : ℕ} {L : List (ℕ × ℕ)} (hchain : BranchingIntervalChain c T N R α z L w) :
    ∀ p ∈ L, z ≤ p.1 ∧ p.2 ≤ w ∧ BranchingInterval c T N R α p.1 p.2 := by
  induction L generalizing z with
  | nil => simp
  | cons p L ih =>
    rcases p with ⟨a, b⟩
    obtain ⟨hza, _, hblock, htail⟩ := hchain
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact ⟨hza, branching_interval_chain_le htail, hblock⟩
    · obtain ⟨hbq, hqw, hqblock⟩ := ih htail q hq
      have hab := hblock.width
      exact ⟨by omega, hqw, hqblock⟩

theorem branching_terminal_entropy {c : ℕ → ℕ} {T N R w : ℕ} {α γ δ : ℝ}
    (hT : 0 < T) (hwN : w ≤ N) (hγ : 0 < γ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hα : 1 - δ / 2 ≤ α)
    (hprefix : ∀ j : ℕ, j ≤ N → γ * (T : ℝ) * (j : ℝ) ≤ (branchPrefix c j : ℝ))
    (hsize : (branchPrefix c N : ℝ) ≤ (1 - δ) * (T : ℝ) * (N : ℝ))
    (hR : 2 * (R : ℝ) ≤ γ * (N : ℝ))
    (hterminal : BranchingIntervalTerminal c T N R α w) :
    γ * δ / 2 * (T : ℝ) * (N : ℝ) ≤ (branchPrefix c w : ℝ) := by
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hNr : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hlower := hprefix N le_rfl
  rcases hterminal with hshort | ⟨a, hwa, haR, hgap, hlong⟩
  · have hEwN := branch_prefix_mono c hwN
    have hshortR : (branchPrefix c N : ℝ) - (branchPrefix c w : ℝ) ≤ (T : ℝ) * (R : ℝ) := by
      exact_mod_cast hshort
    have hRmul := mul_le_mul_of_nonneg_left hR hTr.le
    have hδmul : γ * δ / 2 * (T : ℝ) * (N : ℝ) ≤ γ / 2 * (T : ℝ) * (N : ℝ) := by
      nlinarith [mul_nonneg hγ.le hTr.le,
        mul_nonneg (mul_nonneg hγ.le hTr.le) hNr,
        mul_nonneg (sub_nonneg.mpr hδ1) (mul_nonneg (mul_nonneg hγ.le hTr.le) hNr)]
    nlinarith
  · have haN : a ≤ N := by omega
    have hEaN := branch_prefix_mono c haN
    have hNa : (0 : ℝ) ≤ (N : ℝ) - (a : ℝ) := sub_nonneg.mpr (by exact_mod_cast haN)
    have hlongR : α * (T : ℝ) * ((N : ℝ) - (a : ℝ)) ≤
        (branchPrefix c N : ℝ) - (branchPrefix c a : ℝ) := by
      simpa only [Nat.cast_sub haN, Nat.cast_sub hEaN] using hlong
    have hαmul := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hα hTr.le) hNa
    have hEanonneg : (0 : ℝ) ≤ branchPrefix c a := Nat.cast_nonneg _
    have hhalf : δ / 2 * (T : ℝ) * (N : ℝ) ≤ (T : ℝ) * (a : ℝ) := by
      have hδa := mul_nonneg (mul_nonneg hδ.le hTr.le) (Nat.cast_nonneg a)
      nlinarith
    have hscaled := mul_le_mul_of_nonneg_left hhalf hγ.le
    have hlowerA := hprefix a haN
    have hgapR : (branchPrefix c a : ℝ) = (branchPrefix c w : ℝ) := by exact_mod_cast hgap
    nlinarith

theorem exists_branching_intervals (c : ℕ → ℕ) (T N R : ℕ) (α γ δ : ℝ)
    (hT : 0 < T) (hR : 0 < R) (hγ : 0 < γ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hα : 1 - δ / 2 ≤ α) (hcap : ∀ i : ℕ, i < N → c i ≤ T)
    (hprefix : ∀ j : ℕ, j ≤ N → γ * (T : ℝ) * (j : ℝ) ≤ (branchPrefix c j : ℝ))
    (hsize : (branchPrefix c N : ℝ) ≤ (1 - δ) * (T : ℝ) * (N : ℝ))
    (hRN : 2 * (R : ℝ) ≤ γ * (N : ℝ)) :
    ∃ L : List (ℕ × ℕ), ∃ w : ℕ,
      w ≤ N ∧ BranchingIntervalChain c T N R α 0 L w ∧ L.length * R ≤ N ∧
      γ * δ / 2 * (T : ℝ) * (N : ℝ) ≤
        ((L.map (fun p => branchPrefix c p.2 - branchPrefix c p.1)).sum : ℝ) := by
  obtain ⟨L, w, _, hwN, hchain, hterminal⟩ :=
    exists_branching_interval_chain c T N R α hR hcap 0 (Nat.zero_le N)
  refine ⟨L, w, hwN, hchain, ?_, ?_⟩
  · have hlen : L.length * R ≤ w := by
      simpa only [Nat.sub_zero] using branching_interval_chain_length hchain
    exact hlen.trans hwN
  · rw [branching_interval_chain_entropy hchain, branch_prefix_zero, Nat.sub_zero]
    exact branching_terminal_entropy hT hwN hγ hδ hδ1 hα hprefix hsize hRN hterminal

theorem dyadic_projection_card_mono (A : Finset ℕ) {j k : ℕ} (hjk : j ≤ k) :
    (dyadicProjection A j).card ≤ (dyadicProjection A k).card := by
  rw [← dyadic_projection_trans A hjk]
  exact Finset.card_image_le

theorem dyadic_projection_common_lift {A : Finset ℕ} {b m e : ℕ}
    (hbm : b ≤ m) (hme : m ≤ e)
    (hcommon : ∀ x ∈ dyadicProjection A e, ∀ y ∈ dyadicProjection A e,
      x % 2 ^ b = y % 2 ^ b → x % 2 ^ m = y % 2 ^ m) :
    ∀ x ∈ A, ∀ y ∈ A, x % 2 ^ b = y % 2 ^ b → x % 2 ^ m = y % 2 ^ m := by
  intro x hx y hy hxy
  have heq := hcommon (x % 2 ^ e) (Finset.mem_image_of_mem _ hx)
    (y % 2 ^ e) (Finset.mem_image_of_mem _ hy)
  simp only [Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 (hbm.trans hme)),
    Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 hme)] at heq
  exact heq hxy

theorem dyadic_projection_common {A : Finset ℕ} {b m e : ℕ}
    (hbm : b ≤ m) (hme : m ≤ e)
    (hcommon : ∀ x ∈ A, ∀ y ∈ A,
      x % 2 ^ b = y % 2 ^ b → x % 2 ^ m = y % 2 ^ m) :
    ∀ x ∈ dyadicProjection A e, ∀ y ∈ dyadicProjection A e,
      x % 2 ^ b = y % 2 ^ b → x % 2 ^ m = y % 2 ^ m := by
  intro x hx y hy hxy
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hy
  simp only [Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 (hbm.trans hme))] at hxy
  simpa only [Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 hme)] using hcommon a ha d hd hxy

theorem dyadic_fiber_eq_of_common {A : Finset ℕ} {b m r : ℕ} (hbm : b ≤ m)
    (hcommon : ∀ x ∈ A, ∀ y ∈ A,
      x % 2 ^ b = y % 2 ^ b → x % 2 ^ m = y % 2 ^ m)
    (hr : r ∈ dyadicProjection A m) :
    A.filter (fun x => x % 2 ^ m = r) = A.filter (fun x => x % 2 ^ b = r % 2 ^ b) := by
  obtain ⟨a, ha, har⟩ := Finset.mem_image.mp hr
  ext x
  constructor
  · intro hx
    obtain ⟨hxA, hxr⟩ := Finset.mem_filter.mp hx
    refine Finset.mem_filter.mpr ⟨hxA, ?_⟩
    calc
      _ = (x % 2 ^ m) % 2 ^ b := (Nat.mod_mod_of_dvd x (pow_dvd_pow 2 hbm)).symm
      _ = _ := by rw [hxr]
  · intro hx
    obtain ⟨hxA, hxr⟩ := Finset.mem_filter.mp hx
    have hxa : x % 2 ^ b = a % 2 ^ b := by
      rw [hxr, ← har, Nat.mod_mod_of_dvd a (pow_dvd_pow 2 hbm)]
    exact Finset.mem_filter.mpr ⟨hxA, (hcommon x hxA a ha hxa).trans har⟩

theorem dyadic_regular_profile_fiber_card {A : Finset ℕ} {T N : ℕ} {c : ℕ → ℕ}
    (htree : DyadicRegularTree A T N)
    (hprofile : ∀ j : ℕ, j ≤ N → (dyadicProjection A (T * j)).card = 2 ^ branchPrefix c j)
    {a b r : ℕ} (hab : a ≤ b) (hbN : b ≤ N) (hr : r ∈ dyadicProjection A (T * a)) :
    ((dyadicProjection A (T * b)).filter (fun x => x % 2 ^ (T * a) = r)).card =
      2 ^ (branchPrefix c b - branchPrefix c a) := by
  have hmul := dyadic_regular_tree_zoom_projection_card (i := a) (j := b - a) htree
    (by omega) hr
  rw [dyadic_projection_zoom, ← Nat.mul_add, Nat.add_sub_of_le hab,
    dyadic_zoom_card, hprofile a (hab.trans hbN), hprofile b hbN] at hmul
  have hEab := branch_prefix_mono c hab
  have hpow : 2 ^ branchPrefix c b = 2 ^ branchPrefix c a * 2 ^ (branchPrefix c b - branchPrefix c a) := by
    rw [← pow_add, Nat.add_sub_of_le hEab]
  rw [hpow] at hmul
  exact Nat.eq_of_mul_eq_mul_left (by positivity) hmul

theorem dyadic_regular_profile_fiber_card_le {A : Finset ℕ} {T N : ℕ} {c : ℕ → ℕ}
    (htree : DyadicRegularTree A T N)
    (hprofile : ∀ j : ℕ, j ≤ N → (dyadicProjection A (T * j)).card = 2 ^ branchPrefix c j)
    {a b : ℕ} (hab : a ≤ b) (hbN : b ≤ N) (r : ℕ) :
    ((dyadicProjection A (T * b)).filter (fun x => x % 2 ^ (T * a) = r)).card ≤
      2 ^ (branchPrefix c b - branchPrefix c a) := by
  by_cases hr : r ∈ dyadicProjection A (T * a)
  · exact (dyadic_regular_profile_fiber_card htree hprofile hab hbN hr).le
  · have hempty : (dyadicProjection A (T * b)).filter (fun x => x % 2 ^ (T * a) = r) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      obtain ⟨hxP, hxr⟩ := Finset.mem_filter.mp hx
      apply hr
      rw [← dyadic_projection_trans A (Nat.mul_le_mul_left T hab), ← hxr]
      exact Finset.mem_image_of_mem _ hxP
    rw [hempty, Finset.card_empty]
    exact Nat.zero_le _

theorem dyadic_regular_profile_split_fiber_card {A : Finset ℕ} {T N : ℕ} {m c : ℕ → ℕ}
    (hblocks : ∀ i : ℕ, i < N →
      DyadicTreeBlock (dyadicProjection A (T * (i + 1))) (T * i) T (m i) (c i))
    (hprofile : ∀ j : ℕ, j ≤ N → (dyadicProjection A (T * j)).card = 2 ^ branchPrefix c j)
    {a b r : ℕ} (hab : a < b) (hbN : b ≤ N) (hr : r ∈ dyadicProjection A (m a)) :
    ((dyadicProjection A (T * b)).filter (fun x => x % 2 ^ (m a) = r)).card =
      2 ^ (branchPrefix c b - branchPrefix c a) := by
  have hblock := hblocks a (hab.trans_le hbN)
  have hma : m a ≤ T * (a + 1) := by have := hblock.split_lt; nlinarith
  have hmb : m a ≤ T * b := hma.trans (Nat.mul_le_mul_left T (by omega))
  have hcommon := dyadic_projection_common_lift hblock.base_le hma hblock.common
  have hprojected := dyadic_projection_common hblock.base_le hmb hcommon
  have hr' : r ∈ dyadicProjection (dyadicProjection A (T * b)) (m a) := by
    rwa [dyadic_projection_trans A hmb]
  rw [dyadic_fiber_eq_of_common hblock.base_le hprojected hr']
  apply dyadic_regular_profile_fiber_card (fun i hi => ⟨m i, c i, hblocks i hi⟩) hprofile hab.le hbN
  rw [← dyadic_projection_trans A hblock.base_le]
  exact Finset.mem_image_of_mem _ hr

theorem dyadic_fiber_card_antitone (A : Finset ℕ) {j k : ℕ} (hjk : j ≤ k) (r : ℕ) :
    (A.filter (fun x => x % 2 ^ k = r)).card ≤
      (A.filter (fun x => x % 2 ^ j = r % 2 ^ j)).card := by
  apply Finset.card_le_card
  intro x hx
  obtain ⟨hxA, hxr⟩ := Finset.mem_filter.mp hx
  refine Finset.mem_filter.mpr ⟨hxA, ?_⟩
  calc
    _ = (x % 2 ^ k) % 2 ^ j := (Nat.mod_mod_of_dvd x (pow_dvd_pow 2 hjk)).symm
    _ = _ := by rw [hxr]

theorem dyadic_regular_profile_intermediate_fiber_card_le {A : Finset ℕ} {T N : ℕ}
    {c : ℕ → ℕ} (htree : DyadicRegularTree A T N)
    (hprofile : ∀ j : ℕ, j ≤ N → (dyadicProjection A (T * j)).card = 2 ^ branchPrefix c j)
    {j b k : ℕ} (hjb : j ≤ b) (hbN : b ≤ N) (hjk : T * j ≤ k) (r : ℕ) :
    ((dyadicProjection A (T * b)).filter (fun x => x % 2 ^ k = r)).card ≤
      2 ^ (branchPrefix c b - branchPrefix c j) := by
  exact (dyadic_fiber_card_antitone _ hjk r).trans
    (dyadic_regular_profile_fiber_card_le htree hprofile hjb hbN _)

theorem dyadic_regular_profile_split_fiber_mass_le {A : Finset ℕ} {T N : ℕ} {m c : ℕ → ℕ}
    (hblocks : ∀ i : ℕ, i < N →
      DyadicTreeBlock (dyadicProjection A (T * (i + 1))) (T * i) T (m i) (c i))
    (hprofile : ∀ j : ℕ, j ≤ N → (dyadicProjection A (T * j)).card = 2 ^ branchPrefix c j)
    {a b j k r : ℕ} (hab : a < b) (hbN : b ≤ N) (haj : a ≤ j) (hjb : j ≤ b)
    (hjk : T * j ≤ k) (hr : r ∈ dyadicProjection A (m a)) (s : ℕ) :
    natResidueMass ((dyadicProjection A (T * b)).filter (fun x => x % 2 ^ (m a) = r))
      (2 ^ k) s ≤ (2 : ℝ) ^ (-((branchPrefix c j - branchPrefix c a : ℕ) : ℝ)) := by
  let S := (dyadicProjection A (T * b)).filter (fun x => x % 2 ^ (m a) = r)
  have hS : S.card = 2 ^ (branchPrefix c b - branchPrefix c a) :=
    dyadic_regular_profile_split_fiber_card hblocks hprofile hab hbN hr
  have hsub : natResidueFiber S (2 ^ k) s ⊆
      (dyadicProjection A (T * b)).filter (fun x => x % 2 ^ k = s % 2 ^ k) := by
    intro x hx
    obtain ⟨hxS, hxs⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hxS).1, hxs⟩
  have hfiber := (Finset.card_le_card hsub).trans
    (dyadic_regular_profile_intermediate_fiber_card_le
      (fun i hi => ⟨m i, c i, hblocks i hi⟩) hprofile hjb hbN hjk (s % 2 ^ k))
  have hEaj := branch_prefix_mono c haj
  have hEjb := branch_prefix_mono c hjb
  have hEab := branch_prefix_mono c hab.le
  have hpow : (2 : ℝ) ^ (-((branchPrefix c j - branchPrefix c a : ℕ) : ℝ)) *
      (2 : ℝ) ^ (branchPrefix c b - branchPrefix c a) =
      (2 : ℝ) ^ (branchPrefix c b - branchPrefix c j) := by
    simp only [← Real.rpow_natCast, ← Real.rpow_add (show (0 : ℝ) < 2 by norm_num)]
    congr 1
    simp only [Nat.cast_sub hEaj, Nat.cast_sub hEjb, Nat.cast_sub hEab]
    ring
  change ((natResidueFiber S (2 ^ k) s).card : ℝ) / (S.card : ℝ) ≤ _
  rw [hS, Nat.cast_pow, Nat.cast_ofNat]
  apply (div_le_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) _)).mpr
  rw [hpow]
  exact_mod_cast hfiber

theorem dyadic_regular_profile_split_witnesses {A : Finset ℕ} {T N : ℕ} {m c : ℕ → ℕ}
    (hblocks : ∀ i : ℕ, i < N →
      DyadicTreeBlock (dyadicProjection A (T * (i + 1))) (T * i) T (m i) (c i))
    {a b r : ℕ} (hab : a < b) (hbN : b ≤ N) (hca : 0 < c a)
    (hr : r ∈ dyadicProjection A (m a)) :
    ∃ x ∈ (dyadicProjection A (T * b)).filter (fun x => x % 2 ^ (m a) = r),
      ∃ y ∈ (dyadicProjection A (T * b)).filter (fun x => x % 2 ^ (m a) = r),
        x % 2 ^ (m a + 1) ≠ y % 2 ^ (m a + 1) := by
  have hblock := hblocks a (hab.trans_le hbN)
  have hme : m a + 1 ≤ T * (a + 1) := by have := hblock.split_lt; nlinarith
  have heb : T * (a + 1) ≤ T * b := Nat.mul_le_mul_left T (by omega)
  have hmb : m a + 1 ≤ T * b := hme.trans heb
  have hr' : r ∈ dyadicProjection (dyadicProjection A (T * (a + 1))) (m a) := by
    rwa [dyadic_projection_trans A (show m a ≤ T * (a + 1) by omega)]
  obtain ⟨x, hx, y, hy, hxy⟩ := hblock.splits r hr' hca
  obtain ⟨hxP, hxr⟩ := Finset.mem_filter.mp hx
  obtain ⟨hyP, hyr⟩ := Finset.mem_filter.mp hy
  obtain ⟨u, hu, hux⟩ := Finset.mem_image.mp hxP
  obtain ⟨v, hv, hvy⟩ := Finset.mem_image.mp hyP
  have hur : u % 2 ^ (m a) = r := by
    rw [← hux, Nat.mod_mod_of_dvd u (pow_dvd_pow 2 (show m a ≤ T * (a + 1) by omega))] at hxr
    exact hxr
  have hvr : v % 2 ^ (m a) = r := by
    rw [← hvy, Nat.mod_mod_of_dvd v (pow_dvd_pow 2 (show m a ≤ T * (a + 1) by omega))] at hyr
    exact hyr
  refine ⟨u % 2 ^ (T * b), Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ hu, ?_⟩,
    v % 2 ^ (T * b), Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ hv, ?_⟩, ?_⟩
  · rwa [Nat.mod_mod_of_dvd u (pow_dvd_pow 2 (show m a ≤ T * b by omega))]
  · rwa [Nat.mod_mod_of_dvd v (pow_dvd_pow 2 (show m a ≤ T * b by omega))]
  · intro heq
    apply hxy
    rw [← hux, ← hvy]
    simpa only [Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 hme),
      Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 hmb)] using heq

theorem branching_interval_sparse_physical {c : ℕ → ℕ} {T N R a b m : ℕ} {ρ : ℝ}
    (hR : 0 < R) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hρR : 1 ≤ ρ * (R : ℝ)) (hm : m < T * (a + 1))
    (hinterval : BranchingInterval c T N R (1 - 2 * ρ) a b) :
    ((branchPrefix c b - branchPrefix c a : ℕ) : ℝ) < (1 - ρ) * ((T * b - m : ℕ) : ℝ) := by
  have hab : a < b := by have := hinterval.width; omega
  have hmb : m ≤ T * b := hm.le.trans (Nat.mul_le_mul_left T (by omega))
  have hwidth : (R : ℝ) ≤ (b : ℝ) - (a : ℝ) := by
    have hh : (a : ℝ) + (R : ℝ) ≤ (b : ℝ) := by exact_mod_cast hinterval.width
    linarith
  have hmR : (m : ℝ) ≤ (T : ℝ) * ((a : ℝ) + 1) := by exact_mod_cast hm.le
  have hTr : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  have hρwidth := mul_le_mul_of_nonneg_left hwidth hρ.le
  have hwidthT := mul_le_mul_of_nonneg_right (hρR.trans hρwidth) hTr
  have hshift := mul_le_mul_of_nonneg_left hmR (sub_nonneg.mpr hρ1)
  have hsparse := hinterval.sparse
  rw [Nat.cast_sub hab.le] at hsparse
  rw [Nat.cast_sub hmb, Nat.cast_mul]
  nlinarith [mul_nonneg hρ.le hTr]

theorem branching_interval_dense_physical {c : ℕ → ℕ} {T N R a b m k : ℕ} {ρ : ℝ}
    (hT : 0 < T) (hR : 0 < R) (hρ : 0 < ρ) (hρhalf : ρ ≤ 1 / 2)
    (hρR : 1 ≤ ρ * (R : ℝ)) (hma : T * a ≤ m)
    (hkmin : m + 2 * (T * R) ≤ k) (hkmax : k ≤ T * b)
    (hinterval : BranchingInterval c T N R (1 - 2 * ρ) a b) :
    ∃ j : ℕ, a + R ≤ j ∧ j < b ∧ T * j ≤ k ∧
      (1 - 3 * ρ) * ((k - m : ℕ) : ℝ) ≤
        ((branchPrefix c j - branchPrefix c a : ℕ) : ℝ) := by
  let j := (k - 1) / T
  have hTR : 0 < T * R := Nat.mul_pos hT hR
  have hkpos : 0 < k := by omega
  have hnear : k ≤ T * j + T := by
    have hh := Nat.mod_lt (k - 1) hT
    have hd := Nat.mod_add_div (k - 1) T
    change (k - 1) % T + T * j = k - 1 at hd
    omega
  have hjk : T * j ≤ k := by
    have hh := Nat.mul_div_le (k - 1) T
    change T * j ≤ k - 1 at hh
    omega
  have haj : a + R ≤ j := by
    apply (Nat.le_div_iff_mul_le hT).mpr
    have hh : T * (a + R) < k := by
      rw [Nat.mul_add]
      omega
    rw [Nat.mul_comm]
    omega
  have hjb : j < b := by
    apply (Nat.div_lt_iff_lt_mul hT).mpr
    rw [Nat.mul_comm]
    omega
  have hmkle : m ≤ k := by omega
  have hajle : a ≤ j := by omega
  have hTr : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  have hkmR : (T : ℝ) * (R : ℝ) ≤ (k : ℝ) - (m : ℝ) := by
    have hh : (m : ℝ) + (T : ℝ) * (R : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast (show m + T * R ≤ k by omega)
    linarith
  have hρkm := mul_le_mul_of_nonneg_left hkmR hρ.le
  have hρRT := mul_le_mul_of_nonneg_right hρR hTr
  have hnearR : (k : ℝ) ≤ (T : ℝ) * (j : ℝ) + (T : ℝ) := by exact_mod_cast hnear
  have hmaR : (T : ℝ) * (a : ℝ) ≤ (m : ℝ) := by exact_mod_cast hma
  have hstep : (k : ℝ) - (m : ℝ) - (T : ℝ) ≤ (T : ℝ) * ((j : ℝ) - (a : ℝ)) := by nlinarith
  have hstepmul := mul_le_mul_of_nonneg_left hstep (show 0 ≤ 1 - 2 * ρ by linarith)
  have hdense := hinterval.dense j haj hjb
  rw [Nat.cast_sub hajle] at hdense
  refine ⟨j, haj, hjb, hjk, ?_⟩
  rw [Nat.cast_sub hmkle]
  nlinarith [mul_nonneg hρ.le hTr]

structure DyadicAmplificationBlock (A : Finset ℕ) (u v M e : ℕ) (ρ : ℝ) : Prop where
  start_lt : u < v
  fiber_card : ∀ r ∈ dyadicProjection A u,
    ((dyadicProjection A v).filter (fun x => x % 2 ^ u = r)).card = 2 ^ e
  sparse : (e : ℝ) < (1 - ρ) * ((v - u : ℕ) : ℝ)
  splits : ∀ r ∈ dyadicProjection A u,
    ∃ x ∈ (dyadicProjection A v).filter (fun x => x % 2 ^ u = r),
      ∃ y ∈ (dyadicProjection A v).filter (fun x => x % 2 ^ u = r),
        x % 2 ^ (u + 1) ≠ y % 2 ^ (u + 1)
  mass_le : ∀ k : ℕ, u + M ≤ k → k ≤ v → ∀ r ∈ dyadicProjection A u, ∀ s : ℕ,
    natResidueMass ((dyadicProjection A v).filter (fun x => x % 2 ^ u = r)) (2 ^ k) s ≤
      (2 : ℝ) ^ (-(1 - 3 * ρ) * ((k - u : ℕ) : ℝ))

theorem dyadic_amplification_block_of_branching_interval {A : Finset ℕ} {T N R : ℕ}
    {m c : ℕ → ℕ} {a b : ℕ} {ρ : ℝ}
    (hT : 0 < T) (hR : 0 < R) (hρ : 0 < ρ) (hρhalf : ρ ≤ 1 / 2)
    (hρR : 1 ≤ ρ * (R : ℝ))
    (hblocks : ∀ i : ℕ, i < N →
      DyadicTreeBlock (dyadicProjection A (T * (i + 1))) (T * i) T (m i) (c i))
    (hprofile : ∀ j : ℕ, j ≤ N → (dyadicProjection A (T * j)).card = 2 ^ branchPrefix c j)
    (hinterval : BranchingInterval c T N R (1 - 2 * ρ) a b) :
    DyadicAmplificationBlock A (m a) (T * b) (2 * (T * R))
      (branchPrefix c b - branchPrefix c a) ρ := by
  have hab : a < b := by have := hinterval.width; omega
  have haN : a < N := hab.trans_le hinterval.end_le
  have hblock := hblocks a haN
  have hm : m a < T * (a + 1) := by simpa only [Nat.mul_add, Nat.mul_one] using hblock.split_lt
  refine ⟨hm.trans_le (Nat.mul_le_mul_left T (by omega)),
    fun r hr => dyadic_regular_profile_split_fiber_card hblocks hprofile hab hinterval.end_le hr,
    branching_interval_sparse_physical hR hρ (by linarith) hρR hm hinterval,
    fun r hr => dyadic_regular_profile_split_witnesses hblocks hab hinterval.end_le hinterval.branching hr,
    ?_⟩
  intro k hkmin hkmax r hr s
  obtain ⟨j, haj, hjb, hjk, hbits⟩ := branching_interval_dense_physical hT hR hρ hρhalf hρR
    hblock.base_le hkmin hkmax hinterval
  have hmass := dyadic_regular_profile_split_fiber_mass_le hblocks hprofile hab hinterval.end_le
    (show a ≤ j by omega) hjb.le hjk hr s
  refine hmass.trans ?_
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  nlinarith

theorem exists_dyadic_amplification_intervals {A : Finset ℕ} {T N R : ℕ} {γ δ ρ : ℝ}
    (hA : A.Nonempty) (hT : 0 < T) (hR : 0 < R) (hγ : 0 < γ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hρ : 0 < ρ) (hρδ : ρ ≤ δ / 4) (hρR : 1 ≤ ρ * (R : ℝ))
    (htree : DyadicRegularTree A T N) (hbound : ∀ x ∈ A, x < 2 ^ (T * N))
    (hprefix : ∀ j : ℕ, j ≤ N →
      (2 : ℝ) ^ (γ * (T : ℝ) * (j : ℝ)) ≤ ((dyadicProjection A (T * j)).card : ℝ))
    (hsize : (A.card : ℝ) ≤ (2 : ℝ) ^ ((1 - δ) * (T : ℝ) * (N : ℝ)))
    (hRN : 2 * (R : ℝ) ≤ γ * (N : ℝ)) :
    ∃ m c : ℕ → ℕ, ∃ L : List (ℕ × ℕ), ∃ w : ℕ,
      (∀ i : ℕ, i < N →
        DyadicTreeBlock (dyadicProjection A (T * (i + 1))) (T * i) T (m i) (c i)) ∧
      (∀ j : ℕ, j ≤ N → (dyadicProjection A (T * j)).card = 2 ^ branchPrefix c j) ∧
      w ≤ N ∧ BranchingIntervalChain c T N R (1 - 2 * ρ) 0 L w ∧ L.length * R ≤ N ∧
      γ * δ / 2 * (T : ℝ) * (N : ℝ) ≤
        ((L.map (fun p => branchPrefix c p.2 - branchPrefix c p.1)).sum : ℝ) ∧
      ∀ p ∈ L, DyadicAmplificationBlock A (m p.1) (T * p.2) (2 * (T * R))
        (branchPrefix c p.2 - branchPrefix c p.1) ρ := by
  obtain ⟨m, c, hblocks, hprofile⟩ := dyadic_regular_tree_profile hA htree
  have hprefixE : ∀ j : ℕ, j ≤ N → γ * (T : ℝ) * (j : ℝ) ≤ (branchPrefix c j : ℝ) := by
    intro j hj
    have hh := hprefix j hj
    rw [hprofile j hj, Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast] at hh
    exact (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mp hh
  have hsizeE : (branchPrefix c N : ℝ) ≤ (1 - δ) * (T : ℝ) * (N : ℝ) := by
    have hcard : A.card = 2 ^ branchPrefix c N := by
      simpa only [dyadic_projection_self hbound] using hprofile N le_rfl
    rw [hcard, Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast] at hsize
    exact (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mp hsize
  obtain ⟨L, w, hwN, hchain, hlength, hbits⟩ :=
    exists_branching_intervals c T N R (1 - 2 * ρ) γ δ hT hR hγ hδ hδ1
      (by linarith) (fun i hi => (hblocks i hi).count_le) hprefixE hsizeE hRN
  refine ⟨m, c, L, w, hblocks, hprofile, hwN, hchain, hlength, hbits, ?_⟩
  intro p hp
  exact dyadic_amplification_block_of_branching_interval hT hR hρ (by linarith) hρR
    hblocks hprofile (branching_interval_chain_mem hchain p hp).2.2

theorem nat_residue_mass_mono_modulus (A : Finset ℕ) {q Q : ℕ} (hq : q ∣ Q) (r : ℕ) :
    natResidueMass A Q r ≤ natResidueMass A q r := by
  unfold natResidueMass
  exact div_le_div_of_nonneg_right
    (by exact_mod_cast Finset.card_le_card (nat_residue_fiber_mono_modulus (A := A) (r := r) hq))
    (Nat.cast_nonneg A.card)

theorem dyadic_regular_tree_residue_mass_le {A : Finset ℕ} {T N i : ℕ}
    (htree : DyadicRegularTree A T N) (hbound : ∀ x ∈ A, x < 2 ^ (T * N))
    (hi : i ≤ N) (r : ℕ) :
    natResidueMass A (2 ^ (T * i)) r ≤ 1 / ((dyadicProjection A (T * i)).card : ℝ) := by
  by_cases hr : r % 2 ^ (T * i) ∈ dyadicProjection A (T * i)
  · rw [← nat_residue_mass_mod A (2 ^ (T * i)) r]
    exact (dyadic_regular_tree_residue_mass htree hbound hi hr).le
  · have hempty : natResidueFiber A (2 ^ (T * i)) r = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      obtain ⟨hxA, hxr⟩ := Finset.mem_filter.mp hx
      apply hr
      exact Finset.mem_image.mpr ⟨x, hxA, hxr⟩
    simp only [natResidueMass, hempty, Finset.card_empty, Nat.cast_zero, zero_div]
    positivity

theorem dyadic_regular_tree_mass_le_at_all_levels {A : Finset ℕ} {T N : ℕ} {γ : ℝ}
    (hT : 0 < T) (hγ : 0 ≤ γ) (htree : DyadicRegularTree A T N)
    (hbound : ∀ x ∈ A, x < 2 ^ (T * N))
    (hprefix : ∀ j : ℕ, j ≤ N →
      (2 : ℝ) ^ (γ * (T : ℝ) * (j : ℝ)) ≤ ((dyadicProjection A (T * j)).card : ℝ))
    {k : ℕ} (hkmin : 2 * T ≤ k) (hkmax : k ≤ T * N) (r : ℕ) :
    natResidueMass A (2 ^ k) r ≤ (2 : ℝ) ^ (-(γ / 2) * (k : ℝ)) := by
  let j := k / T
  have hjk : T * j ≤ k := Nat.mul_div_le k T
  have hjN : j ≤ N := by nlinarith
  have hrem := Nat.mod_lt k hT
  have hdiv := Nat.mod_add_div k T
  change k % T + T * j = k at hdiv
  have hgrid : k ≤ 2 * (T * j) := by omega
  have hgridR : (k : ℝ) ≤ 2 * ((T : ℝ) * (j : ℝ)) := by exact_mod_cast hgrid
  have hprefixJ := hprefix j hjN
  calc
    _ ≤ natResidueMass A (2 ^ (T * j)) r :=
      nat_residue_mass_mono_modulus A (pow_dvd_pow 2 hjk) r
    _ ≤ 1 / ((dyadicProjection A (T * j)).card : ℝ) :=
      dyadic_regular_tree_residue_mass_le htree hbound hjN r
    _ ≤ 1 / ((2 : ℝ) ^ (γ * (T : ℝ) * (j : ℝ))) :=
      one_div_le_one_div_of_le (Real.rpow_pos_of_pos (by norm_num) _) hprefixJ
    _ = (2 : ℝ) ^ (-(γ * (T : ℝ) * (j : ℝ))) := by
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), one_div]
    _ ≤ _ := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      nlinarith [mul_le_mul_of_nonneg_left hgridR hγ]

theorem branching_interval_chain_width_sum {c : ℕ → ℕ} {T N R : ℕ} {α : ℝ}
    {z w : ℕ} {L : List (ℕ × ℕ)} (hchain : BranchingIntervalChain c T N R α z L w) :
    (L.map (fun p => p.2 - p.1)).sum ≤ w - z := by
  induction L generalizing z with
  | nil => simp
  | cons p L ih =>
    rcases p with ⟨a, b⟩
    obtain ⟨hza, _, hblock, htail⟩ := hchain
    have hab := hblock.width
    have hbw := branching_interval_chain_le htail
    have hsum := ih htail
    simp only [List.map_cons, List.sum_cons]
    omega

theorem branching_interval_chain_physical_width_sum {c m : ℕ → ℕ} {T N R : ℕ} {α : ℝ}
    {z w : ℕ} {L : List (ℕ × ℕ)} (hchain : BranchingIntervalChain c T N R α z L w)
    (hm : ∀ i : ℕ, i < N → T * i ≤ m i) (hR : 0 < R) :
    (L.map (fun p => T * p.2 - m p.1)).sum ≤ T * (w - z) := by
  have hsum : (L.map (fun p => T * p.2 - m p.1)).sum ≤
      T * (L.map (fun p => p.2 - p.1)).sum := by
    induction L generalizing z with
    | nil => simp
    | cons p L ih =>
      rcases p with ⟨a, b⟩
      obtain ⟨_, _, hblock, htail⟩ := hchain
      have hab : a < b := by have := hblock.width; omega
      have haN : a < N := hab.trans_le hblock.end_le
      have hma := hm a haN
      have hsub : T * b - m a ≤ T * (b - a) := by
        rw [Nat.mul_sub_left_distrib]
        omega
      have htailbound := ih htail
      simp only [List.map_cons, List.sum_cons, Nat.mul_add]
      omega
  exact hsum.trans (Nat.mul_le_mul_left T (branching_interval_chain_width_sum hchain))

theorem dyadic_amplification_blocks_entropy_budget {A : Finset ℕ} {T M : ℕ}
    {m c : ℕ → ℕ} {ρ : ℝ} {L : List (ℕ × ℕ)}
    (hblocks : ∀ p ∈ L, DyadicAmplificationBlock A (m p.1) (T * p.2) M
      (branchPrefix c p.2 - branchPrefix c p.1) ρ) :
    ((L.map (fun p => branchPrefix c p.2 - branchPrefix c p.1)).sum : ℝ) ≤
      (1 - ρ) * ((L.map (fun p => T * p.2 - m p.1)).sum : ℝ) := by
  induction L with
  | nil => simp
  | cons p L ih =>
    have hhead := (hblocks p (by simp)).sparse.le
    have htail := ih (fun q hq => hblocks q (List.mem_cons_of_mem p hq))
    simp only [List.map_cons, List.sum_cons, Nat.cast_add]
    nlinarith

theorem dyadic_amplification_blocks_entropy_gain {A : Finset ℕ} {T M : ℕ}
    {m c : ℕ → ℕ} {ρ : ℝ} {L : List (ℕ × ℕ)} (hρ : 0 ≤ ρ)
    (hblocks : ∀ p ∈ L, DyadicAmplificationBlock A (m p.1) (T * p.2) M
      (branchPrefix c p.2 - branchPrefix c p.1) ρ) :
    ρ * ((L.map (fun p => branchPrefix c p.2 - branchPrefix c p.1)).sum : ℝ) ≤
      ((L.map (fun p => T * p.2 - m p.1)).sum : ℝ) -
        ((L.map (fun p => branchPrefix c p.2 - branchPrefix c p.1)).sum : ℝ) := by
  have hbudget := dyadic_amplification_blocks_entropy_budget hblocks
  have hwidth_nonneg : (0 : ℝ) ≤ (L.map (fun p => T * p.2 - m p.1)).sum := Nat.cast_nonneg _
  have hbits_width : ((L.map (fun p => branchPrefix c p.2 - branchPrefix c p.1)).sum : ℝ) ≤
      ((L.map (fun p => T * p.2 - m p.1)).sum : ℝ) := by
    nlinarith [mul_nonneg hρ hwidth_nonneg]
  nlinarith [mul_le_mul_of_nonneg_left hbits_width hρ]

theorem dyadic_regular_profile_no_branching_gap {A : Finset ℕ} {T N : ℕ} {m c : ℕ → ℕ}
    (hblocks : ∀ i : ℕ, i < N →
      DyadicTreeBlock (dyadicProjection A (T * (i + 1))) (T * i) T (m i) (c i))
    (hprofile : ∀ j : ℕ, j ≤ N → (dyadicProjection A (T * j)).card = 2 ^ branchPrefix c j)
    {z a : ℕ} (hza : z ≤ a) (haN : a < N) (hgap : branchPrefix c a = branchPrefix c z) :
    (dyadicProjection A (m a)).card = (dyadicProjection A (T * z)).card := by
  have hblock := hblocks a haN
  have hma : m a ≤ T * (a + 1) := by have := hblock.split_lt; nlinarith
  have hcommon := dyadic_projection_common_lift hblock.base_le hma hblock.common
  rw [dyadic_projection_card_of_common hblock.base_le hcommon,
    hprofile a haN.le, hprofile z (hza.trans haN.le), hgap]

noncomputable def finiteEntropy {ι : Type*} (S : Finset ι) (p : ι → ℝ) : ℝ :=
  ∑ x ∈ S, Real.negMulLog (p x)

theorem sum_mul_log_le_log_bound {ι : Type*} (S : Finset ι) (p : ι → ℝ) {M : ℝ}
    (hp : ∀ x ∈ S, 0 ≤ p x) (hbound : ∀ x ∈ S, p x ≤ M) :
    (∑ x ∈ S, p x * Real.log (p x)) ≤ (∑ x ∈ S, p x) * Real.log M := by
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro x hx
  by_cases hpx : p x = 0
  · simp [hpx]
  · exact mul_le_mul_of_nonneg_left
      (Real.log_le_log (lt_of_le_of_ne (hp x hx) (Ne.symm hpx)) (hbound x hx)) (hp x hx)

theorem finite_entropy_fiber_defect {ι : Type*} (S : Finset ι) (p : ι → ℝ) {q M : ℝ}
    (hp : ∀ x ∈ S, 0 ≤ p x) (hq : 0 < q) (hM : 0 ≤ M) (hbound : ∀ x ∈ S, p x ≤ M) :
    Real.negMulLog (∑ x ∈ S, p x) + (∑ x ∈ S, p x) * Real.log q - finiteEntropy S p ≤
      q * M - ∑ x ∈ S, p x := by
  let s := ∑ x ∈ S, p x
  have hs : 0 ≤ s := Finset.sum_nonneg hp
  by_cases hMzero : M = 0
  · have hzero : ∀ x ∈ S, p x = 0 := fun x hx => le_antisymm (hMzero ▸ hbound x hx) (hp x hx)
    have hsumzero : ∑ x ∈ S, p x = 0 := Finset.sum_eq_zero hzero
    have hentropy : finiteEntropy S p = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      simp [hzero x hx, Real.negMulLog_def]
    simp [hsumzero, hentropy, hMzero, Real.negMulLog_def]
  have hMpos : 0 < M := lt_of_le_of_ne hM (Ne.symm hMzero)
  have hlog := sum_mul_log_le_log_bound S p hp hbound
  have hentropy : finiteEntropy S p = -(∑ x ∈ S, p x * Real.log (p x)) := by
    simp [finiteEntropy, Real.negMulLog_def, neg_mul, Finset.sum_neg_distrib]
  change Real.negMulLog s + s * Real.log q - finiteEntropy S p ≤ q * M - s
  rw [hentropy]
  change -s * Real.log s + s * Real.log q - -(∑ x ∈ S, p x * Real.log (p x)) ≤ q * M - s
  change (∑ x ∈ S, p x * Real.log (p x)) ≤ s * Real.log M at hlog
  by_cases hszero : s = 0
  · have hlogzero : (∑ x ∈ S, p x * Real.log (p x)) ≤ 0 := by
      simpa only [hszero, zero_mul] using hlog
    simpa only [hszero, neg_zero, zero_mul, zero_add, sub_neg_eq_add, sub_zero] using
      hlogzero.trans (mul_nonneg hq.le hM)
  have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hszero)
  have hratio := Real.log_le_sub_one_of_pos (div_pos (mul_pos hq hMpos) hspos)
  rw [Real.log_div (mul_ne_zero hq.ne' hMpos.ne') hspos.ne', Real.log_mul hq.ne' hMpos.ne'] at hratio
  have hscaled := mul_le_mul_of_nonneg_left hratio hs
  have hcancel : s * (q * M / s) = q * M := by field_simp
  nlinarith

theorem finite_entropy_le_log_card {ι : Type*} (S : Finset ι) (p : ι → ℝ)
    (hp : ∀ x ∈ S, 0 ≤ p x) (hsum : ∑ x ∈ S, p x = 1) :
    finiteEntropy S p ≤ Real.log (S.card : ℝ) := by
  have hSne : S.Nonempty := by
    by_contra hS
    have he := Finset.not_nonempty_iff_eq_empty.mp hS
    norm_num [he] at hsum
  have hcard : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hSne
  have hpoint : ∀ x ∈ S,
      (S.card : ℝ) * Real.negMulLog (p x) ≤
        1 - (S.card : ℝ) * p x + p x * (S.card : ℝ) * Real.log (S.card : ℝ) := by
    intro x hx
    have hh := Real.negMulLog_le_one_sub_self (mul_nonneg hcard.le (hp x hx))
    rw [Real.negMulLog_mul] at hh
    change p x * (-(S.card : ℝ) * Real.log (S.card : ℝ)) +
      (S.card : ℝ) * Real.negMulLog (p x) ≤ 1 - (S.card : ℝ) * p x at hh
    nlinarith
  have htotal := Finset.sum_le_sum hpoint
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.sum_mul, Finset.sum_const, nsmul_eq_mul, mul_one, hsum, one_mul] at htotal
  apply (mul_le_mul_iff_of_pos_left hcard).mp
  simpa only [finiteEntropy, sub_self, zero_add] using htotal

noncomputable def finitePushforward {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (p : ι → ℝ) (π : ι → κ) (b : κ) : ℝ := ∑ a : ι with π a = b, p a

theorem finite_pushforward_sum {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (p : ι → ℝ) (π : ι → κ) : ∑ b : κ, finitePushforward p π b = ∑ a : ι, p a := by
  exact Finset.sum_fiberwise Finset.univ π p

theorem finite_entropy_projection_defect {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (p : ι → ℝ) (π : ι → κ) (M : κ → ℝ) {q : ℝ}
    (hp : ∀ a, 0 ≤ p a) (hq : 0 < q) (hM : ∀ b, 0 ≤ M b)
    (hbound : ∀ a, p a ≤ M (π a)) :
    finiteEntropy Finset.univ (finitePushforward p π) + (∑ a : ι, p a) * Real.log q -
      finiteEntropy Finset.univ p ≤ q * (∑ b : κ, M b) - ∑ a : ι, p a := by
  have hfiber : ∀ b : κ,
      Real.negMulLog (finitePushforward p π b) + finitePushforward p π b * Real.log q -
        finiteEntropy (Finset.univ.filter (fun a => π a = b)) p ≤ q * M b - finitePushforward p π b := by
    intro b
    apply finite_entropy_fiber_defect _ p (fun a _ => hp a) hq (hM b)
    intro a ha
    have heq := (Finset.mem_filter.mp ha).2
    simpa only [heq] using hbound a
  have htotal := Finset.sum_le_sum (s := Finset.univ) (fun b _ => hfiber b)
  have hentropy : (∑ b : κ, finiteEntropy (Finset.univ.filter (fun a => π a = b)) p) =
      finiteEntropy Finset.univ p := Finset.sum_fiberwise Finset.univ π (fun a => Real.negMulLog (p a))
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
    hentropy, finite_pushforward_sum] at htotal
  exact htotal

theorem finite_pushforward_nonneg {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (p : ι → ℝ) (π : ι → κ) (hp : ∀ a, 0 ≤ p a) (b : κ) :
    0 ≤ finitePushforward p π b := Finset.sum_nonneg (fun a _ => hp a)

theorem le_finite_pushforward {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (p : ι → ℝ) (π : ι → κ) (hp : ∀ a, 0 ≤ p a) (a : ι) :
    p a ≤ finitePushforward p π (π a) := by
  exact Finset.single_le_sum (fun b _ => hp b) (by simp)

theorem finite_entropy_mono_projection {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (p : ι → ℝ) (π : ι → κ) (hp : ∀ a, 0 ≤ p a) :
    finiteEntropy Finset.univ (finitePushforward p π) ≤ finiteEntropy Finset.univ p := by
  have hh := finite_entropy_projection_defect p π (finitePushforward p π) hp
    (show (0 : ℝ) < 1 by norm_num) (finite_pushforward_nonneg p π hp) (le_finite_pushforward p π hp)
  simp only [Real.log_one, mul_zero, add_zero, one_mul, finite_pushforward_sum, sub_self] at hh
  linarith

theorem finite_entropy_le_log_support {ι : Type*} [Fintype ι] (p : ι → ℝ) (S : Finset ι)
    (hp : ∀ a, 0 ≤ p a) (hmass : ∑ a : ι, p a = 1) (hzero : ∀ a, a ∉ S → p a = 0) :
    finiteEntropy Finset.univ p ≤ Real.log (S.card : ℝ) := by
  classical
  have hsum : ∑ a ∈ S, p a = 1 := by
    rw [Finset.sum_subset (Finset.subset_univ S) (fun a _ ha => hzero a ha)]
    exact hmass
  have hentropy : finiteEntropy S p = finiteEntropy Finset.univ p := by
    apply Finset.sum_subset (Finset.subset_univ S)
    intro a _ ha
    simp [hzero a ha, Real.negMulLog_def]
  rw [← hentropy]
  exact finite_entropy_le_log_card S p (fun a _ => hp a) hsum

theorem branching_interval_chain_entropy_lower_bound {c m : ℕ → ℕ} {T N R : ℕ}
    {α C : ℝ} {z w : ℕ} {L : List (ℕ × ℕ)} (H : ℕ → ℝ)
    (hchain : BranchingIntervalChain c T N R α z L w) (hR : 0 < R)
    (hH : Monotone H) (hm : ∀ i : ℕ, i < N → T * i ≤ m i)
    (hstep : ∀ p ∈ L,
      H (m p.1) + ((T * p.2 - m p.1 : ℕ) : ℝ) * Real.log 2 - C ≤ H (T * p.2)) :
    H (T * z) + ((L.map (fun p => T * p.2 - m p.1)).sum : ℝ) * Real.log 2 -
      C * (L.length : ℝ) ≤ H (T * w) := by
  induction L generalizing z with
  | nil =>
    change w = z at hchain
    simp [hchain]
  | cons p L ih =>
    rcases p with ⟨a, b⟩
    obtain ⟨hza, _, hblock, htail⟩ := hchain
    have hab : a < b := by have := hblock.width; omega
    have haN : a < N := hab.trans_le hblock.end_le
    have hstart := hH ((Nat.mul_le_mul_left T hza).trans (hm a haN))
    have hhead := hstep (a, b) (by simp)
    have hlast := ih htail (fun q hq => hstep q (List.mem_cons_of_mem (a, b) hq))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    nlinarith

theorem finite_entropy_projection_gain {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (p : ι → ℝ) (π : ι → κ) (M : κ → ℝ) {q C : ℝ}
    (hp : ∀ a, 0 ≤ p a) (hmass : ∑ a : ι, p a = 1) (hq : 0 < q) (hM : ∀ b, 0 ≤ M b)
    (hbound : ∀ a, p a ≤ M (π a)) (hpeak : q * (∑ b : κ, M b) ≤ C + 1) :
    finiteEntropy Finset.univ (finitePushforward p π) + Real.log q - C ≤ finiteEntropy Finset.univ p := by
  have hh := finite_entropy_projection_defect p π M hp hq hM hbound
  rw [hmass, one_mul] at hh
  linarith

theorem finite_pushforward_comp {ι κ ν : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] [DecidableEq ν] (p : ι → ℝ) (π : ι → κ) (σ : κ → ν) :
    finitePushforward (finitePushforward p π) σ = finitePushforward p (σ ∘ π) := by
  funext b
  unfold finitePushforward
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply] using
    Finset.sum_fiberwise_eq_sum_filter (Finset.univ : Finset ι)
      (Finset.univ.filter (fun a => σ a = b)) π p

theorem finite_entropy_pushforward_le_log_image {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (p : ι → ℝ) (π : ι → κ) (hp : ∀ a, 0 ≤ p a) (hmass : ∑ a : ι, p a = 1) :
    finiteEntropy Finset.univ (finitePushforward p π) ≤
      Real.log ((Finset.univ.image π).card : ℝ) := by
  classical
  apply finite_entropy_le_log_support (finitePushforward p π) (Finset.univ.image π)
    (finite_pushforward_nonneg p π hp) (by rw [finite_pushforward_sum, hmass])
  intro b hb
  have he : Finset.univ.filter (fun a => π a = b) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro a ha
    exact hb (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, (Finset.mem_filter.mp ha).2⟩)
  simp only [finitePushforward, he, Finset.sum_empty]

def dyadicIndex (k n : ℕ) : Fin (2 ^ k) := ⟨n % 2 ^ k, Nat.mod_lt n (by positivity)⟩

noncomputable def dyadicDistribution {ι : Type*} [Fintype ι] (p : ι → ℝ) (f : ι → ℕ) (k : ℕ) :
    Fin (2 ^ k) → ℝ := finitePushforward p (fun a => dyadicIndex k (f a))

noncomputable def dyadicEntropy {ι : Type*} [Fintype ι] (p : ι → ℝ) (f : ι → ℕ) (k : ℕ) : ℝ :=
  finiteEntropy Finset.univ (dyadicDistribution p f k)

theorem dyadic_distribution_project {ι : Type*} [Fintype ι] (p : ι → ℝ) (f : ι → ℕ)
    {u v : ℕ} (huv : u ≤ v) :
    finitePushforward (dyadicDistribution p f v) (fun a => dyadicIndex u a.val) = dyadicDistribution p f u := by
  rw [dyadicDistribution, finite_pushforward_comp]
  unfold dyadicDistribution
  congr 1
  funext a
  apply Fin.ext
  exact Nat.mod_mod_of_dvd (f a) (pow_dvd_pow 2 huv)

theorem dyadic_entropy_mono {ι : Type*} [Fintype ι] (p : ι → ℝ) (f : ι → ℕ)
    (hp : ∀ a, 0 ≤ p a) : Monotone (dyadicEntropy p f) := by
  intro u v huv
  have hh := finite_entropy_mono_projection (dyadicDistribution p f v) (fun a => dyadicIndex u a.val)
    (finite_pushforward_nonneg p _ hp)
  rw [dyadic_distribution_project p f huv] at hh
  exact hh

theorem dyadic_entropy_zero {ι : Type*} [Fintype ι] (p : ι → ℝ) (f : ι → ℕ)
    (hmass : ∑ a : ι, p a = 1) : dyadicEntropy p f 0 = 0 := by
  have hi : ∀ a : ι, dyadicIndex 0 (f a) = (0 : Fin (2 ^ 0)) := by
    intro a
    apply Fin.ext
    simp [dyadicIndex]
  have hvalue : dyadicDistribution p f 0 0 = 1 := by
    simpa only [dyadicDistribution, finitePushforward, hi, Finset.filter_true] using hmass
  have hr : ∀ r : Fin (2 ^ 0), r = 0 := by
    intro r
    apply Fin.ext
    have hh := r.isLt
    norm_num at hh
    omega
  unfold dyadicEntropy finiteEntropy
  apply Finset.sum_eq_zero
  intro r _
  rw [hr r, hvalue]
  simp [Real.negMulLog_def]

theorem dyadic_entropy_le_log_projection {ι : Type*} [Fintype ι] (p : ι → ℝ) (f : ι → ℕ)
    (hp : ∀ a, 0 ≤ p a) (hmass : ∑ a : ι, p a = 1) (k : ℕ) :
    dyadicEntropy p f k ≤ Real.log ((dyadicProjection (Finset.univ.image f) k).card : ℝ) := by
  classical
  have hh := finite_entropy_pushforward_le_log_image p (fun a => dyadicIndex k (f a)) hp hmass
  have himage : (Finset.univ.image (fun a => dyadicIndex k (f a))).image Fin.val =
      dyadicProjection (Finset.univ.image f) k := by
    simp only [Finset.image_image, dyadicProjection, dyadicIndex]
    rfl
  have hcard : (Finset.univ.image (fun a => dyadicIndex k (f a))).card =
      (dyadicProjection (Finset.univ.image f) k).card := by
    rw [← himage, Finset.card_image_of_injective _ Fin.val_injective]
  rw [hcard] at hh
  exact hh

theorem dyadic_entropy_interval_gain {ι : Type*} [Fintype ι] (p : ι → ℝ) (f : ι → ℕ)
    (hp : ∀ a, 0 ≤ p a) (hmass : ∑ a : ι, p a = 1) {u v : ℕ} (huv : u ≤ v)
    (M : Fin (2 ^ u) → ℝ) {C : ℝ} (hM : ∀ b, 0 ≤ M b)
    (hbound : ∀ a : Fin (2 ^ v), dyadicDistribution p f v a ≤ M (dyadicIndex u a.val))
    (hpeak : (2 : ℝ) ^ (v - u) * (∑ b, M b) ≤ C + 1) :
    dyadicEntropy p f u + ((v - u : ℕ) : ℝ) * Real.log 2 - C ≤ dyadicEntropy p f v := by
  have hh := finite_entropy_projection_gain (dyadicDistribution p f v) (fun a => dyadicIndex u a.val) M
    (finite_pushforward_nonneg p _ hp) (by rw [dyadicDistribution, finite_pushforward_sum, hmass])
    (pow_pos (by norm_num : (0 : ℝ) < 2) _) hM hbound hpeak
  rw [dyadic_distribution_project p f huv, Real.log_pow] at hh
  exact hh

theorem branching_interval_chain_entropy_amplification {A : Finset ℕ} {c m : ℕ → ℕ}
    {T N R M w : ℕ} {α C ρ B : ℝ} {L : List (ℕ × ℕ)} (H : ℕ → ℝ)
    (hchain : BranchingIntervalChain c T N R α 0 L w) (hR : 0 < R) (hρ : 0 ≤ ρ)
    (hH : Monotone H) (hH0 : H 0 = 0) (hm : ∀ i : ℕ, i < N → T * i ≤ m i)
    (hblocks : ∀ p ∈ L, DyadicAmplificationBlock A (m p.1) (T * p.2) M
      (branchPrefix c p.2 - branchPrefix c p.1) ρ)
    (hstep : ∀ p ∈ L,
      H (m p.1) + ((T * p.2 - m p.1 : ℕ) : ℝ) * Real.log 2 - C ≤ H (T * p.2))
    (hbits : B ≤ ((L.map (fun p => branchPrefix c p.2 - branchPrefix c p.1)).sum : ℝ))
    (hloss : C * (L.length : ℝ) ≤ ρ / 2 * B * Real.log 2) :
    (branchPrefix c w : ℝ) * Real.log 2 + ρ / 2 * B * Real.log 2 ≤ H (T * w) := by
  have hchainH := branching_interval_chain_entropy_lower_bound H hchain hR hH hm hstep
  rw [Nat.mul_zero, hH0, zero_add] at hchainH
  have hgain := dyadic_amplification_blocks_entropy_gain hρ hblocks
  have hlog : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hgainlog := mul_le_mul_of_nonneg_right hgain hlog
  have hbitslog := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbits hρ) hlog
  have hsum : ((L.map (fun p => branchPrefix c p.2 - branchPrefix c p.1)).sum : ℝ) =
      (branchPrefix c w : ℝ) := by
    rw [branching_interval_chain_entropy hchain, branch_prefix_zero, Nat.sub_zero]
  rw [hsum] at hgainlog hbitslog
  nlinarith

theorem sum_test_cyclicPushforward {ι : Type*} [Fintype ι] {q : ℕ} [NeZero q]
    (w : ι → ℂ) (π : ι → ZMod q) (h : ZMod q → ℂ) :
    (∑ a : ZMod q, h a * cyclicPushforward w π a) = ∑ x : ι, h (π x) * w x := by
  classical
  simp only [cyclicPushforward, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp only [mul_ite, mul_zero]
  simp

theorem sum_test_cyclicConvolution {q : ℕ} [NeZero q] (f g h : ZMod q → ℂ) :
    (∑ a : ZMod q, h a * cyclicConvolution f g a) =
      ∑ x : ZMod q, ∑ y : ZMod q, h (x + y) * f x * g y := by
  simp only [cyclicConvolution, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  refine Fintype.sum_equiv (Equiv.subRight x) _ _ ?_
  intro z
  simp only [Equiv.subRight_apply]
  have hh : x + (z - x) = z := by abel
  rw [hh]
  ring

theorem cyclicConvolution_pushforward_left {ι : Type*} [Fintype ι] {q : ℕ} [NeZero q]
    (w : ι → ℂ) (π : ι → ZMod q) (g : ZMod q → ℂ) (a : ZMod q) :
    cyclicConvolution (cyclicPushforward w π) g a = ∑ x : ι, w x * g (a - π x) := by
  simpa only [cyclicConvolution, mul_comm] using sum_test_cyclicPushforward w π (fun b => g (a - b))

theorem cyclicPushforward_convolution {Q q : ℕ} [NeZero Q] [NeZero q]
    (f g : ZMod Q → ℂ) (π : ZMod Q →+ ZMod q) :
    cyclicPushforward (cyclicConvolution f g) π =
      cyclicConvolution (cyclicPushforward f π) (cyclicPushforward g π) := by
  classical
  funext a
  calc
    _ = ∑ z : ZMod Q, (if π z = a then (1 : ℂ) else 0) * cyclicConvolution f g z := by
      simp only [cyclicPushforward, ite_mul, one_mul, zero_mul]
    _ = ∑ x : ZMod Q, ∑ y : ZMod Q, (if π (x + y) = a then (1 : ℂ) else 0) * f x * g y :=
      sum_test_cyclicConvolution f g _
    _ = ∑ x : ZMod Q, f x * cyclicPushforward g π (a - π x) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [cyclicPushforward, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      rw [map_add]
      by_cases hy : π y = a - π x
      · simp [hy]
      · have hxy : π x + π y ≠ a := by
          intro heq
          apply hy
          exact (eq_sub_iff_add_eq').mpr heq
        simp [hy, hxy]
    _ = _ := (cyclicConvolution_pushforward_left f π (cyclicPushforward g π) a).symm

noncomputable def cyclicTwist {q : ℕ} [NeZero q] (f : ZMod q → ℂ) (k x : ZMod q) : ℂ :=
  ZMod.stdAddChar (-(x * k)) * f x

theorem cyclicTwist_convolution {q : ℕ} [NeZero q] (f g : ZMod q → ℂ) (k : ZMod q) :
    cyclicTwist (cyclicConvolution f g) k = cyclicConvolution (cyclicTwist f k) (cyclicTwist g k) := by
  funext x
  simp only [cyclicTwist, cyclicConvolution, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  have hchar : ZMod.stdAddChar (-(x * k)) =
      ZMod.stdAddChar (-(y * k)) * ZMod.stdAddChar (-((x - y) * k)) := by
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  rw [hchar]
  ring

theorem sum_norm_cyclicConvolution_le {q : ℕ} [NeZero q] (f g : ZMod q → ℂ) :
    (∑ x : ZMod q, ‖cyclicConvolution f g x‖) ≤
      (∑ x : ZMod q, ‖f x‖) * (∑ x : ZMod q, ‖g x‖) := by
  calc
    _ ≤ ∑ x : ZMod q, ∑ y : ZMod q, ‖f y‖ * ‖g (x - y)‖ := by
      apply Finset.sum_le_sum
      intro x _
      simpa only [cyclicConvolution, norm_mul] using norm_sum_le Finset.univ (fun y => f y * g (x - y))
    _ = ∑ y : ZMod q, ‖f y‖ * (∑ x : ZMod q, ‖g x‖) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      rw [← Finset.mul_sum]
      congr 1
      exact Fintype.sum_equiv (Equiv.subRight y) _ _ (fun _ => rfl)
    _ = _ := (Finset.sum_mul _ _ _).symm

theorem sum_norm_cyclicConvolutionPow_le {q : ℕ} [NeZero q] (f : ZMod q → ℂ) (r : ℕ) :
    (∑ x : ZMod q, ‖cyclicConvolutionPow f r x‖) ≤ (∑ x : ZMod q, ‖f x‖) ^ r := by
  induction r with
  | zero =>
    simp only [cyclicConvolutionPow, pow_zero]
    have hh : (∑ x : ZMod q, ‖if x = 0 then (1 : ℂ) else 0‖) = 1 := by
      calc
        _ = ∑ x : ZMod q, if x = 0 then (1 : ℝ) else 0 := by
          apply Finset.sum_congr rfl
          intro x _
          by_cases hx : x = 0 <;> simp [hx]
        _ = _ := by simp
    exact hh.le
  | succ r ih =>
    calc
      _ ≤ (∑ x : ZMod q, ‖f x‖) * (∑ x : ZMod q, ‖cyclicConvolutionPow f r x‖) :=
        sum_norm_cyclicConvolution_le f _
      _ ≤ (∑ x : ZMod q, ‖f x‖) * (∑ x : ZMod q, ‖f x‖) ^ r :=
        mul_le_mul_of_nonneg_left ih (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
      _ = _ := by rw [pow_succ]; ring

noncomputable def cyclicFiberDFT {Q q : ℕ} [NeZero Q] [NeZero q]
    (π : ZMod Q →+ ZMod q) (f : ZMod Q → ℂ) (k : ZMod Q) : ZMod q → ℂ :=
  cyclicPushforward (cyclicTwist f k) π

noncomputable def cyclicFiberFourierNorm {Q q : ℕ} [NeZero Q] [NeZero q]
    (π : ZMod Q →+ ZMod q) (f : ZMod Q → ℂ) (k : ZMod Q) : ℝ :=
  ∑ a : ZMod q, ‖cyclicFiberDFT π f k a‖

theorem cyclicFiberDFT_convolution {Q q : ℕ} [NeZero Q] [NeZero q]
    (π : ZMod Q →+ ZMod q) (f g : ZMod Q → ℂ) (k : ZMod Q) :
    cyclicFiberDFT π (cyclicConvolution f g) k =
      cyclicConvolution (cyclicFiberDFT π f k) (cyclicFiberDFT π g k) := by
  unfold cyclicFiberDFT
  rw [cyclicTwist_convolution, cyclicPushforward_convolution]

theorem cyclicFiberDFT_convolutionPow {Q q : ℕ} [NeZero Q] [NeZero q]
    (π : ZMod Q →+ ZMod q) (f : ZMod Q → ℂ) (k : ZMod Q) (r : ℕ) :
    cyclicFiberDFT π (cyclicConvolutionPow f r) k = cyclicConvolutionPow (cyclicFiberDFT π f k) r := by
  induction r with
  | zero =>
    funext a
    change (∑ x : ZMod Q, if π x = a then
      ZMod.stdAddChar (-(x * k)) * (if x = 0 then (1 : ℂ) else 0) else 0) = if a = 0 then 1 else 0
    have hh : ∀ x : ZMod Q,
        (if π x = a then ZMod.stdAddChar (-(x * k)) * (if x = 0 then (1 : ℂ) else 0) else 0) =
          if x = 0 then (if a = 0 then 1 else 0) else 0 := by
      intro x
      by_cases hx : x = 0
      · subst x
        simp [eq_comm]
      · simp [hx]
    simp_rw [hh]
    simp
  | succ r ih => rw [cyclicConvolutionPow, cyclicFiberDFT_convolution, ih, cyclicConvolutionPow]

theorem cyclicFiberFourierNorm_convolutionPow_le {Q q : ℕ} [NeZero Q] [NeZero q]
    (π : ZMod Q →+ ZMod q) (f : ZMod Q → ℂ) (k : ZMod Q) (r : ℕ) :
    cyclicFiberFourierNorm π (cyclicConvolutionPow f r) k ≤ (cyclicFiberFourierNorm π f k) ^ r := by
  unfold cyclicFiberFourierNorm
  rw [cyclicFiberDFT_convolutionPow]
  exact sum_norm_cyclicConvolutionPow_le _ r

theorem mul_norm_le_sum_norm_dft {q : ℕ} [NeZero q] (f : ZMod q → ℂ) (x : ZMod q) :
    (q : ℝ) * ‖f x‖ ≤ ∑ k : ZMod q, ‖ZMod.dft f k‖ := by
  have hsum := congrFun (ZMod.dft_dft f) (-x)
  rw [ZMod.dft_apply] at hsum
  simp only [mul_neg, neg_neg, smul_eq_mul] at hsum
  calc
    _ = ‖(q : ℂ) * f x‖ := by simp
    _ = ‖∑ k : ZMod q, ZMod.stdAddChar (k * x) * ZMod.dft f k‖ := by rw [hsum]
    _ ≤ ∑ k : ZMod q, ‖ZMod.stdAddChar (k * x) * ZMod.dft f k‖ := norm_sum_le _ _
    _ = _ := by simp only [norm_mul, ZMod.stdAddChar_apply, Circle.norm_coe, one_mul]

theorem dft_restrict_cyclic_fiber {Q q : ℕ} [NeZero Q] [NeZero q]
    (π : ZMod Q →+ ZMod q) (f : ZMod Q → ℂ) (a : ZMod q) (k : ZMod Q) :
    ZMod.dft (fun x => if π x = a then f x else 0) k = cyclicFiberDFT π f k a := by
  simp only [ZMod.dft_apply, smul_eq_mul, cyclicFiberDFT, cyclicPushforward, cyclicTwist,
    mul_ite, mul_zero]

theorem cyclic_fiber_norm_bound {Q q : ℕ} [NeZero Q] [NeZero q]
    (π : ZMod Q →+ ZMod q) (f : ZMod Q → ℂ) (x : ZMod Q) :
    (Q : ℝ) * ‖f x‖ ≤ ∑ k : ZMod Q, ‖cyclicFiberDFT π f k (π x)‖ := by
  have hh := mul_norm_le_sum_norm_dft (fun y => if π y = π x then f y else 0) x
  simpa only [if_true, dft_restrict_cyclic_fiber] using hh

theorem exists_cyclic_convolution_power_fiber_bound {Q q : ℕ} [NeZero Q] [NeZero q]
    (π : ZMod Q →+ ZMod q) (f : ZMod Q → ℂ) (r : ℕ) :
    ∃ M : ZMod q → ℝ, (∀ a, 0 ≤ M a) ∧
      (∀ x, ‖cyclicConvolutionPow f r x‖ ≤ M (π x)) ∧
      (Q : ℝ) * (∑ a : ZMod q, M a) ≤ ∑ k : ZMod Q, (cyclicFiberFourierNorm π f k) ^ r := by
  let M : ZMod q → ℝ := fun a => (∑ k : ZMod Q, ‖cyclicFiberDFT π (cyclicConvolutionPow f r) k a‖) / Q
  have hQ : (0 : ℝ) < Q := by exact_mod_cast NeZero.pos Q
  refine ⟨M, fun a => div_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hQ.le, ?_, ?_⟩
  · intro x
    apply (le_div_iff₀ hQ).mpr
    simpa only [mul_comm] using cyclic_fiber_norm_bound π (cyclicConvolutionPow f r) x
  · change (Q : ℝ) * (∑ a : ZMod q, (∑ k : ZMod Q, ‖cyclicFiberDFT π (cyclicConvolutionPow f r) k a‖) / Q) ≤ _
    rw [← Finset.sum_div, mul_div_cancel₀ _ hQ.ne', Finset.sum_comm]
    exact Finset.sum_le_sum (fun k _ => cyclicFiberFourierNorm_convolutionPow_le π f k r)

theorem sum_norm_cyclicPushforward_le {ι : Type*} [Fintype ι] {q : ℕ} [NeZero q]
    (w : ι → ℂ) (π : ι → ZMod q) :
    (∑ a : ZMod q, ‖cyclicPushforward w π a‖) ≤ ∑ x : ι, ‖w x‖ := by
  classical
  calc
    _ ≤ ∑ a : ZMod q, ∑ x : ι, ‖if π x = a then w x else 0‖ :=
      Finset.sum_le_sum (fun a _ => norm_sum_le _ _)
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      simp [apply_ite]

theorem weighted_sum_sq_le {ι : Type*} (S : Finset ι) (w t : ι → ℝ)
    (hw : ∀ i ∈ S, 0 ≤ w i) (hmass : ∑ i ∈ S, w i = 1) :
    (∑ i ∈ S, w i * t i) ^ 2 ≤ ∑ i ∈ S, w i * (t i) ^ 2 := by
  have hleft : (∑ i ∈ S, Real.sqrt (w i) * (Real.sqrt (w i) * t i)) = ∑ i ∈ S, w i * t i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [← mul_assoc, Real.mul_self_sqrt (hw i hi)]
  have hfirst : (∑ i ∈ S, (Real.sqrt (w i)) ^ 2) = 1 := by
    calc
      _ = ∑ i ∈ S, w i := Finset.sum_congr rfl (fun i hi => Real.sq_sqrt (hw i hi))
      _ = _ := hmass
  have hsecond : (∑ i ∈ S, (Real.sqrt (w i) * t i) ^ 2) = ∑ i ∈ S, w i * (t i) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [mul_pow, Real.sq_sqrt (hw i hi)]
  have hh := Finset.sum_mul_sq_le_sq_mul_sq S (fun i => Real.sqrt (w i)) (fun i => Real.sqrt (w i) * t i)
  rwa [hleft, hfirst, hsecond, one_mul] at hh

noncomputable def cyclicMixture {ι : Type*} [Fintype ι] {q : ℕ} [NeZero q]
    (w : ι → ℝ) (F : ι → ZMod q → ℂ) (x : ZMod q) : ℂ := ∑ i : ι, (w i : ℂ) * F i x

theorem cyclicFiberDFT_mixture {ι : Type*} [Fintype ι] {Q q : ℕ} [NeZero Q] [NeZero q]
    (π : ZMod Q →+ ZMod q) (w : ι → ℝ) (F : ι → ZMod Q → ℂ) (k : ZMod Q) (a : ZMod q) :
    cyclicFiberDFT π (cyclicMixture w F) k a = ∑ i : ι, (w i : ℂ) * cyclicFiberDFT π (F i) k a := by
  classical
  unfold cyclicFiberDFT cyclicPushforward cyclicTwist cyclicMixture
  have hh : ∀ x : ZMod Q,
      (if π x = a then ZMod.stdAddChar (-(x * k)) * (∑ i : ι, (w i : ℂ) * F i x) else 0) =
        ∑ i : ι, (w i : ℂ) * (if π x = a then ZMod.stdAddChar (-(x * k)) * F i x else 0) := by
    intro x
    by_cases hx : π x = a
    · simp only [hx, if_true, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    · simp [hx]
  simp_rw [hh, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem cyclicFiberDFT_of_coset_support {Q q : ℕ} [NeZero Q] [NeZero q]
    (π : ZMod Q →+ ZMod q) (f : ZMod Q → ℂ) (k : ZMod Q) (b a : ZMod q)
    (hsupport : ∀ x, f x ≠ 0 → π x = b) :
    cyclicFiberDFT π f k a = if b = a then ZMod.dft f k else 0 := by
  classical
  by_cases hba : b = a
  · subst b
    rw [if_pos rfl, ← dft_restrict_cyclic_fiber]
    have hrestrict : (fun x => if π x = a then f x else 0) = f := by
      funext x
      by_cases hx : π x = a
      · simp [hx]
      · have hzero : f x = 0 := by
          by_contra hn
          exact hx (hsupport x hn)
        simp [hx, hzero]
    rw [hrestrict]
  · rw [if_neg hba]
    unfold cyclicFiberDFT cyclicPushforward cyclicTwist
    apply Finset.sum_eq_zero
    intro x _
    by_cases hx : π x = a
    · have hzero : f x = 0 := by
        by_contra hn
        exact hba ((hsupport x hn).symm.trans hx)
      simp [hx, hzero]
    · simp [hx]

theorem cyclicFiberDFT_coset_mixture {ι : Type*} [Fintype ι] {Q q : ℕ} [NeZero Q] [NeZero q]
    (π : ZMod Q →+ ZMod q) (w : ι → ℝ) (F : ι → ZMod Q → ℂ) (b : ι → ZMod q)
    (hsupport : ∀ i x, F i x ≠ 0 → π x = b i) (k : ZMod Q) :
    cyclicFiberDFT π (cyclicMixture w F) k =
      cyclicPushforward (fun i => (w i : ℂ) * ZMod.dft (F i) k) b := by
  funext a
  rw [cyclicFiberDFT_mixture]
  unfold cyclicPushforward
  apply Finset.sum_congr rfl
  intro i _
  rw [cyclicFiberDFT_of_coset_support π (F i) k (b i) a (hsupport i)]
  simp only [mul_ite, mul_zero]

theorem cyclicFiberFourierNorm_mixture_sq_le {ι : Type*} [Fintype ι] {Q q : ℕ} [NeZero Q] [NeZero q]
    (π : ZMod Q →+ ZMod q) (w : ι → ℝ) (F : ι → ZMod Q → ℂ) (b : ι → ZMod q)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i : ι, w i = 1)
    (hsupport : ∀ i x, F i x ≠ 0 → π x = b i) (k : ZMod Q) :
    (cyclicFiberFourierNorm π (cyclicMixture w F) k) ^ 2 ≤
      ∑ i : ι, w i * ‖ZMod.dft (F i) k‖ ^ 2 := by
  have hnorm : cyclicFiberFourierNorm π (cyclicMixture w F) k ≤
      ∑ i : ι, w i * ‖ZMod.dft (F i) k‖ := by
    unfold cyclicFiberFourierNorm
    rw [cyclicFiberDFT_coset_mixture π w F b hsupport k]
    calc
      _ ≤ ∑ i : ι, ‖(w i : ℂ) * ZMod.dft (F i) k‖ := sum_norm_cyclicPushforward_le _ b
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw i)]
  calc
    _ ≤ (∑ i : ι, w i * ‖ZMod.dft (F i) k‖) ^ 2 :=
      pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hnorm 2
    _ ≤ _ := weighted_sum_sq_le Finset.univ w (fun i => ‖ZMod.dft (F i) k‖) (fun i _ => hw i) hmass

theorem exists_cyclic_mixture_power_fiber_bound {ι : Type*} [Fintype ι] {Q q : ℕ} [NeZero Q] [NeZero q]
    (π : ZMod Q →+ ZMod q) (w : ι → ℝ) (F : ι → ZMod Q → ℂ) (b : ι → ZMod q)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i : ι, w i = 1)
    (hsupport : ∀ i x, F i x ≠ 0 → π x = b i) (B : ZMod Q → ℝ)
    (henergy : ∀ k, (∑ i : ι, w i * ‖ZMod.dft (F i) k‖ ^ 2) ≤ B k) (r : ℕ) :
    ∃ M : ZMod q → ℝ, (∀ a, 0 ≤ M a) ∧
      (∀ x, ‖cyclicConvolutionPow (cyclicMixture w F) (2 * r) x‖ ≤ M (π x)) ∧
      (Q : ℝ) * (∑ a : ZMod q, M a) ≤ ∑ k : ZMod Q, (B k) ^ r := by
  obtain ⟨M, hM, hbound, hsum⟩ := exists_cyclic_convolution_power_fiber_bound π (cyclicMixture w F) (2 * r)
  refine ⟨M, hM, hbound, hsum.trans (Finset.sum_le_sum ?_)⟩
  intro k _
  have hh := (cyclicFiberFourierNorm_mixture_sq_le π w F b hw hmass hsupport k).trans (henergy k)
  simpa only [pow_mul] using pow_le_pow_left₀ (sq_nonneg _) hh r

theorem sum_sq_norm_le_of_sum_norm_one {ι : Type*} [Fintype ι] (f : ι → ℂ) {M : ℝ}
    (hmass : ∑ x : ι, ‖f x‖ = 1) (hbound : ∀ x, ‖f x‖ ≤ M) :
    (∑ x : ι, ‖f x‖ ^ 2) ≤ M := by
  calc
    _ ≤ ∑ x : ι, M * ‖f x‖ := Finset.sum_le_sum (fun x _ => by
      simpa only [pow_two] using mul_le_mul_of_nonneg_right (hbound x) (norm_nonneg _))
    _ = M := by rw [← Finset.mul_sum, hmass, mul_one]

theorem weighted_fourier_energy_le {q : ℕ} [NeZero q] (f : ZMod q → ℂ) (w : ZMod q → ℝ)
    {M₁ M₂ : ℝ} (hmass : ∑ x : ZMod q, ‖f x‖ = 1)
    (hM₁ : ∀ x, ‖f x‖ ≤ M₁) (hM₂ : ∀ x, w x ≤ M₂) (hM₂pos : 0 ≤ M₂)
    {k : ZMod q} (hk : IsUnit k) :
    (∑ x : ZMod q, w x * ‖ZMod.dft f (x * k)‖ ^ 2) ≤ (q : ℝ) * M₁ * M₂ := by
  obtain ⟨u, rfl⟩ := hk
  have hperm : (∑ x : ZMod q, ‖ZMod.dft f (x * (u : ZMod q))‖ ^ 2) =
      ∑ x : ZMod q, ‖ZMod.dft f x‖ ^ 2 :=
    Fintype.sum_equiv u.mulRight _ _ (fun _ => rfl)
  calc
    _ ≤ ∑ x : ZMod q, M₂ * ‖ZMod.dft f (x * (u : ZMod q))‖ ^ 2 :=
      Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_right (hM₂ x) (sq_nonneg _))
    _ = M₂ * ((q : ℝ) * ∑ x : ZMod q, ‖f x‖ ^ 2) := by rw [← Finset.mul_sum, hperm, dft_parseval]
    _ ≤ M₂ * ((q : ℝ) * M₁) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (sum_sq_norm_le_of_sum_norm_one f hmass hM₁) (Nat.cast_nonneg q)) hM₂pos
    _ = _ := by ring

theorem norm_dft_le_sum_norm {q : ℕ} [NeZero q] (f : ZMod q → ℂ) (k : ZMod q) :
    ‖ZMod.dft f k‖ ≤ ∑ x : ZMod q, ‖f x‖ := by
  rw [ZMod.dft_apply]
  calc
    _ ≤ ∑ x : ZMod q, ‖ZMod.stdAddChar (-(x * k)) • f x‖ := norm_sum_le _ _
    _ = _ := by simp only [smul_eq_mul, norm_mul, ZMod.stdAddChar_apply, Circle.norm_coe, one_mul]

theorem weighted_fourier_energy_le_one {q : ℕ} [NeZero q] (f : ZMod q → ℂ) (w : ZMod q → ℝ)
    (hfnorm : ∑ x : ZMod q, ‖f x‖ = 1) (hw : ∀ x, 0 ≤ w x) (hmass : ∑ x : ZMod q, w x = 1)
    (k : ZMod q) : (∑ x : ZMod q, w x * ‖ZMod.dft f (x * k)‖ ^ 2) ≤ 1 := by
  calc
    _ ≤ ∑ x : ZMod q, w x := by
      apply Finset.sum_le_sum
      intro x _
      have hnorm : ‖ZMod.dft f (x * k)‖ ≤ 1 := by simpa only [hfnorm] using norm_dft_le_sum_norm f (x * k)
      have hsq : ‖ZMod.dft f (x * k)‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (ZMod.dft f (x * k))]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hsq (hw x)
    _ = _ := hmass

theorem uniform_fourier_energy_eq {q : ℕ} [NeZero q] (f : ZMod q → ℂ) {k : ZMod q} (hk : IsUnit k) :
    (∑ x : ZMod q, (1 / (q : ℝ)) * ‖ZMod.dft f (x * k)‖ ^ 2) = ∑ x : ZMod q, ‖f x‖ ^ 2 := by
  obtain ⟨u, rfl⟩ := hk
  have hperm : (∑ x : ZMod q, ‖ZMod.dft f (x * (u : ZMod q))‖ ^ 2) =
      ∑ x : ZMod q, ‖ZMod.dft f x‖ ^ 2 := Fintype.sum_equiv u.mulRight _ _ (fun _ => rfl)
  rw [← Finset.mul_sum, hperm, dft_parseval]
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q
  field_simp

theorem probability_point_mass_le_of_two_atoms {ι : Type*} [Fintype ι] (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hmass : ∑ i : ι, p i = 1) {a b : ι} (hab : a ≠ b)
    {β : ℝ} (ha : β ≤ p a) (hb : β ≤ p b) : ∀ i, p i ≤ 1 - β := by
  classical
  have hpair : ∀ i j : ι, i ≠ j → p i + p j ≤ 1 := by
    intro i j hij
    have hh := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ ({i, j} : Finset ι)) (fun x _ _ => hp x)
    simpa only [Finset.sum_pair hij, hmass] using hh
  intro i
  by_cases hia : i = a
  · subst i
    have hh := hpair a b hab
    linarith
  · have hh := hpair i a hia
    linarith

theorem finite_probability_collision_le_of_two_atoms {ι : Type*} [Fintype ι] (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hmass : ∑ i : ι, p i = 1) {a b : ι} (hab : a ≠ b)
    {β : ℝ} (ha : β ≤ p a) (hb : β ≤ p b) : (∑ i : ι, (p i) ^ 2) ≤ 1 - β := by
  have hbound := probability_point_mass_le_of_two_atoms p hp hmass hab ha hb
  calc
    _ ≤ ∑ i : ι, (1 - β) * p i := Finset.sum_le_sum (fun i _ => by
      simpa only [pow_two] using mul_le_mul_of_nonneg_right (hbound i) (hp i))
    _ = _ := by rw [← Finset.mul_sum, hmass, mul_one]

theorem finite_collision_le_pushforward_collision {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (p : ι → ℝ) (π : ι → κ) (hp : ∀ i, 0 ≤ p i) :
    (∑ i : ι, (p i) ^ 2) ≤ ∑ b : κ, (finitePushforward p π b) ^ 2 := by
  calc
    _ ≤ ∑ i : ι, p i * finitePushforward p π (π i) := Finset.sum_le_sum (fun i _ => by
      simpa only [pow_two] using mul_le_mul_of_nonneg_left (le_finite_pushforward p π hp i) (hp i))
    _ = ∑ b : κ, ∑ i : ι with π i = b, p i * finitePushforward p π (π i) :=
      (Finset.sum_fiberwise Finset.univ π _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b _
      calc
        _ = ∑ i : ι with π i = b, p i * finitePushforward p π b := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [(Finset.mem_filter.mp hi).2]
        _ = _ := by rw [← Finset.sum_mul, pow_two]; rfl

theorem uniform_fourier_energy_le_of_projected_atoms {κ : Type*} [Fintype κ] [DecidableEq κ]
    {q : ℕ} [NeZero q] (f : ZMod q → ℂ) (π : ZMod q → κ)
    (hmass : ∑ x : ZMod q, ‖f x‖ = 1) {a b : κ} (hab : a ≠ b) {β : ℝ}
    (ha : β ≤ finitePushforward (fun x => ‖f x‖) π a)
    (hb : β ≤ finitePushforward (fun x => ‖f x‖) π b)
    {k : ZMod q} (hk : IsUnit k) :
    (∑ x : ZMod q, (1 / (q : ℝ)) * ‖ZMod.dft f (x * k)‖ ^ 2) ≤ 1 - β := by
  rw [uniform_fourier_energy_eq f hk]
  exact (finite_collision_le_pushforward_collision (fun x => ‖f x‖) π (fun _ => norm_nonneg _)).trans
    (finite_probability_collision_le_of_two_atoms _ (finite_pushforward_nonneg _ π (fun _ => norm_nonneg _))
      (by rw [finite_pushforward_sum, hmass]) hab ha hb)

theorem sum_comp_le_of_fiber_card_le {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (π : ι → κ) (f : κ → ℝ) {m : ℕ} (hf : ∀ a, 0 ≤ f a)
    (hcard : ∀ a, (Finset.univ.filter (fun i => π i = a)).card ≤ m) :
    (∑ i : ι, f (π i)) ≤ (m : ℝ) * ∑ a : κ, f a := by
  rw [← Finset.sum_fiberwise' Finset.univ π f]
  calc
    _ = ∑ a : κ, ((Finset.univ.filter (fun i => π i = a)).card : ℝ) * f a := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ a : κ, (m : ℝ) * f a := Finset.sum_le_sum (fun a _ =>
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard a) (hf a))
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem dyadic_frequency_reduction_fiber_card_le (u L : ℕ) (a : ZMod (2 ^ L)) :
    ((Finset.univ : Finset (ZMod (2 ^ (u + L)))).filter
      (fun k => (k.val : ZMod (2 ^ L)) = a)).card ≤ 2 ^ u := by
  classical
  let S := (Finset.univ : Finset (ZMod (2 ^ (u + L)))).filter
    (fun k => (k.val : ZMod (2 ^ L)) = a)
  have hsub : S.image ZMod.val ⊆ (Finset.range (2 ^ (u + L))).filter (fun x => x % 2 ^ L = a.val) := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr k.val_lt, ?_⟩
    have hh := congrArg ZMod.val (Finset.mem_filter.mp hk).2
    simpa only [ZMod.val_natCast] using hh
  calc
    _ = (S.image ZMod.val).card := (Finset.card_image_of_injective S (ZMod.val_injective _)).symm
    _ ≤ ((Finset.range (2 ^ (u + L))).filter (fun x => x % 2 ^ L = a.val)).card := Finset.card_le_card hsub
    _ ≤ 2 ^ u := dyadic_residue_fiber_card_le (b := L) (T := u)
      (fun x hx => by simpa only [Nat.add_comm] using Finset.mem_range.mp hx) a.val

theorem sum_dyadic_frequency_reduction_le (u L : ℕ) (f : ZMod (2 ^ L) → ℝ) (hf : ∀ a, 0 ≤ f a) :
    (∑ k : ZMod (2 ^ (u + L)), f (k.val : ZMod (2 ^ L))) ≤
      (2 : ℝ) ^ u * ∑ a : ZMod (2 ^ L), f a := by
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using sum_comp_le_of_fiber_card_le
    (fun k : ZMod (2 ^ (u + L)) => (k.val : ZMod (2 ^ L))) f hf
    (dyadic_frequency_reduction_fiber_card_le u L)

theorem dyadic_nonzero_sum_lt_one_of_quarter_bound {K : ℕ} (f : ZMod (2 ^ K) → ℝ)
    (hbound : ∀ x, x ≠ 0 → f x ≤ (1 / 4 : ℝ) ^ dyadicConductorLevel x) :
    (∑ x ∈ (Finset.univ : Finset (ZMod (2 ^ K))).erase 0, f x) < 1 := by
  classical
  have hmaps : ∀ x ∈ (Finset.univ : Finset (ZMod (2 ^ K))).erase 0,
      dyadicConductorLevel x ∈ Finset.Icc 1 K := by
    intro x hx
    exact Finset.mem_Icc.mpr ⟨dyadic_conductor_pos (Finset.mem_erase.mp hx).1,
      (dyadic_conductor_spec x).1⟩
  have hsum : (∑ x ∈ (Finset.univ : Finset (ZMod (2 ^ K))).erase 0, f x) ≤
      ∑ j ∈ Finset.Icc 1 K, (1 / 2 : ℝ) ^ j := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps f]
    apply Finset.sum_le_sum
    intro j hj
    have hcard : ((((Finset.univ : Finset (ZMod (2 ^ K))).erase 0).filter
        (fun x => dyadicConductorLevel x = j)).card : ℝ) ≤ (2 : ℝ) ^ j := by
      exact_mod_cast dyadic_conductor_fiber_card_le (Finset.mem_Icc.mp hj).2
    calc
      _ ≤ ∑ x ∈ (((Finset.univ : Finset (ZMod (2 ^ K))).erase 0).filter
          (fun x => dyadicConductorLevel x = j)), (1 / 4 : ℝ) ^ j := by
        apply Finset.sum_le_sum
        intro x hx
        obtain ⟨hx, hlevel⟩ := Finset.mem_filter.mp hx
        simpa only [hlevel] using hbound x (Finset.mem_erase.mp hx).1
      _ = ((((Finset.univ : Finset (ZMod (2 ^ K))).erase 0).filter
          (fun x => dyadicConductorLevel x = j)).card : ℝ) * (1 / 4 : ℝ) ^ j := by simp
      _ ≤ (2 : ℝ) ^ j * (1 / 4 : ℝ) ^ j := mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = (1 / 2 : ℝ) ^ j := by rw [← mul_pow]; norm_num
  rw [dyadic_geometric_sum] at hsum
  exact hsum.trans_lt (by have := pow_pos (by norm_num : (0 : ℝ) < 1 / 2) K; linarith)

theorem exists_power_for_piecewise_dyadic_energy (S : ℕ) {θ t : ℝ}
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) (ht : 0 < t) :
    ∃ r : ℕ, 0 < r ∧ ∀ K : ℕ, ∀ B : ZMod (2 ^ K) → ℝ,
      (∀ x, 0 ≤ B x) → B 0 ≤ 1 →
      (∀ x, x ≠ 0 → dyadicConductorLevel x ≤ S → B x ≤ θ) →
      (∀ x, S < dyadicConductorLevel x → B x ≤ (2 : ℝ) ^ (-t * (dyadicConductorLevel x : ℝ))) →
      (∑ x : ZMod (2 ^ K), (B x) ^ r) < 2 := by
  obtain ⟨r₀, hr₀⟩ : ∃ r₀ : ℕ, θ ^ r₀ < (1 / 4 : ℝ) ^ S :=
    exists_pow_lt_of_lt_one (by positivity) hθ1
  obtain ⟨r₁, hr₁⟩ := exists_nat_ge (2 / t)
  let r := r₀ + r₁ + 1
  have htr₁ : 2 ≤ t * (r₁ : ℝ) := by
    have hh := (div_le_iff₀ ht).mp hr₁
    nlinarith
  have htr : 2 ≤ t * (r : ℝ) := htr₁.trans
    (mul_le_mul_of_nonneg_left (by exact_mod_cast (show r₁ ≤ r by omega)) ht.le)
  refine ⟨r, by omega, ?_⟩
  intro K B hB hBzero hshort hlong
  have hpoint : ∀ x : ZMod (2 ^ K), x ≠ 0 → (B x) ^ r ≤ (1 / 4 : ℝ) ^ dyadicConductorLevel x := by
    intro x hx
    by_cases hlevel : dyadicConductorLevel x ≤ S
    · calc
        _ ≤ θ ^ r := pow_le_pow_left₀ (hB x) (hshort x hx hlevel) r
        _ ≤ θ ^ r₀ := pow_le_pow_of_le_one hθ hθ1.le (by omega)
        _ ≤ (1 / 4 : ℝ) ^ S := hr₀.le
        _ ≤ _ := pow_le_pow_of_le_one (by norm_num) (by norm_num) hlevel
    · exact powered_dyadic_decay_le (hB x) (hlong x (by omega)) htr
  have hnonzero := dyadic_nonzero_sum_lt_one_of_quarter_bound (fun x => (B x) ^ r) hpoint
  have hzero : (B 0) ^ r ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ (hB 0) hBzero r
  have hsum := Finset.sum_erase_add (Finset.univ : Finset (ZMod (2 ^ K)))
    (fun x => (B x) ^ r) (Finset.mem_univ 0)
  linarith

theorem dyadic_coset_mixture_peak_bound {ι : Type*} [Fintype ι] (u L r : ℕ)
    (π : ZMod (2 ^ (u + L)) →+ ZMod (2 ^ u))
    (w : ι → ℝ) (F : ι → ZMod (2 ^ (u + L)) → ℂ) (b : ι → ZMod (2 ^ u))
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i : ι, w i = 1)
    (hsupport : ∀ i x, F i x ≠ 0 → π x = b i) (B : ZMod (2 ^ L) → ℝ) (hB : ∀ k, 0 ≤ B k)
    (henergy : ∀ k : ZMod (2 ^ (u + L)),
      (∑ i : ι, w i * ‖ZMod.dft (F i) k‖ ^ 2) ≤ B (k.val : ZMod (2 ^ L)))
    (hsumB : (∑ k : ZMod (2 ^ L), (B k) ^ r) < 2) :
    ∃ M : ZMod (2 ^ u) → ℝ, (∀ a, 0 ≤ M a) ∧
      (∀ x, ‖cyclicConvolutionPow (cyclicMixture w F) (2 * r) x‖ ≤ M (π x)) ∧
      (2 : ℝ) ^ L * (∑ a : ZMod (2 ^ u), M a) < 2 := by
  obtain ⟨M, hM, hbound, hsum⟩ := exists_cyclic_mixture_power_fiber_bound π w F b hw hmass hsupport
    (fun k => B (k.val : ZMod (2 ^ L))) henergy r
  refine ⟨M, hM, hbound, ?_⟩
  have hreduce := sum_dyadic_frequency_reduction_le u L (fun k => (B k) ^ r) (fun k => pow_nonneg (hB k) r)
  have hU : (0 : ℝ) < (2 : ℝ) ^ u := pow_pos (by norm_num) u
  have hscaled := (hsum.trans hreduce).trans_lt (mul_lt_mul_of_pos_left hsumB hU)
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, pow_add, mul_assoc] at hscaled
  exact (mul_lt_mul_iff_of_pos_left hU).mp hscaled

theorem dyadic_fiber_nested (A : Finset ℕ) {d r : ℕ} (hr : r < 2 ^ d) (l s : ℕ) :
    (A.filter (fun x => x % 2 ^ d = r)).filter (fun x => x % 2 ^ (d + l) = r + 2 ^ d * s) =
      A.filter (fun x => x % 2 ^ (d + l) = r + 2 ^ d * s) := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxA, hxh⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hxA).1, hxh⟩
  · intro hx
    obtain ⟨hxA, hxh⟩ := Finset.mem_filter.mp hx
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hxA, ?_⟩, hxh⟩
    calc
      x % 2 ^ d = (x % 2 ^ (d + l)) % 2 ^ d := (Nat.mod_mod_of_dvd x (pow_dvd_pow 2 (by omega))).symm
      _ = (r + 2 ^ d * s) % 2 ^ d := by rw [hxh]
      _ = r := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]

theorem dyadic_zoom_residue_mass (A : Finset ℕ) {d r : ℕ} (hr : r < 2 ^ d) (l s : ℕ) :
    natResidueMass (dyadicZoom A d r) (2 ^ l) s =
      natResidueMass (A.filter (fun x => x % 2 ^ d = r)) (2 ^ (d + l))
        (r + 2 ^ d * (s % 2 ^ l)) := by
  classical
  have hs : s % 2 ^ l < 2 ^ l := Nat.mod_lt s (by positivity)
  have hjoin : r + 2 ^ d * (s % 2 ^ l) < 2 ^ (d + l) := by
    rw [pow_add]
    have hpow : 0 < 2 ^ d := by positivity
    nlinarith
  have hleft : natResidueFiber (dyadicZoom A d r) (2 ^ l) s =
      (dyadicZoom A d r).filter (fun x => x % 2 ^ l = s % 2 ^ l) := by
    ext x
    simp only [natResidueFiber, Finset.mem_filter]
    rfl
  have hright : natResidueFiber (A.filter (fun x => x % 2 ^ d = r)) (2 ^ (d + l))
      (r + 2 ^ d * (s % 2 ^ l)) = A.filter (fun x => x % 2 ^ (d + l) = r + 2 ^ d * (s % 2 ^ l)) := by
    rw [← dyadic_fiber_nested A hr l (s % 2 ^ l)]
    ext x
    simp only [natResidueFiber, Finset.mem_filter, Nat.ModEq, Nat.mod_eq_of_lt hjoin]
  unfold natResidueMass
  rw [hleft, hright, dyadic_zoom_fiber_card A hr l (s % 2 ^ l), dyadic_zoom_card A d r]

theorem dyadic_amplification_block_zoom_card {A : Finset ℕ} {u v M e : ℕ} {ρ : ℝ}
    (hblock : DyadicAmplificationBlock A u v M e ρ) {r : ℕ} (hr : r ∈ dyadicProjection A u) :
    (dyadicZoom (dyadicProjection A v) u r).card = 2 ^ e := by
  rw [dyadic_zoom_card, hblock.fiber_card r hr]

theorem dyadic_amplification_block_zoom_mass {A : Finset ℕ} {u v M e : ℕ} {ρ : ℝ}
    (hblock : DyadicAmplificationBlock A u v M e ρ) {r : ℕ} (hr : r ∈ dyadicProjection A u)
    {l : ℕ} (hlM : M ≤ l) (hlv : u + l ≤ v) (s : ℕ) :
    natResidueMass (dyadicZoom (dyadicProjection A v) u r) (2 ^ l) s ≤
      (2 : ℝ) ^ (-(1 - 3 * ρ) * (l : ℝ)) := by
  rw [dyadic_zoom_residue_mass _ (dyadic_projection_bounded A u r hr)]
  simpa only [Nat.add_sub_cancel_left] using
    hblock.mass_le (u + l) (by omega) hlv r hr (r + 2 ^ u * (s % 2 ^ l))

theorem dyadic_zoom_residue_mass_of_mod (A : Finset ℕ) {d r x : ℕ} (hr : r < 2 ^ d)
    (hxr : x % 2 ^ d = r) (l : ℕ) :
    natResidueMass (dyadicZoom A d r) (2 ^ l) (x / 2 ^ d) =
      natResidueMass (A.filter (fun y => y % 2 ^ d = r)) (2 ^ (d + l)) x := by
  have hjoin : r + 2 ^ d * (x / 2 ^ d) = x := by rw [← hxr, Nat.mod_add_div]
  have hmod := dyadic_join_mod hr l (x / 2 ^ d)
  rw [hjoin] at hmod
  rw [dyadic_zoom_residue_mass A hr l (x / 2 ^ d), ← hmod, nat_residue_mass_mod]

theorem dyadic_regular_profile_split_child_mass {A : Finset ℕ} {T N : ℕ} {m c : ℕ → ℕ}
    (hblocks : ∀ i : ℕ, i < N →
      DyadicTreeBlock (dyadicProjection A (T * (i + 1))) (T * i) T (m i) (c i))
    (hprofile : ∀ j : ℕ, j ≤ N → (dyadicProjection A (T * j)).card = 2 ^ branchPrefix c j)
    {a b r x : ℕ} (hab : a < b) (hbN : b ≤ N)
    (hx : x ∈ dyadicProjection A (T * (a + 1))) (hxr : x % 2 ^ (m a) = r) :
    (2 : ℝ) ^ (-(T : ℝ)) ≤
      natResidueMass ((dyadicProjection A (T * b)).filter (fun y => y % 2 ^ (m a) = r))
        (2 ^ (m a + 1)) x := by
  classical
  let F := (dyadicProjection A (T * b)).filter (fun y => y % 2 ^ (m a) = r)
  let G := (dyadicProjection A (T * b)).filter (fun y => y % 2 ^ (T * (a + 1)) = x)
  have hblock := hblocks a (hab.trans_le hbN)
  have hme : m a + 1 ≤ T * (a + 1) := by have := hblock.split_lt; nlinarith
  have hm : m a ≤ T * (a + 1) := by omega
  have hr : r ∈ dyadicProjection A (m a) := by
    rw [← dyadic_projection_trans A hm]
    exact Finset.mem_image.mpr ⟨x, hx, hxr⟩
  have hF : F.card = 2 ^ (branchPrefix c b - branchPrefix c a) :=
    dyadic_regular_profile_split_fiber_card hblocks hprofile hab hbN hr
  have hG : G.card = 2 ^ (branchPrefix c b - branchPrefix c (a + 1)) :=
    dyadic_regular_profile_fiber_card (fun i hi => ⟨m i, c i, hblocks i hi⟩) hprofile (by omega) hbN hx
  have hsub : G ⊆ natResidueFiber F (2 ^ (m a + 1)) x := by
    intro y hy
    obtain ⟨hyA, hyx⟩ := Finset.mem_filter.mp hy
    have hlow : y % 2 ^ (m a) = r := by
      calc
        _ = (y % 2 ^ (T * (a + 1))) % 2 ^ (m a) := (Nat.mod_mod_of_dvd y (pow_dvd_pow 2 hm)).symm
        _ = x % 2 ^ (m a) := by rw [hyx]
        _ = r := hxr
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hyA, hlow⟩, ?_⟩
    change y % 2 ^ (m a + 1) = x % 2 ^ (m a + 1)
    calc
      _ = (y % 2 ^ (T * (a + 1))) % 2 ^ (m a + 1) := (Nat.mod_mod_of_dvd y (pow_dvd_pow 2 hme)).symm
      _ = _ := by rw [hyx]
  have hE := branch_prefix_mono c (show a + 1 ≤ b by omega)
  have hsucc := branch_prefix_succ c a
  have hsplit : branchPrefix c b - branchPrefix c a = c a + (branchPrefix c b - branchPrefix c (a + 1)) := by omega
  have hcount : F.card ≤ 2 ^ T * (natResidueFiber F (2 ^ (m a + 1)) x).card := by
    rw [hF, hsplit, pow_add, ← hG]
    exact Nat.mul_le_mul (Nat.pow_le_pow_right (by decide : 0 < 2) hblock.count_le) (Finset.card_le_card hsub)
  have hFR : (0 : ℝ) < F.card := by rw [hF]; positivity
  have hTR : (0 : ℝ) < (2 : ℝ) ^ T := pow_pos (by norm_num) T
  have hcountR : (F.card : ℝ) ≤ (2 : ℝ) ^ T * ((natResidueFiber F (2 ^ (m a + 1)) x).card : ℝ) := by
    exact_mod_cast hcount
  change (2 : ℝ) ^ (-(T : ℝ)) ≤ ((natResidueFiber F (2 ^ (m a + 1)) x).card : ℝ) / (F.card : ℝ)
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
  apply (le_div_iff₀ hFR).mpr
  apply (mul_le_mul_iff_of_pos_left hTR).mp
  calc
    _ = (F.card : ℝ) := by rw [← mul_assoc, mul_inv_cancel₀ hTR.ne', one_mul]
    _ ≤ _ := hcountR

theorem dyadic_regular_profile_zoom_split_mass {A : Finset ℕ} {T N : ℕ} {m c : ℕ → ℕ}
    (hblocks : ∀ i : ℕ, i < N →
      DyadicTreeBlock (dyadicProjection A (T * (i + 1))) (T * i) T (m i) (c i))
    (hprofile : ∀ j : ℕ, j ≤ N → (dyadicProjection A (T * j)).card = 2 ^ branchPrefix c j)
    {a b r : ℕ} (hab : a < b) (hbN : b ≤ N) (hca : 0 < c a)
    (hr : r ∈ dyadicProjection A (m a)) :
    ∃ x y : ℕ, x % 2 ≠ y % 2 ∧
      (2 : ℝ) ^ (-(T : ℝ)) ≤ natResidueMass (dyadicZoom (dyadicProjection A (T * b)) (m a) r) 2 x ∧
      (2 : ℝ) ^ (-(T : ℝ)) ≤ natResidueMass (dyadicZoom (dyadicProjection A (T * b)) (m a) r) 2 y := by
  have hblock := hblocks a (hab.trans_le hbN)
  have hm : m a ≤ T * (a + 1) := by have := hblock.split_lt; nlinarith
  have hr' : r ∈ dyadicProjection (dyadicProjection A (T * (a + 1))) (m a) := by
    rwa [dyadic_projection_trans A hm]
  obtain ⟨x, hx, y, hy, hxy⟩ := hblock.splits r hr' hca
  obtain ⟨hxA, hxr⟩ := Finset.mem_filter.mp hx
  obtain ⟨hyA, hyr⟩ := Finset.mem_filter.mp hy
  have hrbound := dyadic_projection_bounded A (m a) r hr
  have hxjoin : r + 2 ^ (m a) * (x / 2 ^ (m a)) = x := by rw [← hxr, Nat.mod_add_div]
  have hyjoin : r + 2 ^ (m a) * (y / 2 ^ (m a)) = y := by rw [← hyr, Nat.mod_add_div]
  refine ⟨x / 2 ^ (m a), y / 2 ^ (m a), ?_, ?_, ?_⟩
  · intro heq
    have hh := (dyadic_join_mod_eq_iff hrbound 1 (x / 2 ^ (m a)) (y / 2 ^ (m a))).mpr
      (by simpa only [pow_one] using heq)
    rw [hxjoin, hyjoin] at hh
    exact hxy hh
  · have hmass := dyadic_regular_profile_split_child_mass hblocks hprofile hab hbN hxA hxr
    have heq := dyadic_zoom_residue_mass_of_mod (dyadicProjection A (T * b)) hrbound hxr 1
    rw [pow_one] at heq
    rw [heq]
    exact hmass
  · have hmass := dyadic_regular_profile_split_child_mass hblocks hprofile hab hbN hyA hyr
    have heq := dyadic_zoom_residue_mass_of_mod (dyadicProjection A (T * b)) hrbound hyr 1
    rw [pow_one] at heq
    rw [heq]
    exact hmass

theorem zmod_mul_zero_fiber_card_le {q : ℕ} [NeZero q] (z : ℕ) :
    (Finset.univ.filter (fun x : ZMod q => x * (z : ZMod q) = 0)).card ≤ q.gcd z := by
  classical
  let d := addOrderOf (z : ZMod q)
  have hdq : d * q.gcd z = q := by
    rw [show d = q / q.gcd z from ZMod.addOrderOf_coe z (NeZero.ne q)]
    exact Nat.div_mul_cancel (Nat.gcd_dvd_left q z)
  have hd : 0 < d := by
    have hq : 0 < q := NeZero.pos q
    nlinarith
  have hmap : Set.MapsTo (fun x : ZMod q => x.val)
      (Finset.univ.filter (fun x : ZMod q => x * (z : ZMod q) = 0))
      (natResidueFiber (Finset.range (d * q.gcd z)) d 0) := by
    intro x hx
    have hxz := (Finset.mem_filter.mp hx).2
    have hdiv : d ∣ x.val := by
      apply addOrderOf_dvd_iff_nsmul_eq_zero.mpr
      simpa only [nsmul_eq_mul, ZMod.natCast_zmod_val] using hxz
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ?_⟩
    · rw [hdq]
      exact ZMod.val_lt x
    · change x.val % d = 0 % d
      simp only [Nat.mod_eq_zero_of_dvd hdiv, Nat.zero_mod]
  have hinj : Set.InjOn (fun x : ZMod q => x.val)
      (Finset.univ.filter (fun x : ZMod q => x * (z : ZMod q) = 0)) :=
    (ZMod.val_injective q).injOn
  exact (Finset.card_le_card_of_injOn _ hmap hinj).trans (nat_residue_fiber_range_card_le hd)

theorem zmod_mul_fiber_card_le {q : ℕ} [NeZero q] (z : ℕ) (a : ZMod q) :
    (Finset.univ.filter (fun x : ZMod q => x * (z : ZMod q) = a)).card ≤ q.gcd z := by
  classical
  let F := Finset.univ.filter (fun x : ZMod q => x * (z : ZMod q) = a)
  by_cases hF : F.Nonempty
  · obtain ⟨x₀, hx₀⟩ := hF
    have hx₀a := (Finset.mem_filter.mp hx₀).2
    have hmap : Set.MapsTo (fun x : ZMod q => x - x₀) F
        (Finset.univ.filter (fun x : ZMod q => x * (z : ZMod q) = 0)) := by
      intro x hx
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [sub_mul, (Finset.mem_filter.mp hx).2, hx₀a, sub_self]
    have hinj : Set.InjOn (fun x : ZMod q => x - x₀) F := by
      intro x hx y hy hxy
      exact sub_left_injective hxy
    exact (Finset.card_le_card_of_injOn _ hmap hinj).trans (zmod_mul_zero_fiber_card_le z)
  · change F.card ≤ q.gcd z
    simpa only [Finset.not_nonempty_iff_eq_empty.mp hF, Finset.card_empty] using Nat.zero_le (q.gcd z)

theorem finite_pushforward_mul_le {q : ℕ} [NeZero q] (w : ZMod q → ℝ)
    {M : ℝ} (hM : 0 ≤ M) (hw : ∀ x, w x ≤ M) (z : ℕ) (a : ZMod q) :
    finitePushforward w (fun x => x * (z : ZMod q)) a ≤ (q.gcd z : ℝ) * M := by
  classical
  calc
    _ ≤ ∑ x : ZMod q with x * (z : ZMod q) = a, M :=
      Finset.sum_le_sum (fun x _ => hw x)
    _ = ((Finset.univ.filter (fun x : ZMod q => x * (z : ZMod q) = a)).card : ℝ) * M := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast zmod_mul_fiber_card_le z a) hM

theorem dyadic_gcd_le_divisor_sum {L S n : ℕ} (hn : 0 < n) (hnS : n ≤ 2 ^ S) :
    (2 ^ L).gcd n ≤ ∑ v ∈ Finset.range (S + 1), if 2 ^ v ∣ n then 2 ^ v else 0 := by
  obtain ⟨a, haL, hga⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (Nat.gcd_dvd_left (2 ^ L) n)
  have hgn : (2 ^ L).gcd n ≤ n := Nat.le_of_dvd hn (Nat.gcd_dvd_right (2 ^ L) n)
  have haS : a ≤ S := by
    by_contra h
    have hh := Nat.pow_le_pow_right (by decide : 0 < 2) (show S + 1 ≤ a by omega)
    have hp : 0 < 2 ^ S := by positivity
    rw [pow_succ] at hh
    rw [hga] at hgn
    nlinarith
  have hadvd : 2 ^ a ∣ n := by rw [← hga]; exact Nat.gcd_dvd_right _ _
  rw [hga]
  calc
    _ = (if 2 ^ a ∣ n then (2 : ℕ) ^ a else 0) := (if_pos hadvd).symm
    _ ≤ _ := Finset.single_le_sum (s := Finset.range (S + 1))
      (f := fun v : ℕ => if 2 ^ v ∣ n then (2 : ℕ) ^ v else 0) (a := a)
      (fun v _ => Nat.zero_le _)
      (Finset.mem_range.mpr (show a < S + 1 by omega))

theorem sum_dyadic_gcd_Ioc_le (L S : ℕ) :
    (∑ n ∈ Finset.Ioc 0 (2 ^ S), (2 ^ L).gcd n) ≤ (S + 1) * 2 ^ S := by
  classical
  calc
    _ ≤ ∑ n ∈ Finset.Ioc 0 (2 ^ S), ∑ v ∈ Finset.range (S + 1),
        if 2 ^ v ∣ n then 2 ^ v else 0 := by
      apply Finset.sum_le_sum
      intro n hn
      exact dyadic_gcd_le_divisor_sum (Finset.mem_Ioc.mp hn).1 (Finset.mem_Ioc.mp hn).2
    _ = ∑ v ∈ Finset.range (S + 1), ∑ n ∈ Finset.Ioc 0 (2 ^ S),
        if 2 ^ v ∣ n then 2 ^ v else 0 := Finset.sum_comm
    _ = ∑ v ∈ Finset.range (S + 1), 2 ^ S := by
      apply Finset.sum_congr rfl
      intro v hv
      have hvS : v ≤ S := by have := Finset.mem_range.mp hv; omega
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, Nat.Ioc_filter_dvd_card_eq_div,
        Nat.pow_div hvS (by decide : 0 < 2), Nat.cast_id, ← pow_add, Nat.sub_add_cancel hvS]
    _ = _ := by simp

noncomputable def cyclicMultiplierAverage {q : ℕ} [NeZero q]
    (w : ZMod q → ℝ) (C : Finset ℕ) (a : ZMod q) : ℝ :=
  (∑ c ∈ C, finitePushforward w (fun x => x * (c : ZMod q)) a) / (C.card : ℝ)

theorem cyclic_multiplier_average_nonneg {q : ℕ} [NeZero q]
    (w : ZMod q → ℝ) (C : Finset ℕ) (hw : ∀ x, 0 ≤ w x) (a : ZMod q) :
    0 ≤ cyclicMultiplierAverage w C a := by
  apply div_nonneg _ (Nat.cast_nonneg _)
  exact Finset.sum_nonneg (fun c _ => finite_pushforward_nonneg w _ hw a)

theorem cyclic_multiplier_average_sum {q : ℕ} [NeZero q]
    (w : ZMod q → ℝ) {C : Finset ℕ} (hC : C.Nonempty) :
    ∑ a : ZMod q, cyclicMultiplierAverage w C a = ∑ x : ZMod q, w x := by
  classical
  have hcard : (C.card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr hC).ne'
  simp only [cyclicMultiplierAverage, ← Finset.sum_div]
  rw [Finset.sum_comm]
  simp only [finite_pushforward_sum, Finset.sum_const, nsmul_eq_mul]
  exact mul_div_cancel_left₀ _ hcard

theorem cyclic_multiplier_average_le {q : ℕ} [NeZero q]
    (w : ZMod q → ℝ) (C : Finset ℕ) {M : ℝ} (hM : 0 ≤ M) (hw : ∀ x, w x ≤ M)
    (a : ZMod q) :
    cyclicMultiplierAverage w C a ≤ ((∑ c ∈ C, (q.gcd c : ℝ)) / (C.card : ℝ)) * M := by
  calc
    _ ≤ (∑ c ∈ C, (q.gcd c : ℝ) * M) / (C.card : ℝ) := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact Finset.sum_le_sum (fun c _ => finite_pushforward_mul_le w hM hw c a)
    _ = _ := by rw [← Finset.sum_mul]; ring

theorem dyadic_multiplier_average_le (L S : ℕ) (w : ZMod (2 ^ L) → ℝ)
    {M : ℝ} (hM : 0 ≤ M) (hw : ∀ x, w x ≤ M) (a : ZMod (2 ^ L)) :
    cyclicMultiplierAverage w (Finset.Ioc 0 (2 ^ S)) a ≤ ((S : ℝ) + 1) * M := by
  have hcard : ((Finset.Ioc 0 (2 ^ S)).card : ℝ) = (2 : ℝ) ^ S := by simp
  have hsum : (∑ c ∈ Finset.Ioc 0 (2 ^ S), ((2 ^ L).gcd c : ℝ)) ≤
      ((S : ℝ) + 1) * (2 : ℝ) ^ S := by
    exact_mod_cast sum_dyadic_gcd_Ioc_le L S
  refine (cyclic_multiplier_average_le w _ hM hw a).trans (mul_le_mul_of_nonneg_right ?_ hM)
  rw [hcard]
  exact (div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ S)).mpr hsum

theorem nat_residue_fiber_range_card {q N : ℕ} (hq : 0 < q) (r : ℕ) :
    (natResidueFiber (Finset.range (q * N)) q r).card = N := by
  have hh := Nat.count_modEq_card (q * N) hq r
  rw [Nat.count_eq_card_filter_range] at hh
  simpa only [natResidueFiber, Nat.mul_div_right _ hq, Nat.mul_mod_right,
    Nat.not_lt_zero, if_false, add_zero] using hh

theorem nat_residue_mass_range_mul {q N : ℕ} (hq : 0 < q) (hN : 0 < N) (r : ℕ) :
    natResidueMass (Finset.range (q * N)) q r = 1 / (q : ℝ) := by
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold natResidueMass
  rw [nat_residue_fiber_range_card hq, Finset.card_range, Nat.cast_mul]
  field_simp

theorem nat_Ioc_eq_translate_range (N : ℕ) :
    Finset.Ioc 0 N = natTranslate (Finset.range N) 1 := by
  ext x
  constructor
  · intro hx
    obtain ⟨hx0, hxN⟩ := Finset.mem_Ioc.mp hx
    exact Finset.mem_image.mpr ⟨x - 1, Finset.mem_range.mpr (by omega), by omega⟩
  · intro hx
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
    have hnN := Finset.mem_range.mp hn
    exact Finset.mem_Ioc.mpr ⟨by omega, by omega⟩

theorem nat_residue_mass_Ioc_mul {q N : ℕ} (hq : 0 < q) (hN : 0 < N) (r : ℕ) :
    natResidueMass (Finset.Ioc 0 (q * N)) q r = 1 / (q : ℝ) := by
  have : NeZero q := ⟨hq.ne'⟩
  rw [nat_Ioc_eq_translate_range, nat_translate_residue_mass]
  exact nat_residue_mass_range_mul hq hN _

theorem nat_residue_mass_dyadic_Ioc {l S : ℕ} (hlS : l ≤ S) (r : ℕ) :
    natResidueMass (Finset.Ioc 0 (2 ^ S)) (2 ^ l) r = 1 / (2 : ℝ) ^ l := by
  have hpow : 2 ^ S = 2 ^ l * 2 ^ (S - l) := by rw [← pow_add, Nat.add_sub_of_le hlS]
  rw [hpow]
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using
    nat_residue_mass_Ioc_mul (by positivity : 0 < 2 ^ l) (by positivity : 0 < 2 ^ (S - l)) r

theorem cyclic_multiplier_average_uniform {q : ℕ} [NeZero q]
    (w : ZMod q → ℝ) (C : Finset ℕ) (hmass : ∑ x : ZMod q, w x = 1)
    (hsupport : ∀ x, w x ≠ 0 → IsUnit x)
    (hC : ∀ r : ℕ, natResidueMass C q r = 1 / (q : ℝ)) (a : ZMod q) :
    cyclicMultiplierAverage w C a = 1 / (q : ℝ) := by
  classical
  unfold cyclicMultiplierAverage finitePushforward
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm, Finset.sum_div]
  calc
    _ = ∑ x : ZMod q, w x * (1 / (q : ℝ)) := by
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hx0 : w x = 0
      · simp only [hx0, ite_self, Finset.sum_const_zero, zero_div, zero_mul]
      · obtain ⟨u, rfl⟩ := hsupport x hx0
        let b : ZMod q := ↑(u⁻¹) * a
        have hpred (c : ℕ) : (u : ZMod q) * (c : ZMod q) = a ↔ Nat.ModEq q c b.val := by
          rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val]
          constructor
          · intro hc
            have hh := congrArg (fun z : ZMod q => ↑(u⁻¹) * z) hc
            simpa only [← mul_assoc, Units.inv_mul, one_mul] using hh
          · intro hc
            rw [hc]
            simp only [b, ← mul_assoc, Units.mul_inv, one_mul]
        have hsum : (∑ c ∈ C, if (u : ZMod q) * (c : ZMod q) = a then w ↑u else 0) =
            ((natResidueFiber C q b.val).card : ℝ) * w ↑u := by
          simp_rw [hpred]
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
          rfl
        rw [hsum]
        calc
          _ = w ↑u * natResidueMass C q b.val := by unfold natResidueMass; ring
          _ = _ := by rw [hC]
    _ = _ := by rw [← Finset.sum_mul, hmass, one_mul]

theorem dyadic_multiplier_average_uniform {l S : ℕ} (hlS : l ≤ S)
    (w : ZMod (2 ^ l) → ℝ) (hmass : ∑ x : ZMod (2 ^ l), w x = 1)
    (hsupport : ∀ x, w x ≠ 0 → IsUnit x) (a : ZMod (2 ^ l)) :
    cyclicMultiplierAverage w (Finset.Ioc 0 (2 ^ S)) a = 1 / (2 : ℝ) ^ l := by
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using
    cyclic_multiplier_average_uniform w (Finset.Ioc 0 (2 ^ S)) hmass hsupport
      (fun r => by simpa only [Nat.cast_pow, Nat.cast_ofNat] using nat_residue_mass_dyadic_Ioc hlS r) a

theorem sum_test_finitePushforward {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (p : ι → ℝ) (π : ι → κ) (h : κ → ℝ) :
    (∑ b : κ, finitePushforward p π b * h b) = ∑ a : ι, p a * h (π a) := by
  classical
  calc
    _ = ∑ b : κ, ∑ a : ι with π a = b, p a * h b := by
      simp only [finitePushforward, Finset.sum_mul]
    _ = ∑ b : κ, ∑ a : ι with π a = b, p a * h (π a) := by
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro a ha
      rw [(Finset.mem_filter.mp ha).2]
    _ = _ := Finset.sum_fiberwise Finset.univ π _

theorem sum_test_cyclicMultiplierAverage {q : ℕ} [NeZero q]
    (w : ZMod q → ℝ) (C : Finset ℕ) (h : ZMod q → ℝ) :
    (∑ a : ZMod q, cyclicMultiplierAverage w C a * h a) =
      (∑ c ∈ C, ∑ x : ZMod q, w x * h (x * (c : ZMod q))) / (C.card : ℝ) := by
  classical
  calc
    _ = (∑ a : ZMod q, ∑ c ∈ C,
        finitePushforward w (fun x => x * (c : ZMod q)) a * h a) / (C.card : ℝ) := by
      simp only [cyclicMultiplierAverage, Finset.sum_mul, Finset.sum_div, div_mul_eq_mul_div]
    _ = _ := by
      rw [Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro c hc
      exact sum_test_finitePushforward w _ h

theorem finite_pushforward_cyclicMultiplierAverage {Q q : ℕ} [NeZero Q] [NeZero q]
    (π : ZMod Q →+* ZMod q) (w : ZMod Q → ℝ) (C : Finset ℕ) :
    finitePushforward (cyclicMultiplierAverage w C) π =
      cyclicMultiplierAverage (finitePushforward w π) C := by
  classical
  funext a
  unfold finitePushforward cyclicMultiplierAverage
  simp only [← Finset.sum_div]
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro c hc
  change finitePushforward (finitePushforward w (fun x => x * (c : ZMod Q))) π a =
    finitePushforward (finitePushforward w π) (fun x => x * (c : ZMod q)) a
  rw [finite_pushforward_comp, finite_pushforward_comp]
  congr 1
  funext x
  simp only [Function.comp_apply, map_mul, map_natCast]

theorem cyclicUniformNatSet_support_odd {A : Finset ℕ} (hodd : ∀ n ∈ A, Odd n)
    (L : ℕ) (x : ZMod (2 ^ L)) (hx : ‖cyclicUniformNatSet A x‖ ≠ 0) : IsUnit x := by
  have hx' : cyclicUniformNatSet A x ≠ 0 := by
    intro h
    exact hx (by rw [h, norm_zero])
  obtain ⟨n, hn, hnx⟩ := cyclicUniformNatSet_support A hx'
  rw [← hnx]
  exact odd_natCast_isUnit_dyadic L (hodd n hn)

theorem dyadic_multiplier_average_decay {g : ℝ} (hg : 0 ≤ g) {S l : ℕ}
    (hS : (S : ℝ) + 1 ≤ (2 : ℝ) ^ (g * (S : ℝ))) (hSl : S ≤ l)
    (w : ZMod (2 ^ l) → ℝ) (hw : ∀ x, w x ≤ (2 : ℝ) ^ (-(2 * g) * (l : ℝ)))
    (a : ZMod (2 ^ l)) :
    cyclicMultiplierAverage w (Finset.Ioc 0 (2 ^ S)) a ≤ (2 : ℝ) ^ (-g * (l : ℝ)) := by
  have hSlR : (S : ℝ) ≤ l := by exact_mod_cast hSl
  have hfactor : (S : ℝ) + 1 ≤ (2 : ℝ) ^ (g * (l : ℝ)) := hS.trans
    (Real.rpow_le_rpow_of_exponent_le (by norm_num) (mul_le_mul_of_nonneg_left hSlR hg))
  calc
    _ ≤ ((S : ℝ) + 1) * (2 : ℝ) ^ (-(2 * g) * (l : ℝ)) :=
      dyadic_multiplier_average_le l S w (by positivity) hw a
    _ ≤ (2 : ℝ) ^ (g * (l : ℝ)) * (2 : ℝ) ^ (-(2 * g) * (l : ℝ)) :=
      mul_le_mul_of_nonneg_right hfactor (by positivity)
    _ = _ := by rw [← Real.rpow_add (by norm_num)]; congr 1; ring

theorem dyadic_multiplier_fourier_energy_le {S l : ℕ}
    (f : ZMod (2 ^ l) → ℂ) (w : ZMod (2 ^ l) → ℝ) {M₁ M₂ : ℝ}
    (hmass : ∑ x : ZMod (2 ^ l), ‖f x‖ = 1) (hf : ∀ x, ‖f x‖ ≤ M₁)
    (hM₂ : 0 ≤ M₂) (hw : ∀ x, w x ≤ M₂) {k : ZMod (2 ^ l)} (hk : IsUnit k) :
    (∑ x : ZMod (2 ^ l), cyclicMultiplierAverage w (Finset.Ioc 0 (2 ^ S)) x *
      ‖ZMod.dft f (x * k)‖ ^ 2) ≤ (2 : ℝ) ^ l * M₁ * (((S : ℝ) + 1) * M₂) := by
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using weighted_fourier_energy_le f
    (cyclicMultiplierAverage w (Finset.Ioc 0 (2 ^ S))) hmass hf
    (dyadic_multiplier_average_le l S w hM₂ hw) (by positivity) hk

theorem dyadic_multiplier_fourier_energy_decay {g ρ : ℝ} (hg : 0 ≤ g) {S l : ℕ}
    (hS : (S : ℝ) + 1 ≤ (2 : ℝ) ^ (g * (S : ℝ))) (hSl : S ≤ l)
    (f : ZMod (2 ^ l) → ℂ) (w : ZMod (2 ^ l) → ℝ)
    (hmass : ∑ x : ZMod (2 ^ l), ‖f x‖ = 1)
    (hf : ∀ x, ‖f x‖ ≤ (2 : ℝ) ^ (-(1 - 3 * ρ) * (l : ℝ)))
    (hw : ∀ x, w x ≤ (2 : ℝ) ^ (-(2 * g) * (l : ℝ)))
    {k : ZMod (2 ^ l)} (hk : IsUnit k) :
    (∑ x : ZMod (2 ^ l), cyclicMultiplierAverage w (Finset.Ioc 0 (2 ^ S)) x *
      ‖ZMod.dft f (x * k)‖ ^ 2) ≤ (2 : ℝ) ^ (-(g - 3 * ρ) * (l : ℝ)) := by
  have hh := weighted_fourier_energy_le f (cyclicMultiplierAverage w (Finset.Ioc 0 (2 ^ S)))
    hmass hf (dyadic_multiplier_average_decay hg hS hSl w hw) (by positivity) hk
  apply hh.trans_eq
  rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast, ← Real.rpow_add (by norm_num),
    ← Real.rpow_add (by norm_num)]
  congr 1; ring

theorem dyadic_multiplier_fourier_energy_gap {κ : Type*} [Fintype κ] [DecidableEq κ]
    {l S : ℕ} (hlS : l ≤ S) (f : ZMod (2 ^ l) → ℂ) (w : ZMod (2 ^ l) → ℝ)
    (π : ZMod (2 ^ l) → κ) (hfnorm : ∑ x : ZMod (2 ^ l), ‖f x‖ = 1)
    (hmass : ∑ x : ZMod (2 ^ l), w x = 1) (hsupport : ∀ x, w x ≠ 0 → IsUnit x)
    {a b : κ} (hab : a ≠ b) {β : ℝ}
    (ha : β ≤ finitePushforward (fun x => ‖f x‖) π a)
    (hb : β ≤ finitePushforward (fun x => ‖f x‖) π b)
    {k : ZMod (2 ^ l)} (hk : IsUnit k) :
    (∑ x : ZMod (2 ^ l), cyclicMultiplierAverage w (Finset.Ioc 0 (2 ^ S)) x *
      ‖ZMod.dft f (x * k)‖ ^ 2) ≤ 1 - β := by
  simp_rw [dyadic_multiplier_average_uniform hlS w hmass hsupport]
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using
    uniform_fourier_energy_le_of_projected_atoms f π hfnorm hab ha hb hk

theorem exists_dyadic_multiplier_cutoff {g : ℝ} (hg : 0 < g) (M : ℕ) :
    ∃ S : ℕ, M ≤ S ∧ 0 < S ∧ (S : ℝ) + 1 ≤ (2 : ℝ) ^ (g * (S : ℝ)) := by
  obtain ⟨S₀, hS₀⟩ := Filter.eventually_atTop.mp (eventually_dyadic_regularization_cost_le hg)
  let S := max S₀ (max M 1)
  have hS : 0 < S := lt_of_lt_of_le (by decide : 0 < 1)
    ((le_max_right M 1).trans (le_max_right S₀ (max M 1)))
  refine ⟨S, (le_max_left M 1).trans (le_max_right S₀ (max M 1)), hS, ?_⟩
  have hh := hS₀ S (le_max_left _ _)
  have hnonneg : (0 : ℝ) ≤ S := Nat.cast_nonneg _
  nlinarith [sq_nonneg (S : ℝ)]

theorem cyclicPushforward_ofReal {ι : Type*} [Fintype ι] {q : ℕ} [NeZero q]
    (p : ι → ℝ) (π : ι → ZMod q) (a : ZMod q) :
    cyclicPushforward (fun i => (p i : ℂ)) π a = (finitePushforward p π a : ℂ) := by
  classical
  simp only [cyclicPushforward, finitePushforward, Finset.sum_filter, Complex.ofReal_sum,
    apply_ite, Complex.ofReal_zero]

theorem norm_cyclicPushforward_ofReal {ι : Type*} [Fintype ι] {q : ℕ} [NeZero q]
    (p : ι → ℝ) (π : ι → ZMod q) (hp : ∀ i, 0 ≤ p i) (a : ZMod q) :
    ‖cyclicPushforward (fun i => (p i : ℂ)) π a‖ = finitePushforward p π a := by
  rw [cyclicPushforward_ofReal]
  exact Complex.norm_of_nonneg (finite_pushforward_nonneg p π hp a)

theorem norm_cyclicUniformNatSet_eq_pushforward {q : ℕ} [NeZero q] (A : Finset ℕ) :
    (fun x : ZMod q => ‖cyclicUniformNatSet A x‖) =
      finitePushforward (fun _ : A => (A.card : ℝ)⁻¹) (fun n => (n.val : ZMod q)) := by
  funext x
  have hh := norm_cyclicPushforward_ofReal (fun _ : A => (A.card : ℝ)⁻¹)
    (fun n : A => (n.val : ZMod q)) (fun _ => by positivity) x
  simpa only [cyclicUniformNatSet, Complex.ofReal_inv, Complex.ofReal_natCast] using hh

theorem finite_pushforward_norm_cyclicUniformNatSet {Q q : ℕ} [NeZero Q] [NeZero q]
    (π : ZMod Q →+* ZMod q) (A : Finset ℕ) :
    finitePushforward (fun x : ZMod Q => ‖cyclicUniformNatSet A x‖) π =
      (fun x : ZMod q => ‖cyclicUniformNatSet A x‖) := by
  rw [norm_cyclicUniformNatSet_eq_pushforward, finite_pushforward_comp,
    norm_cyclicUniformNatSet_eq_pushforward]
  congr 1
  funext n
  simp only [Function.comp_apply, map_natCast]

theorem sum_test_norm_cyclicUniformNatSet {q : ℕ} [NeZero q]
    (A : Finset ℕ) (h : ZMod q → ℝ) :
    (∑ x : ZMod q, ‖cyclicUniformNatSet A x‖ * h x) =
      (∑ n ∈ A, h (n : ZMod q)) / (A.card : ℝ) := by
  have hp (x : ZMod q) : ‖cyclicUniformNatSet A x‖ =
      finitePushforward (fun _ : A => (A.card : ℝ)⁻¹) (fun n => (n.val : ZMod q)) x :=
    congrFun (norm_cyclicUniformNatSet_eq_pushforward A) x
  simp_rw [hp]
  rw [sum_test_finitePushforward]
  simp only [← Finset.mul_sum]
  rw [Finset.sum_coe_sort A (fun n => h (n : ZMod q))]
  ring

theorem dyadic_uniform_parity_mass {A : Finset ℕ} {l : ℕ} (hl : 1 ≤ l) (r : ℕ) :
    finitePushforward (fun x : ZMod (2 ^ l) => ‖cyclicUniformNatSet A x‖)
      (ZMod.castHom (pow_dvd_pow 2 hl) (ZMod 2)) (r : ZMod 2) = natResidueMass A 2 r := by
  rw [finite_pushforward_norm_cyclicUniformNatSet]
  dsimp only
  rw [norm_cyclicUniformNatSet, ZMod.val_natCast, nat_residue_mass_mod]

theorem dyadic_uniform_multiplier_energy_gap {A B : Finset ℕ} {l S : ℕ}
    (hl : 1 ≤ l) (hlS : l ≤ S) (hA : A.Nonempty) (hB : B.Nonempty)
    (hBodd : ∀ n ∈ B, Odd n) {a b : ℕ} (hab : a % 2 ≠ b % 2) {β : ℝ}
    (ha : β ≤ natResidueMass A 2 a) (hb : β ≤ natResidueMass A 2 b)
    {k : ZMod (2 ^ l)} (hk : IsUnit k) :
    (∑ x : ZMod (2 ^ l),
      cyclicMultiplierAverage (fun y : ZMod (2 ^ l) => ‖cyclicUniformNatSet B y‖)
        (Finset.Ioc 0 (2 ^ S)) x * ‖ZMod.dft (cyclicUniformNatSet A) (x * k)‖ ^ 2) ≤ 1 - β := by
  apply dyadic_multiplier_fourier_energy_gap hlS (cyclicUniformNatSet A) _
    (ZMod.castHom (pow_dvd_pow 2 hl) (ZMod 2))
    (sum_norm_cyclicUniformNatSet hA) (sum_norm_cyclicUniformNatSet hB)
    (cyclicUniformNatSet_support_odd hBodd l) (a := (a : ZMod 2)) (b := (b : ZMod 2)) ?_ ?_ ?_ hk
  · intro heq
    have hh := congrArg ZMod.val heq
    exact hab (by simpa only [ZMod.val_natCast] using hh)
  · rwa [dyadic_uniform_parity_mass hl]
  · rwa [dyadic_uniform_parity_mass hl]

noncomputable def natMultiplierEnergy {q : ℕ} [NeZero q]
    (A B C : Finset ℕ) (k : ZMod q) : ℝ :=
  (∑ c ∈ C, ∑ b ∈ B, ‖ZMod.dft (cyclicUniformNatSet A)
    (((b * c : ℕ) : ZMod q) * k)‖ ^ 2) / ((B.card : ℝ) * (C.card : ℝ))

theorem natMultiplierEnergy_eq_weighted {q : ℕ} [NeZero q]
    (A B C : Finset ℕ) (k : ZMod q) :
    natMultiplierEnergy A B C k =
      ∑ x : ZMod q, cyclicMultiplierAverage (fun y : ZMod q => ‖cyclicUniformNatSet B y‖) C x *
        ‖ZMod.dft (cyclicUniformNatSet A) (x * k)‖ ^ 2 := by
  rw [sum_test_cyclicMultiplierAverage]
  simp_rw [sum_test_norm_cyclicUniformNatSet]
  rw [← Finset.sum_div, div_div]
  simp only [natMultiplierEnergy, Nat.cast_mul]

theorem natMultiplierEnergy_nonneg {q : ℕ} [NeZero q]
    (A B C : Finset ℕ) (k : ZMod q) : 0 ≤ natMultiplierEnergy A B C k := by
  unfold natMultiplierEnergy
  positivity

theorem natMultiplierEnergy_le_one {q : ℕ} [NeZero q]
    {A B C : Finset ℕ} (hA : A.Nonempty) (hB : B.Nonempty) (hC : C.Nonempty) (k : ZMod q) :
    natMultiplierEnergy A B C k ≤ 1 := by
  rw [natMultiplierEnergy_eq_weighted]
  exact weighted_fourier_energy_le_one (cyclicUniformNatSet A) _ (sum_norm_cyclicUniformNatSet hA)
    (cyclic_multiplier_average_nonneg _ C (fun _ => norm_nonneg _))
    (by rw [cyclic_multiplier_average_sum _ hC, sum_norm_cyclicUniformNatSet hB]) k

theorem natMultiplierEnergy_transfer {Q q : ℕ} [NeZero Q] [NeZero q]
    (A B C : Finset ℕ) (x : ZMod Q) (y : ZMod q)
    (hphase : ∀ n : ℕ, ZMod.stdAddChar (-((n : ZMod Q) * x)) =
      ZMod.stdAddChar (-((n : ZMod q) * y))) :
    natMultiplierEnergy A B C x = natMultiplierEnergy A B C y := by
  unfold natMultiplierEnergy
  congr 1
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro b hb
  have hterm : ZMod.dft (cyclicUniformNatSet A) (((b * c : ℕ) : ZMod Q) * x) =
      ZMod.dft (cyclicUniformNatSet A) (((b * c : ℕ) : ZMod q) * y) := by
    rw [dft_cyclicUniformNatSet, dft_cyclicUniformNatSet]
    congr 1
    apply Finset.sum_congr rfl
    intro n hn
    simpa only [Nat.cast_mul, mul_assoc] using hphase (n * (b * c))
  rw [hterm]

theorem natMultiplierEnergy_dyadic_short {K S : ℕ} {A B : Finset ℕ}
    (hA : A.Nonempty) (hB : B.Nonempty) (hBodd : ∀ n ∈ B, Odd n)
    {a b : ℕ} (hab : a % 2 ≠ b % 2) {β : ℝ}
    (ha : β ≤ natResidueMass A 2 a) (hb : β ≤ natResidueMass A 2 b)
    {k : ZMod (2 ^ K)} (hk : k ≠ 0) (hlevel : dyadicConductorLevel k ≤ S) :
    natMultiplierEnergy A B (Finset.Ioc 0 (2 ^ S)) k ≤ 1 - β := by
  have hl : 1 ≤ dyadicConductorLevel k := dyadic_conductor_pos hk
  have hlK : dyadicConductorLevel k ≤ K := (dyadic_conductor_spec k).1
  obtain ⟨m, hm, hfactor⟩ := dyadic_frequency_factor hk
  rw [natMultiplierEnergy_transfer A B (Finset.Ioc 0 (2 ^ S)) k
    (m : ZMod (2 ^ dyadicConductorLevel k)) (fun n => dyadic_frequency_phase hlK hfactor n),
    natMultiplierEnergy_eq_weighted]
  exact dyadic_uniform_multiplier_energy_gap hl hlevel hA hB hBodd hab ha hb
    (odd_natCast_isUnit_dyadic _ hm)

theorem natMultiplierEnergy_dyadic_long {g ρ : ℝ} (hg : 0 ≤ g) {K S : ℕ}
    (hS : (S : ℝ) + 1 ≤ (2 : ℝ) ^ (g * (S : ℝ))) {A B : Finset ℕ} (hA : A.Nonempty)
    (hAmass : ∀ l : ℕ, S < l → l ≤ K → ∀ x : ZMod (2 ^ l),
      ‖cyclicUniformNatSet A x‖ ≤ (2 : ℝ) ^ (-(1 - 3 * ρ) * (l : ℝ)))
    (hBmass : ∀ l : ℕ, S < l → l ≤ K → ∀ x : ZMod (2 ^ l),
      ‖cyclicUniformNatSet B x‖ ≤ (2 : ℝ) ^ (-(2 * g) * (l : ℝ)))
    {k : ZMod (2 ^ K)} (hlevel : S < dyadicConductorLevel k) :
    natMultiplierEnergy A B (Finset.Ioc 0 (2 ^ S)) k ≤
      (2 : ℝ) ^ (-(g - 3 * ρ) * (dyadicConductorLevel k : ℝ)) := by
  have hk : k ≠ 0 := by
    intro hk
    subst k
    simp [dyadicConductorLevel] at hlevel
  have hlK : dyadicConductorLevel k ≤ K := (dyadic_conductor_spec k).1
  obtain ⟨m, hm, hfactor⟩ := dyadic_frequency_factor hk
  rw [natMultiplierEnergy_transfer A B (Finset.Ioc 0 (2 ^ S)) k
    (m : ZMod (2 ^ dyadicConductorLevel k)) (fun n => dyadic_frequency_phase hlK hfactor n),
    natMultiplierEnergy_eq_weighted]
  exact dyadic_multiplier_fourier_energy_decay hg hS hlevel.le (cyclicUniformNatSet A) _
    (sum_norm_cyclicUniformNatSet hA) (hAmass _ hlevel hlK) (hBmass _ hlevel hlK)
    (odd_natCast_isUnit_dyadic _ hm)

theorem exists_power_for_dyadic_multiplier_energy {g ρ β : ℝ}
    (hg : 0 < g) (hρ : 3 * ρ < g) (hβ : 0 < β) (hβ1 : β ≤ 1) (M : ℕ) :
    ∃ S r : ℕ, M ≤ S ∧ 0 < S ∧ 0 < r ∧
      ∀ K : ℕ, ∀ A B : Finset ℕ, A.Nonempty → B.Nonempty → (∀ n ∈ B, Odd n) →
      (∃ a b : ℕ, a % 2 ≠ b % 2 ∧ β ≤ natResidueMass A 2 a ∧ β ≤ natResidueMass A 2 b) →
      (∀ l : ℕ, S < l → l ≤ K → ∀ x : ZMod (2 ^ l),
        ‖cyclicUniformNatSet A x‖ ≤ (2 : ℝ) ^ (-(1 - 3 * ρ) * (l : ℝ))) →
      (∀ l : ℕ, S < l → l ≤ K → ∀ x : ZMod (2 ^ l),
        ‖cyclicUniformNatSet B x‖ ≤ (2 : ℝ) ^ (-(2 * g) * (l : ℝ))) →
      (∑ k : ZMod (2 ^ K), (natMultiplierEnergy A B (Finset.Ioc 0 (2 ^ S)) k) ^ r) < 2 := by
  obtain ⟨S, hMS, hSpos, hS⟩ := exists_dyadic_multiplier_cutoff hg M
  obtain ⟨r, hr, hpower⟩ := exists_power_for_piecewise_dyadic_energy S
    (show 0 ≤ 1 - β by linarith) (show 1 - β < 1 by linarith) (show 0 < g - 3 * ρ by linarith)
  refine ⟨S, r, hMS, hSpos, hr, ?_⟩
  intro K A B hA hB hBodd hsplit hAmass hBmass
  obtain ⟨a, b, hab, ha, hb⟩ := hsplit
  have hC : (Finset.Ioc 0 (2 ^ S)).Nonempty := Finset.nonempty_Ioc.mpr (by positivity)
  exact hpower K _ (natMultiplierEnergy_nonneg _ _ _)
    (natMultiplierEnergy_le_one hA hB hC 0)
    (fun k hk hlevel => natMultiplierEnergy_dyadic_short hA hB hBodd hab ha hb hk hlevel)
    (fun k hlevel => natMultiplierEnergy_dyadic_long hg.le hS hA hAmass hBmass hlevel)

theorem stdAddChar_dyadic_affine_phase (u L r n z : ℕ) (k : ZMod (2 ^ (u + L))) :
    ZMod.stdAddChar (-((((r + 2 ^ u * n) * z : ℕ) : ZMod (2 ^ (u + L))) * k)) =
      ZMod.stdAddChar (-(((r * z : ℕ) : ZMod (2 ^ (u + L))) * k)) *
        ZMod.stdAddChar (-(((n * z : ℕ) : ZMod (2 ^ L)) * (k.val : ZMod (2 ^ L)))) := by
  have hs : ZMod.stdAddChar (-((((2 ^ u * n) * z : ℕ) : ZMod (2 ^ (u + L))) * k)) =
      ZMod.stdAddChar (-(((n * z : ℕ) : ZMod (2 ^ L)) * (k.val : ZMod (2 ^ L)))) := by
    have hh := stdAddChar_scaled_modulus (show 2 ^ (u + L) = 2 ^ u * 2 ^ L by rw [pow_add])
      (-((n : ℤ) * (z : ℤ) * (k.val : ℤ)))
    convert hh using 1
    · push_cast
      rw [ZMod.natCast_zmod_val]
      congr 1
      ring
    · push_cast
      rfl
  rw [← hs, ← AddChar.map_add_eq_mul]
  congr 1
  push_cast
  ring

noncomputable def cyclicAffineNatSet {q : ℕ} [NeZero q]
    (A : Finset ℕ) (r d z : ℕ) : ZMod q → ℂ :=
  cyclicPushforward (fun _ : A => (A.card : ℂ)⁻¹)
    (fun n => (((r + d * n.val) * z : ℕ) : ZMod q))

theorem dft_cyclicAffineNatSet (u L : ℕ) (A : Finset ℕ) (r z : ℕ) (k : ZMod (2 ^ (u + L))) :
    ZMod.dft (cyclicAffineNatSet A r (2 ^ u) z) k =
      ZMod.stdAddChar (-(((r * z : ℕ) : ZMod (2 ^ (u + L))) * k)) *
        ZMod.dft (cyclicUniformNatSet A) ((z : ZMod (2 ^ L)) * (k.val : ZMod (2 ^ L))) := by
  rw [cyclicAffineNatSet, dft_cyclicPushforward, dft_cyclicUniformNatSet]
  simp_rw [stdAddChar_dyadic_affine_phase, Nat.cast_mul, mul_assoc]
  rw [← Finset.mul_sum, ← Finset.sum_mul]
  rw [Finset.sum_coe_sort A (fun n : ℕ => ZMod.stdAddChar
    (-((n : ZMod (2 ^ L)) * ((z : ZMod (2 ^ L)) * (k.val : ZMod (2 ^ L))))))]

theorem norm_dft_cyclicAffineNatSet (u L : ℕ) (A : Finset ℕ) (r z : ℕ)
    (k : ZMod (2 ^ (u + L))) :
    ‖ZMod.dft (cyclicAffineNatSet A r (2 ^ u) z) k‖ =
      ‖ZMod.dft (cyclicUniformNatSet A) ((z : ZMod (2 ^ L)) * (k.val : ZMod (2 ^ L)))‖ := by
  rw [dft_cyclicAffineNatSet, norm_mul]
  simp only [ZMod.stdAddChar_apply, Circle.norm_coe, one_mul]

theorem cyclicAffineNatSet_coset_support (u L : ℕ) (A : Finset ℕ) (r z : ℕ)
    (x : ZMod (2 ^ (u + L))) (hx : cyclicAffineNatSet A r (2 ^ u) z x ≠ 0) :
    ZMod.castHom (pow_dvd_pow 2 (show u ≤ u + L by omega)) (ZMod (2 ^ u)) x =
      ((r * z : ℕ) : ZMod (2 ^ u)) := by
  obtain ⟨n, hn, hnw⟩ := cyclicPushforward_support (fun _ : A => (A.card : ℂ)⁻¹)
    (fun n : A => (((r + 2 ^ u * n.val) * z : ℕ) : ZMod (2 ^ (u + L)))) hx
  rw [← hn, map_natCast]
  have hd : ((2 ^ u : ℕ) : ZMod (2 ^ u)) = 0 := ZMod.natCast_self _
  simp only [Nat.cast_mul, Nat.cast_add, hd, zero_mul, add_zero]

noncomputable def cyclicAffineProductLaw {q : ℕ} [NeZero q]
    (A B C : Finset ℕ) (r d : ℕ) : ZMod q → ℂ :=
  cyclicMixture (fun _ : B × C => ((B.card : ℝ) * (C.card : ℝ))⁻¹)
    (fun i => cyclicAffineNatSet A r d (i.1.val * i.2.val))

theorem sum_uniform_pair_weight {B C : Finset ℕ} (hB : B.Nonempty) (hC : C.Nonempty) :
    (∑ _ : B × C, ((B.card : ℝ) * (C.card : ℝ))⁻¹) = 1 := by
  have hBcard : (B.card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr hB).ne'
  have hCcard : (C.card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr hC).ne'
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_prod,
    Fintype.card_coe, Nat.cast_mul]
  exact mul_inv_cancel₀ (mul_ne_zero hBcard hCcard)

theorem cyclicAffineProductLaw_energy (u L : ℕ) (A B C : Finset ℕ) (r : ℕ)
    (k : ZMod (2 ^ (u + L))) :
    (∑ i : B × C, ((B.card : ℝ) * (C.card : ℝ))⁻¹ *
      ‖ZMod.dft (cyclicAffineNatSet A r (2 ^ u) (i.1.val * i.2.val)) k‖ ^ 2) =
        natMultiplierEnergy A B C (k.val : ZMod (2 ^ L)) := by
  simp only [norm_dft_cyclicAffineNatSet]
  rw [← Finset.mul_sum]
  have hsum : (∑ i : B × C,
      ‖ZMod.dft (cyclicUniformNatSet A)
        (((i.1.val * i.2.val : ℕ) : ZMod (2 ^ L)) * (k.val : ZMod (2 ^ L)))‖ ^ 2) =
      ∑ c ∈ C, ∑ b ∈ B, ‖ZMod.dft (cyclicUniformNatSet A)
        (((b * c : ℕ) : ZMod (2 ^ L)) * (k.val : ZMod (2 ^ L)))‖ ^ 2 := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    rw [Finset.sum_coe_sort C (fun c : ℕ => ∑ b : B, ‖ZMod.dft (cyclicUniformNatSet A)
      (((b.val * c : ℕ) : ZMod (2 ^ L)) * (k.val : ZMod (2 ^ L)))‖ ^ 2)]
    apply Finset.sum_congr rfl
    intro c hc
    exact Finset.sum_coe_sort B (fun b : ℕ => ‖ZMod.dft (cyclicUniformNatSet A)
      (((b * c : ℕ) : ZMod (2 ^ L)) * (k.val : ZMod (2 ^ L)))‖ ^ 2)
  rw [hsum]
  unfold natMultiplierEnergy
  ring

theorem dyadic_affine_product_peak_bound (u L s : ℕ) (A B C : Finset ℕ) (r : ℕ)
    (hB : B.Nonempty) (hC : C.Nonempty)
    (henergy : (∑ k : ZMod (2 ^ L), (natMultiplierEnergy A B C k) ^ s) < 2) :
    ∃ M : ZMod (2 ^ u) → ℝ, (∀ a, 0 ≤ M a) ∧
      (∀ x : ZMod (2 ^ (u + L)), ‖cyclicConvolutionPow (cyclicAffineProductLaw A B C r (2 ^ u))
        (2 * s) x‖ ≤ M ((ZMod.castHom (pow_dvd_pow 2 (show u ≤ u + L by omega))
          (ZMod (2 ^ u))) x)) ∧
      (2 : ℝ) ^ L * (∑ a : ZMod (2 ^ u), M a) < 2 := by
  exact dyadic_coset_mixture_peak_bound u L s
    (ZMod.castHom (pow_dvd_pow 2 (show u ≤ u + L by omega)) (ZMod (2 ^ u))).toAddMonoidHom
    (fun _ : B × C => ((B.card : ℝ) * (C.card : ℝ))⁻¹)
    (fun i => cyclicAffineNatSet A r (2 ^ u) (i.1.val * i.2.val))
    (fun i => ((r * (i.1.val * i.2.val) : ℕ) : ZMod (2 ^ u)))
    (fun _ => by positivity) (sum_uniform_pair_weight hB hC)
    (fun i x hx => cyclicAffineNatSet_coset_support u L A r (i.1.val * i.2.val) x hx)
    (natMultiplierEnergy A B C) (natMultiplierEnergy_nonneg A B C)
    (fun k => (cyclicAffineProductLaw_energy u L A B C r k).le) henergy

theorem exists_dyadic_multiplier_energy_majorant {g ρ β : ℝ}
    (hg : 0 < g) (hρ : 3 * ρ < g) (hβ : 0 < β) (hβ1 : β ≤ 1) (M : ℕ) :
    ∃ S s : ℕ, M ≤ S ∧ 0 < S ∧ 0 < s ∧ ∀ K : ℕ,
      ∃ E : ZMod (2 ^ K) → ℝ, (∀ k, 0 ≤ E k) ∧ (∑ k : ZMod (2 ^ K), (E k) ^ s) < 2 ∧
        ∀ A B : Finset ℕ, A.Nonempty → B.Nonempty → (∀ n ∈ B, Odd n) →
        (∃ a b : ℕ, a % 2 ≠ b % 2 ∧ β ≤ natResidueMass A 2 a ∧ β ≤ natResidueMass A 2 b) →
        (∀ l : ℕ, S < l → l ≤ K → ∀ x : ZMod (2 ^ l),
          ‖cyclicUniformNatSet A x‖ ≤ (2 : ℝ) ^ (-(1 - 3 * ρ) * (l : ℝ))) →
        (∀ l : ℕ, S < l → l ≤ K → ∀ x : ZMod (2 ^ l),
          ‖cyclicUniformNatSet B x‖ ≤ (2 : ℝ) ^ (-(2 * g) * (l : ℝ))) →
        ∀ k : ZMod (2 ^ K), natMultiplierEnergy A B (Finset.Ioc 0 (2 ^ S)) k ≤ E k := by
  obtain ⟨S, hMS, hSpos, hS⟩ := exists_dyadic_multiplier_cutoff hg M
  obtain ⟨s, hs, hpower⟩ := exists_power_for_piecewise_dyadic_energy S
    (show 0 ≤ 1 - β by linarith) (show 1 - β < 1 by linarith) (show 0 < g - 3 * ρ by linarith)
  refine ⟨S, s, hMS, hSpos, hs, ?_⟩
  intro K
  let E : ZMod (2 ^ K) → ℝ := fun k => if k = 0 then 1 else
    if dyadicConductorLevel k ≤ S then 1 - β else (2 : ℝ) ^ (-(g - 3 * ρ) * (dyadicConductorLevel k : ℝ))
  have hE : ∀ k, 0 ≤ E k := by
    intro k
    dsimp only [E]
    split_ifs <;> positivity
  have hEzero : E 0 ≤ 1 := by simp only [E, if_pos rfl, le_refl]
  have hshort : ∀ k, k ≠ 0 → dyadicConductorLevel k ≤ S → E k ≤ 1 - β := by
    intro k hk hlevel
    simp only [E, if_neg hk, if_pos hlevel, le_refl]
  have hlong : ∀ k, S < dyadicConductorLevel k → E k ≤
      (2 : ℝ) ^ (-(g - 3 * ρ) * (dyadicConductorLevel k : ℝ)) := by
    intro k hlevel
    have hk : k ≠ 0 := by
      intro hk
      subst k
      simp [dyadicConductorLevel] at hlevel
    simp only [E, if_neg hk, if_neg (not_le.mpr hlevel), le_refl]
  refine ⟨E, hE, hpower K E hE hEzero hshort hlong, ?_⟩
  intro A B hA hB hBodd hsplit hAmass hBmass k
  obtain ⟨a, b, hab, ha, hb⟩ := hsplit
  by_cases hk : k = 0
  · subst k
    simpa only [E, if_pos rfl] using natMultiplierEnergy_le_one hA hB
      (Finset.nonempty_Ioc.mpr (by positivity : 0 < 2 ^ S)) (0 : ZMod (2 ^ K))
  · by_cases hlevel : dyadicConductorLevel k ≤ S
    · simpa only [E, if_neg hk, if_pos hlevel] using
        natMultiplierEnergy_dyadic_short hA hB hBodd hab ha hb hk hlevel
    · simpa only [E, if_neg hk, if_neg hlevel] using
        natMultiplierEnergy_dyadic_long hg.le hS hA hAmass hBmass (lt_of_not_ge hlevel)

noncomputable def cyclicAffineMixtureProductLaw {ι : Type*} [Fintype ι] {q : ℕ} [NeZero q]
    (w : ι → ℝ) (A : ι → Finset ℕ) (B C : Finset ℕ) (r : ι → ℕ) (d : ℕ) : ZMod q → ℂ :=
  cyclicMixture (fun i : ι × (B × C) => w i.1 / ((B.card : ℝ) * (C.card : ℝ)))
    (fun i => cyclicAffineNatSet (A i.1) (r i.1) d (i.2.1.val * i.2.2.val))

theorem sum_mixture_pair_weight {ι : Type*} [Fintype ι] (w : ι → ℝ)
    (hmass : ∑ i : ι, w i = 1) {B C : Finset ℕ} (hB : B.Nonempty) (hC : C.Nonempty) :
    (∑ i : ι × (B × C), w i.1 / ((B.card : ℝ) * (C.card : ℝ))) = 1 := by
  rw [Fintype.sum_prod_type]
  simp only [div_eq_mul_inv, ← Finset.mul_sum, sum_uniform_pair_weight hB hC, mul_one, hmass]

theorem cyclicAffineMixtureProductLaw_energy {ι : Type*} [Fintype ι] (u L : ℕ)
    (w : ι → ℝ) (A : ι → Finset ℕ) (B C : Finset ℕ) (r : ι → ℕ) (k : ZMod (2 ^ (u + L))) :
    (∑ i : ι × (B × C), (w i.1 / ((B.card : ℝ) * (C.card : ℝ))) *
      ‖ZMod.dft (cyclicAffineNatSet (A i.1) (r i.1) (2 ^ u) (i.2.1.val * i.2.2.val)) k‖ ^ 2) =
      ∑ i : ι, w i * natMultiplierEnergy (A i) B C (k.val : ZMod (2 ^ L)) := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← cyclicAffineProductLaw_energy u L (A i) B C (r i) k, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  dsimp only
  ring

theorem dyadic_affine_mixture_peak_bound {ι : Type*} [Fintype ι] (u L s : ℕ)
    (w : ι → ℝ) (A : ι → Finset ℕ) (B C : Finset ℕ) (r : ι → ℕ)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i : ι, w i = 1) (hB : B.Nonempty) (hC : C.Nonempty)
    (E : ZMod (2 ^ L) → ℝ) (hE : ∀ k, 0 ≤ E k)
    (hmajor : ∀ i k, natMultiplierEnergy (A i) B C k ≤ E k)
    (henergy : (∑ k : ZMod (2 ^ L), (E k) ^ s) < 2) :
    ∃ M : ZMod (2 ^ u) → ℝ, (∀ a, 0 ≤ M a) ∧
      (∀ x : ZMod (2 ^ (u + L)),
        ‖cyclicConvolutionPow (cyclicAffineMixtureProductLaw w A B C r (2 ^ u)) (2 * s) x‖ ≤
          M ((ZMod.castHom (pow_dvd_pow 2 (show u ≤ u + L by omega)) (ZMod (2 ^ u))) x)) ∧
      (2 : ℝ) ^ L * (∑ a : ZMod (2 ^ u), M a) < 2 := by
  apply dyadic_coset_mixture_peak_bound u L s
    (ZMod.castHom (pow_dvd_pow 2 (show u ≤ u + L by omega)) (ZMod (2 ^ u))).toAddMonoidHom
    (fun i : ι × (B × C) => w i.1 / ((B.card : ℝ) * (C.card : ℝ)))
    (fun i => cyclicAffineNatSet (A i.1) (r i.1) (2 ^ u) (i.2.1.val * i.2.2.val))
    (fun i => ((r i.1 * (i.2.1.val * i.2.2.val) : ℕ) : ZMod (2 ^ u)))
    (fun i => div_nonneg (hw i.1) (by positivity)) (sum_mixture_pair_weight w hmass hB hC)
    (fun i x hx => cyclicAffineNatSet_coset_support u L (A i.1) (r i.1)
      (i.2.1.val * i.2.2.val) x hx) E hE ?_ henergy
  intro k
  rw [cyclicAffineMixtureProductLaw_energy]
  calc
    _ ≤ ∑ i : ι, w i * E (k.val : ZMod (2 ^ L)) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hmajor i _) (hw i))
    _ = _ := by rw [← Finset.sum_mul, hmass, one_mul]

theorem exists_dyadic_affine_mixture_peak {g ρ β : ℝ}
    (hg : 0 < g) (hρ : 3 * ρ < g) (hβ : 0 < β) (hβ1 : β ≤ 1) (M₀ : ℕ) :
    ∃ S s : ℕ, M₀ ≤ S ∧ 0 < S ∧ 0 < s ∧
      ∀ u L : ℕ, ∀ (ι : Type) [Fintype ι], ∀ (w : ι → ℝ) (A : ι → Finset ℕ)
        (r : ι → ℕ) (B : Finset ℕ),
      (∀ i, 0 ≤ w i) → (∑ i : ι, w i = 1) → (∀ i, (A i).Nonempty) → B.Nonempty →
      (∀ n ∈ B, Odd n) →
      (∀ i, ∃ a b : ℕ, a % 2 ≠ b % 2 ∧ β ≤ natResidueMass (A i) 2 a ∧ β ≤ natResidueMass (A i) 2 b) →
      (∀ i, ∀ l : ℕ, S < l → l ≤ L → ∀ x : ZMod (2 ^ l),
        ‖cyclicUniformNatSet (A i) x‖ ≤ (2 : ℝ) ^ (-(1 - 3 * ρ) * (l : ℝ))) →
      (∀ l : ℕ, S < l → l ≤ L → ∀ x : ZMod (2 ^ l),
        ‖cyclicUniformNatSet B x‖ ≤ (2 : ℝ) ^ (-(2 * g) * (l : ℝ))) →
      ∃ M : ZMod (2 ^ u) → ℝ, (∀ a, 0 ≤ M a) ∧
        (∀ x : ZMod (2 ^ (u + L)),
          ‖cyclicConvolutionPow
            (cyclicAffineMixtureProductLaw w A B (Finset.Ioc 0 (2 ^ S)) r (2 ^ u)) (2 * s) x‖ ≤
            M ((ZMod.castHom (pow_dvd_pow 2 (show u ≤ u + L by omega)) (ZMod (2 ^ u))) x)) ∧
        (2 : ℝ) ^ L * (∑ a : ZMod (2 ^ u), M a) < 2 := by
  obtain ⟨S, s, hMS, hS, hs, hbound⟩ := exists_dyadic_multiplier_energy_majorant hg hρ hβ hβ1 M₀
  refine ⟨S, s, hMS, hS, hs, ?_⟩
  intro u L ι inst w A r B hw hmass hA hB hBodd hsplit hAmass hBmass
  obtain ⟨E, hE, hEsum, hmajor⟩ := hbound L
  exact dyadic_affine_mixture_peak_bound u L s w A B (Finset.Ioc 0 (2 ^ S)) r hw hmass hB
    (Finset.nonempty_Ioc.mpr (by positivity)) E hE
    (fun i k => hmajor (A i) B (hA i) hB hBodd (hsplit i) (hAmass i) hBmass k) hEsum

theorem sum_dyadic_zoom {R : Type*} [AddCommMonoid R] (A : Finset ℕ) (u r : ℕ) (h : ℕ → R) :
    (∑ n ∈ dyadicZoom A u r, h (r + 2 ^ u * n)) =
      ∑ n ∈ A.filter (fun n => n % 2 ^ u = r), h n := by
  rw [dyadicZoom, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro n hn
    rw [← (Finset.mem_filter.mp hn).2, Nat.mod_add_div]
  · intro x hx y hy hxy
    change x / 2 ^ u = y / 2 ^ u at hxy
    have hmod : x % 2 ^ u = y % 2 ^ u :=
      (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm
    calc
      x = x % 2 ^ u + 2 ^ u * (x / 2 ^ u) := (Nat.mod_add_div x (2 ^ u)).symm
      _ = y % 2 ^ u + 2 ^ u * (y / 2 ^ u) := by rw [hmod, hxy]
      _ = y := Nat.mod_add_div y (2 ^ u)

theorem sum_dyadic_fibers {R : Type*} [AddCommMonoid R] (A : Finset ℕ) (u : ℕ) (h : ℕ → R) :
    (∑ r ∈ dyadicProjection A u, ∑ n ∈ A.filter (fun n => n % 2 ^ u = r), h n) = ∑ n ∈ A, h n := by
  have hmaps : ∀ n ∈ A, n % 2 ^ u ∈ dyadicProjection A u :=
    fun n hn => Finset.mem_image.mpr ⟨n, hn, rfl⟩
  exact Finset.sum_fiberwise_of_maps_to hmaps h

noncomputable def dyadicFiberWeight (A : Finset ℕ) (u r : ℕ) : ℝ :=
  ((dyadicZoom A u r).card : ℝ) / (A.card : ℝ)

theorem dyadic_fiber_weight_nonneg (A : Finset ℕ) (u r : ℕ) : 0 ≤ dyadicFiberWeight A u r := by
  unfold dyadicFiberWeight
  positivity

theorem sum_dyadic_fiber_weight {A : Finset ℕ} (hA : A.Nonempty) (u : ℕ) :
    (∑ r : dyadicProjection A u, dyadicFiberWeight A u r.val) = 1 := by
  have hcard : (A.card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr hA).ne'
  rw [Finset.sum_coe_sort (dyadicProjection A u) (dyadicFiberWeight A u)]
  simp only [dyadicFiberWeight, dyadic_zoom_card, ← Finset.sum_div]
  have hh := sum_dyadic_fibers A u (fun _ => (1 : ℝ))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hh
  rw [hh, div_self hcard]

theorem cyclicAffineNatSet_apply {q : ℕ} [NeZero q] (A : Finset ℕ) (r d z : ℕ) (x : ZMod q) :
    cyclicAffineNatSet A r d z x =
      (∑ n ∈ A, if ((((r + d * n) * z : ℕ) : ZMod q)) = x then (1 : ℂ) else 0) / (A.card : ℂ) := by
  classical
  rw [cyclicAffineNatSet, cyclicPushforward]
  rw [Finset.sum_coe_sort A (fun n => if ((((r + d * n) * z : ℕ) : ZMod q)) = x then
    (A.card : ℂ)⁻¹ else 0)]
  rw [div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n hn
  split_ifs <;> simp only [one_mul, zero_mul]

theorem cyclicAffineNatSet_zoom_apply {q : ℕ} [NeZero q]
    (A : Finset ℕ) (u r z : ℕ) (x : ZMod q) :
    cyclicAffineNatSet (dyadicZoom A u r) r (2 ^ u) z x =
      (∑ n ∈ A.filter (fun n => n % 2 ^ u = r),
        if ((n * z : ℕ) : ZMod q) = x then (1 : ℂ) else 0) /
          ((A.filter (fun n => n % 2 ^ u = r)).card : ℂ) := by
  rw [cyclicAffineNatSet_apply, dyadic_zoom_card]
  congr 1
  exact sum_dyadic_zoom A u r (fun n => if ((n * z : ℕ) : ZMod q) = x then (1 : ℂ) else 0)

theorem cyclicAffineNatSet_dyadic_disintegration {q : ℕ} [NeZero q]
    {A : Finset ℕ} (hA : A.Nonempty) (u z : ℕ) :
    cyclicMixture (fun r : dyadicProjection A u => dyadicFiberWeight A u r.val)
      (fun r => cyclicAffineNatSet (dyadicZoom A u r.val) r.val (2 ^ u) z) =
        (cyclicAffineNatSet A 0 1 z : ZMod q → ℂ) := by
  classical
  have hAcard : (A.card : ℂ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr hA).ne'
  funext x
  unfold cyclicMixture
  have hterm (r : dyadicProjection A u) :
      (dyadicFiberWeight A u r.val : ℂ) *
        cyclicAffineNatSet (dyadicZoom A u r.val) r.val (2 ^ u) z x =
      (∑ n ∈ A.filter (fun n => n % 2 ^ u = r.val),
        if ((n * z : ℕ) : ZMod q) = x then (1 : ℂ) else 0) / (A.card : ℂ) := by
    have hcard : ((dyadicZoom A u r.val).card : ℂ) ≠ 0 := by
      exact_mod_cast (Finset.card_pos.mpr (dyadic_zoom_nonempty r.property)).ne'
    rw [dyadic_zoom_card] at hcard
    rw [cyclicAffineNatSet_zoom_apply]
    simp only [dyadicFiberWeight, dyadic_zoom_card, Complex.ofReal_div, Complex.ofReal_natCast]
    field_simp
  simp_rw [hterm]
  rw [Finset.sum_coe_sort (dyadicProjection A u) (fun r =>
    (∑ n ∈ A.filter (fun n => n % 2 ^ u = r),
      if ((n * z : ℕ) : ZMod q) = x then (1 : ℂ) else 0) / (A.card : ℂ))]
  rw [← Finset.sum_div, sum_dyadic_fibers, cyclicAffineNatSet_apply]
  simp only [one_mul, zero_add]

theorem cyclicAffineProductLaw_dyadic_disintegration {q : ℕ} [NeZero q]
    {A : Finset ℕ} (hA : A.Nonempty) (u : ℕ) (B C : Finset ℕ) :
    cyclicAffineMixtureProductLaw
      (fun r : dyadicProjection A u => dyadicFiberWeight A u r.val)
      (fun r => dyadicZoom A u r.val) B C (fun r => r.val) (2 ^ u) =
        (cyclicAffineProductLaw A B C 0 1 : ZMod q → ℂ) := by
  funext x
  unfold cyclicAffineMixtureProductLaw cyclicAffineProductLaw cyclicMixture
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  dsimp only
  have hdis := congrFun (cyclicAffineNatSet_dyadic_disintegration (q := q) hA u
    (j.1.val * j.2.val)) x
  change (∑ r : dyadicProjection A u, (dyadicFiberWeight A u r.val : ℂ) *
    cyclicAffineNatSet (dyadicZoom A u r.val) r.val (2 ^ u) (j.1.val * j.2.val) x) =
      cyclicAffineNatSet A 0 1 (j.1.val * j.2.val) x at hdis
  rw [← hdis, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  simp only [Complex.ofReal_div, Complex.ofReal_inv]
  ring

theorem exists_dyadic_set_product_peak {g ρ β : ℝ}
    (hg : 0 < g) (hρ : 3 * ρ < g) (hβ : 0 < β) (hβ1 : β ≤ 1) (M₀ : ℕ) :
    ∃ S s : ℕ, M₀ ≤ S ∧ 0 < S ∧ 0 < s ∧ ∀ u L : ℕ, ∀ A B : Finset ℕ,
      A.Nonempty → B.Nonempty → (∀ n ∈ B, Odd n) →
      (∀ r ∈ dyadicProjection A u, ∃ a b : ℕ, a % 2 ≠ b % 2 ∧
        β ≤ natResidueMass (dyadicZoom A u r) 2 a ∧ β ≤ natResidueMass (dyadicZoom A u r) 2 b) →
      (∀ r ∈ dyadicProjection A u, ∀ l : ℕ, S < l → l ≤ L → ∀ x : ZMod (2 ^ l),
        ‖cyclicUniformNatSet (dyadicZoom A u r) x‖ ≤ (2 : ℝ) ^ (-(1 - 3 * ρ) * (l : ℝ))) →
      (∀ l : ℕ, S < l → l ≤ L → ∀ x : ZMod (2 ^ l),
        ‖cyclicUniformNatSet B x‖ ≤ (2 : ℝ) ^ (-(2 * g) * (l : ℝ))) →
      ∃ M : ZMod (2 ^ u) → ℝ, (∀ a, 0 ≤ M a) ∧
        (∀ x : ZMod (2 ^ (u + L)),
          ‖cyclicConvolutionPow (cyclicAffineProductLaw A B (Finset.Ioc 0 (2 ^ S)) 0 1) (2 * s) x‖ ≤
            M ((ZMod.castHom (pow_dvd_pow 2 (show u ≤ u + L by omega)) (ZMod (2 ^ u))) x)) ∧
        (2 : ℝ) ^ L * (∑ a : ZMod (2 ^ u), M a) < 2 := by
  obtain ⟨S, s, hMS, hS, hs, hpeak⟩ := exists_dyadic_affine_mixture_peak hg hρ hβ hβ1 M₀
  refine ⟨S, s, hMS, hS, hs, ?_⟩
  intro u L A B hA hB hBodd hsplit hAmass hBmass
  obtain ⟨M, hM, hpoint, hsum⟩ := hpeak u L (dyadicProjection A u)
    (fun r => dyadicFiberWeight A u r.val) (fun r => dyadicZoom A u r.val) (fun r => r.val) B
    (fun r => dyadic_fiber_weight_nonneg A u r.val) (sum_dyadic_fiber_weight hA u)
    (fun r => dyadic_zoom_nonempty r.property) hB hBodd
    (fun r => hsplit r.val r.property) (fun r => hAmass r.val r.property) hBmass
  refine ⟨M, hM, ?_, hsum⟩
  rw [cyclicAffineProductLaw_dyadic_disintegration hA u B (Finset.Ioc 0 (2 ^ S))] at hpoint
  exact hpoint

structure FiniteComplexProbability {ι : Type*} [Fintype ι] (f : ι → ℂ) : Prop where
  norm_cast : ∀ x, f x = (‖f x‖ : ℂ)
  sum_eq_one : ∑ x : ι, f x = 1

theorem finite_complex_probability_ofReal {ι : Type*} [Fintype ι] (p : ι → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hmass : ∑ x : ι, p x = 1) :
    FiniteComplexProbability (fun x => (p x : ℂ)) := by
  refine ⟨?_, ?_⟩
  · intro x
    rw [Complex.norm_of_nonneg (hp x)]
  · rw [← Complex.ofReal_sum, hmass, Complex.ofReal_one]

theorem finite_complex_probability_sum_norm {ι : Type*} [Fintype ι] {f : ι → ℂ}
    (hf : FiniteComplexProbability f) : ∑ x : ι, ‖f x‖ = 1 := by
  have hre (x : ι) : (f x).re = ‖f x‖ := by
    simpa only [Complex.ofReal_re] using congrArg Complex.re (hf.norm_cast x)
  have hh := congrArg Complex.re hf.sum_eq_one
  simpa only [Complex.re_sum, Complex.one_re, hre] using hh

theorem sum_cyclicPushforward {ι : Type*} [Fintype ι] {q : ℕ} [NeZero q]
    (p : ι → ℂ) (π : ι → ZMod q) : ∑ x : ZMod q, cyclicPushforward p π x = ∑ i : ι, p i := by
  simpa only [one_mul] using sum_test_cyclicPushforward p π (fun _ => 1)

theorem cyclicPushforward_eq_norm_pushforward {ι : Type*} [Fintype ι] {q : ℕ} [NeZero q]
    (p : ι → ℂ) (π : ι → ZMod q) (hp : ∀ i, p i = (‖p i‖ : ℂ)) (x : ZMod q) :
    cyclicPushforward p π x = (finitePushforward (fun i => ‖p i‖) π x : ℂ) := by
  calc
    _ = cyclicPushforward (fun i => (‖p i‖ : ℂ)) π x := by
      congr 1
      exact funext hp
    _ = _ := cyclicPushforward_ofReal _ π x

theorem norm_cyclicPushforward_of_probability {ι : Type*} [Fintype ι] {q : ℕ} [NeZero q]
    {p : ι → ℂ} (hp : FiniteComplexProbability p) (π : ι → ZMod q) (x : ZMod q) :
    ‖cyclicPushforward p π x‖ = finitePushforward (fun i => ‖p i‖) π x := by
  rw [cyclicPushforward_eq_norm_pushforward p π hp.norm_cast]
  exact Complex.norm_of_nonneg (finite_pushforward_nonneg _ π (fun _ => norm_nonneg _) x)

theorem cyclicPushforward_probability {ι : Type*} [Fintype ι] {q : ℕ} [NeZero q]
    {p : ι → ℂ} (hp : FiniteComplexProbability p) (π : ι → ZMod q) :
    FiniteComplexProbability (cyclicPushforward p π) := by
  refine ⟨?_, ?_⟩
  · intro x
    rw [norm_cyclicPushforward_of_probability hp]
    exact cyclicPushforward_eq_norm_pushforward p π hp.norm_cast x
  · rw [sum_cyclicPushforward, hp.sum_eq_one]

theorem sum_cyclicConvolution {q : ℕ} [NeZero q] (f g : ZMod q → ℂ) :
    (∑ x : ZMod q, cyclicConvolution f g x) = (∑ x : ZMod q, f x) * ∑ x : ZMod q, g x := by
  simpa only [one_mul, ← Finset.mul_sum, ← Finset.sum_mul] using
    sum_test_cyclicConvolution f g (fun _ => 1)

theorem cyclicConvolution_probability {q : ℕ} [NeZero q] {f g : ZMod q → ℂ}
    (hf : FiniteComplexProbability f) (hg : FiniteComplexProbability g) :
    FiniteComplexProbability (cyclicConvolution f g) := by
  refine ⟨?_, ?_⟩
  · intro x
    have hrep : cyclicConvolution f g x =
        ((∑ y : ZMod q, ‖f y‖ * ‖g (x - y)‖ : ℝ) : ℂ) := by
      unfold cyclicConvolution
      rw [Complex.ofReal_sum]
      apply Finset.sum_congr rfl
      intro y hy
      calc
        _ = (‖f y‖ : ℂ) * (‖g (x - y)‖ : ℂ) :=
          congrArg₂ (fun a b : ℂ => a * b) (hf.norm_cast y) (hg.norm_cast (x - y))
        _ = _ := (Complex.ofReal_mul _ _).symm
    have hnonneg : 0 ≤ ∑ y : ZMod q, ‖f y‖ * ‖g (x - y)‖ :=
      Finset.sum_nonneg (fun y _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
    rw [hrep, Complex.norm_of_nonneg hnonneg]
  · rw [sum_cyclicConvolution, hf.sum_eq_one, hg.sum_eq_one, mul_one]

theorem cyclicConvolutionPow_probability {q : ℕ} [NeZero q] {f : ZMod q → ℂ}
    (hf : FiniteComplexProbability f) (s : ℕ) : FiniteComplexProbability (cyclicConvolutionPow f s) := by
  classical
  induction s with
  | zero =>
    refine ⟨?_, ?_⟩
    · intro x
      by_cases hx : x = 0 <;> simp [cyclicConvolutionPow, hx]
    · simp [cyclicConvolutionPow]
  | succ s ih => exact cyclicConvolution_probability hf ih

theorem cyclicMixture_probability {ι : Type*} [Fintype ι] {q : ℕ} [NeZero q]
    (w : ι → ℝ) (F : ι → ZMod q → ℂ) (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i : ι, w i = 1)
    (hF : ∀ i, FiniteComplexProbability (F i)) : FiniteComplexProbability (cyclicMixture w F) := by
  refine ⟨?_, ?_⟩
  · intro x
    have hrep : cyclicMixture w F x = ((∑ i : ι, w i * ‖F i x‖ : ℝ) : ℂ) := by
      unfold cyclicMixture
      rw [Complex.ofReal_sum]
      apply Finset.sum_congr rfl
      intro i hi
      calc
        _ = (w i : ℂ) * (‖F i x‖ : ℂ) := congrArg (fun z : ℂ => (w i : ℂ) * z) ((hF i).norm_cast x)
        _ = _ := (Complex.ofReal_mul _ _).symm
    have hnonneg : 0 ≤ ∑ i : ι, w i * ‖F i x‖ :=
      Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (norm_nonneg _))
    rw [hrep, Complex.norm_of_nonneg hnonneg]
  · have hFsum (i : ι) : ∑ x : ZMod q, F i x = 1 := (hF i).sum_eq_one
    unfold cyclicMixture
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, hFsum, mul_one, ← Complex.ofReal_sum, hmass, Complex.ofReal_one]

theorem cyclicAffineNatSet_probability {q : ℕ} [NeZero q] {A : Finset ℕ}
    (hA : A.Nonempty) (r d z : ℕ) : FiniteComplexProbability (cyclicAffineNatSet (q := q) A r d z) := by
  have hcard : (A.card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr hA).ne'
  have hmass : (∑ _ : A, (A.card : ℝ)⁻¹) = 1 := by
    simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_coe]
    exact mul_inv_cancel₀ hcard
  have hp := finite_complex_probability_ofReal (fun _ : A => (A.card : ℝ)⁻¹)
    (fun _ => by positivity) hmass
  have hh := cyclicPushforward_probability hp (fun n : A => (((r + d * n.val) * z : ℕ) : ZMod q))
  simpa only [cyclicAffineNatSet, Complex.ofReal_inv, Complex.ofReal_natCast] using hh

theorem cyclicAffineProductLaw_probability {q : ℕ} [NeZero q] {A B C : Finset ℕ}
    (hA : A.Nonempty) (hB : B.Nonempty) (hC : C.Nonempty) (r d : ℕ) :
    FiniteComplexProbability (cyclicAffineProductLaw (q := q) A B C r d) := by
  exact cyclicMixture_probability _ _ (fun _ => by positivity) (sum_uniform_pair_weight hB hC)
    (fun i => cyclicAffineNatSet_probability hA r d (i.1.val * i.2.val))

theorem cyclicPushforward_comp {ι : Type*} [Fintype ι] {Q q : ℕ} [NeZero Q] [NeZero q]
    (w : ι → ℂ) (T : ι → ZMod Q) (π : ZMod Q → ZMod q) :
    cyclicPushforward (cyclicPushforward w T) π = cyclicPushforward w (π ∘ T) := by
  classical
  funext a
  simpa only [cyclicPushforward, Function.comp_apply, ite_mul, one_mul, zero_mul] using
    sum_test_cyclicPushforward w T (fun x => if π x = a then (1 : ℂ) else 0)

theorem cyclicPushforward_mixture {ι : Type*} [Fintype ι] {Q q : ℕ} [NeZero Q] [NeZero q]
    (w : ι → ℝ) (F : ι → ZMod Q → ℂ) (π : ZMod Q → ZMod q) :
    cyclicPushforward (cyclicMixture w F) π = cyclicMixture w (fun i => cyclicPushforward (F i) π) := by
  classical
  funext a
  have hterm (x : ZMod Q) : (if π x = a then ∑ i : ι, (w i : ℂ) * F i x else 0) =
      ∑ i : ι, (w i : ℂ) * (if π x = a then F i x else 0) := by
    by_cases hx : π x = a <;> simp [hx]
  change (∑ x : ZMod Q, if π x = a then ∑ i : ι, (w i : ℂ) * F i x else 0) =
    ∑ i : ι, (w i : ℂ) * ∑ x : ZMod Q, if π x = a then F i x else 0
  simp_rw [hterm, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem cyclicPushforward_convolutionPow {Q q : ℕ} [NeZero Q] [NeZero q]
    (f : ZMod Q → ℂ) (π : ZMod Q →+ ZMod q) (s : ℕ) :
    cyclicPushforward (cyclicConvolutionPow f s) π = cyclicConvolutionPow (cyclicPushforward f π) s := by
  classical
  induction s with
  | zero =>
    funext a
    have hterm (x : ZMod Q) : (if π x = a then (if x = 0 then (1 : ℂ) else 0) else 0) =
        if x = 0 then (if a = 0 then (1 : ℂ) else 0) else 0 := by
      by_cases hx : x = 0
      · subst x
        simp [eq_comm]
      · simp only [if_neg hx, ite_self]
    simp only [cyclicConvolutionPow, cyclicPushforward, hterm]
    simp
  | succ s ih => rw [cyclicConvolutionPow, cyclicPushforward_convolution, ih, cyclicConvolutionPow]

theorem cyclicPushforward_cyclicUniformNatSet {Q q : ℕ} [NeZero Q] [NeZero q]
    (π : ZMod Q →+* ZMod q) (A : Finset ℕ) :
    cyclicPushforward (cyclicUniformNatSet (q := Q) A) π = cyclicUniformNatSet (q := q) A := by
  unfold cyclicUniformNatSet
  rw [cyclicPushforward_comp]
  congr 1
  funext n
  simp only [Function.comp_apply, map_natCast]

theorem cyclicPushforward_cyclicAffineNatSet {Q q : ℕ} [NeZero Q] [NeZero q]
    (π : ZMod Q →+* ZMod q) (A : Finset ℕ) (r d z : ℕ) :
    cyclicPushforward (cyclicAffineNatSet (q := Q) A r d z) π = cyclicAffineNatSet (q := q) A r d z := by
  unfold cyclicAffineNatSet
  rw [cyclicPushforward_comp]
  congr 1
  funext n
  simp only [Function.comp_apply, map_natCast]

theorem cyclicPushforward_cyclicAffineProductLaw {Q q : ℕ} [NeZero Q] [NeZero q]
    (π : ZMod Q →+* ZMod q) (A B C : Finset ℕ) (r d : ℕ) :
    cyclicPushforward (cyclicAffineProductLaw (q := Q) A B C r d) π =
      cyclicAffineProductLaw (q := q) A B C r d := by
  unfold cyclicAffineProductLaw
  rw [cyclicPushforward_mixture]
  congr 1
  funext i
  exact cyclicPushforward_cyclicAffineNatSet π A r d (i.1.val * i.2.val)

noncomputable def dyadicProductSumLaw (A B C : Finset ℕ) (s k : ℕ) : ZMod (2 ^ k) → ℂ :=
  cyclicConvolutionPow (cyclicAffineProductLaw A B C 0 1) s

noncomputable def dyadicProductSumEntropy (A B C : Finset ℕ) (s k : ℕ) : ℝ :=
  finiteEntropy Finset.univ (fun x : ZMod (2 ^ k) => ‖dyadicProductSumLaw A B C s k x‖)

theorem dyadic_product_sum_law_probability {A B C : Finset ℕ}
    (hA : A.Nonempty) (hB : B.Nonempty) (hC : C.Nonempty) (s k : ℕ) :
    FiniteComplexProbability (dyadicProductSumLaw A B C s k) :=
  cyclicConvolutionPow_probability (cyclicAffineProductLaw_probability hA hB hC 0 1) s

theorem dyadic_product_sum_law_project (A B C : Finset ℕ) (s : ℕ) {u v : ℕ} (huv : u ≤ v) :
    cyclicPushforward (dyadicProductSumLaw A B C s v)
      (ZMod.castHom (pow_dvd_pow 2 huv) (ZMod (2 ^ u))) = dyadicProductSumLaw A B C s u := by
  unfold dyadicProductSumLaw
  have hh := cyclicPushforward_convolutionPow (cyclicAffineProductLaw A B C 0 1)
    (ZMod.castHom (pow_dvd_pow 2 huv) (ZMod (2 ^ u))).toAddMonoidHom s
  change cyclicPushforward (cyclicConvolutionPow (cyclicAffineProductLaw A B C 0 1) s)
    (ZMod.castHom (pow_dvd_pow 2 huv) (ZMod (2 ^ u))) =
      cyclicConvolutionPow (cyclicPushforward (cyclicAffineProductLaw A B C 0 1)
        (ZMod.castHom (pow_dvd_pow 2 huv) (ZMod (2 ^ u)))) s at hh
  rw [cyclicPushforward_cyclicAffineProductLaw] at hh
  exact hh

theorem dyadic_product_sum_mass_project {A B C : Finset ℕ}
    (hA : A.Nonempty) (hB : B.Nonempty) (hC : C.Nonempty) (s : ℕ) {u v : ℕ} (huv : u ≤ v) :
    finitePushforward (fun x : ZMod (2 ^ v) => ‖dyadicProductSumLaw A B C s v x‖)
      (ZMod.castHom (pow_dvd_pow 2 huv) (ZMod (2 ^ u))) =
        (fun x : ZMod (2 ^ u) => ‖dyadicProductSumLaw A B C s u x‖) := by
  funext x
  rw [← norm_cyclicPushforward_of_probability (dyadic_product_sum_law_probability hA hB hC s v),
    dyadic_product_sum_law_project A B C s huv]

theorem dyadic_product_sum_entropy_mono {A B C : Finset ℕ}
    (hA : A.Nonempty) (hB : B.Nonempty) (hC : C.Nonempty) (s : ℕ) :
    Monotone (dyadicProductSumEntropy A B C s) := by
  intro u v huv
  have hh := finite_entropy_mono_projection (fun x : ZMod (2 ^ v) => ‖dyadicProductSumLaw A B C s v x‖)
    (ZMod.castHom (pow_dvd_pow 2 huv) (ZMod (2 ^ u))) (fun _ => norm_nonneg _)
  rw [dyadic_product_sum_mass_project hA hB hC s huv] at hh
  exact hh

theorem dyadic_product_sum_entropy_zero {A B C : Finset ℕ}
    (hA : A.Nonempty) (hB : B.Nonempty) (hC : C.Nonempty) (s : ℕ) :
    dyadicProductSumEntropy A B C s 0 = 0 := by
  have hz : ∀ x : ZMod (2 ^ 0), x = 0 := by
    have : Subsingleton (ZMod (2 ^ 0)) := ZMod.subsingleton_iff.mpr (by norm_num)
    exact fun x => Subsingleton.elim x 0
  have hmass := finite_complex_probability_sum_norm (dyadic_product_sum_law_probability hA hB hC s 0)
  have hvalue : ‖dyadicProductSumLaw A B C s 0 0‖ = 1 := by
    have hu : (Finset.univ : Finset (ZMod (2 ^ 0))) = {0} := by
      ext x
      simp only [Finset.mem_univ, Finset.mem_singleton, hz x]
    rw [hu, Finset.sum_singleton] at hmass
    exact hmass
  unfold dyadicProductSumEntropy finiteEntropy
  apply Finset.sum_eq_zero
  intro x hx
  change Real.negMulLog (‖dyadicProductSumLaw A B C s 0 x‖) = 0
  rw [hz x, hvalue]
  simp [Real.negMulLog_def]

theorem dyadic_product_sum_entropy_interval_gain {A B C : Finset ℕ}
    (hA : A.Nonempty) (hB : B.Nonempty) (hC : C.Nonempty) (s u L : ℕ)
    (M : ZMod (2 ^ u) → ℝ) (hM : ∀ a, 0 ≤ M a)
    (hbound : ∀ x : ZMod (2 ^ (u + L)), ‖dyadicProductSumLaw A B C s (u + L) x‖ ≤
      M ((ZMod.castHom (pow_dvd_pow 2 (show u ≤ u + L by omega)) (ZMod (2 ^ u))) x))
    (hpeak : (2 : ℝ) ^ L * (∑ a : ZMod (2 ^ u), M a) ≤ 2) :
    dyadicProductSumEntropy A B C s u + (L : ℝ) * Real.log 2 - 1 ≤
      dyadicProductSumEntropy A B C s (u + L) := by
  have hh := finite_entropy_projection_gain
    (fun x : ZMod (2 ^ (u + L)) => ‖dyadicProductSumLaw A B C s (u + L) x‖)
    (ZMod.castHom (pow_dvd_pow 2 (show u ≤ u + L by omega)) (ZMod (2 ^ u))) M
    (fun _ => norm_nonneg _) (finite_complex_probability_sum_norm
      (dyadic_product_sum_law_probability hA hB hC s (u + L)))
    (show (0 : ℝ) < (2 : ℝ) ^ L by positivity) hM hbound
    (show (2 : ℝ) ^ L * (∑ a : ZMod (2 ^ u), M a) ≤ (1 : ℝ) + 1 by linarith)
  rw [dyadic_product_sum_mass_project hA hB hC s (show u ≤ u + L by omega), Real.log_pow] at hh
  exact hh

theorem exists_dyadic_set_product_entropy_gain {g ρ β : ℝ}
    (hg : 0 < g) (hρ : 3 * ρ < g) (hβ : 0 < β) (hβ1 : β ≤ 1) (M₀ : ℕ) :
    ∃ S s : ℕ, M₀ ≤ S ∧ 0 < S ∧ 0 < s ∧ ∀ u L : ℕ, ∀ A B : Finset ℕ,
      A.Nonempty → B.Nonempty → (∀ n ∈ B, Odd n) →
      (∀ r ∈ dyadicProjection A u, ∃ a b : ℕ, a % 2 ≠ b % 2 ∧
        β ≤ natResidueMass (dyadicZoom A u r) 2 a ∧ β ≤ natResidueMass (dyadicZoom A u r) 2 b) →
      (∀ r ∈ dyadicProjection A u, ∀ l : ℕ, S < l → l ≤ L → ∀ x : ZMod (2 ^ l),
        ‖cyclicUniformNatSet (dyadicZoom A u r) x‖ ≤ (2 : ℝ) ^ (-(1 - 3 * ρ) * (l : ℝ))) →
      (∀ l : ℕ, S < l → l ≤ L → ∀ x : ZMod (2 ^ l),
        ‖cyclicUniformNatSet B x‖ ≤ (2 : ℝ) ^ (-(2 * g) * (l : ℝ))) →
      dyadicProductSumEntropy A B (Finset.Ioc 0 (2 ^ S)) (2 * s) u + (L : ℝ) * Real.log 2 - 1 ≤
        dyadicProductSumEntropy A B (Finset.Ioc 0 (2 ^ S)) (2 * s) (u + L) := by
  obtain ⟨S, s, hMS, hS, hs, hpeak⟩ := exists_dyadic_set_product_peak hg hρ hβ hβ1 M₀
  refine ⟨S, s, hMS, hS, hs, ?_⟩
  intro u L A B hA hB hBodd hsplit hAmass hBmass
  obtain ⟨M, hM, hbound, hsum⟩ := hpeak u L A B hA hB hBodd hsplit hAmass hBmass
  exact dyadic_product_sum_entropy_interval_gain hA hB (Finset.nonempty_Ioc.mpr (by positivity))
    (2 * s) u L M hM hbound hsum.le

theorem cyclicUniformNatSet_bounded_apply {q : ℕ} [NeZero q] (A : Finset ℕ)
    (hA : ∀ n ∈ A, n < q) (x : ZMod q) :
    cyclicUniformNatSet A x = if x.val ∈ A then (A.card : ℂ)⁻¹ else 0 := by
  classical
  unfold cyclicUniformNatSet cyclicPushforward
  rw [Finset.sum_coe_sort A (fun n => if (n : ZMod q) = x then (A.card : ℂ)⁻¹ else 0)]
  have hsum : (∑ n ∈ A, if (n : ZMod q) = x then (A.card : ℂ)⁻¹ else 0) =
      ∑ n ∈ A, if n = x.val then (A.card : ℂ)⁻¹ else 0 := by
    apply Finset.sum_congr rfl
    intro n hn
    have heq : (n : ZMod q) = x ↔ n = x.val := by
      constructor
      · intro h
        have hh := congrArg ZMod.val h
        simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt (hA n hn)] using hh
      · intro h
        rw [h, ZMod.natCast_zmod_val]
    by_cases h : n = x.val
    · simp only [if_pos h, if_pos (heq.mpr h)]
    · simp only [if_neg h, if_neg (fun hc => h (heq.mp hc))]
  rw [hsum]
  simp

theorem cyclicUniformNatSet_regular_projection {A : Finset ℕ} {T N i : ℕ}
    (htree : DyadicRegularTree A T N) (hbound : ∀ x ∈ A, x < 2 ^ (T * N)) (hi : i ≤ N) :
    cyclicUniformNatSet (q := 2 ^ (T * i)) A = cyclicUniformNatSet (dyadicProjection A (T * i)) := by
  funext x
  rw [cyclicUniformNatSet_bounded_apply _ (dyadic_projection_bounded A (T * i))]
  by_cases hx : x.val ∈ dyadicProjection A (T * i)
  · rw [if_pos hx, cyclicUniformNatSet_eq_residue_mass, dyadic_regular_tree_residue_mass htree hbound hi hx]
    simp only [one_div, Complex.ofReal_inv, Complex.ofReal_natCast]
  · rw [if_neg hx]
    by_contra hn
    obtain ⟨n, hnA, hnx⟩ := cyclicUniformNatSet_support A hn
    apply hx
    have hh := congrArg ZMod.val hnx
    exact Finset.mem_image.mpr ⟨n, hnA, by simpa only [ZMod.val_natCast] using hh⟩

theorem cyclicUniformNatSet_congr_reduction {Q q : ℕ} [NeZero Q] [NeZero q]
    (π : ZMod Q →+* ZMod q) {A A' : Finset ℕ}
    (hA : cyclicUniformNatSet (q := Q) A = cyclicUniformNatSet A') :
    cyclicUniformNatSet (q := q) A = cyclicUniformNatSet A' := by
  have hh := congrArg (fun f : ZMod Q → ℂ => cyclicPushforward f π) hA
  simpa only [cyclicPushforward_cyclicUniformNatSet] using hh

theorem cyclicUniformNatSet_regular_projection_lower {A : Finset ℕ} {T N i k : ℕ}
    (htree : DyadicRegularTree A T N) (hbound : ∀ x ∈ A, x < 2 ^ (T * N))
    (hi : i ≤ N) (hk : k ≤ T * i) :
    cyclicUniformNatSet (q := 2 ^ k) A = cyclicUniformNatSet (dyadicProjection A (T * i)) := by
  exact cyclicUniformNatSet_congr_reduction (ZMod.castHom (pow_dvd_pow 2 hk) (ZMod (2 ^ k)))
    (cyclicUniformNatSet_regular_projection htree hbound hi)

theorem cyclicAffineNatSet_eq_mul_pushforward {q : ℕ} [NeZero q] (A : Finset ℕ) (z : ℕ) :
    cyclicAffineNatSet (q := q) A 0 1 z =
      cyclicPushforward (cyclicUniformNatSet A) (fun x : ZMod q => x * (z : ZMod q)) := by
  unfold cyclicAffineNatSet cyclicUniformNatSet
  rw [cyclicPushforward_comp]
  congr 1
  funext n
  simp only [Function.comp_apply, one_mul, zero_add, Nat.cast_mul]

theorem cyclicAffineProductLaw_congr_input {q : ℕ} [NeZero q] {A A' : Finset ℕ}
    (hA : cyclicUniformNatSet (q := q) A = cyclicUniformNatSet A') (B C : Finset ℕ) :
    cyclicAffineProductLaw (q := q) A B C 0 1 = cyclicAffineProductLaw A' B C 0 1 := by
  funext x
  unfold cyclicAffineProductLaw cyclicMixture
  apply Finset.sum_congr rfl
  intro i hi
  dsimp only
  rw [cyclicAffineNatSet_eq_mul_pushforward, cyclicAffineNatSet_eq_mul_pushforward, hA]

theorem dyadic_product_sum_entropy_congr_input {A A' : Finset ℕ} {k : ℕ}
    (hA : cyclicUniformNatSet (q := 2 ^ k) A = cyclicUniformNatSet A') (B C : Finset ℕ) (s : ℕ) :
    dyadicProductSumEntropy A B C s k = dyadicProductSumEntropy A' B C s k := by
  unfold dyadicProductSumEntropy dyadicProductSumLaw
  rw [cyclicAffineProductLaw_congr_input hA B C]

theorem exists_regular_tree_product_entropy_step (T M₀ : ℕ) {g ρ : ℝ}
    (hg : 0 < g) (hρ : 3 * ρ < g) :
    ∃ S s : ℕ, M₀ ≤ S ∧ 0 < S ∧ 0 < s ∧
      ∀ (N : ℕ) (A B : Finset ℕ) (m c : ℕ → ℕ) (a b e : ℕ),
      A.Nonempty → B.Nonempty → (∀ x ∈ A, x < 2 ^ (T * N)) → (∀ n ∈ B, Odd n) →
      (∀ i : ℕ, i < N → DyadicTreeBlock (dyadicProjection A (T * (i + 1))) (T * i) T (m i) (c i)) →
      (∀ j : ℕ, j ≤ N → (dyadicProjection A (T * j)).card = 2 ^ branchPrefix c j) →
      a < b → b ≤ N → 0 < c a → DyadicAmplificationBlock A (m a) (T * b) M₀ e ρ →
      (∀ l : ℕ, S < l → l ≤ T * N → ∀ x : ZMod (2 ^ l),
        ‖cyclicUniformNatSet B x‖ ≤ (2 : ℝ) ^ (-(2 * g) * (l : ℝ))) →
      dyadicProductSumEntropy A B (Finset.Ioc 0 (2 ^ S)) (2 * s) (m a) +
        ((T * b - m a : ℕ) : ℝ) * Real.log 2 - 1 ≤
          dyadicProductSumEntropy A B (Finset.Ioc 0 (2 ^ S)) (2 * s) (T * b) := by
  have hβ : (0 : ℝ) < (2 : ℝ) ^ (-(T : ℝ)) := by positivity
  have hβ1 : (2 : ℝ) ^ (-(T : ℝ)) ≤ 1 := by
    calc
      _ ≤ (2 : ℝ) ^ (0 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (neg_nonpos.mpr (Nat.cast_nonneg T))
      _ = _ := by rw [Real.rpow_zero]
  obtain ⟨S, s, hMS, hS, hs, hstep⟩ := exists_dyadic_set_product_entropy_gain hg hρ hβ hβ1 M₀
  refine ⟨S, s, hMS, hS, hs, ?_⟩
  intro N A B m c a b e hA hB hbound hBodd hblocks hprofile hab hbN hca hblock hBmass
  have huv : m a ≤ T * b := hblock.start_lt.le
  have hwidth : m a + (T * b - m a) = T * b := Nat.add_sub_of_le huv
  have htree : DyadicRegularTree A T N := fun i hi => ⟨m i, c i, hblocks i hi⟩
  have hlocal := hstep (m a) (T * b - m a) (dyadicProjection A (T * b)) B (hA.image _) hB hBodd
    (fun r hr => dyadic_regular_profile_zoom_split_mass hblocks hprofile hab hbN hca
      (by simpa only [dyadic_projection_trans A huv] using hr))
    (fun r hr l hl hlL x => by
      rw [norm_cyclicUniformNatSet]
      exact dyadic_amplification_block_zoom_mass hblock
        (by simpa only [dyadic_projection_trans A huv] using hr) (by omega) (by omega) x.val)
    (fun l hl hlL => hBmass l hl (by
      have hh := Nat.mul_le_mul_left T hbN
      omega))
  rw [hwidth] at hlocal
  have hlow := dyadic_product_sum_entropy_congr_input
    (cyclicUniformNatSet_regular_projection_lower htree hbound hbN huv) B (Finset.Ioc 0 (2 ^ S)) (2 * s)
  have hhigh := dyadic_product_sum_entropy_congr_input
    (cyclicUniformNatSet_regular_projection htree hbound hbN) B (Finset.Ioc 0 (2 ^ S)) (2 * s)
  rw [← hlow, ← hhigh] at hlocal
  exact hlocal

theorem exists_regular_tree_product_entropy_amplification (T R M₀ : ℕ) (hR : 0 < R) {g ρ : ℝ}
    (hg : 0 < g) (hρ : 0 ≤ ρ) (hρg : 3 * ρ < g) :
    ∃ S s : ℕ, M₀ ≤ S ∧ 0 < S ∧ 0 < s ∧
      ∀ (N : ℕ) (A B : Finset ℕ) (m c : ℕ → ℕ) (L : List (ℕ × ℕ)) (w : ℕ) (B₀ : ℝ),
      A.Nonempty → B.Nonempty → (∀ x ∈ A, x < 2 ^ (T * N)) → (∀ n ∈ B, Odd n) →
      (∀ i : ℕ, i < N → DyadicTreeBlock (dyadicProjection A (T * (i + 1))) (T * i) T (m i) (c i)) →
      (∀ j : ℕ, j ≤ N → (dyadicProjection A (T * j)).card = 2 ^ branchPrefix c j) →
      BranchingIntervalChain c T N R (1 - 2 * ρ) 0 L w →
      (∀ p ∈ L, DyadicAmplificationBlock A (m p.1) (T * p.2) M₀
        (branchPrefix c p.2 - branchPrefix c p.1) ρ) →
      (∀ l : ℕ, S < l → l ≤ T * N → ∀ x : ZMod (2 ^ l),
        ‖cyclicUniformNatSet B x‖ ≤ (2 : ℝ) ^ (-(2 * g) * (l : ℝ))) →
      B₀ ≤ ((L.map (fun p => branchPrefix c p.2 - branchPrefix c p.1)).sum : ℝ) →
      (L.length : ℝ) ≤ ρ / 2 * B₀ * Real.log 2 →
      (branchPrefix c w : ℝ) * Real.log 2 + ρ / 2 * B₀ * Real.log 2 ≤
        dyadicProductSumEntropy A B (Finset.Ioc 0 (2 ^ S)) (2 * s) (T * w) := by
  obtain ⟨S, s, hMS, hS, hs, hstep⟩ := exists_regular_tree_product_entropy_step T M₀ hg hρg
  refine ⟨S, s, hMS, hS, hs, ?_⟩
  intro N A B m c L w B₀ hA hB hbound hBodd hblocks hprofile hchain hselected hBmass hbits hloss
  have hC : (Finset.Ioc 0 (2 ^ S)).Nonempty := Finset.nonempty_Ioc.mpr (by positivity)
  have hlocal : ∀ p ∈ L,
      dyadicProductSumEntropy A B (Finset.Ioc 0 (2 ^ S)) (2 * s) (m p.1) +
        ((T * p.2 - m p.1 : ℕ) : ℝ) * Real.log 2 - 1 ≤
          dyadicProductSumEntropy A B (Finset.Ioc 0 (2 ^ S)) (2 * s) (T * p.2) := by
    intro p hp
    have hinterval := (branching_interval_chain_mem hchain p hp).2.2
    have hab : p.1 < p.2 := by have := hinterval.width; omega
    exact hstep N A B m c p.1 p.2 (branchPrefix c p.2 - branchPrefix c p.1)
      hA hB hbound hBodd hblocks hprofile hab hinterval.end_le hinterval.branching (hselected p hp) hBmass
  exact branching_interval_chain_entropy_amplification (C := 1)
    (dyadicProductSumEntropy A B (Finset.Ioc 0 (2 ^ S)) (2 * s)) hchain hR hρ
    (dyadic_product_sum_entropy_mono hA hB hC (2 * s)) (dyadic_product_sum_entropy_zero hA hB hC (2 * s))
    (fun i hi => (hblocks i hi).base_le) hselected hlocal hbits (by simpa only [one_mul] using hloss)

theorem nat_residue_mass_subset_le {D A : Finset ℕ} (hDA : D ⊆ A) (hD : D.Nonempty)
    {K : ℝ} (hsize : (A.card : ℝ) ≤ K * (D.card : ℝ)) (q r : ℕ) :
    natResidueMass D q r ≤ K * natResidueMass A q r := by
  have hA : A.Nonempty := hD.mono hDA
  have hDc : (0 : ℝ) < D.card := by exact_mod_cast Finset.card_pos.mpr hD
  have hAc : (0 : ℝ) < A.card := by exact_mod_cast Finset.card_pos.mpr hA
  have hsub : natResidueFiber D q r ⊆ natResidueFiber A q r := by
    intro n hn
    exact Finset.mem_filter.mpr ⟨hDA (Finset.mem_filter.mp hn).1, (Finset.mem_filter.mp hn).2⟩
  have hcard : ((natResidueFiber D q r).card : ℝ) ≤ (natResidueFiber A q r).card := by
    exact_mod_cast Finset.card_le_card hsub
  unfold natResidueMass
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ hDc hAc).mpr
  calc
    _ ≤ ((natResidueFiber A q r).card : ℝ) * (A.card : ℝ) := mul_le_mul_of_nonneg_right hcard hAc.le
    _ ≤ ((natResidueFiber A q r).card : ℝ) * (K * (D.card : ℝ)) :=
      mul_le_mul_of_nonneg_left hsize (Nat.cast_nonneg _)
    _ = _ := by ring

theorem exists_large_odd_translated_subset {A : Finset ℕ} (hA : A.Nonempty) :
    ∃ D : Finset ℕ, ∃ δ : ℕ, D ⊆ A ∧ D.Nonempty ∧ δ ≤ 1 ∧
      A.card ≤ 2 * D.card ∧ ∀ n ∈ D, Odd (n + δ) := by
  classical
  have hcard := Finset.card_filter_add_card_filter_not (s := A) (fun n : ℕ => Even n)
  have hApos := Finset.card_pos.mpr hA
  by_cases heven : A.card ≤ 2 * (A.filter (fun n => Even n)).card
  · refine ⟨A.filter (fun n => Even n), 1, Finset.filter_subset _ _, ?_, le_rfl, heven, ?_⟩
    · exact Finset.card_pos.mp (by omega)
    · intro n hn
      have hn0 := Nat.mod_eq_zero_of_dvd (Finset.mem_filter.mp hn).2.two_dvd
      exact Nat.odd_iff.mpr (by omega)
  · refine ⟨A.filter (fun n => ¬Even n), 0, Finset.filter_subset _ _, ?_, by omega, by omega, ?_⟩
    · exact Finset.card_pos.mp (by omega)
    · intro n hn
      simpa only [Nat.add_zero] using Nat.not_even_iff_odd.mp (Finset.mem_filter.mp hn).2

theorem norm_cyclicUniformNatSet_translate_subset_le {q : ℕ} [NeZero q] {D A : Finset ℕ}
    (hDA : D ⊆ A) (hD : D.Nonempty) (hsize : A.card ≤ 2 * D.card) (δ : ℕ)
    {M : ℝ} (hM : ∀ x : ZMod q, ‖cyclicUniformNatSet A x‖ ≤ M) (x : ZMod q) :
    ‖cyclicUniformNatSet (natTranslate D δ) x‖ ≤ 2 * M := by
  rw [norm_cyclicUniformNatSet, nat_translate_residue_mass]
  have hh := nat_residue_mass_subset_le hDA hD
    (show (A.card : ℝ) ≤ (2 : ℝ) * (D.card : ℝ) by exact_mod_cast hsize)
    q ((x.val : ZMod q) - (δ : ZMod q)).val
  rw [← norm_cyclicUniformNatSet A ((x.val : ZMod q) - (δ : ZMod q))] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (hM _) (by norm_num))

theorem two_mul_dyadic_decay_le {a b : ℝ} {l : ℕ}
    (hmargin : 1 ≤ (a - b) * (l : ℝ)) :
    2 * (2 : ℝ) ^ (-a * (l : ℝ)) ≤ (2 : ℝ) ^ (-b * (l : ℝ)) := by
  calc
    _ = (2 : ℝ) ^ ((1 : ℝ) + (-a * (l : ℝ))) := by
      rw [Real.rpow_add (by norm_num), Real.rpow_one]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)

theorem odd_translated_subset_dyadic_mass {D A : Finset ℕ} (hDA : D ⊆ A)
    (hD : D.Nonempty) (hsize : A.card ≤ 2 * D.card) (δ : ℕ) {a b : ℝ} {l : ℕ}
    (hmargin : 1 ≤ (a - b) * (l : ℝ))
    (hA : ∀ x : ZMod (2 ^ l), ‖cyclicUniformNatSet A x‖ ≤ (2 : ℝ) ^ (-a * (l : ℝ))) :
    ∀ x : ZMod (2 ^ l), ‖cyclicUniformNatSet (natTranslate D δ) x‖ ≤ (2 : ℝ) ^ (-b * (l : ℝ)) := by
  intro x
  exact (norm_cyclicUniformNatSet_translate_subset_le hDA hD hsize δ hA x).trans
    (two_mul_dyadic_decay_le hmargin)

def natTripleProductSet (A B C : Finset ℕ) : Finset ℕ :=
  ((A ×ˢ B) ×ˢ C).image (fun p => p.1.1 * p.1.2 * p.2)

def natProductSumSet (A B C : Finset ℕ) : ℕ → Finset ℕ
  | 0 => {0}
  | s + 1 => (natTripleProductSet A B C ×ˢ natProductSumSet A B C s).image (fun p => p.1 + p.2)

theorem nat_triple_product_set_nonempty {A B C : Finset ℕ}
    (hA : A.Nonempty) (hB : B.Nonempty) (hC : C.Nonempty) : (natTripleProductSet A B C).Nonempty :=
  ((hA.product hB).product hC).image _

theorem nat_product_sum_set_nonempty {A B C : Finset ℕ}
    (hA : A.Nonempty) (hB : B.Nonempty) (hC : C.Nonempty) (s : ℕ) :
    (natProductSumSet A B C s).Nonempty := by
  induction s with
  | zero => exact Finset.singleton_nonempty 0
  | succ s ih => exact ((nat_triple_product_set_nonempty hA hB hC).product ih).image _

theorem cyclicAffineProductLaw_support {q : ℕ} [NeZero q] (A B C : Finset ℕ)
    {x : ZMod q} (hx : cyclicAffineProductLaw A B C 0 1 x ≠ 0) :
    ∃ n ∈ natTripleProductSet A B C, (n : ZMod q) = x := by
  classical
  obtain ⟨i, hi, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
  have hF : cyclicAffineNatSet A 0 1 (i.1.val * i.2.val) x ≠ 0 := (mul_ne_zero_iff.mp hterm).2
  obtain ⟨n, hnx, hnw⟩ := cyclicPushforward_support (fun _ : A => (A.card : ℂ)⁻¹)
    (fun n : A => (((0 + 1 * n.val) * (i.1.val * i.2.val) : ℕ) : ZMod q)) hF
  refine ⟨n.val * i.1.val * i.2.val, ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨((n.val, i.1.val), i.2.val),
      Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨n.property, i.1.property⟩, i.2.property⟩, rfl⟩
  · simpa only [one_mul, zero_add, mul_assoc] using hnx

theorem dyadic_product_sum_law_support (A B C : Finset ℕ) (s k : ℕ)
    {x : ZMod (2 ^ k)} (hx : dyadicProductSumLaw A B C s k x ≠ 0) :
    ∃ n ∈ natProductSumSet A B C s, (n : ZMod (2 ^ k)) = x := by
  classical
  induction s generalizing x with
  | zero =>
    have hx0 : x = 0 := by
      by_contra h
      exact hx (by simp [dyadicProductSumLaw, cyclicConvolutionPow, h])
    exact ⟨0, Finset.mem_singleton_self _, by simpa only [Nat.cast_zero] using hx0.symm⟩
  | succ s ih =>
    change (∑ y : ZMod (2 ^ k), cyclicAffineProductLaw A B C 0 1 y *
      dyadicProductSumLaw A B C s k (x - y)) ≠ 0 at hx
    obtain ⟨y, hy, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
    obtain ⟨hfy, hgy⟩ := mul_ne_zero_iff.mp hterm
    obtain ⟨a, ha, hay⟩ := cyclicAffineProductLaw_support A B C hfy
    obtain ⟨b, hb, hbx⟩ := ih hgy
    refine ⟨a + b, Finset.mem_image.mpr ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, rfl⟩, ?_⟩
    rw [Nat.cast_add, hay, hbx]
    abel

theorem dyadic_product_sum_entropy_le_log_card {A B C : Finset ℕ}
    (hA : A.Nonempty) (hB : B.Nonempty) (hC : C.Nonempty) (s k : ℕ) :
    dyadicProductSumEntropy A B C s k ≤
      Real.log ((dyadicProjection (natProductSumSet A B C s) k).card : ℝ) := by
  classical
  let S : Finset (ZMod (2 ^ k)) := (natProductSumSet A B C s).image (fun n : ℕ => (n : ZMod (2 ^ k)))
  have hzero : ∀ x : ZMod (2 ^ k), x ∉ S → ‖dyadicProductSumLaw A B C s k x‖ = 0 := by
    intro x hx
    apply norm_eq_zero.mpr
    by_contra hn
    obtain ⟨n, hnS, hnx⟩ := dyadic_product_sum_law_support A B C s k hn
    exact hx (Finset.mem_image.mpr ⟨n, hnS, hnx⟩)
  have hh := finite_entropy_le_log_support (fun x : ZMod (2 ^ k) => ‖dyadicProductSumLaw A B C s k x‖)
    S (fun _ => norm_nonneg _) (finite_complex_probability_sum_norm
      (dyadic_product_sum_law_probability hA hB hC s k)) hzero
  have himage : S.image ZMod.val = dyadicProjection (natProductSumSet A B C s) k := by
    simp only [S, Finset.image_image, Function.comp_def, ZMod.val_natCast, dyadicProjection]
  have hcard : S.card = (dyadicProjection (natProductSumSet A B C s) k).card := by
    rw [← himage, Finset.card_image_of_injective _ (ZMod.val_injective _)]
  rw [hcard] at hh
  exact hh

theorem exists_regular_tree_product_growth (T R : ℕ) {γ δ ρ g : ℝ}
    (hT : 0 < T) (hR : 0 < R) (hγ : 0 < γ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hρ : 0 < ρ) (hρδ : ρ ≤ δ / 4) (hρR : 1 ≤ ρ * (R : ℝ))
    (hg : 0 < g) (hρg : 3 * ρ < g)
    (hbudget : 1 ≤ (ρ / 2 * (γ * δ / 2 * (T : ℝ)) * Real.log 2) * (R : ℝ)) :
    ∃ S s : ℕ, 2 * (T * R) ≤ S ∧ 0 < S ∧ 0 < s ∧ ∀ (N : ℕ) (A B : Finset ℕ),
      A.Nonempty → B.Nonempty → (∀ n ∈ B, Odd n) →
      DyadicRegularTree A T N → (∀ x ∈ A, x < 2 ^ (T * N)) →
      (∀ j : ℕ, j ≤ N → (2 : ℝ) ^ (γ * (T : ℝ) * (j : ℝ)) ≤
        ((dyadicProjection A (T * j)).card : ℝ)) →
      (A.card : ℝ) ≤ (2 : ℝ) ^ ((1 - δ) * (T : ℝ) * (N : ℝ)) →
      2 * (R : ℝ) ≤ γ * (N : ℝ) →
      (∀ l : ℕ, S < l → l ≤ T * N → ∀ x : ZMod (2 ^ l),
        ‖cyclicUniformNatSet B x‖ ≤ (2 : ℝ) ^ (-(2 * g) * (l : ℝ))) →
      ∃ w : ℕ, w ≤ N ∧
        Real.log ((dyadicProjection A (T * w)).card : ℝ) +
          ρ / 2 * (γ * δ / 2 * (T : ℝ) * (N : ℝ)) * Real.log 2 ≤
            Real.log ((dyadicProjection (natProductSumSet A B (Finset.Ioc 0 (2 ^ S)) (2 * s)) (T * w)).card : ℝ) := by
  obtain ⟨S, s, hMS, hS, hs, hamp⟩ := exists_regular_tree_product_entropy_amplification
    T R (2 * (T * R)) hR hg hρ.le hρg
  refine ⟨S, s, hMS, hS, hs, ?_⟩
  intro N A B hA hB hBodd htree hbound hprefix hsize hRN hBmass
  obtain ⟨m, c, L, w, hblocks, hprofile, hwN, hchain, hlength, hbits, hselected⟩ :=
    exists_dyadic_amplification_intervals hA hT hR hγ hδ hδ1 hρ hρδ hρR htree hbound hprefix hsize hRN
  have hlengthR : (L.length : ℝ) * (R : ℝ) ≤ N := by exact_mod_cast hlength
  have hcoef : 0 ≤ ρ / 2 * (γ * δ / 2 * (T : ℝ)) * Real.log 2 := by
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  have hloss : (L.length : ℝ) ≤ ρ / 2 * (γ * δ / 2 * (T : ℝ) * (N : ℝ)) * Real.log 2 := by
    calc
      _ = (L.length : ℝ) * 1 := (mul_one _).symm
      _ ≤ (L.length : ℝ) * ((ρ / 2 * (γ * δ / 2 * (T : ℝ)) * Real.log 2) * (R : ℝ)) :=
        mul_le_mul_of_nonneg_left hbudget (Nat.cast_nonneg _)
      _ = (ρ / 2 * (γ * δ / 2 * (T : ℝ)) * Real.log 2) * ((L.length : ℝ) * (R : ℝ)) := by ring
      _ ≤ (ρ / 2 * (γ * δ / 2 * (T : ℝ)) * Real.log 2) * (N : ℝ) :=
        mul_le_mul_of_nonneg_left hlengthR hcoef
      _ = _ := by ring
  have hgain := hamp N A B m c L w (γ * δ / 2 * (T : ℝ) * (N : ℝ))
    hA hB hbound hBodd hblocks hprofile hchain hselected hBmass hbits hloss
  have hlogP : Real.log ((dyadicProjection A (T * w)).card : ℝ) =
      (branchPrefix c w : ℝ) * Real.log 2 := by
    rw [hprofile w hwN, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  refine ⟨w, hwN, ?_⟩
  rw [hlogP]
  exact hgain.trans (dyadic_product_sum_entropy_le_log_card hA hB
    (Finset.nonempty_Ioc.mpr (by positivity)) (2 * s) (T * w))

theorem odd_translated_subset_regular_mass {T R N S l : ℕ} {γ ρ g : ℝ}
    (hT : 0 < T) (hR : 0 < R) (hg : 0 < g) (hγg : 8 * g ≤ γ)
    (hρg : 3 * ρ < g) (hρR : 1 ≤ ρ * (R : ℝ)) (hS : 2 * (T * R) ≤ S)
    {A D : Finset ℕ} (hDA : D ⊆ A) (hD : D.Nonempty) (hsize : A.card ≤ 2 * D.card) (τ : ℕ)
    (htree : DyadicRegularTree A T N) (hbound : ∀ x ∈ A, x < 2 ^ (T * N))
    (hprefix : ∀ j : ℕ, j ≤ N → (2 : ℝ) ^ (γ * (T : ℝ) * (j : ℝ)) ≤
      ((dyadicProjection A (T * j)).card : ℝ)) (hl : S < l) (hlN : l ≤ T * N) :
    ∀ x : ZMod (2 ^ l), ‖cyclicUniformNatSet (natTranslate D τ) x‖ ≤
      (2 : ℝ) ^ (-(2 * g) * (l : ℝ)) := by
  have hTR : T ≤ T * R := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left T (show 1 ≤ R by omega)
  have hRT : R ≤ T * R := by simpa only [Nat.one_mul] using Nat.mul_le_mul_right R (show 1 ≤ T by omega)
  have hmin : 2 * T ≤ l := by omega
  have hRl : (R : ℝ) ≤ l := by exact_mod_cast (show R ≤ l by omega)
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  have hgap : 0 ≤ γ / 2 - 2 * g := by linarith
  have hmarginR : 1 ≤ (γ / 2 - 2 * g) * (R : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hγg hRpos.le
    have hh' := mul_lt_mul_of_pos_right hρg hRpos
    nlinarith
  apply odd_translated_subset_dyadic_mass hDA hD hsize τ
    (hmarginR.trans (mul_le_mul_of_nonneg_left hRl hgap))
  intro x
  rw [norm_cyclicUniformNatSet]
  exact dyadic_regular_tree_mass_le_at_all_levels hT (by linarith : 0 ≤ γ)
    htree hbound hprefix hmin hlN x.val

theorem exists_regular_tree_translated_product_growth (T R : ℕ) {γ δ ρ g : ℝ}
    (hT : 0 < T) (hR : 0 < R) (hγ : 0 < γ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hρ : 0 < ρ) (hρδ : ρ ≤ δ / 4) (hρR : 1 ≤ ρ * (R : ℝ))
    (hg : 0 < g) (hγg : 8 * g ≤ γ) (hρg : 3 * ρ < g)
    (hbudget : 1 ≤ (ρ / 2 * (γ * δ / 2 * (T : ℝ)) * Real.log 2) * (R : ℝ)) :
    ∃ S s : ℕ, 2 * (T * R) ≤ S ∧ 0 < S ∧ 0 < s ∧ ∀ (N : ℕ) (A : Finset ℕ),
      A.Nonempty → DyadicRegularTree A T N → (∀ x ∈ A, x < 2 ^ (T * N)) →
      (∀ j : ℕ, j ≤ N → (2 : ℝ) ^ (γ * (T : ℝ) * (j : ℝ)) ≤
        ((dyadicProjection A (T * j)).card : ℝ)) →
      (A.card : ℝ) ≤ (2 : ℝ) ^ ((1 - δ) * (T : ℝ) * (N : ℝ)) →
      2 * (R : ℝ) ≤ γ * (N : ℝ) →
      ∃ D : Finset ℕ, ∃ τ w : ℕ, D ⊆ A ∧ D.Nonempty ∧ τ ≤ 1 ∧ A.card ≤ 2 * D.card ∧ w ≤ N ∧
        Real.log ((dyadicProjection A (T * w)).card : ℝ) +
          ρ / 2 * (γ * δ / 2 * (T : ℝ) * (N : ℝ)) * Real.log 2 ≤
            Real.log ((dyadicProjection
              (natProductSumSet A (natTranslate D τ) (Finset.Ioc 0 (2 ^ S)) (2 * s)) (T * w)).card : ℝ) := by
  obtain ⟨S, s, hMS, hS, hs, hgrowth⟩ := exists_regular_tree_product_growth T R
    hT hR hγ hδ hδ1 hρ hρδ hρR hg hρg hbudget
  refine ⟨S, s, hMS, hS, hs, ?_⟩
  intro N A hA htree hbound hprefix hsize hRN
  obtain ⟨D, τ, hDA, hD, hτ, hDsize, hDodd⟩ := exists_large_odd_translated_subset hA
  have hBodd : ∀ n ∈ natTranslate D τ, Odd n := by
    intro n hn
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hn
    exact hDodd d hd
  obtain ⟨w, hwN, hgain⟩ := hgrowth N A (natTranslate D τ) hA (nat_translate_nonempty hD τ)
    hBodd htree hbound hprefix hsize hRN
    (fun l hl hlN => odd_translated_subset_regular_mass hT hR hg hγg hρg hρR hMS
      hDA hD hDsize τ htree hbound hprefix hl hlN)
  exact ⟨D, τ, w, hDA, hD, hτ, hDsize, hwN, hgain⟩

def natBoundedSums (A : Finset ℕ) : ℕ → Finset ℕ
  | 0 => {0}
  | k + 1 => (insert 0 A ×ˢ natBoundedSums A k).image (fun p => p.1 + p.2)

def natLinearQuadraticSet (A : Finset ℕ) : Finset ℕ := A ∪ (A ×ˢ A).image (fun p => p.1 * p.2)

theorem zero_mem_nat_bounded_sums (A : Finset ℕ) (k : ℕ) : 0 ∈ natBoundedSums A k := by
  induction k with
  | zero => exact Finset.mem_singleton_self _
  | succ k ih =>
    exact Finset.mem_image.mpr ⟨(0, 0), Finset.mem_product.mpr ⟨Finset.mem_insert_self _ _, ih⟩, by simp⟩

theorem nat_bounded_sums_mono (A : Finset ℕ) : Monotone (natBoundedSums A) := by
  apply monotone_nat_of_le_succ
  intro k n hn
  exact Finset.mem_image.mpr ⟨(0, n), Finset.mem_product.mpr ⟨Finset.mem_insert_self _ _, hn⟩, by simp⟩

theorem mem_nat_bounded_sums_one {A : Finset ℕ} {n : ℕ} (hn : n ∈ A) : n ∈ natBoundedSums A 1 := by
  exact Finset.mem_image.mpr ⟨(n, 0), Finset.mem_product.mpr
    ⟨Finset.mem_insert_of_mem hn, Finset.mem_singleton_self _⟩, by simp⟩

theorem add_mem_nat_bounded_sums {A : Finset ℕ} {k l a b : ℕ}
    (ha : a ∈ natBoundedSums A k) (hb : b ∈ natBoundedSums A l) :
    a + b ∈ natBoundedSums A (k + l) := by
  induction k generalizing a with
  | zero =>
    have ha0 : a = 0 := Finset.mem_singleton.mp ha
    simpa only [ha0, Nat.zero_add] using hb
  | succ k ih =>
    obtain ⟨⟨x, y⟩, hxy, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp hxy
    have hi := ih hy
    have hkl : k + 1 + l = (k + l) + 1 := by omega
    rw [hkl]
    exact Finset.mem_image.mpr ⟨(x, y + b), Finset.mem_product.mpr ⟨hx, hi⟩, by simp [Nat.add_assoc]⟩

theorem mul_mem_nat_bounded_sums {A : Finset ℕ} {k a : ℕ}
    (ha : a ∈ natBoundedSums A k) (c : ℕ) : a * c ∈ natBoundedSums A (k * c) := by
  induction c with
  | zero => simpa only [Nat.mul_zero] using zero_mem_nat_bounded_sums A 0
  | succ c ih =>
    simpa only [Nat.mul_succ] using add_mem_nat_bounded_sums ih ha

theorem translated_product_mem_bounded_sums {A D : Finset ℕ} (hDA : D ⊆ A) {τ : ℕ} (hτ : τ ≤ 1)
    {a b c M : ℕ} (ha : a ∈ A) (hb : b ∈ natTranslate D τ) (hc : c ≤ M) :
    a * b * c ∈ natBoundedSums (natLinearQuadraticSet A) (2 * M) := by
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hb
  have had : a * d ∈ natBoundedSums (natLinearQuadraticSet A) 1 :=
    mem_nat_bounded_sums_one (Finset.mem_union_right A
      (Finset.mem_image.mpr ⟨(a, d), Finset.mem_product.mpr ⟨ha, hDA hd⟩, rfl⟩))
  have ha' : a ∈ natBoundedSums (natLinearQuadraticSet A) 1 :=
    mem_nat_bounded_sums_one (Finset.mem_union_left _ ha)
  have haτ : a * τ ∈ natBoundedSums (natLinearQuadraticSet A) 1 := by
    have hh := mul_mem_nat_bounded_sums ha' τ
    exact nat_bounded_sums_mono _ (by simpa only [Nat.one_mul] using hτ) hh
  have hbase : a * (d + τ) ∈ natBoundedSums (natLinearQuadraticSet A) 2 := by
    simpa only [Nat.mul_add] using add_mem_nat_bounded_sums had haτ
  exact nat_bounded_sums_mono _ (Nat.mul_le_mul_left 2 hc) (mul_mem_nat_bounded_sums hbase c)

theorem nat_product_sum_set_subset_bounded_sums (A B C E : Finset ℕ) (K : ℕ)
    (hproducts : natTripleProductSet A B C ⊆ natBoundedSums E K) (s : ℕ) :
    natProductSumSet A B C s ⊆ natBoundedSums E (K * s) := by
  induction s with
  | zero =>
    intro n hn
    have hn0 : n = 0 := Finset.mem_singleton.mp hn
    simpa only [hn0, Nat.mul_zero] using zero_mem_nat_bounded_sums E 0
  | succ s ih =>
    intro n hn
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
    have hh := add_mem_nat_bounded_sums (hproducts ha) (ih hb)
    have hindex : K * (s + 1) = K + K * s := by ring
    rw [hindex]
    exact hh

theorem translated_product_sum_subset_bounded_sums {A D : Finset ℕ}
    (hDA : D ⊆ A) {τ : ℕ} (hτ : τ ≤ 1) (M s : ℕ) :
    natProductSumSet A (natTranslate D τ) (Finset.Ioc 0 M) s ⊆
      natBoundedSums (natLinearQuadraticSet A) (2 * M * s) := by
  apply nat_product_sum_set_subset_bounded_sums
  intro n hn
  obtain ⟨⟨⟨a, b⟩, c⟩, habc, rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨hab, hc⟩ := Finset.mem_product.mp habc
  obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
  exact translated_product_mem_bounded_sums hDA hτ ha hb (Finset.mem_Ioc.mp hc).2

theorem log_gain_implies_dyadic_growth {x y t : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hgain : Real.log x + t * Real.log 2 ≤ Real.log y) : (2 : ℝ) ^ t * x ≤ y := by
  have hh := Real.exp_le_exp.mpr hgain
  rw [Real.exp_add, Real.exp_log hx, Real.exp_log hy] at hh
  calc
    _ = x * Real.exp (t * Real.log 2) := by
      rw [Real.rpow_def_of_pos (by norm_num), mul_comm t (Real.log 2)]
      ring
    _ ≤ _ := hh

theorem exists_regular_tree_bounded_sum_projected_growth (T R : ℕ) {γ δ ρ g : ℝ}
    (hT : 0 < T) (hR : 0 < R) (hγ : 0 < γ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hρ : 0 < ρ) (hρδ : ρ ≤ δ / 4) (hρR : 1 ≤ ρ * (R : ℝ))
    (hg : 0 < g) (hγg : 8 * g ≤ γ) (hρg : 3 * ρ < g)
    (hbudget : 1 ≤ (ρ / 2 * (γ * δ / 2 * (T : ℝ)) * Real.log 2) * (R : ℝ)) :
    ∃ K : ℕ, 0 < K ∧ ∀ (N : ℕ) (A : Finset ℕ),
      A.Nonempty → DyadicRegularTree A T N → (∀ x ∈ A, x < 2 ^ (T * N)) →
      (∀ j : ℕ, j ≤ N → (2 : ℝ) ^ (γ * (T : ℝ) * (j : ℝ)) ≤
        ((dyadicProjection A (T * j)).card : ℝ)) →
      (A.card : ℝ) ≤ (2 : ℝ) ^ ((1 - δ) * (T : ℝ) * (N : ℝ)) →
      2 * (R : ℝ) ≤ γ * (N : ℝ) →
      ∃ w : ℕ, w ≤ N ∧ (2 : ℝ) ^ (ρ / 2 * (γ * δ / 2 * (T : ℝ) * (N : ℝ))) *
        ((dyadicProjection A (T * w)).card : ℝ) ≤
          ((dyadicProjection (natBoundedSums (natLinearQuadraticSet A) K) (T * w)).card : ℝ) := by
  obtain ⟨S, s, hMS, hS, hs, hgrowth⟩ := exists_regular_tree_translated_product_growth T R
    hT hR hγ hδ hδ1 hρ hρδ hρR hg hγg hρg hbudget
  let K := 2 * 2 ^ S * (2 * s)
  refine ⟨K, by dsimp [K]; positivity, ?_⟩
  intro N A hA htree hbound hprefix hsize hRN
  obtain ⟨D, τ, w, hDA, hD, hτ, hDsize, hwN, hgain⟩ :=
    hgrowth N A hA htree hbound hprefix hsize hRN
  have hsub := translated_product_sum_subset_bounded_sums hDA hτ (2 ^ S) (2 * s)
  have hcard : ((dyadicProjection
      (natProductSumSet A (natTranslate D τ) (Finset.Ioc 0 (2 ^ S)) (2 * s)) (T * w)).card : ℝ) ≤
      ((dyadicProjection (natBoundedSums (natLinearQuadraticSet A) K) (T * w)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card (Finset.image_subset_image hsub)
  have hprod : (0 : ℝ) < (dyadicProjection
      (natProductSumSet A (natTranslate D τ) (Finset.Ioc 0 (2 ^ S)) (2 * s)) (T * w)).card := by
    exact_mod_cast Finset.card_pos.mpr ((nat_product_sum_set_nonempty hA (nat_translate_nonempty hD τ)
      (Finset.nonempty_Ioc.mpr (by positivity)) (2 * s)).image (fun n => n % 2 ^ (T * w)))
  have hAP : (0 : ℝ) < (dyadicProjection A (T * w)).card := by
    exact_mod_cast Finset.card_pos.mpr (hA.image (fun n => n % 2 ^ (T * w)))
  exact ⟨w, hwN, log_gain_implies_dyadic_growth hAP (hprod.trans_le hcard)
    (hgain.trans (Real.log_le_log hprod hcard))⟩

theorem regular_tree_bounded_sum_growth_of_projected {A : Finset ℕ} {T N w K : ℕ}
    (hA : A.Nonempty) (htree : DyadicRegularTree A T N) (hbound : ∀ x ∈ A, x < 2 ^ (T * N))
    (hwN : w ≤ N) (hK : 0 < K) {Λ : ℝ}
    (hprojected : Λ * ((dyadicProjection A (T * w)).card : ℝ) ≤
      ((dyadicProjection (natBoundedSums (natLinearQuadraticSet A) K) (T * w)).card : ℝ)) :
    Λ * (A.card : ℝ) ≤ ((dyadicProjection
      (natBoundedSums (natLinearQuadraticSet A) (2 * K)) (T * N)).card : ℝ) := by
  let G := natBoundedSums (natLinearQuadraticSet A) K
  have hAG : A ⊆ G := by
    intro a ha
    exact nat_bounded_sums_mono _ (show 1 ≤ K by omega)
      (mem_nat_bounded_sums_one (Finset.mem_union_left _ ha))
  have hraw := dyadic_regular_tree_modular_growth_bound hAG hA htree hbound hwN
  have hsub : ((G ×ˢ G).image (fun p => (p.1 + p.2) % 2 ^ (T * N))) ⊆
      dyadicProjection (natBoundedSums (natLinearQuadraticSet A) (2 * K)) (T * N) := by
    intro n hn
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
    refine Finset.mem_image.mpr ⟨a + b, ?_, rfl⟩
    simpa only [two_mul] using add_mem_nat_bounded_sums ha hb
  have hrawR : ((dyadicProjection G (T * w)).card : ℝ) * (A.card : ℝ) ≤
      ((dyadicProjection A (T * w)).card : ℝ) *
        ((dyadicProjection (natBoundedSums (natLinearQuadraticSet A) (2 * K)) (T * N)).card : ℝ) := by
    exact_mod_cast hraw.trans (Nat.mul_le_mul_left _ (Finset.card_le_card hsub))
  have hP : (0 : ℝ) < (dyadicProjection A (T * w)).card := by
    exact_mod_cast Finset.card_pos.mpr (hA.image (fun n => n % 2 ^ (T * w)))
  apply (mul_le_mul_iff_of_pos_left hP).mp
  calc
    _ = (Λ * ((dyadicProjection A (T * w)).card : ℝ)) * (A.card : ℝ) := by ring
    _ ≤ ((dyadicProjection G (T * w)).card : ℝ) * (A.card : ℝ) :=
      mul_le_mul_of_nonneg_right hprojected (Nat.cast_nonneg _)
    _ ≤ _ := hrawR

theorem exists_regular_tree_bounded_sum_growth (T R : ℕ) {γ δ ρ g : ℝ}
    (hT : 0 < T) (hR : 0 < R) (hγ : 0 < γ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hρ : 0 < ρ) (hρδ : ρ ≤ δ / 4) (hρR : 1 ≤ ρ * (R : ℝ))
    (hg : 0 < g) (hγg : 8 * g ≤ γ) (hρg : 3 * ρ < g)
    (hbudget : 1 ≤ (ρ / 2 * (γ * δ / 2 * (T : ℝ)) * Real.log 2) * (R : ℝ)) :
    ∃ K : ℕ, 0 < K ∧ ∀ (N : ℕ) (A : Finset ℕ),
      A.Nonempty → DyadicRegularTree A T N → (∀ x ∈ A, x < 2 ^ (T * N)) →
      (∀ j : ℕ, j ≤ N → (2 : ℝ) ^ (γ * (T : ℝ) * (j : ℝ)) ≤
        ((dyadicProjection A (T * j)).card : ℝ)) →
      (A.card : ℝ) ≤ (2 : ℝ) ^ ((1 - δ) * (T : ℝ) * (N : ℝ)) →
      2 * (R : ℝ) ≤ γ * (N : ℝ) →
      (2 : ℝ) ^ (ρ / 2 * (γ * δ / 2 * (T : ℝ) * (N : ℝ))) * (A.card : ℝ) ≤
        ((dyadicProjection (natBoundedSums (natLinearQuadraticSet A) K) (T * N)).card : ℝ) := by
  obtain ⟨K, hK, hgrowth⟩ := exists_regular_tree_bounded_sum_projected_growth T R
    hT hR hγ hδ hδ1 hρ hρδ hρR hg hγg hρg hbudget
  refine ⟨2 * K, by positivity, ?_⟩
  intro N A hA htree hbound hprefix hsize hRN
  obtain ⟨w, hwN, hprojected⟩ := hgrowth N A hA htree hbound hprefix hsize hRN
  exact regular_tree_bounded_sum_growth_of_projected hA htree hbound hwN hK hprojected

theorem exists_uniform_regular_tree_amplification {γ δ : ℝ}
    (hγ : 0 < γ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ η : ℝ, 0 < η ∧ ∀ T : ℕ, 0 < T → ∃ K N₀ : ℕ, 0 < K ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ A : Finset ℕ, A.Nonempty → DyadicRegularTree A T N →
      (∀ x ∈ A, x < 2 ^ (T * N)) →
      (∀ j : ℕ, j ≤ N → (2 : ℝ) ^ (γ * (T : ℝ) * (j : ℝ)) ≤
        ((dyadicProjection A (T * j)).card : ℝ)) →
      (A.card : ℝ) ≤ (2 : ℝ) ^ ((1 - δ) * (T : ℝ) * (N : ℝ)) →
      (2 : ℝ) ^ (η * (T : ℝ) * (N : ℝ)) * (A.card : ℝ) ≤
        ((dyadicProjection (natBoundedSums (natLinearQuadraticSet A) K) (T * N)).card : ℝ) := by
  let g := γ / 16
  let ρ := min (δ / 8) (γ / 128)
  let η := ρ / 2 * (γ * δ / 2)
  have hg : 0 < g := by dsimp [g]; positivity
  have hρ : 0 < ρ := lt_min (by positivity) (by positivity)
  have hρδ8 : ρ ≤ δ / 8 := min_le_left _ _
  have hργ128 : ρ ≤ γ / 128 := min_le_right _ _
  have hρδ : ρ ≤ δ / 4 := by linarith
  have hγg : 8 * g ≤ γ := by dsimp [g]; linarith
  have hρg : 3 * ρ < g := by dsimp [g]; linarith
  have hη : 0 < η := by dsimp [η]; positivity
  refine ⟨η, hη, ?_⟩
  intro T hT
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcoef : 0 < η * (T : ℝ) * Real.log 2 := by positivity
  obtain ⟨R, hRbound⟩ := exists_nat_ge (max (1 : ℝ) (max (1 / ρ) (1 / (η * (T : ℝ) * Real.log 2))))
  have hR1 : (1 : ℝ) ≤ R := (le_max_left _ _).trans hRbound
  have hR : 0 < R := by
    have hh : 1 ≤ R := by exact_mod_cast hR1
    omega
  have hρrecip : 1 / ρ ≤ (R : ℝ) := (le_max_left _ _).trans ((le_max_right _ _).trans hRbound)
  have hcoefrecip : 1 / (η * (T : ℝ) * Real.log 2) ≤ (R : ℝ) :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hRbound)
  have hρR : 1 ≤ ρ * (R : ℝ) := by
    have hh := (div_le_iff₀ hρ).mp hρrecip
    nlinarith
  have hcoefR : 1 ≤ (η * (T : ℝ) * Real.log 2) * (R : ℝ) := by
    have hh := (div_le_iff₀ hcoef).mp hcoefrecip
    nlinarith
  have hbudget : 1 ≤ (ρ / 2 * (γ * δ / 2 * (T : ℝ)) * Real.log 2) * (R : ℝ) := by
    calc
      _ ≤ (η * (T : ℝ) * Real.log 2) * (R : ℝ) := hcoefR
      _ = _ := by dsimp [η]; ring
  obtain ⟨K, hK, hgrowth⟩ := exists_regular_tree_bounded_sum_growth T R
    hT hR hγ hδ hδ1 hρ hρδ hρR hg hγg hρg hbudget
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge (2 * (R : ℝ) / γ)
  refine ⟨K, N₀, hK, ?_⟩
  intro N hN A hA htree hbound hprefix hsize
  have hRN : 2 * (R : ℝ) ≤ γ * (N : ℝ) := by
    have hh := (div_le_iff₀ hγ).mp (hN₀.trans (show (N₀ : ℝ) ≤ N by exact_mod_cast hN))
    nlinarith
  have hh := hgrowth N A hA htree hbound hprefix hsize hRN
  have hexponent : ρ / 2 * (γ * δ / 2 * (T : ℝ) * (N : ℝ)) = η * (T : ℝ) * (N : ℝ) := by
    dsimp [η]
    ring
  rwa [hexponent] at hh

theorem dyadic_projection_card_le (A : Finset ℕ) (k : ℕ) :
    (dyadicProjection A k).card ≤ 2 ^ k := by
  calc
    _ ≤ (Finset.range (2 ^ k)).card := Finset.card_le_card (by
      intro x hx
      exact Finset.mem_range.mpr (dyadic_projection_bounded A k x hx))
    _ = _ := Finset.card_range _

theorem nat_factor_of_dyadic_residue {n r T v u : ℕ} (hv : v < T)
    (hr : r = 2 ^ v * u) (hu : Odd u) (hn : n % 2 ^ T = r) :
    ∃ b : ℕ, Odd b ∧ n = 2 ^ v * b := by
  have hpow : 2 ^ T = 2 ^ v * 2 ^ (T - v) := by
    rw [← pow_add, Nat.add_sub_of_le hv.le]
  have heven : Even (2 ^ (T - v) * (n / 2 ^ T)) := by
    apply even_iff_two_dvd.mpr
    exact (pow_dvd_pow 2 (show 1 ≤ T - v by omega)).trans (dvd_mul_right _ _)
  refine ⟨u + 2 ^ (T - v) * (n / 2 ^ T), hu.add_even heven, ?_⟩
  calc
    n = n % 2 ^ T + 2 ^ T * (n / 2 ^ T) := (Nat.mod_add_div _ _).symm
    _ = _ := by rw [hn, hr, hpow]; ring

theorem exists_regular_tree_odd_divided_subset {A : Finset ℕ} {T N : ℕ}
    (htree : DyadicRegularTree A T N) (hbound : ∀ x ∈ A, x < 2 ^ (T * N))
    (hN : 1 ≤ N) (hsize : 1 < (dyadicProjection A T).card) :
    ∃ v : ℕ, v < T ∧ ∃ B : Finset ℕ, B.Nonempty ∧ (∀ b ∈ B, Odd b) ∧
      (∀ b ∈ B, 2 ^ v * b ∈ A) ∧ A.card ≤ 2 ^ T * B.card := by
  obtain ⟨r, hr, hr0⟩ : ∃ r ∈ dyadicProjection A T, r ≠ 0 := by
    by_contra h
    push Not at h
    have hsub : dyadicProjection A T ⊆ {0} := by
      intro x hx
      exact Finset.mem_singleton.mpr (h x hx)
    have hh := Finset.card_le_card hsub
    simp only [Finset.card_singleton] at hh
    omega
  obtain ⟨v, u, hu, hru⟩ := Nat.exists_eq_two_pow_mul_odd hr0
  have hv : v < T := by
    have hrbound := dyadic_projection_bounded A T r hr
    have hu0 : 0 < u := by obtain ⟨t, ht⟩ := hu; omega
    have hvr : 2 ^ v ≤ r := by rw [hru]; nlinarith [pow_pos (by decide : 0 < 2) v]
    by_contra h
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) (show T ≤ v by omega)
    omega
  let D := A.filter (fun x => x % 2 ^ T = r)
  let B := D.image (fun x => x / 2 ^ v)
  have hfactor : ∀ n ∈ D, ∃ b : ℕ, Odd b ∧ n = 2 ^ v * b := by
    intro n hn
    exact nat_factor_of_dyadic_residue hv hru hu (Finset.mem_filter.mp hn).2
  have hD : D.Nonempty := by
    obtain ⟨a, ha, har⟩ := Finset.mem_image.mp hr
    exact ⟨a, Finset.mem_filter.mpr ⟨ha, har⟩⟩
  have hcard : B.card = D.card := by
    apply Finset.card_image_of_injOn
    intro x hx y hy hxy
    obtain ⟨b, hb, rfl⟩ := hfactor x hx
    obtain ⟨c, hc, rfl⟩ := hfactor y hy
    simp only [Nat.mul_div_right _ (by positivity : 0 < 2 ^ v)] at hxy
    rw [hxy]
  refine ⟨v, hv, B, hD.image _, ?_, ?_, ?_⟩
  · intro b hb
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨c, hc, rfl⟩ := hfactor n hn
    simpa only [Nat.mul_div_right _ (by positivity : 0 < 2 ^ v)] using hc
  · intro b hb
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨c, hc, hnc⟩ := hfactor n hn
    have heq : 2 ^ v * (n / 2 ^ v) = n := by
      rw [hnc, Nat.mul_div_right _ (by positivity : 0 < 2 ^ v)]
    rw [heq]
    exact (Finset.mem_filter.mp hn).1
  · obtain ⟨c, hc, hfiber⟩ := dyadic_regular_tree_uniform_fibers htree N le_rfl 1 hN
    rw [dyadic_projection_self hbound] at hfiber
    simp only [Nat.mul_one] at hfiber
    have hDcard : D.card = c := hfiber r hr
    have hAcard : A.card = (dyadicProjection A T).card * c := by
      rw [Finset.card_eq_sum_card_image (fun x => x % 2 ^ T) A]
      calc
        _ = ∑ _r ∈ dyadicProjection A T, c := Finset.sum_congr rfl hfiber
        _ = _ := by simp
    rw [hcard, hDcard, hAcard]
    exact Nat.mul_le_mul_right _ (dyadic_projection_card_le A T)

theorem nat_residue_mass_scaled_subset_le {A B : Finset ℕ} {d : ℕ} (hd : 0 < d)
    (hBA : ∀ b ∈ B, d * b ∈ A) {L : ℝ} (hB : B.Nonempty)
    (hsize : (A.card : ℝ) ≤ L * (B.card : ℝ)) (q r : ℕ) :
    natResidueMass B q r ≤ L * natResidueMass A q (d * r) := by
  have hA : A.Nonempty := by obtain ⟨b, hb⟩ := hB; exact ⟨d * b, hBA b hb⟩
  have hmap : Set.MapsTo (fun b : ℕ => d * b) (natResidueFiber B q r)
      (natResidueFiber A q (d * r)) := by
    intro b hb
    obtain ⟨hbB, hbr⟩ := Finset.mem_filter.mp hb
    exact Finset.mem_filter.mpr ⟨hBA b hbB, (Nat.ModEq.refl d).mul hbr⟩
  have hinj : Function.Injective (fun b : ℕ => d * b) := fun _ _ h => Nat.mul_left_cancel hd h
  have hfiber : ((natResidueFiber B q r).card : ℝ) ≤
      ((natResidueFiber A q (d * r)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card_of_injOn _ hmap hinj.injOn
  have hAp : (0 : ℝ) < A.card := by exact_mod_cast Finset.card_pos.mpr hA
  have hBp : (0 : ℝ) < B.card := by exact_mod_cast Finset.card_pos.mpr hB
  unfold natResidueMass
  rw [← mul_div_assoc, div_le_div_iff₀ hBp hAp]
  calc
    _ ≤ ((natResidueFiber A q (d * r)).card : ℝ) * (A.card : ℝ) :=
      mul_le_mul_of_nonneg_right hfiber hAp.le
    _ ≤ ((natResidueFiber A q (d * r)).card : ℝ) * (L * (B.card : ℝ)) :=
      mul_le_mul_of_nonneg_left hsize (Nat.cast_nonneg _)
    _ = _ := by ring

theorem dyadic_power_times_decay_le {T : ℕ} {a b l : ℝ}
    (hmargin : (T : ℝ) ≤ (a - b) * l) :
    (2 : ℝ) ^ T * (2 : ℝ) ^ (-a * l) ≤ (2 : ℝ) ^ (-b * l) := by
  rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num)]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

theorem odd_divided_subset_regular_mass {T R N S l v : ℕ} {γ ρ g : ℝ}
    (hT : 0 < T) (hR : 0 < R) (hg : 0 < g) (hγg : 8 * g ≤ γ)
    (hρg : 3 * ρ < g) (hρR : 1 ≤ ρ * (R : ℝ)) (hS : 2 * (T * R) ≤ S)
    {A B : Finset ℕ} (hB : B.Nonempty) (hBA : ∀ b ∈ B, 2 ^ v * b ∈ A)
    (hsize : A.card ≤ 2 ^ T * B.card)
    (htree : DyadicRegularTree A T N) (hbound : ∀ x ∈ A, x < 2 ^ (T * N))
    (hprefix : ∀ j : ℕ, j ≤ N → (2 : ℝ) ^ (γ * (T : ℝ) * (j : ℝ)) ≤
      ((dyadicProjection A (T * j)).card : ℝ)) (hl : S < l) (hlN : l ≤ T * N) :
    ∀ x : ZMod (2 ^ l), ‖cyclicUniformNatSet B x‖ ≤
      (2 : ℝ) ^ (-(2 * g) * (l : ℝ)) := by
  have hTR : T ≤ T * R := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left T (show 1 ≤ R by omega)
  have hmin : 2 * T ≤ l := by omega
  have hTl : (T : ℝ) * (R : ℝ) ≤ l := by exact_mod_cast (show T * R ≤ l by omega)
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have hgap : 0 ≤ γ / 2 - 2 * g := by linarith
  have hmarginR : 1 ≤ (γ / 2 - 2 * g) * (R : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hγg hRpos.le
    have hh' := mul_lt_mul_of_pos_right hρg hRpos
    nlinarith
  have hmargin : (T : ℝ) ≤ (γ / 2 - 2 * g) * (l : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hmarginR hTpos.le
    have hh' := mul_le_mul_of_nonneg_left hTl hgap
    nlinarith
  intro x
  rw [norm_cyclicUniformNatSet]
  calc
    _ ≤ (2 : ℝ) ^ T * natResidueMass A (2 ^ l) (2 ^ v * x.val) :=
      nat_residue_mass_scaled_subset_le (by positivity) hBA hB (by exact_mod_cast hsize) _ _
    _ ≤ (2 : ℝ) ^ T * (2 : ℝ) ^ (-(γ / 2) * (l : ℝ)) :=
      mul_le_mul_of_nonneg_left (dyadic_regular_tree_mass_le_at_all_levels hT (by linarith)
        htree hbound hprefix hmin hlN _) (by positivity)
    _ ≤ _ := dyadic_power_times_decay_le hmargin

theorem zmod_card_le_gcd_mul_image {q : ℕ} [NeZero q] (S : Finset (ZMod q)) (d : ℕ) :
    S.card ≤ q.gcd d * (S.image (fun x => x * (d : ZMod q))).card := by
  rw [Finset.card_eq_sum_card_image (fun x : ZMod q => x * (d : ZMod q)) S]
  calc
    _ ≤ ∑ _y ∈ S.image (fun x => x * (d : ZMod q)), q.gcd d := by
      apply Finset.sum_le_sum
      intro y hy
      exact (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ S))).trans
        (zmod_mul_fiber_card_le d y)
    _ = _ := by simp [Nat.mul_comm]

theorem nat_modular_projection_mul_card (A : Finset ℕ) {q : ℕ} [NeZero q] (d : ℕ) :
    (A.image (fun x => x % q)).card ≤
      q.gcd d * (A.image (fun x => (d * x) % q)).card := by
  let S := A.image (fun x : ℕ => (x : ZMod q))
  have hfirst : S.card = (A.image (fun x => x % q)).card := by
    rw [← Finset.card_image_of_injective S (ZMod.val_injective q)]
    simp only [S, Finset.image_image, Function.comp_def, ZMod.val_natCast]
  have hsecond : (S.image (fun x => x * (d : ZMod q))).card =
      (A.image (fun x => (d * x) % q)).card := by
    rw [← Finset.card_image_of_injective (S.image (fun x => x * (d : ZMod q))) (ZMod.val_injective q)]
    simp only [S, Finset.image_image, Function.comp_def]
    congr 1
    apply Finset.image_congr
    intro x hx
    dsimp only
    rw [mul_comm, ← Nat.cast_mul, ZMod.val_natCast]
  have hh := zmod_card_le_gcd_mul_image S d
  rwa [hfirst, hsecond] at hh

theorem dyadic_projection_mul_card_le (A : Finset ℕ) (k d D : ℕ)
    (hgcd : (2 ^ k).gcd d ≤ D) :
    (dyadicProjection A k).card ≤ D * (dyadicProjection (A.image (fun x => d * x)) k).card := by
  have hh := nat_modular_projection_mul_card (q := 2 ^ k) A d
  have heq : A.image (fun x => d * x % 2 ^ k) = dyadicProjection (A.image (fun x => d * x)) k := by
    simp only [dyadicProjection, Finset.image_image, Function.comp_def]
  rw [heq] at hh
  exact hh.trans (Nat.mul_le_mul_right _ hgcd)

theorem dyadic_gcd_scaled_odd_le {b v T : ℕ} (hb : Odd b) (hv : v ≤ T) (k : ℕ) :
    (2 ^ k).gcd (2 ^ v * b) ≤ 2 ^ T := by
  have hcop : (2 ^ k).gcd b = 1 := by
    have hh := (ZMod.isUnit_iff_coprime b (2 ^ k)).mp (odd_natCast_isUnit_dyadic k hb)
    exact hh.symm
  rw [Nat.gcd_mul_left_right_of_gcd_eq_one hcop]
  exact (Nat.gcd_le_right _ (by positivity : 0 < 2 ^ v)).trans
    (Nat.pow_le_pow_right (by decide : 0 < 2) hv)

def natQuadraticSet (A : Finset ℕ) : Finset ℕ := (A ×ˢ A).image (fun p => p.1 * p.2)

theorem scaled_product_sum_mem_quadratic_sums {A B : Finset ℕ} {d : ℕ}
    (hBA : ∀ b ∈ B, d * b ∈ A) (M s : ℕ) :
    ∀ n ∈ natProductSumSet A B (Finset.Ioc 0 M) s,
      d * n ∈ natBoundedSums (natQuadraticSet A) (M * s) := by
  induction s with
  | zero =>
    intro n hn
    have hn0 : n = 0 := Finset.mem_singleton.mp hn
    simpa only [hn0, Nat.mul_zero] using zero_mem_nat_bounded_sums (natQuadraticSet A) 0
  | succ s ih =>
    intro n hn
    obtain ⟨⟨x, y⟩, hxy, rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp hxy
    obtain ⟨⟨⟨a, b⟩, c⟩, habc, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hab, hc⟩ := Finset.mem_product.mp habc
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
    have hprod : a * (d * b) ∈ natBoundedSums (natQuadraticSet A) 1 :=
      mem_nat_bounded_sums_one (Finset.mem_image.mpr ⟨(a, d * b),
        Finset.mem_product.mpr ⟨ha, hBA b hb⟩, rfl⟩)
    have hterm : d * (a * b * c) ∈ natBoundedSums (natQuadraticSet A) M := by
      have hh := nat_bounded_sums_mono (natQuadraticSet A)
        (show 1 * c ≤ M by simpa only [Nat.one_mul] using (Finset.mem_Ioc.mp hc).2)
        (mul_mem_nat_bounded_sums hprod c)
      have heq : d * (a * b * c) = a * (d * b) * c := by ring
      rw [heq]
      exact hh
    have hindex : M * (s + 1) = M + M * s := by ring
    rw [hindex, Nat.mul_add]
    exact add_mem_nat_bounded_sums hterm (ih y hy)

theorem exists_regular_tree_quadratic_projected_growth (T R : ℕ) {γ δ ρ g : ℝ}
    (hT : 0 < T) (hR : 0 < R) (hγ : 0 < γ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hρ : 0 < ρ) (hρδ : ρ ≤ δ / 4) (hρR : 1 ≤ ρ * (R : ℝ))
    (hg : 0 < g) (hγg : 8 * g ≤ γ) (hρg : 3 * ρ < g)
    (hbudget : 1 ≤ (ρ / 2 * (γ * δ / 2 * (T : ℝ)) * Real.log 2) * (R : ℝ)) :
    ∃ K : ℕ, 0 < K ∧ ∀ (N : ℕ) (A : Finset ℕ),
      A.Nonempty → DyadicRegularTree A T N → (∀ x ∈ A, x < 2 ^ (T * N)) →
      (∀ j : ℕ, j ≤ N → (2 : ℝ) ^ (γ * (T : ℝ) * (j : ℝ)) ≤
        ((dyadicProjection A (T * j)).card : ℝ)) →
      (A.card : ℝ) ≤ (2 : ℝ) ^ ((1 - δ) * (T : ℝ) * (N : ℝ)) →
      1 ≤ N → 2 * (R : ℝ) ≤ γ * (N : ℝ) →
      ∃ w a : ℕ, w ≤ N ∧ a ∈ A ∧ (∀ k : ℕ, (2 ^ k).gcd a ≤ 2 ^ T) ∧
        (2 : ℝ) ^ (ρ / 2 * (γ * δ / 2 * (T : ℝ) * (N : ℝ))) *
          ((dyadicProjection A (T * w)).card : ℝ) ≤
            (2 : ℝ) ^ T * ((dyadicProjection (natBoundedSums (natQuadraticSet A) K) (T * w)).card : ℝ) := by
  obtain ⟨S, s, hMS, hS, hs, hgrowth⟩ := exists_regular_tree_product_growth T R
    hT hR hγ hδ hδ1 hρ hρδ hρR hg hρg hbudget
  let K := 2 ^ S * (2 * s)
  refine ⟨K, by dsimp [K]; positivity, ?_⟩
  intro N A hA htree hbound hprefix hsize hN hRN
  have hfirst : 1 < (dyadicProjection A T).card := by
    have hh := hprefix 1 hN
    simp only [Nat.cast_one, mul_one] at hh
    have hp : (1 : ℝ) < (2 : ℝ) ^ (γ * (T : ℝ)) :=
      Real.one_lt_rpow (by norm_num) (mul_pos hγ (by exact_mod_cast hT))
    exact_mod_cast hp.trans_le hh
  obtain ⟨v, hv, B, hB, hBodd, hBA, hAB⟩ :=
    exists_regular_tree_odd_divided_subset htree hbound hN hfirst
  obtain ⟨w, hwN, hgain⟩ := hgrowth N A B hA hB hBodd htree hbound hprefix hsize hRN
    (fun l hl hlN => odd_divided_subset_regular_mass hT hR hg hγg hρg hρR hMS
      hB hBA hAB htree hbound hprefix hl hlN)
  obtain ⟨b, hb⟩ := hB
  have hB : B.Nonempty := ⟨b, hb⟩
  refine ⟨w, 2 ^ v * b, hwN, hBA b hb,
    fun k => dyadic_gcd_scaled_odd_le (hBodd b hb) hv.le k, ?_⟩
  let P := natProductSumSet A B (Finset.Ioc 0 (2 ^ S)) (2 * s)
  have hP : (0 : ℝ) < (dyadicProjection P (T * w)).card := by
    exact_mod_cast Finset.card_pos.mpr ((nat_product_sum_set_nonempty hA hB
      (Finset.nonempty_Ioc.mpr (by positivity)) (2 * s)).image (fun n => n % 2 ^ (T * w)))
  have hAP : (0 : ℝ) < (dyadicProjection A (T * w)).card := by
    exact_mod_cast Finset.card_pos.mpr (hA.image (fun n => n % 2 ^ (T * w)))
  have hscale : (dyadicProjection P (T * w)).card ≤
      2 ^ T * (dyadicProjection (natBoundedSums (natQuadraticSet A) K) (T * w)).card := by
    have hh := dyadic_projection_mul_card_le P (T * w) (2 ^ v) (2 ^ T)
      ((Nat.gcd_le_right _ (by positivity : 0 < 2 ^ v)).trans
        (Nat.pow_le_pow_right (by decide : 0 < 2) hv.le))
    apply hh.trans
    apply Nat.mul_le_mul_left
    apply Finset.card_le_card
    apply Finset.image_subset_image
    intro n hn
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hn
    exact scaled_product_sum_mem_quadratic_sums hBA (2 ^ S) (2 * s) x hx
  exact (log_gain_implies_dyadic_growth hAP hP hgain).trans (by exact_mod_cast hscale)

theorem nat_modular_scaled_fiber_growth (H F : Finset ℕ) {q Q a D : ℕ}
    [NeZero Q] (hq : q ∣ Q) (hbound : ∀ x ∈ F, x < Q)
    (hcommon : ∀ x ∈ F, ∀ y ∈ F, x % q = y % q) (hgcd : Q.gcd a ≤ D) :
    (H.image (fun x => x % q)).card * F.card ≤
      D * ((H ×ˢ F).image (fun p => (p.1 + a * p.2) % Q)).card := by
  let V := F.image (fun x => a * x % Q)
  have hself : F.image (fun x => x % Q) = F := by
    calc
      _ = F.image id := Finset.image_congr (fun x hx => Nat.mod_eq_of_lt (hbound x hx))
      _ = F := Finset.image_id
  have hcard : F.card ≤ D * V.card := by
    have hh := nat_modular_projection_mul_card (q := Q) F a
    rw [hself] at hh
    exact hh.trans (Nat.mul_le_mul_right _ hgcd)
  have hVbound : ∀ x ∈ V, x < Q := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact Nat.mod_lt _ (NeZero.pos Q)
  have hVcommon : ∀ x ∈ V, ∀ y ∈ V, x % q = y % q := by
    intro x hx y hy
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hy
    rw [Nat.mod_mod_of_dvd _ hq, Nat.mod_mod_of_dvd _ hq]
    exact (Nat.ModEq.refl a).mul (hcommon s hs t ht)
  have hsub : ((H ×ˢ V).image (fun p => (p.1 + p.2) % Q)) ⊆
      ((H ×ˢ F).image (fun p => (p.1 + a * p.2) % Q)) := by
    intro z hz
    obtain ⟨⟨h, v⟩, hhv, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hh, hv⟩ := Finset.mem_product.mp hhv
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_image.mpr ⟨(h, f), Finset.mem_product.mpr ⟨hh, hf⟩,
      by simp only [Nat.add_mod_mod]⟩
  calc
    _ ≤ (H.image (fun x => x % q)).card * (D * V.card) := Nat.mul_le_mul_left _ hcard
    _ = D * ((H.image (fun x => x % q)).card * V.card) := by ring
    _ ≤ D * ((H ×ˢ V).image (fun p => (p.1 + p.2) % Q)).card :=
      Nat.mul_le_mul_left _ (nat_modular_sumset_card_ge_projection_mul_fiber H V hq hVbound hVcommon)
    _ ≤ _ := Nat.mul_le_mul_left _ (Finset.card_le_card hsub)

theorem regular_tree_quadratic_growth_of_projected {A : Finset ℕ} {T N w K a D : ℕ}
    (hA : A.Nonempty) (htree : DyadicRegularTree A T N)
    (hbound : ∀ x ∈ A, x < 2 ^ (T * N)) (hwN : w ≤ N) (ha : a ∈ A)
    (hgcd : (2 ^ (T * N)).gcd a ≤ D) {Λ : ℝ}
    (hprojected : Λ * ((dyadicProjection A (T * w)).card : ℝ) ≤
      (D : ℝ) * ((dyadicProjection (natBoundedSums (natQuadraticSet A) K) (T * w)).card : ℝ)) :
    Λ * (A.card : ℝ) ≤ (D : ℝ) ^ 2 *
      ((dyadicProjection (natBoundedSums (natQuadraticSet A) (K + 1)) (T * N)).card : ℝ) := by
  let H := natBoundedSums (natQuadraticSet A) K
  obtain ⟨c, hc, hfiber⟩ := dyadic_regular_tree_uniform_fibers htree N le_rfl w hwN
  rw [dyadic_projection_self hbound] at hfiber
  obtain ⟨x₀, hx₀⟩ := hA
  let r := x₀ % 2 ^ (T * w)
  let F := A.filter (fun x => x % 2 ^ (T * w) = r)
  have hFA : F ⊆ A := Finset.filter_subset _ _
  have hr : r ∈ dyadicProjection A (T * w) := Finset.mem_image_of_mem _ hx₀
  have hFc : F.card = c := hfiber r hr
  have hAcard : A.card = (dyadicProjection A (T * w)).card * c := by
    rw [Finset.card_eq_sum_card_image (fun x => x % 2 ^ (T * w)) A]
    calc
      _ = ∑ _s ∈ dyadicProjection A (T * w), c := Finset.sum_congr rfl hfiber
      _ = _ := by simp
  have hraw := nat_modular_scaled_fiber_growth H F (pow_dvd_pow 2 (Nat.mul_le_mul_left T hwN))
    (fun x hx => hbound x (hFA hx))
    (fun x hx y hy => (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm) hgcd
  have hsub : ((H ×ˢ F).image (fun p => (p.1 + a * p.2) % 2 ^ (T * N))) ⊆
      dyadicProjection (natBoundedSums (natQuadraticSet A) (K + 1)) (T * N) := by
    intro z hz
    obtain ⟨⟨h, f⟩, hhf, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hh, hf⟩ := Finset.mem_product.mp hhf
    refine Finset.mem_image.mpr ⟨h + a * f, ?_, rfl⟩
    exact add_mem_nat_bounded_sums hh (mem_nat_bounded_sums_one
      (Finset.mem_image.mpr ⟨(a, f), Finset.mem_product.mpr ⟨ha, hFA hf⟩, rfl⟩))
  rw [hFc] at hraw
  have hrawR : ((dyadicProjection H (T * w)).card : ℝ) * (c : ℝ) ≤ (D : ℝ) *
      ((dyadicProjection (natBoundedSums (natQuadraticSet A) (K + 1)) (T * N)).card : ℝ) := by
    exact_mod_cast hraw.trans (Nat.mul_le_mul_left _ (Finset.card_le_card hsub))
  calc
    _ = (Λ * ((dyadicProjection A (T * w)).card : ℝ)) * (c : ℝ) := by
      rw [hAcard, Nat.cast_mul]; ring
    _ ≤ ((D : ℝ) * ((dyadicProjection H (T * w)).card : ℝ)) * (c : ℝ) :=
      mul_le_mul_of_nonneg_right hprojected (Nat.cast_nonneg _)
    _ = (D : ℝ) * (((dyadicProjection H (T * w)).card : ℝ) * (c : ℝ)) := by ring
    _ ≤ (D : ℝ) * ((D : ℝ) *
        ((dyadicProjection (natBoundedSums (natQuadraticSet A) (K + 1)) (T * N)).card : ℝ)) :=
      mul_le_mul_of_nonneg_left hrawR (Nat.cast_nonneg _)
    _ = _ := by ring

theorem exists_regular_tree_quadratic_growth (T R : ℕ) {γ δ ρ g : ℝ}
    (hT : 0 < T) (hR : 0 < R) (hγ : 0 < γ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hρ : 0 < ρ) (hρδ : ρ ≤ δ / 4) (hρR : 1 ≤ ρ * (R : ℝ))
    (hg : 0 < g) (hγg : 8 * g ≤ γ) (hρg : 3 * ρ < g)
    (hbudget : 1 ≤ (ρ / 2 * (γ * δ / 2 * (T : ℝ)) * Real.log 2) * (R : ℝ)) :
    ∃ K : ℕ, 0 < K ∧ ∀ (N : ℕ) (A : Finset ℕ),
      A.Nonempty → DyadicRegularTree A T N → (∀ x ∈ A, x < 2 ^ (T * N)) →
      (∀ j : ℕ, j ≤ N → (2 : ℝ) ^ (γ * (T : ℝ) * (j : ℝ)) ≤
        ((dyadicProjection A (T * j)).card : ℝ)) →
      (A.card : ℝ) ≤ (2 : ℝ) ^ ((1 - δ) * (T : ℝ) * (N : ℝ)) →
      1 ≤ N → 2 * (R : ℝ) ≤ γ * (N : ℝ) →
      (2 : ℝ) ^ (ρ / 2 * (γ * δ / 2 * (T : ℝ) * (N : ℝ))) * (A.card : ℝ) ≤
        ((2 : ℝ) ^ T) ^ 2 *
          ((dyadicProjection (natBoundedSums (natQuadraticSet A) K) (T * N)).card : ℝ) := by
  obtain ⟨K, hK, hgrowth⟩ := exists_regular_tree_quadratic_projected_growth T R
    hT hR hγ hδ hδ1 hρ hρδ hρR hg hγg hρg hbudget
  refine ⟨K + 1, by omega, ?_⟩
  intro N A hA htree hbound hprefix hsize hN hRN
  obtain ⟨w, a, hwN, ha, hgcd, hprojected⟩ := hgrowth N A hA htree hbound hprefix hsize hN hRN
  have hh := regular_tree_quadratic_growth_of_projected hA htree hbound hwN ha (hgcd (T * N))
    (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using hprojected)
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using hh

theorem dyadic_quadratic_growth_absorb_loss {α : ℝ} {T N : ℕ} {a b : ℝ}
    (ha : 0 ≤ a) (hN : 4 ≤ α * (N : ℝ))
    (hgain : (2 : ℝ) ^ (α * (T : ℝ) * (N : ℝ)) * a ≤ ((2 : ℝ) ^ T) ^ 2 * b) :
    (2 : ℝ) ^ (α / 2 * (T : ℝ) * (N : ℝ)) * a ≤ b := by
  have hpow : ((2 : ℝ) ^ T) ^ 2 = (2 : ℝ) ^ (2 * (T : ℝ)) := by
    rw [← pow_mul, ← Real.rpow_natCast, Nat.cast_mul, Nat.cast_ofNat, mul_comm]
  rw [hpow] at hgain
  apply (mul_le_mul_iff_of_pos_left (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (2 * (T : ℝ)))).mp
  calc
    _ = (2 : ℝ) ^ (2 * (T : ℝ) + α / 2 * (T : ℝ) * (N : ℝ)) * a := by
      rw [Real.rpow_add (by norm_num)]; ring
    _ ≤ (2 : ℝ) ^ (α * (T : ℝ) * (N : ℝ)) * a := by
      apply mul_le_mul_of_nonneg_right _ ha
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have hh := mul_le_mul_of_nonneg_right hN (Nat.cast_nonneg T : (0 : ℝ) ≤ T)
      nlinarith
    _ ≤ _ := hgain

theorem exists_uniform_regular_tree_quadratic_amplification {γ δ : ℝ}
    (hγ : 0 < γ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ η : ℝ, 0 < η ∧ ∀ T : ℕ, 0 < T → ∃ K N₀ : ℕ, 0 < K ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ A : Finset ℕ, A.Nonempty → DyadicRegularTree A T N →
      (∀ x ∈ A, x < 2 ^ (T * N)) →
      (∀ j : ℕ, j ≤ N → (2 : ℝ) ^ (γ * (T : ℝ) * (j : ℝ)) ≤
        ((dyadicProjection A (T * j)).card : ℝ)) →
      (A.card : ℝ) ≤ (2 : ℝ) ^ ((1 - δ) * (T : ℝ) * (N : ℝ)) →
      (2 : ℝ) ^ (η * (T : ℝ) * (N : ℝ)) * (A.card : ℝ) ≤
        ((dyadicProjection (natBoundedSums (natQuadraticSet A) K) (T * N)).card : ℝ) := by
  let g := γ / 16
  let ρ := min (δ / 8) (γ / 128)
  let α := ρ / 2 * (γ * δ / 2)
  have hg : 0 < g := by dsimp [g]; positivity
  have hρ : 0 < ρ := lt_min (by positivity) (by positivity)
  have hρδ8 : ρ ≤ δ / 8 := min_le_left _ _
  have hργ128 : ρ ≤ γ / 128 := min_le_right _ _
  have hρδ : ρ ≤ δ / 4 := by linarith
  have hγg : 8 * g ≤ γ := by dsimp [g]; linarith
  have hρg : 3 * ρ < g := by dsimp [g]; linarith
  have hα : 0 < α := by dsimp [α]; positivity
  refine ⟨α / 2, by positivity, ?_⟩
  intro T hT
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcoef : 0 < α * (T : ℝ) * Real.log 2 := by positivity
  obtain ⟨R, hRbound⟩ := exists_nat_ge (max (1 : ℝ) (max (1 / ρ) (1 / (α * (T : ℝ) * Real.log 2))))
  have hR1 : (1 : ℝ) ≤ R := (le_max_left _ _).trans hRbound
  have hR : 0 < R := by
    have hh : 1 ≤ R := by exact_mod_cast hR1
    omega
  have hρrecip : 1 / ρ ≤ (R : ℝ) := (le_max_left _ _).trans ((le_max_right _ _).trans hRbound)
  have hcoefrecip : 1 / (α * (T : ℝ) * Real.log 2) ≤ (R : ℝ) :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hRbound)
  have hρR : 1 ≤ ρ * (R : ℝ) := by
    have hh := (div_le_iff₀ hρ).mp hρrecip
    nlinarith
  have hcoefR : 1 ≤ (α * (T : ℝ) * Real.log 2) * (R : ℝ) := by
    have hh := (div_le_iff₀ hcoef).mp hcoefrecip
    nlinarith
  have hbudget : 1 ≤ (ρ / 2 * (γ * δ / 2 * (T : ℝ)) * Real.log 2) * (R : ℝ) := by
    calc
      _ ≤ (α * (T : ℝ) * Real.log 2) * (R : ℝ) := hcoefR
      _ = _ := by dsimp [α]; ring
  obtain ⟨K, hK, hgrowth⟩ := exists_regular_tree_quadratic_growth T R
    hT hR hγ hδ hδ1 hρ hρδ hρR hg hγg hρg hbudget
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge (max (1 : ℝ) (max (2 * (R : ℝ) / γ) (4 / α)))
  refine ⟨K, N₀, hK, ?_⟩
  intro N hN A hA htree hbound hprefix hsize
  have hNbound : max (1 : ℝ) (max (2 * (R : ℝ) / γ) (4 / α)) ≤ N :=
    hN₀.trans (by exact_mod_cast hN)
  have hN1 : 1 ≤ N := by exact_mod_cast (le_max_left _ _).trans hNbound
  have hRN : 2 * (R : ℝ) ≤ γ * (N : ℝ) := by
    have hh := (div_le_iff₀ hγ).mp ((le_max_left _ _).trans ((le_max_right _ _).trans hNbound))
    nlinarith
  have hαN : 4 ≤ α * (N : ℝ) := by
    have hh := (div_le_iff₀ hα).mp ((le_max_right _ _).trans ((le_max_right _ _).trans hNbound))
    nlinarith
  have hh := hgrowth N A hA htree hbound hprefix hsize hN1 hRN
  have hexponent : ρ / 2 * (γ * δ / 2 * (T : ℝ) * (N : ℝ)) = α * (T : ℝ) * (N : ℝ) := by
    dsimp [α]
    ring
  rw [hexponent] at hh
  exact dyadic_quadratic_growth_absorb_loss (Nat.cast_nonneg _) hαN hh

theorem dyadic_tree_block_image {A : Finset ℕ} {b T m k : ℕ} (hA : DyadicTreeBlock A b T m k)
    (f : ℕ → ℕ) (hinj : Set.InjOn f A)
    (hmod : ∀ j : ℕ, j ≤ b + T → ∀ x ∈ A, ∀ y ∈ A,
      f x % 2 ^ j = f y % 2 ^ j ↔ x % 2 ^ j = y % 2 ^ j) :
    DyadicTreeBlock (A.image f) b T m k := by
  have hfiber : ∀ a ∈ A,
      (A.image f).filter (fun y => y % 2 ^ m = f a % 2 ^ m) =
        (A.filter (fun x => x % 2 ^ m = a % 2 ^ m)).image f := by
    intro a ha
    ext y
    constructor
    · intro hy
      obtain ⟨hyA, hym⟩ := Finset.mem_filter.mp hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hyA
      exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr
        ⟨hx, (hmod m hA.split_lt.le x hx a ha).mp hym⟩, rfl⟩
    · intro hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨hxA, hxm⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ hxA,
        (hmod m hA.split_lt.le x hxA a ha).mpr hxm⟩
  refine ⟨hA.base_le, hA.split_lt, hA.count_le, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hy
    exact (hmod m hA.split_lt.le a ha c hc).mpr
      (hA.common a ha c hc ((hmod b (by omega) a ha c hc).mp hxy))
  · intro r hr
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hy
    rw [hfiber a ha, Finset.card_image_of_injOn (hinj.mono (Finset.filter_subset _ _))]
    exact hA.fiber_card _ (Finset.mem_image_of_mem _ ha)
  · intro r hr hk
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨x, hx, z, hz, hxz⟩ := hA.splits _ (Finset.mem_image_of_mem _ ha) hk
    rw [hfiber a ha]
    refine ⟨f x, Finset.mem_image_of_mem _ hx, f z, Finset.mem_image_of_mem _ hz, ?_⟩
    intro h
    exact hxz ((hmod (m + 1) (by have := hA.split_lt; omega) x (Finset.mem_filter.mp hx).1
      z (Finset.mem_filter.mp hz).1).mp h)

theorem dyadic_translation_mod_eq_iff {j e : ℕ} (hje : j ≤ e) (c x y : ℕ) :
    (x + c) % 2 ^ e % 2 ^ j = (y + c) % 2 ^ e % 2 ^ j ↔ x % 2 ^ j = y % 2 ^ j := by
  rw [Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 hje), Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 hje)]
  constructor
  · exact (Nat.ModEq.refl c).add_right_cancel
  · intro h
    exact (show Nat.ModEq (2 ^ j) x y from h).add (Nat.ModEq.refl c)

theorem dyadic_translation_injOn {A : Finset ℕ} {e : ℕ} (hA : ∀ x ∈ A, x < 2 ^ e) (c : ℕ) :
    Set.InjOn (fun x => (x + c) % 2 ^ e) A := by
  intro x hx y hy hxy
  have h := (dyadic_translation_mod_eq_iff (le_refl e) c x y).mp (congrArg (fun n => n % 2 ^ e) hxy)
  simpa only [Nat.mod_eq_of_lt (hA x hx), Nat.mod_eq_of_lt (hA y hy)] using h

theorem dyadic_projection_translate_trans (A : Finset ℕ) (e c : ℕ) :
    dyadicProjection (natTranslate (dyadicProjection A e) c) e =
      dyadicProjection (natTranslate A c) e := by
  simp only [dyadicProjection, natTranslate, Finset.image_image, Function.comp_def]
  apply Finset.image_congr
  intro x hx
  dsimp only
  exact Nat.mod_add_mod _ _ _

theorem dyadic_tree_block_mod_translate {A : Finset ℕ} {b T m k : ℕ}
    (hA : DyadicTreeBlock A b T m k) (hbound : ∀ x ∈ A, x < 2 ^ (b + T)) (c : ℕ) :
    DyadicTreeBlock (dyadicProjection (natTranslate A c) (b + T)) b T m k := by
  have hh := dyadic_tree_block_image hA (fun x => (x + c) % 2 ^ (b + T))
    (dyadic_translation_injOn hbound c)
    (fun j hj x hx y hy => dyadic_translation_mod_eq_iff hj c x y)
  simpa only [dyadicProjection, natTranslate, Finset.image_image, Function.comp_def] using hh

theorem dyadic_regular_tree_mod_translate {A : Finset ℕ} {T N : ℕ}
    (htree : DyadicRegularTree A T N) (c : ℕ) :
    DyadicRegularTree (dyadicProjection (natTranslate A c) (T * N)) T N := by
  intro i hi
  obtain ⟨m, k, hblock⟩ := htree i hi
  have he : T * i + T = T * (i + 1) := by ring
  have hh := dyadic_tree_block_mod_translate hblock
    (by simpa only [he] using dyadic_projection_bounded A (T * (i + 1))) c
  rw [he, dyadic_projection_translate_trans] at hh
  refine ⟨m, k, ?_⟩
  rw [dyadic_projection_trans _ (Nat.mul_le_mul_left T (show i + 1 ≤ N by omega))]
  exact hh

theorem dyadic_projection_translate_card (A : Finset ℕ) (e c : ℕ) :
    (dyadicProjection (natTranslate A c) e).card = (dyadicProjection A e).card := by
  rw [← dyadic_projection_translate_trans A e c]
  change (((dyadicProjection A e).image (fun x => x + c)).image (fun x => x % 2 ^ e)).card = _
  rw [Finset.image_image]
  exact Finset.card_image_of_injOn (dyadic_translation_injOn (dyadic_projection_bounded A e) c)

def natCenter (A : Finset ℕ) (a : ℕ) : Finset ℕ := A.image (fun x => x - a)

theorem nat_center_eq_mod_translate {A : Finset ℕ} {a e : ℕ}
    (ha : a < 2 ^ e) (hbase : ∀ x ∈ A, a ≤ x) (hbound : ∀ x ∈ A, x < 2 ^ e) :
    natCenter A a = dyadicProjection (natTranslate A (2 ^ e - a)) e := by
  simp only [natCenter, dyadicProjection, natTranslate, Finset.image_image, Function.comp_def]
  apply Finset.image_congr
  intro x hx
  have heq : x + (2 ^ e - a) = x - a + 2 ^ e := by have := hbase x hx; omega
  dsimp only
  rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.sub_le x a) (hbound x hx))]

theorem nat_center_card {A : Finset ℕ} {a : ℕ} (hbase : ∀ x ∈ A, a ≤ x) :
    (natCenter A a).card = A.card := by
  apply Finset.card_image_of_injOn
  intro x hx y hy hxy
  change x - a = y - a at hxy
  have := hbase x hx
  have := hbase y hy
  omega

theorem dyadic_regular_tree_center {A : Finset ℕ} {a T N : ℕ}
    (htree : DyadicRegularTree A T N) (ha : a ∈ A)
    (hbase : ∀ x ∈ A, a ≤ x) (hbound : ∀ x ∈ A, x < 2 ^ (T * N)) :
    DyadicRegularTree (natCenter A a) T N := by
  rw [nat_center_eq_mod_translate (hbound a ha) hbase hbound]
  exact dyadic_regular_tree_mod_translate htree _

theorem dyadic_center_projection_card {A : Finset ℕ} {a e j : ℕ}
    (ha : a ∈ A) (hbase : ∀ x ∈ A, a ≤ x) (hbound : ∀ x ∈ A, x < 2 ^ e) (hj : j ≤ e) :
    (dyadicProjection (natCenter A a) j).card = (dyadicProjection A j).card := by
  rw [nat_center_eq_mod_translate (hbound a ha) hbase hbound,
    dyadic_projection_trans _ hj, dyadic_projection_translate_card]

theorem scaled_mem_nat_bounded_sums {A B : Finset ℕ} {d : ℕ}
    (hmap : ∀ a ∈ A, d * a ∈ B) (K : ℕ) :
    ∀ n ∈ natBoundedSums A K, d * n ∈ natBoundedSums B K := by
  induction K with
  | zero =>
    intro n hn
    have hn0 : n = 0 := Finset.mem_singleton.mp hn
    simpa only [hn0, Nat.mul_zero] using zero_mem_nat_bounded_sums B 0
  | succ K ih =>
    intro n hn
    obtain ⟨⟨a, x⟩, hax, rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨ha, hx⟩ := Finset.mem_product.mp hax
    have hda : d * a ∈ insert 0 B := by
      rcases Finset.mem_insert.mp ha with rfl | ha
      · simp only [Nat.mul_zero, Finset.mem_insert_self]
      · exact Finset.mem_insert_of_mem (hmap a ha)
    exact Finset.mem_image.mpr ⟨(d * a, d * x), Finset.mem_product.mpr ⟨hda, ih x hx⟩,
      (Nat.mul_add d a x).symm⟩

theorem scaled_quadratic_sums_mem {A B : Finset ℕ} {d : ℕ}
    (hmap : ∀ a ∈ A, d * a ∈ B) (K : ℕ) :
    ∀ n ∈ natBoundedSums (natQuadraticSet A) K,
      d ^ 2 * n ∈ natBoundedSums (natQuadraticSet B) K := by
  apply scaled_mem_nat_bounded_sums
  intro a ha
  obtain ⟨⟨x, y⟩, hxy, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨hx, hy⟩ := Finset.mem_product.mp hxy
  exact Finset.mem_image.mpr ⟨(d * x, d * y), Finset.mem_product.mpr ⟨hmap x hx, hmap y hy⟩,
    by dsimp only; ring⟩

theorem dyadic_scaled_quadratic_card {A B : Finset ℕ} {d e J : ℕ}
    (hmap : ∀ a ∈ A, 2 ^ d * a ∈ B) (heJ : e ≤ J) (K : ℕ) :
    (dyadicProjection (natBoundedSums (natQuadraticSet A) K) e).card ≤
      2 ^ (2 * d) * (dyadicProjection (natBoundedSums (natQuadraticSet B) K) J).card := by
  have hpow : (2 ^ d : ℕ) ^ 2 = 2 ^ (2 * d) := by rw [← pow_mul, Nat.mul_comm]
  have hsub : (natBoundedSums (natQuadraticSet A) K).image (fun x => 2 ^ (2 * d) * x) ⊆
      natBoundedSums (natQuadraticSet B) K := by
    intro n hn
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hn
    simpa only [hpow] using scaled_quadratic_sums_mem hmap K x hx
  calc
    _ ≤ (dyadicProjection (natBoundedSums (natQuadraticSet A) K) J).card :=
      dyadic_projection_card_mono _ heJ
    _ ≤ 2 ^ (2 * d) * (dyadicProjection
        ((natBoundedSums (natQuadraticSet A) K).image (fun x => 2 ^ (2 * d) * x)) J).card :=
      dyadic_projection_mul_card_le _ J _ _ (Nat.gcd_le_right _ (by positivity))
    _ ≤ _ := Nat.mul_le_mul_left _ (Finset.card_le_card (Finset.image_subset_image hsub))

def natDifferenceSet (A : Finset ℕ) : Finset ℕ := (A ×ˢ A).image (fun p => p.1 - p.2)

theorem centered_zoom_scaled_mem_difference {A B : Finset ℕ} {d r a : ℕ}
    (hBA : B ⊆ A) (hr : r < 2 ^ d) (ha : a ∈ dyadicZoom B d r) :
    ∀ x ∈ natCenter (dyadicZoom B d r) a, 2 ^ d * x ∈ natDifferenceSet A := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
  have hyB := (dyadic_zoom_mem hr).mp hy
  have haB := (dyadic_zoom_mem hr).mp ha
  refine Finset.mem_image.mpr ⟨(r + 2 ^ d * y, r + 2 ^ d * a),
    Finset.mem_product.mpr ⟨hBA hyB, hBA haB⟩, ?_⟩
  dsimp only
  rw [Nat.add_sub_add_left, Nat.mul_sub_left_distrib]

theorem exists_centered_regular_tail {A B : Finset ℕ} {T N i : ℕ} {γ : ℝ}
    (hBA : B ⊆ A) (hB : B.Nonempty) (htree : DyadicRegularTree B T N)
    (hbound : ∀ x ∈ B, x < 2 ^ (T * N)) (hiN : i ≤ N)
    (htail : ∀ j : ℕ, i ≤ j → j ≤ N →
      ((dyadicProjection B (T * i)).card : ℝ) * (2 : ℝ) ^ (γ * ((T * (j - i) : ℕ) : ℝ)) ≤
        ((dyadicProjection B (T * j)).card : ℝ)) :
    ∃ C : Finset ℕ, C.Nonempty ∧ DyadicRegularTree C T (N - i) ∧
      (∀ x ∈ C, x < 2 ^ (T * (N - i))) ∧
      (∀ j : ℕ, j ≤ N - i → (2 : ℝ) ^ (γ * (T : ℝ) * (j : ℝ)) ≤
        ((dyadicProjection C (T * j)).card : ℝ)) ∧
      C.card ≤ A.card ∧ B.card ≤ 2 ^ (T * i) * C.card ∧
      (∀ x ∈ C, 2 ^ (T * i) * x ∈ natDifferenceSet A) := by
  obtain ⟨r, hr⟩ := hB.image (fun x => x % 2 ^ (T * i))
  have hrB : r ∈ dyadicProjection B (T * i) := hr
  have hrlt := dyadic_projection_bounded B (T * i) r hrB
  let Z := dyadicZoom B (T * i) r
  have hZ : Z.Nonempty := dyadic_zoom_nonempty hrB
  have hZbound : ∀ x ∈ Z, x < 2 ^ (T * (N - i)) :=
    dyadic_zoom_bounded (by simpa only [← Nat.mul_add, Nat.add_sub_of_le hiN] using hbound) r
  obtain ⟨a, ha, hamin⟩ := Finset.exists_min_image Z id hZ
  have hbase : ∀ x ∈ Z, a ≤ x := hamin
  let C := natCenter Z a
  have hCcard : C.card = Z.card := nat_center_card hbase
  refine ⟨C, hZ.image _, dyadic_regular_tree_center (dyadic_regular_tree_zoom htree hiN hrlt)
    ha hbase hZbound, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact lt_of_le_of_lt (Nat.sub_le _ _) (hZbound y hy)
  · intro j hj
    rw [dyadic_center_projection_card ha hbase hZbound (Nat.mul_le_mul_left T hj)]
    simpa only [Nat.cast_mul, mul_assoc] using
      dyadic_regular_tree_zoom_growth htree hrB htail j (by omega)
  · rw [hCcard, dyadic_zoom_card]
    exact (Finset.card_filter_le _ _).trans (Finset.card_le_card hBA)
  · rw [hCcard, ← dyadic_regular_tree_zoom_card htree hbound hiN hrB]
    exact Nat.mul_le_mul_right _ (dyadic_projection_card_le B (T * i))
  · exact centered_zoom_scaled_mem_difference hBA hrlt ha

theorem exists_general_dyadic_growth_dichotomy {γ δ : ℝ}
    (hγ : 0 < γ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ κ ε : ℝ, 0 < κ ∧ 0 < ε ∧ ε ≤ 1 / 4 ∧
      ∃ T K N₀ : ℕ, 0 < T ∧ 0 < K ∧ ∀ N : ℕ, N₀ ≤ N →
        ∀ A : Finset ℕ, A.Nonempty → (∀ x ∈ A, x < 2 ^ (T * N)) →
        (A.card : ℝ) ≤ (2 : ℝ) ^ ((1 - δ) * (T : ℝ) * (N : ℝ)) →
        (∀ j : ℕ, j ≤ N → ε * (N : ℝ) < (j : ℝ) →
          (2 : ℝ) ^ (γ * (T : ℝ) * (j : ℝ)) ≤ ((dyadicProjection A (T * j)).card : ℝ)) →
        (2 : ℝ) ^ (κ * (T : ℝ) * (N : ℝ)) * (A.card : ℝ) ≤
          (((A ×ˢ A).image (fun p => (p.1 + p.2) % 2 ^ (T * N))).card : ℝ) ∨
        (2 : ℝ) ^ (κ * (T : ℝ) * (N : ℝ)) * (A.card : ℝ) ≤
          ((dyadicProjection (natBoundedSums (natQuadraticSet (natDifferenceSet A)) K) (T * N)).card : ℝ) := by
  obtain ⟨α, hα, hamp⟩ := exists_uniform_regular_tree_quadratic_amplification
    (show 0 < γ / 2 by positivity) (show 0 < δ / 2 by positivity) (show δ / 2 ≤ 1 by linarith)
  let ε := min (1 / 4 : ℝ) (min (δ / 4) (α / 16))
  let κ := min (ε * γ / 8) (α / 16)
  have hε : 0 < ε := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have hε4 : ε ≤ 1 / 4 := min_le_left _ _
  have hεδ : ε ≤ δ / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hεα : ε ≤ α / 16 := (min_le_right _ _).trans (min_le_right _ _)
  have hκ : 0 < κ := lt_min (by positivity) (by positivity)
  have hκε : κ ≤ ε * γ / 8 := min_le_left _ _
  have hκα : κ ≤ α / 16 := min_le_right _ _
  have hbudget : κ + κ ≤ ε * (γ - γ / 2) := by nlinarith [mul_pos hε hγ]
  have htotal : 2 * κ + (α + 3) * ε ≤ α := by
    have hh := mul_le_mul_of_nonneg_left hε4 hα.le
    nlinarith
  obtain ⟨T, hT, hregular⟩ := exists_dyadic_regular_tree_small_loss hκ
  obtain ⟨K, N₁, hK, hampT⟩ := hamp T hT
  refine ⟨κ, ε, hκ, hε, hε4, T, K, 2 * N₁ + 1, hT, hK, ?_⟩
  intro N hN A hA hbound hsize hprojection
  by_cases hsum : (2 : ℝ) ^ (κ * (T : ℝ) * (N : ℝ)) * (A.card : ℝ) ≤
      (((A ×ˢ A).image (fun p => (p.1 + p.2) % 2 ^ (T * N))).card : ℝ)
  · exact Or.inl hsum
  apply Or.inr
  have hsmall : (((A ×ˢ A).image (fun p => (p.1 + p.2) % 2 ^ (T * N))).card : ℝ) ≤
      (2 : ℝ) ^ (κ * ((T * N : ℕ) : ℝ)) * (A.card : ℝ) := by
    simpa only [Nat.cast_mul, mul_assoc] using (lt_of_not_ge hsum).le
  obtain ⟨B, hBA, htree, hlarge⟩ := hregular N A hbound
  have hB : B.Nonempty := by
    apply Finset.card_pos.mp
    have hApos : (0 : ℝ) < A.card := by exact_mod_cast Finset.card_pos.mpr hA
    have hpow : 0 < (2 : ℝ) ^ (κ * ((T * N : ℕ) : ℝ)) := by positivity
    have hBpos : (0 : ℝ) < B.card := by nlinarith
    exact_mod_cast hBpos
  have hBbound : ∀ x ∈ B, x < 2 ^ (T * N) := fun x hx => hbound x (hBA hx)
  obtain ⟨i, hiN, hiε, hPi, htail⟩ := exists_regular_tree_dense_tail hT hBA hB htree hBbound
    (show γ / 2 < γ by linarith) hbudget hlarge hsmall
    (by intro j hj hεj; simpa only [Nat.cast_mul, mul_assoc] using hprojection j hj hεj)
  obtain ⟨C, hC, hCtree, hCbound, hCprefix, hCA, hBC, hmap⟩ :=
    exists_centered_regular_tail hBA hB htree hBbound hiN htail
  have hi2 : 2 * i ≤ N := by
    have hh := mul_le_mul_of_nonneg_right hε4 (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
    have hh' : (2 : ℝ) * (i : ℝ) ≤ N := by nlinarith
    exact_mod_cast hh'
  have htailN : N₁ ≤ N - i := by omega
  have hdensity : (1 - δ) * (N : ℝ) ≤ (1 - δ / 2) * ((N - i : ℕ) : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hεδ (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
    rw [Nat.cast_sub hiN]
    nlinarith [mul_nonneg hδ.le (Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
  have hCsize : (C.card : ℝ) ≤ (2 : ℝ) ^ ((1 - δ / 2) * (T : ℝ) * ((N - i : ℕ) : ℝ)) := by
    calc
      _ ≤ (A.card : ℝ) := by exact_mod_cast hCA
      _ ≤ (2 : ℝ) ^ ((1 - δ) * (T : ℝ) * (N : ℝ)) := hsize
      _ ≤ _ := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        have hh := mul_le_mul_of_nonneg_left hdensity (Nat.cast_nonneg T : (0 : ℝ) ≤ T)
        nlinarith
  have hgrowth := hampT (N - i) htailN C hC hCtree hCbound hCprefix hCsize
  let Z := ((dyadicProjection (natBoundedSums (natQuadraticSet (natDifferenceSet A)) K) (T * N)).card : ℝ)
  have hlift : ((dyadicProjection (natBoundedSums (natQuadraticSet C) K) (T * (N - i))).card : ℝ) ≤
      (2 : ℝ) ^ (2 * (T : ℝ) * (i : ℝ)) * Z := by
    have hh := dyadic_scaled_quadratic_card hmap (Nat.mul_le_mul_left T (Nat.sub_le N i)) K
    have hhR : ((dyadicProjection (natBoundedSums (natQuadraticSet C) K) (T * (N - i))).card : ℝ) ≤
        (2 : ℝ) ^ (2 * (T * i)) * Z := by dsimp only [Z]; exact_mod_cast hh
    simpa only [← Real.rpow_natCast, Nat.cast_mul, Nat.cast_ofNat, mul_assoc] using hhR
  have hlargeC : (A.card : ℝ) ≤
      (2 : ℝ) ^ (κ * (T : ℝ) * (N : ℝ) + (T : ℝ) * (i : ℝ)) * (C.card : ℝ) := by
    have hBCR : (B.card : ℝ) ≤ (2 : ℝ) ^ ((T : ℝ) * (i : ℝ)) * (C.card : ℝ) := by
      have hh : (B.card : ℝ) ≤ (2 : ℝ) ^ (T * i) * (C.card : ℝ) := by exact_mod_cast hBC
      simpa only [← Real.rpow_natCast, Nat.cast_mul] using hh
    calc
      _ ≤ (2 : ℝ) ^ (κ * (T : ℝ) * (N : ℝ)) * (B.card : ℝ) := by
        simpa only [Nat.cast_mul, mul_assoc] using hlarge
      _ ≤ (2 : ℝ) ^ (κ * (T : ℝ) * (N : ℝ)) *
          ((2 : ℝ) ^ ((T : ℝ) * (i : ℝ)) * (C.card : ℝ)) :=
        mul_le_mul_of_nonneg_left hBCR (by positivity)
      _ = _ := by rw [← mul_assoc, ← Real.rpow_add (by norm_num)]
  have hexp : 2 * κ * (T : ℝ) * (N : ℝ) + 3 * (T : ℝ) * (i : ℝ) ≤
      α * (T : ℝ) * ((N - i : ℕ) : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right htotal (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
    have hh' := mul_le_mul_of_nonneg_left hiε (show 0 ≤ α + 3 by linarith)
    have hi : 2 * κ * (N : ℝ) + 3 * (i : ℝ) ≤ α * ((N - i : ℕ) : ℝ) := by
      rw [Nat.cast_sub hiN]
      nlinarith
    have hh'' := mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg T : (0 : ℝ) ≤ T)
    nlinarith
  apply (mul_le_mul_iff_of_pos_left
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (2 * (T : ℝ) * (i : ℝ)))).mp
  calc
    _ ≤ (2 : ℝ) ^ (2 * (T : ℝ) * (i : ℝ)) *
        ((2 : ℝ) ^ (κ * (T : ℝ) * (N : ℝ)) *
          ((2 : ℝ) ^ (κ * (T : ℝ) * (N : ℝ) + (T : ℝ) * (i : ℝ)) * (C.card : ℝ))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlargeC (by positivity)) (by positivity)
    _ = (2 : ℝ) ^ (2 * κ * (T : ℝ) * (N : ℝ) + 3 * (T : ℝ) * (i : ℝ)) * (C.card : ℝ) := by
      simp only [← mul_assoc]
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 2
      ring
    _ ≤ (2 : ℝ) ^ (α * (T : ℝ) * ((N - i : ℕ) : ℝ)) * (C.card : ℝ) :=
      mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp) (Nat.cast_nonneg _)
    _ ≤ _ := hgrowth.trans hlift

def natSignedResidueHull (E : Finset ℕ) (K q : ℕ) : Finset ℕ :=
  (natBoundedSums E K ×ˢ natBoundedSums E K).image
    (fun p => ((p.1 : ZMod q) - (p.2 : ZMod q)).val)

theorem quadratic_difference_signed_representation (A : Finset ℕ) (q : ℕ) :
    ∀ x ∈ natQuadraticSet (natDifferenceSet A),
      ∃ p ∈ natBoundedSums (natLinearQuadraticSet A) 2,
        ∃ n ∈ natBoundedSums (natLinearQuadraticSet A) 2,
          (x : ZMod q) = (p : ZMod q) - (n : ZMod q) := by
  intro x hx
  obtain ⟨⟨s, t⟩, hst, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨hs, ht⟩ := Finset.mem_product.mp hst
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hs
  obtain ⟨⟨c, d⟩, hcd, rfl⟩ := Finset.mem_image.mp ht
  obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
  obtain ⟨hc, hd⟩ := Finset.mem_product.mp hcd
  have hzero : 0 ∈ natBoundedSums (natLinearQuadraticSet A) 2 := zero_mem_nat_bounded_sums _ _
  by_cases hba : b ≤ a
  · by_cases hdc : d ≤ c
    · have hprod : ∀ u ∈ A, ∀ v ∈ A, u * v ∈ natBoundedSums (natLinearQuadraticSet A) 1 := by
        intro u hu v hv
        exact mem_nat_bounded_sums_one (Finset.mem_union_right A
          (Finset.mem_image.mpr ⟨(u, v), Finset.mem_product.mpr ⟨hu, hv⟩, rfl⟩))
      refine ⟨a * c + b * d, add_mem_nat_bounded_sums (hprod a ha c hc) (hprod b hb d hd),
        a * d + b * c, add_mem_nat_bounded_sums (hprod a ha d hd) (hprod b hb c hc), ?_⟩
      simp only [Nat.cast_mul, Nat.cast_sub hba, Nat.cast_sub hdc, Nat.cast_add]
      ring
    · refine ⟨0, hzero, 0, hzero, ?_⟩
      simp only [Nat.sub_eq_zero_of_le (by omega : c ≤ d), Nat.mul_zero, Nat.cast_zero, sub_self]
  · refine ⟨0, hzero, 0, hzero, ?_⟩
    simp only [Nat.sub_eq_zero_of_le (by omega : a ≤ b), Nat.zero_mul, Nat.cast_zero, sub_self]

theorem nat_bounded_sums_signed_representation {A E : Finset ℕ} {q K : ℕ}
    (hrep : ∀ a ∈ A, ∃ p ∈ natBoundedSums E K, ∃ n ∈ natBoundedSums E K,
      (a : ZMod q) = (p : ZMod q) - (n : ZMod q)) (s : ℕ) :
    ∀ x ∈ natBoundedSums A s, ∃ p ∈ natBoundedSums E (K * s),
      ∃ n ∈ natBoundedSums E (K * s), (x : ZMod q) = (p : ZMod q) - (n : ZMod q) := by
  induction s with
  | zero =>
    intro x hx
    have hx0 : x = 0 := Finset.mem_singleton.mp hx
    refine ⟨0, ?_, 0, ?_, ?_⟩
    · exact zero_mem_nat_bounded_sums _ _
    · exact zero_mem_nat_bounded_sums _ _
    · simp only [hx0, Nat.cast_zero, sub_self]
  | succ s ih =>
    intro x hx
    obtain ⟨⟨a, y⟩, hay, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨ha, hy⟩ := Finset.mem_product.mp hay
    have harep : ∃ p ∈ natBoundedSums E K, ∃ n ∈ natBoundedSums E K,
        (a : ZMod q) = (p : ZMod q) - (n : ZMod q) := by
      rcases Finset.mem_insert.mp ha with rfl | ha
      · exact ⟨0, zero_mem_nat_bounded_sums _ _, 0, zero_mem_nat_bounded_sums _ _, by simp⟩
      · exact hrep a ha
    obtain ⟨p, hp, n, hn, hapn⟩ := harep
    obtain ⟨p', hp', n', hn', hyrep⟩ := ih y hy
    have hindex : K * (s + 1) = K + K * s := by ring
    refine ⟨p + p', ?_, n + n', ?_, ?_⟩
    · rw [hindex]
      exact add_mem_nat_bounded_sums hp hp'
    · rw [hindex]
      exact add_mem_nat_bounded_sums hn hn'
    · simp only [Nat.cast_add, hapn, hyrep]
      ring

theorem mem_nat_signed_residue_hull {E : Finset ℕ} {K q x p n : ℕ} [NeZero q]
    (hp : p ∈ natBoundedSums E K) (hn : n ∈ natBoundedSums E K)
    (hrep : (x : ZMod q) = (p : ZMod q) - (n : ZMod q)) :
    x % q ∈ natSignedResidueHull E K q := by
  refine Finset.mem_image.mpr ⟨(p, n), Finset.mem_product.mpr ⟨hp, hn⟩, ?_⟩
  dsimp only
  rw [← hrep, ZMod.val_natCast]

theorem quadratic_difference_projection_subset_signed_hull (A : Finset ℕ) (K J : ℕ) :
    dyadicProjection (natBoundedSums (natQuadraticSet (natDifferenceSet A)) K) J ⊆
      natSignedResidueHull (natLinearQuadraticSet A) (2 * K + 2) (2 ^ J) := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨p, hp, n, hn, hrep⟩ := nat_bounded_sums_signed_representation
    (quadratic_difference_signed_representation A (2 ^ J)) K y hy
  exact mem_nat_signed_residue_hull (nat_bounded_sums_mono _ (by omega : 2 * K ≤ 2 * K + 2) hp)
    (nat_bounded_sums_mono _ (by omega : 2 * K ≤ 2 * K + 2) hn) hrep

theorem nat_sumset_subset_signed_linear_quadratic_hull (A : Finset ℕ) (K J : ℕ) :
    ((A ×ˢ A).image (fun p => (p.1 + p.2) % 2 ^ J)) ⊆
      natSignedResidueHull (natLinearQuadraticSet A) (2 * K + 2) (2 ^ J) := by
  intro x hx
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
  have hp : a + b ∈ natBoundedSums (natLinearQuadraticSet A) 2 :=
    add_mem_nat_bounded_sums (mem_nat_bounded_sums_one (Finset.mem_union_left _ ha))
      (mem_nat_bounded_sums_one (Finset.mem_union_left _ hb))
  exact mem_nat_signed_residue_hull (nat_bounded_sums_mono _ (by omega : 2 ≤ 2 * K + 2) hp)
    (zero_mem_nat_bounded_sums _ _) (by simp)

theorem exists_general_dyadic_signed_sum_product_growth {γ δ : ℝ}
    (hγ : 0 < γ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ κ ε : ℝ, 0 < κ ∧ 0 < ε ∧ ε ≤ 1 / 4 ∧
      ∃ T K N₀ : ℕ, 0 < T ∧ 0 < K ∧ ∀ N : ℕ, N₀ ≤ N →
        ∀ A : Finset ℕ, A.Nonempty → (∀ x ∈ A, x < 2 ^ (T * N)) →
        (A.card : ℝ) ≤ (2 : ℝ) ^ ((1 - δ) * (T : ℝ) * (N : ℝ)) →
        (∀ j : ℕ, j ≤ N → ε * (N : ℝ) < (j : ℝ) →
          (2 : ℝ) ^ (γ * (T : ℝ) * (j : ℝ)) ≤ ((dyadicProjection A (T * j)).card : ℝ)) →
        (2 : ℝ) ^ (κ * (T : ℝ) * (N : ℝ)) * (A.card : ℝ) ≤
          ((natSignedResidueHull (natLinearQuadraticSet A) K (2 ^ (T * N))).card : ℝ) := by
  obtain ⟨κ, ε, hκ, hε, hε4, T, K, N₀, hT, hK, hgrowth⟩ :=
    exists_general_dyadic_growth_dichotomy hγ hδ hδ1
  refine ⟨κ, ε, hκ, hε, hε4, T, 2 * K + 2, N₀, hT, by omega, ?_⟩
  intro N hN A hA hbound hsize hprojection
  rcases hgrowth N hN A hA hbound hsize hprojection with hsum | hquad
  · apply hsum.trans
    exact_mod_cast Finset.card_le_card (nat_sumset_subset_signed_linear_quadratic_hull A K (T * N))
  · apply hquad.trans
    exact_mod_cast Finset.card_le_card (quadratic_difference_projection_subset_signed_hull A K (T * N))

theorem dyadic_card_le_projection_mul {A : Finset ℕ} {b d : ℕ}
    (hbound : ∀ x ∈ A, x < 2 ^ (b + d)) :
    A.card ≤ 2 ^ d * (dyadicProjection A b).card := by
  rw [Finset.card_eq_sum_card_image (fun x => x % 2 ^ b) A]
  calc
    _ ≤ ∑ _r ∈ dyadicProjection A b, 2 ^ d :=
      Finset.sum_le_sum (fun r _ => dyadic_residue_fiber_card_le hbound r)
    _ = _ := by simp [Nat.mul_comm]

theorem dyadic_sub_val_mod {j m : ℕ} (hjm : j ≤ m) (a b : ℕ) :
    ((a : ZMod (2 ^ m)) - (b : ZMod (2 ^ m))).val % 2 ^ j =
      ((a : ZMod (2 ^ j)) - (b : ZMod (2 ^ j))).val := by
  let π : ZMod (2 ^ m) →+* ZMod (2 ^ j) := ZMod.castHom (pow_dvd_pow 2 hjm) _
  have heq : (((((a : ZMod (2 ^ m)) - (b : ZMod (2 ^ m))).val) : ℕ) : ZMod (2 ^ j)) =
      (a : ZMod (2 ^ j)) - (b : ZMod (2 ^ j)) := by
    calc
      _ = π ((a : ZMod (2 ^ m)) - (b : ZMod (2 ^ m))) := by
        rw [ZMod.castHom_apply, ZMod.cast_eq_val]
      _ = _ := by rw [map_sub, map_natCast, map_natCast]
  have hh := congrArg ZMod.val heq
  simpa only [ZMod.val_natCast] using hh

theorem dyadic_signed_hull_project (E : Finset ℕ) (K : ℕ) {j m : ℕ} (hjm : j ≤ m) :
    dyadicProjection (natSignedResidueHull E K (2 ^ m)) j = natSignedResidueHull E K (2 ^ j) := by
  unfold dyadicProjection natSignedResidueHull
  rw [Finset.image_image]
  apply Finset.image_congr
  intro p hp
  exact dyadic_sub_val_mod hjm p.1 p.2

theorem nat_signed_residue_hull_bounded (E : Finset ℕ) (K : ℕ) {q : ℕ} [NeZero q] :
    ∀ x ∈ natSignedResidueHull E K q, x < q := by
  intro x hx
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
  exact ZMod.val_lt _

theorem dyadic_signed_hull_card_le (E : Finset ℕ) (K : ℕ) {j m d : ℕ}
    (hjm : j ≤ m) (hmd : m ≤ j + d) :
    (natSignedResidueHull E K (2 ^ m)).card ≤ 2 ^ d * (natSignedResidueHull E K (2 ^ j)).card := by
  have hb : ∀ x ∈ natSignedResidueHull E K (2 ^ m), x < 2 ^ (j + d) := by
    intro x hx
    exact (nat_signed_residue_hull_bounded E K x hx).trans_le
      (Nat.pow_le_pow_right (by decide : 0 < 2) hmd)
  have hh := dyadic_card_le_projection_mul hb
  rwa [dyadic_signed_hull_project E K hjm] at hh

theorem exists_dyadic_signed_sum_product_growth {γ δ : ℝ}
    (hγ : 0 < γ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ κ ε : ℝ, 0 < κ ∧ 0 < ε ∧ ε ≤ 1 / 4 ∧
      ∃ K J₀ : ℕ, 0 < K ∧ ∀ J : ℕ, J₀ ≤ J → ∀ A : Finset ℕ,
        A.Nonempty → (∀ x ∈ A, x < 2 ^ J) →
        (A.card : ℝ) ≤ (2 : ℝ) ^ ((1 - δ) * (J : ℝ)) →
        (∀ j : ℕ, j ≤ J → ε * (J : ℝ) < (j : ℝ) →
          (2 : ℝ) ^ (γ * (j : ℝ)) ≤ ((dyadicProjection A j).card : ℝ)) →
        (2 : ℝ) ^ (κ * (J : ℝ)) * (A.card : ℝ) ≤
          ((natSignedResidueHull (natLinearQuadraticSet A) K (2 ^ J)).card : ℝ) := by
  obtain ⟨κ, ε, hκ, hε, hε4, T, K, N₀, hT, hK, hgrowth⟩ :=
    exists_general_dyadic_signed_sum_product_growth (show 0 < γ / 2 by positivity) hδ hδ1
  obtain ⟨J₀, hJ₀⟩ := exists_nat_ge (max (T : ℝ) (max ((T * N₀ : ℕ) : ℝ) (2 * (T : ℝ) / κ)))
  refine ⟨κ / 2, ε, by positivity, hε, hε4, K, J₀, hK, ?_⟩
  intro J hJ A hA hbound hsize hprojection
  have hJbound : max (T : ℝ) (max ((T * N₀ : ℕ) : ℝ) (2 * (T : ℝ) / κ)) ≤ J :=
    hJ₀.trans (by exact_mod_cast hJ)
  have hTJ : T ≤ J := by exact_mod_cast (le_max_left _ _).trans hJbound
  have hTNJ : T * N₀ ≤ J := by
    exact_mod_cast (le_max_left _ _).trans ((le_max_right _ _).trans hJbound)
  have hκJ : 2 * (T : ℝ) ≤ κ * (J : ℝ) := by
    have hh := (div_le_iff₀ hκ).mp ((le_max_right _ _).trans ((le_max_right _ _).trans hJbound))
    nlinarith
  let N := J / T + 1
  have hdecomp : J % T + T * (J / T) = J := Nat.mod_add_div J T
  have hrem : J % T < T := Nat.mod_lt J hT
  have hJm : J ≤ T * N := by dsimp only [N]; rw [Nat.mul_add, Nat.mul_one]; omega
  have hmJ : T * N ≤ J + T := by dsimp only [N]; rw [Nat.mul_add, Nat.mul_one]; omega
  have hm2J : T * N ≤ 2 * J := by omega
  have hN : N₀ ≤ N := by
    have hh : N₀ ≤ J / T := (Nat.le_div_iff_mul_le hT).mpr (by simpa only [Nat.mul_comm] using hTNJ)
    dsimp [N]
    omega
  have hJpos : (0 : ℝ) < J := by exact_mod_cast (lt_of_lt_of_le hT hTJ)
  have hεJ : ε * (J : ℝ) < J := by nlinarith
  have hfull : (2 : ℝ) ^ (γ * (J : ℝ)) ≤ (A.card : ℝ) := by
    simpa only [dyadic_projection_self hbound] using hprojection J le_rfl hεJ
  have hbound' : ∀ x ∈ A, x < 2 ^ (T * N) := fun x hx =>
    (hbound x hx).trans_le (Nat.pow_le_pow_right (by decide : 0 < 2) hJm)
  have hsize' : (A.card : ℝ) ≤ (2 : ℝ) ^ ((1 - δ) * (T : ℝ) * (N : ℝ)) := by
    apply hsize.trans
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hh := mul_le_mul_of_nonneg_left (show (J : ℝ) ≤ (T : ℝ) * (N : ℝ) by exact_mod_cast hJm)
      (show 0 ≤ 1 - δ by linarith)
    nlinarith
  have hprefix : ∀ j : ℕ, j ≤ N → ε * (N : ℝ) < (j : ℝ) →
      (2 : ℝ) ^ (γ / 2 * (T : ℝ) * (j : ℝ)) ≤ ((dyadicProjection A (T * j)).card : ℝ) := by
    intro j hj hεj
    by_cases hjJ : T * j ≤ J
    · have hlarge : ε * (J : ℝ) < ((T * j : ℕ) : ℝ) := by
        have hh := mul_lt_mul_of_pos_left hεj (show (0 : ℝ) < T by exact_mod_cast hT)
        have hh' := mul_le_mul_of_nonneg_left (show (J : ℝ) ≤ (T : ℝ) * (N : ℝ) by exact_mod_cast hJm) hε.le
        simp only [Nat.cast_mul]
        nlinarith
      apply (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) ?_).trans
        (hprojection (T * j) hjJ hlarge)
      simp only [Nat.cast_mul]
      nlinarith [mul_nonneg (mul_nonneg hγ.le (Nat.cast_nonneg T)) (Nat.cast_nonneg j)]
    · have hJtj : J ≤ T * j := by omega
      rw [dyadic_projection_self (fun x hx => (hbound x hx).trans_le
        (Nat.pow_le_pow_right (by decide : 0 < 2) hJtj))]
      apply (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) ?_).trans hfull
      have hle : (T : ℝ) * (j : ℝ) ≤ 2 * (J : ℝ) := by
        exact_mod_cast (Nat.mul_le_mul_left T hj).trans hm2J
      nlinarith [mul_le_mul_of_nonneg_left hle hγ.le]
  have hh := hgrowth N hN A hA hbound' hsize' hprefix
  have hreduce : ((natSignedResidueHull (natLinearQuadraticSet A) K (2 ^ (T * N))).card : ℝ) ≤
      (2 : ℝ) ^ T * ((natSignedResidueHull (natLinearQuadraticSet A) K (2 ^ J)).card : ℝ) := by
    exact_mod_cast dyadic_signed_hull_card_le (natLinearQuadraticSet A) K hJm hmJ
  apply (mul_le_mul_iff_of_pos_left (pow_pos (by norm_num : (0 : ℝ) < 2) T)).mp
  calc
    _ = (2 : ℝ) ^ ((T : ℝ) + κ / 2 * (J : ℝ)) * (A.card : ℝ) := by
      rw [Real.rpow_add (by norm_num), Real.rpow_natCast]; ring
    _ ≤ (2 : ℝ) ^ (κ * (T : ℝ) * (N : ℝ)) * (A.card : ℝ) := by
      apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have hm : (J : ℝ) ≤ (T : ℝ) * (N : ℝ) := by exact_mod_cast hJm
      nlinarith [mul_le_mul_of_nonneg_left hm hκ.le]
    _ ≤ _ := hh.trans hreduce

theorem one_le_projection_card_mul_mass {A : Finset ℕ} (hA : A.Nonempty) (j : ℕ) {M : ℝ}
    (hM : ∀ r : ℕ, natResidueMass A (2 ^ j) r ≤ M) :
    1 ≤ ((dyadicProjection A j).card : ℝ) * M := by
  have hAp : (0 : ℝ) < A.card := by exact_mod_cast Finset.card_pos.mpr hA
  have hfiber : ∀ r ∈ dyadicProjection A j,
      ((A.filter (fun x => x % 2 ^ j = r)).card : ℝ) ≤ M * (A.card : ℝ) := by
    intro r hr
    have hh := (div_le_iff₀ hAp).mp (hM r)
    simpa only [natResidueFiber, Nat.ModEq,
      Nat.mod_eq_of_lt (dyadic_projection_bounded A j r hr)] using hh
  have hcard : (A.card : ℝ) ≤ ((dyadicProjection A j).card : ℝ) * (M * (A.card : ℝ)) := by
    conv_lhs => rw [Finset.card_eq_sum_card_image (fun x => x % 2 ^ j) A, Nat.cast_sum]
    calc
      _ ≤ ∑ _r ∈ dyadicProjection A j, M * (A.card : ℝ) := Finset.sum_le_sum hfiber
      _ = _ := by simp
  apply (mul_le_mul_iff_of_pos_right hAp).mp
  simpa only [one_mul, mul_assoc] using hcard

theorem dyadic_projection_growth_of_mass {A : Finset ℕ} (hA : A.Nonempty) (j : ℕ) {γ : ℝ}
    (hM : ∀ r : ℕ, natResidueMass A (2 ^ j) r ≤ (2 : ℝ) ^ (-γ * (j : ℝ))) :
    (2 : ℝ) ^ (γ * (j : ℝ)) ≤ ((dyadicProjection A j).card : ℝ) := by
  have hh := one_le_projection_card_mul_mass hA j hM
  have hinv : (2 : ℝ) ^ (-γ * (j : ℝ)) * (2 : ℝ) ^ (γ * (j : ℝ)) = 1 := by
    rw [← Real.rpow_add (by norm_num), show -γ * (j : ℝ) + γ * (j : ℝ) = 0 by ring, Real.rpow_zero]
  calc
    _ = 1 * (2 : ℝ) ^ (γ * (j : ℝ)) := (one_mul _).symm
    _ ≤ (((dyadicProjection A j).card : ℝ) * (2 : ℝ) ^ (-γ * (j : ℝ))) *
        (2 : ℝ) ^ (γ * (j : ℝ)) := mul_le_mul_of_nonneg_right hh (by positivity)
    _ = _ := by rw [mul_assoc, hinv, mul_one]

theorem exists_dyadic_signed_sum_product_growth_of_mass {γ δ : ℝ}
    (hγ : 0 < γ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ κ ε : ℝ, 0 < κ ∧ 0 < ε ∧ ε ≤ 1 / 4 ∧
      ∃ K J₀ : ℕ, 0 < K ∧ ∀ J : ℕ, J₀ ≤ J → ∀ A : Finset ℕ,
        A.Nonempty → (∀ x ∈ A, x < 2 ^ J) →
        (A.card : ℝ) ≤ (2 : ℝ) ^ ((1 - δ) * (J : ℝ)) →
        (∀ j : ℕ, j ≤ J → ε * (J : ℝ) < (j : ℝ) → ∀ r : ℕ,
          natResidueMass A (2 ^ j) r ≤ (2 : ℝ) ^ (-γ * (j : ℝ))) →
        (2 : ℝ) ^ (κ * (J : ℝ)) * (A.card : ℝ) ≤
          ((natSignedResidueHull (natLinearQuadraticSet A) K (2 ^ J)).card : ℝ) := by
  obtain ⟨κ, ε, hκ, hε, hε4, K, J₀, hK, hgrowth⟩ := exists_dyadic_signed_sum_product_growth hγ hδ hδ1
  refine ⟨κ, ε, hκ, hε, hε4, K, J₀, hK, ?_⟩
  intro J hJ A hA hbound hsize hmass
  exact hgrowth J hJ A hA hbound hsize (fun j hj hεj =>
    dyadic_projection_growth_of_mass hA j (hmass j hj hεj))

open scoped Pointwise

def natResidueGenerators (E : Finset ℕ) (q : ℕ) : Finset (ZMod q) :=
  insert 0 (E.image (fun n : ℕ => (n : ZMod q)))

theorem nat_sumset_cast_image (A B : Finset ℕ) (q : ℕ) :
    (((A ×ˢ B).image (fun p => p.1 + p.2)).image (fun n : ℕ => (n : ZMod q))) =
      A.image (fun n : ℕ => (n : ZMod q)) + B.image (fun n : ℕ => (n : ZMod q)) := by
  ext z
  constructor
  · intro hz
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
    exact Finset.mem_add.mpr ⟨(a : ZMod q), Finset.mem_image_of_mem _ ha,
      (b : ZMod q), Finset.mem_image_of_mem _ hb, (Nat.cast_add a b).symm⟩
  · intro hz
    obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp hz
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_image.mpr ⟨a + b, Finset.mem_image.mpr
      ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, rfl⟩, Nat.cast_add a b⟩

theorem nat_bounded_sums_cast_image (E : Finset ℕ) (K q : ℕ) :
    (natBoundedSums E K).image (fun n : ℕ => (n : ZMod q)) = K • natResidueGenerators E q := by
  induction K with
  | zero =>
    simp only [natBoundedSums, Finset.image_singleton, Nat.cast_zero, zero_nsmul]
    rfl
  | succ K ih =>
    rw [natBoundedSums, nat_sumset_cast_image, ih, succ_nsmul']
    simp only [Finset.image_insert, Nat.cast_zero, natResidueGenerators]

theorem nat_signed_residue_hull_eq_image (E : Finset ℕ) (K q : ℕ) :
    natSignedResidueHull E K q =
      (K • natResidueGenerators E q - K • natResidueGenerators E q).image ZMod.val := by
  rw [← nat_bounded_sums_cast_image]
  ext z
  constructor
  · intro hz
    obtain ⟨⟨p, n⟩, hpn, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hp, hn⟩ := Finset.mem_product.mp hpn
    exact Finset.mem_image.mpr ⟨(p : ZMod q) - (n : ZMod q),
      Finset.mem_sub.mpr ⟨(p : ZMod q), Finset.mem_image_of_mem _ hp,
        (n : ZMod q), Finset.mem_image_of_mem _ hn, rfl⟩, rfl⟩
  · intro hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨p, hp, n, hn, rfl⟩ := Finset.mem_sub.mp hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hn
    exact Finset.mem_image.mpr ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, rfl⟩

theorem nat_signed_residue_hull_card (E : Finset ℕ) (K : ℕ) {q : ℕ} [NeZero q] :
    (natSignedResidueHull E K q).card =
      (K • natResidueGenerators E q - K • natResidueGenerators E q).card := by
  rw [nat_signed_residue_hull_eq_image, Finset.card_image_of_injective _ (ZMod.val_injective q)]

theorem nat_signed_hull_pluennecke_bound (E : Finset ℕ) (K : ℕ) {q : ℕ} [NeZero q] :
    ((natSignedResidueHull E K q).card : ℝ) ≤
      (((natResidueGenerators E q + natResidueGenerators E q).card : ℝ) /
        ((natResidueGenerators E q).card : ℝ)) ^ (2 * K) * ((natResidueGenerators E q).card : ℝ) := by
  have hF : (natResidueGenerators E q).Nonempty := ⟨0, Finset.mem_insert_self _ _⟩
  have hh := Finset.pluennecke_ruzsa_inequality_nsmul_sub_nsmul_add hF (natResidueGenerators E q) K K
  have hhR : ((K • natResidueGenerators E q - K • natResidueGenerators E q).card : ℝ) ≤
      (((natResidueGenerators E q + natResidueGenerators E q).card : ℝ) /
        ((natResidueGenerators E q).card : ℝ)) ^ (K + K) * ((natResidueGenerators E q).card : ℝ) := by
    have hhQ : ((K • natResidueGenerators E q - K • natResidueGenerators E q).card : ℚ) ≤
        (((natResidueGenerators E q + natResidueGenerators E q).card : ℚ) /
          ((natResidueGenerators E q).card : ℚ)) ^ (K + K) * ((natResidueGenerators E q).card : ℚ) := by
      exact_mod_cast (NNRat.coe_mono hh)
    have hhCast := (Rat.cast_le (K := ℝ)).mpr hhQ
    push_cast at hhCast
    exact hhCast
  simpa only [nat_signed_residue_hull_card, two_mul] using hhR

theorem nat_linear_quadratic_generators_card_ge {A : Finset ℕ} {q : ℕ} [NeZero q]
    (hbound : ∀ x ∈ A, x < q) :
    A.card ≤ (natResidueGenerators (natLinearQuadraticSet A) q).card := by
  have hinj : Set.InjOn (fun n : ℕ => (n : ZMod q)) A := by
    intro x hx y hy hxy
    have hh := congrArg ZMod.val hxy
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt (hbound x hx), Nat.mod_eq_of_lt (hbound y hy)] using hh
  calc
    _ = (A.image (fun n : ℕ => (n : ZMod q))).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ _ := Finset.card_le_card (by
      intro x hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_union_left _ ha)))

theorem nat_signed_hull_bound_of_double_bound (E : Finset ℕ) (K : ℕ) {q : ℕ} [NeZero q]
    {a L : ℝ} (ha : a ≤ ((natResidueGenerators E q).card : ℝ)) (hL : 0 ≤ L)
    (hdouble : ((natResidueGenerators E q + natResidueGenerators E q).card : ℝ) ≤ L * a) :
    ((natSignedResidueHull E K q).card : ℝ) ≤ L ^ (2 * K + 1) * a := by
  let F := natResidueGenerators E q
  have hF : F.Nonempty := ⟨0, Finset.mem_insert_self _ _⟩
  have hFp : (0 : ℝ) < F.card := by exact_mod_cast Finset.card_pos.mpr hF
  have hsub : F ⊆ F + F := by
    intro x hx
    exact Finset.mem_add.mpr ⟨x, hx, 0, Finset.mem_insert_self _ _, add_zero x⟩
  have hsize : (F.card : ℝ) ≤ L * a := (show (F.card : ℝ) ≤ (F + F).card by
    exact_mod_cast Finset.card_le_card hsub).trans hdouble
  have hratio : ((F + F).card : ℝ) / (F.card : ℝ) ≤ L :=
    (div_le_iff₀ hFp).mpr (hdouble.trans (mul_le_mul_of_nonneg_left ha hL))
  have hratio0 : 0 ≤ ((F + F).card : ℝ) / (F.card : ℝ) := by positivity
  calc
    _ ≤ (((F + F).card : ℝ) / (F.card : ℝ)) ^ (2 * K) * (F.card : ℝ) :=
      nat_signed_hull_pluennecke_bound E K
    _ ≤ L ^ (2 * K) * (F.card : ℝ) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hratio0 hratio _) hFp.le
    _ ≤ L ^ (2 * K) * (L * a) := mul_le_mul_of_nonneg_left hsize (pow_nonneg hL _)
    _ = _ := by rw [pow_succ]; ring

theorem exists_dyadic_sum_product_double_growth {γ δ : ℝ}
    (hγ : 0 < γ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ σ ε : ℝ, 0 < σ ∧ 0 < ε ∧ ε ≤ 1 / 4 ∧ ∃ J₀ : ℕ,
      ∀ J : ℕ, J₀ ≤ J → ∀ A : Finset ℕ,
        A.Nonempty → (∀ x ∈ A, x < 2 ^ J) →
        (A.card : ℝ) ≤ (2 : ℝ) ^ ((1 - δ) * (J : ℝ)) →
        (∀ j : ℕ, j ≤ J → ε * (J : ℝ) < (j : ℝ) → ∀ r : ℕ,
          natResidueMass A (2 ^ j) r ≤ (2 : ℝ) ^ (-γ * (j : ℝ))) →
        (2 : ℝ) ^ (σ * (J : ℝ)) * (A.card : ℝ) ≤
          ((natResidueGenerators (natLinearQuadraticSet A) (2 ^ J) +
            natResidueGenerators (natLinearQuadraticSet A) (2 ^ J)).card : ℝ) := by
  obtain ⟨κ, ε, hκ, hε, hε4, K, J₀, hK, hgrowth⟩ :=
    exists_dyadic_signed_sum_product_growth_of_mass hγ hδ hδ1
  let σ := κ / (4 * (K : ℝ) + 2)
  have hden : 0 < 4 * (K : ℝ) + 2 := by positivity
  have hσ : 0 < σ := div_pos hκ hden
  have hexp : σ * ((2 * K + 1 : ℕ) : ℝ) = κ / 2 := by
    dsimp [σ]
    push_cast
    field_simp
    ring
  refine ⟨σ, ε, hσ, hε, hε4, max J₀ 1, ?_⟩
  intro J hJ A hA hbound hsize hmass
  have hJ₀ : J₀ ≤ J := (le_max_left _ _).trans hJ
  have hJ1 : 1 ≤ J := (le_max_right _ _).trans hJ
  have hJp : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  have hAp : (0 : ℝ) < A.card := by exact_mod_cast Finset.card_pos.mpr hA
  by_contra h
  have hupper := nat_signed_hull_bound_of_double_bound (natLinearQuadraticSet A) K
    (q := 2 ^ J) (by exact_mod_cast nat_linear_quadratic_generators_card_ge hbound)
    (show 0 ≤ (2 : ℝ) ^ (σ * (J : ℝ)) by positivity) (lt_of_not_ge h).le
  have hpowlt : ((2 : ℝ) ^ (σ * (J : ℝ))) ^ (2 * K + 1) < (2 : ℝ) ^ (κ * (J : ℝ)) := by
    rw [← Real.rpow_mul_natCast (by norm_num)]
    apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num)
    have hEq : σ * (J : ℝ) * ((2 * K + 1 : ℕ) : ℝ) = κ / 2 * (J : ℝ) := by
      rw [mul_right_comm, hexp]
    rw [hEq]
    nlinarith [mul_pos hκ hJp]
  exact (not_lt_of_ge (hgrowth J hJ₀ A hA hbound hsize hmass))
    (hupper.trans_lt (mul_lt_mul_of_pos_right hpowlt hAp))

theorem nat_productset_cast_image (A B : Finset ℕ) (q : ℕ) :
    (((A ×ˢ B).image (fun p => p.1 * p.2)).image (fun n : ℕ => (n : ZMod q))) =
      A.image (fun n : ℕ => (n : ZMod q)) * B.image (fun n : ℕ => (n : ZMod q)) := by
  ext z
  constructor
  · intro hz
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
    exact Finset.mem_mul.mpr ⟨(a : ZMod q), Finset.mem_image_of_mem _ ha,
      (b : ZMod q), Finset.mem_image_of_mem _ hb, (Nat.cast_mul a b).symm⟩
  · intro hz
    obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_mul.mp hz
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_image.mpr ⟨a * b, Finset.mem_image.mpr
      ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, rfl⟩, Nat.cast_mul a b⟩

theorem nat_linear_quadratic_residue_generators (A : Finset ℕ) (q : ℕ) :
    natResidueGenerators (natLinearQuadraticSet A) q =
      insert 0 (A.image (fun n : ℕ => (n : ZMod q)) ∪
        A.image (fun n : ℕ => (n : ZMod q)) * A.image (fun n : ℕ => (n : ZMod q))) := by
  unfold natResidueGenerators natLinearQuadraticSet
  rw [Finset.image_union, nat_productset_cast_image]

theorem dyadic_projection_cast_image (A : Finset ℕ) (J : ℕ) :
    (dyadicProjection A J).image (fun n : ℕ => (n : ZMod (2 ^ J))) =
      A.image (fun n : ℕ => (n : ZMod (2 ^ J))) := by
  unfold dyadicProjection
  rw [Finset.image_image]
  apply Finset.image_congr
  intro n hn
  exact (ZMod.natCast_eq_natCast_iff' _ _ _).mpr (Nat.mod_mod n _)

theorem dyadic_projection_card_of_cast_inj {A : Finset ℕ} {J : ℕ}
    (hinj : Set.InjOn (fun n : ℕ => (n : ZMod (2 ^ J))) A) :
    (dyadicProjection A J).card = A.card := by
  apply Finset.card_image_of_injOn
  intro a ha b hb hab
  exact hinj ha hb ((ZMod.natCast_eq_natCast_iff' _ _ _).mpr hab)

theorem nat_residue_mass_dyadic_projection {A : Finset ℕ} {J j : ℕ}
    (hinj : Set.InjOn (fun n : ℕ => (n : ZMod (2 ^ J))) A) (hj : j ≤ J) (r : ℕ) :
    natResidueMass (dyadicProjection A J) (2 ^ j) r = natResidueMass A (2 ^ j) r := by
  have heq : natResidueFiber (dyadicProjection A J) (2 ^ j) r =
      (natResidueFiber A (2 ^ j) r).image (fun n => n % 2 ^ J) := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxP, hxr⟩ := Finset.mem_filter.mp hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hxP
      have har : Nat.ModEq (2 ^ j) a r := by
        simpa only [Nat.ModEq, Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 hj)] using hxr
      exact Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, har⟩, rfl⟩
    · intro hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨haA, har⟩ := Finset.mem_filter.mp ha
      refine Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ haA, ?_⟩
      simpa only [Nat.ModEq, Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 hj)] using har
  have hi : Set.InjOn (fun n : ℕ => n % 2 ^ J) (natResidueFiber A (2 ^ j) r) := by
    intro a ha b hb hab
    exact hinj (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1
      ((ZMod.natCast_eq_natCast_iff' _ _ _).mpr hab)
  unfold natResidueMass
  rw [heq, Finset.card_image_of_injOn hi, dyadic_projection_card_of_cast_inj hinj]

theorem dyadic_linear_quadratic_generators_projection (A : Finset ℕ) (J : ℕ) :
    natResidueGenerators (natLinearQuadraticSet (dyadicProjection A J)) (2 ^ J) =
      natResidueGenerators (natLinearQuadraticSet A) (2 ^ J) := by
  rw [nat_linear_quadratic_residue_generators, nat_linear_quadratic_residue_generators,
    dyadic_projection_cast_image]

theorem exists_dyadic_sum_product_double_growth_injective {γ δ : ℝ}
    (hγ : 0 < γ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ σ ε : ℝ, 0 < σ ∧ 0 < ε ∧ ε ≤ 1 / 4 ∧ ∃ J₀ : ℕ,
      ∀ J : ℕ, J₀ ≤ J → ∀ A : Finset ℕ, A.Nonempty →
        Set.InjOn (fun n : ℕ => (n : ZMod (2 ^ J))) A →
        (A.card : ℝ) ≤ (2 : ℝ) ^ ((1 - δ) * (J : ℝ)) →
        (∀ j : ℕ, j ≤ J → ε * (J : ℝ) < (j : ℝ) → ∀ r : ℕ,
          natResidueMass A (2 ^ j) r ≤ (2 : ℝ) ^ (-γ * (j : ℝ))) →
        (2 : ℝ) ^ (σ * (J : ℝ)) * (A.card : ℝ) ≤
          ((natResidueGenerators (natLinearQuadraticSet A) (2 ^ J) +
            natResidueGenerators (natLinearQuadraticSet A) (2 ^ J)).card : ℝ) := by
  obtain ⟨σ, ε, hσ, hε, hε4, J₀, hgrowth⟩ := exists_dyadic_sum_product_double_growth hγ hδ hδ1
  refine ⟨σ, ε, hσ, hε, hε4, J₀, ?_⟩
  intro J hJ A hA hinj hsize hmass
  have hh := hgrowth J hJ (dyadicProjection A J) (hA.image _) (dyadic_projection_bounded A J)
    (by simpa only [dyadic_projection_card_of_cast_inj hinj] using hsize)
    (fun j hj hεj r => by rw [nat_residue_mass_dyadic_projection hinj hj]; exact hmass j hj hεj r)
  simpa only [dyadic_projection_card_of_cast_inj hinj, dyadic_linear_quadratic_generators_projection] using hh

theorem dyadic_large_subset_mass {A B : Finset ℕ} {J j : ℕ} {γ ε τ : ℝ}
    (hBA : B ⊆ A) (hB : B.Nonempty) (hγ : 0 < γ) (hτ : τ ≤ γ * ε / 2)
    (hlarge : (A.card : ℝ) ≤ (2 : ℝ) ^ (τ * (J : ℝ)) * (B.card : ℝ))
    (hj : ε * (J : ℝ) < (j : ℝ))
    (hmass : ∀ r : ℕ, natResidueMass A (2 ^ j) r ≤ (2 : ℝ) ^ (-γ * (j : ℝ))) :
    ∀ r : ℕ, natResidueMass B (2 ^ j) r ≤ (2 : ℝ) ^ (-(γ / 2) * (j : ℝ)) := by
  intro r
  calc
    _ ≤ (2 : ℝ) ^ (τ * (J : ℝ)) * natResidueMass A (2 ^ j) r :=
      nat_residue_mass_subset_le hBA hB hlarge _ _
    _ ≤ (2 : ℝ) ^ (τ * (J : ℝ)) * (2 : ℝ) ^ (-γ * (j : ℝ)) :=
      mul_le_mul_of_nonneg_left (hmass r) (by positivity)
    _ = (2 : ℝ) ^ (τ * (J : ℝ) - γ * (j : ℝ)) := by
      rw [← Real.rpow_add (by norm_num)]
      congr 1
      ring
    _ ≤ _ := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have hh := mul_le_mul_of_nonneg_right hτ (Nat.cast_nonneg J : (0 : ℝ) ≤ J)
      have hh' := mul_lt_mul_of_pos_left hj hγ
      nlinarith

theorem exists_hereditary_dyadic_sum_product_growth {γ δ : ℝ}
    (hγ : 0 < γ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ σ ε τ : ℝ, 0 < σ ∧ 0 < ε ∧ ε ≤ 1 / 4 ∧ 0 < τ ∧ ∃ J₀ : ℕ,
      ∀ J : ℕ, J₀ ≤ J → ∀ A B : Finset ℕ,
        B ⊆ A → B.Nonempty → Set.InjOn (fun n : ℕ => (n : ZMod (2 ^ J))) A →
        (A.card : ℝ) ≤ (2 : ℝ) ^ ((1 - δ) * (J : ℝ)) →
        (A.card : ℝ) ≤ (2 : ℝ) ^ (τ * (J : ℝ)) * (B.card : ℝ) →
        (∀ j : ℕ, j ≤ J → ε * (J : ℝ) < (j : ℝ) → ∀ r : ℕ,
          natResidueMass A (2 ^ j) r ≤ (2 : ℝ) ^ (-γ * (j : ℝ))) →
        (2 : ℝ) ^ (σ * (J : ℝ)) * (B.card : ℝ) ≤
          ((natResidueGenerators (natLinearQuadraticSet B) (2 ^ J) +
            natResidueGenerators (natLinearQuadraticSet B) (2 ^ J)).card : ℝ) := by
  obtain ⟨σ, ε, hσ, hε, hε4, J₀, hgrowth⟩ :=
    exists_dyadic_sum_product_double_growth_injective (show 0 < γ / 2 by positivity) hδ hδ1
  refine ⟨σ, ε, γ * ε / 4, hσ, hε, hε4, by positivity, J₀, ?_⟩
  intro J hJ A B hBA hB hinj hsize hlarge hmass
  apply hgrowth J hJ B hB (hinj.mono hBA)
  · exact (show (B.card : ℝ) ≤ A.card by exact_mod_cast Finset.card_le_card hBA).trans hsize
  · intro j hj hεj
    exact dyadic_large_subset_mass hBA hB hγ (by nlinarith [mul_pos hγ hε]) hlarge hεj (hmass j hj hεj)

/- Quantitative inverse energy via weighted translate selection and common-neighbor counting. -/

open scoped BigOperators Pointwise

section FiniteInverseEnergy
variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

def finiteDifferenceFiber (A B : Finset G) (x : G) : Finset (G × G) :=
  (A ×ˢ B).filter (fun p => p.1 - p.2 = x)

def finiteDifferenceCount (A B : Finset G) (x : G) : ℕ :=
  (finiteDifferenceFiber A B x).card

def finiteDifferenceEnergy (A B : Finset G) : ℕ :=
  ∑ x : G, finiteDifferenceCount A B x ^ 2

def finiteShiftOverlap (A B : Finset G) (s : G) : Finset G :=
  A.filter (fun a => a - s ∈ B)

theorem finite_difference_count_eq_overlap (A B : Finset G) (s : G) :
    finiteDifferenceCount A B s = (finiteShiftOverlap A B s).card := by
  unfold finiteDifferenceCount finiteDifferenceFiber finiteShiftOverlap
  apply Finset.card_bij (fun p _ => p.1)
  · rintro ⟨a, b⟩ hp
    obtain ⟨⟨ha, hb⟩, hs⟩ := by simpa only [Finset.mem_filter, Finset.mem_product] using hp
    refine Finset.mem_filter.mpr ⟨ha, ?_⟩
    rw [← hs, sub_sub_cancel]
    exact hb
  · intro p hp q hq hpq
    apply Prod.ext hpq
    have hh := (Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm
    simpa only [hpq, sub_right_inj] using hh
  · intro a ha
    obtain ⟨haA, haB⟩ := Finset.mem_filter.mp ha
    exact ⟨(a, a - s), Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨haA, haB⟩, sub_sub_cancel a s⟩, rfl⟩

theorem finite_difference_count_le_right (A B : Finset G) (s : G) :
    finiteDifferenceCount A B s ≤ B.card := by
  apply Finset.card_le_card_of_injOn (fun p => p.2)
  · intro p hp
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).2
  · intro p hp q hq hpq
    apply Prod.ext ?_ hpq
    have hh := (Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm
    simpa only [hpq, sub_left_inj] using hh

theorem finite_difference_count_sum (A B : Finset G) :
    ∑ s : G, finiteDifferenceCount A B s = A.card * B.card := by
  unfold finiteDifferenceCount finiteDifferenceFiber
  rw [← Finset.card_product]
  exact (Finset.card_eq_sum_card_fiberwise (f := fun p : G × G => p.1 - p.2)
    (t := Finset.univ) (fun _ _ => Finset.mem_univ _)).symm

theorem finite_difference_count_sum_real (A B : Finset G) :
    ∑ s : G, (finiteDifferenceCount A B s : ℝ) = (A.card : ℝ) * (B.card : ℝ) := by
  exact_mod_cast finite_difference_count_sum A B

theorem finite_difference_energy_sum_real (A B : Finset G) :
    ∑ s : G, (finiteDifferenceCount A B s : ℝ) ^ 2 = (finiteDifferenceEnergy A B : ℝ) := by
  unfold finiteDifferenceEnergy
  push_cast
  rfl

theorem finite_difference_cubic_moment (A B : Finset G) :
    (finiteDifferenceEnergy A B : ℝ) ^ 2 ≤
      ((A.card : ℝ) * (B.card : ℝ)) * ∑ s : G, (finiteDifferenceCount A B s : ℝ) ^ 3 := by
  let r := fun s => (finiteDifferenceCount A B s : ℝ)
  let f := fun s => Real.sqrt (r s)
  have hf (s : G) : f s ^ 2 = r s := Real.sq_sqrt (Nat.cast_nonneg _)
  have h₁ : ∑ s : G, f s ^ 2 = (A.card : ℝ) * (B.card : ℝ) := by
    simp_rw [hf]
    exact finite_difference_count_sum_real A B
  have h₂ : ∑ s : G, f s * (f s * r s) = (finiteDifferenceEnergy A B : ℝ) := by
    calc
      _ = ∑ s : G, r s ^ 2 := Finset.sum_congr rfl (fun s _ => by
        calc _ = f s ^ 2 * r s := by ring
             _ = r s ^ 2 := by rw [hf]; ring)
      _ = _ := finite_difference_energy_sum_real A B
  have h₃ : ∑ s : G, (f s * r s) ^ 2 = ∑ s : G, r s ^ 3 := by
    apply Finset.sum_congr rfl
    intro s hs
    rw [mul_pow, hf]
    ring
  have hh := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f (fun s => f s * r s)
  rwa [h₁, h₂, h₃] at hh

theorem finite_common_shift_count (B : Finset G) (a b : G) :
    (Finset.univ.filter (fun s : G => a - s ∈ B ∧ b - s ∈ B)).card =
      finiteDifferenceCount B B (a - b) := by
  unfold finiteDifferenceCount finiteDifferenceFiber
  apply Finset.card_bij (fun s _ => (a - s, b - s))
  · intro s hs
    obtain ⟨ha, hb⟩ := (Finset.mem_filter.mp hs).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩, sub_sub_sub_cancel_right a b s⟩
  · intro s hs t ht hst
    simpa only [Prod.mk.injEq, sub_right_inj, and_self] using hst
  · rintro ⟨c, d⟩ hp
    obtain ⟨⟨hc, hd⟩, hcd⟩ := by simpa only [Finset.mem_filter, Finset.mem_product] using hp
    have heq : b - (a - c) = d := by
      rw [(sub_eq_iff_eq_add).mp hcd]
      abel
    refine ⟨a - c, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · simpa only [sub_sub_cancel, heq] using And.intro hc hd
    · simp only [sub_sub_cancel, heq]

def finiteShiftPairCount (B : Finset G) (H : Finset (G × G)) (s : G) : ℕ :=
  (H.filter (fun p => p.1 - s ∈ B ∧ p.2 - s ∈ B)).card

theorem finite_shift_pair_count_sum (B : Finset G) (H : Finset (G × G)) :
    ∑ s : G, finiteShiftPairCount B H s =
      ∑ p ∈ H, finiteDifferenceCount B B (p.1 - p.2) := by
  unfold finiteShiftPairCount
  simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  simpa only [Finset.card_eq_sum_ones, Finset.sum_filter] using finite_common_shift_count B p.1 p.2

theorem finite_weighted_shift_pair_bound (A B : Finset G) (H : Finset (G × G)) :
    ∑ s : G, (finiteDifferenceCount A B s : ℝ) * (finiteShiftPairCount B H s : ℝ) ≤
      (B.card : ℝ) * ∑ p ∈ H, (finiteDifferenceCount B B (p.1 - p.2) : ℝ) := by
  calc
    _ ≤ ∑ s : G, (B.card : ℝ) * (finiteShiftPairCount B H s : ℝ) := by
      apply Finset.sum_le_sum
      intro s hs
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast finite_difference_count_le_right A B s)
        (Nat.cast_nonneg _)
    _ = _ := by
      rw [← Finset.mul_sum]
      congr 1
      exact_mod_cast finite_shift_pair_count_sum B H

theorem finite_difference_energy_eq_card (A B : Finset G) :
    finiteDifferenceEnergy A B =
      (((A ×ˢ B) ×ˢ (A ×ˢ B)).filter
        (fun p => p.1.1 - p.1.2 = p.2.1 - p.2.2)).card := by
  let Q := (((A ×ˢ B) ×ˢ (A ×ˢ B)).filter
    (fun p => p.1.1 - p.1.2 = p.2.1 - p.2.2))
  have hf (x : G) : Q.filter (fun p => p.1.1 - p.1.2 = x) =
      finiteDifferenceFiber A B x ×ˢ finiteDifferenceFiber A B x := by
    ext p
    simp only [Q, finiteDifferenceFiber, Finset.mem_filter, Finset.mem_product]
    aesop
  calc
    _ = ∑ x : G, (finiteDifferenceFiber A B x ×ˢ finiteDifferenceFiber A B x).card := by
      simp only [finiteDifferenceEnergy, finiteDifferenceCount, Finset.card_product, pow_two]
    _ = ∑ x : G, (Q.filter (fun p => p.1.1 - p.1.2 = x)).card := by simp only [hf]
    _ = Q.card := (Finset.card_eq_sum_card_fiberwise
      (f := fun p : (G × G) × (G × G) => p.1.1 - p.1.2)
      (t := Finset.univ) (fun _ _ => Finset.mem_univ _)).symm

theorem finite_difference_energy_eq_addEnergy (A B : Finset G) :
    finiteDifferenceEnergy A B = Finset.addEnergy A B := by
  rw [finite_difference_energy_eq_card]
  unfold Finset.addEnergy
  apply Finset.card_bij (fun p _ => ((p.1.1, p.2.1), (p.2.2, p.1.2)))
  · intro p hp
    simpa only [Finset.mem_filter, Finset.mem_product, sub_eq_sub_iff_add_eq_add, and_assoc] using
      (show (p.1.1 ∈ A ∧ p.2.1 ∈ A) ∧ (p.2.2 ∈ B ∧ p.1.2 ∈ B) ∧
          p.1.1 - p.1.2 = p.2.1 - p.2.2 from by
        simpa only [Finset.mem_filter, Finset.mem_product, and_assoc, and_left_comm, and_comm] using hp)
  · intro p hp q hq hpq
    aesop
  · intro p hp
    refine ⟨((p.1.1, p.2.2), (p.1.2, p.2.1)), ?_, by simp⟩
    simpa only [Finset.mem_filter, Finset.mem_product, sub_eq_sub_iff_add_eq_add,
      and_assoc, and_left_comm, and_comm] using hp

theorem finite_energy_lower_cubic {A B : Finset G} {K : ℝ}
    (hA : A.Nonempty) (hB : B.Nonempty) (hK : 0 ≤ K)
    (hE : (A.card : ℝ) ^ 2 * (B.card : ℝ) ≤ K * (finiteDifferenceEnergy A B : ℝ)) :
    (A.card : ℝ) ^ 3 * (B.card : ℝ) ≤
      K ^ 2 * ∑ s : G, (finiteDifferenceCount A B s : ℝ) ^ 3 := by
  have hAp : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have hBp : (0 : ℝ) < B.card := by exact_mod_cast hB.card_pos
  have hsq := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (A.card : ℝ) ^ 2 * B.card) hE 2
  have hmoment := mul_le_mul_of_nonneg_left (finite_difference_cubic_moment A B)
    (sq_nonneg K)
  apply (mul_le_mul_iff_left₀ (mul_pos hAp hBp)).mp
  calc
    _ = ((A.card : ℝ) ^ 2 * (B.card : ℝ)) ^ 2 := by ring
    _ ≤ (K * (finiteDifferenceEnergy A B : ℝ)) ^ 2 := hsq
    _ = K ^ 2 * (finiteDifferenceEnergy A B : ℝ) ^ 2 := mul_pow _ _ _
    _ ≤ _ := hmoment
    _ = _ := by ring

theorem finite_weighted_bad_pair_bound {A B : Finset G} {H : Finset (G × G)} {K : ℝ}
    (hH : H ⊆ A ×ˢ A)
    (hbad : ∀ p ∈ H, 16 * K ^ 2 * (finiteDifferenceCount B B (p.1 - p.2) : ℝ) ≤ A.card) :
    16 * K ^ 2 *
        (∑ s : G, (finiteDifferenceCount A B s : ℝ) * (finiteShiftPairCount B H s : ℝ)) ≤
      (A.card : ℝ) ^ 3 * (B.card : ℝ) := by
  have hcard : (H.card : ℝ) ≤ (A.card : ℝ) ^ 2 := by
    exact_mod_cast (Finset.card_le_card hH).trans_eq (by simp [pow_two])
  calc
    _ ≤ 16 * K ^ 2 * ((B.card : ℝ) * ∑ p ∈ H,
        (finiteDifferenceCount B B (p.1 - p.2) : ℝ)) :=
      mul_le_mul_of_nonneg_left (finite_weighted_shift_pair_bound A B H) (by positivity)
    _ = (B.card : ℝ) * ∑ p ∈ H, 16 * K ^ 2 * (finiteDifferenceCount B B (p.1 - p.2) : ℝ) := by
      rw [← Finset.mul_sum]
      ring
    _ ≤ (B.card : ℝ) * ∑ _p ∈ H, (A.card : ℝ) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hbad) (Nat.cast_nonneg _)
    _ = (B.card : ℝ) * ((H.card : ℝ) * (A.card : ℝ)) := by simp
    _ ≤ (B.card : ℝ) * ((A.card : ℝ) ^ 2 * (A.card : ℝ)) := by gcongr
    _ = _ := by ring

theorem finite_exists_good_shift {A B : Finset G} {H : Finset (G × G)} {K : ℝ}
    (hA : A.Nonempty) (hB : B.Nonempty) (hK : 0 ≤ K)
    (hE : (A.card : ℝ) ^ 2 * (B.card : ℝ) ≤ K * (finiteDifferenceEnergy A B : ℝ))
    (hH : H ⊆ A ×ˢ A)
    (hbad : ∀ p ∈ H, 16 * K ^ 2 * (finiteDifferenceCount B B (p.1 - p.2) : ℝ) ≤ A.card) :
    ∃ s : G, (A.card : ℝ) ^ 2 + 16 * K ^ 2 * (finiteShiftPairCount B H s : ℝ) ≤
      2 * K ^ 2 * ((finiteShiftOverlap A B s).card : ℝ) ^ 2 := by
  have htotal :
      (∑ s : G, (finiteDifferenceCount A B s : ℝ) *
        ((A.card : ℝ) ^ 2 + 16 * K ^ 2 * (finiteShiftPairCount B H s : ℝ))) ≤
      ∑ s : G, (finiteDifferenceCount A B s : ℝ) *
        (2 * K ^ 2 * ((finiteShiftOverlap A B s).card : ℝ) ^ 2) := by
    calc
      _ = (A.card : ℝ) ^ 3 * (B.card : ℝ) + 16 * K ^ 2 *
          (∑ s : G, (finiteDifferenceCount A B s : ℝ) * (finiteShiftPairCount B H s : ℝ)) := by
        simp only [mul_add, Finset.sum_add_distrib]
        rw [← Finset.sum_mul, finite_difference_count_sum_real]
        have heq : (∑ s : G, (finiteDifferenceCount A B s : ℝ) *
            (16 * K ^ 2 * (finiteShiftPairCount B H s : ℝ))) =
            16 * K ^ 2 * ∑ s : G, (finiteDifferenceCount A B s : ℝ) * (finiteShiftPairCount B H s : ℝ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro s hs
          ring
        rw [heq]
        ring
      _ ≤ 2 * ((A.card : ℝ) ^ 3 * (B.card : ℝ)) := by
        linarith [finite_weighted_bad_pair_bound hH hbad]
      _ ≤ 2 * (K ^ 2 * ∑ s : G, (finiteDifferenceCount A B s : ℝ) ^ 3) :=
        mul_le_mul_of_nonneg_left (finite_energy_lower_cubic hA hB hK hE) (by norm_num)
      _ = _ := by
        rw [← mul_assoc, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s hs
        rw [← finite_difference_count_eq_overlap]
        ring
  by_contra! hn
  apply not_lt_of_ge htotal
  apply Finset.sum_lt_sum
  · intro s hs
    exact mul_le_mul_of_nonneg_left (hn s).le (Nat.cast_nonneg _)
  · obtain ⟨a, ha⟩ := hA
    obtain ⟨b, hb⟩ := hB
    have hpos : (0 : ℝ) < finiteDifferenceCount A B (a - b) := by
      exact_mod_cast (Finset.card_pos.mpr
        ⟨(a, b), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩, rfl⟩⟩ :
          0 < (finiteDifferenceFiber A B (a - b)).card)
    exact ⟨a - b, Finset.mem_univ _, mul_lt_mul_of_pos_left (hn _) hpos⟩

theorem finite_energy_dense_overlap {A B : Finset G} {K : ℝ}
    (hA : A.Nonempty) (hB : B.Nonempty) (hK : 0 < K)
    (hE : (A.card : ℝ) ^ 2 * (B.card : ℝ) ≤ K * (Finset.addEnergy A B : ℝ)) :
    ∃ s : G, (A.card : ℝ) / (2 * K) ≤ ((finiteShiftOverlap A B s).card : ℝ) ∧
      (7 / 8 : ℝ) * ((finiteShiftOverlap A B s).card : ℝ) ^ 2 ≤
        (((finiteShiftOverlap A B s ×ˢ finiteShiftOverlap A B s).filter
          (fun p => (A.card : ℝ) ≤ 16 * K ^ 2 *
            (finiteDifferenceCount B B (p.1 - p.2) : ℝ))).card : ℝ) := by
  classical
  let P := fun p : G × G => (A.card : ℝ) ≤
    16 * K ^ 2 * (finiteDifferenceCount B B (p.1 - p.2) : ℝ)
  let H := (A ×ˢ A).filter (fun p => ¬ P p)
  have hbad : ∀ p ∈ H, 16 * K ^ 2 * (finiteDifferenceCount B B (p.1 - p.2) : ℝ) ≤ A.card := by
    intro p hp
    exact (lt_of_not_ge (Finset.mem_filter.mp hp).2).le
  obtain ⟨s, hs⟩ := finite_exists_good_shift hA hB hK.le
    (by rwa [finite_difference_energy_eq_addEnergy]) (Finset.filter_subset _ _) hbad
  let X := finiteShiftOverlap A B s
  have hbadEq : finiteShiftPairCount B H s = ((X ×ˢ X).filter (fun p => ¬ P p)).card := by
    unfold finiteShiftPairCount
    congr 1
    ext p
    simp only [H, X, finiteShiftOverlap, Finset.mem_filter, Finset.mem_product]
    aesop
  have hpart : (((X ×ˢ X).filter P).card : ℝ) + (finiteShiftPairCount B H s : ℝ) = (X.card : ℝ) ^ 2 := by
    rw [hbadEq]
    exact_mod_cast (Finset.card_filter_add_card_filter_not (s := X ×ˢ X) P).trans
      (by simp [pow_two])
  have hs' : (A.card : ℝ) ^ 2 ≤ 2 * K ^ 2 * (X.card : ℝ) ^ 2 :=
    (le_add_of_nonneg_right (by positivity)).trans hs
  have hsize : (A.card : ℝ) ≤ 2 * K * (X.card : ℝ) := by
    apply (sq_le_sq₀ (Nat.cast_nonneg _) (by positivity)).mp
    nlinarith [sq_nonneg (K * (X.card : ℝ))]
  have hbadSmall : 8 * (finiteShiftPairCount B H s : ℝ) ≤ (X.card : ℝ) ^ 2 := by
    apply (mul_le_mul_iff_left₀ (show 0 < 2 * K ^ 2 by positivity)).mp
    nlinarith [sq_nonneg (A.card : ℝ)]
  refine ⟨s, (div_le_iff₀ (by positivity)).mpr (by nlinarith [hsize]), ?_⟩
  change (7 / 8 : ℝ) * (X.card : ℝ) ^ 2 ≤ (((X ×ˢ X).filter P).card : ℝ)
  nlinarith

def finiteGraphRow (X : Finset G) (H : Finset (G × G)) (a : G) : Finset G :=
  X.filter (fun b => (a, b) ∈ H)

noncomputable def finiteGraphCore (X : Finset G) (H : Finset (G × G)) : Finset G := by
  classical
  exact X.filter (fun a => (3 / 4 : ℝ) * (X.card : ℝ) ≤ (finiteGraphRow X H a).card)

theorem finite_graph_row_fiber {X : Finset G} {H : Finset (G × G)}
    (hH : H ⊆ X ×ˢ X) (a : G) :
    (H.filter (fun p => p.1 = a)).card = (finiteGraphRow X H a).card := by
  apply Finset.card_bij (fun p _ => p.2)
  · intro p hp
    obtain ⟨hpH, hpa⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨(Finset.mem_product.mp (hH hpH)).2, by simpa only [← hpa] using hpH⟩
  · intro p hp q hq hpq
    exact Prod.ext ((Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm) hpq
  · intro b hb
    exact ⟨(a, b), Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hb).2, rfl⟩, rfl⟩

theorem finite_graph_row_sum {X : Finset G} {H : Finset (G × G)}
    (hH : H ⊆ X ×ˢ X) :
    ∑ a ∈ X, (finiteGraphRow X H a).card = H.card := by
  simp_rw [← finite_graph_row_fiber hH]
  exact (Finset.card_eq_sum_card_fiberwise (f := Prod.fst)
    (fun _ hp => (Finset.mem_product.mp (hH hp)).1)).symm

theorem finite_graph_core_card {X : Finset G} {H : Finset (G × G)}
    (hH : H ⊆ X ×ˢ X) (hdense : (7 / 8 : ℝ) * (X.card : ℝ) ^ 2 ≤ H.card) :
    (X.card : ℝ) / 8 ≤ (finiteGraphCore X H).card := by
  classical
  let C := finiteGraphCore X H
  have hCX : C ⊆ X := Finset.filter_subset _ _
  have hrow : ∀ a ∈ X, ((finiteGraphRow X H a).card : ℝ) ≤
      (3 / 4 : ℝ) * (X.card : ℝ) + if a ∈ C then (X.card : ℝ) else 0 := by
    intro a ha
    by_cases hc : a ∈ C
    · rw [if_pos hc]
      have hh : ((finiteGraphRow X H a).card : ℝ) ≤ X.card := by
        exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
      nlinarith [show (0 : ℝ) ≤ X.card from Nat.cast_nonneg _]
    · rw [if_neg hc, add_zero]
      have hn : ¬ (3 / 4 : ℝ) * (X.card : ℝ) ≤ (finiteGraphRow X H a).card := by
        intro hh
        exact hc (Finset.mem_filter.mpr ⟨ha, hh⟩)
      exact (lt_of_not_ge hn).le
  have hbound : (H.card : ℝ) ≤ (3 / 4 : ℝ) * (X.card : ℝ) ^ 2 + (C.card : ℝ) * (X.card : ℝ) := by
    calc
      _ = ∑ a ∈ X, ((finiteGraphRow X H a).card : ℝ) := by
        exact_mod_cast (finite_graph_row_sum hH).symm
      _ ≤ ∑ a ∈ X, ((3 / 4 : ℝ) * (X.card : ℝ) + if a ∈ C then (X.card : ℝ) else 0) :=
        Finset.sum_le_sum hrow
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.sum_filter, Finset.filter_mem_eq_inter,
          Finset.inter_eq_right.mpr hCX]
        simp only [Finset.sum_const, nsmul_eq_mul]
        ring
  by_cases hX : X.card = 0
  · simp only [hX, Nat.cast_zero, zero_div]
    positivity
  · have hXp : (0 : ℝ) < X.card := by exact_mod_cast Nat.pos_of_ne_zero hX
    apply (mul_le_mul_iff_left₀ hXp).mp
    nlinarith

theorem finite_graph_core_common {X : Finset G} {H : Finset (G × G)} {a b : G}
    (ha : a ∈ finiteGraphCore X H) (hb : b ∈ finiteGraphCore X H) :
    (X.card : ℝ) / 2 ≤ ((finiteGraphRow X H a ∩ finiteGraphRow X H b).card : ℝ) := by
  have ha' := (Finset.mem_filter.mp ha).2
  have hb' := (Finset.mem_filter.mp hb).2
  have hu : (finiteGraphRow X H a ∪ finiteGraphRow X H b) ⊆ X :=
    Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have huc : ((finiteGraphRow X H a ∪ finiteGraphRow X H b).card : ℝ) ≤ X.card := by
    exact_mod_cast Finset.card_le_card hu
  have hh : ((finiteGraphRow X H a ∪ finiteGraphRow X H b).card : ℝ) +
      ((finiteGraphRow X H a ∩ finiteGraphRow X H b).card : ℝ) =
      ((finiteGraphRow X H a).card : ℝ) + ((finiteGraphRow X H b).card : ℝ) := by
    exact_mod_cast Finset.card_union_add_card_inter (finiteGraphRow X H a) (finiteGraphRow X H b)
  nlinarith

def finiteQuadDifferenceFiber (B : Finset G) (x : G) : Finset ((G × G) × (G × G)) :=
  ((B ×ˢ B) ×ˢ (B ×ˢ B)).filter (fun p => (p.1.1 - p.1.2) - (p.2.1 - p.2.2) = x)

theorem finite_quad_difference_sum (B : Finset G) :
    ∑ x : G, (finiteQuadDifferenceFiber B x).card = B.card ^ 4 := by
  unfold finiteQuadDifferenceFiber
  calc
    _ = ((B ×ˢ B) ×ˢ (B ×ˢ B)).card :=
      (Finset.card_eq_sum_card_fiberwise
        (f := fun p : (G × G) × (G × G) => (p.1.1 - p.1.2) - (p.2.1 - p.2.2))
        (t := Finset.univ) (fun _ _ => Finset.mem_univ _)).symm
    _ = _ := by simp only [Finset.card_product]; ring

theorem finite_common_neighbors_inject_quad (B C : Finset G) (a b : G) :
    (C.sigma (fun c => finiteDifferenceFiber B B (a - c) ×ˢ finiteDifferenceFiber B B (b - c))).card ≤
      (finiteQuadDifferenceFiber B (a - b)).card := by
  apply Finset.card_le_card_of_injOn (fun p : Σ _c : G, (G × G) × (G × G) => p.2)
  · intro p hp
    obtain ⟨hc, hp'⟩ := Finset.mem_sigma.mp hp
    obtain ⟨hu, hv⟩ := Finset.mem_product.mp hp'
    obtain ⟨huB, hue⟩ := Finset.mem_filter.mp hu
    obtain ⟨hvB, hve⟩ := Finset.mem_filter.mp hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨huB, hvB⟩,
      by rw [hue, hve, sub_sub_sub_cancel_right]⟩
  · intro p hp q hq hpq
    dsimp only at hpq
    have hp₁ := (Finset.mem_filter.mp (Finset.mem_product.mp (Finset.mem_sigma.mp hp).2).1).2
    have hq₁ := (Finset.mem_filter.mp (Finset.mem_product.mp (Finset.mem_sigma.mp hq).2).1).2
    have heq : a - p.1 = a - q.1 := by
      rw [← hp₁, ← hq₁, hpq]
    have hpq₁ : p.1 = q.1 := sub_right_injective heq
    exact Sigma.ext hpq₁ (heq_of_eq hpq)

theorem finite_graph_core_quad_lower {X B : Finset G} {H : Finset (G × G)} {a b : G} {L : ℝ}
    (hL : 0 ≤ L) (ha : a ∈ finiteGraphCore X H) (hb : b ∈ finiteGraphCore X H)
    (hrep : ∀ p ∈ H, L ≤ (finiteDifferenceCount B B (p.1 - p.2) : ℝ)) :
    (X.card : ℝ) / 2 * L ^ 2 ≤ (finiteQuadDifferenceFiber B (a - b)).card := by
  let C := finiteGraphRow X H a ∩ finiteGraphRow X H b
  calc
    _ ≤ (C.card : ℝ) * L ^ 2 :=
      mul_le_mul_of_nonneg_right (finite_graph_core_common ha hb) (sq_nonneg L)
    _ = ∑ _c ∈ C, L ^ 2 := by simp
    _ ≤ ∑ c ∈ C, ((finiteDifferenceFiber B B (a - c) ×ˢ finiteDifferenceFiber B B (b - c)).card : ℝ) := by
      apply Finset.sum_le_sum
      intro c hc
      obtain ⟨hca, hcb⟩ := Finset.mem_inter.mp hc
      have h₁ := hrep (a, c) (Finset.mem_filter.mp hca).2
      have h₂ := hrep (b, c) (Finset.mem_filter.mp hcb).2
      simpa only [Finset.card_product, Nat.cast_mul, pow_two, finiteDifferenceCount] using
        mul_le_mul h₁ h₂ hL (Nat.cast_nonneg _)
    _ = ((C.sigma (fun c => finiteDifferenceFiber B B (a - c) ×ˢ finiteDifferenceFiber B B (b - c))).card : ℝ) := by
      rw [Finset.card_sigma, Nat.cast_sum]
    _ ≤ _ := by exact_mod_cast finite_common_neighbors_inject_quad B C a b

theorem finite_graph_core_difference_bound {X B : Finset G} {H : Finset (G × G)} {L : ℝ}
    (hL : 0 ≤ L)
    (hrep : ∀ p ∈ H, L ≤ (finiteDifferenceCount B B (p.1 - p.2) : ℝ)) :
    ((finiteGraphCore X H - finiteGraphCore X H).card : ℝ) * ((X.card : ℝ) / 2 * L ^ 2) ≤
      (B.card : ℝ) ^ 4 := by
  let C := finiteGraphCore X H
  calc
    _ = ∑ _x ∈ C - C, (X.card : ℝ) / 2 * L ^ 2 := by simp [C]
    _ ≤ ∑ x ∈ C - C, ((finiteQuadDifferenceFiber B x).card : ℝ) := by
      apply Finset.sum_le_sum
      intro x hx
      obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_sub.mp hx
      exact finite_graph_core_quad_lower hL ha hb hrep
    _ ≤ ∑ x : G, ((finiteQuadDifferenceFiber B x).card : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => Nat.cast_nonneg _)
    _ = _ := by exact_mod_cast finite_quad_difference_sum B

/-- A quantitative inverse-energy theorem for two sets in any finite abelian group.
The extracted set lies in a translate overlap and has a controlled difference set. -/
theorem finite_bsg_overlap {A B : Finset G} {K : ℝ}
    (hA : A.Nonempty) (hB : B.Nonempty) (hK : 0 < K)
    (hE : (A.card : ℝ) ^ 2 * (B.card : ℝ) ≤ K * (Finset.addEnergy A B : ℝ)) :
    ∃ s : G, ∃ C : Finset G, C ⊆ finiteShiftOverlap A B s ∧
      (A.card : ℝ) ≤ 16 * K * (C.card : ℝ) ∧
      (A.card : ℝ) ^ 3 * ((C - C).card : ℝ) ≤ 1024 * K ^ 5 * (B.card : ℝ) ^ 4 := by
  classical
  obtain ⟨s, hlarge, hdense⟩ := finite_energy_dense_overlap hA hB hK hE
  let X := finiteShiftOverlap A B s
  let H := (X ×ˢ X).filter (fun p => (A.card : ℝ) ≤
    16 * K ^ 2 * (finiteDifferenceCount B B (p.1 - p.2) : ℝ))
  let C := finiteGraphCore X H
  have hH : H ⊆ X ×ˢ X := Finset.filter_subset _ _
  have hcore : (X.card : ℝ) / 8 ≤ (C.card : ℝ) := finite_graph_core_card hH hdense
  have hrep : ∀ p ∈ H, (A.card : ℝ) / (16 * K ^ 2) ≤
      (finiteDifferenceCount B B (p.1 - p.2) : ℝ) := by
    intro p hp
    exact (div_le_iff₀ (by positivity)).mpr (by
      simpa only [mul_comm] using (Finset.mem_filter.mp hp).2)
  have hdiff := finite_graph_core_difference_bound
    (X := X) (B := B) (H := H) (by positivity : (0 : ℝ) ≤ (A.card : ℝ) / (16 * K ^ 2)) hrep
  have hpref : (A.card : ℝ) ^ 3 / (1024 * K ^ 5) ≤
      (X.card : ℝ) / 2 * ((A.card : ℝ) / (16 * K ^ 2)) ^ 2 := by
    calc
      _ = ((A.card : ℝ) / (2 * K)) / 2 * ((A.card : ℝ) / (16 * K ^ 2)) ^ 2 := by
        field_simp
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hlarge (by norm_num)) (by positivity)
  have hdiff' : ((C - C).card : ℝ) * ((A.card : ℝ) ^ 3 / (1024 * K ^ 5)) ≤ (B.card : ℝ) ^ 4 :=
    (mul_le_mul_of_nonneg_left hpref (Nat.cast_nonneg _)).trans hdiff
  refine ⟨s, C, Finset.filter_subset _ _, ?_, ?_⟩
  · have hh : (A.card : ℝ) / (16 * K) ≤ (C.card : ℝ) := by
      calc
        _ = ((A.card : ℝ) / (2 * K)) / 8 := by ring
        _ ≤ (X.card : ℝ) / 8 := div_le_div_of_nonneg_right hlarge (by norm_num)
        _ ≤ _ := hcore
    have hh' := (div_le_iff₀ (show 0 < 16 * K by positivity)).mp hh
    nlinarith
  · rw [← mul_div_assoc] at hdiff'
    have hh := (div_le_iff₀ (show 0 < 1024 * K ^ 5 by positivity)).mp hdiff'
    nlinarith

/-- Self-energy at least `|A|³/K` yields a subset of size at least `|A|/(16K)`
whose difference set is bounded by an explicit power of `K`. -/
theorem finite_bsg_self {A : Finset G} {K : ℝ}
    (hA : A.Nonempty) (hK : 0 < K)
    (hE : (A.card : ℝ) ^ 3 ≤ K * (Finset.addEnergy A A : ℝ)) :
    ∃ C : Finset G, C ⊆ A ∧ C.Nonempty ∧
      (A.card : ℝ) ≤ 16 * K * (C.card : ℝ) ∧
      ((C - C).card : ℝ) ≤ 16384 * K ^ 6 * (C.card : ℝ) := by
  obtain ⟨s, C, hCA, hsize, hdiff⟩ := finite_bsg_overlap hA hA hK (by nlinarith [hE])
  have hAp : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have hCp : (0 : ℝ) < C.card := by
    by_contra hn
    have hc : (C.card : ℝ) = 0 := le_antisymm (le_of_not_gt hn) (Nat.cast_nonneg _)
    rw [hc, mul_zero] at hsize
    exact not_le_of_gt hAp hsize
  refine ⟨C, hCA.trans (Finset.filter_subset _ _), by exact_mod_cast Finset.card_pos.mp (show 0 < C.card by exact_mod_cast hCp), hsize, ?_⟩
  have hdiff' : ((C - C).card : ℝ) ≤ 1024 * K ^ 5 * (A.card : ℝ) := by
    apply (mul_le_mul_iff_right₀ (show (0 : ℝ) < (A.card : ℝ) ^ 3 by positivity)).mp
    calc
      _ ≤ 1024 * K ^ 5 * (A.card : ℝ) ^ 4 := hdiff
      _ = _ := by ring
  calc
    _ ≤ 1024 * K ^ 5 * (A.card : ℝ) := hdiff'
    _ ≤ 1024 * K ^ 5 * (16 * K * (C.card : ℝ)) :=
      mul_le_mul_of_nonneg_left hsize (by positivity)
    _ = _ := by ring

theorem finite_sub_translated_image (C : Finset G) (s : G) :
    C - C.image (fun x => x - s) = (C - C).image (fun x => x + s) := by
  ext z
  constructor
  · intro hz
    obtain ⟨a, ha, y, hy, rfl⟩ := Finset.mem_sub.mp hz
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_image.mpr ⟨a - b, Finset.mem_sub.mpr ⟨a, ha, b, hb, rfl⟩, by
      simp only [sub_eq_add_neg, neg_add_rev, neg_neg]
      abel⟩
  · intro hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_sub.mp hx
    exact Finset.mem_sub.mpr ⟨a, ha, b - s, Finset.mem_image_of_mem _ hb, by
      simp only [sub_eq_add_neg, neg_add_rev, neg_neg]
      abel⟩

/-- Two subsets of equal cardinality with a controlled mixed difference set. -/
theorem finite_bsg_two_sets {A B : Finset G} {K : ℝ}
    (hA : A.Nonempty) (hB : B.Nonempty) (hK : 0 < K)
    (hE : (A.card : ℝ) ^ 2 * (B.card : ℝ) ≤ K * (Finset.addEnergy A B : ℝ)) :
    ∃ C D : Finset G, C ⊆ A ∧ D ⊆ B ∧ C.Nonempty ∧ D.card = C.card ∧
      (A.card : ℝ) ≤ 16 * K * (C.card : ℝ) ∧
      (A.card : ℝ) ^ 3 * ((C - D).card : ℝ) ≤ 1024 * K ^ 5 * (B.card : ℝ) ^ 4 := by
  obtain ⟨s, C, hC, hsize, hdiff⟩ := finite_bsg_overlap hA hB hK hE
  let D := C.image (fun x => x - s)
  have hDB : D ⊆ B := by
    intro d hd
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hd
    exact (Finset.mem_filter.mp (hC hc)).2
  have hDcard : D.card = C.card := Finset.card_image_of_injective C (fun _ _ h => sub_left_injective h)
  have hdiffcard : (C - D).card = (C - C).card := by
    dsimp only [D]
    rw [finite_sub_translated_image, Finset.card_image_of_injective _ (fun _ _ h => add_right_cancel h)]
  have hCp : (0 : ℝ) < C.card := by
    have hAp : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
    by_contra hn
    have hc : (C.card : ℝ) = 0 := le_antisymm (le_of_not_gt hn) (Nat.cast_nonneg _)
    rw [hc, mul_zero] at hsize
    exact not_le_of_gt hAp hsize
  refine ⟨C, D, hC.trans (Finset.filter_subset _ _), hDB,
    Finset.card_pos.mp (by exact_mod_cast hCp), hDcard, hsize, ?_⟩
  simpa only [hdiffcard] using hdiff

end FiniteInverseEnergy

noncomputable def cyclicSetIndicator {q : ℕ} [NeZero q]
    (A : Finset (ZMod q)) (x : ZMod q) : ℂ := if x ∈ A then 1 else 0

theorem finite_sum_fiber_card {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A B : Finset G) (x : G) :
    ((A ×ˢ B).filter (fun p => p.1 + p.2 = x)).card =
      (A.filter (fun a => x - a ∈ B)).card := by
  apply Finset.card_bij (fun p _ => p.1)
  · intro p hp
    obtain ⟨hpAB, heq⟩ := Finset.mem_filter.mp hp
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hpAB
    exact Finset.mem_filter.mpr ⟨ha, by simpa only [← heq, add_sub_cancel_left] using hb⟩
  · intro p hp q hq hpq
    apply Prod.ext hpq
    have hh := (Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm
    simpa only [hpq, add_left_cancel_iff] using hh
  · intro a ha
    obtain ⟨haA, haB⟩ := Finset.mem_filter.mp ha
    exact ⟨(a, x - a), Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨haA, haB⟩, add_sub_cancel a x⟩, rfl⟩

theorem cyclic_set_indicator_convolution {q : ℕ} [NeZero q]
    (A B : Finset (ZMod q)) (x : ZMod q) :
    cyclicConvolution (cyclicSetIndicator A) (cyclicSetIndicator B) x =
      (((A ×ˢ B).filter (fun p => p.1 + p.2 = x)).card : ℂ) := by
  classical
  rw [finite_sum_fiber_card]
  simp only [cyclicConvolution, cyclicSetIndicator, ite_mul, one_mul, zero_mul,
    ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter,
    Finset.sum_const, nsmul_eq_mul, mul_one]

theorem cyclic_set_convolution_energy {q : ℕ} [NeZero q] (A B : Finset (ZMod q)) :
    (∑ x : ZMod q, ‖cyclicConvolution (cyclicSetIndicator A) (cyclicSetIndicator B) x‖ ^ 2) =
      (Finset.addEnergy A B : ℝ) := by
  simp_rw [cyclic_set_indicator_convolution, Complex.norm_natCast]
  exact_mod_cast (Finset.addEnergy_eq_sum_sq A B).symm

theorem cyclic_set_fourier_energy {q : ℕ} [NeZero q] (A B : Finset (ZMod q)) :
    (∑ k : ZMod q, ‖ZMod.dft (cyclicSetIndicator A) k‖ ^ 2 *
      ‖ZMod.dft (cyclicSetIndicator B) k‖ ^ 2) = (q : ℝ) * (Finset.addEnergy A B : ℝ) := by
  have hh := dft_parseval (cyclicConvolution (cyclicSetIndicator A) (cyclicSetIndicator B))
  simpa only [dft_cyclicConvolution, norm_mul, mul_pow, cyclic_set_convolution_energy] using hh

theorem cyclic_large_fourier_energy_subset {q : ℕ} [NeZero q]
    {A : Finset (ZMod q)} {K : ℝ} (hA : A.Nonempty) (hK : 0 < K)
    (hFourier : (q : ℝ) * (A.card : ℝ) ^ 3 ≤
      K * ∑ k : ZMod q, ‖ZMod.dft (cyclicSetIndicator A) k‖ ^ 4) :
    ∃ C : Finset (ZMod q), C ⊆ A ∧ C.Nonempty ∧
      (A.card : ℝ) ≤ 16 * K * (C.card : ℝ) ∧
      ((C - C).card : ℝ) ≤ 16384 * K ^ 6 * (C.card : ℝ) := by
  apply finite_bsg_self hA hK
  have hsum : (∑ k : ZMod q, ‖ZMod.dft (cyclicSetIndicator A) k‖ ^ 4) =
      (q : ℝ) * (Finset.addEnergy A A : ℝ) := by
    convert cyclic_set_fourier_energy A A using 1
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hsum] at hFourier
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  apply (mul_le_mul_iff_right₀ hq).mp
  simpa only [mul_left_comm K (q : ℝ)] using hFourier


/- Common intersections and Ruzsa bounds for assembling inverse-energy subsets. -/

theorem finite_sub_card_comm {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A B : Finset G) : (A - B).card = (B - A).card := by
  apply Finset.card_bij (fun x _ => -x)
  · intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_sub.mp hx
    exact Finset.mem_sub.mpr ⟨b, hb, a, ha, (neg_sub a b).symm⟩
  · intro x hx y hy hxy
    exact neg_injective hxy
  · intro y hy
    obtain ⟨b, hb, a, ha, rfl⟩ := Finset.mem_sub.mp hy
    exact ⟨a - b, Finset.mem_sub.mpr ⟨a, ha, b, hb, rfl⟩, neg_sub a b⟩

theorem finite_sum_card_common_difference {G : Type*} [AddCommGroup G] [DecidableEq G]
    (X Y U V : Finset G) :
    (U + V).card * (X ∩ Y).card ≤ (X - U).card * (Y - V).card := by
  have hh := Finset.ruzsa_triangle_inequality_add_add_add U (-(X ∩ Y)) V
  have h₁ : (U + -(X ∩ Y)).card ≤ (X - U).card := by
    rw [← sub_eq_add_neg, finite_sub_card_comm]
    exact Finset.card_le_card (Finset.sub_subset_sub_right Finset.inter_subset_left)
  have h₂ : (-(X ∩ Y) + V).card ≤ (Y - V).card := by
    rw [add_comm, ← sub_eq_add_neg, finite_sub_card_comm]
    exact Finset.card_le_card (Finset.sub_subset_sub_right Finset.inter_subset_right)
  simp only [Finset.card_neg] at hh
  exact hh.trans (Nat.mul_le_mul h₁ h₂)

theorem finite_sum_card_common_middle {G : Type*} [AddCommGroup G] [DecidableEq G]
    (U V W : Finset G) :
    (U + W).card * (V ∩ W).card ≤ (U + V).card * (W + W).card := by
  have hh := Finset.ruzsa_triangle_inequality_add_add_add U (V ∩ W) W
  apply hh.trans
  apply Nat.mul_le_mul
  · exact Finset.card_le_card (Finset.add_subset_add_left Finset.inter_subset_left)
  · exact Finset.card_le_card (Finset.add_subset_add_right Finset.inter_subset_right)

theorem finite_common_structure_card_bound {G : Type*} [AddCommGroup G] [DecidableEq G]
    (X Y U V W : Finset G) (hdouble : (W + W).card = (U + U).card) :
    (U + W).card * (V ∩ W).card * (X ∩ Y).card * X.card ≤
      (X - U).card ^ 3 * (Y - V).card := by
  have hcross := finite_sum_card_common_difference X Y U V
  have hself : (U + U).card * X.card ≤ (X - U).card ^ 2 := by
    simpa only [Finset.inter_self, pow_two] using finite_sum_card_common_difference X X U U
  calc
    _ ≤ ((U + V).card * (W + W).card) * (X ∩ Y).card * X.card :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (finite_sum_card_common_middle U V W))
    _ = ((U + V).card * (X ∩ Y).card) * ((U + U).card * X.card) := by rw [hdouble]; ring
    _ ≤ ((X - U).card * (Y - V).card) * (X - U).card ^ 2 := Nat.mul_le_mul hcross hself
    _ = _ := by ring

theorem finite_family_incidence_sum {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (I : Finset ι) (S : Finset α) (F : ι → Finset α)
    (hF : ∀ i ∈ I, F i ⊆ S) :
    (∑ x ∈ S, (I.filter (fun i => x ∈ F i)).card) = ∑ i ∈ I, (F i).card := by
  classical
  calc
    _ = ∑ i ∈ I, (S.filter (fun x => x ∈ F i)).card := by
      simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
      exact Finset.sum_comm
    _ = _ := Finset.sum_congr rfl (fun i hi => by
      rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr (hF i hi)])

theorem finite_family_intersection_moment {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (I : Finset ι) (S : Finset α) (F : ι → Finset α)
    (hF : ∀ i ∈ I, F i ⊆ S) :
    (∑ i ∈ I, ∑ j ∈ I, (F i ∩ F j).card) =
      ∑ x ∈ S, (I.filter (fun i => x ∈ F i)).card ^ 2 := by
  classical
  let f := fun x i => if x ∈ F i then (1 : ℕ) else 0
  have hinter (i j : ι) (hi : i ∈ I) :
      (F i ∩ F j).card = ∑ x ∈ S, f x i * f x j := by
    have heq : S.filter (fun x => x ∈ F i ∧ x ∈ F j) = F i ∩ F j := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_inter]
      exact ⟨fun h => h.2, fun h => ⟨hF i hi h.1, h⟩⟩
    rw [← heq, Finset.card_eq_sum_ones, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x hx
    simp only [f]
    split_ifs <;> simp_all
  calc
    _ = ∑ i ∈ I, ∑ j ∈ I, ∑ x ∈ S, f x i * f x j := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_congr rfl (fun j hj => hinter i j hi)
    _ = ∑ i ∈ I, ∑ x ∈ S, ∑ j ∈ I, f x i * f x j := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_comm
    _ = ∑ x ∈ S, ∑ i ∈ I, ∑ j ∈ I, f x i * f x j := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [← Finset.sum_mul_sum]
      simp only [f, Finset.card_eq_sum_ones, Finset.sum_filter, pow_two]

theorem finite_family_intersection_lower {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    {I : Finset ι} {S : Finset α} {F : ι → Finset α} {δ : ℝ}
    (hS : S.Nonempty) (hδ : 0 ≤ δ) (hF : ∀ i ∈ I, F i ⊆ S)
    (hlarge : ∀ i ∈ I, δ * (S.card : ℝ) ≤ (F i).card) :
    δ ^ 2 * (I.card : ℝ) ^ 2 * (S.card : ℝ) ≤
      ∑ i ∈ I, ∑ j ∈ I, ((F i ∩ F j).card : ℝ) := by
  classical
  have hsum : δ * (I.card : ℝ) * (S.card : ℝ) ≤ ∑ i ∈ I, ((F i).card : ℝ) := by
    calc
      _ = ∑ _i ∈ I, δ * (S.card : ℝ) := by simp; ring
      _ ≤ _ := Finset.sum_le_sum hlarge
  have hsum' : δ * (I.card : ℝ) * (S.card : ℝ) ≤
      ∑ x ∈ S, ((I.filter (fun i => x ∈ F i)).card : ℝ) := by
    have heq : (∑ x ∈ S, ((I.filter (fun i => x ∈ F i)).card : ℝ)) =
        ∑ i ∈ I, ((F i).card : ℝ) := by exact_mod_cast finite_family_incidence_sum I S F hF
    rwa [heq]
  have hsq := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ δ * I.card * S.card) hsum' 2
  have hc := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ))
    (fun x => ((I.filter (fun i => x ∈ F i)).card : ℝ))
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hc
  have hm : (∑ x ∈ S, ((I.filter (fun i => x ∈ F i)).card : ℝ) ^ 2) =
      ∑ i ∈ I, ∑ j ∈ I, ((F i ∩ F j).card : ℝ) := by
    exact_mod_cast (finite_family_intersection_moment I S F hF).symm
  rw [hm] at hc
  have hSp : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  apply (mul_le_mul_iff_right₀ hSp).mp
  calc
    _ = (δ * (I.card : ℝ) * (S.card : ℝ)) ^ 2 := by ring
    _ ≤ _ := hsq.trans hc

theorem finite_family_large_intersections {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    {I : Finset ι} {S : Finset α} {F : ι → Finset α} {δ : ℝ}
    (hI : I.Nonempty) (hS : S.Nonempty) (hδ : 0 ≤ δ) (hF : ∀ i ∈ I, F i ⊆ S)
    (hlarge : ∀ i ∈ I, δ * (S.card : ℝ) ≤ (F i).card) :
    ∃ i ∈ I, δ ^ 2 / 2 * (I.card : ℝ) ≤
      ((I.filter (fun j => δ ^ 2 / 2 * (S.card : ℝ) ≤ ((F i ∩ F j).card : ℝ))).card : ℝ) := by
  classical
  have htotal := finite_family_intersection_lower hS hδ hF hlarge
  have hex : ∃ i ∈ I, δ ^ 2 * (I.card : ℝ) * (S.card : ℝ) ≤
      ∑ j ∈ I, ((F i ∩ F j).card : ℝ) := by
    by_contra! hn
    have hh : (∑ i ∈ I, ∑ j ∈ I, ((F i ∩ F j).card : ℝ)) <
        ∑ _i ∈ I, δ ^ 2 * (I.card : ℝ) * (S.card : ℝ) := by
      apply Finset.sum_lt_sum
      · intro i hi
        exact (hn i hi).le
      · obtain ⟨i, hi⟩ := hI
        exact ⟨i, hi, hn i hi⟩
    have heq : (∑ _i ∈ I, δ ^ 2 * (I.card : ℝ) * (S.card : ℝ)) =
        δ ^ 2 * (I.card : ℝ) ^ 2 * (S.card : ℝ) := by simp; ring
    rw [heq] at hh
    exact not_lt_of_ge htotal hh
  obtain ⟨i, hi, hrow⟩ := hex
  let C := I.filter (fun j => δ ^ 2 / 2 * (S.card : ℝ) ≤ ((F i ∩ F j).card : ℝ))
  have hpoint : ∀ j ∈ I, ((F i ∩ F j).card : ℝ) ≤
      δ ^ 2 / 2 * (S.card : ℝ) + if j ∈ C then (S.card : ℝ) else 0 := by
    intro j hj
    by_cases hc : j ∈ C
    · rw [if_pos hc]
      have hcard : ((F i ∩ F j).card : ℝ) ≤ S.card := by
        exact_mod_cast Finset.card_le_card ((Finset.inter_subset_left).trans (hF i hi))
      have hnonneg : 0 ≤ δ ^ 2 / 2 * (S.card : ℝ) := by positivity
      linarith
    · rw [if_neg hc, add_zero]
      have hn : ¬ δ ^ 2 / 2 * (S.card : ℝ) ≤ ((F i ∩ F j).card : ℝ) := by
        intro hh
        exact hc (Finset.mem_filter.mpr ⟨hj, hh⟩)
      exact (lt_of_not_ge hn).le
  have hbound : (∑ j ∈ I, ((F i ∩ F j).card : ℝ)) ≤
      (I.card : ℝ) * (δ ^ 2 / 2 * (S.card : ℝ)) + (C.card : ℝ) * (S.card : ℝ) := by
    calc
      _ ≤ ∑ j ∈ I, (δ ^ 2 / 2 * (S.card : ℝ) + if j ∈ C then (S.card : ℝ) else 0) :=
        Finset.sum_le_sum hpoint
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.sum_filter, Finset.filter_mem_eq_inter,
          Finset.inter_eq_right.mpr (Finset.filter_subset _ _)]
        simp [C]
  refine ⟨i, hi, ?_⟩
  have hSp : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  apply (mul_le_mul_iff_left₀ hSp).mp
  change δ ^ 2 / 2 * (I.card : ℝ) * (S.card : ℝ) ≤ (C.card : ℝ) * (S.card : ℝ)
  nlinarith

theorem finite_common_structure_quantitative {G : Type*} [AddCommGroup G] [DecidableEq G]
    {X Y U V W : Finset G} {a α δ M : ℝ}
    (ha : 0 < a) (hα : 0 < α) (hδ : 0 < δ) (hM : 0 ≤ M)
    (hX : α * a ≤ (X.card : ℝ)) (hU : α * a ≤ (U.card : ℝ))
    (hXY : δ * a ≤ ((X ∩ Y).card : ℝ)) (hVW : δ * a ≤ ((V ∩ W).card : ℝ))
    (hXU : ((X - U).card : ℝ) ≤ M * a) (hYV : ((Y - V).card : ℝ) ≤ M * a)
    (hdouble : (W + W).card = (U + U).card) :
    ((U + W).card : ℝ) ≤ M ^ 4 / (α ^ 2 * δ ^ 2) * (U.card : ℝ) := by
  have hc : ((U + W).card : ℝ) * ((V ∩ W).card : ℝ) * ((X ∩ Y).card : ℝ) * (X.card : ℝ) ≤
      ((X - U).card : ℝ) ^ 3 * ((Y - V).card : ℝ) := by
    exact_mod_cast finite_common_structure_card_bound X Y U V W hdouble
  have hprefix : α * δ ^ 2 * a ^ 3 ≤ ((V ∩ W).card : ℝ) * ((X ∩ Y).card : ℝ) * (X.card : ℝ) := by
    calc
      _ = (δ * a) * (δ * a) * (α * a) := by ring
      _ ≤ _ := by gcongr
  have hpow : ((X - U).card : ℝ) ^ 3 * ((Y - V).card : ℝ) ≤ M ^ 4 * a ^ 4 := by
    calc
      _ ≤ (M * a) ^ 3 * (M * a) := by gcongr
      _ = _ := by ring
  have htotal : ((U + W).card : ℝ) * (α * δ ^ 2 * a ^ 3) ≤ M ^ 4 * a ^ 4 := by
    calc
      _ ≤ ((U + W).card : ℝ) * (((V ∩ W).card : ℝ) * ((X ∩ Y).card : ℝ) * (X.card : ℝ)) :=
        mul_le_mul_of_nonneg_left hprefix (Nat.cast_nonneg _)
      _ = ((U + W).card : ℝ) * ((V ∩ W).card : ℝ) * ((X ∩ Y).card : ℝ) * (X.card : ℝ) := by ring
      _ ≤ _ := hc.trans hpow
  have hcancel : ((U + W).card : ℝ) * (α * δ ^ 2) ≤ M ^ 4 * a := by
    apply (mul_le_mul_iff_left₀ (show 0 < a ^ 3 by positivity)).mp
    calc
      _ = ((U + W).card : ℝ) * (α * δ ^ 2 * a ^ 3) := by ring
      _ ≤ M ^ 4 * a ^ 4 := htotal
      _ = _ := by ring
  have hfinal : ((U + W).card : ℝ) * (α ^ 2 * δ ^ 2) ≤ M ^ 4 * (U.card : ℝ) := by
    calc
      _ = (((U + W).card : ℝ) * (α * δ ^ 2)) * α := by ring
      _ ≤ (M ^ 4 * a) * α := mul_le_mul_of_nonneg_right hcancel hα.le
      _ = M ^ 4 * (α * a) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hU (by positivity)
  calc
    _ ≤ M ^ 4 * (U.card : ℝ) / (α ^ 2 * δ ^ 2) :=
      (le_div_iff₀ (by positivity)).mpr hfinal
    _ = _ := by ring

theorem finite_bsg_common_structure {G : Type*} [AddCommGroup G] [DecidableEq G]
    {X Y U V W : Finset G} {a K : ℝ} (ha : 0 < a) (hK : 0 < K)
    (hX : a / (16 * K) ≤ (X.card : ℝ)) (hU : a / (16 * K) ≤ (U.card : ℝ))
    (hXY : a / (131072 * K ^ 4) ≤ ((X ∩ Y).card : ℝ))
    (hVW : a / (131072 * K ^ 4) ≤ ((V ∩ W).card : ℝ))
    (hXU : ((X - U).card : ℝ) ≤ 1024 * K ^ 5 * a)
    (hYV : ((Y - V).card : ℝ) ≤ 1024 * K ^ 5 * a)
    (hdouble : (W + W).card = (U + U).card) :
    ((U + W).card : ℝ) ≤ (2 : ℝ) ^ (82 : ℕ) * K ^ 30 * (U.card : ℝ) := by
  have hh := finite_common_structure_quantitative (X := X) (Y := Y) (U := U) (V := V) (W := W)
    (a := a) (α := (16 * K)⁻¹) (δ := (131072 * K ^ 4)⁻¹) (M := 1024 * K ^ 5)
    ha (by positivity) (by positivity) (by positivity)
    (by simpa only [inv_mul_eq_div] using hX) (by simpa only [inv_mul_eq_div] using hU)
    (by simpa only [inv_mul_eq_div] using hXY) (by simpa only [inv_mul_eq_div] using hVW)
    hXU hYV hdouble
  have heq : (1024 * K ^ 5) ^ 4 / ((16 * K)⁻¹ ^ 2 * (131072 * K ^ 4)⁻¹ ^ 2) =
      (2 : ℝ) ^ (82 : ℕ) * K ^ 30 := by
    field_simp
    ring
  rwa [heq] at hh


/- Simultaneous inverse energy and sum-product closure of additive stabilizers. -/

theorem finite_add_equiv_image_add {G : Type*} [AddCommGroup G] [DecidableEq G]
    (φ : G ≃+ G) (A B : Finset G) :
    (A + B).image φ = A.image φ + B.image φ := by
  ext z
  constructor
  · intro hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hx
    exact Finset.mem_add.mpr ⟨φ a, Finset.mem_image_of_mem _ ha,
      φ b, Finset.mem_image_of_mem _ hb, (map_add φ a b).symm⟩
  · intro hz
    obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp hz
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_image.mpr ⟨a + b, Finset.mem_add.mpr ⟨a, ha, b, hb, rfl⟩, map_add φ a b⟩

theorem finite_add_equiv_sum_card {G : Type*} [AddCommGroup G] [DecidableEq G]
    (φ : G ≃+ G) (A B : Finset G) :
    (A.image φ + B.image φ).card = (A + B).card := by
  rw [← finite_add_equiv_image_add, Finset.card_image_of_injective _ φ.injective]

theorem finite_add_equiv_inter_card {G : Type*} [AddCommGroup G] [DecidableEq G]
    (φ : G ≃+ G) (A B : Finset G) :
    (A.image φ ∩ B.image φ).card = (A ∩ B).card := by
  rw [← Finset.image_inter _ _ φ.injective, Finset.card_image_of_injective _ φ.injective]

theorem finite_bsg_add_equiv {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {A : Finset G} {K : ℝ} (φ : G ≃+ G) (hA : A.Nonempty) (hK : 0 < K)
    (hE : (A.card : ℝ) ^ 3 ≤ K * (Finset.addEnergy A (A.image φ) : ℝ)) :
    ∃ X Y : Finset G, X ⊆ A ∧ Y ⊆ A ∧
      (A.card : ℝ) / (16 * K) ≤ (X.card : ℝ) ∧
      (A.card : ℝ) / (16 * K) ≤ (Y.card : ℝ) ∧
      ((X - Y.image φ).card : ℝ) ≤ 1024 * K ^ 5 * (A.card : ℝ) := by
  have hBcard : (A.image φ).card = A.card := Finset.card_image_of_injective _ φ.injective
  have hE' : (A.card : ℝ) ^ 2 * ((A.image φ).card : ℝ) ≤
      K * (Finset.addEnergy A (A.image φ) : ℝ) := by
    calc
      _ = (A.card : ℝ) ^ 3 := by rw [hBcard]; ring
      _ ≤ _ := hE
  obtain ⟨X, D, hXA, hDB, hX, hDcard, hsize, hdiff⟩ := finite_bsg_two_sets hA (hA.image φ) hK hE'
  let Y := D.image φ.symm
  have hYA : Y ⊆ A := by
    intro y hy
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp (hDB hd)
    simpa only [AddEquiv.symm_apply_apply] using ha
  have hYcard : Y.card = X.card := (Finset.card_image_of_injective _ φ.symm.injective).trans hDcard
  have hYimage : Y.image φ = D := by
    ext d
    simp only [Y, Finset.mem_image]
    constructor
    · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
      simpa only [AddEquiv.apply_symm_apply] using hx
    · intro hd
      exact ⟨φ.symm d, ⟨d, hd, rfl⟩, φ.apply_symm_apply d⟩
  have hsize' : (A.card : ℝ) / (16 * K) ≤ (X.card : ℝ) :=
    (div_le_iff₀ (by positivity)).mpr (by simpa only [mul_comm] using hsize)
  refine ⟨X, Y, hXA, hYA, hsize', by simpa only [hYcard] using hsize', ?_⟩
  rw [hYimage]
  have hAp : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  apply (mul_le_mul_iff_right₀ (show (0 : ℝ) < (A.card : ℝ) ^ 3 by positivity)).mp
  calc
    _ ≤ 1024 * K ^ 5 * ((A.image φ).card : ℝ) ^ 4 := hdiff
    _ = _ := by rw [hBcard]; ring

theorem finite_large_product_intersections {G : Type*} [DecidableEq G]
    {A X Y U V : Finset G} {d : ℝ} (hA : A.Nonempty) (hXA : X ⊆ A) (hYA : Y ⊆ A)
    (hlarge : d * (A.card : ℝ) ^ 2 ≤ (((X ×ˢ Y) ∩ (U ×ˢ V)).card : ℝ)) :
    d * (A.card : ℝ) ≤ ((X ∩ U).card : ℝ) ∧ d * (A.card : ℝ) ≤ ((Y ∩ V).card : ℝ) := by
  have hAp : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have hX : ((X ∩ U).card : ℝ) ≤ A.card := by
    exact_mod_cast Finset.card_le_card ((Finset.inter_subset_left).trans hXA)
  have hY : ((Y ∩ V).card : ℝ) ≤ A.card := by
    exact_mod_cast Finset.card_le_card ((Finset.inter_subset_left).trans hYA)
  rw [Finset.product_inter_product, Finset.card_product, Nat.cast_mul] at hlarge
  constructor
  · apply (mul_le_mul_iff_left₀ hAp).mp
    calc
      _ = d * (A.card : ℝ) ^ 2 := by ring
      _ ≤ _ := hlarge
      _ ≤ _ := mul_le_mul_of_nonneg_left hY (Nat.cast_nonneg _)
  · apply (mul_le_mul_iff_right₀ hAp).mp
    calc
      _ = d * (A.card : ℝ) ^ 2 := by ring
      _ ≤ _ := hlarge
      _ ≤ _ := mul_le_mul_of_nonneg_right hX (Nat.cast_nonneg _)

/-- High additive energy for many automorphisms gives one common large subset
with controlled mixed sumsets for a large subfamily. -/
theorem finite_many_automorphisms_small_sumsets {G ι : Type*}
    [AddCommGroup G] [Fintype G] [DecidableEq G] [DecidableEq ι]
    {A : Finset G} {I : Finset ι} {K : ℝ} (φ : ι → G ≃+ G)
    (hA : A.Nonempty) (hI : I.Nonempty) (hK : 0 < K)
    (hE : ∀ i ∈ I, (A.card : ℝ) ^ 3 ≤ K * (Finset.addEnergy A (A.image (φ i)) : ℝ)) :
    ∃ B : Finset G, B ⊆ A ∧ B.Nonempty ∧ (A.card : ℝ) / (16 * K) ≤ (B.card : ℝ) ∧
      ∃ i₀ ∈ I, ∃ J : Finset ι, J ⊆ I ∧
        (I.card : ℝ) / (131072 * K ^ 4) ≤ (J.card : ℝ) ∧
        ∀ i ∈ J, ((B.image (φ i₀) + B.image (φ i)).card : ℝ) ≤
          (2 : ℝ) ^ (82 : ℕ) * K ^ 30 * (B.card : ℝ) := by
  classical
  have hex : ∀ i : ι, ∃ X Y : Finset G, i ∈ I → X ⊆ A ∧ Y ⊆ A ∧
      (A.card : ℝ) / (16 * K) ≤ (X.card : ℝ) ∧
      (A.card : ℝ) / (16 * K) ≤ (Y.card : ℝ) ∧
      ((X - Y.image (φ i)).card : ℝ) ≤ 1024 * K ^ 5 * (A.card : ℝ) := by
    intro i
    by_cases hi : i ∈ I
    · obtain ⟨X, Y, hXY⟩ := finite_bsg_add_equiv (φ i) hA hK (hE i hi)
      exact ⟨X, Y, fun _ => hXY⟩
    · exact ⟨∅, ∅, fun h => False.elim (hi h)⟩
  choose X Y hXY using hex
  let F := fun i => X i ×ˢ Y i
  let δ : ℝ := (16 * K)⁻¹ ^ 2
  have hF : ∀ i ∈ I, F i ⊆ A ×ˢ A := by
    intro i hi
    exact Finset.product_subset_product (hXY i hi).1 (hXY i hi).2.1
  have hlarge : ∀ i ∈ I, δ * ((A ×ˢ A).card : ℝ) ≤ (F i).card := by
    intro i hi
    obtain ⟨hXi, hYi, hXsize, hYsize, hsmall⟩ := hXY i hi
    dsimp only [F, δ]
    rw [Finset.card_product, Finset.card_product, Nat.cast_mul, Nat.cast_mul]
    calc
      _ = ((A.card : ℝ) / (16 * K)) * ((A.card : ℝ) / (16 * K)) := by ring
      _ ≤ _ := mul_le_mul hXsize hYsize (by positivity) (Nat.cast_nonneg _)
  obtain ⟨i₀, hi₀, hmany⟩ := finite_family_large_intersections hI (hA.product hA)
    (show 0 ≤ δ by positivity) hF hlarge
  let J := I.filter (fun i => δ ^ 2 / 2 * ((A ×ˢ A).card : ℝ) ≤ ((F i₀ ∩ F i).card : ℝ))
  have hconstant : δ ^ 2 / 2 = (131072 * K ^ 4)⁻¹ := by
    dsimp only [δ]
    field_simp
    ring
  have hAp : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have hYpos : (0 : ℝ) < (Y i₀).card :=
    (div_pos hAp (by positivity)).trans_le (hXY i₀ hi₀).2.2.2.1
  refine ⟨Y i₀, (hXY i₀ hi₀).2.1, Finset.card_pos.mp (by exact_mod_cast hYpos),
    (hXY i₀ hi₀).2.2.2.1, i₀, hi₀, J, Finset.filter_subset _ _, ?_, ?_⟩
  · have hh : δ ^ 2 / 2 * (I.card : ℝ) ≤ (J.card : ℝ) := hmany
    simpa only [hconstant, inv_mul_eq_div] using hh
  · intro i hi
    obtain ⟨hiI, hgood⟩ := Finset.mem_filter.mp hi
    have hgood' : δ ^ 2 / 2 * (A.card : ℝ) ^ 2 ≤ ((F i₀ ∩ F i).card : ℝ) := by
      simpa only [Finset.card_product, Nat.cast_mul, pow_two] using hgood
    obtain ⟨hXinter, hYinter⟩ := finite_large_product_intersections hA
      (hXY i₀ hi₀).1 (hXY i₀ hi₀).2.1 hgood'
    have hXinter' : (A.card : ℝ) / (131072 * K ^ 4) ≤ ((X i₀ ∩ X i).card : ℝ) := by
      simpa only [hconstant, inv_mul_eq_div] using hXinter
    have hYinter' : (A.card : ℝ) / (131072 * K ^ 4) ≤ ((Y i ∩ Y i₀).card : ℝ) := by
      simpa only [hconstant, inv_mul_eq_div, Finset.inter_comm] using hYinter
    have hh := finite_bsg_common_structure (X := X i₀) (Y := X i)
      (U := (Y i₀).image (φ i₀)) (V := (Y i).image (φ i)) (W := (Y i₀).image (φ i)) hAp hK
      (hXY i₀ hi₀).2.2.1
      (by simpa only [Finset.card_image_of_injective _ (φ i₀).injective] using (hXY i₀ hi₀).2.2.2.1)
      hXinter'
      (by simpa only [finite_add_equiv_inter_card] using hYinter')
      (hXY i₀ hi₀).2.2.2.2 (hXY i hiI).2.2.2.2
      (by rw [finite_add_equiv_sum_card, finite_add_equiv_sum_card])
    simpa only [Finset.card_image_of_injective _ (φ i₀).injective] using hh

def ringDilate {R : Type*} [Ring R] [DecidableEq R] (a : R) (A : Finset R) : Finset R :=
  A.image (fun x => a * x)

def ringUnitMulAddEquiv {R : Type*} [Ring R] (u : Rˣ) : R ≃+ R where
  toFun x := (u : R) * x
  invFun x := (u⁻¹ : Rˣ) * x
  left_inv x := by simp only [← mul_assoc, Units.inv_mul, one_mul]
  right_inv x := by simp only [← mul_assoc, Units.mul_inv, one_mul]
  map_add' x y := mul_add _ _ _

theorem ring_dilate_add {R : Type*} [Ring R] [DecidableEq R] (a : R) (A B : Finset R) :
    ringDilate a (A + B) = ringDilate a A + ringDilate a B := by
  exact Finset.image_add (AddMonoidHom.mulLeft a)

theorem ring_dilate_sub {R : Type*} [Ring R] [DecidableEq R] (a : R) (A B : Finset R) :
    ringDilate a (A - B) = ringDilate a A - ringDilate a B := by
  exact Finset.image_image₂_distrib (map_sub (AddMonoidHom.mulLeft a))

theorem ring_dilate_mul {R : Type*} [Ring R] [DecidableEq R] (a b : R) (A : Finset R) :
    ringDilate a (ringDilate b A) = ringDilate (a * b) A := by
  unfold ringDilate
  rw [Finset.image_image]
  apply Finset.image_congr
  intro x hx
  exact (mul_assoc a b x).symm

theorem ring_dilate_one {R : Type*} [Ring R] [DecidableEq R] (A : Finset R) :
    ringDilate 1 A = A := by simp [ringDilate]

theorem ring_dilate_unit_card {R : Type*} [Ring R] [DecidableEq R] (u : Rˣ) (A : Finset R) :
    (ringDilate (u : R) A).card = A.card :=
  Finset.card_image_of_injective A (ringUnitMulAddEquiv u).injective

theorem ring_unit_relative_sum_card {R : Type*} [Ring R] [DecidableEq R]
    (u v : Rˣ) (A : Finset R) :
    (A + ringDilate ((u⁻¹ * v : Rˣ) : R) A).card =
      (ringDilate (u : R) A + ringDilate (v : R) A).card := by
  have heq : ringDilate ((u⁻¹ : Rˣ) : R) (ringDilate (u : R) A + ringDilate (v : R) A) =
      A + ringDilate ((u⁻¹ * v : Rˣ) : R) A := by
    rw [ring_dilate_add, ring_dilate_mul, ring_dilate_mul, Units.inv_mul, ring_dilate_one]
    rfl
  rw [← heq, ring_dilate_unit_card]

noncomputable def ringSumStabilizer {R : Type*} [Ring R] [Fintype R] [DecidableEq R]
    (A : Finset R) (K : ℝ) : Finset R := by
  classical
  exact Finset.univ.filter (fun a => ((A + ringDilate a A).card : ℝ) ≤ K * (A.card : ℝ))

theorem mem_ring_sum_stabilizer {R : Type*} [Ring R] [Fintype R] [DecidableEq R]
    (A : Finset R) (K : ℝ) (a : R) :
    a ∈ ringSumStabilizer A K ↔ ((A + ringDilate a A).card : ℝ) ≤ K * (A.card : ℝ) := by
  classical
  simp only [ringSumStabilizer, Finset.mem_filter, Finset.mem_univ, true_and]

/-- A large family of unit dilates with high energy yields many normalized
unit multipliers stabilizing the additive size of one common large subset. -/
theorem finite_many_unit_dilates_stabilizer {R : Type*} [Ring R] [Fintype R] [DecidableEq R]
    {A : Finset R} {T : Finset Rˣ} {K : ℝ} (hA : A.Nonempty) (hT : T.Nonempty) (hK : 0 < K)
    (hE : ∀ u ∈ T, (A.card : ℝ) ^ 3 ≤ K * (Finset.addEnergy A (ringDilate (u : R) A) : ℝ)) :
    ∃ B : Finset R, B ⊆ A ∧ B.Nonempty ∧ (A.card : ℝ) / (16 * K) ≤ (B.card : ℝ) ∧
      ∃ u₀ ∈ T, ∃ S : Finset R,
        S ⊆ T.image (fun u => ((u₀⁻¹ * u : Rˣ) : R)) ∧ S.Nonempty ∧
        (T.card : ℝ) / (131072 * K ^ 4) ≤ (S.card : ℝ) ∧
        (∀ x ∈ S, IsUnit x) ∧ S ⊆ ringSumStabilizer B ((2 : ℝ) ^ (82 : ℕ) * K ^ 30) := by
  classical
  obtain ⟨B, hBA, hB, hsize, u₀, hu₀, J, hJT, hJsize, hsmall⟩ :=
    finite_many_automorphisms_small_sumsets (fun u : Rˣ => ringUnitMulAddEquiv u) hA hT hK hE
  let S := J.image (fun u => ((u₀⁻¹ * u : Rˣ) : R))
  have hinj : Function.Injective (fun u : Rˣ => ((u₀⁻¹ * u : Rˣ) : R)) := by
    intro u v huv
    exact mul_left_cancel (Units.val_injective huv)
  have hScard : S.card = J.card := Finset.card_image_of_injective _ hinj
  have hTp : (0 : ℝ) < T.card := by exact_mod_cast hT.card_pos
  have hJp : (0 : ℝ) < J.card := (div_pos hTp (by positivity)).trans_le hJsize
  have hJ : J.Nonempty := Finset.card_pos.mp (by exact_mod_cast hJp)
  refine ⟨B, hBA, hB, hsize, u₀, hu₀, S, Finset.image_subset_image hJT, hJ.image _,
    by simpa only [hScard] using hJsize, ?_, ?_⟩
  · intro x hx
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨u₀⁻¹ * u, rfl⟩
  · intro x hx
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    rw [mem_ring_sum_stabilizer, ring_unit_relative_sum_card]
    exact hsmall u hu

theorem finite_signed_sum_card_bound {G : Type*} [AddCommGroup G] [DecidableEq G]
    {A : Finset G} {D : ℝ} (hA : A.Nonempty) (hD : 0 ≤ D)
    (hdouble : ((A + A).card : ℝ) ≤ D * (A.card : ℝ)) (m n : ℕ) :
    ((m • A - n • A).card : ℝ) ≤ D ^ (m + n) * (A.card : ℝ) := by
  have hAp : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have hh := Finset.pluennecke_ruzsa_inequality_nsmul_sub_nsmul_add hA A m n
  have hhQ : ((m • A - n • A).card : ℚ) ≤
      (((A + A).card : ℚ) / (A.card : ℚ)) ^ (m + n) * (A.card : ℚ) := by
    exact_mod_cast (NNRat.coe_mono hh)
  have hhR := (Rat.cast_le (K := ℝ)).mpr hhQ
  push_cast at hhR
  have hratio : ((A + A).card : ℝ) / (A.card : ℝ) ≤ D := (div_le_iff₀ hAp).mpr hdouble
  exact hhR.trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (by positivity) hratio _) hAp.le)

theorem finite_three_two_hull_card {G : Type*} [AddCommGroup G] [DecidableEq G]
    {A : Finset G} {D : ℝ} (hA : A.Nonempty) (hD : 0 ≤ D)
    (hdouble : ((A + A).card : ℝ) ≤ D * (A.card : ℝ)) :
    (((A + (A - A)) + (A - A)).card : ℝ) ≤ D ^ (5 : ℕ) * (A.card : ℝ) := by
  have heq : (A + (A - A)) + (A - A) = (3 : ℕ) • A - (2 : ℕ) • A := by
    simp only [succ_nsmul, zero_nsmul, zero_add, sub_eq_add_neg, neg_add_rev,
      neg_zero, add_zero]
    ac_rfl
  rw [heq]
  exact finite_signed_sum_card_bound hA hD hdouble 3 2

theorem ring_sum_stabilizer_cover {R : Type*} [Ring R] [Fintype R] [DecidableEq R]
    {A : Finset R} {K : ℝ} {x : R} (hA : A.Nonempty) (hx : x ∈ ringSumStabilizer A K) :
    ∃ F : Finset R, F ⊆ ringDilate x A ∧ (F.card : ℝ) ≤ K ∧ ringDilate x A ⊆ F + (A - A) := by
  exact Finset.ruzsa_covering_add hA (by
    rw [add_comm]
    exact (mem_ring_sum_stabilizer A K x).mp hx)

theorem ring_dilate_subset {R : Type*} [Ring R] [DecidableEq R] (x : R)
    {A B : Finset R} (hAB : A ⊆ B) : ringDilate x A ⊆ ringDilate x B :=
  Finset.image_subset_image hAB

theorem ring_dilate_scalar_add_subset {R : Type*} [Ring R] [DecidableEq R] (x y : R) (A : Finset R) :
    ringDilate (x + y) A ⊆ ringDilate x A + ringDilate y A := by
  intro z hz
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
  exact Finset.mem_add.mpr ⟨x * a, Finset.mem_image_of_mem _ ha,
    y * a, Finset.mem_image_of_mem _ ha, (add_mul x y a).symm⟩

theorem finite_three_sum_card_bound {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A B C : Finset G) : (A + B + C).card ≤ A.card * B.card * C.card :=
  Finset.card_add_le.trans (Nat.mul_le_mul_right _ Finset.card_add_le)

theorem ring_sum_stabilizer_add {R : Type*} [Ring R] [Fintype R] [DecidableEq R]
    {A : Finset R} {D K L : ℝ} {x y : R} (hA : A.Nonempty)
    (hD : 0 ≤ D) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hdouble : ((A + A).card : ℝ) ≤ D * (A.card : ℝ))
    (hx : x ∈ ringSumStabilizer A K) (hy : y ∈ ringSumStabilizer A L) :
    x + y ∈ ringSumStabilizer A (K * L * D ^ (5 : ℕ)) := by
  obtain ⟨F, hFx, hF, hcoverx⟩ := ring_sum_stabilizer_cover hA hx
  obtain ⟨G, hGy, hG, hcovery⟩ := ring_sum_stabilizer_cover hA hy
  let H := (A + (A - A)) + (A - A)
  have hsub : A + ringDilate (x + y) A ⊆ F + G + H := by
    calc
      _ ⊆ A + (ringDilate x A + ringDilate y A) :=
        Finset.add_subset_add_left (ring_dilate_scalar_add_subset x y A)
      _ ⊆ A + ((F + (A - A)) + (G + (A - A))) :=
        Finset.add_subset_add_left (Finset.add_subset_add hcoverx hcovery)
      _ = _ := by dsimp only [H]; ac_rfl
  rw [mem_ring_sum_stabilizer]
  calc
    _ ≤ ((F + G + H).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
    _ ≤ (F.card : ℝ) * (G.card : ℝ) * (H.card : ℝ) := by
      exact_mod_cast finite_three_sum_card_bound F G H
    _ ≤ K * L * (D ^ (5 : ℕ) * (A.card : ℝ)) := by
      gcongr
      exact finite_three_two_hull_card hA hD hdouble
    _ = _ := by ring

theorem ring_sum_stabilizer_mul {R : Type*} [Ring R] [Fintype R] [DecidableEq R]
    {A : Finset R} {D K L : ℝ} {x y : R} (hA : A.Nonempty)
    (hD : 0 ≤ D) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hdouble : ((A + A).card : ℝ) ≤ D * (A.card : ℝ))
    (hx : x ∈ ringSumStabilizer A K) (hy : y ∈ ringSumStabilizer A L) :
    x * y ∈ ringSumStabilizer A (K ^ 2 * L * D ^ (5 : ℕ)) := by
  obtain ⟨F, hFx, hF, hcoverx⟩ := ring_sum_stabilizer_cover hA hx
  obtain ⟨G, hGy, hG, hcovery⟩ := ring_sum_stabilizer_cover hA hy
  let H := (A + (A - A)) + (A - A)
  have hsub : A + ringDilate (x * y) A ⊆ (ringDilate x G + (F - F)) + H := by
    calc
      _ = A + ringDilate x (ringDilate y A) := by rw [ring_dilate_mul]
      _ ⊆ A + ringDilate x (G + (A - A)) :=
        Finset.add_subset_add_left (ring_dilate_subset x hcovery)
      _ = A + (ringDilate x G + (ringDilate x A - ringDilate x A)) := by
        rw [ring_dilate_add, ring_dilate_sub]
      _ ⊆ A + (ringDilate x G + ((F + (A - A)) - (F + (A - A)))) :=
        Finset.add_subset_add_left (Finset.add_subset_add_left (Finset.sub_subset_sub hcoverx hcoverx))
      _ = _ := by
        dsimp only [H]
        simp only [sub_eq_add_neg, neg_add_rev, neg_neg]
        ac_rfl
  have hcardx : ((ringDilate x G).card : ℝ) ≤ G.card := by exact_mod_cast Finset.card_image_le
  have hcardF : ((F - F).card : ℝ) ≤ (F.card : ℝ) ^ 2 := by
    exact_mod_cast (Finset.card_sub_le : (F - F).card ≤ F.card * F.card).trans_eq (pow_two F.card).symm
  rw [mem_ring_sum_stabilizer]
  calc
    _ ≤ (((ringDilate x G + (F - F)) + H).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
    _ ≤ ((ringDilate x G).card : ℝ) * ((F - F).card : ℝ) * (H.card : ℝ) := by
      exact_mod_cast finite_three_sum_card_bound (ringDilate x G) (F - F) H
    _ ≤ L * K ^ 2 * (D ^ (5 : ℕ) * (A.card : ℝ)) := by
      gcongr
      · exact hcardx.trans hG
      · exact hcardF.trans (pow_le_pow_left₀ (Nat.cast_nonneg _) hF 2)
      · exact finite_three_two_hull_card hA hD hdouble
    _ = _ := by ring

theorem ring_dilate_neg {R : Type*} [Ring R] [DecidableEq R] (x : R) (A : Finset R) :
    ringDilate (-x) A = -(ringDilate x A) := by
  ext z
  simp only [ringDilate, Finset.mem_image, Finset.mem_neg, neg_mul, neg_eq_iff_eq_neg]
  aesop

theorem ring_sum_stabilizer_neg {R : Type*} [Ring R] [Fintype R] [DecidableEq R]
    {A : Finset R} {D K : ℝ} {x : R} (hA : A.Nonempty) (hD : 0 ≤ D) (hK : 0 ≤ K)
    (hdouble : ((A + A).card : ℝ) ≤ D * (A.card : ℝ))
    (hx : x ∈ ringSumStabilizer A K) : -x ∈ ringSumStabilizer A (D * K) := by
  have hAp : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have hh : ((A - ringDilate x A).card : ℝ) * (A.card : ℝ) ≤
      ((A + A).card : ℝ) * ((ringDilate x A + A).card : ℝ) := by
    exact_mod_cast Finset.ruzsa_triangle_inequality_sub_add_add A A (ringDilate x A)
  have hx' : ((ringDilate x A + A).card : ℝ) ≤ K * (A.card : ℝ) := by
    rw [add_comm]
    exact (mem_ring_sum_stabilizer A K x).mp hx
  rw [mem_ring_sum_stabilizer, ring_dilate_neg, ← sub_eq_add_neg]
  apply (mul_le_mul_iff_left₀ hAp).mp
  calc
    _ ≤ _ := hh
    _ ≤ (D * (A.card : ℝ)) * (K * (A.card : ℝ)) := by gcongr
    _ = _ := by ring

theorem ring_sum_stabilizer_mono {R : Type*} [Ring R] [Fintype R] [DecidableEq R]
    (A : Finset R) {K L : ℝ} (hKL : K ≤ L) : ringSumStabilizer A K ⊆ ringSumStabilizer A L := by
  intro x hx
  rw [mem_ring_sum_stabilizer] at hx ⊢
  exact hx.trans (mul_le_mul_of_nonneg_right hKL (Nat.cast_nonneg _))

theorem ring_sum_stabilizer_zero {R : Type*} [Ring R] [Fintype R] [DecidableEq R]
    {A : Finset R} {K : ℝ} (hA : A.Nonempty) (hK : 1 ≤ K) : 0 ∈ ringSumStabilizer A K := by
  have hz : ringDilate (0 : R) A = {0} := by
    ext z
    simp only [ringDilate, Finset.mem_image, zero_mul, Finset.mem_singleton]
    constructor
    · rintro ⟨a, ha, hz⟩
      exact hz.symm
    · intro hz
      obtain ⟨a, ha⟩ := hA
      exact ⟨a, ha, hz.symm⟩
  rw [mem_ring_sum_stabilizer, hz]
  have heq : A + ({0} : Finset R) = A := by change A + 0 = A; exact add_zero A
  rw [heq]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hK (Nat.cast_nonneg A.card : (0 : ℝ) ≤ A.card)

theorem ring_sum_stabilizer_one {R : Type*} [Ring R] [Fintype R] [DecidableEq R]
    {A : Finset R} {K : ℝ} (hdouble : ((A + A).card : ℝ) ≤ K * (A.card : ℝ)) :
    1 ∈ ringSumStabilizer A K := by
  rw [mem_ring_sum_stabilizer, ring_dilate_one]
  exact hdouble

theorem ring_sum_stabilizer_unit_doubling {R : Type*} [Ring R] [Fintype R] [DecidableEq R]
    {A : Finset R} {K : ℝ} (hA : A.Nonempty) (hK : 0 ≤ K) (u : Rˣ)
    (hu : (u : R) ∈ ringSumStabilizer A K) :
    ((A + A).card : ℝ) ≤ K ^ 2 * (A.card : ℝ) := by
  have hAp : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have hh : ((A + A).card : ℝ) * (A.card : ℝ) ≤
      ((A + ringDilate (u : R) A).card : ℝ) ^ 2 := by
    have hh' := Finset.ruzsa_triangle_inequality_add_add_add A (ringDilate (u : R) A) A
    rw [ring_dilate_unit_card, add_comm (ringDilate (u : R) A) A] at hh'
    exact_mod_cast hh'.trans_eq (pow_two (A + ringDilate (u : R) A).card).symm
  have hbound := (mem_ring_sum_stabilizer A K (u : R)).mp hu
  apply (mul_le_mul_iff_left₀ hAp).mp
  calc
    _ ≤ _ := hh
    _ ≤ (K * (A.card : ℝ)) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hbound 2
    _ = _ := by ring

theorem ring_sum_stabilizer_add_power {R : Type*} [Ring R] [Fintype R] [DecidableEq R]
    {A : Finset R} {K : ℝ} {x y : R} (hA : A.Nonempty) (hK : 1 ≤ K)
    (hdouble : ((A + A).card : ℝ) ≤ K * (A.card : ℝ))
    (hx : x ∈ ringSumStabilizer A K) (hy : y ∈ ringSumStabilizer A K) :
    x + y ∈ ringSumStabilizer A (K ^ (8 : ℕ)) := by
  have hK0 : 0 ≤ K := (by norm_num : (0 : ℝ) ≤ 1).trans hK
  have hh := ring_sum_stabilizer_add hA hK0 hK0 hK0 hdouble hx hy
  apply ring_sum_stabilizer_mono A (show K * K * K ^ (5 : ℕ) ≤ K ^ (8 : ℕ) from ?_) hh
  calc
    _ = K ^ (7 : ℕ) := by ring
    _ ≤ _ := pow_le_pow_right₀ hK (by norm_num)

theorem ring_sum_stabilizer_mul_power {R : Type*} [Ring R] [Fintype R] [DecidableEq R]
    {A : Finset R} {K : ℝ} {x y : R} (hA : A.Nonempty) (hK : 1 ≤ K)
    (hdouble : ((A + A).card : ℝ) ≤ K * (A.card : ℝ))
    (hx : x ∈ ringSumStabilizer A K) (hy : y ∈ ringSumStabilizer A K) :
    x * y ∈ ringSumStabilizer A (K ^ (8 : ℕ)) := by
  have hK0 : 0 ≤ K := (by norm_num : (0 : ℝ) ≤ 1).trans hK
  have hh := ring_sum_stabilizer_mul hA hK0 hK0 hK0 hdouble hx hy
  have heq : K ^ (2 : ℕ) * K * K ^ (5 : ℕ) = K ^ (8 : ℕ) := by ring
  rwa [heq] at hh

theorem ring_sum_stabilizer_neg_power {R : Type*} [Ring R] [Fintype R] [DecidableEq R]
    {A : Finset R} {K : ℝ} {x : R} (hA : A.Nonempty) (hK : 1 ≤ K)
    (hdouble : ((A + A).card : ℝ) ≤ K * (A.card : ℝ))
    (hx : x ∈ ringSumStabilizer A K) : -x ∈ ringSumStabilizer A (K ^ (8 : ℕ)) := by
  have hK0 : 0 ≤ K := (by norm_num : (0 : ℝ) ≤ 1).trans hK
  have hh := ring_sum_stabilizer_neg hA hK0 hK0 hdouble hx
  apply ring_sum_stabilizer_mono A (show K * K ≤ K ^ (8 : ℕ) from ?_) hh
  calc
    _ = K ^ (2 : ℕ) := by ring
    _ ≤ _ := pow_le_pow_right₀ hK (by norm_num)

/-- The sum-product closure used in the growth theorem remains a stabilizer,
with a fixed power loss in the parameter. This does not require units. -/
theorem ring_sum_stabilizer_quadratic_closure {R : Type*} [Ring R] [Fintype R] [DecidableEq R]
    {A S : Finset R} {K : ℝ} (hA : A.Nonempty) (hK : 1 ≤ K)
    (hdouble : ((A + A).card : ℝ) ≤ K * (A.card : ℝ)) (hS : S ⊆ ringSumStabilizer A K) :
    (insert 0 (S ∪ S * S) + insert 0 (S ∪ S * S)) ⊆ ringSumStabilizer A (K ^ (64 : ℕ)) := by
  have hKK : K ≤ K ^ (8 : ℕ) := by
    simpa only [pow_one] using pow_le_pow_right₀ hK (show 1 ≤ (8 : ℕ) by norm_num)
  have hF : insert 0 (S ∪ S * S) ⊆ ringSumStabilizer A (K ^ (8 : ℕ)) := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ring_sum_stabilizer_mono A hKK (ring_sum_stabilizer_zero hA hK)
    · rcases Finset.mem_union.mp hx with hx | hx
      · exact ring_sum_stabilizer_mono A hKK (hS hx)
      · obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_mul.mp hx
        exact ring_sum_stabilizer_mul_power hA hK hdouble (hS ha) (hS hb)
  intro z hz
  obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp hz
  have hdouble' : ((A + A).card : ℝ) ≤ K ^ (8 : ℕ) * (A.card : ℝ) :=
    hdouble.trans (mul_le_mul_of_nonneg_right hKK (Nat.cast_nonneg _))
  have hh := ring_sum_stabilizer_add_power hA (one_le_pow₀ hK) hdouble' (hF hx) (hF hy)
  simpa only [← pow_mul, show (8 : ℕ) * 8 = 64 from rfl] using hh


/- Fourier averaging and a density bound for all additive stabilizers. -/

theorem cyclic_set_indicator_norm {q : ℕ} [NeZero q] (A : Finset (ZMod q)) (x : ZMod q) :
    ‖cyclicSetIndicator A x‖ = if x ∈ A then (1 : ℝ) else 0 := by
  classical
  by_cases hx : x ∈ A <;> simp [cyclicSetIndicator, hx]

theorem cyclic_set_indicator_norm_sum {q : ℕ} [NeZero q] (A : Finset (ZMod q)) :
    (∑ x : ZMod q, ‖cyclicSetIndicator A x‖) = (A.card : ℝ) := by
  classical
  simp [cyclic_set_indicator_norm]

theorem cyclic_set_indicator_sq_norm_sum {q : ℕ} [NeZero q] (A : Finset (ZMod q)) :
    (∑ x : ZMod q, ‖cyclicSetIndicator A x‖ ^ 2) = (A.card : ℝ) := by
  classical
  simp [cyclic_set_indicator_norm, ite_pow]

theorem cyclic_set_indicator_pushforward {q : ℕ} [NeZero q]
    (A : Finset (ZMod q)) (T : ZMod q → ZMod q) (z : ZMod q) :
    cyclicPushforward (cyclicSetIndicator A) T z = ((A.filter (fun x => T x = z)).card : ℂ) := by
  classical
  have heq (x : ZMod q) : (if T x = z then (if x ∈ A then (1 : ℂ) else 0) else 0) =
      if x ∈ A then (if T x = z then (1 : ℂ) else 0) else 0 := by
    by_cases hx : x ∈ A <;> by_cases hz : T x = z <;> simp [hx, hz]
  unfold cyclicPushforward cyclicSetIndicator
  simp_rw [heq]
  simp only [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter,
    Finset.sum_const, nsmul_eq_mul, mul_one]

theorem cyclic_set_pushforward_norm_sum {q : ℕ} [NeZero q]
    (A : Finset (ZMod q)) (T : ZMod q → ZMod q) :
    (∑ z : ZMod q, ‖cyclicPushforward (cyclicSetIndicator A) T z‖) = (A.card : ℝ) := by
  simp_rw [cyclic_set_indicator_pushforward, Complex.norm_natCast]
  exact_mod_cast (Finset.card_eq_sum_card_fiberwise (f := T) (s := A)
    (t := Finset.univ) (fun _ _ => Finset.mem_univ _)).symm

theorem dft_cyclic_pushforward_mul {q : ℕ} [NeZero q]
    (f : ZMod q → ℂ) (k x : ZMod q) :
    ZMod.dft (cyclicPushforward f (fun a => a * k)) x = ZMod.dft f (x * k) := by
  rw [dft_cyclicPushforward, ZMod.dft_apply]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [smul_eq_mul]
  rw [show a * k * x = a * (x * k) by ring]

theorem uniform_mul_fourier_energy_eq_pushforward {q : ℕ} [NeZero q]
    (f : ZMod q → ℂ) (k : ZMod q) :
    (∑ x : ZMod q, (1 / (q : ℝ)) * ‖ZMod.dft f (x * k)‖ ^ 2) =
      ∑ z : ZMod q, ‖cyclicPushforward f (fun a => a * k) z‖ ^ 2 := by
  have hh := dft_parseval (cyclicPushforward f (fun a => a * k))
  simp_rw [dft_cyclic_pushforward_mul] at hh
  rw [← Finset.mul_sum, hh]
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q
  field_simp

theorem uniform_set_fourier_energy_le_fibers {q : ℕ} [NeZero q]
    (A : Finset (ZMod q)) (k : ZMod q) {M : ℝ}
    (hM : ∀ z : ZMod q, ((A.filter (fun a => a * k = z)).card : ℝ) ≤ M) :
    (∑ x : ZMod q, (1 / (q : ℝ)) * ‖ZMod.dft (cyclicSetIndicator A) (x * k)‖ ^ 2) ≤
      M * (A.card : ℝ) := by
  rw [uniform_mul_fourier_energy_eq_pushforward]
  calc
    _ ≤ ∑ z : ZMod q, M * ‖cyclicPushforward (cyclicSetIndicator A) (fun a => a * k) z‖ := by
      apply Finset.sum_le_sum
      intro z hz
      have hb : ‖cyclicPushforward (cyclicSetIndicator A) (fun a => a * k) z‖ ≤ M := by
        simpa only [cyclic_set_indicator_pushforward, Complex.norm_natCast] using hM z
      simpa only [pow_two] using mul_le_mul_of_nonneg_right hb (norm_nonneg _)
    _ = _ := by rw [← Finset.mul_sum, cyclic_set_pushforward_norm_sum]

theorem finite_fiber_card_le_of_kernel {α β κ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq κ]
    (A : Finset α) (f : α → β) (g : α → κ) {M : ℝ} (hM : 0 ≤ M)
    (hkernel : ∀ a b : α, f a = f b → g a = g b)
    (hbound : ∀ r : κ, ((A.filter (fun a => g a = r)).card : ℝ) ≤ M) :
    ∀ z : β, ((A.filter (fun a => f a = z)).card : ℝ) ≤ M := by
  classical
  intro z
  by_cases hF : (A.filter (fun a => f a = z)).Nonempty
  · obtain ⟨a₀, ha₀⟩ := hF
    have hsub : A.filter (fun a => f a = z) ⊆ A.filter (fun a => g a = g a₀) := by
      intro a ha
      obtain ⟨haA, haz⟩ := Finset.mem_filter.mp ha
      exact Finset.mem_filter.mpr ⟨haA, hkernel a a₀ (haz.trans (Finset.mem_filter.mp ha₀).2.symm)⟩
    exact (show ((A.filter (fun a => f a = z)).card : ℝ) ≤
      ((A.filter (fun a => g a = g a₀)).card : ℝ) by exact_mod_cast Finset.card_le_card hsub).trans (hbound _)
  · simpa only [Finset.not_nonempty_iff_eq_empty.mp hF, Finset.card_empty, Nat.cast_zero] using hM

theorem dyadic_mul_kernel_refines_coarse {J L : ℕ} (hL : L ≤ J) {k : ZMod (2 ^ J)}
    (hk : L ≤ dyadicConductorLevel k) (a b : ZMod (2 ^ J)) (hab : a * k = b * k) :
    (a.val : ZMod (2 ^ L)) = (b.val : ZMod (2 ^ L)) := by
  have hkill : (a - b) * k = 0 := by rw [sub_mul, hab, sub_self]
  have hd : addOrderOf k ∣ (a - b).val := by
    apply addOrderOf_dvd_iff_nsmul_eq_zero.mpr
    simpa only [nsmul_eq_mul, ZMod.natCast_zmod_val] using hkill
  rw [(dyadic_conductor_spec k).2] at hd
  have hdL : 2 ^ L ∣ (a - b).val := (pow_dvd_pow 2 hk).trans hd
  have hh := dyadic_sub_val_mod hL a.val b.val
  simp only [ZMod.natCast_zmod_val] at hh
  have hzero : ((a.val : ZMod (2 ^ L)) - (b.val : ZMod (2 ^ L))).val = 0 :=
    hh.symm.trans (Nat.mod_eq_zero_of_dvd hdL)
  apply sub_eq_zero.mp
  apply ZMod.val_injective (2 ^ L)
  simpa only [ZMod.val_zero] using hzero

theorem dyadic_uniform_set_fourier_energy_coarse {J L : ℕ} (hL : L ≤ J)
    (A : Finset (ZMod (2 ^ J))) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ r : ZMod (2 ^ L),
      ((A.filter (fun a => (a.val : ZMod (2 ^ L)) = r)).card : ℝ) ≤ M * (A.card : ℝ))
    {k : ZMod (2 ^ J)} (hk : L ≤ dyadicConductorLevel k) :
    (∑ x : ZMod (2 ^ J), (1 / ((2 ^ J : ℕ) : ℝ)) *
      ‖ZMod.dft (cyclicSetIndicator A) (x * k)‖ ^ 2) ≤ M * (A.card : ℝ) ^ 2 := by
  have hfiber := finite_fiber_card_le_of_kernel A (fun a => a * k)
    (fun a => (a.val : ZMod (2 ^ L))) (show 0 ≤ M * (A.card : ℝ) by positivity)
    (dyadic_mul_kernel_refines_coarse hL hk) hbound
  have hh := uniform_set_fourier_energy_le_fibers A k hfiber
  simpa only [mul_assoc, pow_two] using hh

theorem dyadic_low_conductor_card_le {J L : ℕ} (hL : L ≤ J) :
    (Finset.univ.filter (fun k : ZMod (2 ^ J) => dyadicConductorLevel k ≤ L)).card ≤ 2 ^ L := by
  classical
  have hsub : (Finset.univ.filter (fun k : ZMod (2 ^ J) => dyadicConductorLevel k ≤ L)) ⊆
      Finset.univ.filter (fun k : ZMod (2 ^ J) => k * ((2 ^ L : ℕ) : ZMod (2 ^ J)) = 0) := by
    intro k hk
    have hh := dyadic_conductor_power_nsmul_eq_zero (Finset.mem_filter.mp hk).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      simpa only [nsmul_eq_mul, mul_comm] using hh⟩
  calc
    _ ≤ (Finset.univ.filter (fun k : ZMod (2 ^ J) => k * ((2 ^ L : ℕ) : ZMod (2 ^ J)) = 0)).card :=
      Finset.card_le_card hsub
    _ ≤ (2 ^ J).gcd (2 ^ L) := zmod_mul_zero_fiber_card_le (2 ^ L)
    _ = _ := Nat.gcd_eq_right (pow_dvd_pow 2 hL)

noncomputable def cyclicSetDilateCollision {q : ℕ} [NeZero q]
    (A : Finset (ZMod q)) (x : ZMod q) : ℝ :=
  ∑ z : ZMod q, ‖cyclicConvolution (cyclicSetIndicator A)
    (cyclicPushforward (cyclicSetIndicator A) (fun a => a * x)) z‖ ^ 2

theorem cyclic_set_dilate_collision_nonneg {q : ℕ} [NeZero q]
    (A : Finset (ZMod q)) (x : ZMod q) : 0 ≤ cyclicSetDilateCollision A x := by
  unfold cyclicSetDilateCollision
  positivity

theorem cyclic_set_dilate_collision_fourier {q : ℕ} [NeZero q]
    (A : Finset (ZMod q)) (x : ZMod q) :
    (q : ℝ) * cyclicSetDilateCollision A x =
      ∑ k : ZMod q, ‖ZMod.dft (cyclicSetIndicator A) k‖ ^ 2 *
        ‖ZMod.dft (cyclicSetIndicator A) (k * x)‖ ^ 2 := by
  unfold cyclicSetDilateCollision
  rw [← dft_parseval]
  simp only [dft_cyclicConvolution, dft_cyclic_pushforward_mul, norm_mul, mul_pow]

theorem cyclic_set_dilate_collision_sum_fourier {q : ℕ} [NeZero q]
    (A : Finset (ZMod q)) :
    (q : ℝ) * (∑ x : ZMod q, cyclicSetDilateCollision A x) =
      ∑ k : ZMod q, ‖ZMod.dft (cyclicSetIndicator A) k‖ ^ 2 *
        (∑ x : ZMod q, ‖ZMod.dft (cyclicSetIndicator A) (x * k)‖ ^ 2) := by
  rw [Finset.mul_sum]
  simp_rw [cyclic_set_dilate_collision_fourier]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [mul_comm x k]

/-- Coarse residue control bounds the average additive collision of all dilates,
including multiplication by nonunits. -/
theorem dyadic_set_dilate_collision_sum_bound {J L : ℕ} (hL : L ≤ J)
    (A : Finset (ZMod (2 ^ J))) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ r : ZMod (2 ^ L),
      ((A.filter (fun a => (a.val : ZMod (2 ^ L)) = r)).card : ℝ) ≤ M * (A.card : ℝ)) :
    (∑ x : ZMod (2 ^ J), cyclicSetDilateCollision A x) ≤
      (2 : ℝ) ^ L * (A.card : ℝ) ^ 4 + (2 : ℝ) ^ J * M * (A.card : ℝ) ^ 3 := by
  classical
  let F := fun k : ZMod (2 ^ J) => ‖ZMod.dft (cyclicSetIndicator A) k‖ ^ 2
  let Q : ℝ := (2 : ℝ) ^ J
  let Z := Finset.univ.filter (fun k : ZMod (2 ^ J) => dyadicConductorLevel k ≤ L)
  have hQ : 0 < Q := by dsimp only [Q]; positivity
  have hF (k : ZMod (2 ^ J)) : 0 ≤ F k := sq_nonneg _
  have hFbound (k : ZMod (2 ^ J)) : F k ≤ (A.card : ℝ) ^ 2 := by
    have hh := norm_dft_le_sum_norm (cyclicSetIndicator A) k
    rw [cyclic_set_indicator_norm_sum] at hh
    exact pow_le_pow_left₀ (norm_nonneg _) hh 2
  have hsumF : (∑ k : ZMod (2 ^ J), F k) = Q * (A.card : ℝ) := by
    simpa only [F, Q, Nat.cast_pow, Nat.cast_ofNat, cyclic_set_indicator_sq_norm_sum] using
      dft_parseval (cyclicSetIndicator A)
  have hsum (k : ZMod (2 ^ J)) : (∑ x : ZMod (2 ^ J), F (x * k)) ≤ Q * (A.card : ℝ) ^ 2 := by
    calc
      _ ≤ ∑ _x : ZMod (2 ^ J), (A.card : ℝ) ^ 2 := Finset.sum_le_sum (fun x _ => hFbound _)
      _ = _ := by simp [Q]
  have hhigh (k : ZMod (2 ^ J)) (hk : k ∉ Z) :
      (∑ x : ZMod (2 ^ J), F (x * k)) ≤ Q * M * (A.card : ℝ) ^ 2 := by
    have hkL : L ≤ dyadicConductorLevel k := by
      have hh : ¬ dyadicConductorLevel k ≤ L := by
        intro hh
        exact hk (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩)
      omega
    have hh := dyadic_uniform_set_fourier_energy_coarse hL A hM hbound hkL
    have heq : (∑ x : ZMod (2 ^ J), F (x * k)) =
        Q * (∑ x : ZMod (2 ^ J), (1 / ((2 ^ J : ℕ) : ℝ)) * F (x * k)) := by
      rw [← Finset.mul_sum]
      simp only [Nat.cast_pow, Nat.cast_ofNat]
      dsimp only [Q]
      field_simp
    calc
      _ = _ := heq
      _ ≤ Q * (M * (A.card : ℝ) ^ 2) := mul_le_mul_of_nonneg_left hh hQ.le
      _ = _ := by ring
  have hpoint (k : ZMod (2 ^ J)) : F k * (∑ x : ZMod (2 ^ J), F (x * k)) ≤
      (if k ∈ Z then Q * (A.card : ℝ) ^ 4 else 0) + Q * M * (A.card : ℝ) ^ 2 * F k := by
    by_cases hk : k ∈ Z
    · rw [if_pos hk]
      calc
        _ ≤ (A.card : ℝ) ^ 2 * (Q * (A.card : ℝ) ^ 2) :=
          mul_le_mul (hFbound k) (hsum k) (Finset.sum_nonneg (fun _ _ => hF _)) (by positivity)
        _ = Q * (A.card : ℝ) ^ 4 := by ring
        _ ≤ _ := le_add_of_nonneg_right (by positivity)
    · rw [if_neg hk, zero_add]
      calc
        _ ≤ F k * (Q * M * (A.card : ℝ) ^ 2) := mul_le_mul_of_nonneg_left (hhigh k hk) (hF k)
        _ = _ := by ring
  have hZ : (Z.card : ℝ) ≤ (2 : ℝ) ^ L := by exact_mod_cast dyadic_low_conductor_card_le hL
  apply (mul_le_mul_iff_right₀ hQ).mp
  calc
    _ = ∑ k : ZMod (2 ^ J), F k * (∑ x : ZMod (2 ^ J), F (x * k)) := by
      simpa only [Q, F, Nat.cast_pow, Nat.cast_ofNat] using cyclic_set_dilate_collision_sum_fourier A
    _ ≤ ∑ k : ZMod (2 ^ J), ((if k ∈ Z then Q * (A.card : ℝ) ^ 4 else 0) +
        Q * M * (A.card : ℝ) ^ 2 * F k) := Finset.sum_le_sum (fun k _ => hpoint k)
    _ = (Z.card : ℝ) * (Q * (A.card : ℝ) ^ 4) + Q * M * (A.card : ℝ) ^ 2 * (Q * (A.card : ℝ)) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsumF]
      rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
      simp
    _ ≤ (2 : ℝ) ^ L * (Q * (A.card : ℝ) ^ 4) + Q * M * (A.card : ℝ) ^ 2 * (Q * (A.card : ℝ)) := by
      gcongr
    _ = _ := by dsimp only [Q]; ring

theorem cyclic_convolution_set_indicator_left {q : ℕ} [NeZero q]
    (A : Finset (ZMod q)) (g : ZMod q → ℂ) (z : ZMod q) :
    cyclicConvolution (cyclicSetIndicator A) g z = ∑ a ∈ A, g (z - a) := by
  classical
  simp only [cyclicConvolution, cyclicSetIndicator, ite_mul, one_mul, zero_mul,
    ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]

theorem cyclic_set_dilate_convolution_card {q : ℕ} [NeZero q]
    (A : Finset (ZMod q)) (x z : ZMod q) :
    cyclicConvolution (cyclicSetIndicator A)
      (cyclicPushforward (cyclicSetIndicator A) (fun a => a * x)) z =
      (((A ×ˢ A).filter (fun p => p.1 + p.2 * x = z)).card : ℂ) := by
  classical
  rw [cyclic_convolution_set_indicator_left]
  simp_rw [cyclic_set_indicator_pushforward]
  simp only [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one,
    Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  have heq : b * x = z - a ↔ a + b * x = z := by
    constructor
    · intro h
      rw [h, add_sub_cancel]
    · intro h
      rw [← h, add_sub_cancel_left]
  simp only [heq, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

theorem finite_map_collision_lower {α β : Type*} [DecidableEq α] [DecidableEq β] [Fintype β]
    (A : Finset α) (f : α → β) :
    (A.card : ℝ) ^ 2 ≤ ((A.image f).card : ℝ) *
      ∑ y : β, ((A.filter (fun a => f a = y)).card : ℝ) ^ 2 := by
  have hsum : (∑ y ∈ A.image f, ((A.filter (fun a => f a = y)).card : ℝ)) = (A.card : ℝ) := by
    exact_mod_cast (Finset.card_eq_sum_card_image f A).symm
  have hh := Finset.sum_mul_sq_le_sq_mul_sq (A.image f) (fun _ => (1 : ℝ))
    (fun y => ((A.filter (fun a => f a = y)).card : ℝ))
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, hsum] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _))
    (Nat.cast_nonneg _))

theorem ring_sum_dilate_product_image {R : Type*} [CommRing R] [DecidableEq R]
    (A : Finset R) (x : R) :
    (A ×ˢ A).image (fun p => p.1 + p.2 * x) = A + ringDilate x A := by
  ext z
  constructor
  · intro hz
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
    exact Finset.mem_add.mpr ⟨a, ha, x * b, Finset.mem_image_of_mem _ hb, by rw [mul_comm x b]⟩
  · intro hz
    obtain ⟨a, ha, y, hy, rfl⟩ := Finset.mem_add.mp hz
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_image.mpr ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, by rw [mul_comm b x]⟩

theorem cyclic_set_dilate_sumset_collision {q : ℕ} [NeZero q]
    (A : Finset (ZMod q)) (x : ZMod q) :
    (A.card : ℝ) ^ 4 ≤ ((A + ringDilate x A).card : ℝ) * cyclicSetDilateCollision A x := by
  have hh := finite_map_collision_lower (A ×ˢ A) (fun p => p.1 + p.2 * x)
  rw [ring_sum_dilate_product_image] at hh
  have heq : cyclicSetDilateCollision A x =
      ∑ z : ZMod q, (((A ×ˢ A).filter (fun p => p.1 + p.2 * x = z)).card : ℝ) ^ 2 := by
    simp only [cyclicSetDilateCollision, cyclic_set_dilate_convolution_card, Complex.norm_natCast]
  rw [heq]
  calc
    _ = ((A ×ˢ A).card : ℝ) ^ 2 := by rw [Finset.card_product, Nat.cast_mul]; ring
    _ ≤ _ := hh

theorem ring_sum_stabilizer_collision_lower {q : ℕ} [NeZero q]
    {A : Finset (ZMod q)} {K : ℝ} {x : ZMod q} (hA : A.Nonempty)
    (hx : x ∈ ringSumStabilizer A K) :
    (A.card : ℝ) ^ 3 ≤ K * cyclicSetDilateCollision A x := by
  have hAp : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have hx' := (mem_ring_sum_stabilizer A K x).mp hx
  apply (mul_le_mul_iff_right₀ hAp).mp
  calc
    _ = (A.card : ℝ) ^ 4 := by ring
    _ ≤ _ := cyclic_set_dilate_sumset_collision A x
    _ ≤ (K * (A.card : ℝ)) * cyclicSetDilateCollision A x :=
      mul_le_mul_of_nonneg_right hx' (cyclic_set_dilate_collision_nonneg A x)
    _ = _ := by ring

/-- A single coarse fiber bound controls the size of the full stabilizer,
without restricting its multipliers to units. -/
theorem dyadic_sum_stabilizer_card_bound {J L : ℕ} (hL : L ≤ J)
    {A : Finset (ZMod (2 ^ J))} {M K : ℝ} (hA : A.Nonempty) (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hbound : ∀ r : ZMod (2 ^ L),
      ((A.filter (fun a => (a.val : ZMod (2 ^ L)) = r)).card : ℝ) ≤ M * (A.card : ℝ)) :
    ((ringSumStabilizer A K).card : ℝ) ≤ K * ((2 : ℝ) ^ L * (A.card : ℝ) + (2 : ℝ) ^ J * M) := by
  have hAp : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  apply (mul_le_mul_iff_left₀ (show (0 : ℝ) < (A.card : ℝ) ^ 3 by positivity)).mp
  calc
    _ = ∑ _x ∈ ringSumStabilizer A K, (A.card : ℝ) ^ 3 := by simp
    _ ≤ ∑ x ∈ ringSumStabilizer A K, K * cyclicSetDilateCollision A x :=
      Finset.sum_le_sum (fun x hx => ring_sum_stabilizer_collision_lower hA hx)
    _ ≤ ∑ x : ZMod (2 ^ J), K * cyclicSetDilateCollision A x :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun x _ _ => mul_nonneg hK (cyclic_set_dilate_collision_nonneg A x))
    _ = K * ∑ x : ZMod (2 ^ J), cyclicSetDilateCollision A x := (Finset.mul_sum _ _ _).symm
    _ ≤ K * ((2 : ℝ) ^ L * (A.card : ℝ) ^ 4 + (2 : ℝ) ^ J * M * (A.card : ℝ) ^ 3) :=
      mul_le_mul_of_nonneg_left (dyadic_set_dilate_collision_sum_bound hL A hM hbound) hK
    _ = _ := by ring

/-- Nonconcentration and a density deficit force a power-saving upper bound
on every additive stabilizer, uniformly in its parameter. -/
theorem exists_dyadic_sum_stabilizer_density_bound {γ δ : ℝ}
    (hγ : 0 < γ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ c ε : ℝ, 0 < c ∧ 0 < ε ∧ ε ≤ 1 / 4 ∧ ∃ J₀ : ℕ,
      ∀ J : ℕ, J₀ ≤ J → ∀ A : Finset (ZMod (2 ^ J)), A.Nonempty →
        (A.card : ℝ) ≤ (2 : ℝ) ^ ((1 - δ) * (J : ℝ)) →
        (∀ L : ℕ, L ≤ J → ε * (J : ℝ) < (L : ℝ) → ∀ r : ZMod (2 ^ L),
          ((A.filter (fun a => (a.val : ZMod (2 ^ L)) = r)).card : ℝ) ≤
            (2 : ℝ) ^ (-γ * (L : ℝ)) * (A.card : ℝ)) →
        ∀ K : ℝ, 0 ≤ K → ((ringSumStabilizer A K).card : ℝ) ≤
          K * (2 : ℝ) ^ ((1 - c) * (J : ℝ)) := by
  let c₀ := min (δ / 2) (γ * δ / 4)
  have hc₀ : 0 < c₀ := lt_min (by positivity) (by positivity)
  have hcδ : c₀ ≤ δ / 2 := min_le_left _ _
  have hcγ : c₀ ≤ γ * δ / 4 := min_le_right _ _
  obtain ⟨J₀, hJ₀⟩ := exists_nat_ge (max (8 / δ) (2 / c₀))
  refine ⟨c₀ / 2, δ / 8, by positivity, by positivity, by linarith, J₀, ?_⟩
  intro J hJ A hA hsize hmass K hK
  have hJr : (J₀ : ℝ) ≤ J := by exact_mod_cast hJ
  have hJ8 : 8 / δ ≤ (J : ℝ) := (le_max_left _ _).trans (hJ₀.trans hJr)
  have hJ2 : 2 / c₀ ≤ (J : ℝ) := (le_max_right _ _).trans (hJ₀.trans hJr)
  have hδJ : 8 ≤ δ * (J : ℝ) := by
    have hh := (div_le_iff₀ hδ).mp hJ8
    nlinarith
  have hcJ : 2 ≤ c₀ * (J : ℝ) := by
    have hh := (div_le_iff₀ hc₀).mp hJ2
    nlinarith
  let L := Nat.floor (δ * (J : ℝ) / 2)
  have hLupper : (L : ℝ) ≤ δ * (J : ℝ) / 2 := Nat.floor_le (by positivity)
  have hLlt : δ * (J : ℝ) / 2 < (L : ℝ) + 1 := Nat.lt_floor_add_one _
  have hLlower : δ * (J : ℝ) / 4 ≤ (L : ℝ) := by linarith
  have hεL : δ / 8 * (J : ℝ) < (L : ℝ) := by nlinarith
  have hLJ : L ≤ J := by
    have hh : (L : ℝ) ≤ (J : ℝ) := by nlinarith [show (0 : ℝ) ≤ J from Nat.cast_nonneg _]
    exact_mod_cast hh
  have hcard := dyadic_sum_stabilizer_card_bound hLJ hA
    (show (0 : ℝ) ≤ (2 : ℝ) ^ (-γ * (L : ℝ)) by positivity) hK (hmass L hLJ hεL)
  have hfirst : (2 : ℝ) ^ L * (A.card : ℝ) ≤ (2 : ℝ) ^ ((1 - c₀) * (J : ℝ)) := by
    calc
      _ ≤ (2 : ℝ) ^ L * (2 : ℝ) ^ ((1 - δ) * (J : ℝ)) :=
        mul_le_mul_of_nonneg_left hsize (by positivity)
      _ = (2 : ℝ) ^ ((L : ℝ) + (1 - δ) * (J : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num)]
      _ ≤ _ := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        have hh := mul_le_mul_of_nonneg_right hcδ (Nat.cast_nonneg J : (0 : ℝ) ≤ J)
        nlinarith
  have hsecond : (2 : ℝ) ^ J * (2 : ℝ) ^ (-γ * (L : ℝ)) ≤
      (2 : ℝ) ^ ((1 - c₀) * (J : ℝ)) := by
    calc
      _ = (2 : ℝ) ^ ((J : ℝ) - γ * (L : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num)]
        congr 1
        ring
      _ ≤ _ := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        have hh := mul_le_mul_of_nonneg_right hcγ (Nat.cast_nonneg J : (0 : ℝ) ≤ J)
        have hl := mul_le_mul_of_nonneg_left hLlower hγ.le
        nlinarith
  have htwo : (2 : ℝ) ≤ (2 : ℝ) ^ ((c₀ / 2) * (J : ℝ)) := by
    calc
      _ = (2 : ℝ) ^ (1 : ℝ) := (Real.rpow_one 2).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
  calc
    _ ≤ K * ((2 : ℝ) ^ L * (A.card : ℝ) + (2 : ℝ) ^ J * (2 : ℝ) ^ (-γ * (L : ℝ))) := hcard
    _ ≤ K * ((2 : ℝ) ^ ((1 - c₀) * (J : ℝ)) + (2 : ℝ) ^ ((1 - c₀) * (J : ℝ))) := by gcongr
    _ = K * (2 * (2 : ℝ) ^ ((1 - c₀) * (J : ℝ))) := by ring
    _ ≤ K * ((2 : ℝ) ^ ((c₀ / 2) * (J : ℝ)) * (2 : ℝ) ^ ((1 - c₀) * (J : ℝ))) := by gcongr
    _ = _ := by
      rw [← Real.rpow_add (by norm_num)]
      congr 2
      ring



/- Iterated stabilizer growth and energy saving for unit dilates. -/

theorem exists_dyadic_sum_product_double_growth_of_projection {γ δ : ℝ}
    (hγ : 0 < γ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ σ ε : ℝ, 0 < σ ∧ 0 < ε ∧ ε ≤ 1 / 4 ∧ ∃ J₀ : ℕ,
      ∀ J : ℕ, J₀ ≤ J → ∀ A : Finset ℕ,
        A.Nonempty → (∀ x ∈ A, x < 2 ^ J) →
        (A.card : ℝ) ≤ (2 : ℝ) ^ ((1 - δ) * (J : ℝ)) →
        (∀ j : ℕ, j ≤ J → ε * (J : ℝ) < (j : ℝ) →
          (2 : ℝ) ^ (γ * (j : ℝ)) ≤ ((dyadicProjection A j).card : ℝ)) →
        (2 : ℝ) ^ (σ * (J : ℝ)) * (A.card : ℝ) ≤
          ((natResidueGenerators (natLinearQuadraticSet A) (2 ^ J) +
            natResidueGenerators (natLinearQuadraticSet A) (2 ^ J)).card : ℝ) := by
  obtain ⟨κ, ε, hκ, hε, hε4, K, J₀, hK, hgrowth⟩ :=
    exists_dyadic_signed_sum_product_growth hγ hδ hδ1
  let σ := κ / (4 * (K : ℝ) + 2)
  have hden : 0 < 4 * (K : ℝ) + 2 := by positivity
  have hσ : 0 < σ := div_pos hκ hden
  have hexp : σ * ((2 * K + 1 : ℕ) : ℝ) = κ / 2 := by
    dsimp [σ]
    push_cast
    field_simp
    ring
  refine ⟨σ, ε, hσ, hε, hε4, max J₀ 1, ?_⟩
  intro J hJ A hA hbound hsize hmass
  have hJ₀ : J₀ ≤ J := (le_max_left _ _).trans hJ
  have hJ1 : 1 ≤ J := (le_max_right _ _).trans hJ
  have hJp : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  have hAp : (0 : ℝ) < A.card := by exact_mod_cast Finset.card_pos.mpr hA
  by_contra h
  have hupper := nat_signed_hull_bound_of_double_bound (natLinearQuadraticSet A) K
    (q := 2 ^ J) (by exact_mod_cast nat_linear_quadratic_generators_card_ge hbound)
    (show 0 ≤ (2 : ℝ) ^ (σ * (J : ℝ)) by positivity) (lt_of_not_ge h).le
  have hpowlt : ((2 : ℝ) ^ (σ * (J : ℝ))) ^ (2 * K + 1) < (2 : ℝ) ^ (κ * (J : ℝ)) := by
    rw [← Real.rpow_mul_natCast (by norm_num)]
    apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num)
    have hEq : σ * (J : ℝ) * ((2 * K + 1 : ℕ) : ℝ) = κ / 2 * (J : ℝ) := by
      rw [mul_right_comm, hexp]
    rw [hEq]
    nlinarith [mul_pos hκ hJp]
  exact (not_lt_of_ge (hgrowth J hJ₀ A hA hbound hsize hmass))
    (hupper.trans_lt (mul_lt_mul_of_pos_right hpowlt hAp))

def ringQuadraticClosure {R : Type*} [Ring R] [DecidableEq R] (S : Finset R) : Finset R :=
  insert 0 (S ∪ S * S) + insert 0 (S ∪ S * S)

def ringQuadraticIterate {R : Type*} [Ring R] [DecidableEq R] (S : Finset R) : ℕ → Finset R
  | 0 => S
  | n + 1 => ringQuadraticClosure (ringQuadraticIterate S n)

def dyadicRingProjection {J : ℕ} (A : Finset (ZMod (2 ^ J))) (j : ℕ) : Finset (ZMod (2 ^ j)) :=
  A.image (fun x => (x.val : ZMod (2 ^ j)))

theorem ring_quadratic_closure_extensive {R : Type*} [Ring R] [DecidableEq R] (S : Finset R) :
    S ⊆ ringQuadraticClosure S := by
  intro x hx
  exact Finset.mem_add.mpr ⟨x, Finset.mem_insert_of_mem (Finset.mem_union_left _ hx),
    0, Finset.mem_insert_self _ _, add_zero x⟩

theorem ring_quadratic_iterate_extensive {R : Type*} [Ring R] [DecidableEq R]
    (S : Finset R) (n : ℕ) : S ⊆ ringQuadraticIterate S n := by
  induction n with
  | zero => exact Finset.Subset.refl _
  | succ n ih => exact ih.trans (ring_quadratic_closure_extensive _)

theorem ring_quadratic_iterate_stabilizer {R : Type*} [Ring R] [Fintype R] [DecidableEq R]
    {A S : Finset R} {K : ℝ} (hA : A.Nonempty) (hK : 1 ≤ K)
    (hdouble : ((A + A).card : ℝ) ≤ K * (A.card : ℝ))
    (hS : S ⊆ ringSumStabilizer A K) (n : ℕ) :
    ringQuadraticIterate S n ⊆ ringSumStabilizer A (K ^ (64 ^ n)) := by
  induction n with
  | zero => simpa only [ringQuadraticIterate, pow_zero, pow_one] using hS
  | succ n ih =>
    have hKK : K ≤ K ^ (64 ^ n) := by
      have hn : 1 ≤ (64 : ℕ) ^ n := Nat.succ_le_of_lt (pow_pos (by norm_num) n)
      simpa only [pow_one] using pow_le_pow_right₀ hK hn
    have hd : ((A + A).card : ℝ) ≤ K ^ (64 ^ n) * (A.card : ℝ) :=
      hdouble.trans (mul_le_mul_of_nonneg_right hKK (Nat.cast_nonneg _))
    have hh := ring_sum_stabilizer_quadratic_closure hA (one_le_pow₀ hK) hd ih
    have heq : (K ^ (64 ^ n)) ^ (64 : ℕ) = K ^ (64 ^ (n + 1)) := by
      rw [← pow_mul, ← pow_succ]
    rw [heq] at hh
    exact hh

theorem dyadic_ring_projection_mono {J : ℕ} {A B : Finset (ZMod (2 ^ J))}
    (hAB : A ⊆ B) (j : ℕ) : dyadicRingProjection A j ⊆ dyadicRingProjection B j :=
  Finset.image_subset_image hAB

theorem dyadic_ring_projection_card {J : ℕ} (A : Finset (ZMod (2 ^ J))) (j : ℕ) :
    (dyadicRingProjection A j).card = (dyadicProjection (A.image ZMod.val) j).card := by
  rw [← Finset.card_image_of_injective (dyadicRingProjection A j) (ZMod.val_injective _)]
  simp only [dyadicRingProjection, dyadicProjection, Finset.image_image, Function.comp_def,
    ZMod.val_natCast]

theorem zmod_cast_image_val {q : ℕ} [NeZero q] (A : Finset (ZMod q)) :
    (A.image ZMod.val).image (fun n : ℕ => (n : ZMod q)) = A := by
  simp [Finset.image_image]

/-- Sum-product growth in the native residue ring, under projection lower bounds.
These hypotheses pass to every superset, as needed for iteration. -/
theorem exists_dyadic_ring_quadratic_growth {γ δ : ℝ}
    (hγ : 0 < γ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ σ ε : ℝ, 0 < σ ∧ 0 < ε ∧ ε ≤ 1 / 4 ∧ ∃ J₀ : ℕ,
      ∀ J : ℕ, J₀ ≤ J → ∀ A : Finset (ZMod (2 ^ J)), A.Nonempty →
        (A.card : ℝ) ≤ (2 : ℝ) ^ ((1 - δ) * (J : ℝ)) →
        (∀ j : ℕ, j ≤ J → ε * (J : ℝ) < (j : ℝ) →
          (2 : ℝ) ^ (γ * (j : ℝ)) ≤ ((dyadicRingProjection A j).card : ℝ)) →
        (2 : ℝ) ^ (σ * (J : ℝ)) * (A.card : ℝ) ≤ ((ringQuadraticClosure A).card : ℝ) := by
  obtain ⟨σ, ε, hσ, hε, hε4, J₀, hg⟩ :=
    exists_dyadic_sum_product_double_growth_of_projection hγ hδ hδ1
  refine ⟨σ, ε, hσ, hε, hε4, J₀, ?_⟩
  intro J hJ A hA hsize hproj
  have hcard : (A.image ZMod.val).card = A.card :=
    Finset.card_image_of_injective _ (ZMod.val_injective _)
  have hb : ∀ x ∈ A.image ZMod.val, x < 2 ^ J := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    exact ZMod.val_lt _
  have hh := hg J hJ (A.image ZMod.val) (hA.image _) hb
    (by simpa only [hcard] using hsize)
    (fun j hj hjε => by simpa only [← dyadic_ring_projection_card] using hproj j hj hjε)
  simpa only [hcard, nat_linear_quadratic_residue_generators, zmod_cast_image_val,
    ringQuadraticClosure] using hh

theorem dyadic_ring_quadratic_iterate_card_growth {J R : ℕ}
    {S : Finset (ZMod (2 ^ J))} {g B γ ε : ℝ} (hS : S.Nonempty) (hg : 0 ≤ g)
    (hproj : ∀ j : ℕ, j ≤ J → ε * (J : ℝ) < (j : ℝ) →
      (2 : ℝ) ^ (γ * (j : ℝ)) ≤ ((dyadicRingProjection S j).card : ℝ))
    (hgrowth : ∀ U : Finset (ZMod (2 ^ J)), U.Nonempty → (U.card : ℝ) ≤ B →
      (∀ j : ℕ, j ≤ J → ε * (J : ℝ) < (j : ℝ) →
        (2 : ℝ) ^ (γ * (j : ℝ)) ≤ ((dyadicRingProjection U j).card : ℝ)) →
      g * (U.card : ℝ) ≤ ((ringQuadraticClosure U).card : ℝ))
    (hsize : ∀ i : ℕ, i < R → ((ringQuadraticIterate S i).card : ℝ) ≤ B) :
    g ^ R * (S.card : ℝ) ≤ ((ringQuadraticIterate S R).card : ℝ) := by
  have hi : ∀ i : ℕ, i ≤ R → g ^ i * (S.card : ℝ) ≤ ((ringQuadraticIterate S i).card : ℝ) := by
    intro i
    induction i with
    | zero => intro _; simp [ringQuadraticIterate]
    | succ i ih =>
      intro hi
      have hsub := ring_quadratic_iterate_extensive S i
      calc
        _ = g * (g ^ i * (S.card : ℝ)) := by rw [pow_succ]; ring
        _ ≤ g * ((ringQuadraticIterate S i).card : ℝ) :=
          mul_le_mul_of_nonneg_left (ih (by omega)) hg
        _ ≤ _ := hgrowth _ (hS.mono hsub) (hsize i (by omega)) (fun j hj hεj =>
          (hproj j hj hεj).trans (by exact_mod_cast Finset.card_le_card (dyadic_ring_projection_mono hsub j)))
  exact hi R le_rfl

/-- A nonconcentrated set of moderate size cannot have a well-projecting
family of stabilizers at a sufficiently small power of the modulus. -/
theorem exists_dyadic_no_projecting_stabilizer {α β δ : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ η ε : ℝ, 0 < η ∧ 0 < ε ∧ ε ≤ 1 / 4 ∧ ∃ J₀ : ℕ,
      ∀ J : ℕ, J₀ ≤ J → ∀ A S : Finset (ZMod (2 ^ J)), A.Nonempty → S.Nonempty →
        (A.card : ℝ) ≤ (2 : ℝ) ^ ((1 - δ) * (J : ℝ)) →
        (∀ L : ℕ, L ≤ J → ε * (J : ℝ) < (L : ℝ) → ∀ r : ZMod (2 ^ L),
          ((A.filter (fun a => (a.val : ZMod (2 ^ L)) = r)).card : ℝ) ≤
            (2 : ℝ) ^ (-α * (L : ℝ)) * (A.card : ℝ)) →
        (∀ L : ℕ, L ≤ J → ε * (J : ℝ) < (L : ℝ) →
          (2 : ℝ) ^ (β * (L : ℝ)) ≤ ((dyadicRingProjection S L).card : ℝ)) →
        ((A + A).card : ℝ) ≤ (2 : ℝ) ^ (η * (J : ℝ)) * (A.card : ℝ) →
        ¬ S ⊆ ringSumStabilizer A ((2 : ℝ) ^ (η * (J : ℝ))) := by
  obtain ⟨c₀, ε₀, hc₀, hε₀, hε₀4, J₀, hstab⟩ :=
    exists_dyadic_sum_stabilizer_density_bound hα hδ hδ1
  let c := min c₀ 1
  have hc : 0 < c := lt_min hc₀ (by norm_num)
  have hcc₀ : c ≤ c₀ := min_le_left _ _
  have hc1 : c ≤ 1 := min_le_right _ _
  obtain ⟨σ, ε₁, hσ, hε₁, hε₁4, J₁, hgrowth⟩ :=
    exists_dyadic_ring_quadratic_growth hβ (show 0 < c / 2 by positivity) (by linarith)
  obtain ⟨R, hR⟩ := exists_nat_ge (2 / σ)
  have hσR : 2 ≤ σ * (R : ℝ) := by
    have hh := (div_le_iff₀ hσ).mp hR
    nlinarith
  let η := c / (2 * ((64 ^ R : ℕ) : ℝ))
  have hden : (0 : ℝ) < (64 ^ R : ℕ) := by positivity
  have hη : 0 < η := div_pos hc (mul_pos (by norm_num) hden)
  have hηR : η * ((64 ^ R : ℕ) : ℝ) = c / 2 := by
    dsimp [η]
    field_simp
  refine ⟨η, min ε₀ ε₁, hη, lt_min hε₀ hε₁,
    (min_le_left _ _).trans hε₀4, max (max J₀ J₁) 1, ?_⟩
  intro J hJ A S hA hS hsize hmass hproj hdouble hSstab
  have hJ₀ : J₀ ≤ J := (le_max_left _ _).trans ((le_max_left _ _).trans hJ)
  have hJ₁ : J₁ ≤ J := (le_max_right _ _).trans ((le_max_left _ _).trans hJ)
  have hJp : (0 : ℝ) < J := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (1 : ℕ)) ((le_max_right _ _).trans hJ))
  have hJ0 := hJp.le
  have hm : ∀ L : ℕ, L ≤ J → ε₀ * (J : ℝ) < (L : ℝ) → ∀ r : ZMod (2 ^ L),
      ((A.filter (fun a => (a.val : ZMod (2 ^ L)) = r)).card : ℝ) ≤
        (2 : ℝ) ^ (-α * (L : ℝ)) * (A.card : ℝ) := by
    intro L hL hεL
    exact hmass L hL ((mul_le_mul_of_nonneg_right (min_le_left _ _) hJ0).trans_lt hεL)
  have hp : ∀ L : ℕ, L ≤ J → ε₁ * (J : ℝ) < (L : ℝ) →
      (2 : ℝ) ^ (β * (L : ℝ)) ≤ ((dyadicRingProjection S L).card : ℝ) := by
    intro L hL hεL
    exact hproj L hL ((mul_le_mul_of_nonneg_right (min_le_right _ _) hJ0).trans_lt hεL)
  let K := (2 : ℝ) ^ (η * (J : ℝ))
  have hK : 1 ≤ K := Real.one_le_rpow (by norm_num) (mul_nonneg hη.le hJ0)
  have hiter : ∀ i : ℕ, i ≤ R →
      ((ringQuadraticIterate S i).card : ℝ) ≤ (2 : ℝ) ^ ((1 - c / 2) * (J : ℝ)) := by
    intro i hi
    have hsub := ring_quadratic_iterate_stabilizer hA hK hdouble hSstab i
    have hexp : η * ((64 ^ i : ℕ) : ℝ) ≤ c / 2 := by
      rw [← hηR]
      apply mul_le_mul_of_nonneg_left _ hη.le
      exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0 < (64 : ℕ)) hi
    calc
      _ ≤ ((ringSumStabilizer A (K ^ (64 ^ i))).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
      _ ≤ K ^ (64 ^ i) * (2 : ℝ) ^ ((1 - c₀) * (J : ℝ)) :=
        hstab J hJ₀ A hA hsize hm _ (by positivity)
      _ = (2 : ℝ) ^ ((η * ((64 ^ i : ℕ) : ℝ) + 1 - c₀) * (J : ℝ)) := by
        dsimp only [K]
        rw [← Real.rpow_mul_natCast (by norm_num), ← Real.rpow_add (by norm_num)]
        congr 1
        ring
      _ ≤ _ := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        apply mul_le_mul_of_nonneg_right _ hJ0
        linarith
  have hlower := dyadic_ring_quadratic_iterate_card_growth hS
    (show (0 : ℝ) ≤ (2 : ℝ) ^ (σ * (J : ℝ)) by positivity) hp
    (hgrowth J hJ₁) (fun i hi => hiter i hi.le)
  have hcard : ((ringQuadraticIterate S R).card : ℝ) ≤ (2 : ℝ) ^ J := by
    have hh : (ringQuadraticIterate S R).card ≤ 2 ^ J := by
      simpa only [ZMod.card] using (Finset.card_le_univ (s := ringQuadraticIterate S R))
    exact_mod_cast hh
  have hS1 : (1 : ℝ) ≤ S.card := by exact_mod_cast hS.card_pos
  have hupper : ((2 : ℝ) ^ (σ * (J : ℝ))) ^ R ≤ (2 : ℝ) ^ J := by
    calc
      _ = ((2 : ℝ) ^ (σ * (J : ℝ))) ^ R * 1 := (mul_one _).symm
      _ ≤ ((2 : ℝ) ^ (σ * (J : ℝ))) ^ R * (S.card : ℝ) :=
        mul_le_mul_of_nonneg_left hS1 (by positivity)
      _ ≤ _ := hlower.trans hcard
  have hlt : (2 : ℝ) ^ J < ((2 : ℝ) ^ (σ * (J : ℝ))) ^ R := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul_natCast (by norm_num)]
    apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num)
    have hh := mul_le_mul_of_nonneg_right hσR hJ0
    nlinarith
  exact (not_lt_of_ge hupper) hlt

theorem dyadic_ring_projection_growth_of_fiber_bound {J L : ℕ}
    {A : Finset (ZMod (2 ^ J))} {γ : ℝ} (hA : A.Nonempty)
    (hmass : ∀ r : ZMod (2 ^ L),
      ((A.filter (fun a => (a.val : ZMod (2 ^ L)) = r)).card : ℝ) ≤
        (2 : ℝ) ^ (-γ * (L : ℝ)) * (A.card : ℝ)) :
    (2 : ℝ) ^ (γ * (L : ℝ)) ≤ ((dyadicRingProjection A L).card : ℝ) := by
  have hAp : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have hh : (A.card : ℝ) ≤ ((dyadicRingProjection A L).card : ℝ) *
      ((2 : ℝ) ^ (-γ * (L : ℝ)) * (A.card : ℝ)) := by
    conv_lhs => rw [Finset.card_eq_sum_card_image (fun a => (a.val : ZMod (2 ^ L))) A, Nat.cast_sum]
    calc
      _ ≤ ∑ _r ∈ dyadicRingProjection A L,
          (2 : ℝ) ^ (-γ * (L : ℝ)) * (A.card : ℝ) :=
        Finset.sum_le_sum (fun r _ => hmass r)
      _ = _ := by simp
  have hbound : 1 ≤ ((dyadicRingProjection A L).card : ℝ) * (2 : ℝ) ^ (-γ * (L : ℝ)) := by
    apply (mul_le_mul_iff_left₀ hAp).mp
    simpa only [one_mul, mul_assoc] using hh
  have hinv : (2 : ℝ) ^ (-γ * (L : ℝ)) * (2 : ℝ) ^ (γ * (L : ℝ)) = 1 := by
    rw [← Real.rpow_add (by norm_num), show -γ * (L : ℝ) + γ * (L : ℝ) = 0 by ring,
      Real.rpow_zero]
  calc
    _ = 1 * (2 : ℝ) ^ (γ * (L : ℝ)) := (one_mul _).symm
    _ ≤ (((dyadicRingProjection A L).card : ℝ) * (2 : ℝ) ^ (-γ * (L : ℝ))) *
        (2 : ℝ) ^ (γ * (L : ℝ)) := mul_le_mul_of_nonneg_right hbound (by positivity)
    _ = _ := by rw [mul_assoc, hinv, mul_one]

theorem finite_fiber_bound_large_subset {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    {A B : Finset X} (π : X → Y) {D M : ℝ} (hBA : B ⊆ A) (hM : 0 ≤ M)
    (hsize : (A.card : ℝ) ≤ D * (B.card : ℝ))
    (hbound : ∀ r : Y, ((A.filter (fun a => π a = r)).card : ℝ) ≤ M * (A.card : ℝ)) :
    ∀ r : Y, ((B.filter (fun a => π a = r)).card : ℝ) ≤ (D * M) * (B.card : ℝ) := by
  intro r
  calc
    _ ≤ ((A.filter (fun a => π a = r)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ hBA)
    _ ≤ M * (A.card : ℝ) := hbound r
    _ ≤ M * (D * (B.card : ℝ)) := mul_le_mul_of_nonneg_left hsize hM
    _ = _ := by ring

theorem ring_unit_dilate_fiber_card {R Q : Type*} [Ring R] [Ring Q]
    [DecidableEq R] [DecidableEq Q] (π : R →+* Q) (u : Rˣ) (A : Finset R) (r : Q) :
    ((ringDilate (u : R) A).filter (fun a => π a = r)).card =
      (A.filter (fun a => π a = π ((u⁻¹ : Rˣ) : R) * r)).card := by
  unfold ringDilate
  have hinj : Function.Injective (fun x : R => (u : R) * x) := (ringUnitMulAddEquiv u).injective
  rw [Finset.filter_image, Finset.card_image_of_injective _ hinj]
  congr 1
  apply Finset.filter_congr
  intro x hx
  rw [map_mul]
  exact (Units.eq_inv_mul_iff_mul_eq (Units.map π.toMonoidHom u)).symm

theorem dyadic_unit_dilate_fiber_bound {J L : ℕ} (hL : L ≤ J)
    (u : (ZMod (2 ^ J))ˣ) {A : Finset (ZMod (2 ^ J))} {M : ℝ}
    (hbound : ∀ r : ZMod (2 ^ L),
      ((A.filter (fun a => (a.val : ZMod (2 ^ L)) = r)).card : ℝ) ≤ M * (A.card : ℝ)) :
    ∀ r : ZMod (2 ^ L),
      (((ringDilate (u : ZMod (2 ^ J)) A).filter
        (fun a => (a.val : ZMod (2 ^ L)) = r)).card : ℝ) ≤ M * (A.card : ℝ) := by
  let π : ZMod (2 ^ J) →+* ZMod (2 ^ L) := ZMod.castHom (pow_dvd_pow 2 hL) _
  have hπ : ∀ x : ZMod (2 ^ J), π x = (x.val : ZMod (2 ^ L)) := by
    intro x
    exact ZMod.cast_eq_val _
  intro r
  have hh := ring_unit_dilate_fiber_card π u A r
  simp only [hπ] at hh
  rw [hh]
  exact hbound _

theorem unit_relative_image_eq_dilate {R : Type*} [Ring R] [DecidableEq R]
    (u : Rˣ) (T : Finset Rˣ) :
    T.image (fun v => ((u⁻¹ * v : Rˣ) : R)) =
      ringDilate ((u⁻¹ : Rˣ) : R) (T.image (fun v : Rˣ => (v : R))) := by
  simp only [ringDilate, Finset.image_image, Function.comp_def, Units.val_mul]

theorem exists_dyadic_fixed_power_absorption (a p : ℕ) {τ ξ : ℝ}
    (hgap : (p : ℝ) * τ < ξ) :
    ∃ J₀ : ℕ, ∀ J : ℕ, J₀ ≤ J →
      (2 : ℝ) ^ a * ((2 : ℝ) ^ (τ * (J : ℝ))) ^ p ≤ (2 : ℝ) ^ (ξ * (J : ℝ)) := by
  have hg : 0 < ξ - (p : ℝ) * τ := sub_pos.mpr hgap
  obtain ⟨J₀, hJ₀⟩ := exists_nat_ge ((a : ℝ) / (ξ - (p : ℝ) * τ))
  refine ⟨J₀, ?_⟩
  intro J hJ
  have hJr : (J₀ : ℝ) ≤ (J : ℝ) := by exact_mod_cast hJ
  have hh := (div_le_iff₀ hg).mp (hJ₀.trans hJr)
  calc
    _ = (2 : ℝ) ^ ((a : ℝ) + τ * (J : ℝ) * (p : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul_natCast (by norm_num),
        ← Real.rpow_add (by norm_num)]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)


theorem dyadic_unit_extraction_fiber_bounds {J : ℕ} {γ ε H : ℝ}
    (hγ : 0 < γ) {A B S : Finset (ZMod (2 ^ J))} {T : Finset (ZMod (2 ^ J))ˣ}
    (u₀ : (ZMod (2 ^ J))ˣ) (hBA : B ⊆ A)
    (hST : S ⊆ T.image (fun u : (ZMod (2 ^ J))ˣ => ((u₀⁻¹ * u : (ZMod (2 ^ J))ˣ) : ZMod (2 ^ J))))
    (hBlarge : (A.card : ℝ) ≤ H * (B.card : ℝ))
    (hSlarge : (T.card : ℝ) ≤ H * (S.card : ℝ))
    (hHcap : H ≤ (2 : ℝ) ^ ((γ * ε / 2) * (J : ℝ)))
    (hAmass : ∀ L : ℕ, L ≤ J → ε * (J : ℝ) < (L : ℝ) → ∀ r : ZMod (2 ^ L),
      ((A.filter (fun a => (a.val : ZMod (2 ^ L)) = r)).card : ℝ) ≤
        (2 : ℝ) ^ (-γ * (L : ℝ)) * (A.card : ℝ))
    (hTmass : ∀ L : ℕ, L ≤ J → ε * (J : ℝ) < (L : ℝ) → ∀ r : ZMod (2 ^ L),
      (((T.image (fun u : (ZMod (2 ^ J))ˣ => (u : ZMod (2 ^ J)))).filter
        (fun a => (a.val : ZMod (2 ^ L)) = r)).card : ℝ) ≤
          (2 : ℝ) ^ (-γ * (L : ℝ)) * (T.card : ℝ)) :
    (∀ L : ℕ, L ≤ J → ε * (J : ℝ) < (L : ℝ) → ∀ r : ZMod (2 ^ L),
      ((B.filter (fun a => (a.val : ZMod (2 ^ L)) = r)).card : ℝ) ≤
        (2 : ℝ) ^ (-(γ / 2) * (L : ℝ)) * (B.card : ℝ)) ∧
    (∀ L : ℕ, L ≤ J → ε * (J : ℝ) < (L : ℝ) → ∀ r : ZMod (2 ^ L),
      ((S.filter (fun a => (a.val : ZMod (2 ^ L)) = r)).card : ℝ) ≤
        (2 : ℝ) ^ (-(γ / 2) * (L : ℝ)) * (S.card : ℝ)) := by
  classical
  have hloss : ∀ L : ℕ, ε * (J : ℝ) < (L : ℝ) →
      H * (2 : ℝ) ^ (-γ * (L : ℝ)) ≤ (2 : ℝ) ^ (-(γ / 2) * (L : ℝ)) := by
    intro L hL
    calc
      _ ≤ (2 : ℝ) ^ ((γ * ε / 2) * (J : ℝ)) * (2 : ℝ) ^ (-γ * (L : ℝ)) :=
        mul_le_mul_of_nonneg_right hHcap (by positivity)
      _ = (2 : ℝ) ^ ((γ * ε / 2) * (J : ℝ) - γ * (L : ℝ)) := by
        rw [← Real.rpow_add (by norm_num)]; congr 1; ring
      _ ≤ _ := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        nlinarith only [mul_lt_mul_of_pos_left hL hγ]
  have hBmass : ∀ L : ℕ, L ≤ J → ε * (J : ℝ) < (L : ℝ) → ∀ r : ZMod (2 ^ L),
      ((B.filter (fun a => (a.val : ZMod (2 ^ L)) = r)).card : ℝ) ≤
        (2 : ℝ) ^ (-(γ / 2) * (L : ℝ)) * (B.card : ℝ) := by
    intro L hL hεL r
    exact (finite_fiber_bound_large_subset (fun a : ZMod (2 ^ J) => (a.val : ZMod (2 ^ L))) hBA
      (show 0 ≤ (2 : ℝ) ^ (-γ * (L : ℝ)) by positivity) hBlarge (hAmass L hL hεL) r).trans
        (mul_le_mul_of_nonneg_right (hloss L hεL) (Nat.cast_nonneg _))
  let U := ringDilate ((u₀⁻¹ : (ZMod (2 ^ J))ˣ) : ZMod (2 ^ J))
    (T.image (fun u : (ZMod (2 ^ J))ˣ => (u : ZMod (2 ^ J))))
  have hTcard : (T.image (fun u : (ZMod (2 ^ J))ˣ => (u : ZMod (2 ^ J)))).card = T.card :=
    Finset.card_image_of_injective _ Units.val_injective
  have hUcard : U.card = T.card := by rw [ring_dilate_unit_card, hTcard]
  have hSU : S ⊆ U := by simpa only [unit_relative_image_eq_dilate] using hST
  have hSmass : ∀ L : ℕ, L ≤ J → ε * (J : ℝ) < (L : ℝ) → ∀ r : ZMod (2 ^ L),
      ((S.filter (fun a => (a.val : ZMod (2 ^ L)) = r)).card : ℝ) ≤
        (2 : ℝ) ^ (-(γ / 2) * (L : ℝ)) * (S.card : ℝ) := by
    intro L hL hεL r
    have huMass : ∀ r : ZMod (2 ^ L),
        ((U.filter (fun a => (a.val : ZMod (2 ^ L)) = r)).card : ℝ) ≤
          (2 : ℝ) ^ (-γ * (L : ℝ)) * (U.card : ℝ) := by
      intro r
      have hh := dyadic_unit_dilate_fiber_bound hL u₀⁻¹
        (A := T.image (fun u : (ZMod (2 ^ J))ˣ => (u : ZMod (2 ^ J))))
        (M := (2 : ℝ) ^ (-γ * (L : ℝ)))
        (fun r => by simpa only [hTcard] using hTmass L hL hεL r) r
      simpa only [hTcard, hUcard] using hh
    exact (finite_fiber_bound_large_subset (fun a : ZMod (2 ^ J) => (a.val : ZMod (2 ^ L))) hSU
      (show 0 ≤ (2 : ℝ) ^ (-γ * (L : ℝ)) by positivity)
      (by simpa only [hUcard] using hSlarge) huMass r).trans
        (mul_le_mul_of_nonneg_right (hloss L hεL) (Nat.cast_nonneg _))
  exact ⟨hBmass, hSmass⟩

theorem dyadic_energy_parameter_square (K : ℝ) :
    ((2 : ℝ) ^ (82 : ℕ) * K ^ 30) ^ 2 = (2 : ℝ) ^ (164 : ℕ) * K ^ 60 := by
  ring

theorem dyadic_energy_parameter_lower (K : ℝ) (hK : 1 ≤ K) :
    16 * K ≤ (2 : ℝ) ^ (17 : ℕ) * K ^ 4 := by
  have hh : K ≤ K ^ (4 : ℕ) := by
    simpa only [pow_one] using pow_le_pow_right₀ hK (show 1 ≤ (4 : ℕ) by norm_num)
  norm_num only [Nat.reducePow]
  nlinarith only [hh, hK]

theorem exists_dyadic_unit_dilate_energy_saving {γ δ : ℝ}
    (hγ : 0 < γ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ τ ε : ℝ, 0 < τ ∧ 0 < ε ∧ ε ≤ 1 / 4 ∧ ∃ J₀ : ℕ,
      ∀ J : ℕ, J₀ ≤ J → ∀ A : Finset (ZMod (2 ^ J)), ∀ T : Finset (ZMod (2 ^ J))ˣ,
        A.Nonempty → T.Nonempty → (A.card : ℝ) ≤ (2 : ℝ) ^ ((1 - δ) * (J : ℝ)) →
        (∀ L : ℕ, L ≤ J → ε * (J : ℝ) < (L : ℝ) → ∀ r : ZMod (2 ^ L),
          ((A.filter (fun a => (a.val : ZMod (2 ^ L)) = r)).card : ℝ) ≤
            (2 : ℝ) ^ (-γ * (L : ℝ)) * (A.card : ℝ)) →
        (∀ L : ℕ, L ≤ J → ε * (J : ℝ) < (L : ℝ) → ∀ r : ZMod (2 ^ L),
          (((T.image (fun u : (ZMod (2 ^ J))ˣ => (u : ZMod (2 ^ J)))).filter
            (fun a => (a.val : ZMod (2 ^ L)) = r)).card : ℝ) ≤
              (2 : ℝ) ^ (-γ * (L : ℝ)) * (T.card : ℝ)) →
        ∃ u ∈ T, (2 : ℝ) ^ (τ * (J : ℝ)) *
          (Finset.addEnergy A (ringDilate (u : ZMod (2 ^ J)) A) : ℝ) < (A.card : ℝ) ^ 3 := by
  classical
  obtain ⟨η, ε, hη, hε, hε4, J₀, hobstruct⟩ :=
    exists_dyadic_no_projecting_stabilizer (show 0 < γ / 2 by positivity)
      (show 0 < γ / 2 by positivity) hδ hδ1
  let τ := min (η / 120) (γ * ε / 16)
  have hτ : 0 < τ := lt_min (by positivity) (by positivity)
  have hτη : τ ≤ η / 120 := min_le_left _ _
  have hτγε : τ ≤ γ * ε / 16 := min_le_right _ _
  obtain ⟨J₁, hJ₁⟩ := exists_dyadic_fixed_power_absorption 164 60
    (show (60 : ℝ) * τ < η by nlinarith only [hη, hτη])
  obtain ⟨J₂, hJ₂⟩ := exists_dyadic_fixed_power_absorption 17 4
    (show (4 : ℝ) * τ < γ * ε / 2 by nlinarith only [hτγε, mul_pos hγ hε])
  refine ⟨τ, ε, hτ, hε, hε4, max J₀ (max J₁ J₂), ?_⟩
  intro J hJ A T hA hT hsize hAmass hTmass
  have hj₀ : J₀ ≤ J := (le_max_left _ _).trans hJ
  have hj₁ : J₁ ≤ J := (le_max_left _ _).trans ((le_max_right _ _).trans hJ)
  have hj₂ : J₂ ≤ J := (le_max_right _ _).trans ((le_max_right _ _).trans hJ)
  let K := (2 : ℝ) ^ (τ * (J : ℝ))
  have hKp : 0 < K := by positivity
  have hK : 1 ≤ K := Real.one_le_rpow (by norm_num) (mul_nonneg hτ.le (Nat.cast_nonneg J))
  by_contra h
  push Not at h
  obtain ⟨B, hBA, hB, hBsize, u₀, hu₀, S, hST, hS, hSsize, hunit, hstab⟩ :=
    finite_many_unit_dilates_stabilizer hA hT hKp h
  let H := (2 : ℝ) ^ (17 : ℕ) * K ^ 4
  let D := (2 : ℝ) ^ (82 : ℕ) * K ^ 30
  have hD : 1 ≤ D := by
    exact one_le_mul_of_one_le_of_one_le (by norm_num) (one_le_pow₀ hK)
  have hDcap : D ^ 2 ≤ (2 : ℝ) ^ (η * (J : ℝ)) := by
    have heq : D ^ 2 = (2 : ℝ) ^ (164 : ℕ) * K ^ 60 := dyadic_energy_parameter_square K
    rw [heq]
    exact hJ₁ J hj₁
  have hHcap : H ≤ (2 : ℝ) ^ ((γ * ε / 2) * (J : ℝ)) := hJ₂ J hj₂
  have h16 : 16 * K ≤ H := dyadic_energy_parameter_lower K hK
  have hBlarge : (A.card : ℝ) ≤ H * (B.card : ℝ) := by
    have hh := (div_le_iff₀ (show 0 < 16 * K by positivity)).mp hBsize
    calc
      _ ≤ (16 * K) * (B.card : ℝ) := by simpa only [mul_comm] using hh
      _ ≤ _ := mul_le_mul_of_nonneg_right h16 (Nat.cast_nonneg _)
  have hSlarge : (T.card : ℝ) ≤ H * (S.card : ℝ) := by
    have hh := (div_le_iff₀ (show 0 < 131072 * K ^ 4 by positivity)).mp hSsize
    simpa only [H, show (2 : ℝ) ^ (17 : ℕ) = 131072 by norm_num, mul_comm] using hh
  obtain ⟨hBmass, hSmass⟩ := dyadic_unit_extraction_fiber_bounds hγ u₀ hBA hST
    hBlarge hSlarge hHcap hAmass hTmass
  have hBbound : (B.card : ℝ) ≤ (2 : ℝ) ^ ((1 - δ) * (J : ℝ)) :=
    (show (B.card : ℝ) ≤ A.card by exact_mod_cast Finset.card_le_card hBA).trans hsize
  have hSproj : ∀ L : ℕ, L ≤ J → ε * (J : ℝ) < (L : ℝ) →
      (2 : ℝ) ^ ((γ / 2) * (L : ℝ)) ≤ ((dyadicRingProjection S L).card : ℝ) :=
    fun L hL hεL => dyadic_ring_projection_growth_of_fiber_bound hS (hSmass L hL hεL)
  obtain ⟨x, hx⟩ := hS
  obtain ⟨u, hu⟩ := hunit x hx
  have hdouble : ((B + B).card : ℝ) ≤ (2 : ℝ) ^ (η * (J : ℝ)) * (B.card : ℝ) := by
    have hh := ring_sum_stabilizer_unit_doubling hB (show 0 ≤ D by positivity) u
      (by simpa only [hu] using hstab hx)
    exact hh.trans (mul_le_mul_of_nonneg_right hDcap (Nat.cast_nonneg _))
  have hSstab : S ⊆ ringSumStabilizer B ((2 : ℝ) ^ (η * (J : ℝ))) := by
    have hDD : D ≤ D ^ (2 : ℕ) := by
      simpa only [pow_one] using pow_le_pow_right₀ hD (show 1 ≤ (2 : ℕ) by norm_num)
    exact hstab.trans (ring_sum_stabilizer_mono B (hDD.trans hDcap))
  exact hobstruct J hj₀ B S hB ⟨x, hx⟩ hBbound hBmass hSproj hdouble hSstab


theorem finite_add_energy_upper {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (A B : Finset G) : (Finset.addEnergy A B : ℝ) ≤ (A.card : ℝ) * (B.card : ℝ) ^ 2 := by
  rw [← finite_difference_energy_eq_addEnergy, ← finite_difference_energy_sum_real]
  calc
    _ ≤ ∑ x : G, (B.card : ℝ) * (finiteDifferenceCount A B x : ℝ) := by
      apply Finset.sum_le_sum
      intro x hx
      have hh : (finiteDifferenceCount A B x : ℝ) ≤ B.card := by
        exact_mod_cast finite_difference_count_le_right A B x
      simpa only [pow_two] using mul_le_mul_of_nonneg_right hh
        (Nat.cast_nonneg (finiteDifferenceCount A B x) : (0 : ℝ) ≤ finiteDifferenceCount A B x)
    _ = _ := by rw [← Finset.mul_sum, finite_difference_count_sum_real]; ring

theorem ring_unit_dilate_energy_upper {R : Type*} [Ring R] [Fintype R] [DecidableEq R]
    (A : Finset R) (u : Rˣ) :
    (Finset.addEnergy A (ringDilate (u : R) A) : ℝ) ≤ (A.card : ℝ) ^ 3 := by
  have hh := finite_add_energy_upper A (ringDilate (u : R) A)
  rw [ring_dilate_unit_card] at hh
  calc _ ≤ (A.card : ℝ) * (A.card : ℝ) ^ 2 := hh
       _ = _ := by ring

/-- A small value in every sufficiently large subset bounds the full average. -/
theorem finite_sum_bound_of_hereditary_small_value {X : Type*} [DecidableEq X]
    {T : Finset X} {f : X → ℝ} {ρ a M : ℝ}
    (hT : T.Nonempty) (hρ : 0 < ρ) (ha : 0 ≤ a) (hM : 0 ≤ M)
    (hupper : ∀ x ∈ T, f x ≤ M)
    (hsmall : ∀ U : Finset X, U ⊆ T → U.Nonempty →
      ρ * (T.card : ℝ) ≤ (U.card : ℝ) → ∃ x ∈ U, f x < a * M) :
    ∑ x ∈ T, f x ≤ (ρ + a) * (T.card : ℝ) * M := by
  classical
  let U := T.filter (fun x => a * M ≤ f x)
  have hU : (U.card : ℝ) < ρ * (T.card : ℝ) := by
    by_contra h
    have hh := le_of_not_gt h
    have hTp : (0 : ℝ) < T.card := by exact_mod_cast hT.card_pos
    have hUp : (0 : ℝ) < U.card := (mul_pos hρ hTp).trans_le hh
    obtain ⟨x, hx, hfx⟩ := hsmall U (Finset.filter_subset _ _)
      (Finset.card_pos.mp (by exact_mod_cast hUp)) hh
    exact (not_lt_of_ge (Finset.mem_filter.mp hx).2) hfx
  have hsplit : ∑ x ∈ T, f x =
      (∑ x ∈ T.filter (fun x => a * M ≤ f x), f x) +
      ∑ x ∈ T.filter (fun x => ¬ a * M ≤ f x), f x := by
    rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    split_ifs <;> simp_all
  rw [hsplit]
  calc
    _ ≤ (∑ _x ∈ U, M) + ∑ _x ∈ T.filter (fun x => ¬ a * M ≤ f x), a * M := by
      apply add_le_add
      · exact Finset.sum_le_sum (fun x hx => hupper x (Finset.mem_filter.mp hx).1)
      · exact Finset.sum_le_sum (fun x hx => (lt_of_not_ge (Finset.mem_filter.mp hx).2).le)
    _ = (U.card : ℝ) * M + ((T.filter (fun x => ¬ a * M ≤ f x)).card : ℝ) * (a * M) := by simp
    _ ≤ (ρ * (T.card : ℝ)) * M + (T.card : ℝ) * (a * M) := by
      apply add_le_add (mul_le_mul_of_nonneg_right hU.le hM)
      apply mul_le_mul_of_nonneg_right _ (mul_nonneg ha hM)
      exact_mod_cast Finset.card_filter_le T (fun x => ¬ a * M ≤ f x)
    _ = _ := by ring


/-- Uniform power-saving decay for the average mixed additive energy over a
nonconcentrated family of unit dilates. -/
theorem exists_dyadic_average_unit_energy_decay {γ δ : ℝ}
    (hγ : 0 < γ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ τ ε : ℝ, 0 < τ ∧ 0 < ε ∧ ε ≤ 1 / 4 ∧ ∃ J₀ : ℕ,
      ∀ J : ℕ, J₀ ≤ J → ∀ A : Finset (ZMod (2 ^ J)), ∀ T : Finset (ZMod (2 ^ J))ˣ,
        A.Nonempty → T.Nonempty → (A.card : ℝ) ≤ (2 : ℝ) ^ ((1 - δ) * (J : ℝ)) →
        (∀ L : ℕ, L ≤ J → ε * (J : ℝ) < (L : ℝ) → ∀ r : ZMod (2 ^ L),
          ((A.filter (fun a => (a.val : ZMod (2 ^ L)) = r)).card : ℝ) ≤
            (2 : ℝ) ^ (-γ * (L : ℝ)) * (A.card : ℝ)) →
        (∀ L : ℕ, L ≤ J → ε * (J : ℝ) < (L : ℝ) → ∀ r : ZMod (2 ^ L),
          (((T.image (fun u : (ZMod (2 ^ J))ˣ => (u : ZMod (2 ^ J)))).filter
            (fun a => (a.val : ZMod (2 ^ L)) = r)).card : ℝ) ≤
              (2 : ℝ) ^ (-γ * (L : ℝ)) * (T.card : ℝ)) →
        (∑ u ∈ T, (Finset.addEnergy A (ringDilate (u : ZMod (2 ^ J)) A) : ℝ)) ≤
          (2 : ℝ) ^ (-τ * (J : ℝ)) * (T.card : ℝ) * (A.card : ℝ) ^ 3 := by
  classical
  obtain ⟨κ, ε, hκ, hε, hε4, J₀, hpoint⟩ :=
    exists_dyadic_unit_dilate_energy_saving (show 0 < γ / 2 by positivity) hδ hδ1
  let ρ := min κ (γ * ε / 4)
  have hρ : 0 < ρ := lt_min hκ (by positivity)
  have hρκ : ρ ≤ κ := min_le_left _ _
  have hργε : ρ ≤ γ * ε / 4 := min_le_right _ _
  obtain ⟨J₁, hJ₁⟩ := exists_dyadic_fixed_power_absorption 1 0 (τ := 0)
    (ξ := ρ / 2) (by simpa using (show 0 < ρ / 2 by positivity))
  refine ⟨ρ / 2, ε, by positivity, hε, hε4, max J₀ J₁, ?_⟩
  intro J hJ A T hA hT hsize hAmass hTmass
  have hj₀ : J₀ ≤ J := (le_max_left _ _).trans hJ
  have hj₁ : J₁ ≤ J := (le_max_right _ _).trans hJ
  have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg _
  have hTcard : (T.image (fun u : (ZMod (2 ^ J))ˣ => (u : ZMod (2 ^ J)))).card = T.card :=
    Finset.card_image_of_injective _ Units.val_injective
  have hAmass' : ∀ L : ℕ, L ≤ J → ε * (J : ℝ) < (L : ℝ) → ∀ r : ZMod (2 ^ L),
      ((A.filter (fun a => (a.val : ZMod (2 ^ L)) = r)).card : ℝ) ≤
        (2 : ℝ) ^ (-(γ / 2) * (L : ℝ)) * (A.card : ℝ) := by
    intro L hL hεL r
    apply (hAmass L hL hεL r).trans
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    nlinarith only [mul_nonneg hγ.le (Nat.cast_nonneg L : (0 : ℝ) ≤ L)]
  have hhereditary : ∀ U : Finset (ZMod (2 ^ J))ˣ, U ⊆ T → U.Nonempty →
      (2 : ℝ) ^ (-ρ * (J : ℝ)) * (T.card : ℝ) ≤ (U.card : ℝ) →
      ∃ u ∈ U, (Finset.addEnergy A (ringDilate (u : ZMod (2 ^ J)) A) : ℝ) <
        (2 : ℝ) ^ (-κ * (J : ℝ)) * (A.card : ℝ) ^ 3 := by
    intro U hUT hU hlarge
    have hUcard : (U.image (fun u : (ZMod (2 ^ J))ˣ => (u : ZMod (2 ^ J)))).card = U.card :=
      Finset.card_image_of_injective _ Units.val_injective
    have hinv : (2 : ℝ) ^ (ρ * (J : ℝ)) * (2 : ℝ) ^ (-ρ * (J : ℝ)) = 1 := by
      rw [← Real.rpow_add (by norm_num), show ρ * (J : ℝ) + -ρ * (J : ℝ) = 0 by ring,
        Real.rpow_zero]
    have hratio : (T.card : ℝ) ≤ (2 : ℝ) ^ (ρ * (J : ℝ)) * (U.card : ℝ) := by
      calc
        _ = (2 : ℝ) ^ (ρ * (J : ℝ)) * ((2 : ℝ) ^ (-ρ * (J : ℝ)) * (T.card : ℝ)) := by
          rw [← mul_assoc, hinv, one_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_left hlarge (by positivity)
    have hUmass : ∀ L : ℕ, L ≤ J → ε * (J : ℝ) < (L : ℝ) → ∀ r : ZMod (2 ^ L),
        (((U.image (fun u : (ZMod (2 ^ J))ˣ => (u : ZMod (2 ^ J)))).filter
          (fun a => (a.val : ZMod (2 ^ L)) = r)).card : ℝ) ≤
            (2 : ℝ) ^ (-(γ / 2) * (L : ℝ)) * (U.card : ℝ) := by
      intro L hL hεL r
      have hh := finite_fiber_bound_large_subset (fun a : ZMod (2 ^ J) => (a.val : ZMod (2 ^ L)))
        (Finset.image_subset_image (f := fun u : (ZMod (2 ^ J))ˣ => (u : ZMod (2 ^ J))) hUT)
        (show 0 ≤ (2 : ℝ) ^ (-γ * (L : ℝ)) by positivity)
        (D := (2 : ℝ) ^ (ρ * (J : ℝ)))
        (by simpa only [hTcard, hUcard] using hratio)
        (fun r => by simpa only [hTcard] using hTmass L hL hεL r) r
      simp only [hUcard] at hh
      apply hh.trans
      apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
      rw [← Real.rpow_add (by norm_num)]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have hρJ := mul_le_mul_of_nonneg_right hργε hJ0
      have hγL := mul_lt_mul_of_pos_left hεL hγ
      nlinarith only [hρJ, hγL, mul_nonneg hγ.le (Nat.cast_nonneg L : (0 : ℝ) ≤ L)]
    obtain ⟨u, hu, hE⟩ := hpoint J hj₀ A U hA hU hsize hAmass' hUmass
    refine ⟨u, hu, ?_⟩
    apply (mul_lt_mul_iff_of_pos_left
      (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (κ * (J : ℝ)))).mp
    calc
      _ < (A.card : ℝ) ^ 3 := hE
      _ = _ := by
        rw [← mul_assoc, ← Real.rpow_add (by norm_num),
          show κ * (J : ℝ) + -κ * (J : ℝ) = 0 by ring, Real.rpow_zero, one_mul]
  have havg := finite_sum_bound_of_hereditary_small_value hT
    (show 0 < (2 : ℝ) ^ (-ρ * (J : ℝ)) by positivity)
    (show 0 ≤ (2 : ℝ) ^ (-κ * (J : ℝ)) by positivity)
    (show 0 ≤ (A.card : ℝ) ^ 3 by positivity)
    (fun u _ => ring_unit_dilate_energy_upper A u) hhereditary
  have htwo : (2 : ℝ) ≤ (2 : ℝ) ^ ((ρ / 2) * (J : ℝ)) := by
    simpa using hJ₁ J hj₁
  have hcoef : (2 : ℝ) ^ (-ρ * (J : ℝ)) + (2 : ℝ) ^ (-κ * (J : ℝ)) ≤
      (2 : ℝ) ^ (-(ρ / 2) * (J : ℝ)) := by
    have hpow : (2 : ℝ) ^ (-κ * (J : ℝ)) ≤ (2 : ℝ) ^ (-ρ * (J : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have hh := mul_le_mul_of_nonneg_right hρκ hJ0
      linarith only [hh]
    calc
      _ ≤ 2 * (2 : ℝ) ^ (-ρ * (J : ℝ)) := by linarith only [hpow]
      _ ≤ (2 : ℝ) ^ ((ρ / 2) * (J : ℝ)) * (2 : ℝ) ^ (-ρ * (J : ℝ)) :=
        mul_le_mul_of_nonneg_right htwo (by positivity)
      _ = _ := by rw [← Real.rpow_add (by norm_num)]; congr 1; ring
  exact havg.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg _)) (by positivity))


theorem finite_fiber_bound_union {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    (π : X → Y) {A B : Finset X} {M : ℝ} (hM : 0 ≤ M)
    (hA : ∀ r : Y, ((A.filter (fun x => π x = r)).card : ℝ) ≤ M * (A.card : ℝ))
    (hB : ∀ r : Y, ((B.filter (fun x => π x = r)).card : ℝ) ≤ M * (B.card : ℝ)) :
    ∀ r : Y, (((A ∪ B).filter (fun x => π x = r)).card : ℝ) ≤
      (2 * M) * ((A ∪ B).card : ℝ) := by
  intro r
  have hAU : (A.card : ℝ) ≤ (A ∪ B).card := by
    exact_mod_cast Finset.card_le_card (Finset.subset_union_left : A ⊆ A ∪ B)
  have hBU : (B.card : ℝ) ≤ (A ∪ B).card := by
    exact_mod_cast Finset.card_le_card (Finset.subset_union_right : B ⊆ A ∪ B)
  calc
    _ ≤ ((A.filter (fun x => π x = r)).card : ℝ) + ((B.filter (fun x => π x = r)).card : ℝ) := by
      rw [Finset.filter_union]
      exact_mod_cast Finset.card_union_le _ _
    _ ≤ M * (A.card : ℝ) + M * (B.card : ℝ) := add_le_add (hA r) (hB r)
    _ ≤ M * ((A ∪ B).card : ℝ) + M * ((A ∪ B).card : ℝ) := by gcongr
    _ = _ := by ring

/-- Interpolate the union bound and the elementary mixed-energy bound. -/
theorem ordered_mixed_energy_square_bound {e a b t v r w : ℝ}
    (he : 0 ≤ e) (ha : 0 ≤ a) (hb : 0 ≤ b) (ht : 0 ≤ t) (hv : 0 ≤ v)
    (hr : 0 ≤ r) (hw : 0 ≤ w) (hab : a ≤ b)
    (hbalance : 64 * v ^ 2 * r ^ 3 ≤ w) (hinverse : 1 ≤ w * r)
    (hunion : e ≤ v * t * (a + b) ^ 3) (htrivial : e ≤ t * a ^ 2 * b) :
    e ^ 2 ≤ w * t ^ 2 * a ^ 3 * b ^ 3 := by
  by_cases hratio : b ≤ r * a
  · have he' : e ≤ v * t * (2 * b) ^ 3 := by
      apply hunion.trans
      gcongr
      linarith only [hab]
    have hb' : b ^ 3 ≤ r ^ 3 * a ^ 3 := by
      simpa only [mul_pow] using pow_le_pow_left₀ hb hratio 3
    calc
      _ ≤ (v * t * (2 * b) ^ 3) ^ 2 := pow_le_pow_left₀ he he' 2
      _ = (64 * v ^ 2 * t ^ 2 * b ^ 3) * b ^ 3 := by ring
      _ ≤ (64 * v ^ 2 * t ^ 2 * b ^ 3) * (r ^ 3 * a ^ 3) :=
        mul_le_mul_of_nonneg_left hb' (by positivity)
      _ = (64 * v ^ 2 * r ^ 3) * (t ^ 2 * a ^ 3 * b ^ 3) := by ring
      _ ≤ w * (t ^ 2 * a ^ 3 * b ^ 3) := mul_le_mul_of_nonneg_right hbalance (by positivity)
      _ = _ := by ring
  · have hratio' : r * a ≤ b := (lt_of_not_ge hratio).le
    have haw : a ≤ w * b := by
      calc
        _ = 1 * a := (one_mul _).symm
        _ ≤ (w * r) * a := mul_le_mul_of_nonneg_right hinverse ha
        _ = w * (r * a) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hratio' hw
    calc
      _ ≤ (t * a ^ 2 * b) ^ 2 := pow_le_pow_left₀ he htrivial 2
      _ = (t ^ 2 * a ^ 3 * b ^ 2) * a := by ring
      _ ≤ (t ^ 2 * a ^ 3 * b ^ 2) * (w * b) := mul_le_mul_of_nonneg_left haw (by positivity)
      _ = _ := by ring

theorem mixed_energy_square_bound {e a b t v r w : ℝ}
    (he : 0 ≤ e) (ha : 0 ≤ a) (hb : 0 ≤ b) (ht : 0 ≤ t) (hv : 0 ≤ v)
    (hr : 0 ≤ r) (hw : 0 ≤ w)
    (hbalance : 64 * v ^ 2 * r ^ 3 ≤ w) (hinverse : 1 ≤ w * r)
    (hunion : e ≤ v * t * (a + b) ^ 3)
    (hleft : e ≤ t * a ^ 2 * b) (hright : e ≤ t * a * b ^ 2) :
    e ^ 2 ≤ w * t ^ 2 * a ^ 3 * b ^ 3 := by
  rcases le_total a b with hab | hba
  · exact ordered_mixed_energy_square_bound he ha hb ht hv hr hw hab hbalance hinverse hunion hleft
  · have hh := ordered_mixed_energy_square_bound he hb ha ht hv hr hw hba hbalance hinverse
      (by simpa only [add_comm] using hunion)
      (by simpa only [mul_assoc, mul_comm, mul_left_comm] using hright)
    calc _ ≤ w * t ^ 2 * b ^ 3 * a ^ 3 := hh
         _ = _ := by ring

theorem ring_unit_mixed_energy_upper_left {R : Type*} [Ring R] [Fintype R] [DecidableEq R]
    (A B : Finset R) (u : Rˣ) :
    (Finset.addEnergy A (ringDilate (u : R) B) : ℝ) ≤ (A.card : ℝ) ^ 2 * (B.card : ℝ) := by
  rw [Finset.addEnergy_comm]
  have hh := finite_add_energy_upper (ringDilate (u : R) B) A
  rw [ring_dilate_unit_card] at hh
  simpa only [mul_comm] using hh

theorem ring_unit_mixed_energy_upper_right {R : Type*} [Ring R] [Fintype R] [DecidableEq R]
    (A B : Finset R) (u : Rˣ) :
    (Finset.addEnergy A (ringDilate (u : R) B) : ℝ) ≤ (A.card : ℝ) * (B.card : ℝ) ^ 2 := by
  have hh := finite_add_energy_upper A (ringDilate (u : R) B)
  simpa only [ring_dilate_unit_card] using hh

def DyadicRingSetNonconcentration {J : ℕ} (γ ε : ℝ) (A : Finset (ZMod (2 ^ J))) : Prop :=
  ∀ L : ℕ, L ≤ J → ε * (J : ℝ) < (L : ℝ) → ∀ r : ZMod (2 ^ L),
    ((A.filter (fun a => (a.val : ZMod (2 ^ L)) = r)).card : ℝ) ≤
      (2 : ℝ) ^ (-γ * (L : ℝ)) * (A.card : ℝ)

def DyadicUnitSetNonconcentration {J : ℕ} (γ ε : ℝ) (T : Finset (ZMod (2 ^ J))ˣ) : Prop :=
  ∀ L : ℕ, L ≤ J → ε * (J : ℝ) < (L : ℝ) → ∀ r : ZMod (2 ^ L),
    (((T.image (fun u : (ZMod (2 ^ J))ˣ => (u : ZMod (2 ^ J)))).filter
      (fun a => (a.val : ZMod (2 ^ L)) = r)).card : ℝ) ≤
        (2 : ℝ) ^ (-γ * (L : ℝ)) * (T.card : ℝ)

/-- Average mixed energy of two distinct nonconcentrated sets, with a
cardinality-symmetric normalization suitable for weighted level sets. -/
theorem exists_dyadic_average_mixed_energy_decay {γ δ : ℝ}
    (hγ : 0 < γ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ τ ε : ℝ, 0 < τ ∧ 0 < ε ∧ ε ≤ 1 / 4 ∧ ∃ J₀ : ℕ,
      ∀ J : ℕ, J₀ ≤ J → ∀ A B : Finset (ZMod (2 ^ J)), ∀ T : Finset (ZMod (2 ^ J))ˣ,
        A.Nonempty → B.Nonempty → T.Nonempty →
        (A.card : ℝ) ≤ (2 : ℝ) ^ ((1 - δ) * (J : ℝ)) →
        (B.card : ℝ) ≤ (2 : ℝ) ^ ((1 - δ) * (J : ℝ)) →
        DyadicRingSetNonconcentration γ ε A → DyadicRingSetNonconcentration γ ε B →
        DyadicUnitSetNonconcentration γ ε T →
        (∑ u ∈ T, (Finset.addEnergy A (ringDilate (u : ZMod (2 ^ J)) B) : ℝ)) ^ 2 ≤
          (2 : ℝ) ^ (-τ * (J : ℝ)) * (T.card : ℝ) ^ 2 * (A.card : ℝ) ^ 3 * (B.card : ℝ) ^ 3 := by
  classical
  obtain ⟨κ, ε, hκ, hε, hε4, J₀, havg⟩ := exists_dyadic_average_unit_energy_decay
    (show 0 < γ / 2 by positivity) (show 0 < δ / 2 by positivity) (by linarith only [hδ1])
  obtain ⟨J₁, hJ₁⟩ := exists_dyadic_fixed_power_absorption 1 0 (τ := 0) (ξ := δ / 2)
    (by simpa using (show 0 < δ / 2 by positivity))
  obtain ⟨J₂, hJ₂⟩ := exists_dyadic_fixed_power_absorption 1 0 (τ := 0) (ξ := γ * ε / 2)
    (by simpa using (show 0 < γ * ε / 2 by positivity))
  obtain ⟨J₃, hJ₃⟩ := exists_dyadic_fixed_power_absorption 6 0 (τ := 0) (ξ := κ)
    (by simpa using hκ)
  refine ⟨κ / 4, ε, by positivity, hε, hε4, max J₀ (max J₁ (max J₂ J₃)), ?_⟩
  intro J hJ A B T hA hB hT hAsize hBsize hAmass hBmass hTmass
  have hj₀ : J₀ ≤ J := (le_max_left _ _).trans hJ
  have hj₁ : J₁ ≤ J := (le_max_left _ _).trans ((le_max_right _ _).trans hJ)
  have hj₂ : J₂ ≤ J := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hJ))
  have hj₃ : J₃ ≤ J := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hJ))
  have h2δ : (2 : ℝ) ≤ (2 : ℝ) ^ ((δ / 2) * (J : ℝ)) := by simpa using hJ₁ J hj₁
  have h2γ : (2 : ℝ) ≤ (2 : ℝ) ^ ((γ * ε / 2) * (J : ℝ)) := by simpa using hJ₂ J hj₂
  have h64 : (64 : ℝ) ≤ (2 : ℝ) ^ (κ * (J : ℝ)) := by
    have hh := hJ₃ J hj₃
    norm_num at hh
    exact hh
  let U := A ∪ B
  have hUcard : (U.card : ℝ) ≤ (A.card : ℝ) + (B.card : ℝ) := by
    exact_mod_cast Finset.card_union_le A B
  have hUsize : (U.card : ℝ) ≤ (2 : ℝ) ^ ((1 - δ / 2) * (J : ℝ)) := by
    calc
      _ ≤ (A.card : ℝ) + (B.card : ℝ) := hUcard
      _ ≤ (2 : ℝ) ^ ((1 - δ) * (J : ℝ)) + (2 : ℝ) ^ ((1 - δ) * (J : ℝ)) := add_le_add hAsize hBsize
      _ = 2 * (2 : ℝ) ^ ((1 - δ) * (J : ℝ)) := by ring
      _ ≤ (2 : ℝ) ^ ((δ / 2) * (J : ℝ)) * (2 : ℝ) ^ ((1 - δ) * (J : ℝ)) := by gcongr
      _ = _ := by rw [← Real.rpow_add (by norm_num)]; congr 1; ring
  have hUmass : DyadicRingSetNonconcentration (γ / 2) ε U := by
    intro L hL hεL r
    have hh := finite_fiber_bound_union (fun a : ZMod (2 ^ J) => (a.val : ZMod (2 ^ L)))
      (show 0 ≤ (2 : ℝ) ^ (-γ * (L : ℝ)) by positivity) (hAmass L hL hεL) (hBmass L hL hεL) r
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    calc
      _ ≤ (2 : ℝ) ^ ((γ * ε / 2) * (J : ℝ)) * (2 : ℝ) ^ (-γ * (L : ℝ)) := by gcongr
      _ = (2 : ℝ) ^ ((γ * ε / 2) * (J : ℝ) - γ * (L : ℝ)) := by
        rw [← Real.rpow_add (by norm_num)]; congr 1; ring
      _ ≤ _ := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        nlinarith only [mul_lt_mul_of_pos_left hεL hγ]
  have hTmass' : DyadicUnitSetNonconcentration (γ / 2) ε T := by
    intro L hL hεL r
    apply (hTmass L hL hεL r).trans
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    nlinarith only [mul_nonneg hγ.le (Nat.cast_nonneg L : (0 : ℝ) ≤ L)]
  have hUE := havg J hj₀ U T (hA.mono Finset.subset_union_left) hT hUsize hUmass hTmass'
  have hunion : (∑ u ∈ T, (Finset.addEnergy A (ringDilate (u : ZMod (2 ^ J)) B) : ℝ)) ≤
      (2 : ℝ) ^ (-κ * (J : ℝ)) * (T.card : ℝ) * ((A.card : ℝ) + (B.card : ℝ)) ^ 3 := by
    calc
      _ ≤ ∑ u ∈ T, (Finset.addEnergy U (ringDilate (u : ZMod (2 ^ J)) U) : ℝ) := by
        apply Finset.sum_le_sum
        intro u hu
        exact_mod_cast Finset.addEnergy_mono Finset.subset_union_left
          (ring_dilate_subset (u : ZMod (2 ^ J)) (Finset.subset_union_right : B ⊆ A ∪ B))
      _ ≤ (2 : ℝ) ^ (-κ * (J : ℝ)) * (T.card : ℝ) * (U.card : ℝ) ^ 3 := hUE
      _ ≤ _ := by gcongr
  have hleft : (∑ u ∈ T, (Finset.addEnergy A (ringDilate (u : ZMod (2 ^ J)) B) : ℝ)) ≤
      (T.card : ℝ) * (A.card : ℝ) ^ 2 * (B.card : ℝ) := by
    calc
      _ ≤ ∑ _u ∈ T, (A.card : ℝ) ^ 2 * (B.card : ℝ) :=
        Finset.sum_le_sum (fun u _ => ring_unit_mixed_energy_upper_left A B u)
      _ = _ := by simp; ring
  have hright : (∑ u ∈ T, (Finset.addEnergy A (ringDilate (u : ZMod (2 ^ J)) B) : ℝ)) ≤
      (T.card : ℝ) * (A.card : ℝ) * (B.card : ℝ) ^ 2 := by
    calc
      _ ≤ ∑ _u ∈ T, (A.card : ℝ) * (B.card : ℝ) ^ 2 :=
        Finset.sum_le_sum (fun u _ => ring_unit_mixed_energy_upper_right A B u)
      _ = _ := by simp; ring
  have hbalance : 64 * ((2 : ℝ) ^ (-κ * (J : ℝ))) ^ 2 *
      ((2 : ℝ) ^ ((κ / 4) * (J : ℝ))) ^ 3 ≤ (2 : ℝ) ^ (-(κ / 4) * (J : ℝ)) := by
    calc
      _ ≤ (2 : ℝ) ^ (κ * (J : ℝ)) * ((2 : ℝ) ^ (-κ * (J : ℝ))) ^ 2 *
          ((2 : ℝ) ^ ((κ / 4) * (J : ℝ))) ^ 3 := by gcongr
      _ = _ := by
        rw [← Real.rpow_mul_natCast (by norm_num), ← Real.rpow_mul_natCast (by norm_num),
          ← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num)]
        congr 1
        norm_num
        ring
  have hinverse : 1 ≤ (2 : ℝ) ^ (-(κ / 4) * (J : ℝ)) * (2 : ℝ) ^ ((κ / 4) * (J : ℝ)) := by
    rw [← Real.rpow_add (by norm_num),
      show -(κ / 4) * (J : ℝ) + (κ / 4) * (J : ℝ) = 0 by ring, Real.rpow_zero]
  exact mixed_energy_square_bound (Finset.sum_nonneg (fun u _ => Nat.cast_nonneg _))
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (by positivity) (by positivity) (by positivity) hbalance hinverse hunion hleft hright


theorem norm_sum_sq_le_card_mul_sum_sq {X : Type*} (I : Finset X) (f : X → ℂ) :
    ‖∑ i ∈ I, f i‖ ^ 2 ≤ (I.card : ℝ) * ∑ i ∈ I, ‖f i‖ ^ 2 := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq I (fun _ => (1 : ℝ)) (fun i => ‖f i‖)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hc
  exact (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le I f) 2).trans hc

noncomputable def cyclicUnitDilate {q : ℕ} [NeZero q]
    (f : ZMod q → ℂ) (u : (ZMod q)ˣ) (x : ZMod q) : ℂ := f ((u⁻¹ : (ZMod q)ˣ) * x)

noncomputable def cyclicSetCombination {X : Type*} {q : ℕ} [NeZero q]
    (I : Finset X) (w : X → ℝ) (A : X → Finset (ZMod q)) (x : ZMod q) : ℂ :=
  ∑ i ∈ I, (w i : ℂ) * cyclicSetIndicator (A i) x

theorem mem_ring_unit_dilate {R : Type*} [Ring R] [DecidableEq R]
    (u : Rˣ) (A : Finset R) (x : R) :
    x ∈ ringDilate (u : R) A ↔ ((u⁻¹ : Rˣ) : R) * x ∈ A := by
  constructor
  · intro hx
    obtain ⟨a, ha, hax⟩ := Finset.mem_image.mp hx
    rw [← hax, ← mul_assoc, Units.inv_mul, one_mul]
    exact ha
  · intro hx
    apply Finset.mem_image.mpr
    exact ⟨((u⁻¹ : Rˣ) : R) * x, hx, by rw [← mul_assoc, Units.mul_inv, one_mul]⟩

theorem cyclic_unit_dilate_indicator {q : ℕ} [NeZero q]
    (A : Finset (ZMod q)) (u : (ZMod q)ˣ) :
    cyclicUnitDilate (cyclicSetIndicator A) u = cyclicSetIndicator (ringDilate (u : ZMod q) A) := by
  classical
  funext x
  simp only [cyclicUnitDilate, cyclicSetIndicator, mem_ring_unit_dilate]

theorem cyclic_unit_dilate_set_combination {X : Type*} {q : ℕ} [NeZero q]
    (I : Finset X) (w : X → ℝ) (A : X → Finset (ZMod q)) (u : (ZMod q)ˣ) :
    cyclicUnitDilate (cyclicSetCombination I w A) u =
      cyclicSetCombination I w (fun i => ringDilate (u : ZMod q) (A i)) := by
  funext x
  unfold cyclicSetCombination cyclicUnitDilate
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  exact congrFun (cyclic_unit_dilate_indicator (A i) u) x

theorem cyclic_convolution_scaled {q : ℕ} [NeZero q]
    (f g : ZMod q → ℂ) (a b : ℂ) (x : ZMod q) :
    cyclicConvolution (fun y => a * f y) (fun y => b * g y) x = a * b * cyclicConvolution f g x := by
  unfold cyclicConvolution
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  ring

theorem cyclic_convolution_sum_left {X : Type*} {q : ℕ} [NeZero q]
    (I : Finset X) (f : X → ZMod q → ℂ) (g : ZMod q → ℂ) (x : ZMod q) :
    cyclicConvolution (fun y => ∑ i ∈ I, f i y) g x = ∑ i ∈ I, cyclicConvolution (f i) g x := by
  simp only [cyclicConvolution, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem cyclic_convolution_sum_right {X : Type*} {q : ℕ} [NeZero q]
    (I : Finset X) (f : ZMod q → ℂ) (g : X → ZMod q → ℂ) (x : ZMod q) :
    cyclicConvolution f (fun y => ∑ i ∈ I, g i y) x = ∑ i ∈ I, cyclicConvolution f (g i) x := by
  simp only [cyclicConvolution, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem cyclic_convolution_set_combinations {X Y : Type*} {q : ℕ} [NeZero q]
    (I : Finset X) (K : Finset Y) (w : X → ℝ) (v : Y → ℝ)
    (A : X → Finset (ZMod q)) (B : Y → Finset (ZMod q)) (x : ZMod q) :
    cyclicConvolution (cyclicSetCombination I w A) (cyclicSetCombination K v B) x =
      ∑ i ∈ I, ∑ j ∈ K, (w i : ℂ) * (v j : ℂ) *
        cyclicConvolution (cyclicSetIndicator (A i)) (cyclicSetIndicator (B j)) x := by
  unfold cyclicSetCombination
  rw [cyclic_convolution_sum_left]
  apply Finset.sum_congr rfl
  intro i hi
  rw [cyclic_convolution_sum_right]
  apply Finset.sum_congr rfl
  intro j hj
  exact cyclic_convolution_scaled _ _ _ _ _

theorem finite_weighted_card_three_halves_bound {X : Type*}
    (I : Finset X) (w a : X → ℝ) (hw : ∀ i ∈ I, 0 ≤ w i) (ha : ∀ i ∈ I, 0 ≤ a i) :
    (∑ i ∈ I, w i ^ 2 * (a i * Real.sqrt (a i))) ^ 2 ≤
      (∑ i ∈ I, w i ^ 2 * a i) * (∑ i ∈ I, w i * a i) ^ 2 := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq I (fun i => w i * Real.sqrt (a i)) (fun i => w i * a i)
  have hfirst : (∑ i ∈ I, (w i * Real.sqrt (a i)) ^ 2) = ∑ i ∈ I, w i ^ 2 * a i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [mul_pow, Real.sq_sqrt (ha i hi)]
  have hprod : (∑ i ∈ I, (w i * Real.sqrt (a i)) * (w i * a i)) =
      ∑ i ∈ I, w i ^ 2 * (a i * Real.sqrt (a i)) := by
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hfirst, hprod] at hc
  apply hc.trans
  apply mul_le_mul_of_nonneg_left _ (Finset.sum_nonneg (fun i hi => mul_nonneg (sq_nonneg _) (ha i hi)))
  exact Finset.sum_sq_le_sq_sum_of_nonneg (fun i hi => mul_nonneg (hw i hi) (ha i hi))

theorem cyclic_set_combination_unit_energy {X : Type*} {q : ℕ} [NeZero q]
    (I : Finset X) (w : X → ℝ) (A : X → Finset (ZMod q)) (u : (ZMod q)ˣ)
    (hw : ∀ i ∈ I, 0 ≤ w i) :
    (∑ x : ZMod q, ‖cyclicConvolution (cyclicSetCombination I w A)
      (cyclicUnitDilate (cyclicSetCombination I w A) u) x‖ ^ 2) ≤
      (I.card : ℝ) ^ 2 * ∑ i ∈ I, ∑ j ∈ I, w i ^ 2 * w j ^ 2 *
        (Finset.addEnergy (A i) (ringDilate (u : ZMod q) (A j)) : ℝ) := by
  have hpoint : ∀ x : ZMod q,
      ‖cyclicConvolution (cyclicSetCombination I w A)
        (cyclicUnitDilate (cyclicSetCombination I w A) u) x‖ ^ 2 ≤
        (I.card : ℝ) ^ 2 * ∑ i ∈ I, ∑ j ∈ I, w i ^ 2 * w j ^ 2 *
          ‖cyclicConvolution (cyclicSetIndicator (A i))
            (cyclicSetIndicator (ringDilate (u : ZMod q) (A j))) x‖ ^ 2 := by
    intro x
    rw [cyclic_unit_dilate_set_combination, cyclic_convolution_set_combinations]
    have hh := norm_sum_sq_le_card_mul_sum_sq (I ×ˢ I) (fun p =>
      (w p.1 : ℂ) * (w p.2 : ℂ) * cyclicConvolution (cyclicSetIndicator (A p.1))
        (cyclicSetIndicator (ringDilate (u : ZMod q) (A p.2))) x)
    simp only [Finset.sum_product, Finset.card_product, Nat.cast_mul] at hh
    apply hh.trans_eq
    rw [pow_two]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hw i hi), abs_of_nonneg (hw j hj),
      mul_pow, mul_pow]
  calc
    _ ≤ ∑ x : ZMod q, (I.card : ℝ) ^ 2 * ∑ i ∈ I, ∑ j ∈ I, w i ^ 2 * w j ^ 2 *
        ‖cyclicConvolution (cyclicSetIndicator (A i))
          (cyclicSetIndicator (ringDilate (u : ZMod q) (A j))) x‖ ^ 2 :=
      Finset.sum_le_sum (fun x _ => hpoint x)
    _ = (I.card : ℝ) ^ 2 * ∑ i ∈ I, ∑ j ∈ I, w i ^ 2 * w j ^ 2 *
        ∑ x : ZMod q, ‖cyclicConvolution (cyclicSetIndicator (A i))
          (cyclicSetIndicator (ringDilate (u : ZMod q) (A j))) x‖ ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [← Finset.mul_sum]
    _ = _ := by simp_rw [cyclic_set_convolution_energy]

theorem cyclic_set_combination_average_energy {X : Type*} {q : ℕ} [NeZero q]
    (I : Finset X) (w : X → ℝ) (A : X → Finset (ZMod q)) (T : Finset (ZMod q)ˣ)
    {C : ℝ} (hw : ∀ i ∈ I, 0 ≤ w i) (hC : 0 ≤ C)
    (hE : ∀ i ∈ I, ∀ j ∈ I,
      (∑ u ∈ T, (Finset.addEnergy (A i) (ringDilate (u : ZMod q) (A j)) : ℝ)) ≤
        C * ((A i).card : ℝ) * Real.sqrt ((A i).card : ℝ) *
          ((A j).card : ℝ) * Real.sqrt ((A j).card : ℝ)) :
    (∑ u ∈ T, ∑ x : ZMod q, ‖cyclicConvolution (cyclicSetCombination I w A)
      (cyclicUnitDilate (cyclicSetCombination I w A) u) x‖ ^ 2) ≤
      (I.card : ℝ) ^ 2 * C * (∑ i ∈ I, w i ^ 2 * ((A i).card : ℝ)) *
        (∑ i ∈ I, w i * ((A i).card : ℝ)) ^ 2 := by
  let a := fun i => ((A i).card : ℝ)
  have hfactor : (∑ i ∈ I, ∑ j ∈ I, w i ^ 2 * w j ^ 2 *
      (C * a i * Real.sqrt (a i) * a j * Real.sqrt (a j))) =
      C * (∑ i ∈ I, w i ^ 2 * (a i * Real.sqrt (a i))) ^ 2 := by
    rw [pow_two, Finset.sum_mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  calc
    _ ≤ ∑ u ∈ T, (I.card : ℝ) ^ 2 * ∑ i ∈ I, ∑ j ∈ I, w i ^ 2 * w j ^ 2 *
        (Finset.addEnergy (A i) (ringDilate (u : ZMod q) (A j)) : ℝ) :=
      Finset.sum_le_sum (fun u _ => cyclic_set_combination_unit_energy I w A u hw)
    _ = (I.card : ℝ) ^ 2 * ∑ i ∈ I, ∑ j ∈ I, w i ^ 2 * w j ^ 2 *
        ∑ u ∈ T, (Finset.addEnergy (A i) (ringDilate (u : ZMod q) (A j)) : ℝ) := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [← Finset.mul_sum]
    _ ≤ (I.card : ℝ) ^ 2 * ∑ i ∈ I, ∑ j ∈ I, w i ^ 2 * w j ^ 2 *
        (C * a i * Real.sqrt (a i) * a j * Real.sqrt (a j)) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (hE i hi j hj) (by positivity)
    _ = (I.card : ℝ) ^ 2 * C *
        (∑ i ∈ I, w i ^ 2 * (a i * Real.sqrt (a i))) ^ 2 := by rw [hfactor]; ring
    _ ≤ (I.card : ℝ) ^ 2 * C *
        ((∑ i ∈ I, w i ^ 2 * a i) * (∑ i ∈ I, w i * a i) ^ 2) :=
      mul_le_mul_of_nonneg_left (finite_weighted_card_three_halves_bound I w a hw
        (fun i _ => Nat.cast_nonneg _)) (mul_nonneg (sq_nonneg _) hC)
    _ = _ := by ring

theorem dyadic_mixed_energy_bound_of_sq {J : ℕ}
    {A B : Finset (ZMod (2 ^ J))} {T : Finset (ZMod (2 ^ J))ˣ} {τ : ℝ}
    (hE : (∑ u ∈ T, (Finset.addEnergy A (ringDilate (u : ZMod (2 ^ J)) B) : ℝ)) ^ 2 ≤
      (2 : ℝ) ^ (-τ * (J : ℝ)) * (T.card : ℝ) ^ 2 * (A.card : ℝ) ^ 3 * (B.card : ℝ) ^ 3) :
    (∑ u ∈ T, (Finset.addEnergy A (ringDilate (u : ZMod (2 ^ J)) B) : ℝ)) ≤
      ((2 : ℝ) ^ (-(τ / 2) * (J : ℝ)) * (T.card : ℝ)) *
        (A.card : ℝ) * Real.sqrt (A.card : ℝ) * (B.card : ℝ) * Real.sqrt (B.card : ℝ) := by
  have hscale : ((2 : ℝ) ^ (-(τ / 2) * (J : ℝ))) ^ 2 = (2 : ℝ) ^ (-τ * (J : ℝ)) := by
    rw [← Real.rpow_mul_natCast (by norm_num)]
    congr 1
    norm_num
    ring
  have hsquare : (((2 : ℝ) ^ (-(τ / 2) * (J : ℝ)) * (T.card : ℝ)) *
      (A.card : ℝ) * Real.sqrt (A.card : ℝ) * (B.card : ℝ) * Real.sqrt (B.card : ℝ)) ^ 2 =
      (2 : ℝ) ^ (-τ * (J : ℝ)) * (T.card : ℝ) ^ 2 * (A.card : ℝ) ^ 3 * (B.card : ℝ) ^ 3 := by
    simp only [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), hscale]
    ring
  have hnonneg : 0 ≤ ((2 : ℝ) ^ (-(τ / 2) * (J : ℝ)) * (T.card : ℝ)) *
      (A.card : ℝ) * Real.sqrt (A.card : ℝ) * (B.card : ℝ) * Real.sqrt (B.card : ℝ) := by positivity
  rw [← hsquare] at hE
  exact (sq_le_sq₀ (Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)) hnonneg).mp hE

theorem cyclic_set_combination_norm {X : Type*} {q : ℕ} [NeZero q]
    (I : Finset X) (w : X → ℝ) (A : X → Finset (ZMod q))
    (hw : ∀ i ∈ I, 0 ≤ w i) (x : ZMod q) :
    ‖cyclicSetCombination I w A x‖ = ∑ i ∈ I, w i * ‖cyclicSetIndicator (A i) x‖ := by
  classical
  have heq : cyclicSetCombination I w A x =
      ((∑ i ∈ I, w i * ‖cyclicSetIndicator (A i) x‖ : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hx : x ∈ A i <;> simp [cyclicSetIndicator, hx]
  rw [heq, Complex.norm_of_nonneg (Finset.sum_nonneg (fun i hi => mul_nonneg (hw i hi) (norm_nonneg _)))]

theorem cyclic_set_combination_sum_norm {X : Type*} {q : ℕ} [NeZero q]
    (I : Finset X) (w : X → ℝ) (A : X → Finset (ZMod q))
    (hw : ∀ i ∈ I, 0 ≤ w i) :
    (∑ x : ZMod q, ‖cyclicSetCombination I w A x‖) = ∑ i ∈ I, w i * ((A i).card : ℝ) := by
  simp_rw [cyclic_set_combination_norm I w A hw]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.mul_sum, cyclic_set_indicator_norm_sum]

theorem cyclic_set_combination_sq_norm_lower {X : Type*} {q : ℕ} [NeZero q]
    (I : Finset X) (w : X → ℝ) (A : X → Finset (ZMod q))
    (hw : ∀ i ∈ I, 0 ≤ w i) :
    (∑ i ∈ I, w i ^ 2 * ((A i).card : ℝ)) ≤ ∑ x : ZMod q, ‖cyclicSetCombination I w A x‖ ^ 2 := by
  calc
    _ = ∑ i ∈ I, w i ^ 2 * ∑ x : ZMod q, ‖cyclicSetIndicator (A i) x‖ ^ 2 := by
      simp_rw [cyclic_set_indicator_sq_norm_sum]
    _ = ∑ x : ZMod q, ∑ i ∈ I, (w i * ‖cyclicSetIndicator (A i) x‖) ^ 2 := by
      simp_rw [Finset.mul_sum, mul_pow]
      rw [Finset.sum_comm]
    _ ≤ ∑ x : ZMod q, (∑ i ∈ I, w i * ‖cyclicSetIndicator (A i) x‖) ^ 2 :=
      Finset.sum_le_sum (fun x _ => Finset.sum_sq_le_sq_sum_of_nonneg
        (fun i hi => mul_nonneg (hw i hi) (norm_nonneg _)))
    _ = _ := by simp_rw [cyclic_set_combination_norm I w A hw]

/-- Flattening for a bounded number of nonnegative set levels. The level
sets satisfy the same density and residue bounds, and their total mass is at most one. -/
theorem exists_dyadic_set_combination_flattening {X : Type*} {γ δ : ℝ}
    (hγ : 0 < γ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ τ ε : ℝ, 0 < τ ∧ 0 < ε ∧ ε ≤ 1 / 4 ∧ ∃ J₀ : ℕ,
      ∀ J : ℕ, J₀ ≤ J → ∀ I : Finset X, ∀ w : X → ℝ,
      ∀ A : X → Finset (ZMod (2 ^ J)), ∀ T : Finset (ZMod (2 ^ J))ˣ,
        (∀ i ∈ I, 0 ≤ w i) → T.Nonempty →
        (I.card : ℝ) ≤ (2 : ℝ) ^ (τ * (J : ℝ)) →
        (∑ i ∈ I, w i * ((A i).card : ℝ)) ≤ 1 →
        (∀ i ∈ I, (A i).Nonempty ∧
          ((A i).card : ℝ) ≤ (2 : ℝ) ^ ((1 - δ) * (J : ℝ)) ∧
          DyadicRingSetNonconcentration γ ε (A i)) →
        DyadicUnitSetNonconcentration γ ε T →
        (∑ u ∈ T, ∑ x : ZMod (2 ^ J), ‖cyclicConvolution (cyclicSetCombination I w A)
          (cyclicUnitDilate (cyclicSetCombination I w A) u) x‖ ^ 2) ≤
          (2 : ℝ) ^ (-τ * (J : ℝ)) * (T.card : ℝ) *
            ∑ x : ZMod (2 ^ J), ‖cyclicSetCombination I w A x‖ ^ 2 := by
  obtain ⟨κ, ε, hκ, hε, hε4, J₀, hmix⟩ := exists_dyadic_average_mixed_energy_decay hγ hδ hδ1
  refine ⟨κ / 6, ε, by positivity, hε, hε4, J₀, ?_⟩
  intro J hJ I w A T hw hT hI hmass hA hTmass
  have hE : ∀ i ∈ I, ∀ j ∈ I,
      (∑ u ∈ T, (Finset.addEnergy (A i) (ringDilate (u : ZMod (2 ^ J)) (A j)) : ℝ)) ≤
        ((2 : ℝ) ^ (-(κ / 2) * (J : ℝ)) * (T.card : ℝ)) *
          ((A i).card : ℝ) * Real.sqrt ((A i).card : ℝ) *
            ((A j).card : ℝ) * Real.sqrt ((A j).card : ℝ) := by
    intro i hi j hj
    exact dyadic_mixed_energy_bound_of_sq (hmix J hJ (A i) (A j) T (hA i hi).1
      (hA j hj).1 hT (hA i hi).2.1 (hA j hj).2.1 (hA i hi).2.2 (hA j hj).2.2 hTmass)
  have hh := cyclic_set_combination_average_energy I w A T hw (by positivity) hE
  have hmass0 : 0 ≤ ∑ i ∈ I, w i * ((A i).card : ℝ) :=
    Finset.sum_nonneg (fun i hi => mul_nonneg (hw i hi) (Nat.cast_nonneg _))
  have hmass2 : (∑ i ∈ I, w i * ((A i).card : ℝ)) ^ 2 ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ hmass0 hmass 2
  have hI2 : (I.card : ℝ) ^ 2 ≤ ((2 : ℝ) ^ ((κ / 6) * (J : ℝ))) ^ 2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hI 2
  have hcoef : (I.card : ℝ) ^ 2 *
      ((2 : ℝ) ^ (-(κ / 2) * (J : ℝ)) * (T.card : ℝ)) ≤
        (2 : ℝ) ^ (-(κ / 6) * (J : ℝ)) * (T.card : ℝ) := by
    calc
      _ ≤ ((2 : ℝ) ^ ((κ / 6) * (J : ℝ))) ^ 2 *
          ((2 : ℝ) ^ (-(κ / 2) * (J : ℝ)) * (T.card : ℝ)) :=
        mul_le_mul_of_nonneg_right hI2 (by positivity)
      _ = _ := by
        rw [← Real.rpow_mul_natCast (by norm_num), ← mul_assoc, ← Real.rpow_add (by norm_num)]
        congr 2
        norm_num
        ring
  calc
    _ ≤ (I.card : ℝ) ^ 2 * ((2 : ℝ) ^ (-(κ / 2) * (J : ℝ)) * (T.card : ℝ)) *
        (∑ i ∈ I, w i ^ 2 * ((A i).card : ℝ)) * (∑ i ∈ I, w i * ((A i).card : ℝ)) ^ 2 := hh
    _ ≤ (I.card : ℝ) ^ 2 * ((2 : ℝ) ^ (-(κ / 2) * (J : ℝ)) * (T.card : ℝ)) *
        (∑ i ∈ I, w i ^ 2 * ((A i).card : ℝ)) * 1 :=
      mul_le_mul_of_nonneg_left hmass2 (by positivity)
    _ ≤ ((2 : ℝ) ^ (-(κ / 6) * (J : ℝ)) * (T.card : ℝ)) *
        (∑ i ∈ I, w i ^ 2 * ((A i).card : ℝ)) := by
      rw [mul_one]
      exact mul_le_mul_of_nonneg_right hcoef (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left (cyclic_set_combination_sq_norm_lower I w A hw) (by positivity)

theorem weighted_sum_sq_le_mass_mul {X : Type*} (I : Finset X) (w t : X → ℝ)
    (hw : ∀ i ∈ I, 0 ≤ w i) :
    (∑ i ∈ I, w i * t i) ^ 2 ≤ (∑ i ∈ I, w i) * ∑ i ∈ I, w i * t i ^ 2 := by
  have hprod : (∑ i ∈ I, Real.sqrt (w i) * (Real.sqrt (w i) * t i)) = ∑ i ∈ I, w i * t i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [← mul_assoc, Real.mul_self_sqrt (hw i hi)]
  have hfirst : (∑ i ∈ I, Real.sqrt (w i) ^ 2) = ∑ i ∈ I, w i :=
    Finset.sum_congr rfl (fun i hi => Real.sq_sqrt (hw i hi))
  have hsecond : (∑ i ∈ I, (Real.sqrt (w i) * t i) ^ 2) = ∑ i ∈ I, w i * t i ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [mul_pow, Real.sq_sqrt (hw i hi)]
  have hh := Finset.sum_mul_sq_le_sq_mul_sq I (fun i => Real.sqrt (w i)) (fun i => Real.sqrt (w i) * t i)
  rwa [hprod, hfirst, hsecond] at hh

theorem cyclic_convolution_young_sq {q : ℕ} [NeZero q] (f g : ZMod q → ℂ) :
    (∑ x : ZMod q, ‖cyclicConvolution f g x‖ ^ 2) ≤
      (∑ x : ZMod q, ‖f x‖) ^ 2 * ∑ x : ZMod q, ‖g x‖ ^ 2 := by
  have hpoint : ∀ x : ZMod q, ‖cyclicConvolution f g x‖ ^ 2 ≤
      (∑ y : ZMod q, ‖f y‖) * ∑ y : ZMod q, ‖f y‖ * ‖g (x - y)‖ ^ 2 := by
    intro x
    have hh : ‖cyclicConvolution f g x‖ ≤ ∑ y : ZMod q, ‖f y‖ * ‖g (x - y)‖ := by
      simpa only [cyclicConvolution, norm_mul] using norm_sum_le Finset.univ (fun y => f y * g (x - y))
    exact (pow_le_pow_left₀ (norm_nonneg _) hh 2).trans
      (weighted_sum_sq_le_mass_mul Finset.univ (fun y => ‖f y‖) (fun y => ‖g (x - y)‖)
        (fun _ _ => norm_nonneg _))
  calc
    _ ≤ ∑ x : ZMod q, (∑ y : ZMod q, ‖f y‖) * ∑ y : ZMod q, ‖f y‖ * ‖g (x - y)‖ ^ 2 :=
      Finset.sum_le_sum (fun x _ => hpoint x)
    _ = (∑ y : ZMod q, ‖f y‖) * ∑ y : ZMod q, ‖f y‖ * ∑ x : ZMod q, ‖g x‖ ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro y hy
      rw [← Finset.mul_sum]
      congr 1
      exact Fintype.sum_equiv (Equiv.subRight y) _ _ (fun _ => rfl)
    _ = _ := by rw [← Finset.sum_mul]; ring

theorem cyclic_convolution_comm {q : ℕ} [NeZero q] (f g : ZMod q → ℂ) :
    cyclicConvolution f g = cyclicConvolution g f := by
  funext x
  unfold cyclicConvolution
  apply Fintype.sum_equiv (Equiv.subLeft x)
  intro y
  simp only [Equiv.subLeft_apply, sub_sub_cancel]
  ring

theorem cyclic_convolution_young_sq_right {q : ℕ} [NeZero q] (f g : ZMod q → ℂ) :
    (∑ x : ZMod q, ‖cyclicConvolution f g x‖ ^ 2) ≤
      (∑ x : ZMod q, ‖g x‖) ^ 2 * ∑ x : ZMod q, ‖f x‖ ^ 2 := by
  rw [cyclic_convolution_comm]
  exact cyclic_convolution_young_sq g f

theorem cyclic_unit_dilate_sum_norm {q : ℕ} [NeZero q] (f : ZMod q → ℂ) (u : (ZMod q)ˣ) :
    (∑ x : ZMod q, ‖cyclicUnitDilate f u x‖) = ∑ x : ZMod q, ‖f x‖ := by
  exact Fintype.sum_equiv (ringUnitMulAddEquiv u⁻¹).toEquiv _ _ (fun _ => rfl)

theorem cyclic_unit_dilate_sq_norm {q : ℕ} [NeZero q] (f : ZMod q → ℂ) (u : (ZMod q)ˣ) :
    (∑ x : ZMod q, ‖cyclicUnitDilate f u x‖ ^ 2) = ∑ x : ZMod q, ‖f x‖ ^ 2 := by
  exact Fintype.sum_equiv (ringUnitMulAddEquiv u⁻¹).toEquiv _ _ (fun _ => rfl)

theorem cyclic_convolution_norm_of_nonnegative {q : ℕ} [NeZero q]
    (f g : ZMod q → ℂ) (hf : ∀ x, f x = (‖f x‖ : ℂ)) (hg : ∀ x, g x = (‖g x‖ : ℂ))
    (x : ZMod q) : ‖cyclicConvolution f g x‖ = ∑ y : ZMod q, ‖f y‖ * ‖g (x - y)‖ := by
  have heq : cyclicConvolution f g x = ((∑ y : ZMod q, ‖f y‖ * ‖g (x - y)‖ : ℝ) : ℂ) := by
    unfold cyclicConvolution
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro y hy
    rw [Complex.ofReal_mul, ← hf, ← hg]
  rw [heq, Complex.norm_of_nonneg (Finset.sum_nonneg (fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)))]

theorem cyclic_set_combination_nonnegative {X : Type*} {q : ℕ} [NeZero q]
    (I : Finset X) (w : X → ℝ) (A : X → Finset (ZMod q)) (hw : ∀ i ∈ I, 0 ≤ w i)
    (x : ZMod q) : cyclicSetCombination I w A x = (‖cyclicSetCombination I w A x‖ : ℂ) := by
  classical
  rw [cyclic_set_combination_norm I w A hw, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hx : x ∈ A i <;> simp [cyclicSetIndicator, hx]

theorem cyclic_convolution_norm_dominated {q : ℕ} [NeZero q]
    (f g F G : ZMod q → ℂ) (hF : ∀ x, F x = (‖F x‖ : ℂ)) (hG : ∀ x, G x = (‖G x‖ : ℂ))
    (hf : ∀ x, ‖f x‖ ≤ ‖F x‖) (hg : ∀ x, ‖g x‖ ≤ ‖G x‖) (x : ZMod q) :
    ‖cyclicConvolution f g x‖ ≤ ‖cyclicConvolution F G x‖ := by
  rw [cyclic_convolution_norm_of_nonnegative F G hF hG]
  calc
    _ ≤ ∑ y : ZMod q, ‖f y‖ * ‖g (x - y)‖ := by
      simpa only [cyclicConvolution, norm_mul] using norm_sum_le Finset.univ (fun y => f y * g (x - y))
    _ ≤ _ := Finset.sum_le_sum (fun y _ => mul_le_mul (hf y) (hg _) (norm_nonneg _) (norm_nonneg _))


noncomputable def dyadicLevelWeight (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ n

noncomputable def finiteDyadicLevel {X : Type*} [Fintype X] (p : X → ℝ) (n : ℕ) : Finset X := by
  classical
  exact Finset.univ.filter (fun x => dyadicLevelWeight n ≤ p x ∧ p x < 2 * dyadicLevelWeight n)

theorem dyadic_level_weight_pos (n : ℕ) : 0 < dyadicLevelWeight n := by
  unfold dyadicLevelWeight
  positivity

theorem dyadic_level_weight_zero : dyadicLevelWeight 0 = 1 := by simp [dyadicLevelWeight]

theorem dyadic_level_weight_succ (n : ℕ) : 2 * dyadicLevelWeight (n + 1) = dyadicLevelWeight n := by
  unfold dyadicLevelWeight
  rw [pow_succ]
  ring

theorem dyadic_level_weight_antitone {m n : ℕ} (hmn : m ≤ n) : dyadicLevelWeight n ≤ dyadicLevelWeight m := by
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hmn

theorem dyadic_level_weight_rpow (n : ℕ) : dyadicLevelWeight n = (2 : ℝ) ^ (-(n : ℝ)) := by
  rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, ← inv_pow]
  simp only [dyadicLevelWeight, one_div]

theorem mem_finite_dyadic_level {X : Type*} [Fintype X] (p : X → ℝ) (n : ℕ) (x : X) :
    x ∈ finiteDyadicLevel p n ↔ dyadicLevelWeight n ≤ p x ∧ p x < 2 * dyadicLevelWeight n := by
  classical
  simp only [finiteDyadicLevel, Finset.mem_filter, Finset.mem_univ, true_and]

theorem finite_dyadic_level_disjoint {X : Type*} [Fintype X] (p : X → ℝ) {m n : ℕ}
    (hmn : m ≠ n) : Disjoint (finiteDyadicLevel p m) (finiteDyadicLevel p n) := by
  classical
  rw [Finset.disjoint_left]
  intro x hxm hxn
  obtain ⟨hmlo, hmhi⟩ := (mem_finite_dyadic_level p m x).mp hxm
  obtain ⟨hnlo, hnhi⟩ := (mem_finite_dyadic_level p n x).mp hxn
  rcases lt_or_gt_of_ne hmn with hmn | hnm
  · have hh := mul_le_mul_of_nonneg_left (dyadic_level_weight_antitone (Nat.succ_le_of_lt hmn)) (by norm_num : (0 : ℝ) ≤ 2)
    rw [dyadic_level_weight_succ] at hh
    linarith only [hh, hmlo, hnhi]
  · have hh := mul_le_mul_of_nonneg_left (dyadic_level_weight_antitone (Nat.succ_le_of_lt hnm)) (by norm_num : (0 : ℝ) ≤ 2)
    rw [dyadic_level_weight_succ] at hh
    linarith only [hh, hnlo, hmhi]

theorem exists_finite_dyadic_level {X : Type*} [Fintype X] (p : X → ℝ) (N : ℕ) {x : X}
    (hxlo : dyadicLevelWeight N ≤ p x) (hxhi : p x ≤ 1) :
    ∃ n : ℕ, n ≤ N ∧ x ∈ finiteDyadicLevel p n := by
  induction N with
  | zero =>
    refine ⟨0, le_rfl, (mem_finite_dyadic_level p 0 x).mpr ⟨hxlo, ?_⟩⟩
    rw [dyadic_level_weight_zero]
    linarith only [hxhi]
  | succ N ih =>
    by_cases hh : dyadicLevelWeight N ≤ p x
    · obtain ⟨n, hn, hxn⟩ := ih hh
      exact ⟨n, hn.trans (Nat.le_succ _), hxn⟩
    · refine ⟨N + 1, le_rfl, (mem_finite_dyadic_level p (N + 1) x).mpr ⟨hxlo, ?_⟩⟩
      rw [dyadic_level_weight_succ]
      exact lt_of_not_ge hh

theorem finite_level_card_bound {X : Type*} [Fintype X] [DecidableEq X]
    (p : X → ℝ) {A : Finset X} {w M : ℝ} (hp : ∀ x, 0 ≤ p x)
    (hmass : ∑ x : X, p x ≤ M) (hlower : ∀ x ∈ A, w ≤ p x) :
    w * (A.card : ℝ) ≤ M := by
  calc
    _ = ∑ _x ∈ A, w := by simp [mul_comm]
    _ ≤ ∑ x ∈ A, p x := Finset.sum_le_sum hlower
    _ ≤ ∑ x : X, p x := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun x _ _ => hp x)
    _ ≤ _ := hmass

theorem finite_level_fiber_bound {X Y : Type*} [Fintype X] [DecidableEq X] [DecidableEq Y]
    (p : X → ℝ) (π : X → Y) {A : Finset X} {w m M : ℝ}
    (hp : ∀ x, 0 ≤ p x) (hm : 0 < m)
    (hlower : ∀ x ∈ A, w ≤ p x) (hupper : ∀ x ∈ A, p x ≤ 2 * w)
    (hmass : m ≤ ∑ x ∈ A, p x)
    (hfiber : ∀ r : Y, (∑ x ∈ Finset.univ.filter (fun x => π x = r), p x) ≤ M) :
    ∀ r : Y, ((A.filter (fun x => π x = r)).card : ℝ) ≤ (2 * M / m) * (A.card : ℝ) := by
  intro r
  have hsize : m ≤ (2 * w) * (A.card : ℝ) := by
    apply hmass.trans
    calc
      _ ≤ ∑ _x ∈ A, 2 * w := Finset.sum_le_sum hupper
      _ = _ := by simp [mul_comm]
  have hcount : w * ((A.filter (fun x => π x = r)).card : ℝ) ≤ M := by
    calc
      _ = ∑ _x ∈ A.filter (fun x => π x = r), w := by simp [mul_comm]
      _ ≤ ∑ x ∈ A.filter (fun x => π x = r), p x :=
        Finset.sum_le_sum (fun x hx => hlower x (Finset.mem_filter.mp hx).1)
      _ ≤ ∑ x ∈ Finset.univ.filter (fun x => π x = r), p x :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset_filter _ (Finset.subset_univ _))
          (fun x _ _ => hp x)
      _ ≤ _ := hfiber r
  apply (mul_le_mul_iff_left₀ hm).mp
  calc
    _ ≤ ((2 * w) * (A.card : ℝ)) * ((A.filter (fun x => π x = r)).card : ℝ) := by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_right hsize
        (Nat.cast_nonneg (A.filter (fun x => π x = r)).card : (0 : ℝ) ≤ (A.filter (fun x => π x = r)).card)
    _ = (2 * (A.card : ℝ)) * (w * ((A.filter (fun x => π x = r)).card : ℝ)) := by ring
    _ ≤ (2 * (A.card : ℝ)) * M := mul_le_mul_of_nonneg_left hcount (by positivity)
    _ = _ := by field_simp

theorem finite_dyadic_level_fiber_bound {X Y : Type*} [Fintype X] [DecidableEq X] [DecidableEq Y]
    (p : X → ℝ) (π : X → Y) (n : ℕ) {m M : ℝ}
    (hp : ∀ x, 0 ≤ p x) (hm : 0 < m) (hmass : m ≤ ∑ x ∈ finiteDyadicLevel p n, p x)
    (hfiber : ∀ r : Y, (∑ x ∈ Finset.univ.filter (fun x => π x = r), p x) ≤ M) :
    ∀ r : Y, (((finiteDyadicLevel p n).filter (fun x => π x = r)).card : ℝ) ≤
      (2 * M / m) * ((finiteDyadicLevel p n).card : ℝ) :=
  finite_level_fiber_bound p π hp hm
    (fun x hx => ((mem_finite_dyadic_level p n x).mp hx).1)
    (fun x hx => ((mem_finite_dyadic_level p n x).mp hx).2.le) hmass hfiber

noncomputable def finiteDyadicApprox {X : Type*} [Fintype X]
    (p : X → ℝ) (I : Finset ℕ) (x : X) : ℝ := by
  classical
  exact ∑ n ∈ I, if x ∈ finiteDyadicLevel p n then dyadicLevelWeight n else 0

theorem finite_dyadic_approx_eq_weight {X : Type*} [Fintype X]
    (p : X → ℝ) {I : Finset ℕ} {n : ℕ} {x : X}
    (hn : n ∈ I) (hx : x ∈ finiteDyadicLevel p n) : finiteDyadicApprox p I x = dyadicLevelWeight n := by
  classical
  unfold finiteDyadicApprox
  rw [Finset.sum_eq_single n]
  · simp only [hx, if_true]
  · intro k hk hkn
    have hnot : x ∉ finiteDyadicLevel p k := by
      intro hxk
      exact (Finset.disjoint_left.mp (finite_dyadic_level_disjoint p hkn)) hxk hx
    simp only [hnot, if_false]
  · exact fun h => (h hn).elim

theorem finite_dyadic_approx_nonneg {X : Type*} [Fintype X]
    (p : X → ℝ) (I : Finset ℕ) (x : X) : 0 ≤ finiteDyadicApprox p I x := by
  classical
  unfold finiteDyadicApprox
  apply Finset.sum_nonneg
  intro n hn
  split_ifs
  · exact (dyadic_level_weight_pos n).le
  · exact le_rfl

theorem finite_dyadic_approx_le {X : Type*} [Fintype X]
    (p : X → ℝ) (I : Finset ℕ) (hp : ∀ x, 0 ≤ p x) (x : X) : finiteDyadicApprox p I x ≤ p x := by
  classical
  by_cases hx : ∃ n ∈ I, x ∈ finiteDyadicLevel p n
  · obtain ⟨n, hn, hxn⟩ := hx
    rw [finite_dyadic_approx_eq_weight p hn hxn]
    exact ((mem_finite_dyadic_level p n x).mp hxn).1
  · have hzero : finiteDyadicApprox p I x = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      have hnot : x ∉ finiteDyadicLevel p n := fun hxn => hx ⟨n, hn, hxn⟩
      simp only [hnot, if_false]
    rw [hzero]
    exact hp x

theorem finite_dyadic_approx_dominates {X : Type*} [Fintype X] [DecidableEq X]
    (p : X → ℝ) (I : Finset ℕ) {x : X} (hx : x ∈ I.biUnion (finiteDyadicLevel p)) :
    p x ≤ 2 * finiteDyadicApprox p I x := by
  obtain ⟨n, hn, hxn⟩ := Finset.mem_biUnion.mp hx
  rw [finite_dyadic_approx_eq_weight p hn hxn]
  exact ((mem_finite_dyadic_level p n x).mp hxn).2.le

theorem finite_dyadic_approx_sum {X : Type*} [Fintype X]
    (p : X → ℝ) (I : Finset ℕ) :
    (∑ x : X, finiteDyadicApprox p I x) = ∑ n ∈ I, dyadicLevelWeight n * ((finiteDyadicLevel p n).card : ℝ) := by
  classical
  unfold finiteDyadicApprox
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  simp [← Finset.sum_filter, mul_comm]

theorem finite_dyadic_union_mass {X : Type*} [Fintype X] [DecidableEq X]
    (p : X → ℝ) (I : Finset ℕ) :
    (∑ x ∈ I.biUnion (finiteDyadicLevel p), p x) = ∑ n ∈ I, ∑ x ∈ finiteDyadicLevel p n, p x := by
  apply Finset.sum_biUnion
  intro m hm n hn hmn
  exact finite_dyadic_level_disjoint p hmn

theorem cyclic_dyadic_combination_norm {q : ℕ} [NeZero q]
    (p : ZMod q → ℝ) (I : Finset ℕ) (x : ZMod q) :
    ‖cyclicSetCombination I dyadicLevelWeight (finiteDyadicLevel p) x‖ = finiteDyadicApprox p I x := by
  classical
  rw [cyclic_set_combination_norm _ _ _ (fun n _ => (dyadic_level_weight_pos n).le)]
  simp only [cyclic_set_indicator_norm, mul_ite, mul_one, mul_zero, finiteDyadicApprox]
  apply Finset.sum_congr rfl
  intro n hn
  split_ifs <;> rfl

/-- Retain high-weight levels with significant mass. The remaining points
split into a part of small total mass and a part of uniformly small weight. -/
theorem exists_finite_dyadic_level_decomposition {X : Type*} [Fintype X] [DecidableEq X]
    (p : X → ℝ) (N : ℕ) {v m : ℝ} (hp : ∀ x, 0 ≤ p x) (hp1 : ∀ x, p x ≤ 1)
    (hm : 0 < m) (hNv : dyadicLevelWeight N ≤ v) :
    ∃ I : Finset ℕ, ∃ G S : Finset X,
      I.card ≤ N + 1 ∧ G = I.biUnion (finiteDyadicLevel p) ∧ Disjoint G S ∧
      (∀ n ∈ I, (finiteDyadicLevel p n).Nonempty ∧ v < dyadicLevelWeight n ∧
        m ≤ ∑ x ∈ finiteDyadicLevel p n, p x) ∧
      (∑ x ∈ S, p x) ≤ (N + 1 : ℕ) * m ∧
      (∀ x : X, x ∉ G → x ∉ S → p x ≤ 2 * v) := by
  classical
  let I := (Finset.range (N + 1)).filter (fun n => v < dyadicLevelWeight n ∧ m ≤ ∑ x ∈ finiteDyadicLevel p n, p x)
  let K := (Finset.range (N + 1)).filter (fun n => v < dyadicLevelWeight n ∧ (∑ x ∈ finiteDyadicLevel p n, p x) < m)
  let G := I.biUnion (finiteDyadicLevel p)
  let S := K.biUnion (finiteDyadicLevel p)
  have hI : I.card ≤ N + 1 := (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)
  have hK : K.card ≤ N + 1 := (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)
  refine ⟨I, G, S, hI, rfl, ?_, ?_, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro x hxG hxS
    obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.mp hxG
    obtain ⟨k, hk, hxk⟩ := Finset.mem_biUnion.mp hxS
    have hik : i ≠ k := by
      intro heq
      subst k
      exact (not_lt_of_ge (Finset.mem_filter.mp hi).2.2) (Finset.mem_filter.mp hk).2.2
    exact (Finset.disjoint_left.mp (finite_dyadic_level_disjoint p hik)) hxi hxk
  · intro n hn
    have hgood := (Finset.mem_filter.mp hn).2
    refine ⟨?_, hgood⟩
    by_contra h
    have he : finiteDyadicLevel p n = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp only [he, Finset.sum_empty] at hgood
    exact (not_le_of_gt hm) hgood.2
  · rw [finite_dyadic_union_mass]
    calc
      _ ≤ ∑ _n ∈ K, m := Finset.sum_le_sum (fun n hn => (Finset.mem_filter.mp hn).2.2.le)
      _ = (K.card : ℝ) * m := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hK) hm.le
  · intro x hxG hxS
    by_contra hx
    have hxv : 2 * v < p x := lt_of_not_ge hx
    have hv : 0 < v := (dyadic_level_weight_pos N).trans_le hNv
    have hxN : dyadicLevelWeight N ≤ p x := by linarith only [hNv, hxv, hv]
    obtain ⟨n, hn, hxn⟩ := exists_finite_dyadic_level p N hxN (hp1 x)
    have hnrange : n ∈ Finset.range (N + 1) := Finset.mem_range.mpr (by omega)
    have hnv : v < dyadicLevelWeight n := by
      have hh := ((mem_finite_dyadic_level p n x).mp hxn).2
      linarith only [hh, hxv]
    by_cases hmass : m ≤ ∑ x ∈ finiteDyadicLevel p n, p x
    · exact hxG (Finset.mem_biUnion.mpr ⟨n, Finset.mem_filter.mpr ⟨hnrange, hnv, hmass⟩, hxn⟩)
    · exact hxS (Finset.mem_biUnion.mpr ⟨n, Finset.mem_filter.mpr ⟨hnrange, hnv, lt_of_not_ge hmass⟩, hxn⟩)

theorem norm_five_sum_sq_le (a b c d e : ℂ) :
    ‖a + b + c + d + e‖ ^ 2 ≤ 5 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2 + ‖d‖ ^ 2 + ‖e‖ ^ 2) := by
  have hh := norm_sum_sq_le_card_mul_sum_sq (Finset.univ : Finset (Fin 5)) ![a, b, c, d, e]
  simpa [Fin.sum_univ_succ, add_assoc] using hh

theorem cyclic_unit_convolution_decomposition {q : ℕ} [NeZero q]
    (f g l s : ZMod q → ℂ) (u : (ZMod q)ˣ)
    (hdecomp : ∀ x, f x = g x + l x + s x) (x : ZMod q) :
    cyclicConvolution f (cyclicUnitDilate f u) x =
      cyclicConvolution g (cyclicUnitDilate g u) x +
      cyclicConvolution l (cyclicUnitDilate f u) x +
      cyclicConvolution s (cyclicUnitDilate f u) x +
      cyclicConvolution g (cyclicUnitDilate l u) x +
      cyclicConvolution g (cyclicUnitDilate s u) x := by
  unfold cyclicConvolution cyclicUnitDilate
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y hy
  rw [hdecomp y, hdecomp (((u⁻¹ : (ZMod q)ˣ) : ZMod q) * (x - y))]
  ring

theorem cyclic_unit_convolution_error_bound {q : ℕ} [NeZero q]
    (f g l s : ZMod q → ℂ) (u : (ZMod q)ˣ) {v m : ℝ}
    (hdecomp : ∀ x, f x = g x + l x + s x)
    (hfmass : (∑ x : ZMod q, ‖f x‖) ≤ 1) (hgmass : (∑ x : ZMod q, ‖g x‖) ≤ 1)
    (hgener : (∑ x : ZMod q, ‖g x‖ ^ 2) ≤ ∑ x : ZMod q, ‖f x‖ ^ 2)
    (hlener : (∑ x : ZMod q, ‖l x‖ ^ 2) ≤ v)
    (hsmass : (∑ x : ZMod q, ‖s x‖) ≤ m) (hm : 0 ≤ m) :
    (∑ x : ZMod q, ‖cyclicConvolution f (cyclicUnitDilate f u) x‖ ^ 2) ≤
      5 * (∑ x : ZMod q, ‖cyclicConvolution g (cyclicUnitDilate g u) x‖ ^ 2) +
        10 * v + 10 * m ^ 2 * ∑ x : ZMod q, ‖f x‖ ^ 2 := by
  have hfmass2 : (∑ x : ZMod q, ‖f x‖) ^ 2 ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hfmass 2
  have hgmass2 : (∑ x : ZMod q, ‖g x‖) ^ 2 ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hgmass 2
  have hsmass2 : (∑ x : ZMod q, ‖s x‖) ^ 2 ≤ m ^ 2 :=
    pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hsmass 2
  have hlf : (∑ x : ZMod q, ‖cyclicConvolution l (cyclicUnitDilate f u) x‖ ^ 2) ≤ v := by
    calc
      _ ≤ (∑ x : ZMod q, ‖cyclicUnitDilate f u x‖) ^ 2 * ∑ x : ZMod q, ‖l x‖ ^ 2 :=
        cyclic_convolution_young_sq_right _ _
      _ = (∑ x : ZMod q, ‖f x‖) ^ 2 * ∑ x : ZMod q, ‖l x‖ ^ 2 := by rw [cyclic_unit_dilate_sum_norm]
      _ ≤ 1 * ∑ x : ZMod q, ‖l x‖ ^ 2 := mul_le_mul_of_nonneg_right hfmass2 (by positivity)
      _ ≤ _ := by simpa only [one_mul] using hlener
  have hsf : (∑ x : ZMod q, ‖cyclicConvolution s (cyclicUnitDilate f u) x‖ ^ 2) ≤
      m ^ 2 * ∑ x : ZMod q, ‖f x‖ ^ 2 := by
    calc
      _ ≤ (∑ x : ZMod q, ‖s x‖) ^ 2 * ∑ x : ZMod q, ‖cyclicUnitDilate f u x‖ ^ 2 :=
        cyclic_convolution_young_sq _ _
      _ = (∑ x : ZMod q, ‖s x‖) ^ 2 * ∑ x : ZMod q, ‖f x‖ ^ 2 := by rw [cyclic_unit_dilate_sq_norm]
      _ ≤ _ := mul_le_mul_of_nonneg_right hsmass2 (by positivity)
  have hgl : (∑ x : ZMod q, ‖cyclicConvolution g (cyclicUnitDilate l u) x‖ ^ 2) ≤ v := by
    calc
      _ ≤ (∑ x : ZMod q, ‖g x‖) ^ 2 * ∑ x : ZMod q, ‖cyclicUnitDilate l u x‖ ^ 2 :=
        cyclic_convolution_young_sq _ _
      _ = (∑ x : ZMod q, ‖g x‖) ^ 2 * ∑ x : ZMod q, ‖l x‖ ^ 2 := by rw [cyclic_unit_dilate_sq_norm]
      _ ≤ 1 * ∑ x : ZMod q, ‖l x‖ ^ 2 := mul_le_mul_of_nonneg_right hgmass2 (by positivity)
      _ ≤ _ := by simpa only [one_mul] using hlener
  have hgs : (∑ x : ZMod q, ‖cyclicConvolution g (cyclicUnitDilate s u) x‖ ^ 2) ≤
      m ^ 2 * ∑ x : ZMod q, ‖f x‖ ^ 2 := by
    calc
      _ ≤ (∑ x : ZMod q, ‖cyclicUnitDilate s u x‖) ^ 2 * ∑ x : ZMod q, ‖g x‖ ^ 2 :=
        cyclic_convolution_young_sq_right _ _
      _ = (∑ x : ZMod q, ‖s x‖) ^ 2 * ∑ x : ZMod q, ‖g x‖ ^ 2 := by rw [cyclic_unit_dilate_sum_norm]
      _ ≤ _ := mul_le_mul hsmass2 hgener (by positivity) (sq_nonneg _)
  calc
    _ ≤ ∑ x : ZMod q, 5 * (
        ‖cyclicConvolution g (cyclicUnitDilate g u) x‖ ^ 2 +
        ‖cyclicConvolution l (cyclicUnitDilate f u) x‖ ^ 2 +
        ‖cyclicConvolution s (cyclicUnitDilate f u) x‖ ^ 2 +
        ‖cyclicConvolution g (cyclicUnitDilate l u) x‖ ^ 2 +
        ‖cyclicConvolution g (cyclicUnitDilate s u) x‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro x hx
      rw [cyclic_unit_convolution_decomposition f g l s u hdecomp]
      exact norm_five_sum_sq_le _ _ _ _ _
    _ = 5 * ((∑ x : ZMod q, ‖cyclicConvolution g (cyclicUnitDilate g u) x‖ ^ 2) +
        (∑ x : ZMod q, ‖cyclicConvolution l (cyclicUnitDilate f u) x‖ ^ 2) +
        (∑ x : ZMod q, ‖cyclicConvolution s (cyclicUnitDilate f u) x‖ ^ 2) +
        (∑ x : ZMod q, ‖cyclicConvolution g (cyclicUnitDilate l u) x‖ ^ 2) +
        ∑ x : ZMod q, ‖cyclicConvolution g (cyclicUnitDilate s u) x‖ ^ 2) := by
      rw [← Finset.mul_sum]
      simp only [Finset.sum_add_distrib]
    _ ≤ _ := by linarith only [hlf, hsf, hgl, hgs]

theorem cyclic_unit_energy_dominated {q : ℕ} [NeZero q]
    (f F : ZMod q → ℂ) (u : (ZMod q)ˣ) {c : ℝ} (hc : 0 ≤ c)
    (hF : ∀ x, F x = (‖F x‖ : ℂ)) (hf : ∀ x, ‖f x‖ ≤ c * ‖F x‖) :
    (∑ x : ZMod q, ‖cyclicConvolution f (cyclicUnitDilate f u) x‖ ^ 2) ≤
      c ^ 4 * ∑ x : ZMod q, ‖cyclicConvolution F (cyclicUnitDilate F u) x‖ ^ 2 := by
  have hpoint : ∀ x : ZMod q, ‖cyclicConvolution f (cyclicUnitDilate f u) x‖ ≤
      c ^ 2 * ‖cyclicConvolution F (cyclicUnitDilate F u) x‖ := by
    intro x
    rw [cyclic_convolution_norm_of_nonnegative F (cyclicUnitDilate F u) hF
      (fun y => hF (((u⁻¹ : (ZMod q)ˣ) : ZMod q) * y))]
    calc
      _ ≤ ∑ y : ZMod q, ‖f y‖ * ‖cyclicUnitDilate f u (x - y)‖ := by
        simpa only [cyclicConvolution, norm_mul] using
          norm_sum_le Finset.univ (fun y => f y * cyclicUnitDilate f u (x - y))
      _ ≤ ∑ y : ZMod q, (c * ‖F y‖) * (c * ‖cyclicUnitDilate F u (x - y)‖) :=
        Finset.sum_le_sum (fun y _ => mul_le_mul (hf y) (hf _) (norm_nonneg _) (by positivity))
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y hy
        ring
  calc
    _ ≤ ∑ x : ZMod q, (c ^ 2 * ‖cyclicConvolution F (cyclicUnitDilate F u) x‖) ^ 2 :=
      Finset.sum_le_sum (fun x _ => pow_le_pow_left₀ (norm_nonneg _) (hpoint x) 2)
    _ = _ := by simp only [mul_pow, ← pow_mul, show (2 : ℕ) * 2 = 4 from rfl, Finset.mul_sum]

/-- A fixed exponential bound absorbs the number of dyadic levels. -/
theorem exists_dyadic_linear_count_bound {η : ℝ} (hη : 0 < η) :
    ∃ J₀ : ℕ, ∀ J : ℕ, J₀ ≤ J → ((2 * J + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (η * (J : ℝ)) := by
  let b := (2 : ℝ) ^ (η / 2)
  have hb : 1 < b := Real.one_lt_rpow (by norm_num) (by positivity)
  let d := b - 1
  have hd : 0 < d := sub_pos.mpr hb
  obtain ⟨J₀, hJ₀⟩ := exists_nat_ge (2 / d ^ 2)
  refine ⟨J₀, ?_⟩
  intro J hJ
  have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg _
  have hJr : (J₀ : ℝ) ≤ (J : ℝ) := by exact_mod_cast hJ
  have hbound : 2 ≤ (J : ℝ) * d ^ 2 := (div_le_iff₀ (sq_pos_of_pos hd)).mp (hJ₀.trans hJr)
  have hquad : 2 * (J : ℝ) ≤ ((J : ℝ) * d) ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hbound hJ0
    nlinarith only [hh]
  have hbern : 1 + (J : ℝ) * d ≤ b ^ J := by
    have hh := one_add_mul_le_pow (show -2 ≤ d by linarith only [hd]) J
    simpa only [d, add_sub_cancel] using hh
  calc
    _ ≤ (1 + (J : ℝ) * d) ^ 2 := by
      push_cast
      nlinarith only [hquad, mul_nonneg hJ0 hd.le]
    _ ≤ (b ^ J) ^ 2 := pow_le_pow_left₀ (by positivity) hbern 2
    _ = _ := by
      dsimp only [b]
      rw [← Real.rpow_mul_natCast (by norm_num), ← Real.rpow_mul_natCast (by norm_num)]
      congr 1
      norm_num
      ring

noncomputable def finiteRealRestriction {X : Type*} [DecidableEq X]
    (p : X → ℝ) (A : Finset X) (x : X) : ℂ := if x ∈ A then (p x : ℂ) else 0

theorem finite_real_restriction_norm {X : Type*} [DecidableEq X]
    (p : X → ℝ) (A : Finset X) (hp : ∀ x, 0 ≤ p x) (x : X) :
    ‖finiteRealRestriction p A x‖ = if x ∈ A then p x else 0 := by
  by_cases hx : x ∈ A <;>
    simp [finiteRealRestriction, hx, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hp x)]

theorem finite_real_restriction_norm_le {X : Type*} [DecidableEq X]
    (p : X → ℝ) (A : Finset X) (hp : ∀ x, 0 ≤ p x) (x : X) :
    ‖finiteRealRestriction p A x‖ ≤ p x := by
  rw [finite_real_restriction_norm p A hp]
  split_ifs
  · exact le_rfl
  · exact hp x

theorem finite_real_restriction_mass {X : Type*} [Fintype X] [DecidableEq X]
    (p : X → ℝ) (A : Finset X) (hp : ∀ x, 0 ≤ p x) :
    (∑ x : X, ‖finiteRealRestriction p A x‖) = ∑ x ∈ A, p x := by
  simp only [finite_real_restriction_norm p A hp, ← Finset.sum_filter,
    Finset.filter_mem_eq_inter, Finset.univ_inter]

theorem finite_real_restriction_mass_le {X : Type*} [Fintype X] [DecidableEq X]
    (p : X → ℝ) (A : Finset X) (hp : ∀ x, 0 ≤ p x) :
    (∑ x : X, ‖finiteRealRestriction p A x‖) ≤ ∑ x : X, p x :=
  Finset.sum_le_sum (fun x _ => finite_real_restriction_norm_le p A hp x)

theorem finite_real_restriction_energy_le {X : Type*} [Fintype X] [DecidableEq X]
    (p : X → ℝ) (A : Finset X) (hp : ∀ x, 0 ≤ p x) :
    (∑ x : X, ‖finiteRealRestriction p A x‖ ^ 2) ≤ ∑ x : X, p x ^ 2 :=
  Finset.sum_le_sum (fun x _ => pow_le_pow_left₀ (norm_nonneg _) (finite_real_restriction_norm_le p A hp x) 2)

theorem finite_real_restriction_energy_of_peak {X : Type*} [Fintype X] [DecidableEq X]
    (p : X → ℝ) (A : Finset X) {M : ℝ} (hp : ∀ x, 0 ≤ p x) (hM : 0 ≤ M)
    (hmass : (∑ x : X, p x) ≤ 1) (hpeak : ∀ x ∈ A, p x ≤ M) :
    (∑ x : X, ‖finiteRealRestriction p A x‖ ^ 2) ≤ M := by
  have hh : ∀ x : X, ‖finiteRealRestriction p A x‖ ≤ M := by
    intro x
    rw [finite_real_restriction_norm p A hp]
    split_ifs with hx
    · exact hpeak x hx
    · exact hM
  calc
    _ ≤ ∑ x : X, M * ‖finiteRealRestriction p A x‖ := by
      apply Finset.sum_le_sum
      intro x hx
      simpa only [pow_two] using mul_le_mul_of_nonneg_right (hh x) (norm_nonneg _)
    _ = M * ∑ x : X, ‖finiteRealRestriction p A x‖ := (Finset.mul_sum _ _ _).symm
    _ ≤ M * 1 := mul_le_mul_of_nonneg_left ((finite_real_restriction_mass_le p A hp).trans hmass) hM
    _ = _ := mul_one _

theorem finite_real_restriction_three_parts {X : Type*} [Fintype X] [DecidableEq X]
    (p : X → ℝ) {G S : Finset X} (hGS : Disjoint G S) (x : X) :
    (p x : ℂ) = finiteRealRestriction p G x + finiteRealRestriction p ((G ∪ S)ᶜ) x +
      finiteRealRestriction p S x := by
  by_cases hxG : x ∈ G
  · have hxS : x ∉ S := fun hxS => (Finset.disjoint_left.mp hGS) hxG hxS
    simp [finiteRealRestriction, hxG, hxS]
  · by_cases hxS : x ∈ S <;> simp [finiteRealRestriction, hxG, hxS]


def DyadicProbabilityNonconcentration {J : ℕ} (γ ε : ℝ) (p : ZMod (2 ^ J) → ℝ) : Prop :=
  ∀ L : ℕ, L ≤ J → ε * (J : ℝ) < (L : ℝ) → ∀ r : ZMod (2 ^ L),
    (∑ x ∈ Finset.univ.filter (fun x : ZMod (2 ^ J) => (x.val : ZMod (2 ^ L)) = r), p x) ≤
      (2 : ℝ) ^ (-γ * (L : ℝ))

/-- Averaged additive flattening for an arbitrary nonnegative law whose
squared norm remains above the density threshold. -/
theorem exists_dyadic_probability_flattening {γ δ : ℝ}
    (hγ : 0 < γ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ τ ε : ℝ, 0 < τ ∧ 0 < ε ∧ ε ≤ 1 / 4 ∧ ∃ J₀ : ℕ,
      ∀ J : ℕ, J₀ ≤ J → ∀ p : ZMod (2 ^ J) → ℝ, ∀ T : Finset (ZMod (2 ^ J))ˣ,
        (∀ x, 0 ≤ p x) → (∑ x : ZMod (2 ^ J), p x) ≤ 1 →
        (2 : ℝ) ^ (-(1 - δ) * (J : ℝ)) ≤ (∑ x : ZMod (2 ^ J), p x ^ 2) →
        DyadicProbabilityNonconcentration γ ε p → T.Nonempty → DyadicUnitSetNonconcentration γ ε T →
        (∑ u ∈ T, ∑ x : ZMod (2 ^ J),
          ‖cyclicConvolution (fun y => (p y : ℂ)) (cyclicUnitDilate (fun y => (p y : ℂ)) u) x‖ ^ 2) ≤
          (2 : ℝ) ^ (-τ * (J : ℝ)) * (T.card : ℝ) * ∑ x : ZMod (2 ^ J), p x ^ 2 := by
  classical
  obtain ⟨a, ε, ha, hε, hε4, J₀, hflat⟩ := exists_dyadic_set_combination_flattening (X := ℕ)
    (show 0 < γ / 2 by positivity) (show 0 < δ / 2 by positivity) (by linarith only [hδ1])
  let η := γ * ε / 8
  have hη : 0 < η := by dsimp only [η]; positivity
  let b := min a (min (δ / 2) η)
  have hb : 0 < b := lt_min ha (lt_min (by positivity) hη)
  have hba : b ≤ a := min_le_left _ _
  have hbδ : b ≤ δ / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hbη : b ≤ η := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨J₁, hJ₁⟩ := exists_dyadic_linear_count_bound ha
  obtain ⟨J₂, hJ₂⟩ := exists_dyadic_linear_count_bound (show 0 < η / 2 by positivity)
  obtain ⟨J₃, hJ₃⟩ := exists_dyadic_fixed_power_absorption 1 0 (τ := 0) (ξ := η) (by simpa using hη)
  obtain ⟨J₄, hJ₄⟩ := exists_dyadic_fixed_power_absorption 7 0 (τ := 0) (ξ := b / 2)
    (by simpa using (show 0 < b / 2 by positivity))
  refine ⟨b / 2, ε, by positivity, hε, hε4, max J₀ (max J₁ (max J₂ (max J₃ J₄))), ?_⟩
  intro J hJ p T hp hmass hnorm hspread hT hTspread
  have hj₀ : J₀ ≤ J := (le_max_left _ _).trans hJ
  have hj₁ : J₁ ≤ J := (le_max_left _ _).trans ((le_max_right _ _).trans hJ)
  have hj₂ : J₂ ≤ J := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hJ))
  have hj₃ : J₃ ≤ J := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hJ)))
  have hj₄ : J₄ ≤ J := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hJ)))
  have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg _
  have hp1 : ∀ x, p x ≤ 1 := fun x =>
    (Finset.single_le_sum (fun y _ => hp y) (Finset.mem_univ x)).trans hmass
  let v := (2 : ℝ) ^ (-(1 - δ / 2) * (J : ℝ))
  let m := (2 : ℝ) ^ (-η * (J : ℝ))
  let z := (2 : ℝ) ^ (-(η / 2) * (J : ℝ))
  let H := ∑ x : ZMod (2 ^ J), p x ^ 2
  have hv : 0 < v := by positivity
  have hm : 0 < m := by positivity
  have hz : 0 ≤ z := by positivity
  have hH : 0 ≤ H := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hNv : dyadicLevelWeight (2 * J) ≤ v := by
    rw [dyadic_level_weight_rpow]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    nlinarith only [hJ0, mul_nonneg hδ.le hJ0]
  obtain ⟨I, G, S, hI, hG, hGS, hlevels, hS, hlow⟩ :=
    exists_finite_dyadic_level_decomposition p (2 * J) hp hp1 hm hNv
  let A := finiteDyadicLevel p
  let F := cyclicSetCombination I dyadicLevelWeight A
  let f := fun x => (p x : ℂ)
  let g := finiteRealRestriction p G
  let l := finiteRealRestriction p ((G ∪ S)ᶜ)
  let s := finiteRealRestriction p S
  have hfnorm : ∀ x, ‖f x‖ = p x := fun x => Complex.norm_of_nonneg (hp x)
  have hfmass : (∑ x : ZMod (2 ^ J), ‖f x‖) ≤ 1 := by simpa only [hfnorm] using hmass
  have hfenergy : (∑ x : ZMod (2 ^ J), ‖f x‖ ^ 2) = H := by simp only [hfnorm, H]
  have hIcap : (I.card : ℝ) ≤ (2 : ℝ) ^ (a * (J : ℝ)) :=
    (show (I.card : ℝ) ≤ ((2 * J + 1 : ℕ) : ℝ) by exact_mod_cast hI).trans (hJ₁ J hj₁)
  have hsmass : (∑ x : ZMod (2 ^ J), ‖s x‖) ≤ z := by
    rw [finite_real_restriction_mass p S hp]
    calc
      _ ≤ ((2 * J + 1 : ℕ) : ℝ) * m := hS
      _ ≤ (2 : ℝ) ^ ((η / 2) * (J : ℝ)) * (2 : ℝ) ^ (-η * (J : ℝ)) :=
        mul_le_mul_of_nonneg_right (hJ₂ J hj₂) hm.le
      _ = _ := by
        rw [← Real.rpow_add (by norm_num)]
        congr 1
        ring
  have h2η : (2 : ℝ) ≤ (2 : ℝ) ^ (η * (J : ℝ)) := by simpa using hJ₃ J hj₃
  have hloss : ∀ L : ℕ, ε * (J : ℝ) < (L : ℝ) →
      2 * (2 : ℝ) ^ (-γ * (L : ℝ)) / m ≤ (2 : ℝ) ^ (-(γ / 2) * (L : ℝ)) := by
    intro L hL
    apply (div_le_iff₀ hm).mpr
    calc
      _ ≤ (2 : ℝ) ^ (η * (J : ℝ)) * (2 : ℝ) ^ (-γ * (L : ℝ)) := by gcongr
      _ = (2 : ℝ) ^ (η * (J : ℝ) - γ * (L : ℝ)) := by
        rw [← Real.rpow_add (by norm_num)]; congr 1; ring
      _ ≤ (2 : ℝ) ^ (-(γ / 2) * (L : ℝ) - η * (J : ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        dsimp only [η]
        nlinarith only [mul_lt_mul_of_pos_left hL hγ, mul_nonneg hγ.le (Nat.cast_nonneg L : (0 : ℝ) ≤ L)]
      _ = _ := by
        dsimp only [m]
        rw [← Real.rpow_add (by norm_num)]
        congr 1
        ring
  have hA : ∀ n ∈ I, (A n).Nonempty ∧
      ((A n).card : ℝ) ≤ (2 : ℝ) ^ ((1 - δ / 2) * (J : ℝ)) ∧
      DyadicRingSetNonconcentration (γ / 2) ε (A n) := by
    intro n hn
    obtain ⟨hnonempty, hnweight, hnmass⟩ := hlevels n hn
    refine ⟨hnonempty, ?_, ?_⟩
    · have hcard := finite_level_card_bound p hp hmass
        (fun x hx => ((mem_finite_dyadic_level p n x).mp hx).1)
      have hvc : v * ((A n).card : ℝ) ≤ 1 :=
        (mul_le_mul_of_nonneg_right hnweight.le (Nat.cast_nonneg _)).trans hcard
      apply (mul_le_mul_iff_of_pos_left hv).mp
      calc
        _ ≤ 1 := hvc
        _ = _ := by
          dsimp only [v]
          rw [← Real.rpow_add (by norm_num),
            show -(1 - δ / 2) * (J : ℝ) + (1 - δ / 2) * (J : ℝ) = 0 by ring, Real.rpow_zero]
    · intro L hL hεL r
      have hh := finite_dyadic_level_fiber_bound p (fun x => (x.val : ZMod (2 ^ L))) n
        hp hm hnmass (hspread L hL hεL) r
      exact hh.trans (mul_le_mul_of_nonneg_right (hloss L hεL) (Nat.cast_nonneg _))
  have hTspread' : DyadicUnitSetNonconcentration (γ / 2) ε T := by
    intro L hL hεL r
    apply (hTspread L hL hεL r).trans
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    nlinarith only [mul_nonneg hγ.le (Nat.cast_nonneg L : (0 : ℝ) ≤ L)]
  have hFmass : (∑ n ∈ I, dyadicLevelWeight n * ((A n).card : ℝ)) ≤ 1 := by
    rw [← finite_dyadic_approx_sum p I]
    exact (Finset.sum_le_sum (fun x _ => finite_dyadic_approx_le p I hp x)).trans hmass
  have hFenergy : (∑ x : ZMod (2 ^ J), ‖F x‖ ^ 2) ≤ H := by
    apply Finset.sum_le_sum
    intro x hx
    rw [cyclic_dyadic_combination_norm]
    exact pow_le_pow_left₀ (finite_dyadic_approx_nonneg p I x) (finite_dyadic_approx_le p I hp x) 2
  have hFflat := hflat J hj₀ I dyadicLevelWeight A T (fun n _ => (dyadic_level_weight_pos n).le)
    hT hIcap hFmass hA hTspread'
  have hFnonneg : ∀ x, F x = (‖F x‖ : ℂ) :=
    cyclic_set_combination_nonnegative I dyadicLevelWeight A (fun n _ => (dyadic_level_weight_pos n).le)
  have hgdom : ∀ x, ‖g x‖ ≤ 2 * ‖F x‖ := by
    intro x
    rw [finite_real_restriction_norm p G hp]
    by_cases hx : x ∈ G
    · rw [if_pos hx, cyclic_dyadic_combination_norm]
      exact finite_dyadic_approx_dominates p I (by rwa [← hG])
    · rw [if_neg hx]
      positivity
  have hgavg : (∑ u ∈ T, ∑ x : ZMod (2 ^ J), ‖cyclicConvolution g (cyclicUnitDilate g u) x‖ ^ 2) ≤
      16 * (2 : ℝ) ^ (-a * (J : ℝ)) * (T.card : ℝ) * H := by
    have hFbound : (∑ u ∈ T, ∑ x : ZMod (2 ^ J), ‖cyclicConvolution F (cyclicUnitDilate F u) x‖ ^ 2) ≤
        (2 : ℝ) ^ (-a * (J : ℝ)) * (T.card : ℝ) * H := by
      exact hFflat.trans (mul_le_mul_of_nonneg_left hFenergy
        (show 0 ≤ (2 : ℝ) ^ (-a * (J : ℝ)) * (T.card : ℝ) from mul_nonneg
          (Real.rpow_pos_of_pos (by norm_num) _).le (Nat.cast_nonneg _)))
    calc
      _ ≤ ∑ u ∈ T, (2 : ℝ) ^ (4 : ℕ) * ∑ x : ZMod (2 ^ J), ‖cyclicConvolution F (cyclicUnitDilate F u) x‖ ^ 2 :=
        Finset.sum_le_sum (fun u _ => cyclic_unit_energy_dominated g F u (by norm_num) hFnonneg hgdom)
      _ = 16 * ∑ u ∈ T, ∑ x : ZMod (2 ^ J), ‖cyclicConvolution F (cyclicUnitDilate F u) x‖ ^ 2 := by
        rw [← Finset.mul_sum, show (2 : ℝ) ^ (4 : ℕ) = 16 by norm_num]
      _ ≤ 16 * ((2 : ℝ) ^ (-a * (J : ℝ)) * (T.card : ℝ) * H) :=
        mul_le_mul_of_nonneg_left hFbound (by norm_num)
      _ = _ := by ring
  have hlener : (∑ x : ZMod (2 ^ J), ‖l x‖ ^ 2) ≤ 2 * v := by
    apply finite_real_restriction_energy_of_peak p _ hp (by positivity) hmass
    intro x hx
    have hh : x ∉ G ∧ x ∉ S := by simpa only [Finset.mem_compl, Finset.mem_union, not_or] using hx
    exact hlow x hh.1 hh.2
  have hzsq : z ^ 2 = (2 : ℝ) ^ (-η * (J : ℝ)) := by
    dsimp only [z]
    rw [← Real.rpow_mul_natCast (by norm_num)]
    congr 1
    norm_num
    ring
  have hvrel : v ≤ (2 : ℝ) ^ (-(δ / 2) * (J : ℝ)) * H := by
    calc
      _ = (2 : ℝ) ^ (-(δ / 2) * (J : ℝ)) * (2 : ℝ) ^ (-(1 - δ) * (J : ℝ)) := by
        dsimp only [v]
        rw [← Real.rpow_add (by norm_num)]
        congr 1
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hnorm (by positivity)
  have herr : (∑ u ∈ T, ∑ x : ZMod (2 ^ J), ‖cyclicConvolution f (cyclicUnitDilate f u) x‖ ^ 2) ≤
      (80 * (2 : ℝ) ^ (-a * (J : ℝ)) + 20 * (2 : ℝ) ^ (-(δ / 2) * (J : ℝ)) +
        10 * (2 : ℝ) ^ (-η * (J : ℝ))) * (T.card : ℝ) * H := by
    have hu : ∀ u ∈ T, (∑ x : ZMod (2 ^ J), ‖cyclicConvolution f (cyclicUnitDilate f u) x‖ ^ 2) ≤
        5 * (∑ x : ZMod (2 ^ J), ‖cyclicConvolution g (cyclicUnitDilate g u) x‖ ^ 2) +
          20 * v + 10 * (2 : ℝ) ^ (-η * (J : ℝ)) * H := by
      intro u hu
      have hh := cyclic_unit_convolution_error_bound f g l s u
        (finite_real_restriction_three_parts p hGS) hfmass
        ((finite_real_restriction_mass_le p G hp).trans hmass)
        (by simpa only [hfenergy] using finite_real_restriction_energy_le p G hp)
        hlener hsmass hz
      simpa only [hfenergy, hzsq, show (10 : ℝ) * (2 * v) = 20 * v by ring] using hh
    calc
      _ ≤ ∑ u ∈ T, (5 * (∑ x : ZMod (2 ^ J), ‖cyclicConvolution g (cyclicUnitDilate g u) x‖ ^ 2) +
          20 * v + 10 * (2 : ℝ) ^ (-η * (J : ℝ)) * H) := Finset.sum_le_sum hu
      _ = 5 * (∑ u ∈ T, ∑ x : ZMod (2 ^ J), ‖cyclicConvolution g (cyclicUnitDilate g u) x‖ ^ 2) +
          (T.card : ℝ) * (20 * v + 10 * (2 : ℝ) ^ (-η * (J : ℝ)) * H) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
        simp only [Finset.sum_const, nsmul_eq_mul]
        ring
      _ ≤ 5 * (16 * (2 : ℝ) ^ (-a * (J : ℝ)) * (T.card : ℝ) * H) +
          (T.card : ℝ) * (20 * ((2 : ℝ) ^ (-(δ / 2) * (J : ℝ)) * H) +
            10 * (2 : ℝ) ^ (-η * (J : ℝ)) * H) := by
        apply add_le_add (mul_le_mul_of_nonneg_left hgavg (by norm_num : (0 : ℝ) ≤ 5))
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg T.card : (0 : ℝ) ≤ T.card)
        exact add_le_add (mul_le_mul_of_nonneg_left hvrel (by norm_num : (0 : ℝ) ≤ 20)) le_rfl
      _ = _ := by ring
  have h110 : (110 : ℝ) ≤ (2 : ℝ) ^ ((b / 2) * (J : ℝ)) := by
    have hh := hJ₄ J hj₄
    norm_num at hh
    exact (by norm_num : (110 : ℝ) ≤ 128).trans hh
  have hcoef : 80 * (2 : ℝ) ^ (-a * (J : ℝ)) + 20 * (2 : ℝ) ^ (-(δ / 2) * (J : ℝ)) +
      10 * (2 : ℝ) ^ (-η * (J : ℝ)) ≤ (2 : ℝ) ^ (-(b / 2) * (J : ℝ)) := by
    have hpow : ∀ c : ℝ, b ≤ c → (2 : ℝ) ^ (-c * (J : ℝ)) ≤ (2 : ℝ) ^ (-b * (J : ℝ)) := by
      intro c hc
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have hh := mul_le_mul_of_nonneg_right hc hJ0
      linarith only [hh]
    calc
      _ ≤ 110 * (2 : ℝ) ^ (-b * (J : ℝ)) := by
        linarith only [hpow a hba, hpow (δ / 2) hbδ, hpow η hbη]
      _ ≤ (2 : ℝ) ^ ((b / 2) * (J : ℝ)) * (2 : ℝ) ^ (-b * (J : ℝ)) :=
        mul_le_mul_of_nonneg_right h110 (by positivity)
      _ = _ := by rw [← Real.rpow_add (by norm_num)]; congr 1; ring
  exact herr.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg _)) hH)


theorem finite_dyadic_approx_weighted_sum {X : Type*} [Fintype X]
    (p : X → ℝ) (I : Finset ℕ) (b : X → ℝ) :
    (∑ x : X, finiteDyadicApprox p I x * b x) =
      ∑ n ∈ I, dyadicLevelWeight n * ∑ x ∈ finiteDyadicLevel p n, b x := by
  classical
  simp only [finiteDyadicApprox, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.mul_sum]
  simp only [ite_mul, zero_mul, ← Finset.sum_filter]
  simp

/-- Lift bounds on retained dyadic levels to an average under a nonnegative
law. The two discarded parts are controlled by mass and pointwise size. -/
theorem finite_dyadic_weighted_average {X : Type*} [Fintype X] [DecidableEq X]
    (p b : X → ℝ) (I : Finset ℕ) (G S : Finset X) {C D v H : ℝ}
    (hp : ∀ x, 0 ≤ p x) (hmass : (∑ x : X, p x) ≤ 1)
    (hb : ∀ x, 0 ≤ b x) (hbH : ∀ x, b x ≤ H) (hH : 0 ≤ H)
    (hC : 0 ≤ C) (hv : 0 ≤ v) (hG : G = I.biUnion (finiteDyadicLevel p))
    (hGS : Disjoint G S) (hS : (∑ x ∈ S, p x) ≤ D)
    (hlow : ∀ x, x ∉ G → x ∉ S → p x ≤ v)
    (hlevels : ∀ n ∈ I, (∑ x ∈ finiteDyadicLevel p n, b x) ≤
      C * ((finiteDyadicLevel p n).card : ℝ)) :
    (∑ x : X, p x * b x) ≤ 2 * C + (D + v * Fintype.card X) * H := by
  classical
  have happrox : (∑ x : X, finiteDyadicApprox p I x * b x) ≤ C := by
    rw [finite_dyadic_approx_weighted_sum]
    calc
      _ ≤ ∑ n ∈ I, dyadicLevelWeight n *
          (C * ((finiteDyadicLevel p n).card : ℝ)) :=
        Finset.sum_le_sum (fun n hn => mul_le_mul_of_nonneg_left (hlevels n hn)
          (dyadic_level_weight_pos n).le)
      _ = C * ∑ n ∈ I, dyadicLevelWeight n * ((finiteDyadicLevel p n).card : ℝ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n hn
        ring
      _ ≤ C * 1 := by
        apply mul_le_mul_of_nonneg_left _ hC
        rw [← finite_dyadic_approx_sum]
        exact (Finset.sum_le_sum (fun x _ => finite_dyadic_approx_le p I hp x)).trans hmass
      _ = C := mul_one _
  have hgood : (∑ x ∈ G, p x * b x) ≤ 2 * C := by
    calc
      _ ≤ ∑ x ∈ G, 2 * (finiteDyadicApprox p I x * b x) := by
        apply Finset.sum_le_sum
        intro x hx
        have hh := mul_le_mul_of_nonneg_right
          (finite_dyadic_approx_dominates p I (by rwa [← hG])) (hb x)
        simpa only [mul_assoc] using hh
      _ = 2 * ∑ x ∈ G, finiteDyadicApprox p I x * b x := (Finset.mul_sum _ _ _).symm
      _ ≤ 2 * ∑ x : X, finiteDyadicApprox p I x * b x := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun x _ _ => mul_nonneg (finite_dyadic_approx_nonneg p I x) (hb x))
      _ ≤ 2 * C := mul_le_mul_of_nonneg_left happrox (by norm_num)
  have hsmall : (∑ x ∈ S, p x * b x) ≤ D * H := by
    calc
      _ ≤ ∑ x ∈ S, p x * H := Finset.sum_le_sum (fun x _ =>
        mul_le_mul_of_nonneg_left (hbH x) (hp x))
      _ = (∑ x ∈ S, p x) * H := (Finset.sum_mul _ _ _).symm
      _ ≤ D * H := mul_le_mul_of_nonneg_right hS hH
  have htail : (∑ x ∈ (G ∪ S)ᶜ, p x * b x) ≤ v * Fintype.card X * H := by
    calc
      _ ≤ ∑ _x ∈ (G ∪ S)ᶜ, v * H := by
        apply Finset.sum_le_sum
        intro x hx
        have hnot : x ∉ G ∧ x ∉ S := by
          simpa only [Finset.mem_compl, Finset.mem_union, not_or] using hx
        exact mul_le_mul (hlow x hnot.1 hnot.2) (hbH x) (hb x) hv
      _ = (((G ∪ S)ᶜ).card : ℝ) * (v * H) := by simp
      _ ≤ (Fintype.card X : ℝ) * (v * H) := by
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg hv hH)
        exact_mod_cast Finset.card_le_univ ((G ∪ S)ᶜ)
      _ = _ := by ring
  have hpartition : (∑ x : X, p x * b x) =
      (∑ x ∈ G, p x * b x) + (∑ x ∈ S, p x * b x) +
        ∑ x ∈ (G ∪ S)ᶜ, p x * b x := by
    rw [← Finset.sum_union hGS, Finset.sum_add_sum_compl]
  rw [hpartition]
  calc
    _ ≤ 2 * C + D * H + v * Fintype.card X * H := add_le_add (add_le_add hgood hsmall) htail
    _ = _ := by ring

theorem unit_image_fiber_card {R Q : Type*} [Monoid R] [DecidableEq R]
    (T : Finset Rˣ) (π : R → Q) (r : Q) [DecidableEq Q] :
    ((T.image (fun u : Rˣ => (u : R))).filter (fun a => π a = r)).card =
      (T.filter (fun u : Rˣ => π (u : R) = r)).card := by
  classical
  rw [Finset.filter_image, Finset.card_image_of_injective _ Units.val_injective]

def DyadicUnitProbabilityNonconcentration {J : ℕ} (γ ε : ℝ)
    (w : (ZMod (2 ^ J))ˣ → ℝ) : Prop :=
  ∀ L : ℕ, L ≤ J → ε * (J : ℝ) < (L : ℝ) → ∀ r : ZMod (2 ^ L),
    (∑ u ∈ Finset.univ.filter
      (fun u : (ZMod (2 ^ J))ˣ => (((u : ZMod (2 ^ J)).val : ZMod (2 ^ L))) = r), w u) ≤
        (2 : ℝ) ^ (-γ * (L : ℝ))

theorem cyclic_probability_unit_energy_bound {q : ℕ} [NeZero q]
    (p : ZMod q → ℝ) (hp : ∀ x, 0 ≤ p x) (hmass : (∑ x : ZMod q, p x) ≤ 1)
    (u : (ZMod q)ˣ) :
    (∑ x : ZMod q, ‖cyclicConvolution (fun y => (p y : ℂ))
      (cyclicUnitDilate (fun y => (p y : ℂ)) u) x‖ ^ 2) ≤ ∑ x : ZMod q, p x ^ 2 := by
  have hfnorm : ∀ x : ZMod q, ‖(p x : ℂ)‖ = p x := fun x => Complex.norm_of_nonneg (hp x)
  have hh := cyclic_convolution_young_sq (fun y => (p y : ℂ))
    (cyclicUnitDilate (fun y => (p y : ℂ)) u)
  rw [cyclic_unit_dilate_sq_norm] at hh
  simp only [hfnorm] at hh
  have hsq : (∑ x : ZMod q, p x) ^ 2 ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ (Finset.sum_nonneg (fun x _ => hp x)) hmass 2
  exact hh.trans (by simpa only [one_mul] using
    mul_le_mul_of_nonneg_right hsq (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

/-- Additive flattening with both a nonuniform input law and a nonuniform
law on unit multipliers. All parameters are independent of the two laws. -/
theorem exists_dyadic_weighted_probability_flattening {γ δ : ℝ}
    (hγ : 0 < γ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ τ ε : ℝ, 0 < τ ∧ 0 < ε ∧ ε ≤ 1 / 4 ∧ ∃ J₀ : ℕ,
      ∀ J : ℕ, J₀ ≤ J → ∀ p : ZMod (2 ^ J) → ℝ,
      ∀ w : (ZMod (2 ^ J))ˣ → ℝ,
        (∀ x, 0 ≤ p x) → (∑ x : ZMod (2 ^ J), p x) ≤ 1 →
        (2 : ℝ) ^ (-(1 - δ) * (J : ℝ)) ≤ (∑ x : ZMod (2 ^ J), p x ^ 2) →
        DyadicProbabilityNonconcentration γ ε p →
        (∀ u, 0 ≤ w u) → (∑ u : (ZMod (2 ^ J))ˣ, w u) ≤ 1 →
        DyadicUnitProbabilityNonconcentration γ ε w →
        (∑ u : (ZMod (2 ^ J))ˣ, w u * ∑ x : ZMod (2 ^ J),
          ‖cyclicConvolution (fun y => (p y : ℂ))
            (cyclicUnitDilate (fun y => (p y : ℂ)) u) x‖ ^ 2) ≤
          (2 : ℝ) ^ (-τ * (J : ℝ)) * ∑ x : ZMod (2 ^ J), p x ^ 2 := by
  classical
  obtain ⟨a, ε, ha, hε, hε4, J₀, hflat⟩ := exists_dyadic_probability_flattening
    (show 0 < γ / 2 by positivity) hδ hδ1
  let η := γ * ε / 8
  have hη : 0 < η := by dsimp only [η]; positivity
  let b := min a (min (η / 2) 1)
  have hb : 0 < b := lt_min ha (lt_min (by positivity) (by norm_num))
  have hba : b ≤ a := min_le_left _ _
  have hbη : b ≤ η / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hb1 : b ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨J₁, hJ₁⟩ := exists_dyadic_linear_count_bound (show 0 < η / 2 by positivity)
  obtain ⟨J₂, hJ₂⟩ := exists_dyadic_fixed_power_absorption 1 0
    (τ := 0) (ξ := η) (by simpa using hη)
  obtain ⟨J₃, hJ₃⟩ := exists_dyadic_fixed_power_absorption 3 0
    (τ := 0) (ξ := b / 2) (by simpa using (show 0 < b / 2 by positivity))
  refine ⟨b / 2, ε, by positivity, hε, hε4, max J₀ (max J₁ (max J₂ J₃)), ?_⟩
  intro J hJ p w hp hmass hnorm hspread hw hwmass hwspread
  have hj₀ : J₀ ≤ J := (le_max_left _ _).trans hJ
  have hj₁ : J₁ ≤ J := (le_max_left _ _).trans ((le_max_right _ _).trans hJ)
  have hj₂ : J₂ ≤ J := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hJ))
  have hj₃ : J₃ ≤ J := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hJ))
  have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg _
  have hw1 : ∀ u, w u ≤ 1 := fun u =>
    (Finset.single_le_sum (fun v _ => hw v) (Finset.mem_univ u)).trans hwmass
  let v := (2 : ℝ) ^ (-2 * (J : ℝ))
  let m := (2 : ℝ) ^ (-η * (J : ℝ))
  let H := ∑ x : ZMod (2 ^ J), p x ^ 2
  let E := fun u : (ZMod (2 ^ J))ˣ => ∑ x : ZMod (2 ^ J),
    ‖cyclicConvolution (fun y => (p y : ℂ)) (cyclicUnitDilate (fun y => (p y : ℂ)) u) x‖ ^ 2
  have hv : 0 < v := by positivity
  have hm : 0 < m := by positivity
  have hH : 0 ≤ H := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hNv : dyadicLevelWeight (2 * J) ≤ v := by
    rw [dyadic_level_weight_rpow]
    dsimp only [v]
    norm_num
  obtain ⟨I, G, S, hI, hG, hGS, hlevels, hS, hlow⟩ :=
    exists_finite_dyadic_level_decomposition w (2 * J) hw hw1 hm hNv
  have h2η : (2 : ℝ) ≤ (2 : ℝ) ^ (η * (J : ℝ)) := by simpa using hJ₂ J hj₂
  have hloss : ∀ L : ℕ, ε * (J : ℝ) < (L : ℝ) →
      2 * (2 : ℝ) ^ (-γ * (L : ℝ)) / m ≤ (2 : ℝ) ^ (-(γ / 2) * (L : ℝ)) := by
    intro L hL
    apply (div_le_iff₀ hm).mpr
    calc
      _ ≤ (2 : ℝ) ^ (η * (J : ℝ)) * (2 : ℝ) ^ (-γ * (L : ℝ)) := by gcongr
      _ = (2 : ℝ) ^ (η * (J : ℝ) - γ * (L : ℝ)) := by
        rw [← Real.rpow_add (by norm_num)]; congr 1; ring
      _ ≤ (2 : ℝ) ^ (-(γ / 2) * (L : ℝ) - η * (J : ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        dsimp only [η]
        nlinarith only [mul_lt_mul_of_pos_left hL hγ,
          mul_nonneg hγ.le (Nat.cast_nonneg L : (0 : ℝ) ≤ L)]
      _ = _ := by
        dsimp only [m]
        rw [← Real.rpow_add (by norm_num)]
        congr 1
        ring
  have hlevelspread : ∀ n ∈ I,
      DyadicUnitSetNonconcentration (γ / 2) ε (finiteDyadicLevel w n) := by
    intro n hn L hL hεL r
    rw [unit_image_fiber_card]
    have hh := finite_dyadic_level_fiber_bound w
      (fun u : (ZMod (2 ^ J))ˣ => (((u : ZMod (2 ^ J)).val : ZMod (2 ^ L)))) n
      hw hm (hlevels n hn).2.2 (hwspread L hL hεL) r
    exact hh.trans (mul_le_mul_of_nonneg_right (hloss L hεL) (Nat.cast_nonneg _))
  have hspread' : DyadicProbabilityNonconcentration (γ / 2) ε p := by
    intro L hL hεL r
    apply (hspread L hL hεL r).trans
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    nlinarith only [mul_nonneg hγ.le (Nat.cast_nonneg L : (0 : ℝ) ≤ L)]
  have hsmall : (∑ u ∈ S, w u) ≤ (2 : ℝ) ^ (-(η / 2) * (J : ℝ)) := by
    calc
      _ ≤ ((2 * J + 1 : ℕ) : ℝ) * m := hS
      _ ≤ (2 : ℝ) ^ ((η / 2) * (J : ℝ)) * (2 : ℝ) ^ (-η * (J : ℝ)) :=
        mul_le_mul_of_nonneg_right (hJ₁ J hj₁) hm.le
      _ = _ := by rw [← Real.rpow_add (by norm_num)]; congr 1; ring
  have htail : 2 * v * (Fintype.card (ZMod (2 ^ J))ˣ : ℝ) ≤
      2 * (2 : ℝ) ^ (-(J : ℝ)) := by
    have hcard : Fintype.card (ZMod (2 ^ J))ˣ ≤ 2 ^ J := by
      calc
        _ ≤ Fintype.card (ZMod (2 ^ J)) :=
          Fintype.card_le_of_injective (fun u : (ZMod (2 ^ J))ˣ => (u : ZMod (2 ^ J))) Units.val_injective
        _ = _ := ZMod.card _
    calc
      _ ≤ 2 * v * ((2 ^ J : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hcard) (by positivity)
      _ = _ := by
        dsimp only [v]
        push_cast
        rw [← Real.rpow_natCast, mul_assoc, ← Real.rpow_add (by norm_num)]
        congr 2
        ring
  have hmain : (∑ u : (ZMod (2 ^ J))ˣ, w u * E u) ≤
      (2 * (2 : ℝ) ^ (-a * (J : ℝ)) + (2 : ℝ) ^ (-(η / 2) * (J : ℝ)) +
        2 * (2 : ℝ) ^ (-(J : ℝ))) * H := by
    have hh := finite_dyadic_weighted_average w E I G S hw hwmass
      (fun _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
      (cyclic_probability_unit_energy_bound p hp hmass) hH
      (show 0 ≤ (2 : ℝ) ^ (-a * (J : ℝ)) * H by positivity)
      (show 0 ≤ 2 * v by positivity) hG hGS hsmall hlow (by
        intro n hn
        have hflatn := hflat J hj₀ p (finiteDyadicLevel w n) hp hmass hnorm hspread'
          (hlevels n hn).1 (hlevelspread n hn)
        simpa only [E, H, mul_assoc, mul_left_comm, mul_comm] using hflatn)
    calc
      _ ≤ 2 * ((2 : ℝ) ^ (-a * (J : ℝ)) * H) +
          ((2 : ℝ) ^ (-(η / 2) * (J : ℝ)) + 2 * v * Fintype.card (ZMod (2 ^ J))ˣ) * H := hh
      _ ≤ 2 * ((2 : ℝ) ^ (-a * (J : ℝ)) * H) +
          ((2 : ℝ) ^ (-(η / 2) * (J : ℝ)) + 2 * (2 : ℝ) ^ (-(J : ℝ))) * H := by
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_right (add_le_add le_rfl htail) hH)
      _ = _ := by ring
  have h5 : (5 : ℝ) ≤ (2 : ℝ) ^ ((b / 2) * (J : ℝ)) := by
    have hh := hJ₃ J hj₃
    norm_num at hh
    exact (by norm_num : (5 : ℝ) ≤ 8).trans hh
  have hcoef : 2 * (2 : ℝ) ^ (-a * (J : ℝ)) + (2 : ℝ) ^ (-(η / 2) * (J : ℝ)) +
      2 * (2 : ℝ) ^ (-(J : ℝ)) ≤ (2 : ℝ) ^ (-(b / 2) * (J : ℝ)) := by
    have hpow : ∀ c : ℝ, b ≤ c → (2 : ℝ) ^ (-c * (J : ℝ)) ≤ (2 : ℝ) ^ (-b * (J : ℝ)) := by
      intro c hc
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have hh := mul_le_mul_of_nonneg_right hc hJ0
      linarith only [hh]
    have hpow1 : (2 : ℝ) ^ (-(J : ℝ)) ≤ (2 : ℝ) ^ (-b * (J : ℝ)) := by
      simpa using hpow 1 hb1
    calc
      _ ≤ 5 * (2 : ℝ) ^ (-b * (J : ℝ)) := by
        linarith only [hpow a hba, hpow (η / 2) hbη, hpow1]
      _ ≤ (2 : ℝ) ^ ((b / 2) * (J : ℝ)) * (2 : ℝ) ^ (-b * (J : ℝ)) :=
        mul_le_mul_of_nonneg_right h5 (by positivity)
      _ = _ := by rw [← Real.rpow_add (by norm_num)]; congr 1; ring
  exact hmain.trans (mul_le_mul_of_nonneg_right hcoef hH)



theorem finite_pushforward_equivariant {X Y : Type*} [Fintype X] [DecidableEq Y]
    (p : X → ℝ) (π : X → Y) (e : X ≃ X) (σ : Y ≃ Y)
    (hπ : ∀ x, π (e x) = σ (π x)) (r : Y) :
    finitePushforward (fun x => p (e x)) π r = finitePushforward p π (σ r) := by
  classical
  unfold finitePushforward
  simp only [Finset.sum_filter]
  apply Fintype.sum_equiv e
  intro x
  rw [hπ]
  simp only [Equiv.apply_eq_iff_eq]

theorem finite_pushforward_unit_dilate {R Q : Type*} [Ring R] [Ring Q]
    [Fintype R] [DecidableEq Q] (p : R → ℝ) (π : R →+* Q) (u : Rˣ) (r : Q) :
    finitePushforward (fun x => p ((u : R) * x)) π r =
      finitePushforward p π (π (u : R) * r) := by
  let v : Qˣ := Units.map π.toMonoidHom u
  exact finite_pushforward_equivariant p π (ringUnitMulAddEquiv u).toEquiv
    (ringUnitMulAddEquiv v).toEquiv (fun x => by simp [ringUnitMulAddEquiv, v]) r

theorem finite_pushforward_unit_translate {R Q : Type*} [Ring R] [Ring Q]
    [Fintype Rˣ] [DecidableEq Q] (w : Rˣ → ℝ) (π : R →+* Q) (u : Rˣ) (r : Q) :
    finitePushforward (fun v : Rˣ => w (u * v)) (fun v : Rˣ => π (v : R)) r =
      finitePushforward w (fun v : Rˣ => π (v : R)) (π (u : R) * r) := by
  let v : Qˣ := Units.map π.toMonoidHom u
  exact finite_pushforward_equivariant w (fun z : Rˣ => π (z : R)) (Equiv.mulLeft u)
    (ringUnitMulAddEquiv v).toEquiv (fun x => by simp [ringUnitMulAddEquiv, v]) r

theorem dyadic_probability_nonconcentration_unit_dilate {J : ℕ} {γ ε : ℝ}
    {p : ZMod (2 ^ J) → ℝ} (hp : DyadicProbabilityNonconcentration γ ε p)
    (u : (ZMod (2 ^ J))ˣ) :
    DyadicProbabilityNonconcentration γ ε (fun x => p ((u : ZMod (2 ^ J)) * x)) := by
  intro L hL hεL r
  let π : ZMod (2 ^ J) →+* ZMod (2 ^ L) := ZMod.castHom (pow_dvd_pow 2 hL) _
  have hπ : ∀ x : ZMod (2 ^ J), π x = (x.val : ZMod (2 ^ L)) := by
    intro x
    exact ZMod.cast_eq_val _
  change finitePushforward _ (fun x : ZMod (2 ^ J) => (x.val : ZMod (2 ^ L))) r ≤ _
  simp only [← hπ]
  rw [finite_pushforward_unit_dilate]
  simpa only [finitePushforward, hπ] using hp L hL hεL (π (u : ZMod (2 ^ J)) * r)

theorem dyadic_unit_probability_nonconcentration_translate {J : ℕ} {γ ε : ℝ}
    {w : (ZMod (2 ^ J))ˣ → ℝ} (hw : DyadicUnitProbabilityNonconcentration γ ε w)
    (u : (ZMod (2 ^ J))ˣ) :
    DyadicUnitProbabilityNonconcentration γ ε (fun v => w (u * v)) := by
  intro L hL hεL r
  let π : ZMod (2 ^ J) →+* ZMod (2 ^ L) := ZMod.castHom (pow_dvd_pow 2 hL) _
  have hπ : ∀ x : ZMod (2 ^ J), π x = (x.val : ZMod (2 ^ L)) := by
    intro x
    exact ZMod.cast_eq_val _
  change finitePushforward _ (fun v : (ZMod (2 ^ J))ˣ => ((v : ZMod (2 ^ J)).val : ZMod (2 ^ L))) r ≤ _
  simp only [← hπ]
  rw [finite_pushforward_unit_translate]
  simpa only [finitePushforward, hπ] using hw L hL hεL (π (u : ZMod (2 ^ J)) * r)

theorem finite_pushforward_linear_combination {X Y I : Type*} [Fintype X] [Fintype I]
    [DecidableEq Y] (w : I → ℝ) (F : I → X → ℝ) (π : X → Y) (r : Y) :
    finitePushforward (fun x => ∑ i : I, w i * F i x) π r =
      ∑ i : I, w i * finitePushforward (F i) π r := by
  unfold finitePushforward
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]

theorem cyclic_mixture_norm_of_nonnegative {I : Type*} [Fintype I] {q : ℕ} [NeZero q]
    (w : I → ℝ) (F : I → ZMod q → ℂ) (hw : ∀ i, 0 ≤ w i)
    (hF : ∀ i x, F i x = (‖F i x‖ : ℂ)) (x : ZMod q) :
    ‖cyclicMixture w F x‖ = ∑ i : I, w i * ‖F i x‖ := by
  have heq : cyclicMixture w F x = ((∑ i : I, w i * ‖F i x‖ : ℝ) : ℂ) := by
    unfold cyclicMixture
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Complex.ofReal_mul]
    exact congrArg (fun z : ℂ => (w i : ℂ) * z) (hF i x)
  rw [heq]
  exact Complex.norm_of_nonneg (Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (norm_nonneg _)))

theorem dyadic_probability_nonconcentration_mixture {I : Type*} [Fintype I]
    {J : ℕ} {γ ε : ℝ} (w : I → ℝ) (F : I → ZMod (2 ^ J) → ℂ)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i : I, w i = 1)
    (hF : ∀ i x, F i x = (‖F i x‖ : ℂ))
    (hspread : ∀ i, DyadicProbabilityNonconcentration γ ε (fun x => ‖F i x‖)) :
    DyadicProbabilityNonconcentration γ ε (fun x => ‖cyclicMixture w F x‖) := by
  intro L hL hεL r
  simp only [cyclic_mixture_norm_of_nonnegative w F hw hF]
  change finitePushforward _ (fun x : ZMod (2 ^ J) => (x.val : ZMod (2 ^ L))) r ≤ _
  rw [finite_pushforward_linear_combination]
  calc
    _ ≤ ∑ i : I, w i * (2 : ℝ) ^ (-γ * (L : ℝ)) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hspread i L hL hεL r) (hw i))
    _ = _ := by rw [← Finset.sum_mul, hmass, one_mul]

theorem cyclic_convolution_norm_le_peak {q : ℕ} [NeZero q]
    (f g : ZMod q → ℂ) {M : ℝ} (hpeak : ∀ x, ‖f x‖ ≤ M) (x : ZMod q) :
    ‖cyclicConvolution f g x‖ ≤ M * ∑ y : ZMod q, ‖g y‖ := by
  rw [cyclic_convolution_comm]
  calc
    _ ≤ ∑ y : ZMod q, ‖g y * f (x - y)‖ := norm_sum_le _ _
    _ ≤ ∑ y : ZMod q, M * ‖g y‖ := by
      apply Finset.sum_le_sum
      intro y hy
      rw [norm_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hpeak (x - y)) (norm_nonneg _)
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem cyclic_probability_convolution_fiber_bound {Q q : ℕ} [NeZero Q] [NeZero q]
    {f g : ZMod Q → ℂ} (hf : FiniteComplexProbability f) (hg : FiniteComplexProbability g)
    (π : ZMod Q →+ ZMod q) {M : ℝ}
    (hpeak : ∀ r : ZMod q, finitePushforward (fun x => ‖f x‖) π r ≤ M) (r : ZMod q) :
    finitePushforward (fun x => ‖cyclicConvolution f g x‖) π r ≤ M := by
  rw [← norm_cyclicPushforward_of_probability (cyclicConvolution_probability hf hg),
    cyclicPushforward_convolution]
  have hpeak' : ∀ x, ‖cyclicPushforward f π x‖ ≤ M := by
    intro x
    rw [norm_cyclicPushforward_of_probability hf]
    exact hpeak x
  have hh := cyclic_convolution_norm_le_peak (cyclicPushforward f π) (cyclicPushforward g π) hpeak' r
  simpa only [finite_complex_probability_sum_norm (cyclicPushforward_probability hg π), mul_one] using hh

theorem dyadic_probability_nonconcentration_convolution {J : ℕ} {γ ε : ℝ}
    {f g : ZMod (2 ^ J) → ℂ} (hf : FiniteComplexProbability f) (hg : FiniteComplexProbability g)
    (hspread : DyadicProbabilityNonconcentration γ ε (fun x => ‖f x‖)) :
    DyadicProbabilityNonconcentration γ ε (fun x => ‖cyclicConvolution f g x‖) := by
  intro L hL hεL r
  let π : ZMod (2 ^ J) →+* ZMod (2 ^ L) := ZMod.castHom (pow_dvd_pow 2 hL) _
  have hπ : ∀ x : ZMod (2 ^ J), π x = (x.val : ZMod (2 ^ L)) := by
    intro x
    exact ZMod.cast_eq_val _
  have hπadd : ∀ x : ZMod (2 ^ J), π.toAddMonoidHom x = (x.val : ZMod (2 ^ L)) := hπ
  have hh := cyclic_probability_convolution_fiber_bound hf hg π.toAddMonoidHom
    (M := (2 : ℝ) ^ (-γ * (L : ℝ))) (by
      intro r
      simpa only [finitePushforward, hπadd] using hspread L hL hεL r) r
  simpa only [finitePushforward, hπadd] using hh

theorem cyclic_unit_dilate_probability {q : ℕ} [NeZero q] {f : ZMod q → ℂ}
    (hf : FiniteComplexProbability f) (u : (ZMod q)ˣ) :
    FiniteComplexProbability (cyclicUnitDilate f u) := by
  refine ⟨fun x => hf.norm_cast _, ?_⟩
  calc
    _ = ∑ x : ZMod q, f x := Fintype.sum_equiv (ringUnitMulAddEquiv u⁻¹).toEquiv _ _ (fun _ => rfl)
    _ = 1 := hf.sum_eq_one

theorem dyadic_probability_nonconcentration_cyclic_unit_dilate {J : ℕ} {γ ε : ℝ}
    {f : ZMod (2 ^ J) → ℂ}
    (hf : DyadicProbabilityNonconcentration γ ε (fun x => ‖f x‖))
    (u : (ZMod (2 ^ J))ˣ) :
    DyadicProbabilityNonconcentration γ ε (fun x => ‖cyclicUnitDilate f u x‖) :=
  dyadic_probability_nonconcentration_unit_dilate hf u⁻¹

theorem cyclic_mixture_energy_le {I : Type*} [Fintype I] {q : ℕ} [NeZero q]
    (w : I → ℝ) (F : I → ZMod q → ℂ) (hw : ∀ i, 0 ≤ w i)
    (hmass : ∑ i : I, w i = 1) :
    (∑ x : ZMod q, ‖cyclicMixture w F x‖ ^ 2) ≤
      ∑ i : I, w i * ∑ x : ZMod q, ‖F i x‖ ^ 2 := by
  have hx : ∀ x : ZMod q, ‖cyclicMixture w F x‖ ^ 2 ≤ ∑ i : I, w i * ‖F i x‖ ^ 2 := by
    intro x
    have hnorm : ‖cyclicMixture w F x‖ ≤ ∑ i : I, w i * ‖F i x‖ := by
      calc
        _ ≤ ∑ i : I, ‖(w i : ℂ) * F i x‖ := norm_sum_le _ _
        _ = _ := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [norm_mul, Complex.norm_of_nonneg (hw i)]
    exact (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans
      (weighted_sum_sq_le Finset.univ w (fun i => ‖F i x‖) (fun i _ => hw i) hmass)
  calc
    _ ≤ ∑ x : ZMod q, ∑ i : I, w i * ‖F i x‖ ^ 2 := Finset.sum_le_sum (fun x _ => hx x)
    _ = _ := by rw [Finset.sum_comm]; simp only [Finset.mul_sum]

theorem cyclic_convolution_mixture_left {I : Type*} [Fintype I] {q : ℕ} [NeZero q]
    (w : I → ℝ) (F : I → ZMod q → ℂ) (g : ZMod q → ℂ) :
    cyclicConvolution (cyclicMixture w F) g = cyclicMixture w (fun i => cyclicConvolution (F i) g) := by
  funext x
  unfold cyclicConvolution cyclicMixture
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro y hy
  ring

theorem cyclic_convolution_mixture_right {I : Type*} [Fintype I] {q : ℕ} [NeZero q]
    (f : ZMod q → ℂ) (w : I → ℝ) (G : I → ZMod q → ℂ) :
    cyclicConvolution f (cyclicMixture w G) = cyclicMixture w (fun i => cyclicConvolution f (G i)) := by
  rw [cyclic_convolution_comm, cyclic_convolution_mixture_left]
  congr 1
  funext i
  exact cyclic_convolution_comm _ _

theorem cyclic_convolution_mixture_energy_le {I K : Type*} [Fintype I] [Fintype K]
    {q : ℕ} [NeZero q] (w : I → ℝ) (v : K → ℝ)
    (F : I → ZMod q → ℂ) (G : K → ZMod q → ℂ)
    (hw : ∀ i, 0 ≤ w i) (hwmass : ∑ i : I, w i = 1)
    (hv : ∀ k, 0 ≤ v k) (hvmass : ∑ k : K, v k = 1) :
    (∑ x : ZMod q, ‖cyclicConvolution (cyclicMixture w F) (cyclicMixture v G) x‖ ^ 2) ≤
      ∑ i : I, w i * ∑ k : K, v k * ∑ x : ZMod q, ‖cyclicConvolution (F i) (G k) x‖ ^ 2 := by
  rw [cyclic_convolution_mixture_left]
  apply (cyclic_mixture_energy_le w _ hw hwmass).trans
  apply Finset.sum_le_sum
  intro i hi
  apply mul_le_mul_of_nonneg_left _ (hw i)
  rw [cyclic_convolution_mixture_right]
  exact cyclic_mixture_energy_le v _ hv hvmass

theorem cyclic_unit_dilate_mul {q : ℕ} [NeZero q]
    (f : ZMod q → ℂ) (u v : (ZMod q)ˣ) :
    cyclicUnitDilate (cyclicUnitDilate f v) u = cyclicUnitDilate f (u * v) := by
  funext x
  simp only [cyclicUnitDilate, mul_inv_rev, Units.val_mul, mul_assoc]

theorem cyclic_unit_dilate_convolution {q : ℕ} [NeZero q]
    (f g : ZMod q → ℂ) (u : (ZMod q)ˣ) :
    cyclicConvolution (cyclicUnitDilate f u) (cyclicUnitDilate g u) =
      cyclicUnitDilate (cyclicConvolution f g) u := by
  funext x
  unfold cyclicConvolution cyclicUnitDilate
  apply Fintype.sum_equiv (ringUnitMulAddEquiv u⁻¹).toEquiv
  intro y
  change f ((u⁻¹ : (ZMod q)ˣ) * y) * g ((u⁻¹ : (ZMod q)ˣ) * (x - y)) =
    f ((u⁻¹ : (ZMod q)ˣ) * y) * g ((u⁻¹ : (ZMod q)ˣ) * x - (u⁻¹ : (ZMod q)ˣ) * y)
  rw [mul_sub]

theorem cyclic_unit_pair_convolution_energy {q : ℕ} [NeZero q]
    (f g : ZMod q → ℂ) (u v : (ZMod q)ˣ) :
    (∑ x : ZMod q, ‖cyclicConvolution (cyclicUnitDilate f u) (cyclicUnitDilate g v) x‖ ^ 2) =
      ∑ x : ZMod q, ‖cyclicConvolution f (cyclicUnitDilate g (u⁻¹ * v)) x‖ ^ 2 := by
  have hrel : cyclicUnitDilate (cyclicUnitDilate g (u⁻¹ * v)) u = cyclicUnitDilate g v := by
    rw [cyclic_unit_dilate_mul, mul_inv_cancel_left]
  rw [← hrel, cyclic_unit_dilate_convolution, cyclic_unit_dilate_sq_norm]

/-- One probability step: average unit dilations, then add two independent
samples from that averaged law. -/
noncomputable def cyclicUnitAveragingStep {q : ℕ} [NeZero q]
    (f : ZMod q → ℂ) (w : (ZMod q)ˣ → ℝ) : ZMod q → ℂ :=
  cyclicConvolution (cyclicMixture w (cyclicUnitDilate f)) (cyclicMixture w (cyclicUnitDilate f))

theorem cyclic_unit_averaging_step_probability {q : ℕ} [NeZero q] {f : ZMod q → ℂ}
    (hf : FiniteComplexProbability f) (w : (ZMod q)ˣ → ℝ)
    (hw : ∀ u, 0 ≤ w u) (hmass : ∑ u : (ZMod q)ˣ, w u = 1) :
    FiniteComplexProbability (cyclicUnitAveragingStep f w) := by
  have hmix := cyclicMixture_probability w (cyclicUnitDilate f) hw hmass
    (cyclic_unit_dilate_probability hf)
  exact cyclicConvolution_probability hmix hmix

theorem dyadic_probability_nonconcentration_averaging_step {J : ℕ} {γ ε : ℝ}
    {f : ZMod (2 ^ J) → ℂ} (hf : FiniteComplexProbability f)
    (hspread : DyadicProbabilityNonconcentration γ ε (fun x => ‖f x‖))
    (w : (ZMod (2 ^ J))ˣ → ℝ) (hw : ∀ u, 0 ≤ w u) (hmass : ∑ u : (ZMod (2 ^ J))ˣ, w u = 1) :
    DyadicProbabilityNonconcentration γ ε (fun x => ‖cyclicUnitAveragingStep f w x‖) := by
  have hmix := cyclicMixture_probability w (cyclicUnitDilate f) hw hmass
    (cyclic_unit_dilate_probability hf)
  exact dyadic_probability_nonconcentration_convolution hmix hmix
    (dyadic_probability_nonconcentration_mixture w (cyclicUnitDilate f) hw hmass
      (fun u => (cyclic_unit_dilate_probability hf u).norm_cast)
      (dyadic_probability_nonconcentration_cyclic_unit_dilate hspread))

theorem cyclic_unit_averaging_step_energy_le {q : ℕ} [NeZero q]
    (f : ZMod q → ℂ) (w : (ZMod q)ˣ → ℝ)
    (hw : ∀ u, 0 ≤ w u) (hmass : ∑ u : (ZMod q)ˣ, w u = 1) :
    (∑ x : ZMod q, ‖cyclicUnitAveragingStep f w x‖ ^ 2) ≤
      ∑ u : (ZMod q)ˣ, w u * ∑ v : (ZMod q)ˣ, w v *
        ∑ x : ZMod q, ‖cyclicConvolution f (cyclicUnitDilate f (u⁻¹ * v)) x‖ ^ 2 := by
  have hh := cyclic_convolution_mixture_energy_le w w (cyclicUnitDilate f) (cyclicUnitDilate f)
    hw hmass hw hmass
  simpa only [cyclicUnitAveragingStep, cyclic_unit_pair_convolution_energy] using hh

theorem cyclic_unit_averaging_step_energy_mono {q : ℕ} [NeZero q]
    {f : ZMod q → ℂ} (hf : FiniteComplexProbability f) (w : (ZMod q)ˣ → ℝ)
    (hw : ∀ u, 0 ≤ w u) (hmass : ∑ u : (ZMod q)ˣ, w u = 1) :
    (∑ x : ZMod q, ‖cyclicUnitAveragingStep f w x‖ ^ 2) ≤ ∑ x : ZMod q, ‖f x‖ ^ 2 := by
  let θ := cyclicMixture w (cyclicUnitDilate f)
  have hθ := cyclicMixture_probability w (cyclicUnitDilate f) hw hmass
    (cyclic_unit_dilate_probability hf)
  have hconv := cyclic_convolution_young_sq θ θ
  rw [finite_complex_probability_sum_norm hθ, one_pow, one_mul] at hconv
  have hmix := cyclic_mixture_energy_le w (cyclicUnitDilate f) hw hmass
  simp only [cyclic_unit_dilate_sq_norm, ← Finset.sum_mul, hmass, one_mul] at hmix
  exact hconv.trans hmix

theorem exists_dyadic_averaging_step_flattening {γ δ : ℝ}
    (hγ : 0 < γ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ τ ε : ℝ, 0 < τ ∧ 0 < ε ∧ ε ≤ 1 / 4 ∧ ∃ J₀ : ℕ,
      ∀ J : ℕ, J₀ ≤ J → ∀ f : ZMod (2 ^ J) → ℂ,
      ∀ w : (ZMod (2 ^ J))ˣ → ℝ,
        FiniteComplexProbability f →
        (2 : ℝ) ^ (-(1 - δ) * (J : ℝ)) ≤ (∑ x : ZMod (2 ^ J), ‖f x‖ ^ 2) →
        DyadicProbabilityNonconcentration γ ε (fun x => ‖f x‖) →
        (∀ u, 0 ≤ w u) → (∑ u : (ZMod (2 ^ J))ˣ, w u) = 1 →
        DyadicUnitProbabilityNonconcentration γ ε w →
        (∑ x : ZMod (2 ^ J), ‖cyclicUnitAveragingStep f w x‖ ^ 2) ≤
          (2 : ℝ) ^ (-τ * (J : ℝ)) * ∑ x : ZMod (2 ^ J), ‖f x‖ ^ 2 := by
  classical
  obtain ⟨τ, ε, hτ, hε, hε4, J₀, hflat⟩ := exists_dyadic_weighted_probability_flattening hγ hδ hδ1
  refine ⟨τ, ε, hτ, hε, hε4, J₀, ?_⟩
  intro J hJ f w hf hnorm hspread hw hmass hwspread
  have hfreal : (fun x : ZMod (2 ^ J) => (‖f x‖ : ℂ)) = f := funext (fun x => (hf.norm_cast x).symm)
  have hu : ∀ u : (ZMod (2 ^ J))ˣ,
      (∑ v : (ZMod (2 ^ J))ˣ, w v * ∑ x : ZMod (2 ^ J),
        ‖cyclicConvolution f (cyclicUnitDilate f (u⁻¹ * v)) x‖ ^ 2) ≤
          (2 : ℝ) ^ (-τ * (J : ℝ)) * ∑ x : ZMod (2 ^ J), ‖f x‖ ^ 2 := by
    intro u
    have hmassu : (∑ v : (ZMod (2 ^ J))ˣ, w (u * v)) = 1 := by
      calc
        _ = ∑ v : (ZMod (2 ^ J))ˣ, w v := Fintype.sum_equiv (Equiv.mulLeft u) _ _ (fun _ => rfl)
        _ = 1 := hmass
    have hh := hflat J hJ (fun x => ‖f x‖) (fun v => w (u * v)) (fun x => norm_nonneg _)
      (finite_complex_probability_sum_norm hf).le hnorm hspread (fun v => hw (u * v)) hmassu.le
      (dyadic_unit_probability_nonconcentration_translate hwspread u)
    rw [hfreal] at hh
    have heq : (∑ v : (ZMod (2 ^ J))ˣ, w (u * v) * ∑ x : ZMod (2 ^ J),
        ‖cyclicConvolution f (cyclicUnitDilate f v) x‖ ^ 2) =
        ∑ v : (ZMod (2 ^ J))ˣ, w v * ∑ x : ZMod (2 ^ J),
          ‖cyclicConvolution f (cyclicUnitDilate f (u⁻¹ * v)) x‖ ^ 2 := by
      apply Fintype.sum_equiv (Equiv.mulLeft u)
      intro v
      change w (u * v) * (∑ x : ZMod (2 ^ J), ‖cyclicConvolution f (cyclicUnitDilate f v) x‖ ^ 2) =
        w (u * v) * ∑ x : ZMod (2 ^ J), ‖cyclicConvolution f (cyclicUnitDilate f (u⁻¹ * (u * v))) x‖ ^ 2
      rw [inv_mul_cancel_left]
    rwa [heq] at hh
  calc
    _ ≤ ∑ u : (ZMod (2 ^ J))ˣ, w u * ∑ v : (ZMod (2 ^ J))ˣ, w v *
        ∑ x : ZMod (2 ^ J), ‖cyclicConvolution f (cyclicUnitDilate f (u⁻¹ * v)) x‖ ^ 2 :=
      cyclic_unit_averaging_step_energy_le f w hw hmass
    _ ≤ ∑ u : (ZMod (2 ^ J))ˣ, w u *
        ((2 : ℝ) ^ (-τ * (J : ℝ)) * ∑ x : ZMod (2 ^ J), ‖f x‖ ^ 2) :=
      Finset.sum_le_sum (fun u _ => mul_le_mul_of_nonneg_left (hu u) (hw u))
    _ = _ := by rw [← Finset.sum_mul, hmass, one_mul]

theorem exists_dyadic_averaging_step_energy_bound {γ δ : ℝ}
    (hγ : 0 < γ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ τ ε : ℝ, 0 < τ ∧ 0 < ε ∧ ε ≤ 1 / 4 ∧ ∃ J₀ : ℕ,
      ∀ J : ℕ, J₀ ≤ J → ∀ f : ZMod (2 ^ J) → ℂ,
      ∀ w : (ZMod (2 ^ J))ˣ → ℝ,
        FiniteComplexProbability f →
        DyadicProbabilityNonconcentration γ ε (fun x => ‖f x‖) →
        (∀ u, 0 ≤ w u) → (∑ u : (ZMod (2 ^ J))ˣ, w u) = 1 →
        DyadicUnitProbabilityNonconcentration γ ε w →
        (∑ x : ZMod (2 ^ J), ‖cyclicUnitAveragingStep f w x‖ ^ 2) ≤
          max ((2 : ℝ) ^ (-(1 - δ) * (J : ℝ)))
            ((2 : ℝ) ^ (-τ * (J : ℝ)) * ∑ x : ZMod (2 ^ J), ‖f x‖ ^ 2) := by
  obtain ⟨τ, ε, hτ, hε, hε4, J₀, hflat⟩ := exists_dyadic_averaging_step_flattening hγ hδ hδ1
  refine ⟨τ, ε, hτ, hε, hε4, J₀, ?_⟩
  intro J hJ f w hf hspread hw hmass hwspread
  by_cases hnorm : (2 : ℝ) ^ (-(1 - δ) * (J : ℝ)) ≤ ∑ x : ZMod (2 ^ J), ‖f x‖ ^ 2
  · exact (hflat J hJ f w hf hnorm hspread hw hmass hwspread).trans (le_max_right _ _)
  · exact (cyclic_unit_averaging_step_energy_mono hf w hw hmass).trans
      ((lt_of_not_ge hnorm).le.trans (le_max_left _ _))

theorem finite_complex_probability_sq_norm_le_one {X : Type*} [Fintype X]
    {f : X → ℂ} (hf : FiniteComplexProbability f) : (∑ x : X, ‖f x‖ ^ 2) ≤ 1 := by
  have hh := Finset.sum_sq_le_sq_sum_of_nonneg (s := (Finset.univ : Finset X))
    (f := fun x => ‖f x‖) (fun _ _ => norm_nonneg _)
  simpa only [finite_complex_probability_sum_norm hf, one_pow] using hh

theorem finite_contractive_iteration {R : ℕ} (E : ℕ → ℝ) {M c : ℝ}
    (hM : 0 ≤ M) (hc : 0 ≤ c) (hc1 : c ≤ 1) (hbase : E 0 ≤ 1)
    (hstep : ∀ n < R, E (n + 1) ≤ max M (c * E n)) :
    ∀ n ≤ R, E n ≤ max M (c ^ n) := by
  intro n
  induction n with
  | zero =>
    intro hn
    exact hbase.trans (by simpa using le_max_right M (1 : ℝ))
  | succ n ih =>
    intro hn
    apply (hstep n (by omega)).trans
    apply max_le (le_max_left _ _)
    calc
      c * E n ≤ c * max M (c ^ n) := mul_le_mul_of_nonneg_left (ih (by omega)) hc
      _ = max (c * M) (c ^ (n + 1)) := by rw [mul_max_of_nonneg _ _ hc, pow_succ']
      _ ≤ max M (c ^ (n + 1)) := max_le_max
        (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hc1 hM) le_rfl

noncomputable def cyclicUnitAveragingIter {q : ℕ} [NeZero q]
    (f : ZMod q → ℂ) (w : ℕ → (ZMod q)ˣ → ℝ) : ℕ → ZMod q → ℂ
  | 0 => f
  | n + 1 => cyclicUnitAveragingStep (cyclicUnitAveragingIter f w n) (w n)

theorem cyclic_unit_averaging_iter_probability {q R : ℕ} [NeZero q]
    {f : ZMod q → ℂ} (hf : FiniteComplexProbability f) (w : ℕ → (ZMod q)ˣ → ℝ)
    (hw : ∀ n < R, ∀ u, 0 ≤ w n u) (hmass : ∀ n < R, ∑ u : (ZMod q)ˣ, w n u = 1) :
    ∀ n ≤ R, FiniteComplexProbability (cyclicUnitAveragingIter f w n) := by
  intro n
  induction n with
  | zero => intro hn; exact hf
  | succ n ih =>
    intro hn
    exact cyclic_unit_averaging_step_probability (ih (by omega)) (w n) (hw n (by omega)) (hmass n (by omega))

theorem dyadic_probability_nonconcentration_averaging_iter {J R : ℕ} {γ ε : ℝ}
    {f : ZMod (2 ^ J) → ℂ} (hf : FiniteComplexProbability f)
    (hspread : DyadicProbabilityNonconcentration γ ε (fun x => ‖f x‖))
    (w : ℕ → (ZMod (2 ^ J))ˣ → ℝ)
    (hw : ∀ n < R, ∀ u, 0 ≤ w n u) (hmass : ∀ n < R, ∑ u : (ZMod (2 ^ J))ˣ, w n u = 1) :
    ∀ n ≤ R, DyadicProbabilityNonconcentration γ ε (fun x => ‖cyclicUnitAveragingIter f w n x‖) := by
  intro n
  induction n with
  | zero => intro hn; exact hspread
  | succ n ih =>
    intro hn
    exact dyadic_probability_nonconcentration_averaging_step
      (cyclic_unit_averaging_iter_probability hf w hw hmass n (by omega)) (ih (by omega))
      (w n) (hw n (by omega)) (hmass n (by omega))

/-- A fixed number of independent unit-averaging steps reaches the density
threshold. The number of steps and residue cutoff are uniform in the modulus. -/
theorem exists_dyadic_probability_flattening_iteration {γ δ : ℝ}
    (hγ : 0 < γ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 4 ∧ ∃ R : ℕ, 0 < R ∧ ∃ J₀ : ℕ,
      ∀ J : ℕ, J₀ ≤ J → ∀ f : ZMod (2 ^ J) → ℂ,
      ∀ w : ℕ → (ZMod (2 ^ J))ˣ → ℝ,
        FiniteComplexProbability f →
        DyadicProbabilityNonconcentration γ ε (fun x => ‖f x‖) →
        (∀ n < R, ∀ u, 0 ≤ w n u) →
        (∀ n < R, (∑ u : (ZMod (2 ^ J))ˣ, w n u) = 1) →
        (∀ n < R, DyadicUnitProbabilityNonconcentration γ ε (w n)) →
        (∑ x : ZMod (2 ^ J), ‖cyclicUnitAveragingIter f w R x‖ ^ 2) ≤
          (2 : ℝ) ^ (-(1 - δ) * (J : ℝ)) := by
  obtain ⟨τ, ε, hτ, hε, hε4, J₀, hstep⟩ := exists_dyadic_averaging_step_energy_bound hγ hδ hδ1
  obtain ⟨R, hR⟩ := exists_nat_gt (1 / τ)
  have hRτ : 1 ≤ (R : ℝ) * τ := ((div_lt_iff₀ hτ).mp hR).le
  have hR0 : 0 < R := by
    by_contra hn
    have heq : R = 0 := by omega
    subst R
    norm_num at hRτ
  refine ⟨ε, hε, hε4, R, hR0, J₀, ?_⟩
  intro J hJ f w hf hspread hw hmass hwspread
  let M := (2 : ℝ) ^ (-(1 - δ) * (J : ℝ))
  let c := (2 : ℝ) ^ (-τ * (J : ℝ))
  let E := fun n : ℕ => ∑ x : ZMod (2 ^ J), ‖cyclicUnitAveragingIter f w n x‖ ^ 2
  have hc : 0 ≤ c := by positivity
  have hc1 : c ≤ 1 := by
    calc
      _ ≤ (2 : ℝ) ^ (0 : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        nlinarith only [mul_nonneg hτ.le (Nat.cast_nonneg J : (0 : ℝ) ≤ J)]
      _ = 1 := Real.rpow_zero _
  have hE : E R ≤ max M (c ^ R) := by
    apply finite_contractive_iteration E (by positivity) hc hc1 (finite_complex_probability_sq_norm_le_one hf)
      (fun n hn => hstep J hJ (cyclicUnitAveragingIter f w n) (w n)
        (cyclic_unit_averaging_iter_probability hf w hw hmass n hn.le)
        (dyadic_probability_nonconcentration_averaging_iter hf hspread w hw hmass n hn.le)
        (hw n hn) (hmass n hn) (hwspread n hn)) R le_rfl
  have hcR : c ^ R ≤ M := by
    dsimp only [c, M]
    rw [← Real.rpow_mul_natCast (by norm_num)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg _
    have hRτJ := mul_le_mul_of_nonneg_right hRτ hJ0
    have hδJ := mul_nonneg hδ.le hJ0
    nlinarith only [hRτJ, hδJ]
  exact hE.trans (max_le le_rfl hcR)



theorem dft_cyclic_unit_dilate {q : ℕ} [NeZero q]
    (f : ZMod q → ℂ) (u : (ZMod q)ˣ) (k : ZMod q) :
    ZMod.dft (cyclicUnitDilate f u) k = ZMod.dft f ((u : ZMod q) * k) := by
  simp only [ZMod.dft_apply, smul_eq_mul, cyclicUnitDilate]
  apply Fintype.sum_equiv (ringUnitMulAddEquiv u⁻¹).toEquiv
  intro x
  change ZMod.stdAddChar (-(x * k)) * f (((u⁻¹ : (ZMod q)ˣ) : ZMod q) * x) =
    ZMod.stdAddChar (-((((u⁻¹ : (ZMod q)ˣ) : ZMod q) * x) * ((u : ZMod q) * k))) *
      f (((u⁻¹ : (ZMod q)ˣ) : ZMod q) * x)
  have heq : (((u⁻¹ : (ZMod q)ˣ) : ZMod q) * x) * ((u : ZMod q) * k) = x * k := by
    calc
      _ = (((u⁻¹ : (ZMod q)ˣ) : ZMod q) * (u : ZMod q)) * (x * k) := by ring
      _ = _ := by rw [Units.inv_mul, one_mul]
  rw [heq]

theorem dft_cyclic_mixture {I : Type*} [Fintype I] {q : ℕ} [NeZero q]
    (w : I → ℝ) (F : I → ZMod q → ℂ) (k : ZMod q) :
    ZMod.dft (cyclicMixture w F) k = ∑ i : I, (w i : ℂ) * ZMod.dft (F i) k := by
  simp only [ZMod.dft_apply, smul_eq_mul, cyclicMixture, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro x hx
  ring

theorem norm_dft_cyclic_unit_mixture_le {q : ℕ} [NeZero q]
    (f : ZMod q → ℂ) (w : (ZMod q)ˣ → ℝ) (hw : ∀ u, 0 ≤ w u) (k : ZMod q) :
    ‖ZMod.dft (cyclicMixture w (cyclicUnitDilate f)) k‖ ≤
      ∑ u : (ZMod q)ˣ, w u * ‖ZMod.dft f ((u : ZMod q) * k)‖ := by
  rw [dft_cyclic_mixture]
  calc
    _ ≤ ∑ u : (ZMod q)ˣ, ‖(w u : ℂ) * ZMod.dft (cyclicUnitDilate f u) k‖ := norm_sum_le _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [norm_mul, Complex.norm_of_nonneg (hw u), dft_cyclic_unit_dilate]

theorem weighted_sum_two_power_le {I : Type*} [Fintype I]
    (w t : I → ℝ) (hw : ∀ i, 0 ≤ w i) (ht : ∀ i, 0 ≤ t i)
    (hmass : ∑ i : I, w i = 1) (n : ℕ) :
    (∑ i : I, w i * t i) ^ (2 ^ n) ≤ ∑ i : I, w i * t i ^ (2 ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_mul]
    calc
      _ ≤ (∑ i : I, w i * t i ^ (2 ^ n)) ^ 2 :=
        pow_le_pow_left₀ (pow_nonneg (Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (ht i))) _) ih 2
      _ ≤ ∑ i : I, w i * (t i ^ (2 ^ n)) ^ 2 :=
        weighted_sum_sq_le Finset.univ w (fun i => t i ^ (2 ^ n)) (fun i _ => hw i) hmass
      _ = _ := by simp only [pow_mul]

theorem norm_dft_unit_mixture_two_power_le {q : ℕ} [NeZero q]
    (f : ZMod q → ℂ) (w : (ZMod q)ˣ → ℝ)
    (hw : ∀ u, 0 ≤ w u) (hmass : ∑ u : (ZMod q)ˣ, w u = 1)
    (n : ℕ) (k : ZMod q) :
    ‖ZMod.dft (cyclicMixture w (cyclicUnitDilate f)) k‖ ^ (2 ^ n) ≤
      ∑ u : (ZMod q)ˣ, w u * ‖ZMod.dft f ((u : ZMod q) * k)‖ ^ (2 ^ n) := by
  exact (pow_le_pow_left₀ (norm_nonneg _) (norm_dft_cyclic_unit_mixture_le f w hw k) _).trans
    (weighted_sum_two_power_le w (fun u => ‖ZMod.dft f ((u : ZMod q) * k)‖)
      hw (fun _ => norm_nonneg _) hmass n)

theorem dft_neg_of_real {q : ℕ} [NeZero q] (f : ZMod q → ℂ)
    (hf : ∀ x, f x = (‖f x‖ : ℂ)) (k : ZMod q) :
    ZMod.dft f (-k) = starRingEnd ℂ (ZMod.dft f k) := by
  have hconj : (fun x => starRingEnd ℂ (f x)) = f := by
    funext x
    rw [hf x]
    exact Complex.conj_ofReal _
  have hh := dft_conjugate f (-k)
  rwa [hconj, neg_neg] at hh

noncomputable def cyclicSymmetrize {q : ℕ} [NeZero q] (f : ZMod q → ℂ) : ZMod q → ℂ :=
  cyclicConvolution f (cyclicUnitDilate f (-1))

theorem dft_cyclic_symmetrize {q : ℕ} [NeZero q] (f : ZMod q → ℂ)
    (hf : ∀ x, f x = (‖f x‖ : ℂ)) (k : ZMod q) :
    ZMod.dft (cyclicSymmetrize f) k = (‖ZMod.dft f k‖ ^ 2 : ℝ) := by
  rw [cyclicSymmetrize, dft_cyclicConvolution, dft_cyclic_unit_dilate]
  simp only [Units.val_neg, Units.val_one, neg_one_mul]
  rw [dft_neg_of_real f hf]
  simpa only [Complex.ofReal_pow] using Complex.mul_conj' (ZMod.dft f k)

theorem cyclic_symmetrize_probability {q : ℕ} [NeZero q]
    {f : ZMod q → ℂ} (hf : FiniteComplexProbability f) :
    FiniteComplexProbability (cyclicSymmetrize f) :=
  cyclicConvolution_probability hf (cyclic_unit_dilate_probability hf (-1))

theorem dyadic_probability_nonconcentration_symmetrize {J : ℕ} {γ ε : ℝ}
    {f : ZMod (2 ^ J) → ℂ} (hf : FiniteComplexProbability f)
    (hspread : DyadicProbabilityNonconcentration γ ε (fun x => ‖f x‖)) :
    DyadicProbabilityNonconcentration γ ε (fun x => ‖cyclicSymmetrize f x‖) :=
  dyadic_probability_nonconcentration_convolution hf (cyclic_unit_dilate_probability hf (-1)) hspread

theorem dft_cyclic_symmetrize_nonnegative {q : ℕ} [NeZero q] (f : ZMod q → ℂ)
    (hf : ∀ x, f x = (‖f x‖ : ℂ)) (k : ZMod q) :
    ZMod.dft (cyclicSymmetrize f) k = (‖ZMod.dft (cyclicSymmetrize f) k‖ : ℂ) := by
  rw [dft_cyclic_symmetrize f hf, Complex.norm_of_nonneg (sq_nonneg _)]

theorem dft_unit_mixture_of_nonnegative_fourier {q : ℕ} [NeZero q]
    (f : ZMod q → ℂ) (w : (ZMod q)ˣ → ℝ)
    (hf : ∀ k, ZMod.dft f k = (‖ZMod.dft f k‖ : ℂ)) (k : ZMod q) :
    ZMod.dft (cyclicMixture w (cyclicUnitDilate f)) k =
      ((∑ u : (ZMod q)ˣ, w u * ‖ZMod.dft f ((u : ZMod q) * k)‖ : ℝ) : ℂ) := by
  rw [dft_cyclic_mixture, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro u hu
  rw [dft_cyclic_unit_dilate, Complex.ofReal_mul]
  exact congrArg (fun z : ℂ => (w u : ℂ) * z) (hf ((u : ZMod q) * k))

theorem norm_dft_unit_mixture_of_nonnegative_fourier {q : ℕ} [NeZero q]
    (f : ZMod q → ℂ) (w : (ZMod q)ˣ → ℝ) (hw : ∀ u, 0 ≤ w u)
    (hf : ∀ k, ZMod.dft f k = (‖ZMod.dft f k‖ : ℂ)) (k : ZMod q) :
    ‖ZMod.dft (cyclicMixture w (cyclicUnitDilate f)) k‖ =
      ∑ u : (ZMod q)ˣ, w u * ‖ZMod.dft f ((u : ZMod q) * k)‖ := by
  rw [dft_unit_mixture_of_nonnegative_fourier f w hf]
  exact Complex.norm_of_nonneg (Finset.sum_nonneg (fun u _ => mul_nonneg (hw u) (norm_nonneg _)))

theorem dft_unit_averaging_step_of_nonnegative_fourier {q : ℕ} [NeZero q]
    (f : ZMod q → ℂ) (w : (ZMod q)ˣ → ℝ)
    (hf : ∀ k, ZMod.dft f k = (‖ZMod.dft f k‖ : ℂ)) (k : ZMod q) :
    ZMod.dft (cyclicUnitAveragingStep f w) k =
      (((∑ u : (ZMod q)ˣ, w u * ‖ZMod.dft f ((u : ZMod q) * k)‖) ^ 2 : ℝ) : ℂ) := by
  rw [cyclicUnitAveragingStep, dft_cyclicConvolution, dft_unit_mixture_of_nonnegative_fourier f w hf]
  push_cast
  ring

theorem norm_dft_unit_averaging_step_of_nonnegative_fourier {q : ℕ} [NeZero q]
    (f : ZMod q → ℂ) (w : (ZMod q)ˣ → ℝ)
    (hf : ∀ k, ZMod.dft f k = (‖ZMod.dft f k‖ : ℂ)) (k : ZMod q) :
    ‖ZMod.dft (cyclicUnitAveragingStep f w) k‖ =
      (∑ u : (ZMod q)ˣ, w u * ‖ZMod.dft f ((u : ZMod q) * k)‖) ^ 2 := by
  rw [dft_unit_averaging_step_of_nonnegative_fourier f w hf, Complex.norm_of_nonneg (sq_nonneg _)]

theorem dft_unit_averaging_step_nonnegative {q : ℕ} [NeZero q]
    (f : ZMod q → ℂ) (w : (ZMod q)ˣ → ℝ)
    (hf : ∀ k, ZMod.dft f k = (‖ZMod.dft f k‖ : ℂ)) (k : ZMod q) :
    ZMod.dft (cyclicUnitAveragingStep f w) k = (‖ZMod.dft (cyclicUnitAveragingStep f w) k‖ : ℂ) := by
  rw [dft_unit_averaging_step_of_nonnegative_fourier f w hf, Complex.norm_of_nonneg (sq_nonneg _)]

theorem dft_unit_averaging_iter_nonnegative {q : ℕ} [NeZero q]
    (f : ZMod q → ℂ) (w : ℕ → (ZMod q)ˣ → ℝ)
    (hf : ∀ k, ZMod.dft f k = (‖ZMod.dft f k‖ : ℂ)) (n : ℕ) :
    ∀ k, ZMod.dft (cyclicUnitAveragingIter f w n) k =
      (‖ZMod.dft (cyclicUnitAveragingIter f w n) k‖ : ℂ) := by
  induction n with
  | zero => exact hf
  | succ n ih => exact dft_unit_averaging_step_nonnegative _ _ ih

noncomputable def cyclicUnitProductIter {q : ℕ} [NeZero q]
    (f : ZMod q → ℂ) (w : ℕ → (ZMod q)ˣ → ℝ) : ℕ → ZMod q → ℂ
  | 0 => f
  | n + 1 => cyclicMixture (w n) (cyclicUnitDilate (cyclicUnitProductIter f w n))

theorem norm_dft_unit_product_dominated {q R : ℕ} [NeZero q]
    (f : ZMod q → ℂ) (w : ℕ → (ZMod q)ˣ → ℝ)
    (hf : ∀ x, f x = (‖f x‖ : ℂ))
    (hw : ∀ n < R, ∀ u, 0 ≤ w n u) (hmass : ∀ n < R, ∑ u : (ZMod q)ˣ, w n u = 1) :
    ∀ n ≤ R, ∀ k : ZMod q,
      ‖ZMod.dft (cyclicUnitProductIter f w n) k‖ ^ (2 ^ (n + 1)) ≤
        ‖ZMod.dft (cyclicUnitAveragingIter (cyclicSymmetrize f) w n) k‖ := by
  intro n
  induction n with
  | zero =>
    intro hn k
    simp only [cyclicUnitProductIter, cyclicUnitAveragingIter, zero_add, pow_one,
      dft_cyclic_symmetrize f hf, Complex.norm_of_nonneg (sq_nonneg _)]
    exact le_rfl
  | succ n ih =>
    intro hn k
    let ν := cyclicUnitAveragingIter (cyclicSymmetrize f) w n
    have hν : ∀ k, ZMod.dft ν k = (‖ZMod.dft ν k‖ : ℂ) :=
      dft_unit_averaging_iter_nonnegative _ w (dft_cyclic_symmetrize_nonnegative f hf) n
    have hh : ‖ZMod.dft (cyclicUnitProductIter f w (n + 1)) k‖ ^ (2 ^ (n + 1)) ≤
        ∑ u : (ZMod q)ˣ, w n u * ‖ZMod.dft ν ((u : ZMod q) * k)‖ := by
      apply (norm_dft_unit_mixture_two_power_le (cyclicUnitProductIter f w n) (w n)
        (hw n (by omega)) (hmass n (by omega)) (n + 1) k).trans
      exact Finset.sum_le_sum (fun u _ => mul_le_mul_of_nonneg_left (ih (by omega) _) (hw n (by omega) u))
    change ‖ZMod.dft (cyclicUnitProductIter f w (n + 1)) k‖ ^ (2 ^ (n + 1 + 1)) ≤
      ‖ZMod.dft (cyclicUnitAveragingStep ν (w n)) k‖
    rw [norm_dft_unit_averaging_step_of_nonnegative_fourier ν (w n) hν, pow_succ, pow_mul]
    exact pow_le_pow_left₀ (pow_nonneg (norm_nonneg _) _) hh 2

theorem norm_dft_unit_product_final_power_le {q R : ℕ} [NeZero q]
    (f : ZMod q → ℂ) (w : ℕ → (ZMod q)ˣ → ℝ)
    (hf : ∀ x, f x = (‖f x‖ : ℂ))
    (hw : ∀ n < R + 1, ∀ u, 0 ≤ w n u)
    (hmass : ∀ n < R + 1, ∑ u : (ZMod q)ˣ, w n u = 1) (k : ZMod q) :
    ‖ZMod.dft (cyclicUnitProductIter f w (R + 1)) k‖ ^ (2 ^ (R + 1)) ≤
      ‖ZMod.dft (cyclicMixture (w R)
        (cyclicUnitDilate (cyclicUnitAveragingIter (cyclicSymmetrize f) w R))) k‖ := by
  have hν := dft_unit_averaging_iter_nonnegative (cyclicSymmetrize f) w
    (dft_cyclic_symmetrize_nonnegative f hf) R
  rw [norm_dft_unit_mixture_of_nonnegative_fourier _ _ (hw R (by omega)) hν]
  apply (norm_dft_unit_mixture_two_power_le (cyclicUnitProductIter f w R) (w R)
    (hw R (by omega)) (hmass R (by omega)) (R + 1) k).trans
  apply Finset.sum_le_sum
  intro u hu
  apply mul_le_mul_of_nonneg_left _ (hw R (by omega) u)
  exact norm_dft_unit_product_dominated f w hf hw hmass R (by omega) _

theorem finite_sum_comp_le_of_injective {X Y : Type*} [Fintype X] [Fintype Y]
    (e : X → Y) (he : Function.Injective e) (F : Y → ℝ) (hF : ∀ y, 0 ≤ F y) :
    (∑ x : X, F (e x)) ≤ ∑ y : Y, F y := by
  classical
  calc
    _ = ∑ y ∈ (Finset.univ : Finset X).image e, F y := by
      symm
      exact Finset.sum_image (fun x _ y _ hxy => he hxy)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun y _ _ => hF y)

theorem norm_dft_unit_mixture_sq_le {q : ℕ} [NeZero q]
    (f : ZMod q → ℂ) (w : (ZMod q)ˣ → ℝ)
    (hw : ∀ u, 0 ≤ w u) (hmass : ∑ u : (ZMod q)ˣ, w u = 1)
    {M : ℝ} (hpeak : ∀ u, w u ≤ M) {k : ZMod q} (hk : IsUnit k) :
    ‖ZMod.dft (cyclicMixture w (cyclicUnitDilate f)) k‖ ^ 2 ≤
      (q : ℝ) * M * ∑ x : ZMod q, ‖f x‖ ^ 2 := by
  have hM : 0 ≤ M := (hw 1).trans (hpeak 1)
  have hwsq : (∑ u : (ZMod q)ˣ, w u ^ 2) ≤ M := by
    calc
      _ ≤ ∑ u : (ZMod q)ˣ, w u * M := Finset.sum_le_sum (fun u _ => by
        simpa only [pow_two] using mul_le_mul_of_nonneg_left (hpeak u) (hw u))
      _ = M := by rw [← Finset.sum_mul, hmass, one_mul]
  have hfsq : (∑ u : (ZMod q)ˣ, ‖ZMod.dft f ((u : ZMod q) * k)‖ ^ 2) ≤
      (q : ℝ) * ∑ x : ZMod q, ‖f x‖ ^ 2 := by
    obtain ⟨v, rfl⟩ := hk
    have hinj : Function.Injective (fun u : (ZMod q)ˣ => (u : ZMod q) * (v : ZMod q)) := by
      intro u z huz
      exact Units.val_injective (v.mulRight.injective huz)
    exact (finite_sum_comp_le_of_injective _ hinj (fun x => ‖ZMod.dft f x‖ ^ 2)
      (fun _ => sq_nonneg _)).trans_eq (dft_parseval f)
  calc
    _ ≤ (∑ u : (ZMod q)ˣ, w u * ‖ZMod.dft f ((u : ZMod q) * k)‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_dft_cyclic_unit_mixture_le f w hw k) 2
    _ ≤ (∑ u : (ZMod q)ˣ, w u ^ 2) *
        ∑ u : (ZMod q)ˣ, ‖ZMod.dft f ((u : ZMod q) * k)‖ ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ ≤ M * ((q : ℝ) * ∑ x : ZMod q, ‖f x‖ ^ 2) :=
      mul_le_mul hwsq hfsq (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) hM
    _ = _ := by ring

theorem dyadic_unit_probability_point_bound {J : ℕ} {γ ε : ℝ}
    {w : (ZMod (2 ^ J))ˣ → ℝ} (hw : ∀ u, 0 ≤ w u)
    (hspread : DyadicUnitProbabilityNonconcentration γ ε w)
    (hJ : 0 < J) (hε : ε < 1) (u : (ZMod (2 ^ J))ˣ) :
    w u ≤ (2 : ℝ) ^ (-γ * (J : ℝ)) := by
  have hεJ : ε * (J : ℝ) < (J : ℝ) := by
    simpa only [one_mul] using mul_lt_mul_of_pos_right hε (show (0 : ℝ) < J by exact_mod_cast hJ)
  apply (Finset.single_le_sum (fun v _ => hw v) (show u ∈ Finset.univ.filter
    (fun v : (ZMod (2 ^ J))ˣ => (((v : ZMod (2 ^ J)).val : ZMod (2 ^ J))) = (u : ZMod (2 ^ J))) by simp)).trans
  exact hspread J le_rfl hεJ (u : ZMod (2 ^ J))

/-- Power cancellation for an initial nonconcentrated law followed by a
fixed number of independent nonconcentrated unit inputs. -/
theorem exists_dyadic_unit_product_fourier_decay {γ : ℝ} (hγ : 0 < γ) :
    ∃ ε τ : ℝ, 0 < ε ∧ ε ≤ 1 / 4 ∧ 0 < τ ∧ ∃ r : ℕ, 0 < r ∧ ∃ J₀ : ℕ,
      ∀ J : ℕ, J₀ ≤ J → ∀ f : ZMod (2 ^ J) → ℂ,
      ∀ w : ℕ → (ZMod (2 ^ J))ˣ → ℝ,
        FiniteComplexProbability f →
        DyadicProbabilityNonconcentration γ ε (fun x => ‖f x‖) →
        (∀ n < r, ∀ u, 0 ≤ w n u) →
        (∀ n < r, (∑ u : (ZMod (2 ^ J))ˣ, w n u) = 1) →
        (∀ n < r, DyadicUnitProbabilityNonconcentration γ ε (w n)) →
        ∀ k : ZMod (2 ^ J), IsUnit k →
          ‖ZMod.dft (cyclicUnitProductIter f w r) k‖ ≤ (2 : ℝ) ^ (-τ * (J : ℝ)) := by
  let δ := min (γ / 2) (1 / 2)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδ1 : δ ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have hκ : 0 < γ - δ := by
    have hh : δ ≤ γ / 2 := min_le_left _ _
    linarith only [hh, hγ]
  obtain ⟨ε, hε, hε4, R, hR, J₀, hflat⟩ := exists_dyadic_probability_flattening_iteration hγ hδ hδ1
  let N := 2 ^ (R + 2)
  have hN : 0 < N := by dsimp only [N]; positivity
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  let τ := (γ - δ) / (N : ℝ)
  have hτ : 0 < τ := div_pos hκ hNR
  refine ⟨ε, τ, hε, hε4, hτ, R + 1, by omega, max J₀ 1, ?_⟩
  intro J hJ f w hf hspread hw hmass hwspread k hk
  have hJ₀ : J₀ ≤ J := (le_max_left _ _).trans hJ
  have hJpos : 0 < J := by have hh := (le_max_right J₀ 1).trans hJ; omega
  let ν := cyclicUnitAveragingIter (cyclicSymmetrize f) w R
  have henergy : (∑ x : ZMod (2 ^ J), ‖ν x‖ ^ 2) ≤ (2 : ℝ) ^ (-(1 - δ) * (J : ℝ)) :=
    hflat J hJ₀ (cyclicSymmetrize f) w (cyclic_symmetrize_probability hf)
      (dyadic_probability_nonconcentration_symmetrize hf hspread)
      (fun n hn => hw n (by omega)) (fun n hn => hmass n (by omega))
      (fun n hn => hwspread n (by omega))
  have hlast : ∀ u, w R u ≤ (2 : ℝ) ^ (-γ * (J : ℝ)) :=
    dyadic_unit_probability_point_bound (hw R (by omega)) (hwspread R (by omega))
      hJpos (by linarith only [hε4])
  have hbilinear : ‖ZMod.dft (cyclicMixture (w R) (cyclicUnitDilate ν)) k‖ ^ 2 ≤
      (2 : ℝ) ^ (-(γ - δ) * (J : ℝ)) := by
    calc
      _ ≤ ((2 ^ J : ℕ) : ℝ) * (2 : ℝ) ^ (-γ * (J : ℝ)) * ∑ x : ZMod (2 ^ J), ‖ν x‖ ^ 2 :=
        norm_dft_unit_mixture_sq_le ν (w R) (hw R (by omega)) (hmass R (by omega)) hlast hk
      _ ≤ ((2 ^ J : ℕ) : ℝ) * (2 : ℝ) ^ (-γ * (J : ℝ)) * (2 : ℝ) ^ (-(1 - δ) * (J : ℝ)) :=
        mul_le_mul_of_nonneg_left henergy (by positivity)
      _ = _ := by
        push_cast
        rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num)]
        congr 1
        ring
  have hpower : ‖ZMod.dft (cyclicUnitProductIter f w (R + 1)) k‖ ^ N ≤
      (2 : ℝ) ^ (-(γ - δ) * (J : ℝ)) := by
    have hh := pow_le_pow_left₀ (pow_nonneg (norm_nonneg _) _)
      (norm_dft_unit_product_final_power_le f w hf.norm_cast hw hmass k) 2
    have he : N = 2 ^ (R + 1) * 2 := by dsimp only [N]; rw [show R + 2 = R + 1 + 1 by omega, pow_succ]
    rw [he, pow_mul]
    exact hh.trans hbilinear
  apply (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) hN.ne').mp
  calc
    _ ≤ (2 : ℝ) ^ (-(γ - δ) * (J : ℝ)) := hpower
    _ = ((2 : ℝ) ^ (-τ * (J : ℝ))) ^ N := by
      rw [← Real.rpow_mul_natCast (by norm_num)]
      congr 1
      dsimp only [τ]
      field_simp



theorem finite_sum_units_eq {R M : Type*} [Monoid R] [Fintype R] [Fintype Rˣ]
    [AddCommMonoid M] (F : R → M) (hsupport : ∀ x, F x ≠ 0 → IsUnit x) :
    (∑ u : Rˣ, F (u : R)) = ∑ x : R, F x := by
  classical
  calc
    _ = ∑ x ∈ (Finset.univ : Finset Rˣ).image (fun u : Rˣ => (u : R)), F x := by
      symm
      exact Finset.sum_image (fun u _ v _ huv => Units.val_injective huv)
    _ = _ := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro x hx hxnot
      by_contra hzero
      obtain ⟨u, rfl⟩ := hsupport x hzero
      exact hxnot (Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩)

theorem finite_unit_fiber_mass_eq {R Q : Type*} [Monoid R] [Fintype R] [Fintype Rˣ]
    [DecidableEq Q] (p : R → ℝ) (π : R → Q)
    (hsupport : ∀ x, p x ≠ 0 → IsUnit x) (r : Q) :
    (∑ u ∈ Finset.univ.filter (fun u : Rˣ => π (u : R) = r), p (u : R)) =
      finitePushforward p π r := by
  simp only [finitePushforward, Finset.sum_filter]
  apply finite_sum_units_eq (fun x => if π x = r then p x else 0)
  intro x hx
  by_cases hxr : π x = r
  · exact hsupport x (by simpa only [if_pos hxr] using hx)
  · simp only [if_neg hxr, ne_eq, not_true_eq_false] at hx

theorem dyadic_unit_probability_nonconcentration_of_supported {J : ℕ} {γ ε : ℝ}
    {p : ZMod (2 ^ J) → ℝ} (hsupport : ∀ x, p x ≠ 0 → IsUnit x)
    (hspread : DyadicProbabilityNonconcentration γ ε p) :
    DyadicUnitProbabilityNonconcentration γ ε (fun u : (ZMod (2 ^ J))ˣ => p (u : ZMod (2 ^ J))) := by
  intro L hL hεL r
  have heq := finite_unit_fiber_mass_eq p (fun x : ZMod (2 ^ J) => (x.val : ZMod (2 ^ L))) hsupport r
  exact heq.trans_le (hspread L hL hεL r)

theorem cyclic_multiplicative_convolution_comm {q : ℕ} [NeZero q]
    (f g : ZMod q → ℂ) : cyclicMultiplicativeConvolution f g = cyclicMultiplicativeConvolution g f := by
  classical
  funext x
  unfold cyclicMultiplicativeConvolution cyclicPushforward
  apply Fintype.sum_equiv (Equiv.prodComm (ZMod q) (ZMod q))
  intro p
  rcases p with ⟨a, b⟩
  simp [mul_comm]

theorem cyclic_product_pow_one {q : ℕ} [NeZero q] (f : ZMod q → ℂ) :
    cyclicProductPow f 1 = f := by
  apply ZMod.dft.injective
  funext k
  rw [cyclicProductPow, dft_cyclicMultiplicativeConvolution]
  simp [cyclicProductPow, ite_mul]

theorem cyclic_mixture_units_eq_mulconv {q : ℕ} [NeZero q]
    (f g : ZMod q → ℂ) (hg : ∀ x, g x = (‖g x‖ : ℂ))
    (hsupport : ∀ x, g x ≠ 0 → IsUnit x) :
    cyclicMixture (fun u : (ZMod q)ˣ => ‖g (u : ZMod q)‖) (cyclicUnitDilate f) =
      cyclicMultiplicativeConvolution f g := by
  apply ZMod.dft.injective
  funext k
  rw [dft_cyclic_mixture, dft_cyclicMultiplicativeConvolution]
  calc
    _ = ∑ u : (ZMod q)ˣ, g (u : ZMod q) * ZMod.dft f ((u : ZMod q) * k) := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [dft_cyclic_unit_dilate, ← hg (u : ZMod q)]
    _ = _ := finite_sum_units_eq (fun x : ZMod q => g x * ZMod.dft f (x * k))
      (fun x hx => hsupport x (mul_ne_zero_iff.mp hx).1)

theorem cyclic_unit_product_iter_const {q : ℕ} [NeZero q]
    (f : ZMod q → ℂ) (hf : ∀ x, f x = (‖f x‖ : ℂ))
    (hsupport : ∀ x, f x ≠ 0 → IsUnit x) (r : ℕ) :
    cyclicUnitProductIter f (fun _ u => ‖f (u : ZMod q)‖) r = cyclicProductPow f (r + 1) := by
  induction r with
  | zero => exact (cyclic_product_pow_one f).symm
  | succ r ih =>
    rw [cyclicUnitProductIter, ih, cyclic_mixture_units_eq_mulconv _ f hf hsupport]
    exact cyclic_multiplicative_convolution_comm _ _

theorem cyclic_uniform_nat_set_complex_probability {q : ℕ} [NeZero q]
    {A : Finset ℕ} (hA : A.Nonempty) : FiniteComplexProbability (cyclicUniformNatSet (q := q) A) := by
  refine ⟨?_, ?_⟩
  · intro x
    rw [norm_cyclicUniformNatSet, cyclicUniformNatSet_eq_residue_mass]
  · simpa only [ZMod.dft_apply_zero] using dft_cyclicUniformNatSet_at_zero (q := q) hA

theorem dyadic_uniform_nat_set_probability_nonconcentration {J : ℕ} {γ ε : ℝ}
    (A : Finset ℕ) (hcutoff : 2 ≤ ε * (J : ℝ))
    (hspread : ∀ L : ℕ, 2 ≤ L → L ≤ J → ∀ x : ZMod (2 ^ L),
      ‖cyclicUniformNatSet A x‖ ≤ (2 : ℝ) ^ (-γ * (L : ℝ))) :
    DyadicProbabilityNonconcentration γ ε (fun x : ZMod (2 ^ J) => ‖cyclicUniformNatSet A x‖) := by
  intro L hL hεL r
  have hL2 : 2 ≤ L := by exact_mod_cast (hcutoff.trans_lt hεL).le
  let π : ZMod (2 ^ J) →+* ZMod (2 ^ L) := ZMod.castHom (pow_dvd_pow 2 hL) _
  have hπ : ∀ x : ZMod (2 ^ J), π x = (x.val : ZMod (2 ^ L)) := fun x => ZMod.cast_eq_val _
  have heq := congrFun (finite_pushforward_norm_cyclicUniformNatSet π A) r
  have hh := hspread L hL2 hL r
  rw [← heq] at hh
  simpa only [finitePushforward, hπ] using hh

theorem weighted_dyadic_mixing : WeightedDyadicMixing := by
  intro γ hγ hγhalf
  obtain ⟨ε, τ, hε, hε4, hτ, r, hr, J₀, hdecay⟩ := exists_dyadic_unit_product_fourier_decay hγ
  refine ⟨r + 1, τ, max J₀ ⌈2 / ε⌉₊, by omega, hτ, ?_⟩
  intro J hJ A hA hodd hspread a ha
  have hJ₀ : J₀ ≤ J := (le_max_left _ _).trans hJ
  have hJceil : ⌈2 / ε⌉₊ ≤ J := (le_max_right _ _).trans hJ
  have hcutoff : 2 ≤ ε * (J : ℝ) := by
    have hcast : (2 / ε : ℝ) ≤ J := (Nat.le_ceil _).trans (by exact_mod_cast hJceil)
    have hh := (div_le_iff₀ hε).mp hcast
    simpa only [mul_comm] using hh
  let f : ZMod (2 ^ J) → ℂ := cyclicUniformNatSet A
  let w : (ZMod (2 ^ J))ˣ → ℝ := fun u => ‖f (u : ZMod (2 ^ J))‖
  have hf : FiniteComplexProbability f := cyclic_uniform_nat_set_complex_probability hA
  have hsupport : ∀ x, ‖f x‖ ≠ 0 → IsUnit x := cyclicUniformNatSet_support_odd hodd J
  have hsupport' : ∀ x, f x ≠ 0 → IsUnit x := fun x hx => hsupport x (norm_ne_zero_iff.mpr hx)
  have hnonconcentration : DyadicProbabilityNonconcentration γ ε (fun x => ‖f x‖) :=
    dyadic_uniform_nat_set_probability_nonconcentration A hcutoff hspread
  have hw : ∀ u, 0 ≤ w u := fun _ => norm_nonneg _
  have hmass : ∑ u : (ZMod (2 ^ J))ˣ, w u = 1 := by
    rw [finite_sum_units_eq (fun x => ‖f x‖) hsupport]
    exact finite_complex_probability_sum_norm hf
  have hwspread : DyadicUnitProbabilityNonconcentration γ ε w :=
    dyadic_unit_probability_nonconcentration_of_supported hsupport hnonconcentration
  have hh := hdecay J hJ₀ f (fun _ => w) hf hnonconcentration (fun _ _ => hw)
    (fun _ _ => hmass) (fun _ _ => hwspread) (a : ZMod (2 ^ J)) (odd_natCast_isUnit_dyadic J ha)
  rw [cyclic_unit_product_iter_const f hf.norm_cast hsupport'] at hh
  exact hh

theorem target : fcTypeOfName% "Erdos18.erdos_18b" := by
  exact erdos18b_of_weighted_dyadic_mixing weighted_dyadic_mixing


