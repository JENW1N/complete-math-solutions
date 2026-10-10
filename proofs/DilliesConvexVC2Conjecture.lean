import Mathlib
import FormalConjecturesForMathlib.Combinatorics.Additive.VCDim
import FormalConjecturesForMathlib.Geometry.«3d»

/-!
# Dillies's convex VC₂ conjecture in three dimensions

Authors: Jensen Kohlmeyer and Liam Kruer.
Conjecture attribution: Yaël Dillies, Formal Conjectures PR #4657.
https://github.com/google-deepmind/formal-conjectures/pull/4657#discussion_r3669113366
AI assistance: OpenAI Codex assisted with proof exploration and formalization.

The target is `HasAddVCNDimAtMost C 2 2` for every convex `C : Set ℝ³`,
as stated in `FormalConjectures/Other/VCDimConvex.lean`.
-/

open scoped BigOperators EuclideanGeometry

namespace ConvexVC2Dimension

section Algebra

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Every pair of vertices has a common strict exposing functional. -/
def ExposedGrid (a b : Fin 3 → E) : Prop :=
  ∀ i j, ∃ f : E →ₗ[ℝ] ℝ,
    (∀ k, k ≠ i → f (a k) < f (a i)) ∧
    (∀ k, k ≠ j → f (b k) < f (b j))

theorem ExposedGrid.symm {a b : Fin 3 → E} (h : ExposedGrid a b) :
    ExposedGrid b a := by
  intro i j
  obtain ⟨f, ha, hb⟩ := h j i
  exact ⟨f, hb, ha⟩

theorem ExposedGrid.reindex {a b : Fin 3 → E} (h : ExposedGrid a b)
    (σ τ : Equiv.Perm (Fin 3)) : ExposedGrid (fun k => a (σ k)) (fun k => b (τ k)) := by
  intro i j
  obtain ⟨f, ha, hb⟩ := h (σ i) (τ j)
  refine ⟨f, ?_, ?_⟩
  · intro k hk
    exact ha (σ k) (fun he => hk (σ.injective he))
  · intro k hk
    exact hb (τ k) (fun he => hk (τ.injective he))

/-- All subsets of the additive three-by-three array are realized by translations. -/
def GridShattered (C : Set E) (a b : Fin 3 → E) : Prop :=
  ∀ S : Set (Fin 3 × Fin 3), ∃ t : E, ∀ i j,
    t + a i + b j ∈ C ↔ (i, j) ∈ S

omit [Module ℝ E] in
theorem GridShattered.reindex {C : Set E} {a b : Fin 3 → E}
    (h : GridShattered C a b) (σ τ : Equiv.Perm (Fin 3)) :
    GridShattered C (fun k => a (σ k)) (fun k => b (τ k)) := by
  intro S
  obtain ⟨t, ht⟩ := h {p | (σ.symm p.1, τ.symm p.2) ∈ S}
  refine ⟨t, ?_⟩
  intro i j
  simpa only [Set.mem_ofPred_eq, Equiv.symm_apply_apply] using ht (σ i) (τ j)

/-- Two affine relations cannot have their positive coefficients concentrated
at a commonly exposed pair unless both relations are trivial. -/
theorem relation_zero_of_same_side {a b : Fin 3 → E} (h : ExposedGrid a b)
    (α β : Fin 3 → ℝ) (hα : ∑ k, α k = 0) (hβ : ∑ k, β k = 0)
    (hrel : (∑ k, α k • a k) + (∑ k, β k • b k) = 0)
    (i j : Fin 3) (ha : ∀ k, k ≠ i → α k ≤ 0)
    (hb : ∀ k, k ≠ j → β k ≤ 0) :
    (∀ k, α k = 0) ∧ (∀ k, β k = 0) := by
  classical
  obtain ⟨f, hfa, hfb⟩ := h i j
  have hz : (∑ k, α k * (f (a k) - f (a i))) +
      (∑ k, β k * (f (b k) - f (b j))) = 0 := by
    have hf := congrArg f hrel
    simp only [map_add, map_sum, map_smul, map_zero, smul_eq_mul] at hf
    simpa only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
      hα, hβ, zero_mul, sub_zero] using hf
  have hpa : ∀ k ∈ (Finset.univ : Finset (Fin 3)),
      0 ≤ α k * (f (a k) - f (a i)) := by
    intro k _
    by_cases hk : k = i
    · subst k
      simp
    · exact mul_nonneg_of_nonpos_of_nonpos (ha k hk) (le_of_lt (sub_neg.mpr (hfa k hk)))
  have hpb : ∀ k ∈ (Finset.univ : Finset (Fin 3)),
      0 ≤ β k * (f (b k) - f (b j)) := by
    intro k _
    by_cases hk : k = j
    · subst k
      simp
    · exact mul_nonneg_of_nonpos_of_nonpos (hb k hk) (le_of_lt (sub_neg.mpr (hfb k hk)))
  have hsa : ∑ k, α k * (f (a k) - f (a i)) = 0 := by
    linarith [Finset.sum_nonneg hpa, Finset.sum_nonneg hpb]
  have hsb : ∑ k, β k * (f (b k) - f (b j)) = 0 := by
    linarith [Finset.sum_nonneg hpa, Finset.sum_nonneg hpb]
  have hza : ∀ k, k ≠ i → α k = 0 := by
    intro k hk
    have hp := (Finset.sum_eq_zero_iff_of_nonneg hpa).mp hsa k (Finset.mem_univ k)
    exact (mul_eq_zero.mp hp).resolve_right (ne_of_lt (sub_neg.mpr (hfa k hk)))
  have hzb : ∀ k, k ≠ j → β k = 0 := by
    intro k hk
    have hp := (Finset.sum_eq_zero_iff_of_nonneg hpb).mp hsb k (Finset.mem_univ k)
    exact (mul_eq_zero.mp hp).resolve_right (ne_of_lt (sub_neg.mpr (hfb k hk)))
  have hai : α i = 0 := by
    have hs : ∑ k, α k = α i :=
      Finset.sum_eq_single i (fun k _ hk => hza k hk) (by simp)
    exact hs.symm.trans hα
  have hbj : β j = 0 := by
    have hs : ∑ k, β k = β j :=
      Finset.sum_eq_single j (fun k _ hk => hzb k hk) (by simp)
    exact hs.symm.trans hβ
  constructor
  · intro k
    by_cases hk : k = i
    · simpa [hk] using hai
    · exact hza k hk
  · intro k
    by_cases hk : k = j
    · simpa [hk] using hbj
    · exact hzb k hk

theorem triple_one_sided (x : Fin 3 → ℝ) :
    (∃ i, ∀ k, k ≠ i → x k ≤ 0) ∨ (∃ i, ∀ k, k ≠ i → 0 ≤ x k) := by
  by_cases h0 : 0 ≤ x 0
  · by_cases h1 : 0 ≤ x 1
    · right
      refine ⟨2, ?_⟩
      intro k hk
      fin_cases k <;> simp_all
    · by_cases h2 : 0 ≤ x 2
      · right
        refine ⟨1, ?_⟩
        intro k hk
        fin_cases k <;> simp_all
      · left
        refine ⟨0, ?_⟩
        intro k hk
        fin_cases k <;> simp_all <;> linarith
  · by_cases h1 : 0 ≤ x 1
    · by_cases h2 : 0 ≤ x 2
      · right
        refine ⟨0, ?_⟩
        intro k hk
        fin_cases k <;> simp_all
      · left
        refine ⟨1, ?_⟩
        intro k hk
        fin_cases k <;> simp_all <;> linarith
    · left
      refine ⟨2, ?_⟩
      intro k hk
      fin_cases k <;> simp_all <;> linarith

theorem zero_entry_both_sides (x : Fin 3 → ℝ) (hs : ∑ k, x k = 0)
    (i : Fin 3) (hi : x i = 0) :
    (∃ j, ∀ k, k ≠ j → x k ≤ 0) ∧ (∃ j, ∀ k, k ≠ j → 0 ≤ x k) := by
  simp only [Fin.sum_univ_three] at hs
  fin_cases i
  · change x 0 = 0 at hi
    by_cases h : 0 ≤ x 1
    · have h2 : x 2 ≤ 0 := by linarith
      constructor
      · refine ⟨1, ?_⟩
        intro k hk
        fin_cases k <;> simp_all
      · refine ⟨2, ?_⟩
        intro k hk
        fin_cases k <;> simp_all
    · have h1 : x 1 ≤ 0 := by linarith
      have h2 : 0 ≤ x 2 := by linarith
      constructor
      · refine ⟨2, ?_⟩
        intro k hk
        fin_cases k <;> simp_all
      · refine ⟨1, ?_⟩
        intro k hk
        fin_cases k <;> simp_all
  · change x 1 = 0 at hi
    by_cases h : 0 ≤ x 0
    · have h2 : x 2 ≤ 0 := by linarith
      constructor
      · refine ⟨0, ?_⟩
        intro k hk
        fin_cases k <;> simp_all
      · refine ⟨2, ?_⟩
        intro k hk
        fin_cases k <;> simp_all
    · have h0 : x 0 ≤ 0 := by linarith
      have h2 : 0 ≤ x 2 := by linarith
      constructor
      · refine ⟨2, ?_⟩
        intro k hk
        fin_cases k <;> simp_all
      · refine ⟨0, ?_⟩
        intro k hk
        fin_cases k <;> simp_all
  · change x 2 = 0 at hi
    by_cases h : 0 ≤ x 0
    · have h1 : x 1 ≤ 0 := by linarith
      constructor
      · refine ⟨0, ?_⟩
        intro k hk
        fin_cases k <;> simp_all
      · refine ⟨1, ?_⟩
        intro k hk
        fin_cases k <;> simp_all
    · have h0 : x 0 ≤ 0 := by linarith
      have h1 : 0 ≤ x 1 := by linarith
      constructor
      · refine ⟨1, ?_⟩
        intro k hk
        fin_cases k <;> simp_all
      · refine ⟨0, ?_⟩
        intro k hk
        fin_cases k <;> simp_all

theorem relation_zero_of_zero_entry {a b : Fin 3 → E} (h : ExposedGrid a b)
    (α β : Fin 3 → ℝ) (hα : ∑ k, α k = 0) (hβ : ∑ k, β k = 0)
    (hrel : (∑ k, α k • a k) + (∑ k, β k • b k) = 0)
    (i : Fin 3) (hi : α i = 0) :
    (∀ k, α k = 0) ∧ (∀ k, β k = 0) := by
  obtain ⟨⟨j, hj⟩, ⟨j', hj'⟩⟩ := zero_entry_both_sides α hα i hi
  rcases triple_one_sided β with ⟨k, hk⟩ | ⟨k, hk⟩
  · exact relation_zero_of_same_side h α β hα hβ hrel j k hj hk
  · have hnegα : ∑ k, -α k = 0 := by simp [Finset.sum_neg_distrib, hα]
    have hnegβ : ∑ k, -β k = 0 := by simp [Finset.sum_neg_distrib, hβ]
    have hnegrel : (∑ k, (-α k) • a k) + (∑ k, (-β k) • b k) = 0 := by
      simp only [neg_smul, Finset.sum_neg_distrib, ← neg_add, hrel, neg_zero]
    obtain ⟨hza, hzb⟩ := relation_zero_of_same_side h (fun k => -α k) (fun k => -β k)
      hnegα hnegβ hnegrel j' k (fun l hl => neg_nonpos.mpr (hj' l hl))
      (fun l hl => neg_nonpos.mpr (hk l hl))
    exact ⟨fun l => neg_eq_zero.mp (hza l), fun l => neg_eq_zero.mp (hzb l)⟩

theorem relation_zero_of_same_nonneg {a b : Fin 3 → E} (h : ExposedGrid a b)
    (α β : Fin 3 → ℝ) (hα : ∑ k, α k = 0) (hβ : ∑ k, β k = 0)
    (hrel : (∑ k, α k • a k) + (∑ k, β k • b k) = 0)
    (i j : Fin 3) (ha : ∀ k, k ≠ i → 0 ≤ α k)
    (hb : ∀ k, k ≠ j → 0 ≤ β k) :
    (∀ k, α k = 0) ∧ (∀ k, β k = 0) := by
  have hnegα : ∑ k, -α k = 0 := by simp [Finset.sum_neg_distrib, hα]
  have hnegβ : ∑ k, -β k = 0 := by simp [Finset.sum_neg_distrib, hβ]
  have hnegrel : (∑ k, (-α k) • a k) + (∑ k, (-β k) • b k) = 0 := by
    simp only [neg_smul, Finset.sum_neg_distrib, ← neg_add, hrel, neg_zero]
  obtain ⟨hza, hzb⟩ := relation_zero_of_same_side h (fun k => -α k) (fun k => -β k)
    hnegα hnegβ hnegrel i j (fun l hl => neg_nonpos.mpr (ha l hl))
    (fun l hl => neg_nonpos.mpr (hb l hl))
  exact ⟨fun l => neg_eq_zero.mp (hza l), fun l => neg_eq_zero.mp (hzb l)⟩

theorem relation_entries_ne_zero {a b : Fin 3 → E} (h : ExposedGrid a b)
    (α β : Fin 3 → ℝ) (hα : ∑ k, α k = 0) (hβ : ∑ k, β k = 0)
    (hrel : (∑ k, α k • a k) + (∑ k, β k • b k) = 0)
    (hn : ¬ ((∀ k, α k = 0) ∧ (∀ k, β k = 0))) :
    ∀ k, α k ≠ 0 ∧ β k ≠ 0 := by
  intro k
  constructor
  · intro hk
    exact hn (relation_zero_of_zero_entry h α β hα hβ hrel k hk)
  · intro hk
    have hrel' : (∑ k, β k • b k) + (∑ k, α k • a k) = 0 := by
      simpa only [add_comm] using hrel
    obtain ⟨hzb, hza⟩ := relation_zero_of_zero_entry h.symm β α hβ hα hrel' k hk
    exact hn ⟨hza, hzb⟩

/-- Two directions from one triangle and any edge of the other are independent. -/
theorem exposed_three_independent {a b : Fin 3 → E} (h : ExposedGrid a b) :
    LinearIndependent ℝ ![a 1 - a 0, a 2 - a 0, b 1 - b 0] := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc k
  let α : Fin 3 → ℝ := ![-c 0 - c 1, c 0, c 1]
  let β : Fin 3 → ℝ := ![-c 2, c 2, 0]
  have hα : ∑ l, α l = 0 := by simp [α, Fin.sum_univ_three]; ring
  have hβ : ∑ l, β l = 0 := by simp [β, Fin.sum_univ_three]
  have hrel : (∑ l, α l • a l) + (∑ l, β l • b l) = 0 := by
    calc
      _ = ∑ l, c l • (![a 1 - a 0, a 2 - a 0, b 1 - b 0] : Fin 3 → E) l := by
        simp [α, β, Fin.sum_univ_three]
        module
      _ = 0 := hc
  obtain ⟨hzb, hza⟩ := relation_zero_of_zero_entry h.symm β α hβ hα
    (by simpa only [add_comm] using hrel) 2 (by simp [β])
  have hc0 : c 0 = 0 := by simpa [α] using hza 1
  have hc1 : c 1 = 0 := by simpa [α] using hza 2
  have hc2 : c 2 = 0 := by simpa [β] using hzb 1
  fin_cases k <;> assumption

/-- The signed affine relation determines the canonical three real parameters. -/
theorem parameters_from_relation (a b : Fin 3 → E) (α β : Fin 3 → ℝ)
    (hα : ∑ k, α k = 0) (hβ : ∑ k, β k = 0)
    (hrel : (∑ k, α k • a k) + (∑ k, β k • b k) = 0)
    (ha1 : 0 < α 1) (ha2 : 0 < α 2)
    (hb0 : β 0 < 0) (hb1 : β 1 < 0) (hb2 : 0 < β 2) :
    ∃ u v w : ℝ, u < 0 ∧ v < 0 ∧ 0 < w ∧ w < 1 ∧
      b 2 - b 0 = u • (a 1 - a 0) + v • (a 2 - a 0) + w • (b 1 - b 0) := by
  let u := -α 1 / β 2
  let v := -α 2 / β 2
  let w := -β 1 / β 2
  have hb2ne : β 2 ≠ 0 := ne_of_gt hb2
  have hu : β 2 * u = -α 1 := by dsimp [u]; field_simp
  have hv : β 2 * v = -α 2 := by dsimp [v]; field_simp
  have hw : β 2 * w = -β 1 := by dsimp [w]; field_simp
  simp only [Fin.sum_univ_three] at hα hβ
  have ha0 : α 0 = -α 1 - α 2 := by linarith
  have hb0eq : β 0 = -β 1 - β 2 := by linarith
  refine ⟨u, v, w, ?_, ?_, ?_, ?_, ?_⟩
  · exact div_neg_of_neg_of_pos (neg_neg_of_pos ha1) hb2
  · exact div_neg_of_neg_of_pos (neg_neg_of_pos ha2) hb2
  · exact div_pos (neg_pos.mpr hb1) hb2
  · change -β 1 / β 2 < 1
    apply (div_lt_one hb2).mpr
    linarith
  · have hzero : β 2 • ((b 2 - b 0) -
        (u • (a 1 - a 0) + v • (a 2 - a 0) + w • (b 1 - b 0))) = 0 := by
      calc
        _ = (∑ k, α k • a k) + (∑ k, β k • b k) := by
          simp only [Fin.sum_univ_three, smul_sub, smul_add, smul_smul, hu, hv, hw]
          rw [ha0, hb0eq]
          module
        _ = 0 := hrel
    exact sub_eq_zero.mp ((smul_eq_zero.mp hzero).resolve_left hb2ne)

theorem normal_form_of_affine_relation {a b : Fin 3 → E} (h : ExposedGrid a b)
    (α β : Fin 3 → ℝ) (hα : ∑ k, α k = 0) (hβ : ∑ k, β k = 0)
    (hrel : (∑ k, α k • a k) + (∑ k, β k • b k) = 0)
    (hn : ¬ ((∀ k, α k = 0) ∧ (∀ k, β k = 0)))
    (i : Fin 3) (hi : ∀ k, k ≠ i → 0 ≤ α k) :
    ∃ (σ τ : Equiv.Perm (Fin 3)) (u v w : ℝ),
      u < 0 ∧ v < 0 ∧ 0 < w ∧ w < 1 ∧
      b (τ 2) - b (τ 0) = u • (a (σ 1) - a (σ 0)) +
        v • (a (σ 2) - a (σ 0)) + w • (b (τ 1) - b (τ 0)) := by
  classical
  rcases triple_one_sided β with ⟨j, hj⟩ | ⟨j, hj⟩
  · let σ := Equiv.swap (0 : Fin 3) i
    let τ := Equiv.swap (2 : Fin 3) j
    have hσ : σ 0 = i := Equiv.swap_apply_left _ _
    have hτ : τ 2 = j := Equiv.swap_apply_left _ _
    have hneσ : ∀ k, k ≠ 0 → σ k ≠ i := by
      intro k hk he
      exact hk (σ.injective (he.trans hσ.symm))
    have hneτ : ∀ k, k ≠ 2 → τ k ≠ j := by
      intro k hk he
      exact hk (τ.injective (he.trans hτ.symm))
    have hne := relation_entries_ne_zero h α β hα hβ hrel hn
    have ha1 : 0 < α (σ 1) :=
      lt_of_le_of_ne (hi _ (hneσ 1 (by decide))) (Ne.symm (hne _).1)
    have ha2 : 0 < α (σ 2) :=
      lt_of_le_of_ne (hi _ (hneσ 2 (by decide))) (Ne.symm (hne _).1)
    have hb0 : β (τ 0) < 0 :=
      lt_of_le_of_ne (hj _ (hneτ 0 (by decide))) (hne _).2
    have hb1 : β (τ 1) < 0 :=
      lt_of_le_of_ne (hj _ (hneτ 1 (by decide))) (hne _).2
    have hsα : ∑ k, α (σ k) = 0 := (Equiv.sum_comp σ α).trans hα
    have hsβ : ∑ k, β (τ k) = 0 := (Equiv.sum_comp τ β).trans hβ
    have hb2 : 0 < β (τ 2) := by
      simp only [Fin.sum_univ_three] at hsβ
      linarith
    have hr : (∑ k, α (σ k) • a (σ k)) + (∑ k, β (τ k) • b (τ k)) = 0 := by
      rw [Equiv.sum_comp σ (fun k => α k • a k), Equiv.sum_comp τ (fun k => β k • b k)]
      exact hrel
    obtain ⟨u, v, w, hu, hv, hw0, hw1, hform⟩ := parameters_from_relation
      (fun k => a (σ k)) (fun k => b (τ k)) (fun k => α (σ k)) (fun k => β (τ k))
      hsα hsβ hr ha1 ha2 hb0 hb1 hb2
    exact ⟨σ, τ, u, v, w, hu, hv, hw0, hw1, hform⟩
  · exact (hn (relation_zero_of_same_nonneg h α β hα hβ hrel i j hi hj)).elim

end Algebra

/-- Four difference vectors in three dimensions give a nontrivial two-block
affine relation. The coefficient sums vanish separately in both blocks. -/
theorem exists_affine_relation (a b : Fin 3 → ℝ³) :
    ∃ α β : Fin 3 → ℝ, (∑ k, α k = 0) ∧ (∑ k, β k = 0) ∧
      (∑ k, α k • a k) + (∑ k, β k • b k) = 0 ∧
      ¬ ((∀ k, α k = 0) ∧ (∀ k, β k = 0)) := by
  classical
  let v : Fin 4 → ℝ³ := ![a 1 - a 0, a 2 - a 0, b 1 - b 0, b 2 - b 0]
  have hn : ¬ LinearIndependent ℝ v := by
    intro h
    have hd := h.fintype_card_le_finrank
    norm_num [finrank_euclideanSpace] at hd
  obtain ⟨c, hc, k, hk⟩ := Fintype.not_linearIndependent_iff.mp hn
  let α : Fin 3 → ℝ := ![-c 0 - c 1, c 0, c 1]
  let β : Fin 3 → ℝ := ![-c 2 - c 3, c 2, c 3]
  refine ⟨α, β, ?_, ?_, ?_, ?_⟩
  · simp [α, Fin.sum_univ_three]
    ring
  · simp [β, Fin.sum_univ_three]
    ring
  · calc
      _ = ∑ l, c l • v l := by
        simp [α, β, v, Fin.sum_univ_three, Fin.sum_univ_four]
        module
      _ = 0 := hc
  · rintro ⟨hα, hβ⟩
    have hc0 : c 0 = 0 := by simpa [α] using hα 1
    have hc1 : c 1 = 0 := by simpa [α] using hα 2
    have hc2 : c 2 = 0 := by simpa [β] using hβ 1
    have hc3 : c 3 = 0 := by simpa [β] using hβ 2
    fin_cases k <;> contradiction

/-- The normal-form relation is forced by the nine exposed sums; no
nondegeneracy or spanning hypothesis is added. -/
theorem exposed_normal_form {a b : Fin 3 → ℝ³} (h : ExposedGrid a b) :
    ∃ (σ τ : Equiv.Perm (Fin 3)) (u v w : ℝ),
      u < 0 ∧ v < 0 ∧ 0 < w ∧ w < 1 ∧
      b (τ 2) - b (τ 0) = u • (a (σ 1) - a (σ 0)) +
        v • (a (σ 2) - a (σ 0)) + w • (b (τ 1) - b (τ 0)) := by
  obtain ⟨α, β, hα, hβ, hrel, hn⟩ := exists_affine_relation a b
  rcases triple_one_sided α with ⟨i, hi⟩ | ⟨i, hi⟩
  · have hnegα : ∑ k, -α k = 0 := by simp [Finset.sum_neg_distrib, hα]
    have hnegβ : ∑ k, -β k = 0 := by simp [Finset.sum_neg_distrib, hβ]
    have hnegrel : (∑ k, (-α k) • a k) + (∑ k, (-β k) • b k) = 0 := by
      simp only [neg_smul, Finset.sum_neg_distrib, ← neg_add, hrel, neg_zero]
    have hn' : ¬ ((∀ k, -α k = 0) ∧ (∀ k, -β k = 0)) := by
      rintro ⟨ha, hb⟩
      exact hn ⟨fun k => neg_eq_zero.mp (ha k), fun k => neg_eq_zero.mp (hb k)⟩
    exact normal_form_of_affine_relation h (fun k => -α k) (fun k => -β k)
      hnegα hnegβ hnegrel hn' i (fun k hk => neg_nonneg.mpr (hi k hk))
  · exact normal_form_of_affine_relation h α β hα hβ hrel hn i hi

/-- Separate an excluded point strictly from finitely many included points. -/
theorem finite_separator {C : Set ℝ³} (hC : Convex ℝ C) {s : Set ℝ³}
    (hs : s.Finite) (hsub : s ⊆ C) {q : ℝ³} (hq : q ∉ C) :
    ∃ f : ℝ³ →ₗ[ℝ] ℝ, ∀ p ∈ s, f p < f q := by
  have hHull : convexHull ℝ s ⊆ C := convexHull_min hsub hC
  have hnot : q ∉ convexHull ℝ s := fun hq' => hq (hHull hq')
  have hcompact := hs.isCompact_convexHull ℝ
  obtain ⟨f, c, hf, hc⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ s) hcompact.isClosed hnot
  refine ⟨f.toLinearMap, ?_⟩
  intro p hp
  exact (hf p (subset_convexHull ℝ s hp)).trans hc

theorem GridShattered.exposed {C : Set ℝ³} (hC : Convex ℝ C)
    {a b : Fin 3 → ℝ³} (h : GridShattered C a b) : ExposedGrid a b := by
  classical
  intro i j
  obtain ⟨t, ht⟩ := h {p | p ≠ (i, j)}
  let s : Set ℝ³ := (fun p : Fin 3 × Fin 3 => t + a p.1 + b p.2) '' {p | p ≠ (i, j)}
  have hs : s.Finite := (Set.toFinite _).image _
  have hsub : s ⊆ C := by
    rintro p ⟨⟨k, l⟩, hkl, rfl⟩
    exact (ht k l).mpr hkl
  have hnot : t + a i + b j ∉ C := by
    intro hc
    exact (ht i j).mp hc rfl
  obtain ⟨f, hf⟩ := finite_separator hC hs hsub hnot
  refine ⟨f, ?_, ?_⟩
  · intro k hk
    have hkj : (k, j) ≠ (i, j) := fun he => hk (congrArg Prod.fst he)
    have hc := hf (t + a k + b j) ⟨(k, j), hkj, rfl⟩
    simp only [map_add] at hc
    linarith
  · intro k hk
    have hik : (i, k) ≠ (i, j) := fun he => hk (congrArg Prod.snd he)
    have hc := hf (t + a i + b k) ⟨(i, k), hik, rfl⟩
    simp only [map_add] at hc
    linarith

/-- An affine function cannot put bottom/top strip points on its positive
side and right/left strip points on its negative side. -/
theorem cross_strip_impossible (x y : Fin 4 → ℝ) (α β γ : ℝ)
    (hbottom : 0 < x 0 ∧ x 0 < 1 ∧ y 0 < 0)
    (htop : 0 < x 1 ∧ x 1 < 1 ∧ 1 < y 1)
    (hright : 1 < x 2 ∧ 0 < y 2 ∧ y 2 < 1)
    (hleft : x 3 < 0 ∧ 0 < y 3 ∧ y 3 < 1)
    (h0 : 0 < α * x 0 + β * y 0 + γ)
    (h1 : 0 < α * x 1 + β * y 1 + γ)
    (h2 : α * x 2 + β * y 2 + γ < 0)
    (h3 : α * x 3 + β * y 3 + γ < 0) : False := by
  obtain ⟨hb0, hb1, hb2⟩ := hbottom
  obtain ⟨ht0, ht1, ht2⟩ := htop
  obtain ⟨hr0, hr1, hr2⟩ := hright
  obtain ⟨hl0, hl1, hl2⟩ := hleft
  by_cases ha : 0 ≤ α
  · by_cases hb : 0 ≤ β
    · have hx : 0 ≤ α * (x 2 - x 0) := mul_nonneg ha (by linarith)
      have hy : 0 ≤ β * (y 2 - y 0) := mul_nonneg hb (by linarith)
      nlinarith only [h0, h2, hx, hy]
    · have hx : 0 ≤ α * (x 2 - x 1) := mul_nonneg ha (by linarith)
      have hy : 0 ≤ β * (y 2 - y 1) :=
        mul_nonneg_of_nonpos_of_nonpos (le_of_not_ge hb) (by linarith)
      nlinarith only [h1, h2, hx, hy]
  · by_cases hb : 0 ≤ β
    · have hx : 0 ≤ α * (x 3 - x 0) :=
        mul_nonneg_of_nonpos_of_nonpos (le_of_not_ge ha) (by linarith)
      have hy : 0 ≤ β * (y 3 - y 0) := mul_nonneg hb (by linarith)
      nlinarith only [h0, h3, hx, hy]
    · have hx : 0 ≤ α * (x 3 - x 1) :=
        mul_nonneg_of_nonpos_of_nonpos (le_of_not_ge ha) (by linarith)
      have hy : 0 ≤ β * (y 3 - y 1) :=
        mul_nonneg_of_nonpos_of_nonpos (le_of_not_ge hb) (by linarith)
      nlinarith only [h1, h3, hx, hy]

/-- The canonical normal plane and translation signs are incompatible. -/
theorem normalized_normal_obstruction (u v w D₁ D₂ D₃ : ℝ)
    (hu : u < 0) (hv : v < 0) (hw0 : 0 < w) (hw1 : w < 1)
    (p q r : Fin 4 → ℝ) (hslice : ∀ i, u * p i + v * q i = 1)
    (hp0 : p 0 < 0) (hq0 : q 0 < 0) (hr0 : 1 + w * r 0 < 0)
    (hp1 : p 1 < 0) (hq1 : q 1 < 0) (hr1 : 1 - (1 - w) * r 1 < 0)
    (hp2 : 0 < p 2) (hr20 : 0 < 1 + w * r 2) (hr21 : 0 < 1 - (1 - w) * r 2)
    (hq3 : 0 < q 3) (hr30 : 0 < 1 + w * r 3) (hr31 : 0 < 1 - (1 - w) * r 3)
    (hd0 : 0 < D₁ * p 0 + D₂ * q 0 + D₃ * r 0)
    (hd1 : 0 < D₁ * p 1 + D₂ * q 1 + D₃ * r 1)
    (hd2 : D₁ * p 2 + D₂ * q 2 + D₃ * r 2 < 0)
    (hd3 : D₁ * p 3 + D₂ * q 3 + D₃ * r 3 < 0) : False := by
  let x : Fin 4 → ℝ := fun i => v * q i
  let y : Fin 4 → ℝ := fun i => w * (1 - w) * r i + 1 - w
  have hwm : 0 < 1 - w := by linarith
  have hu0 : u ≠ 0 := ne_of_lt hu
  have hv0 : v ≠ 0 := ne_of_lt hv
  have hwne : w ≠ 0 := ne_of_gt hw0
  have hwmne : 1 - w ≠ 0 := ne_of_gt hwm
  have hden : w * (1 - w) ≠ 0 := mul_ne_zero hwne hwmne
  have hbottom : 0 < x 0 ∧ x 0 < 1 ∧ y 0 < 0 := by
    refine ⟨mul_pos_of_neg_of_neg hv hq0, ?_, ?_⟩
    · dsimp [x]
      nlinarith only [hslice 0, mul_pos_of_neg_of_neg hu hp0]
    · dsimp [y]
      nlinarith only [mul_neg_of_pos_of_neg hwm hr0]
  have htop : 0 < x 1 ∧ x 1 < 1 ∧ 1 < y 1 := by
    refine ⟨mul_pos_of_neg_of_neg hv hq1, ?_, ?_⟩
    · dsimp [x]
      nlinarith only [hslice 1, mul_pos_of_neg_of_neg hu hp1]
    · dsimp [y]
      nlinarith only [mul_neg_of_pos_of_neg hw0 hr1]
  have hright : 1 < x 2 ∧ 0 < y 2 ∧ y 2 < 1 := by
    constructor
    · dsimp [x]
      nlinarith only [hslice 2, mul_neg_of_neg_of_pos hu hp2]
    · constructor
      · dsimp [y]
        nlinarith only [mul_pos hwm hr20]
      · dsimp [y]
        nlinarith only [mul_pos hw0 hr21]
  have hleft : x 3 < 0 ∧ 0 < y 3 ∧ y 3 < 1 := by
    constructor
    · exact mul_neg_of_neg_of_pos hv hq3
    · constructor
      · dsimp [y]
        nlinarith only [mul_pos hwm hr30]
      · dsimp [y]
        nlinarith only [mul_pos hw0 hr31]
  let α := D₂ / v - D₁ / u
  let β := D₃ / (w * (1 - w))
  let γ := D₁ / u - D₃ / w
  have hpi : ∀ i, p i = (1 - x i) / u := by
    intro i
    apply (eq_div_iff hu0).mpr
    dsimp [x]
    nlinarith only [hslice i]
  have hqi : ∀ i, q i = x i / v := by
    intro i
    apply (eq_div_iff hv0).mpr
    dsimp [x]
    ring
  have hri : ∀ i, r i = (y i - 1 + w) / (w * (1 - w)) := by
    intro i
    apply (eq_div_iff hden).mpr
    dsimp [y]
    ring
  have heval : ∀ i, D₁ * p i + D₂ * q i + D₃ * r i = α * x i + β * y i + γ := by
    intro i
    calc
      _ = D₁ * ((1 - x i) / u) + D₂ * (x i / v) +
          D₃ * ((y i - 1 + w) / (w * (1 - w))) := by rw [hpi i, hqi i, hri i]
      _ = _ := by
        dsimp [α, β, γ]
        field_simp
        ring
  exact cross_strip_impossible x y α β γ hbottom htop hright hleft
    (by simpa only [← heval 0] using hd0) (by simpa only [← heval 1] using hd1)
    (by simpa only [← heval 2] using hd2) (by simpa only [← heval 3] using hd3)

/-- Positive normalization reduces the original separating inequalities to
the affine normal-plane obstruction. -/
theorem raw_normal_obstruction (u v w D₁ D₂ D₃ : ℝ)
    (hu : u < 0) (hv : v < 0) (hw0 : 0 < w) (hw1 : w < 1)
    (P Q R : Fin 4 → ℝ)
    (hp0 : P 0 < 0) (hq0 : Q 0 < 0) (hr0 : u * P 0 + v * Q 0 + w * R 0 < 0)
    (hp1 : P 1 < 0) (hq1 : Q 1 < 0) (hr1 : u * P 1 + v * Q 1 - (1 - w) * R 1 < 0)
    (hp2 : 0 < P 2) (hr20 : 0 < u * P 2 + v * Q 2 + w * R 2)
    (hr21 : 0 < u * P 2 + v * Q 2 - (1 - w) * R 2)
    (hq3 : 0 < Q 3) (hr30 : 0 < u * P 3 + v * Q 3 + w * R 3)
    (hr31 : 0 < u * P 3 + v * Q 3 - (1 - w) * R 3)
    (hd0 : 0 < D₁ * P 0 + D₂ * Q 0 + D₃ * R 0)
    (hd1 : 0 < D₁ * P 1 + D₂ * Q 1 + D₃ * R 1)
    (hd2 : D₁ * P 2 + D₂ * Q 2 + D₃ * R 2 < 0)
    (hd3 : D₁ * P 3 + D₂ * Q 3 + D₃ * R 3 < 0) : False := by
  let c : Fin 4 → ℝ := fun i => u * P i + v * Q i
  have hwm : 0 < 1 - w := by linarith
  have hc : ∀ i, 0 < c i := by
    intro i
    fin_cases i
    · change 0 < u * P 0 + v * Q 0
      exact add_pos (mul_pos_of_neg_of_neg hu hp0) (mul_pos_of_neg_of_neg hv hq0)
    · change 0 < u * P 1 + v * Q 1
      exact add_pos (mul_pos_of_neg_of_neg hu hp1) (mul_pos_of_neg_of_neg hv hq1)
    · change 0 < u * P 2 + v * Q 2
      nlinarith only [mul_pos hwm hr20, mul_pos hw0 hr21]
    · change 0 < u * P 3 + v * Q 3
      nlinarith only [mul_pos hwm hr30, mul_pos hw0 hr31]
  let p : Fin 4 → ℝ := fun i => P i / c i
  let q : Fin 4 → ℝ := fun i => Q i / c i
  let r : Fin 4 → ℝ := fun i => R i / c i
  have hslice : ∀ i, u * p i + v * q i = 1 := by
    intro i
    calc
      _ = (u * P i + v * Q i) / c i := by dsimp [p, q]; ring
      _ = c i / c i := rfl
      _ = 1 := div_self (ne_of_gt (hc i))
  have he0 : ∀ i, 1 + w * r i = (c i + w * R i) / c i := by
    intro i
    dsimp [r]
    field_simp [ne_of_gt (hc i)]
  have he1 : ∀ i, 1 - (1 - w) * r i = (c i - (1 - w) * R i) / c i := by
    intro i
    dsimp [r]
    field_simp [ne_of_gt (hc i)]
  have hed : ∀ i, D₁ * p i + D₂ * q i + D₃ * r i =
      (D₁ * P i + D₂ * Q i + D₃ * R i) / c i := by
    intro i
    dsimp [p, q, r]
    ring
  apply normalized_normal_obstruction u v w D₁ D₂ D₃ hu hv hw0 hw1 p q r hslice
  · exact div_neg_of_neg_of_pos hp0 (hc 0)
  · exact div_neg_of_neg_of_pos hq0 (hc 0)
  · rw [he0 0]
    exact div_neg_of_neg_of_pos hr0 (hc 0)
  · exact div_neg_of_neg_of_pos hp1 (hc 1)
  · exact div_neg_of_neg_of_pos hq1 (hc 1)
  · rw [he1 1]
    exact div_neg_of_neg_of_pos hr1 (hc 1)
  · exact div_pos hp2 (hc 2)
  · rw [he0 2]
    exact div_pos hr20 (hc 2)
  · rw [he1 2]
    exact div_pos hr21 (hc 2)
  · exact div_pos hq3 (hc 3)
  · rw [he0 3]
    exact div_pos hr30 (hc 3)
  · rw [he1 3]
    exact div_pos hr31 (hc 3)
  · rw [hed 0]
    exact div_pos hd0 (hc 0)
  · rw [hed 1]
    exact div_pos hd1 (hc 1)
  · rw [hed 2]
    exact div_neg_of_neg_of_pos hd2 (hc 2)
  · rw [hed 3]
    exact div_neg_of_neg_of_pos hd3 (hc 3)

/-- The two patterns omitting `(0,0),(0,1)` and `(1,2),(2,2)` cannot coexist
on a grid with the forced canonical relation. -/
theorem canonical_grid_not_shattered {C : Set ℝ³} (hC : Convex ℝ C)
    {a b : Fin 3 → ℝ³} (h : GridShattered C a b) (u v w : ℝ)
    (hu : u < 0) (hv : v < 0) (hw0 : 0 < w) (hw1 : w < 1)
    (hform : b 2 - b 0 = u • (a 1 - a 0) + v • (a 2 - a 0) + w • (b 1 - b 0)) :
    False := by
  classical
  let S : Set (Fin 3 × Fin 3) := {p | p ≠ (0, 0) ∧ p ≠ (0, 1)}
  let T : Set (Fin 3 × Fin 3) := {p | p ≠ (1, 2) ∧ p ≠ (2, 2)}
  obtain ⟨t, ht⟩ := h S
  obtain ⟨z, hz⟩ := h T
  let s : Set ℝ³ := ((fun p : Fin 3 × Fin 3 => t + a p.1 + b p.2) '' S) ∪
    ((fun p : Fin 3 × Fin 3 => z + a p.1 + b p.2) '' T)
  have hs : s.Finite := ((Set.toFinite S).image _).union ((Set.toFinite T).image _)
  have hsub : s ⊆ C := by
    intro p hp
    rcases hp with ⟨⟨i, j⟩, hij, rfl⟩ | ⟨⟨i, j⟩, hij, rfl⟩
    · exact (ht i j).mpr hij
    · exact (hz i j).mpr hij
  have hS : ∀ i j, (i, j) ∈ S → t + a i + b j ∈ s := by
    intro i j hij
    exact Or.inl ⟨(i, j), hij, rfl⟩
  have hT : ∀ i j, (i, j) ∈ T → z + a i + b j ∈ s := by
    intro i j hij
    exact Or.inr ⟨(i, j), hij, rfl⟩
  have hnot0 : t + a 0 + b 0 ∉ C := by simpa [S] using ht 0 0
  have hnot1 : t + a 0 + b 1 ∉ C := by simpa [S] using ht 0 1
  have hnot2 : z + a 1 + b 2 ∉ C := by simpa [T] using hz 1 2
  have hnot3 : z + a 2 + b 2 ∉ C := by simpa [T] using hz 2 2
  obtain ⟨f₀, hf₀⟩ := finite_separator hC hs hsub hnot0
  obtain ⟨f₁, hf₁⟩ := finite_separator hC hs hsub hnot1
  obtain ⟨f₂, hf₂⟩ := finite_separator hC hs hsub hnot2
  obtain ⟨f₃, hf₃⟩ := finite_separator hC hs hsub hnot3
  let f : Fin 4 → (ℝ³ →ₗ[ℝ] ℝ) := ![f₀, f₁, f₂, f₃]
  let P : Fin 4 → ℝ := fun i => f i (a 1 - a 0)
  let Q : Fin 4 → ℝ := fun i => f i (a 2 - a 0)
  let R : Fin 4 → ℝ := fun i => f i (b 1 - b 0)
  have hB : ∀ i, f i (b 2 - b 0) = u * P i + v * Q i + w * R i := by
    intro i
    rw [hform]
    simp only [map_add, map_smul, smul_eq_mul, P, Q, R]
  let V : Fin 3 → ℝ³ := ![a 1 - a 0, a 2 - a 0, b 1 - b 0]
  have hli : LinearIndependent ℝ V := exposed_three_independent (h.exposed hC)
  have hspan : Submodule.span ℝ (Set.range V) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank (by simp [finrank_euclideanSpace])
  have hdmem : t - z ∈ Submodule.span ℝ (Set.range V) := by rw [hspan]; trivial
  obtain ⟨D, hD⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hdmem
  have heval : ∀ i, D 0 * P i + D 1 * Q i + D 2 * R i = f i (t - z) := by
    intro i
    have hd := congrArg (f i) hD
    simpa [Fin.sum_univ_three, V, map_smul, smul_eq_mul, P, Q, R] using hd
  apply raw_normal_obstruction u v w (D 0) (D 1) (D 2) hu hv hw0 hw1 P Q R
  · change f₀ (a 1 - a 0) < 0
    have hh := hf₀ _ (hS 1 0 (by simp [S]))
    simp only [map_add, map_sub] at hh ⊢
    linarith
  · change f₀ (a 2 - a 0) < 0
    have hh := hf₀ _ (hS 2 0 (by simp [S]))
    simp only [map_add, map_sub] at hh ⊢
    linarith
  · rw [← hB 0]
    change f₀ (b 2 - b 0) < 0
    have hh := hf₀ _ (hS 0 2 (by simp [S]))
    simp only [map_add, map_sub] at hh ⊢
    linarith
  · change f₁ (a 1 - a 0) < 0
    have hh := hf₁ _ (hS 1 1 (by simp [S]))
    simp only [map_add, map_sub] at hh ⊢
    linarith
  · change f₁ (a 2 - a 0) < 0
    have hh := hf₁ _ (hS 2 1 (by simp [S]))
    simp only [map_add, map_sub] at hh ⊢
    linarith
  · have hh := hf₁ _ (hS 0 2 (by simp [S]))
    have hb := hB 1
    change f₁ (b 2 - b 0) = u * P 1 + v * Q 1 + w * R 1 at hb
    have hd : f₁ (b 2 - b 0) - R 1 < 0 := by
      change f₁ (b 2 - b 0) - f₁ (b 1 - b 0) < 0
      simp only [map_add, map_sub] at hh ⊢
      linarith
    nlinarith only [hb, hd]
  · change 0 < f₂ (a 1 - a 0)
    have hh := hf₂ _ (hT 0 2 (by simp [T]))
    simp only [map_add, map_sub] at hh ⊢
    linarith
  · rw [← hB 2]
    change 0 < f₂ (b 2 - b 0)
    have hh := hf₂ _ (hT 1 0 (by simp [T]))
    simp only [map_add, map_sub] at hh ⊢
    linarith
  · have hh := hf₂ _ (hT 1 1 (by simp [T]))
    have hb := hB 2
    change f₂ (b 2 - b 0) = u * P 2 + v * Q 2 + w * R 2 at hb
    have hd : 0 < f₂ (b 2 - b 0) - R 2 := by
      change 0 < f₂ (b 2 - b 0) - f₂ (b 1 - b 0)
      simp only [map_add, map_sub] at hh ⊢
      linarith
    nlinarith only [hb, hd]
  · change 0 < f₃ (a 2 - a 0)
    have hh := hf₃ _ (hT 0 2 (by simp [T]))
    simp only [map_add, map_sub] at hh ⊢
    linarith
  · rw [← hB 3]
    change 0 < f₃ (b 2 - b 0)
    have hh := hf₃ _ (hT 2 0 (by simp [T]))
    simp only [map_add, map_sub] at hh ⊢
    linarith
  · have hh := hf₃ _ (hT 2 1 (by simp [T]))
    have hb := hB 3
    change f₃ (b 2 - b 0) = u * P 3 + v * Q 3 + w * R 3 at hb
    have hd : 0 < f₃ (b 2 - b 0) - R 3 := by
      change 0 < f₃ (b 2 - b 0) - f₃ (b 1 - b 0)
      simp only [map_add, map_sub] at hh ⊢
      linarith
    nlinarith only [hb, hd]
  · rw [heval 0]
    change 0 < f₀ (t - z)
    have hh := hf₀ _ (hT 0 0 (by simp [T]))
    simp only [map_add, map_sub] at hh ⊢
    linarith
  · rw [heval 1]
    change 0 < f₁ (t - z)
    have hh := hf₁ _ (hT 0 1 (by simp [T]))
    simp only [map_add, map_sub] at hh ⊢
    linarith
  · rw [heval 2]
    change f₂ (t - z) < 0
    have hh := hf₂ _ (hS 1 2 (by simp [S]))
    simp only [map_add, map_sub] at hh ⊢
    linarith
  · rw [heval 3]
    change f₃ (t - z) < 0
    have hh := hf₃ _ (hS 2 2 (by simp [S]))
    simp only [map_add, map_sub] at hh ⊢
    linarith

/-- No additive three-by-three array is shattered by a convex set in `ℝ³`. -/
theorem grid_not_shattered {C : Set ℝ³} (hC : Convex ℝ C) (a b : Fin 3 → ℝ³) :
    ¬ GridShattered C a b := by
  intro h
  obtain ⟨σ, τ, u, v, w, hu, hv, hw0, hw1, hform⟩ := exposed_normal_form (h.exposed hC)
  exact canonical_grid_not_shattered hC (h.reindex σ τ) u v w hu hv hw0 hw1 hform

end ConvexVC2Dimension

namespace VCDimConvex

/-- Every convex set in `ℝ³` has additive VC₂ dimension at most two.
This is the exact statement in the Formal Conjectures repository. -/
theorem hasAddVCNDimAtMost_two_two_of_convex_r3 {C : Set ℝ³} (hC : Convex ℝ C) :
    HasAddVCNDimAtMost C 2 2 := by
  intro x y hxy
  apply ConvexVC2Dimension.grid_not_shattered hC (x 0) (x 1)
  intro S
  let S' : Set (Fin 2 → Fin 3) := {i | (i 0, i 1) ∈ S}
  refine ⟨y S', ?_⟩
  intro i j
  have hh := hxy ![i, j] S'
  simpa [S', Fin.sum_univ_two, add_assoc] using hh

end VCDimConvex

#check @VCDimConvex.hasAddVCNDimAtMost_two_two_of_convex_r3
#print axioms VCDimConvex.hasAddVCNDimAtMost_two_two_of_convex_r3
