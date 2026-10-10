/-
Copyright (c) 2026 Jensen Kohlmeyer and Liam Kruer.
Released under Apache 2.0 license.
-/
import Mathlib
import FormalConjectures.Mathoverflow.«235893»

/-!
# Wong's connectedness-preserving bijection problem (MathOverflow 235893)

An unconditional counterexample in dimension two is constructed here.
The final theorem `wong235893_repository_answer` gives `False` for the
exact universal assertion in the imported repository statement.
The tube construction uses explicit ambient shears, recurrent whole
cross-sections, and colored boundary arcs. Every custom declaration is
audited below; no admitted proof or extra existence axiom is used.
The mathematical strategy follows L. Peter's recurrent-tube approach.
-/

namespace Wong235893

open Set

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The connectedness-preservation predicate imported from the unmodified repository. -/
abbrev IsConnectedMap (f : X → Y) : Prop :=
  Mathoverflow235893.IsConnectedMap f

/-- A set between a connected set and its closure is connected. -/
theorem connected_of_dense_connected_subset {d s : Set Y}
    (hd : IsConnected d) (hds : d ⊆ s) (hsd : s ⊆ closure d) :
    IsConnected s :=
  hd.subset_closure hds hsd

/-- A recurrent gate makes one side of a prospective separation clopen. -/
theorem gate_isClopen (f : X → Y) (ρ : X → ℝ)
    (hρ : Continuous ρ)
    (hf : ContinuousOn f {x | ρ x ≠ 0})
    (u v : Set Y) (hu : IsOpen u) (hv : IsOpen v)
    (hcover : ∀ x, f x ∈ u ∨ f x ∈ v)
    (hdisjoint : ∀ x, ¬ (f x ∈ u ∧ f x ∈ v))
    (τ : ℝ) (hτ : 0 < τ)
    (hgate : ∀ x, ρ x = τ → f x ∈ v) :
    IsClopen ({x | τ < ρ x} ∩ f ⁻¹' u) := by
  have hgt : IsOpen {x | τ < ρ x} := isOpen_lt continuous_const hρ
  have hne : IsOpen {x | ρ x ≠ 0} := isOpen_ne_fun hρ continuous_const
  have hsub : {x | τ < ρ x} ⊆ {x | ρ x ≠ 0} := by
    intro x hx
    exact ne_of_gt (hτ.trans hx)
  have hopen : IsOpen ({x | τ < ρ x} ∩ f ⁻¹' u) :=
    (hf.mono hsub).isOpen_inter_preimage hgt hu
  have heq :
      ({x | τ < ρ x} ∩ f ⁻¹' u)ᶜ =
        {x | ρ x < τ} ∪ ({x | ρ x ≠ 0} ∩ f ⁻¹' v) := by
    ext x
    change ¬ (τ < ρ x ∧ f x ∈ u) ↔
      ρ x < τ ∨ (ρ x ≠ 0 ∧ f x ∈ v)
    constructor
    · intro hx
      by_cases hlt : ρ x < τ
      · exact Or.inl hlt
      · by_cases hgt' : τ < ρ x
        · refine Or.inr ⟨ne_of_gt (hτ.trans hgt'), ?_⟩
          exact (hcover x).resolve_left (fun hxu => hx ⟨hgt', hxu⟩)
        · have he : ρ x = τ := le_antisymm (le_of_not_gt hgt') (le_of_not_gt hlt)
          exact Or.inr ⟨by rw [he]; exact ne_of_gt hτ, hgate x he⟩
    · rintro (hlt | ⟨-, hxv⟩) ⟨hgt', hxu⟩
      · exact (not_lt_of_ge hlt.le) hgt'
      · exact hdisjoint x ⟨hxu, hxv⟩
  have hcompl : IsOpen ({x | τ < ρ x} ∩ f ⁻¹' u)ᶜ := by
    rw [heq]
    exact (isOpen_lt hρ continuous_const).union
      (hf.isOpen_inter_preimage hne hv)
  exact ⟨isOpen_compl_iff.mp hcompl, hopen⟩

/-- A positive-source point and a zero-source point cannot lie on opposite
sides of a separation when arbitrarily small recurrent gates are available. -/
theorem recurrent_gate_contradiction [PreconnectedSpace X]
    (f : X → Y) (ρ : X → ℝ)
    (hρ : Continuous ρ)
    (hf : ContinuousOn f {x | ρ x ≠ 0})
    (hrec : ∀ y, ρ y = 0 → ∀ o : Set Y, IsOpen o → f y ∈ o →
      ∀ ε : ℝ, 0 < ε →
        ∃ τ : ℝ, 0 < τ ∧ τ < ε ∧ ∀ z, ρ z = τ → f z ∈ o)
    (u v : Set Y) (hu : IsOpen u) (hv : IsOpen v)
    (hcover : ∀ z, f z ∈ u ∨ f z ∈ v)
    (hdisjoint : ∀ z, ¬ (f z ∈ u ∧ f z ∈ v))
    (x y : X) (hx : 0 < ρ x) (hy : ρ y = 0)
    (hxu : f x ∈ u) (hyv : f y ∈ v) : False := by
  obtain ⟨τ, hτ, hτx, hgate⟩ := hrec y hy v hv hyv (ρ x) hx
  have ht := gate_isClopen f ρ hρ hf u v hu hv hcover hdisjoint τ hτ hgate
  have hall := isPreconnected_univ.subset_isClopen ht
    (show (univ ∩ ({z | τ < ρ z} ∩ f ⁻¹' u)).Nonempty from
      ⟨x, mem_univ x, hτx, hxu⟩)
  have hyT := hall (mem_univ y)
  have hlt : τ < ρ y := hyT.1
  rw [hy] at hlt
  exact (not_lt_of_ge hτ.le) hlt

omit [TopologicalSpace X] [TopologicalSpace Y] in
/-- Bookkeeping for a separation of a set meeting both zero and nonzero levels. -/
theorem exists_cross_pair (f : X → Y) (ρ : X → ℝ) (s : Set X) (u v : Set Y)
    (hcover : ∀ x ∈ s, f x ∈ u ∨ f x ∈ v)
    (hune : ∃ a ∈ s, f a ∈ u) (hvne : ∃ b ∈ s, f b ∈ v)
    (hoff : ∃ x ∈ s, ρ x ≠ 0) (hzero : ∃ y ∈ s, ρ y = 0) :
    ∃ x ∈ s, ∃ y ∈ s, ρ x ≠ 0 ∧ ρ y = 0 ∧
      ((f x ∈ u ∧ f y ∈ v) ∨ (f x ∈ v ∧ f y ∈ u)) := by
  classical
  obtain ⟨x, hxs, hx⟩ := hoff
  obtain ⟨y, hys, hy⟩ := hzero
  by_cases hxu : f x ∈ u
  · by_cases hyu : f y ∈ u
    · obtain ⟨b, hbs, hbv⟩ := hvne
      by_cases hb : ρ b = 0
      · exact ⟨x, hxs, b, hbs, hx, hb, Or.inl ⟨hxu, hbv⟩⟩
      · exact ⟨b, hbs, y, hys, hb, hy, Or.inr ⟨hbv, hyu⟩⟩
    · exact ⟨x, hxs, y, hys, hx, hy,
        Or.inl ⟨hxu, (hcover y hys).resolve_left hyu⟩⟩
  · have hxv := (hcover x hxs).resolve_left hxu
    by_cases hyu : f y ∈ u
    · exact ⟨x, hxs, y, hys, hx, hy, Or.inr ⟨hxv, hyu⟩⟩
    · have hyv := (hcover y hys).resolve_left hyu
      obtain ⟨a, has, hau⟩ := hune
      by_cases ha : ρ a = 0
      · exact ⟨x, hxs, a, has, hx, ha, Or.inr ⟨hxv, hau⟩⟩
      · exact ⟨a, has, y, hys, ha, hy, Or.inl ⟨hau, hyv⟩⟩

/-- The gate lemma for every connected set, with no compactness or path hypothesis. -/
theorem isConnectedMap_of_recurrent_levels (f : X → Y) (ρ : X → ℝ)
    (hρ : Continuous ρ) (hρ_nonneg : ∀ x, 0 ≤ ρ x)
    (hf : ContinuousOn f {x | ρ x ≠ 0})
    (hzero : ∀ s : Set X, s ⊆ {x | ρ x = 0} →
      IsConnected s → IsConnected (f '' s))
    (hrec : ∀ y, ρ y = 0 → ∀ o : Set Y, IsOpen o → f y ∈ o →
      ∀ ε : ℝ, 0 < ε →
        ∃ τ : ℝ, 0 < τ ∧ τ < ε ∧ ∀ z, ρ z = τ → f z ∈ o) :
    IsConnectedMap f := by
  classical
  intro s hs
  by_cases hz : s ⊆ {x | ρ x = 0}
  · exact hzero s hz hs
  by_cases hn : s ⊆ {x | ρ x ≠ 0}
  · exact hs.image f (hf.mono hn)
  have hoff : ∃ x ∈ s, ρ x ≠ 0 := by
    by_contra h
    apply hz
    intro x hx
    by_contra hne
    exact h ⟨x, hx, hne⟩
  have hzer : ∃ y ∈ s, ρ y = 0 := by
    by_contra h
    apply hn
    intro y hy he
    exact h ⟨y, hy, he⟩
  refine ⟨hs.nonempty.image f, ?_⟩
  intro u v hu hv hcover hune hvne
  by_contra hboth
  have hcover_s : ∀ x ∈ s, f x ∈ u ∨ f x ∈ v :=
    fun x hx => hcover (mem_image_of_mem f hx)
  have hdisjoint_s : ∀ x ∈ s, ¬ (f x ∈ u ∧ f x ∈ v) := by
    intro x hx h
    exact hboth ⟨f x, mem_image_of_mem f hx, h⟩
  obtain ⟨a', ⟨a, has, rfl⟩, hau⟩ := hune
  obtain ⟨b', ⟨b, hbs, rfl⟩, hbv⟩ := hvne
  obtain ⟨x, hxs, y, hys, hx, hy, hparts⟩ :=
    exists_cross_pair f ρ s u v hcover_s ⟨a, has, hau⟩ ⟨b, hbs, hbv⟩ hoff hzer
  let : ConnectedSpace s := isConnected_iff_connectedSpace.mp hs
  let F : s → Y := fun z => f z
  let R : s → ℝ := fun z => ρ z
  have hR : Continuous R := hρ.comp continuous_subtype_val
  have hF : ContinuousOn F {z | R z ≠ 0} := by
    exact hf.comp continuous_subtype_val.continuousOn (fun z hz => hz)
  have hrec' : ∀ y' : s, R y' = 0 → ∀ o : Set Y, IsOpen o → F y' ∈ o →
      ∀ ε : ℝ, 0 < ε →
        ∃ τ : ℝ, 0 < τ ∧ τ < ε ∧ ∀ z : s, R z = τ → F z ∈ o := by
    intro y' hy' o ho hyo ε hε
    obtain ⟨τ, hτ, hτε, hgate⟩ := hrec y'.val hy' o ho hyo ε hε
    exact ⟨τ, hτ, hτε, fun z hz => hgate z.val hz⟩
  have hcov : ∀ z : s, F z ∈ u ∨ F z ∈ v := fun z => hcover_s z z.property
  have hdis : ∀ z : s, ¬ (F z ∈ u ∧ F z ∈ v) :=
    fun z => hdisjoint_s z z.property
  have hxpos : 0 < R ⟨x, hxs⟩ := lt_of_le_of_ne (hρ_nonneg x) (Ne.symm hx)
  rcases hparts with hparts | hparts
  · exact recurrent_gate_contradiction F R hR hF hrec' u v hu hv hcov hdis
      ⟨x, hxs⟩ ⟨y, hys⟩ hxpos hy hparts.1 hparts.2
  · exact recurrent_gate_contradiction F R hR hF hrec' v u hv hu
      (fun z => (hcov z).symm) (fun z h => hdis z ⟨h.2, h.1⟩)
      ⟨x, hxs⟩ ⟨y, hys⟩ hxpos hy hparts.1 hparts.2

section ClosedCoverGluing

variable {ι : Type*}

noncomputable def coveredMap (s : ι → Set X) (hs : ∀ x, ∃ i, x ∈ s i)
    (maps : ∀ i, s i → Y) (x : X) : Y :=
  maps (Classical.choose (hs x)) ⟨x, Classical.choose_spec (hs x)⟩

omit [TopologicalSpace X] [TopologicalSpace Y] in
theorem coveredMap_apply (s : ι → Set X) (hs : ∀ x, ∃ i, x ∈ s i)
    (maps : ∀ i, s i → Y)
    (hcompat : ∀ i j x (hi : x ∈ s i) (hj : x ∈ s j), maps i ⟨x, hi⟩ = maps j ⟨x, hj⟩)
    (i : ι) (x : X) (hx : x ∈ s i) : coveredMap s hs maps x = maps i ⟨x, hx⟩ :=
  hcompat _ i x (Classical.choose_spec (hs x)) hx

/-- Compatible chart homeomorphisms on locally finite closed covers glue to a
global homeomorphism. Compatibility is required in both directions. -/
structure ClosedCoverHomeomorphData (X Y ι : Type*)
    [TopologicalSpace X] [TopologicalSpace Y] where
  source : ι → Set X
  target : ι → Set Y
  source_cover : ∀ x, ∃ i, x ∈ source i
  target_cover : ∀ y, ∃ i, y ∈ target i
  source_closed : ∀ i, IsClosed (source i)
  target_closed : ∀ i, IsClosed (target i)
  source_locallyFinite : LocallyFinite source
  target_locallyFinite : LocallyFinite target
  chart : ∀ i, source i ≃ₜ target i
  compatible : ∀ i j x (hi : x ∈ source i) (hj : x ∈ source j),
    (chart i ⟨x, hi⟩ : Y) = (chart j ⟨x, hj⟩ : Y)
  inverse_compatible : ∀ i j y (hi : y ∈ target i) (hj : y ∈ target j),
    ((chart i).symm ⟨y, hi⟩ : X) = ((chart j).symm ⟨y, hj⟩ : X)

noncomputable def ClosedCoverHomeomorphData.forward (d : ClosedCoverHomeomorphData X Y ι) :
    X → Y := coveredMap d.source d.source_cover (fun i z => (d.chart i z : Y))

noncomputable def ClosedCoverHomeomorphData.inverse (d : ClosedCoverHomeomorphData X Y ι) :
    Y → X := coveredMap d.target d.target_cover (fun i z => ((d.chart i).symm z : X))

theorem ClosedCoverHomeomorphData.forward_on (d : ClosedCoverHomeomorphData X Y ι)
    (i : ι) (x : X) (hx : x ∈ d.source i) :
    d.forward x = (d.chart i ⟨x, hx⟩ : Y) :=
  coveredMap_apply d.source d.source_cover _ d.compatible i x hx

theorem ClosedCoverHomeomorphData.inverse_on (d : ClosedCoverHomeomorphData X Y ι)
    (i : ι) (y : Y) (hy : y ∈ d.target i) :
    d.inverse y = ((d.chart i).symm ⟨y, hy⟩ : X) :=
  coveredMap_apply d.target d.target_cover _ d.inverse_compatible i y hy

theorem ClosedCoverHomeomorphData.forward_continuous
    (d : ClosedCoverHomeomorphData X Y ι) : Continuous d.forward := by
  apply d.source_locallyFinite.continuous
    (eq_univ_iff_forall.mpr fun x => mem_iUnion.mpr (d.source_cover x)) d.source_closed
  intro i
  apply continuousOn_iff_continuous_domRestrict.mpr
  exact (continuous_subtype_val.comp (d.chart i).continuous).congr
    (fun z => (d.forward_on i z z.property).symm)

theorem ClosedCoverHomeomorphData.inverse_continuous
    (d : ClosedCoverHomeomorphData X Y ι) : Continuous d.inverse := by
  apply d.target_locallyFinite.continuous
    (eq_univ_iff_forall.mpr fun y => mem_iUnion.mpr (d.target_cover y)) d.target_closed
  intro i
  apply continuousOn_iff_continuous_domRestrict.mpr
  exact (continuous_subtype_val.comp (d.chart i).symm.continuous).congr
    (fun z => (d.inverse_on i z z.property).symm)

noncomputable def ClosedCoverHomeomorphData.toHomeomorph
    (d : ClosedCoverHomeomorphData X Y ι) : X ≃ₜ Y where
  toFun := d.forward
  invFun := d.inverse
  left_inv x := by
    obtain ⟨i, hx⟩ := d.source_cover x
    rw [d.forward_on i x hx,
      d.inverse_on i (d.chart i ⟨x, hx⟩ : Y) (d.chart i ⟨x, hx⟩).property]
    exact congrArg Subtype.val ((d.chart i).symm_apply_apply ⟨x, hx⟩)
  right_inv y := by
    obtain ⟨i, hy⟩ := d.target_cover y
    rw [d.inverse_on i y hy,
      d.forward_on i ((d.chart i).symm ⟨y, hy⟩ : X) ((d.chart i).symm ⟨y, hy⟩).property]
    exact congrArg Subtype.val ((d.chart i).apply_symm_apply ⟨y, hy⟩)
  continuous_toFun := d.forward_continuous
  continuous_invFun := d.inverse_continuous

theorem ClosedCoverHomeomorphData.toHomeomorph_on (d : ClosedCoverHomeomorphData X Y ι)
    (i : ι) (x : X) (hx : x ∈ d.source i) :
    d.toHomeomorph x = (d.chart i ⟨x, hx⟩ : Y) := d.forward_on i x hx

end ClosedCoverGluing

section StripBoundaryInterpolation

abbrev UnitHeight := Icc (0 : ℝ) 1
abbrev ClosedStrip := ℝ × UnitHeight

def interpolatedCoordinate (a b : ℝ ≃o ℝ) (t : UnitHeight) (x : ℝ) : ℝ :=
  (1 - (t : ℝ)) * a x + (t : ℝ) * b x

theorem interpolatedCoordinate_continuous (a b : ℝ ≃o ℝ) (t : UnitHeight) :
    Continuous (interpolatedCoordinate a b t) :=
  (continuous_const.mul a.continuous).add (continuous_const.mul b.continuous)

theorem interpolatedCoordinate_strictMono (a b : ℝ ≃o ℝ) (t : UnitHeight) :
    StrictMono (interpolatedCoordinate a b t) := by
  intro x y hxy
  change (1 - (t : ℝ)) * a x + (t : ℝ) * b x <
    (1 - (t : ℝ)) * a y + (t : ℝ) * b y
  by_cases ht : (t : ℝ) < 1
  · exact add_lt_add_of_lt_of_le
      (mul_lt_mul_of_pos_left (a.strictMono hxy) (sub_pos.mpr ht))
      (mul_le_mul_of_nonneg_left (b.monotone hxy.le) t.property.1)
  · have hteq : (t : ℝ) = 1 := le_antisymm t.property.2 (le_of_not_gt ht)
    simpa only [hteq, sub_self, zero_mul, one_mul, zero_add] using b.strictMono hxy

theorem interpolatedCoordinate_le (a b : ℝ ≃o ℝ) (t : UnitHeight) (x c : ℝ)
    (ha : a x ≤ c) (hb : b x ≤ c) : interpolatedCoordinate a b t x ≤ c := by
  have hleft := mul_nonneg (sub_nonneg.mpr t.property.2) (sub_nonneg.mpr ha)
  have hright := mul_nonneg t.property.1 (sub_nonneg.mpr hb)
  unfold interpolatedCoordinate
  nlinarith

theorem le_interpolatedCoordinate (a b : ℝ ≃o ℝ) (t : UnitHeight) (x c : ℝ)
    (ha : c ≤ a x) (hb : c ≤ b x) : c ≤ interpolatedCoordinate a b t x := by
  have hleft := mul_nonneg (sub_nonneg.mpr t.property.2) (sub_nonneg.mpr ha)
  have hright := mul_nonneg t.property.1 (sub_nonneg.mpr hb)
  unfold interpolatedCoordinate
  nlinarith

theorem interpolatedCoordinate_lower_bound (a b : ℝ ≃o ℝ) (t : UnitHeight) (c : ℝ) :
    interpolatedCoordinate a b t (min (a.symm c) (b.symm c)) ≤ c := by
  apply interpolatedCoordinate_le
  · calc
      a (min (a.symm c) (b.symm c)) ≤ a (a.symm c) := a.monotone (min_le_left _ _)
      _ = c := a.apply_symm_apply c
  · calc
      b (min (a.symm c) (b.symm c)) ≤ b (b.symm c) := b.monotone (min_le_right _ _)
      _ = c := b.apply_symm_apply c

theorem interpolatedCoordinate_upper_bound (a b : ℝ ≃o ℝ) (t : UnitHeight) (c : ℝ) :
    c ≤ interpolatedCoordinate a b t (max (a.symm c) (b.symm c)) := by
  apply le_interpolatedCoordinate
  · calc
      c = a (a.symm c) := (a.apply_symm_apply c).symm
      _ ≤ a (max (a.symm c) (b.symm c)) := a.monotone (le_max_left _ _)
  · calc
      c = b (b.symm c) := (b.apply_symm_apply c).symm
      _ ≤ b (max (a.symm c) (b.symm c)) := b.monotone (le_max_right _ _)

theorem interpolatedCoordinate_surjective (a b : ℝ ≃o ℝ) (t : UnitHeight) :
    Function.Surjective (interpolatedCoordinate a b t) := by
  intro y
  exact mem_range_of_exists_le_of_exists_ge (interpolatedCoordinate_continuous a b t)
    ⟨_, interpolatedCoordinate_lower_bound a b t y⟩
    ⟨_, interpolatedCoordinate_upper_bound a b t y⟩

def boundaryInterpolation (a b : ℝ ≃o ℝ) (z : ClosedStrip) : ClosedStrip :=
  (interpolatedCoordinate a b z.2 z.1, z.2)

theorem boundaryInterpolation_continuous (a b : ℝ ≃o ℝ) :
    Continuous (boundaryInterpolation a b) := by
  have ht : Continuous (fun z : ClosedStrip => (z.2 : ℝ)) :=
    continuous_subtype_val.comp continuous_snd
  exact (((continuous_const.sub ht).mul (a.continuous.comp continuous_fst)).add
    (ht.mul (b.continuous.comp continuous_fst))).prodMk continuous_snd

theorem boundaryInterpolation_bijective (a b : ℝ ≃o ℝ) :
    Function.Bijective (boundaryInterpolation a b) := by
  constructor
  · intro x y hxy
    have ht := congrArg Prod.snd hxy
    change x.2 = y.2 at ht
    have hc := congrArg Prod.fst hxy
    change interpolatedCoordinate a b x.2 x.1 = interpolatedCoordinate a b y.2 y.1 at hc
    rw [← ht] at hc
    exact Prod.ext ((interpolatedCoordinate_strictMono a b x.2).injective hc) ht
  · rintro ⟨y, t⟩
    obtain ⟨x, hx⟩ := interpolatedCoordinate_surjective a b t y
    exact ⟨(x, t), Prod.ext hx rfl⟩

/-- Uniform bounds over the compact height interval make interpolation proper.
This gives continuity of the inverse, not just separate inverses on each line. -/
theorem boundaryInterpolation_isProperMap (a b : ℝ ≃o ℝ) :
    IsProperMap (boundaryInterpolation a b) := by
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨boundaryInterpolation_continuous a b, ?_⟩
  intro k hk
  obtain ⟨l, hl⟩ := (hk.image continuous_fst).bddBelow
  obtain ⟨u, hu⟩ := (hk.image continuous_fst).bddAbove
  apply (isCompact_Icc.prod (isCompact_univ (X := UnitHeight))).of_isClosed_subset
    (hk.isClosed.preimage (boundaryInterpolation_continuous a b))
  intro z hz
  change boundaryInterpolation a b z ∈ k at hz
  refine ⟨⟨?_, ?_⟩, mem_univ _⟩
  · have hbound : l ≤ interpolatedCoordinate a b z.2 z.1 :=
      hl (mem_image_of_mem Prod.fst hz)
    by_contra h
    have hstrict := interpolatedCoordinate_strictMono a b z.2 (lt_of_not_ge h)
    exact (not_lt_of_ge hbound)
      (hstrict.trans_le (interpolatedCoordinate_lower_bound a b z.2 l))
  · have hbound : interpolatedCoordinate a b z.2 z.1 ≤ u :=
      hu (mem_image_of_mem Prod.fst hz)
    by_contra h
    have hstrict := interpolatedCoordinate_strictMono a b z.2 (lt_of_not_ge h)
    exact (not_lt_of_ge hbound)
      ((interpolatedCoordinate_upper_bound a b z.2 u).trans_lt hstrict)

noncomputable def boundaryInterpolationHomeomorph (a b : ℝ ≃o ℝ) : ClosedStrip ≃ₜ ClosedStrip :=
  (Equiv.ofBijective _ (boundaryInterpolation_bijective a b)).toHomeomorphOfContinuousClosed
    (boundaryInterpolation_continuous a b) (boundaryInterpolation_isProperMap a b).isClosedMap

theorem boundaryInterpolationHomeomorph_bottom (a b : ℝ ≃o ℝ) (x : ℝ)
    (t : UnitHeight) (ht : (t : ℝ) = 0) :
    boundaryInterpolationHomeomorph a b (x, t) = (a x, t) := by
  apply Prod.ext
  · change (1 - (t : ℝ)) * a x + (t : ℝ) * b x = a x
    simp only [ht, sub_zero, one_mul, zero_mul, add_zero]
  · rfl

theorem boundaryInterpolationHomeomorph_top (a b : ℝ ≃o ℝ) (x : ℝ)
    (t : UnitHeight) (ht : (t : ℝ) = 1) :
    boundaryInterpolationHomeomorph a b (x, t) = (b x, t) := by
  apply Prod.ext
  · change (1 - (t : ℝ)) * a x + (t : ℝ) * b x = b x
    simp only [ht, sub_self, zero_mul, one_mul, zero_add]
  · rfl

end StripBoundaryInterpolation

section ContinuumFoundations

open Topology

/-- Compact Hausdorff components have a basis of clopen neighbourhoods of the whole
component. This is the compactness form of the component/quasicomponent theorem. -/
theorem exists_clopen_containing_component [T2Space X] [CompactSpace X]
    (x : X) {u : Set X} (hu : IsOpen u) (hcu : connectedComponent x ⊆ u) :
    ∃ v : Set X, IsClopen v ∧ x ∈ v ∧ v ⊆ u := by
  let N := {s : Set X // IsClopen s ∧ x ∈ s}
  have : Nonempty N := ⟨⟨univ, isClopen_univ, mem_univ x⟩⟩
  have hdir : Directed (· ⊇ ·) (fun s : N => s.val) := by
    rintro ⟨s, hs, hxs⟩ ⟨t, ht, hxt⟩
    exact ⟨⟨s ∩ t, hs.inter ht, ⟨hxs, hxt⟩⟩, inter_subset_left, inter_subset_right⟩
  have hnhds : ∀ y ∈ ⋂ s : N, s.val, u ∈ 𝓝 y := by
    intro y hy
    apply hu.mem_nhds
    apply hcu
    simpa only [connectedComponent_eq_iInter_isClopen x] using hy
  obtain ⟨v, hv⟩ := exists_subset_nhds_of_compactSpace hdir (fun s => s.property.1.1) hnhds
  exact ⟨v.val, v.property.1, v.property.2, hv⟩

/-- Boundary bumping for a component of a proper closed subset of a continuum. -/
theorem connectedComponentIn_inter_frontier [T2Space X] [CompactSpace X]
    [ConnectedSpace X] {s : Set X} (hs : IsClosed s) (hproper : s ≠ univ)
    {x : X} (hx : x ∈ s) :
    (connectedComponentIn s x ∩ frontier s).Nonempty := by
  classical
  have : CompactSpace s := isCompact_iff_compactSpace.mp hs.isCompact
  by_contra h
  let xs : s := ⟨x, hx⟩
  have hsub : connectedComponent xs ⊆ ((↑) : s → X) ⁻¹' interior s := by
    intro y hy
    have hyc : (y : X) ∈ connectedComponentIn s x := by
      rw [connectedComponentIn_eq_image hx]
      exact mem_image_of_mem _ hy
    by_contra hyint
    apply h
    refine ⟨y, hyc, ?_⟩
    rw [hs.frontier_eq]
    exact ⟨y.property, hyint⟩
  obtain ⟨v, hv, hxv, hvsub⟩ := exists_clopen_containing_component xs
    (isOpen_interior.preimage continuous_subtype_val) hsub
  let w : Set X := ((↑) : s → X) '' v
  have hwclosed : IsClosed w := hs.isClosedMap_subtype_val v hv.isClosed
  have hwint : w ⊆ interior s := by
    rintro y ⟨z, hz, rfl⟩
    exact hvsub hz
  obtain ⟨u, hu, huv⟩ := isOpen_induced_iff.mp hv.isOpen
  have hweq : w = u ∩ interior s := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨by rw [← huv] at hz; exact hz, hwint (mem_image_of_mem _ hz)⟩
    · intro hy
      refine ⟨⟨y, interior_subset hy.2⟩, ?_, rfl⟩
      rw [← huv]
      exact hy.1
  have hwopen : IsOpen w := hweq ▸ hu.inter isOpen_interior
  have hxw : x ∈ w := ⟨xs, hxv, rfl⟩
  have hall : univ ⊆ w :=
    isPreconnected_univ.subset_isClopen ⟨hwclosed, hwopen⟩ ⟨x, mem_univ x, hxw⟩
  apply hproper
  exact eq_univ_of_univ_subset (hall.trans (hwint.trans interior_subset))

/-- A proper subcontinuum, interpreted inside its compact ambient continuum. -/
def ProperContinuum (c : Set X) : Prop :=
  IsCompact c ∧ IsConnected c ∧ c ≠ univ

/-- The usual indecomposability condition, with the ambient continuum as `univ`. -/
def Indecomposable (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ c d : Set X, ProperContinuum c → ProperContinuum d → c ∪ d ≠ univ

/-- The composant of a point is the union of proper subcontinua containing it. -/
def composant (x : X) : Set X :=
  {y | ∃ c : Set X, ProperContinuum c ∧ x ∈ c ∧ y ∈ c}

theorem mem_composant [Nontrivial X] (x : X) : x ∈ composant x := by
  refine ⟨{x}, ⟨isCompact_singleton, isConnected_singleton, ?_⟩, by simp, by simp⟩
  intro h
  obtain ⟨y, hy⟩ := exists_ne x
  apply hy
  simpa only [← h, mem_singleton_iff] using (mem_univ y)

theorem composant_isConnected [Nontrivial X] (x : X) : IsConnected (composant x) := by
  refine ⟨⟨x, mem_composant x⟩, isPreconnected_of_forall x ?_⟩
  rintro y ⟨c, hc, hxc, hyc⟩
  refine ⟨c, ?_, hxc, hyc, hc.2.1.isPreconnected⟩
  intro z hzc
  exact ⟨c, hc, hxc, hzc⟩

theorem composant_symm {x y : X} (h : y ∈ composant x) : x ∈ composant y := by
  obtain ⟨c, hc, hx, hy⟩ := h
  exact ⟨c, hc, hy, hx⟩

theorem composant_trans (hi : Indecomposable X) {x y z : X}
    (hxy : y ∈ composant x) (hyz : z ∈ composant y) : z ∈ composant x := by
  obtain ⟨c, hc, hxc, hyc⟩ := hxy
  obtain ⟨d, hd, hyd, hzd⟩ := hyz
  exact ⟨c ∪ d, ⟨hc.1.union hd.1, hc.2.1.union ⟨y, hyc, hyd⟩ hd.2.1,
    hi c d hc hd⟩, Or.inl hxc, Or.inr hzd⟩

theorem composant_eq_of_mem (hi : Indecomposable X) {x y : X}
    (hxy : y ∈ composant x) : composant y = composant x := by
  apply Subset.antisymm
  · intro z hz
    exact composant_trans hi hxy hz
  · intro z hz
    exact composant_trans hi (composant_symm hxy) hz

theorem composant_disjoint_of_ne (hi : Indecomposable X) {x y : X}
    (hne : composant x ≠ composant y) : Disjoint (composant x) (composant y) := by
  apply disjoint_left.mpr
  intro z hxz hyz
  exact hne ((composant_eq_of_mem hi hxz).symm.trans (composant_eq_of_mem hi hyz))

theorem isCompact_connectedComponentIn [T2Space X] [CompactSpace X]
    {s : Set X} (hs : IsClosed s) {x : X} (hx : x ∈ s) :
    IsCompact (connectedComponentIn s x) := by
  have : CompactSpace s := isCompact_iff_compactSpace.mp hs.isCompact
  rw [connectedComponentIn_eq_image hx]
  exact isClosed_connectedComponent.isCompact.image continuous_subtype_val

/-- Every composant is dense in its ambient continuum. Indecomposability is not
needed for this particular assertion. -/
theorem composant_dense [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [Nontrivial X] (x : X) : Dense (composant x) := by
  classical
  rw [dense_iff_inter_open]
  intro o ho hnonempty
  by_cases hxo : x ∈ o
  · exact ⟨x, hxo, mem_composant x⟩
  obtain ⟨q, hq⟩ := hnonempty
  obtain ⟨v, ⟨hqv, hv⟩, hvcl⟩ :=
    (hasBasis_opens_closure q).mem_iff.mp (ho.mem_nhds hq)
  have hxv : x ∈ vᶜ := fun h => hxo (hvcl (subset_closure h))
  have hvproper : vᶜ ≠ univ := by
    intro h
    have : q ∈ vᶜ := h ▸ mem_univ q
    exact this hqv
  obtain ⟨z, hzc, hzf⟩ := connectedComponentIn_inter_frontier hv.isClosed_compl hvproper hxv
  have hzo : z ∈ o := by
    apply hvcl
    rw [frontier_compl] at hzf
    exact frontier_subset_closure hzf
  have hcproper : connectedComponentIn vᶜ x ≠ univ := by
    intro h
    have : q ∈ vᶜ := connectedComponentIn_subset vᶜ x (h ▸ mem_univ q)
    exact this hqv
  exact ⟨z, hzo, connectedComponentIn vᶜ x,
    ⟨isCompact_connectedComponentIn hv.isClosed_compl hxv,
      isConnected_connectedComponentIn_iff.mpr hxv, hcproper⟩,
    mem_connectedComponentIn hxv, hzc⟩

/-- A clopen collection of components of a closed set can be joined to a connected
set containing the frontier. Every component meets that frontier. -/
theorem connected_union_clopen_components [T2Space X] [CompactSpace X]
    [ConnectedSpace X] {c s : Set X} (hc : IsConnected c) (hs : IsClosed s)
    (hproper : s ≠ univ) (hfrontier : frontier s ⊆ c)
    (v : Set s) (hv : IsClopen v) :
    IsConnected (c ∪ ((↑) : s → X) '' v) := by
  obtain ⟨p, hpc⟩ := hc.nonempty
  refine ⟨⟨p, Or.inl hpc⟩, isPreconnected_of_forall p ?_⟩
  intro z hz
  rcases hz with hzc | ⟨zs, hzv, rfl⟩
  · exact ⟨c, subset_union_left, hpc, hzc, hc.isPreconnected⟩
  have hcomp : connectedComponentIn s (zs : X) ⊆ ((↑) : s → X) '' v := by
    rw [connectedComponentIn_eq_image zs.property]
    apply image_mono
    exact hv.connectedComponent_subset hzv
  obtain ⟨q, hqc, hqf⟩ := connectedComponentIn_inter_frontier hs hproper zs.property
  have hconn := hc.union ⟨q, hfrontier hqf, hqc⟩
    (isConnected_connectedComponentIn_iff.mpr zs.property)
  exact ⟨c ∪ connectedComponentIn s (zs : X), union_subset_union_right c hcomp,
    Or.inl hpc, Or.inr (mem_connectedComponentIn zs.property), hconn.isPreconnected⟩

/-- A proper subcontinuum of an indecomposable continuum has empty interior. -/
theorem properContinuum_interior_empty [T2Space X] [CompactSpace X]
    [ConnectedSpace X] (hi : Indecomposable X) {c : Set X} (hc : ProperContinuum c) :
    interior c = ∅ := by
  classical
  by_contra hnonempty
  obtain ⟨p, hp⟩ := nonempty_iff_ne_empty.mpr hnonempty
  obtain ⟨x, hxc⟩ := (ne_univ_iff_exists_notMem c).mp hc.2.2
  let s := (interior c)ᶜ
  have hs : IsClosed s := isOpen_interior.isClosed_compl
  have hsproper : s ≠ univ := by
    intro h
    exact (show p ∈ s from h ▸ mem_univ p) hp
  have hxs : x ∈ s := fun hx => hxc (interior_subset hx)
  have hcfrontier : frontier s ⊆ c := by
    rw [show s = (interior c)ᶜ from rfl, frontier_compl]
    exact frontier_subset_closure.trans (closure_minimal interior_subset hc.1.isClosed)
  have hcomp : ProperContinuum (connectedComponentIn s x) := by
    refine ⟨isCompact_connectedComponentIn hs hxs,
      isConnected_connectedComponentIn_iff.mpr hxs, ?_⟩
    intro h
    exact hsproper (eq_univ_of_univ_subset (h ▸ connectedComponentIn_subset s x))
  obtain ⟨y, hy⟩ := (ne_univ_iff_exists_notMem _).mp (hi c _ hc hcomp)
  have hyc : y ∉ c := fun h => hy (Or.inl h)
  have hycomp : y ∉ connectedComponentIn s x := fun h => hy (Or.inr h)
  have hys : y ∈ s := fun h => hyc (interior_subset h)
  let xs : s := ⟨x, hxs⟩
  let ys : s := ⟨y, hys⟩
  have hynot : ys ∉ connectedComponent xs := by
    intro h
    apply hycomp
    rw [connectedComponentIn_eq_image hxs]
    exact mem_image_of_mem _ h
  have : CompactSpace s := isCompact_iff_compactSpace.mp hs.isCompact
  rw [connectedComponent_eq_iInter_isClopen xs] at hynot
  simp only [mem_iInter, not_forall] at hynot
  obtain ⟨⟨v, hv, hxv⟩, hyv⟩ := hynot
  let a := c ∪ ((↑) : s → X) '' v
  let b := c ∪ ((↑) : s → X) '' vᶜ
  have ha : ProperContinuum a := by
    refine ⟨hc.1.union (hv.isClosed.isCompact.image continuous_subtype_val),
      connected_union_clopen_components hc.2.1 hs hsproper hcfrontier v hv, ?_⟩
    intro h
    have hya : y ∈ a := h ▸ mem_univ y
    rcases hya with h | ⟨z, hz, hzy⟩
    · exact hyc h
    · exact hyv (show ys ∈ v from (Subtype.ext hzy : z = ys) ▸ hz)
  have hb : ProperContinuum b := by
    refine ⟨hc.1.union (hv.compl.isClosed.isCompact.image continuous_subtype_val),
      connected_union_clopen_components hc.2.1 hs hsproper hcfrontier vᶜ hv.compl, ?_⟩
    intro h
    have hxb : x ∈ b := h ▸ mem_univ x
    rcases hxb with h | ⟨z, hz, hzx⟩
    · exact hxc h
    · exact hz (show z ∈ v from (Subtype.ext hzx : z = xs).symm ▸ hxv)
  apply hi a b ha hb
  apply eq_univ_iff_forall.mpr
  intro z
  by_cases hzc : z ∈ c
  · exact Or.inl (Or.inl hzc)
  · have hzs : z ∈ s := fun h => hzc (interior_subset h)
    by_cases hzv : (⟨z, hzs⟩ : s) ∈ v
    · exact Or.inl (Or.inr ⟨⟨z, hzs⟩, hzv, rfl⟩)
    · exact Or.inr (Or.inr ⟨⟨z, hzs⟩, hzv, rfl⟩)

theorem properContinuum_isNowhereDense [T2Space X] [CompactSpace X]
    [ConnectedSpace X] (hi : Indecomposable X) {c : Set X} (hc : ProperContinuum c) :
    IsNowhereDense c :=
  hc.1.isClosed.isNowhereDense_iff.mpr (properContinuum_interior_empty hi hc)

/-- In a second countable indecomposable continuum, each composant is meagre.
The countable cover consists of components of complements of basis elements. -/
theorem composant_isMeagre [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [SecondCountableTopology X] (hi : Indecomposable X) (x : X) :
    IsMeagre (composant x) := by
  classical
  let parts : TopologicalSpace.countableBasis X → Set X :=
    fun b => connectedComponentIn b.valᶜ x
  have hparts : ∀ b, IsMeagre (parts b) := by
    intro b
    by_cases hx : x ∈ b.valᶜ
    · have hproper : ProperContinuum (parts b) := by
        refine ⟨isCompact_connectedComponentIn
          (TopologicalSpace.isOpen_of_mem_countableBasis b.property).isClosed_compl hx,
          isConnected_connectedComponentIn_iff.mpr hx, ?_⟩
        obtain ⟨q, hq⟩ := TopologicalSpace.nonempty_of_mem_countableBasis b.property
        intro h
        change connectedComponentIn b.valᶜ x = univ at h
        exact connectedComponentIn_subset b.valᶜ x (h ▸ mem_univ q) hq
      exact (properContinuum_isNowhereDense hi hproper).isMeagre
    · have hparts_empty : parts b = ∅ := connectedComponentIn_eq_empty hx
      exact hparts_empty ▸ IsMeagre.empty
  apply (isMeagre_iUnion hparts).mono
  rintro y ⟨c, hc, hxc, hyc⟩
  obtain ⟨q, hqc⟩ := (ne_univ_iff_exists_notMem c).mp hc.2.2
  obtain ⟨b, hb, -, hbc⟩ := (TopologicalSpace.isBasis_countableBasis X).isOpen_iff.mp
    hc.1.isClosed.isOpen_compl q hqc
  have hcb : c ⊆ bᶜ := fun z hzc hzb => hbc hzb hzc
  exact mem_iUnion.mpr ⟨⟨b, hb⟩, hc.2.1.isPreconnected.subset_connectedComponentIn hxc hcb hyc⟩

/-- There are uncountably many distinct composants in a nondegenerate compact,
second countable indecomposable continuum. -/
theorem composants_not_countable [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [SecondCountableTopology X] [Nontrivial X] (hi : Indecomposable X) :
    ¬ (range (composant (X := X))).Countable := by
  intro hcountable
  have hmeagre : IsMeagre (⋃ c ∈ range (composant (X := X)), c) :=
    isMeagre_biUnion hcountable (by rintro c ⟨x, rfl⟩; exact composant_isMeagre hi x)
  have hcover : univ ⊆ ⋃ c ∈ range (composant (X := X)), c := by
    intro x _
    exact mem_iUnion.mpr ⟨composant x, mem_iUnion.mpr ⟨mem_range_self x, mem_composant x⟩⟩
  exact not_isMeagre_of_isOpen isOpen_univ Set.univ_nonempty (hmeagre.mono hcover)

theorem composant_not_subsingleton [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [Nontrivial X] (x : X) : ¬ (composant x).Subsingleton := by
  intro hsub
  have hsingle : composant x ⊆ {x} := fun y hy => hsub hy (mem_composant x)
  obtain ⟨q, hqx⟩ := exists_ne x
  apply hqx
  have : q ∈ closure ({x} : Set X) := closure_mono hsingle (composant_dense x q)
  simpa only [isClosed_singleton.closure_eq, mem_singleton_iff] using this

/-- Select countably many different composants avoiding two specified ones. -/
theorem exists_composant_sequence_avoiding [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [SecondCountableTopology X] [Nontrivial X]
    (hi : Indecomposable X) (a b : X) :
    ∃ r : ℕ → X,
      Pairwise (fun i j => composant (r i) ≠ composant (r j)) ∧
      ∀ n, composant (r n) ≠ composant a ∧ composant (r n) ≠ composant b := by
  classical
  let allowed := range (composant (X := X)) \ {composant a, composant b}
  have hinfinite : allowed.Infinite := by
    intro hfinite
    apply composants_not_countable hi
    exact hfinite.countable.of_sdiff (by simp)
  let e : ℕ ↪ allowed := hinfinite.natEmbedding allowed
  have hexists : ∀ n, ∃ x : X, composant x = (e n).val := fun n => (e n).property.1
  choose r hr using hexists
  refine ⟨r, ?_, ?_⟩
  · intro i j hij heq
    apply hij
    apply e.injective
    apply Subtype.ext
    rw [← hr i, ← hr j]
    exact heq
  · intro n
    have havoid := (e n).property.2
    rw [← hr n] at havoid
    simpa only [mem_insert_iff, mem_singleton_iff, not_or] using havoid

/-- The inverse witness need not be an arc: any nontrivial proper subcontinuum
avoiding the pole suffices, and such a subcontinuum always exists. -/
theorem exists_properContinuum_nontrivial_avoiding [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [SecondCountableTopology X] [Nontrivial X]
    (hi : Indecomposable X) (p : X) :
    ∃ c : Set X, ProperContinuum c ∧ c.Nontrivial ∧ p ∉ c := by
  classical
  obtain ⟨r, -, havoid⟩ := exists_composant_sequence_avoiding hi p p
  let a := r 0
  have hexists : ∃ q ∈ composant a, q ≠ a := by
    by_contra h
    push Not at h
    apply composant_not_subsingleton a
    exact fun x hx y hy => (h x hx).trans (h y hy).symm
  obtain ⟨q, ⟨c, hc, hac, hqc⟩, hqa⟩ := hexists
  refine ⟨c, hc, ⟨a, hac, q, hqc, hqa.symm⟩, ?_⟩
  intro hpc
  apply (havoid 0).1
  exact (composant_eq_of_mem hi (show p ∈ composant a from ⟨c, hc, hac, hpc⟩)).symm

end ContinuumFoundations

section Plane

abbrev Plane := EuclideanSpace ℝ (Fin 2)

noncomputable def planeOf (x y : ℝ) : Plane :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm ![x, y]

@[simp] theorem planeOf_zero (x y : ℝ) : planeOf x y 0 = x := rfl

@[simp] theorem planeOf_one (x y : ℝ) : planeOf x y 1 = y := rfl

theorem planeOf_coords (z : Plane) : planeOf (z 0) (z 1) = z := by
  apply (EuclideanSpace.equiv (Fin 2) ℝ).injective
  funext i
  fin_cases i <;> rfl

theorem continuous_coord (i : Fin 2) : Continuous (fun z : Plane => z i) :=
  (continuous_apply i).comp (EuclideanSpace.equiv (Fin 2) ℝ).continuous

noncomputable def ray (t : ℝ) : Plane := planeOf t 0

theorem continuous_ray : Continuous ray := by
  apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp
  apply continuous_pi
  intro i
  fin_cases i
  · exact continuous_id
  · exact continuous_const

def slit : Set Plane := {z | 0 ≤ z 0 ∧ z 1 = 0}

noncomputable def planeCantor : Set Plane := ray '' cantorSet

theorem three_quarters_mem_cantorSet : (3 : ℝ) / 4 ∈ cantorSet :=
  mem_iInter.mpr (fun n => (quarters_mem_preCantorSet n).2)

theorem half_not_mem_cantorSet : (1 : ℝ) / 2 ∉ cantorSet := by
  intro h
  rw [cantorSet_eq_union_halves] at h
  rcases h with ⟨x, hx, he⟩ | ⟨x, hx, he⟩
  · have hx' := cantorSet_subset_unitInterval hx
    norm_num at he
    linarith [hx'.2]
  · have hx' := cantorSet_subset_unitInterval hx
    norm_num at he
    linarith [hx'.1]

theorem not_isConnected_cantorSet : ¬ IsConnected cantorSet := by
  intro h
  have hhalf := h.isPreconnected.ordConnected.out quarter_mem_cantorSet
    three_quarters_mem_cantorSet (show (1 : ℝ) / 2 ∈ Icc (1 / 4) (3 / 4) by norm_num)
  exact half_not_mem_cantorSet hhalf

theorem planeCantor_subset_slit : planeCantor ⊆ slit := by
  rintro z ⟨t, ht, rfl⟩
  exact ⟨(cantorSet_subset_unitInterval ht).1, rfl⟩

theorem coord_image_planeCantor : (fun z : Plane => z 0) '' planeCantor = cantorSet := by
  ext t
  constructor
  · rintro ⟨z, ⟨u, hu, rfl⟩, rfl⟩
    exact hu
  · intro ht
    exact ⟨ray t, ⟨t, ht, rfl⟩, rfl⟩

theorem not_isConnected_planeCantor : ¬ IsConnected planeCantor := by
  intro h
  have hi := h.image (fun z : Plane => z 0) (continuous_coord 0).continuousOn
  rw [coord_image_planeCantor] at hi
  exact not_isConnected_cantorSet hi

/-- The nonnegative continuous level function used in the planar construction. -/
noncomputable def rho (z : Plane) : ℝ :=
  Real.sqrt ((Real.sqrt ((z 0) ^ 2 + (z 1) ^ 2) - z 0) / 2)

theorem continuous_rho : Continuous rho := by
  exact Real.continuous_sqrt.comp
    (((Real.continuous_sqrt.comp
      (((continuous_coord 0).pow 2).add ((continuous_coord 1).pow 2))).sub
      (continuous_coord 0)).div_const 2)

theorem rho_nonneg (z : Plane) : 0 ≤ rho z := Real.sqrt_nonneg _

theorem radial_nonneg (z : Plane) :
    0 ≤ (Real.sqrt ((z 0) ^ 2 + (z 1) ^ 2) - z 0) / 2 := by
  have h := Real.le_sqrt_of_sq_le
    (show (z 0) ^ 2 ≤ (z 0) ^ 2 + (z 1) ^ 2 by nlinarith [sq_nonneg (z 1)])
  linarith

theorem rho_eq_zero_iff (z : Plane) : rho z = 0 ↔ z ∈ slit := by
  rw [rho, Real.sqrt_eq_zero (radial_nonneg z)]
  constructor
  · intro h
    have he : Real.sqrt ((z 0) ^ 2 + (z 1) ^ 2) = z 0 := by linarith
    have hx : 0 ≤ z 0 := he ▸ Real.sqrt_nonneg _
    have hs := Real.sq_sqrt (show 0 ≤ (z 0) ^ 2 + (z 1) ^ 2 by positivity)
    rw [he] at hs
    have hy : z 1 = 0 := by nlinarith [sq_nonneg (z 1)]
    exact ⟨hx, hy⟩
  · rintro ⟨hx, hy⟩
    rw [hy, zero_pow (by decide : 2 ≠ 0), add_zero, Real.sqrt_sq_eq_abs,
      abs_of_nonneg hx]
    ring

/-- Coordinates on the slit plane, obtained from the upper square-root branch. -/
noncomputable def psi (z : Plane) : Plane :=
  planeOf (z 1 / (2 * rho z)) (-Real.log (rho z))

/-- The explicit inverse of the slit-plane coordinate map. -/
noncomputable def inversePsi (w : Plane) : Plane :=
  planeOf ((w 0) ^ 2 - (Real.exp (-w 1)) ^ 2) (2 * w 0 * Real.exp (-w 1))

theorem rho_inversePsi (w : Plane) : rho (inversePsi w) = Real.exp (-w 1) := by
  have hb : 0 < Real.exp (-w 1) := Real.exp_pos _
  have heq : ((w 0) ^ 2 - (Real.exp (-w 1)) ^ 2) ^ 2 +
      (2 * w 0 * Real.exp (-w 1)) ^ 2 =
      ((w 0) ^ 2 + (Real.exp (-w 1)) ^ 2) ^ 2 := by ring
  simp only [rho, inversePsi, planeOf_zero, planeOf_one]
  rw [heq, Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
  have heq' : ((w 0) ^ 2 + (Real.exp (-w 1)) ^ 2 -
      ((w 0) ^ 2 - (Real.exp (-w 1)) ^ 2)) / 2 = (Real.exp (-w 1)) ^ 2 := by ring
  rw [heq', Real.sqrt_sq_eq_abs, abs_of_pos hb]

theorem inversePsi_not_mem_slit (w : Plane) : inversePsi w ∉ slit := by
  intro h
  have he := (rho_eq_zero_iff _).mpr h
  rw [rho_inversePsi] at he
  exact Real.exp_ne_zero _ he

theorem psi_inversePsi (w : Plane) : psi (inversePsi w) = w := by
  rw [psi, rho_inversePsi]
  simp only [inversePsi, planeOf_one]
  have hcoord : 2 * w 0 * Real.exp (-w 1) / (2 * Real.exp (-w 1)) = w 0 := by
    field_simp
  rw [hcoord, Real.log_exp, neg_neg]
  exact planeOf_coords w

theorem inversePsi_psi {z : Plane} (hz : z ∉ slit) : inversePsi (psi z) = z := by
  have hr : 0 < rho z := lt_of_le_of_ne (rho_nonneg z)
    (Ne.symm (fun h => hz ((rho_eq_zero_iff z).mp h)))
  have hsq : (rho z) ^ 2 = (Real.sqrt ((z 0) ^ 2 + (z 1) ^ 2) - z 0) / 2 :=
    Real.sq_sqrt (radial_nonneg z)
  have he : Real.sqrt ((z 0) ^ 2 + (z 1) ^ 2) = 2 * (rho z) ^ 2 + z 0 := by
    linarith
  have hnorm := Real.sq_sqrt (show 0 ≤ (z 0) ^ 2 + (z 1) ^ 2 by positivity)
  rw [he] at hnorm
  have hy2 : (z 1) ^ 2 = 4 * (rho z) ^ 2 * (z 0 + (rho z) ^ 2) := by
    nlinarith [hnorm]
  have hx : (z 1 / (2 * rho z)) ^ 2 - (rho z) ^ 2 = z 0 := by
    field_simp
    nlinarith [hy2]
  have hy : 2 * (z 1 / (2 * rho z)) * rho z = z 1 := by
    field_simp
  simp only [inversePsi, psi, planeOf_zero, planeOf_one, neg_neg, Real.exp_log hr]
  rw [hx, hy]
  exact planeOf_coords z

theorem continuous_inversePsi : Continuous inversePsi := by
  apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp
  apply continuous_pi
  intro i
  fin_cases i
  · exact ((continuous_coord 0).pow 2).sub
      ((Real.continuous_exp.comp (continuous_coord 1).neg).pow 2)
  · exact (continuous_const.mul (continuous_coord 0)).mul
      (Real.continuous_exp.comp (continuous_coord 1).neg)

theorem continuousOn_psi : ContinuousOn psi (slitᶜ : Set Plane) := by
  have hn : ∀ z ∈ (slitᶜ : Set Plane), 2 * rho z ≠ 0 := by
    intro z hz
    exact mul_ne_zero (by norm_num) (fun h => hz ((rho_eq_zero_iff z).mp h))
  have hx : ContinuousOn (fun z : Plane => z 1 / (2 * rho z)) (slitᶜ : Set Plane) :=
    (continuous_coord 1).continuousOn.div
      (continuous_const.mul continuous_rho).continuousOn hn
  have hy : ContinuousOn (fun z : Plane => -Real.log (rho z)) (slitᶜ : Set Plane) := by
    exact (Real.continuousOn_log.comp continuous_rho.continuousOn
      (fun z hz => by simpa using (fun h => hz ((rho_eq_zero_iff z).mp h)))).neg
  apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.continuousOn.comp
  · apply continuousOn_pi.mpr
    intro i
    fin_cases i
    · exact hx
    · exact hy
  · exact mapsTo_univ _ _

noncomputable def slitHomeomorph : (slitᶜ : Set Plane) ≃ₜ Plane where
  toFun z := psi z
  invFun w := ⟨inversePsi w, inversePsi_not_mem_slit w⟩
  left_inv z := Subtype.ext (inversePsi_psi z.property)
  right_inv := psi_inversePsi
  continuous_toFun := continuousOn_psi.domRestrict
  continuous_invFun := continuous_inversePsi.subtype_mk _

/-- Join two bijections on a partition and its complementary partition. -/
noncomputable def glue {α β : Type*} (s : Set α) (t : Set β) (g : s ≃ t)
    (h : (sᶜ : Set α) ≃ (tᶜ : Set β)) : α ≃ β := by
  classical
  exact (Equiv.Set.sumCompl s).symm.trans
    ((Equiv.sumCongr g h).trans (Equiv.Set.sumCompl t))

theorem glue_apply_mem {α β : Type*} (s : Set α) (t : Set β) (g : s ≃ t)
    (h : (sᶜ : Set α) ≃ (tᶜ : Set β)) (z : α) (hz : z ∈ s) :
    glue s t g h z = (g ⟨z, hz⟩ : β) := by
  classical
  simp [glue, Equiv.Set.sumCompl_symm_apply_of_mem hz]

theorem glue_apply_notMem {α β : Type*} (s : Set α) (t : Set β) (g : s ≃ t)
    (h : (sᶜ : Set α) ≃ (tᶜ : Set β)) (z : α) (hz : z ∉ s) :
    glue s t g h z = (h ⟨z, hz⟩ : β) := by
  classical
  simp [glue, Equiv.Set.sumCompl_symm_apply_of_notMem hz]

theorem continuousOn_glue_compl (s t : Set Plane) (g : s ≃ t)
    (h : (sᶜ : Set Plane) ≃ₜ (tᶜ : Set Plane)) :
    ContinuousOn (glue s t g h.toEquiv) (sᶜ : Set Plane) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  exact (continuous_subtype_val.comp h.continuous).congr
    (fun z => (glue_apply_notMem s t g h.toEquiv z z.property).symm)

theorem connected_subtype_preimage {s t : Set X} (hts : t ⊆ s)
    (ht : IsConnected t) : IsConnected (((↑) : s → X) ⁻¹' t) := by
  have himage : ((↑) : s → X) '' (((↑) : s → X) ⁻¹' t) = t := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hz
      exact ⟨⟨z, hts hz⟩, hz, rfl⟩
  refine ⟨?_, Topology.IsInducing.subtypeVal.isPreconnected_image.mp ?_⟩
  · obtain ⟨z, hz⟩ := ht.nonempty
    exact ⟨⟨z, hts hz⟩, hz⟩
  · rw [himage]
    exact ht.isPreconnected

theorem isConnected_glue_image_on_set (s t : Set Plane) (g : s ≃ t)
    (h : (sᶜ : Set Plane) ≃ (tᶜ : Set Plane))
    (hg : IsConnectedMap (fun z : s => (g z : Plane)))
    (c : Set Plane) (hcs : c ⊆ s) (hc : IsConnected c) :
    IsConnected (glue s t g h '' c) := by
  have hi := hg (connected_subtype_preimage hcs hc)
  have heq : (fun z : s => (g z : Plane)) '' (((↑) : s → Plane) ⁻¹' c) =
      glue s t g h '' c := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, glue_apply_mem s t g h x x.property⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hcs hx⟩, hx, (glue_apply_mem s t g h x (hcs hx)).symm⟩
  rwa [heq] at hi

theorem glue_preimage (s t : Set Plane) (g : s ≃ t)
    (h : (sᶜ : Set Plane) ≃ (tᶜ : Set Plane))
    (a c : Set Plane) (hat : a ⊆ t) (hcs : c ⊆ s)
    (hg : ∀ z : s, (g z : Plane) ∈ a ↔ (z : Plane) ∈ c) :
    (glue s t g h) ⁻¹' a = c := by
  ext z
  change glue s t g h z ∈ a ↔ z ∈ c
  by_cases hz : z ∈ s
  · rw [glue_apply_mem s t g h z hz]
    exact hg ⟨z, hz⟩
  · constructor
    · intro hza
      have hout := (h ⟨z, hz⟩).property
      have hin := hat hza
      rw [glue_apply_notMem s t g h z hz] at hin
      exact False.elim (hout hin)
    · intro hzc
      exact False.elim (hz (hcs hzc))

/-- Data which the geometric and ray-assignment parts of the construction
must supply. This structure is a hypothesis, not an existence assertion. -/
structure PlanarData where
  boundary : Set Plane
  exterior : (slitᶜ : Set Plane) ≃ₜ (boundaryᶜ : Set Plane)
  rayMap : slit ≃ boundary
  ray_connected : IsConnectedMap (fun z : slit => (rayMap z : Plane))
  recurrent : ∀ p ∈ boundary, ∀ o : Set Plane, IsOpen o → p ∈ o →
    ∀ ε : ℝ, 0 < ε → ∃ τ : ℝ, 0 < τ ∧ τ < ε ∧
      ∀ z : (slitᶜ : Set Plane), rho z = τ → (exterior z : Plane) ∈ o
  arc : Set Plane
  arc_subset : arc ⊆ boundary
  arc_connected : IsConnected arc
  ray_arc_preimage : ∀ z : slit, (rayMap z : Plane) ∈ arc ↔ (z : Plane) ∈ planeCantor

noncomputable def PlanarData.bijection (d : PlanarData) : Plane ≃ Plane :=
  glue slit d.boundary d.rayMap d.exterior.toEquiv

theorem PlanarData.bijection_isConnectedMap (d : PlanarData) :
    IsConnectedMap d.bijection := by
  apply isConnectedMap_of_recurrent_levels d.bijection rho continuous_rho rho_nonneg
  · have he : {z : Plane | rho z ≠ 0} = (slitᶜ : Set Plane) := by
      ext z
      simp only [mem_ofPred_eq, mem_compl_iff, ← rho_eq_zero_iff]
    rw [he]
    exact continuousOn_glue_compl slit d.boundary d.rayMap d.exterior
  · intro c hcs hc
    apply isConnected_glue_image_on_set slit d.boundary d.rayMap d.exterior.toEquiv
      d.ray_connected c _ hc
    intro z hz
    exact (rho_eq_zero_iff z).mp (hcs hz)
  · intro y hy o ho hyo ε hε
    have hys : y ∈ slit := (rho_eq_zero_iff y).mp hy
    have he : d.bijection y = (d.rayMap ⟨y, hys⟩ : Plane) :=
      glue_apply_mem slit d.boundary d.rayMap d.exterior.toEquiv y hys
    have hyb : d.bijection y ∈ d.boundary := he ▸ (d.rayMap ⟨y, hys⟩).property
    obtain ⟨τ, hτ, hτε, hgate⟩ := d.recurrent (d.bijection y) hyb o ho hyo ε hε
    refine ⟨τ, hτ, hτε, ?_⟩
    intro z hz
    have hzs : z ∉ slit := by
      intro h
      have hez := (rho_eq_zero_iff z).mpr h
      linarith
    rw [PlanarData.bijection, glue_apply_notMem slit d.boundary d.rayMap
      d.exterior.toEquiv z hzs]
    exact hgate ⟨z, hzs⟩ hz

theorem PlanarData.bijection_preimage_arc (d : PlanarData) :
    d.bijection ⁻¹' d.arc = planeCantor :=
  glue_preimage slit d.boundary d.rayMap d.exterior.toEquiv d.arc planeCantor
    d.arc_subset planeCantor_subset_slit d.ray_arc_preimage

theorem PlanarData.inverse_not_isConnectedMap (d : PlanarData) :
    ¬ IsConnectedMap d.bijection.symm := by
  intro h
  have hi := h d.arc_connected
  rw [Equiv.image_symm_eq_preimage, d.bijection_preimage_arc] at hi
  exact not_isConnected_planeCantor hi

/-- The exact universal assertion on the right of the repository's answer. -/
def RepositoryAssertion : Prop :=
  ∀ n > 1, ∀ f : EuclideanSpace ℝ (Fin n) ≃ EuclideanSpace ℝ (Fin n),
    Mathoverflow235893.IsConnectedMap f → Mathoverflow235893.IsConnectedMap f.symm

/-- The assembly is checked, conditional on constructing `PlanarData`. -/
theorem PlanarData.not_repositoryAssertion (d : PlanarData) : ¬ RepositoryAssertion := by
  intro h
  exact d.inverse_not_isConnectedMap
    (h 2 (by norm_num) d.bijection d.bijection_isConnectedMap)

theorem PlanarData.repository_answer_false (d : PlanarData) :
    False ↔ ∀ n > 1, ∀ f : EuclideanSpace ℝ (Fin n) ≃ EuclideanSpace ℝ (Fin n),
      Mathoverflow235893.IsConnectedMap f → Mathoverflow235893.IsConnectedMap f.symm := by
  exact iff_of_false False.elim d.not_repositoryAssertion

/-- Geometric data before composing with the explicit slit-plane coordinates. -/
structure CanalModel where
  boundary : Set Plane
  straightening : Plane ≃ₜ (boundaryᶜ : Set Plane)
  recurrent_lines : ∀ p ∈ boundary, ∀ o : Set Plane, IsOpen o → p ∈ o →
    ∀ m : ℕ, ∃ j : ℕ, m ≤ j ∧
      ∀ w : Plane, w 1 = (j : ℝ) → (straightening w : Plane) ∈ o

def horizontalPieces : Option ℕ → Set Plane :=
  Option.elim' {w | w 1 ≤ 1} (fun n => {w | (n : ℝ) + 1 ≤ w 1 ∧ w 1 ≤ (n : ℝ) + 2})

theorem horizontalPieces_cover : ∀ w : Plane, ∃ i, w ∈ horizontalPieces i := by
  intro w
  by_cases hw : w 1 ≤ 1
  · exact ⟨none, hw⟩
  · refine ⟨some ⌊w 1 - 1⌋₊, ?_⟩
    change (⌊w 1 - 1⌋₊ : ℝ) + 1 ≤ w 1 ∧ w 1 ≤ (⌊w 1 - 1⌋₊ : ℝ) + 2
    have hfloor := Nat.floor_le (show 0 ≤ w 1 - 1 by linarith)
    have hfloor' := Nat.lt_floor_add_one (w 1 - 1)
    constructor <;> linarith

theorem horizontalPieces_closed : ∀ i, IsClosed (horizontalPieces i) := by
  intro i
  cases i with
  | none => exact isClosed_le (continuous_coord 1) continuous_const
  | some n =>
    exact (isClosed_le continuous_const (continuous_coord 1)).inter
      (isClosed_le (continuous_coord 1) continuous_const)

theorem horizontalPieces_locallyFinite : LocallyFinite horizontalPieces := by
  open Filter in
    have hlf : LocallyFinite (fun n : ℤ => Icc (n : ℝ) ((n : ℝ) + 1)) :=
      locallyFinite_Icc_of_tendsto tendsto_intCast_atTop_atTop
        (tendsto_atBot_add_const_right atBot 1 (tendsto_intCast_atBot_iff.mpr tendsto_id))
  have hshift : Function.Injective (fun n : ℕ => (n : ℤ) + 1) := by
    intro i j h
    exact_mod_cast add_right_cancel h
  have hnat : LocallyFinite (fun n : ℕ => Icc ((n : ℝ) + 1) ((n : ℝ) + 2)) := by
    simpa [Function.comp_def, add_assoc, show (1 : ℝ) + 1 = 2 by norm_num] using
      hlf.comp_injective hshift
  exact (hnat.preimage_continuous (continuous_coord 1)).option_elim' _

theorem lowerEdge_mem_horizontalPieces {n : ℕ} {w : Plane}
    (hw : w 1 = (n : ℝ) + 1) : w ∈ horizontalPieces (some n) := by
  change (n : ℝ) + 1 ≤ w 1 ∧ w 1 ≤ (n : ℝ) + 2
  rw [hw]
  constructor <;> linarith

/-- A stripwise formulation of the crosscut straightening input. The source
cover and its local finiteness are supplied by the preceding theorems. -/
structure CanalStripAtlas (k : Set Plane) where
  target : Option ℕ → Set (kᶜ : Set Plane)
  target_cover : ∀ y, ∃ i, y ∈ target i
  target_closed : ∀ i, IsClosed (target i)
  target_locallyFinite : LocallyFinite target
  chart : ∀ i, horizontalPieces i ≃ₜ target i
  compatible : ∀ i j w (hi : w ∈ horizontalPieces i) (hj : w ∈ horizontalPieces j),
    (chart i ⟨w, hi⟩ : (kᶜ : Set Plane)) = (chart j ⟨w, hj⟩ : (kᶜ : Set Plane))
  inverse_compatible : ∀ i j y (hi : y ∈ target i) (hj : y ∈ target j),
    ((chart i).symm ⟨y, hi⟩ : Plane) = ((chart j).symm ⟨y, hj⟩ : Plane)
  recurrent_edges : ∀ p ∈ k, ∀ o : Set Plane, IsOpen o → p ∈ o →
    ∀ m : ℕ, ∃ n : ℕ, m ≤ n ∧ ∀ w : Plane, ∀ hw : w 1 = (n : ℝ) + 1,
      ((chart (some n) ⟨w, lowerEdge_mem_horizontalPieces hw⟩ : (kᶜ : Set Plane)) : Plane) ∈ o

noncomputable def CanalStripAtlas.toGluing {k : Set Plane} (d : CanalStripAtlas k) :
    ClosedCoverHomeomorphData Plane (kᶜ : Set Plane) (Option ℕ) where
  source := horizontalPieces
  target := d.target
  source_cover := horizontalPieces_cover
  target_cover := d.target_cover
  source_closed := horizontalPieces_closed
  target_closed := d.target_closed
  source_locallyFinite := horizontalPieces_locallyFinite
  target_locallyFinite := d.target_locallyFinite
  chart := d.chart
  compatible := d.compatible
  inverse_compatible := d.inverse_compatible

noncomputable def CanalStripAtlas.toCanalModel {k : Set Plane} (d : CanalStripAtlas k) :
    CanalModel where
  boundary := k
  straightening := d.toGluing.toHomeomorph
  recurrent_lines := by
    intro p hp o ho hpo m
    obtain ⟨n, hmn, hgate⟩ := d.recurrent_edges p hp o ho hpo m
    refine ⟨n + 1, by omega, ?_⟩
    intro w hw
    have hw' : w 1 = (n : ℝ) + 1 := by simpa only [Nat.cast_add, Nat.cast_one] using hw
    rw [d.toGluing.toHomeomorph_on (some n) w (lowerEdge_mem_horizontalPieces hw')]
    exact hgate w hw'

/-- The purely set-theoretic assignment which must be made on the ray. -/
structure RayModel (boundary : Set Plane) where
  bijection : slit ≃ boundary
  connected : IsConnectedMap (fun z : slit => (bijection z : Plane))
  arc : Set Plane
  arc_subset : arc ⊆ boundary
  arc_connected : IsConnected arc
  arc_preimage : ∀ z : slit, (bijection z : Plane) ∈ arc ↔ (z : Plane) ∈ planeCantor

def rayCoord (z : slit) : ℝ := (z : Plane) 0

theorem continuous_rayCoord : Continuous rayCoord :=
  (continuous_coord 0).comp continuous_subtype_val

theorem rayCoord_injective : Function.Injective rayCoord := by
  intro x y hxy
  apply Subtype.ext
  apply (EuclideanSpace.equiv (Fin 2) ℝ).injective
  funext i
  fin_cases i
  · exact hxy
  · exact x.property.2.trans y.property.2.symm

/-- Interval density of connected target pieces is sufficient for the ray map. -/
theorem ray_isConnectedMap_of_interval_density (g : slit → Plane) (k : Set Plane)
    (hgk : ∀ z, g z ∈ k)
    (hinterval : ∀ a b : ℝ, 0 ≤ a → a < b →
      ∃ d : Set Plane, IsConnected d ∧ k ⊆ closure d ∧
        d ⊆ g '' {z : slit | a < rayCoord z ∧ rayCoord z < b}) :
    IsConnectedMap g := by
  classical
  intro s hs
  by_cases hss : s.Subsingleton
  · exact ⟨hs.nonempty.image g, (hss.image g).isPreconnected⟩
  have hc := hs.image rayCoord continuous_rayCoord.continuousOn
  have hn := (not_subsingleton_iff.mp hss).image rayCoord_injective
  obtain ⟨a, ha, b, hb, hab⟩ := hn.exists_lt
  have ha0 : 0 ≤ a := by
    obtain ⟨x, -, rfl⟩ := ha
    exact x.property.1
  obtain ⟨d, hd, hkd, hdg⟩ := hinterval a b ha0 hab
  have hsub : {z : slit | a < rayCoord z ∧ rayCoord z < b} ⊆ s := by
    intro z hz
    obtain ⟨w, hw, hwz⟩ := hc.isPreconnected.ordConnected.out ha hb
      (show rayCoord z ∈ Icc a b from ⟨hz.1.le, hz.2.le⟩)
    exact rayCoord_injective hwz ▸ hw
  apply connected_of_dense_connected_subset hd (hdg.trans (image_mono hsub))
  rintro y ⟨z, -, rfl⟩
  exact hkd (hgk z)

theorem ray_isConnectedMap_of_dense_pieces (g : slit → Plane) (k : Set Plane)
    (c : ℕ → Set slit) (d : ℕ → Set Plane)
    (hgk : ∀ z, g z ∈ k) (himage : ∀ j, g '' c j = d j)
    (hd : ∀ j, IsConnected (d j)) (hclosure : ∀ j, k ⊆ closure (d j))
    (hinterval : ∀ a b : ℝ, 0 ≤ a → a < b →
      ∃ j, c j ⊆ {z : slit | a < rayCoord z ∧ rayCoord z < b}) :
    IsConnectedMap g := by
  apply ray_isConnectedMap_of_interval_density g k hgk
  intro a b ha hab
  obtain ⟨j, hj⟩ := hinterval a b ha hab
  refine ⟨d j, hd j, hclosure j, ?_⟩
  rw [← himage j]
  exact image_mono hj

theorem cardinal_plane : Cardinal.mk Plane = Cardinal.continuum := by
  have he := Cardinal.mk_congr
    ((EuclideanSpace.equiv (Fin 2) ℝ).toEquiv.trans (finTwoArrowEquiv ℝ))
  rw [he, Cardinal.mk_prod, Cardinal.mk_real]
  simp only [Cardinal.lift_id, Cardinal.continuum_mul_self]

/-- Each nondegenerate connected planar set has continuum cardinality. -/
theorem cardinal_connected_plane_set (c : Set Plane) (hc : IsConnected c)
    (hnt : c.Nontrivial) : Cardinal.mk c = Cardinal.continuum := by
  apply le_antisymm
  · exact cardinal_plane ▸ Cardinal.mk_set_le c
  · by_contra h
    have hlt : Cardinal.mk c < Cardinal.continuum := lt_of_not_ge h
    let : TotallySeparatedSpace c :=
      CompletelyRegularSpace.totallySeparatedSpace_of_cardinalMk_lt_continuum hlt
    let : ConnectedSpace c := isConnected_iff_connectedSpace.mp hc
    let : Subsingleton c := subsingleton_of_preconnected_totallyDisconnected
    obtain ⟨x, hx, y, hy, hxy⟩ := hnt
    exact hxy (congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : c) ⟨y, hy⟩))

theorem cardinal_cantorSet : Cardinal.mk cantorSet = Cardinal.continuum := by
  rw [Cardinal.mk_congr cantorSetEquivNatToBool, Cardinal.mk_arrow]
  simp only [Cardinal.mk_bool, Cardinal.mk_nat, Cardinal.lift_id, Cardinal.continuum]

theorem ray_injective : Function.Injective ray := by
  intro a b hab
  exact congrArg (fun z : Plane => z 0) hab

theorem cardinal_planeCantor : Cardinal.mk planeCantor = Cardinal.continuum := by
  have hinj : Function.Injective (fun t : cantorSet =>
      (⟨ray t, ⟨t, t.property, rfl⟩⟩ : planeCantor)) := by
    intro x y hxy
    exact Subtype.ext (ray_injective (congrArg Subtype.val hxy))
  have hsurj : Function.Surjective (fun t : cantorSet =>
      (⟨ray t, ⟨t, t.property, rfl⟩⟩ : planeCantor)) := by
    rintro ⟨z, t, ht, rfl⟩
    exact ⟨⟨t, ht⟩, rfl⟩
  rw [← Cardinal.mk_congr (Equiv.ofBijective _ ⟨hinj, hsurj⟩)]
  exact cardinal_cantorSet

theorem cardinal_slit : Cardinal.mk slit = Cardinal.continuum := by
  apply le_antisymm
  · exact cardinal_plane ▸ Cardinal.mk_set_le slit
  · exact cardinal_planeCantor ▸ Cardinal.mk_le_mk_of_subset planeCantor_subset_slit

noncomputable def reserveCantor : Set Plane := (fun t : ℝ => ray (2 + t)) '' cantorSet

theorem reserveCantor_subset_slit : reserveCantor ⊆ slit := by
  rintro z ⟨t, ht, rfl⟩
  refine ⟨?_, rfl⟩
  change 0 ≤ 2 + t
  linarith [(cantorSet_subset_unitInterval ht).1]

theorem cardinal_reserveCantor : Cardinal.mk reserveCantor = Cardinal.continuum := by
  have hinj : Function.Injective (fun t : ℝ => ray (2 + t)) := by
    intro a b hab
    have h := ray_injective hab
    linarith
  rw [reserveCantor, Cardinal.mk_image_eq hinj]
  exact cardinal_cantorSet

theorem disjoint_planeCantor_reserveCantor : Disjoint planeCantor reserveCantor := by
  apply Set.disjoint_left.mpr
  rintro z ⟨t, ht, rfl⟩ ⟨u, hu, he⟩
  have hcoords := congrArg (fun w : Plane => w 0) he
  change 2 + u = t at hcoords
  linarith [(cantorSet_subset_unitInterval ht).2, (cantorSet_subset_unitInterval hu).1]

theorem cardinal_subtype_preimage {s t : Set Plane} (hts : t ⊆ s) :
    Cardinal.mk (((↑) : s → Plane) ⁻¹' t) = Cardinal.mk t := by
  have himage : ((↑) : s → Plane) '' (((↑) : s → Plane) ⁻¹' t) = t := by
    apply image_preimage_eq_of_subset
    simpa only [Subtype.range_val] using hts
  rw [← Cardinal.mk_image_eq Subtype.val_injective, himage]

theorem cardinal_rayReserve :
    Cardinal.mk (((↑) : slit → Plane) ⁻¹' reserveCantor) = Cardinal.continuum := by
  rw [cardinal_subtype_preimage reserveCantor_subset_slit]
  exact cardinal_reserveCantor

section PiecewiseAssignment

variable {α β ι : Type*}

noncomputable def pieceUnionEquiv (c : ι → Set α) (d : ι → Set β)
    (hc : Pairwise (fun i j => Disjoint (c i) (c j)))
    (hd : Pairwise (fun i j => Disjoint (d i) (d j)))
    (e : ∀ i, c i ≃ d i) : (⋃ i, c i) ≃ (⋃ i, d i) :=
  (unionEqSigmaOfDisjoint hc).trans
    ((Equiv.sigmaCongrRight e).trans (unionEqSigmaOfDisjoint hd).symm)

theorem pieceUnionEquiv_apply_mem (c : ι → Set α) (d : ι → Set β)
    (hc : Pairwise (fun i j => Disjoint (c i) (c j)))
    (hd : Pairwise (fun i j => Disjoint (d i) (d j)))
    (e : ∀ i, c i ≃ d i) (i : ι) (x : α) (hx : x ∈ c i) :
    (pieceUnionEquiv c d hc hd e ⟨x, mem_iUnion.mpr ⟨i, hx⟩⟩ : β) =
      (e i ⟨x, hx⟩ : β) := by
  have heq : unionEqSigmaOfDisjoint hc ⟨x, mem_iUnion.mpr ⟨i, hx⟩⟩ =
      Sigma.mk i ⟨x, hx⟩ := by
    apply (unionEqSigmaOfDisjoint hc).eq_symm_apply.mp
    exact Subtype.ext rfl
  simp [pieceUnionEquiv, heq]

noncomputable def completePieces (c : ι → Set α) (d : ι → Set β)
    (hc : Pairwise (fun i j => Disjoint (c i) (c j)))
    (hd : Pairwise (fun i j => Disjoint (d i) (d j)))
    (e : ∀ i, c i ≃ d i)
    (r : ((⋃ i, c i)ᶜ : Set α) ≃ ((⋃ i, d i)ᶜ : Set β)) : α ≃ β :=
  glue (⋃ i, c i) (⋃ i, d i) (pieceUnionEquiv c d hc hd e) r

theorem completePieces_apply_mem (c : ι → Set α) (d : ι → Set β)
    (hc : Pairwise (fun i j => Disjoint (c i) (c j)))
    (hd : Pairwise (fun i j => Disjoint (d i) (d j)))
    (e : ∀ i, c i ≃ d i)
    (r : ((⋃ i, c i)ᶜ : Set α) ≃ ((⋃ i, d i)ᶜ : Set β))
    (i : ι) (x : α) (hx : x ∈ c i) :
    completePieces c d hc hd e r x = (e i ⟨x, hx⟩ : β) := by
  rw [completePieces, glue_apply_mem _ _ _ r x (mem_iUnion.mpr ⟨i, hx⟩)]
  exact pieceUnionEquiv_apply_mem c d hc hd e i x hx

theorem completePieces_image_piece (c : ι → Set α) (d : ι → Set β)
    (hc : Pairwise (fun i j => Disjoint (c i) (c j)))
    (hd : Pairwise (fun i j => Disjoint (d i) (d j)))
    (e : ∀ i, c i ≃ d i)
    (r : ((⋃ i, c i)ᶜ : Set α) ≃ ((⋃ i, d i)ᶜ : Set β)) (i : ι) :
    completePieces c d hc hd e r '' c i = d i := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [completePieces_apply_mem c d hc hd e r i x hx]
    exact (e i ⟨x, hx⟩).property
  · intro hy
    let x := (e i).symm ⟨y, hy⟩
    refine ⟨x, x.property, ?_⟩
    rw [completePieces_apply_mem c d hc hd e r i x x.property]
    exact congrArg Subtype.val ((e i).apply_symm_apply ⟨y, hy⟩)

/-- Equal continuum cardinalities give the required complementary bijection. -/
noncomputable def equivOfContinuum (s : Set α) (t : Set β)
    (hs : Cardinal.mk s = Cardinal.continuum)
    (ht : Cardinal.mk t = Cardinal.continuum) : s ≃ t :=
  Classical.choice (Cardinal.lift_mk_eq'.mp (by simp only [hs, ht, Cardinal.lift_continuum]))

theorem cardinal_of_reserved_subset (s r : Set α) (hrs : r ⊆ s)
    (hα : Cardinal.mk α = Cardinal.continuum)
    (hr : Cardinal.mk r = Cardinal.continuum) : Cardinal.mk s = Cardinal.continuum := by
  exact le_antisymm (hα ▸ Cardinal.mk_set_le s) (hr ▸ Cardinal.mk_le_mk_of_subset hrs)

theorem cardinal_unassigned_of_reserved (c : ι → Set α) (r : Set α)
    (hα : Cardinal.mk α = Cardinal.continuum)
    (hr : Cardinal.mk r = Cardinal.continuum)
    (hdisj : ∀ i, Disjoint r (c i)) :
    Cardinal.mk ((⋃ i, c i)ᶜ : Set α) = Cardinal.continuum := by
  apply cardinal_of_reserved_subset _ r _ hα hr
  intro x hx hc
  obtain ⟨i, hi⟩ := mem_iUnion.mp hc
  exact (hdisj i).le_bot ⟨hx, hi⟩

end PiecewiseAssignment

/-- Countably many assigned pieces, with one reserved continuum-sized set
on each side. The construction of these pieces remains an existence task. -/
structure RayPartition (k : Set Plane) where
  source : ℕ → Set slit
  target : ℕ → Set k
  source_disjoint : Pairwise (fun i j => Disjoint (source i) (source j))
  target_disjoint : Pairwise (fun i j => Disjoint (target i) (target j))
  source_card : ∀ j, Cardinal.mk (source j) = Cardinal.continuum
  target_card : ∀ j, Cardinal.mk (target j) = Cardinal.continuum
  source_reserve : Set slit
  source_reserve_card : Cardinal.mk source_reserve = Cardinal.continuum
  source_reserve_disjoint : ∀ j, Disjoint source_reserve (source j)
  target_reserve : Set k
  target_reserve_card : Cardinal.mk target_reserve = Cardinal.continuum
  target_reserve_disjoint : ∀ j, Disjoint target_reserve (target j)
  source_zero : source 0 = ((↑) : slit → Plane) ⁻¹' planeCantor
  target_zero_connected : IsConnected (((↑) : k → Plane) '' target 0)
  target_connected : ∀ j, IsConnected (((↑) : k → Plane) '' target (j + 1))
  target_dense : ∀ j, k ⊆ closure (((↑) : k → Plane) '' target (j + 1))
  interval : ∀ a b : ℝ, 0 ≤ a → a < b →
    ∃ j, source (j + 1) ⊆ {z : slit | a < rayCoord z ∧ rayCoord z < b}

theorem RayPartition.cardinal_boundary {k : Set Plane} (d : RayPartition k) :
    Cardinal.mk k = Cardinal.continuum := by
  exact le_antisymm (cardinal_plane ▸ Cardinal.mk_set_le k)
    (d.target_card 0 ▸ Cardinal.mk_set_le (d.target 0))

noncomputable def RayPartition.pieceEquiv {k : Set Plane} (d : RayPartition k) (j : ℕ) :
    d.source j ≃ d.target j :=
  equivOfContinuum _ _ (d.source_card j) (d.target_card j)

noncomputable def RayPartition.remainderEquiv {k : Set Plane} (d : RayPartition k) :
    ((⋃ j, d.source j)ᶜ : Set slit) ≃ ((⋃ j, d.target j)ᶜ : Set k) :=
  equivOfContinuum _ _
    (cardinal_unassigned_of_reserved d.source d.source_reserve cardinal_slit
      d.source_reserve_card d.source_reserve_disjoint)
    (cardinal_unassigned_of_reserved d.target d.target_reserve d.cardinal_boundary
      d.target_reserve_card d.target_reserve_disjoint)

noncomputable def RayPartition.bijection {k : Set Plane} (d : RayPartition k) : slit ≃ k :=
  completePieces d.source d.target d.source_disjoint d.target_disjoint
    d.pieceEquiv d.remainderEquiv

theorem RayPartition.image_piece {k : Set Plane} (d : RayPartition k) (j : ℕ) :
    (fun z : slit => (d.bijection z : Plane)) '' d.source j =
      ((↑) : k → Plane) '' d.target j := by
  have he := completePieces_image_piece d.source d.target d.source_disjoint
    d.target_disjoint d.pieceEquiv d.remainderEquiv j
  have he' := congrArg (fun s : Set k => ((↑) : k → Plane) '' s) he
  simpa only [image_image, RayPartition.bijection] using he'

theorem RayPartition.isConnectedMap {k : Set Plane} (d : RayPartition k) :
    IsConnectedMap (fun z : slit => (d.bijection z : Plane)) := by
  apply ray_isConnectedMap_of_dense_pieces _ k
    (fun j => d.source (j + 1)) (fun j => ((↑) : k → Plane) '' d.target (j + 1))
  · exact fun z => (d.bijection z).property
  · exact fun j => d.image_piece (j + 1)
  · exact d.target_connected
  · exact d.target_dense
  · exact d.interval

theorem RayPartition.arc_preimage {k : Set Plane} (d : RayPartition k) (z : slit) :
    (d.bijection z : Plane) ∈ ((↑) : k → Plane) '' d.target 0 ↔
      (z : Plane) ∈ planeCantor := by
  rw [← d.image_piece 0]
  have hinj : Function.Injective (fun z' : slit => (d.bijection z' : Plane)) :=
    Subtype.val_injective.comp d.bijection.injective
  rw [hinj.mem_set_image, d.source_zero]
  rfl

/-- The standard Cantor set contains no real interval of positive length. -/
theorem interior_cantorSet_eq_empty : interior cantorSet = ∅ := by
  let : TotallyDisconnectedSpace cantorSet :=
    cantorSetHomeomorphNatToBool.symm.totallyDisconnectedSpace
  have htd : IsTotallyDisconnected cantorSet := totallyDisconnectedSpace_subtype_iff.mp
    (inferInstance : TotallyDisconnectedSpace cantorSet)
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior x hx
  have hsub : Icc x (x + ε / 2) ⊆ cantorSet := by
    intro y hy
    apply interior_subset (hball _)
    rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (by linarith [hy.1])]
    linarith [hy.2]
  have hss := htd (Icc x (x + ε / 2)) hsub isPreconnected_Icc
  have he := hss (show x ∈ Icc x (x + ε / 2) by constructor <;> linarith)
    (show x + ε / 2 ∈ Icc x (x + ε / 2) by constructor <;> linarith)
  linarith

theorem isNowhereDense_cantorSet : IsNowhereDense cantorSet :=
  isClosed_cantorSet.isNowhereDense_iff.mpr interior_cantorSet_eq_empty

noncomputable def affineHomeomorph (a b : ℝ) (hab : a < b) : ℝ ≃ₜ ℝ where
  toFun t := a + (b - a) * t
  invFun t := (t - a) / (b - a)
  left_inv t := by
    have hne : b - a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
    field_simp
    ring
  right_inv t := by
    have hne : b - a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
    field_simp
    ring
  continuous_toFun := continuous_const.add (continuous_const.mul continuous_id)
  continuous_invFun := (continuous_id.sub continuous_const).div_const _

theorem exists_compact_cantor_subset_open (o : Set ℝ) (ho : IsOpen o) (hne : o.Nonempty) :
    ∃ c : Set ℝ, c ⊆ o ∧ IsCompact c ∧ IsNowhereDense c ∧
      Cardinal.mk c = Cardinal.continuum := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp ho x hx
  let h := affineHomeomorph (x - ε / 2) (x + ε / 2) (by linarith)
  refine ⟨h '' cantorSet, ?_, isCompact_cantorSet.image h.continuous,
    h.isInducing.isNowhereDense_image isNowhereDense_cantorSet, ?_⟩
  · rintro y ⟨t, ht, rfl⟩
    apply hball
    rw [Metric.mem_ball, Real.dist_eq]
    change |x - ε / 2 + (x + ε / 2 - (x - ε / 2)) * t - x| < ε
    apply abs_lt.mpr
    constructor
    · nlinarith [(cantorSet_subset_unitInterval ht).1,
        mul_nonneg hε.le (cantorSet_subset_unitInterval ht).1]
    · nlinarith [(cantorSet_subset_unitInterval ht).2,
        mul_nonneg hε.le (sub_nonneg.mpr (cantorSet_subset_unitInterval ht).2)]
  · rw [Cardinal.mk_image_eq h.injective]
    exact cardinal_cantorSet

theorem closed_nowhereDense_union (s t : Set ℝ) (hs : IsClosed s) (ht : IsClosed t)
    (hsn : IsNowhereDense s) (htn : IsNowhereDense t) : IsNowhereDense (s ∪ t) := by
  have hsd := (isClosed_isNowhereDense_iff_compl.mp ⟨hs, hsn⟩).2
  have htd := (isClosed_isNowhereDense_iff_compl.mp ⟨ht, htn⟩).2
  apply (hs.union ht).isNowhereDense_iff.mpr
  apply interior_eq_empty_iff_dense_compl.mpr
  rw [compl_union]
  exact hsd.inter_of_isOpen_right htd ht.isOpen_compl

theorem exists_compact_cantor_avoiding (o s : Set ℝ) (ho : IsOpen o) (hne : o.Nonempty)
    (hs : IsClosed s) (hsn : IsNowhereDense s) :
    ∃ c : Set ℝ, c ⊆ o ∧ Disjoint c s ∧ IsCompact c ∧ IsNowhereDense c ∧
      Cardinal.mk c = Cardinal.continuum := by
  have hd := (isClosed_isNowhereDense_iff_compl.mp ⟨hs, hsn⟩).2
  obtain ⟨c, hco, hcc, hcn, hcard⟩ := exists_compact_cantor_subset_open (o ∩ sᶜ)
    (ho.inter hs.isOpen_compl) (hd.inter_open_nonempty o ho hne)
  refine ⟨c, hco.trans inter_subset_left, ?_, hcc, hcn, hcard⟩
  exact disjoint_left.mpr (fun x hx hxs => (hco hx).2 hxs)

structure CantorChoice (o s : Set ℝ) where
  piece : Set ℝ
  subset_open : piece ⊆ o
  disjoint_old : Disjoint piece s
  compact : IsCompact piece
  nowhereDense : IsNowhereDense piece
  cardinal : Cardinal.mk piece = Cardinal.continuum

noncomputable def chooseCantor (o s : Set ℝ) (ho : IsOpen o) (hne : o.Nonempty)
    (hs : IsClosed s) (hsn : IsNowhereDense s) : CantorChoice o s := by
  choose c hco hcs hcc hcn hcard using exists_compact_cantor_avoiding o s ho hne hs hsn
  exact ⟨c, hco, hcs, hcc, hcn, hcard⟩

abbrev GoodCantorUnion := {s : Set ℝ // IsCompact s ∧ IsNowhereDense s}

noncomputable def cantorAccum (o : ℕ → Set ℝ) (ho : ∀ n, IsOpen (o n))
    (hne : ∀ n, (o n).Nonempty) (f : GoodCantorUnion) : ℕ → GoodCantorUnion :=
  Nat.rec f (fun n s =>
    let c := chooseCantor (o n) s (ho n) (hne n) s.property.1.isClosed s.property.2
    ⟨s.val ∪ c.piece, s.property.1.union c.compact,
      closed_nowhereDense_union s.val c.piece s.property.1.isClosed c.compact.isClosed
        s.property.2 c.nowhereDense⟩)

noncomputable def cantorAt (o : ℕ → Set ℝ) (ho : ∀ n, IsOpen (o n))
    (hne : ∀ n, (o n).Nonempty) (f : GoodCantorUnion) (n : ℕ) :
    CantorChoice (o n) (cantorAccum o ho hne f n).val :=
  chooseCantor (o n) (cantorAccum o ho hne f n).val (ho n) (hne n)
    (cantorAccum o ho hne f n).property.1.isClosed (cantorAccum o ho hne f n).property.2

theorem cantorAccum_succ (o : ℕ → Set ℝ) (ho : ∀ n, IsOpen (o n))
    (hne : ∀ n, (o n).Nonempty) (f : GoodCantorUnion) (n : ℕ) :
    (cantorAccum o ho hne f (n + 1)).val =
      (cantorAccum o ho hne f n).val ∪ (cantorAt o ho hne f n).piece := rfl

theorem cantorAccum_mono (o : ℕ → Set ℝ) (ho : ∀ n, IsOpen (o n))
    (hne : ∀ n, (o n).Nonempty) (f : GoodCantorUnion) :
    Monotone (fun n => (cantorAccum o ho hne f n).val) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [cantorAccum_succ]
  exact subset_union_left

theorem cantorAt_subset_accum (o : ℕ → Set ℝ) (ho : ∀ n, IsOpen (o n))
    (hne : ∀ n, (o n).Nonempty) (f : GoodCantorUnion) {i j : ℕ} (hij : i < j) :
    (cantorAt o ho hne f i).piece ⊆ (cantorAccum o ho hne f j).val := by
  have hi : (cantorAt o ho hne f i).piece ⊆ (cantorAccum o ho hne f (i + 1)).val := by
    rw [cantorAccum_succ]
    exact subset_union_right
  exact hi.trans (cantorAccum_mono o ho hne f (Nat.succ_le_of_lt hij))

theorem cantorAt_pairwise_disjoint (o : ℕ → Set ℝ) (ho : ∀ n, IsOpen (o n))
    (hne : ∀ n, (o n).Nonempty) (f : GoodCantorUnion) :
    Pairwise (fun i j => Disjoint (cantorAt o ho hne f i).piece
      (cantorAt o ho hne f j).piece) := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact ((cantorAt o ho hne f j).disjoint_old.mono_right
      (cantorAt_subset_accum o ho hne f hij)).symm
  · exact (cantorAt o ho hne f i).disjoint_old.mono_right
      (cantorAt_subset_accum o ho hne f hji)

theorem cantorAt_disjoint_initial (o : ℕ → Set ℝ) (ho : ∀ n, IsOpen (o n))
    (hne : ∀ n, (o n).Nonempty) (f : GoodCantorUnion) (n : ℕ) :
    Disjoint (cantorAt o ho hne f n).piece f.val := by
  have hf : f.val ⊆ (cantorAccum o ho hne f n).val :=
    cantorAccum_mono o ho hne f (Nat.zero_le n)
  exact (cantorAt o ho hne f n).disjoint_old.mono_right hf

abbrev PositiveRatPair := {p : ℚ × ℚ // 0 < p.1 ∧ p.1 < p.2}

noncomputable def rationalIntervalCode : ℕ → PositiveRatPair :=
  let : Encodable PositiveRatPair := Encodable.ofCountable PositiveRatPair
  fun n => (Encodable.decode n).getD ⟨(1, 2), by norm_num⟩

theorem rationalIntervalCode_surjective : Function.Surjective rationalIntervalCode := by
  let : Encodable PositiveRatPair := Encodable.ofCountable PositiveRatPair
  exact Encodable.surjective_decode_getD PositiveRatPair ⟨(1, 2), by norm_num⟩

noncomputable def rationalIntervals (n : ℕ) : Set ℝ :=
  Ioo ((rationalIntervalCode n).val.1 : ℝ) ((rationalIntervalCode n).val.2 : ℝ)

theorem rationalIntervals_open (n : ℕ) : IsOpen (rationalIntervals n) := isOpen_Ioo

theorem rationalIntervals_nonempty (n : ℕ) : (rationalIntervals n).Nonempty := by
  apply nonempty_Ioo.mpr
  exact_mod_cast (rationalIntervalCode n).property.2

theorem rationalIntervals_positive (n : ℕ) : rationalIntervals n ⊆ Ioi 0 := by
  intro x hx
  have hp : (0 : ℝ) < (rationalIntervalCode n).val.1 := by
    exact_mod_cast (rationalIntervalCode n).property.1
  exact hp.trans hx.1

theorem rationalIntervals_refine (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) :
    ∃ n, rationalIntervals n ⊆ Ioo a b := by
  obtain ⟨p, hap, hpb⟩ := exists_rat_btwn hab
  obtain ⟨q, hpq, hqb⟩ := exists_rat_btwn hpb
  let pair : PositiveRatPair := ⟨(p, q), by
    constructor
    · exact_mod_cast ha.trans_lt hap
    · exact_mod_cast hpq⟩
  obtain ⟨n, hn⟩ := rationalIntervalCode_surjective pair
  refine ⟨n, ?_⟩
  rw [rationalIntervals, hn]
  intro x hx
  exact ⟨hap.trans hx.1, hx.2.trans hqb⟩

def raySubset (c : Set ℝ) : Set slit := rayCoord ⁻¹' c

noncomputable def raySubsetEquiv (c : Set ℝ) (hc : c ⊆ Ici 0) : raySubset c ≃ c where
  toFun z := ⟨rayCoord z, z.property⟩
  invFun t := ⟨⟨ray t, ⟨hc t.property, rfl⟩⟩, t.property⟩
  left_inv _ := Subtype.ext (rayCoord_injective rfl)
  right_inv _ := rfl

theorem cardinal_raySubset (c : Set ℝ) (hc : c ⊆ Ici 0)
    (hcard : Cardinal.mk c = Cardinal.continuum) :
    Cardinal.mk (raySubset c) = Cardinal.continuum :=
  (Cardinal.mk_congr (raySubsetEquiv c hc)).trans hcard

theorem raySubset_cantorSet : raySubset cantorSet = ((↑) : slit → Plane) ⁻¹' planeCantor := by
  ext z
  constructor
  · intro hz
    refine ⟨rayCoord z, hz, ?_⟩
    change planeOf ((z : Plane) 0) 0 = (z : Plane)
    rw [← z.property.2]
    exact planeOf_coords z
  · rintro ⟨t, ht, he⟩
    have hcoords := congrArg (fun w : Plane => w 0) he
    change t = rayCoord z at hcoords
    change rayCoord z ∈ cantorSet
    exact hcoords ▸ ht

noncomputable def reserveRealCantor : Set ℝ := (fun t : ℝ => 2 + t) '' cantorSet

theorem compact_reserveRealCantor : IsCompact reserveRealCantor :=
  isCompact_cantorSet.image (continuous_const.add continuous_id)

theorem nowhereDense_reserveRealCantor : IsNowhereDense reserveRealCantor :=
  (Homeomorph.addLeft (2 : ℝ)).isInducing.isNowhereDense_image isNowhereDense_cantorSet

theorem cardinal_reserveRealCantor : Cardinal.mk reserveRealCantor = Cardinal.continuum := by
  rw [reserveRealCantor, Cardinal.mk_image_eq (add_right_injective (2 : ℝ))]
  exact cardinal_cantorSet

theorem reserveRealCantor_nonneg : reserveRealCantor ⊆ Ici 0 := by
  rintro x ⟨t, ht, rfl⟩
  have ht0 := (cantorSet_subset_unitInterval ht).1
  change 0 ≤ 2 + t
  linarith

theorem disjoint_cantorSet_reserveRealCantor : Disjoint cantorSet reserveRealCantor := by
  apply disjoint_left.mpr
  rintro x hx ⟨t, ht, rfl⟩
  linarith [(cantorSet_subset_unitInterval hx).2, (cantorSet_subset_unitInterval ht).1]

noncomputable def initialCantorUnion : GoodCantorUnion :=
  ⟨cantorSet ∪ reserveRealCantor, isCompact_cantorSet.union compact_reserveRealCantor,
    closed_nowhereDense_union _ _ isClosed_cantorSet compact_reserveRealCantor.isClosed
      isNowhereDense_cantorSet nowhereDense_reserveRealCantor⟩

noncomputable def sourceReal : ℕ → Set ℝ
  | 0 => cantorSet
  | n + 1 => (cantorAt rationalIntervals rationalIntervals_open rationalIntervals_nonempty
      initialCantorUnion n).piece

theorem sourceReal_nonneg (n : ℕ) : sourceReal n ⊆ Ici 0 := by
  cases n with
  | zero => exact fun _ hx => (cantorSet_subset_unitInterval hx).1
  | succ n =>
    intro x hx
    have hxpos : 0 < x := rationalIntervals_positive n
      ((cantorAt rationalIntervals rationalIntervals_open rationalIntervals_nonempty
        initialCantorUnion n).subset_open hx)
    exact hxpos.le

theorem sourceReal_cardinal (n : ℕ) : Cardinal.mk (sourceReal n) = Cardinal.continuum := by
  cases n with
  | zero => exact cardinal_cantorSet
  | succ n => exact (cantorAt rationalIntervals rationalIntervals_open rationalIntervals_nonempty
      initialCantorUnion n).cardinal

theorem sourceReal_pairwise_disjoint : Pairwise (fun i j => Disjoint (sourceReal i) (sourceReal j)) := by
  intro i j hij
  cases i with
  | zero =>
    cases j with
    | zero => exact False.elim (hij rfl)
    | succ j =>
      exact ((cantorAt_disjoint_initial rationalIntervals rationalIntervals_open
        rationalIntervals_nonempty initialCantorUnion j).mono_right subset_union_left).symm
  | succ i =>
    cases j with
    | zero =>
      exact (cantorAt_disjoint_initial rationalIntervals rationalIntervals_open
        rationalIntervals_nonempty initialCantorUnion i).mono_right subset_union_left
    | succ j =>
      exact cantorAt_pairwise_disjoint rationalIntervals rationalIntervals_open
        rationalIntervals_nonempty initialCantorUnion (fun h => hij (congrArg Nat.succ h))

theorem sourceReal_disjoint_reserve (n : ℕ) : Disjoint reserveRealCantor (sourceReal n) := by
  cases n with
  | zero => exact disjoint_cantorSet_reserveRealCantor.symm
  | succ n =>
    exact ((cantorAt_disjoint_initial rationalIntervals rationalIntervals_open
      rationalIntervals_nonempty initialCantorUnion n).mono_right subset_union_right).symm

theorem sourceReal_refine (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) :
    ∃ n, sourceReal (n + 1) ⊆ Ioo a b := by
  obtain ⟨n, hn⟩ := rationalIntervals_refine a b ha hab
  exact ⟨n, (cantorAt rationalIntervals rationalIntervals_open rationalIntervals_nonempty
    initialCantorUnion n).subset_open.trans hn⟩

/-- The full source-side partition data are constructed, without an existence hypothesis. -/
structure SourceFamily where
  pieces : ℕ → Set slit
  reserve : Set slit
  pairwise_disjoint : Pairwise (fun i j => Disjoint (pieces i) (pieces j))
  pieces_cardinal : ∀ n, Cardinal.mk (pieces n) = Cardinal.continuum
  reserve_cardinal : Cardinal.mk reserve = Cardinal.continuum
  reserve_disjoint : ∀ n, Disjoint reserve (pieces n)
  zero_piece : pieces 0 = ((↑) : slit → Plane) ⁻¹' planeCantor
  interval : ∀ a b : ℝ, 0 ≤ a → a < b →
    ∃ n, pieces (n + 1) ⊆ {z : slit | a < rayCoord z ∧ rayCoord z < b}

noncomputable def sourceFamily : SourceFamily where
  pieces n := raySubset (sourceReal n)
  reserve := raySubset reserveRealCantor
  pairwise_disjoint := by
    intro i j hij
    exact disjoint_left.mpr (fun _ hi hj => (sourceReal_pairwise_disjoint hij).le_bot ⟨hi, hj⟩)
  pieces_cardinal n := cardinal_raySubset _ (sourceReal_nonneg n) (sourceReal_cardinal n)
  reserve_cardinal := cardinal_raySubset _ reserveRealCantor_nonneg cardinal_reserveRealCantor
  reserve_disjoint := by
    intro n
    exact disjoint_left.mpr (fun _ hr hn => (sourceReal_disjoint_reserve n).le_bot ⟨hr, hn⟩)
  zero_piece := raySubset_cantorSet
  interval := by
    intro a b ha hab
    obtain ⟨n, hn⟩ := sourceReal_refine a b ha hab
    exact ⟨n, fun _ hz => hn hz⟩

/-- Target-side data supplied in the paper by distinct composants and one arc. -/
structure BoundaryPieces (k : Set Plane) where
  arc : Set Plane
  arc_subset : arc ⊆ k
  arc_connected : IsConnected arc
  arc_nontrivial : arc.Nontrivial
  densePieces : ℕ → Set Plane
  pieces_subset : ∀ n, densePieces n ⊆ k
  pieces_connected : ∀ n, IsConnected (densePieces n)
  pieces_nontrivial : ∀ n, (densePieces n).Nontrivial
  pieces_dense : ∀ n, k ⊆ closure (densePieces n)
  pieces_disjoint : Pairwise (fun i j => Disjoint (densePieces i) (densePieces j))
  arc_disjoint : ∀ n, Disjoint arc (densePieces n)
  reserve : Set Plane
  reserve_subset : reserve ⊆ k
  reserve_connected : IsConnected reserve
  reserve_nontrivial : reserve.Nontrivial
  reserve_arc_disjoint : Disjoint reserve arc
  reserve_pieces_disjoint : ∀ n, Disjoint reserve (densePieces n)

def punctured (p : X) : Set X := {x | x ≠ p}

def puncturedImage {p : X} {k : Set Plane} (e : punctured p ≃ₜ k) (c : Set X) :
    Set Plane :=
  (fun z : punctured p => (e z : Plane)) '' (((↑) : punctured p → X) ⁻¹' c)

theorem puncturedImage_subset {p : X} {k : Set Plane}
    (e : punctured p ≃ₜ k) (c : Set X) : puncturedImage e c ⊆ k := by
  rintro z ⟨x, -, rfl⟩
  exact (e x).property

theorem puncturedImage_connected {p : X} {k : Set Plane} (e : punctured p ≃ₜ k)
    {c : Set X} (hcp : c ⊆ punctured p) (hc : IsConnected c) :
    IsConnected (puncturedImage e c) :=
  (connected_subtype_preimage hcp hc).image _
    (continuous_subtype_val.comp e.continuous).continuousOn

theorem puncturedImage_nontrivial {p : X} {k : Set Plane} (e : punctured p ≃ₜ k)
    {c : Set X} (hcp : c ⊆ punctured p) (hc : c.Nontrivial) :
    (puncturedImage e c).Nontrivial := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hc
  have hsource : ((((↑) : punctured p → X) ⁻¹' c)).Nontrivial :=
    ⟨⟨x, hcp hx⟩, hx, ⟨y, hcp hy⟩, hy, fun h => hxy (congrArg Subtype.val h)⟩
  exact hsource.image (Subtype.val_injective.comp e.injective)

theorem puncturedImage_disjoint {p : X} {k : Set Plane} (e : punctured p ≃ₜ k)
    {c d : Set X} (hcd : Disjoint c d) :
    Disjoint (puncturedImage e c) (puncturedImage e d) := by
  apply (disjoint_image_iff (Subtype.val_injective.comp e.injective)).mpr
  exact disjoint_left.mpr (fun _ hc hd => hcd.le_bot ⟨hc, hd⟩)

theorem puncturedImage_dense {p : X} {k : Set Plane} (e : punctured p ≃ₜ k)
    {c : Set X} (hcp : c ⊆ punctured p) (hc : Dense c) :
    k ⊆ closure (puncturedImage e c) := by
  have himage : ((↑) : punctured p → X) '' (((↑) : punctured p → X) ⁻¹' c) = c := by
    apply image_preimage_eq_of_subset
    simpa only [Subtype.range_val] using hcp
  have hsource : Dense (((↑) : punctured p → X) ⁻¹' c) := by
    apply Subtype.dense_iff.mpr
    rw [himage]
    exact fun x _ => hc x
  have htarget := e.surjective.denseRange.dense_image e.continuous hsource
  simpa only [puncturedImage, image_image, Function.comp_def] using
    (Subtype.dense_iff.mp htarget)

/-- All boundary pieces are obtained from the ordinary composant theorem. The
remaining input is a punctured compact indecomposable continuum and an arc. -/
noncomputable def boundaryPieces_of_punctured_continuum [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [SecondCountableTopology X] [Nontrivial X]
    (hi : Indecomposable X) (p : X) {k : Set Plane} (e : punctured p ≃ₜ k)
    (c : Set X) (hc : ProperContinuum c) (hcn : c.Nontrivial) (hpc : p ∉ c) :
    BoundaryPieces k := by
  classical
  let a := Classical.choose hc.2.1.nonempty
  have hac : a ∈ c := Classical.choose_spec hc.2.1.nonempty
  let selection := exists_composant_sequence_avoiding hi p a
  let r := Classical.choose selection
  have hr : Pairwise (fun i j => composant (r i) ≠ composant (r j)) :=
    (Classical.choose_spec selection).1
  have havoid : ∀ n, composant (r n) ≠ composant p ∧ composant (r n) ≠ composant a :=
    (Classical.choose_spec selection).2
  have hcp : c ⊆ punctured p := by
    intro z hz heq
    exact hpc (heq ▸ hz)
  have hdcp : ∀ n, composant (r n) ⊆ punctured p := by
    intro n z hz heq
    apply (havoid n).1
    have hpcomp : p ∈ composant (r n) := by simpa only [heq] using hz
    exact (composant_eq_of_mem hi hpcomp).symm
  have hdcn : ∀ n, (composant (r n)).Nontrivial := fun n =>
    not_subsingleton_iff.mp (composant_not_subsingleton (r n))
  have hdcc : ∀ n, Disjoint (composant (r n)) c := by
    intro n
    apply (composant_disjoint_of_ne hi (havoid n).2).mono_right
    intro z hz
    exact ⟨c, hc, hac, hz⟩
  have hdcd : ∀ i j, i ≠ j → Disjoint (composant (r i)) (composant (r j)) :=
    fun i j hij => composant_disjoint_of_ne hi (hr hij)
  exact {
    arc := puncturedImage e c
    arc_subset := puncturedImage_subset e c
    arc_connected := puncturedImage_connected e hcp hc.2.1
    arc_nontrivial := puncturedImage_nontrivial e hcp hcn
    densePieces := fun n => puncturedImage e (composant (r (n + 1)))
    pieces_subset := fun n => puncturedImage_subset e _
    pieces_connected := fun n => puncturedImage_connected e (hdcp (n + 1))
      (composant_isConnected (r (n + 1)))
    pieces_nontrivial := fun n => puncturedImage_nontrivial e (hdcp (n + 1)) (hdcn (n + 1))
    pieces_dense := fun n => puncturedImage_dense e (hdcp (n + 1))
      (composant_dense (r (n + 1)))
    pieces_disjoint := fun _ _ hij => puncturedImage_disjoint e
      (hdcd _ _ (fun h => hij (Nat.succ.inj h)))
    arc_disjoint := fun n => puncturedImage_disjoint e (hdcc (n + 1)).symm
    reserve := puncturedImage e (composant (r 0))
    reserve_subset := puncturedImage_subset e _
    reserve_connected := puncturedImage_connected e (hdcp 0) (composant_isConnected (r 0))
    reserve_nontrivial := puncturedImage_nontrivial e (hdcp 0) (hdcn 0)
    reserve_arc_disjoint := puncturedImage_disjoint e (hdcc 0)
    reserve_pieces_disjoint := fun n => puncturedImage_disjoint e (hdcd 0 (n + 1) (by omega))
  }

theorem disjoint_subtype_preimage {k a b : Set Plane} (hab : Disjoint a b) :
    Disjoint (((↑) : k → Plane) ⁻¹' a) (((↑) : k → Plane) ⁻¹' b) :=
  disjoint_left.mpr (fun _ ha hb => hab.le_bot ⟨ha, hb⟩)

theorem subtype_val_image_preimage {k a : Set Plane} (hak : a ⊆ k) :
    ((↑) : k → Plane) '' (((↑) : k → Plane) ⁻¹' a) = a := by
  apply image_preimage_eq_of_subset
  simpa only [Subtype.range_val] using hak

def BoundaryPieces.target {k : Set Plane} (d : BoundaryPieces k) : ℕ → Set k
  | 0 => ((↑) : k → Plane) ⁻¹' d.arc
  | n + 1 => ((↑) : k → Plane) ⁻¹' d.densePieces n

theorem BoundaryPieces.target_cardinal {k : Set Plane} (d : BoundaryPieces k) (n : ℕ) :
    Cardinal.mk (d.target n) = Cardinal.continuum := by
  cases n with
  | zero =>
    rw [BoundaryPieces.target, cardinal_subtype_preimage d.arc_subset]
    exact cardinal_connected_plane_set _ d.arc_connected d.arc_nontrivial
  | succ n =>
    rw [BoundaryPieces.target, cardinal_subtype_preimage (d.pieces_subset n)]
    exact cardinal_connected_plane_set _ (d.pieces_connected n) (d.pieces_nontrivial n)

theorem BoundaryPieces.target_disjoint {k : Set Plane} (d : BoundaryPieces k) :
    Pairwise (fun i j => Disjoint (d.target i) (d.target j)) := by
  intro i j hij
  cases i with
  | zero =>
    cases j with
    | zero => exact False.elim (hij rfl)
    | succ j => exact disjoint_subtype_preimage (d.arc_disjoint j)
  | succ i =>
    cases j with
    | zero => exact disjoint_subtype_preimage (d.arc_disjoint i).symm
    | succ j =>
      exact disjoint_subtype_preimage
        (d.pieces_disjoint (fun h => hij (congrArg Nat.succ h)))

noncomputable def BoundaryPieces.toRayPartition {k : Set Plane} (d : BoundaryPieces k) :
    RayPartition k where
  source := sourceFamily.pieces
  target := d.target
  source_disjoint := sourceFamily.pairwise_disjoint
  target_disjoint := d.target_disjoint
  source_card := sourceFamily.pieces_cardinal
  target_card := d.target_cardinal
  source_reserve := sourceFamily.reserve
  source_reserve_card := sourceFamily.reserve_cardinal
  source_reserve_disjoint := sourceFamily.reserve_disjoint
  target_reserve := ((↑) : k → Plane) ⁻¹' d.reserve
  target_reserve_card := by
    rw [cardinal_subtype_preimage d.reserve_subset]
    exact cardinal_connected_plane_set _ d.reserve_connected d.reserve_nontrivial
  target_reserve_disjoint := by
    intro n
    cases n with
    | zero => exact disjoint_subtype_preimage d.reserve_arc_disjoint
    | succ n => exact disjoint_subtype_preimage (d.reserve_pieces_disjoint n)
  source_zero := sourceFamily.zero_piece
  target_zero_connected := by
    rw [BoundaryPieces.target, subtype_val_image_preimage d.arc_subset]
    exact d.arc_connected
  target_connected := by
    intro n
    rw [BoundaryPieces.target, subtype_val_image_preimage (d.pieces_subset n)]
    exact d.pieces_connected n
  target_dense := by
    intro n
    rw [BoundaryPieces.target, subtype_val_image_preimage (d.pieces_subset n)]
    exact d.pieces_dense n
  interval := sourceFamily.interval

noncomputable def RayPartition.toRayModel {k : Set Plane} (d : RayPartition k) :
    RayModel k where
  bijection := d.bijection
  connected := d.isConnectedMap
  arc := ((↑) : k → Plane) '' d.target 0
  arc_subset := by
    rintro y ⟨z, -, rfl⟩
    exact z.property
  arc_connected := d.target_zero_connected
  arc_preimage := d.arc_preimage

noncomputable def CanalModel.exterior (d : CanalModel) :
    (slitᶜ : Set Plane) ≃ₜ (d.boundaryᶜ : Set Plane) :=
  slitHomeomorph.trans d.straightening

theorem CanalModel.recurrent_levels (d : CanalModel) :
    ∀ p ∈ d.boundary, ∀ o : Set Plane, IsOpen o → p ∈ o →
      ∀ ε : ℝ, 0 < ε → ∃ τ : ℝ, 0 < τ ∧ τ < ε ∧
        ∀ z : (slitᶜ : Set Plane), rho z = τ → (d.exterior z : Plane) ∈ o := by
  intro p hp o ho hpo ε hε
  obtain ⟨m, hm⟩ := exists_nat_gt (-Real.log ε)
  obtain ⟨j, hmj, hgate⟩ := d.recurrent_lines p hp o ho hpo m
  refine ⟨Real.exp (-(j : ℝ)), Real.exp_pos _, ?_, ?_⟩
  · rw [← Real.exp_log hε]
    apply Real.exp_lt_exp.mpr
    have hmj' : (m : ℝ) ≤ (j : ℝ) := by exact_mod_cast hmj
    linarith
  · intro z hz
    apply hgate (psi z)
    simp only [psi, planeOf_one, hz, Real.log_exp, neg_neg]

noncomputable def CanalModel.toPlanarData (d : CanalModel) (r : RayModel d.boundary) :
    PlanarData where
  boundary := d.boundary
  exterior := d.exterior
  rayMap := r.bijection
  ray_connected := r.connected
  recurrent := d.recurrent_levels
  arc := r.arc
  arc_subset := r.arc_subset
  arc_connected := r.arc_connected
  ray_arc_preimage := r.arc_preimage

theorem CanalModel.not_repositoryAssertion (d : CanalModel) (r : RayModel d.boundary) :
    ¬ RepositoryAssertion :=
  (d.toPlanarData r).not_repositoryAssertion

/-- A fully checked reduction: only the specified target geometry remains to be supplied. -/
theorem not_repositoryAssertion_of_geometry (d : CanalModel) (b : BoundaryPieces d.boundary) :
    ¬ RepositoryAssertion :=
  d.not_repositoryAssertion b.toRayPartition.toRayModel

/-- The full construction reduces to one geometric existence theorem: a punctured
compact indecomposable continuum carrying the recurrent-line parametrization. -/
theorem not_repositoryAssertion_of_compact_canal [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [SecondCountableTopology X] [Nontrivial X]
    (d : CanalModel) (hi : Indecomposable X) (p : X)
    (e : punctured p ≃ₜ d.boundary) : ¬ RepositoryAssertion := by
  obtain ⟨c, hc, hcn, hpc⟩ := exists_properContinuum_nontrivial_avoiding hi p
  exact not_repositoryAssertion_of_geometry d
    (boundaryPieces_of_punctured_continuum hi p e c hc hcn hpc)

noncomputable def compactifiedPlaneSphere :
    OnePoint Plane ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  onePointEquivSphereOfFinrankEq (by simp [Plane])

instance compactifiedPlane_secondCountable : SecondCountableTopology (OnePoint Plane) :=
  compactifiedPlaneSphere.secondCountableTopology

def finitePart (k : Set (OnePoint Plane)) : Set Plane :=
  OnePoint.some ⁻¹' k

/-- Removing infinity from a compactified planar set has the ordinary planar
subspace topology. No separate identification homeomorphism needs to be assumed. -/
noncomputable def finitePartHomeomorph (k : Set (OnePoint Plane))
    (hinfty : OnePoint.infty ∈ k) :
    finitePart k ≃ₜ punctured (⟨OnePoint.infty, hinfty⟩ : k) := by
  classical
  let f : finitePart k → punctured (⟨OnePoint.infty, hinfty⟩ : k) := fun z =>
    ⟨⟨OnePoint.some z.val, z.property⟩,
      fun h => OnePoint.coe_ne_infty z.val (congrArg Subtype.val h)⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      apply OnePoint.coe_injective
      exact congrArg (fun z => z.val.val) hxy
    · intro z
      have hzinfty : z.val.val ≠ OnePoint.infty := fun h => z.property (Subtype.ext h)
      have hzrange : z.val.val ∈ range (OnePoint.some : Plane → OnePoint Plane) := by
        by_contra h
        exact hzinfty (OnePoint.notMem_range_coe_iff.mp h)
      obtain ⟨x, hx⟩ := hzrange
      have hxk : OnePoint.some x ∈ k := hx ▸ z.val.property
      refine ⟨⟨x, hxk⟩, ?_⟩
      apply Subtype.ext
      exact Subtype.ext hx
  have hfinducing : Topology.IsInducing f := by
    apply Topology.IsInducing.subtypeVal.of_comp_iff.mp
    apply Topology.IsInducing.subtypeVal.of_comp_iff.mp
    exact OnePoint.isOpenEmbedding_coe.isInducing.comp Topology.IsInducing.subtypeVal
  exact (Equiv.ofBijective f hf).toHomeomorphOfIsInducing hfinducing

/-- The outstanding geometric existence obligation, expressed without any
composant, ray-map, cardinality, or inverse-witness assumptions. -/
structure CompactifiedCanal where
  continuum : Set (OnePoint Plane)
  closed : IsClosed continuum
  connected : IsConnected continuum
  nontrivial : continuum.Nontrivial
  infty_mem : OnePoint.infty ∈ continuum
  indecomposable : Indecomposable continuum
  straightening : Plane ≃ₜ ((finitePart continuum)ᶜ : Set Plane)
  recurrent_lines : ∀ p ∈ finitePart continuum, ∀ o : Set Plane, IsOpen o → p ∈ o →
    ∀ m : ℕ, ∃ j : ℕ, m ≤ j ∧
      ∀ w : Plane, w 1 = (j : ℝ) → (straightening w : Plane) ∈ o

noncomputable def CompactifiedCanal.toCanalModel (d : CompactifiedCanal) : CanalModel where
  boundary := finitePart d.continuum
  straightening := d.straightening
  recurrent_lines := d.recurrent_lines

noncomputable def compactifiedCanalOfStripAtlas (k : Set (OnePoint Plane))
    (hk : IsClosed k) (hkc : IsConnected k) (hkn : k.Nontrivial)
    (hkinfty : OnePoint.infty ∈ k) (hki : Indecomposable k)
    (atlas : CanalStripAtlas (finitePart k)) : CompactifiedCanal where
  continuum := k
  closed := hk
  connected := hkc
  nontrivial := hkn
  infty_mem := hkinfty
  indecomposable := hki
  straightening := atlas.toCanalModel.straightening
  recurrent_lines := atlas.toCanalModel.recurrent_lines

theorem CompactifiedCanal.not_repositoryAssertion (d : CompactifiedCanal) :
    ¬ RepositoryAssertion := by
  have : CompactSpace d.continuum := isCompact_iff_compactSpace.mp d.closed.isCompact
  have : ConnectedSpace d.continuum := isConnected_iff_connectedSpace.mp d.connected
  have : Nontrivial d.continuum := d.nontrivial.coe_sort
  exact not_repositoryAssertion_of_compact_canal d.toCanalModel d.indecomposable
    ⟨OnePoint.infty, d.infty_mem⟩ (finitePartHomeomorph d.continuum d.infty_mem).symm

theorem CompactifiedCanal.repository_answer_false (d : CompactifiedCanal) :
    False ↔ RepositoryAssertion :=
  ⟨False.elim, fun h => d.not_repositoryAssertion h⟩

def GeometricExistence : Prop := Nonempty CompactifiedCanal

/-- Conditional on the isolated existence obligation, the answer is exactly false. -/
theorem repository_answer_false_of_geometricExistence (h : GeometricExistence) :
    False ↔ RepositoryAssertion := by
  obtain ⟨d⟩ := h
  exact d.repository_answer_false

end Plane

open Function Topology

section InverseLimit

variable {A : Type*} [TopologicalSpace A]

def inverseLimitSet (f : A → A) : Set (ℕ → A) :=
  {x | ∀ n, f (x (n + 1)) = x n}

def finiteLimitSet (f : A → A) (N : ℕ) : Set (ℕ → A) :=
  {x | ∀ n < N, f (x (n + 1)) = x n}

def finiteFill (f : A → A) (N : ℕ) (y : ℕ → A) (i : ℕ) : A :=
  if i ≤ N then f^[N - i] (y 0) else y (i - N)

omit [TopologicalSpace A] in
theorem finiteLimit_iterate {f : A → A} {N : ℕ} {x : ℕ → A}
    (hx : x ∈ finiteLimitSet f N) (i k : ℕ) (hik : i + k ≤ N) :
    f^[k] (x (i + k)) = x i := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iterate_succ_apply]
    have heq := hx (i + k) (by omega)
    rw [show i + (k + 1) = (i + k) + 1 by omega, heq]
    exact ih (by omega)

omit [TopologicalSpace A] in
theorem finiteFill_mem (f : A → A) (N : ℕ) (y : ℕ → A) :
    finiteFill f N y ∈ finiteLimitSet f N := by
  intro i hi
  simp only [finiteFill, if_pos (show i + 1 ≤ N by omega),
    if_pos (show i ≤ N by omega)]
  rw [← iterate_succ_apply' f (N - (i + 1)) (y 0)]
  congr 1
  omega

theorem continuous_finiteFill {f : A → A} (hf : Continuous f) (N : ℕ) :
    Continuous (finiteFill f N) := by
  apply continuous_pi
  intro i
  by_cases hi : i ≤ N
  · simp only [finiteFill, if_pos hi]
    exact (hf.iterate _).comp (continuous_apply 0)
  · simp only [finiteFill, if_neg hi]
    exact continuous_apply _

omit [TopologicalSpace A] in
theorem finiteFill_range (f : A → A) (N : ℕ) :
    range (finiteFill f N) = finiteLimitSet f N := by
  apply Subset.antisymm
  · rintro x ⟨y, rfl⟩
    exact finiteFill_mem f N y
  · intro x hx
    refine ⟨fun i => x (N + i), ?_⟩
    funext i
    by_cases hi : i ≤ N
    · simp only [finiteFill, if_pos hi, Nat.add_zero]
      simpa only [Nat.add_sub_of_le hi] using finiteLimit_iterate hx i (N - i) (by omega)
    · simp only [finiteFill, if_neg hi]
      congr 1
      omega

theorem finiteLimit_connected [ConnectedSpace A] {f : A → A}
    (hf : Continuous f) (N : ℕ) : IsConnected (finiteLimitSet f N) := by
  rw [← finiteFill_range]
  exact isConnected_range (continuous_finiteFill hf N)

theorem finiteLimit_closed [T2Space A] {f : A → A}
    (hf : Continuous f) (N : ℕ) : IsClosed (finiteLimitSet f N) := by
  have heq : finiteLimitSet f N = ⋂ i : Fin N,
      {x : ℕ → A | f (x (i.val + 1)) = x i.val} := by
    ext x
    simp only [finiteLimitSet, mem_ofPred_eq, mem_iInter]
    exact ⟨fun hx i => hx i.val i.isLt, fun hx i hi => hx ⟨i, hi⟩⟩
  rw [heq]
  exact isClosed_iInter fun i => isClosed_eq
    (hf.comp (continuous_apply _)) (continuous_apply _)

omit [TopologicalSpace A] in
theorem inverseLimit_iInter (f : A → A) :
    inverseLimitSet f = ⋂ N, finiteLimitSet f N := by
  ext x
  simp only [inverseLimitSet, finiteLimitSet, mem_ofPred_eq, mem_iInter]
  exact ⟨fun hx _ i _ => hx i, fun hx i => hx (i + 1) i (by omega)⟩

omit [TopologicalSpace A] in
theorem finiteLimit_antitone (f : A → A) : Antitone (finiteLimitSet f) := by
  intro n m hnm x hx i hi
  exact hx i (hi.trans_le hnm)

theorem preconnected_iInter_antitone_compact [T2Space A] [CompactSpace A]
    (s : ℕ → Set A) (hs : ∀ n, IsClosed (s n)) (hc : ∀ n, IsPreconnected (s n))
    (hanti : Antitone s) : IsPreconnected (⋂ n, s n) := by
  rw [isPreconnected_iff_subset_of_fully_disjoint_closed (isClosed_iInter hs)]
  intro a b ha hb hab hdis
  obtain ⟨u, v, hu, hv, hau, hbv, huv⟩ := normal_separation ha hb hdis
  have hdir : Directed (· ⊇ ·) s := fun i j =>
    ⟨max i j, hanti (le_max_left _ _), hanti (le_max_right _ _)⟩
  have hnhds : ∀ x ∈ ⋂ n, s n, u ∪ v ∈ 𝓝 x := fun x hx =>
    (hu.union hv).mem_nhds ((hab.trans (union_subset_union hau hbv)) hx)
  obtain ⟨n, hn⟩ := exists_subset_nhds_of_compactSpace hdir hs hnhds
  have hside := (hc n).subset_or_subset hu hv huv hn
  rcases hside with hsu | hsv
  · left
    exact Disjoint.left_le_of_le_sup_right hab
      (huv.mono ((iInter_subset s n).trans hsu) hbv)
  · right
    exact (huv.symm.mono ((iInter_subset s n).trans hsv) hau).left_le_of_le_sup_left hab

theorem inverseLimit_closed [T2Space A] {f : A → A} (hf : Continuous f) :
    IsClosed (inverseLimitSet f) := by
  rw [inverseLimit_iInter]
  exact isClosed_iInter (finiteLimit_closed hf)

theorem inverseLimit_preconnected [T2Space A] [CompactSpace A] [ConnectedSpace A]
    {f : A → A} (hf : Continuous f) : IsPreconnected (inverseLimitSet f) := by
  rw [inverseLimit_iInter]
  exact preconnected_iInter_antitone_compact _ (finiteLimit_closed hf)
    (fun N => (finiteLimit_connected hf N).isPreconnected) (finiteLimit_antitone f)

theorem inverseLimit_connected [T2Space A] [CompactSpace A] [ConnectedSpace A]
    {f : A → A} (hf : Continuous f) : IsConnected (inverseLimitSet f) := by
  refine ⟨?_, inverseLimit_preconnected hf⟩
  rw [inverseLimit_iInter]
  exact IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (finiteLimitSet f) (fun i => finiteLimit_antitone f (by omega))
    (fun N => (finiteLimit_connected hf N).nonempty)
    ((finiteLimit_closed hf 0).isCompact) (finiteLimit_closed hf)

abbrev InverseLimit (f : A → A) := inverseLimitSet f

omit [TopologicalSpace A] in
theorem inverseLimit_iterate {f : A → A} (x : InverseLimit f) (i k : ℕ) :
    f^[k] (x.val (i + k)) = x.val i :=
  finiteLimit_iterate (N := i + k) (fun n _ => x.property n) i k le_rfl

def inverseLift (f b : A → A) (N : ℕ) (u : A) (i : ℕ) : A :=
  if i ≤ N then f^[N - i] u else b^[i - N] u

omit [TopologicalSpace A] in
theorem inverseLift_mem (f b : A → A) (hb : RightInverse b f) (N : ℕ) (u : A) :
    inverseLift f b N u ∈ inverseLimitSet f := by
  intro i
  by_cases hi : i < N
  · simp only [inverseLift, if_pos (show i + 1 ≤ N by omega),
      if_pos (show i ≤ N by omega)]
    rw [← iterate_succ_apply' f (N - (i + 1)) u]
    congr 1
    omega
  · by_cases he : i = N
    · subst i
      simp only [inverseLift, if_neg (show ¬ N + 1 ≤ N by omega), if_pos le_rfl,
        Nat.add_sub_cancel_left, iterate_one, hb u, Nat.sub_self, iterate_zero, id_eq]
    · simp only [inverseLift, if_neg (show ¬ i + 1 ≤ N by omega),
        if_neg (show ¬ i ≤ N by omega)]
      rw [show i + 1 - N = (i - N) + 1 by omega,
        iterate_succ_apply' b (i - N) u, hb]

theorem continuous_inverseLift {f b : A → A} (hf : Continuous f) (hb : Continuous b)
    (N : ℕ) : Continuous (inverseLift f b N) := by
  apply continuous_pi
  intro i
  by_cases hi : i ≤ N
  · simp only [inverseLift, if_pos hi]
    exact hf.iterate _
  · simp only [inverseLift, if_neg hi]
    exact hb.iterate _

def inverseLiftTo (f b : A → A) (hb : RightInverse b f) (N : ℕ) : A → InverseLimit f :=
  fun u => ⟨inverseLift f b N u, inverseLift_mem f b hb N u⟩

omit [TopologicalSpace A] in
theorem inverseLiftTo_apply (f b : A → A) (hb : RightInverse b f) (N : ℕ) (u : A) :
    (inverseLiftTo f b hb N u).val N = u := by
  simp only [inverseLiftTo, inverseLift, if_pos le_rfl, Nat.sub_self, iterate_zero, id_eq]

theorem continuous_inverseLiftTo {f b : A → A} (hf : Continuous f) (hb : Continuous b)
    (hbf : RightInverse b f) (N : ℕ) : Continuous (inverseLiftTo f b hbf N) :=
  (continuous_inverseLift hf hb N).subtype_mk _

omit [TopologicalSpace A] in
theorem inverseLimit_projection_surjective (f b : A → A) (hb : RightInverse b f) (N : ℕ) :
    Surjective (fun x : InverseLimit f => x.val N) := fun u =>
  ⟨inverseLiftTo f b hb N u, inverseLiftTo_apply f b hb N u⟩

theorem inverseLiftTo_embedding [T2Space A] [CompactSpace A] {f b : A → A}
    (hf : Continuous f) (hb : Continuous b) (hbf : RightInverse b f) (N : ℕ) :
    Topology.IsEmbedding (inverseLiftTo f b hbf N) := by
  apply Topology.IsClosedEmbedding.isEmbedding
  apply (continuous_inverseLiftTo hf hb hbf N).isClosedEmbedding
  intro x y h
  have := congrArg (fun z : InverseLimit f => z.val N) h
  simpa only [inverseLiftTo_apply] using this

theorem proper_inverseLimit_projection [T2Space A] {f : A → A}
    {c : Set (InverseLimit f)} (hc : IsCompact c) (hproper : c ≠ univ) :
    ∃ N : ℕ, (fun x : InverseLimit f => x.val N) '' c ≠ univ := by
  classical
  by_contra! hfull
  apply hproper
  apply eq_univ_of_forall
  intro x
  let s : ℕ → Set (InverseLimit f) := fun N => c ∩ {y | y.val N = x.val N}
  have hsclosed : ∀ N, IsClosed (s N) := fun N => hc.isClosed.inter
    (isClosed_eq ((continuous_apply N).comp continuous_subtype_val) continuous_const)
  have hanti : ∀ i, s (i + 1) ⊆ s i := by
    intro i y hy
    refine ⟨hy.1, ?_⟩
    change y.val i = x.val i
    rw [← y.property i, ← x.property i, hy.2]
  have hsnonempty : ∀ N, (s N).Nonempty := by
    intro N
    have hx : x.val N ∈ (fun y : InverseLimit f => y.val N) '' c := by
      rw [hfull N]
      exact mem_univ _
    obtain ⟨y, hy, hyx⟩ := hx
    exact ⟨y, hy, hyx⟩
  have hcompact : IsCompact (s 0) :=
    hc.inter_right (isClosed_eq ((continuous_apply 0).comp continuous_subtype_val) continuous_const)
  obtain ⟨y, hy⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    s hanti hsnonempty hcompact hsclosed
  have hyx : y = x := by
    apply Subtype.ext
    funext N
    exact (mem_iInter.mp hy N).2
  exact hyx ▸ (mem_iInter.mp hy 0).1

end InverseLimit

section GoldenTent

abbrev TentInterval := Icc (0 : ℝ) 1

noncomputable def goldenTurning : ℝ := 2 - Real.goldenRatio

theorem goldenTurning_pos : 0 < goldenTurning := by
  dsimp [goldenTurning]
  linarith [Real.goldenRatio_lt_two]

theorem goldenTurning_lt_one : goldenTurning < 1 := by
  dsimp [goldenTurning]
  linarith [Real.one_lt_goldenRatio]

noncomputable def goldenTentReal (x : ℝ) : ℝ :=
  min (goldenTurning + Real.goldenRatio * x) (Real.goldenRatio * (1 - x))

theorem continuous_goldenTentReal : Continuous goldenTentReal :=
  (continuous_const.add (continuous_const.mul continuous_id)).min
    (continuous_const.mul (continuous_const.sub continuous_id))

theorem goldenTentReal_mem {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    goldenTentReal x ∈ Icc (0 : ℝ) 1 := by
  have hp := Real.goldenRatio_pos
  have hs := Real.goldenRatio_sq
  constructor
  · exact le_min (by dsimp [goldenTurning]; nlinarith [hx.1, Real.goldenRatio_lt_two])
      (by nlinarith [hx.2])
  · by_cases hxc : x ≤ goldenTurning
    · apply (min_le_left _ _).trans
      dsimp [goldenTurning] at hxc ⊢
      nlinarith
    · apply (min_le_right _ _).trans
      dsimp [goldenTurning] at hxc
      nlinarith

noncomputable def goldenTent : TentInterval → TentInterval :=
  fun x => ⟨goldenTentReal x.val, goldenTentReal_mem x.property⟩

theorem continuous_goldenTent : Continuous goldenTent :=
  (continuous_goldenTentReal.comp continuous_subtype_val).subtype_mk _

noncomputable def goldenBack : TentInterval → TentInterval := fun x =>
  ⟨1 - x.val / Real.goldenRatio, by
    constructor
    · have hdiv : x.val / Real.goldenRatio ≤ 1 :=
        (div_le_iff₀ Real.goldenRatio_pos).mpr (by linarith [x.property.2, Real.one_lt_goldenRatio])
      linarith
    · have hdiv := div_nonneg x.property.1 Real.goldenRatio_pos.le
      linarith⟩

theorem continuous_goldenBack : Continuous goldenBack :=
  (continuous_const.sub (continuous_subtype_val.div_const _)).subtype_mk _

theorem goldenBack_rightInverse : RightInverse goldenBack goldenTent := by
  intro x
  apply Subtype.ext
  change min (goldenTurning + Real.goldenRatio * (1 - x.val / Real.goldenRatio))
    (Real.goldenRatio * (1 - (1 - x.val / Real.goldenRatio))) = x.val
  have hleft : goldenTurning + Real.goldenRatio * (1 - x.val / Real.goldenRatio) =
      2 - x.val := by
    dsimp [goldenTurning]
    field_simp [Real.goldenRatio_ne_zero]
    ring
  have hright : Real.goldenRatio * (1 - (1 - x.val / Real.goldenRatio)) = x.val := by
    field_simp [Real.goldenRatio_ne_zero]
    ring
  rw [hleft, hright, min_eq_right (by linarith [x.property.2])]

theorem goldenTentReal_zero : goldenTentReal 0 = goldenTurning := by
  dsimp [goldenTentReal, goldenTurning]
  rw [mul_zero, add_zero, sub_zero, mul_one, min_eq_left]
  linarith [Real.one_lt_goldenRatio]

theorem goldenTentReal_turning : goldenTentReal goldenTurning = 1 := by
  have hs := Real.goldenRatio_sq
  have hl : goldenTurning + Real.goldenRatio * goldenTurning = 1 := by
    dsimp [goldenTurning]
    nlinarith
  have hr : Real.goldenRatio * (1 - goldenTurning) = 1 := by
    dsimp [goldenTurning]
    nlinarith
  simp only [goldenTentReal, hl, hr, min_self]

theorem goldenTentReal_one : goldenTentReal 1 = 0 := by
  dsimp [goldenTentReal, goldenTurning]
  norm_num

abbrev GoldenContinuum := InverseLimit goldenTent

instance goldenContinuum_compact : CompactSpace GoldenContinuum :=
  isCompact_iff_compactSpace.mp (inverseLimit_closed continuous_goldenTent).isCompact

instance goldenContinuum_connected : ConnectedSpace GoldenContinuum :=
  isConnected_iff_connectedSpace.mp (inverseLimit_connected continuous_goldenTent)

noncomputable def goldenArc : TentInterval → GoldenContinuum :=
  inverseLiftTo goldenTent goldenBack goldenBack_rightInverse 0

theorem goldenArc_embedding : Topology.IsEmbedding goldenArc :=
  inverseLiftTo_embedding continuous_goldenTent continuous_goldenBack goldenBack_rightInverse 0

theorem goldenArc_coordinate (x : TentInterval) : (goldenArc x).val 0 = x :=
  inverseLiftTo_apply _ _ _ _ x

instance goldenContinuum_nontrivial : Nontrivial GoldenContinuum := by
  refine ⟨⟨goldenArc ⟨0, by norm_num⟩, goldenArc ⟨1, by norm_num⟩, ?_⟩⟩
  intro h
  have hz := congrArg (fun x : GoldenContinuum => (x.val 0).val) h
  simp only [goldenArc_coordinate] at hz
  norm_num at hz

def goldenState (right : Bool) : Set ℝ :=
  if right then Icc goldenTurning 1 else Icc 0 goldenTurning

theorem goldenState_subset (right : Bool) : goldenState right ⊆ Icc (0 : ℝ) 1 := by
  cases right <;> simp only [goldenState, Bool.false_eq_true, ↓reduceIte]
  · intro x hx
    exact ⟨hx.1, hx.2.trans goldenTurning_lt_one.le⟩
  · intro x hx
    exact ⟨goldenTurning_pos.le.trans hx.1, hx.2⟩

theorem goldenTentReal_left {x : ℝ} (hx : x ∈ goldenState false) :
    goldenTentReal x = goldenTurning + Real.goldenRatio * x := by
  apply min_eq_left
  change x ∈ Icc 0 goldenTurning at hx
  dsimp [goldenTurning] at hx ⊢
  have hp := Real.goldenRatio_pos
  nlinarith [Real.goldenRatio_sq, mul_nonneg hp.le (sub_nonneg.mpr hx.2)]

theorem goldenTentReal_right {x : ℝ} (hx : x ∈ goldenState true) :
    goldenTentReal x = Real.goldenRatio * (1 - x) := by
  apply min_eq_right
  change x ∈ Icc goldenTurning 1 at hx
  dsimp [goldenTurning] at hx ⊢
  have hp := Real.goldenRatio_pos
  nlinarith [Real.goldenRatio_sq, mul_nonneg hp.le (sub_nonneg.mpr hx.1)]

theorem goldenTentReal_left_state {x : ℝ} (hx : x ∈ goldenState false) :
    goldenTentReal x ∈ goldenState true := by
  have hI := goldenTentReal_mem (goldenState_subset false hx)
  change goldenTurning ≤ goldenTentReal x ∧ goldenTentReal x ≤ 1
  refine ⟨?_, hI.2⟩
  rw [goldenTentReal_left hx]
  change x ∈ Icc 0 goldenTurning at hx
  exact le_add_of_nonneg_right (mul_nonneg Real.goldenRatio_pos.le hx.1)

noncomputable def goldenInverseReal (right : Bool) (x : ℝ) : ℝ :=
  if right then 1 - x / Real.goldenRatio else (x - goldenTurning) / Real.goldenRatio

theorem goldenInverseReal_mapsTo (b c : Bool) (hbc : b = false → c = true) :
    MapsTo (goldenInverseReal b) (goldenState c) (goldenState b) := by
  have hp := Real.goldenRatio_pos
  have hs := Real.goldenRatio_sq
  cases b with
  | false =>
    have hc := hbc rfl
    subst c
    intro x hx
    change goldenTurning ≤ x ∧ x ≤ 1 at hx
    change 0 ≤ (x - goldenTurning) / Real.goldenRatio ∧
      (x - goldenTurning) / Real.goldenRatio ≤ goldenTurning
    constructor
    · exact div_nonneg (sub_nonneg.mpr hx.1) hp.le
    · apply (div_le_iff₀ hp).mpr
      dsimp [goldenTurning] at hx ⊢
      nlinarith
  | true =>
    intro x hx
    have hxI := goldenState_subset c hx
    change goldenTurning ≤ 1 - x / Real.goldenRatio ∧ 1 - x / Real.goldenRatio ≤ 1
    constructor
    · have hdiv : x / Real.goldenRatio ≤ 1 - goldenTurning := by
        apply (div_le_iff₀ hp).mpr
        dsimp [goldenTurning]
        nlinarith [hxI.2]
      linarith
    · have hdiv := div_nonneg hxI.1 hp.le
      linarith

theorem goldenInverseReal_rightInverse (b c : Bool) (hbc : b = false → c = true)
    {x : ℝ} (hx : x ∈ goldenState c) :
    goldenTentReal (goldenInverseReal b x) = x := by
  have hm := goldenInverseReal_mapsTo b c hbc hx
  cases b with
  | false =>
    rw [goldenTentReal_left hm]
    change goldenTurning + Real.goldenRatio * ((x - goldenTurning) / Real.goldenRatio) = x
    field_simp [Real.goldenRatio_ne_zero]
    ring
  | true =>
    rw [goldenTentReal_right hm]
    change Real.goldenRatio * (1 - (1 - x / Real.goldenRatio)) = x
    field_simp [Real.goldenRatio_ne_zero]
    ring

theorem goldenInverseReal_leftInverse (b : Bool) {x : ℝ} (hx : x ∈ goldenState b) :
    goldenInverseReal b (goldenTentReal x) = x := by
  cases b with
  | false =>
    rw [goldenTentReal_left hx]
    change ((goldenTurning + Real.goldenRatio * x) - goldenTurning) / Real.goldenRatio = x
    field_simp [Real.goldenRatio_ne_zero]
    ring
  | true =>
    rw [goldenTentReal_right hx]
    change 1 - (Real.goldenRatio * (1 - x)) / Real.goldenRatio = x
    field_simp [Real.goldenRatio_ne_zero]
    ring

theorem goldenInverseReal_lipschitz (b : Bool) :
    LipschitzWith (2 / 3 : NNReal) (goldenInverseReal b) := by
  have hp := Real.goldenRatio_pos
  have hs : (3 : ℝ) / 2 ≤ Real.goldenRatio := by
    nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio]
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hdiff : dist (goldenInverseReal b x) (goldenInverseReal b y) =
      |x - y| / Real.goldenRatio := by
    cases b <;> simp only [goldenInverseReal, Bool.false_eq_true,
      ↓reduceIte, Real.dist_eq]
    · rw [show (x - goldenTurning) / Real.goldenRatio -
          (y - goldenTurning) / Real.goldenRatio = (x - y) / Real.goldenRatio by ring,
        abs_div, abs_of_pos hp]
    · rw [show (1 - x / Real.goldenRatio) - (1 - y / Real.goldenRatio) =
          -(x - y) / Real.goldenRatio by ring,
        abs_div, abs_neg, abs_of_pos hp]
  rw [hdiff, Real.dist_eq]
  change |x - y| / Real.goldenRatio ≤ (2 / 3 : ℝ) * |x - y|
  apply (div_le_iff₀ hp).mpr
  nlinarith [mul_nonneg (abs_nonneg (x - y)) (sub_nonneg.mpr hs)]

structure GoldenCylinder (x : ℝ) (n : ℕ) where
  right : Bool
  param : ℝ → ℝ
  lipschitz : LipschitzWith ((2 / 3 : NNReal) ^ n) param
  mapsTo : MapsTo param (goldenState right) (Icc (0 : ℝ) 1)
  inverse : ∀ u ∈ goldenState right, goldenTentReal^[n] (param u) = u
  center_mem : goldenTentReal^[n] x ∈ goldenState right
  center : param (goldenTentReal^[n] x) = x

theorem goldenCylinder_exists {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (n : ℕ) :
    Nonempty (GoldenCylinder x n) := by
  classical
  induction n with
  | zero =>
    let b : Bool := decide (goldenTurning ≤ x)
    have hxb : x ∈ goldenState b := by
      by_cases h : goldenTurning ≤ x
      · simpa only [b, goldenState, h, decide_true, ↓reduceIte] using (show x ∈ Icc goldenTurning 1 from ⟨h, hx.2⟩)
      · simpa [b, goldenState, h] using
          (show x ∈ Icc 0 goldenTurning from ⟨hx.1, (lt_of_not_ge h).le⟩)
    exact ⟨⟨b, id, by simpa only [pow_zero] using LipschitzWith.id,
      goldenState_subset b, fun _ _ => rfl, hxb, rfl⟩⟩
  | succ n ih =>
    obtain ⟨d⟩ := ih
    let y := goldenTentReal^[n] x
    let c : Bool := if d.right then decide (goldenTurning ≤ goldenTentReal y) else true
    have hbc : d.right = false → c = true := by
      intro h
      simp only [c, h, Bool.false_eq_true, ↓reduceIte]
    have hyI : y ∈ Icc (0 : ℝ) 1 := goldenState_subset d.right d.center_mem
    have hfc : goldenTentReal y ∈ goldenState c := by
      by_cases hb : d.right = true
      · have hI := goldenTentReal_mem hyI
        by_cases h : goldenTurning ≤ goldenTentReal y
        · simpa [c, hb, goldenState, h] using
            (show goldenTentReal y ∈ Icc goldenTurning 1 from ⟨h, hI.2⟩)
        · simpa [c, hb, goldenState, h] using
            (show goldenTentReal y ∈ Icc 0 goldenTurning from ⟨hI.1, (lt_of_not_ge h).le⟩)
      · have hfalse : d.right = false := Bool.eq_false_of_not_eq_true hb
        rw [hbc hfalse]
        exact goldenTentReal_left_state (hfalse ▸ d.center_mem)
    refine ⟨⟨c, d.param ∘ goldenInverseReal d.right, ?_, ?_, ?_, ?_, ?_⟩⟩
    · simpa only [pow_succ] using d.lipschitz.comp (goldenInverseReal_lipschitz d.right)
    · exact d.mapsTo.comp (goldenInverseReal_mapsTo d.right c hbc)
    · intro u hu
      rw [iterate_succ_apply', comp_apply, d.inverse _ (goldenInverseReal_mapsTo d.right c hbc hu)]
      exact goldenInverseReal_rightInverse d.right c hbc hu
    · simpa only [iterate_succ_apply'] using hfc
    · simp only [iterate_succ_apply', comp_apply]
      rw [goldenInverseReal_leftInverse d.right d.center_mem]
      exact d.center

theorem goldenState_cover {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    x ∈ goldenState false ∨ x ∈ goldenState true := by
  by_cases h : goldenTurning ≤ x
  · right
    exact ⟨h, hx.2⟩
  · left
    exact ⟨hx.1, (lt_of_not_ge h).le⟩

theorem goldenInverseReal_true_state {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    goldenInverseReal true x ∈ goldenState true := by
  rcases goldenState_cover hx with h | h
  · exact goldenInverseReal_mapsTo true false (by simp) h
  · exact goldenInverseReal_mapsTo true true (by simp) h

theorem goldenInverseReal_true_inverse {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    goldenTentReal (goldenInverseReal true x) = x := by
  rcases goldenState_cover hx with h | h
  · exact goldenInverseReal_rightInverse true false (by simp) h
  · exact goldenInverseReal_rightInverse true true (by simp) h

noncomputable def goldenFinish (b : Bool) (u : ℝ) : ℝ :=
  goldenInverseReal b (goldenInverseReal true u)

theorem goldenFinish_mem (b : Bool) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    goldenFinish b u ∈ goldenState b :=
  goldenInverseReal_mapsTo b true (by simp) (goldenInverseReal_true_state hu)

theorem goldenFinish_inverse (b : Bool) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    goldenTentReal^[2] (goldenFinish b u) = u := by
  change goldenTentReal (goldenTentReal (goldenInverseReal b (goldenInverseReal true u))) = u
  rw [goldenInverseReal_rightInverse b true (by simp) (goldenInverseReal_true_state hu)]
  exact goldenInverseReal_true_inverse hu

theorem goldenTent_iterate_val (n : ℕ) (x : TentInterval) :
    (goldenTent^[n] x).val = goldenTentReal^[n] x.val := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [iterate_succ_apply']
    change goldenTentReal (goldenTent^[n] x).val = _
    rw [ih]

theorem golden_small_inverse (x : TentInterval) :
    ∃ e : TentInterval → TentInterval, (∀ u, goldenTent^[6] (e u) = u) ∧
      ∀ u, |(e u).val - x.val| < 1 / 4 := by
  obtain ⟨d⟩ := goldenCylinder_exists x.property 4
  let e : TentInterval → TentInterval := fun u =>
    ⟨d.param (goldenFinish d.right u.val), d.mapsTo (goldenFinish_mem d.right u.property)⟩
  refine ⟨e, ?_, ?_⟩
  · intro u
    apply Subtype.ext
    rw [goldenTent_iterate_val]
    change goldenTentReal^[6] (d.param (goldenFinish d.right u.val)) = u.val
    rw [show (6 : ℕ) = 2 + 4 by rfl, iterate_add_apply,
      d.inverse _ (goldenFinish_mem d.right u.property)]
    exact goldenFinish_inverse d.right u.property
  · intro u
    have huc := goldenState_subset d.right (goldenFinish_mem d.right u.property)
    have hxc := goldenState_subset d.right d.center_mem
    have hdist : dist (goldenFinish d.right u.val) (goldenTentReal^[4] x.val) ≤ 1 := by
      rw [Real.dist_eq, abs_sub_le_iff]
      constructor <;> linarith [huc.1, huc.2, hxc.1, hxc.2]
    have hbound := d.lipschitz.dist_le_mul_of_le hdist
    rw [d.center] at hbound
    change dist (e u).val x.val ≤ (((2 / 3 : NNReal) ^ 4 : NNReal) : ℝ) * 1 at hbound
    norm_num at hbound
    rw [Real.dist_eq] at hbound
    linarith

theorem inverseLimit_projection_proper_mono {A : Type*} (f b : A → A) (hb : RightInverse b f)
    {c : Set (InverseLimit f)} {N M : ℕ} (hNM : N ≤ M)
    (hp : (fun x : InverseLimit f => x.val N) '' c ≠ univ) :
    (fun x : InverseLimit f => x.val M) '' c ≠ univ := by
  intro hfull
  apply hp
  apply eq_univ_of_forall
  intro u
  let x := inverseLiftTo f b hb N u
  have hx : x.val M ∈ (fun y : InverseLimit f => y.val M) '' c := hfull ▸ mem_univ _
  obtain ⟨y, hy, hyx⟩ := hx
  refine ⟨y, hy, ?_⟩
  have heq : y.val N = x.val N := by
    rw [← inverseLimit_iterate y N (M - N), ← inverseLimit_iterate x N (M - N)]
    simpa only [Nat.add_sub_of_le hNM] using congrArg (f^[M - N]) hyx
  exact heq.trans (inverseLiftTo_apply f b hb N u)

theorem golden_projection_gap {c : Set GoldenContinuum} (hc : IsConnected c) (N : ℕ)
    (hp : (fun x : GoldenContinuum => x.val N) '' c ≠ univ) :
    ∀ x ∈ (fun z : GoldenContinuum => (z.val (N + 6)).val) '' c,
      ∀ y ∈ (fun z : GoldenContinuum => (z.val (N + 6)).val) '' c, y - x < 1 / 2 := by
  intro x hx y hy
  by_contra! hgap
  let v : TentInterval := ⟨(x + y) / 2, by
    obtain ⟨zx, _, rfl⟩ := hx
    obtain ⟨zy, _, rfl⟩ := hy
    constructor <;> linarith [(zx.val (N + 6)).property.1, (zx.val (N + 6)).property.2,
      (zy.val (N + 6)).property.1, (zy.val (N + 6)).property.2]⟩
  obtain ⟨e, he, hsmall⟩ := golden_small_inverse v
  have hconn := hc.isPreconnected.image
    (fun z : GoldenContinuum => (z.val (N + 6)).val)
    (continuous_subtype_val.comp ((continuous_apply (N + 6)).comp continuous_subtype_val)).continuousOn
  have he_mem : ∀ u, (e u).val ∈ (fun z : GoldenContinuum => (z.val (N + 6)).val) '' c := by
    intro u
    apply hconn.Icc_subset hx hy
    have hsu := hsmall u
    rw [abs_lt] at hsu
    change -(1 / 4 : ℝ) < (e u).val - (x + y) / 2 ∧
      (e u).val - (x + y) / 2 < 1 / 4 at hsu
    constructor <;> linarith [hsu.1, hsu.2]
  apply hp
  apply eq_univ_of_forall
  intro u
  obtain ⟨z, hz, hzu⟩ := he_mem u
  refine ⟨z, hz, ?_⟩
  have hze : z.val (N + 6) = e u := Subtype.ext hzu
  change z.val N = u
  rw [← inverseLimit_iterate z N 6, hze, he]

theorem goldenContinuum_indecomposable : Indecomposable GoldenContinuum := by
  intro c d hc hd hcover
  obtain ⟨Nc, hNc⟩ := proper_inverseLimit_projection hc.1 hc.2.2
  obtain ⟨Nd, hNd⟩ := proper_inverseLimit_projection hd.1 hd.2.2
  let N := max Nc Nd
  have hpc := inverseLimit_projection_proper_mono goldenTent goldenBack
    goldenBack_rightInverse (le_max_left Nc Nd) hNc
  have hpd := inverseLimit_projection_proper_mono goldenTent goldenBack
    goldenBack_rightInverse (le_max_right Nc Nd) hNd
  let pc := (fun z : GoldenContinuum => (z.val (N + 6)).val) '' c
  let pd := (fun z : GoldenContinuum => (z.val (N + 6)).val) '' d
  have hgc : ∀ x ∈ pc, ∀ y ∈ pc, y - x < (1 / 2 : ℝ) := golden_projection_gap hc.2.1 N hpc
  have hgd : ∀ x ∈ pd, ∀ y ∈ pd, y - x < (1 / 2 : ℝ) := golden_projection_gap hd.2.1 N hpd
  have hmem : ∀ u ∈ Icc (0 : ℝ) 1, u ∈ pc ∨ u ∈ pd := by
    intro u hu
    let z := inverseLiftTo goldenTent goldenBack goldenBack_rightInverse (N + 6) ⟨u, hu⟩
    have hz : z ∈ c ∪ d := hcover ▸ mem_univ _
    rcases hz with hz | hz
    · exact Or.inl ⟨z, hz, congrArg Subtype.val (inverseLiftTo_apply _ _ _ _ _)⟩
    · exact Or.inr ⟨z, hz, congrArg Subtype.val (inverseLiftTo_apply _ _ _ _ _)⟩
  have h0 := hmem 0 (by norm_num)
  have hh := hmem (1 / 2) (by norm_num)
  have h1 := hmem 1 (by norm_num)
  rcases h0 with h0 | h0
  · rcases hh with hh | hh
    · linarith [hgc 0 h0 (1 / 2) hh]
    · rcases h1 with h1 | h1
      · linarith [hgc 0 h0 1 h1]
      · linarith [hgd (1 / 2) hh 1 h1]
  · rcases hh with hh | hh
    · rcases h1 with h1 | h1
      · linarith [hgc (1 / 2) hh 1 h1]
      · linarith [hgd 0 h0 1 h1]
    · linarith [hgd 0 h0 (1 / 2) hh]

theorem goldenArc_proper : range goldenArc ≠ univ := by
  intro hfull
  let z := inverseLiftTo goldenTent goldenBack goldenBack_rightInverse 1 ⟨0, by norm_num⟩
  have hz : z ∈ range goldenArc := hfull ▸ mem_univ _
  obtain ⟨u, hu⟩ := hz
  have heq : (goldenBack u).val = 0 := by
    have heq := congrArg (fun w : GoldenContinuum => (w.val 1).val) hu
    have heqz : (z.val 1).val = 0 := congrArg Subtype.val (inverseLiftTo_apply _ _ _ _ _)
    have hequ : (goldenArc u).val 1 = goldenBack u := by
      simp only [goldenArc, inverseLiftTo, inverseLift, show ¬ (1 : ℕ) ≤ 0 by omega,
        ↓reduceIte, Nat.sub_zero, iterate_one]
    rw [hequ, heqz] at heq
    exact heq
  have huR := goldenInverseReal_true_state u.property
  change goldenTurning ≤ 1 - u.val / Real.goldenRatio ∧
    1 - u.val / Real.goldenRatio ≤ 1 at huR
  change 1 - u.val / Real.goldenRatio = 0 at heq
  linarith [goldenTurning_pos]

theorem goldenArc_properContinuum : ProperContinuum (range goldenArc) :=
  ⟨isCompact_range goldenArc_embedding.continuous,
    isConnected_range goldenArc_embedding.continuous, goldenArc_proper⟩

noncomputable def goldenCoreRescale (x : ℝ) : ℝ :=
  (x + Real.goldenRatio - 1) / 2

noncomputable def originalGoldenTent (x : ℝ) : ℝ :=
  min (Real.goldenRatio * x) (Real.goldenRatio * (1 - x))

/-- The unit-interval map is precisely the affine rescaling of the core map in the paper. -/
theorem goldenCore_conjugacy (x : ℝ) :
    originalGoldenTent (goldenCoreRescale x) = goldenCoreRescale (goldenTentReal x) := by
  have hs := Real.goldenRatio_sq
  have hl : Real.goldenRatio * goldenCoreRescale x =
      (goldenTurning + Real.goldenRatio * x + Real.goldenRatio - 1) / 2 := by
    dsimp [goldenCoreRescale, goldenTurning]
    nlinarith
  have hr : Real.goldenRatio * (1 - goldenCoreRescale x) =
      (Real.goldenRatio * (1 - x) + Real.goldenRatio - 1) / 2 := by
    dsimp [goldenCoreRescale]
    nlinarith
  dsimp only [originalGoldenTent]
  rw [hl, hr]
  simp only [goldenCoreRescale, goldenTentReal, min_div_div_right (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  rw [min_sub_sub_right, min_add_add_right]

end GoldenTent


section RecurrentTube

open Set Function Topology

abbrev ProductPlane := ℝ × ℝ

def tubeRectangle (H : ℝ) : Set ProductPlane := Icc (-1 : ℝ) 1 ×ˢ Icc 0 H

def horizontalShear (a : ℝ → ℝ) (ha : Continuous a) : ProductPlane ≃ₜ ProductPlane where
  toFun z := (z.1 + a z.2, z.2)
  invFun z := (z.1 - a z.2, z.2)
  left_inv z := by simp
  right_inv z := by simp
  continuous_toFun := (continuous_fst.add (ha.comp continuous_snd)).prodMk continuous_snd
  continuous_invFun := (continuous_fst.sub (ha.comp continuous_snd)).prodMk continuous_snd

def verticalShear (a : ℝ → ℝ) (ha : Continuous a) : ProductPlane ≃ₜ ProductPlane where
  toFun z := (z.1, z.2 + a z.1)
  invFun z := (z.1, z.2 - a z.1)
  left_inv z := by simp
  right_inv z := by simp
  continuous_toFun := continuous_fst.prodMk (continuous_snd.add (ha.comp continuous_fst))
  continuous_invFun := continuous_fst.prodMk (continuous_snd.sub (ha.comp continuous_fst))

theorem horizontalShear_apply (a : ℝ → ℝ) (ha : Continuous a) (z : ProductPlane) :
    horizontalShear a ha z = (z.1 + a z.2, z.2) := rfl

theorem verticalShear_apply (a : ℝ → ℝ) (ha : Continuous a) (z : ProductPlane) :
    verticalShear a ha z = (z.1, z.2 + a z.1) := rfl

noncomputable def upperWeight (H T y : ℝ) : ℝ := max 0 (y - H) / (T - H)

theorem continuous_upperWeight (H T : ℝ) : Continuous (upperWeight H T) :=
  (continuous_const.max (continuous_id.sub continuous_const)).div_const _

theorem upperWeight_zero {H T y : ℝ} (hy : y ≤ H) : upperWeight H T y = 0 := by
  simp only [upperWeight, max_eq_left (sub_nonpos.mpr hy), zero_div]

theorem upperWeight_self {H T : ℝ} (hHT : H < T) : upperWeight H T T = 1 := by
  rw [upperWeight, max_eq_right (sub_nonneg.mpr hHT.le)]
  exact div_self (sub_ne_zero.mpr hHT.ne')

noncomputable def sideWeight (X x : ℝ) : ℝ := max 0 (|x| - 1) / (|X| - 1)

theorem continuous_sideWeight (X : ℝ) : Continuous (sideWeight X) :=
  (continuous_const.max (continuous_abs.sub continuous_const)).div_const _

theorem sideWeight_zero {X x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) : sideWeight X x = 0 := by
  have habs : |x| ≤ 1 := abs_le.mpr hx
  simp only [sideWeight, max_eq_left (sub_nonpos.mpr habs), zero_div]

theorem sideWeight_self {X : ℝ} (hX : 1 < |X|) : sideWeight X X = 1 := by
  rw [sideWeight, max_eq_right (sub_nonneg.mpr hX.le)]
  exact div_self (sub_ne_zero.mpr hX.ne')

noncomputable def heightWeight (H Q y : ℝ) : ℝ :=
  if Q < 0 then max 0 (-y) / (-Q) else upperWeight H Q y

theorem continuous_heightWeight (H Q : ℝ) : Continuous (heightWeight H Q) := by
  classical
  by_cases hQ : Q < 0
  · have heq : heightWeight H Q = (fun y => max 0 (-y) / (-Q)) := by
      funext y
      exact if_pos hQ
    rw [heq]
    exact (continuous_const.max continuous_id.neg).div_const _
  · have heq : heightWeight H Q = upperWeight H Q := by
      funext y
      exact if_neg hQ
    rw [heq]
    exact continuous_upperWeight H Q

theorem heightWeight_zero {H Q y : ℝ} (hy : y ∈ Icc 0 H) : heightWeight H Q y = 0 := by
  classical
  by_cases hQ : Q < 0
  · simp only [heightWeight, if_pos hQ, max_eq_left (neg_nonpos.mpr hy.1), zero_div]
  · simp only [heightWeight, if_neg hQ]
    exact upperWeight_zero hy.2

theorem heightWeight_self {H Q : ℝ} (hQ : Q ∉ Icc 0 H) : heightWeight H Q Q = 1 := by
  classical
  by_cases hneg : Q < 0
  · rw [heightWeight, if_pos hneg, max_eq_right (neg_nonneg.mpr hneg.le)]
    exact div_self (neg_ne_zero.mpr hneg.ne)
  · rw [heightWeight, if_neg hneg]
    apply upperWeight_self
    by_contra! h
    exact hQ ⟨le_of_not_gt hneg, h⟩

theorem horizontalShear_fixed_rectangle {H : ℝ} {a : ℝ → ℝ} (ha : Continuous a)
    (hz : ∀ y ∈ Icc 0 H, a y = 0) : EqOn (horizontalShear a ha) id (tubeRectangle H) := by
  intro z hzrect
  rw [horizontalShear_apply, hz z.2 hzrect.2]
  exact Prod.ext (add_zero _) rfl

theorem verticalShear_fixed_rectangle {H : ℝ} {a : ℝ → ℝ} (ha : Continuous a)
    (hz : ∀ x ∈ Icc (-1 : ℝ) 1, a x = 0) : EqOn (verticalShear a ha) id (tubeRectangle H) := by
  intro z hzrect
  rw [verticalShear_apply, hz z.1 hzrect.1]
  exact Prod.ext rfl (add_zero _)

/-- Three triangular shears move a point above a frozen rectangle to any exterior point. -/
theorem exists_homeomorph_fixed_rectangle_moves {H T : ℝ} (hHT : H < T)
    (q : ProductPlane) (hq : q ∉ tubeRectangle H) :
    ∃ g : ProductPlane ≃ₜ ProductPlane, EqOn g id (tubeRectangle H) ∧ g (0, T) = q := by
  classical
  by_cases hqy : q.2 ∈ Icc 0 H
  · have hqx : q.1 ∉ Icc (-1 : ℝ) 1 := fun h => hq ⟨h, hqy⟩
    have hqabs : 1 < |q.1| := by
      by_contra! h
      exact hqx (abs_le.mp h)
    let g1 := horizontalShear (fun y => q.1 * upperWeight H T y)
      (continuous_const.mul (continuous_upperWeight H T))
    let g2 := verticalShear (fun x => (q.2 - T) * sideWeight q.1 x)
      (continuous_const.mul (continuous_sideWeight q.1))
    have h1 : EqOn g1 id (tubeRectangle H) := horizontalShear_fixed_rectangle _
      (fun y hy => by rw [upperWeight_zero hy.2, mul_zero])
    have h2 : EqOn g2 id (tubeRectangle H) := verticalShear_fixed_rectangle _
      (fun x hx => by rw [sideWeight_zero hx, mul_zero])
    refine ⟨g1.trans g2, ?_, ?_⟩
    · intro z hz
      change g2 (g1 z) = z
      simp only [h1 hz, id_eq, h2 hz]
    · change (g2 (g1 (0, T))) = q
      simp only [g1, g2, horizontalShear_apply, verticalShear_apply,
        upperWeight_self hHT, mul_one, zero_add, sideWeight_self hqabs]
      exact Prod.ext rfl (by ring)
  · let g1 := horizontalShear (fun y => 2 * upperWeight H T y)
      (continuous_const.mul (continuous_upperWeight H T))
    let g2 := verticalShear (fun x => (q.2 - T) * sideWeight 2 x)
      (continuous_const.mul (continuous_sideWeight 2))
    let g3 := horizontalShear (fun y => (q.1 - 2) * heightWeight H q.2 y)
      (continuous_const.mul (continuous_heightWeight H q.2))
    have h1 : EqOn g1 id (tubeRectangle H) := horizontalShear_fixed_rectangle _
      (fun y hy => by rw [upperWeight_zero hy.2, mul_zero])
    have h2 : EqOn g2 id (tubeRectangle H) := verticalShear_fixed_rectangle _
      (fun x hx => by rw [sideWeight_zero hx, mul_zero])
    have h3 : EqOn g3 id (tubeRectangle H) := horizontalShear_fixed_rectangle _
      (fun y hy => by rw [heightWeight_zero hy, mul_zero])
    refine ⟨(g1.trans g2).trans g3, ?_, ?_⟩
    · intro z hz
      change g3 (g2 (g1 z)) = z
      simp only [h1 hz, id_eq, h2 hz, h3 hz]
    · change g3 (g2 (g1 (0, T))) = q
      have hs : sideWeight 2 2 = 1 := sideWeight_self (by norm_num)
      simp only [g1, g2, g3, horizontalShear_apply, verticalShear_apply,
        upperWeight_self hHT, mul_one, zero_add, hs]
      rw [show T + (q.2 - T) = q.2 by ring, heightWeight_self hqy]
      simp only [mul_one]
      exact Prod.ext (by ring) rfl

noncomputable def horizontalScaling (c : ℝ → ℝ) (hc : Continuous c)
    (hpos : ∀ y, 0 < c y) : ProductPlane ≃ₜ ProductPlane where
  toFun z := (c z.2 * z.1, z.2)
  invFun z := (z.1 / c z.2, z.2)
  left_inv z := by simp [hpos z.2 |>.ne']
  right_inv z := by
    apply Prod.ext
    · change c z.2 * (z.1 / c z.2) = z.1
      field_simp [(hpos z.2).ne']
    · rfl
  continuous_toFun := ((hc.comp continuous_snd).mul continuous_fst).prodMk continuous_snd
  continuous_invFun := (continuous_fst.div (hc.comp continuous_snd)
    (fun z => (hpos z.2).ne')).prodMk continuous_snd

theorem horizontalScaling_apply (c : ℝ → ℝ) (hc : Continuous c)
    (hpos : ∀ y, 0 < c y) (z : ProductPlane) :
    horizontalScaling c hc hpos z = (c z.2 * z.1, z.2) := rfl

noncomputable def clippedUpperWeight (H T y : ℝ) : ℝ := min 1 (upperWeight H T y)

theorem continuous_clippedUpperWeight (H T : ℝ) : Continuous (clippedUpperWeight H T) :=
  continuous_const.min (continuous_upperWeight H T)

theorem clippedUpperWeight_bounds {H T : ℝ} (hHT : H < T) (y : ℝ) :
    0 ≤ clippedUpperWeight H T y ∧ clippedUpperWeight H T y ≤ 1 :=
  ⟨le_min (by norm_num) (div_nonneg (le_max_left _ _) (sub_nonneg.mpr hHT.le)), min_le_left _ _⟩

theorem clippedUpperWeight_zero {H T y : ℝ} (hy : y ≤ H) :
    clippedUpperWeight H T y = 0 := by
  rw [clippedUpperWeight, upperWeight_zero hy]
  norm_num

theorem clippedUpperWeight_self {H T : ℝ} (hHT : H < T) :
    clippedUpperWeight H T T = 1 := by
  rw [clippedUpperWeight, upperWeight_self hHT, min_self]

/-- Compress a future horizontal cross-section while freezing the earlier rectangle. -/
theorem exists_homeomorph_fixed_rectangle_shrinks {H T δ : ℝ}
    (hHT : H < T) (hδ : 0 < δ) :
    ∃ g : ProductPlane ≃ₜ ProductPlane, EqOn g id (tubeRectangle H) ∧
      ∀ x ∈ Icc (-1 : ℝ) 1, g (x, T) ∈ Metric.ball (0, T) δ := by
  let a := min (δ / 2) (1 / 2)
  have ha : 0 < a := lt_min (by linarith) (by norm_num)
  have ha1 : a ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have haδ : a < δ := (min_le_left _ _).trans_lt (by linarith)
  let c : ℝ → ℝ := fun y => 1 - clippedUpperWeight H T y + clippedUpperWeight H T y * a
  have hc : Continuous c := (continuous_const.sub (continuous_clippedUpperWeight H T)).add
    ((continuous_clippedUpperWeight H T).mul continuous_const)
  have hcp : ∀ y, 0 < c y := by
    intro y
    have hb := clippedUpperWeight_bounds hHT y
    have hbound : a ≤ c y := by
      dsimp [c]
      nlinarith [mul_nonneg (sub_nonneg.mpr hb.2) (sub_nonneg.mpr ha1)]
    exact ha.trans_le hbound
  let g := horizontalScaling c hc hcp
  refine ⟨g, ?_, ?_⟩
  · intro z hz
    rw [horizontalScaling_apply]
    have hcz : c z.2 = 1 := by
      dsimp [c]
      rw [clippedUpperWeight_zero hz.2.2]
      ring
    apply Prod.ext
    · change c z.2 * z.1 = z.1
      rw [hcz, one_mul]
    · rfl
  · intro x hx
    have hcT : c T = a := by
      dsimp [c]
      rw [clippedUpperWeight_self hHT]
      ring
    rw [Metric.mem_ball, horizontalScaling_apply, hcT]
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    simp only [sub_zero, sub_self, abs_zero]
    rw [max_eq_left (abs_nonneg (a * x))]
    have habs : |a * x| ≤ a := by
      rw [abs_mul, abs_of_pos ha]
      exact mul_le_of_le_one_right ha.le (abs_le.mpr hx)
    exact habs.trans_lt haδ

/-- One complete finite stage: put the new whole cap in any exterior open target. -/
theorem exists_homeomorph_fixed_rectangle_cap_into {H T : ℝ} (hHT : H < T)
    (o : Set ProductPlane) (ho : IsOpen o) (hne : (o \ tubeRectangle H).Nonempty) :
    ∃ g : ProductPlane ≃ₜ ProductPlane, EqOn g id (tubeRectangle H) ∧
      ∀ x ∈ Icc (-1 : ℝ) 1, g (x, T) ∈ o := by
  obtain ⟨q, hqo, hqrect⟩ := hne
  obtain ⟨f, hffix, hfq⟩ := exists_homeomorph_fixed_rectangle_moves hHT q hqrect
  have hopen := ho.preimage f.continuous
  have hc : (0, T) ∈ f ⁻¹' o := by
    change f (0, T) ∈ o
    rw [hfq]
    exact hqo
  obtain ⟨δ, hδ, hb⟩ := Metric.isOpen_iff.mp hopen (0, T) hc
  obtain ⟨g, hgfix, hgcap⟩ := exists_homeomorph_fixed_rectangle_shrinks hHT hδ
  refine ⟨g.trans f, ?_, ?_⟩
  · intro z hz
    change f (g z) = z
    simp only [hgfix hz, id_eq, hffix hz]
  · intro x hx
    exact hb (hgcap x hx)

noncomputable def tubeBasis (n : ℕ) : Set ProductPlane :=
  ((Encodable.decode n : Option (TopologicalSpace.countableBasis ProductPlane)).map
    Subtype.val).getD univ

theorem tubeBasis_open (n : ℕ) : IsOpen (tubeBasis n) := by
  classical
  unfold tubeBasis
  cases h : (Encodable.decode n : Option (TopologicalSpace.countableBasis ProductPlane)) with
  | none => exact isOpen_univ
  | some b => exact TopologicalSpace.isOpen_of_mem_countableBasis b.property

theorem tubeBasis_refines {p : ProductPlane} {o : Set ProductPlane}
    (ho : IsOpen o) (hp : p ∈ o) :
    ∃ n, p ∈ tubeBasis n ∧ tubeBasis n ⊆ o := by
  obtain ⟨b, hb, hpb, hbo⟩ :=
    (TopologicalSpace.isBasis_countableBasis ProductPlane).exists_subset_of_mem_open hp ho
  let v : TopologicalSpace.countableBasis ProductPlane := ⟨b, hb⟩
  refine ⟨Encodable.encode v, ?_⟩
  simpa only [tubeBasis, Encodable.encodek, Option.map_some, Option.getD_some]
    using (show p ∈ v.val ∧ v.val ⊆ o from ⟨hpb, hbo⟩)

noncomputable def tubeTarget (n : ℕ) : Set ProductPlane := tubeBasis n.unpair.1

theorem tubeTarget_open (n : ℕ) : IsOpen (tubeTarget n) := tubeBasis_open _

theorem tubeTarget_repeats (i m : ℕ) :
    ∃ n, m ≤ n ∧ tubeTarget n = tubeBasis i :=
  ⟨Nat.pair i m, Nat.right_le_pair _ _, by simp only [tubeTarget, Nat.unpair_pair]⟩

noncomputable def tubeHeight (n : ℕ) : ℝ := Real.exp (n : ℝ)

theorem tubeHeight_pos (n : ℕ) : 0 < tubeHeight n := Real.exp_pos _

theorem tubeHeight_strictMono : StrictMono tubeHeight := by
  intro i j hij
  exact Real.exp_lt_exp.mpr (by exact_mod_cast hij)

theorem tubeRectangle_mono {H T : ℝ} (hHT : H ≤ T) : tubeRectangle H ⊆ tubeRectangle T :=
  prod_mono_right (Icc_subset_Icc_right hHT)

noncomputable def tubeStepHomeomorph (n : ℕ) (e : ProductPlane ≃ₜ ProductPlane) :
    ProductPlane ≃ₜ ProductPlane := by
  classical
  let o := e ⁻¹' tubeTarget n
  by_cases h : (o \ tubeRectangle (tubeHeight n)).Nonempty
  · exact Classical.choose (exists_homeomorph_fixed_rectangle_cap_into
      (tubeHeight_strictMono (Nat.lt_succ_self n)) o
      ((tubeTarget_open n).preimage e.continuous) h)
  · exact Homeomorph.refl ProductPlane

theorem tubeStepHomeomorph_fixed (n : ℕ) (e : ProductPlane ≃ₜ ProductPlane) :
    EqOn (tubeStepHomeomorph n e) id (tubeRectangle (tubeHeight n)) := by
  classical
  unfold tubeStepHomeomorph
  dsimp only
  split_ifs with h
  · exact (Classical.choose_spec (exists_homeomorph_fixed_rectangle_cap_into
      (tubeHeight_strictMono (Nat.lt_succ_self n)) _
      ((tubeTarget_open n).preimage e.continuous) h)).1
  · intro z _
    rfl

theorem tubeStepHomeomorph_cap (n : ℕ) (e : ProductPlane ≃ₜ ProductPlane)
    (h : (e ⁻¹' tubeTarget n \ tubeRectangle (tubeHeight n)).Nonempty) :
    ∀ x ∈ Icc (-1 : ℝ) 1,
      e (tubeStepHomeomorph n e (x, tubeHeight (n + 1))) ∈ tubeTarget n := by
  classical
  unfold tubeStepHomeomorph
  rw [dif_pos h]
  exact (Classical.choose_spec (exists_homeomorph_fixed_rectangle_cap_into
    (tubeHeight_strictMono (Nat.lt_succ_self n)) _
    ((tubeTarget_open n).preimage e.continuous) h)).2

noncomputable def tubeCharts : ℕ → (ProductPlane ≃ₜ ProductPlane)
  | 0 => Homeomorph.refl ProductPlane
  | n + 1 => (tubeStepHomeomorph n (tubeCharts n)).trans (tubeCharts n)

theorem tubeCharts_step_agrees (n : ℕ) :
    EqOn (tubeCharts (n + 1)) (tubeCharts n) (tubeRectangle (tubeHeight n)) := by
  intro z hz
  change tubeCharts n (tubeStepHomeomorph n (tubeCharts n) z) = tubeCharts n z
  rw [tubeStepHomeomorph_fixed n (tubeCharts n) hz]
  rfl

theorem tubeCharts_agrees_of_le {n m : ℕ} (hnm : n ≤ m) :
    EqOn (tubeCharts m) (tubeCharts n) (tubeRectangle (tubeHeight n)) := by
  induction m with
  | zero =>
    have hn : n = 0 := by omega
    subst n
    intro _ _
    rfl
  | succ m ih =>
    by_cases he : n = m + 1
    · subst n
      intro _ _
      rfl
    · have hnm' : n ≤ m := by omega
      intro z hz
      exact (tubeCharts_step_agrees m
        (tubeRectangle_mono (tubeHeight_strictMono.monotone hnm') hz)).trans (ih hnm' hz)

def closedTube : Set ProductPlane := Icc (-1 : ℝ) 1 ×ˢ Ici 0

def tubeInterior : Set ProductPlane := Ioo (-1 : ℝ) 1 ×ˢ Ioi 0

theorem tubeInterior_open : IsOpen tubeInterior := isOpen_Ioo.prod isOpen_Ioi

theorem tubeInterior_subset_closed : tubeInterior ⊆ closedTube := by
  intro z hz
  change (-1 < z.1 ∧ z.1 < 1) ∧ 0 < z.2 at hz
  exact ⟨⟨hz.1.1.le, hz.1.2.le⟩, hz.2.le⟩

theorem exists_tubeHeight_gt (y : ℝ) : ∃ n, y < tubeHeight n := by
  obtain ⟨n, hn⟩ := exists_nat_gt y
  refine ⟨n, hn.trans ?_⟩
  have he := Real.add_one_le_exp (n : ℝ)
  change (n : ℝ) < Real.exp (n : ℝ)
  linarith

noncomputable def tubeLimit (z : closedTube) : ProductPlane :=
  tubeCharts (Classical.choose (exists_tubeHeight_gt z.val.2)) z.val

theorem tubeLimit_eq_chart (z : closedTube) {n : ℕ}
    (hz : z.val ∈ tubeRectangle (tubeHeight n)) : tubeLimit z = tubeCharts n z.val := by
  let m := Classical.choose (exists_tubeHeight_gt z.val.2)
  have hzm : z.val ∈ tubeRectangle (tubeHeight m) :=
    ⟨z.property.1, z.property.2, (Classical.choose_spec (exists_tubeHeight_gt z.val.2)).le⟩
  change tubeCharts m z.val = tubeCharts n z.val
  exact (tubeCharts_agrees_of_le (le_max_left m n) hzm).symm.trans
    (tubeCharts_agrees_of_le (le_max_right m n) hz)

theorem tubeLimit_injective : Injective tubeLimit := by
  intro z w heq
  obtain ⟨n, hn⟩ := exists_tubeHeight_gt (max z.val.2 w.val.2)
  have hz : z.val ∈ tubeRectangle (tubeHeight n) :=
    ⟨z.property.1, z.property.2, ((le_max_left _ _).trans hn.le)⟩
  have hw : w.val ∈ tubeRectangle (tubeHeight n) :=
    ⟨w.property.1, w.property.2, ((le_max_right _ _).trans hn.le)⟩
  rw [tubeLimit_eq_chart z hz, tubeLimit_eq_chart w hw] at heq
  exact Subtype.ext ((tubeCharts n).injective heq)

theorem continuous_tubeLimit : Continuous tubeLimit := by
  apply continuous_iff_continuousAt.mpr
  intro z
  obtain ⟨n, hn⟩ := exists_tubeHeight_gt z.val.2
  have hf : Continuous (fun w : closedTube => tubeCharts n w.val) :=
    (tubeCharts n).continuous.comp continuous_subtype_val
  have heq : tubeLimit =ᶠ[𝓝 z] (fun w : closedTube => tubeCharts n w.val) := by
    apply eventually_nhds_iff.mpr
    refine ⟨{w | w.val.2 < tubeHeight n}, ?_, ?_, hn⟩
    · intro w hw
      exact tubeLimit_eq_chart w ⟨w.property.1, w.property.2, hw.le⟩
    · exact isOpen_lt (continuous_snd.comp continuous_subtype_val) continuous_const
  exact hf.continuousAt.congr_of_eventuallyEq heq

def tubeInteriorInclusion : tubeInterior → closedTube :=
  fun z => ⟨z.val, tubeInterior_subset_closed z.property⟩

noncomputable def tubeCore : tubeInterior → ProductPlane :=
  tubeLimit ∘ tubeInteriorInclusion

theorem continuous_tubeCore : Continuous tubeCore :=
  continuous_tubeLimit.comp (continuous_subtype_val.subtype_mk _)

theorem tubeCore_injective : Injective tubeCore := by
  intro x y h
  have heq := tubeLimit_injective h
  apply Subtype.ext
  exact congrArg (fun z : closedTube => z.val) heq

def tubeImage : Set ProductPlane := range tubeCore

theorem interior_tubeRectangle (H : ℝ) :
    interior (tubeRectangle H) = Ioo (-1 : ℝ) 1 ×ˢ Ioo 0 H := by
  rw [tubeRectangle, interior_prod_eq, interior_Icc, interior_Icc]

theorem interior_tubeRectangle_subset (H : ℝ) : interior (tubeRectangle H) ⊆ tubeInterior := by
  rw [interior_tubeRectangle]
  intro z hz
  exact ⟨hz.1, hz.2.1⟩

theorem tubeCore_image_set (s : Set tubeInterior) :
    tubeCore '' s = ⋃ n, tubeCharts n ''
      (((Subtype.val : tubeInterior → ProductPlane) '' s) ∩ interior (tubeRectangle (tubeHeight n))) := by
  ext p
  constructor
  · rintro ⟨z, hzs, hzp⟩
    obtain ⟨n, hn⟩ := exists_tubeHeight_gt z.val.2
    have hzint : z.val ∈ interior (tubeRectangle (tubeHeight n)) := by
      rw [interior_tubeRectangle]
      exact ⟨z.property.1, z.property.2, hn⟩
    apply mem_iUnion.mpr
    refine ⟨n, z.val, ⟨⟨z, hzs, rfl⟩, hzint⟩, ?_⟩
    exact (tubeLimit_eq_chart (tubeInteriorInclusion z) (interior_subset hzint)).symm.trans hzp
  · intro hp
    obtain ⟨n, z, ⟨⟨w, hws, hwz⟩, hzint⟩, hzp⟩ := mem_iUnion.mp hp
    subst z
    exact ⟨w, hws, (tubeLimit_eq_chart (tubeInteriorInclusion w) (interior_subset hzint)).trans hzp⟩

theorem tubeImage_iUnion :
    tubeImage = ⋃ n, tubeCharts n '' interior (tubeRectangle (tubeHeight n)) := by
  rw [tubeImage, ← image_univ, tubeCore_image_set]
  congr 1
  funext n
  congr 1
  apply inter_eq_right.mpr
  intro z hz
  exact ⟨⟨z, interior_tubeRectangle_subset _ hz⟩, mem_univ _, rfl⟩

theorem tubeImage_open : IsOpen tubeImage := by
  rw [tubeImage_iUnion]
  exact isOpen_iUnion fun n => (tubeCharts n).isOpenMap _ isOpen_interior

theorem tubeCore_openMap : IsOpenMap tubeCore := by
  intro s hs
  rw [tubeCore_image_set]
  have hopen : IsOpen ((Subtype.val : tubeInterior → ProductPlane) '' s) :=
    tubeInterior_open.isOpenMap_subtype_val s hs
  exact isOpen_iUnion fun n => (tubeCharts n).isOpenMap _ (hopen.inter isOpen_interior)

noncomputable def tubeCoreHomeomorph : tubeInterior ≃ₜ tubeImage := by
  let f : tubeInterior → tubeImage := fun z => ⟨tubeCore z, mem_range_self z⟩
  have hf : Bijective f := by
    constructor
    · intro x y h
      exact tubeCore_injective (congrArg Subtype.val h)
    · rintro ⟨p, z, rfl⟩
      exact ⟨z, rfl⟩
  exact (Equiv.ofBijective f hf).toHomeomorphOfContinuousOpen
    (continuous_tubeCore.subtype_mk _) (tubeCore_openMap.subtype_mk _)

theorem tubeChart_interior_subset (n : ℕ) :
    tubeCharts n '' interior (tubeRectangle (tubeHeight n)) ⊆ tubeImage := by
  rw [tubeImage_iUnion]
  exact subset_iUnion_of_subset n (Subset.refl _)

theorem tubeBasis_exterior {p : ProductPlane} (hp : p ∉ tubeImage)
    {i : ℕ} (hpi : p ∈ tubeBasis i) (n : ℕ) :
    ((tubeCharts n) ⁻¹' tubeBasis i \ tubeRectangle (tubeHeight n)).Nonempty := by
  classical
  by_contra h
  have hsub : tubeBasis i ⊆ tubeCharts n '' tubeRectangle (tubeHeight n) := by
    intro q hq
    refine ⟨(tubeCharts n).symm q, ?_, (tubeCharts n).apply_symm_apply q⟩
    by_contra hqrect
    exact h ⟨(tubeCharts n).symm q, by simpa using hq, hqrect⟩
  have hpint := ((tubeBasis_open i).subset_interior_iff.mpr hsub) hpi
  rw [← (tubeCharts n).image_interior] at hpint
  exact hp (tubeChart_interior_subset n hpint)

noncomputable def tubeCapPoint (x : Icc (-1 : ℝ) 1) (j : ℕ) : closedTube :=
  ⟨(x.val, tubeHeight j), x.property, (tubeHeight_pos j).le⟩

theorem tubeCaps_recurrent {p : ProductPlane} (hp : p ∉ tubeImage)
    {o : Set ProductPlane} (ho : IsOpen o) (hpo : p ∈ o) (m : ℕ) :
    ∃ j : ℕ, m ≤ j ∧ ∀ x : Icc (-1 : ℝ) 1, tubeLimit (tubeCapPoint x j) ∈ o := by
  obtain ⟨i, hpi, hio⟩ := tubeBasis_refines ho hpo
  obtain ⟨n, hmn, hni⟩ := tubeTarget_repeats i m
  refine ⟨n + 1, hmn.trans (Nat.le_succ n), ?_⟩
  intro x
  have hn : ((tubeCharts n) ⁻¹' tubeTarget n \ tubeRectangle (tubeHeight n)).Nonempty := by
    rw [hni]
    exact tubeBasis_exterior hp hpi n
  have hcap := tubeStepHomeomorph_cap n (tubeCharts n) hn x.val x.property
  rw [hni] at hcap
  apply hio
  rw [tubeLimit_eq_chart (tubeCapPoint x (n + 1))
    ⟨x.property, (tubeHeight_pos (n + 1)).le, le_rfl⟩]
  exact hcap

theorem tubeLimit_boundary {z : closedTube} (hz : z.val ∉ tubeInterior) :
    tubeLimit z ∉ tubeImage := by
  rintro ⟨w, hw⟩
  have heq : tubeInteriorInclusion w = z := tubeLimit_injective hw
  apply hz
  rw [← heq]
  exact w.property

def tubeSideSource (t : ℝ) : closedTube :=
  ⟨(1, max 0 t), ⟨by norm_num, le_rfl⟩, show 0 ≤ max 0 t from le_max_left _ _⟩

noncomputable def tubeSide (t : ℝ) : ProductPlane := tubeLimit (tubeSideSource t)

theorem continuous_tubeSide : Continuous tubeSide := by
  apply continuous_tubeLimit.comp
  exact ((continuous_const.prodMk (continuous_const.max continuous_id)).subtype_mk _)

theorem tubeSide_boundary (t : ℝ) : tubeSide t ∉ tubeImage := by
  apply tubeLimit_boundary
  intro h
  exact (lt_irrefl (1 : ℝ)) (show 1 < 1 from h.1.2)

theorem tubeSide_injOn : InjOn tubeSide (Ici 0) := by
  intro t ht u hu h
  change 0 ≤ t at ht
  change 0 ≤ u at hu
  have heq := congrArg (fun z : closedTube => z.val.2) (tubeLimit_injective h)
  simpa only [tubeSideSource, max_eq_right ht, max_eq_right hu] using heq

theorem tubeSide_recurrent {p : ProductPlane} (hp : p ∉ tubeImage)
    {o : Set ProductPlane} (ho : IsOpen o) (hpo : p ∈ o) (a : ℝ) :
    ∃ t : ℝ, a ≤ t ∧ 0 ≤ t ∧ tubeSide t ∈ o := by
  obtain ⟨m, hm⟩ := exists_nat_gt a
  obtain ⟨j, hmj, hcap⟩ := tubeCaps_recurrent hp ho hpo m
  refine ⟨tubeHeight j, ?_, (tubeHeight_pos j).le, ?_⟩
  · have hmj' : (m : ℝ) ≤ (j : ℝ) := by exact_mod_cast hmj
    have he := Real.add_one_le_exp (j : ℝ)
    change a ≤ Real.exp (j : ℝ)
    linarith
  · have heq : tubeSideSource (tubeHeight j) = tubeCapPoint ⟨1, by norm_num⟩ j := by
      apply Subtype.ext
      simp only [tubeSideSource, tubeCapPoint, max_eq_right (tubeHeight_pos j).le]
    simpa only [tubeSide, heq] using hcap ⟨1, by norm_num⟩

noncomputable def tubeHorizontalParam : ℝ ≃ₜ Ioo (-1 : ℝ) 1 :=
  (Homeomorph.unitBall : ℝ ≃ₜ Metric.ball (0 : ℝ) 1).trans
    (Homeomorph.setCongr (by ext x; simp [Real.ball_eq_Ioo]))

noncomputable def tubeVerticalParam : ℝ ≃ₜ Ioi (0 : ℝ) :=
  (Homeomorph.Set.univ ℝ).symm.trans Real.expPartialHomeomorph.toHomeomorphSourceTarget

noncomputable def tubeParam : ProductPlane ≃ₜ tubeInterior :=
  (tubeHorizontalParam.prodCongr tubeVerticalParam).trans
    (Homeomorph.Set.prod (Ioo (-1 : ℝ) 1) (Ioi (0 : ℝ))).symm

theorem tubeParam_snd (z : ProductPlane) : (tubeParam z).val.2 = Real.exp z.2 := rfl

noncomputable def planeProductHomeomorph : Plane ≃ₜ ProductPlane :=
  (EuclideanSpace.equiv (Fin 2) ℝ).toHomeomorph.trans
    (Homeomorph.finTwoArrow : (Fin 2 → ℝ) ≃ₜ ℝ × ℝ)

theorem planeProductHomeomorph_snd (z : Plane) : (planeProductHomeomorph z).2 = z 1 := rfl

def tubeBoundaryPlane : Set Plane := planeProductHomeomorph ⁻¹' tubeImageᶜ

noncomputable def tubeImageToPlane : tubeImage ≃ₜ (tubeBoundaryPlaneᶜ : Set Plane) :=
  planeProductHomeomorph.symm.subtype
    (p := fun z => z ∈ tubeImage) (q := fun z => z ∈ tubeBoundaryPlaneᶜ)
    (by intro z; simp [tubeBoundaryPlane])

noncomputable def recurrentTube : CanalModel where
  boundary := tubeBoundaryPlane
  straightening := planeProductHomeomorph.trans
    (tubeParam.trans (tubeCoreHomeomorph.trans tubeImageToPlane))
  recurrent_lines := by
    intro p hp o ho hpo m
    have hpp : planeProductHomeomorph p ∉ tubeImage := hp
    have hopen : IsOpen (planeProductHomeomorph '' o) := planeProductHomeomorph.isOpenMap o ho
    obtain ⟨j, hmj, hcap⟩ := tubeCaps_recurrent hpp hopen ⟨p, hpo, rfl⟩ m
    refine ⟨j, hmj, ?_⟩
    intro w hw
    let z := tubeParam (planeProductHomeomorph w)
    have hzheight : z.val.2 = tubeHeight j := by
      rw [tubeParam_snd, planeProductHomeomorph_snd, hw]
      rfl
    have heq : tubeInteriorInclusion z = tubeCapPoint ⟨z.val.1, z.property.1.1.le,
        z.property.1.2.le⟩ j := by
      apply Subtype.ext
      exact Prod.ext rfl hzheight
    have hmem := hcap ⟨z.val.1, z.property.1.1.le, z.property.1.2.le⟩
    rw [← heq] at hmem
    obtain ⟨q, hqo, hq⟩ := hmem
    have hinv := congrArg planeProductHomeomorph.symm hq
    have heq' : q = planeProductHomeomorph.symm (tubeLimit (tubeInteriorInclusion z)) := by
      simpa only [Homeomorph.symm_apply_apply] using hinv
    change planeProductHomeomorph.symm (tubeLimit (tubeInteriorInclusion z)) ∈ o
    rw [← heq']
    exact hqo

noncomputable def tubeHit (a : ℝ) (i : ℕ) : ℝ := by
  classical
  by_cases h : (tubeBasis i ∩ tubeImageᶜ).Nonempty
  · let p := Classical.choose h
    have hp := Classical.choose_spec h
    exact Classical.choose (tubeSide_recurrent hp.2 (tubeBasis_open i) hp.1 (a + 1))
  · exact max 0 (a + 1)

theorem tubeHit_spec (a : ℝ) (i : ℕ) (h : (tubeBasis i ∩ tubeImageᶜ).Nonempty) :
    a + 1 ≤ tubeHit a i ∧ 0 ≤ tubeHit a i ∧ tubeSide (tubeHit a i) ∈ tubeBasis i := by
  classical
  unfold tubeHit
  rw [dif_pos h]
  exact Classical.choose_spec (tubeSide_recurrent (Classical.choose_spec h).2
    (tubeBasis_open i) (Classical.choose_spec h).1 (a + 1))

noncomputable def tubeBound (a : ℝ) : ℕ → ℝ
  | 0 => max 0 (a + 1)
  | n + 1 => max (tubeBound a n) (tubeHit a n)

theorem tubeBound_mono (a : ℝ) : Monotone (tubeBound a) :=
  monotone_nat_of_le_succ (fun _ => le_max_left _ _)

theorem tubeBound_ge (a : ℝ) (n : ℕ) : a + 1 ≤ tubeBound a n :=
  (le_max_right _ _).trans (tubeBound_mono a (Nat.zero_le n))

theorem tubeBound_nonneg (a : ℝ) (n : ℕ) : 0 ≤ tubeBound a n :=
  (le_max_left _ _).trans (tubeBound_mono a (Nat.zero_le n))

theorem tubeHit_le_bound (a : ℝ) {i n : ℕ} (hin : i < n) : tubeHit a i ≤ tubeBound a n :=
  (show tubeHit a i ≤ tubeBound a (i + 1) from le_max_right _ _).trans
    (tubeBound_mono a hin)

noncomputable def tubeEnds : ℕ → ℝ
  | 0 => 1
  | n + 1 => tubeBound (tubeEnds n + 1) (n + 1) + 1

theorem tubeEnds_step (n : ℕ) : tubeEnds n + 2 < tubeEnds (n + 1) := by
  have h := tubeBound_ge (tubeEnds n + 1) (n + 1)
  change tubeEnds n + 2 < tubeBound (tubeEnds n + 1) (n + 1) + 1
  linarith

theorem tubeEnds_strictMono : StrictMono tubeEnds :=
  strictMono_nat_of_lt_succ (fun n => by have h := tubeEnds_step n; linarith)

theorem tubeEnds_pos (n : ℕ) : 0 < tubeEnds n := by
  have h := tubeEnds_strictMono.monotone (Nat.zero_le n)
  change 1 ≤ tubeEnds n at h
  linarith

def tubeArcInterval (n : ℕ) : Set ℝ := Icc (tubeEnds n + 1) (tubeEnds (n + 1))

def tubeRayArc (n : ℕ) : Set ProductPlane := tubeSide '' tubeArcInterval n

theorem tubeArcInterval_nontrivial (n : ℕ) : (tubeArcInterval n).Nontrivial := by
  have h := tubeEnds_step n
  have hab : tubeEnds n + 1 < tubeEnds (n + 1) := by linarith
  exact ⟨tubeEnds n + 1, ⟨le_rfl, hab.le⟩, tubeEnds (n + 1),
    ⟨hab.le, le_rfl⟩, hab.ne⟩

theorem tubeArcInterval_nonneg (n : ℕ) : tubeArcInterval n ⊆ Ici 0 := by
  intro t ht
  have h := tubeEnds_pos n
  change 0 ≤ t
  change tubeEnds n + 1 ≤ t ∧ t ≤ tubeEnds (n + 1) at ht
  linarith [ht.1]

theorem tubeRayArc_connected (n : ℕ) : IsConnected (tubeRayArc n) :=
  (isConnected_Icc (by have h := tubeEnds_step n; linarith)).image _ continuous_tubeSide.continuousOn

theorem tubeRayArc_nontrivial (n : ℕ) : (tubeRayArc n).Nontrivial :=
  (tubeArcInterval_nontrivial n).image_of_injOn (tubeSide_injOn.mono (tubeArcInterval_nonneg n))

theorem tubeRayArc_boundary (n : ℕ) : tubeRayArc n ⊆ tubeImageᶜ := by
  rintro p ⟨t, -, rfl⟩
  exact tubeSide_boundary t

theorem tubeRayArc_hits (n : ℕ) {i : ℕ} (hin : i ≤ n)
    (hne : (tubeBasis i ∩ tubeImageᶜ).Nonempty) : (tubeRayArc n ∩ tubeBasis i).Nonempty := by
  have ht := tubeHit_spec (tubeEnds n + 1) i hne
  refine ⟨tubeSide (tubeHit (tubeEnds n + 1) i), ?_, ht.2.2⟩
  refine ⟨tubeHit (tubeEnds n + 1) i, ⟨?_, ?_⟩, rfl⟩
  · linarith [ht.1]
  · have hu := tubeHit_le_bound (tubeEnds n + 1) (Nat.lt_succ_of_le hin)
    change tubeHit (tubeEnds n + 1) i ≤ tubeBound (tubeEnds n + 1) (n + 1) + 1
    linarith

theorem tubeArcInterval_disjoint_of_lt {i j : ℕ} (hij : i < j) :
    Disjoint (tubeArcInterval i) (tubeArcInterval j) := by
  apply disjoint_left.mpr
  intro t hti htj
  have he := tubeEnds_strictMono.monotone hij
  change tubeEnds (i + 1) ≤ tubeEnds j at he
  have hi : t ≤ tubeEnds (i + 1) := hti.2
  have hj : tubeEnds j + 1 ≤ t := htj.1
  linarith

theorem tubeArcInterval_pairwise_disjoint :
    Pairwise (fun i j => Disjoint (tubeArcInterval i) (tubeArcInterval j)) := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact tubeArcInterval_disjoint_of_lt h
  · exact (tubeArcInterval_disjoint_of_lt h).symm

theorem tubeRayArc_pairwise_disjoint :
    Pairwise (fun i j => Disjoint (tubeRayArc i) (tubeRayArc j)) := by
  intro i j hij
  apply disjoint_left.mpr
  rintro p ⟨t, ht, htp⟩ ⟨u, hu, hup⟩
  have htu := tubeSide_injOn (tubeArcInterval_nonneg i ht)
    (tubeArcInterval_nonneg j hu) (htp.trans hup.symm)
  subst u
  exact (tubeArcInterval_pairwise_disjoint hij).le_bot ⟨ht, hu⟩

def tubeColor (c : ℕ) : Set ProductPlane := ⋃ m, tubeRayArc (Nat.pair c m)

theorem tubeColor_boundary (c : ℕ) : tubeColor c ⊆ tubeImageᶜ := by
  intro p hp
  obtain ⟨m, hm⟩ := mem_iUnion.mp hp
  exact tubeRayArc_boundary _ hm

theorem tubeColor_nontrivial (c : ℕ) : (tubeColor c).Nontrivial :=
  (tubeRayArc_nontrivial (Nat.pair c 0)).mono (subset_iUnion_of_subset 0 (Subset.refl _))

theorem tubeColor_hits_open (c : ℕ) {o : Set ProductPlane} (ho : IsOpen o)
    (hne : (o ∩ tubeImageᶜ).Nonempty) : (tubeColor c ∩ o).Nonempty := by
  obtain ⟨p, hpo, hpk⟩ := hne
  obtain ⟨i, hpi, hio⟩ := tubeBasis_refines ho hpo
  obtain ⟨q, hqa, hqi⟩ := tubeRayArc_hits (Nat.pair c i) (Nat.right_le_pair _ _) ⟨p, hpi, hpk⟩
  exact ⟨q, mem_iUnion.mpr ⟨i, hqa⟩, hio hqi⟩

theorem tubeColor_dense (c : ℕ) : tubeImageᶜ ⊆ closure (tubeColor c) := by
  intro p hp
  apply mem_closure_iff.mpr
  intro o ho hpo
  simpa only [inter_comm] using tubeColor_hits_open c ho ⟨p, hpo, hp⟩

theorem tubeColor_connected (c : ℕ) : IsConnected (tubeColor c) := by
  refine ⟨(tubeColor_nontrivial c).nonempty, ?_⟩
  intro u v hu hv hcover hune hvne
  obtain ⟨p, hpc, hpu⟩ := hune
  obtain ⟨q, hqc, hqv⟩ := hvne
  obtain ⟨i, hpi, hiu⟩ := tubeBasis_refines hu hpu
  obtain ⟨j, hqj, hjv⟩ := tubeBasis_refines hv hqv
  let n := Nat.pair c (max i j)
  have hmn : max i j ≤ n := Nat.right_le_pair _ _
  have harcsub : tubeRayArc n ⊆ tubeColor c := subset_iUnion_of_subset (max i j) (Subset.refl _)
  obtain ⟨x, hxa, hxi⟩ := tubeRayArc_hits n ((le_max_left _ _).trans hmn)
    ⟨p, hpi, tubeColor_boundary c hpc⟩
  obtain ⟨y, hya, hyj⟩ := tubeRayArc_hits n ((le_max_right _ _).trans hmn)
    ⟨q, hqj, tubeColor_boundary c hqc⟩
  obtain ⟨z, hza, hzu, hzv⟩ := (tubeRayArc_connected n).isPreconnected u v hu hv
    (harcsub.trans hcover) ⟨x, hxa, hiu hxi⟩ ⟨y, hya, hjv hyj⟩
  exact ⟨z, harcsub hza, hzu, hzv⟩

theorem tubeColor_pairwise_disjoint : Pairwise (fun c d => Disjoint (tubeColor c) (tubeColor d)) := by
  intro c d hcd
  apply disjoint_left.mpr
  intro p hpc hpd
  obtain ⟨m, hpm⟩ := mem_iUnion.mp hpc
  obtain ⟨n, hpn⟩ := mem_iUnion.mp hpd
  have hpair : Nat.pair c m ≠ Nat.pair d n := by
    intro h
    have heq := congrArg (fun t : ℕ => t.unpair.1) h
    exact hcd (by simpa only [Nat.unpair_pair] using heq)
  exact (tubeRayArc_pairwise_disjoint hpair).le_bot ⟨hpm, hpn⟩

def tubeBottomSource (x : Icc (-1 / 2 : ℝ) (1 / 2)) : closedTube :=
  ⟨(x.val, 0), ⟨by linarith [x.property.1], by linarith [x.property.2]⟩,
    show (0 : ℝ) ≤ 0 from le_rfl⟩

noncomputable def tubeBottom : Icc (-1 / 2 : ℝ) (1 / 2) → ProductPlane := tubeLimit ∘ tubeBottomSource

theorem continuous_tubeBottom : Continuous tubeBottom := by
  apply continuous_tubeLimit.comp
  have hc : Continuous (fun x : Icc (-1 / 2 : ℝ) (1 / 2) => (x.val, (0 : ℝ))) :=
    continuous_subtype_val.prodMk continuous_const
  exact hc.subtype_mk _

theorem tubeBottom_injective : Injective tubeBottom := by
  intro x y h
  have heq := congrArg (fun z : closedTube => z.val.1) (tubeLimit_injective h)
  exact Subtype.ext heq

def tubeBottomArc : Set ProductPlane := range tubeBottom

theorem tubeBottom_apply (x : Icc (-1 / 2 : ℝ) (1 / 2)) :
    tubeBottom x = (x.val, 0) := by
  change tubeLimit (tubeBottomSource x) = (x.val, 0)
  exact tubeLimit_eq_chart (tubeBottomSource x)
    ⟨(tubeBottomSource x).property.1, le_rfl, (tubeHeight_pos 0).le⟩

theorem tubeBottomArc_compact : IsCompact tubeBottomArc := isCompact_range continuous_tubeBottom

theorem tubeBottomArc_boundary : tubeBottomArc ⊆ tubeImageᶜ := by
  rintro p ⟨x, rfl⟩
  apply tubeLimit_boundary
  intro h
  exact (lt_irrefl (0 : ℝ)) (show 0 < 0 from h.2)

theorem tubeBottomArc_connected : IsConnected tubeBottomArc := by
  rw [tubeBottomArc, ← image_univ]
  let : ConnectedSpace (Icc (-1 / 2 : ℝ) (1 / 2)) :=
    isConnected_iff_connectedSpace.mp (isConnected_Icc (by norm_num : (-1 / 2 : ℝ) ≤ 1 / 2))
  exact isConnected_univ.image _ continuous_tubeBottom.continuousOn

theorem tubeBottomArc_nontrivial : tubeBottomArc.Nontrivial := by
  let x : Icc (-1 / 2 : ℝ) (1 / 2) := ⟨-1 / 2, by norm_num⟩
  let y : Icc (-1 / 2 : ℝ) (1 / 2) := ⟨1 / 2, by norm_num⟩
  refine ⟨tubeBottom x, mem_range_self x, tubeBottom y, mem_range_self y, ?_⟩
  intro h
  have heq := congrArg Subtype.val (tubeBottom_injective h)
  norm_num [x, y] at heq

theorem tubeBottomArc_disjoint_color (c : ℕ) : Disjoint tubeBottomArc (tubeColor c) := by
  apply disjoint_left.mpr
  rintro p ⟨x, hxp⟩ hpc
  obtain ⟨m, t, -, htp⟩ := mem_iUnion.mp hpc
  have heq := congrArg (fun z : closedTube => z.val.1)
    (tubeLimit_injective (hxp.trans htp.symm))
  have hx : x.val = 1 := heq
  have hxu := x.property.2
  rw [hx] at hxu
  norm_num at hxu

def tubeTransport (s : Set ProductPlane) : Set Plane := planeProductHomeomorph.symm '' s

theorem tubeTransport_boundary {s : Set ProductPlane} (hs : s ⊆ tubeImageᶜ) :
    tubeTransport s ⊆ tubeBoundaryPlane := by
  rintro p ⟨q, hq, rfl⟩
  change planeProductHomeomorph (planeProductHomeomorph.symm q) ∉ tubeImage
  rw [Homeomorph.apply_symm_apply]
  exact hs hq

theorem tubeTransport_connected {s : Set ProductPlane} (hs : IsConnected s) :
    IsConnected (tubeTransport s) := hs.image _ planeProductHomeomorph.symm.continuous.continuousOn

theorem tubeTransport_compact {s : Set ProductPlane} (hs : IsCompact s) :
    IsCompact (tubeTransport s) := hs.image planeProductHomeomorph.symm.continuous

theorem tubeTransport_nontrivial {s : Set ProductPlane} (hs : s.Nontrivial) :
    (tubeTransport s).Nontrivial := hs.image planeProductHomeomorph.symm.injective

theorem tubeTransport_disjoint {s t : Set ProductPlane} (hst : Disjoint s t) :
    Disjoint (tubeTransport s) (tubeTransport t) :=
  (disjoint_image_iff planeProductHomeomorph.symm.injective).mpr hst

theorem tubeTransport_dense {s : Set ProductPlane} (hs : tubeImageᶜ ⊆ closure s) :
    tubeBoundaryPlane ⊆ closure (tubeTransport s) := by
  intro p hp
  have hq := hs hp
  have hi : planeProductHomeomorph.symm (planeProductHomeomorph p) ∈
      planeProductHomeomorph.symm '' closure s := ⟨planeProductHomeomorph p, hq, rfl⟩
  rw [planeProductHomeomorph.symm.image_closure] at hi
  change p ∈ closure (planeProductHomeomorph.symm '' s)
  simpa only [Homeomorph.symm_apply_apply] using hi

/-- The boundary partition is obtained directly from the recurrent retained ray. -/
noncomputable def tubeBoundaryPieces : BoundaryPieces recurrentTube.boundary where
  arc := tubeTransport tubeBottomArc
  arc_subset := tubeTransport_boundary tubeBottomArc_boundary
  arc_connected := tubeTransport_connected tubeBottomArc_connected
  arc_nontrivial := tubeTransport_nontrivial tubeBottomArc_nontrivial
  densePieces n := tubeTransport (tubeColor (n + 1))
  pieces_subset n := tubeTransport_boundary (tubeColor_boundary (n + 1))
  pieces_connected n := tubeTransport_connected (tubeColor_connected (n + 1))
  pieces_nontrivial n := tubeTransport_nontrivial (tubeColor_nontrivial (n + 1))
  pieces_dense n := tubeTransport_dense (tubeColor_dense (n + 1))
  pieces_disjoint := fun _ _ hij => tubeTransport_disjoint
    (tubeColor_pairwise_disjoint (fun h => hij (Nat.succ.inj h)))
  arc_disjoint n := tubeTransport_disjoint (tubeBottomArc_disjoint_color (n + 1))
  reserve := tubeTransport (tubeColor 0)
  reserve_subset := tubeTransport_boundary (tubeColor_boundary 0)
  reserve_connected := tubeTransport_connected (tubeColor_connected 0)
  reserve_nontrivial := tubeTransport_nontrivial (tubeColor_nontrivial 0)
  reserve_arc_disjoint := tubeTransport_disjoint (tubeBottomArc_disjoint_color 0).symm
  reserve_pieces_disjoint := fun n => tubeTransport_disjoint
    (tubeColor_pairwise_disjoint (by omega : 0 ≠ n + 1))

noncomputable def wongPlanarData : PlanarData :=
  recurrentTube.toPlanarData tubeBoundaryPieces.toRayPartition.toRayModel

/-- An unconditional connectedness-preserving bijection of the Euclidean plane. -/
noncomputable def wongCounterexample : Plane ≃ Plane := wongPlanarData.bijection

theorem wongPlanarData_arc_eq : wongPlanarData.arc = tubeTransport tubeBottomArc := by
  change ((Subtype.val : recurrentTube.boundary → Plane) ''
    ((Subtype.val : recurrentTube.boundary → Plane) ⁻¹' tubeTransport tubeBottomArc)) =
      tubeTransport tubeBottomArc
  exact subtype_val_image_preimage (tubeTransport_boundary tubeBottomArc_boundary)

theorem wongCounterexample_preimage_bottom :
    wongCounterexample ⁻¹' tubeTransport tubeBottomArc = planeCantor := by
  rw [← wongPlanarData_arc_eq]
  exact wongPlanarData.bijection_preimage_arc

theorem wongCounterexample_compact_witness :
    IsCompact (tubeTransport tubeBottomArc) ∧ IsConnected (tubeTransport tubeBottomArc) ∧
      (tubeTransport tubeBottomArc).Nontrivial ∧
      wongCounterexample ⁻¹' tubeTransport tubeBottomArc = planeCantor :=
  ⟨tubeTransport_compact tubeBottomArc_compact, tubeTransport_connected tubeBottomArc_connected,
    tubeTransport_nontrivial tubeBottomArc_nontrivial, wongCounterexample_preimage_bottom⟩

theorem wongCounterexample_preserves_connectedness :
    Mathoverflow235893.IsConnectedMap wongCounterexample :=
  wongPlanarData.bijection_isConnectedMap

theorem wongCounterexample_inverse_fails :
    ¬ Mathoverflow235893.IsConnectedMap wongCounterexample.symm :=
  wongPlanarData.inverse_not_isConnectedMap

theorem wong235893_negative_answer : ¬ RepositoryAssertion := wongPlanarData.not_repositoryAssertion

/-- The exact repository assertion has the answer `False`, with no geometric assumptions. -/
theorem wong235893_repository_answer :
    False ↔ ∀ n > 1, ∀ f : EuclideanSpace ℝ (Fin n) ≃ EuclideanSpace ℝ (Fin n),
      Mathoverflow235893.IsConnectedMap f → Mathoverflow235893.IsConnectedMap f.symm :=
  wongPlanarData.repository_answer_false


end RecurrentTube


end Wong235893

#print axioms Wong235893.wong235893_repository_answer
#print axioms Wong235893.wongCounterexample_preserves_connectedness
#print axioms Wong235893.wongCounterexample_inverse_fails
#print axioms Wong235893.tubeBoundaryPieces
#print axioms Wong235893.recurrentTube

#print axioms Wong235893.gate_isClopen
#print axioms Wong235893.isConnectedMap_of_recurrent_levels
#print axioms Wong235893.not_isConnected_planeCantor
#print axioms Wong235893.rho_eq_zero_iff
#print axioms Wong235893.slitHomeomorph
#print axioms Wong235893.PlanarData.repository_answer_false
#print axioms Wong235893.CanalModel.not_repositoryAssertion
#print axioms Wong235893.ray_isConnectedMap_of_dense_pieces
#print axioms Wong235893.cardinal_connected_plane_set
#print axioms Wong235893.cardinal_planeCantor
#print axioms Wong235893.completePieces_image_piece
#print axioms Wong235893.cardinal_unassigned_of_reserved
#print axioms Wong235893.RayPartition.toRayModel
#print axioms Wong235893.cantorAt_pairwise_disjoint
#print axioms Wong235893.sourceFamily
#print axioms Wong235893.not_repositoryAssertion_of_geometry
#print axioms Wong235893.connectedComponentIn_inter_frontier
#print axioms Wong235893.properContinuum_interior_empty
#print axioms Wong235893.composants_not_countable
#print axioms Wong235893.boundaryPieces_of_punctured_continuum
#print axioms Wong235893.not_repositoryAssertion_of_compact_canal
#print axioms Wong235893.finitePartHomeomorph
#print axioms Wong235893.CompactifiedCanal.repository_answer_false
#print axioms Wong235893.repository_answer_false_of_geometricExistence
#print axioms Wong235893.ClosedCoverHomeomorphData.toHomeomorph
#print axioms Wong235893.horizontalPieces_locallyFinite
#print axioms Wong235893.CanalStripAtlas.toCanalModel
#print axioms Wong235893.compactifiedCanalOfStripAtlas
#print axioms Wong235893.boundaryInterpolationHomeomorph

#print axioms Wong235893.inverseLimit_connected
#print axioms Wong235893.proper_inverseLimit_projection
#print axioms Wong235893.goldenArc_embedding
#print axioms Wong235893.goldenCylinder_exists
#print axioms Wong235893.goldenContinuum_indecomposable
#print axioms Wong235893.goldenArc_properContinuum
#print axioms Wong235893.goldenCore_conjugacy

-- Check the right-hand side against the imported repository theorem's actual type.
-- This inspects its declaration type without using its admitted proof.
run_elab do
  let reference ← Lean.getConstInfo `Mathoverflow235893.mathoverflow_235893
  let rhs := reference.type.appArg!
  unless ← Lean.Meta.isDefEq rhs (Lean.mkConst `Wong235893.RepositoryAssertion) do
    throwError "The counterexample target does not match the repository statement."
  Lean.logInfo "Repository right-hand side matches by definitional equality."
  let result ← Lean.getConstInfo `Wong235893.wong235893_repository_answer
  let expected := Lean.mkApp2 (Lean.mkConst `Iff) (Lean.mkConst `False) rhs
  unless ← Lean.Meta.isDefEq result.type expected do
    throwError "The unconditional answer theorem does not match False ↔ the repository assertion."
  Lean.logInfo "Unconditional answer False matches the exact repository statement."

-- Reject any nonstandard axiom in any theorem or definition in this namespace.
run_elab do
  let env ← Lean.getEnv
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : ℕ := 0
  for (name, _) in env.constants.toList do
    if (`Wong235893).isPrefixOf name then
      for axiomName in (← Lean.collectAxioms name) do
        unless allowed.contains axiomName do
          throwError m!"Nonstandard axiom {axiomName} in {name}."
      checked := checked + 1
  Lean.logInfo m!"Axiom audit passed for {checked} declarations."
