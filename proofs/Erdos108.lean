/-!
# A counterexample to Erdős problem 108

For every chromatic threshold, we construct an arc graph exceeding that threshold
whose four-cycle-free subgraphs are six-colorable.  Taking girth five and chromatic
number seven therefore disproves the assertion in the target.

The base graph is obtained by finite counting in a multipartite random model.
Its parts have explicitly chosen sizes.  All probability estimates, coloring
arguments, and the lift to arbitrary universes are proved below.
-/

open SimpleGraph

universe u

section ArcGraph

variable {V : Type u} [LinearOrder V]

/-- Edges directed from their smaller endpoint to their larger endpoint. -/
abbrev Arc (F : SimpleGraph V) := {e : V × V // e.1 < e.2 ∧ F.Adj e.1 e.2}

/-- The undirected graph on concatenating directed edges. -/
def arcGraph (F : SimpleGraph V) : SimpleGraph (Arc F) where
  Adj a b := a.1.2 = b.1.1 ∨ b.1.2 = a.1.1
  symm := ⟨fun _ _ => Or.symm⟩
  loopless := ⟨fun a h => (ne_of_lt a.2.1) (h.elim Eq.symm Eq.symm)⟩

/-- The colors appearing on edges directed out of a vertex. -/
def outgoingColors {F : SimpleGraph V} {α : Type*}
    (c : (arcGraph F).Coloring α) (v : V) : Set α :=
  {i | ∃ a : Arc F, a.1.1 = v ∧ c a = i}

theorem outgoingColors_ne {F : SimpleGraph V} {α : Type*}
    (c : (arcGraph F).Coloring α) (a : Arc F) :
    outgoingColors c a.1.1 ≠ outgoingColors c a.1.2 := by
  intro h
  have hm : c a ∈ outgoingColors c a.1.1 := ⟨a, rfl, rfl⟩
  rw [h] at hm
  obtain ⟨b, hb, hbc⟩ := hm
  exact c.valid (Or.inl hb.symm) hbc.symm

/-- A coloring of the arc graph gives a set-valued coloring of the base graph. -/
def baseColoring {F : SimpleGraph V} {α : Type*}
    (c : (arcGraph F).Coloring α) : F.Coloring (Set α) :=
  SimpleGraph.Coloring.mk (outgoingColors c) fun {x y} hxy => by
    rcases lt_or_gt_of_ne hxy.ne with hlt | hgt
    · exact outgoingColors_ne c ⟨(x, y), hlt, hxy⟩
    · exact (outgoingColors_ne c ⟨(y, x), hgt, hxy.symm⟩).symm

/-- Lemma 2 of the attachment, stated without natural-valued chromatic numbers. -/
theorem base_colorable_of_arc_colorable {F : SimpleGraph V} {t : ℕ}
    (h : (arcGraph F).Colorable t) : F.Colorable (2 ^ t) := by
  obtain ⟨c⟩ := h
  simpa using (baseColoring c).colorable

end ArcGraph

/-- Absence of a four-cycle, allowing arbitrary deletions of edges. -/
def FourCycleFree {V : Type*} (H : SimpleGraph V) : Prop :=
  ∀ a b x y, a ≠ b → x ≠ y →
    H.Adj a x → H.Adj a y → H.Adj b x → H.Adj b y → False

theorem fourCycleFree_of_girth_ge_five {V : Type*} {H : SimpleGraph V}
    (hg : 5 ≤ H.girth) : FourCycleFree H := by
  intro a b x y hab hxy hax hay hbx hby
  let w : H.Walk a a := .cons hax (.cons hbx.symm (.cons hby (.cons hay.symm .nil)))
  have hw : w.IsCycle := {
    edges_nodup := by simp [w, hab, hab.symm, hxy, hax.ne, hay.ne, hby.ne]
    ne_nil := by simp [w]
    support_nodup := by simp [w, hab.symm, hxy, hax.ne.symm, hay.ne.symm, hbx.ne.symm, hby.ne]
  }
  have hle := H.girth_le_length hw
  have hlen : w.length = 4 := rfl
  omega

/-- Distinct vertices with two neighbors in `T` require distinct neighbor pairs. -/
theorem card_le_choose_two_of_fourCycleFree {V : Type*} {H : SimpleGraph V}
    (h4 : FourCycleFree H) (S T : Finset V)
    (hS : ∀ a ∈ S, ∃ x ∈ T, ∃ y ∈ T, x ≠ y ∧ H.Adj a x ∧ H.Adj a y) :
    S.card ≤ T.card.choose 2 := by
  classical
  have hpair : ∀ a : S, ∃ p : T.powersetCard 2,
      ∀ x ∈ p.1, H.Adj a.1 x := by
    intro a
    obtain ⟨x, hx, y, hy, hxy, hax, hay⟩ := hS a.1 a.2
    refine ⟨⟨{x, y}, ?_⟩, ?_⟩
    · refine Finset.mem_powersetCard.mpr ⟨?_, by simp [hxy]⟩
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hx
      · simpa only [Finset.mem_singleton.mp hz] using hy
    · intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hax
      · exact hay
  choose p hp using hpair
  have hinj : Function.Injective p := by
    intro a b heq
    apply Subtype.ext
    by_contra hab
    have hcard : (p a).1.card = 2 := (Finset.mem_powersetCard.mp (p a).2).2
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp (show 1 < (p a).1.card by omega)
    have hx' : x ∈ (p b).1 := by simpa only [heq] using hx
    have hy' : y ∈ (p b).1 := by simpa only [heq] using hy
    exact h4 a b x y hab hxy (hp a x hx) (hp a y hy) (hp b x hx') (hp b y hy')
  simpa using Fintype.card_le_of_injective p hinj

section Selection

variable {V : Type u} [LinearOrder V] {F : SimpleGraph V}

/-- An arc vertex with at least two distinct outgoing neighbors in `H`. -/
def Branching (H : SimpleGraph (Arc F)) (a : Arc F) : Prop :=
  ∃ b c : Arc F, b ≠ c ∧ H.Adj a b ∧ H.Adj a c ∧
    a.1.2 = b.1.1 ∧ a.1.2 = c.1.1

/-- The base graph whose directed edges are the members of `S`. -/
def baseOfArcs (S : Set (Arc F)) : SimpleGraph V where
  Adj x y := ∃ a ∈ S, (a.1.1 = x ∧ a.1.2 = y) ∨ (a.1.1 = y ∧ a.1.2 = x)
  symm := ⟨fun _ _ ⟨a, ha, he⟩ => ⟨a, ha, he.symm⟩⟩
  loopless := ⟨fun x ⟨a, _, he⟩ => by
    rcases he with he | he <;> exact (ne_of_lt a.2.1) (he.1.trans he.2.symm)⟩

theorem baseOfArcs_le (S : Set (Arc F)) : baseOfArcs S ≤ F := by
  intro x y ⟨a, _, he⟩
  rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact a.2.2
  · exact a.2.2.symm

theorem branching_colorable {H : SimpleGraph (Arc F)} {a : ℕ}
    (hH : H ≤ arcGraph F) (hc : (baseOfArcs {b | Branching H b}).Colorable a) :
    (H.induce {b | Branching H b}).Colorable a := by
  obtain ⟨c⟩ := hc
  refine ⟨SimpleGraph.Coloring.mk (fun b => c b.1.1.1) ?_⟩
  intro b d hbd
  apply c.valid
  rcases hH hbd with hbd | hdb
  · exact ⟨b.1, b.2, Or.inl ⟨rfl, hbd⟩⟩
  · exact ⟨d.1, d.2, Or.inr ⟨rfl, hdb⟩⟩

variable [Fintype V]

noncomputable def outgoingArcs (F : SimpleGraph V) (v : V) : Finset (Arc F) := by
  classical
  exact Finset.univ.filter fun a => a.1.1 = v

noncomputable def incomingBranches (H : SimpleGraph (Arc F)) (v : V) : Finset (Arc F) := by
  classical
  exact Finset.univ.filter fun a => a.1.2 = v ∧ Branching H a

theorem incomingBranches_card_le {H : SimpleGraph (Arc F)}
    (h4 : FourCycleFree H) (v : V) :
    (incomingBranches H v).card ≤ (outgoingArcs F v).card.choose 2 := by
  classical
  apply card_le_choose_two_of_fourCycleFree h4
  intro a ha
  obtain ⟨hav, b, c, hbc, hab, hac, hbt, hct⟩ :=
    (Finset.mem_filter.mp ha).2
  refine ⟨b, ?_, c, ?_, hbc, hab, hac⟩
  · simp [outgoingArcs, ← hbt, hav]
  · simp [outgoingArcs, ← hct, hav]

theorem selected_degree_le {H : SimpleGraph (Arc F)} (h4 : FourCycleFree H) (v : V) :
    Nat.card ((baseOfArcs {a | Branching H a}).neighborSet v) ≤
      (outgoingArcs F v).card + (outgoingArcs F v).card.choose 2 := by
  classical
  let J := baseOfArcs {a | Branching H a}
  change Nat.card (J.neighborSet v) ≤ _
  rw [Nat.card_eq_fintype_card, SimpleGraph.card_neighborSet_eq_degree]
  have hsub : J.neighborFinset v ⊆
      (outgoingArcs F v).image (fun a => a.1.2) ∪
        (incomingBranches H v).image (fun a => a.1.1) := by
    intro w hw
    obtain ⟨a, ha, he⟩ := (J.mem_neighborFinset v w).mp hw
    rcases he with ⟨hat, hah⟩ | ⟨hat, hah⟩
    · apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨a, by simp [outgoingArcs, hat], hah⟩
    · apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨a,
        Finset.mem_filter.mpr ⟨Finset.mem_univ a, hah, ha⟩, hat⟩
  calc
    J.degree v = (J.neighborFinset v).card := rfl
    _ ≤ ((outgoingArcs F v).image (fun a => a.1.2) ∪
        (incomingBranches H v).image (fun a => a.1.1)).card := Finset.card_le_card hsub
    _ ≤ ((outgoingArcs F v).image (fun a => a.1.2)).card +
        ((incomingBranches H v).image (fun a => a.1.1)).card := Finset.card_union_le _ _
    _ ≤ (outgoingArcs F v).card + (incomingBranches H v).card :=
      Nat.add_le_add (Finset.card_image_le) (Finset.card_image_le)
    _ ≤ _ := Nat.add_le_add_left (incomingBranches_card_le h4 v) _

end Selection

/-- Greedy coloring, with a low-degree vertex available in every remaining set. -/
theorem colorable_of_low_degree {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] {k : ℕ} (hk : 0 < k)
    (hdeg : ∀ S : Finset V, S.Nonempty → ∃ v ∈ S, (S.filter (H.Adj v)).card < k) :
    H.Colorable k := by
  classical
  have hcolor : ∀ S : Finset V, ∃ c : V → Fin k,
      ∀ x ∈ S, ∀ y ∈ S, H.Adj x y → c x ≠ c y := by
    intro S
    induction S using Finset.strongInductionOn with
    | _ S ih =>
      by_cases hS : S.Nonempty
      · obtain ⟨v, hv, hvc⟩ := hdeg S hS
        obtain ⟨c, hc⟩ := ih (S.erase v) (Finset.erase_ssubset hv)
        have hcard : ((S.filter (H.Adj v)).image c).card <
            (Finset.univ : Finset (Fin k)).card := by
          simpa using lt_of_le_of_lt Finset.card_image_le hvc
        obtain ⟨j, _, hj⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
        refine ⟨Function.update c v j, ?_⟩
        intro x hx y hy hxy
        by_cases hxv : x = v
        · subst x
          have hyv : y ≠ v := hxy.ne.symm
          simp only [Function.update_self, Function.update_of_ne hyv]
          intro heq
          exact hj (Finset.mem_image.mpr ⟨y, Finset.mem_filter.mpr ⟨hy, hxy⟩, heq.symm⟩)
        · by_cases hyv : y = v
          · subst y
            simp only [Function.update_self, Function.update_of_ne hxv]
            intro heq
            exact hj (Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, hxy.symm⟩, heq⟩)
          · simpa only [Function.update_of_ne hxv, Function.update_of_ne hyv] using
              hc x (Finset.mem_erase.mpr ⟨hxv, hx⟩) y (Finset.mem_erase.mpr ⟨hyv, hy⟩) hxy
      · refine ⟨fun _ => ⟨0, hk⟩, ?_⟩
        intro x hx
        exact (hS ⟨x, hx⟩).elim
  obtain ⟨c, hc⟩ := hcolor Finset.univ
  exact ⟨SimpleGraph.Coloring.mk c fun {x y} hxy =>
    hc x (Finset.mem_univ x) y (Finset.mem_univ y) hxy⟩

theorem colorable_of_partition {V : Type*} {H : SimpleGraph V} (S : Set V) {a b : ℕ}
    (hS : (H.induce S).Colorable a) (hR : (H.induce Sᶜ).Colorable b) :
    H.Colorable (a + b) := by
  classical
  obtain ⟨cS⟩ := hS
  obtain ⟨cR⟩ := hR
  let c : V → Fin a ⊕ Fin b := fun v =>
    if hv : v ∈ S then Sum.inl (cS ⟨v, hv⟩) else Sum.inr (cR ⟨v, hv⟩)
  have hc : ∀ {x y}, H.Adj x y → c x ≠ c y := by
    intro x y hxy
    dsimp [c]
    split_ifs with hx hy hy
    · exact fun heq => cS.valid (v := ⟨x, hx⟩) (w := ⟨y, hy⟩) hxy (Sum.inl.inj heq)
    · exact id
    · exact id
    · exact fun heq => cR.valid (v := ⟨x, hx⟩) (w := ⟨y, hy⟩) hxy (Sum.inr.inj heq)
  simpa using (SimpleGraph.Coloring.mk c hc).colorable

section ArcColorBound

variable {V : Type u} [LinearOrder V] [Fintype V] {F : SimpleGraph V}

/-- The residual arc vertices can be greedily colored with two colors. -/
theorem nonbranching_colorable {H : SimpleGraph (Arc F)} (hH : H ≤ arcGraph F) :
    (H.induce {a | ¬ Branching H a}).Colorable 2 := by
  classical
  apply colorable_of_low_degree _ (by decide)
  intro S hS
  obtain ⟨a, ha, hmin⟩ := S.exists_min_image (fun a => a.1.1.1) hS
  refine ⟨a, ha, ?_⟩
  have hforward : ∀ b ∈ S, H.Adj a.1 b.1 → a.1.1.2 = b.1.1.1 := by
    intro b hb hab
    rcases hH hab with hab | hba
    · exact hab
    · have hlt := b.1.2.1
      rw [hba] at hlt
      exact ((not_lt_of_ge (hmin b hb)) hlt).elim
  have hcard : (S.filter (fun b => H.Adj a.1 b.1)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro b hb c hc
    obtain ⟨hbS, hab⟩ := Finset.mem_filter.mp hb
    obtain ⟨hcS, hac⟩ := Finset.mem_filter.mp hc
    by_contra hbc
    exact a.2 ⟨b.1, c.1, (fun heq => hbc (Subtype.ext heq)), hab, hac,
      hforward b hbS hab, hforward c hcS hac⟩
  exact Nat.lt_succ_of_le hcard

/-- Lemma 1 of the attachment, for arbitrary spanning edge selections. -/
theorem arc_colorable_bound {d a : ℕ}
    (hout : ∀ v, (outgoingArcs F v).card ≤ d)
    (hbase : ∀ J : SimpleGraph V, J ≤ F →
      (∀ v, Nat.card (J.neighborSet v) ≤ d + d.choose 2) → J.Colorable a)
    {H : SimpleGraph (Arc F)} (hH : H ≤ arcGraph F) (h4 : FourCycleFree H) :
    H.Colorable (a + 2) := by
  apply colorable_of_partition {b | Branching H b}
  · apply branching_colorable hH
    apply hbase _ (baseOfArcs_le _)
    intro v
    exact (selected_degree_le h4 v).trans
      (Nat.add_le_add (hout v) (Nat.choose_le_choose 2 (hout v)))
  · exact nonbranching_colorable hH

end ArcColorBound

theorem FourCycleFree.spanningCoe {V : Type*} {G : SimpleGraph V} {H : G.Subgraph}
    (h : FourCycleFree H.coe) : FourCycleFree H.spanningCoe := by
  intro a b x y hab hxy hax hay hbx hby
  let a' : H.verts := ⟨a, H.edge_vert hax⟩
  let b' : H.verts := ⟨b, H.edge_vert hbx⟩
  let x' : H.verts := ⟨x, H.edge_vert (H.adj_symm hax)⟩
  let y' : H.verts := ⟨y, H.edge_vert (H.adj_symm hay)⟩
  exact h a' b' x' y' (fun heq => hab (congrArg Subtype.val heq))
    (fun heq => hxy (congrArg Subtype.val heq)) hax hay hbx hby

/-- The arc lemma applies to ordinary subgraphs, including vertex and edge deletion. -/
theorem arc_subgraph_colorable_bound {V : Type u} [LinearOrder V] [Fintype V]
    {F : SimpleGraph V} {d a : ℕ}
    (hout : ∀ v, (outgoingArcs F v).card ≤ d)
    (hbase : ∀ J : SimpleGraph V, J ≤ F →
      (∀ v, Nat.card (J.neighborSet v) ≤ d + d.choose 2) → J.Colorable a)
    (H : (arcGraph F).Subgraph) (h4 : FourCycleFree H.coe) :
    H.coe.Colorable (a + 2) :=
  (arc_colorable_bound hout hbase H.spanningCoe_le h4.spanningCoe).of_hom
    H.coeEmbeddingSpanningCoe.toHom

section EdgeCounting

variable {V : Type*}

/-- Ordered incidences from `X` to `Y`, counted as a real number. -/
noncomputable def crossingCount (G : SimpleGraph V) (X Y : Finset V) : ℝ := by
  classical
  exact ∑ x ∈ X, ∑ y ∈ Y, if G.Adj x y then 1 else 0

/-- The number of edges with both endpoints in `X`. -/
noncomputable def internalCount (G : SimpleGraph V) (X : Finset V) : ℝ :=
  crossingCount G X X / 2

theorem crossingCount_nonneg (G : SimpleGraph V) (X Y : Finset V) :
    0 ≤ crossingCount G X Y := by
  classical
  unfold crossingCount
  positivity

theorem crossingCount_comm (G : SimpleGraph V) (X Y : Finset V) :
    crossingCount G X Y = crossingCount G Y X := by
  classical
  unfold crossingCount
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro x hx
  rw [G.adj_comm]

theorem crossingCount_union_left [DecidableEq V] (G : SimpleGraph V) {X Y : Finset V}
    (hd : Disjoint X Y) (Z : Finset V) :
    crossingCount G (X ∪ Y) Z = crossingCount G X Z + crossingCount G Y Z := by
  classical
  exact Finset.sum_union hd

theorem crossingCount_union_right [DecidableEq V] (G : SimpleGraph V) (X : Finset V) {Y Z : Finset V}
    (hd : Disjoint Y Z) :
    crossingCount G X (Y ∪ Z) = crossingCount G X Y + crossingCount G X Z := by
  rw [crossingCount_comm G X, crossingCount_union_left G hd,
    crossingCount_comm G Y, crossingCount_comm G Z]

theorem crossingCount_graph_mono {F G : SimpleGraph V} (h : F ≤ G) (X Y : Finset V) :
    crossingCount F X Y ≤ crossingCount G X Y := by
  classical
  apply Finset.sum_le_sum
  intro x hx
  apply Finset.sum_le_sum
  intro y hy
  by_cases hxy : F.Adj x y
  · simp [hxy, h hxy]
  · simp only [hxy, if_false]
    positivity

theorem crossingCount_eq_sum_card (G : SimpleGraph V) (X Y : Finset V)
    [DecidableRel G.Adj] :
    crossingCount G X Y = ∑ x ∈ X, ((Y.filter (G.Adj x)).card : ℝ) := by
  classical
  simp only [crossingCount, Finset.card_filter, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  split_ifs <;> rfl

theorem crossingCount_eq_card_product (G : SimpleGraph V) (X Y : Finset V)
    [DecidableRel G.Adj] : crossingCount G X Y =
      (((X ×ˢ Y).filter (fun e => G.Adj e.1 e.2)).card : ℝ) := by
  classical
  simp only [crossingCount, Finset.card_filter, Finset.sum_product, Nat.cast_sum,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  split_ifs <;> rfl

theorem crossingCount_le_card_mul (G : SimpleGraph V) (X Y : Finset V)
    [DecidableRel G.Adj] {k : ℕ}
    (h : ∀ x ∈ X, (Y.filter (G.Adj x)).card ≤ k) :
    crossingCount G X Y ≤ X.card * k := by
  rw [crossingCount_eq_sum_card]
  calc
    _ ≤ ∑ _x ∈ X, (k : ℝ) := Finset.sum_le_sum fun x hx => by exact_mod_cast h x hx
    _ = _ := by simp

theorem crossingCount_eq_zero (G : SimpleGraph V) (X Y : Finset V)
    (h : ∀ x ∈ X, ∀ y ∈ Y, ¬ G.Adj x y) : crossingCount G X Y = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro x hx
  apply Finset.sum_eq_zero
  intro y hy
  simp [h x hx y hy]

/-- Deleting all edges incident with `Z` costs at most its total incidence count. -/
theorem internalCount_cut [DecidableEq V] (G : SimpleGraph V) {X Y Z : Finset V}
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z)
    (hY : crossingCount G Y Y = 0) :
    internalCount G (X ∪ Y ∪ Z) ≤ internalCount G X + crossingCount G X Y +
      crossingCount G Z (X ∪ Y ∪ Z) := by
  have hXYZ : Disjoint (X ∪ Y) Z := Finset.disjoint_union_left.mpr ⟨hXZ, hYZ⟩
  unfold internalCount
  rw [crossingCount_union_left G hXYZ, crossingCount_union_left G hXY,
    crossingCount_union_right G X hXYZ, crossingCount_union_right G X hXY,
    crossingCount_union_right G Y hXYZ, crossingCount_union_right G Y hXY,
    crossingCount_union_right G Z hXYZ, crossingCount_union_right G Z hXY,
    crossingCount_comm G Y X, crossingCount_comm G Z X, crossingCount_comm G Z Y, hY]
  nlinarith [crossingCount_nonneg G Z Z]

end EdgeCounting

/-- The numerical core of the deterministic cut in Lemma 3. -/
theorem cut_density_inequality {K s x y z e f : ℝ}
    (hK : 4 ≤ K) (hs : 0 < s) (_hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x + y ≤ s)
    (hz : z < 2 * s / (16 * K * (K + 1)))
    (he : 2 * s ≤ e + f + K * z) (hfX : f ≤ x) (hfY : f ≤ K * y) :
    (1 + 1 / (2 * (K + 1))) * x < e := by
  have hK0 : 0 < K := by linarith
  have hK1 : 0 < K + 1 := by linarith
  have hden : 0 < 16 * K * (K + 1) := by positivity
  have hcross : (K + 1) * f ≤ K * s := by nlinarith
  have htail : (16 * K * (K + 1)) * z < 2 * s := by
    nlinarith [(lt_div_iff₀ hden).mp hz]
  have he' : (K + 1) * (2 * s) ≤ (K + 1) * (e + f + K * z) :=
    mul_le_mul_of_nonneg_left he (le_of_lt hK1)
  have hmain : 8 * (K + 1) * e > (8 * K + 15) * s := by nlinarith
  have hxs : x ≤ s := by linarith
  have htarget : (2 * (K + 1) + 1) * x < 2 * (K + 1) * e := by
    nlinarith [mul_nonneg (show 0 ≤ 2 * (K + 1) + 1 by positivity) (sub_nonneg.mpr hxs)]
  have hden2 : 0 < 2 * (K + 1) := by positivity
  have heq : (1 + 1 / (2 * (K + 1))) * x =
      ((2 * (K + 1) + 1) * x) / (2 * (K + 1)) := by field_simp
  rw [heq]
  exact (div_lt_iff₀ hden2).mpr (by nlinarith)

section DeterministicObstruction

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The partitions and density estimates used by the deterministic cut argument. -/
def SparseCutProperty (F : SimpleGraph V) (K : ℕ) : Prop :=
  ∀ S : Finset V, S.Nonempty → ∃ X Y Z : Finset V,
    S = X ∪ Y ∪ Z ∧ Disjoint X Y ∧ Disjoint X Z ∧ Disjoint Y Z ∧
    crossingCount F Y Y = 0 ∧ crossingCount F X Y ≤ X.card ∧
    (Z.card : ℝ) < 2 * S.card / (16 * K * (K + 1)) ∧
    internalCount F X ≤ (1 + 1 / (2 * (K + 1))) * X.card

omit [DecidableEq V] in
theorem filter_neighbors_card_le (J : SimpleGraph V) [DecidableRel J.Adj]
    (S : Finset V) (v : V) : (S.filter (J.Adj v)).card ≤ Nat.card (J.neighborSet v) := by
  classical
  rw [Nat.card_eq_fintype_card, SimpleGraph.card_neighborSet_eq_degree,
    ← SimpleGraph.card_neighborFinset_eq_degree]
  apply Finset.card_le_card
  intro w hw
  exact (J.mem_neighborFinset v w).mpr (Finset.mem_filter.mp hw).2

/-- Every bounded-degree subgraph of a graph with the sparse cuts is 4-colorable. -/
theorem colorable_four_of_sparse_cuts {F J : SimpleGraph V} {K : ℕ}
    (hK : 4 ≤ K) (hcuts : SparseCutProperty F K) (hJF : J ≤ F)
    (hdeg : ∀ v, Nat.card (J.neighborSet v) ≤ K) : J.Colorable 4 := by
  classical
  apply colorable_of_low_degree _ (by decide)
  intro S hS
  by_contra! hmin
  obtain ⟨X, Y, Z, hSXYZ, hXY, hXZ, hYZ, hFY, hFXY, hZ, hFX⟩ := hcuts S hS
  have hJY : crossingCount J Y Y = 0 :=
    le_antisymm ((crossingCount_graph_mono hJF Y Y).trans_eq hFY)
      (crossingCount_nonneg J Y Y)
  have hJS : 2 * (S.card : ℝ) ≤ internalCount J S := by
    have hsum : (4 : ℝ) * S.card ≤ crossingCount J S S := by
      rw [crossingCount_eq_sum_card]
      calc
        _ = ∑ _v ∈ S, (4 : ℝ) := by simp [mul_comm]
        _ ≤ _ := Finset.sum_le_sum fun v hv => by exact_mod_cast hmin v hv
    unfold internalCount
    linarith
  have hXYS : (X.card : ℝ) + Y.card ≤ S.card := by
    norm_cast
    rw [← Finset.card_union_of_disjoint hXY]
    apply Finset.card_le_card
    rw [hSXYZ]
    exact Finset.subset_union_left
  have hJXY : crossingCount J X Y ≤ X.card :=
    (crossingCount_graph_mono hJF X Y).trans hFXY
  have hJYX : crossingCount J X Y ≤ (K : ℝ) * Y.card := by
    rw [crossingCount_comm J X Y, mul_comm]
    apply crossingCount_le_card_mul
    intro v hv
    exact (filter_neighbors_card_le J X v).trans (hdeg v)
  have hJZS : crossingCount J Z S ≤ (K : ℝ) * Z.card := by
    rw [mul_comm]
    apply crossingCount_le_card_mul
    intro v hv
    exact (filter_neighbors_card_le J S v).trans (hdeg v)
  have hcut : internalCount J S ≤ internalCount J X + crossingCount J X Y +
      crossingCount J Z S := by
    rw [hSXYZ]
    exact internalCount_cut J hXY hXZ hYZ hJY
  have hbad := cut_density_inequality
    (K := (K : ℝ)) (s := (S.card : ℝ)) (x := (X.card : ℝ)) (y := (Y.card : ℝ))
    (z := (Z.card : ℝ)) (e := internalCount J X) (f := crossingCount J X Y)
    (by exact_mod_cast hK) (by exact_mod_cast Finset.card_pos.mpr hS)
    (by positivity) (by positivity) hXYS hZ (by linarith) hJXY hJYX
  have hJX : internalCount J X ≤ internalCount F X :=
    div_le_div_of_nonneg_right (crossingCount_graph_mono hJF X X) (by positivity)
  linarith

/- Local sparsity in earlier parts yields the cuts used in Lemma 3. -/
omit [Fintype V] in
theorem sparse_cuts_of_parts {F : SimpleGraph V} {C K A : ℕ}
    (part : V → Fin C) (n : Fin C → ℕ)
    (hsame : ∀ v w, part v = part w → ¬ F.Adj v w)
    (hone : ∀ v i, part v < i → ∀ w z, part w = i → part z = i →
      F.Adj v w → F.Adj v z → w = z)
    (hcut : ∀ S : Finset V, S.Nonempty → ∃ i : Fin C,
      S.card ≤ A * n i ∧
      ((S.filter (fun v => i < part v)).card : ℝ) <
        2 * S.card / (16 * K * (K + 1)))
    (hsparse : ∀ (i : Fin C) (X : Finset V), (∀ v ∈ X, part v < i) →
      X.card ≤ A * n i →
      internalCount F X ≤ (1 + 1 / (2 * (K + 1))) * X.card) :
    SparseCutProperty F K := by
  classical
  intro S hS
  obtain ⟨i, hsize, htail⟩ := hcut S hS
  let X := S.filter fun v => part v < i
  let Y := S.filter fun v => part v = i
  let Z := S.filter fun v => i < part v
  have hpartition : S = X ∪ Y ∪ Z := by
    ext v
    simp only [X, Y, Z, Finset.mem_union, Finset.mem_filter]
    have htri := lt_trichotomy (part v) i
    tauto
  have hXY : Disjoint X Y := by
    apply Finset.disjoint_left.mpr
    intro v hx hy
    have hx' := (Finset.mem_filter.mp hx).2
    have hy' := (Finset.mem_filter.mp hy).2
    omega
  have hXZ : Disjoint X Z := by
    apply Finset.disjoint_left.mpr
    intro v hx hz
    have hx' := (Finset.mem_filter.mp hx).2
    have hz' := (Finset.mem_filter.mp hz).2
    omega
  have hYZ : Disjoint Y Z := by
    apply Finset.disjoint_left.mpr
    intro v hy hz
    have hy' := (Finset.mem_filter.mp hy).2
    have hz' := (Finset.mem_filter.mp hz).2
    omega
  refine ⟨X, Y, Z, hpartition, hXY, hXZ, hYZ, ?_, ?_, htail, ?_⟩
  · apply crossingCount_eq_zero
    intro v hv w hw
    exact hsame v w ((Finset.mem_filter.mp hv).2.trans (Finset.mem_filter.mp hw).2.symm)
  · have hbound : crossingCount F X Y ≤ X.card * (1 : ℕ) := by
      apply crossingCount_le_card_mul
      intro v hv
      apply Finset.card_le_one.mpr
      intro w hw z hz
      have hw' := Finset.mem_filter.mp hw
      have hz' := Finset.mem_filter.mp hz
      exact hone v i (Finset.mem_filter.mp hv).2 w z
        (Finset.mem_filter.mp hw'.1).2 (Finset.mem_filter.mp hz'.1).2 hw'.2 hz'.2
    simpa using hbound
  · exact hsparse i X (fun v hv => (Finset.mem_filter.mp hv).2)
      (le_trans (Finset.card_filter_le _ _) hsize)

end DeterministicObstruction

section FiniteProbability

variable {Ω : Type*} [Fintype Ω]

/-- Uniform probability on a finite sample space, expressed by counting. -/
noncomputable def finiteProb (A : Set Ω) : ℝ := (A.ncard : ℝ) / Fintype.card Ω

theorem finiteProb_nonneg (A : Set Ω) : 0 ≤ finiteProb A := by
  unfold finiteProb
  positivity

theorem finiteProb_mono {A B : Set Ω} (h : A ⊆ B) : finiteProb A ≤ finiteProb B := by
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Set.ncard_mono h

theorem finiteProb_empty : finiteProb (∅ : Set Ω) = 0 := by simp [finiteProb]

theorem finiteProb_univ [Nonempty Ω] : finiteProb (Set.univ : Set Ω) = 1 := by
  simp [finiteProb, Fintype.card_ne_zero]

theorem finiteProb_union_le (A B : Set Ω) :
    finiteProb (A ∪ B) ≤ finiteProb A + finiteProb B := by
  unfold finiteProb
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Set.ncard_union_le A B

theorem finiteProb_biUnion_le {ι : Type*} (s : Finset ι) (A : ι → Set Ω) :
    finiteProb {ω | ∃ i ∈ s, ω ∈ A i} ≤ ∑ i ∈ s, finiteProb (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [finiteProb]
  | @insert i s hi ih =>
    have heq : {ω | ∃ j ∈ insert i s, ω ∈ A j} = A i ∪ {ω | ∃ j ∈ s, ω ∈ A j} := by
      ext ω
      simp
    rw [heq, Finset.sum_insert hi]
    exact (finiteProb_union_le _ _).trans (add_le_add le_rfl ih)

theorem exists_avoiding_of_finiteProb_lt_one [Nonempty Ω] (A B : Set Ω)
    (h : finiteProb A + finiteProb B < 1) : ∃ ω, ω ∉ A ∧ ω ∉ B := by
  by_contra! hbad
  have heq : A ∪ B = Set.univ := by
    ext ω
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    by_cases ha : ω ∈ A
    · exact Or.inl ha
    · exact Or.inr (hbad ω ha)
  have hu := finiteProb_union_le A B
  rw [heq, finiteProb_univ] at hu
  linarith

theorem finiteProb_box {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
    [∀ i, Fintype (α i)] (A : ∀ i, Set (α i)) :
    finiteProb {ω : ∀ i, α i | ∀ i, ω i ∈ A i} =
      ∏ i, ((A i).ncard : ℝ) / Fintype.card (α i) := by
  classical
  unfold finiteProb
  have hcard : {ω : ∀ i, α i | ∀ i, ω i ∈ A i}.ncard = ∏ i, (A i).ncard := by
    change Nat.card {ω : ∀ i, α i // ∀ i, ω i ∈ A i} = _
    rw [Nat.card_congr (Equiv.subtypePiEquivPi (β := α) (p := fun i x => x ∈ A i)),
      Nat.card_pi]
    rfl
  rw [hcard, Fintype.card_pi]
  simp only [Nat.cast_prod, Finset.prod_div_distrib]

theorem finiteProb_agreement {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
    [∀ i, Fintype (α i)] (ω₀ : ∀ i, α i) (s : Finset ι) :
    finiteProb {ω : ∀ i, α i | ∀ i ∈ s, ω i = ω₀ i} =
      ∏ i ∈ s, (1 / (Fintype.card (α i) : ℝ)) := by
  classical
  let : ∀ i, Nonempty (α i) := fun i => ⟨ω₀ i⟩
  let A : ∀ i, Set (α i) := fun i => if i ∈ s then {ω₀ i} else Set.univ
  have heq : {ω : ∀ i, α i | ∀ i ∈ s, ω i = ω₀ i} =
      {ω | ∀ i, ω i ∈ A i} := by
    ext ω
    simp [A]
  rw [heq, finiteProb_box]
  calc
    _ = ∏ i, if i ∈ s then (1 / (Fintype.card (α i) : ℝ)) else 1 := by
      apply Finset.prod_congr rfl
      intro i hi
      by_cases his : i ∈ s <;> simp [A, his, Fintype.card_ne_zero]
    _ = _ := Fintype.prod_ite_mem s _

theorem finiteProb_agreement_le {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
    [∀ i, Fintype (α i)] (ω₀ : ∀ i, α i) (s : Finset ι) {n : ℕ} (hn : 0 < n)
    (hcard : ∀ i ∈ s, n ≤ Fintype.card (α i)) :
    finiteProb {ω : ∀ i, α i | ∀ i ∈ s, ω i = ω₀ i} ≤ (1 / (n : ℝ)) ^ s.card := by
  rw [finiteProb_agreement]
  calc
    _ ≤ ∏ _i ∈ s, (1 / (n : ℝ)) := by
      apply Finset.prod_le_prod (fun _ _ => by positivity)
      intro i hi
      exact one_div_le_one_div_of_le (by exact_mod_cast hn) (by exact_mod_cast hcard i hi)
    _ = _ := by simp

theorem finiteProb_card_ge_le {ε : Type*} [DecidableEq ε]
    (P : Finset ε) (present : Ω → Finset ε) (hP : ∀ ω, present ω ⊆ P)
    (m : ℕ) (B : ℝ)
    (hB : ∀ E ∈ P.powersetCard m, finiteProb {ω | E ⊆ present ω} ≤ B) :
    finiteProb {ω | m ≤ (present ω).card} ≤ (P.card.choose m : ℝ) * B := by
  classical
  have hsub : {ω | m ≤ (present ω).card} ⊆
      {ω | ∃ E ∈ P.powersetCard m, E ⊆ present ω} := by
    intro ω hω
    obtain ⟨E, hE, hEm⟩ := Finset.exists_subset_card_eq hω
    exact ⟨E, Finset.mem_powersetCard.mpr ⟨hE.trans (hP ω), hEm⟩, hE⟩
  calc
    _ ≤ finiteProb {ω | ∃ E ∈ P.powersetCard m, E ⊆ present ω} := finiteProb_mono hsub
    _ ≤ ∑ E ∈ P.powersetCard m, finiteProb {ω | E ⊆ present ω} := finiteProb_biUnion_le _ _
    _ ≤ ∑ _E ∈ P.powersetCard m, B := Finset.sum_le_sum hB
    _ = _ := by simp

end FiniteProbability

section MultipartiteModel

variable {C : ℕ}

/-- Vertices in ordered parts of the specified sizes. -/
abbrev ModelVertex (n : Fin C → ℕ) := Lex (Σ i : Fin C, Fin (n i))

/-- Unused choices into earlier parts are retained to make a rectangular product. -/
abbrev ModelSample (n : Fin C → ℕ) := (k : ModelVertex n × Fin C) → Fin (n k.2)

/-- Each vertex chooses exactly one neighbor in each later part. -/
def modelGraph {n : Fin C → ℕ} (ω : ModelSample n) : SimpleGraph (ModelVertex n) where
  Adj v w := (v.1 < w.1 ∧ ω (v, w.1) = w.2) ∨ (w.1 < v.1 ∧ ω (w, v.1) = v.2)
  symm := ⟨fun _ _ => Or.symm⟩
  loopless := ⟨fun v h => h.elim (fun h => (lt_irrefl v.1) h.1) (fun h => (lt_irrefl v.1) h.1)⟩

theorem modelGraph_same_part {n : Fin C → ℕ} (ω : ModelSample n)
    (v w : ModelVertex n) (hvw : v.1 = w.1) : ¬ (modelGraph ω).Adj v w := by
  rintro (h | h) <;> have hlt := h.1 <;> rw [hvw] at hlt <;> exact (lt_irrefl _) hlt

theorem modelGraph_forward {n : Fin C → ℕ} (ω : ModelSample n)
    {v w : ModelVertex n} (hvw : v.1 < w.1) :
    (modelGraph ω).Adj v w ↔ ω (v, w.1) = w.2 := by
  constructor
  · rintro (h | h)
    · exact h.2
    · exact (hvw.not_gt h.1).elim
  · exact fun h => Or.inl ⟨hvw, h⟩

theorem modelGraph_one_neighbor {n : Fin C → ℕ} (ω : ModelSample n)
    (v : ModelVertex n) (i : Fin C) (hvi : v.1 < i)
    (w z : ModelVertex n) (hwi : w.1 = i) (hzi : z.1 = i)
    (hvw : (modelGraph ω).Adj v w) (hvz : (modelGraph ω).Adj v z) : w = z := by
  obtain ⟨j, w⟩ := w
  obtain ⟨k, z⟩ := z
  dsimp at hwi hzi
  subst j
  subst k
  have hw := (modelGraph_forward ω hvi).mp hvw
  have hz := (modelGraph_forward ω hvi).mp hvz
  exact congrArg (fun x : Fin (n i) => (⟨i, x⟩ : ModelVertex n)) (hw.symm.trans hz)

theorem model_arc_forward {n : Fin C → ℕ} (ω : ModelSample n) (a : Arc (modelGraph ω)) :
    a.1.1.1 < a.1.2.1 := by
  rcases a.2.2 with h | h
  · exact h.1
  · rcases Sigma.Lex.lt_def.mp a.2.1 with hlt | ⟨heq, _⟩
    · exact (hlt.not_gt h.1).elim
    · have hlt := h.1
      rw [heq] at hlt
      exact (lt_irrefl _ hlt).elim

/-- The maximum outdegree depends only on the number of parts. -/
theorem model_outgoing_card_le {n : Fin C → ℕ} (ω : ModelSample n) (v : ModelVertex n) :
    (outgoingArcs (modelGraph ω) v).card ≤ C - 1 := by
  classical
  let S := outgoingArcs (modelGraph ω) v
  let f : Arc (modelGraph ω) → Fin C := fun a => a.1.2.1
  have hinj : Set.InjOn f (S : Set (Arc (modelGraph ω))) := by
    intro a ha b hb hab
    have hat : a.1.1 = v := (Finset.mem_filter.mp ha).2
    have hbt : b.1.1 = v := (Finset.mem_filter.mp hb).2
    apply Subtype.ext
    apply Prod.ext (hat.trans hbt.symm)
    have hav : (modelGraph ω).Adj v a.1.2 := by simpa only [hat] using a.2.2
    have hbv : (modelGraph ω).Adj v b.1.2 := by simpa only [hbt] using b.2.2
    have hvi : v.1 < a.1.2.1 := by simpa only [hat] using model_arc_forward ω a
    exact modelGraph_one_neighbor ω v a.1.2.1 hvi a.1.2 b.1.2 rfl hab.symm hav hbv
  have hsub : S.image f ⊆ (Finset.univ : Finset (Fin C)).erase v.1 := by
    intro j hj
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hj
    have hat : a.1.1 = v := (Finset.mem_filter.mp ha).2
    have hlt : v.1 < f a := by simpa only [f, hat] using model_arc_forward ω a
    exact Finset.mem_erase.mpr ⟨hlt.ne.symm, Finset.mem_univ _⟩
  calc
    S.card = (S.image f).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ ((Finset.univ : Finset (Fin C)).erase v.1).card := Finset.card_le_card hsub
    _ = C - 1 := by simp

/-- The probability of a specified set of distinct forward edges. -/
theorem model_contains_probability_le {n : Fin C → ℕ}
    (E : Finset (ModelVertex n × ModelVertex n))
    (hE : ∀ e ∈ E, e.1.1 < e.2.1) {N : ℕ} (hN : 0 < N)
    (hsize : ∀ e ∈ E, N ≤ n e.2.1) :
    finiteProb {ω : ModelSample n | ∀ e ∈ E, (modelGraph ω).Adj e.1 e.2} ≤
      (1 / (N : ℝ)) ^ E.card := by
  classical
  let A : Set (ModelSample n) := {ω | ∀ e ∈ E, (modelGraph ω).Adj e.1 e.2}
  by_cases hA : A.Nonempty
  · obtain ⟨ω₀, hω₀⟩ := hA
    let key : ModelVertex n × ModelVertex n → ModelVertex n × Fin C :=
      fun e => (e.1, e.2.1)
    have hinj : Set.InjOn key (E : Set (ModelVertex n × ModelVertex n)) := by
      intro a ha b hb hab
      have hs : a.1 = b.1 := congrArg (fun k : ModelVertex n × Fin C => k.1) hab
      have ht : a.2.1 = b.2.1 := congrArg (fun k : ModelVertex n × Fin C => k.2) hab
      apply Prod.ext hs
      apply modelGraph_one_neighbor ω₀ a.1 a.2.1 (hE a ha) a.2 b.2 rfl ht.symm
      · exact hω₀ a ha
      · simpa only [hs] using hω₀ b hb
    have hsub : A ⊆ {ω : ModelSample n | ∀ k ∈ E.image key, ω k = ω₀ k} := by
      intro ω hω k hk
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hk
      exact ((modelGraph_forward ω (hE e he)).mp (hω e he)).trans
        ((modelGraph_forward ω₀ (hE e he)).mp (hω₀ e he)).symm
    have hsz : ∀ k ∈ E.image key, N ≤ Fintype.card (Fin (n k.2)) := by
      intro k hk
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hk
      simpa using hsize e he
    have hb := (finiteProb_mono hsub).trans (finiteProb_agreement_le ω₀ (E.image key) hN hsz)
    simpa only [Finset.card_image_of_injOn hinj] using hb
  · have heq : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hA
    change finiteProb A ≤ _
    rw [heq, finiteProb_empty]
    positivity

noncomputable def possibleEdges {n : Fin C → ℕ} (X : Finset (ModelVertex n)) :
    Finset (ModelVertex n × ModelVertex n) := by
  classical
  exact (X ×ˢ X).filter fun e => e.1.1 < e.2.1

noncomputable def modelEdges {n : Fin C → ℕ} (ω : ModelSample n)
    (X : Finset (ModelVertex n)) : Finset (ModelVertex n × ModelVertex n) := by
  classical
  exact (possibleEdges X).filter fun e => (modelGraph ω).Adj e.1 e.2

/-- Each internal edge has precisely one orientation from an earlier to a later part. -/
theorem internalCount_modelGraph {n : Fin C → ℕ} (ω : ModelSample n)
    (X : Finset (ModelVertex n)) : internalCount (modelGraph ω) X = (modelEdges ω X).card := by
  classical
  let A := (X ×ˢ X).filter fun e => (modelGraph ω).Adj e.1 e.2
  let B := A.filter fun e => ¬ e.1.1 < e.2.1
  have hA : A.filter (fun e => e.1.1 < e.2.1) = modelEdges ω X := by
    ext e
    simp [A, modelEdges, possibleEdges, and_left_comm, and_comm]
  have hB : (modelEdges ω X).card = B.card := by
    apply Finset.card_bij (fun e _ => (e.2, e.1))
    · intro e he
      have he' : (e.1 ∈ X ∧ e.2 ∈ X) ∧ e.1.1 < e.2.1 ∧ (modelGraph ω).Adj e.1 e.2 := by
        simpa [modelEdges, possibleEdges, and_assoc] using he
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨he'.1.2, he'.1.1⟩,
        he'.2.2.symm⟩, ?_⟩
      exact he'.2.1.not_gt
    · intro a ha b hb hab
      exact Prod.ext (congrArg Prod.snd hab) (congrArg Prod.fst hab)
    · intro e he
      obtain ⟨heA, heback⟩ := Finset.mem_filter.mp he
      obtain ⟨heX, heAdj⟩ := Finset.mem_filter.mp heA
      have hedir : e.2.1 < e.1.1 := by
        rcases heAdj with h | h
        · exact (heback h.1).elim
        · exact h.1
      refine ⟨(e.2, e.1), ?_, rfl⟩
      have hx := Finset.mem_product.mp heX
      simp only [modelEdges, possibleEdges, Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨⟨hx.2, hx.1⟩, hedir⟩, heAdj.symm⟩
  have hc : (modelEdges ω X).card + (modelEdges ω X).card = A.card := by
    have h := Finset.card_filter_add_card_filter_not (s := A) (fun e => e.1.1 < e.2.1)
    rw [hA] at h
    change (modelEdges ω X).card + B.card = A.card at h
    rw [← hB] at h
    exact h
  rw [internalCount, crossingCount_eq_card_product]
  change (A.card : ℝ) / 2 = _
  have hcR : ((modelEdges ω X).card : ℝ) + (modelEdges ω X).card = A.card := by exact_mod_cast hc
  linarith

theorem model_many_edges_probability_le {n : Fin C → ℕ}
    (X : Finset (ModelVertex n)) (m : ℕ) {N : ℕ} (hN : 0 < N)
    (hsize : ∀ v ∈ X, N ≤ n v.1) :
    finiteProb {ω : ModelSample n | m ≤ (modelEdges ω X).card} ≤
      ((X.card ^ 2).choose m : ℝ) * (1 / (N : ℝ)) ^ m := by
  classical
  have hbound := finiteProb_card_ge_le (possibleEdges X) (fun ω : ModelSample n => modelEdges ω X)
    (fun _ => Finset.filter_subset _ _) m ((1 / (N : ℝ)) ^ m) (by
      intro E hE
      obtain ⟨hEP, hEm⟩ := Finset.mem_powersetCard.mp hE
      have hsub : {ω : ModelSample n | E ⊆ modelEdges ω X} ⊆
          {ω | ∀ e ∈ E, (modelGraph ω).Adj e.1 e.2} := by
        intro ω hω e he
        exact (Finset.mem_filter.mp (hω he)).2
      have hdir : ∀ e ∈ E, e.1.1 < e.2.1 := fun e he => (Finset.mem_filter.mp (hEP he)).2
      have hsz : ∀ e ∈ E, N ≤ n e.2.1 := by
        intro e he
        exact hsize e.2 (Finset.mem_product.mp (Finset.mem_filter.mp (hEP he)).1).2
      exact (finiteProb_mono hsub).trans (by
        simpa only [hEm] using model_contains_probability_le E hdir hN hsz))
  apply hbound.trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact_mod_cast Nat.choose_le_choose m (show (possibleEdges X).card ≤ X.card ^ 2 by
    calc
      _ ≤ (X ×ˢ X).card := Finset.card_filter_le _ _
      _ = _ := by simp [pow_two])

noncomputable def modelFiber {n : Fin C → ℕ} (I : Finset (ModelVertex n)) (i : Fin C) :
    Finset (Fin (n i)) := by
  classical
  exact Finset.univ.filter fun x => (⟨i, x⟩ : ModelVertex n) ∈ I

noncomputable def modelDensity {n : Fin C → ℕ} (I : Finset (ModelVertex n)) (i : Fin C) : ℝ :=
  ((modelFiber I i).card : ℝ) / n i

noncomputable def modelWeight {n : Fin C → ℕ} (I : Finset (ModelVertex n)) : ℝ :=
  ∑ i, modelDensity I i

theorem modelDensity_nonneg {n : Fin C → ℕ} (I : Finset (ModelVertex n)) (i : Fin C) :
    0 ≤ modelDensity I i := by unfold modelDensity; positivity

theorem modelDensity_le_one {n : Fin C → ℕ} (I : Finset (ModelVertex n)) (i : Fin C)
    (hn : 0 < n i) : modelDensity I i ≤ 1 := by
  classical
  apply (div_le_one₀ (by exact_mod_cast hn : (0 : ℝ) < n i)).mpr
  exact_mod_cast (show (modelFiber I i).card ≤ n i from
    (Finset.card_filter_le _ _).trans_eq (Fintype.card_fin (n i)))

noncomputable def modelColorClass {n : Fin C → ℕ} {k : ℕ}
    (c : ModelVertex n → Fin k) (a : Fin k) : Finset (ModelVertex n) := by
  classical
  exact @Finset.filter _ (fun v => c v = a) (fun _ => Classical.propDecidable _) Finset.univ

theorem mem_modelColorClass {n : Fin C → ℕ} {k : ℕ}
    (c : ModelVertex n → Fin k) (a : Fin k) (v : ModelVertex n) :
    v ∈ modelColorClass c a ↔ c v = a := by
  classical
  exact (@Finset.mem_filter (ModelVertex n) (fun v => c v = a)
    (fun _ => Classical.propDecidable _) Finset.univ v).trans
      (and_iff_right (Finset.mem_univ _))

/-- The weights of all color classes sum to the number of parts. -/
theorem modelWeight_color_sum {n : Fin C → ℕ} {k : ℕ}
    (hn : ∀ i, 0 < n i) (c : ModelVertex n → Fin k) :
    (∑ a : Fin k, modelWeight (modelColorClass c a)) = C := by
  classical
  unfold modelWeight modelDensity
  rw [Finset.sum_comm]
  calc
    _ = ∑ _i : Fin C, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hcount : (∑ a : Fin k, (modelFiber (modelColorClass c a) i).card) = n i := by
        have hfiber : ∀ a : Fin k, modelFiber (modelColorClass c a) i =
            Finset.univ.filter (fun x : Fin (n i) => c (⟨i, x⟩ : ModelVertex n) = a) := by
          intro a
          ext x
          simp only [modelFiber, Finset.mem_filter, Finset.mem_univ, true_and]
          exact mem_modelColorClass c a (⟨i, x⟩ : ModelVertex n)
        simp_rw [hfiber]
        simpa using
          (Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset (Fin (n i)))
            (Finset.univ : Finset (Fin k)) (fun x => c (⟨i, x⟩ : ModelVertex n)))
      rw [← Finset.sum_div]
      have hcountR : (∑ a : Fin k, ((modelFiber (modelColorClass c a) i).card : ℝ)) =
          n i := by exact_mod_cast hcount
      rw [hcountR]
      exact div_self (by exact_mod_cast Nat.ne_of_gt (hn i))
    _ = _ := by simp

/-- Small independent-set weights force a large chromatic number. -/
theorem model_not_colorable_of_independent_weights {n : Fin C → ℕ} {k : ℕ}
    (hn : ∀ i, 0 < n i) (hk : 0 < k) (ω : ModelSample n)
    (hsmall : ∀ I : Finset (ModelVertex n),
      (∀ v ∈ I, ∀ w ∈ I, ¬ (modelGraph ω).Adj v w) → modelWeight I < (C : ℝ) / k) :
    ¬ (modelGraph ω).Colorable k := by
  classical
  let : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  rintro ⟨c⟩
  have hclasses : ∀ a : Fin k, modelWeight (modelColorClass c a) < (C : ℝ) / k := by
    intro a
    apply hsmall
    intro v hv w hw hvw
    exact c.valid hvw (((mem_modelColorClass c a v).mp hv).trans
      ((mem_modelColorClass c a w).mp hw).symm)
  have hsum : (∑ a : Fin k, modelWeight (modelColorClass c a)) <
      ∑ _a : Fin k, (C : ℝ) / k :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun a _ => hclasses a)
  rw [modelWeight_color_sum hn c] at hsum
  have heq : (∑ _a : Fin k, (C : ℝ) / k) = C := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  linarith

/-- Counting a fiber as vertices or as coordinates gives the same cardinality. -/
theorem modelFiber_card {n : Fin C → ℕ} (I : Finset (ModelVertex n)) (i : Fin C) :
    (modelFiber I i).card = (I.filter (fun v => v.1 = i)).card := by
  classical
  apply Finset.card_bij (fun x _ => (⟨i, x⟩ : ModelVertex n))
  · intro x hx
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).2, rfl⟩
  · intro x hx y hy heq
    cases heq
    rfl
  · intro v hv
    obtain ⟨j, x⟩ := v
    obtain ⟨hvI, hji⟩ := Finset.mem_filter.mp hv
    dsimp at hji
    subst j
    exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvI⟩, rfl⟩

noncomputable def modelLaterWeight {n : Fin C → ℕ}
    (I : Finset (ModelVertex n)) (i : Fin C) : ℝ :=
  ∑ j : Fin C, if i < j then modelDensity I j else 0

theorem modelLaterWeight_nonneg {n : Fin C → ℕ}
    (I : Finset (ModelVertex n)) (i : Fin C) : 0 ≤ modelLaterWeight I i := by
  apply Finset.sum_nonneg
  intro j hj
  split_ifs <;> first | exact modelDensity_nonneg _ _ | rfl

/-- Choices from one fiber already give an exponential bound for independence. -/
theorem model_independent_probability_le {n : Fin C → ℕ} (hn : ∀ j, 0 < n j)
    (I : Finset (ModelVertex n)) (i : Fin C) :
    finiteProb {ω : ModelSample n | ∀ v ∈ I, ∀ w ∈ I, ¬ (modelGraph ω).Adj v w} ≤
      Real.exp (-((modelFiber I i).card : ℝ) * modelLaterWeight I i) := by
  classical
  let S := I.filter (fun v => v.1 = i)
  let A : ∀ k : ModelVertex n × Fin C, Set (Fin (n k.2)) := fun k =>
    if k.1 ∈ S ∧ i < k.2 then (↑(modelFiber I k.2) : Set (Fin (n k.2)))ᶜ else Set.univ
  let e : ModelVertex n × Fin C → ℝ := fun k =>
    if k.1 ∈ S then if i < k.2 then -modelDensity I k.2 else 0 else 0
  have hsub : {ω : ModelSample n | ∀ v ∈ I, ∀ w ∈ I, ¬ (modelGraph ω).Adj v w} ⊆
      {ω | ∀ k, ω k ∈ A k} := by
    intro ω hω k
    by_cases hk : k.1 ∈ S ∧ i < k.2
    · simp only [A, if_pos hk, Set.mem_compl_iff, Finset.mem_coe]
      intro hx
      have hsource := Finset.mem_filter.mp hk.1
      have htarget : (⟨k.2, ω k⟩ : ModelVertex n) ∈ I := (Finset.mem_filter.mp hx).2
      apply hω k.1 hsource.1 (⟨k.2, ω k⟩ : ModelVertex n) htarget
      apply Or.inl
      exact ⟨by simpa only [hsource.2] using hk.2, rfl⟩
    · simp only [A, if_neg hk, Set.mem_univ]
  have hfactor : ∀ k : ModelVertex n × Fin C,
      ((A k).ncard : ℝ) / Fintype.card (Fin (n k.2)) ≤ Real.exp (e k) := by
    intro k
    have hnR : (0 : ℝ) < n k.2 := by exact_mod_cast hn k.2
    by_cases hs : k.1 ∈ S
    · by_cases hj : i < k.2
      · have hc : (modelFiber I k.2).card ≤ n k.2 :=
          (Finset.card_filter_le _ _).trans_eq (Fintype.card_fin _)
        have heq : ((A k).ncard : ℝ) / Fintype.card (Fin (n k.2)) =
            1 - modelDensity I k.2 := by
          simp only [A, if_pos (And.intro hs hj)]
          rw [Set.ncard_compl (↑(modelFiber I k.2) : Set (Fin (n k.2)))]
          simp only [Nat.card_eq_fintype_card,
            Fintype.card_fin, Set.ncard_coe_finset, Nat.cast_sub hc, modelDensity]
          field_simp
        rw [heq]
        have hb := Real.add_one_le_exp (-modelDensity I k.2)
        simpa only [e, if_pos hs, if_pos hj, sub_eq_add_neg, add_comm] using hb
      · simp [A, e, hs, hj, Set.ncard_univ, Nat.card_eq_fintype_card, hnR.ne']
    · simp [A, e, hs, Set.ncard_univ, Nat.card_eq_fintype_card, hnR.ne']
  have hexponent : (∑ k, e k) = -((modelFiber I i).card : ℝ) * modelLaterWeight I i := by
    rw [Fintype.sum_prod_type]
    calc
      _ = ∑ v : ModelVertex n, if v ∈ S then -modelLaterWeight I i else 0 := by
        apply Finset.sum_congr rfl
        intro v hv
        by_cases hs : v ∈ S
        · simp only [e, if_pos hs, modelLaterWeight, ← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro j hj
          split_ifs <;> simp
        · simp only [e, if_neg hs, Finset.sum_const_zero]
      _ = (S.card : ℝ) * (-modelLaterWeight I i) := by
        rw [Fintype.sum_ite_mem]
        simp
      _ = _ := by rw [modelFiber_card]; ring
  calc
    _ ≤ finiteProb {ω : ModelSample n | ∀ k, ω k ∈ A k} := finiteProb_mono hsub
    _ = ∏ k, ((A k).ncard : ℝ) / Fintype.card (Fin (n k.2)) := finiteProb_box A
    _ ≤ ∏ k, Real.exp (e k) := Finset.prod_le_prod (fun _ _ => by positivity) (fun k _ => hfactor k)
    _ = Real.exp (∑ k, e k) := (Real.exp_sum _ _).symm
    _ = _ := by rw [hexponent]

end MultipartiteModel

/-- The first substantial coordinate leaves a substantial sum to its right. -/
theorem exists_heavy_coordinate {C : ℕ} (hC : 0 < C) (p : Fin C → ℝ) {θ : ℝ}
    (hθ : 0 < θ) (hp : ∀ i, p i ≤ 1) (hsum : 2 * C * θ ≤ ∑ i, p i) :
    ∃ i : Fin C, θ ≤ p i ∧ (C : ℝ) * θ - 1 ≤ ∑ j : Fin C, if i < j then p j else 0 := by
  classical
  have hCR : (0 : ℝ) < C := by exact_mod_cast hC
  have hex : ∃ i : Fin C, θ ≤ p i := by
    by_contra! h
    have hb : (∑ i, p i) ≤ ∑ _i : Fin C, θ :=
      Finset.sum_le_sum (fun i _ => (h i).le)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hb
    nlinarith [mul_pos hCR hθ]
  let S := Finset.univ.filter (fun i : Fin C => θ ≤ p i)
  have hS : S.Nonempty := by
    obtain ⟨i, hi⟩ := hex
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  let i := S.min' hS
  have hi : θ ≤ p i := (Finset.mem_filter.mp (Finset.min'_mem S hS)).2
  refine ⟨i, hi, ?_⟩
  have hpoint : ∀ j : Fin C, p j ≤ θ + (if j = i then 1 else 0) +
      (if i < j then p j else 0) := by
    intro j
    rcases lt_trichotomy j i with hj | rfl | hj
    · have hjp : p j < θ := by
        by_contra! hbad
        have hji : i ≤ j := Finset.min'_le S j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbad⟩)
        exact (not_lt_of_ge hji) hj
      simp only [if_neg hj.ne, if_neg hj.not_gt, add_zero]
      exact hjp.le
    · simp only [eq_self, if_true, lt_self_iff_false, if_false, add_zero]
      linarith [hp i]
    · simp only [if_neg hj.ne.symm, if_pos hj, add_zero]
      linarith
  have hb := Finset.sum_le_sum (fun j (_hj : j ∈ (Finset.univ : Finset (Fin C))) => hpoint j)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at hb
  linarith

/-- A large independent-set weight has a fiber witnessing both required lower bounds. -/
theorem model_weight_heavy_part {q C : ℕ} (hq : 1 ≤ q) (hC : C = 64 * q ^ 2)
    {n : Fin C → ℕ} (hn : ∀ j, 0 < n j) (I : Finset (ModelVertex n))
    (hweight : (C : ℝ) / (2 * q) ≤ modelWeight I) :
    ∃ i : Fin C, 1 / (4 * (q : ℝ)) ≤ modelDensity I i ∧
      15 * (q : ℝ) ≤ modelLaterWeight I i := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hCpos : 0 < C := by rw [hC]; positivity
  have hsum : 2 * (C : ℝ) * (1 / (4 * q)) ≤ ∑ i, modelDensity I i := by
    have heq : 2 * (C : ℝ) * (1 / (4 * q)) = (C : ℝ) / (2 * q) := by ring
    rw [heq]
    exact hweight
  obtain ⟨i, hi, hright⟩ := exists_heavy_coordinate hCpos (modelDensity I)
    (by positivity) (fun j => modelDensity_le_one I j (hn j)) hsum
  refine ⟨i, hi, le_trans ?_ hright⟩
  have hq1R : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hCR : (C : ℝ) = 64 * (q : ℝ) ^ 2 := by exact_mod_cast hC
  rw [hCR]
  have heq : 64 * (q : ℝ) ^ 2 * (1 / (4 * q)) = 16 * q := by field_simp; ring
  rw [heq]
  linarith

noncomputable def modelSuffix {C : ℕ} (n : Fin C → ℕ) (i : Fin C) : Finset (ModelVertex n) := by
  classical
  exact Finset.univ.filter fun v => i ≤ v.1

noncomputable def modelRestrict {C : ℕ} {n : Fin C → ℕ}
    (I : Finset (ModelVertex n)) (i : Fin C) : Finset (ModelVertex n) := by
  classical
  exact I.filter fun v => i ≤ v.1

theorem mem_modelRestrict {C : ℕ} {n : Fin C → ℕ}
    (I : Finset (ModelVertex n)) (i : Fin C) (v : ModelVertex n) :
    v ∈ modelRestrict I i ↔ v ∈ I ∧ i ≤ v.1 := by
  classical
  exact Finset.mem_filter

theorem modelFiber_restrict {C : ℕ} {n : Fin C → ℕ}
    (I : Finset (ModelVertex n)) (i j : Fin C) (hij : i ≤ j) :
    modelFiber (modelRestrict I i) j = modelFiber I j := by
  classical
  ext x
  simp only [modelFiber, Finset.mem_filter, Finset.mem_univ, true_and]
  exact (mem_modelRestrict I i (⟨j, x⟩ : ModelVertex n)).trans (and_iff_left hij)

theorem modelLaterWeight_restrict {C : ℕ} {n : Fin C → ℕ}
    (I : Finset (ModelVertex n)) (i : Fin C) :
    modelLaterWeight (modelRestrict I i) i = modelLaterWeight I i := by
  unfold modelLaterWeight
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs with hij
  · simp only [modelDensity, modelFiber_restrict I i j hij.le]
  · rfl

/-- The exceptional independent sets can be searched for within a suffix. -/
def modelBadColor {C : ℕ} (n : Fin C → ℕ) (q : ℕ) : Set (ModelSample n) :=
  {ω | ∃ i : Fin C, ∃ I : Finset (ModelVertex n), I ⊆ modelSuffix n i ∧
    1 / (4 * (q : ℝ)) ≤ modelDensity I i ∧ 15 * (q : ℝ) ≤ modelLaterWeight I i ∧
      ∀ v ∈ I, ∀ w ∈ I, ¬ (modelGraph ω).Adj v w}

theorem model_small_weights_of_not_bad {q C : ℕ} (hq : 1 ≤ q) (hC : C = 64 * q ^ 2)
    {n : Fin C → ℕ} (hn : ∀ j, 0 < n j) (ω : ModelSample n)
    (hω : ω ∉ modelBadColor n q) (I : Finset (ModelVertex n))
    (hI : ∀ v ∈ I, ∀ w ∈ I, ¬ (modelGraph ω).Adj v w) :
    modelWeight I < (C : ℝ) / (2 * q) := by
  classical
  by_contra! hlarge
  obtain ⟨i, hi, hright⟩ := model_weight_heavy_part hq hC hn I hlarge
  apply hω
  refine ⟨i, modelRestrict I i, ?_, ?_, ?_, ?_⟩
  · intro v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ((mem_modelRestrict I i v).mp hv).2⟩
  · simpa only [modelDensity, modelFiber_restrict I i i le_rfl] using hi
  · simpa only [modelLaterWeight_restrict] using hright
  · intro v hv w hw
    exact hI v ((mem_modelRestrict I i v).mp hv).1 w ((mem_modelRestrict I i w).mp hw).1

theorem model_heavy_independent_probability_le {q C : ℕ} (hq : 0 < q)
    {n : Fin C → ℕ} (hn : ∀ j, 0 < n j) (I : Finset (ModelVertex n)) (i : Fin C)
    (hi : 1 / (4 * (q : ℝ)) ≤ modelDensity I i)
    (hright : 15 * (q : ℝ) ≤ modelLaterWeight I i) :
    finiteProb {ω : ModelSample n | ∀ v ∈ I, ∀ w ∈ I, ¬ (modelGraph ω).Adj v w} ≤
      Real.exp (-3 * (n i : ℝ)) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hnR : (0 : ℝ) < n i := by exact_mod_cast hn i
  have ht : (n i : ℝ) ≤ ((modelFiber I i).card : ℝ) * (4 * q) := by
    have hb := (div_le_div_iff₀ (show (0 : ℝ) < 4 * q by positivity) hnR).mp hi
    simpa only [one_mul] using hb
  have hprod := mul_le_mul_of_nonneg_left hright
    (show (0 : ℝ) ≤ (modelFiber I i).card by positivity)
  apply (model_independent_probability_le hn I i).trans
  apply Real.exp_le_exp.mpr
  nlinarith

/-- A union bound over all suffix sets and all possible first heavy parts. -/
theorem model_badColor_probability_le {q C : ℕ} (hq : 0 < q) (hC : 0 < C)
    {n : Fin C → ℕ} (hn : ∀ j, 0 < n j)
    (hsuffix : ∀ i, (modelSuffix n i).card ≤ 2 * n i)
    (hlarge : ∀ i, 8 * C ≤ n i) :
    finiteProb (modelBadColor n q) ≤ (1 : ℝ) / 8 := by
  classical
  let A : Fin C → Finset (ModelVertex n) → Set (ModelSample n) := fun i I =>
    {ω | 1 / (4 * (q : ℝ)) ≤ modelDensity I i ∧
      15 * (q : ℝ) ≤ modelLaterWeight I i ∧
      ∀ v ∈ I, ∀ w ∈ I, ¬ (modelGraph ω).Adj v w}
  have hfixed : ∀ i I, finiteProb (A i I) ≤ Real.exp (-3 * (n i : ℝ)) := by
    intro i I
    by_cases hi : 1 / (4 * (q : ℝ)) ≤ modelDensity I i
    · by_cases hr : 15 * (q : ℝ) ≤ modelLaterWeight I i
      · exact (finiteProb_mono (fun _ h => h.2.2)).trans
          (model_heavy_independent_probability_le hq hn I i hi hr)
      · have heq : A i I = ∅ := by ext ω; simp [A, hr]
        rw [heq, finiteProb_empty]
        exact Real.exp_nonneg _
    · have heq : A i I = ∅ := by
        ext ω
        exact ⟨fun h => (hi h.1).elim, fun h => h.elim⟩
      rw [heq, finiteProb_empty]
      exact Real.exp_nonneg _
  have hpart : ∀ i, finiteProb {ω | ∃ I ∈ (modelSuffix n i).powerset, ω ∈ A i I} ≤
      1 / (8 * (C : ℝ)) := by
    intro i
    have hnR : (0 : ℝ) < n i := by exact_mod_cast hn i
    have hCR : (0 : ℝ) < C := by exact_mod_cast hC
    calc
      _ ≤ ∑ I ∈ (modelSuffix n i).powerset, finiteProb (A i I) := finiteProb_biUnion_le _ _
      _ ≤ ∑ _I ∈ (modelSuffix n i).powerset, Real.exp (-3 * (n i : ℝ)) :=
        Finset.sum_le_sum (fun I _ => hfixed i I)
      _ = (2 : ℝ) ^ (modelSuffix n i).card * Real.exp (-3 * (n i : ℝ)) := by simp
      _ ≤ (2 : ℝ) ^ (2 * n i) * Real.exp (-3 * (n i : ℝ)) := by
        gcongr
        · norm_num
        · exact hsuffix i
      _ ≤ Real.exp (2 * (n i : ℝ)) * Real.exp (-3 * (n i : ℝ)) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
        calc
          _ ≤ Real.exp 1 ^ (2 * n i) :=
            pow_le_pow_left₀ (by norm_num) (by linarith [Real.add_one_le_exp (1 : ℝ)]) _
          _ = _ := by rw [← Real.exp_nat_mul]; norm_cast; simp
      _ = Real.exp (-(n i : ℝ)) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ 1 / (8 * (C : ℝ)) := by
        rw [Real.exp_neg, one_div]
        apply (inv_le_inv₀ (Real.exp_pos _) (by positivity)).mpr
        have hlargeR : 8 * (C : ℝ) ≤ n i := by exact_mod_cast hlarge i
        linarith [Real.add_one_le_exp (n i : ℝ)]
  have heq : modelBadColor n q =
      {ω | ∃ i ∈ (Finset.univ : Finset (Fin C)),
        ∃ I ∈ (modelSuffix n i).powerset, ω ∈ A i I} := by
    ext ω
    simp only [modelBadColor, A, Set.mem_ofPred_eq, Finset.mem_univ, true_and, Finset.mem_powerset]
  calc
    _ = finiteProb {ω | ∃ i ∈ (Finset.univ : Finset (Fin C)),
        ∃ I ∈ (modelSuffix n i).powerset, ω ∈ A i I} := congrArg finiteProb heq
    _ ≤ ∑ i : Fin C, finiteProb {ω | ∃ I ∈ (modelSuffix n i).powerset, ω ∈ A i I} :=
      finiteProb_biUnion_le _ _
    _ ≤ ∑ _i : Fin C, 1 / (8 * (C : ℝ)) := Finset.sum_le_sum (fun i _ => hpart i)
    _ = 1 / 8 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp

/-- A convenient binomial estimate avoiding logarithms in the probability bounds. -/
theorem choose_le_three_mul_div_pow (N k : ℕ) (hk : 0 < k) :
    (N.choose k : ℝ) ≤ (3 * N / k) ^ k := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hfact : (k : ℝ) ^ k / k.factorial ≤ (3 : ℝ) ^ k := by
    calc
      _ ≤ Real.exp k := Real.pow_div_factorial_le_exp (k : ℝ) (by positivity) k
      _ = Real.exp 1 ^ k := by simp [Real.exp_nat_mul]
      _ ≤ _ := pow_le_pow_left₀ (Real.exp_nonneg _) Real.exp_one_lt_three.le _
  have hchoose := (Nat.choose_le_pow_div k N : (N.choose k : ℝ) ≤ (N : ℝ) ^ k / k.factorial)
  have hm := mul_le_mul_of_nonneg_left hfact (show 0 ≤ (N : ℝ) ^ k by positivity)
  have heq : (3 * (N : ℝ) / k) ^ k = (3 : ℝ) ^ k * (N : ℝ) ^ k / (k : ℝ) ^ k := by
    rw [div_pow, mul_pow]
  rw [heq]
  apply (le_div_iff₀ (pow_pos hkR _)).mpr
  have hc := mul_le_mul_of_nonneg_right hchoose (le_of_lt (pow_pos hkR k))
  have he : (N : ℝ) ^ k / k.factorial * (k : ℝ) ^ k =
      (N : ℝ) ^ k * ((k : ℝ) ^ k / k.factorial) := by ring
  rw [he] at hc
  exact hc.trans (by simpa only [mul_comm] using hm)

/-- Taking an integer power avoids fractional exponents in the sparse-set estimate. -/
theorem sparse_product_power_bound {a b δ : ℝ} {D x m : ℕ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hb1 : b ≤ 1) (hδ : 0 ≤ δ) (hD : 0 < D)
    (hm : (D + 1) * x ≤ m * D) (hcoef : a ^ D * b ^ (D + 1) ≤ δ ^ D) :
    a ^ x * b ^ m ≤ δ ^ x := by
  apply le_of_pow_le_pow_left₀ (Nat.ne_of_gt hD) (pow_nonneg hδ x)
  calc
    (a ^ x * b ^ m) ^ D = (a ^ D) ^ x * b ^ (m * D) := by
      simp only [mul_pow, ← pow_mul, Nat.mul_comm]
    _ ≤ (a ^ D) ^ x * b ^ ((D + 1) * x) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hb hb1 hm) (by positivity)
    _ = (a ^ D * b ^ (D + 1)) ^ x := by simp only [mul_pow, pow_mul]
    _ ≤ (δ ^ D) ^ x := pow_le_pow_left₀ (by positivity) hcoef x
    _ = (δ ^ x) ^ D := by simp only [← pow_mul, Nat.mul_comm]

theorem sparse_binomial_bound {N L x m D : ℕ} {δ : ℝ}
    (hx : 0 < x) (hxm : x ≤ m) (hD : 0 < D) (hm : (D + 1) * x ≤ m * D)
    (hL : 3 * x ≤ L) (hδ : 0 ≤ δ)
    (hcoef : (3 : ℝ) ^ (2 * D + 1) * (N : ℝ) ^ D * x / (L : ℝ) ^ (D + 1) ≤ δ ^ D) :
    (N.choose x : ℝ) * ((x ^ 2).choose m : ℝ) * (1 / (L : ℝ)) ^ m ≤ δ ^ x := by
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  have hmR : (0 : ℝ) < m := by exact_mod_cast lt_of_lt_of_le hx hxm
  have hLR : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hxmR : (x : ℝ) ≤ m := by exact_mod_cast hxm
  have hLR' : 3 * (x : ℝ) ≤ L := by exact_mod_cast hL
  let a : ℝ := 3 * N / x
  let b : ℝ := 3 * x / L
  have hchoose₁ : (N.choose x : ℝ) ≤ a ^ x := choose_le_three_mul_div_pow N x hx
  have hchoose₂ : ((x ^ 2).choose m : ℝ) ≤ (3 * (x : ℝ)) ^ m := by
    apply (choose_le_three_mul_div_pow (x ^ 2) m (by omega)).trans
    apply pow_le_pow_left₀ (by positivity)
    apply (div_le_iff₀ hmR).mpr
    push_cast
    nlinarith
  have hpow : a ^ D * b ^ (D + 1) ≤ δ ^ D := by
    have heq : a ^ D * b ^ (D + 1) =
        (3 : ℝ) ^ (2 * D + 1) * (N : ℝ) ^ D * x / (L : ℝ) ^ (D + 1) := by
      dsimp [a, b]
      rw [show 2 * D + 1 = D + (D + 1) by omega, pow_add]
      simp only [div_pow, mul_pow, pow_succ]
      field_simp
      ring
    rw [heq]
    exact hcoef
  calc
    _ ≤ a ^ x * (3 * (x : ℝ)) ^ m * (1 / (L : ℝ)) ^ m := by gcongr
    _ = a ^ x * b ^ m := by
      rw [mul_assoc, ← mul_pow]
      congr 1
      dsimp [b]
      congr 1
      ring
    _ ≤ _ := sparse_product_power_bound (by dsimp [a]; positivity) (by dsimp [b]; positivity)
      ((div_le_one₀ hLR).mpr hLR') hδ hD hm hpow

/-- A union bound over all vertex sets of one specified size. -/
theorem model_fixed_size_density_probability_le {C : ℕ} {n : Fin C → ℕ}
    (P : Finset (ModelVertex n)) {x D L N : ℕ} {δ : ℝ}
    (hx : 0 < x) (hD : 0 < D) (hL : 3 * x ≤ L) (hδ : 0 ≤ δ)
    (hP : P.card ≤ N) (hsize : ∀ v ∈ P, L ≤ n v.1)
    (hcoef : (3 : ℝ) ^ (2 * D + 1) * (N : ℝ) ^ D * x / (L : ℝ) ^ (D + 1) ≤ δ ^ D) :
    finiteProb {ω : ModelSample n | ∃ X : Finset (ModelVertex n),
      X ⊆ P ∧ X.card = x ∧ (D + 1) * x ≤ (modelEdges ω X).card * D} ≤ δ ^ x := by
  classical
  have hmex : ∃ m : ℕ, (D + 1) * x ≤ m * D :=
    ⟨(D + 1) * x, Nat.le_mul_of_pos_right _ hD⟩
  let m := Nat.find hmex
  have hm : (D + 1) * x ≤ m * D := Nat.find_spec hmex
  have hxm : x ≤ m := by nlinarith
  have hLpos : 0 < L := by omega
  have hsub : {ω : ModelSample n | ∃ X : Finset (ModelVertex n),
      X ⊆ P ∧ X.card = x ∧ (D + 1) * x ≤ (modelEdges ω X).card * D} ⊆
      {ω | ∃ X ∈ P.powersetCard x, m ≤ (modelEdges ω X).card} := by
    intro ω hω
    obtain ⟨X, hXP, hXx, hX⟩ := hω
    exact ⟨X, Finset.mem_powersetCard.mpr ⟨hXP, hXx⟩, Nat.find_min' hmex hX⟩
  have hb : ∀ X ∈ P.powersetCard x,
      finiteProb {ω : ModelSample n | m ≤ (modelEdges ω X).card} ≤
        ((x ^ 2).choose m : ℝ) * (1 / (L : ℝ)) ^ m := by
    intro X hX
    obtain ⟨hXP, hXx⟩ := Finset.mem_powersetCard.mp hX
    simpa only [hXx] using model_many_edges_probability_le X m hLpos
      (fun v hv => hsize v (hXP hv))
  calc
    _ ≤ finiteProb {ω : ModelSample n | ∃ X ∈ P.powersetCard x, m ≤ (modelEdges ω X).card} :=
      finiteProb_mono hsub
    _ ≤ ∑ X ∈ P.powersetCard x, finiteProb {ω : ModelSample n | m ≤ (modelEdges ω X).card} :=
      finiteProb_biUnion_le _ _
    _ ≤ ∑ _X ∈ P.powersetCard x, ((x ^ 2).choose m : ℝ) * (1 / (L : ℝ)) ^ m :=
      Finset.sum_le_sum hb
    _ = (P.card.choose x : ℝ) * ((x ^ 2).choose m : ℝ) * (1 / (L : ℝ)) ^ m := by
      simp [mul_assoc]
    _ ≤ (N.choose x : ℝ) * ((x ^ 2).choose m : ℝ) * (1 / (L : ℝ)) ^ m := by
      gcongr
    _ ≤ _ := sparse_binomial_bound hx hxm hD hm hL hδ hcoef

noncomputable def modelBefore {C : ℕ} (n : Fin C → ℕ) (i : Fin C) : Finset (ModelVertex n) := by
  classical
  exact Finset.univ.filter fun v => v.1 < i

def modelBadSparse {C : ℕ} (n : Fin C → ℕ) (A D : ℕ) : Set (ModelSample n) :=
  {ω | ∃ i : Fin C, ∃ X : Finset (ModelVertex n), X ⊆ modelBefore n i ∧
    X.Nonempty ∧ X.card ≤ A * n i ∧ (D + 1) * X.card ≤ (modelEdges ω X).card * D}

/-- Summing the dense-set estimate over sizes and parts. -/
theorem model_badSparse_probability_le {C A D : ℕ} (hC : 0 < C) (hD : 0 < D)
    {n : Fin C → ℕ}
    (hbounds : ∀ i : Fin C, 0 < i.val → ∀ x : ℕ, 0 < x → x ≤ A * n i →
      ∃ L N : ℕ, 3 * x ≤ L ∧ (modelBefore n i).card ≤ N ∧
        (∀ v ∈ modelBefore n i, L ≤ n v.1) ∧
        (3 : ℝ) ^ (2 * D + 1) * (N : ℝ) ^ D * x / (L : ℝ) ^ (D + 1) ≤
          (1 / (16 * (C : ℝ))) ^ D) :
    finiteProb (modelBadSparse n A D) ≤ (1 : ℝ) / 8 := by
  classical
  let δ : ℝ := 1 / (16 * (C : ℝ))
  have hCR : (0 : ℝ) < C := by exact_mod_cast hC
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hδhalf : δ ≤ 1 / 2 := by
    dsimp [δ]
    apply one_div_le_one_div_of_le (by norm_num)
    have : (1 : ℝ) ≤ C := by exact_mod_cast hC
    linarith
  let E : Fin C → Set (ModelSample n) := fun i =>
    {ω | ∃ X : Finset (ModelVertex n), X ⊆ modelBefore n i ∧
      X.Nonempty ∧ X.card ≤ A * n i ∧ (D + 1) * X.card ≤ (modelEdges ω X).card * D}
  have hpart : ∀ i, finiteProb (E i) ≤ 1 / (8 * (C : ℝ)) := by
    intro i
    by_cases hiz : i.val = 0
    · have heq : E i = ∅ := by
        ext ω
        constructor
        · rintro ⟨X, hX, hnonempty, _⟩
          obtain ⟨v, hv⟩ := hnonempty
          have hvi : v.1 < i := (Finset.mem_filter.mp (hX hv)).2
          have : v.1.val < i.val := hvi
          omega
        · exact fun h => h.elim
      rw [heq, finiteProb_empty]
      positivity
    · let B : ℕ → Set (ModelSample n) := fun k =>
        {ω | ∃ X : Finset (ModelVertex n), X ⊆ modelBefore n i ∧ X.card = k + 1 ∧
          (D + 1) * (k + 1) ≤ (modelEdges ω X).card * D}
      have hsub : E i ⊆ {ω | ∃ k ∈ Finset.range (A * n i), ω ∈ B k} := by
        rintro ω ⟨X, hX, hnonempty, hsize, hdense⟩
        have hx : 0 < X.card := hnonempty.card_pos
        refine ⟨X.card - 1, Finset.mem_range.mpr (by omega), X, hX, by omega, ?_⟩
        simpa only [Nat.sub_add_cancel (show 1 ≤ X.card by omega)] using hdense
      have hfixed : ∀ k ∈ Finset.range (A * n i), finiteProb (B k) ≤ δ ^ (k + 1) := by
        intro k hk
        have hk' : k + 1 ≤ A * n i := by have := Finset.mem_range.mp hk; omega
        obtain ⟨L, N, hL, hP, hsize, hcoef⟩ := hbounds i (by omega) (k + 1) (by omega) hk'
        exact model_fixed_size_density_probability_le (modelBefore n i) (by omega) hD hL hδ
          hP hsize hcoef
      calc
        _ ≤ finiteProb {ω | ∃ k ∈ Finset.range (A * n i), ω ∈ B k} := finiteProb_mono hsub
        _ ≤ ∑ k ∈ Finset.range (A * n i), finiteProb (B k) := finiteProb_biUnion_le _ _
        _ ≤ ∑ k ∈ Finset.range (A * n i), δ ^ (k + 1) := Finset.sum_le_sum hfixed
        _ ≤ ∑ k ∈ Finset.range (A * n i), δ * ((1 : ℝ) / 2) ^ k := by
          apply Finset.sum_le_sum
          intro k hk
          rw [pow_succ']
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hδ hδhalf k) hδ
        _ = δ * (∑ k ∈ Finset.range (A * n i), ((1 : ℝ) / 2) ^ k) :=
          (Finset.mul_sum _ _ _).symm
        _ ≤ δ * 2 := mul_le_mul_of_nonneg_left (sum_geometric_two_le _) hδ
        _ = 1 / (8 * (C : ℝ)) := by dsimp [δ]; ring
  have heq : modelBadSparse n A D = {ω | ∃ i ∈ (Finset.univ : Finset (Fin C)), ω ∈ E i} := by
    ext ω
    simp only [modelBadSparse, E, Set.mem_ofPred_eq, Finset.mem_univ, true_and]
  calc
    _ = finiteProb {ω | ∃ i ∈ (Finset.univ : Finset (Fin C)), ω ∈ E i} := congrArg finiteProb heq
    _ ≤ ∑ i : Fin C, finiteProb (E i) := finiteProb_biUnion_le _ _
    _ ≤ ∑ _i : Fin C, 1 / (8 * (C : ℝ)) := Finset.sum_le_sum (fun i _ => hpart i)
    _ = 1 / 8 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp

theorem model_sparse_of_not_bad {C A D : ℕ} (hD : 0 < D) {n : Fin C → ℕ}
    (ω : ModelSample n) (hω : ω ∉ modelBadSparse n A D)
    (i : Fin C) (X : Finset (ModelVertex n)) (hX : ∀ v ∈ X, v.1 < i)
    (hsize : X.card ≤ A * n i) :
    internalCount (modelGraph ω) X ≤ (1 + 1 / (D : ℝ)) * X.card := by
  classical
  by_cases hx : X.Nonempty
  · have hbad : ¬ (D + 1) * X.card ≤ (modelEdges ω X).card * D := by
      intro h
      apply hω
      exact ⟨i, X, fun v hv => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hX v hv⟩,
        hx, hsize, h⟩
    have hlt : ((modelEdges ω X).card : ℝ) * D < ((D : ℝ) + 1) * X.card := by
      exact_mod_cast lt_of_not_ge hbad
    rw [internalCount_modelGraph]
    have hDR : (0 : ℝ) < D := by exact_mod_cast hD
    have heq : (1 + 1 / (D : ℝ)) * X.card = ((D + 1) * X.card) / (D : ℝ) := by
      field_simp
    rw [heq]
    exact (le_div_iff₀ hDR).mpr hlt.le
  · have heq : X = ∅ := Finset.not_nonempty_iff_eq_empty.mp hx
    subst X
    simp [internalCount, crossingCount]

theorem model_card {C : ℕ} (n : Fin C → ℕ) : Fintype.card (ModelVertex n) = ∑ i, n i := by
  change Fintype.card (Σ i : Fin C, Fin (n i)) = _
  simp only [Fintype.card_sigma, Fintype.card_fin]

theorem model_count_parts {C : ℕ} (n : Fin C → ℕ) (P : Fin C → Prop) [DecidablePred P] :
    ((Finset.univ : Finset (ModelVertex n)).filter (fun v => P v.1)).card =
      ∑ i : Fin C, if P i then n i else 0 := by
  classical
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  change (∑ v : Σ i : Fin C, Fin (n i), if P v.1 then (1 : ℕ) else 0) = _
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hp : P i <;> simp only [hp, if_true, if_false, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one, mul_zero]

theorem model_filter_card_le {C : ℕ} {n : Fin C → ℕ}
    (S : Finset (ModelVertex n)) (P : Fin C → Prop) [DecidablePred P] :
    (S.filter (fun v => P v.1)).card ≤ ∑ i : Fin C, if P i then n i else 0 := by
  rw [← model_count_parts n P]
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))

theorem model_suffix_card_le {C : ℕ} (hC : 0 < C) {n : Fin C → ℕ}
    (hsep : ∀ i j : Fin C, i < j → C * n j ≤ n i) (i : Fin C) :
    (modelSuffix n i).card ≤ 2 * n i := by
  classical
  let t : ℕ := ∑ j : Fin C, if i < j then n j else 0
  have hmul : C * t ≤ C * n i := by
    dsimp [t]
    rw [Finset.mul_sum]
    calc
      _ ≤ ∑ _j : Fin C, n i := by
        apply Finset.sum_le_sum
        intro j hj
        by_cases hij : i < j
        · simpa only [if_pos hij] using hsep i j hij
        · simp only [if_neg hij, mul_zero, Nat.zero_le]
      _ = _ := by simp
  have ht : t ≤ n i := Nat.le_of_mul_le_mul_left hmul hC
  have hcard : (modelSuffix n i).card = n i + t := by
    rw [modelSuffix, model_count_parts]
    calc
      _ = ∑ j : Fin C, ((if j = i then n i else 0) + (if i < j then n j else 0)) := by
        apply Finset.sum_congr rfl
        intro j hj
        rcases lt_trichotomy i j with hij | rfl | hij
        · simp only [if_pos hij.le, if_neg hij.ne.symm, if_pos hij, zero_add]
        · simp
        · simp only [if_neg hij.not_ge, if_neg hij.ne, if_neg hij.not_gt, add_zero]
      _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true, t]
  omega

/-- The last part large enough for a set provides the deterministic sparse cut. -/
theorem model_size_cut {C K A : ℕ} (hC : 0 < C) (hK : 4 ≤ K)
    (hA : A = 16 * C * K * (K + 1)) {n : Fin C → ℕ}
    (hmono : Antitone n) (S : Finset (ModelVertex n)) (hS : S.Nonempty) :
    ∃ i : Fin C, S.card ≤ A * n i ∧
      ((S.filter (fun v => i < v.1)).card : ℝ) <
        2 * S.card / (16 * K * (K + 1)) := by
  classical
  let z : Fin C := ⟨0, hC⟩
  have hCA : C ≤ A := by
    rw [hA]
    have hmul : 1 ≤ 16 * K * (K + 1) := by nlinarith
    nlinarith
  have htotal : Fintype.card (ModelVertex n) ≤ C * n z := by
    rw [model_card]
    calc
      _ ≤ ∑ _i : Fin C, n z := Finset.sum_le_sum (fun j _ => hmono (by exact Nat.zero_le _))
      _ = _ := by simp
  have hz : S.card ≤ A * n z := (Finset.card_le_univ S).trans
    (htotal.trans (Nat.mul_le_mul_right _ hCA))
  let Q := Finset.univ.filter (fun i : Fin C => S.card ≤ A * n i)
  have hQ : Q.Nonempty := ⟨z, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩⟩
  let i := Q.max' hQ
  refine ⟨i, (Finset.mem_filter.mp (Finset.max'_mem Q hQ)).2, ?_⟩
  have hKR : (0 : ℝ) < 16 * K * (K + 1) := by positivity
  have hSR : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  by_cases hnext : i.val + 1 < C
  · let j : Fin C := ⟨i.val + 1, hnext⟩
    have hij : i < j := by change i.val < i.val + 1; omega
    have hjbig : A * n j < S.card := by
      by_contra! hbad
      have hji : j ≤ i := Finset.le_max' Q j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbad⟩)
      exact (not_lt_of_ge hji) hij
    have htail : (S.filter (fun v => i < v.1)).card ≤ C * n j := by
      apply (model_filter_card_le S (fun k => i < k)).trans
      calc
        _ ≤ ∑ _k : Fin C, n j := by
          apply Finset.sum_le_sum
          intro k hk
          by_cases hik : i < k
          · simp only [if_pos hik]
            exact hmono (show j ≤ k by change i.val + 1 ≤ k.val; exact hik)
          · simp only [if_neg hik, Nat.zero_le]
        _ = _ := by simp
    have htailR : ((S.filter (fun v => i < v.1)).card : ℝ) ≤ C * n j := by exact_mod_cast htail
    have hjR : (16 * (C : ℝ) * K * (K + 1)) * n j < S.card := by
      rw [hA] at hjbig
      exact_mod_cast hjbig
    apply (lt_div_iff₀ hKR).mpr
    have hm := mul_le_mul_of_nonneg_right htailR hKR.le
    nlinarith
  · have hempty : S.filter (fun v => i < v.1) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro v hv
      have hvi : i.val < v.1.val := (Finset.mem_filter.mp hv).2
      have hvC := v.1.isLt
      omega
    rw [hempty, Finset.card_empty, Nat.cast_zero]
    positivity

/-- Explicit, widely separated part sizes satisfying both probability estimates. -/
theorem model_sizes_exist {C A D : ℕ} (hC : 0 < C) (hD : 0 < D) :
    ∃ n : Fin C → ℕ,
      (∀ i, 0 < n i) ∧ Antitone n ∧
      (∀ i j : Fin C, i < j → C * n j ≤ n i) ∧ (∀ i, 8 * C ≤ n i) ∧
      ∀ i : Fin C, 0 < i.val → ∀ x : ℕ, 0 < x → x ≤ A * n i →
        ∃ L N : ℕ, 3 * x ≤ L ∧ (modelBefore n i).card ≤ N ∧
          (∀ v ∈ modelBefore n i, L ≤ n v.1) ∧
          (3 : ℝ) ^ (2 * D + 1) * (N : ℝ) ^ D * x / (L : ℝ) ^ (D + 1) ≤
            (1 / (16 * (C : ℝ))) ^ D := by
  classical
  let R := (16 * C) ^ D * 3 ^ (2 * D + 1) * A + 3 * A + 8 * C + 2
  let b := D + 2
  let B := b ^ (C + 1)
  let n : Fin C → ℕ := fun i => R ^ (B - b ^ (i.val + 1))
  have hR : 2 ≤ R := by dsimp [R]; omega
  have hRC : C ≤ R := by dsimp [R]; omega
  have hRlarge : 8 * C ≤ R := by dsimp [R]; omega
  have hRA : 3 * A ≤ R := by dsimp [R]; omega
  have hRcoef : (16 * C) ^ D * 3 ^ (2 * D + 1) * A ≤ R := by dsimp [R]; omega
  have hb : 1 < b := by dsimp [b]; omega
  have hB : 0 < B := by dsimp [B]; positivity
  have hpowlt : ∀ i : Fin C, b ^ (i.val + 1) < B := by
    intro i
    exact pow_lt_pow_right₀ hb (by have := i.isLt; omega)
  have hnR : ∀ i, R ≤ n i := by
    intro i
    calc
      R = R ^ 1 := by simp
      _ ≤ _ := pow_le_pow_right₀ (by omega) (by have := hpowlt i; omega)
  have hn : ∀ i, 0 < n i := fun i => lt_of_lt_of_le (by omega) (hnR i)
  have hmono : Antitone n := by
    intro i j hij
    apply pow_le_pow_right₀ (by omega)
    have hp : b ^ (i.val + 1) ≤ b ^ (j.val + 1) := pow_le_pow_right₀ hb.le (by exact Nat.add_le_add_right hij 1)
    exact Nat.sub_le_sub_left hp B
  have hgap : ∀ i j : Fin C, i < j → R * n j ≤ n i := by
    intro i j hij
    change R * R ^ (B - b ^ (j.val + 1)) ≤ R ^ (B - b ^ (i.val + 1))
    rw [← pow_succ']
    apply pow_le_pow_right₀ (by omega)
    have hp : b ^ (i.val + 1) < b ^ (j.val + 1) :=
      pow_lt_pow_right₀ hb (by exact Nat.add_lt_add_right hij 1)
    have := hpowlt j
    omega
  have hsep : ∀ i j : Fin C, i < j → C * n j ≤ n i :=
    fun i j hij => (Nat.mul_le_mul_right _ hRC).trans (hgap i j hij)
  have htotal : Fintype.card (ModelVertex n) ≤ R ^ B := by
    rw [model_card]
    have hsmall : ∀ i : Fin C, n i ≤ R ^ (B - 1) := by
      intro i
      apply pow_le_pow_right₀ (by omega)
      apply Nat.sub_le_sub_left
      exact Nat.one_le_pow _ _ (by omega)
    calc
      _ ≤ ∑ _i : Fin C, R ^ (B - 1) := Finset.sum_le_sum (fun i _ => hsmall i)
      _ = C * R ^ (B - 1) := by simp
      _ ≤ R * R ^ (B - 1) := Nat.mul_le_mul_right _ hRC
      _ = R ^ B := by rw [← pow_succ', Nat.sub_add_cancel hB]
  refine ⟨n, hn, hmono, hsep, fun i => hRlarge.trans (hnR i), ?_⟩
  intro i hi x hx hxi
  let p : Fin C := ⟨i.val - 1, by have := i.isLt; omega⟩
  let L := n p
  let N := R ^ B
  have hpi : p < i := by change i.val - 1 < i.val; omega
  have hL : L = R ^ (B - b ^ i.val) := by
    dsimp [L, n, p]
    rw [Nat.sub_add_cancel hi]
  have hLR : 0 < L := hn p
  have hthree : 3 * x ≤ L := calc
    3 * x ≤ 3 * (A * n i) := Nat.mul_le_mul_left _ hxi
    _ = (3 * A) * n i := by ring
    _ ≤ R * n i := Nat.mul_le_mul_right _ hRA
    _ ≤ L := hgap p i hpi
  have hP : (modelBefore n i).card ≤ N := (Finset.card_filter_le _ _).trans htotal
  have hmin : ∀ v ∈ modelBefore n i, L ≤ n v.1 := by
    intro v hv
    apply hmono
    have hvi : v.1.val < i.val := (Finset.mem_filter.mp hv).2
    change v.1.val ≤ i.val - 1
    omega
  have hden : R * N ^ D * n i ≤ L ^ (D + 1) := by
    rw [hL]
    change R * (R ^ B) ^ D * R ^ (B - b ^ (i.val + 1)) ≤
      (R ^ (B - b ^ i.val)) ^ (D + 1)
    rw [← pow_mul, ← pow_succ', ← pow_add, ← pow_mul]
    apply pow_le_pow_right₀ (by omega)
    have ht : 1 ≤ b ^ i.val := Nat.one_le_pow _ _ (by omega)
    have hbig : b ^ (i.val + 1) ≤ B := (hpowlt i).le
    have hsmall : b ^ i.val ≤ B :=
      (pow_le_pow_right₀ hb.le (by omega : i.val ≤ i.val + 1)).trans hbig
    have he₁ := Nat.sub_add_cancel hsmall
    have he₂ := Nat.sub_add_cancel hbig
    rw [pow_succ] at he₂ ⊢
    dsimp [b] at ht he₁ he₂ ⊢
    nlinarith
  have hnat : 3 ^ (2 * D + 1) * N ^ D * x * (16 * C) ^ D ≤ L ^ (D + 1) := calc
    _ ≤ 3 ^ (2 * D + 1) * N ^ D * (A * n i) * (16 * C) ^ D :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hxi)
    _ = ((16 * C) ^ D * 3 ^ (2 * D + 1) * A) * (N ^ D * n i) := by ring
    _ ≤ R * (N ^ D * n i) := Nat.mul_le_mul_right _ hRcoef
    _ ≤ L ^ (D + 1) := by simpa only [mul_assoc] using hden
  refine ⟨L, N, hthree, hP, hmin, ?_⟩
  rw [div_pow, one_pow]
  apply (div_le_div_iff₀ (by exact_mod_cast pow_pos hLR (D + 1))
    (by positivity : (0 : ℝ) < (16 * C) ^ D)).mpr
  simpa only [one_mul] using (show (3 : ℝ) ^ (2 * D + 1) * (N : ℝ) ^ D * x *
    (16 * (C : ℝ)) ^ D ≤ (L : ℝ) ^ (D + 1) by exact_mod_cast hnat)

/-- The probabilistic base graph: large chromatic number and sparse bounded-degree subgraphs. -/
theorem model_base_exists {q K : ℕ} (hq : 1 ≤ q) (hK : 4 ≤ K) :
    ∃ n : Fin (64 * q ^ 2) → ℕ, ∃ ω : ModelSample n,
      ¬ (modelGraph ω).Colorable (2 * q) ∧
      ∀ J : SimpleGraph (ModelVertex n), J ≤ modelGraph ω →
        (∀ v, Nat.card (J.neighborSet v) ≤ K) → J.Colorable 4 := by
  classical
  let C := 64 * q ^ 2
  let A := 16 * C * K * (K + 1)
  let D := 2 * (K + 1)
  have hqpos : 0 < q := by omega
  have hC : 0 < C := by dsimp [C]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  obtain ⟨n, hn, hmono, hsep, hlarge, hbounds⟩ := model_sizes_exist (A := A) hC hD
  let : Nonempty (ModelSample n) := ⟨fun k => ⟨0, hn k.2⟩⟩
  have hcolor := model_badColor_probability_le hqpos hC hn (model_suffix_card_le hC hsep) hlarge
  have hsparse := model_badSparse_probability_le hC hD hbounds
  obtain ⟨ω, hωcolor, hωsparse⟩ := exists_avoiding_of_finiteProb_lt_one
    (modelBadColor n q) (modelBadSparse n A D) (by linarith)
  refine ⟨n, ω, ?_, ?_⟩
  · apply model_not_colorable_of_independent_weights hn (by omega) ω
    intro I hI
    simpa only [C, Nat.cast_mul, Nat.cast_ofNat] using
      model_small_weights_of_not_bad hq rfl hn ω hωcolor I hI
  · have hcuts : SparseCutProperty (modelGraph ω) K := by
      apply sparse_cuts_of_parts (A := A) (fun v : ModelVertex n => v.1) n
        (modelGraph_same_part ω) (modelGraph_one_neighbor ω)
      · exact model_size_cut hC hK rfl hmono
      · intro i X hX hsize
        simpa only [D, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using
          model_sparse_of_not_bad hD ω hωsparse i X hX hsize
    intro J hJ hdeg
    exact colorable_four_of_sparse_cuts hK hcuts hJ hdeg

/-- Arc graphs have arbitrarily large chromatic number while their four-cycle-free subgraphs
are six-colorable. -/
theorem arc_counterexample_family (M : ℕ) :
    ∃ (V : Type) (G : SimpleGraph V), Nonempty V ∧ M ≤ G.chromaticNumber ∧
      ∀ J : SimpleGraph V, J ≤ G → FourCycleFree J → J.Colorable 6 := by
  classical
  let q : ℕ := 2 ^ M + 2
  let d := 64 * q ^ 2 - 1
  let K := d + d.choose 2
  have hq : 1 ≤ q := Nat.succ_le_succ (Nat.zero_le (2 ^ M + 1))
  have hd : 4 ≤ d := by
    have hbig : 64 ≤ 64 * q ^ 2 := by nlinarith
    dsimp [d]
    omega
  have hK : 4 ≤ K := by dsimp [K]; omega
  obtain ⟨n, ω, hnot, hbase⟩ := model_base_exists hq hK
  let F := modelGraph ω
  have hnotArc : ¬ (arcGraph F).Colorable M := by
    intro hc
    apply hnot
    exact (base_colorable_of_arc_colorable hc).mono (by dsimp [q]; omega)
  have hV : Nonempty (Arc F) := by
    by_contra hempty
    let : IsEmpty (Arc F) := not_nonempty_iff.mp hempty
    exact hnotArc (SimpleGraph.Colorable.of_isEmpty M)
  have hchi : (M : ℕ∞) ≤ (arcGraph F).chromaticNumber := by
    apply le_of_lt
    apply lt_of_not_ge
    intro h
    exact hnotArc (SimpleGraph.chromaticNumber_le_iff_colorable.mp h)
  refine ⟨Arc F, arcGraph F, hV, hchi, ?_⟩
  intro J hJ h4
  exact arc_colorable_bound (d := d) (a := 4) (model_outgoing_card_le ω) hbase hJ h4

/-- The counterexample is available in every universe occurring in the conjecture. -/
theorem counterexample_family (M : ℕ) :
    ∃ (V : Type u) (G : SimpleGraph V), Nonempty V ∧ M ≤ G.chromaticNumber ∧
      ∀ H : G.Subgraph, 5 ≤ H.coe.girth → H.coe.Colorable 6 := by
  classical
  obtain ⟨V, G, hV, hchi, hcolor⟩ := arc_counterexample_family M
  let W := ULift.{u} V
  let G' : SimpleGraph W := G.comap ULift.down
  let e : G' ≃g G := SimpleGraph.Iso.comap Equiv.ulift G
  have hW : Nonempty W := hV.map ULift.up
  refine ⟨W, G', hW, ?_, ?_⟩
  · simpa only [SimpleGraph.chromaticNumber_congr e] using hchi
  · intro H hg
    have h4 : FourCycleFree H.spanningCoe := (fourCycleFree_of_girth_ge_five hg).spanningCoe
    let J : SimpleGraph V := H.spanningCoe.comap ULift.up
    have hJG : J ≤ G := by
      intro a b hab
      exact H.adj_sub hab
    have hJ4 : FourCycleFree J := by
      intro a b x y hab hxy hax hay hbx hby
      exact h4 (ULift.up a) (ULift.up b) (ULift.up x) (ULift.up y)
        (fun h => hab (congrArg ULift.down h)) (fun h => hxy (congrArg ULift.down h))
        hax hay hbx hby
    have hc : J.Colorable 6 := hcolor J hJG hJ4
    let f : H.coe →g J := {
      toFun := fun v => v.val.down
      map_rel' := by
        intro v w hvw
        change H.Adj v.val w.val at hvw
        change H.Adj (ULift.up v.val.down) (ULift.up w.val.down)
        simpa only [ULift.up_down] using hvw
    }
    exact hc.of_hom f

/-- The final logical reduction at girth five and chromatic number seven. -/
theorem counterexample_of_family
    (hfamily : ∀ M : ℕ, ∃ (V : Type u) (G : SimpleGraph V),
      Nonempty V ∧ M ≤ G.chromaticNumber ∧
        ∀ H : G.Subgraph, 5 ≤ H.coe.girth → H.coe.Colorable 6) :
    ¬ (fcTypeOfName% "Erdos108.erdos_108") := by
  intro h
  obtain ⟨f, hf⟩ := h.mp trivial 5 (by decide) 7 (by decide)
  obtain ⟨V, G, hV, hchi, hG⟩ := hfamily f
  obtain ⟨H, hgirth, hseven⟩ := hf V G hV hchi
  have hsix := (hG H hgirth).chromaticNumber_le
  have hbad : (7 : ℕ∞) ≤ 6 := hseven.trans hsix
  norm_num at hbad

theorem target : ¬ (fcTypeOfName% "Erdos108.erdos_108") := by
  exact counterexample_of_family counterexample_family
