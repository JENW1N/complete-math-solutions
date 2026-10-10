/-
Math15Catalog.source10 — declaration-only challenge submission.
Submit this file's contents directly. The challenge supplies its trusted imports
and outer Bounty namespace. Checked with Lean 4.35.0-rc2.
-/
end Bounty

/- Foundation -/
section
namespace Math15.Graceful

theorem edgeCount_eq_card_edgeFinset {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] :
    edgeCount G = G.edgeFinset.card := by
  classical
  unfold edgeCount
  apply Finset.card_bij (fun e _ => s(e.1, e.2))
  · intro e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
    exact SimpleGraph.mem_edgeFinset.mpr (G.mem_edgeSet.mpr he.2)
  · intro e he e' he' heq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he he'
    rcases Sym2.eq_iff.mp heq with h | h
    · exact Prod.ext h.1 h.2
    · have hrev : e'.2 < e'.1 := by simpa [h.1, h.2] using he.1
      exact (lt_asymm he'.1 hrev).elim
  · intro e he
    induction e using Sym2.ind with | _ x y =>
    have hxy := G.mem_edgeSet.mp (SimpleGraph.mem_edgeFinset.mp he)
    rcases lt_trichotomy x y with hlt | heq | hgt
    · refine ⟨(x, y), ?_, rfl⟩
      simpa using And.intro hlt hxy
    · subst y
      exact (G.irrefl hxy).elim
    · refine ⟨(y, x), ?_, Sym2.eq_swap⟩
      simpa using And.intro hgt hxy.symm

theorem edgeCount_add_one_eq_of_isTree {n : ℕ} (G : SimpleGraph (Fin n))
    (hG : G.IsTree) : edgeCount G + 1 = n := by
  classical
  rw [edgeCount_eq_card_edgeFinset]
  simpa using hG.card_edgeFinset

theorem edgeCount_eq_of_isTree {n : ℕ} (G : SimpleGraph (Fin n))
    (hG : G.IsTree) : edgeCount G = n - 1 := by
  have := edgeCount_add_one_eq_of_isTree G hG
  omega

theorem degree_eq_graph_degree {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (v : Fin n) : degree G v = G.degree v := by
  classical
  rw [← G.card_neighborFinset_eq_degree, G.neighborFinset_eq_filter]
  unfold degree
  congr 1
  ext w
  simp

theorem branch43_leaf_count {n : ℕ} (G : SimpleGraph (Fin n))
    (hG : G.IsTree) {u v : Fin n} (hbranch : Branch43 G u v) :
    (Finset.univ.filter (fun w => degree G w = 1)).card = 5 := by
  classical
  obtain ⟨huv, hu, hv, hrest⟩ := hbranch
  let : Nontrivial (Fin n) := ⟨⟨u, v, huv⟩⟩
  have hpos (w : Fin n) : 1 ≤ degree G w := by
    rw [degree_eq_graph_degree]
    exact hG.preconnected.degree_pos_of_nontrivial w
  have hpoint (w : Fin n) :
      degree G w + (if degree G w = 1 then 1 else 0) =
        2 + (if w = u then 2 else 0) + (if w = v then 1 else 0) := by
    by_cases hwu : w = u
    · subst w
      simp [hu, huv]
    by_cases hwv : w = v
    · subst w
      simp [hv, huv.symm]
    have := hrest w hwu hwv
    have := hpos w
    split_ifs <;> omega
  have hsum := congrArg (fun f : Fin n → ℕ => ∑ w, f w) (funext hpoint)
  have hdegrees : ∑ w : Fin n, degree G w = 2 * edgeCount G := by
    simp_rw [degree_eq_graph_degree, edgeCount_eq_card_edgeFinset]
    exact G.sum_degrees_eq_twice_card_edges
  have htree := edgeCount_add_one_eq_of_isTree G hG
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    Finset.sum_boole] at hsum
  rw [hdegrees] at hsum
  norm_num at hsum
  omega

/-- For a finite graph, distinct nonzero edge differences bounded by the number
of edges necessarily give complete coverage. -/
theorem labeling_of_injective_differences {n : ℕ} (G : SimpleGraph (Fin n))
    (f : Fin n → ℕ) (hinj : Function.Injective f)
    (hbound : ∀ v, f v ≤ edgeCount G)
    (hdiff : ∀ e e' : Fin n × Fin n,
      e.1 < e.2 → G.Adj e.1 e.2 → e'.1 < e'.2 → G.Adj e'.1 e'.2 →
      Nat.dist (f e.1) (f e.2) = Nat.dist (f e'.1) (f e'.2) → e = e') :
    Function.Injective f ∧ (∀ v, f v ≤ edgeCount G) ∧
      (∀ d, 1 ≤ d → d ≤ edgeCount G →
        ∃! e : Fin n × Fin n, e.1 < e.2 ∧ G.Adj e.1 e.2 ∧
          Nat.dist (f e.1) (f e.2) = d) := by
  classical
  let edges : Finset (Fin n × Fin n) :=
    Finset.univ.filter (fun e => e.1 < e.2 ∧ G.Adj e.1 e.2)
  let diff : Fin n × Fin n → ℕ := fun e => Nat.dist (f e.1) (f e.2)
  have edges_card : edges.card = edgeCount G := rfl
  have image_card : (edges.image diff).card = edgeCount G := by
    rw [Finset.card_image_iff.mpr, edges_card]
    intro e he e' he' h
    simp [edges] at he he'
    exact hdiff e e' he.1 he.2 he'.1 he'.2 h
  have image_subset : edges.image diff ⊆ Finset.Icc 1 (edgeCount G) := by
    intro d hd
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hd
    simp only [edges, Finset.mem_filter, Finset.mem_univ, true_and] at he
    have hn : f e.1 ≠ f e.2 := fun h => (ne_of_lt he.1) (hinj h)
    have hpos := Nat.dist_pos_of_ne hn
    have h1 := hbound e.1
    have h2 := hbound e.2
    simp only [Finset.mem_Icc, diff]
    unfold Nat.dist at *
    omega
  have image_eq : edges.image diff = Finset.Icc 1 (edgeCount G) := by
    apply Finset.eq_of_subset_of_card_le image_subset
    simpa only [Nat.card_Icc, image_card, Nat.add_sub_cancel] using
      (le_refl (edgeCount G))
  refine ⟨hinj, hbound, ?_⟩
  intro d hlow hupp
  have hd : d ∈ edges.image diff := by rw [image_eq]; exact Finset.mem_Icc.mpr ⟨hlow, hupp⟩
  obtain ⟨e, he, hde⟩ := Finset.mem_image.mp hd
  simp only [edges, Finset.mem_filter, Finset.mem_univ, true_and] at he
  refine ⟨e, ⟨he.1, he.2, hde⟩, ?_⟩
  intro e' he'
  exact hdiff e' e he'.1 he'.2.1 he.1 he.2 (he'.2.2.trans hde.symm)


theorem isGraceful_of_injective_differences {n : ℕ} (G : SimpleGraph (Fin n))
    (f : Fin n → ℕ) (hinj : Function.Injective f)
    (hbound : ∀ v, f v ≤ edgeCount G)
    (hdiff : ∀ e e' : Fin n × Fin n,
      e.1 < e.2 → G.Adj e.1 e.2 → e'.1 < e'.2 → G.Adj e'.1 e'.2 →
      Nat.dist (f e.1) (f e.2) = Nat.dist (f e'.1) (f e'.2) → e = e') :
    IsGraceful G :=
  ⟨f, labeling_of_injective_differences G f hinj hbound hdiff⟩

end Math15.Graceful
end

/- DoubleSpider -/
section
namespace Bounty

/-- A graph whose positive vertices each have a single lower-indexed parent. -/
def parentGraph (N : ℕ) (parent : ℕ → ℕ) : SimpleGraph (Fin (N + 1)) where
  Adj i j := (i.val < j.val ∧ parent j.val = i.val) ∨
    (j.val < i.val ∧ parent i.val = j.val)
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by intro i; simp⟩

theorem parentGraph_edgeCount (N : ℕ) (parent : ℕ → ℕ)
    (hp : ∀ j, 0 < j → j ≤ N → parent j < j) :
    Math15.Graceful.edgeCount (parentGraph N parent) = N := by
  classical
  unfold Math15.Graceful.edgeCount
  let es : Finset (Fin (N+1) × Fin (N+1)) := Finset.univ.filter
    (fun e => e.1 < e.2 ∧ (parentGraph N parent).Adj e.1 e.2)
  let verts : Finset (Fin (N+1)) := Finset.univ.filter (fun j => 0 < j.val)
  have hc : es.card = verts.card := by
    apply Finset.card_bij (fun e _ => e.2)
    · intro e he
      simp only [es, Finset.mem_filter, Finset.mem_univ, true_and] at he
      simp only [verts, Finset.mem_filter, Finset.mem_univ, true_and]
      exact Nat.lt_of_le_of_lt (Nat.zero_le e.1.val) he.1
    · intro a ha b hb heq
      simp only [es, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      have hpa : parent a.2.val = a.1.val := by
        rcases ha.2 with h | h
        · exact h.2
        · exact False.elim (Nat.lt_asymm ha.1 h.1)
      have hpb : parent b.2.val = b.1.val := by
        rcases hb.2 with h | h
        · exact h.2
        · exact False.elim (Nat.lt_asymm hb.1 h.1)
      apply Prod.ext _ heq
      apply Fin.ext
      rw [← hpa, ← hpb, heq]
    · intro j hj
      simp only [verts, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      have hpj := hp j.val hj (by omega)
      let i : Fin (N+1) := ⟨parent j.val, hpj.trans j.isLt⟩
      refine ⟨(i,j), ?_, rfl⟩
      simp only [es, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hpj, Or.inl ⟨hpj, rfl⟩⟩
  have hv : verts = Finset.univ.erase (0 : Fin (N+1)) := by
    ext j
    simp only [verts, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_erase, and_true]
    constructor
    · intro hj hzero
      subst j
      norm_num at hj
    · intro hj
      by_contra hzero
      apply hj
      apply Fin.ext
      have : j.val = 0 := by omega
      simpa using this
  have hcard : verts.card = N := by rw [hv]; simp
  calc
    _ = es.card := by rfl
    _ = N := hc.trans hcard

theorem parentGraph_connected (N : ℕ) (parent : ℕ → ℕ)
    (hp : ∀ j, 0 < j → j ≤ N → parent j < j) :
    (parentGraph N parent).Connected := by
  have hroot (k : ℕ) : ∀ hk : k < N+1,
      (parentGraph N parent).Reachable 0 ⟨k, hk⟩ := by
    induction k using Nat.strong_induction_on with | h k ih =>
    intro hk
    by_cases hzero : k = 0
    · subst k
      exact SimpleGraph.Reachable.refl _
    have hkpos : 0 < k := by omega
    have hpk := hp k hkpos (by omega)
    have hparent := ih (parent k) hpk (hpk.trans hk)
    apply hparent.trans
    apply SimpleGraph.Adj.reachable
    exact Or.inl ⟨hpk, rfl⟩
  refine ⟨fun u v => ?_⟩
  exact (hroot u.val u.isLt).symm.trans (hroot v.val v.isLt)

theorem parentGraph_isTree (N : ℕ) (parent : ℕ → ℕ)
    (hp : ∀ j, 0 < j → j ≤ N → parent j < j) :
    (parentGraph N parent).IsTree := by
  classical
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  refine ⟨parentGraph_connected N parent hp, ?_⟩
  rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card,
    ← Math15.Graceful.edgeCount_eq_card_edgeFinset, parentGraph_edgeCount N parent hp]
  simp

def doubleSpiderEdges (a b c d e f : ℕ) : ℕ := d+a+b+c+e+f

def doubleSpiderParent (a b c d e _f j : ℕ) : ℕ :=
  if j = d+1 ∨ j = d+a+1 ∨ j = d+a+b+1 then 0
  else if j = d+a+b+c+1 ∨ j = d+a+b+c+e+1 then d
  else j-1

def doubleSpider (a b c d e f : ℕ) : SimpleGraph (Fin (doubleSpiderEdges a b c d e f + 1)) :=
  parentGraph (doubleSpiderEdges a b c d e f) (doubleSpiderParent a b c d e f)

theorem doubleSpiderParent_lt (a b c d e f j : ℕ) (hj : 0 < j) :
    doubleSpiderParent a b c d e f j < j := by
  unfold doubleSpiderParent
  split_ifs <;> omega

theorem doubleSpider_edgeCount (a b c d e f : ℕ) :
    Math15.Graceful.edgeCount (doubleSpider a b c d e f) = doubleSpiderEdges a b c d e f :=
  parentGraph_edgeCount _ _ (fun j hj _ => doubleSpiderParent_lt _ _ _ _ _ _ j hj)

theorem doubleSpider_isTree (a b c d e f : ℕ) : (doubleSpider a b c d e f).IsTree :=
  parentGraph_isTree _ _ (fun j hj _ => doubleSpiderParent_lt _ _ _ _ _ _ j hj)

end Bounty
end

/- AllTwoTest -/
section
namespace Bounty

def allTwoLabel (d j : ℕ) : ℕ :=
  if j ≤ d then
    if j % 4 = 0 then j / 2
    else if j % 4 = 1 then d + (if d % 2 = 0 then 4 else 10) - j / 2
    else if j % 4 = 2 then j / 2 + 6
    else d + (if d % 2 = 0 then 10 else 4) - j / 2
  else if j = d+1 then d+10-d%2
  else if j = d+2 then 1
  else if j = d+3 then d+8-d%2
  else if j = d+4 then 3
  else if j = d+5 then d+6-d%2
  else if j = d+6 then 5
  else if j = d+7 then
    if d%4 = 0 ∨ d%4 = 3 then 2*(d/4)+2 else d+11-d%2-(2*(d/4)+2)
  else if j = d+8 then
    if d%4 = 0 ∨ d%4 = 3 then d+11-d%2-(2*(d/4)+2) else 2*(d/4)+2
  else if j = d+9 then
    if d%4 = 0 ∨ d%4 = 3 then 2*(d/4)+4 else d+11-d%2-(2*(d/4)+4)
  else if d%4 = 0 ∨ d%4 = 3 then d+11-d%2-(2*(d/4)+4) else 2*(d/4)+4

lemma allTwo_index_cases (d x : ℕ) (hx : x ≤ d+10) :
    x ≤ d ∨ x=d+1 ∨ x=d+2 ∨ x=d+3 ∨ x=d+4 ∨ x=d+5 ∨ x=d+6 ∨ x=d+7 ∨ x=d+8 ∨ x=d+9 ∨ x=d+10 := by omega

lemma allTwoLabel_case_0_0 {d : ℕ} {i : ℕ} (hi : i ≤ d) {j : ℕ} (hj : j ≤ d)
    (heq : allTwoLabel d i = allTwoLabel d j) : i = j := by
  simp (discharger := omega) only [allTwoLabel, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoLabel_case_0_1 {d : ℕ} {i : ℕ} (hi : i ≤ d)
    (heq : allTwoLabel d i = allTwoLabel d (d+1)) : i = (d+1) := by
  simp (discharger := omega) only [allTwoLabel, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoLabel_case_0_2 {d : ℕ} {i : ℕ} (hi : i ≤ d)
    (heq : allTwoLabel d i = allTwoLabel d (d+2)) : i = (d+2) := by
  simp (discharger := omega) only [allTwoLabel, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoLabel_case_0_3 {d : ℕ} {i : ℕ} (hi : i ≤ d)
    (heq : allTwoLabel d i = allTwoLabel d (d+3)) : i = (d+3) := by
  simp (discharger := omega) only [allTwoLabel, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoLabel_case_0_4 {d : ℕ} {i : ℕ} (hi : i ≤ d)
    (heq : allTwoLabel d i = allTwoLabel d (d+4)) : i = (d+4) := by
  simp (discharger := omega) only [allTwoLabel, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoLabel_case_0_5 {d : ℕ} {i : ℕ} (hi : i ≤ d)
    (heq : allTwoLabel d i = allTwoLabel d (d+5)) : i = (d+5) := by
  simp (discharger := omega) only [allTwoLabel, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoLabel_case_0_6 {d : ℕ} {i : ℕ} (hi : i ≤ d)
    (heq : allTwoLabel d i = allTwoLabel d (d+6)) : i = (d+6) := by
  simp (discharger := omega) only [allTwoLabel, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoLabel_case_0_7 {d : ℕ} {i : ℕ} (hi : i ≤ d)
    (heq : allTwoLabel d i = allTwoLabel d (d+7)) : i = (d+7) := by
  simp (discharger := omega) only [allTwoLabel, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoLabel_case_0_8 {d : ℕ} {i : ℕ} (hi : i ≤ d)
    (heq : allTwoLabel d i = allTwoLabel d (d+8)) : i = (d+8) := by
  simp (discharger := omega) only [allTwoLabel, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoLabel_case_0_9 {d : ℕ} {i : ℕ} (hi : i ≤ d)
    (heq : allTwoLabel d i = allTwoLabel d (d+9)) : i = (d+9) := by
  simp (discharger := omega) only [allTwoLabel, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoLabel_case_0_10 {d : ℕ} {i : ℕ} (hi : i ≤ d)
    (heq : allTwoLabel d i = allTwoLabel d (d+10)) : i = (d+10) := by
  simp (discharger := omega) only [allTwoLabel, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoLabel_case_1_2 {d : ℕ}
    (heq : allTwoLabel d (d+1) = allTwoLabel d (d+2)) : (d+1) = (d+2) := by
  simp (discharger := omega) only [allTwoLabel, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoLabel_case_1_3 {d : ℕ}
    (heq : allTwoLabel d (d+1) = allTwoLabel d (d+3)) : (d+1) = (d+3) := by
  simp (discharger := omega) only [allTwoLabel, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoLabel_case_1_4 {d : ℕ}
    (heq : allTwoLabel d (d+1) = allTwoLabel d (d+4)) : (d+1) = (d+4) := by
  simp (discharger := omega) only [allTwoLabel, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoLabel_case_1_5 {d : ℕ}
    (heq : allTwoLabel d (d+1) = allTwoLabel d (d+5)) : (d+1) = (d+5) := by
  simp (discharger := omega) only [allTwoLabel, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoLabel_case_1_6 {d : ℕ}
    (heq : allTwoLabel d (d+1) = allTwoLabel d (d+6)) : (d+1) = (d+6) := by
  simp (discharger := omega) only [allTwoLabel, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoLabel_case_1_7 {d : ℕ}
    (heq : allTwoLabel d (d+1) = allTwoLabel d (d+7)) : (d+1) = (d+7) := by
  simp (discharger := omega) only [allTwoLabel, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoLabel_case_1_8 {d : ℕ}
    (heq : allTwoLabel d (d+1) = allTwoLabel d (d+8)) : (d+1) = (d+8) := by
  simp (discharger := omega) only [allTwoLabel, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoLabel_case_1_9 {d : ℕ}
    (heq : allTwoLabel d (d+1) = allTwoLabel d (d+9)) : (d+1) = (d+9) := by
  simp (discharger := omega) only [allTwoLabel, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoLabel_case_1_10 {d : ℕ}
    (heq : allTwoLabel d (d+1) = allTwoLabel d (d+10)) : (d+1) = (d+10) := by
  simp (discharger := omega) only [allTwoLabel, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoLabel_case_2_3 {d : ℕ}
    (heq : allTwoLabel d (d+2) = allTwoLabel d (d+3)) : (d+2) = (d+3) := by
  simp (discharger := omega) only [allTwoLabel, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoLabel_case_2_4 {d : ℕ}
    (heq : allTwoLabel d (d+2) = allTwoLabel d (d+4)) : (d+2) = (d+4) := by
  simp (discharger := omega) only [allTwoLabel, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoLabel_case_2_5 {d : ℕ}
    (heq : allTwoLabel d (d+2) = allTwoLabel d (d+5)) : (d+2) = (d+5) := by
  simp (discharger := omega) only [allTwoLabel, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoLabel_case_2_6 {d : ℕ}
    (heq : allTwoLabel d (d+2) = allTwoLabel d (d+6)) : (d+2) = (d+6) := by
  simp (discharger := omega) only [allTwoLabel, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoLabel_case_2_7 {d : ℕ}
    (heq : allTwoLabel d (d+2) = allTwoLabel d (d+7)) : (d+2) = (d+7) := by
  simp (discharger := omega) only [allTwoLabel, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoLabel_case_2_8 {d : ℕ}
    (heq : allTwoLabel d (d+2) = allTwoLabel d (d+8)) : (d+2) = (d+8) := by
  simp (discharger := omega) only [allTwoLabel, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoLabel_case_2_9 {d : ℕ}
    (heq : allTwoLabel d (d+2) = allTwoLabel d (d+9)) : (d+2) = (d+9) := by
  simp (discharger := omega) only [allTwoLabel, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoLabel_case_2_10 {d : ℕ}
    (heq : allTwoLabel d (d+2) = allTwoLabel d (d+10)) : (d+2) = (d+10) := by
  simp (discharger := omega) only [allTwoLabel, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoLabel_case_3_4 {d : ℕ}
    (heq : allTwoLabel d (d+3) = allTwoLabel d (d+4)) : (d+3) = (d+4) := by
  simp (discharger := omega) only [allTwoLabel, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoLabel_case_3_5 {d : ℕ}
    (heq : allTwoLabel d (d+3) = allTwoLabel d (d+5)) : (d+3) = (d+5) := by
  simp (discharger := omega) only [allTwoLabel, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoLabel_case_3_6 {d : ℕ}
    (heq : allTwoLabel d (d+3) = allTwoLabel d (d+6)) : (d+3) = (d+6) := by
  simp (discharger := omega) only [allTwoLabel, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoLabel_case_3_7 {d : ℕ}
    (heq : allTwoLabel d (d+3) = allTwoLabel d (d+7)) : (d+3) = (d+7) := by
  simp (discharger := omega) only [allTwoLabel, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoLabel_case_3_8 {d : ℕ}
    (heq : allTwoLabel d (d+3) = allTwoLabel d (d+8)) : (d+3) = (d+8) := by
  simp (discharger := omega) only [allTwoLabel, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoLabel_case_3_9 {d : ℕ}
    (heq : allTwoLabel d (d+3) = allTwoLabel d (d+9)) : (d+3) = (d+9) := by
  simp (discharger := omega) only [allTwoLabel, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoLabel_case_3_10 {d : ℕ}
    (heq : allTwoLabel d (d+3) = allTwoLabel d (d+10)) : (d+3) = (d+10) := by
  simp (discharger := omega) only [allTwoLabel, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoLabel_case_4_5 {d : ℕ}
    (heq : allTwoLabel d (d+4) = allTwoLabel d (d+5)) : (d+4) = (d+5) := by
  simp (discharger := omega) only [allTwoLabel, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoLabel_case_4_6 {d : ℕ}
    (heq : allTwoLabel d (d+4) = allTwoLabel d (d+6)) : (d+4) = (d+6) := by
  simp (discharger := omega) only [allTwoLabel, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoLabel_case_4_7 {d : ℕ}
    (heq : allTwoLabel d (d+4) = allTwoLabel d (d+7)) : (d+4) = (d+7) := by
  simp (discharger := omega) only [allTwoLabel, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoLabel_case_4_8 {d : ℕ}
    (heq : allTwoLabel d (d+4) = allTwoLabel d (d+8)) : (d+4) = (d+8) := by
  simp (discharger := omega) only [allTwoLabel, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoLabel_case_4_9 {d : ℕ}
    (heq : allTwoLabel d (d+4) = allTwoLabel d (d+9)) : (d+4) = (d+9) := by
  simp (discharger := omega) only [allTwoLabel, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoLabel_case_4_10 {d : ℕ}
    (heq : allTwoLabel d (d+4) = allTwoLabel d (d+10)) : (d+4) = (d+10) := by
  simp (discharger := omega) only [allTwoLabel, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoLabel_case_5_6 {d : ℕ}
    (heq : allTwoLabel d (d+5) = allTwoLabel d (d+6)) : (d+5) = (d+6) := by
  simp (discharger := omega) only [allTwoLabel, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoLabel_case_5_7 {d : ℕ}
    (heq : allTwoLabel d (d+5) = allTwoLabel d (d+7)) : (d+5) = (d+7) := by
  simp (discharger := omega) only [allTwoLabel, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoLabel_case_5_8 {d : ℕ}
    (heq : allTwoLabel d (d+5) = allTwoLabel d (d+8)) : (d+5) = (d+8) := by
  simp (discharger := omega) only [allTwoLabel, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoLabel_case_5_9 {d : ℕ}
    (heq : allTwoLabel d (d+5) = allTwoLabel d (d+9)) : (d+5) = (d+9) := by
  simp (discharger := omega) only [allTwoLabel, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoLabel_case_5_10 {d : ℕ}
    (heq : allTwoLabel d (d+5) = allTwoLabel d (d+10)) : (d+5) = (d+10) := by
  simp (discharger := omega) only [allTwoLabel, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoLabel_case_6_7 {d : ℕ}
    (heq : allTwoLabel d (d+6) = allTwoLabel d (d+7)) : (d+6) = (d+7) := by
  simp (discharger := omega) only [allTwoLabel, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoLabel_case_6_8 {d : ℕ}
    (heq : allTwoLabel d (d+6) = allTwoLabel d (d+8)) : (d+6) = (d+8) := by
  simp (discharger := omega) only [allTwoLabel, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoLabel_case_6_9 {d : ℕ}
    (heq : allTwoLabel d (d+6) = allTwoLabel d (d+9)) : (d+6) = (d+9) := by
  simp (discharger := omega) only [allTwoLabel, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoLabel_case_6_10 {d : ℕ}
    (heq : allTwoLabel d (d+6) = allTwoLabel d (d+10)) : (d+6) = (d+10) := by
  simp (discharger := omega) only [allTwoLabel, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoLabel_case_7_8 {d : ℕ}
    (heq : allTwoLabel d (d+7) = allTwoLabel d (d+8)) : (d+7) = (d+8) := by
  simp (discharger := omega) only [allTwoLabel, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoLabel_case_7_9 {d : ℕ}
    (heq : allTwoLabel d (d+7) = allTwoLabel d (d+9)) : (d+7) = (d+9) := by
  simp (discharger := omega) only [allTwoLabel, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoLabel_case_7_10 {d : ℕ}
    (heq : allTwoLabel d (d+7) = allTwoLabel d (d+10)) : (d+7) = (d+10) := by
  simp (discharger := omega) only [allTwoLabel, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoLabel_case_8_9 {d : ℕ}
    (heq : allTwoLabel d (d+8) = allTwoLabel d (d+9)) : (d+8) = (d+9) := by
  simp (discharger := omega) only [allTwoLabel, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoLabel_case_8_10 {d : ℕ}
    (heq : allTwoLabel d (d+8) = allTwoLabel d (d+10)) : (d+8) = (d+10) := by
  simp (discharger := omega) only [allTwoLabel, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoLabel_case_9_10 {d : ℕ}
    (heq : allTwoLabel d (d+9) = allTwoLabel d (d+10)) : (d+9) = (d+10) := by
  simp (discharger := omega) only [allTwoLabel, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoLabel_injective {d i j : ℕ} (hi : i ≤ d+10) (hj : j ≤ d+10)
    (heq : allTwoLabel d i = allTwoLabel d j) : i=j := by

  rcases allTwo_index_cases d i hi with hix | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl

  · rcases allTwo_index_cases d j hj with hjx | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl

    · exact allTwoLabel_case_0_0 hix hjx heq

    · exact allTwoLabel_case_0_1 hix heq

    · exact allTwoLabel_case_0_2 hix heq

    · exact allTwoLabel_case_0_3 hix heq

    · exact allTwoLabel_case_0_4 hix heq

    · exact allTwoLabel_case_0_5 hix heq

    · exact allTwoLabel_case_0_6 hix heq

    · exact allTwoLabel_case_0_7 hix heq

    · exact allTwoLabel_case_0_8 hix heq

    · exact allTwoLabel_case_0_9 hix heq

    · exact allTwoLabel_case_0_10 hix heq

  · rcases allTwo_index_cases d j hj with hjx | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl

    · exact (allTwoLabel_case_0_1 hjx heq.symm).symm

    · exact rfl

    · exact allTwoLabel_case_1_2 heq

    · exact allTwoLabel_case_1_3 heq

    · exact allTwoLabel_case_1_4 heq

    · exact allTwoLabel_case_1_5 heq

    · exact allTwoLabel_case_1_6 heq

    · exact allTwoLabel_case_1_7 heq

    · exact allTwoLabel_case_1_8 heq

    · exact allTwoLabel_case_1_9 heq

    · exact allTwoLabel_case_1_10 heq

  · rcases allTwo_index_cases d j hj with hjx | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl

    · exact (allTwoLabel_case_0_2 hjx heq.symm).symm

    · exact (allTwoLabel_case_1_2 heq.symm).symm

    · exact rfl

    · exact allTwoLabel_case_2_3 heq

    · exact allTwoLabel_case_2_4 heq

    · exact allTwoLabel_case_2_5 heq

    · exact allTwoLabel_case_2_6 heq

    · exact allTwoLabel_case_2_7 heq

    · exact allTwoLabel_case_2_8 heq

    · exact allTwoLabel_case_2_9 heq

    · exact allTwoLabel_case_2_10 heq

  · rcases allTwo_index_cases d j hj with hjx | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl

    · exact (allTwoLabel_case_0_3 hjx heq.symm).symm

    · exact (allTwoLabel_case_1_3 heq.symm).symm

    · exact (allTwoLabel_case_2_3 heq.symm).symm

    · exact rfl

    · exact allTwoLabel_case_3_4 heq

    · exact allTwoLabel_case_3_5 heq

    · exact allTwoLabel_case_3_6 heq

    · exact allTwoLabel_case_3_7 heq

    · exact allTwoLabel_case_3_8 heq

    · exact allTwoLabel_case_3_9 heq

    · exact allTwoLabel_case_3_10 heq

  · rcases allTwo_index_cases d j hj with hjx | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl

    · exact (allTwoLabel_case_0_4 hjx heq.symm).symm

    · exact (allTwoLabel_case_1_4 heq.symm).symm

    · exact (allTwoLabel_case_2_4 heq.symm).symm

    · exact (allTwoLabel_case_3_4 heq.symm).symm

    · exact rfl

    · exact allTwoLabel_case_4_5 heq

    · exact allTwoLabel_case_4_6 heq

    · exact allTwoLabel_case_4_7 heq

    · exact allTwoLabel_case_4_8 heq

    · exact allTwoLabel_case_4_9 heq

    · exact allTwoLabel_case_4_10 heq

  · rcases allTwo_index_cases d j hj with hjx | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl

    · exact (allTwoLabel_case_0_5 hjx heq.symm).symm

    · exact (allTwoLabel_case_1_5 heq.symm).symm

    · exact (allTwoLabel_case_2_5 heq.symm).symm

    · exact (allTwoLabel_case_3_5 heq.symm).symm

    · exact (allTwoLabel_case_4_5 heq.symm).symm

    · exact rfl

    · exact allTwoLabel_case_5_6 heq

    · exact allTwoLabel_case_5_7 heq

    · exact allTwoLabel_case_5_8 heq

    · exact allTwoLabel_case_5_9 heq

    · exact allTwoLabel_case_5_10 heq

  · rcases allTwo_index_cases d j hj with hjx | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl

    · exact (allTwoLabel_case_0_6 hjx heq.symm).symm

    · exact (allTwoLabel_case_1_6 heq.symm).symm

    · exact (allTwoLabel_case_2_6 heq.symm).symm

    · exact (allTwoLabel_case_3_6 heq.symm).symm

    · exact (allTwoLabel_case_4_6 heq.symm).symm

    · exact (allTwoLabel_case_5_6 heq.symm).symm

    · exact rfl

    · exact allTwoLabel_case_6_7 heq

    · exact allTwoLabel_case_6_8 heq

    · exact allTwoLabel_case_6_9 heq

    · exact allTwoLabel_case_6_10 heq

  · rcases allTwo_index_cases d j hj with hjx | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl

    · exact (allTwoLabel_case_0_7 hjx heq.symm).symm

    · exact (allTwoLabel_case_1_7 heq.symm).symm

    · exact (allTwoLabel_case_2_7 heq.symm).symm

    · exact (allTwoLabel_case_3_7 heq.symm).symm

    · exact (allTwoLabel_case_4_7 heq.symm).symm

    · exact (allTwoLabel_case_5_7 heq.symm).symm

    · exact (allTwoLabel_case_6_7 heq.symm).symm

    · exact rfl

    · exact allTwoLabel_case_7_8 heq

    · exact allTwoLabel_case_7_9 heq

    · exact allTwoLabel_case_7_10 heq

  · rcases allTwo_index_cases d j hj with hjx | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl

    · exact (allTwoLabel_case_0_8 hjx heq.symm).symm

    · exact (allTwoLabel_case_1_8 heq.symm).symm

    · exact (allTwoLabel_case_2_8 heq.symm).symm

    · exact (allTwoLabel_case_3_8 heq.symm).symm

    · exact (allTwoLabel_case_4_8 heq.symm).symm

    · exact (allTwoLabel_case_5_8 heq.symm).symm

    · exact (allTwoLabel_case_6_8 heq.symm).symm

    · exact (allTwoLabel_case_7_8 heq.symm).symm

    · exact rfl

    · exact allTwoLabel_case_8_9 heq

    · exact allTwoLabel_case_8_10 heq

  · rcases allTwo_index_cases d j hj with hjx | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl

    · exact (allTwoLabel_case_0_9 hjx heq.symm).symm

    · exact (allTwoLabel_case_1_9 heq.symm).symm

    · exact (allTwoLabel_case_2_9 heq.symm).symm

    · exact (allTwoLabel_case_3_9 heq.symm).symm

    · exact (allTwoLabel_case_4_9 heq.symm).symm

    · exact (allTwoLabel_case_5_9 heq.symm).symm

    · exact (allTwoLabel_case_6_9 heq.symm).symm

    · exact (allTwoLabel_case_7_9 heq.symm).symm

    · exact (allTwoLabel_case_8_9 heq.symm).symm

    · exact rfl

    · exact allTwoLabel_case_9_10 heq

  · rcases allTwo_index_cases d j hj with hjx | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl

    · exact (allTwoLabel_case_0_10 hjx heq.symm).symm

    · exact (allTwoLabel_case_1_10 heq.symm).symm

    · exact (allTwoLabel_case_2_10 heq.symm).symm

    · exact (allTwoLabel_case_3_10 heq.symm).symm

    · exact (allTwoLabel_case_4_10 heq.symm).symm

    · exact (allTwoLabel_case_5_10 heq.symm).symm

    · exact (allTwoLabel_case_6_10 heq.symm).symm

    · exact (allTwoLabel_case_7_10 heq.symm).symm

    · exact (allTwoLabel_case_8_10 heq.symm).symm

    · exact (allTwoLabel_case_9_10 heq.symm).symm

    · exact rfl

lemma allTwoLabel_bound {d j : ℕ} (hj : j ≤ d+10) : allTwoLabel d j ≤ d+10 := by
  rcases allTwo_index_cases d j hj with hjx | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp (discharger := omega) only [allTwoLabel, ite_eq_left, ite_eq_right,
    ite_true]
  all_goals try split_ifs
  all_goals omega


def allTwoDiff (d j : ℕ) : ℕ :=
  if j ≤ d then
    if j % 2 ≠ d % 2 then d+5-j
    else if j % 4 < 2 then d+11-j
    else Nat.dist (d+4) (j+5)
  else if j = d+1 then d+10-d%2
  else if j = d+2 then d+9-d%2
  else if j = d+3 then d+8-d%2
  else if j = d+4 then d+5-d%2
  else if j = d+5 then d+6-d%2
  else if j = d+6 then d+1-d%2
  else if j = d+7 then if d%4 < 2 then 2 else 4
  else if j = d+8 then if d%4 < 2 then 7 else 9
  else if j = d+9 then if d%4 < 2 then 4 else 2
  else if d%4 < 2 then 3 else 5




end Bounty
end

/- AllTwoArms -/
section
namespace Bounty

lemma allTwoLabel_diff_spine_0_0 {d j : ℕ} (hj : 0 < j) (hb : j ≤ d)
    (hdmod : d%4=0) (hjmod : j%4=0) :
    Nat.dist (allTwoLabel d (doubleSpiderParent 2 2 2 d 2 2 j)) (allTwoLabel d j) = allTwoDiff d j := by
  simp (discharger := omega) only [doubleSpiderParent, allTwoLabel, allTwoDiff,
    ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true]
  try split_ifs
  all_goals try simp only [Nat.dist]
  all_goals omega

lemma allTwoLabel_diff_spine_0_1 {d j : ℕ} (hj : 0 < j) (hb : j ≤ d)
    (hdmod : d%4=0) (hjmod : j%4=1) :
    Nat.dist (allTwoLabel d (doubleSpiderParent 2 2 2 d 2 2 j)) (allTwoLabel d j) = allTwoDiff d j := by
  simp (discharger := omega) only [doubleSpiderParent, allTwoLabel, allTwoDiff,
    ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true]
  try split_ifs
  all_goals try simp only [Nat.dist]
  all_goals omega

lemma allTwoLabel_diff_spine_0_2 {d j : ℕ} (hj : 0 < j) (hb : j ≤ d)
    (hdmod : d%4=0) (hjmod : j%4=2) :
    Nat.dist (allTwoLabel d (doubleSpiderParent 2 2 2 d 2 2 j)) (allTwoLabel d j) = allTwoDiff d j := by
  simp (discharger := omega) only [doubleSpiderParent, allTwoLabel, allTwoDiff,
    ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true]
  try split_ifs
  all_goals try simp only [Nat.dist]
  all_goals omega

lemma allTwoLabel_diff_spine_0_3 {d j : ℕ} (hj : 0 < j) (hb : j ≤ d)
    (hdmod : d%4=0) (hjmod : j%4=3) :
    Nat.dist (allTwoLabel d (doubleSpiderParent 2 2 2 d 2 2 j)) (allTwoLabel d j) = allTwoDiff d j := by
  simp (discharger := omega) only [doubleSpiderParent, allTwoLabel, allTwoDiff,
    ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true]
  try split_ifs
  all_goals try simp only [Nat.dist]
  all_goals omega

lemma allTwoLabel_diff_spine_1_0 {d j : ℕ} (hj : 0 < j) (hb : j ≤ d)
    (hdmod : d%4=1) (hjmod : j%4=0) :
    Nat.dist (allTwoLabel d (doubleSpiderParent 2 2 2 d 2 2 j)) (allTwoLabel d j) = allTwoDiff d j := by
  simp (discharger := omega) only [doubleSpiderParent, allTwoLabel, allTwoDiff,
    ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true]
  try split_ifs
  all_goals try simp only [Nat.dist]
  all_goals omega

lemma allTwoLabel_diff_spine_1_1 {d j : ℕ} (hj : 0 < j) (hb : j ≤ d)
    (hdmod : d%4=1) (hjmod : j%4=1) :
    Nat.dist (allTwoLabel d (doubleSpiderParent 2 2 2 d 2 2 j)) (allTwoLabel d j) = allTwoDiff d j := by
  simp (discharger := omega) only [doubleSpiderParent, allTwoLabel, allTwoDiff,
    ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true]
  try split_ifs
  all_goals try simp only [Nat.dist]
  all_goals omega

lemma allTwoLabel_diff_spine_1_2 {d j : ℕ} (hj : 0 < j) (hb : j ≤ d)
    (hdmod : d%4=1) (hjmod : j%4=2) :
    Nat.dist (allTwoLabel d (doubleSpiderParent 2 2 2 d 2 2 j)) (allTwoLabel d j) = allTwoDiff d j := by
  simp (discharger := omega) only [doubleSpiderParent, allTwoLabel, allTwoDiff,
    ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true]
  try split_ifs
  all_goals try simp only [Nat.dist]
  all_goals omega

lemma allTwoLabel_diff_spine_1_3 {d j : ℕ} (hj : 0 < j) (hb : j ≤ d)
    (hdmod : d%4=1) (hjmod : j%4=3) :
    Nat.dist (allTwoLabel d (doubleSpiderParent 2 2 2 d 2 2 j)) (allTwoLabel d j) = allTwoDiff d j := by
  simp (discharger := omega) only [doubleSpiderParent, allTwoLabel, allTwoDiff,
    ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true]
  try split_ifs
  all_goals try simp only [Nat.dist]
  all_goals omega

lemma allTwoLabel_diff_spine_2_0 {d j : ℕ} (hj : 0 < j) (hb : j ≤ d)
    (hdmod : d%4=2) (hjmod : j%4=0) :
    Nat.dist (allTwoLabel d (doubleSpiderParent 2 2 2 d 2 2 j)) (allTwoLabel d j) = allTwoDiff d j := by
  simp (discharger := omega) only [doubleSpiderParent, allTwoLabel, allTwoDiff,
    ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true]
  try split_ifs
  all_goals try simp only [Nat.dist]
  all_goals omega

lemma allTwoLabel_diff_spine_2_1 {d j : ℕ} (hj : 0 < j) (hb : j ≤ d)
    (hdmod : d%4=2) (hjmod : j%4=1) :
    Nat.dist (allTwoLabel d (doubleSpiderParent 2 2 2 d 2 2 j)) (allTwoLabel d j) = allTwoDiff d j := by
  simp (discharger := omega) only [doubleSpiderParent, allTwoLabel, allTwoDiff,
    ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true]
  try split_ifs
  all_goals try simp only [Nat.dist]
  all_goals omega

lemma allTwoLabel_diff_spine_2_2 {d j : ℕ} (hj : 0 < j) (hb : j ≤ d)
    (hdmod : d%4=2) (hjmod : j%4=2) :
    Nat.dist (allTwoLabel d (doubleSpiderParent 2 2 2 d 2 2 j)) (allTwoLabel d j) = allTwoDiff d j := by
  simp (discharger := omega) only [doubleSpiderParent, allTwoLabel, allTwoDiff,
    ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true]
  try split_ifs
  all_goals try simp only [Nat.dist]
  all_goals omega

lemma allTwoLabel_diff_spine_2_3 {d j : ℕ} (hj : 0 < j) (hb : j ≤ d)
    (hdmod : d%4=2) (hjmod : j%4=3) :
    Nat.dist (allTwoLabel d (doubleSpiderParent 2 2 2 d 2 2 j)) (allTwoLabel d j) = allTwoDiff d j := by
  simp (discharger := omega) only [doubleSpiderParent, allTwoLabel, allTwoDiff,
    ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true]
  try split_ifs
  all_goals try simp only [Nat.dist]
  all_goals omega

lemma allTwoLabel_diff_spine_3_0 {d j : ℕ} (hj : 0 < j) (hb : j ≤ d)
    (hdmod : d%4=3) (hjmod : j%4=0) :
    Nat.dist (allTwoLabel d (doubleSpiderParent 2 2 2 d 2 2 j)) (allTwoLabel d j) = allTwoDiff d j := by
  simp (discharger := omega) only [doubleSpiderParent, allTwoLabel, allTwoDiff,
    ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true]
  try split_ifs
  all_goals try simp only [Nat.dist]
  all_goals omega

lemma allTwoLabel_diff_spine_3_1 {d j : ℕ} (hj : 0 < j) (hb : j ≤ d)
    (hdmod : d%4=3) (hjmod : j%4=1) :
    Nat.dist (allTwoLabel d (doubleSpiderParent 2 2 2 d 2 2 j)) (allTwoLabel d j) = allTwoDiff d j := by
  simp (discharger := omega) only [doubleSpiderParent, allTwoLabel, allTwoDiff,
    ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true]
  try split_ifs
  all_goals try simp only [Nat.dist]
  all_goals omega

lemma allTwoLabel_diff_spine_3_2 {d j : ℕ} (hj : 0 < j) (hb : j ≤ d)
    (hdmod : d%4=3) (hjmod : j%4=2) :
    Nat.dist (allTwoLabel d (doubleSpiderParent 2 2 2 d 2 2 j)) (allTwoLabel d j) = allTwoDiff d j := by
  simp (discharger := omega) only [doubleSpiderParent, allTwoLabel, allTwoDiff,
    ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true]
  try split_ifs
  all_goals try simp only [Nat.dist]
  all_goals omega

lemma allTwoLabel_diff_spine_3_3 {d j : ℕ} (hj : 0 < j) (hb : j ≤ d)
    (hdmod : d%4=3) (hjmod : j%4=3) :
    Nat.dist (allTwoLabel d (doubleSpiderParent 2 2 2 d 2 2 j)) (allTwoLabel d j) = allTwoDiff d j := by
  simp (discharger := omega) only [doubleSpiderParent, allTwoLabel, allTwoDiff,
    ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true]
  try split_ifs
  all_goals try simp only [Nat.dist]
  all_goals omega

lemma allTwoLabel_diff_case_0 {d j : ℕ} (hj : 0 < j) (hb : j ≤ d) :
    Nat.dist (allTwoLabel d (doubleSpiderParent 2 2 2 d 2 2 j)) (allTwoLabel d j) = allTwoDiff d j := by
  have hdmod : d%4=0 ∨ d%4=1 ∨ d%4=2 ∨ d%4=3 := by omega
  have hjmod : j%4=0 ∨ j%4=1 ∨ j%4=2 ∨ j%4=3 := by omega
  rcases hdmod with hdmod | hdmod | hdmod | hdmod
  · rcases hjmod with hjmod | hjmod | hjmod | hjmod
    · exact allTwoLabel_diff_spine_0_0 hj hb hdmod hjmod
    · exact allTwoLabel_diff_spine_0_1 hj hb hdmod hjmod
    · exact allTwoLabel_diff_spine_0_2 hj hb hdmod hjmod
    · exact allTwoLabel_diff_spine_0_3 hj hb hdmod hjmod
  · rcases hjmod with hjmod | hjmod | hjmod | hjmod
    · exact allTwoLabel_diff_spine_1_0 hj hb hdmod hjmod
    · exact allTwoLabel_diff_spine_1_1 hj hb hdmod hjmod
    · exact allTwoLabel_diff_spine_1_2 hj hb hdmod hjmod
    · exact allTwoLabel_diff_spine_1_3 hj hb hdmod hjmod
  · rcases hjmod with hjmod | hjmod | hjmod | hjmod
    · exact allTwoLabel_diff_spine_2_0 hj hb hdmod hjmod
    · exact allTwoLabel_diff_spine_2_1 hj hb hdmod hjmod
    · exact allTwoLabel_diff_spine_2_2 hj hb hdmod hjmod
    · exact allTwoLabel_diff_spine_2_3 hj hb hdmod hjmod
  · rcases hjmod with hjmod | hjmod | hjmod | hjmod
    · exact allTwoLabel_diff_spine_3_0 hj hb hdmod hjmod
    · exact allTwoLabel_diff_spine_3_1 hj hb hdmod hjmod
    · exact allTwoLabel_diff_spine_3_2 hj hb hdmod hjmod
    · exact allTwoLabel_diff_spine_3_3 hj hb hdmod hjmod

lemma allTwoLabel_diff_case_1 {d : ℕ} :
    Nat.dist (allTwoLabel d (doubleSpiderParent 2 2 2 d 2 2 (d+1))) (allTwoLabel d (d+1)) = allTwoDiff d (d+1) := by
  simp (discharger := omega) only [doubleSpiderParent, allTwoLabel, allTwoDiff,
    ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true]
  try split_ifs
  all_goals try simp only [Nat.dist]
  all_goals omega

lemma allTwoLabel_diff_case_2 {d : ℕ} :
    Nat.dist (allTwoLabel d (doubleSpiderParent 2 2 2 d 2 2 (d+2))) (allTwoLabel d (d+2)) = allTwoDiff d (d+2) := by
  simp (discharger := omega) only [doubleSpiderParent, allTwoLabel, allTwoDiff,
    ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true]
  try split_ifs
  all_goals try simp only [Nat.dist]
  all_goals omega

lemma allTwoLabel_diff_case_3 {d : ℕ} :
    Nat.dist (allTwoLabel d (doubleSpiderParent 2 2 2 d 2 2 (d+3))) (allTwoLabel d (d+3)) = allTwoDiff d (d+3) := by
  simp (discharger := omega) only [doubleSpiderParent, allTwoLabel, allTwoDiff,
    ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true]
  try split_ifs
  all_goals try simp only [Nat.dist]
  all_goals omega

lemma allTwoLabel_diff_case_4 {d : ℕ} :
    Nat.dist (allTwoLabel d (doubleSpiderParent 2 2 2 d 2 2 (d+4))) (allTwoLabel d (d+4)) = allTwoDiff d (d+4) := by
  simp (discharger := omega) only [doubleSpiderParent, allTwoLabel, allTwoDiff,
    ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true]
  try split_ifs
  all_goals try simp only [Nat.dist]
  all_goals omega

lemma allTwoLabel_diff_case_5 {d : ℕ} :
    Nat.dist (allTwoLabel d (doubleSpiderParent 2 2 2 d 2 2 (d+5))) (allTwoLabel d (d+5)) = allTwoDiff d (d+5) := by
  simp (discharger := omega) only [doubleSpiderParent, allTwoLabel, allTwoDiff,
    ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true]
  try split_ifs
  all_goals try simp only [Nat.dist]
  all_goals omega

lemma allTwoLabel_diff_case_6 {d : ℕ} :
    Nat.dist (allTwoLabel d (doubleSpiderParent 2 2 2 d 2 2 (d+6))) (allTwoLabel d (d+6)) = allTwoDiff d (d+6) := by
  simp (discharger := omega) only [doubleSpiderParent, allTwoLabel, allTwoDiff,
    ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true]
  try split_ifs
  all_goals try simp only [Nat.dist]
  all_goals omega

lemma allTwoLabel_diff_case_7 {d : ℕ} :
    Nat.dist (allTwoLabel d (doubleSpiderParent 2 2 2 d 2 2 (d+7))) (allTwoLabel d (d+7)) = allTwoDiff d (d+7) := by
  simp (discharger := omega) only [doubleSpiderParent, allTwoLabel, allTwoDiff,
    ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true]
  try split_ifs
  all_goals try simp only [Nat.dist]
  all_goals omega

lemma allTwoLabel_diff_case_8 {d : ℕ} :
    Nat.dist (allTwoLabel d (doubleSpiderParent 2 2 2 d 2 2 (d+8))) (allTwoLabel d (d+8)) = allTwoDiff d (d+8) := by
  simp (discharger := omega) only [doubleSpiderParent, allTwoLabel, allTwoDiff,
    ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true]
  try split_ifs
  all_goals try simp only [Nat.dist]
  all_goals omega

lemma allTwoLabel_diff_case_9 {d : ℕ} :
    Nat.dist (allTwoLabel d (doubleSpiderParent 2 2 2 d 2 2 (d+9))) (allTwoLabel d (d+9)) = allTwoDiff d (d+9) := by
  simp (discharger := omega) only [doubleSpiderParent, allTwoLabel, allTwoDiff,
    ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true]
  try split_ifs
  all_goals try simp only [Nat.dist]
  all_goals omega

lemma allTwoLabel_diff_case_10 {d : ℕ} :
    Nat.dist (allTwoLabel d (doubleSpiderParent 2 2 2 d 2 2 (d+10))) (allTwoLabel d (d+10)) = allTwoDiff d (d+10) := by
  simp (discharger := omega) only [doubleSpiderParent, allTwoLabel, allTwoDiff,
    ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true]
  try split_ifs
  all_goals try simp only [Nat.dist]
  all_goals omega

lemma allTwoLabel_diff {d j : ℕ} (hj : 0 < j) (hb : j ≤ d+10) :
    Nat.dist (allTwoLabel d (doubleSpiderParent 2 2 2 d 2 2 j)) (allTwoLabel d j) = allTwoDiff d j := by
  rcases allTwo_index_cases d j hb with hjx | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact allTwoLabel_diff_case_0 hj hjx
  · exact allTwoLabel_diff_case_1
  · exact allTwoLabel_diff_case_2
  · exact allTwoLabel_diff_case_3
  · exact allTwoLabel_diff_case_4
  · exact allTwoLabel_diff_case_5
  · exact allTwoLabel_diff_case_6
  · exact allTwoLabel_diff_case_7
  · exact allTwoLabel_diff_case_8
  · exact allTwoLabel_diff_case_9
  · exact allTwoLabel_diff_case_10

lemma allTwoDiff_case_0_0 {d : ℕ} {i : ℕ} (hi : i ≤ d) {j : ℕ} (hj : j ≤ d) (hip : 0 < i) (hjp : 0 < j)
    (heq : allTwoDiff d i = allTwoDiff d j) : i = j := by
  simp (discharger := omega) only [allTwoDiff, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoDiff_case_0_1 {d : ℕ} {i : ℕ} (hi : i ≤ d) (hip : 0 < i)
    (heq : allTwoDiff d i = allTwoDiff d (d+1)) : i = (d+1) := by
  simp (discharger := omega) only [allTwoDiff, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoDiff_case_0_2 {d : ℕ} {i : ℕ} (hi : i ≤ d) (hip : 0 < i)
    (heq : allTwoDiff d i = allTwoDiff d (d+2)) : i = (d+2) := by
  simp (discharger := omega) only [allTwoDiff, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoDiff_case_0_3 {d : ℕ} {i : ℕ} (hi : i ≤ d) (hip : 0 < i)
    (heq : allTwoDiff d i = allTwoDiff d (d+3)) : i = (d+3) := by
  simp (discharger := omega) only [allTwoDiff, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoDiff_case_0_4 {d : ℕ} {i : ℕ} (hi : i ≤ d) (hip : 0 < i)
    (heq : allTwoDiff d i = allTwoDiff d (d+4)) : i = (d+4) := by
  simp (discharger := omega) only [allTwoDiff, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoDiff_case_0_5 {d : ℕ} {i : ℕ} (hi : i ≤ d) (hip : 0 < i)
    (heq : allTwoDiff d i = allTwoDiff d (d+5)) : i = (d+5) := by
  simp (discharger := omega) only [allTwoDiff, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoDiff_case_0_6 {d : ℕ} {i : ℕ} (hi : i ≤ d) (hip : 0 < i)
    (heq : allTwoDiff d i = allTwoDiff d (d+6)) : i = (d+6) := by
  simp (discharger := omega) only [allTwoDiff, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoDiff_case_0_7 {d : ℕ} {i : ℕ} (hi : i ≤ d) (hip : 0 < i)
    (heq : allTwoDiff d i = allTwoDiff d (d+7)) : i = (d+7) := by
  simp (discharger := omega) only [allTwoDiff, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoDiff_case_0_8 {d : ℕ} {i : ℕ} (hi : i ≤ d) (hip : 0 < i)
    (heq : allTwoDiff d i = allTwoDiff d (d+8)) : i = (d+8) := by
  simp (discharger := omega) only [allTwoDiff, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoDiff_case_0_9 {d : ℕ} {i : ℕ} (hi : i ≤ d) (hip : 0 < i)
    (heq : allTwoDiff d i = allTwoDiff d (d+9)) : i = (d+9) := by
  simp (discharger := omega) only [allTwoDiff, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoDiff_case_0_10 {d : ℕ} {i : ℕ} (hi : i ≤ d) (hip : 0 < i)
    (heq : allTwoDiff d i = allTwoDiff d (d+10)) : i = (d+10) := by
  simp (discharger := omega) only [allTwoDiff, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoDiff_case_1_2 {d : ℕ}
    (heq : allTwoDiff d (d+1) = allTwoDiff d (d+2)) : (d+1) = (d+2) := by
  simp (discharger := omega) only [allTwoDiff, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoDiff_case_1_3 {d : ℕ}
    (heq : allTwoDiff d (d+1) = allTwoDiff d (d+3)) : (d+1) = (d+3) := by
  simp (discharger := omega) only [allTwoDiff, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoDiff_case_1_4 {d : ℕ}
    (heq : allTwoDiff d (d+1) = allTwoDiff d (d+4)) : (d+1) = (d+4) := by
  simp (discharger := omega) only [allTwoDiff, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoDiff_case_1_5 {d : ℕ}
    (heq : allTwoDiff d (d+1) = allTwoDiff d (d+5)) : (d+1) = (d+5) := by
  simp (discharger := omega) only [allTwoDiff, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoDiff_case_1_6 {d : ℕ}
    (heq : allTwoDiff d (d+1) = allTwoDiff d (d+6)) : (d+1) = (d+6) := by
  simp (discharger := omega) only [allTwoDiff, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoDiff_case_1_7 {d : ℕ}
    (heq : allTwoDiff d (d+1) = allTwoDiff d (d+7)) : (d+1) = (d+7) := by
  simp (discharger := omega) only [allTwoDiff, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoDiff_case_1_8 {d : ℕ}
    (heq : allTwoDiff d (d+1) = allTwoDiff d (d+8)) : (d+1) = (d+8) := by
  simp (discharger := omega) only [allTwoDiff, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoDiff_case_1_9 {d : ℕ}
    (heq : allTwoDiff d (d+1) = allTwoDiff d (d+9)) : (d+1) = (d+9) := by
  simp (discharger := omega) only [allTwoDiff, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoDiff_case_1_10 {d : ℕ}
    (heq : allTwoDiff d (d+1) = allTwoDiff d (d+10)) : (d+1) = (d+10) := by
  simp (discharger := omega) only [allTwoDiff, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoDiff_case_2_3 {d : ℕ}
    (heq : allTwoDiff d (d+2) = allTwoDiff d (d+3)) : (d+2) = (d+3) := by
  simp (discharger := omega) only [allTwoDiff, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoDiff_case_2_4 {d : ℕ}
    (heq : allTwoDiff d (d+2) = allTwoDiff d (d+4)) : (d+2) = (d+4) := by
  simp (discharger := omega) only [allTwoDiff, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoDiff_case_2_5 {d : ℕ}
    (heq : allTwoDiff d (d+2) = allTwoDiff d (d+5)) : (d+2) = (d+5) := by
  simp (discharger := omega) only [allTwoDiff, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoDiff_case_2_6 {d : ℕ}
    (heq : allTwoDiff d (d+2) = allTwoDiff d (d+6)) : (d+2) = (d+6) := by
  simp (discharger := omega) only [allTwoDiff, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoDiff_case_2_7 {d : ℕ}
    (heq : allTwoDiff d (d+2) = allTwoDiff d (d+7)) : (d+2) = (d+7) := by
  simp (discharger := omega) only [allTwoDiff, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoDiff_case_2_8 {d : ℕ}
    (heq : allTwoDiff d (d+2) = allTwoDiff d (d+8)) : (d+2) = (d+8) := by
  simp (discharger := omega) only [allTwoDiff, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoDiff_case_2_9 {d : ℕ}
    (heq : allTwoDiff d (d+2) = allTwoDiff d (d+9)) : (d+2) = (d+9) := by
  simp (discharger := omega) only [allTwoDiff, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoDiff_case_2_10 {d : ℕ}
    (heq : allTwoDiff d (d+2) = allTwoDiff d (d+10)) : (d+2) = (d+10) := by
  simp (discharger := omega) only [allTwoDiff, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoDiff_case_3_4 {d : ℕ}
    (heq : allTwoDiff d (d+3) = allTwoDiff d (d+4)) : (d+3) = (d+4) := by
  simp (discharger := omega) only [allTwoDiff, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoDiff_case_3_5 {d : ℕ}
    (heq : allTwoDiff d (d+3) = allTwoDiff d (d+5)) : (d+3) = (d+5) := by
  simp (discharger := omega) only [allTwoDiff, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoDiff_case_3_6 {d : ℕ}
    (heq : allTwoDiff d (d+3) = allTwoDiff d (d+6)) : (d+3) = (d+6) := by
  simp (discharger := omega) only [allTwoDiff, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoDiff_case_3_7 {d : ℕ}
    (heq : allTwoDiff d (d+3) = allTwoDiff d (d+7)) : (d+3) = (d+7) := by
  simp (discharger := omega) only [allTwoDiff, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoDiff_case_3_8 {d : ℕ}
    (heq : allTwoDiff d (d+3) = allTwoDiff d (d+8)) : (d+3) = (d+8) := by
  simp (discharger := omega) only [allTwoDiff, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoDiff_case_3_9 {d : ℕ}
    (heq : allTwoDiff d (d+3) = allTwoDiff d (d+9)) : (d+3) = (d+9) := by
  simp (discharger := omega) only [allTwoDiff, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoDiff_case_3_10 {d : ℕ}
    (heq : allTwoDiff d (d+3) = allTwoDiff d (d+10)) : (d+3) = (d+10) := by
  simp (discharger := omega) only [allTwoDiff, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoDiff_case_4_5 {d : ℕ}
    (heq : allTwoDiff d (d+4) = allTwoDiff d (d+5)) : (d+4) = (d+5) := by
  simp (discharger := omega) only [allTwoDiff, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoDiff_case_4_6 {d : ℕ}
    (heq : allTwoDiff d (d+4) = allTwoDiff d (d+6)) : (d+4) = (d+6) := by
  simp (discharger := omega) only [allTwoDiff, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoDiff_case_4_7 {d : ℕ}
    (heq : allTwoDiff d (d+4) = allTwoDiff d (d+7)) : (d+4) = (d+7) := by
  simp (discharger := omega) only [allTwoDiff, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoDiff_case_4_8 {d : ℕ}
    (heq : allTwoDiff d (d+4) = allTwoDiff d (d+8)) : (d+4) = (d+8) := by
  simp (discharger := omega) only [allTwoDiff, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoDiff_case_4_9 {d : ℕ}
    (heq : allTwoDiff d (d+4) = allTwoDiff d (d+9)) : (d+4) = (d+9) := by
  simp (discharger := omega) only [allTwoDiff, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoDiff_case_4_10 {d : ℕ}
    (heq : allTwoDiff d (d+4) = allTwoDiff d (d+10)) : (d+4) = (d+10) := by
  simp (discharger := omega) only [allTwoDiff, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoDiff_case_5_6 {d : ℕ}
    (heq : allTwoDiff d (d+5) = allTwoDiff d (d+6)) : (d+5) = (d+6) := by
  simp (discharger := omega) only [allTwoDiff, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoDiff_case_5_7 {d : ℕ}
    (heq : allTwoDiff d (d+5) = allTwoDiff d (d+7)) : (d+5) = (d+7) := by
  simp (discharger := omega) only [allTwoDiff, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoDiff_case_5_8 {d : ℕ}
    (heq : allTwoDiff d (d+5) = allTwoDiff d (d+8)) : (d+5) = (d+8) := by
  simp (discharger := omega) only [allTwoDiff, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoDiff_case_5_9 {d : ℕ}
    (heq : allTwoDiff d (d+5) = allTwoDiff d (d+9)) : (d+5) = (d+9) := by
  simp (discharger := omega) only [allTwoDiff, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoDiff_case_5_10 {d : ℕ}
    (heq : allTwoDiff d (d+5) = allTwoDiff d (d+10)) : (d+5) = (d+10) := by
  simp (discharger := omega) only [allTwoDiff, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoDiff_case_6_7 {d : ℕ}
    (heq : allTwoDiff d (d+6) = allTwoDiff d (d+7)) : (d+6) = (d+7) := by
  simp (discharger := omega) only [allTwoDiff, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoDiff_case_6_8 {d : ℕ}
    (heq : allTwoDiff d (d+6) = allTwoDiff d (d+8)) : (d+6) = (d+8) := by
  simp (discharger := omega) only [allTwoDiff, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoDiff_case_6_9 {d : ℕ}
    (heq : allTwoDiff d (d+6) = allTwoDiff d (d+9)) : (d+6) = (d+9) := by
  simp (discharger := omega) only [allTwoDiff, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoDiff_case_6_10 {d : ℕ}
    (heq : allTwoDiff d (d+6) = allTwoDiff d (d+10)) : (d+6) = (d+10) := by
  simp (discharger := omega) only [allTwoDiff, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoDiff_case_7_8 {d : ℕ}
    (heq : allTwoDiff d (d+7) = allTwoDiff d (d+8)) : (d+7) = (d+8) := by
  simp (discharger := omega) only [allTwoDiff, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoDiff_case_7_9 {d : ℕ}
    (heq : allTwoDiff d (d+7) = allTwoDiff d (d+9)) : (d+7) = (d+9) := by
  simp (discharger := omega) only [allTwoDiff, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoDiff_case_7_10 {d : ℕ}
    (heq : allTwoDiff d (d+7) = allTwoDiff d (d+10)) : (d+7) = (d+10) := by
  simp (discharger := omega) only [allTwoDiff, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoDiff_case_8_9 {d : ℕ}
    (heq : allTwoDiff d (d+8) = allTwoDiff d (d+9)) : (d+8) = (d+9) := by
  simp (discharger := omega) only [allTwoDiff, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoDiff_case_8_10 {d : ℕ}
    (heq : allTwoDiff d (d+8) = allTwoDiff d (d+10)) : (d+8) = (d+10) := by
  simp (discharger := omega) only [allTwoDiff, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoDiff_case_9_10 {d : ℕ}
    (heq : allTwoDiff d (d+9) = allTwoDiff d (d+10)) : (d+9) = (d+10) := by
  simp (discharger := omega) only [allTwoDiff, ite_eq_left, ite_eq_right, ite_true, ite_false, true_or, or_true] at heq
  try split_ifs at heq
  all_goals try simp only [Nat.dist] at heq
  all_goals omega

lemma allTwoDiff_injective {d i j : ℕ} (hip : 0 < i) (hi : i ≤ d+10) (hjp : 0 < j) (hj : j ≤ d+10)
    (heq : allTwoDiff d i = allTwoDiff d j) : i=j := by

  rcases allTwo_index_cases d i hi with hix | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl

  · rcases allTwo_index_cases d j hj with hjx | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl

    · exact allTwoDiff_case_0_0 hix hjx hip hjp heq

    · exact allTwoDiff_case_0_1 hix hip heq

    · exact allTwoDiff_case_0_2 hix hip heq

    · exact allTwoDiff_case_0_3 hix hip heq

    · exact allTwoDiff_case_0_4 hix hip heq

    · exact allTwoDiff_case_0_5 hix hip heq

    · exact allTwoDiff_case_0_6 hix hip heq

    · exact allTwoDiff_case_0_7 hix hip heq

    · exact allTwoDiff_case_0_8 hix hip heq

    · exact allTwoDiff_case_0_9 hix hip heq

    · exact allTwoDiff_case_0_10 hix hip heq

  · rcases allTwo_index_cases d j hj with hjx | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl

    · exact (allTwoDiff_case_0_1 hjx hjp heq.symm).symm

    · exact rfl

    · exact allTwoDiff_case_1_2 heq

    · exact allTwoDiff_case_1_3 heq

    · exact allTwoDiff_case_1_4 heq

    · exact allTwoDiff_case_1_5 heq

    · exact allTwoDiff_case_1_6 heq

    · exact allTwoDiff_case_1_7 heq

    · exact allTwoDiff_case_1_8 heq

    · exact allTwoDiff_case_1_9 heq

    · exact allTwoDiff_case_1_10 heq

  · rcases allTwo_index_cases d j hj with hjx | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl

    · exact (allTwoDiff_case_0_2 hjx hjp heq.symm).symm

    · exact (allTwoDiff_case_1_2 heq.symm).symm

    · exact rfl

    · exact allTwoDiff_case_2_3 heq

    · exact allTwoDiff_case_2_4 heq

    · exact allTwoDiff_case_2_5 heq

    · exact allTwoDiff_case_2_6 heq

    · exact allTwoDiff_case_2_7 heq

    · exact allTwoDiff_case_2_8 heq

    · exact allTwoDiff_case_2_9 heq

    · exact allTwoDiff_case_2_10 heq

  · rcases allTwo_index_cases d j hj with hjx | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl

    · exact (allTwoDiff_case_0_3 hjx hjp heq.symm).symm

    · exact (allTwoDiff_case_1_3 heq.symm).symm

    · exact (allTwoDiff_case_2_3 heq.symm).symm

    · exact rfl

    · exact allTwoDiff_case_3_4 heq

    · exact allTwoDiff_case_3_5 heq

    · exact allTwoDiff_case_3_6 heq

    · exact allTwoDiff_case_3_7 heq

    · exact allTwoDiff_case_3_8 heq

    · exact allTwoDiff_case_3_9 heq

    · exact allTwoDiff_case_3_10 heq

  · rcases allTwo_index_cases d j hj with hjx | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl

    · exact (allTwoDiff_case_0_4 hjx hjp heq.symm).symm

    · exact (allTwoDiff_case_1_4 heq.symm).symm

    · exact (allTwoDiff_case_2_4 heq.symm).symm

    · exact (allTwoDiff_case_3_4 heq.symm).symm

    · exact rfl

    · exact allTwoDiff_case_4_5 heq

    · exact allTwoDiff_case_4_6 heq

    · exact allTwoDiff_case_4_7 heq

    · exact allTwoDiff_case_4_8 heq

    · exact allTwoDiff_case_4_9 heq

    · exact allTwoDiff_case_4_10 heq

  · rcases allTwo_index_cases d j hj with hjx | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl

    · exact (allTwoDiff_case_0_5 hjx hjp heq.symm).symm

    · exact (allTwoDiff_case_1_5 heq.symm).symm

    · exact (allTwoDiff_case_2_5 heq.symm).symm

    · exact (allTwoDiff_case_3_5 heq.symm).symm

    · exact (allTwoDiff_case_4_5 heq.symm).symm

    · exact rfl

    · exact allTwoDiff_case_5_6 heq

    · exact allTwoDiff_case_5_7 heq

    · exact allTwoDiff_case_5_8 heq

    · exact allTwoDiff_case_5_9 heq

    · exact allTwoDiff_case_5_10 heq

  · rcases allTwo_index_cases d j hj with hjx | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl

    · exact (allTwoDiff_case_0_6 hjx hjp heq.symm).symm

    · exact (allTwoDiff_case_1_6 heq.symm).symm

    · exact (allTwoDiff_case_2_6 heq.symm).symm

    · exact (allTwoDiff_case_3_6 heq.symm).symm

    · exact (allTwoDiff_case_4_6 heq.symm).symm

    · exact (allTwoDiff_case_5_6 heq.symm).symm

    · exact rfl

    · exact allTwoDiff_case_6_7 heq

    · exact allTwoDiff_case_6_8 heq

    · exact allTwoDiff_case_6_9 heq

    · exact allTwoDiff_case_6_10 heq

  · rcases allTwo_index_cases d j hj with hjx | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl

    · exact (allTwoDiff_case_0_7 hjx hjp heq.symm).symm

    · exact (allTwoDiff_case_1_7 heq.symm).symm

    · exact (allTwoDiff_case_2_7 heq.symm).symm

    · exact (allTwoDiff_case_3_7 heq.symm).symm

    · exact (allTwoDiff_case_4_7 heq.symm).symm

    · exact (allTwoDiff_case_5_7 heq.symm).symm

    · exact (allTwoDiff_case_6_7 heq.symm).symm

    · exact rfl

    · exact allTwoDiff_case_7_8 heq

    · exact allTwoDiff_case_7_9 heq

    · exact allTwoDiff_case_7_10 heq

  · rcases allTwo_index_cases d j hj with hjx | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl

    · exact (allTwoDiff_case_0_8 hjx hjp heq.symm).symm

    · exact (allTwoDiff_case_1_8 heq.symm).symm

    · exact (allTwoDiff_case_2_8 heq.symm).symm

    · exact (allTwoDiff_case_3_8 heq.symm).symm

    · exact (allTwoDiff_case_4_8 heq.symm).symm

    · exact (allTwoDiff_case_5_8 heq.symm).symm

    · exact (allTwoDiff_case_6_8 heq.symm).symm

    · exact (allTwoDiff_case_7_8 heq.symm).symm

    · exact rfl

    · exact allTwoDiff_case_8_9 heq

    · exact allTwoDiff_case_8_10 heq

  · rcases allTwo_index_cases d j hj with hjx | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl

    · exact (allTwoDiff_case_0_9 hjx hjp heq.symm).symm

    · exact (allTwoDiff_case_1_9 heq.symm).symm

    · exact (allTwoDiff_case_2_9 heq.symm).symm

    · exact (allTwoDiff_case_3_9 heq.symm).symm

    · exact (allTwoDiff_case_4_9 heq.symm).symm

    · exact (allTwoDiff_case_5_9 heq.symm).symm

    · exact (allTwoDiff_case_6_9 heq.symm).symm

    · exact (allTwoDiff_case_7_9 heq.symm).symm

    · exact (allTwoDiff_case_8_9 heq.symm).symm

    · exact rfl

    · exact allTwoDiff_case_9_10 heq

  · rcases allTwo_index_cases d j hj with hjx | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl

    · exact (allTwoDiff_case_0_10 hjx hjp heq.symm).symm

    · exact (allTwoDiff_case_1_10 heq.symm).symm

    · exact (allTwoDiff_case_2_10 heq.symm).symm

    · exact (allTwoDiff_case_3_10 heq.symm).symm

    · exact (allTwoDiff_case_4_10 heq.symm).symm

    · exact (allTwoDiff_case_5_10 heq.symm).symm

    · exact (allTwoDiff_case_6_10 heq.symm).symm

    · exact (allTwoDiff_case_7_10 heq.symm).symm

    · exact (allTwoDiff_case_8_10 heq.symm).symm

    · exact (allTwoDiff_case_9_10 heq.symm).symm

    · exact rfl

end Bounty
end

/- PathConstruction -/
section
namespace Bounty.PathConstruction

abbrev Symbol := Sum ℕ ℕ
abbrev L : ℕ → Symbol := Sum.inl
abbrev H : ℕ → Symbol := Sum.inr

def index : Symbol → ℕ
  | .inl i => i
  | .inr i => i

def Opposite : Symbol → Symbol → Prop
  | .inl _, .inr _ => True
  | .inr _, .inl _ => True
  | _, _ => False

def edgeSums : List Symbol → List ℕ
  | [] => []
  | [_] => []
  | x :: y :: xs => (index x + index y) :: edgeSums (y :: xs)

def bag {α : Type*} (xs : List α) : Multiset α := xs

theorem bag_nil {α : Type*} : bag ([] : List α) = 0 := rfl
theorem bag_cons {α : Type*} (x : α) (xs : List α) :
    bag (x :: xs) = {x} + bag xs := rfl
theorem bag_append {α : Type*} (xs ys : List α) :
    bag (xs ++ ys) = bag xs + bag ys := (Multiset.coe_add xs ys).symm

theorem edgeSums_append (P Q : List Symbol) (p q : Symbol) :
    P.getLast? = some p → Q.head? = some q →
    edgeSums (P ++ Q) = edgeSums P ++ [index p + index q] ++ edgeSums Q := by
  induction P with
  | nil => simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append]
  | cons x xs ih =>
    intro hp hq
    obtain ⟨ys, rfl⟩ := List.head?_eq_some_iff.mp hq
    cases xs with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at hp
      subst p
      rfl
    | cons y ys' =>
      have hp' : (y :: ys').getLast? = some p := by simpa [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append] using hp
      simpa only [List.cons_append, edgeSums, List.append_assoc] using
        congrArg (List.cons (index x + index y)) (ih hp' rfl)

abbrev edgeBag (P : List Symbol) : Multiset ℕ := bag (edgeSums P)

theorem edgeBag_append (P Q : List Symbol) (p q : Symbol)
    (hp : P.getLast? = some p) (hq : Q.head? = some q) :
    edgeBag (P ++ Q) = edgeBag P + {index p + index q} + edgeBag Q := by
  simp only [edgeBag, edgeSums_append P Q p q hp hq, bag_append, bag_cons, bag_nil, add_zero]

def lowBag (n : ℕ) : Multiset Symbol := bag ((List.range n).map L)
def highBag (n : ℕ) : Multiset Symbol := bag ((List.range n).map H)
def rangeBag (n : ℕ) : Multiset ℕ := bag (List.range n)

theorem lowBag_succ (n : ℕ) : lowBag (n+1) = lowBag n + {L n} := by
  simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, lowBag, List.range_succ]
theorem highBag_succ (n : ℕ) : highBag (n+1) = highBag n + {H n} := by
  simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, highBag, List.range_succ]
theorem rangeBag_succ (n : ℕ) : rangeBag (n+1) = rangeBag n + {n} := by
  simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, rangeBag, List.range_succ]

structure Core (a b : ℕ) (P Q : List Symbol) : Prop where
  main_start : P.head? = some (L 1)
  main_alternates : P.IsChain Opposite
  extra_alternates : Q.IsChain Opposite
  vertices : bag P + bag Q = lowBag (a+1) + highBag (b+1)
  edges : edgeBag P + edgeBag Q = rangeBag (a+b)

structure VH (a b : ℕ) (P Q : List Symbol) : Prop extends Core a b P Q where
  high_pos : 1 ≤ b
  main_end : P.getLast? = some (H b)
  extra_start : Q.head? = some (L a)
  extra_end : Q.getLast? = some (H (b-1))

structure VL (a b : ℕ) (P Q : List Symbol) : Prop extends Core a b P Q where
  low_pos : 1 ≤ a
  main_end : P.getLast? = some (L a)
  extra_start : Q.head? = some (L (a-1))
  extra_end : Q.getLast? = some (H b)

def vhMain (a b : ℕ) (P : List Symbol) := P ++ [L (a+2), H (b+3)]
def vhExtra (a b : ℕ) (Q : List Symbol) := [L (a+3), H (b+1)] ++ Q ++ [L (a+1), H (b+2)]
def vlMain (a b : ℕ) (P : List Symbol) := P ++ [H (b+2), L (a+3)]
def vlExtra (a b : ℕ) (Q : List Symbol) := [L (a+2), H (b+1)] ++ Q ++ [L (a+1), H (b+3)]

private theorem cycle_vertices (a b : ℕ) (P Q : List Symbol)
    (h : bag P + bag Q = lowBag (a+1) + highBag (b+1)) :
    bag (vhMain a b P) + bag (vhExtra a b Q) = lowBag (a+3+1) + highBag (b+3+1) := by
  have ha : a+3+1 = (a+1)+1+1+1 := by omega
  have hb : b+3+1 = (b+1)+1+1+1 := by omega
  rw [ha, hb]
  simp only [lowBag_succ, highBag_succ, vhMain, vhExtra, bag_append, bag_cons, bag_nil, add_zero]
  have h' := congrArg (fun x : Multiset Symbol =>
    x + {L (a+2)} + {H (b+3)} + {L (a+3)} + {H (b+1)} + {L (a+1)} + {H (b+2)}) h
  simp only [lowBag_succ, highBag_succ] at h'
  convert h' using 1 <;> ac_rfl

theorem vh_cycle (a b : ℕ) (P Q : List Symbol) (h : VH a b P Q) :
    VH (a+3) (b+3) (vhMain a b P) (vhExtra a b Q) := by
  have hmain : edgeBag (vhMain a b P) =
      edgeBag P + {a+b+2} + {a+b+5} := by
    rw [vhMain, edgeBag_append _ _ (H b) (L (a+2)) h.main_end rfl]
    have h1 : b+(a+2) = a+b+2 := by omega
    have h2 : a+2+(b+3) = a+b+5 := by omega
    simp only [edgeBag, edgeSums, index, bag_cons, bag_nil, add_zero, h1, h2]
  have hfront : ([L (a+3), H (b+1)] ++ Q).getLast? = some (H (b-1)) := by
    rw [List.getLast?_append, h.extra_end]
    rfl
  have hextra : edgeBag (vhExtra a b Q) =
      {a+b+4} + {a+b+1} + edgeBag Q + {a+b} + {a+b+3} := by
    rw [vhExtra, edgeBag_append _ _ (H (b-1)) (L (a+1)) hfront rfl]
    rw [edgeBag_append _ _ (H (b+1)) (L a) rfl h.extra_start]
    have hp := h.high_pos
    have h1 : a+3+(b+1) = a+b+4 := by omega
    have h2 : b+1+a = a+b+1 := by omega
    have h3 : b-1+(a+1) = a+b := by omega
    have h4 : a+1+(b+2) = a+b+3 := by omega
    simp only [edgeBag, edgeSums, index, bag_cons, bag_nil, add_zero, h1, h2, h3, h4]
  refine ⟨⟨?_, ?_, ?_, cycle_vertices a b P Q h.vertices, ?_⟩, by omega, ?_, ?_, ?_⟩
  · simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, vhMain, List.head?_append, h.main_start]
  · rw [vhMain, List.isChain_append]
    simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, h.main_alternates, h.main_end, Opposite, List.isChain_cons]
  · simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, vhExtra, List.isChain_append, List.isChain_cons, h.extra_alternates,
      h.extra_start, h.extra_end, List.getLast?_append, Opposite]
  · rw [hmain, hextra]
    have he := congrArg (fun x : Multiset ℕ =>
      x + {a+b} + {a+b+1} + {a+b+2} + {a+b+3} + {a+b+4} + {a+b+5}) h.edges
    have hh : a+3+(b+3) = (a+b)+1+1+1+1+1+1 := by omega
    rw [hh]
    simp only [rangeBag_succ]
    convert he using 1 <;> ac_rfl
  · simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, vhMain, List.getLast?_append]
  · simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, vhExtra, List.head?_append]
  · change ([L (a+3), H (b+1)] ++ Q ++ [L (a+1), H (b+2)]).getLast? = some (H (b+3-1))
    rw [List.getLast?_append]
    simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ]


private theorem cycle_vertices_vl (a b : ℕ) (P Q : List Symbol)
    (h : bag P + bag Q = lowBag (a+1) + highBag (b+1)) :
    bag (vlMain a b P) + bag (vlExtra a b Q) = lowBag (a+3+1) + highBag (b+3+1) := by
  simp only [lowBag_succ, highBag_succ, vlMain, vlExtra, bag_append, bag_cons, bag_nil, add_zero]
  have h' := congrArg (fun x : Multiset Symbol =>
    x + {H (b+2)} + {L (a+3)} + {L (a+2)} + {H (b+1)} + {L (a+1)} + {H (b+3)}) h
  simp only [lowBag_succ, highBag_succ] at h'
  convert h' using 1 <;> ac_rfl

theorem vl_cycle (a b : ℕ) (P Q : List Symbol) (h : VL a b P Q) :
    VL (a+3) (b+3) (vlMain a b P) (vlExtra a b Q) := by
  have hmain : edgeBag (vlMain a b P) =
      edgeBag P + {a+b+2} + {a+b+5} := by
    rw [vlMain, edgeBag_append _ _ (L a) (H (b+2)) h.main_end rfl]
    have h1 : a+(b+2) = a+b+2 := by omega
    have h2 : b+2+(a+3) = a+b+5 := by omega
    simp only [edgeBag, edgeSums, index, bag_cons, bag_nil, add_zero, h1, h2]
  have hfront : ([L (a+2), H (b+1)] ++ Q).getLast? = some (H b) := by
    rw [List.getLast?_append, h.extra_end]
    rfl
  have hextra : edgeBag (vlExtra a b Q) =
      {a+b+3} + {a+b} + edgeBag Q + {a+b+1} + {a+b+4} := by
    rw [vlExtra, edgeBag_append _ _ (H b) (L (a+1)) hfront rfl]
    rw [edgeBag_append _ _ (H (b+1)) (L (a-1)) rfl h.extra_start]
    have hp := h.low_pos
    have h1 : a+2+(b+1) = a+b+3 := by omega
    have h2 : b+1+(a-1) = a+b := by omega
    have h3 : b+(a+1) = a+b+1 := by omega
    have h4 : a+1+(b+3) = a+b+4 := by omega
    simp only [edgeBag, edgeSums, index, bag_cons, bag_nil, add_zero, h1, h2, h3, h4]
  refine ⟨⟨?_, ?_, ?_, cycle_vertices_vl a b P Q h.vertices, ?_⟩, by omega, ?_, ?_, ?_⟩
  · simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, vlMain, List.head?_append, h.main_start]
  · rw [vlMain, List.isChain_append]
    simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, h.main_alternates, h.main_end, Opposite, List.isChain_cons]
  · simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, vlExtra, List.isChain_append, List.isChain_cons, h.extra_alternates,
      h.extra_start, h.extra_end, Opposite]
  · rw [hmain, hextra]
    have he := congrArg (fun x : Multiset ℕ =>
      x + {a+b} + {a+b+1} + {a+b+2} + {a+b+3} + {a+b+4} + {a+b+5}) h.edges
    have hh : a+3+(b+3) = (a+b)+1+1+1+1+1+1 := by omega
    rw [hh]
    simp only [rangeBag_succ]
    convert he using 1 <;> ac_rfl
  · simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, vlMain, List.getLast?_append]
  · simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, vlExtra]
  · change ([L (a+2), H (b+1)] ++ Q ++ [L (a+1), H (b+3)]).getLast? = some (H (b+3))
    rw [List.getLast?_append]
    rfl

theorem vh_cycles (t a b : ℕ) (P Q : List Symbol) (h : VH a b P Q) :
    ∃ P' Q', VH (a+3*t) (b+3*t) P' Q' ∧
      P'.length = P.length+2*t ∧ Q'.length = Q.length+4*t := by
  induction t with
  | zero => exact ⟨P, Q, by simpa [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ] using h, by simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ], by simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ]⟩
  | succ t ih =>
    obtain ⟨P', Q', hi, hP, hQ⟩ := ih
    refine ⟨vhMain (a+3*t) (b+3*t) P', vhExtra (a+3*t) (b+3*t) Q', ?_, ?_, ?_⟩
    · convert vh_cycle (a+3*t) (b+3*t) P' Q' hi using 1 <;> omega
    · simp only [vhMain, List.length_append, List.length_cons, List.length_nil, hP]
      omega
    · simp only [vhExtra, List.length_append, List.length_cons, List.length_nil, hQ]
      omega

theorem vl_cycles (t a b : ℕ) (P Q : List Symbol) (h : VL a b P Q) :
    ∃ P' Q', VL (a+3*t) (b+3*t) P' Q' ∧
      P'.length = P.length+2*t ∧ Q'.length = Q.length+4*t := by
  induction t with
  | zero => exact ⟨P, Q, by simpa [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ] using h, by simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ], by simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ]⟩
  | succ t ih =>
    obtain ⟨P', Q', hi, hP, hQ⟩ := ih
    refine ⟨vlMain (a+3*t) (b+3*t) P', vlExtra (a+3*t) (b+3*t) Q', ?_, ?_, ?_⟩
    · convert vl_cycle (a+3*t) (b+3*t) P' Q' hi using 1 <;> omega
    · simp only [vlMain, List.length_append, List.length_cons, List.length_nil, hP]
      omega
    · simp only [vlExtra, List.length_append, List.length_cons, List.length_nil, hQ]
      omega


theorem bag_reverse {α : Type*} (P : List α) : bag P.reverse = bag P :=
  Multiset.coe_reverse P

theorem edgeSums_reverse (P : List Symbol) : edgeSums P.reverse = (edgeSums P).reverse := by
  induction P with
  | nil => rfl
  | cons x xs ih =>
    cases xs with
    | nil => rfl
    | cons y ys =>
      rw [List.reverse_cons, edgeSums_append _ _ y x (by simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse]) rfl, ih]
      simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, edgeSums, Nat.add_comm]

theorem edgeBag_reverse (P : List Symbol) : edgeBag P.reverse = edgeBag P := by
  simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, edgeBag, edgeSums_reverse]

theorem opposite_reverse (x y : Symbol) : Opposite y x ↔ Opposite x y := by
  cases x <;> cases y <;> rfl

theorem alternates_reverse (P : List Symbol) : P.reverse.IsChain Opposite ↔ P.IsChain Opposite := by
  rw [List.isChain_reverse]
  simp only [opposite_reverse]

structure Terminal (a b : ℕ) (P : List Symbol) : Prop where
  main_start : P.head? = some (L 1)
  alternates : P.IsChain Opposite
  vertices : bag P = lowBag (a+1) + highBag (b+1)
  edges : edgeBag P = rangeBag (a+b+1)

structure TL (a b : ℕ) (P : List Symbol) : Prop extends Terminal a b P where
  low_pos : 1 ≤ a
  main_end : P.getLast? = some (L (a-1))

structure TH (a b : ℕ) (P : List Symbol) : Prop extends Terminal a b P where
  high_pos : 1 ≤ b
  main_end : P.getLast? = some (H (b-1))

theorem vh_exit (a b : ℕ) (P Q : List Symbol) (h : VH a b P Q) :
    TH a b (P ++ Q) := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, h.high_pos, ?_⟩
  · simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, List.head?_append, h.main_start]
  · rw [List.isChain_append]
    simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, h.main_alternates, h.extra_alternates, h.main_end, h.extra_start, Opposite]
  · simpa [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse] using h.vertices
  · rw [edgeBag_append _ _ _ _ h.main_end h.extra_start]
    simp only [index]
    have he := congrArg (fun x : Multiset ℕ => x + {a+b}) h.edges
    rw [rangeBag_succ]
    convert he using 1 <;> simp only [Nat.add_comm b a] <;> ac_rfl
  · rw [List.getLast?_append, h.extra_end]
    rfl

theorem vl_exit (a b : ℕ) (P Q : List Symbol) (h : VL a b P Q) :
    TL a b (P ++ Q.reverse) := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, h.low_pos, ?_⟩
  · simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, List.head?_append, h.main_start]
  · rw [List.isChain_append]
    simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, h.main_alternates, h.extra_alternates, h.main_end, h.extra_end, Opposite]
  · simpa [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse] using h.vertices
  · rw [edgeBag_append _ _ (L a) (H b) h.main_end (by simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, h.extra_end])]
    simp only [index, edgeBag_reverse]
    have he := congrArg (fun x : Multiset ℕ => x + {a+b}) h.edges
    rw [rangeBag_succ]
    convert he using 1 <;> ac_rfl
  · rw [List.getLast?_append, List.getLast?_reverse, h.extra_start]
    rfl

def halfExtra (a b : ℕ) (Q : List Symbol) := [L (a+1)] ++ Q.reverse ++ [H (b+1)]

theorem vh_half (a b : ℕ) (P Q : List Symbol) (h : VH a b P Q) :
    VL (a+2) (b+1) (P ++ [L (a+2)]) (halfExtra a b Q) := by
  have hp := h.high_pos
  have hmain : edgeBag (P ++ [L (a+2)]) = edgeBag P + {a+b+2} := by
    rw [edgeBag_append _ _ (H b) (L (a+2)) h.main_end rfl]
    have hh : b+(a+2) = a+b+2 := by omega
    simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, edgeBag, edgeSums, index, hh]
  have hfront : ([L (a+1)] ++ Q.reverse).getLast? = some (L a) := by
    rw [List.getLast?_append, List.getLast?_reverse, h.extra_start]
    rfl
  have hextra : edgeBag (halfExtra a b Q) = {a+b} + edgeBag Q + {a+b+1} := by
    rw [halfExtra, edgeBag_append _ _ (L a) (H (b+1)) hfront rfl]
    rw [edgeBag_append _ _ (L (a+1)) (H (b-1)) rfl (by simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, h.extra_end])]
    have h1 : a+1+(b-1) = a+b := by omega
    have h2 : a+(b+1) = a+b+1 := by omega
    simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, edgeBag, edgeSums, index, edgeSums_reverse, h1, h2]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, by omega, ?_, ?_, ?_⟩
  · simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, List.head?_append, h.main_start]
  · rw [List.isChain_append]
    simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, h.main_alternates, h.main_end, Opposite]
  · rw [halfExtra, List.isChain_append]
    refine ⟨?_, by simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse], ?_⟩
    · rw [List.isChain_append]
      simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, h.extra_alternates, h.extra_end, Opposite]
    · rw [hfront]
      simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Opposite]
  · simp only [halfExtra, bag_append, bag_cons, bag_nil, add_zero, bag_reverse,
      lowBag_succ, highBag_succ]
    have hv := congrArg (fun x : Multiset Symbol => x + {L (a+1)} + {L (a+2)} + {H (b+1)}) h.vertices
    simp only [lowBag_succ, highBag_succ] at hv
    convert hv using 1 <;> ac_rfl
  · rw [hmain, hextra]
    have he := congrArg (fun x : Multiset ℕ => x + {a+b} + {a+b+1} + {a+b+2}) h.edges
    have heq : a+2+(b+1) = a+b+1+1+1 := by omega
    try rw [heq]
    simp only [rangeBag_succ]
    convert he using 1 <;> ac_rfl
  · simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse]
  · simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, halfExtra]
  · rw [halfExtra, List.getLast?_append]
    rfl

theorem vl_half (a b : ℕ) (P Q : List Symbol) (h : VL a b P Q) :
    VH (a+1) (b+2) (P ++ [H (b+2)]) (halfExtra a b Q) := by
  have hp := h.low_pos
  have hmain : edgeBag (P ++ [H (b+2)]) = edgeBag P + {a+b+2} := by
    rw [edgeBag_append _ _ (L a) (H (b+2)) h.main_end rfl]
    have hh : a+(b+2) = a+b+2 := by omega
    simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, edgeBag, edgeSums, index, hh]
  have hfront : ([L (a+1)] ++ Q.reverse).getLast? = some (L (a-1)) := by
    rw [List.getLast?_append, List.getLast?_reverse, h.extra_start]
    rfl
  have hextra : edgeBag (halfExtra a b Q) = {a+b+1} + edgeBag Q + {a+b} := by
    rw [halfExtra, edgeBag_append _ _ (L (a-1)) (H (b+1)) hfront rfl]
    rw [edgeBag_append _ _ (L (a+1)) (H b) rfl (by simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, h.extra_end])]
    have h1 : a+1+b = a+b+1 := by omega
    have h2 : a-1+(b+1) = a+b := by omega
    simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, edgeBag, edgeSums, index, edgeSums_reverse, h1, h2]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, by omega, ?_, ?_, ?_⟩
  · simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, List.head?_append, h.main_start]
  · rw [List.isChain_append]
    simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, h.main_alternates, h.main_end, Opposite]
  · rw [halfExtra, List.isChain_append]
    refine ⟨?_, by simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse], ?_⟩
    · rw [List.isChain_append]
      simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, h.extra_alternates, h.extra_end, Opposite]
    · rw [hfront]
      simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Opposite]
  · simp only [halfExtra, bag_append, bag_cons, bag_nil, add_zero, bag_reverse,
      lowBag_succ, highBag_succ]
    have hv := congrArg (fun x : Multiset Symbol => x + {L (a+1)} + {H (b+1)} + {H (b+2)}) h.vertices
    simp only [lowBag_succ, highBag_succ] at hv
    convert hv using 1 <;> ac_rfl
  · rw [hmain, hextra]
    have he := congrArg (fun x : Multiset ℕ => x + {a+b} + {a+b+1} + {a+b+2}) h.edges
    have heq : a+1+(b+2) = a+b+1+1+1 := by omega
    try rw [heq]
    simp only [rangeBag_succ]
    convert he using 1 <;> ac_rfl
  · simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse]
  · simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, halfExtra]
  · rw [halfExtra, List.getLast?_append]
    simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse]


theorem vh_exit_short (a b : ℕ) (P Q : List Symbol) (h : VH a b P Q) :
    TL (a+1) b (P ++ [L (a+1)] ++ Q.reverse) := by
  have hp := h.high_pos
  have hend : (P ++ [L (a+1)]).getLast? = some (L (a+1)) := by simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, by omega, ?_⟩
  · simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, List.head?_append, h.main_start]
  · rw [List.isChain_append]
    refine ⟨?_, by simpa [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse] using h.extra_alternates, ?_⟩
    · rw [List.isChain_append]
      simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, h.main_alternates, h.main_end, Opposite]
    · simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, hend, h.extra_end, Opposite]
  · simp only [bag_append, bag_cons, bag_nil, add_zero, bag_reverse, lowBag_succ, highBag_succ]
    have hv := congrArg (fun x : Multiset Symbol => x + {L (a+1)}) h.vertices
    simp only [lowBag_succ, highBag_succ] at hv
    convert hv using 1 <;> ac_rfl
  · rw [edgeBag_append _ _ (L (a+1)) (H (b-1)) hend (by simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, h.extra_end])]
    rw [edgeBag_append _ _ (H b) (L (a+1)) h.main_end rfl]
    have h1 : b+(a+1) = a+b+1 := by omega
    have h2 : a+1+(b-1) = a+b := by omega
    have heq : a+1+b+1 = a+b+1+1 := by omega
    simp only [edgeBag_reverse, edgeBag, edgeSums, index, bag_nil, add_zero, h1, h2]
    have he := congrArg (fun x : Multiset ℕ => x + {a+b} + {a+b+1}) h.edges
    try rw [heq]
    simp only [rangeBag_succ]
    convert he using 1 <;> ac_rfl
  · rw [List.getLast?_append, List.getLast?_reverse, h.extra_start]
    simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse]

theorem vl_exit_short (a b : ℕ) (P Q : List Symbol) (h : VL a b P Q) :
    TH a (b+1) (P ++ [H (b+1)] ++ Q) := by
  have hp := h.low_pos
  have hend : (P ++ [H (b+1)]).getLast? = some (H (b+1)) := by simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, by omega, ?_⟩
  · simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, List.head?_append, h.main_start]
  · rw [List.isChain_append]
    refine ⟨?_, h.extra_alternates, ?_⟩
    · rw [List.isChain_append]
      simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, h.main_alternates, h.main_end, Opposite]
    · simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, hend, h.extra_start, Opposite]
  · simp only [bag_append, bag_cons, bag_nil, add_zero, lowBag_succ, highBag_succ]
    have hv := congrArg (fun x : Multiset Symbol => x + {H (b+1)}) h.vertices
    simp only [lowBag_succ, highBag_succ] at hv
    convert hv using 1 <;> ac_rfl
  · rw [edgeBag_append _ _ (H (b+1)) (L (a-1)) hend h.extra_start]
    rw [edgeBag_append _ _ (L a) (H (b+1)) h.main_end rfl]
    have h1 : a+(b+1) = a+b+1 := by omega
    have h2 : b+1+(a-1) = a+b := by omega
    have heq : a+(b+1)+1 = a+b+1+1 := by omega
    simp only [edgeBag, edgeSums, index, bag_nil, add_zero, h1, h2]
    have he := congrArg (fun x : Multiset ℕ => x + {a+b} + {a+b+1}) h.edges
    try rw [heq]
    simp only [rangeBag_succ]
    convert he using 1 <;> ac_rfl
  · rw [List.getLast?_append, h.extra_end]
    simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse]

theorem tl_enter (a b : ℕ) (P : List Symbol) (h : TL a b P) :
    VH (a+1) (b+2) (P ++ [H (b+2)]) [L (a+1), H (b+1)] := by
  have hp := h.low_pos
  refine ⟨⟨?_, ?_, by simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, List.isChain_cons, Opposite], ?_, ?_⟩, by omega, by simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse], rfl, ?_⟩
  · simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, List.head?_append, h.main_start]
  · rw [List.isChain_append]
    simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, h.alternates, h.main_end, Opposite]
  · simp only [bag_append, bag_cons, bag_nil, add_zero, lowBag_succ, highBag_succ]
    have hv := congrArg (fun x : Multiset Symbol => x + {H (b+2)} + {L (a+1)} + {H (b+1)}) h.vertices
    simp only [lowBag_succ, highBag_succ] at hv
    convert hv using 1 <;> ac_rfl
  · rw [edgeBag_append _ _ (L (a-1)) (H (b+2)) h.main_end rfl]
    have h1 : a-1+(b+2) = a+b+1 := by omega
    have h2 : a+1+(b+1) = a+b+2 := by omega
    have heq : a+1+(b+2) = a+b+1+1+1 := by omega
    simp only [edgeBag, edgeSums, index, bag_nil, bag_cons, add_zero, h1, h2]
    have he := h.edges
    dsimp only [edgeBag] at he
    rw [he, heq]
    simp only [rangeBag_succ]
  · simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse]

theorem th_enter (a b : ℕ) (P : List Symbol) (h : TH a b P) :
    VL (a+2) (b+1) (P ++ [L (a+2)]) [L (a+1), H (b+1)] := by
  have hp := h.high_pos
  refine ⟨⟨?_, ?_, by simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, List.isChain_cons, Opposite], ?_, ?_⟩, by omega, by simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse], ?_, rfl⟩
  · simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, List.head?_append, h.main_start]
  · rw [List.isChain_append]
    simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, h.alternates, h.main_end, Opposite]
  · simp only [bag_append, bag_cons, bag_nil, add_zero, lowBag_succ, highBag_succ]
    have hv := congrArg (fun x : Multiset Symbol => x + {L (a+2)} + {L (a+1)} + {H (b+1)}) h.vertices
    simp only [lowBag_succ, highBag_succ] at hv
    convert hv using 1 <;> ac_rfl
  · rw [edgeBag_append _ _ (H (b-1)) (L (a+2)) h.main_end rfl]
    have h1 : b-1+(a+2) = a+b+1 := by omega
    have h2 : a+1+(b+1) = a+b+2 := by omega
    have heq : a+2+(b+1) = a+b+1+1+1 := by omega
    simp only [edgeBag, edgeSums, index, bag_nil, bag_cons, add_zero, h1, h2]
    have he := h.edges
    dsimp only [edgeBag] at he
    rw [he, heq]
    simp only [rangeBag_succ]
  · simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse]

theorem tl_extend (a b : ℕ) (P : List Symbol) (h : TL a b P) :
    TL (a+2) (b+2) (P ++ [H (b+2), L (a+2), H (b+1), L (a+1)]) := by
  simpa [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, List.append_assoc] using vh_exit_short _ _ _ _ (tl_enter a b P h)

theorem th_extend (a b : ℕ) (P : List Symbol) (h : TH a b P) :
    TH (a+2) (b+2) (P ++ [L (a+2), H (b+2), L (a+1), H (b+1)]) := by
  simpa [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, List.append_assoc] using vl_exit_short _ _ _ _ (th_enter a b P h)


theorem Terminal.length {a b : ℕ} {P : List Symbol} (h : Terminal a b P) :
    P.length = a+b+2 := by
  have hv := congrArg Multiset.card h.vertices
  simpa [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, bag, lowBag, highBag, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hv

theorem Terminal.vertex_perm {a b : ℕ} {P : List Symbol} (h : Terminal a b P) :
    P.Perm ((List.range (a+1)).map L ++ (List.range (b+1)).map H) := by
  apply Multiset.coe_eq_coe.mp
  simpa only [lowBag, highBag, bag, Multiset.coe_add] using h.vertices

theorem Terminal.edge_perm {a b : ℕ} {P : List Symbol} (h : Terminal a b P) :
    (edgeSums P).Perm (List.range (a+b+1)) := Multiset.coe_eq_coe.mp h.edges

theorem tl_extend_many (t a b : ℕ) (P : List Symbol) (h : TL a b P) :
    ∃ P', TL (a+2*t) (b+2*t) P' ∧ P'.length = P.length+4*t := by
  induction t with
  | zero => exact ⟨P, by simpa [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse] using h, by simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse]⟩
  | succ t ih =>
    obtain ⟨P', hi, hp⟩ := ih
    refine ⟨P' ++ [H (b+2*t+2), L (a+2*t+2), H (b+2*t+1), L (a+2*t+1)], ?_, ?_⟩
    · convert tl_extend _ _ _ hi using 1 <;> omega
    · simp only [List.length_append, List.length_cons, List.length_nil, hp]
      omega

theorem th_extend_many (t a b : ℕ) (P : List Symbol) (h : TH a b P) :
    ∃ P', TH (a+2*t) (b+2*t) P' ∧ P'.length = P.length+4*t := by
  induction t with
  | zero => exact ⟨P, by simpa [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse] using h, by simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse]⟩
  | succ t ih =>
    obtain ⟨P', hi, hp⟩ := ih
    refine ⟨P' ++ [L (a+2*t+2), H (b+2*t+2), L (a+2*t+1), H (b+2*t+1)], ?_, ?_⟩
    · convert th_extend _ _ _ hi using 1 <;> omega
    · simp only [List.length_append, List.length_cons, List.length_nil, hp]
      omega

theorem base3 : TL 1 0 [L 1, H 0, L 0] := by
  refine ⟨⟨rfl, by simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, List.isChain_cons, Opposite], by decide, by decide⟩, by decide, rfl⟩
theorem base4 : TH 1 1 [L 1, H 1, L 0, H 0] := by
  refine ⟨⟨rfl, by simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, List.isChain_cons, Opposite], by decide, by decide⟩, by decide, rfl⟩
theorem base6 : TH 2 2 [L 1, H 0, L 0, H 2, L 2, H 1] := by
  refine ⟨⟨rfl, by simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, List.isChain_cons, Opposite], by decide, by decide⟩, by decide, rfl⟩
theorem base9 : TL 4 3 [L 1, H 0, L 0, H 2, L 2, H 1, L 4, H 3, L 3] := by
  refine ⟨⟨rfl, by simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, List.isChain_cons, Opposite], by decide, by decide⟩, by decide, rfl⟩

theorem starting_odd (n : ℕ) (hn : 7 ≤ n) (ho : n%2 = 1) :
    ∃ a b P, TL a b P ∧ P.length = n := by
  have hmod : n%4 = 1 ∨ n%4 = 3 := by omega
  rcases hmod with h1 | h3
  · obtain ⟨P, hp, hlen⟩ := tl_extend_many ((n-9)/4) 4 3 _ base9
    refine ⟨_, _, P, hp, ?_⟩
    simp only [List.length_cons, List.length_nil] at hlen
    omega
  · obtain ⟨P, hp, hlen⟩ := tl_extend_many ((n-3)/4) 1 0 _ base3
    refine ⟨_, _, P, hp, ?_⟩
    simp only [List.length_cons, List.length_nil] at hlen
    omega

theorem starting_even (n : ℕ) (hn : 6 ≤ n) (ho : n%2 = 0) :
    ∃ a b P, TH a b P ∧ P.length = n := by
  have hmod : n%4 = 0 ∨ n%4 = 2 := by omega
  rcases hmod with h0 | h2
  · obtain ⟨P, hp, hlen⟩ := th_extend_many ((n-4)/4) 1 1 _ base4
    refine ⟨_, _, P, hp, ?_⟩
    simp only [List.length_cons, List.length_nil] at hlen
    omega
  · obtain ⟨P, hp, hlen⟩ := th_extend_many ((n-6)/4) 2 2 _ base6
    refine ⟨_, _, P, hp, ?_⟩
    simp only [List.length_cons, List.length_nil] at hlen
    omega


theorem get_append_boundary {α : Type*} (P Q : List α) :
    (P ++ Q)[P.length]? = Q.head? := by
  simp only [List.getElem?_append, lt_self_iff_false, ite_false, Nat.sub_self]
  cases Q <;> rfl

theorem get_append_last {α : Type*} (P Q : List α) (hp : 0 < P.length) :
    (P ++ Q)[P.length-1]? = P.getLast? := by
  rw [List.getElem?_append, ite_eq_left (by omega)]
  exact List.getLast?_eq_getElem?.symm

theorem Core.main_pos {a b : ℕ} {P Q : List Symbol} (h : Core a b P Q) :
    0 < P.length := by
  cases P with
  | nil => simpa [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse] using h.main_start
  | cons x xs => simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse]

def HasLow (n k : ℕ) : Prop :=
  ∃ a b P, Terminal a b P ∧ P.length = n ∧ P[k]? = some (L a)
def HasHigh (n k : ℕ) : Prop :=
  ∃ a b P, Terminal a b P ∧ P.length = n ∧ P[k]? = some (H b)

theorem vh_low_direct {a b : ℕ} {P Q : List Symbol} (h : VH a b P Q) :
    HasLow (P.length+Q.length) P.length := by
  refine ⟨a,b,P++Q,(vh_exit _ _ _ _ h).toTerminal, by simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse], ?_⟩
  simpa only [get_append_boundary] using h.extra_start

theorem vh_high_direct {a b : ℕ} {P Q : List Symbol} (h : VH a b P Q) :
    HasHigh (P.length+Q.length) (P.length-1) := by
  refine ⟨a,b,P++Q,(vh_exit _ _ _ _ h).toTerminal, by simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse], ?_⟩
  simpa only [get_append_last _ _ h.toCore.main_pos] using h.main_end

theorem vl_low_direct {a b : ℕ} {P Q : List Symbol} (h : VL a b P Q) :
    HasLow (P.length+Q.length) (P.length-1) := by
  refine ⟨a,b,P++Q.reverse,(vl_exit _ _ _ _ h).toTerminal, by simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse], ?_⟩
  simpa only [get_append_last _ _ h.toCore.main_pos] using h.main_end

theorem vl_high_direct {a b : ℕ} {P Q : List Symbol} (h : VL a b P Q) :
    HasHigh (P.length+Q.length) P.length := by
  refine ⟨a,b,P++Q.reverse,(vl_exit _ _ _ _ h).toTerminal, by simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse], ?_⟩
  simpa only [get_append_boundary, List.head?_reverse] using h.extra_end

theorem vl_low_short {a b : ℕ} {P Q : List Symbol} (h : VL a b P Q) :
    HasLow (P.length+Q.length+1) (P.length-1) := by
  refine ⟨a,b+1,P++[H (b+1)]++Q,(vl_exit_short _ _ _ _ h).toTerminal, ?_, ?_⟩
  · simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse]; omega
  · rw [List.append_assoc, get_append_last _ _ h.toCore.main_pos]
    exact h.main_end

theorem vl_high_short {a b : ℕ} {P Q : List Symbol} (h : VL a b P Q) :
    HasHigh (P.length+Q.length+1) P.length := by
  refine ⟨a,b+1,P++[H (b+1)]++Q,(vl_exit_short _ _ _ _ h).toTerminal, ?_, ?_⟩
  · simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse]; omega
  · rw [List.append_assoc, get_append_boundary]
    rfl

theorem vh_high_short {a b : ℕ} {P Q : List Symbol} (h : VH a b P Q) :
    HasHigh (P.length+Q.length+1) (P.length-1) := by
  refine ⟨a+1,b,P++[L (a+1)]++Q.reverse,(vh_exit_short _ _ _ _ h).toTerminal, ?_, ?_⟩
  · simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse]; omega
  · rw [List.append_assoc, get_append_last _ _ h.toCore.main_pos]
    exact h.main_end

theorem vh_low_long {a b : ℕ} {P Q : List Symbol} (h : VH a b P Q) :
    HasLow (P.length+Q.length+3) P.length := by
  have hh := vl_low_direct (vh_half _ _ _ _ h)
  simp only [List.length_append, List.length_cons, List.length_nil, List.length_reverse, halfExtra] at hh
  convert hh using 1 <;> (try simp only [List.length_append, List.length_cons, List.length_nil, List.length_reverse]) <;> omega

theorem vl_high_long {a b : ℕ} {P Q : List Symbol} (h : VL a b P Q) :
    HasHigh (P.length+Q.length+3) P.length := by
  have hh := vh_high_direct (vl_half _ _ _ _ h)
  simp only [List.length_append, List.length_cons, List.length_nil, List.length_reverse, halfExtra] at hh
  convert hh using 1 <;> (try simp only [List.length_append, List.length_cons, List.length_nil, List.length_reverse]) <;> omega

theorem prepared_odd (n t : ℕ) (hn : 7 ≤ n) (ho : n%2 = 1) :
    ∃ a b P Q, VH a b P Q ∧ P.length = n+1+2*t ∧ Q.length = 2+4*t := by
  obtain ⟨a,b,P,h,hlen⟩ := starting_odd n hn ho
  obtain ⟨P',Q',h',hP,hQ⟩ := vh_cycles t _ _ _ _ (tl_enter a b P h)
  refine ⟨_,_,P',Q',h',?_,?_⟩
  · simpa [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, hlen] using hP
  · simpa [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse] using hQ

theorem prepared_even (n t : ℕ) (hn : 6 ≤ n) (ho : n%2 = 0) :
    ∃ a b P Q, VL a b P Q ∧ P.length = n+1+2*t ∧ Q.length = 2+4*t := by
  obtain ⟨a,b,P,h,hlen⟩ := starting_even n hn ho
  obtain ⟨P',Q',h',hP,hQ⟩ := vl_cycles t _ _ _ _ (th_enter a b P h)
  refine ⟨_,_,P',Q',h',?_,?_⟩
  · simpa [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, hlen] using hP
  · simpa [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse] using hQ


/-- The symbolic form of Proposition 7: exact symbol and edge inventories,
    alternating sides, fixed first label, and the specified boundary position. -/
theorem symbolic_proposition7 (d c : ℕ) (hdpos : 1 ≤ d) (hcpos : 1 ≤ c)
    (hregion : c ≤ 2*d-16) :
    ∃ a b P, Terminal a b P ∧ P.length = d+c ∧
      P[d-1]? = some (if d%2 = 1 then L a else H b) := by
  let t := (c-1)/4
  have hc : c = 4*t + (c-1)%4 + 1 := by dsimp [t]; omega
  have hs : (c-1)%4 = 0 ∨ (c-1)%4 = 1 ∨ (c-1)%4 = 2 ∨ (c-1)%4 = 3 := by omega
  by_cases hd : d%2 = 1
  · simp only [ite_eq_left hd]
    change HasLow (d+c) (d-1)
    rcases hs with hs | hs | hs | hs
    · obtain ⟨a,b,P,Q,h,hP,hQ⟩ := prepared_odd (d-2-2*t) t (by omega) (by omega)
      have hr := vh_low_direct h
      rw [hP,hQ] at hr
      convert hr using 1 <;> omega
    · obtain ⟨a,b,P,Q,h,hP,hQ⟩ := prepared_even (d-1-2*t) t (by omega) (by omega)
      have hr := vl_low_direct h
      rw [hP,hQ] at hr
      convert hr using 1 <;> omega
    · obtain ⟨a,b,P,Q,h,hP,hQ⟩ := prepared_even (d-1-2*t) t (by omega) (by omega)
      have hr := vl_low_short h
      rw [hP,hQ] at hr
      convert hr using 1 <;> omega
    · obtain ⟨a,b,P,Q,h,hP,hQ⟩ := prepared_odd (d-2-2*t) t (by omega) (by omega)
      have hr := vh_low_long h
      rw [hP,hQ] at hr
      convert hr using 1 <;> omega
  · simp only [ite_eq_right hd]
    change HasHigh (d+c) (d-1)
    have hd0 : d%2 = 0 := by omega
    rcases hs with hs | hs | hs | hs
    · obtain ⟨a,b,P,Q,h,hP,hQ⟩ := prepared_even (d-2-2*t) t (by omega) (by omega)
      have hr := vl_high_direct h
      rw [hP,hQ] at hr
      convert hr using 1 <;> omega
    · obtain ⟨a,b,P,Q,h,hP,hQ⟩ := prepared_even (d-2-2*t) t (by omega) (by omega)
      have hr := vl_high_short h
      rw [hP,hQ] at hr
      convert hr using 1 <;> omega
    · obtain ⟨a,b,P,Q,h,hP,hQ⟩ := prepared_odd (d-1-2*t) t (by omega) (by omega)
      have hr := vh_high_short h
      rw [hP,hQ] at hr
      convert hr using 1 <;> omega
    · obtain ⟨a,b,P,Q,h,hP,hQ⟩ := prepared_even (d-2-2*t) t (by omega) (by omega)
      have hr := vl_high_long h
      rw [hP,hQ] at hr
      convert hr using 1 <;> omega

end Bounty.PathConstruction
end

/- Alpha -/
section
namespace Math15.Graceful

/-- Reverse the labels separately on the two sides of an alpha cut. -/
def reverseLabel (q k x : ℕ) : ℕ :=
  if x ≤ k then k - x else q + k + 1 - x

/-- Normalize the least high label to zero, swapping the two cut classes. -/
def normalizeHighLabel (q k x : ℕ) : ℕ :=
  if x ≤ k then q - k + x else x - k - 1

lemma reverseLabel_le {q k x : ℕ} (hk : k ≤ q) (hx : x ≤ q) :
    reverseLabel q k x ≤ q := by
  unfold reverseLabel
  split <;> omega

lemma reverseLabel_low_iff {q k x : ℕ} (hx : x ≤ q) :
    reverseLabel q k x ≤ k ↔ x ≤ k := by
  unfold reverseLabel
  split <;> omega

lemma reverseLabel_involutive {q k x : ℕ} (hx : x ≤ q) :
    reverseLabel q k (reverseLabel q k x) = x := by
  unfold reverseLabel
  split <;> split <;> omega

lemma reverseLabel_injective {q k x y : ℕ} (hx : x ≤ q) (hy : y ≤ q)
    (h : reverseLabel q k x = reverseLabel q k y) : x = y := by
  rw [← reverseLabel_involutive (k := k) hx, h, reverseLabel_involutive hy]

lemma reverseLabel_dist {q k x y : ℕ} (hx : x ≤ k) (hy : k < y) (hq : y ≤ q) :
    Nat.dist (reverseLabel q k x) (reverseLabel q k y) = q + 1 - Nat.dist x y := by
  simp only [reverseLabel, ite_eq_left hx, ite_eq_right (by omega : ¬ y ≤ k)]
  unfold Nat.dist
  omega

lemma normalizeHighLabel_le {q k x : ℕ} (hk : k < q) (hx : x ≤ q) :
    normalizeHighLabel q k x ≤ q := by
  unfold normalizeHighLabel
  split <;> omega

lemma normalizeHighLabel_low_iff {q k x : ℕ} (hk : k < q) (hx : x ≤ q) :
    normalizeHighLabel q k x ≤ q - k - 1 ↔ k < x := by
  unfold normalizeHighLabel
  split <;> omega

lemma normalizeHighLabel_injective {q k x y : ℕ} (hk : k < q)
    (hx : x ≤ q) (hy : y ≤ q)
    (h : normalizeHighLabel q k x = normalizeHighLabel q k y) : x = y := by
  unfold normalizeHighLabel at h
  split at h <;> split at h <;> omega

lemma normalizeHighLabel_dist {q k x y : ℕ} (hx : x ≤ k) (hy : k < y)
    (hq : y ≤ q) :
    Nat.dist (normalizeHighLabel q k x) (normalizeHighLabel q k y) =
      q + 1 - Nat.dist x y := by
  simp only [normalizeHighLabel, ite_eq_left hx, ite_eq_right (by omega : ¬ y ≤ k)]
  unfold Nat.dist
  omega

lemma reverseLabel_at_cut (q k : ℕ) : reverseLabel q k k = 0 := by
  simp [reverseLabel]

lemma normalizeHighLabel_at_cut (q k : ℕ) :
    normalizeHighLabel q k (k + 1) = 0 := by
  simp [normalizeHighLabel]

/-- A specified witness for the target's graceful-labeling predicate. -/
def IsGracefulLabeling {n : ℕ} (G : SimpleGraph (Fin n)) (f : Fin n → ℕ) : Prop :=
  Function.Injective f ∧
  (∀ v, f v ≤ edgeCount G) ∧
  (∀ d, 1 ≤ d → d ≤ edgeCount G →
    ∃! e : Fin n × Fin n, e.1 < e.2 ∧ G.Adj e.1 e.2 ∧ Nat.dist (f e.1) (f e.2) = d)

lemma IsGracefulLabeling.isGraceful {n : ℕ} {G : SimpleGraph (Fin n)}
    {f : Fin n → ℕ} (hf : IsGracefulLabeling G f) : IsGraceful G := ⟨f, hf⟩

/-- A graceful labeling whose every edge crosses the indicated cut. -/
def IsAlphaLabeling {n : ℕ} (G : SimpleGraph (Fin n)) (f : Fin n → ℕ) (k : ℕ) : Prop :=
  IsGracefulLabeling G f ∧ k < edgeCount G ∧
  ∀ u v, G.Adj u v → (f u ≤ k ∧ k < f v) ∨ (f v ≤ k ∧ k < f u)

lemma IsGracefulLabeling.dist_le {n : ℕ} {G : SimpleGraph (Fin n)}
    {f : Fin n → ℕ} (hf : IsGracefulLabeling G f) (u v : Fin n) :
    Nat.dist (f u) (f v) ≤ edgeCount G := by
  have hu := hf.2.1 u
  have hv := hf.2.1 v
  unfold Nat.dist
  omega

/-- Complementing all edge differences permutes the required interval of edge labels. -/
lemma IsGracefulLabeling.of_dist_complement {n : ℕ} {G : SimpleGraph (Fin n)}
    {f g : Fin n → ℕ} (hf : IsGracefulLabeling G f)
    (hg_inj : Function.Injective g) (hg_bound : ∀ v, g v ≤ edgeCount G)
    (hcomp : ∀ u v, G.Adj u v →
      Nat.dist (g u) (g v) = edgeCount G + 1 - Nat.dist (f u) (f v)) :
    IsGracefulLabeling G g := by
  refine ⟨hg_inj, hg_bound, ?_⟩
  intro d hd hq
  obtain ⟨e, he, he_unique⟩ := hf.2.2 (edgeCount G + 1 - d) (by omega) (by omega)
  refine ⟨e, ⟨he.1, he.2.1, ?_⟩, ?_⟩
  · rw [hcomp e.1 e.2 he.2.1, he.2.2]
    omega
  · intro e' he'
    apply he_unique e'
    refine ⟨he'.1, he'.2.1, ?_⟩
    have hc := hcomp e'.1 e'.2 he'.2.1
    have hb := hf.dist_le e'.1 e'.2
    omega

lemma IsAlphaLabeling.reverse {n : ℕ} {G : SimpleGraph (Fin n)}
    {f : Fin n → ℕ} {k : ℕ} (hf : IsAlphaLabeling G f k) :
    IsAlphaLabeling G (fun v => reverseLabel (edgeCount G) k (f v)) k := by
  rcases hf with ⟨hf, hk, hcross⟩
  refine ⟨hf.of_dist_complement ?_ ?_ ?_, hk, ?_⟩
  · intro u v h
    exact hf.1 (reverseLabel_injective (hf.2.1 u) (hf.2.1 v) h)
  · intro v
    exact reverseLabel_le (Nat.le_of_lt hk) (hf.2.1 v)
  · intro u v hadj
    rcases hcross u v hadj with h | h
    · exact reverseLabel_dist h.1 h.2 (hf.2.1 v)
    · rw [Nat.dist_comm (reverseLabel _ _ _), Nat.dist_comm (f u)]
      exact reverseLabel_dist h.1 h.2 (hf.2.1 u)
  · intro u v hadj
    rcases hcross u v hadj with h | h
    · left
      constructor
      · exact (reverseLabel_low_iff (hf.2.1 u)).2 h.1
      · have := (reverseLabel_low_iff (k := k) (hf.2.1 v))
        dsimp only at *
        omega
    · right
      constructor
      · exact (reverseLabel_low_iff (hf.2.1 v)).2 h.1
      · have := (reverseLabel_low_iff (k := k) (hf.2.1 u))
        dsimp only at *
        omega

lemma IsAlphaLabeling.normalizeHigh {n : ℕ} {G : SimpleGraph (Fin n)}
    {f : Fin n → ℕ} {k : ℕ} (hf : IsAlphaLabeling G f k) :
    IsAlphaLabeling G (fun v => normalizeHighLabel (edgeCount G) k (f v))
      (edgeCount G - k - 1) := by
  rcases hf with ⟨hf, hk, hcross⟩
  refine ⟨hf.of_dist_complement ?_ ?_ ?_, by omega, ?_⟩
  · intro u v h
    exact hf.1 (normalizeHighLabel_injective hk (hf.2.1 u) (hf.2.1 v) h)
  · intro v
    exact normalizeHighLabel_le hk (hf.2.1 v)
  · intro u v hadj
    rcases hcross u v hadj with h | h
    · exact normalizeHighLabel_dist h.1 h.2 (hf.2.1 v)
    · rw [Nat.dist_comm (normalizeHighLabel _ _ _), Nat.dist_comm (f u)]
      exact normalizeHighLabel_dist h.1 h.2 (hf.2.1 u)
  · intro u v hadj
    rcases hcross u v hadj with h | h
    · right
      constructor
      · exact (normalizeHighLabel_low_iff hk (hf.2.1 v)).2 h.2
      · have := (normalizeHighLabel_low_iff hk (hf.2.1 u))
        dsimp only at *
        omega
    · left
      constructor
      · exact (normalizeHighLabel_low_iff hk (hf.2.1 u)).2 h.2
      · have := (normalizeHighLabel_low_iff hk (hf.2.1 v))
        dsimp only at *
        omega

/-- Either boundary label can be moved to zero while retaining an alpha labeling. -/
lemma IsAlphaLabeling.normalizePin {n : ℕ} {G : SimpleGraph (Fin n)}
    {f : Fin n → ℕ} {k : ℕ} (hf : IsAlphaLabeling G f k) (v : Fin n)
    (hpin : f v = k ∨ f v = k + 1) :
    ∃ g k', IsAlphaLabeling G g k' ∧ g v = 0 := by
  rcases hpin with h | h
  · refine ⟨fun x => reverseLabel (edgeCount G) k (f x), k, hf.reverse, ?_⟩
    simp [h, reverseLabel_at_cut, normalizeHighLabel_at_cut]
  · refine ⟨fun x => normalizeHighLabel (edgeCount G) k (f x),
      edgeCount G - k - 1, hf.normalizeHigh, ?_⟩
    simp [h, reverseLabel_at_cut, normalizeHighLabel_at_cut]

/-- Insert a block of `m` unused labels immediately above an alpha cut. -/
def shiftAboveCut (k m x : ℕ) : ℕ := if x ≤ k then x else x + m

lemma shiftAboveCut_le {q k m x : ℕ} (hx : x ≤ q) :
    shiftAboveCut k m x ≤ q + m := by
  unfold shiftAboveCut
  split <;> omega

lemma shiftAboveCut_injective (k m : ℕ) : Function.Injective (shiftAboveCut k m) := by
  intro x y h
  unfold shiftAboveCut at h
  split at h <;> split at h <;> omega

lemma shiftAboveCut_dist {k m x y : ℕ} (hx : x ≤ k) (hy : k < y) :
    Nat.dist (shiftAboveCut k m x) (shiftAboveCut k m y) = m + Nat.dist x y := by
  simp only [shiftAboveCut, ite_eq_left hx, ite_eq_right (by omega : ¬ y ≤ k)]
  unfold Nat.dist
  omega

lemma translate_dist (k x y : ℕ) : Nat.dist (k + x) (k + y) = Nat.dist x y := by
  unfold Nat.dist
  omega

/-- After the shift, the inserted label interval meets the old labels only at the link. -/
lemma shiftAboveCut_eq_translate_iff {k m x y : ℕ} (hy : y ≤ m) :
    shiftAboveCut k m x = k + y ↔ x = k ∧ y = 0 := by
  unfold shiftAboveCut
  split <;> omega

lemma translate_le {q k m y : ℕ} (hk : k ≤ q) (hy : y ≤ m) : k + y ≤ q + m := by
  omega

/-- The two edge-label intervals in an amalgamation are disjoint. -/
lemma amalgamation_edge_intervals_disjoint {m d e : ℕ}
    (hd : 1 ≤ d) (he : e ≤ m) : m + d ≠ e := by
  omega

/-- The shifted graph's link and the inserted graph's zero label agree. -/
lemma shiftAboveCut_link (k m : ℕ) : shiftAboveCut k m k = k := by
  simp [shiftAboveCut]

/-- Appending a path can join the old low endpoint using the new difference `m`. -/
lemma appendPath_low_endpoint {k m b : ℕ} (hb : b ≤ k) (hm : k + 1 - b ≤ m) :
    k + 1 ≤ b + m ∧ b + m ≤ k + m ∧
      Nat.dist (shiftAboveCut k m b) (b + m) = m := by
  simp only [shiftAboveCut, ite_eq_left hb]
  unfold Nat.dist
  omega

/-- Appending a path can join the old high endpoint using the new difference `m`. -/
lemma appendPath_high_endpoint {k m b : ℕ} (hb : k < b) (hm : b - k ≤ m) :
    k + 1 ≤ b ∧ b ≤ k + m ∧
      Nat.dist (shiftAboveCut k m b) b = m := by
  simp only [shiftAboveCut, ite_eq_right (by omega : ¬ b ≤ k)]
  unfold Nat.dist
  omega

end Math15.Graceful
end

/- SpiderCertificates -/
section
namespace Bounty

/-- The parent of vertex `j` in the vertex order used for S(2,2,L). -/
def spiderParent (j : ℕ) : ℕ :=
  if j = 1 ∨ j = 3 ∨ j = 5 then 0 else j - 1

lemma spiderParent_lt {j : ℕ} (hj : 0 < j) : spiderParent j < j := by
  unfold spiderParent
  split <;> omega

/-- Vertices 0,1,2,3,4 are the hub and the two length-two arms. -/
def spider (L : ℕ) : SimpleGraph (Fin (L + 5)) where
  Adj i j := (i.val < j.val ∧ spiderParent j.val = i.val) ∨
    (j.val < i.val ∧ spiderParent i.val = j.val)
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by intro i; simp⟩

def spiderAdjDecidable (L : ℕ) : DecidableRel (spider L).Adj := fun _ _ => inferInstanceAs
  (Decidable ((_ ∧ _) ∨ (_ ∧ _)))


lemma spider_edgeCount (L : ℕ) : Math15.Graceful.edgeCount (spider L) = L + 4 := by
  classical
  unfold Math15.Graceful.edgeCount
  let es : Finset (Fin (L+5) × Fin (L+5)) := Finset.univ.filter
    (fun e => e.1 < e.2 ∧ (spider L).Adj e.1 e.2)
  let verts : Finset (Fin (L+5)) := Finset.univ.filter (fun j => 0 < j.val)
  have hc : es.card = verts.card := by
    apply Finset.card_bij (fun e _ => e.2)
    · intro e he
      simp only [es, Finset.mem_filter, Finset.mem_univ, true_and] at he
      simp only [verts, Finset.mem_filter, Finset.mem_univ, true_and]
      exact Nat.lt_of_le_of_lt (Nat.zero_le e.1.val) he.1
    · intro a ha b hb heq
      simp only [es, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      have hpa : spiderParent a.2.val = a.1.val := by
        rcases ha.2 with h | h
        · exact h.2
        · exact False.elim (Nat.lt_asymm ha.1 h.1)
      have hpb : spiderParent b.2.val = b.1.val := by
        rcases hb.2 with h | h
        · exact h.2
        · exact False.elim (Nat.lt_asymm hb.1 h.1)
      apply Prod.ext _ heq
      apply Fin.ext
      rw [← hpa, ← hpb, heq]
    · intro j hj
      simp only [verts, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      let i : Fin (L+5) := ⟨spiderParent j.val, (spiderParent_lt hj).trans j.isLt⟩
      refine ⟨(i,j), ?_, rfl⟩
      simp only [es, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨spiderParent_lt hj, Or.inl ⟨spiderParent_lt hj, rfl⟩⟩
  have hv : verts = Finset.univ.erase (0 : Fin (L+5)) := by
    ext j
    simp only [verts, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_erase, and_true]
    constructor
    · intro hj hzero
      subst j
      norm_num at hj
    · intro hj
      by_contra hzero
      apply hj
      apply Fin.ext
      have : j.val = 0 := by omega
      simpa using this
  have hcard : verts.card = L + 4 := by rw [hv]; simp
  calc
    _ = es.card := by rfl
    _ = L + 4 := hc.trans hcard

lemma spiderParent_le (j : ℕ) : spiderParent j ≤ j := by
  unfold spiderParent
  split <;> omega

def spiderParentFin {L : ℕ} (j : Fin (L+5)) : Fin (L+5) :=
  ⟨spiderParent j.val, (spiderParent_le j.val).trans_lt j.isLt⟩

def SpiderCertificate (L : ℕ) (f : Fin (L+5) → ℕ) : Prop :=
  Function.Injective f ∧ (∀ v, f v ≤ L+4) ∧
  ∀ i j : Fin (L+5), 0 < i.val → 0 < j.val →
    Nat.dist (f (spiderParentFin i)) (f i) =
      Nat.dist (f (spiderParentFin j)) (f j) → i = j

def spiderCertificateDecidable (L : ℕ) (f : Fin (L+5) → ℕ) : Decidable (SpiderCertificate L f) := by
  unfold SpiderCertificate Function.Injective
  infer_instance

theorem SpiderCertificate.isGracefulLabeling {L : ℕ} {f : Fin (L+5) → ℕ}
    (h : SpiderCertificate L f) : Math15.Graceful.IsGracefulLabeling (spider L) f := by
  apply Math15.Graceful.labeling_of_injective_differences _ f h.1
  · intro v
    rw [spider_edgeCount]
    exact h.2.1 v
  · intro e e' hlt he hlt' he' hsame
    have hp : spiderParentFin e.2 = e.1 := by
      apply Fin.ext
      rcases he with he | he
      · exact he.2
      · exact False.elim (Nat.lt_asymm hlt he.1)
    have hp' : spiderParentFin e'.2 = e'.1 := by
      apply Fin.ext
      rcases he' with he | he
      · exact he.2
      · exact False.elim (Nat.lt_asymm hlt' he.1)
    have hright : e.2 = e'.2 := by
      apply h.2.2 _ _ (Nat.lt_of_le_of_lt (Nat.zero_le _) hlt)
        (Nat.lt_of_le_of_lt (Nat.zero_le _) hlt')
      simpa only [hp, hp'] using hsame
    exact Prod.ext (hp.symm.trans ((congrArg spiderParentFin hright).trans hp')) hright

theorem SpiderCertificate.isGraceful {L : ℕ} {f : Fin (L+5) → ℕ}
    (h : SpiderCertificate L f) : Math15.Graceful.IsGraceful (spider L) :=
  h.isGracefulLabeling.isGraceful

end Bounty
end

/- Prefix -/
section
namespace Bounty

/-- A natural-index form of `SpiderCertificate`, with bounds stated explicitly. -/
def NatSpiderCertificate (L : ℕ) (f : ℕ → ℕ) : Prop :=
  (∀ i j, i < L + 5 → j < L + 5 → f i = f j → i = j) ∧
  (∀ i, i < L + 5 → f i ≤ L + 4) ∧
  ∀ i j, 0 < i → i < L + 5 → 0 < j → j < L + 5 →
    Nat.dist (f (spiderParent i)) (f i) = Nat.dist (f (spiderParent j)) (f j) → i = j

lemma NatSpiderCertificate.toCertificate {L : ℕ} {f : ℕ → ℕ}
    (hf : NatSpiderCertificate L f) : SpiderCertificate L (fun i => f i.val) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j heq
    exact Fin.ext (hf.1 i.val j.val i.isLt j.isLt heq)
  · intro i
    exact hf.2.1 i.val i.isLt
  · intro i j hi hj heq
    exact Fin.ext (hf.2.2 i.val j.val hi i.isLt hj j.isLt heq)

/-- The six prescribed initial labels of a canonical spider. -/
def CanonicalSpider (L : ℕ) (f : ℕ → ℕ) : Prop :=
  f 0 = 1 ∧ f 1 = L + 4 ∧ f 2 = 0 ∧ f 3 = L + 3 ∧ f 4 = 2 ∧ f 5 = L + 1

/-- Every parent edge crosses the cut. -/
def NatSpiderAlpha (L : ℕ) (f : ℕ → ℕ) (k : ℕ) : Prop :=
  ∀ j, 0 < j → j < L + 5 →
    (f (spiderParent j) ≤ k ∧ k < f j) ∨ (f j ≤ k ∧ k < f (spiderParent j))

/-- Insert the four-edge prefixExtend from Lemma 5 of the supplied manuscript. -/
def spiderPrefix (L : ℕ) (f : ℕ → ℕ) (j : ℕ) : ℕ :=
  if j = 0 then 1 else if j = 1 then L + 8 else if j = 2 then 0 else
  if j = 3 then L + 7 else if j = 4 then 2 else if j = 5 then L + 5 else
  if j = 6 then 4 else if j = 7 then L + 6 else if j = 8 then 3 else f (j - 4) + 2

lemma spiderPrefix_tail {L j : ℕ} (f : ℕ → ℕ) (hj : 9 ≤ j) :
    spiderPrefix L f j = f (j - 4) + 2 := by
  simp only [spiderPrefix]
  split_ifs <;> omega

lemma canonical_tail_bounds {L : ℕ} {f : ℕ → ℕ}
    (hf : NatSpiderCertificate L f) (hc : CanonicalSpider L f)
    {j : ℕ} (hj : 5 ≤ j) (hb : j < L + 5) : 3 ≤ f j ∧ f j ≤ L + 2 := by
  have hne (i : ℕ) (hi : i < 5) : f j ≠ f i := by
    intro heq
    have := hf.1 j i hb (by omega) heq
    omega
  have h0 := hne 0 (by omega)
  have h1 := hne 1 (by omega)
  have h2 := hne 2 (by omega)
  have h3 := hne 3 (by omega)
  have h4 := hne 4 (by omega)
  have hbound := hf.2.1 j hb
  rcases hc with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  omega

lemma spiderPrefix_injective {L : ℕ} {f : ℕ → ℕ} (_hL : 1 ≤ L)
    (hf : NatSpiderCertificate L f) (hc : CanonicalSpider L f)
    {i j : ℕ} (hi : i < L + 9) (hj : j < L + 9)
    (heq : spiderPrefix L f i = spiderPrefix L f j) : i = j := by
  by_cases hi9 : i < 9 <;> by_cases hj9 : j < 9
  · interval_cases i <;> interval_cases j <;> simp [spiderPrefix] at heq ⊢
  · have htail := canonical_tail_bounds hf hc (j := j - 4) (by omega) (by omega)
    rw [spiderPrefix_tail (j := j) f (by omega)] at heq
    interval_cases i <;> simp [spiderPrefix] at heq <;> omega
  · have htail := canonical_tail_bounds hf hc (j := i - 4) (by omega) (by omega)
    rw [spiderPrefix_tail f (by omega)] at heq
    interval_cases j <;> simp [spiderPrefix] at heq <;> omega
  · rw [spiderPrefix_tail f (by omega), spiderPrefix_tail f (by omega)] at heq
    have := hf.1 (i - 4) (j - 4) (by omega) (by omega) (by omega)
    omega

lemma spiderPrefix_bound {L : ℕ} {f : ℕ → ℕ}
    (hf : NatSpiderCertificate L f) {i : ℕ} (hi : i < L + 9) :
    spiderPrefix L f i ≤ L + 8 := by
  by_cases hi9 : i < 9
  · interval_cases i <;> simp [spiderPrefix]
  · rw [spiderPrefix_tail f (by omega)]
    have := hf.2.1 (i - 4) (by omega)
    omega

/-- The old edge represented by a new edge after the four newly largest differences. -/
def prefixOldEdge (j : ℕ) : ℕ :=
  if j = 5 then 2 else if j = 6 then 4 else if j = 7 then 3 else if j = 8 then 1 else j - 4

lemma prefixOldEdge_bounds {L j : ℕ} (hL : 1 ≤ L) (hj : 5 ≤ j) (hb : j < L + 9) :
    0 < prefixOldEdge j ∧ prefixOldEdge j < L + 5 := by
  unfold prefixOldEdge
  split_ifs <;> omega

lemma prefixOldEdge_injective {i j : ℕ} (hi : 5 ≤ i) (hj : 5 ≤ j)
    (h : prefixOldEdge i = prefixOldEdge j) : i = j := by
  unfold prefixOldEdge at h
  split_ifs at h <;> omega

lemma spiderPrefix_parent_tail {L j : ℕ} {f : ℕ → ℕ}
    (hc : CanonicalSpider L f) (hj : 9 ≤ j) :
    spiderPrefix L f (spiderParent j) = f (spiderParent (j - 4)) + 2 := by
  rcases eq_or_lt_of_le hj with rfl | hj
  · simp [spiderParent, spiderPrefix, hc.1]
  · have hp : spiderParent j = j - 1 := by
      unfold spiderParent
      split_ifs <;> omega
    have hp' : spiderParent (j - 4) = j - 5 := by
      unfold spiderParent
      split_ifs <;> omega
    rw [hp, spiderPrefix_tail f (by omega), hp']
    congr 2

lemma spiderPrefix_edge {L j : ℕ} {f : ℕ → ℕ}
    (hc : CanonicalSpider L f) (hj : 5 ≤ j) :
    Nat.dist (spiderPrefix L f (spiderParent j)) (spiderPrefix L f j) =
      Nat.dist (f (spiderParent (prefixOldEdge j))) (f (prefixOldEdge j)) := by
  by_cases h9 : j < 9
  · rcases hc with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
    interval_cases j <;> simp [spiderParent, spiderPrefix, prefixOldEdge, hc0, hc1, hc2, hc3, hc4, Nat.dist]
  · have hm : prefixOldEdge j = j - 4 := by
      unfold prefixOldEdge
      split_ifs <;> omega
    rw [spiderPrefix_parent_tail hc (by omega), spiderPrefix_tail f (by omega), hm]
    unfold Nat.dist
    omega

lemma NatSpiderCertificate.edge_bound {L : ℕ} {f : ℕ → ℕ}
    (hf : NatSpiderCertificate L f) {j : ℕ} (hj : j < L + 5) :
    Nat.dist (f (spiderParent j)) (f j) ≤ L + 4 := by
  have h1 := hf.2.1 j hj
  have h2 := hf.2.1 (spiderParent j) ((spiderParent_le j).trans_lt hj)
  unfold Nat.dist
  omega

lemma spiderPrefix_high_edge {L j : ℕ} (f : ℕ → ℕ) (hj : 0 < j) (hb : j < 5) :
    L + 4 < Nat.dist (spiderPrefix L f (spiderParent j)) (spiderPrefix L f j) := by
  interval_cases j <;> simp [spiderParent, spiderPrefix, Nat.dist]

lemma spiderPrefix_low_edge {L j : ℕ} {f : ℕ → ℕ} (hL : 1 ≤ L)
    (hf : NatSpiderCertificate L f) (hc : CanonicalSpider L f)
    (hj : 5 ≤ j) (hb : j < L + 9) :
    Nat.dist (spiderPrefix L f (spiderParent j)) (spiderPrefix L f j) ≤ L + 4 := by
  rw [spiderPrefix_edge hc hj]
  exact hf.edge_bound (prefixOldEdge_bounds hL hj hb).2

lemma NatSpiderCertificate.prefixExtend {L : ℕ} {f : ℕ → ℕ} (hL : 1 ≤ L)
    (hf : NatSpiderCertificate L f) (hc : CanonicalSpider L f) :
    NatSpiderCertificate (L + 4) (spiderPrefix L f) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j hi hj heq
    exact spiderPrefix_injective hL hf hc (by omega) (by omega) heq
  · intro i hi
    exact spiderPrefix_bound hf (by omega)
  · intro i j hi hib hj hjb heq
    by_cases hi5 : i < 5 <;> by_cases hj5 : j < 5
    · interval_cases i <;> interval_cases j <;>
        simp [spiderParent, spiderPrefix, Nat.dist] at heq ⊢
    · have hhigh := spiderPrefix_high_edge (L := L) f hi hi5
      have hlow := spiderPrefix_low_edge hL hf hc (by omega : 5 ≤ j) (by omega)
      omega
    · have hhigh := spiderPrefix_high_edge (L := L) f hj hj5
      have hlow := spiderPrefix_low_edge hL hf hc (by omega : 5 ≤ i) (by omega)
      omega
    · rw [spiderPrefix_edge hc (by omega), spiderPrefix_edge hc (by omega)] at heq
      have hbi := prefixOldEdge_bounds hL (by omega : 5 ≤ i) (by omega : i < L + 9)
      have hbj := prefixOldEdge_bounds hL (by omega : 5 ≤ j) (by omega : j < L + 9)
      have hm := hf.2.2 (prefixOldEdge i) (prefixOldEdge j) hbi.1 hbi.2 hbj.1 hbj.2 heq
      exact prefixOldEdge_injective (by omega) (by omega) hm

lemma CanonicalSpider.prefixExtend {L : ℕ} {f : ℕ → ℕ} :
    CanonicalSpider (L + 4) (spiderPrefix L f) := by
  simp [CanonicalSpider, spiderPrefix]

lemma NatSpiderAlpha.prefixExtend {L k : ℕ} {f : ℕ → ℕ}
    (hc : CanonicalSpider L f) (hα : NatSpiderAlpha L f k)
    (hk0 : 2 ≤ k) (hk1 : k < L + 3) :
    NatSpiderAlpha (L + 4) (spiderPrefix L f) (k + 2) := by
  intro j hj hb
  by_cases h9 : j < 9
  · interval_cases j <;> simp [spiderParent, spiderPrefix] <;> omega
  · have hm : 0 < j - 4 := by omega
    have hmb : j - 4 < L + 5 := by omega
    have hcross := hα (j - 4) hm hmb
    rw [spiderPrefix_parent_tail hc (by omega), spiderPrefix_tail f (by omega)]
    omega

lemma spiderPrefix_pin {L d : ℕ} {f : ℕ → ℕ} (hd : 1 ≤ d)
    (hpin : f (4 + d) = 2 + L / 2 + d % 2) :
    spiderPrefix L f (4 + (d + 4)) = 2 + (L + 4) / 2 + (d + 4) % 2 := by
  rw [spiderPrefix_tail f (by omega), show 4 + (d + 4) - 4 = 4 + d by omega, hpin]
  omega

/-- Canonical alpha certificates with the boundary label required at the pin. -/
def CanonicalPinnedSpider (L d : ℕ) (f : ℕ → ℕ) : Prop :=
  NatSpiderCertificate L f ∧ CanonicalSpider L f ∧
  NatSpiderAlpha L f (2 + L / 2) ∧ f (4 + d) = 2 + L / 2 + d % 2

/-- Lemma 5: adding the four-edge prefixExtend increases the long leg and pin position by four. -/
theorem CanonicalPinnedSpider.prefixExtend {L d : ℕ} {f : ℕ → ℕ}
    (hL : 1 ≤ L) (hd : 1 ≤ d) (hf : CanonicalPinnedSpider L d f) :
    CanonicalPinnedSpider (L + 4) (d + 4) (spiderPrefix L f) := by
  refine ⟨hf.1.prefixExtend hL hf.2.1, CanonicalSpider.prefixExtend, ?_, spiderPrefix_pin hd hf.2.2.2⟩
  have ha := hf.2.2.1.prefixExtend hf.2.1 (by omega) (by omega)
  have hk : 2 + (L + 4) / 2 = (2 + L / 2) + 2 := by omega
  rwa [hk]

lemma NatSpiderAlpha.toAlphaLabeling {L k : ℕ} {f : ℕ → ℕ}
    (hf : NatSpiderCertificate L f) (hα : NatSpiderAlpha L f k) (hk : k < L + 4) :
    Math15.Graceful.IsAlphaLabeling (spider L) (fun i => f i.val) k := by
  refine ⟨hf.toCertificate.isGracefulLabeling, ?_, ?_⟩
  · rwa [spider_edgeCount]
  · intro u v hadj
    change (f u.val ≤ k ∧ k < f v.val) ∨ (f v.val ≤ k ∧ k < f u.val)
    rcases hadj with h | h
    · have hc := hα v.val (by omega) v.isLt
      rwa [h.2] at hc
    · have hc := hα u.val (by omega) u.isLt
      rw [h.2] at hc
      exact hc.symm

/-- Extend a finite certificate by zero outside its vertex interval. -/
def extendSpiderLabel {L : ℕ} (f : Fin (L + 5) → ℕ) (j : ℕ) : ℕ :=
  if hj : j < L + 5 then f ⟨j, hj⟩ else 0

lemma extendSpiderLabel_at {L : ℕ} (f : Fin (L + 5) → ℕ) (j : Fin (L + 5)) :
    extendSpiderLabel f j.val = f j := by
  simp [extendSpiderLabel]

lemma SpiderCertificate.toNat {L : ℕ} {f : Fin (L + 5) → ℕ}
    (hf : SpiderCertificate L f) : NatSpiderCertificate L (extendSpiderLabel f) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j hi hj heq
    simp only [extendSpiderLabel, dite_eq_left hi, dite_eq_left hj] at heq
    exact congrArg Fin.val (hf.1 heq)
  · intro i hi
    simpa only [extendSpiderLabel, dite_eq_left hi] using hf.2.1 ⟨i, hi⟩
  · intro i j hi hib hj hjb heq
    have hpi := (spiderParent_le i).trans_lt hib
    have hpj := (spiderParent_le j).trans_lt hjb
    simp only [extendSpiderLabel, dite_eq_left hib, dite_eq_left hjb,
      dite_eq_left hpi, dite_eq_left hpj] at heq
    exact congrArg Fin.val (hf.2.2 ⟨i, hib⟩ ⟨j, hjb⟩ hi hj heq)

/-- Repeated prefixes give an actual label function, not just an existence assertion. -/
def iterateSpiderPrefix (L : ℕ) (f : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0 => f
  | t + 1 => spiderPrefix (L + 4 * t) (iterateSpiderPrefix L f t)

theorem CanonicalPinnedSpider.iterate {L d : ℕ} {f : ℕ → ℕ}
    (hL : 1 ≤ L) (hd : 1 ≤ d) (hf : CanonicalPinnedSpider L d f) (t : ℕ) :
    CanonicalPinnedSpider (L + 4 * t) (d + 4 * t) (iterateSpiderPrefix L f t) := by
  induction t with
  | zero => simpa only [Nat.mul_zero, Nat.add_zero, iterateSpiderPrefix] using hf
  | succ t ih =>
    simpa only [iterateSpiderPrefix, Nat.mul_succ, Nat.add_assoc] using
      ih.prefixExtend (by omega) (by omega)

/-- A canonical boundary pin can always be normalized to zero on the actual finite spider. -/
theorem CanonicalPinnedSpider.zeroPin {L d : ℕ} {f : ℕ → ℕ}
    (hf : CanonicalPinnedSpider L d f) (hd : d ≤ L) :
    ∃ g k, Math15.Graceful.IsAlphaLabeling (spider L) g k ∧
      g ⟨4 + d, by omega⟩ = 0 := by
  have ha := hf.2.2.1.toAlphaLabeling hf.1 (by omega)
  apply ha.normalizePin
  change f (4 + d) = 2 + L / 2 ∨ f (4 + d) = 2 + L / 2 + 1
  rw [hf.2.2.2]
  omega

end Bounty
end

/- NumericConstruction -/
section
namespace Bounty.PathConstruction

private theorem highCount_low (P : List Symbol) :
    P.IsChain Opposite → (∀ i, P.head? ≠ some (H i)) →
    (P.filter Sum.isRight).length = P.length/2 := by
  induction P using List.twoStepInduction with
  | nil => simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse]
  | singleton x =>
    intro hc hh
    cases x with
    | inl i => simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse]
    | inr i => exact False.elim (hh i rfl)
  | cons_cons x y xs ih _ =>
    intro hc hh
    cases x with
    | inr i => exact False.elim (hh i rfl)
    | inl i =>
      cases y with
      | inl j => simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, List.isChain_cons_cons, Opposite] at hc
      | inr j =>
        have hct : xs.IsChain Opposite := ((List.isChain_cons_cons.mp hc).2).tail
        have hht : ∀ k, xs.head? ≠ some (H k) := by
          intro k hk
          have hr := (List.isChain_cons.mp (List.isChain_cons_cons.mp hc).2).1 (H k) (by simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, hk])
          simpa [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Opposite] using hr
        have ht := ih hct hht
        simp only [List.filter_cons, Sum.isRight_inl, Sum.isRight_inr, Bool.false_eq_true,
          ite_false, ite_true, List.length_cons]
        omega

theorem Terminal.high_size {a b : ℕ} {P : List Symbol} (h : Terminal a b P) :
    b+1 = P.length/2 := by
  have hc := highCount_low P h.alternates (by intro i; simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, h.main_start])
  have hv := (h.vertex_perm.filter Sum.isRight).length_eq
  simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, List.filter_map, Function.comp_def] at hv
  omega

theorem Terminal.balanced {a b : ℕ} {P : List Symbol} (h : Terminal a b P) :
    a = b ∨ a = b+1 := by
  have hlen := h.length
  have hhalf := h.high_size
  omega

theorem Terminal.symbol_bound {a b : ℕ} {P : List Symbol} (h : Terminal a b P)
    {s : Symbol} (hs : s ∈ P) :
    match s with | .inl i => i ≤ a | .inr i => i ≤ b := by
  have hm := h.vertex_perm.mem_iff.mp hs
  cases s <;> simpa [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse] using hm

theorem Terminal.nodup {a b : ℕ} {P : List Symbol} (h : Terminal a b P) : P.Nodup := by
  apply h.vertex_perm.symm.nodup
  rw [List.nodup_append]
  refine ⟨List.nodup_range.map Sum.inl_injective, List.nodup_range.map Sum.inr_injective, ?_⟩
  intro x hx y hy heq
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hy
  cases heq

theorem Terminal.edge_nodup {a b : ℕ} {P : List Symbol} (h : Terminal a b P) :
    (edgeSums P).Nodup := h.edge_perm.symm.nodup List.nodup_range

def symbolAt (P : List Symbol) (i : ℕ) : Symbol := P[i]?.getD (L 0)

theorem symbolAt_eq (P : List Symbol) (i : ℕ) (hi : i < P.length) :
    symbolAt P i = P[i] := by simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, symbolAt, List.getElem?_eq_getElem hi]

theorem symbolAt_mem (P : List Symbol) (i : ℕ) (hi : i < P.length) :
    symbolAt P i ∈ P := by rw [symbolAt_eq P i hi]; exact List.getElem_mem hi

def tailLabel (n : ℕ) : Symbol → ℕ
  | .inl i => n+2-i
  | .inr i => 3+i

theorem tailLabel_bound {a b n : ℕ} {P : List Symbol} (h : Terminal a b P)
    (hn : P.length = n) {s : Symbol} (hs : s ∈ P) :
    3 ≤ tailLabel n s ∧ tailLabel n s ≤ n+2 := by
  have hb := h.symbol_bound hs
  have hlen := h.length
  cases s <;> simp only [tailLabel] <;> dsimp at hb <;> omega

theorem tailLabel_injective {a b n : ℕ} {P : List Symbol} (h : Terminal a b P)
    (hn : P.length = n) {s t : Symbol} (hs : s ∈ P) (ht : t ∈ P)
    (heq : tailLabel n s = tailLabel n t) : s = t := by
  have hb := h.symbol_bound hs
  have hb' := h.symbol_bound ht
  have hlen := h.length
  cases s <;> cases t <;> simp only [tailLabel] at heq <;> dsimp at hb hb' <;>
    first | congr 1; omega | omega

theorem tailLabel_dist {a b n : ℕ} {P : List Symbol} (h : Terminal a b P)
    (hn : P.length = n) {s t : Symbol} (hs : s ∈ P) (ht : t ∈ P)
    (hop : Opposite s t) :
    Nat.dist (tailLabel n s) (tailLabel n t) = n-1-(index s+index t) := by
  have hb := h.symbol_bound hs
  have hb' := h.symbol_bound ht
  have hlen := h.length
  cases s <;> cases t <;> simp only [tailLabel, index, Opposite] at * <;>
    unfold Nat.dist <;> omega


def sumAt (P : List Symbol) (i : ℕ) : ℕ :=
  index (symbolAt P i) + index (symbolAt P (i+1))

theorem edgeSums_length (P : List Symbol) : (edgeSums P).length = P.length-1 := by
  induction P with
  | nil => rfl
  | cons x xs ih =>
    cases xs with
    | nil => rfl
    | cons y ys => simpa [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, edgeSums] using ih

theorem edgeSums_get (P : List Symbol) (i : ℕ) (hi : i+1 < P.length) :
    (edgeSums P)[i]? = some (sumAt P i) := by
  induction P generalizing i with
  | nil => simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse] at hi
  | cons x xs ih =>
    cases xs with
    | nil => simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse] at hi
    | cons y ys =>
      cases i with
      | zero => rfl
      | succ i =>
        simpa [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, edgeSums, sumAt, symbolAt, Nat.add_assoc] using ih i (by simpa [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse] using hi)

theorem Terminal.sumAt_bound {a b : ℕ} {P : List Symbol} (h : Terminal a b P)
    (i : ℕ) (hi : i+1 < P.length) : sumAt P i < P.length-1 := by
  have hm := h.edge_perm.mem_iff.mp (List.mem_of_getElem? (edgeSums_get P i hi))
  have hlen := h.length
  simp only [List.mem_range] at hm
  omega

theorem Terminal.sumAt_injective {a b : ℕ} {P : List Symbol} (h : Terminal a b P)
    (i j : ℕ) (hi : i+1 < P.length) (hj : j+1 < P.length)
    (heq : sumAt P i = sumAt P j) : i = j := by
  apply (List.Nodup.getElem?_inj (by rw [edgeSums_length]; omega) h.edge_nodup).mp
  rw [edgeSums_get P i hi, edgeSums_get P j hj, heq]

theorem Terminal.adjacent {a b : ℕ} {P : List Symbol} (h : Terminal a b P)
    (i : ℕ) (hi : i+1 < P.length) :
    Opposite (symbolAt P i) (symbolAt P (i+1)) := by
  rw [symbolAt_eq P i (by omega), symbolAt_eq P (i+1) hi]
  exact (List.isChain_iff_getElem.mp h.alternates) i hi

theorem Terminal.tail_edge {a b n : ℕ} {P : List Symbol} (h : Terminal a b P)
    (hn : P.length = n) (i : ℕ) (hi : i+1 < n) :
    Nat.dist (tailLabel n (symbolAt P i)) (tailLabel n (symbolAt P (i+1))) = n-1-sumAt P i :=
  tailLabel_dist h hn (symbolAt_mem P i (by omega)) (symbolAt_mem P (i+1) (by omega))
    (h.adjacent i (by omega))

theorem Terminal.tail_cross {a b n : ℕ} {P : List Symbol} (h : Terminal a b P)
    (hn : P.length = n) {s t : Symbol} (hs : s ∈ P) (ht : t ∈ P) (hop : Opposite s t) :
    (tailLabel n s ≤ 2+n/2 ∧ 2+n/2 < tailLabel n t) ∨
    (tailLabel n t ≤ 2+n/2 ∧ 2+n/2 < tailLabel n s) := by
  have hb := h.symbol_bound hs
  have hb' := h.symbol_bound ht
  have hlen := h.length
  have hhalf := h.high_size
  cases s <;> cases t <;> simp only [tailLabel, Opposite] at * <;> omega


theorem symbolAt_zero (P : List Symbol) : symbolAt P 0 = P.head?.getD (L 0) := by
  cases P <;> rfl

def pathSpiderLabel (n : ℕ) (P : List Symbol) (j : ℕ) : ℕ :=
  if j = 0 then 1 else if j = 1 then n+4 else if j = 2 then 0 else
  if j = 3 then n+3 else if j = 4 then 2 else tailLabel n (symbolAt P (j-5))

theorem pathSpiderLabel_tail (n : ℕ) (P : List Symbol) (j : ℕ) (hj : 5 ≤ j) :
    pathSpiderLabel n P j = tailLabel n (symbolAt P (j-5)) := by
  unfold pathSpiderLabel
  split_ifs <;> omega

theorem pathSpiderLabel_canonical {a b n : ℕ} {P : List Symbol} (h : Terminal a b P) :
    CanonicalSpider n (pathSpiderLabel n P) := by
  simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, CanonicalSpider, pathSpiderLabel, h.main_start, tailLabel]

theorem pathSpiderLabel_tail_bounds {a b n : ℕ} {P : List Symbol}
    (h : Terminal a b P) (hn : P.length = n) (j : ℕ) (hj : 5 ≤ j) (hb : j < n+5) :
    3 ≤ pathSpiderLabel n P j ∧ pathSpiderLabel n P j ≤ n+2 := by
  rw [pathSpiderLabel_tail n P j hj]
  exact tailLabel_bound h hn (symbolAt_mem P (j-5) (by omega))

theorem pathSpiderLabel_injective {a b n : ℕ} {P : List Symbol}
    (h : Terminal a b P) (hn : P.length = n) (hsize : 3 ≤ n)
    (i j : ℕ) (hi : i < n+5) (hj : j < n+5)
    (heq : pathSpiderLabel n P i = pathSpiderLabel n P j) : i = j := by
  by_cases hi5 : i < 5 <;> by_cases hj5 : j < 5
  · interval_cases i <;> interval_cases j <;> simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, pathSpiderLabel] at heq ⊢ <;> omega
  · have hb := pathSpiderLabel_tail_bounds h hn j (by omega) hj
    rw [pathSpiderLabel_tail n P j (by omega)] at heq hb
    interval_cases i <;> simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, pathSpiderLabel] at heq <;> omega
  · have hb := pathSpiderLabel_tail_bounds h hn i (by omega) hi
    rw [pathSpiderLabel_tail n P i (by omega)] at heq hb
    interval_cases j <;> simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, pathSpiderLabel] at heq <;> omega
  · have hi' : i-5 < P.length := by omega
    have hj' : j-5 < P.length := by omega
    rw [pathSpiderLabel_tail n P i (by omega), pathSpiderLabel_tail n P j (by omega)] at heq
    have hs := tailLabel_injective h hn (symbolAt_mem P (i-5) hi') (symbolAt_mem P (j-5) hj') heq
    rw [symbolAt_eq P (i-5) hi', symbolAt_eq P (j-5) hj'] at hs
    have hindex := h.nodup.getElem_inj_iff.mp hs
    omega

theorem pathSpiderLabel_bound {a b n : ℕ} {P : List Symbol}
    (h : Terminal a b P) (hn : P.length = n) (i : ℕ) (hi : i < n+5) :
    pathSpiderLabel n P i ≤ n+4 := by
  by_cases hi5 : i < 5
  · interval_cases i <;> simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, pathSpiderLabel]
  · have hb := pathSpiderLabel_tail_bounds h hn i (by omega) hi
    omega

theorem pathSpiderLabel_edge_tail {a b n : ℕ} {P : List Symbol}
    (h : Terminal a b P) (hn : P.length = n) (j : ℕ) (hj : 6 ≤ j) (hb : j < n+5) :
    Nat.dist (pathSpiderLabel n P (spiderParent j)) (pathSpiderLabel n P j) =
      n-1-sumAt P (j-6) := by
  have hparent : spiderParent j = j-1 := by unfold spiderParent; split_ifs <;> omega
  rw [hparent, pathSpiderLabel_tail n P (j-1) (by omega), pathSpiderLabel_tail n P j (by omega)]
  have h1 : j-1-5 = j-6 := by omega
  have h2 : j-5 = (j-6)+1 := by omega
  rw [h1,h2]
  exact h.tail_edge hn (j-6) (by omega)

theorem pathSpiderLabel_edge_initial {a b n : ℕ} {P : List Symbol}
    (h : Terminal a b P) (j : ℕ) (hj : 0 < j) (hb : j < 6) :
    n ≤ Nat.dist (pathSpiderLabel n P (spiderParent j)) (pathSpiderLabel n P j) := by
  interval_cases j <;> simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, spiderParent, pathSpiderLabel, h.main_start, tailLabel, Nat.dist]

theorem pathSpiderLabel_edges_injective {a b n : ℕ} {P : List Symbol}
    (h : Terminal a b P) (hn : P.length = n) (hsize : 3 ≤ n)
    (i j : ℕ) (hi : 0 < i) (hib : i < n+5) (hj : 0 < j) (hjb : j < n+5)
    (heq : Nat.dist (pathSpiderLabel n P (spiderParent i)) (pathSpiderLabel n P i) =
      Nat.dist (pathSpiderLabel n P (spiderParent j)) (pathSpiderLabel n P j)) : i = j := by
  by_cases hi6 : i < 6 <;> by_cases hj6 : j < 6
  · interval_cases i <;> interval_cases j <;>
      simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, spiderParent, pathSpiderLabel, h.main_start, tailLabel, Nat.dist] at heq ⊢ <;> omega
  · have hb := pathSpiderLabel_edge_initial (n := n) h i hi hi6
    rw [pathSpiderLabel_edge_tail h hn j (by omega) hjb] at heq
    omega
  · have hb := pathSpiderLabel_edge_initial (n := n) h j hj hj6
    rw [pathSpiderLabel_edge_tail h hn i (by omega) hib] at heq
    omega
  · have hbi := h.sumAt_bound (i-6) (by omega)
    have hbj := h.sumAt_bound (j-6) (by omega)
    rw [pathSpiderLabel_edge_tail h hn i (by omega) hib,
      pathSpiderLabel_edge_tail h hn j (by omega) hjb] at heq
    have hs : sumAt P (i-6) = sumAt P (j-6) := by omega
    have hij := h.sumAt_injective (i-6) (j-6) (by omega) (by omega) hs
    omega

theorem pathSpiderLabel_certificate {a b n : ℕ} {P : List Symbol}
    (h : Terminal a b P) (hn : P.length = n) (hsize : 3 ≤ n) :
    NatSpiderCertificate n (pathSpiderLabel n P) :=
  ⟨pathSpiderLabel_injective h hn hsize, pathSpiderLabel_bound h hn,
    pathSpiderLabel_edges_injective h hn hsize⟩

theorem pathSpiderLabel_alpha {a b n : ℕ} {P : List Symbol}
    (h : Terminal a b P) (hn : P.length = n) (hsize : 3 ≤ n) :
    NatSpiderAlpha n (pathSpiderLabel n P) (2+n/2) := by
  intro j hj hjb
  by_cases hj6 : j < 6
  · interval_cases j <;> simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, spiderParent, pathSpiderLabel, h.main_start, tailLabel] <;> omega
  · have hparent : spiderParent j = j-1 := by unfold spiderParent; split_ifs <;> omega
    rw [hparent, pathSpiderLabel_tail n P (j-1) (by omega), pathSpiderLabel_tail n P j (by omega)]
    have h1 : j-1-5 = j-6 := by omega
    have h2 : j-5 = (j-6)+1 := by omega
    rw [h1,h2]
    exact h.tail_cross hn (symbolAt_mem P (j-6) (by omega))
      (symbolAt_mem P (j-6+1) (by omega)) (h.adjacent (j-6) (by omega))

theorem pathSpiderLabel_pinned {a b n d : ℕ} {P : List Symbol}
    (h : Terminal a b P) (hn : P.length = n) (hsize : 3 ≤ n) (hd : 1 ≤ d)
    (hpin : P[d-1]? = some (if d%2 = 1 then L a else H b)) :
    CanonicalPinnedSpider n d (pathSpiderLabel n P) := by
  refine ⟨pathSpiderLabel_certificate h hn hsize, pathSpiderLabel_canonical h,
    pathSpiderLabel_alpha h hn hsize, ?_⟩
  rw [pathSpiderLabel_tail n P (4+d) (by omega), show 4+d-5 = d-1 by omega]
  unfold symbolAt
  rw [hpin]
  simp only [Option.getD_some]
  have hb := h.high_size
  have hlen := h.length
  by_cases hodd : d%2 = 1
  · simp only [ite_eq_left hodd, tailLabel]
    omega
  · simp only [ite_eq_right hodd, tailLabel]
    omega

/-- The unbounded first region of the prescribed-zero spider construction. -/
theorem canonical_pinned_first_region (d c : ℕ) (hd : 1 ≤ d) (hc : 1 ≤ c)
    (hregion : c ≤ 2*d-16) :
    ∃ f : ℕ → ℕ, CanonicalPinnedSpider (d+c) d f := by
  obtain ⟨a,b,P,h,hlen,hpin⟩ := symbolic_proposition7 d c hd hc hregion
  exact ⟨pathSpiderLabel (d+c) P, pathSpiderLabel_pinned h hlen (by omega) hd hpin⟩

end Bounty.PathConstruction
end

/- PathAppend -/
section
namespace Bounty
open Math15.Graceful

/-- A graceful permutation of `0,...,m-1`, represented by a total function. -/
def NatGracefulPath (m : ℕ) (p : ℕ → ℕ) : Prop :=
  (∀ i j, i < m → j < m → p i = p j → i = j) ∧
  (∀ i, i < m → p i < m) ∧
  ∀ i j, 0 < i → i < m → 0 < j → j < m →
    Nat.dist (p (i - 1)) (p i) = Nat.dist (p (j - 1)) (p j) → i = j

lemma NatGracefulPath.edge_lt {m : ℕ} {p : ℕ → ℕ} (hp : NatGracefulPath m p)
    {j : ℕ} (hj : 0 < j) (hb : j < m) : Nat.dist (p (j - 1)) (p j) < m := by
  have h1 := hp.2.1 j hb
  have h2 := hp.2.1 (j - 1) (by omega)
  unfold Nat.dist
  omega

/-- Shift the high labels of a spider and put a translated path in the gap. -/
def appendSpiderLabels (L k m : ℕ) (f p : ℕ → ℕ) (j : ℕ) : ℕ :=
  if j < L + 5 then shiftAboveCut k m (f j) else k + 1 + p (j - (L + 5))

lemma appendSpiderLabels_old {L k m j : ℕ} (f p : ℕ → ℕ) (hj : j < L + 5) :
    appendSpiderLabels L k m f p j = shiftAboveCut k m (f j) := by
  simp [appendSpiderLabels, hj]

lemma appendSpiderLabels_new {L k m j : ℕ} (f p : ℕ → ℕ) (hj : L + 5 ≤ j) :
    appendSpiderLabels L k m f p j = k + 1 + p (j - (L + 5)) := by
  simp [appendSpiderLabels, show ¬j < L + 5 by omega]

lemma appendSpiderLabels_injective {L k m : ℕ} {f p : ℕ → ℕ}
    (hf : NatSpiderCertificate L f) (hp : NatGracefulPath m p)
    {i j : ℕ} (hi : i < L + m + 5) (hj : j < L + m + 5)
    (heq : appendSpiderLabels L k m f p i = appendSpiderLabels L k m f p j) : i = j := by
  by_cases hi0 : i < L + 5 <;> by_cases hj0 : j < L + 5
  · rw [appendSpiderLabels_old f p hi0, appendSpiderLabels_old f p hj0] at heq
    exact hf.1 i j hi0 hj0 (shiftAboveCut_injective k m heq)
  · rw [appendSpiderLabels_old f p hi0, appendSpiderLabels_new f p (by omega)] at heq
    have hpb := hp.2.1 (j - (L + 5)) (by omega)
    have hzero := (shiftAboveCut_eq_translate_iff (k := k) (m := m) (x := f i)
      (y := 1 + p (j - (L + 5))) (by omega)).1 (by simpa [Nat.add_assoc] using heq)
    omega
  · rw [appendSpiderLabels_new f p (by omega), appendSpiderLabels_old f p hj0] at heq
    have hpb := hp.2.1 (i - (L + 5)) (by omega)
    have hzero := (shiftAboveCut_eq_translate_iff (k := k) (m := m) (x := f j)
      (y := 1 + p (i - (L + 5))) (by omega)).1 (by simpa [Nat.add_assoc] using heq.symm)
    omega
  · rw [appendSpiderLabels_new f p (by omega), appendSpiderLabels_new f p (by omega)] at heq
    have he := hp.1 (i - (L + 5)) (j - (L + 5)) (by omega) (by omega) (by omega)
    omega

lemma appendSpiderLabels_bound {L k m : ℕ} {f p : ℕ → ℕ}
    (hf : NatSpiderCertificate L f) (hp : NatGracefulPath m p) (hk : k ≤ L + 4)
    {i : ℕ} (hi : i < L + m + 5) : appendSpiderLabels L k m f p i ≤ L + m + 4 := by
  by_cases hi0 : i < L + 5
  · rw [appendSpiderLabels_old f p hi0]
    have h := shiftAboveCut_le (k := k) (m := m) (hf.2.1 i hi0)
    omega
  · rw [appendSpiderLabels_new f p (by omega)]
    have h := hp.2.1 (i - (L + 5)) (by omega)
    omega

lemma appendSpiderLabels_old_edge {L k m : ℕ} {f p : ℕ → ℕ}
    (hα : NatSpiderAlpha L f k) {j : ℕ} (hj : 0 < j) (hb : j < L + 5) :
    Nat.dist (appendSpiderLabels L k m f p (spiderParent j)) (appendSpiderLabels L k m f p j) =
      m + Nat.dist (f (spiderParent j)) (f j) := by
  rw [appendSpiderLabels_old f p ((spiderParent_le j).trans_lt hb), appendSpiderLabels_old f p hb]
  rcases hα j hj hb with h | h
  · exact shiftAboveCut_dist h.1 h.2
  · rw [Nat.dist_comm (shiftAboveCut _ _ _), Nat.dist_comm (f (spiderParent j))]
    exact shiftAboveCut_dist h.1 h.2

lemma appendSpiderLabels_path_edge {L k m : ℕ} {f p : ℕ → ℕ} {j : ℕ}
    (hj : L + 5 < j) :
    Nat.dist (appendSpiderLabels L k m f p (spiderParent j)) (appendSpiderLabels L k m f p j) =
      Nat.dist (p (j - (L + 5) - 1)) (p (j - (L + 5))) := by
  have hparent : spiderParent j = j - 1 := by
    unfold spiderParent
    split_ifs <;> omega
  rw [hparent, appendSpiderLabels_new f p (by omega), appendSpiderLabels_new f p (by omega)]
  rw [translate_dist]
  congr 2
  omega

lemma appendSpiderLabels_join_edge {L k m : ℕ} {f p : ℕ → ℕ} (hL : 1 ≤ L) :
    Nat.dist (appendSpiderLabels L k m f p (spiderParent (L + 5))) (appendSpiderLabels L k m f p (L + 5)) =
      Nat.dist (shiftAboveCut k m (f (L + 4))) (k + 1 + p 0) := by
  have hparent : spiderParent (L + 5) = L + 4 := by
    unfold spiderParent
    split_ifs <;> omega
  rw [hparent, appendSpiderLabels_old f p (by omega), appendSpiderLabels_new f p (by omega)]
  simp

lemma NatSpiderCertificate.edge_pos {L : ℕ} {f : ℕ → ℕ}
    (hf : NatSpiderCertificate L f) {j : ℕ} (hj : 0 < j) (hb : j < L + 5) :
    0 < Nat.dist (f (spiderParent j)) (f j) := by
  apply Nat.dist_pos_of_ne
  intro heq
  have he := hf.1 (spiderParent j) j ((spiderParent_lt hj).trans hb) hb heq
  have hl := spiderParent_lt hj
  omega

/-- The full append operation, conditional only on an explicitly certified path
whose first new label makes the joining difference equal to the path size. -/
theorem NatSpiderCertificate.appendPath {L k m : ℕ} {f p : ℕ → ℕ}
    (hL : 1 ≤ L) (hf : NatSpiderCertificate L f) (hα : NatSpiderAlpha L f k)
    (hp : NatGracefulPath m p) (hk : k ≤ L + 4)
    (hjoin : Nat.dist (shiftAboveCut k m (f (L + 4))) (k + 1 + p 0) = m) :
    NatSpiderCertificate (L + m) (appendSpiderLabels L k m f p) := by
  refine ⟨?_, ?_, ?_⟩
  · exact fun i j hi hj heq => appendSpiderLabels_injective hf hp hi hj heq
  · exact fun i hi => appendSpiderLabels_bound hf hp hk hi
  · intro i j hi hib hj hjb heq
    rcases lt_trichotomy i (L + 5) with hi0 | rfl | hi0 <;>
      rcases lt_trichotomy j (L + 5) with hj0 | rfl | hj0
    · rw [appendSpiderLabels_old_edge hα hi hi0, appendSpiderLabels_old_edge hα hj hj0] at heq
      exact hf.2.2 i j hi hi0 hj hj0 (by omega)
    · rw [appendSpiderLabels_old_edge hα hi hi0, appendSpiderLabels_join_edge hL, hjoin] at heq
      have hpos := hf.edge_pos hi hi0
      omega
    · rw [appendSpiderLabels_old_edge hα hi hi0, appendSpiderLabels_path_edge hj0] at heq
      have hb := hp.edge_lt (by omega : 0 < j - (L + 5)) (by omega)
      omega
    · rw [appendSpiderLabels_join_edge hL, hjoin, appendSpiderLabels_old_edge hα hj hj0] at heq
      have hpos := hf.edge_pos hj hj0
      omega
    · rfl
    · rw [appendSpiderLabels_join_edge hL, hjoin, appendSpiderLabels_path_edge hj0] at heq
      have hb := hp.edge_lt (by omega : 0 < j - (L + 5)) (by omega)
      omega
    · rw [appendSpiderLabels_path_edge hi0, appendSpiderLabels_old_edge hα hj hj0] at heq
      have hb := hp.edge_lt (by omega : 0 < i - (L + 5)) (by omega)
      omega
    · rw [appendSpiderLabels_path_edge hi0, appendSpiderLabels_join_edge hL, hjoin] at heq
      have hb := hp.edge_lt (by omega : 0 < i - (L + 5)) (by omega)
      omega
    · rw [appendSpiderLabels_path_edge hi0, appendSpiderLabels_path_edge hj0] at heq
      have he := hp.2.2 (i - (L + 5)) (j - (L + 5)) (by omega) (by omega)
        (by omega) (by omega) heq
      omega

lemma appendSpiderLabels_preserves_zero {L k m z : ℕ} {f p : ℕ → ℕ}
    (hz : z < L + 5) (hzero : f z = 0) : appendSpiderLabels L k m f p z = 0 := by
  rw [appendSpiderLabels_old f p hz, hzero]
  simp [shiftAboveCut]

end Bounty
end

/- AlphaPath -/
section
namespace Bounty
open PathConstruction

/-- A path labeling with an explicit separating alpha cut. -/
def NatAlphaPath (n : ℕ) (p : ℕ → ℕ) (k : ℕ) : Prop :=
  NatGracefulPath n p ∧ k < n-1 ∧
  ∀ j, 0 < j → j < n →
    (p (j-1) ≤ k ∧ k < p j) ∨ (p j ≤ k ∧ k < p (j-1))

def ZeroAlphaPath (a b : ℕ) : Prop :=
  ∃ p k, NatAlphaPath (a+b+1) p k ∧ p a = 0

def boundaryLabel : Bool → ℕ → ℕ → Symbol → ℕ
  | true, a, _, .inl i => a-i
  | true, a, _, .inr i => a+1+i
  | false, _, b, .inl i => b+1+i
  | false, _, b, .inr i => b-i

def boundaryCut (low : Bool) (a b : ℕ) : ℕ := if low then a else b

theorem boundaryLabel_bound {a b n : ℕ} {P : List Symbol}
    (h : Terminal a b P) (hn : P.length = n) (low : Bool)
    {s : Symbol} (hs : s ∈ P) : boundaryLabel low a b s < n := by
  have hb := h.symbol_bound hs
  have hlen := h.length
  cases low <;> cases s <;> simp only [boundaryLabel] <;> dsimp at hb <;> omega

theorem boundaryLabel_injective {a b : ℕ} {P : List Symbol}
    (h : Terminal a b P) (low : Bool) {s t : Symbol} (hs : s ∈ P) (ht : t ∈ P)
    (heq : boundaryLabel low a b s = boundaryLabel low a b t) : s = t := by
  have hb := h.symbol_bound hs
  have hb' := h.symbol_bound ht
  cases low <;> cases s <;> cases t <;> simp only [boundaryLabel] at heq <;>
    dsimp at hb hb' <;> first | congr 1; omega | omega

theorem boundaryLabel_dist {a b : ℕ} {P : List Symbol}
    (h : Terminal a b P) (low : Bool) {s t : Symbol} (hs : s ∈ P) (ht : t ∈ P)
    (hop : PathConstruction.Opposite s t) :
    Nat.dist (boundaryLabel low a b s) (boundaryLabel low a b t) = index s+index t+1 := by
  have hb := h.symbol_bound hs
  have hb' := h.symbol_bound ht
  cases low <;> cases s <;> cases t <;>
    simp only [boundaryLabel, PathConstruction.Opposite, index] at * <;> unfold Nat.dist <;> omega

theorem boundaryLabel_cross {a b : ℕ} {P : List Symbol}
    (h : Terminal a b P) (low : Bool) {s t : Symbol} (hs : s ∈ P) (ht : t ∈ P)
    (hop : PathConstruction.Opposite s t) :
    (boundaryLabel low a b s ≤ boundaryCut low a b ∧ boundaryCut low a b < boundaryLabel low a b t) ∨
    (boundaryLabel low a b t ≤ boundaryCut low a b ∧ boundaryCut low a b < boundaryLabel low a b s) := by
  have hb := h.symbol_bound hs
  have hb' := h.symbol_bound ht
  cases low <;> cases s <;> cases t <;>
    simp only [boundaryLabel, boundaryCut, Bool.false_eq_true, ite_false, ite_true, PathConstruction.Opposite] at * <;> omega

def boundaryPath (low : Bool) (a b : ℕ) (P : List Symbol) (i : ℕ) : ℕ :=
  boundaryLabel low a b (symbolAt P i)

theorem boundaryPath_edge {a b n : ℕ} {P : List Symbol} (h : Terminal a b P)
    (hn : P.length = n) (low : Bool) {j : ℕ} (hj : 0 < j) (hb : j < n) :
    Nat.dist (boundaryPath low a b P (j-1)) (boundaryPath low a b P j) = sumAt P (j-1)+1 := by
  have heq : j-1+1=j := by omega
  have he := boundaryLabel_dist h low (symbolAt_mem P (j-1) (by omega))
    (symbolAt_mem P j (by omega)) (by simpa only [heq] using h.adjacent (j-1) (by omega))
  simpa only [boundaryPath, sumAt, heq] using he

theorem boundaryPath_alpha {a b n : ℕ} {P : List Symbol}
    (h : Terminal a b P) (hn : P.length = n) (low : Bool) :
    NatAlphaPath n (boundaryPath low a b P) (boundaryCut low a b) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro i j hi hj heq
    have hi' : i < P.length := by omega
    have hj' : j < P.length := by omega
    have hs := boundaryLabel_injective h low (symbolAt_mem P i hi') (symbolAt_mem P j hj') heq
    rw [symbolAt_eq P i hi', symbolAt_eq P j hj'] at hs
    exact h.nodup.getElem_inj_iff.mp hs
  · intro i hi
    exact boundaryLabel_bound h hn low (symbolAt_mem P i (by omega))
  · intro i j hi hib hj hjb heq
    rw [boundaryPath_edge h hn low hi hib, boundaryPath_edge h hn low hj hjb] at heq
    have hs : sumAt P (i-1) = sumAt P (j-1) := by omega
    have hh := h.sumAt_injective (i-1) (j-1) (by omega) (by omega) hs
    omega
  · have hlen := h.length
    cases low <;> simp only [boundaryCut, Bool.false_eq_true, ite_false, ite_true] <;> omega
  · intro j hj hjb
    have heq : j-1+1=j := by omega
    exact boundaryLabel_cross h low (symbolAt_mem P (j-1) (by omega))
      (symbolAt_mem P j (by omega)) (by simpa only [heq] using h.adjacent (j-1) (by omega))

theorem zeroAlphaPath_large_left (a b : ℕ) (ha : 14 ≤ a) (hb : 1 ≤ b) (hba : b ≤ a) :
    ZeroAlphaPath a b := by
  obtain ⟨A,B,P,h,hlen,hpin⟩ := symbolic_proposition7 (a+1) b (by omega) hb (by omega)
  let low := decide ((a+1)%2 = 1)
  refine ⟨boundaryPath low A B P, boundaryCut low A B, boundaryPath_alpha h (by omega) low, ?_⟩
  have hi : P[a]? = some (if low then L A else H B) := by simpa [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, low] using hpin
  simp only [boundaryPath, symbolAt, hi, Option.getD_some]
  cases low <;> simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, boundaryLabel]

def reverseNatPath (n : ℕ) (p : ℕ → ℕ) (i : ℕ) : ℕ := p (n-1-i)

theorem NatAlphaPath.reverse {n k : ℕ} {p : ℕ → ℕ} (h : NatAlphaPath n p k) :
    NatAlphaPath n (reverseNatPath n p) k := by
  refine ⟨⟨?_, ?_, ?_⟩, h.2.1, ?_⟩
  · intro i j hi hj heq
    have hh := h.1.1 (n-1-i) (n-1-j) (by omega) (by omega) heq
    omega
  · intro i hi
    exact h.1.2.1 _ (by omega)
  · intro i j hi hib hj hjb heq
    have h1 : n-1-(i-1) = n-i := by omega
    have h2 : n-1-i = n-i-1 := by omega
    have h3 : n-1-(j-1) = n-j := by omega
    have h4 : n-1-j = n-j-1 := by omega
    simp only [reverseNatPath, h1, h2, h3, h4] at heq
    have hs : Nat.dist (p (n-i-1)) (p (n-i)) = Nat.dist (p (n-j-1)) (p (n-j)) := by
      simpa only [Nat.dist_comm] using heq
    have hij := h.1.2.2 (n-i) (n-j) (by omega) (by omega) (by omega) (by omega) hs
    omega
  · intro j hj hjb
    have hc := h.2.2 (n-j) (by omega) (by omega)
    have h1 : n-1-(j-1) = n-j := by omega
    have h2 : n-1-j = n-j-1 := by omega
    simp only [reverseNatPath, h1, h2]
    exact hc.symm

theorem ZeroAlphaPath.symm {a b : ℕ} (h : ZeroAlphaPath a b) : ZeroAlphaPath b a := by
  obtain ⟨p,k,hp,hpin⟩ := h
  refine ⟨reverseNatPath (a+b+1) p,k,?_,?_⟩
  · simpa only [Nat.add_comm a b] using hp.reverse
  · simpa [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, reverseNatPath] using hpin


def pathPred {n : ℕ} (i : Fin n) : Fin n := ⟨i.val-1, (Nat.sub_le _ _).trans_lt i.isLt⟩

def FiniteAlphaPath (n : ℕ) (p : Fin n → ℕ) (k : ℕ) : Prop :=
  Function.Injective p ∧ (∀ i, p i < n) ∧
  (∀ i j : Fin n, 0 < i.val → 0 < j.val →
    Nat.dist (p (pathPred i)) (p i) = Nat.dist (p (pathPred j)) (p j) → i = j) ∧
  k < n-1 ∧ ∀ j : Fin n, 0 < j.val →
    (p (pathPred j) ≤ k ∧ k < p j) ∨ (p j ≤ k ∧ k < p (pathPred j))

def finiteAlphaPathDecidable (n : ℕ) (p : Fin n → ℕ) (k : ℕ) : Decidable (FiniteAlphaPath n p k) := by
  unfold FiniteAlphaPath Function.Injective
  infer_instance

def finitePathLabel {n : ℕ} (p : Fin n → ℕ) (i : ℕ) : ℕ :=
  if hi : i < n then p ⟨i,hi⟩ else 0

theorem FiniteAlphaPath.toNat {n k : ℕ} {p : Fin n → ℕ} (h : FiniteAlphaPath n p k) :
    NatAlphaPath n (finitePathLabel p) k := by
  refine ⟨⟨?_, ?_, ?_⟩, h.2.2.2.1, ?_⟩
  · intro i j hi hj heq
    simp only [finitePathLabel, dite_eq_left hi, dite_eq_left hj] at heq
    exact congrArg Fin.val (h.1 heq)
  · intro i hi
    simpa only [finitePathLabel, dite_eq_left hi] using h.2.1 ⟨i,hi⟩
  · intro i j hi hib hj hjb heq
    have hi' : i-1 < n := by omega
    have hj' : j-1 < n := by omega
    simp only [finitePathLabel, dite_eq_left hi', dite_eq_left hj', dite_eq_left hib,
      dite_eq_left hjb] at heq
    exact congrArg Fin.val (h.2.2.1 ⟨i,hib⟩ ⟨j,hjb⟩ hi hj heq)
  · intro j hj hjb
    have hj' : j-1 < n := by omega
    simpa only [finitePathLabel, dite_eq_left hj', dite_eq_left hjb, pathPred] using
      h.2.2.2.2 ⟨j,hjb⟩ hj

private theorem alphaCase_1_1 : ZeroAlphaPath 1 1 := by
  let p : Fin 3 → ℕ := ![1, 0, 2]
  have hp : FiniteAlphaPath 3 p 0 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 0, hp.toNat, rfl⟩

private theorem alphaCase_13_13 : ZeroAlphaPath 13 13 := by
  let p : Fin 27 → ℕ := ![15, 12, 13, 11, 16, 10, 14, 7, 21, 5, 22, 3, 23, 0, 26, 1, 25, 4, 19, 6, 17, 9, 18, 8, 20, 2, 24]
  have hp : FiniteAlphaPath 27 p 12 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 12, hp.toNat, rfl⟩

private theorem alphaCase_1_2 : ZeroAlphaPath 1 2 := by
  let p : Fin 4 → ℕ := ![3, 0, 2, 1]
  have hp : FiniteAlphaPath 4 p 1 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 1, hp.toNat, rfl⟩

private theorem alphaCase_1_3 : ZeroAlphaPath 1 3 := by
  let p : Fin 5 → ℕ := ![4, 0, 3, 1, 2]
  have hp : FiniteAlphaPath 5 p 1 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 1, hp.toNat, rfl⟩

private theorem alphaCase_2_3 : ZeroAlphaPath 2 3 := by
  let p : Fin 6 → ℕ := ![1, 5, 0, 3, 2, 4]
  have hp : FiniteAlphaPath 6 p 2 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 2, hp.toNat, rfl⟩

private theorem alphaCase_3_3 : ZeroAlphaPath 3 3 := by
  let p : Fin 7 → ℕ := ![4, 2, 3, 0, 6, 1, 5]
  have hp : FiniteAlphaPath 7 p 2 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 2, hp.toNat, rfl⟩

private theorem alphaCase_1_4 : ZeroAlphaPath 1 4 := by
  let p : Fin 6 → ℕ := ![5, 0, 4, 1, 3, 2]
  have hp : FiniteAlphaPath 6 p 2 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 2, hp.toNat, rfl⟩

private theorem alphaCase_2_4 : ZeroAlphaPath 2 4 := by
  let p : Fin 7 → ℕ := ![2, 6, 0, 5, 3, 4, 1]
  have hp : FiniteAlphaPath 7 p 3 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 3, hp.toNat, rfl⟩

private theorem alphaCase_3_4 : ZeroAlphaPath 3 4 := by
  let p : Fin 8 → ℕ := ![6, 1, 7, 0, 4, 3, 5, 2]
  have hp : FiniteAlphaPath 8 p 3 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 3, hp.toNat, rfl⟩

private theorem alphaCase_4_4 : ZeroAlphaPath 4 4 := by
  let p : Fin 9 → ℕ := ![3, 5, 4, 7, 0, 8, 2, 6, 1]
  have hp : FiniteAlphaPath 9 p 4 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 4, hp.toNat, rfl⟩

private theorem alphaCase_1_5 : ZeroAlphaPath 1 5 := by
  let p : Fin 7 → ℕ := ![6, 0, 5, 1, 4, 2, 3]
  have hp : FiniteAlphaPath 7 p 2 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 2, hp.toNat, rfl⟩

private theorem alphaCase_2_5 : ZeroAlphaPath 2 5 := by
  let p : Fin 8 → ℕ := ![1, 6, 0, 7, 3, 4, 2, 5]
  have hp : FiniteAlphaPath 8 p 3 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 3, hp.toNat, rfl⟩

private theorem alphaCase_3_5 : ZeroAlphaPath 3 5 := by
  let p : Fin 9 → ℕ := ![7, 2, 6, 0, 8, 1, 4, 3, 5]
  have hp : FiniteAlphaPath 9 p 3 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 3, hp.toNat, rfl⟩

private theorem alphaCase_4_5 : ZeroAlphaPath 4 5 := by
  let p : Fin 10 → ℕ := ![2, 8, 1, 9, 0, 5, 4, 6, 3, 7]
  have hp : FiniteAlphaPath 10 p 4 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 4, hp.toNat, rfl⟩

private theorem alphaCase_5_5 : ZeroAlphaPath 5 5 := by
  let p : Fin 11 → ℕ := ![8, 2, 6, 1, 9, 0, 10, 3, 5, 4, 7]
  have hp : FiniteAlphaPath 11 p 4 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 4, hp.toNat, rfl⟩

private theorem alphaCase_1_6 : ZeroAlphaPath 1 6 := by
  let p : Fin 8 → ℕ := ![7, 0, 6, 1, 5, 2, 4, 3]
  have hp : FiniteAlphaPath 8 p 3 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 3, hp.toNat, rfl⟩

private theorem alphaCase_2_6 : ZeroAlphaPath 2 6 := by
  let p : Fin 9 → ℕ := ![1, 8, 0, 6, 2, 7, 4, 5, 3]
  have hp : FiniteAlphaPath 9 p 4 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 4, hp.toNat, rfl⟩

private theorem alphaCase_3_6 : ZeroAlphaPath 3 6 := by
  let p : Fin 10 → ℕ := ![7, 1, 8, 0, 9, 4, 5, 3, 6, 2]
  have hp : FiniteAlphaPath 10 p 4 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 4, hp.toNat, rfl⟩

private theorem alphaCase_4_6 : ZeroAlphaPath 4 6 := by
  let p : Fin 11 → ℕ := ![2, 9, 1, 10, 0, 6, 5, 7, 4, 8, 3]
  have hp : FiniteAlphaPath 11 p 5 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 5, hp.toNat, rfl⟩

private theorem alphaCase_5_6 : ZeroAlphaPath 5 6 := by
  let p : Fin 12 → ℕ := ![9, 1, 8, 2, 11, 0, 10, 5, 6, 4, 7, 3]
  have hp : FiniteAlphaPath 12 p 5 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 5, hp.toNat, rfl⟩

private theorem alphaCase_6_6 : ZeroAlphaPath 6 6 := by
  let p : Fin 13 → ℕ := ![1, 10, 4, 9, 2, 12, 0, 11, 3, 7, 6, 8, 5]
  have hp : FiniteAlphaPath 13 p 6 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 6, hp.toNat, rfl⟩

private theorem alphaCase_1_7 : ZeroAlphaPath 1 7 := by
  let p : Fin 9 → ℕ := ![7, 0, 8, 2, 6, 1, 4, 3, 5]
  have hp : FiniteAlphaPath 9 p 3 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 3, hp.toNat, rfl⟩

private theorem alphaCase_2_7 : ZeroAlphaPath 2 7 := by
  let p : Fin 10 → ℕ := ![1, 9, 0, 7, 3, 8, 2, 5, 4, 6]
  have hp : FiniteAlphaPath 10 p 4 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 4, hp.toNat, rfl⟩

private theorem alphaCase_3_7 : ZeroAlphaPath 3 7 := by
  let p : Fin 11 → ℕ := ![9, 1, 10, 0, 7, 3, 8, 2, 5, 4, 6]
  have hp : FiniteAlphaPath 11 p 4 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 4, hp.toNat, rfl⟩

private theorem alphaCase_4_7 : ZeroAlphaPath 4 7 := by
  let p : Fin 12 → ℕ := ![3, 6, 5, 7, 0, 11, 1, 10, 2, 8, 4, 9]
  have hp : FiniteAlphaPath 12 p 5 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 5, hp.toNat, rfl⟩

private theorem alphaCase_5_7 : ZeroAlphaPath 5 7 := by
  let p : Fin 13 → ℕ := ![7, 5, 6, 3, 10, 0, 12, 1, 9, 4, 8, 2, 11]
  have hp : FiniteAlphaPath 13 p 5 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 5, hp.toNat, rfl⟩

private theorem alphaCase_6_7 : ZeroAlphaPath 6 7 := by
  let p : Fin 14 → ℕ := ![5, 8, 6, 7, 3, 11, 0, 13, 1, 10, 4, 9, 2, 12]
  have hp : FiniteAlphaPath 14 p 6 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 6, hp.toNat, rfl⟩

private theorem alphaCase_7_7 : ZeroAlphaPath 7 7 := by
  let p : Fin 15 → ℕ := ![8, 6, 7, 4, 11, 1, 14, 0, 12, 3, 9, 5, 10, 2, 13]
  have hp : FiniteAlphaPath 15 p 6 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 6, hp.toNat, rfl⟩

private theorem alphaCase_1_8 : ZeroAlphaPath 1 8 := by
  let p : Fin 10 → ℕ := ![8, 0, 9, 2, 5, 4, 6, 1, 7, 3]
  have hp : FiniteAlphaPath 10 p 4 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 4, hp.toNat, rfl⟩

private theorem alphaCase_2_8 : ZeroAlphaPath 2 8 := by
  let p : Fin 11 → ℕ := ![1, 9, 0, 10, 3, 7, 2, 8, 5, 6, 4]
  have hp : FiniteAlphaPath 11 p 5 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 5, hp.toNat, rfl⟩

private theorem alphaCase_3_8 : ZeroAlphaPath 3 8 := by
  let p : Fin 12 → ℕ := ![8, 3, 11, 0, 10, 1, 7, 4, 6, 5, 9, 2]
  have hp : FiniteAlphaPath 12 p 5 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 5, hp.toNat, rfl⟩

private theorem alphaCase_4_8 : ZeroAlphaPath 4 8 := by
  let p : Fin 13 → ℕ := ![4, 9, 1, 12, 0, 10, 3, 7, 6, 8, 5, 11, 2]
  have hp : FiniteAlphaPath 13 p 6 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 6, hp.toNat, rfl⟩

private theorem alphaCase_5_8 : ZeroAlphaPath 5 8 := by
  let p : Fin 14 → ℕ := ![9, 4, 10, 1, 13, 0, 11, 3, 7, 6, 8, 5, 12, 2]
  have hp : FiniteAlphaPath 14 p 6 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 6, hp.toNat, rfl⟩

private theorem alphaCase_6_8 : ZeroAlphaPath 6 8 := by
  let p : Fin 15 → ℕ := ![1, 12, 4, 11, 2, 14, 0, 13, 3, 9, 5, 10, 7, 8, 6]
  have hp : FiniteAlphaPath 15 p 7 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 7, hp.toNat, rfl⟩

private theorem alphaCase_7_8 : ZeroAlphaPath 7 8 := by
  let p : Fin 16 → ℕ := ![10, 7, 8, 6, 12, 3, 15, 0, 14, 1, 11, 4, 9, 5, 13, 2]
  have hp : FiniteAlphaPath 16 p 7 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 7, hp.toNat, rfl⟩

private theorem alphaCase_8_8 : ZeroAlphaPath 8 8 := by
  let p : Fin 17 → ℕ := ![1, 14, 4, 11, 6, 12, 3, 15, 0, 16, 2, 13, 5, 9, 8, 10, 7]
  have hp : FiniteAlphaPath 17 p 8 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 8, hp.toNat, rfl⟩

private theorem alphaCase_1_9 : ZeroAlphaPath 1 9 := by
  let p : Fin 11 → ℕ := ![8, 0, 10, 1, 6, 2, 9, 3, 5, 4, 7]
  have hp : FiniteAlphaPath 11 p 4 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 4, hp.toNat, rfl⟩

private theorem alphaCase_2_9 : ZeroAlphaPath 2 9 := by
  let p : Fin 12 → ℕ := ![3, 11, 0, 10, 1, 6, 5, 7, 4, 8, 2, 9]
  have hp : FiniteAlphaPath 12 p 5 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 5, hp.toNat, rfl⟩

private theorem alphaCase_3_9 : ZeroAlphaPath 3 9 := by
  let p : Fin 13 → ℕ := ![8, 3, 12, 0, 11, 1, 7, 4, 6, 5, 9, 2, 10]
  have hp : FiniteAlphaPath 13 p 5 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 5, hp.toNat, rfl⟩

private theorem alphaCase_4_9 : ZeroAlphaPath 4 9 := by
  let p : Fin 14 → ℕ := ![4, 12, 1, 13, 0, 10, 6, 7, 5, 8, 3, 9, 2, 11]
  have hp : FiniteAlphaPath 14 p 6 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 6, hp.toNat, rfl⟩

private theorem alphaCase_5_9 : ZeroAlphaPath 5 9 := by
  let p : Fin 15 → ℕ := ![12, 1, 11, 4, 13, 0, 14, 2, 10, 6, 7, 5, 8, 3, 9]
  have hp : FiniteAlphaPath 15 p 6 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 6, hp.toNat, rfl⟩

private theorem alphaCase_6_9 : ZeroAlphaPath 6 9 := by
  let p : Fin 16 → ℕ := ![1, 13, 4, 11, 3, 14, 0, 15, 2, 12, 6, 10, 5, 8, 7, 9]
  have hp : FiniteAlphaPath 16 p 7 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 7, hp.toNat, rfl⟩

private theorem alphaCase_7_9 : ZeroAlphaPath 7 9 := by
  let p : Fin 17 → ℕ := ![10, 7, 8, 6, 12, 1, 15, 0, 16, 3, 13, 5, 9, 4, 11, 2, 14]
  have hp : FiniteAlphaPath 17 p 7 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 7, hp.toNat, rfl⟩

private theorem alphaCase_8_9 : ZeroAlphaPath 8 9 := by
  let p : Fin 18 → ℕ := ![1, 15, 4, 12, 5, 14, 2, 17, 0, 16, 3, 13, 7, 9, 8, 11, 6, 10]
  have hp : FiniteAlphaPath 18 p 8 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 8, hp.toNat, rfl⟩

private theorem alphaCase_9_9 : ZeroAlphaPath 9 9 := by
  let p : Fin 19 → ℕ := ![15, 1, 16, 3, 13, 5, 14, 2, 18, 0, 17, 6, 9, 8, 10, 4, 11, 7, 12]
  have hp : FiniteAlphaPath 19 p 8 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 8, hp.toNat, rfl⟩

private theorem alphaCase_1_10 : ZeroAlphaPath 1 10 := by
  let p : Fin 12 → ℕ := ![11, 0, 10, 1, 9, 2, 8, 3, 7, 4, 6, 5]
  have hp : FiniteAlphaPath 12 p 5 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 5, hp.toNat, rfl⟩

private theorem alphaCase_2_10 : ZeroAlphaPath 2 10 := by
  let p : Fin 13 → ℕ := ![4, 9, 0, 12, 1, 11, 5, 8, 6, 7, 3, 10, 2]
  have hp : FiniteAlphaPath 13 p 6 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 6, hp.toNat, rfl⟩

private theorem alphaCase_3_10 : ZeroAlphaPath 3 10 := by
  let p : Fin 14 → ℕ := ![9, 1, 12, 0, 13, 3, 7, 6, 8, 5, 10, 4, 11, 2]
  have hp : FiniteAlphaPath 14 p 6 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 6, hp.toNat, rfl⟩

private theorem alphaCase_4_10 : ZeroAlphaPath 4 10 := by
  let p : Fin 15 → ℕ := ![1, 12, 2, 14, 0, 13, 4, 11, 3, 9, 5, 10, 7, 8, 6]
  have hp : FiniteAlphaPath 15 p 7 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 7, hp.toNat, rfl⟩

private theorem alphaCase_5_10 : ZeroAlphaPath 5 10 := by
  let p : Fin 16 → ℕ := ![10, 4, 11, 1, 14, 0, 15, 3, 12, 7, 8, 6, 9, 5, 13, 2]
  have hp : FiniteAlphaPath 16 p 7 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 7, hp.toNat, rfl⟩

private theorem alphaCase_6_10 : ZeroAlphaPath 6 10 := by
  let p : Fin 17 → ℕ := ![1, 14, 4, 13, 2, 16, 0, 15, 3, 11, 6, 12, 5, 9, 8, 10, 7]
  have hp : FiniteAlphaPath 17 p 8 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 8, hp.toNat, rfl⟩

private theorem alphaCase_7_10 : ZeroAlphaPath 7 10 := by
  let p : Fin 18 → ℕ := ![11, 5, 12, 4, 14, 3, 17, 0, 16, 1, 13, 8, 9, 7, 10, 6, 15, 2]
  have hp : FiniteAlphaPath 18 p 8 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 8, hp.toNat, rfl⟩

private theorem alphaCase_8_10 : ZeroAlphaPath 8 10 := by
  let p : Fin 19 → ℕ := ![1, 16, 4, 13, 5, 15, 2, 18, 0, 17, 3, 14, 7, 10, 9, 11, 6, 12, 8]
  have hp : FiniteAlphaPath 19 p 9 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 9, hp.toNat, rfl⟩

private theorem alphaCase_9_10 : ZeroAlphaPath 9 10 := by
  let p : Fin 20 → ℕ := ![16, 8, 12, 7, 10, 9, 11, 5, 17, 0, 19, 1, 15, 2, 18, 3, 14, 4, 13, 6]
  have hp : FiniteAlphaPath 20 p 9 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 9, hp.toNat, rfl⟩

private theorem alphaCase_10_10 : ZeroAlphaPath 10 10 := by
  let p : Fin 21 → ℕ := ![1, 18, 4, 15, 7, 14, 5, 17, 2, 20, 0, 19, 3, 16, 6, 12, 8, 13, 10, 11, 9]
  have hp : FiniteAlphaPath 21 p 10 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 10, hp.toNat, rfl⟩

private theorem alphaCase_1_11 : ZeroAlphaPath 1 11 := by
  let p : Fin 13 → ℕ := ![8, 0, 12, 1, 11, 2, 6, 5, 7, 4, 9, 3, 10]
  have hp : FiniteAlphaPath 13 p 5 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 5, hp.toNat, rfl⟩

private theorem alphaCase_2_11 : ZeroAlphaPath 2 11 := by
  let p : Fin 14 → ℕ := ![3, 13, 0, 12, 1, 9, 5, 8, 6, 7, 2, 11, 4, 10]
  have hp : FiniteAlphaPath 14 p 6 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 6, hp.toNat, rfl⟩

private theorem alphaCase_3_11 : ZeroAlphaPath 3 11 := by
  let p : Fin 15 → ℕ := ![9, 1, 13, 0, 14, 3, 8, 5, 7, 6, 10, 4, 11, 2, 12]
  have hp : FiniteAlphaPath 15 p 6 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 6, hp.toNat, rfl⟩

private theorem alphaCase_4_11 : ZeroAlphaPath 4 11 := by
  let p : Fin 16 → ℕ := ![5, 10, 1, 14, 0, 15, 3, 11, 4, 8, 7, 9, 6, 12, 2, 13]
  have hp : FiniteAlphaPath 16 p 7 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 7, hp.toNat, rfl⟩

private theorem alphaCase_5_11 : ZeroAlphaPath 5 11 := by
  let p : Fin 17 → ℕ := ![14, 1, 13, 2, 16, 0, 15, 5, 8, 7, 9, 4, 11, 3, 12, 6, 10]
  have hp : FiniteAlphaPath 17 p 7 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 7, hp.toNat, rfl⟩

private theorem alphaCase_6_11 : ZeroAlphaPath 6 11 := by
  let p : Fin 18 → ℕ := ![1, 15, 4, 14, 2, 17, 0, 16, 3, 12, 5, 13, 7, 9, 8, 11, 6, 10]
  have hp : FiniteAlphaPath 18 p 8 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 8, hp.toNat, rfl⟩

private theorem alphaCase_7_11 : ZeroAlphaPath 7 11 := by
  let p : Fin 19 → ℕ := ![14, 8, 9, 7, 10, 6, 11, 0, 18, 1, 17, 2, 16, 3, 15, 5, 12, 4, 13]
  have hp : FiniteAlphaPath 19 p 8 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 8, hp.toNat, rfl⟩

private theorem alphaCase_8_11 : ZeroAlphaPath 8 11 := by
  let p : Fin 20 → ℕ := ![1, 17, 4, 14, 5, 16, 2, 19, 0, 18, 3, 15, 7, 12, 6, 13, 9, 10, 8, 11]
  have hp : FiniteAlphaPath 20 p 9 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 9, hp.toNat, rfl⟩

private theorem alphaCase_9_11 : ZeroAlphaPath 9 11 := by
  let p : Fin 21 → ℕ := ![18, 4, 14, 5, 11, 7, 15, 3, 16, 0, 20, 1, 19, 2, 17, 6, 13, 8, 10, 9, 12]
  have hp : FiniteAlphaPath 21 p 9 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 9, hp.toNat, rfl⟩

private theorem alphaCase_10_11 : ZeroAlphaPath 10 11 := by
  let p : Fin 22 → ℕ := ![5, 15, 8, 12, 7, 13, 10, 11, 9, 18, 0, 21, 1, 20, 3, 19, 4, 17, 6, 14, 2, 16]
  have hp : FiniteAlphaPath 22 p 10 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 10, hp.toNat, rfl⟩

private theorem alphaCase_11_11 : ZeroAlphaPath 11 11 := by
  let p : Fin 23 → ℕ := ![13, 10, 11, 9, 15, 8, 12, 7, 18, 3, 22, 0, 21, 1, 17, 4, 16, 6, 14, 5, 19, 2, 20]
  have hp : FiniteAlphaPath 23 p 10 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 10, hp.toNat, rfl⟩

private theorem alphaCase_1_12 : ZeroAlphaPath 1 12 := by
  let p : Fin 14 → ℕ := ![11, 0, 13, 1, 10, 5, 8, 6, 7, 3, 9, 2, 12, 4]
  have hp : FiniteAlphaPath 14 p 6 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 6, hp.toNat, rfl⟩

private theorem alphaCase_2_12 : ZeroAlphaPath 2 12 := by
  let p : Fin 15 → ℕ := ![5, 12, 0, 14, 1, 11, 3, 8, 7, 9, 6, 10, 4, 13, 2]
  have hp : FiniteAlphaPath 15 p 7 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 7, hp.toNat, rfl⟩

private theorem alphaCase_3_12 : ZeroAlphaPath 3 12 := by
  let p : Fin 16 → ℕ := ![11, 1, 15, 0, 13, 4, 12, 6, 10, 5, 8, 7, 9, 2, 14, 3]
  have hp : FiniteAlphaPath 16 p 7 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 7, hp.toNat, rfl⟩

private theorem alphaCase_4_12 : ZeroAlphaPath 4 12 := by
  let p : Fin 17 → ℕ := ![1, 14, 3, 15, 0, 16, 2, 12, 5, 13, 4, 10, 8, 9, 6, 11, 7]
  have hp : FiniteAlphaPath 17 p 8 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 8, hp.toNat, rfl⟩

private theorem alphaCase_5_12 : ZeroAlphaPath 5 12 := by
  let p : Fin 18 → ℕ := ![12, 1, 15, 2, 17, 0, 16, 4, 14, 5, 13, 7, 11, 6, 9, 8, 10, 3]
  have hp : FiniteAlphaPath 18 p 8 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 8, hp.toNat, rfl⟩

private theorem alphaCase_6_12 : ZeroAlphaPath 6 12 := by
  let p : Fin 19 → ℕ := ![1, 16, 4, 15, 2, 18, 0, 17, 3, 13, 7, 10, 9, 11, 6, 14, 5, 12, 8]
  have hp : FiniteAlphaPath 19 p 9 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 9, hp.toNat, rfl⟩

private theorem alphaCase_7_12 : ZeroAlphaPath 7 12 := by
  let p : Fin 20 → ℕ := ![16, 3, 14, 4, 18, 2, 17, 0, 19, 1, 13, 5, 11, 9, 10, 7, 12, 8, 15, 6]
  have hp : FiniteAlphaPath 20 p 9 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 9, hp.toNat, rfl⟩

private theorem alphaCase_8_12 : ZeroAlphaPath 8 12 := by
  let p : Fin 21 → ℕ := ![1, 18, 4, 15, 5, 17, 2, 20, 0, 19, 3, 16, 7, 12, 8, 14, 6, 13, 10, 11, 9]
  have hp : FiniteAlphaPath 21 p 10 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 10, hp.toNat, rfl⟩

private theorem alphaCase_9_12 : ZeroAlphaPath 9 12 := by
  let p : Fin 22 → ℕ := ![18, 5, 13, 9, 12, 10, 11, 6, 16, 0, 21, 1, 20, 2, 19, 4, 15, 3, 17, 8, 14, 7]
  have hp : FiniteAlphaPath 22 p 10 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 10, hp.toNat, rfl⟩

private theorem alphaCase_10_12 : ZeroAlphaPath 10 12 := by
  let p : Fin 23 → ℕ := ![10, 13, 11, 12, 8, 16, 5, 19, 2, 22, 0, 21, 3, 18, 6, 15, 9, 14, 7, 17, 4, 20, 1]
  have hp : FiniteAlphaPath 23 p 11 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 11, hp.toNat, rfl⟩

private theorem alphaCase_11_12 : ZeroAlphaPath 11 12 := by
  let p : Fin 24 → ℕ := ![14, 11, 12, 10, 15, 7, 13, 9, 16, 4, 20, 0, 23, 1, 22, 5, 19, 6, 17, 8, 18, 3, 21, 2]
  have hp : FiniteAlphaPath 24 p 11 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 11, hp.toNat, rfl⟩

private theorem alphaCase_12_12 : ZeroAlphaPath 12 12 := by
  let p : Fin 25 → ℕ := ![7, 15, 9, 16, 6, 17, 12, 13, 11, 14, 10, 19, 0, 24, 1, 23, 2, 22, 4, 18, 3, 20, 8, 21, 5]
  have hp : FiniteAlphaPath 25 p 12 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 12, hp.toNat, rfl⟩

private theorem alphaCase_1_13 : ZeroAlphaPath 1 13 := by
  let p : Fin 15 → ℕ := ![12, 0, 14, 1, 11, 4, 13, 2, 10, 6, 7, 5, 8, 3, 9]
  have hp : FiniteAlphaPath 15 p 6 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 6, hp.toNat, rfl⟩

private theorem alphaCase_2_13 : ZeroAlphaPath 2 13 := by
  let p : Fin 16 → ℕ := ![5, 12, 0, 15, 1, 14, 4, 10, 6, 9, 7, 8, 3, 11, 2, 13]
  have hp : FiniteAlphaPath 16 p 7 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 7, hp.toNat, rfl⟩

private theorem alphaCase_3_13 : ZeroAlphaPath 3 13 := by
  let p : Fin 17 → ℕ := ![15, 1, 16, 0, 13, 4, 11, 3, 14, 2, 12, 6, 10, 5, 8, 7, 9]
  have hp : FiniteAlphaPath 17 p 7 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 7, hp.toNat, rfl⟩

private theorem alphaCase_4_13 : ZeroAlphaPath 4 13 := by
  let p : Fin 18 → ℕ := ![6, 13, 3, 14, 0, 17, 1, 16, 4, 12, 8, 9, 7, 10, 5, 11, 2, 15]
  have hp : FiniteAlphaPath 18 p 8 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 8, hp.toNat, rfl⟩

private theorem alphaCase_5_13 : ZeroAlphaPath 5 13 := by
  let p : Fin 19 → ℕ := ![14, 2, 16, 1, 17, 0, 18, 5, 11, 8, 9, 7, 12, 4, 15, 6, 10, 3, 13]
  have hp : FiniteAlphaPath 19 p 8 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 8, hp.toNat, rfl⟩

private theorem alphaCase_6_13 : ZeroAlphaPath 6 13 := by
  let p : Fin 20 → ℕ := ![1, 17, 4, 15, 3, 18, 0, 19, 2, 16, 6, 12, 9, 10, 8, 13, 5, 14, 7, 11]
  have hp : FiniteAlphaPath 20 p 9 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 9, hp.toNat, rfl⟩

private theorem alphaCase_7_13 : ZeroAlphaPath 7 13 := by
  let p : Fin 21 → ℕ := ![13, 8, 12, 6, 16, 2, 20, 0, 19, 4, 11, 9, 10, 7, 15, 3, 14, 5, 18, 1, 17]
  have hp : FiniteAlphaPath 21 p 9 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 9, hp.toNat, rfl⟩

private theorem alphaCase_8_13 : ZeroAlphaPath 8 13 := by
  let p : Fin 22 → ℕ := ![6, 12, 10, 11, 8, 16, 5, 19, 0, 21, 1, 18, 3, 15, 2, 20, 4, 13, 9, 14, 7, 17]
  have hp : FiniteAlphaPath 22 p 10 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 10, hp.toNat, rfl⟩

private theorem alphaCase_9_13 : ZeroAlphaPath 9 13 := by
  let p : Fin 23 → ℕ := ![12, 9, 11, 10, 14, 6, 17, 3, 20, 0, 22, 1, 19, 4, 16, 7, 13, 8, 15, 5, 18, 2, 21]
  have hp : FiniteAlphaPath 23 p 10 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 10, hp.toNat, rfl⟩

private theorem alphaCase_10_13 : ZeroAlphaPath 10 13 := by
  let p : Fin 24 → ℕ := ![1, 21, 4, 18, 7, 17, 5, 20, 2, 23, 0, 22, 3, 19, 6, 15, 8, 16, 10, 12, 11, 14, 9, 13]
  have hp : FiniteAlphaPath 24 p 11 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 11, hp.toNat, rfl⟩

private theorem alphaCase_11_13 : ZeroAlphaPath 11 13 := by
  let p : Fin 25 → ℕ := ![15, 9, 14, 10, 13, 11, 12, 5, 20, 1, 23, 0, 24, 3, 17, 8, 16, 6, 19, 7, 18, 2, 22, 4, 21]
  have hp : FiniteAlphaPath 25 p 11 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 11, hp.toNat, rfl⟩

private theorem alphaCase_12_13 : ZeroAlphaPath 12 13 := by
  let p : Fin 26 → ℕ := ![10, 15, 11, 14, 12, 13, 7, 17, 6, 22, 3, 25, 0, 24, 1, 21, 4, 19, 5, 18, 9, 16, 8, 20, 2, 23]
  have hp : FiniteAlphaPath 26 p 12 := by
    unfold FiniteAlphaPath Function.Injective
    decide +kernel
  exact ⟨finitePathLabel p, 12, hp.toNat, rfl⟩

private theorem zeroAlphaPath_small (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hab : a ≤ b) (hb13 : b ≤ 13) (hex : a ≠ 2 ∨ b ≠ 2) : ZeroAlphaPath a b := by
  interval_cases b
  · interval_cases a
    · exact alphaCase_1_1
  · interval_cases a
    · exact alphaCase_1_2
    · omega
  · interval_cases a
    · exact alphaCase_1_3
    · exact alphaCase_2_3
    · exact alphaCase_3_3
  · interval_cases a
    · exact alphaCase_1_4
    · exact alphaCase_2_4
    · exact alphaCase_3_4
    · exact alphaCase_4_4
  · interval_cases a
    · exact alphaCase_1_5
    · exact alphaCase_2_5
    · exact alphaCase_3_5
    · exact alphaCase_4_5
    · exact alphaCase_5_5
  · interval_cases a
    · exact alphaCase_1_6
    · exact alphaCase_2_6
    · exact alphaCase_3_6
    · exact alphaCase_4_6
    · exact alphaCase_5_6
    · exact alphaCase_6_6
  · interval_cases a
    · exact alphaCase_1_7
    · exact alphaCase_2_7
    · exact alphaCase_3_7
    · exact alphaCase_4_7
    · exact alphaCase_5_7
    · exact alphaCase_6_7
    · exact alphaCase_7_7
  · interval_cases a
    · exact alphaCase_1_8
    · exact alphaCase_2_8
    · exact alphaCase_3_8
    · exact alphaCase_4_8
    · exact alphaCase_5_8
    · exact alphaCase_6_8
    · exact alphaCase_7_8
    · exact alphaCase_8_8
  · interval_cases a
    · exact alphaCase_1_9
    · exact alphaCase_2_9
    · exact alphaCase_3_9
    · exact alphaCase_4_9
    · exact alphaCase_5_9
    · exact alphaCase_6_9
    · exact alphaCase_7_9
    · exact alphaCase_8_9
    · exact alphaCase_9_9
  · interval_cases a
    · exact alphaCase_1_10
    · exact alphaCase_2_10
    · exact alphaCase_3_10
    · exact alphaCase_4_10
    · exact alphaCase_5_10
    · exact alphaCase_6_10
    · exact alphaCase_7_10
    · exact alphaCase_8_10
    · exact alphaCase_9_10
    · exact alphaCase_10_10
  · interval_cases a
    · exact alphaCase_1_11
    · exact alphaCase_2_11
    · exact alphaCase_3_11
    · exact alphaCase_4_11
    · exact alphaCase_5_11
    · exact alphaCase_6_11
    · exact alphaCase_7_11
    · exact alphaCase_8_11
    · exact alphaCase_9_11
    · exact alphaCase_10_11
    · exact alphaCase_11_11
  · interval_cases a
    · exact alphaCase_1_12
    · exact alphaCase_2_12
    · exact alphaCase_3_12
    · exact alphaCase_4_12
    · exact alphaCase_5_12
    · exact alphaCase_6_12
    · exact alphaCase_7_12
    · exact alphaCase_8_12
    · exact alphaCase_9_12
    · exact alphaCase_10_12
    · exact alphaCase_11_12
    · exact alphaCase_12_12
  · interval_cases a
    · exact alphaCase_1_13
    · exact alphaCase_2_13
    · exact alphaCase_3_13
    · exact alphaCase_4_13
    · exact alphaCase_5_13
    · exact alphaCase_6_13
    · exact alphaCase_7_13
    · exact alphaCase_8_13
    · exact alphaCase_9_13
    · exact alphaCase_10_13
    · exact alphaCase_11_13
    · exact alphaCase_12_13
    · exact alphaCase_13_13

/-- Rosa's prescribed-zero alpha-path theorem, derived here from the symbolic
construction and explicit finite certificates. The exceptional central P5
corresponds exactly to arm lengths (2,2). -/
theorem rosa_zero_alpha_path (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hex : a ≠ 2 ∨ b ≠ 2) : ZeroAlphaPath a b := by
  by_cases hab : a ≤ b
  · by_cases hb14 : 14 ≤ b
    · exact (zeroAlphaPath_large_left b a hb14 ha hab).symm
    · exact zeroAlphaPath_small a b ha hb hab (by omega) hex
  · by_cases ha14 : 14 ≤ a
    · exact zeroAlphaPath_large_left a b ha14 hb (by omega)
    · exact (zeroAlphaPath_small b a hb ha (by omega) (by omega) hex.symm).symm

end Bounty
end

/- AlphaCut -/
section
namespace Bounty

noncomputable def NatGracefulPath.labelEquiv {n : ℕ} {p : ℕ → ℕ}
    (h : NatGracefulPath n p) : Fin n ≃ Fin n :=
  Equiv.ofBijective (fun i => ⟨p i.val, h.2.1 i.val i.isLt⟩) (by
    have hi : Function.Injective (fun i : Fin n => (⟨p i.val, h.2.1 i.val i.isLt⟩ : Fin n)) := by
      intro i j heq
      apply Fin.ext
      exact h.1 i.val j.val i.isLt j.isLt (congrArg Fin.val heq)
    exact ⟨hi, Finite.surjective_of_injective hi⟩)

lemma NatAlphaPath.not_adjacent_low {n k : ℕ} {p : ℕ → ℕ}
    (h : NatAlphaPath n p k) {i : ℕ} (hi : i+1 < n)
    (hl : p i ≤ k) : ¬ p (i+1) ≤ k := by
  have hc := h.2.2 (i+1) (by omega) hi
  simp only [Nat.add_sub_cancel] at hc
  omega

theorem NatAlphaPath.cut_bound {n k : ℕ} {p : ℕ → ℕ}
    (h : NatAlphaPath n p k) : k ≤ (n-1)/2 := by
  classical
  let e := h.1.labelEquiv
  let v (x : Fin (k+1)) : Fin n := e.symm ⟨x.val, by have := h.2.1; omega⟩
  have hv (x : Fin (k+1)) : p (v x).val = x.val := by
    have he := congrArg Fin.val (e.apply_symm_apply ⟨x.val, by have := h.2.1; omega⟩)
    exact he
  let g (x : Fin (k+1)) : Fin ((n+1)/2) := ⟨(v x).val/2, by have := (v x).isLt; omega⟩
  have hg : Function.Injective g := by
    intro x y heq
    have hh : (v x).val/2 = (v y).val/2 := congrArg Fin.val heq
    have hx := (v x).isLt
    have hy := (v y).isLt
    have hxl : p (v x).val ≤ k := by rw [hv]; omega
    have hyl : p (v y).val ≤ k := by rw [hv]; omega
    have hxy : (v x).val = (v y).val := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · have hstep : (v y).val = (v x).val+1 := by omega
        exact h.not_adjacent_low (by omega) hxl (by simpa only [← hstep] using hyl)
      · have hstep : (v x).val = (v y).val+1 := by omega
        exact h.not_adjacent_low (by omega) hyl (by simpa only [← hstep] using hxl)
    apply Fin.ext
    rw [← hv x, ← hv y, hxy]
  have hc := Fintype.card_le_of_injective g hg
  simp only [Fintype.card_fin] at hc
  have := h.2.1
  omega

lemma NatAlphaPath.low_parity {n k : ℕ} {p : ℕ → ℕ}
    (h : NatAlphaPath n p k) {i : ℕ} (hi : i < n) :
    (p i ≤ k ↔ if i%2=0 then p 0 ≤ k else ¬ p 0 ≤ k) := by
  induction i with
  | zero => simp
  | succ i ih =>
    have ih := ih (by omega)
    have hc := h.2.2 (i+1) (by omega) hi
    simp only [Nat.add_sub_cancel] at hc
    split_ifs at ih ⊢ <;> omega

theorem NatAlphaPath.cut_bound_odd_zero {n k z : ℕ} {p : ℕ → ℕ}
    (h : NatAlphaPath n p k) (hz : z < n) (hodd : z%2=1) (hzero : p z=0) :
    k+1 ≤ n/2 := by
  classical
  have hnlow : ¬ p 0 ≤ k := by
    have hh := (h.low_parity hz).1 (show p z ≤ k by omega)
    simpa only [hodd, Nat.one_ne_zero, ite_false] using hh
  let e := h.1.labelEquiv
  let v (x : Fin (k+1)) : Fin n := e.symm ⟨x.val, by have := h.2.1; omega⟩
  have hv (x : Fin (k+1)) : p (v x).val = x.val := by
    exact congrArg Fin.val (e.apply_symm_apply ⟨x.val, by have := h.2.1; omega⟩)
  have hvo (x : Fin (k+1)) : (v x).val%2=1 := by
    have hh := (h.low_parity (v x).isLt).1 (show p (v x).val ≤ k by rw [hv]; omega)
    split_ifs at hh <;> omega
  let g (x : Fin (k+1)) : Fin (n/2) := ⟨(v x).val/2, by have := (v x).isLt; have := hvo x; omega⟩
  have hg : Function.Injective g := by
    intro x y heq
    have hh : (v x).val/2 = (v y).val/2 := congrArg Fin.val heq
    have hxy : (v x).val = (v y).val := by have := hvo x; have := hvo y; omega
    apply Fin.ext
    rw [← hv x, ← hv y, hxy]
  have hc := Fintype.card_le_of_injective g hg
  simpa only [Fintype.card_fin] using hc

end Bounty
end

/- Endpoint -/
section
namespace Bounty

/-- A binary expansion of an integer label: complementary labels have odd sum. -/
def binaryLabel (s : ℕ) (p : ℕ → ℕ) (i : ℕ) (b : Bool) : ℕ :=
  if b then 2 * p i else 2 * s - 1 - 2 * p i

lemma binaryLabel_inj {s x y : ℕ} {b c : Bool} (hx : x < s) (hy : y < s)
    (h : (if b then 2*x else 2*s-1-2*x) =
      (if c then 2*y else 2*s-1-2*y)) : x = y ∧ b = c := by
  cases b <;> cases c <;> simp_all <;> omega

lemma binaryLabel_same {s : ℕ} {p : ℕ → ℕ} {i j : ℕ} (b : Bool)
    (hi : p i < s) (hj : p j < s) :
    Nat.dist (binaryLabel s p i b) (binaryLabel s p j b) = 2 * Nat.dist (p i) (p j) := by
  cases b <;> simp only [binaryLabel, Bool.false_eq_true, ↓reduceIte]
  all_goals unfold Nat.dist; omega

lemma binaryLabel_opposite {s : ℕ} {p : ℕ → ℕ} {i : ℕ} {b c : Bool}
    (h : b ≠ c) :
    Nat.dist (binaryLabel s p i b) (binaryLabel s p i c) =
      Nat.dist (2*p i) (2*s-1-2*p i) := by
  cases b <;> cases c <;> simp_all [binaryLabel, Nat.dist_comm]

lemma binaryLabel_pair_inj {s x y : ℕ} (hx : x < s) (hy : y < s)
    (h : Nat.dist (2*x) (2*s-1-2*x) = Nat.dist (2*y) (2*s-1-2*y)) : x = y := by
  unfold Nat.dist at h
  omega

lemma binaryLabel_pair_odd {s x : ℕ} (hx : x < s) :
    Nat.dist (2*x) (2*s-1-2*x) % 2 = 1 := by
  unfold Nat.dist
  omega

/-- The combinatorial data for replacing path vertices by pairs, possibly leaving
one vertex as a singleton. `index` is the old vertex and `side` chooses the label. -/
structure PathExpansion (s N : ℕ) (index : ℕ → ℕ) (side : ℕ → Bool) : Prop where
  index_lt : ∀ j, j < N → index j < s
  vertex_inj : ∀ i j, i < N → j < N → index i = index j → side i = side j → i = j
  edge_step : ∀ j, 0 < j → j < N →
    (index (j-1) = index j ∧ side (j-1) ≠ side j) ∨
    (index (j-1) + 1 = index j ∧ side (j-1) = side j)
  matching_inj : ∀ i j, 0 < i → i < N → 0 < j → j < N →
    index (i-1) = index i → index (j-1) = index j → index i = index j → i = j
  joining_inj : ∀ i j, 0 < i → i < N → 0 < j → j < N →
    index (i-1) + 1 = index i → index (j-1) + 1 = index j → index i = index j → i = j

lemma NatGracefulPath.expand {s N : ℕ} {p index : ℕ → ℕ} {side : ℕ → Bool}
    (hp : NatGracefulPath s p) (he : PathExpansion s N index side)
    (hb : ∀ j, j < N → binaryLabel s p (index j) (side j) < N) :
    NatGracefulPath N (fun j => binaryLabel s p (index j) (side j)) := by
  refine ⟨?_, hb, ?_⟩
  · intro i j hi hj h
    have h' := binaryLabel_inj (hp.2.1 _ (he.index_lt _ hi))
      (hp.2.1 _ (he.index_lt _ hj)) h
    exact he.vertex_inj i j hi hj (hp.1 _ _ (he.index_lt _ hi) (he.index_lt _ hj) h'.1) h'.2
  · intro i j hi hib hj hjb h
    dsimp only at h
    have hip := he.index_lt (i-1) (by omega)
    have hjp := he.index_lt (j-1) (by omega)
    have hiq := he.index_lt i hib
    have hjq := he.index_lt j hjb
    rcases he.edge_step i hi hib with ⟨hei, hbi⟩ | ⟨hei, hbi⟩ <;>
      rcases he.edge_step j hj hjb with ⟨hej, hbj⟩ | ⟨hej, hbj⟩
    · rw [hei, hej, binaryLabel_opposite hbi, binaryLabel_opposite hbj] at h
      have h' := binaryLabel_pair_inj (hp.2.1 _ hiq) (hp.2.1 _ hjq) h
      exact he.matching_inj i j hi hib hj hjb hei hej (hp.1 _ _ hiq hjq h')
    · rw [hei, binaryLabel_opposite hbi, hbj, binaryLabel_same _ (hp.2.1 _ hjp) (hp.2.1 _ hjq)] at h
      have ho := binaryLabel_pair_odd (hp.2.1 _ hiq)
      omega
    · rw [hej, binaryLabel_opposite hbj, hbi, binaryLabel_same _ (hp.2.1 _ hip) (hp.2.1 _ hiq)] at h
      have ho := binaryLabel_pair_odd (hp.2.1 _ hjq)
      omega
    · rw [hbi, hbj, binaryLabel_same _ (hp.2.1 _ hip) (hp.2.1 _ hiq),
        binaryLabel_same _ (hp.2.1 _ hjp) (hp.2.1 _ hjq)] at h
      have hi' : index (i-1) = index i - 1 := by omega
      have hj' : index (j-1) = index j - 1 := by omega
      rw [hi', hj'] at h
      have heq := hp.2.2 (index i) (index j) (by omega) hiq (by omega) hjq (by omega)
      exact he.joining_inj i j hi hib hj hjb hei hej heq


def evenSide (j : ℕ) : Bool := decide (j % 2 = (j / 2) % 2)
def evenLift (s : ℕ) (p : ℕ → ℕ) (j : ℕ) : ℕ :=
  binaryLabel s p (j / 2) (evenSide j)

lemma evenSide_eq_iff {i j : ℕ} : evenSide i = evenSide j ↔
    (i % 2 = (i / 2) % 2 ↔ j % 2 = (j / 2) % 2) := by
  exact decide_eq_decide

lemma evenExpansion (s : ℕ) : PathExpansion s (2*s) (fun j => j/2) evenSide := by
  constructor
  · intro j hj; omega
  · intro i j hi hj he hb
    rw [evenSide_eq_iff] at hb
    omega
  · intro j hj hb
    by_cases he : j % 2 = 0
    · right
      constructor
      · omega
      · rw [evenSide_eq_iff]; omega
    · left
      constructor
      · omega
      · intro heq
        rw [evenSide_eq_iff] at heq
        omega
  · intro i j hi hib hj hjb hiq hjq heq; omega
  · intro i j hi hib hj hjb hiq hjq heq; omega

lemma NatGracefulPath.evenLift {s : ℕ} {p : ℕ → ℕ} (hp : NatGracefulPath s p) :
    NatGracefulPath (2*s) (evenLift s p) := by
  apply hp.expand (evenExpansion s)
  intro j hj
  have h := hp.2.1 (j/2) (by omega)
  unfold binaryLabel
  split_ifs <;> omega

def oddIndex (r j : ℕ) : ℕ := if j ≤ 2*r then j/2 else (j+1)/2
def oddSide (r j : ℕ) : Bool := decide (j % 2 = (oddIndex r j + r) % 2)
def oddLift (s : ℕ) (p : ℕ → ℕ) (r j : ℕ) : ℕ :=
  binaryLabel s p (oddIndex r j) (oddSide r j)

lemma oddSide_eq_iff {r i j : ℕ} : oddSide r i = oddSide r j ↔
    (i % 2 = (oddIndex r i+r) % 2 ↔ j % 2 = (oddIndex r j+r) % 2) := by
  exact decide_eq_decide

lemma oddExpansion {s r : ℕ} (hr : r < s) :
    PathExpansion s (2*s-1) (oddIndex r) (oddSide r) := by
  constructor
  · intro j hj
    unfold oddIndex
    split_ifs <;> omega
  · intro i j hi hj he hb
    rw [oddSide_eq_iff] at hb
    unfold oddIndex at *
    split_ifs at * <;> omega
  · intro j hj hb
    by_cases he : oddIndex r (j-1) = oddIndex r j
    · left
      refine ⟨he, ?_⟩
      intro heq
      rw [oddSide_eq_iff] at heq
      unfold oddIndex at *
      split_ifs at * <;> omega
    · right
      constructor
      · unfold oddIndex at *
        split_ifs at * <;> omega
      · rw [oddSide_eq_iff]
        unfold oddIndex at *
        split_ifs at * <;> omega
  · intro i j hi hib hj hjb hiq hjq heq
    unfold oddIndex at *
    split_ifs at * <;> omega
  · intro i j hi hib hj hjb hiq hjq heq
    unfold oddIndex at *
    split_ifs at * <;> omega

lemma NatGracefulPath.oddLift {s r : ℕ} {p : ℕ → ℕ} (hp : NatGracefulPath s p)
    (hr : r < s) (hz : p r = 0) : NatGracefulPath (2*s-1) (oddLift s p r) := by
  apply hp.expand (oddExpansion hr)
  intro j hj
  have hi := (oddExpansion hr).index_lt j hj
  have h := hp.2.1 (oddIndex r j) hi
  unfold binaryLabel
  split_ifs with hb
  · omega
  · have hne : p (oddIndex r j) ≠ 0 := by
      intro he
      have hiq := hp.1 (oddIndex r j) r hi hr (he.trans hz.symm)
      have hjq : j = 2*r := by
        unfold oddIndex at hiq
        split_ifs at hiq <;> omega
      subst j
      simp only [oddSide, oddIndex, le_refl, ↓reduceIte, Nat.mul_mod_right, decide_eq_true_eq] at hb
      omega
    omega


/-- A graceful path together with the positions of its extreme labels. -/
structure SupportedPath (n : ℕ) where
  label : ℕ → ℕ
  root : ℕ
  top : ℕ
  graceful : NatGracefulPath n label
  root_lt : root < n
  root_label : label root = 0
  top_lt : top < n
  top_label : label top = n-1
  neighbors : n = 1 ∨ Nat.dist root top = 1

def SupportedPath.start {n : ℕ} (P : SupportedPath n) : ℕ := P.label 0

def SupportedPath.parity {n : ℕ} (P : SupportedPath n) : ℕ := P.root % 2

lemma SupportedPath.pos {n : ℕ} (P : SupportedPath n) : 0 < n := by
  have := P.root_lt
  omega

lemma SupportedPath.start_lt {n : ℕ} (P : SupportedPath n) : P.start < n :=
  P.graceful.2.1 0 P.pos

lemma SupportedPath.parity_lt {n : ℕ} (P : SupportedPath n) : P.parity < 2 := by
  exact Nat.mod_lt _ (by decide)

lemma NatGracefulPath.complement {s : ℕ} {p : ℕ → ℕ} (hp : NatGracefulPath s p) :
    NatGracefulPath s (fun j => s-1-p j) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j hi hj he
    dsimp only at he
    exact hp.1 i j hi hj (by have := hp.2.1 i hi; have := hp.2.1 j hj; omega)
  · intro i hi
    dsimp only
    have := hp.2.1 i hi
    omega
  · intro i j hi hib hj hjb he
    have hip := hp.2.1 (i-1) (by omega)
    have hiq := hp.2.1 i hib
    have hjp := hp.2.1 (j-1) (by omega)
    have hjq := hp.2.1 j hjb
    apply hp.2.2 i j hi hib hj hjb
    dsimp only at he
    unfold Nat.dist at *
    omega

def SupportedPath.complement {n : ℕ} (P : SupportedPath n) : SupportedPath n where
  label j := n-1-P.label j
  root := P.top
  top := P.root
  graceful := P.graceful.complement
  root_lt := P.top_lt
  root_label := by simp [P.top_label]
  top_lt := P.root_lt
  top_label := by simp [P.root_label]
  neighbors := P.neighbors.imp id (by rw [Nat.dist_comm]; exact id)

lemma SupportedPath.complement_start {n : ℕ} (P : SupportedPath n) :
    P.complement.start = n-1-P.start := rfl

lemma SupportedPath.complement_parity {n : ℕ} (P : SupportedPath n) (hn : 1 < n) :
    P.complement.parity = 1-P.parity := by
  have h := P.neighbors
  unfold Nat.dist at h
  dsimp [SupportedPath.complement, SupportedPath.parity]
  omega

lemma evenLift_root {s r : ℕ} {p : ℕ → ℕ} (hz : p r = 0) :
    evenLift s p (2*r+r%2) = 0 := by
  have hi : (2*r+r%2)/2 = r := by omega
  have hb : evenSide (2*r+r%2) = true := by
    simp only [evenSide, decide_eq_true_eq]
    omega
  simp [evenLift, hi, hb, binaryLabel, hz]

lemma evenLift_top {s r : ℕ} {p : ℕ → ℕ} (hz : p r = 0) :
    evenLift s p (2*r+(1-r%2)) = 2*s-1 := by
  have hi : (2*r+(1-r%2))/2 = r := by omega
  have hb : evenSide (2*r+(1-r%2)) = false := by
    simp only [evenSide, decide_eq_false_iff_not]
    omega
  simp [evenLift, hi, hb, binaryLabel, hz]

def SupportedPath.double {s : ℕ} (P : SupportedPath s) : SupportedPath (2*s) where
  label := evenLift s P.label
  root := 2*P.root+P.root%2
  top := 2*P.root+(1-P.root%2)
  graceful := P.graceful.evenLift
  root_lt := by have := P.root_lt; omega
  root_label := evenLift_root P.root_label
  top_lt := by have := P.root_lt; omega
  top_label := evenLift_top P.root_label
  neighbors := by right; unfold Nat.dist; omega

lemma SupportedPath.double_start {s : ℕ} (P : SupportedPath s) :
    P.double.start = 2*P.start := by
  simp [SupportedPath.double, SupportedPath.start, evenLift, evenSide, binaryLabel]

lemma SupportedPath.double_parity {s : ℕ} (P : SupportedPath s) :
    P.double.parity = P.parity := by
  dsimp [SupportedPath.double, SupportedPath.parity]
  omega

lemma oddLift_root {s r : ℕ} {p : ℕ → ℕ} (hz : p r = 0) :
    oddLift s p r (2*r) = 0 := by
  have hi : oddIndex r (2*r) = r := by simp [oddIndex]
  have hb : oddSide r (2*r) = true := by
    simp only [oddSide, hi, decide_eq_true_eq]
    omega
  simp [oddLift, hi, hb, binaryLabel, hz]

lemma oddLift_top {s r t : ℕ} {p : ℕ → ℕ} (ht : p t = s-1)
    (hrt : Nat.dist r t = 1) :
    oddLift s p r (if t < r then 2*t+1 else 2*t-1) = 2*(s-1) := by
  have hi : oddIndex r (if t < r then 2*t+1 else 2*t-1) = t := by
    unfold oddIndex Nat.dist at *
    split_ifs <;> omega
  have hb : oddSide r (if t < r then 2*t+1 else 2*t-1) = true := by
    simp only [oddSide, hi, decide_eq_true_eq]
    unfold Nat.dist at hrt
    split_ifs <;> omega
  simp [oddLift, hi, hb, binaryLabel, ht]

def SupportedPath.oddDouble {s : ℕ} (P : SupportedPath s) (hs : 1 < s) :
    SupportedPath (2*s-1) where
  label := oddLift s P.label P.root
  root := 2*P.root
  top := if P.top < P.root then 2*P.top+1 else 2*P.top-1
  graceful := P.graceful.oddLift P.root_lt P.root_label
  root_lt := by have := P.root_lt; omega
  root_label := oddLift_root P.root_label
  top_lt := by
    have hr := P.root_lt
    have ht := P.top_lt
    have h := P.neighbors
    unfold Nat.dist at h
    split_ifs <;> omega
  top_label := by
    rw [oddLift_top P.top_label (P.neighbors.resolve_left (by omega))]
    omega
  neighbors := by
    right
    have h := P.neighbors
    unfold Nat.dist at *
    split_ifs <;> omega

lemma SupportedPath.oddDouble_start_even {s : ℕ} (P : SupportedPath s) (hs : 1 < s)
    (he : P.parity = 0) : (P.oddDouble hs).start = 2*P.start := by
  have hi : oddIndex P.root 0 = 0 := by simp [oddIndex]
  have hb : oddSide P.root 0 = true := by
    simp only [oddSide, hi, Nat.zero_mod, zero_add, decide_eq_true_eq]
    exact he.symm
  simp [SupportedPath.oddDouble, SupportedPath.start, oddLift, hi, hb, binaryLabel]

lemma SupportedPath.oddDouble_start_odd {s : ℕ} (P : SupportedPath s) (hs : 1 < s)
    (he : P.parity = 1) : (P.oddDouble hs).start = 2*s-1-2*P.start := by
  have hi : oddIndex P.root 0 = 0 := by simp [oddIndex]
  have hb : oddSide P.root 0 = false := by
    simp only [oddSide, hi, Nat.zero_mod, zero_add, decide_eq_false_iff_not]
    dsimp [SupportedPath.parity] at he
    omega
  simp [SupportedPath.oddDouble, SupportedPath.start, oddLift, hi, hb, binaryLabel]

lemma SupportedPath.oddDouble_parity {s : ℕ} (P : SupportedPath s) (hs : 1 < s) :
    (P.oddDouble hs).parity = 0 := by
  dsimp [SupportedPath.oddDouble, SupportedPath.parity]
  omega


/-- A prescribed endpoint and prescribed parity of the position of zero. -/
def Endpoint (n a e : ℕ) : Prop :=
  ∃ P : SupportedPath n, P.start = a ∧ P.parity = e

lemma Endpoint.bound {n a e : ℕ} (h : Endpoint n a e) : a < n ∧ e < 2 := by
  rcases h with ⟨P, rfl, rfl⟩
  exact ⟨P.start_lt, P.parity_lt⟩

lemma Endpoint.complement {n a e : ℕ} (h : Endpoint n a e) (hn : 1 < n) :
    Endpoint n (n-1-a) (1-e) := by
  rcases h with ⟨P, ha, he⟩
  exact ⟨P.complement, by rw [P.complement_start, ha],
    by rw [P.complement_parity hn, he]⟩

lemma Endpoint.double_even {n a e : ℕ} (h : Endpoint n a e) :
    Endpoint (2*n) (2*a) e := by
  rcases h with ⟨P, ha, he⟩
  exact ⟨P.double, by rw [P.double_start, ha], by rw [P.double_parity, he]⟩

lemma Endpoint.double_odd {n a e : ℕ} (h : Endpoint n a e) (hn : 1 < n) :
    Endpoint (2*n) (2*a+1) e := by
  have hb := h.bound
  have h' := ((h.complement hn).double_even).complement (by omega)
  convert h' using 1 <;> omega

lemma Endpoint.odd_even_zero {n a : ℕ} (h : Endpoint n a 0) (hn : 1 < n) :
    Endpoint (2*n-1) (2*a) 0 := by
  rcases h with ⟨P, ha, he⟩
  exact ⟨P.oddDouble hn, by rw [P.oddDouble_start_even hn he, ha], P.oddDouble_parity hn⟩

lemma Endpoint.odd_even {n a e : ℕ} (h : Endpoint n a e) (hn : 1 < n) :
    Endpoint (2*n-1) (2*a) e := by
  have hb := h.bound
  rcases (by omega : e = 0 ∨ e = 1) with rfl | rfl
  · exact h.odd_even_zero hn
  · have h' := ((h.complement hn).odd_even_zero hn).complement (by omega)
    convert h' using 1; omega

lemma Endpoint.odd_odd_left {n a : ℕ} (h : Endpoint n a 0) (hn : 1 < n)
    (ha : a+1 < n) : Endpoint (2*n-1) (2*a+1) 0 := by
  rcases h.complement hn with ⟨P, hp, he⟩
  have he' : P.parity = 1 := by simpa using he
  refine ⟨P.oddDouble hn, ?_, P.oddDouble_parity hn⟩
  rw [P.oddDouble_start_odd hn he', hp]
  omega

lemma Endpoint.odd_odd_right {n a : ℕ} (h : Endpoint n (a+1) 1) (hn : 1 < n) :
    Endpoint (2*n-1) (2*a+1) 1 := by
  rcases h with ⟨P, hp, he⟩
  refine ⟨(P.oddDouble hn).complement, ?_, ?_⟩
  · rw [SupportedPath.complement_start, P.oddDouble_start_odd hn he, hp]
    have := P.start_lt
    rw [hp] at this
    omega
  · rw [SupportedPath.complement_parity _ (by omega), P.oddDouble_parity hn]

/-- The second clause is the inductive bridge required for odd endpoints. -/
def AllEndpoints (n : ℕ) : Prop :=
  (∀ a, a < n → ∃ e, Endpoint n a e) ∧
  ∀ a, a+1 < n → Endpoint n a 0 ∨ Endpoint n (a+1) 1

lemma AllEndpoints.double {n : ℕ} (h : AllEndpoints n) (hn : 1 < n) :
    AllEndpoints (2*n) := by
  constructor
  · intro a ha
    obtain ⟨e, he⟩ := h.1 (a/2) (by omega)
    refine ⟨e, ?_⟩
    rcases (by omega : a = 2*(a/2) ∨ a = 2*(a/2)+1) with hae | hae
    · rw [hae]
      exact he.double_even
    · rw [hae]
      exact he.double_odd hn
  · intro a ha
    by_cases he : a % 2 = 0
    · obtain ⟨e, hep⟩ := h.1 (a/2) (by omega)
      have hb := hep.bound
      rcases (by omega : e = 0 ∨ e = 1) with rfl | rfl
      · left
        convert hep.double_even using 1; omega
      · right
        convert hep.double_odd hn using 1; omega
    · rcases h.2 (a/2) (by omega) with hp | hp
      · left
        convert hp.double_odd hn using 1; omega
      · right
        convert hp.double_even using 1; omega

lemma AllEndpoints.oddDouble {n : ℕ} (h : AllEndpoints n) (hn : 1 < n) :
    AllEndpoints (2*n-1) := by
  constructor
  · intro a ha
    by_cases he : a % 2 = 0
    · obtain ⟨e, hep⟩ := h.1 (a/2) (by omega)
      refine ⟨e, ?_⟩
      convert hep.odd_even hn using 1; omega
    · rcases h.2 (a/2) (by omega) with hp | hp
      · refine ⟨0, ?_⟩
        convert hp.odd_odd_left hn (by omega) using 1; omega
      · refine ⟨1, ?_⟩
        convert hp.odd_odd_right hn using 1; omega
  · intro a ha
    by_cases he : a % 2 = 0
    · rcases h.2 (a/2) (by omega) with hp | hp
      · left
        convert hp.odd_even hn using 1; omega
      · right
        convert hp.odd_odd_right hn using 1; omega
    · rcases h.2 (a/2) (by omega) with hp | hp
      · left
        convert hp.odd_odd_left hn (by omega) using 1; omega
      · right
        convert hp.odd_even hn using 1; omega

def singletonPath : SupportedPath 1 where
  label := fun _ => 0
  root := 0
  top := 0
  graceful := ⟨by intros; omega, by intros; dsimp; omega, by intros; omega⟩
  root_lt := by decide
  root_label := rfl
  top_lt := by decide
  top_label := rfl
  neighbors := Or.inl rfl

lemma endpoint_one : Endpoint 1 0 0 := ⟨singletonPath, rfl, rfl⟩

lemma allEndpoints_one : AllEndpoints 1 := by
  constructor
  · intro a ha
    have : a = 0 := by omega
    subst a
    exact ⟨0, endpoint_one⟩
  · intros; omega

lemma allEndpoints_two : AllEndpoints 2 := by
  have h0 : Endpoint 2 0 0 := endpoint_one.double_even
  have h1 : Endpoint 2 1 1 := h0.complement (by omega)
  constructor
  · intro a ha
    interval_cases a
    · exact ⟨0, h0⟩
    · exact ⟨1, h1⟩
  · intro a ha
    have : a = 0 := by omega
    subst a
    exact Or.inl h0

/-- Every path has a graceful labeling with any prescribed endpoint label.
The proof simultaneously maintains the adjacent-label parity bridge. -/
theorem allEndpoints (n : ℕ) (hn : 0 < n) : AllEndpoints n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h1 : n = 1
    · subst n
      exact allEndpoints_one
    by_cases h2 : n = 2
    · subst n
      exact allEndpoints_two
    by_cases he : n % 2 = 0
    · have hsmall : 1 < n/2 := by omega
      have h' := (ih (n/2) (by omega) (by omega)).double hsmall
      convert h' using 1; omega
    · have hsmall : 1 < (n+1)/2 := by omega
      have h' := (ih ((n+1)/2) (by omega) (by omega)).oddDouble hsmall
      convert h' using 1; omega

theorem exists_graceful_path_endpoint {n a : ℕ} (ha : a < n) :
    ∃ p : ℕ → ℕ, NatGracefulPath n p ∧ p 0 = a := by
  obtain ⟨e, P, hp, _⟩ := (allEndpoints n (by omega)).1 a ha
  exact ⟨P.label, P.graceful, hp⟩

end Bounty
end

/- ThreeSpider -/
section
namespace Bounty

/-- Natural-index certificate for a graph with one lower-index parent per positive vertex. -/
def NatParentCertificate (N : ℕ) (parent f : ℕ → ℕ) : Prop :=
  (∀ i j, i ≤ N → j ≤ N → f i = f j → i = j) ∧
  (∀ i, i ≤ N → f i ≤ N) ∧
  ∀ i j, 0 < i → i ≤ N → 0 < j → j ≤ N →
    Nat.dist (f (parent i)) (f i) = Nat.dist (f (parent j)) (f j) → i = j

structure ParentExpansion (N M : ℕ) (parent newParent index : ℕ → ℕ) (side : ℕ → Bool) : Prop where
  index_le : ∀ j, j ≤ M → index j ≤ N
  vertex_inj : ∀ i j, i ≤ M → j ≤ M → index i = index j → side i = side j → i = j
  edge_step : ∀ j, 0 < j → j ≤ M →
    (index (newParent j) = index j ∧ side (newParent j) ≠ side j) ∨
    (0 < index j ∧ index (newParent j) = parent (index j) ∧ side (newParent j) = side j)
  matching_inj : ∀ i j, 0 < i → i ≤ M → 0 < j → j ≤ M →
    index (newParent i) = index i → index (newParent j) = index j → index i = index j → i = j
  joining_inj : ∀ i j, 0 < i → i ≤ M → 0 < j → j ≤ M →
    index (newParent i) = parent (index i) →
    index (newParent j) = parent (index j) → index i = index j → i = j

theorem NatParentCertificate.expand {N M : ℕ} {parent newParent f index : ℕ → ℕ} {side : ℕ → Bool}
    (hf : NatParentCertificate N parent f) (he : ParentExpansion N M parent newParent index side)
    (hp : ∀ j, 0 < j → j ≤ M → newParent j < j)
    (hb : ∀ j, j ≤ M → binaryLabel (N+1) f (index j) (side j) ≤ M) :
    NatParentCertificate M newParent (fun j => binaryLabel (N+1) f (index j) (side j)) := by
  refine ⟨?_, hb, ?_⟩
  · intro i j hi hj h
    have hiq := he.index_le i hi
    have hjq := he.index_le j hj
    have hh := binaryLabel_inj (by have := hf.2.1 _ hiq; omega)
      (by have := hf.2.1 _ hjq; omega) h
    exact he.vertex_inj i j hi hj (hf.1 _ _ hiq hjq hh.1) hh.2
  · intro i j hi hib hj hjb h
    have hip := he.index_le (newParent i) (by have := hp i hi hib; omega)
    have hjp := he.index_le (newParent j) (by have := hp j hj hjb; omega)
    have hiq := he.index_le i hib
    have hjq := he.index_le j hjb
    have hfi : f (index i) < N+1 := by have := hf.2.1 _ hiq; omega
    have hfj : f (index j) < N+1 := by have := hf.2.1 _ hjq; omega
    have hfip : f (index (newParent i)) < N+1 := by have := hf.2.1 _ hip; omega
    have hfjp : f (index (newParent j)) < N+1 := by have := hf.2.1 _ hjp; omega
    dsimp only at h
    rcases he.edge_step i hi hib with ⟨hei,hbi⟩ | ⟨hipos,hei,hbi⟩ <;>
      rcases he.edge_step j hj hjb with ⟨hej,hbj⟩ | ⟨hjpos,hej,hbj⟩
    · rw [hei,hej,binaryLabel_opposite hbi,binaryLabel_opposite hbj] at h
      have hh := binaryLabel_pair_inj hfi hfj h
      exact he.matching_inj i j hi hib hj hjb hei hej (hf.1 _ _ hiq hjq hh)
    · rw [hei,binaryLabel_opposite hbi,hbj,binaryLabel_same _ hfjp hfj] at h
      have ho := binaryLabel_pair_odd hfi
      omega
    · rw [hej,binaryLabel_opposite hbj,hbi,binaryLabel_same _ hfip hfi] at h
      have ho := binaryLabel_pair_odd hfj
      omega
    · rw [hbi,hbj,binaryLabel_same _ hfip hfi,binaryLabel_same _ hfjp hfj,hei,hej] at h
      have hh := hf.2.2 (index i) (index j) hipos hiq hjpos hjq (by omega)
      exact he.joining_inj i j hi hib hj hjb hei hej hh

def subdivisionParent (parent : ℕ → ℕ) (j : ℕ) : ℕ :=
  if j%2=0 then j-1 else 2*parent ((j+1)/2)
def subdivisionIndex (j : ℕ) : ℕ := (j+1)/2
def subdivisionSide (color : ℕ → Bool) (j : ℕ) : Bool :=
  if j%2=0 then color ((j+1)/2) else !(color ((j+1)/2))

theorem subdivisionParent_lt {N : ℕ} {parent : ℕ → ℕ}
    (hp : ∀ j, 0 < j → j ≤ N → parent j < j)
    {j : ℕ} (hj : 0 < j) (hb : j ≤ 2*N) : subdivisionParent parent j < j := by
  unfold subdivisionParent
  split_ifs with he
  · omega
  · have hh := hp ((j+1)/2) (by omega) (by omega)
    omega

theorem subdivisionExpansion {N : ℕ} {parent : ℕ → ℕ} {color : ℕ → Bool}
    (hp : ∀ j, 0 < j → j ≤ N → parent j < j)
    (hc : ∀ j, 0 < j → j ≤ N → color (parent j) = !(color j)) :
    ParentExpansion N (2*N) parent (subdivisionParent parent) subdivisionIndex (subdivisionSide color) := by
  constructor
  · intro j hj; dsimp [subdivisionIndex]; omega
  · intro i j hi hj he hb
    dsimp [subdivisionIndex] at he
    by_cases hi2 : i%2=0 <;> by_cases hj2 : j%2=0
    · omega
    · simp only [subdivisionSide, ite_eq_left hi2, ite_eq_right hj2, he] at hb
      cases color ((j+1)/2) <;> simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero] at hb
    · simp only [subdivisionSide, ite_eq_right hi2, ite_eq_left hj2, he] at hb
      cases color ((j+1)/2) <;> simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero] at hb
    · omega
  · intro j hj hb
    by_cases hj2 : j%2=0
    · left
      have hidx : (j-1+1)/2 = (j+1)/2 := by omega
      have hodd : ¬(j-1)%2=0 := by omega
      simp only [subdivisionParent, ite_eq_left hj2, subdivisionIndex, hidx]
      constructor
      · trivial
      · simp only [subdivisionSide, ite_eq_right hodd, ite_eq_left hj2, hidx]
        cases color ((j+1)/2) <;> decide
    · right
      have hi : 0 < (j+1)/2 := by omega
      have hib : (j+1)/2 ≤ N := by omega
      have hidx : (2*parent ((j+1)/2)+1)/2 = parent ((j+1)/2) := by omega
      have heven : (2*parent ((j+1)/2))%2=0 := by omega
      simp only [subdivisionParent, ite_eq_right hj2, subdivisionIndex, hidx]
      refine ⟨hi, trivial, ?_⟩
      simp only [subdivisionSide, ite_eq_left heven, ite_eq_right hj2, hidx]
      exact hc _ hi hib
  · intro i j hi hib hj hjb hiq hjq heq
    have hpi := hp ((i+1)/2) (by omega) (by omega)
    have hpj := hp ((j+1)/2) (by omega) (by omega)
    dsimp [subdivisionIndex, subdivisionParent] at hiq hjq heq
    split_ifs at hiq hjq <;> omega
  · intro i j hi hib hj hjb hiq hjq heq
    have hpi := hp ((i+1)/2) (by omega) (by omega)
    have hpj := hp ((j+1)/2) (by omega) (by omega)
    dsimp [subdivisionIndex, subdivisionParent] at hiq hjq heq
    split_ifs at hiq hjq <;> omega

def subdivisionLabel (N : ℕ) (f : ℕ → ℕ) (color : ℕ → Bool) (j : ℕ) : ℕ :=
  binaryLabel (N+1) f (subdivisionIndex j) (subdivisionSide color j)

theorem NatParentCertificate.subdivide {N : ℕ} {parent f : ℕ → ℕ} {color : ℕ → Bool}
    (hf : NatParentCertificate N parent f)
    (hp : ∀ j, 0 < j → j ≤ N → parent j < j)
    (hc : ∀ j, 0 < j → j ≤ N → color (parent j) = !(color j))
    (hc0 : color 0 = true) (hf0 : f 0 = 0) :
    NatParentCertificate (2*N) (subdivisionParent parent) (subdivisionLabel N f color) := by
  apply hf.expand (subdivisionExpansion hp hc) (fun j hj hb => subdivisionParent_lt hp hj hb)
  intro j hj
  have hi : subdivisionIndex j ≤ N := by dsimp [subdivisionIndex]; omega
  have hv := hf.2.1 _ hi
  unfold binaryLabel
  split_ifs with hs
  · omega
  · have hn : f (subdivisionIndex j) ≠ 0 := by
      intro hz
      have he := hf.1 _ 0 hi (by omega) (hz.trans hf0.symm)
      have hj0 : j=0 := by dsimp [subdivisionIndex] at he; omega
      subst j
      simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, subdivisionSide,hc0] at hs
    omega

theorem subdivisionLabel_zero {N : ℕ} {f : ℕ → ℕ} {color : ℕ → Bool}
    (hc0 : color 0 = true) (hf0 : f 0 = 0) : subdivisionLabel N f color 0 = 0 := by
  simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, subdivisionLabel,binaryLabel,subdivisionIndex,subdivisionSide,hc0,hf0]


def threeParent (a b : ℕ) (j : ℕ) : ℕ :=
  if j=1 ∨ j=a+1 ∨ j=a+b+1 then 0 else j-1

def threeSpider (a b c : ℕ) : SimpleGraph (Fin (a+b+c+1)) :=
  parentGraph (a+b+c) (threeParent a b)

def ThreeZero (a b c : ℕ) : Prop :=
  ∃ f : ℕ → ℕ, NatParentCertificate (a+b+c) (threeParent a b) f ∧ f 0=0

theorem threeParent_lt (a b j : ℕ) (hj : 0<j) : threeParent a b j<j := by
  unfold threeParent
  split_ifs <;> omega

def threeLevel (a b j : ℕ) : ℕ :=
  if j≤a then j else if j≤a+b then j-a else j-a-b

theorem threeLevel_parent {a b c j : ℕ} (ha : 0<a) (hb : 0<b) (hc : 0<c)
    (hj : 0<j) (hjb : j≤a+b+c) :
    threeLevel a b (threeParent a b j)+1 = threeLevel a b j := by
  unfold threeParent threeLevel
  split_ifs <;> omega

def threeColor (a b j : ℕ) : Bool := decide (threeLevel a b j % 2 = 0)

theorem threeColor_zero (a b : ℕ) : threeColor a b 0 = true := by
  simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, Bounty.subdivisionLabel_zero, threeColor,threeLevel]

theorem threeColor_parent {a b c j : ℕ} (ha : 0<a) (hb : 0<b) (hc : 0<c)
    (hj : 0<j) (hjb : j≤a+b+c) :
    threeColor a b (threeParent a b j) = !(threeColor a b j) := by
  have hl := threeLevel_parent ha hb hc hj hjb
  by_cases h0 : threeLevel a b j % 2 = 0
  · have h1 : ¬threeLevel a b (threeParent a b j)%2=0 := by omega
    simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, Bounty.subdivisionLabel_zero, Bounty.threeColor_zero, threeColor,h0,h1]
  · have h1 : threeLevel a b (threeParent a b j)%2=0 := by omega
    simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, Bounty.subdivisionLabel_zero, Bounty.threeColor_zero, threeColor,h0,h1]

theorem subdivision_threeParent (a b : ℕ) :
    subdivisionParent (threeParent a b) = threeParent (2*a) (2*b) := by
  funext j
  unfold subdivisionParent threeParent
  split_ifs <;> omega

theorem ThreeZero.subdivide {a b c : ℕ} (h : ThreeZero a b c)
    (ha : 0<a) (hb : 0<b) (hc : 0<c) : ThreeZero (2*a) (2*b) (2*c) := by
  obtain ⟨f,hf,hf0⟩ := h
  refine ⟨subdivisionLabel (a+b+c) f (threeColor a b), ?_, subdivisionLabel_zero (threeColor_zero a b) hf0⟩
  have hh := hf.subdivide (fun j hj _ => threeParent_lt a b j hj)
    (fun j hj hjb => threeColor_parent ha hb hc hj hjb) (threeColor_zero a b) hf0
  rw [subdivision_threeParent] at hh
  convert hh using 1 <;> omega

end Bounty
end

/- ParentCertificate -/
section
namespace Bounty
open Math15.Graceful

theorem NatParentCertificate.isGracefulLabeling {N : ℕ} {parent f : ℕ → ℕ}
    (hf : NatParentCertificate N parent f)
    (hp : ∀ j, 0<j → j≤N → parent j<j) :
    IsGracefulLabeling (parentGraph N parent) (fun v => f v.val) := by
  apply labeling_of_injective_differences
  · intro i j heq
    apply Fin.ext
    exact hf.1 _ _ (by omega) (by omega) heq
  · intro i
    rw [parentGraph_edgeCount N parent hp]
    exact hf.2.1 i.val (by omega)
  · intro e e' ho ha ho' ha' heq
    have he : parent e.2.val=e.1.val := by
      rcases ha with h | h
      · exact h.2
      · have : e.1.val<e.2.val := ho
        omega
    have he' : parent e'.2.val=e'.1.val := by
      rcases ha' with h | h
      · exact h.2
      · have : e'.1.val<e'.2.val := ho'
        omega
    have hright : e.2.val=e'.2.val := by
      apply hf.2.2
      · have : e.1.val<e.2.val := ho
        omega
      · omega
      · have : e'.1.val<e'.2.val := ho'
        omega
      · omega
      · simpa only [he, he'] using heq
    apply Prod.ext
    · apply Fin.ext
      rw [← he, ← he', hright]
    · exact Fin.ext hright

theorem ThreeZero.isGraceful {a b c : ℕ} (h : ThreeZero a b c) :
    IsGraceful (threeSpider a b c) := by
  obtain ⟨f,hf,_⟩ := h
  exact (hf.isGracefulLabeling (fun j hj _ => threeParent_lt a b j hj)).isGraceful

end Bounty
end

/- AllTwoComplete -/
section
namespace Bounty

theorem all_two_arms_graceful (d : ℕ) :
    Math15.Graceful.IsGraceful (doubleSpider 2 2 2 d 2 2) := by
  have hf : NatParentCertificate (doubleSpiderEdges 2 2 2 d 2 2)
      (doubleSpiderParent 2 2 2 d 2 2) (allTwoLabel d) := by
    refine ⟨?_, ?_, ?_⟩
    · intro i j hi hj heq
      apply allTwoLabel_injective (d:=d) (by simpa [doubleSpiderEdges] using hi)
        (by simpa [doubleSpiderEdges] using hj) heq
    · intro j hj
      have := allTwoLabel_bound (d:=d) (j:=j) (by dsimp [doubleSpiderEdges] at hj; omega)
      dsimp [doubleSpiderEdges]
      omega
    · intro i j hi hib hj hjb heq
      have hib' : i≤d+10 := by dsimp [doubleSpiderEdges] at hib; omega
      have hjb' : j≤d+10 := by dsimp [doubleSpiderEdges] at hjb; omega
      rw [allTwoLabel_diff hi hib', allTwoLabel_diff hj hjb'] at heq
      exact allTwoDiff_injective hi hib' hj hjb' heq
  exact (hf.isGracefulLabeling (fun j hj _ => doubleSpiderParent_lt 2 2 2 d 2 2 j hj)).isGraceful

end Bounty
end

/- PathGraphBridge -/
section
namespace Bounty
open Math15.Graceful

/-- A path in increasing vertex order. -/
def lineGraph (n : ℕ) := parentGraph n (fun j => j-1)

lemma lineGraph_adj_iff {n : ℕ} (i j : Fin (n+1)) :
    (lineGraph n).Adj i j ↔ i.val+1=j.val ∨ j.val+1=i.val := by
  simp only [lineGraph, parentGraph]
  omega

lemma lineGraph_edgeCount (n : ℕ) : edgeCount (lineGraph n) = n :=
  parentGraph_edgeCount n _ (by intros; omega)

lemma NatGracefulPath.toLineLabeling {n : ℕ} {p : ℕ → ℕ}
    (hp : NatGracefulPath (n+1) p) :
    IsGracefulLabeling (lineGraph n) (fun i => p i.val) := by
  apply labeling_of_injective_differences
  · intro i j heq
    exact Fin.ext (hp.1 i.val j.val i.isLt j.isLt heq)
  · intro i
    rw [lineGraph_edgeCount]
    have := hp.2.1 i.val i.isLt
    omega
  · intro e e' hlt he hlt' he' heq
    rw [lineGraph_adj_iff] at he he'
    have h₁ : e.1.val = e.2.val-1 := by have := e.1.isLt; have := e.2.isLt; change e.1.val < e.2.val at hlt; omega
    have h₂ : e'.1.val = e'.2.val-1 := by have := e'.1.isLt; have := e'.2.isLt; change e'.1.val < e'.2.val at hlt'; omega
    have hi : 0 < e.2.val := by change e.1.val < e.2.val at hlt; omega
    have hj : 0 < e'.2.val := by change e'.1.val < e'.2.val at hlt'; omega
    rw [h₁, h₂] at heq
    have hr := hp.2.2 e.2.val e'.2.val hi e.2.isLt hj e'.2.isLt heq
    apply Prod.ext (Fin.ext (by omega)) (Fin.ext hr)

lemma NatAlphaPath.toLineAlpha {n k : ℕ} {p : ℕ → ℕ}
    (hp : NatAlphaPath (n+1) p k) :
    IsAlphaLabeling (lineGraph n) (fun i => p i.val) k := by
  refine ⟨hp.1.toLineLabeling, ?_, ?_⟩
  · rw [lineGraph_edgeCount]
    have := hp.2.1
    omega
  · intro i j hij
    rw [lineGraph_adj_iff] at hij
    dsimp only
    rcases hij with hij | hij
    · have h := hp.2.2 j.val (by omega) j.isLt
      have heq : j.val-1=i.val := by omega
      simpa only [heq] using h
    · have h := hp.2.2 i.val (by omega) i.isLt
      have heq : i.val-1=j.val := by omega
      simpa only [heq, or_comm] using h


end Bounty
end

/- AppendComplete -/
section
namespace Bounty
open Math15.Graceful

/-- Append a path of any sufficiently large size to the long leg. The old zero
labels survive; the needed endpoint permutation is supplied constructively. -/
theorem NatSpiderCertificate.exists_append {L k m : ℕ} {f : ℕ → ℕ}
    (hL : 1 ≤ L) (hf : NatSpiderCertificate L f) (hα : NatSpiderAlpha L f k)
    (hk : k ≤ L+4)
    (hm : max (k+1-f (L+4)) (f (L+4)-k) ≤ m) :
    ∃ g : ℕ → ℕ, NatSpiderCertificate (L+m) g ∧
      ∀ z, z < L+5 → f z = 0 → g z = 0 := by
  have hm1 : k+1-f (L+4) ≤ m := (le_max_left _ _).trans hm
  have hm2 : f (L+4)-k ≤ m := (le_max_right _ _).trans hm
  by_cases he : f (L+4) ≤ k
  · obtain ⟨p, hp, hp0⟩ := exists_graceful_path_endpoint
      (n := m) (a := f (L+4)+m-(k+1)) (by omega)
    refine ⟨appendSpiderLabels L k m f p, hf.appendPath hL hα hp hk ?_, ?_⟩
    · rw [hp0]
      have hs : shiftAboveCut k m (f (L+4)) = f (L+4) := by simp [shiftAboveCut, he]
      rw [hs]
      unfold Nat.dist
      omega
    · intro z hz hzero
      exact appendSpiderLabels_preserves_zero hz hzero
  · obtain ⟨p, hp, hp0⟩ := exists_graceful_path_endpoint
      (n := m) (a := f (L+4)-(k+1)) (by omega)
    refine ⟨appendSpiderLabels L k m f p, hf.appendPath hL hα hp hk ?_, ?_⟩
    · rw [hp0]
      have hs : shiftAboveCut k m (f (L+4)) = f (L+4)+m := by simp [shiftAboveCut, he]
      rw [hs]
      unfold Nat.dist
      omega
    · intro z hz hzero
      exact appendSpiderLabels_preserves_zero hz hzero

end Bounty
end

/- StartingCertificates -/
section
namespace Bounty


def AlphaSpiderCertificate (L : ℕ) (f : Fin (L+5) → ℕ) (k : ℕ) : Prop :=
  SpiderCertificate L f ∧ k < L+4 ∧
  ∀ u v, (spider L).Adj u v → (f u ≤ k ∧ k < f v) ∨ (f v ≤ k ∧ k < f u)

def alphaSpiderCertificateDecidable (L : ℕ) (f : Fin (L+5) → ℕ) (k : ℕ) :
    Decidable (AlphaSpiderCertificate L f k) := by
  letI := spiderAdjDecidable L
  letI := spiderCertificateDecidable L f
  unfold AlphaSpiderCertificate
  infer_instance

lemma AlphaSpiderCertificate.isAlphaLabeling {L : ℕ} {f : Fin (L+5) → ℕ} {k : ℕ}
    (h : AlphaSpiderCertificate L f k) : Math15.Graceful.IsAlphaLabeling (spider L) f k := by
  refine ⟨h.1.isGracefulLabeling, ?_, h.2.2⟩
  simpa only [spider_edgeCount] using h.2.1

def startingLabeling_1 : Fin (3+5) → ℕ := ![5,2,6,3,4,0,7,1]
theorem startingLabeling_1_checked :
    AlphaSpiderCertificate 3 startingLabeling_1 3 ∧
      startingLabeling_1 ⟨5, by decide⟩ = 0 := by
  refine ⟨?_, by decide⟩
  exact @of_decide_eq_true _ (alphaSpiderCertificateDecidable 3 startingLabeling_1 3) (by decide +kernel)

def startingLabeling_2 : Fin (3+5) → ℕ := ![2,5,1,4,3,7,0,6]
theorem startingLabeling_2_checked :
    AlphaSpiderCertificate 3 startingLabeling_2 3 ∧
      startingLabeling_2 ⟨6, by decide⟩ = 0 := by
  refine ⟨?_, by decide⟩
  exact @of_decide_eq_true _ (alphaSpiderCertificateDecidable 3 startingLabeling_2 3) (by decide +kernel)

def startingLabeling_3 : Fin (4+5) → ℕ := ![5,2,7,3,4,1,8,0,6]
theorem startingLabeling_3_checked :
    AlphaSpiderCertificate 4 startingLabeling_3 3 ∧
      startingLabeling_3 ⟨7, by decide⟩ = 0 := by
  refine ⟨?_, by decide⟩
  exact @of_decide_eq_true _ (alphaSpiderCertificateDecidable 4 startingLabeling_3 3) (by decide +kernel)

def startingLabeling_4 : Fin (5+5) → ℕ := ![4,7,2,5,3,8,1,9,0,6]
theorem startingLabeling_4_checked :
    AlphaSpiderCertificate 5 startingLabeling_4 4 ∧
      startingLabeling_4 ⟨8, by decide⟩ = 0 := by
  refine ⟨?_, by decide⟩
  exact @of_decide_eq_true _ (alphaSpiderCertificateDecidable 5 startingLabeling_4 4) (by decide +kernel)

def startingLabeling_5 : Fin (6+5) → ℕ := ![6,3,7,4,5,1,8,2,10,0,9]
theorem startingLabeling_5_checked :
    AlphaSpiderCertificate 6 startingLabeling_5 4 ∧
      startingLabeling_5 ⟨9, by decide⟩ = 0 := by
  refine ⟨?_, by decide⟩
  exact @of_decide_eq_true _ (alphaSpiderCertificateDecidable 6 startingLabeling_5 4) (by decide +kernel)

def startingLabeling_6 : Fin (7+5) → ℕ := ![4,10,2,6,5,7,3,8,1,11,0,9]
theorem startingLabeling_6_checked :
    AlphaSpiderCertificate 7 startingLabeling_6 5 ∧
      startingLabeling_6 ⟨10, by decide⟩ = 0 := by
  refine ⟨?_, by decide⟩
  exact @of_decide_eq_true _ (alphaSpiderCertificateDecidable 7 startingLabeling_6 5) (by decide +kernel)

def startingLabeling_7 : Fin (8+5) → ℕ := ![7,4,9,5,6,3,11,2,8,1,12,0,10]
theorem startingLabeling_7_checked :
    AlphaSpiderCertificate 8 startingLabeling_7 5 ∧
      startingLabeling_7 ⟨11, by decide⟩ = 0 := by
  refine ⟨?_, by decide⟩
  exact @of_decide_eq_true _ (alphaSpiderCertificateDecidable 8 startingLabeling_7 5) (by decide +kernel)

def startingLabeling_8 : Fin (9+5) → ℕ := ![1,13,0,12,2,10,5,9,3,11,4,7,6,8]
theorem startingLabeling_8_checked :
    AlphaSpiderCertificate 9 startingLabeling_8 6 ∧
      startingLabeling_8 ⟨12, by decide⟩ = 6 := by
  refine ⟨?_, by decide⟩
  exact @of_decide_eq_true _ (alphaSpiderCertificateDecidable 9 startingLabeling_8 6) (by decide +kernel)

def startingLabeling_9 : Fin (10+5) → ℕ := ![1,14,0,13,2,11,3,12,5,9,4,10,7,8,6]
theorem startingLabeling_9_checked :
    AlphaSpiderCertificate 10 startingLabeling_9 7 ∧
      startingLabeling_9 ⟨13, by decide⟩ = 8 := by
  refine ⟨?_, by decide⟩
  exact @of_decide_eq_true _ (alphaSpiderCertificateDecidable 10 startingLabeling_9 7) (by decide +kernel)

def startingLabeling_10 : Fin (11+5) → ℕ := ![1,15,0,14,2,12,4,13,3,10,6,11,5,8,7,9]
theorem startingLabeling_10_checked :
    AlphaSpiderCertificate 11 startingLabeling_10 7 ∧
      startingLabeling_10 ⟨14, by decide⟩ = 7 := by
  refine ⟨?_, by decide⟩
  exact @of_decide_eq_true _ (alphaSpiderCertificateDecidable 11 startingLabeling_10 7) (by decide +kernel)

def startingLabeling_11 : Fin (12+5) → ℕ := ![1,16,0,15,2,13,5,12,3,14,4,10,6,11,8,9,7]
theorem startingLabeling_11_checked :
    AlphaSpiderCertificate 12 startingLabeling_11 8 ∧
      startingLabeling_11 ⟨15, by decide⟩ = 9 := by
  refine ⟨?_, by decide⟩
  exact @of_decide_eq_true _ (alphaSpiderCertificateDecidable 12 startingLabeling_11 8) (by decide +kernel)

end Bounty
end

/- FiniteCertificates -/
section
namespace Bounty


def smallLabeling_1_1 : Fin (2+5) → ℕ := ![6,1,2,3,5,0,4]
theorem smallLabeling_1_1_checked :
    SpiderCertificate 2 smallLabeling_1_1 ∧ smallLabeling_1_1 ⟨5, by decide⟩ = 0 := by
  refine ⟨?_, by decide⟩
  exact @of_decide_eq_true _ (spiderCertificateDecidable 2 smallLabeling_1_1) (by decide +kernel)

def smallLabeling_1_2 : Fin (3+5) → ℕ := ![7,1,4,6,2,0,5,3]
theorem smallLabeling_1_2_checked :
    SpiderCertificate 3 smallLabeling_1_2 ∧ smallLabeling_1_2 ⟨5, by decide⟩ = 0 := by
  refine ⟨?_, by decide⟩
  exact @of_decide_eq_true _ (spiderCertificateDecidable 3 smallLabeling_1_2) (by decide +kernel)

def smallLabeling_1_3 : Fin (4+5) → ℕ := ![8,1,5,3,2,0,6,4,7]
theorem smallLabeling_1_3_checked :
    SpiderCertificate 4 smallLabeling_1_3 ∧ smallLabeling_1_3 ⟨5, by decide⟩ = 0 := by
  refine ⟨?_, by decide⟩
  exact @of_decide_eq_true _ (spiderCertificateDecidable 4 smallLabeling_1_3) (by decide +kernel)

def smallLabeling_1_4 : Fin (5+5) → ℕ := ![9,1,6,3,2,0,7,5,8,4]
theorem smallLabeling_1_4_checked :
    SpiderCertificate 5 smallLabeling_1_4 ∧ smallLabeling_1_4 ⟨5, by decide⟩ = 0 := by
  refine ⟨?_, by decide⟩
  exact @of_decide_eq_true _ (spiderCertificateDecidable 5 smallLabeling_1_4) (by decide +kernel)

def smallLabeling_1_5 : Fin (6+5) → ℕ := ![10,1,7,3,2,0,8,5,9,4,6]
theorem smallLabeling_1_5_checked :
    SpiderCertificate 6 smallLabeling_1_5 ∧ smallLabeling_1_5 ⟨5, by decide⟩ = 0 := by
  refine ⟨?_, by decide⟩
  exact @of_decide_eq_true _ (spiderCertificateDecidable 6 smallLabeling_1_5) (by decide +kernel)

def smallLabeling_2_1 : Fin (3+5) → ℕ := ![1,6,3,5,4,7,0,2]
theorem smallLabeling_2_1_checked :
    SpiderCertificate 3 smallLabeling_2_1 ∧ smallLabeling_2_1 ⟨6, by decide⟩ = 0 := by
  refine ⟨?_, by decide⟩
  exact @of_decide_eq_true _ (spiderCertificateDecidable 3 smallLabeling_2_1) (by decide +kernel)

def smallLabeling_2_2 : Fin (4+5) → ℕ := ![1,7,3,4,2,8,0,5,6]
theorem smallLabeling_2_2_checked :
    SpiderCertificate 4 smallLabeling_2_2 ∧ smallLabeling_2_2 ⟨6, by decide⟩ = 0 := by
  refine ⟨?_, by decide⟩
  exact @of_decide_eq_true _ (spiderCertificateDecidable 4 smallLabeling_2_2) (by decide +kernel)

def smallLabeling_2_3 : Fin (5+5) → ℕ := ![1,5,4,3,6,9,0,7,2,8]
theorem smallLabeling_2_3_checked :
    SpiderCertificate 5 smallLabeling_2_3 ∧ smallLabeling_2_3 ⟨6, by decide⟩ = 0 := by
  refine ⟨?_, by decide⟩
  exact @of_decide_eq_true _ (spiderCertificateDecidable 5 smallLabeling_2_3) (by decide +kernel)

def smallLabeling_2_4 : Fin (6+5) → ℕ := ![1,7,3,6,4,10,0,8,9,2,5]
theorem smallLabeling_2_4_checked :
    SpiderCertificate 6 smallLabeling_2_4 ∧ smallLabeling_2_4 ⟨6, by decide⟩ = 0 := by
  refine ⟨?_, by decide⟩
  exact @of_decide_eq_true _ (spiderCertificateDecidable 6 smallLabeling_2_4) (by decide +kernel)

def smallLabeling_3_1 : Fin (4+5) → ℕ := ![5,2,7,3,4,1,8,0,6]
theorem smallLabeling_3_1_checked :
    SpiderCertificate 4 smallLabeling_3_1 ∧ smallLabeling_3_1 ⟨7, by decide⟩ = 0 := by
  refine ⟨?_, by decide⟩
  exact @of_decide_eq_true _ (spiderCertificateDecidable 4 smallLabeling_3_1) (by decide +kernel)

def smallLabeling_3_2 : Fin (5+5) → ℕ := ![6,2,8,5,3,1,9,0,7,4]
theorem smallLabeling_3_2_checked :
    SpiderCertificate 5 smallLabeling_3_2 ∧ smallLabeling_3_2 ⟨7, by decide⟩ = 0 := by
  refine ⟨?_, by decide⟩
  exact @of_decide_eq_true _ (spiderCertificateDecidable 5 smallLabeling_3_2) (by decide +kernel)

def smallLabeling_3_3 : Fin (6+5) → ℕ := ![6,3,7,4,5,1,10,0,8,2,9]
theorem smallLabeling_3_3_checked :
    SpiderCertificate 6 smallLabeling_3_3 ∧ smallLabeling_3_3 ⟨7, by decide⟩ = 0 := by
  refine ⟨?_, by decide⟩
  exact @of_decide_eq_true _ (spiderCertificateDecidable 6 smallLabeling_3_3) (by decide +kernel)

def smallLabeling_3_4 : Fin (7+5) → ℕ := ![8,2,10,6,5,1,11,0,9,4,7,3]
theorem smallLabeling_3_4_checked :
    SpiderCertificate 7 smallLabeling_3_4 ∧ smallLabeling_3_4 ⟨7, by decide⟩ = 0 := by
  refine ⟨?_, by decide⟩
  exact @of_decide_eq_true _ (spiderCertificateDecidable 7 smallLabeling_3_4) (by decide +kernel)

def smallLabeling_3_5 : Fin (8+5) → ℕ := ![9,4,8,6,7,1,12,0,10,3,5,11,2]
theorem smallLabeling_3_5_checked :
    SpiderCertificate 8 smallLabeling_3_5 ∧ smallLabeling_3_5 ⟨7, by decide⟩ = 0 := by
  refine ⟨?_, by decide⟩
  exact @of_decide_eq_true _ (spiderCertificateDecidable 8 smallLabeling_3_5) (by decide +kernel)

def smallLabeling_4_1 : Fin (5+5) → ℕ := ![2,8,5,4,3,6,1,9,0,7]
theorem smallLabeling_4_1_checked :
    SpiderCertificate 5 smallLabeling_4_1 ∧ smallLabeling_4_1 ⟨8, by decide⟩ = 0 := by
  refine ⟨?_, by decide⟩
  exact @of_decide_eq_true _ (spiderCertificateDecidable 5 smallLabeling_4_1) (by decide +kernel)

def smallLabeling_4_2 : Fin (6+5) → ℕ := ![2,9,6,3,5,7,1,10,0,8,4]
theorem smallLabeling_4_2_checked :
    SpiderCertificate 6 smallLabeling_4_2 ∧ smallLabeling_4_2 ⟨8, by decide⟩ = 0 := by
  refine ⟨?_, by decide⟩
  exact @of_decide_eq_true _ (spiderCertificateDecidable 6 smallLabeling_4_2) (by decide +kernel)

def smallLabeling_4_3 : Fin (7+5) → ℕ := ![5,10,2,4,6,8,1,11,0,9,3,7]
theorem smallLabeling_4_3_checked :
    SpiderCertificate 7 smallLabeling_4_3 ∧ smallLabeling_4_3 ⟨8, by decide⟩ = 0 := by
  refine ⟨?_, by decide⟩
  exact @of_decide_eq_true _ (spiderCertificateDecidable 7 smallLabeling_4_3) (by decide +kernel)

def smallLabeling_4_4 : Fin (8+5) → ℕ := ![5,11,2,4,7,9,1,12,0,10,3,8,6]
theorem smallLabeling_4_4_checked :
    SpiderCertificate 8 smallLabeling_4_4 ∧ smallLabeling_4_4 ⟨8, by decide⟩ = 0 := by
  refine ⟨?_, by decide⟩
  exact @of_decide_eq_true _ (spiderCertificateDecidable 8 smallLabeling_4_4) (by decide +kernel)

def smallLabeling_4_5 : Fin (9+5) → ℕ := ![4,9,6,8,7,10,1,13,0,11,3,5,12,2]
theorem smallLabeling_4_5_checked :
    SpiderCertificate 9 smallLabeling_4_5 ∧ smallLabeling_4_5 ⟨8, by decide⟩ = 0 := by
  refine ⟨?_, by decide⟩
  exact @of_decide_eq_true _ (spiderCertificateDecidable 9 smallLabeling_4_5) (by decide +kernel)

def smallLabeling_5_1 : Fin (6+5) → ℕ := ![2,9,4,5,3,6,7,1,10,0,8]
theorem smallLabeling_5_1_checked :
    SpiderCertificate 6 smallLabeling_5_1 ∧ smallLabeling_5_1 ⟨9, by decide⟩ = 0 := by
  refine ⟨?_, by decide⟩
  exact @of_decide_eq_true _ (spiderCertificateDecidable 6 smallLabeling_5_1) (by decide +kernel)

def smallLabeling_5_2 : Fin (7+5) → ℕ := ![7,2,10,5,6,4,8,1,11,0,9,3]
theorem smallLabeling_5_2_checked :
    SpiderCertificate 7 smallLabeling_5_2 ∧ smallLabeling_5_2 ⟨9, by decide⟩ = 0 := by
  refine ⟨?_, by decide⟩
  exact @of_decide_eq_true _ (spiderCertificateDecidable 7 smallLabeling_5_2) (by decide +kernel)

def smallLabeling_5_3 : Fin (8+5) → ℕ := ![5,11,2,8,6,4,9,1,12,0,10,3,7]
theorem smallLabeling_5_3_checked :
    SpiderCertificate 8 smallLabeling_5_3 ∧ smallLabeling_5_3 ⟨9, by decide⟩ = 0 := by
  refine ⟨?_, by decide⟩
  exact @of_decide_eq_true _ (spiderCertificateDecidable 8 smallLabeling_5_3) (by decide +kernel)

def smallLabeling_5_4 : Fin (9+5) → ℕ := ![2,12,5,6,9,4,10,1,13,0,11,3,8,7]
theorem smallLabeling_5_4_checked :
    SpiderCertificate 9 smallLabeling_5_4 ∧ smallLabeling_5_4 ⟨9, by decide⟩ = 0 := by
  refine ⟨?_, by decide⟩
  exact @of_decide_eq_true _ (spiderCertificateDecidable 9 smallLabeling_5_4) (by decide +kernel)

def smallLabeling_5_5 : Fin (10+5) → ℕ := ![2,13,5,7,8,4,11,1,14,0,12,3,9,6,10]
theorem smallLabeling_5_5_checked :
    SpiderCertificate 10 smallLabeling_5_5 ∧ smallLabeling_5_5 ⟨9, by decide⟩ = 0 := by
  refine ⟨?_, by decide⟩
  exact @of_decide_eq_true _ (spiderCertificateDecidable 10 smallLabeling_5_5) (by decide +kernel)

def smallLabeling_5_6 : Fin (11+5) → ℕ := ![2,14,5,8,9,4,12,1,15,0,13,3,10,7,11,6]
theorem smallLabeling_5_6_checked :
    SpiderCertificate 11 smallLabeling_5_6 ∧ smallLabeling_5_6 ⟨9, by decide⟩ = 0 := by
  refine ⟨?_, by decide⟩
  exact @of_decide_eq_true _ (spiderCertificateDecidable 11 smallLabeling_5_6) (by decide +kernel)

def smallLabeling_6_1 : Fin (7+5) → ℕ := ![4,10,2,6,5,7,3,8,1,11,0,9]
theorem smallLabeling_6_1_checked :
    SpiderCertificate 7 smallLabeling_6_1 ∧ smallLabeling_6_1 ⟨10, by decide⟩ = 0 := by
  refine ⟨?_, by decide⟩
  exact @of_decide_eq_true _ (spiderCertificateDecidable 7 smallLabeling_6_1) (by decide +kernel)

def smallLabeling_6_2 : Fin (8+5) → ℕ := ![5,11,2,7,6,8,4,9,1,12,0,10,3]
theorem smallLabeling_6_2_checked :
    SpiderCertificate 8 smallLabeling_6_2 ∧ smallLabeling_6_2 ⟨10, by decide⟩ = 0 := by
  refine ⟨?_, by decide⟩
  exact @of_decide_eq_true _ (spiderCertificateDecidable 8 smallLabeling_6_2) (by decide +kernel)

def smallLabeling_6_3 : Fin (9+5) → ℕ := ![9,2,12,5,6,7,4,10,1,13,0,11,3,8]
theorem smallLabeling_6_3_checked :
    SpiderCertificate 9 smallLabeling_6_3 ∧ smallLabeling_6_3 ⟨10, by decide⟩ = 0 := by
  refine ⟨?_, by decide⟩
  exact @of_decide_eq_true _ (spiderCertificateDecidable 9 smallLabeling_6_3) (by decide +kernel)

def smallLabeling_6_4 : Fin (10+5) → ℕ := ![2,13,5,6,8,7,4,11,1,14,0,12,3,9,10]
theorem smallLabeling_6_4_checked :
    SpiderCertificate 10 smallLabeling_6_4 ∧ smallLabeling_6_4 ⟨10, by decide⟩ = 0 := by
  refine ⟨?_, by decide⟩
  exact @of_decide_eq_true _ (spiderCertificateDecidable 10 smallLabeling_6_4) (by decide +kernel)

def smallLabeling_6_5 : Fin (11+5) → ℕ := ![11,2,14,5,8,9,4,12,1,15,0,13,3,10,6,7]
theorem smallLabeling_6_5_checked :
    SpiderCertificate 11 smallLabeling_6_5 ∧ smallLabeling_6_5 ⟨10, by decide⟩ = 0 := by
  refine ⟨?_, by decide⟩
  exact @of_decide_eq_true _ (spiderCertificateDecidable 11 smallLabeling_6_5) (by decide +kernel)

def smallLabeling_6_6 : Fin (12+5) → ℕ := ![5,15,2,12,9,10,4,13,1,16,0,14,3,11,7,6,8]
theorem smallLabeling_6_6_checked :
    SpiderCertificate 12 smallLabeling_6_6 ∧ smallLabeling_6_6 ⟨10, by decide⟩ = 0 := by
  refine ⟨?_, by decide⟩
  exact @of_decide_eq_true _ (spiderCertificateDecidable 12 smallLabeling_6_6) (by decide +kernel)

def smallLabeling_7_1 : Fin (8+5) → ℕ := ![3,8,4,6,7,5,11,2,9,1,12,0,10]
theorem smallLabeling_7_1_checked :
    SpiderCertificate 8 smallLabeling_7_1 ∧ smallLabeling_7_1 ⟨11, by decide⟩ = 0 := by
  refine ⟨?_, by decide⟩
  exact @of_decide_eq_true _ (spiderCertificateDecidable 8 smallLabeling_7_1) (by decide +kernel)

def smallLabeling_7_2 : Fin (9+5) → ℕ := ![12,2,9,8,5,7,6,4,10,1,13,0,11,3]
theorem smallLabeling_7_2_checked :
    SpiderCertificate 9 smallLabeling_7_2 ∧ smallLabeling_7_2 ⟨11, by decide⟩ = 0 := by
  refine ⟨?_, by decide⟩
  exact @of_decide_eq_true _ (spiderCertificateDecidable 9 smallLabeling_7_2) (by decide +kernel)

def smallLabeling_7_3 : Fin (10+5) → ℕ := ![5,13,2,10,7,6,8,4,11,1,14,0,12,3,9]
theorem smallLabeling_7_3_checked :
    SpiderCertificate 10 smallLabeling_7_3 ∧ smallLabeling_7_3 ⟨11, by decide⟩ = 0 := by
  refine ⟨?_, by decide⟩
  exact @of_decide_eq_true _ (spiderCertificateDecidable 10 smallLabeling_7_3) (by decide +kernel)

def smallLabeling_7_4 : Fin (11+5) → ℕ := ![5,14,2,11,7,6,9,4,12,1,15,0,13,3,10,8]
theorem smallLabeling_7_4_checked :
    SpiderCertificate 11 smallLabeling_7_4 ∧ smallLabeling_7_4 ⟨11, by decide⟩ = 0 := by
  refine ⟨?_, by decide⟩
  exact @of_decide_eq_true _ (spiderCertificateDecidable 11 smallLabeling_7_4) (by decide +kernel)

def smallLabeling_7_5 : Fin (12+5) → ℕ := ![2,15,8,5,9,12,10,4,13,1,16,0,14,3,11,6,7]
theorem smallLabeling_7_5_checked :
    SpiderCertificate 12 smallLabeling_7_5 ∧ smallLabeling_7_5 ⟨11, by decide⟩ = 0 := by
  refine ⟨?_, by decide⟩
  exact @of_decide_eq_true _ (spiderCertificateDecidable 12 smallLabeling_7_5) (by decide +kernel)

def smallLabeling_7_6 : Fin (13+5) → ℕ := ![5,16,2,13,8,7,11,4,14,1,17,0,15,3,12,6,9,10]
theorem smallLabeling_7_6_checked :
    SpiderCertificate 13 smallLabeling_7_6 ∧ smallLabeling_7_6 ⟨11, by decide⟩ = 0 := by
  refine ⟨?_, by decide⟩
  exact @of_decide_eq_true _ (spiderCertificateDecidable 13 smallLabeling_7_6) (by decide +kernel)

def smallLabeling_7_7 : Fin (14+5) → ℕ := ![2,14,8,11,10,17,12,4,15,1,18,0,16,3,13,6,9,5,7]
theorem smallLabeling_7_7_checked :
    SpiderCertificate 14 smallLabeling_7_7 ∧ smallLabeling_7_7 ⟨11, by decide⟩ = 0 := by
  refine ⟨?_, by decide⟩
  exact @of_decide_eq_true _ (spiderCertificateDecidable 14 smallLabeling_7_7) (by decide +kernel)

def smallLabeling_8_1 : Fin (9+5) → ℕ := ![3,8,7,6,4,9,5,12,2,10,1,13,0,11]
theorem smallLabeling_8_1_checked :
    SpiderCertificate 9 smallLabeling_8_1 ∧ smallLabeling_8_1 ⟨12, by decide⟩ = 0 := by
  refine ⟨?_, by decide⟩
  exact @of_decide_eq_true _ (spiderCertificateDecidable 9 smallLabeling_8_1) (by decide +kernel)

def smallLabeling_8_2 : Fin (10+5) → ℕ := ![8,5,9,6,7,13,2,10,4,11,1,14,0,12,3]
theorem smallLabeling_8_2_checked :
    SpiderCertificate 10 smallLabeling_8_2 ∧ smallLabeling_8_2 ⟨12, by decide⟩ = 0 := by
  refine ⟨?_, by decide⟩
  exact @of_decide_eq_true _ (spiderCertificateDecidable 10 smallLabeling_8_2) (by decide +kernel)

def smallLabeling_8_3 : Fin (11+5) → ℕ := ![2,14,8,5,6,11,7,9,4,12,1,15,0,13,3,10]
theorem smallLabeling_8_3_checked :
    SpiderCertificate 11 smallLabeling_8_3 ∧ smallLabeling_8_3 ⟨12, by decide⟩ = 0 := by
  refine ⟨?_, by decide⟩
  exact @of_decide_eq_true _ (spiderCertificateDecidable 11 smallLabeling_8_3) (by decide +kernel)

def smallLabeling_8_4 : Fin (12+5) → ℕ := ![12,2,15,8,9,5,7,10,4,13,1,16,0,14,3,11,6]
theorem smallLabeling_8_4_checked :
    SpiderCertificate 12 smallLabeling_8_4 ∧ smallLabeling_8_4 ⟨12, by decide⟩ = 0 := by
  refine ⟨?_, by decide⟩
  exact @of_decide_eq_true _ (spiderCertificateDecidable 12 smallLabeling_8_4) (by decide +kernel)

def smallLabeling_8_5 : Fin (13+5) → ℕ := ![13,5,9,10,8,2,16,11,4,14,1,17,0,15,3,12,6,7]
theorem smallLabeling_8_5_checked :
    SpiderCertificate 13 smallLabeling_8_5 ∧ smallLabeling_8_5 ⟨12, by decide⟩ = 0 := by
  refine ⟨?_, by decide⟩
  exact @of_decide_eq_true _ (spiderCertificateDecidable 13 smallLabeling_8_5) (by decide +kernel)

def smallLabeling_8_6 : Fin (14+5) → ℕ := ![14,2,17,5,11,10,7,12,4,15,1,18,0,16,3,13,6,8,9]
theorem smallLabeling_8_6_checked :
    SpiderCertificate 14 smallLabeling_8_6 ∧ smallLabeling_8_6 ⟨12, by decide⟩ = 0 := by
  refine ⟨?_, by decide⟩
  exact @of_decide_eq_true _ (spiderCertificateDecidable 14 smallLabeling_8_6) (by decide +kernel)

def smallLabeling_8_7 : Fin (15+5) → ℕ := ![5,18,2,15,11,12,7,13,4,16,1,19,0,17,3,14,6,9,8,10]
theorem smallLabeling_8_7_checked :
    SpiderCertificate 15 smallLabeling_8_7 ∧ smallLabeling_8_7 ⟨12, by decide⟩ = 0 := by
  refine ⟨?_, by decide⟩
  exact @of_decide_eq_true _ (spiderCertificateDecidable 15 smallLabeling_8_7) (by decide +kernel)

def smallLabeling_8_8 : Fin (16+5) → ℕ := ![19,5,9,8,16,2,7,14,4,17,1,20,0,18,3,15,6,12,11,13,10]
theorem smallLabeling_8_8_checked :
    SpiderCertificate 16 smallLabeling_8_8 ∧ smallLabeling_8_8 ⟨12, by decide⟩ = 0 := by
  refine ⟨?_, by decide⟩
  exact @of_decide_eq_true _ (spiderCertificateDecidable 16 smallLabeling_8_8) (by decide +kernel)

def smallLabeling_9_3 : Fin (12+5) → ℕ := ![9,12,8,7,6,2,15,5,10,4,13,1,16,0,14,3,11]
theorem smallLabeling_9_3_checked :
    SpiderCertificate 12 smallLabeling_9_3 ∧ smallLabeling_9_3 ⟨13, by decide⟩ = 0 := by
  refine ⟨?_, by decide⟩
  exact @of_decide_eq_true _ (spiderCertificateDecidable 12 smallLabeling_9_3) (by decide +kernel)

def smallLabeling_9_4 : Fin (13+5) → ℕ := ![5,9,8,7,10,13,2,16,11,4,14,1,17,0,15,3,12,6]
theorem smallLabeling_9_4_checked :
    SpiderCertificate 13 smallLabeling_9_4 ∧ smallLabeling_9_4 ⟨13, by decide⟩ = 0 := by
  refine ⟨?_, by decide⟩
  exact @of_decide_eq_true _ (spiderCertificateDecidable 13 smallLabeling_9_4) (by decide +kernel)

def smallLabeling_9_5 : Fin (14+5) → ℕ := ![2,11,14,8,9,17,5,7,12,4,15,1,18,0,16,3,13,6,10]
theorem smallLabeling_9_5_checked :
    SpiderCertificate 14 smallLabeling_9_5 ∧ smallLabeling_9_5 ⟨13, by decide⟩ = 0 := by
  refine ⟨?_, by decide⟩
  exact @of_decide_eq_true _ (spiderCertificateDecidable 14 smallLabeling_9_5) (by decide +kernel)

def smallLabeling_9_6 : Fin (15+5) → ℕ := ![15,2,18,5,9,8,10,7,13,4,16,1,19,0,17,3,14,6,11,12]
theorem smallLabeling_9_6_checked :
    SpiderCertificate 15 smallLabeling_9_6 ∧ smallLabeling_9_6 ⟨13, by decide⟩ = 0 := by
  refine ⟨?_, by decide⟩
  exact @of_decide_eq_true _ (spiderCertificateDecidable 15 smallLabeling_9_6) (by decide +kernel)

def smallLabeling_9_7 : Fin (16+5) → ℕ := ![5,16,8,9,11,19,2,7,14,4,17,1,20,0,18,3,15,6,12,13,10]
theorem smallLabeling_9_7_checked :
    SpiderCertificate 16 smallLabeling_9_7 ∧ smallLabeling_9_7 ⟨13, by decide⟩ = 0 := by
  refine ⟨?_, by decide⟩
  exact @of_decide_eq_true _ (spiderCertificateDecidable 16 smallLabeling_9_7) (by decide +kernel)

def smallLabeling_9_8 : Fin (17+5) → ℕ := ![5,17,8,11,10,20,2,7,15,4,18,1,21,0,19,3,16,6,13,9,12,14]
theorem smallLabeling_9_8_checked :
    SpiderCertificate 17 smallLabeling_9_8 ∧ smallLabeling_9_8 ⟨13, by decide⟩ = 0 := by
  refine ⟨?_, by decide⟩
  exact @of_decide_eq_true _ (spiderCertificateDecidable 17 smallLabeling_9_8) (by decide +kernel)

def smallLabeling_10_5 : Fin (15+5) → ℕ := ![12,8,15,9,10,2,18,5,7,13,4,16,1,19,0,17,3,14,6,11]
theorem smallLabeling_10_5_checked :
    SpiderCertificate 15 smallLabeling_10_5 ∧ smallLabeling_10_5 ⟨14, by decide⟩ = 0 := by
  refine ⟨?_, by decide⟩
  exact @of_decide_eq_true _ (spiderCertificateDecidable 15 smallLabeling_10_5) (by decide +kernel)

def smallLabeling_10_6 : Fin (16+5) → ℕ := ![16,8,10,13,9,5,19,2,7,14,4,17,1,20,0,18,3,15,6,12,11]
theorem smallLabeling_10_6_checked :
    SpiderCertificate 16 smallLabeling_10_6 ∧ smallLabeling_10_6 ⟨14, by decide⟩ = 0 := by
  refine ⟨?_, by decide⟩
  exact @of_decide_eq_true _ (spiderCertificateDecidable 16 smallLabeling_10_6) (by decide +kernel)

def smallLabeling_10_7 : Fin (17+5) → ℕ := ![17,2,20,8,14,5,9,12,7,15,4,18,1,21,0,19,3,16,6,13,11,10]
theorem smallLabeling_10_7_checked :
    SpiderCertificate 17 smallLabeling_10_7 ∧ smallLabeling_10_7 ⟨14, by decide⟩ = 0 := by
  refine ⟨?_, by decide⟩
  exact @of_decide_eq_true _ (spiderCertificateDecidable 17 smallLabeling_10_7) (by decide +kernel)

def smallLabeling_10_8 : Fin (18+5) → ℕ := ![2,21,11,18,5,9,8,13,7,16,4,19,1,22,0,20,3,17,6,14,10,12,15]
theorem smallLabeling_10_8_checked :
    SpiderCertificate 18 smallLabeling_10_8 ∧ smallLabeling_10_8 ⟨14, by decide⟩ = 0 := by
  refine ⟨?_, by decide⟩
  exact @of_decide_eq_true _ (spiderCertificateDecidable 18 smallLabeling_10_8) (by decide +kernel)

def smallLabeling_10_9 : Fin (19+5) → ℕ := ![20,6,14,7,13,4,16,5,12,10,15,11,8,17,0,23,1,22,2,21,3,18,19,9]
theorem smallLabeling_10_9_checked :
    SpiderCertificate 19 smallLabeling_10_9 ∧ smallLabeling_10_9 ⟨14, by decide⟩ = 0 := by
  refine ⟨?_, by decide⟩
  exact @of_decide_eq_true _ (spiderCertificateDecidable 19 smallLabeling_10_9) (by decide +kernel)

def smallLabeling_11_7 : Fin (18+5) → ℕ := ![2,12,10,9,8,21,5,18,13,7,16,4,19,1,22,0,20,3,17,6,14,11,15]
theorem smallLabeling_11_7_checked :
    SpiderCertificate 18 smallLabeling_11_7 ∧ smallLabeling_11_7 ⟨15, by decide⟩ = 0 := by
  refine ⟨?_, by decide⟩
  exact @of_decide_eq_true _ (spiderCertificateDecidable 18 smallLabeling_11_7) (by decide +kernel)

def smallLabeling_11_8 : Fin (19+5) → ℕ := ![5,12,11,16,13,20,6,14,10,15,9,7,19,1,23,0,21,4,17,8,18,2,22,3]
theorem smallLabeling_11_8_checked :
    SpiderCertificate 19 smallLabeling_11_8 ∧ smallLabeling_11_8 ⟨15, by decide⟩ = 0 := by
  refine ⟨?_, by decide⟩
  exact @of_decide_eq_true _ (spiderCertificateDecidable 19 smallLabeling_11_8) (by decide +kernel)

def smallLabeling_11_9 : Fin (20+5) → ℕ := ![1,22,8,19,6,20,5,21,4,16,7,18,12,2,24,0,23,3,10,15,17,9,13,14,11]
theorem smallLabeling_11_9_checked :
    SpiderCertificate 20 smallLabeling_11_9 ∧ smallLabeling_11_9 ⟨15, by decide⟩ = 0 := by
  refine ⟨?_, by decide⟩
  exact @of_decide_eq_true _ (spiderCertificateDecidable 20 smallLabeling_11_9) (by decide +kernel)

def smallLabeling_12_9 : Fin (21+5) → ℕ := ![1,23,6,21,5,20,7,19,9,16,8,22,4,13,2,25,0,24,3,18,12,11,14,10,15,17]
theorem smallLabeling_12_9_checked :
    SpiderCertificate 21 smallLabeling_12_9 ∧ smallLabeling_12_9 ⟨16, by decide⟩ = 0 := by
  refine ⟨?_, by decide⟩
  exact @of_decide_eq_true _ (spiderCertificateDecidable 21 smallLabeling_12_9) (by decide +kernel)

def smallLabeling_12_10 : Fin (22+5) → ℕ := ![5,19,12,20,10,13,4,21,1,24,6,18,7,23,2,26,0,25,3,22,9,8,14,17,15,11,16]
theorem smallLabeling_12_10_checked :
    SpiderCertificate 22 smallLabeling_12_10 ∧ smallLabeling_12_10 ⟨16, by decide⟩ = 0 := by
  refine ⟨?_, by decide⟩
  exact @of_decide_eq_true _ (spiderCertificateDecidable 22 smallLabeling_12_10) (by decide +kernel)

end Bounty
end

/- CanonicalFamily -/
section
namespace Bounty

lemma AlphaSpiderCertificate.toNat {L k : ℕ} {f : Fin (L+5) → ℕ}
    (hf : AlphaSpiderCertificate L f k) :
    NatSpiderAlpha L (extendSpiderLabel f) k := by
  intro j hj hb
  have hp : spiderParent j < L + 5 := (spiderParent_le j).trans_lt hb
  have h := hf.2.2 ⟨spiderParent j, hp⟩ ⟨j, hb⟩
    (Or.inl ⟨spiderParent_lt hj, rfl⟩)
  simpa only [extendSpiderLabel, dite_eq_left hb, dite_eq_left hp] using h

lemma canonical_seed8 :
    CanonicalPinnedSpider 9 8 (extendSpiderLabel startingLabeling_8) := by
  refine ⟨startingLabeling_8_checked.1.1.toNat, ?_, startingLabeling_8_checked.1.toNat, ?_⟩
  · norm_num [CanonicalSpider, extendSpiderLabel, startingLabeling_8]
  · norm_num [extendSpiderLabel, startingLabeling_8]

lemma canonical_seed9 :
    CanonicalPinnedSpider 10 9 (extendSpiderLabel startingLabeling_9) := by
  refine ⟨startingLabeling_9_checked.1.1.toNat, ?_, startingLabeling_9_checked.1.toNat, ?_⟩
  · norm_num [CanonicalSpider, extendSpiderLabel, startingLabeling_9]
  · norm_num [extendSpiderLabel, startingLabeling_9]

lemma canonical_seed10 :
    CanonicalPinnedSpider 11 10 (extendSpiderLabel startingLabeling_10) := by
  refine ⟨startingLabeling_10_checked.1.1.toNat, ?_, startingLabeling_10_checked.1.toNat, ?_⟩
  · norm_num [CanonicalSpider, extendSpiderLabel, startingLabeling_10]
  · norm_num [extendSpiderLabel, startingLabeling_10]

lemma canonical_seed11 :
    CanonicalPinnedSpider 12 11 (extendSpiderLabel startingLabeling_11) := by
  refine ⟨startingLabeling_11_checked.1.1.toNat, ?_, startingLabeling_11_checked.1.toNat, ?_⟩
  · norm_num [CanonicalSpider, extendSpiderLabel, startingLabeling_11]
  · norm_num [extendSpiderLabel, startingLabeling_11]

/-- Every pin distance at least eight has a canonical seed with one vertex beyond the pin. -/
theorem canonical_one_tail (d : ℕ) (hd : 8 ≤ d) :
    ∃ f, CanonicalPinnedSpider (d+1) d f := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    by_cases hsmall : d < 12
    · interval_cases d
      · exact ⟨_, canonical_seed8⟩
      · exact ⟨_, canonical_seed9⟩
      · exact ⟨_, canonical_seed10⟩
      · exact ⟨_, canonical_seed11⟩
    · obtain ⟨f, hf⟩ := ih (d-4) (by omega) (by omega)
      refine ⟨spiderPrefix (d-4+1) f, ?_⟩
      have h := hf.prefixExtend (by omega) (by omega)
      convert h using 1 <;> omega

/-- Normalized one-vertex-tail seeds have a uniform bound on both sides of the cut. -/
theorem normalized_one_tail (d : ℕ) (hd : 8 ≤ d) :
    ∃ (g : Fin (d+1+5) → ℕ) (k : ℕ),
      Math15.Graceful.IsAlphaLabeling (spider (d+1)) g k ∧
      g ⟨4+d, by omega⟩ = 0 ∧ k+1 ≤ d/2+4 ∧ (d+5)-k ≤ d/2+4 := by
  obtain ⟨f, hf⟩ := canonical_one_tail d hd
  have ha := hf.2.2.1.toAlphaLabeling hf.1 (by omega)
  by_cases heven : d % 2 = 0
  · refine ⟨_, _, ha.reverse, ?_, ?_, ?_⟩
    · change Math15.Graceful.reverseLabel _ _ (f (4+d)) = 0
      simp only [hf.2.2.2, heven, Nat.add_zero, Math15.Graceful.reverseLabel_at_cut]
    · omega
    · omega
  · refine ⟨_, _, ha.normalizeHigh, ?_, ?_, ?_⟩
    · change Math15.Graceful.normalizeHighLabel _ _ (f (4+d)) = 0
      have hodd : d % 2 = 1 := by omega
      rw [hf.2.2.2, hodd]
      exact Math15.Graceful.normalizeHighLabel_at_cut _ _
    · rw [spider_edgeCount]
      omega
    · rw [spider_edgeCount]
      omega

end Bounty
end

/- FiniteCover -/
section
namespace Bounty

def spiderPin (d c : ℕ) : Fin (d+c+5) := ⟨4+d, by omega⟩

def FiniteCase (d c : ℕ) : Prop :=
  1 ≤ c ∧ match d with
  | 1 => c ≤ 5
  | 2 => c ≤ 4
  | 3 => c ≤ 5
  | 4 => c ≤ 5
  | 5 => c ≤ 6
  | 6 => c ≤ 6
  | 7 => c ≤ 7
  | 8 => c ≤ 8
  | 9 => 3 ≤ c ∧ c ≤ 8
  | 10 => 5 ≤ c ∧ c ≤ 9
  | 11 => 7 ≤ c ∧ c ≤ 9
  | 12 => 9 ≤ c ∧ c ≤ 10
  | _ => False

theorem finiteCase_bounds {d c : ℕ} (h : FiniteCase d c) :
    1 ≤ d ∧ d ≤ 12 ∧ 1 ≤ c ∧ c ≤ 10 := by
  unfold FiniteCase at h
  obtain ⟨hc, h⟩ := h
  split at h <;> first | contradiction | omega

theorem finiteCase_pinned {d c : ℕ} (h : FiniteCase d c) :
    ∃ f : Fin (d+c+5) → ℕ,
      Math15.Graceful.IsGracefulLabeling (spider (d+c)) f ∧ f (spiderPin d c) = 0 := by
  obtain ⟨hd, hd', hc, hc'⟩ := finiteCase_bounds h
  interval_cases d <;> interval_cases c <;> norm_num [FiniteCase] at h
  all_goals first
    | exact ⟨smallLabeling_1_1, smallLabeling_1_1_checked.1.isGracefulLabeling, smallLabeling_1_1_checked.2⟩
    | exact ⟨smallLabeling_1_2, smallLabeling_1_2_checked.1.isGracefulLabeling, smallLabeling_1_2_checked.2⟩
    | exact ⟨smallLabeling_1_3, smallLabeling_1_3_checked.1.isGracefulLabeling, smallLabeling_1_3_checked.2⟩
    | exact ⟨smallLabeling_1_4, smallLabeling_1_4_checked.1.isGracefulLabeling, smallLabeling_1_4_checked.2⟩
    | exact ⟨smallLabeling_1_5, smallLabeling_1_5_checked.1.isGracefulLabeling, smallLabeling_1_5_checked.2⟩
    | exact ⟨smallLabeling_2_1, smallLabeling_2_1_checked.1.isGracefulLabeling, smallLabeling_2_1_checked.2⟩
    | exact ⟨smallLabeling_2_2, smallLabeling_2_2_checked.1.isGracefulLabeling, smallLabeling_2_2_checked.2⟩
    | exact ⟨smallLabeling_2_3, smallLabeling_2_3_checked.1.isGracefulLabeling, smallLabeling_2_3_checked.2⟩
    | exact ⟨smallLabeling_2_4, smallLabeling_2_4_checked.1.isGracefulLabeling, smallLabeling_2_4_checked.2⟩
    | exact ⟨smallLabeling_3_1, smallLabeling_3_1_checked.1.isGracefulLabeling, smallLabeling_3_1_checked.2⟩
    | exact ⟨smallLabeling_3_2, smallLabeling_3_2_checked.1.isGracefulLabeling, smallLabeling_3_2_checked.2⟩
    | exact ⟨smallLabeling_3_3, smallLabeling_3_3_checked.1.isGracefulLabeling, smallLabeling_3_3_checked.2⟩
    | exact ⟨smallLabeling_3_4, smallLabeling_3_4_checked.1.isGracefulLabeling, smallLabeling_3_4_checked.2⟩
    | exact ⟨smallLabeling_3_5, smallLabeling_3_5_checked.1.isGracefulLabeling, smallLabeling_3_5_checked.2⟩
    | exact ⟨smallLabeling_4_1, smallLabeling_4_1_checked.1.isGracefulLabeling, smallLabeling_4_1_checked.2⟩
    | exact ⟨smallLabeling_4_2, smallLabeling_4_2_checked.1.isGracefulLabeling, smallLabeling_4_2_checked.2⟩
    | exact ⟨smallLabeling_4_3, smallLabeling_4_3_checked.1.isGracefulLabeling, smallLabeling_4_3_checked.2⟩
    | exact ⟨smallLabeling_4_4, smallLabeling_4_4_checked.1.isGracefulLabeling, smallLabeling_4_4_checked.2⟩
    | exact ⟨smallLabeling_4_5, smallLabeling_4_5_checked.1.isGracefulLabeling, smallLabeling_4_5_checked.2⟩
    | exact ⟨smallLabeling_5_1, smallLabeling_5_1_checked.1.isGracefulLabeling, smallLabeling_5_1_checked.2⟩
    | exact ⟨smallLabeling_5_2, smallLabeling_5_2_checked.1.isGracefulLabeling, smallLabeling_5_2_checked.2⟩
    | exact ⟨smallLabeling_5_3, smallLabeling_5_3_checked.1.isGracefulLabeling, smallLabeling_5_3_checked.2⟩
    | exact ⟨smallLabeling_5_4, smallLabeling_5_4_checked.1.isGracefulLabeling, smallLabeling_5_4_checked.2⟩
    | exact ⟨smallLabeling_5_5, smallLabeling_5_5_checked.1.isGracefulLabeling, smallLabeling_5_5_checked.2⟩
    | exact ⟨smallLabeling_5_6, smallLabeling_5_6_checked.1.isGracefulLabeling, smallLabeling_5_6_checked.2⟩
    | exact ⟨smallLabeling_6_1, smallLabeling_6_1_checked.1.isGracefulLabeling, smallLabeling_6_1_checked.2⟩
    | exact ⟨smallLabeling_6_2, smallLabeling_6_2_checked.1.isGracefulLabeling, smallLabeling_6_2_checked.2⟩
    | exact ⟨smallLabeling_6_3, smallLabeling_6_3_checked.1.isGracefulLabeling, smallLabeling_6_3_checked.2⟩
    | exact ⟨smallLabeling_6_4, smallLabeling_6_4_checked.1.isGracefulLabeling, smallLabeling_6_4_checked.2⟩
    | exact ⟨smallLabeling_6_5, smallLabeling_6_5_checked.1.isGracefulLabeling, smallLabeling_6_5_checked.2⟩
    | exact ⟨smallLabeling_6_6, smallLabeling_6_6_checked.1.isGracefulLabeling, smallLabeling_6_6_checked.2⟩
    | exact ⟨smallLabeling_7_1, smallLabeling_7_1_checked.1.isGracefulLabeling, smallLabeling_7_1_checked.2⟩
    | exact ⟨smallLabeling_7_2, smallLabeling_7_2_checked.1.isGracefulLabeling, smallLabeling_7_2_checked.2⟩
    | exact ⟨smallLabeling_7_3, smallLabeling_7_3_checked.1.isGracefulLabeling, smallLabeling_7_3_checked.2⟩
    | exact ⟨smallLabeling_7_4, smallLabeling_7_4_checked.1.isGracefulLabeling, smallLabeling_7_4_checked.2⟩
    | exact ⟨smallLabeling_7_5, smallLabeling_7_5_checked.1.isGracefulLabeling, smallLabeling_7_5_checked.2⟩
    | exact ⟨smallLabeling_7_6, smallLabeling_7_6_checked.1.isGracefulLabeling, smallLabeling_7_6_checked.2⟩
    | exact ⟨smallLabeling_7_7, smallLabeling_7_7_checked.1.isGracefulLabeling, smallLabeling_7_7_checked.2⟩
    | exact ⟨smallLabeling_8_1, smallLabeling_8_1_checked.1.isGracefulLabeling, smallLabeling_8_1_checked.2⟩
    | exact ⟨smallLabeling_8_2, smallLabeling_8_2_checked.1.isGracefulLabeling, smallLabeling_8_2_checked.2⟩
    | exact ⟨smallLabeling_8_3, smallLabeling_8_3_checked.1.isGracefulLabeling, smallLabeling_8_3_checked.2⟩
    | exact ⟨smallLabeling_8_4, smallLabeling_8_4_checked.1.isGracefulLabeling, smallLabeling_8_4_checked.2⟩
    | exact ⟨smallLabeling_8_5, smallLabeling_8_5_checked.1.isGracefulLabeling, smallLabeling_8_5_checked.2⟩
    | exact ⟨smallLabeling_8_6, smallLabeling_8_6_checked.1.isGracefulLabeling, smallLabeling_8_6_checked.2⟩
    | exact ⟨smallLabeling_8_7, smallLabeling_8_7_checked.1.isGracefulLabeling, smallLabeling_8_7_checked.2⟩
    | exact ⟨smallLabeling_8_8, smallLabeling_8_8_checked.1.isGracefulLabeling, smallLabeling_8_8_checked.2⟩
    | exact ⟨smallLabeling_9_3, smallLabeling_9_3_checked.1.isGracefulLabeling, smallLabeling_9_3_checked.2⟩
    | exact ⟨smallLabeling_9_4, smallLabeling_9_4_checked.1.isGracefulLabeling, smallLabeling_9_4_checked.2⟩
    | exact ⟨smallLabeling_9_5, smallLabeling_9_5_checked.1.isGracefulLabeling, smallLabeling_9_5_checked.2⟩
    | exact ⟨smallLabeling_9_6, smallLabeling_9_6_checked.1.isGracefulLabeling, smallLabeling_9_6_checked.2⟩
    | exact ⟨smallLabeling_9_7, smallLabeling_9_7_checked.1.isGracefulLabeling, smallLabeling_9_7_checked.2⟩
    | exact ⟨smallLabeling_9_8, smallLabeling_9_8_checked.1.isGracefulLabeling, smallLabeling_9_8_checked.2⟩
    | exact ⟨smallLabeling_10_5, smallLabeling_10_5_checked.1.isGracefulLabeling, smallLabeling_10_5_checked.2⟩
    | exact ⟨smallLabeling_10_6, smallLabeling_10_6_checked.1.isGracefulLabeling, smallLabeling_10_6_checked.2⟩
    | exact ⟨smallLabeling_10_7, smallLabeling_10_7_checked.1.isGracefulLabeling, smallLabeling_10_7_checked.2⟩
    | exact ⟨smallLabeling_10_8, smallLabeling_10_8_checked.1.isGracefulLabeling, smallLabeling_10_8_checked.2⟩
    | exact ⟨smallLabeling_10_9, smallLabeling_10_9_checked.1.isGracefulLabeling, smallLabeling_10_9_checked.2⟩
    | exact ⟨smallLabeling_11_7, smallLabeling_11_7_checked.1.isGracefulLabeling, smallLabeling_11_7_checked.2⟩
    | exact ⟨smallLabeling_11_8, smallLabeling_11_8_checked.1.isGracefulLabeling, smallLabeling_11_8_checked.2⟩
    | exact ⟨smallLabeling_11_9, smallLabeling_11_9_checked.1.isGracefulLabeling, smallLabeling_11_9_checked.2⟩
    | exact ⟨smallLabeling_12_9, smallLabeling_12_9_checked.1.isGracefulLabeling, smallLabeling_12_9_checked.2⟩
    | exact ⟨smallLabeling_12_10, smallLabeling_12_10_checked.1.isGracefulLabeling, smallLabeling_12_10_checked.2⟩

end Bounty
end

/- Amalgamation -/
section
namespace Math15.Graceful

lemma IsGracefulLabeling.dist_pos {n : ℕ} {G : SimpleGraph (Fin n)}
    {f : Fin n → ℕ} (hf : IsGracefulLabeling G f) {u v : Fin n} (h : G.Adj u v) :
    1 ≤ Nat.dist (f u) (f v) := by
  exact Nat.dist_pos_of_ne (fun heq => h.ne (hf.1 heq))

lemma IsGracefulLabeling.ordered_edge_unique {n : ℕ} {G : SimpleGraph (Fin n)}
    {f : Fin n → ℕ} (hf : IsGracefulLabeling G f) {u v x y : Fin n}
    (huv : u < v) (hxy : x < y) (h₁ : G.Adj u v) (h₂ : G.Adj x y)
    (heq : Nat.dist (f u) (f v) = Nat.dist (f x) (f y)) : u = x ∧ v = y := by
  obtain ⟨e, _, hunique⟩ := hf.2.2 (Nat.dist (f u) (f v)) (hf.dist_pos h₁) (hf.dist_le u v)
  have hu := hunique (u, v) ⟨huv, h₁, rfl⟩
  have hx := hunique (x, y) ⟨hxy, h₂, heq.symm⟩
  exact Prod.mk.inj (hu.trans hx.symm)

lemma IsGracefulLabeling.edge_unique {n : ℕ} {G : SimpleGraph (Fin n)}
    {f : Fin n → ℕ} (hf : IsGracefulLabeling G f) {u v x y : Fin n}
    (h₁ : G.Adj u v) (h₂ : G.Adj x y)
    (heq : Nat.dist (f u) (f v) = Nat.dist (f x) (f y)) :
    (u = x ∧ v = y) ∨ (u = y ∧ v = x) := by
  rcases lt_or_gt_of_ne h₁.ne with huv | hvu <;>
    rcases lt_or_gt_of_ne h₂.ne with hxy | hyx
  · exact Or.inl (hf.ordered_edge_unique huv hxy h₁ h₂ heq)
  · apply Or.inr
    exact hf.ordered_edge_unique huv hyx h₁ h₂.symm (by simpa [Nat.dist_comm] using heq)
  · apply Or.inr
    have h := hf.ordered_edge_unique hvu hxy h₁.symm h₂ (by simpa [Nat.dist_comm] using heq)
    exact ⟨h.2, h.1⟩
  · apply Or.inl
    have h := hf.ordered_edge_unique hvu hyx h₁.symm h₂.symm (by simpa [Nat.dist_comm] using heq)
    exact ⟨h.2, h.1⟩

/-- Two covered pieces carry compatible functions to their union. -/
lemma exists_glued_label {n a b : ℕ} (i : Fin a → Fin n) (j : Fin b → Fin n)
    (hi : Function.Injective i) (hj : Function.Injective j)
    (hcover : ∀ v, (∃ x, i x = v) ∨ (∃ y, j y = v))
    (f : Fin a → ℕ) (g : Fin b → ℕ)
    (hagree : ∀ x y, i x = j y → f x = g y) :
    ∃ h : Fin n → ℕ, (∀ x, h (i x) = f x) ∧ (∀ y, h (j y) = g y) := by
  classical
  let h : Fin n → ℕ := fun v =>
    if hv : ∃ x, i x = v then f hv.choose else g ((hcover v).resolve_left hv).choose
  refine ⟨h, ?_, ?_⟩
  · intro x
    have hx : ∃ z, i z = i x := ⟨x, rfl⟩
    simp only [h, dite_eq_left hx]
    exact congrArg f (hi hx.choose_spec)
  · intro y
    by_cases hy : ∃ x, i x = j y
    · simp only [h, dite_eq_left hy]
      exact hagree _ _ hy.choose_spec
    · simp only [h, dite_eq_right hy]
      exact congrArg g (hj ((hcover (j y)).resolve_left hy).choose_spec)

private lemma mapped_pair_eq {n a : ℕ} (i : Fin a → Fin n) {u v x y : Fin a}
    (huv : i u < i v) (hxy : i x < i y)
    (h : (u = x ∧ v = y) ∨ (u = y ∧ v = x)) :
    (i u, i v) = (i x, i y) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact False.elim (lt_asymm huv hxy)

/-- Amalgamate an alpha-labeled graph at its cut with a zero-labeled graceful graph.
The host is described by injective maps covering its vertices and edges, overlapping at
exactly the indicated link. The count hypothesis expresses disjointness of the two edge sets. -/
theorem isGraceful_amalgamation_at_cut {n a b : ℕ}
    (K : SimpleGraph (Fin n)) (L : SimpleGraph (Fin a)) (R : SimpleGraph (Fin b))
    (i : Fin a → Fin n) (j : Fin b → Fin n)
    (hi : Function.Injective i) (hj : Function.Injective j)
    (linkL : Fin a) (linkR : Fin b)
    (hoverlap : ∀ x y, i x = j y ↔ x = linkL ∧ y = linkR)
    (hcover : ∀ v, (∃ x, i x = v) ∨ (∃ y, j y = v))
    (hedges : ∀ u v, K.Adj u v ↔
      (∃ x y, L.Adj x y ∧ i x = u ∧ i y = v) ∨
      (∃ x y, R.Adj x y ∧ j x = u ∧ j y = v))
    (hcount : edgeCount K = edgeCount L + edgeCount R)
    (f : Fin a → ℕ) (g : Fin b → ℕ) (k : ℕ)
    (hf : IsAlphaLabeling L f k) (hg : IsGracefulLabeling R g)
    (hlinkL : f linkL = k) (hlinkR : g linkR = 0) : IsGraceful K := by
  classical
  have hlink : i linkL = j linkR := (hoverlap _ _).2 ⟨rfl, rfl⟩
  obtain ⟨h, hleft, hright⟩ := exists_glued_label i j hi hj hcover
    (fun x => shiftAboveCut k (edgeCount R) (f x)) (fun y => k + g y) (by
      intro x y heq
      obtain ⟨rfl, rfl⟩ := (hoverlap x y).1 heq
      simp [hlinkL, hlinkR, shiftAboveCut_link])
  have hcross (x : Fin a) (y : Fin b) (heq : h (i x) = h (j y)) : i x = j y := by
    rw [hleft, hright] at heq
    obtain ⟨hx, hy⟩ := (shiftAboveCut_eq_translate_iff (hg.2.1 y)).1 heq
    have hx' : x = linkL := hf.1.1 (hx.trans hlinkL.symm)
    have hy' : y = linkR := hg.1 (hy.trans hlinkR.symm)
    simpa [hx', hy'] using hlink
  have hleftDiff (x y : Fin a) (hadj : L.Adj x y) :
      Nat.dist (h (i x)) (h (i y)) = edgeCount R + Nat.dist (f x) (f y) := by
    rw [hleft, hleft]
    rcases hf.2.2 x y hadj with hc | hc
    · exact shiftAboveCut_dist hc.1 hc.2
    · rw [Nat.dist_comm (shiftAboveCut _ _ _), Nat.dist_comm (f x)]
      exact shiftAboveCut_dist hc.1 hc.2
  have hrightDiff (x y : Fin b) : Nat.dist (h (j x)) (h (j y)) = Nat.dist (g x) (g y) := by
    rw [hright, hright, translate_dist]
  apply isGraceful_of_injective_differences K h
  · intro u v heq
    rcases hcover u with ⟨x, rfl⟩ | ⟨x, rfl⟩ <;>
      rcases hcover v with ⟨y, rfl⟩ | ⟨y, rfl⟩
    · rw [hleft, hleft] at heq
      exact congrArg i (hf.1.1 (shiftAboveCut_injective k (edgeCount R) heq))
    · exact hcross x y heq
    · exact (hcross y x heq.symm).symm
    · rw [hright, hright] at heq
      exact congrArg j (hg.1 (Nat.add_left_cancel heq))
  · intro v
    rw [hcount]
    rcases hcover v with ⟨x, rfl⟩ | ⟨y, rfl⟩
    · rw [hleft]
      exact shiftAboveCut_le (hf.1.2.1 x)
    · rw [hright]
      exact translate_le (Nat.le_of_lt hf.2.1) (hg.2.1 y)
  · rintro ⟨u, v⟩ ⟨u', v'⟩ huv hadj huv' hadj' heq
    dsimp only at *
    rcases (hedges u v).1 hadj with ⟨x, y, hxy, rfl, rfl⟩ | ⟨x, y, hxy, rfl, rfl⟩ <;>
      rcases (hedges u' v').1 hadj' with ⟨x', y', hxy', rfl, rfl⟩ | ⟨x', y', hxy', rfl, rfl⟩
    · rw [hleftDiff x y hxy, hleftDiff x' y' hxy'] at heq
      exact mapped_pair_eq i huv huv' (hf.1.edge_unique hxy hxy' (Nat.add_left_cancel heq))
    · rw [hleftDiff x y hxy, hrightDiff] at heq
      exact False.elim ((amalgamation_edge_intervals_disjoint (hf.1.dist_pos hxy)
        (hg.dist_le x' y')) heq)
    · rw [hrightDiff, hleftDiff x' y' hxy'] at heq
      exact False.elim ((amalgamation_edge_intervals_disjoint (hf.1.dist_pos hxy')
        (hg.dist_le x y)) heq.symm)
    · rw [hrightDiff, hrightDiff] at heq
      exact mapped_pair_eq j huv huv' (hg.edge_unique hxy hxy' heq)


/-- The usual zero-or-cut form of graceful amalgamation. -/
theorem isGraceful_amalgamation {n a b : ℕ}
    (K : SimpleGraph (Fin n)) (L : SimpleGraph (Fin a)) (R : SimpleGraph (Fin b))
    (i : Fin a → Fin n) (j : Fin b → Fin n)
    (hi : Function.Injective i) (hj : Function.Injective j)
    (linkL : Fin a) (linkR : Fin b)
    (hoverlap : ∀ x y, i x = j y ↔ x = linkL ∧ y = linkR)
    (hcover : ∀ v, (∃ x, i x = v) ∨ (∃ y, j y = v))
    (hedges : ∀ u v, K.Adj u v ↔
      (∃ x y, L.Adj x y ∧ i x = u ∧ i y = v) ∨
      (∃ x y, R.Adj x y ∧ j x = u ∧ j y = v))
    (hcount : edgeCount K = edgeCount L + edgeCount R)
    (f : Fin a → ℕ) (g : Fin b → ℕ) (k : ℕ)
    (hf : IsAlphaLabeling L f k) (hg : IsGracefulLabeling R g)
    (hlinkL : f linkL = 0 ∨ f linkL = k) (hlinkR : g linkR = 0) : IsGraceful K := by
  rcases hlinkL with hz | hk
  · apply isGraceful_amalgamation_at_cut K L R i j hi hj linkL linkR
      hoverlap hcover hedges hcount _ g k hf.reverse hg _ hlinkR
    simp [reverseLabel, hz]
  · exact isGraceful_amalgamation_at_cut K L R i j hi hj linkL linkR
      hoverlap hcover hedges hcount f g k hf hg hk hlinkR

end Math15.Graceful
end

/- SpiderRegions -/
section
namespace Bounty
open Math15.Graceful

lemma IsGracefulLabeling.toSpiderCertificate {L : ℕ} {f : Fin (L+5) → ℕ}
    (hf : IsGracefulLabeling (spider L) f) : SpiderCertificate L f := by
  refine ⟨hf.1, ?_, ?_⟩
  · intro v
    simpa only [spider_edgeCount] using hf.2.1 v
  · intro i j hi hj heq
    have hpi : spiderParentFin i < i := spiderParent_lt hi
    have hpj : spiderParentFin j < j := spiderParent_lt hj
    exact (hf.ordered_edge_unique hpi hpj (Or.inl ⟨hpi, rfl⟩)
      (Or.inl ⟨hpj, rfl⟩) heq).2

lemma IsAlphaLabeling.toNatSpiderAlpha {L k : ℕ} {f : Fin (L+5) → ℕ}
    (hf : IsAlphaLabeling (spider L) f k) :
    NatSpiderAlpha L (extendSpiderLabel f) k := by
  apply AlphaSpiderCertificate.toNat
  exact ⟨IsGracefulLabeling.toSpiderCertificate hf.1, by simpa only [spider_edgeCount] using hf.2.1, hf.2.2⟩

/-- A pinned alpha spider can be lengthened using a uniformly sufficient bound
that depends only on the two label intervals at its cut. -/
theorem alpha_spider_append {d c₀ c k : ℕ} {f : Fin (d+c₀+5) → ℕ}
    (hL : 1 ≤ d+c₀) (hc₀ : c₀ ≤ c)
    (hf : IsAlphaLabeling (spider (d+c₀)) f k)
    (hz : f (spiderPin d c₀) = 0)
    (hm : max (k+1) (d+c₀+4-k) ≤ c-c₀) :
    ∃ g : Fin (d+c+5) → ℕ, IsGracefulLabeling (spider (d+c)) g ∧
      g (spiderPin d c) = 0 := by
  have hcert := (IsGracefulLabeling.toSpiderCertificate hf.1).toNat
  have ha := IsAlphaLabeling.toNatSpiderAlpha hf
  have hk : k < d+c₀+4 := by simpa only [spider_edgeCount] using hf.2.1
  have hbound := hcert.2.1 (d+c₀+4) (by omega)
  have hm1 : k+1 ≤ c-c₀ := (le_max_left _ _).trans hm
  have hm2 : d+c₀+4-k ≤ c-c₀ := (le_max_right _ _).trans hm
  obtain ⟨g, hg, hzero⟩ := hcert.exists_append hL ha (by omega)
    (m := c-c₀) (by apply max_le <;> omega)
  have hlen : (d+c₀)+(c-c₀) = d+c := by omega
  rw [hlen] at hg
  refine ⟨fun v => g v.val, hg.toCertificate.isGracefulLabeling, ?_⟩
  apply hzero (4+d) (by omega)
  simpa only [spiderPin, extendSpiderLabel, dite_eq_left (show 4+d < d+c₀+5 by omega)] using hz

/-- The region reached by starting with one vertex after the pin. -/
theorem second_region_pinned (d c : ℕ) (hd : 8 ≤ d) (hc : d/2+5 ≤ c) :
    ∃ f : Fin (d+c+5) → ℕ, IsGracefulLabeling (spider (d+c)) f ∧
      f (spiderPin d c) = 0 := by
  obtain ⟨f, k, hf, hz, hk1, hk2⟩ := normalized_one_tail d hd
  apply alpha_spider_append (c₀ := 1) (f := f) (by omega) (by omega) hf hz
  apply max_le <;> omega

def smallThreshold (d : ℕ) : ℕ :=
  match d with
  | 1 => 6
  | 2 => 5
  | 3 => 6
  | 4 => 6
  | 5 => 7
  | 6 => 7
  | 7 => 8
  | _ => 0

/-- The seven small pin distances each have a checked alpha seed. -/
theorem small_region_pinned (d c : ℕ) (hd : 1 ≤ d) (hd7 : d ≤ 7)
    (hc : smallThreshold d ≤ c) :
    ∃ f : Fin (d+c+5) → ℕ, IsGracefulLabeling (spider (d+c)) f ∧
      f (spiderPin d c) = 0 := by
  interval_cases d
  · apply alpha_spider_append (c₀ := 2) (f := startingLabeling_1)
      (by omega) (by norm_num [smallThreshold] at hc; omega)
      startingLabeling_1_checked.1.isAlphaLabeling startingLabeling_1_checked.2
    norm_num [smallThreshold] at hc ⊢
    omega
  · apply alpha_spider_append (c₀ := 1) (f := startingLabeling_2)
      (by omega) (by norm_num [smallThreshold] at hc; omega)
      startingLabeling_2_checked.1.isAlphaLabeling startingLabeling_2_checked.2
    norm_num [smallThreshold] at hc ⊢
    omega
  · apply alpha_spider_append (c₀ := 1) (f := startingLabeling_3)
      (by omega) (by norm_num [smallThreshold] at hc; omega)
      startingLabeling_3_checked.1.isAlphaLabeling startingLabeling_3_checked.2
    norm_num [smallThreshold] at hc ⊢
    omega
  · apply alpha_spider_append (c₀ := 1) (f := startingLabeling_4)
      (by omega) (by norm_num [smallThreshold] at hc; omega)
      startingLabeling_4_checked.1.isAlphaLabeling startingLabeling_4_checked.2
    norm_num [smallThreshold] at hc ⊢
    omega
  · apply alpha_spider_append (c₀ := 1) (f := startingLabeling_5)
      (by omega) (by norm_num [smallThreshold] at hc; omega)
      startingLabeling_5_checked.1.isAlphaLabeling startingLabeling_5_checked.2
    norm_num [smallThreshold] at hc ⊢
    omega
  · apply alpha_spider_append (c₀ := 1) (f := startingLabeling_6)
      (by omega) (by norm_num [smallThreshold] at hc; omega)
      startingLabeling_6_checked.1.isAlphaLabeling startingLabeling_6_checked.2
    norm_num [smallThreshold] at hc ⊢
    omega
  · apply alpha_spider_append (c₀ := 1) (f := startingLabeling_7)
      (by omega) (by norm_num [smallThreshold] at hc; omega)
      startingLabeling_7_checked.1.isAlphaLabeling startingLabeling_7_checked.2
    norm_num [smallThreshold] at hc ⊢
    omega

/-- Every S(2,2,d+c) admits a graceful labeling with the vertex at distance d
along the long arm labeled zero, for all positive d and c. -/
theorem spider_pinned_zero (d c : ℕ) (hd : 1 ≤ d) (hc : 1 ≤ c) :
    ∃ f : Fin (d+c+5) → ℕ, IsGracefulLabeling (spider (d+c)) f ∧
      f (spiderPin d c) = 0 := by
  by_cases hfirst : c ≤ 2*d-16
  · obtain ⟨f, hf⟩ := PathConstruction.canonical_pinned_first_region d c hd hc hfirst
    obtain ⟨g, k, hg, hz⟩ := hf.zeroPin (by omega)
    exact ⟨g, hg.1, hz⟩
  by_cases hlarge : 8 ≤ d
  · by_cases hsecond : d/2+5 ≤ c
    · exact second_region_pinned d c hlarge hsecond
    · apply finiteCase_pinned
      have hd12 : d ≤ 12 := by omega
      interval_cases d <;> norm_num [FiniteCase] <;> omega
  · by_cases hsmall : smallThreshold d ≤ c
    · exact small_region_pinned d c hd (by omega) hsmall
    · apply finiteCase_pinned
      have hd7 : d ≤ 7 := by omega
      interval_cases d <;> norm_num [FiniteCase, smallThreshold] at hsmall ⊢ <;> omega

end Bounty
end

/- DoubleEmbeddings -/
section
namespace Bounty
open Math15.Graceful

def pathEmbedNat (a d j : ℕ) : ℕ :=
  if j=a then 0 else if j < a then d+a-j else d+j

def coreEmbedNat (a b c d j : ℕ) : ℕ :=
  if j=0 then d else if j≤4 then d+a+b+c+j
  else if j≤d+4 then d+4-j else a+b+j-4

def pathEmbed (a b c d : ℕ) (j : Fin (a+b+1)) :
    Fin (doubleSpiderEdges a b c d 2 2+1) :=
  ⟨pathEmbedNat a d j.val, by
    have := j.isLt
    unfold pathEmbedNat doubleSpiderEdges
    split_ifs <;> omega⟩

def coreEmbed (a b c d : ℕ) (j : Fin (d+c+5)) :
    Fin (doubleSpiderEdges a b c d 2 2+1) :=
  ⟨coreEmbedNat a b c d j.val, by
    have := j.isLt
    unfold coreEmbedNat doubleSpiderEdges
    split_ifs <;> omega⟩

lemma pathEmbed_injective (a b c d : ℕ) : Function.Injective (pathEmbed a b c d) := by
  intro i j he
  have hi := i.isLt
  have hj := j.isLt
  have heq := congrArg Fin.val he
  dsimp [pathEmbed] at heq
  unfold pathEmbedNat at heq
  apply Fin.ext
  split_ifs at heq <;> omega

lemma coreEmbed_injective (a b c d : ℕ) : Function.Injective (coreEmbed a b c d) := by
  intro i j he
  have hi := i.isLt
  have hj := j.isLt
  have heq := congrArg Fin.val he
  dsimp [coreEmbed] at heq
  unfold coreEmbedNat at heq
  apply Fin.ext
  split_ifs at heq <;> omega

lemma pathEmbed_adj (a b c d : ℕ) (ha : 1≤a) (hb : 1≤b) (hc : 1≤c) (hd : 1≤d)
    (i j : Fin (a+b+1)) :
    (doubleSpider a b c d 2 2).Adj (pathEmbed a b c d i) (pathEmbed a b c d j) ↔
      (lineGraph (a+b)).Adj i j := by
  rw [lineGraph_adj_iff]
  have hi := i.isLt
  have hj := j.isLt
  change ((_  <  _ ∧ doubleSpiderParent a b c d 2 2 _ = _) ∨
    (_  <  _ ∧ doubleSpiderParent a b c d 2 2 _ = _)) ↔ _
  dsimp [pathEmbed]
  unfold pathEmbedNat doubleSpiderParent
  split_ifs <;> omega

lemma coreEmbedNat_region0 (a b c d i : ℕ) (hi0 : i=0) :
    coreEmbedNat a b c d i = d := by
  unfold coreEmbedNat
  split_ifs <;> omega

lemma coreEmbedNat_region1 (a b c d i : ℕ) (hi0 : i≠0) (hi1 : i≤4) :
    coreEmbedNat a b c d i = d+a+b+c+i := by
  unfold coreEmbedNat
  split_ifs <;> omega

lemma coreEmbedNat_region2 (a b c d i : ℕ) (hi0 : 4 < i) (hi1 : i≤d+4) :
    coreEmbedNat a b c d i = d+4-i := by
  unfold coreEmbedNat
  split_ifs <;> omega

lemma coreEmbedNat_region3 (a b c d i : ℕ) (hi0 : d+4 < i) :
    coreEmbedNat a b c d i = a+b+i-4 := by
  unfold coreEmbedNat
  split_ifs <;> omega

private lemma coreAdj_0_0 (a b c d i j : ℕ)
    (ha : 1≤a) (hb : 1≤b) (hc : 1≤c) (hd : 1≤d)
    (hi : i < d+c+5) (hj : j < d+c+5) (hi0 : i=0) (hj0 : j=0) :
    ((coreEmbedNat a b c d i  <  coreEmbedNat a b c d j ∧
        doubleSpiderParent a b c d 2 2 (coreEmbedNat a b c d j) = coreEmbedNat a b c d i) ∨
      (coreEmbedNat a b c d j  <  coreEmbedNat a b c d i ∧
        doubleSpiderParent a b c d 2 2 (coreEmbedNat a b c d i) = coreEmbedNat a b c d j)) ↔
      ((i < j ∧ spiderParent j=i) ∨ (j < i ∧ spiderParent i=j)) := by
  rw [coreEmbedNat_region0 a b c d i hi0, coreEmbedNat_region0 a b c d j hj0]
  unfold doubleSpiderParent spiderParent
  split_ifs <;> omega

private lemma coreAdj_0_1 (a b c d i j : ℕ)
    (ha : 1≤a) (hb : 1≤b) (hc : 1≤c) (hd : 1≤d)
    (hi : i < d+c+5) (hj : j < d+c+5) (hi0 : i=0) (hj0 : j≠0) (hj1 : j≤4) :
    ((coreEmbedNat a b c d i  <  coreEmbedNat a b c d j ∧
        doubleSpiderParent a b c d 2 2 (coreEmbedNat a b c d j) = coreEmbedNat a b c d i) ∨
      (coreEmbedNat a b c d j  <  coreEmbedNat a b c d i ∧
        doubleSpiderParent a b c d 2 2 (coreEmbedNat a b c d i) = coreEmbedNat a b c d j)) ↔
      ((i < j ∧ spiderParent j=i) ∨ (j < i ∧ spiderParent i=j)) := by
  rw [coreEmbedNat_region0 a b c d i hi0, coreEmbedNat_region1 a b c d j hj0 hj1]
  unfold doubleSpiderParent spiderParent
  split_ifs <;> omega

private lemma coreAdj_0_2 (a b c d i j : ℕ)
    (ha : 1≤a) (hb : 1≤b) (hc : 1≤c) (hd : 1≤d)
    (hi : i < d+c+5) (hj : j < d+c+5) (hi0 : i=0) (hj0 : 4 < j) (hj1 : j≤d+4) :
    ((coreEmbedNat a b c d i  <  coreEmbedNat a b c d j ∧
        doubleSpiderParent a b c d 2 2 (coreEmbedNat a b c d j) = coreEmbedNat a b c d i) ∨
      (coreEmbedNat a b c d j  <  coreEmbedNat a b c d i ∧
        doubleSpiderParent a b c d 2 2 (coreEmbedNat a b c d i) = coreEmbedNat a b c d j)) ↔
      ((i < j ∧ spiderParent j=i) ∨ (j < i ∧ spiderParent i=j)) := by
  rw [coreEmbedNat_region0 a b c d i hi0, coreEmbedNat_region2 a b c d j hj0 hj1]
  unfold doubleSpiderParent spiderParent
  split_ifs <;> omega

private lemma coreAdj_0_3 (a b c d i j : ℕ)
    (ha : 1≤a) (hb : 1≤b) (hc : 1≤c) (hd : 1≤d)
    (hi : i < d+c+5) (hj : j < d+c+5) (hi0 : i=0) (hj0 : d+4 < j) :
    ((coreEmbedNat a b c d i  <  coreEmbedNat a b c d j ∧
        doubleSpiderParent a b c d 2 2 (coreEmbedNat a b c d j) = coreEmbedNat a b c d i) ∨
      (coreEmbedNat a b c d j  <  coreEmbedNat a b c d i ∧
        doubleSpiderParent a b c d 2 2 (coreEmbedNat a b c d i) = coreEmbedNat a b c d j)) ↔
      ((i < j ∧ spiderParent j=i) ∨ (j < i ∧ spiderParent i=j)) := by
  rw [coreEmbedNat_region0 a b c d i hi0, coreEmbedNat_region3 a b c d j hj0]
  unfold doubleSpiderParent spiderParent
  split_ifs <;> omega

private lemma coreAdj_1_0 (a b c d i j : ℕ)
    (ha : 1≤a) (hb : 1≤b) (hc : 1≤c) (hd : 1≤d)
    (hi : i < d+c+5) (hj : j < d+c+5) (hi0 : i≠0) (hi1 : i≤4) (hj0 : j=0) :
    ((coreEmbedNat a b c d i  <  coreEmbedNat a b c d j ∧
        doubleSpiderParent a b c d 2 2 (coreEmbedNat a b c d j) = coreEmbedNat a b c d i) ∨
      (coreEmbedNat a b c d j  <  coreEmbedNat a b c d i ∧
        doubleSpiderParent a b c d 2 2 (coreEmbedNat a b c d i) = coreEmbedNat a b c d j)) ↔
      ((i < j ∧ spiderParent j=i) ∨ (j < i ∧ spiderParent i=j)) := by
  rw [coreEmbedNat_region1 a b c d i hi0 hi1, coreEmbedNat_region0 a b c d j hj0]
  unfold doubleSpiderParent spiderParent
  split_ifs <;> omega

private lemma coreAdj_1_1 (a b c d i j : ℕ)
    (ha : 1≤a) (hb : 1≤b) (hc : 1≤c) (hd : 1≤d)
    (hi : i < d+c+5) (hj : j < d+c+5) (hi0 : i≠0) (hi1 : i≤4) (hj0 : j≠0) (hj1 : j≤4) :
    ((coreEmbedNat a b c d i  <  coreEmbedNat a b c d j ∧
        doubleSpiderParent a b c d 2 2 (coreEmbedNat a b c d j) = coreEmbedNat a b c d i) ∨
      (coreEmbedNat a b c d j  <  coreEmbedNat a b c d i ∧
        doubleSpiderParent a b c d 2 2 (coreEmbedNat a b c d i) = coreEmbedNat a b c d j)) ↔
      ((i < j ∧ spiderParent j=i) ∨ (j < i ∧ spiderParent i=j)) := by
  rw [coreEmbedNat_region1 a b c d i hi0 hi1, coreEmbedNat_region1 a b c d j hj0 hj1]
  unfold doubleSpiderParent spiderParent
  split_ifs <;> omega

private lemma coreAdj_1_2 (a b c d i j : ℕ)
    (ha : 1≤a) (hb : 1≤b) (hc : 1≤c) (hd : 1≤d)
    (hi : i < d+c+5) (hj : j < d+c+5) (hi0 : i≠0) (hi1 : i≤4) (hj0 : 4 < j) (hj1 : j≤d+4) :
    ((coreEmbedNat a b c d i  <  coreEmbedNat a b c d j ∧
        doubleSpiderParent a b c d 2 2 (coreEmbedNat a b c d j) = coreEmbedNat a b c d i) ∨
      (coreEmbedNat a b c d j  <  coreEmbedNat a b c d i ∧
        doubleSpiderParent a b c d 2 2 (coreEmbedNat a b c d i) = coreEmbedNat a b c d j)) ↔
      ((i < j ∧ spiderParent j=i) ∨ (j < i ∧ spiderParent i=j)) := by
  rw [coreEmbedNat_region1 a b c d i hi0 hi1, coreEmbedNat_region2 a b c d j hj0 hj1]
  unfold doubleSpiderParent spiderParent
  split_ifs <;> omega

private lemma coreAdj_1_3 (a b c d i j : ℕ)
    (ha : 1≤a) (hb : 1≤b) (hc : 1≤c) (hd : 1≤d)
    (hi : i < d+c+5) (hj : j < d+c+5) (hi0 : i≠0) (hi1 : i≤4) (hj0 : d+4 < j) :
    ((coreEmbedNat a b c d i  <  coreEmbedNat a b c d j ∧
        doubleSpiderParent a b c d 2 2 (coreEmbedNat a b c d j) = coreEmbedNat a b c d i) ∨
      (coreEmbedNat a b c d j  <  coreEmbedNat a b c d i ∧
        doubleSpiderParent a b c d 2 2 (coreEmbedNat a b c d i) = coreEmbedNat a b c d j)) ↔
      ((i < j ∧ spiderParent j=i) ∨ (j < i ∧ spiderParent i=j)) := by
  rw [coreEmbedNat_region1 a b c d i hi0 hi1, coreEmbedNat_region3 a b c d j hj0]
  unfold doubleSpiderParent spiderParent
  split_ifs <;> omega

private lemma coreAdj_2_0 (a b c d i j : ℕ)
    (ha : 1≤a) (hb : 1≤b) (hc : 1≤c) (hd : 1≤d)
    (hi : i < d+c+5) (hj : j < d+c+5) (hi0 : 4 < i) (hi1 : i≤d+4) (hj0 : j=0) :
    ((coreEmbedNat a b c d i  <  coreEmbedNat a b c d j ∧
        doubleSpiderParent a b c d 2 2 (coreEmbedNat a b c d j) = coreEmbedNat a b c d i) ∨
      (coreEmbedNat a b c d j  <  coreEmbedNat a b c d i ∧
        doubleSpiderParent a b c d 2 2 (coreEmbedNat a b c d i) = coreEmbedNat a b c d j)) ↔
      ((i < j ∧ spiderParent j=i) ∨ (j < i ∧ spiderParent i=j)) := by
  rw [coreEmbedNat_region2 a b c d i hi0 hi1, coreEmbedNat_region0 a b c d j hj0]
  unfold doubleSpiderParent spiderParent
  split_ifs <;> omega

private lemma coreAdj_2_1 (a b c d i j : ℕ)
    (ha : 1≤a) (hb : 1≤b) (hc : 1≤c) (hd : 1≤d)
    (hi : i < d+c+5) (hj : j < d+c+5) (hi0 : 4 < i) (hi1 : i≤d+4) (hj0 : j≠0) (hj1 : j≤4) :
    ((coreEmbedNat a b c d i  <  coreEmbedNat a b c d j ∧
        doubleSpiderParent a b c d 2 2 (coreEmbedNat a b c d j) = coreEmbedNat a b c d i) ∨
      (coreEmbedNat a b c d j  <  coreEmbedNat a b c d i ∧
        doubleSpiderParent a b c d 2 2 (coreEmbedNat a b c d i) = coreEmbedNat a b c d j)) ↔
      ((i < j ∧ spiderParent j=i) ∨ (j < i ∧ spiderParent i=j)) := by
  rw [coreEmbedNat_region2 a b c d i hi0 hi1, coreEmbedNat_region1 a b c d j hj0 hj1]
  unfold doubleSpiderParent spiderParent
  split_ifs <;> omega

private lemma coreAdj_2_2 (a b c d i j : ℕ)
    (ha : 1≤a) (hb : 1≤b) (hc : 1≤c) (hd : 1≤d)
    (hi : i < d+c+5) (hj : j < d+c+5) (hi0 : 4 < i) (hi1 : i≤d+4) (hj0 : 4 < j) (hj1 : j≤d+4) :
    ((coreEmbedNat a b c d i  <  coreEmbedNat a b c d j ∧
        doubleSpiderParent a b c d 2 2 (coreEmbedNat a b c d j) = coreEmbedNat a b c d i) ∨
      (coreEmbedNat a b c d j  <  coreEmbedNat a b c d i ∧
        doubleSpiderParent a b c d 2 2 (coreEmbedNat a b c d i) = coreEmbedNat a b c d j)) ↔
      ((i < j ∧ spiderParent j=i) ∨ (j < i ∧ spiderParent i=j)) := by
  rw [coreEmbedNat_region2 a b c d i hi0 hi1, coreEmbedNat_region2 a b c d j hj0 hj1]
  unfold doubleSpiderParent spiderParent
  split_ifs <;> omega

private lemma coreAdj_2_3 (a b c d i j : ℕ)
    (ha : 1≤a) (hb : 1≤b) (hc : 1≤c) (hd : 1≤d)
    (hi : i < d+c+5) (hj : j < d+c+5) (hi0 : 4 < i) (hi1 : i≤d+4) (hj0 : d+4 < j) :
    ((coreEmbedNat a b c d i  <  coreEmbedNat a b c d j ∧
        doubleSpiderParent a b c d 2 2 (coreEmbedNat a b c d j) = coreEmbedNat a b c d i) ∨
      (coreEmbedNat a b c d j  <  coreEmbedNat a b c d i ∧
        doubleSpiderParent a b c d 2 2 (coreEmbedNat a b c d i) = coreEmbedNat a b c d j)) ↔
      ((i < j ∧ spiderParent j=i) ∨ (j < i ∧ spiderParent i=j)) := by
  rw [coreEmbedNat_region2 a b c d i hi0 hi1, coreEmbedNat_region3 a b c d j hj0]
  unfold doubleSpiderParent spiderParent
  split_ifs <;> omega

private lemma coreAdj_3_0 (a b c d i j : ℕ)
    (ha : 1≤a) (hb : 1≤b) (hc : 1≤c) (hd : 1≤d)
    (hi : i < d+c+5) (hj : j < d+c+5) (hi0 : d+4 < i) (hj0 : j=0) :
    ((coreEmbedNat a b c d i  <  coreEmbedNat a b c d j ∧
        doubleSpiderParent a b c d 2 2 (coreEmbedNat a b c d j) = coreEmbedNat a b c d i) ∨
      (coreEmbedNat a b c d j  <  coreEmbedNat a b c d i ∧
        doubleSpiderParent a b c d 2 2 (coreEmbedNat a b c d i) = coreEmbedNat a b c d j)) ↔
      ((i < j ∧ spiderParent j=i) ∨ (j < i ∧ spiderParent i=j)) := by
  rw [coreEmbedNat_region3 a b c d i hi0, coreEmbedNat_region0 a b c d j hj0]
  unfold doubleSpiderParent spiderParent
  split_ifs <;> omega

private lemma coreAdj_3_1 (a b c d i j : ℕ)
    (ha : 1≤a) (hb : 1≤b) (hc : 1≤c) (hd : 1≤d)
    (hi : i < d+c+5) (hj : j < d+c+5) (hi0 : d+4 < i) (hj0 : j≠0) (hj1 : j≤4) :
    ((coreEmbedNat a b c d i  <  coreEmbedNat a b c d j ∧
        doubleSpiderParent a b c d 2 2 (coreEmbedNat a b c d j) = coreEmbedNat a b c d i) ∨
      (coreEmbedNat a b c d j  <  coreEmbedNat a b c d i ∧
        doubleSpiderParent a b c d 2 2 (coreEmbedNat a b c d i) = coreEmbedNat a b c d j)) ↔
      ((i < j ∧ spiderParent j=i) ∨ (j < i ∧ spiderParent i=j)) := by
  rw [coreEmbedNat_region3 a b c d i hi0, coreEmbedNat_region1 a b c d j hj0 hj1]
  unfold doubleSpiderParent spiderParent
  split_ifs <;> omega

private lemma coreAdj_3_2 (a b c d i j : ℕ)
    (ha : 1≤a) (hb : 1≤b) (hc : 1≤c) (hd : 1≤d)
    (hi : i < d+c+5) (hj : j < d+c+5) (hi0 : d+4 < i) (hj0 : 4 < j) (hj1 : j≤d+4) :
    ((coreEmbedNat a b c d i  <  coreEmbedNat a b c d j ∧
        doubleSpiderParent a b c d 2 2 (coreEmbedNat a b c d j) = coreEmbedNat a b c d i) ∨
      (coreEmbedNat a b c d j  <  coreEmbedNat a b c d i ∧
        doubleSpiderParent a b c d 2 2 (coreEmbedNat a b c d i) = coreEmbedNat a b c d j)) ↔
      ((i < j ∧ spiderParent j=i) ∨ (j < i ∧ spiderParent i=j)) := by
  rw [coreEmbedNat_region3 a b c d i hi0, coreEmbedNat_region2 a b c d j hj0 hj1]
  unfold doubleSpiderParent spiderParent
  split_ifs <;> omega

private lemma coreAdj_3_3 (a b c d i j : ℕ)
    (ha : 1≤a) (hb : 1≤b) (hc : 1≤c) (hd : 1≤d)
    (hi : i < d+c+5) (hj : j < d+c+5) (hi0 : d+4 < i) (hj0 : d+4 < j) :
    ((coreEmbedNat a b c d i  <  coreEmbedNat a b c d j ∧
        doubleSpiderParent a b c d 2 2 (coreEmbedNat a b c d j) = coreEmbedNat a b c d i) ∨
      (coreEmbedNat a b c d j  <  coreEmbedNat a b c d i ∧
        doubleSpiderParent a b c d 2 2 (coreEmbedNat a b c d i) = coreEmbedNat a b c d j)) ↔
      ((i < j ∧ spiderParent j=i) ∨ (j < i ∧ spiderParent i=j)) := by
  rw [coreEmbedNat_region3 a b c d i hi0, coreEmbedNat_region3 a b c d j hj0]
  unfold doubleSpiderParent spiderParent
  split_ifs <;> omega

lemma coreEmbed_adj (a b c d : ℕ) (ha : 1≤a) (hb : 1≤b) (hc : 1≤c) (hd : 1≤d)
    (i j : Fin (d+c+5)) :
    (doubleSpider a b c d 2 2).Adj (coreEmbed a b c d i) (coreEmbed a b c d j) ↔
      (spider (d+c)).Adj i j := by
  change ((coreEmbedNat a b c d i.val  <  coreEmbedNat a b c d j.val ∧
        doubleSpiderParent a b c d 2 2 (coreEmbedNat a b c d j.val) = coreEmbedNat a b c d i.val) ∨
      (coreEmbedNat a b c d j.val  <  coreEmbedNat a b c d i.val ∧
        doubleSpiderParent a b c d 2 2 (coreEmbedNat a b c d i.val) = coreEmbedNat a b c d j.val)) ↔
      ((i.val < j.val ∧ spiderParent j.val=i.val) ∨ (j.val < i.val ∧ spiderParent i.val=j.val))
  have hir : i.val=0 ∨ (i.val≠0 ∧ i.val≤4) ∨ (4 < i.val ∧ i.val≤d+4) ∨ d+4 < i.val := by omega
  have hjr : j.val=0 ∨ (j.val≠0 ∧ j.val≤4) ∨ (4 < j.val ∧ j.val≤d+4) ∨ d+4 < j.val := by omega
  rcases hir with hi0 | ⟨hi0, hi1⟩ | ⟨hi0, hi1⟩ | hi0 <;>
    rcases hjr with hj0 | ⟨hj0, hj1⟩ | ⟨hj0, hj1⟩ | hj0
  · exact coreAdj_0_0 a b c d i.val j.val ha hb hc hd i.isLt j.isLt hi0 hj0
  · exact coreAdj_0_1 a b c d i.val j.val ha hb hc hd i.isLt j.isLt hi0 hj0 hj1
  · exact coreAdj_0_2 a b c d i.val j.val ha hb hc hd i.isLt j.isLt hi0 hj0 hj1
  · exact coreAdj_0_3 a b c d i.val j.val ha hb hc hd i.isLt j.isLt hi0 hj0
  · exact coreAdj_1_0 a b c d i.val j.val ha hb hc hd i.isLt j.isLt hi0 hi1 hj0
  · exact coreAdj_1_1 a b c d i.val j.val ha hb hc hd i.isLt j.isLt hi0 hi1 hj0 hj1
  · exact coreAdj_1_2 a b c d i.val j.val ha hb hc hd i.isLt j.isLt hi0 hi1 hj0 hj1
  · exact coreAdj_1_3 a b c d i.val j.val ha hb hc hd i.isLt j.isLt hi0 hi1 hj0
  · exact coreAdj_2_0 a b c d i.val j.val ha hb hc hd i.isLt j.isLt hi0 hi1 hj0
  · exact coreAdj_2_1 a b c d i.val j.val ha hb hc hd i.isLt j.isLt hi0 hi1 hj0 hj1
  · exact coreAdj_2_2 a b c d i.val j.val ha hb hc hd i.isLt j.isLt hi0 hi1 hj0 hj1
  · exact coreAdj_2_3 a b c d i.val j.val ha hb hc hd i.isLt j.isLt hi0 hi1 hj0
  · exact coreAdj_3_0 a b c d i.val j.val ha hb hc hd i.isLt j.isLt hi0 hj0
  · exact coreAdj_3_1 a b c d i.val j.val ha hb hc hd i.isLt j.isLt hi0 hj0 hj1
  · exact coreAdj_3_2 a b c d i.val j.val ha hb hc hd i.isLt j.isLt hi0 hj0 hj1
  · exact coreAdj_3_3 a b c d i.val j.val ha hb hc hd i.isLt j.isLt hi0 hj0

end Bounty
end

/- DoubleAmalgamation -/
section
namespace Bounty
open Math15.Graceful

lemma path_core_overlap (a b c d : ℕ) (hd : 1≤d)
    (i : Fin (a+b+1)) (j : Fin (d+c+5)) :
    pathEmbed a b c d i = coreEmbed a b c d j ↔
      i = ⟨a, by omega⟩ ∧ j = spiderPin d c := by
  constructor
  · intro he
    have hi := i.isLt
    have hj := j.isLt
    have heq := congrArg Fin.val he
    dsimp [pathEmbed, coreEmbed] at heq
    unfold pathEmbedNat coreEmbedNat at heq
    constructor <;> apply Fin.ext
    all_goals split_ifs at heq <;> simp only [spiderPin] <;> omega
  · rintro ⟨rfl, rfl⟩
    apply Fin.ext
    simp only [pathEmbed, coreEmbed, spiderPin]
    unfold pathEmbedNat coreEmbedNat
    split_ifs <;> omega

def PathZone (a b d v : ℕ) : Prop := v=0 ∨ d<v ∧ v≤d+a+b
def CoreZone (a b d v : ℕ) : Prop := v≤d ∨ d+a+b<v

lemma pathEmbed_surj (a b c d : ℕ)
    (v : Fin (doubleSpiderEdges a b c d 2 2+1)) (hv : PathZone a b d v.val) :
    ∃ i, pathEmbed a b c d i = v := by
  let i := if v.val=0 then a else if v.val≤d+a then d+a-v.val else v.val-d
  have hi : i < a+b+1 := by
    unfold i PathZone at *
    split_ifs <;> omega
  refine ⟨⟨i, hi⟩, ?_⟩
  apply Fin.ext
  change pathEmbedNat a d i = v.val
  unfold pathEmbedNat i PathZone at *
  split_ifs <;> omega

lemma coreEmbed_surj (a b c d : ℕ) (hd : 1≤d)
    (v : Fin (doubleSpiderEdges a b c d 2 2+1)) (hv : CoreZone a b d v.val) :
    ∃ i, coreEmbed a b c d i = v := by
  let i := if v.val=d then 0 else if v.val≤d then d+4-v.val
    else if v.val≤d+a+b+c then v.val-a-b+4 else v.val-(d+a+b+c)
  have hb := v.isLt
  unfold doubleSpiderEdges at hb
  have hi : i < d+c+5 := by
    unfold i CoreZone at *
    split_ifs <;> omega
  refine ⟨⟨i, hi⟩, ?_⟩
  apply Fin.ext
  change coreEmbedNat a b c d i = v.val
  unfold coreEmbedNat i CoreZone at *
  split_ifs at * <;> omega

lemma path_core_cover (a b c d : ℕ) (hd : 1≤d)
    (v : Fin (doubleSpiderEdges a b c d 2 2+1)) :
    (∃ i, pathEmbed a b c d i = v) ∨ (∃ i, coreEmbed a b c d i = v) := by
  by_cases h : PathZone a b d v.val
  · exact Or.inl (pathEmbed_surj a b c d v h)
  · apply Or.inr
    apply coreEmbed_surj a b c d hd v
    unfold PathZone at h
    unfold CoreZone
    omega

lemma double_edges_zones (a b c d : ℕ) (ha : 1≤a) (hb : 1≤b) (hc : 1≤c) (hd : 1≤d)
    (u v : Fin (doubleSpiderEdges a b c d 2 2+1))
    (h : (doubleSpider a b c d 2 2).Adj u v) :
    (PathZone a b d u.val ∧ PathZone a b d v.val) ∨
      (CoreZone a b d u.val ∧ CoreZone a b d v.val) := by
  have hu := u.isLt
  have hv := v.isLt
  unfold doubleSpiderEdges at hu hv
  change ((_ < _ ∧ doubleSpiderParent a b c d 2 2 _ = _) ∨
    (_ < _ ∧ doubleSpiderParent a b c d 2 2 _ = _)) at h
  unfold PathZone CoreZone doubleSpiderParent at *
  split_ifs at h <;> omega

lemma path_core_edges (a b c d : ℕ) (ha : 1≤a) (hb : 1≤b) (hc : 1≤c) (hd : 1≤d)
    (u v : Fin (doubleSpiderEdges a b c d 2 2+1)) :
    (doubleSpider a b c d 2 2).Adj u v ↔
      (∃ i j, (lineGraph (a+b)).Adj i j ∧ pathEmbed a b c d i=u ∧ pathEmbed a b c d j=v) ∨
      (∃ i j, (spider (d+c)).Adj i j ∧ coreEmbed a b c d i=u ∧ coreEmbed a b c d j=v) := by
  constructor
  · intro h
    rcases double_edges_zones a b c d ha hb hc hd u v h with hzone | hzone
    · obtain ⟨i, hi⟩ := pathEmbed_surj a b c d u hzone.1
      obtain ⟨j, hj⟩ := pathEmbed_surj a b c d v hzone.2
      refine Or.inl ⟨i, j, ?_, hi, hj⟩
      apply (pathEmbed_adj a b c d ha hb hc hd i j).1
      rwa [hi, hj]
    · obtain ⟨i, hi⟩ := coreEmbed_surj a b c d hd u hzone.1
      obtain ⟨j, hj⟩ := coreEmbed_surj a b c d hd v hzone.2
      refine Or.inr ⟨i, j, ?_, hi, hj⟩
      apply (coreEmbed_adj a b c d ha hb hc hd i j).1
      rwa [hi, hj]
  · rintro (⟨i, j, hij, rfl, rfl⟩ | ⟨i, j, hij, rfl, rfl⟩)
    · exact (pathEmbed_adj a b c d ha hb hc hd i j).2 hij
    · exact (coreEmbed_adj a b c d ha hb hc hd i j).2 hij

/-- The S(2,2,d+c) core is amalgamated with a path through the other branch vertex. -/
theorem doubleSpider_graceful_twoArms (a b c d : ℕ)
    (ha : 1≤a) (hb : 1≤b) (hc : 1≤c) (hd : 1≤d) (hex : a≠2 ∨ b≠2) :
    IsGraceful (doubleSpider a b c d 2 2) := by
  obtain ⟨p, k, hp, hpzero⟩ := rosa_zero_alpha_path a b ha hb hex
  obtain ⟨f, hf, hfzero⟩ := spider_pinned_zero d c hd hc
  apply isGraceful_amalgamation (doubleSpider a b c d 2 2) (lineGraph (a+b)) (spider (d+c))
    (pathEmbed a b c d) (coreEmbed a b c d)
    (pathEmbed_injective a b c d) (coreEmbed_injective a b c d)
    ⟨a, by omega⟩ (spiderPin d c)
    (path_core_overlap a b c d hd) (path_core_cover a b c d hd)
    (path_core_edges a b c d ha hb hc hd) ?_
    (fun i => p i.val) f k hp.toLineAlpha hf (Or.inl hpzero) hfzero
  rw [doubleSpider_edgeCount, lineGraph_edgeCount, spider_edgeCount]
  unfold doubleSpiderEdges
  omega

end Bounty
end

/- FourDefinitions -/
section
namespace Bounty

def fourParent (a b c j : ℕ) : ℕ :=
  if j=1 ∨ j=a+1 ∨ j=a+b+1 ∨ j=a+b+c+1 then 0 else j-1

def FourLeafZero (a b c d : ℕ) : Prop :=
  ∃f : ℕ → ℕ, NatParentCertificate (a+b+c+d) (fourParent a b c) f ∧ f (a+b+c+d)=0

theorem fourParent_lt (a b c j : ℕ) (hj : 0<j) : fourParent a b c j<j := by
  unfold fourParent
  split_ifs <;> omega

end Bounty
end

/- GeneralAmalgamation -/
section
namespace Bounty
open Math15.Graceful

/-- The path through the degree-three hub, read from the end of its first arm. -/
def generalPathCode (a b c d e j : ℕ) : ℕ :=
  if j=e then d else if j<e then d+a+b+c+e-j else d+a+b+c+j

/-- Rotate the distinguished fourth arm of a four-legged spider to the spine. -/
def generalCoreCode (a b c d j : ℕ) : ℕ :=
  if j=0 then 0 else if j≤a+b+c then d+j else j-(a+b+c)

def generalPathEmbed (a b c d e f : ℕ) (j : Fin (e+f+1)) :
    Fin (doubleSpiderEdges a b c d e f+1) :=
  ⟨generalPathCode a b c d e j.val, by
    have := j.isLt
    dsimp [generalPathCode, doubleSpiderEdges]
    split_ifs <;> omega⟩

def generalCoreEmbed (a b c d e f : ℕ) (j : Fin (a+b+c+d+1)) :
    Fin (doubleSpiderEdges a b c d e f+1) :=
  ⟨generalCoreCode a b c d j.val, by
    have := j.isLt
    dsimp [generalCoreCode, doubleSpiderEdges]
    split_ifs <;> omega⟩

lemma generalPathEmbed_injective (a b c d e f : ℕ) :
    Function.Injective (generalPathEmbed a b c d e f) := by
  intro i j hij
  have hi := i.isLt
  have hj := j.isLt
  have h := congrArg Fin.val hij
  dsimp [generalPathEmbed, generalPathCode] at h
  apply Fin.ext
  split_ifs at h <;> omega

lemma generalCoreEmbed_injective (a b c d e f : ℕ) :
    Function.Injective (generalCoreEmbed a b c d e f) := by
  intro i j hij
  have hi := i.isLt
  have hj := j.isLt
  have h := congrArg Fin.val hij
  dsimp [generalCoreEmbed, generalCoreCode] at h
  apply Fin.ext
  split_ifs at h <;> omega

lemma generalEmbed_overlap (a b c d e f : ℕ) (hd : 0<d)
    (x : Fin (e+f+1)) (y : Fin (a+b+c+d+1)) :
    generalPathEmbed a b c d e f x=generalCoreEmbed a b c d e f y ↔
      x.val=e ∧ y.val=a+b+c+d := by
  have hx := x.isLt
  have hy := y.isLt
  simp only [Fin.ext_iff, generalPathEmbed, generalCoreEmbed,
    generalPathCode, generalCoreCode]
  split_ifs <;> omega

lemma generalEmbed_cover (a b c d e f : ℕ)
    (v : Fin (doubleSpiderEdges a b c d e f+1)) :
    (∃x, generalPathEmbed a b c d e f x=v) ∨
    (∃y, generalCoreEmbed a b c d e f y=v) := by
  have hv := v.isLt
  dsimp [doubleSpiderEdges] at hv
  by_cases hcore : v.val≤d+a+b+c
  · right
    by_cases hz : v.val=0
    · refine ⟨0, ?_⟩
      apply Fin.ext
      simp [generalCoreEmbed, generalCoreCode, hz]
    · by_cases hspine : v.val≤d
      · refine ⟨⟨a+b+c+v.val, by omega⟩, ?_⟩
        apply Fin.ext
        dsimp [generalCoreEmbed, generalCoreCode]
        split_ifs <;> omega
      · refine ⟨⟨v.val-d, by omega⟩, ?_⟩
        apply Fin.ext
        dsimp [generalCoreEmbed, generalCoreCode]
        split_ifs <;> omega
  · left
    by_cases hfirst : v.val≤d+a+b+c+e
    · refine ⟨⟨d+a+b+c+e-v.val, by omega⟩, ?_⟩
      apply Fin.ext
      dsimp [generalPathEmbed, generalPathCode]
      split_ifs <;> omega
    · refine ⟨⟨v.val-(d+a+b+c), by omega⟩, ?_⟩
      apply Fin.ext
      dsimp [generalPathEmbed, generalPathCode]
      split_ifs <;> omega

lemma generalPathEmbed_adj_left_left (a b c d e f : ℕ)
    (ha : 0<a) (hb : 0<b) (hc : 0<c) (hd : 0<d) (he : 0<e) (hf : 0<f)
    (x y : Fin (e+f+1)) (hxcase : x.val<e) (hycase : y.val<e) :
    (doubleSpider a b c d e f).Adj
      (generalPathEmbed a b c d e f x) (generalPathEmbed a b c d e f y) ↔
    (lineGraph (e+f)).Adj x y := by
  have hx := x.isLt
  have hy := y.isLt
  rw [lineGraph_adj_iff]
  dsimp [doubleSpider, parentGraph, generalPathEmbed, generalPathCode,
    doubleSpiderParent]
  simp only [show x.val≠e from by omega, hxcase, show y.val≠e from by omega, hycase, ite_true, ite_false]
  split_ifs <;> omega

lemma generalPathEmbed_adj_left_hub (a b c d e f : ℕ)
    (ha : 0<a) (hb : 0<b) (hc : 0<c) (hd : 0<d) (he : 0<e) (hf : 0<f)
    (x y : Fin (e+f+1)) (hxcase : x.val<e) (hycase : y.val=e) :
    (doubleSpider a b c d e f).Adj
      (generalPathEmbed a b c d e f x) (generalPathEmbed a b c d e f y) ↔
    (lineGraph (e+f)).Adj x y := by
  have hx := x.isLt
  have hy := y.isLt
  rw [lineGraph_adj_iff]
  dsimp [doubleSpider, parentGraph, generalPathEmbed, generalPathCode,
    doubleSpiderParent]
  simp only [show x.val≠e from by omega, hxcase, hycase, ite_true, ite_false]
  split_ifs <;> omega

lemma generalPathEmbed_adj_left_right (a b c d e f : ℕ)
    (ha : 0<a) (hb : 0<b) (hc : 0<c) (hd : 0<d) (he : 0<e) (hf : 0<f)
    (x y : Fin (e+f+1)) (hxcase : x.val<e) (hycase : e<y.val) :
    (doubleSpider a b c d e f).Adj
      (generalPathEmbed a b c d e f x) (generalPathEmbed a b c d e f y) ↔
    (lineGraph (e+f)).Adj x y := by
  have hx := x.isLt
  have hy := y.isLt
  rw [lineGraph_adj_iff]
  dsimp [doubleSpider, parentGraph, generalPathEmbed, generalPathCode,
    doubleSpiderParent]
  simp only [show x.val≠e from by omega, hxcase, show y.val≠e from by omega, show ¬y.val<e from by omega, ite_true, ite_false]
  split_ifs <;> omega

lemma generalPathEmbed_adj_hub_left (a b c d e f : ℕ)
    (ha : 0<a) (hb : 0<b) (hc : 0<c) (hd : 0<d) (he : 0<e) (hf : 0<f)
    (x y : Fin (e+f+1)) (hxcase : x.val=e) (hycase : y.val<e) :
    (doubleSpider a b c d e f).Adj
      (generalPathEmbed a b c d e f x) (generalPathEmbed a b c d e f y) ↔
    (lineGraph (e+f)).Adj x y := by
  have hx := x.isLt
  have hy := y.isLt
  rw [lineGraph_adj_iff]
  dsimp [doubleSpider, parentGraph, generalPathEmbed, generalPathCode,
    doubleSpiderParent]
  simp only [hxcase, show y.val≠e from by omega, hycase, ite_true, ite_false]
  split_ifs <;> omega

lemma generalPathEmbed_adj_hub_hub (a b c d e f : ℕ)
    (ha : 0<a) (hb : 0<b) (hc : 0<c) (hd : 0<d) (he : 0<e) (hf : 0<f)
    (x y : Fin (e+f+1)) (hxcase : x.val=e) (hycase : y.val=e) :
    (doubleSpider a b c d e f).Adj
      (generalPathEmbed a b c d e f x) (generalPathEmbed a b c d e f y) ↔
    (lineGraph (e+f)).Adj x y := by
  have hx := x.isLt
  have hy := y.isLt
  rw [lineGraph_adj_iff]
  dsimp [doubleSpider, parentGraph, generalPathEmbed, generalPathCode,
    doubleSpiderParent]
  simp only [hxcase, hycase, ite_true, ite_false]
  split_ifs <;> omega

lemma generalPathEmbed_adj_hub_right (a b c d e f : ℕ)
    (ha : 0<a) (hb : 0<b) (hc : 0<c) (hd : 0<d) (he : 0<e) (hf : 0<f)
    (x y : Fin (e+f+1)) (hxcase : x.val=e) (hycase : e<y.val) :
    (doubleSpider a b c d e f).Adj
      (generalPathEmbed a b c d e f x) (generalPathEmbed a b c d e f y) ↔
    (lineGraph (e+f)).Adj x y := by
  have hx := x.isLt
  have hy := y.isLt
  rw [lineGraph_adj_iff]
  dsimp [doubleSpider, parentGraph, generalPathEmbed, generalPathCode,
    doubleSpiderParent]
  simp only [hxcase, show y.val≠e from by omega, show ¬y.val<e from by omega, ite_true, ite_false]
  split_ifs <;> omega

lemma generalPathEmbed_adj_right_left (a b c d e f : ℕ)
    (ha : 0<a) (hb : 0<b) (hc : 0<c) (hd : 0<d) (he : 0<e) (hf : 0<f)
    (x y : Fin (e+f+1)) (hxcase : e<x.val) (hycase : y.val<e) :
    (doubleSpider a b c d e f).Adj
      (generalPathEmbed a b c d e f x) (generalPathEmbed a b c d e f y) ↔
    (lineGraph (e+f)).Adj x y := by
  have hx := x.isLt
  have hy := y.isLt
  rw [lineGraph_adj_iff]
  dsimp [doubleSpider, parentGraph, generalPathEmbed, generalPathCode,
    doubleSpiderParent]
  simp only [show x.val≠e from by omega, show ¬x.val<e from by omega, show y.val≠e from by omega, hycase, ite_true, ite_false]
  split_ifs <;> omega

lemma generalPathEmbed_adj_right_hub (a b c d e f : ℕ)
    (ha : 0<a) (hb : 0<b) (hc : 0<c) (hd : 0<d) (he : 0<e) (hf : 0<f)
    (x y : Fin (e+f+1)) (hxcase : e<x.val) (hycase : y.val=e) :
    (doubleSpider a b c d e f).Adj
      (generalPathEmbed a b c d e f x) (generalPathEmbed a b c d e f y) ↔
    (lineGraph (e+f)).Adj x y := by
  have hx := x.isLt
  have hy := y.isLt
  rw [lineGraph_adj_iff]
  dsimp [doubleSpider, parentGraph, generalPathEmbed, generalPathCode,
    doubleSpiderParent]
  simp only [show x.val≠e from by omega, show ¬x.val<e from by omega, hycase, ite_true, ite_false]
  split_ifs <;> omega

lemma generalPathEmbed_adj_right_right (a b c d e f : ℕ)
    (ha : 0<a) (hb : 0<b) (hc : 0<c) (hd : 0<d) (he : 0<e) (hf : 0<f)
    (x y : Fin (e+f+1)) (hxcase : e<x.val) (hycase : e<y.val) :
    (doubleSpider a b c d e f).Adj
      (generalPathEmbed a b c d e f x) (generalPathEmbed a b c d e f y) ↔
    (lineGraph (e+f)).Adj x y := by
  have hx := x.isLt
  have hy := y.isLt
  rw [lineGraph_adj_iff]
  dsimp [doubleSpider, parentGraph, generalPathEmbed, generalPathCode,
    doubleSpiderParent]
  simp only [show x.val≠e from by omega, show ¬x.val<e from by omega, show y.val≠e from by omega, show ¬y.val<e from by omega, ite_true, ite_false]
  split_ifs <;> omega

lemma generalPathEmbed_adj (a b c d e f : ℕ)
    (ha : 0<a) (hb : 0<b) (hc : 0<c) (hd : 0<d) (he : 0<e) (hf : 0<f)
    (x y : Fin (e+f+1)) :
    (doubleSpider a b c d e f).Adj
      (generalPathEmbed a b c d e f x) (generalPathEmbed a b c d e f y) ↔
    (lineGraph (e+f)).Adj x y := by
  rcases lt_trichotomy x.val e with hx | hx | hx <;>
    rcases lt_trichotomy y.val e with hy | hy | hy
  · exact generalPathEmbed_adj_left_left a b c d e f ha hb hc hd he hf x y hx hy
  · exact generalPathEmbed_adj_left_hub a b c d e f ha hb hc hd he hf x y hx hy
  · exact generalPathEmbed_adj_left_right a b c d e f ha hb hc hd he hf x y hx hy
  · exact generalPathEmbed_adj_hub_left a b c d e f ha hb hc hd he hf x y hx hy
  · exact generalPathEmbed_adj_hub_hub a b c d e f ha hb hc hd he hf x y hx hy
  · exact generalPathEmbed_adj_hub_right a b c d e f ha hb hc hd he hf x y hx hy
  · exact generalPathEmbed_adj_right_left a b c d e f ha hb hc hd he hf x y hx hy
  · exact generalPathEmbed_adj_right_hub a b c d e f ha hb hc hd he hf x y hx hy
  · exact generalPathEmbed_adj_right_right a b c d e f ha hb hc hd he hf x y hx hy

lemma generalCoreEmbed_adj_zero_zero (a b c d e f : ℕ)
    (ha : 0<a) (hb : 0<b) (hc : 0<c) (hd : 0<d) (he : 0<e) (hf : 0<f)
    (x y : Fin (a+b+c+d+1)) (hxcase : x.val=0) (hycase : y.val=0) :
    (doubleSpider a b c d e f).Adj
      (generalCoreEmbed a b c d e f x) (generalCoreEmbed a b c d e f y) ↔
    (parentGraph (a+b+c+d) (fourParent a b c)).Adj x y := by
  have hx := x.isLt
  have hy := y.isLt
  dsimp [doubleSpider, parentGraph, generalCoreEmbed, generalCoreCode,
    doubleSpiderParent, fourParent]
  simp only [hxcase, hycase, ite_true, ite_false]
  split_ifs <;> omega

lemma generalCoreEmbed_adj_zero_arm (a b c d e f : ℕ)
    (ha : 0<a) (hb : 0<b) (hc : 0<c) (hd : 0<d) (he : 0<e) (hf : 0<f)
    (x y : Fin (a+b+c+d+1)) (hxcase : x.val=0) (hypos : 0<y.val) (hycase : y.val≤a+b+c) :
    (doubleSpider a b c d e f).Adj
      (generalCoreEmbed a b c d e f x) (generalCoreEmbed a b c d e f y) ↔
    (parentGraph (a+b+c+d) (fourParent a b c)).Adj x y := by
  have hx := x.isLt
  have hy := y.isLt
  dsimp [doubleSpider, parentGraph, generalCoreEmbed, generalCoreCode,
    doubleSpiderParent, fourParent]
  simp only [hxcase, show y.val≠0 from by omega, hycase, ite_true, ite_false]
  split_ifs <;> omega

lemma generalCoreEmbed_adj_zero_spine (a b c d e f : ℕ)
    (ha : 0<a) (hb : 0<b) (hc : 0<c) (hd : 0<d) (he : 0<e) (hf : 0<f)
    (x y : Fin (a+b+c+d+1)) (hxcase : x.val=0) (hycase : a+b+c<y.val) :
    (doubleSpider a b c d e f).Adj
      (generalCoreEmbed a b c d e f x) (generalCoreEmbed a b c d e f y) ↔
    (parentGraph (a+b+c+d) (fourParent a b c)).Adj x y := by
  have hx := x.isLt
  have hy := y.isLt
  dsimp [doubleSpider, parentGraph, generalCoreEmbed, generalCoreCode,
    doubleSpiderParent, fourParent]
  simp only [hxcase, show y.val≠0 from by omega, show ¬y.val≤a+b+c from by omega, ite_true, ite_false]
  split_ifs <;> omega

lemma generalCoreEmbed_adj_arm_zero (a b c d e f : ℕ)
    (ha : 0<a) (hb : 0<b) (hc : 0<c) (hd : 0<d) (he : 0<e) (hf : 0<f)
    (x y : Fin (a+b+c+d+1)) (hxpos : 0<x.val) (hxcase : x.val≤a+b+c) (hycase : y.val=0) :
    (doubleSpider a b c d e f).Adj
      (generalCoreEmbed a b c d e f x) (generalCoreEmbed a b c d e f y) ↔
    (parentGraph (a+b+c+d) (fourParent a b c)).Adj x y := by
  have hx := x.isLt
  have hy := y.isLt
  dsimp [doubleSpider, parentGraph, generalCoreEmbed, generalCoreCode,
    doubleSpiderParent, fourParent]
  simp only [show x.val≠0 from by omega, hxcase, hycase, ite_true, ite_false]
  split_ifs <;> omega

lemma generalCoreEmbed_adj_arm_arm (a b c d e f : ℕ)
    (ha : 0<a) (hb : 0<b) (hc : 0<c) (hd : 0<d) (he : 0<e) (hf : 0<f)
    (x y : Fin (a+b+c+d+1)) (hxpos : 0<x.val) (hxcase : x.val≤a+b+c) (hypos : 0<y.val) (hycase : y.val≤a+b+c) :
    (doubleSpider a b c d e f).Adj
      (generalCoreEmbed a b c d e f x) (generalCoreEmbed a b c d e f y) ↔
    (parentGraph (a+b+c+d) (fourParent a b c)).Adj x y := by
  have hx := x.isLt
  have hy := y.isLt
  dsimp [doubleSpider, parentGraph, generalCoreEmbed, generalCoreCode,
    doubleSpiderParent, fourParent]
  simp only [show x.val≠0 from by omega, hxcase, show y.val≠0 from by omega, hycase, ite_true, ite_false]
  split_ifs <;> omega

lemma generalCoreEmbed_adj_arm_spine (a b c d e f : ℕ)
    (ha : 0<a) (hb : 0<b) (hc : 0<c) (hd : 0<d) (he : 0<e) (hf : 0<f)
    (x y : Fin (a+b+c+d+1)) (hxpos : 0<x.val) (hxcase : x.val≤a+b+c) (hycase : a+b+c<y.val) :
    (doubleSpider a b c d e f).Adj
      (generalCoreEmbed a b c d e f x) (generalCoreEmbed a b c d e f y) ↔
    (parentGraph (a+b+c+d) (fourParent a b c)).Adj x y := by
  have hx := x.isLt
  have hy := y.isLt
  dsimp [doubleSpider, parentGraph, generalCoreEmbed, generalCoreCode,
    doubleSpiderParent, fourParent]
  simp only [show x.val≠0 from by omega, hxcase, show y.val≠0 from by omega, show ¬y.val≤a+b+c from by omega, ite_true, ite_false]
  split_ifs <;> omega

lemma generalCoreEmbed_adj_spine_zero (a b c d e f : ℕ)
    (ha : 0<a) (hb : 0<b) (hc : 0<c) (hd : 0<d) (he : 0<e) (hf : 0<f)
    (x y : Fin (a+b+c+d+1)) (hxcase : a+b+c<x.val) (hycase : y.val=0) :
    (doubleSpider a b c d e f).Adj
      (generalCoreEmbed a b c d e f x) (generalCoreEmbed a b c d e f y) ↔
    (parentGraph (a+b+c+d) (fourParent a b c)).Adj x y := by
  have hx := x.isLt
  have hy := y.isLt
  dsimp [doubleSpider, parentGraph, generalCoreEmbed, generalCoreCode,
    doubleSpiderParent, fourParent]
  simp only [show x.val≠0 from by omega, show ¬x.val≤a+b+c from by omega, hycase, ite_true, ite_false]
  split_ifs <;> omega

lemma generalCoreEmbed_adj_spine_arm (a b c d e f : ℕ)
    (ha : 0<a) (hb : 0<b) (hc : 0<c) (hd : 0<d) (he : 0<e) (hf : 0<f)
    (x y : Fin (a+b+c+d+1)) (hxcase : a+b+c<x.val) (hypos : 0<y.val) (hycase : y.val≤a+b+c) :
    (doubleSpider a b c d e f).Adj
      (generalCoreEmbed a b c d e f x) (generalCoreEmbed a b c d e f y) ↔
    (parentGraph (a+b+c+d) (fourParent a b c)).Adj x y := by
  have hx := x.isLt
  have hy := y.isLt
  dsimp [doubleSpider, parentGraph, generalCoreEmbed, generalCoreCode,
    doubleSpiderParent, fourParent]
  simp only [show x.val≠0 from by omega, show ¬x.val≤a+b+c from by omega, show y.val≠0 from by omega, hycase, ite_true, ite_false]
  split_ifs <;> omega

lemma generalCoreEmbed_adj_spine_spine (a b c d e f : ℕ)
    (ha : 0<a) (hb : 0<b) (hc : 0<c) (hd : 0<d) (he : 0<e) (hf : 0<f)
    (x y : Fin (a+b+c+d+1)) (hxcase : a+b+c<x.val) (hycase : a+b+c<y.val) :
    (doubleSpider a b c d e f).Adj
      (generalCoreEmbed a b c d e f x) (generalCoreEmbed a b c d e f y) ↔
    (parentGraph (a+b+c+d) (fourParent a b c)).Adj x y := by
  have hx := x.isLt
  have hy := y.isLt
  dsimp [doubleSpider, parentGraph, generalCoreEmbed, generalCoreCode,
    doubleSpiderParent, fourParent]
  simp only [show x.val≠0 from by omega, show ¬x.val≤a+b+c from by omega, show y.val≠0 from by omega, show ¬y.val≤a+b+c from by omega, ite_true, ite_false]
  split_ifs <;> omega

lemma generalCoreEmbed_adj (a b c d e f : ℕ)
    (ha : 0<a) (hb : 0<b) (hc : 0<c) (hd : 0<d) (he : 0<e) (hf : 0<f)
    (x y : Fin (a+b+c+d+1)) :
    (doubleSpider a b c d e f).Adj
      (generalCoreEmbed a b c d e f x) (generalCoreEmbed a b c d e f y) ↔
    (parentGraph (a+b+c+d) (fourParent a b c)).Adj x y := by
  rcases lt_trichotomy x.val 0 with hx | hx | hx
  · omega
  · rcases lt_trichotomy y.val 0 with hy | hy | hy
    · omega
    · exact generalCoreEmbed_adj_zero_zero a b c d e f ha hb hc hd he hf x y hx hy
    · by_cases hyle : y.val≤a+b+c
      · exact generalCoreEmbed_adj_zero_arm a b c d e f ha hb hc hd he hf x y hx hy hyle
      · exact generalCoreEmbed_adj_zero_spine a b c d e f ha hb hc hd he hf x y hx (by omega)
  · by_cases hxle : x.val≤a+b+c
    · rcases lt_trichotomy y.val 0 with hy | hy | hy
      · omega
      · exact generalCoreEmbed_adj_arm_zero a b c d e f ha hb hc hd he hf x y hx hxle hy
      · by_cases hyle : y.val≤a+b+c
        · exact generalCoreEmbed_adj_arm_arm a b c d e f ha hb hc hd he hf x y hx hxle hy hyle
        · exact generalCoreEmbed_adj_arm_spine a b c d e f ha hb hc hd he hf x y hx hxle (by omega)
    · rcases lt_trichotomy y.val 0 with hy | hy | hy
      · omega
      · exact generalCoreEmbed_adj_spine_zero a b c d e f ha hb hc hd he hf x y (by omega) hy
      · by_cases hyle : y.val≤a+b+c
        · exact generalCoreEmbed_adj_spine_arm a b c d e f ha hb hc hd he hf x y (by omega) hy hyle
        · exact generalCoreEmbed_adj_spine_spine a b c d e f ha hb hc hd he hf x y (by omega) (by omega)

lemma generalEmbed_cross (a b c d e f : ℕ)
    (ha : 0<a) (hb : 0<b) (hc : 0<c) (hd : 0<d) (he : 0<e) (hf : 0<f)
    (x : Fin (e+f+1)) (y : Fin (a+b+c+d+1))
    (hxy : (doubleSpider a b c d e f).Adj
      (generalPathEmbed a b c d e f x) (generalCoreEmbed a b c d e f y)) :
    x.val=e ∨ y.val=a+b+c+d := by
  have hx := x.isLt
  have hy := y.isLt
  dsimp [doubleSpider, parentGraph, generalPathEmbed, generalPathCode,
    generalCoreEmbed, generalCoreCode, doubleSpiderParent] at hxy
  split_ifs at hxy <;> omega

lemma generalEmbed_edges (a b c d e f : ℕ)
    (ha : 0<a) (hb : 0<b) (hc : 0<c) (hd : 0<d) (he : 0<e) (hf : 0<f)
    (u v : Fin (doubleSpiderEdges a b c d e f+1)) :
    (doubleSpider a b c d e f).Adj u v ↔
      (∃ x y, (lineGraph (e+f)).Adj x y ∧
        generalPathEmbed a b c d e f x=u ∧ generalPathEmbed a b c d e f y=v) ∨
      (∃ x y, (parentGraph (a+b+c+d) (fourParent a b c)).Adj x y ∧
        generalCoreEmbed a b c d e f x=u ∧ generalCoreEmbed a b c d e f y=v) := by
  let linkL : Fin (e+f+1) := ⟨e, by omega⟩
  let linkR : Fin (a+b+c+d+1) := ⟨a+b+c+d, by omega⟩
  have hlink : generalPathEmbed a b c d e f linkL =
      generalCoreEmbed a b c d e f linkR :=
    (generalEmbed_overlap a b c d e f hd _ _).2 ⟨rfl, rfl⟩
  have hcross (x : Fin (e+f+1)) (y : Fin (a+b+c+d+1))
      (hxy : (doubleSpider a b c d e f).Adj
        (generalPathEmbed a b c d e f x) (generalCoreEmbed a b c d e f y)) :
      (∃ x' y', (lineGraph (e+f)).Adj x' y' ∧
        generalPathEmbed a b c d e f x'=generalPathEmbed a b c d e f x ∧
        generalPathEmbed a b c d e f y'=generalCoreEmbed a b c d e f y) ∨
      (∃ x' y', (parentGraph (a+b+c+d) (fourParent a b c)).Adj x' y' ∧
        generalCoreEmbed a b c d e f x'=generalPathEmbed a b c d e f x ∧
        generalCoreEmbed a b c d e f y'=generalCoreEmbed a b c d e f y) := by
    rcases generalEmbed_cross a b c d e f ha hb hc hd he hf x y hxy with hx | hy
    · have hx' : x=linkL := Fin.ext hx
      subst x
      rw [hlink] at hxy
      exact Or.inr ⟨linkR,y,(generalCoreEmbed_adj a b c d e f ha hb hc hd he hf _ _).1 hxy,
        hlink.symm,rfl⟩
    · have hy' : y=linkR := Fin.ext hy
      subst y
      rw [← hlink] at hxy
      exact Or.inl ⟨x,linkL,(generalPathEmbed_adj a b c d e f ha hb hc hd he hf _ _).1 hxy,
        rfl,hlink⟩
  constructor
  · intro huv
    rcases generalEmbed_cover a b c d e f u with ⟨x,rfl⟩ | ⟨x,rfl⟩ <;>
      rcases generalEmbed_cover a b c d e f v with ⟨y,rfl⟩ | ⟨y,rfl⟩
    · exact Or.inl ⟨x,y,(generalPathEmbed_adj a b c d e f ha hb hc hd he hf _ _).1 huv,rfl,rfl⟩
    · exact hcross x y huv
    · rcases hcross y x huv.symm with ⟨x',y',hxy',hx',hy'⟩ | ⟨x',y',hxy',hx',hy'⟩
      · exact Or.inl ⟨y',x',hxy'.symm,hy',hx'⟩
      · exact Or.inr ⟨y',x',hxy'.symm,hy',hx'⟩
    · exact Or.inr ⟨x,y,(generalCoreEmbed_adj a b c d e f ha hb hc hd he hf _ _).1 huv,rfl,rfl⟩
  · rintro (⟨x,y,hxy,rfl,rfl⟩ | ⟨x,y,hxy,rfl,rfl⟩)
    · exact (generalPathEmbed_adj a b c d e f ha hb hc hd he hf _ _).2 hxy
    · exact (generalCoreEmbed_adj a b c d e f ha hb hc hd he hf _ _).2 hxy

/-- The general case follows by joining a prescribed-zero alpha path to a
four-legged spider whose distinguished leaf has label zero. -/
theorem doubleSpider_graceful_of_fourLeafZero (a b c d e f : ℕ)
    (ha : 0<a) (hb : 0<b) (hc : 0<c) (hd : 0<d) (he : 0<e) (hf : 0<f)
    (hex : e≠2 ∨ f≠2) (hfour : FourLeafZero a b c d) :
    IsGraceful (doubleSpider a b c d e f) := by
  obtain ⟨p,k,hp,hpzero⟩ := rosa_zero_alpha_path e f he hf hex
  obtain ⟨g,hg,hgzero⟩ := hfour
  let linkL : Fin (e+f+1) := ⟨e, by omega⟩
  let linkR : Fin (a+b+c+d+1) := ⟨a+b+c+d, by omega⟩
  apply isGraceful_amalgamation (doubleSpider a b c d e f)
    (lineGraph (e+f)) (parentGraph (a+b+c+d) (fourParent a b c))
    (generalPathEmbed a b c d e f) (generalCoreEmbed a b c d e f)
    (generalPathEmbed_injective a b c d e f) (generalCoreEmbed_injective a b c d e f)
    linkL linkR
    (fun x y => (generalEmbed_overlap a b c d e f hd x y).trans (by
      simp only [Fin.ext_iff]; rfl))
    (generalEmbed_cover a b c d e f)
    (generalEmbed_edges a b c d e f ha hb hc hd he hf)
    ?_ (fun i => p i.val) (fun i => g i.val) k
    hp.toLineAlpha (hg.isGracefulLabeling (fun j hj _ => fourParent_lt a b c j hj))
    (Or.inl hpzero) hgzero
  rw [doubleSpider_edgeCount, lineGraph_edgeCount,
    parentGraph_edgeCount _ _ (fun j hj _ => fourParent_lt a b c j hj)]
  unfold doubleSpiderEdges
  omega

end Bounty
end

/- ThreeCore -/
section
namespace Bounty
open Math15.Graceful

def NatParentAlpha (N : ℕ) (parent f : ℕ → ℕ) (k : ℕ) : Prop :=
  ∀ j, 0<j → j≤N → (f (parent j)≤k ∧ k<f j) ∨ (f j≤k ∧ k<f (parent j))

def appendParent (N : ℕ) (parent : ℕ → ℕ) (j : ℕ) : ℕ :=
  if j≤N then parent j else if j=N+1 then 0 else j-1

def appendParentLabel (N k m : ℕ) (f p : ℕ → ℕ) (j : ℕ) : ℕ :=
  if j≤N then shiftAboveCut k m (f j) else k+1+p (j-(N+1))

lemma appendParentLabel_old {N k m j : ℕ} (f p : ℕ → ℕ) (hj : j≤N) :
    appendParentLabel N k m f p j = shiftAboveCut k m (f j) := by simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, Bounty.subdivisionLabel_zero, Bounty.threeColor_zero, appendParentLabel,hj]
lemma appendParentLabel_new {N k m j : ℕ} (f p : ℕ → ℕ) (hj : N<j) :
    appendParentLabel N k m f p j = k+1+p (j-(N+1)) := by simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, Bounty.subdivisionLabel_zero, Bounty.threeColor_zero, appendParentLabel,show ¬j≤N by omega]

lemma appendParentLabel_injective {N k m : ℕ} {parent f p : ℕ → ℕ}
    (hf : NatParentCertificate N parent f) (hp : NatGracefulPath m p)
    {i j : ℕ} (hi : i≤N+m) (hj : j≤N+m)
    (heq : appendParentLabel N k m f p i = appendParentLabel N k m f p j) : i=j := by
  by_cases hi0 : i≤N <;> by_cases hj0 : j≤N
  · rw [appendParentLabel_old f p hi0,appendParentLabel_old f p hj0] at heq
    exact hf.1 i j hi0 hj0 (shiftAboveCut_injective k m heq)
  · rw [appendParentLabel_old f p hi0,appendParentLabel_new f p (by omega)] at heq
    have hpb := hp.2.1 (j-(N+1)) (by omega)
    have hzero := (shiftAboveCut_eq_translate_iff (k:=k) (m:=m) (x:=f i)
      (y:=1+p (j-(N+1))) (by omega)).1 (by simpa [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, Bounty.subdivisionLabel_zero, Bounty.threeColor_zero, Nat.add_assoc] using heq)
    omega
  · rw [appendParentLabel_new f p (by omega),appendParentLabel_old f p hj0] at heq
    have hpb := hp.2.1 (i-(N+1)) (by omega)
    have hzero := (shiftAboveCut_eq_translate_iff (k:=k) (m:=m) (x:=f j)
      (y:=1+p (i-(N+1))) (by omega)).1 (by simpa [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, Bounty.subdivisionLabel_zero, Bounty.threeColor_zero, Nat.add_assoc] using heq.symm)
    omega
  · rw [appendParentLabel_new f p (by omega),appendParentLabel_new f p (by omega)] at heq
    have he := hp.1 (i-(N+1)) (j-(N+1)) (by omega) (by omega) (by omega)
    omega

lemma appendParentLabel_bound {N k m : ℕ} {parent f p : ℕ → ℕ}
    (hf : NatParentCertificate N parent f) (hp : NatGracefulPath m p) (hk : k≤N)
    {i : ℕ} (hi : i≤N+m) : appendParentLabel N k m f p i≤N+m := by
  by_cases hi0 : i≤N
  · rw [appendParentLabel_old f p hi0]
    exact shiftAboveCut_le (hf.2.1 i hi0)
  · rw [appendParentLabel_new f p (by omega)]
    have h := hp.2.1 (i-(N+1)) (by omega)
    omega

lemma appendParentLabel_old_edge {N k m : ℕ} {parent f p : ℕ → ℕ}
    (hα : NatParentAlpha N parent f k) (hparent : ∀j,0<j→j≤N→parent j<j)
    {j : ℕ} (hj : 0<j) (hb : j≤N) :
    Nat.dist (appendParentLabel N k m f p (appendParent N parent j)) (appendParentLabel N k m f p j) =
      m+Nat.dist (f (parent j)) (f j) := by
  have he : appendParent N parent j=parent j := by simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, Bounty.subdivisionLabel_zero, Bounty.threeColor_zero, appendParent,hb]
  rw [he,appendParentLabel_old f p (by have := hparent j hj hb; omega),appendParentLabel_old f p hb]
  rcases hα j hj hb with h|h
  · exact shiftAboveCut_dist h.1 h.2
  · rw [Nat.dist_comm (shiftAboveCut _ _ _),Nat.dist_comm (f (parent j))]
    exact shiftAboveCut_dist h.1 h.2

lemma appendParentLabel_path_edge {N k m : ℕ} {parent f p : ℕ → ℕ} {j : ℕ}
    (hj : N+1<j) :
    Nat.dist (appendParentLabel N k m f p (appendParent N parent j)) (appendParentLabel N k m f p j) =
      Nat.dist (p (j-(N+1)-1)) (p (j-(N+1))) := by
  have he : appendParent N parent j=j-1 := by simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, Bounty.subdivisionLabel_zero, Bounty.threeColor_zero, appendParent,show ¬j≤N by omega,show j≠N+1 by omega]
  rw [he,appendParentLabel_new f p (by omega),appendParentLabel_new f p (by omega),translate_dist]
  congr 2
  omega

lemma appendParentLabel_join_edge {N k m : ℕ} {parent f p : ℕ → ℕ}
    (hf0 : f 0=0) (hp0 : p 0=m-k-1) (hm : k+1≤m) :
    Nat.dist (appendParentLabel N k m f p (appendParent N parent (N+1))) (appendParentLabel N k m f p (N+1))=m := by
  have he : appendParent N parent (N+1)=0 := by simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, Bounty.subdivisionLabel_zero, Bounty.threeColor_zero, appendParent]
  rw [he,appendParentLabel_old f p (by omega),appendParentLabel_new f p (by omega)]
  simp only [Nat.sub_self,hf0,hp0,shiftAboveCut,Nat.zero_le,ite_true,Nat.dist_zero_left]
  omega

lemma NatParentCertificate.edge_pos {N : ℕ} {parent f : ℕ → ℕ}
    (hf : NatParentCertificate N parent f) (hp : ∀j,0<j→j≤N→parent j<j)
    {j : ℕ} (hj : 0<j) (hb : j≤N) : 0<Nat.dist (f (parent j)) (f j) := by
  apply Nat.dist_pos_of_ne
  intro he
  have h := hf.1 (parent j) j (by have := hp j hj hb; omega) hb he
  have := hp j hj hb
  omega

theorem NatParentCertificate.appendAtZero {N k m : ℕ} {parent f p : ℕ → ℕ}
    (hf : NatParentCertificate N parent f) (hα : NatParentAlpha N parent f k)
    (hparent : ∀j,0<j→j≤N→parent j<j)
    (hp : NatGracefulPath m p) (hk : k≤N) (hf0 : f 0=0) (hp0 : p 0=m-k-1) (hm : k+1≤m) :
    NatParentCertificate (N+m) (appendParent N parent) (appendParentLabel N k m f p) := by
  refine ⟨?_, ?_, ?_⟩
  · exact fun i j hi hj heq => appendParentLabel_injective hf hp hi hj heq
  · exact fun i hi => appendParentLabel_bound hf hp hk hi
  · intro i j hi hib hj hjb heq
    rcases lt_trichotomy i (N + 1) with hi0 | rfl | hi0 <;>
      rcases lt_trichotomy j (N + 1) with hj0 | rfl | hj0
    · rw [appendParentLabel_old_edge hα hparent hi (by omega), appendParentLabel_old_edge hα hparent hj (by omega)] at heq
      exact hf.2.2 i j hi (by omega) hj (by omega) (by omega)
    · rw [appendParentLabel_old_edge hα hparent hi (by omega), appendParentLabel_join_edge hf0 hp0 hm] at heq
      have hpos := hf.edge_pos hparent hi (by omega)
      omega
    · rw [appendParentLabel_old_edge hα hparent hi (by omega), appendParentLabel_path_edge hj0] at heq
      have hb := hp.edge_lt (by omega : 0 < j - (N + 1)) (by omega)
      omega
    · rw [appendParentLabel_join_edge hf0 hp0 hm, appendParentLabel_old_edge hα hparent hj (by omega)] at heq
      have hpos := hf.edge_pos hparent hj (by omega)
      omega
    · rfl
    · rw [appendParentLabel_join_edge hf0 hp0 hm, appendParentLabel_path_edge hj0] at heq
      have hb := hp.edge_lt (by omega : 0 < j - (N + 1)) (by omega)
      omega
    · rw [appendParentLabel_path_edge hi0, appendParentLabel_old_edge hα hparent hj (by omega)] at heq
      have hb := hp.edge_lt (by omega : 0 < i - (N + 1)) (by omega)
      omega
    · rw [appendParentLabel_path_edge hi0, appendParentLabel_join_edge hf0 hp0 hm] at heq
      have hb := hp.edge_lt (by omega : 0 < i - (N + 1)) (by omega)
      omega
    · rw [appendParentLabel_path_edge hi0, appendParentLabel_path_edge hj0] at heq
      have he := hp.2.2 (i - (N + 1)) (j - (N + 1)) (by omega) (by omega)
        (by omega) (by omega) heq
      omega


theorem NatParentCertificate.exists_append_zero {N k m : ℕ} {parent f : ℕ → ℕ}
    (hf : NatParentCertificate N parent f) (hα : NatParentAlpha N parent f k)
    (hparent : ∀j,0<j→j≤N→parent j<j) (hk : k≤N) (hf0 : f 0=0) (hm : k+1≤m) :
    ∃g, NatParentCertificate (N+m) (appendParent N parent) g ∧ g 0=0 := by
  obtain ⟨p,hp,hp0⟩ := exists_graceful_path_endpoint (n:=m) (a:=m-k-1) (by omega)
  refine ⟨appendParentLabel N k m f p,hf.appendAtZero hα hparent hp hk hf0 hp0 hm,?_⟩
  simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, Bounty.subdivisionLabel_zero, Bounty.threeColor_zero, appendParentLabel,hf0,shiftAboveCut]

def twoArmIndex (a j : ℕ) : ℕ := if j≤a then a-j else j

def twoArmEdge (a j : ℕ) : ℕ := if j≤a then a-j+1 else j

lemma twoArmIndex_bound {a b j : ℕ} (hj : j≤a+b) : twoArmIndex a j≤a+b := by
  unfold twoArmIndex
  split_ifs <;> omega

lemma twoArmIndex_inj {a i j : ℕ} (h : twoArmIndex a i=twoArmIndex a j) : i=j := by
  unfold twoArmIndex at h
  split_ifs at h <;> omega

lemma twoArmEdge_bound {a b j : ℕ} (hj : 0<j) (hb : j≤a+b) :
    0<twoArmEdge a j ∧ twoArmEdge a j≤a+b := by
  unfold twoArmEdge
  split_ifs <;> omega

lemma twoArmEdge_inj {a i j : ℕ} (hi : 0 < i) (hj : 0<j)
    (h : twoArmEdge a i=twoArmEdge a j) : i=j := by
  unfold twoArmEdge at h
  split_ifs at h <;> omega

lemma twoArmIndex_edge {a b j : ℕ} (ha : 0<a) (hb : 0<b) (hj : 0<j) (hjb : j≤a+b) :
    (twoArmIndex a (threeParent a b j)=twoArmEdge a j-1 ∧ twoArmIndex a j=twoArmEdge a j) ∨
    (twoArmIndex a (threeParent a b j)=twoArmEdge a j ∧ twoArmIndex a j=twoArmEdge a j-1) := by
  unfold twoArmIndex twoArmEdge threeParent
  split_ifs <;> omega

lemma twoArm_dist {a b j : ℕ} (p : ℕ → ℕ) (ha : 0<a) (hb : 0<b) (hj : 0<j) (hjb : j≤a+b) :
    Nat.dist (p (twoArmIndex a (threeParent a b j))) (p (twoArmIndex a j)) =
      Nat.dist (p (twoArmEdge a j-1)) (p (twoArmEdge a j)) := by
  rcases twoArmIndex_edge ha hb hj hjb with ⟨h1,h2⟩|⟨h1,h2⟩
  · rw [h1,h2]
  · rw [h1,h2,Nat.dist_comm]

lemma NatAlphaPath.twoArm {a b k : ℕ} {p : ℕ → ℕ}
    (hp : NatAlphaPath (a+b+1) p k) (ha : 0<a) (hb : 0<b) :
    NatParentCertificate (a+b) (threeParent a b) (p ∘ twoArmIndex a) ∧
      NatParentAlpha (a+b) (threeParent a b) (p ∘ twoArmIndex a) k := by
  constructor
  · refine ⟨?_,?_,?_⟩
    · intro i j hi hj he
      exact twoArmIndex_inj (hp.1.1 _ _ (by have := twoArmIndex_bound hi; omega)
        (by have := twoArmIndex_bound hj; omega) he)
    · intro i hi
      have hh := hp.1.2.1 (twoArmIndex a i) (by have := twoArmIndex_bound hi; omega)
      exact Nat.le_of_lt_succ hh
    · intro i j hi hib hj hjb he
      simp only [Function.comp_apply] at he
      rw [twoArm_dist p ha hb hi hib,twoArm_dist p ha hb hj hjb] at he
      have hi' := twoArmEdge_bound hi hib
      have hj' := twoArmEdge_bound hj hjb
      exact twoArmEdge_inj hi hj (hp.1.2.2 _ _ hi'.1 (by omega) hj'.1 (by omega) he)
  · intro j hj hjb
    have hj' := twoArmEdge_bound hj hjb
    have hh := hp.2.2 _ hj'.1 (by omega)
    dsimp only [Function.comp_apply]
    rcases twoArmIndex_edge ha hb hj hjb with ⟨h1,h2⟩|⟨h1,h2⟩
    · rwa [h1,h2]
    · rw [h1,h2]
      tauto

lemma appendParent_three {a b j : ℕ} (hj : 0<j) :
    appendParent (a+b) (threeParent a b) j = threeParent a b j := by
  unfold appendParent threeParent
  split_ifs <;> omega

theorem ThreeZero.of_alpha_path {a b c k : ℕ} {p : ℕ → ℕ}
    (ha : 0<a) (hb : 0<b) (hp : NatAlphaPath (a+b+1) p k) (hp0 : p a=0) (hc : k+1≤c) :
    ThreeZero a b c := by
  have ht := hp.twoArm ha hb
  obtain ⟨g,hg,hg0⟩ := ht.1.exists_append_zero ht.2
    (fun j hj _ => threeParent_lt a b j hj) (by have := hp.2.1; omega)
    (by simpa [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, Bounty.subdivisionLabel_zero, Bounty.threeColor_zero, Function.comp_apply,twoArmIndex] using hp0) hc
  refine ⟨g,⟨hg.1,hg.2.1,?_⟩,hg0⟩
  intro i j hi hib hj hjb he
  exact hg.2.2 i j hi hib hj hjb (by simpa [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, Bounty.subdivisionLabel_zero, Bounty.threeColor_zero, appendParent_three hi,appendParent_three hj] using he)

lemma NatSpiderCertificate.toThreeZero {c : ℕ} {f : ℕ → ℕ}
    (hf : NatSpiderCertificate c f) (hf0 : f 0=0) : ThreeZero 2 2 c := by
  refine ⟨f,⟨?_,?_,?_⟩,hf0⟩
  · intro i j hi hj he
    exact hf.1 i j (by omega) (by omega) he
  · intro i hi
    have := hf.2.1 i (by omega)
    omega
  · intro i j hi hib hj hjb he
    exact hf.2.2 i j hi (by omega) hj (by omega) (by simpa [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, Bounty.subdivisionLabel_zero, Bounty.threeColor_zero, threeParent,spiderParent] using he)

def hub22Label_2 : Fin (2+5) → ℕ := ![0,3,1,6,2,5,4]
theorem hub22Label_2_checked : SpiderCertificate 2 hub22Label_2 ∧ hub22Label_2 ⟨0,by decide⟩=0 := by
  refine ⟨?_, by decide⟩
  exact @of_decide_eq_true _ (spiderCertificateDecidable 2 hub22Label_2) (by decide +kernel)
def hub22Label_3 : Fin (3+5) → ℕ := ![0,1,5,6,3,7,2,4]
theorem hub22Label_3_checked : SpiderCertificate 3 hub22Label_3 ∧ hub22Label_3 ⟨0,by decide⟩=0 := by
  refine ⟨?_, by decide⟩
  exact @of_decide_eq_true _ (spiderCertificateDecidable 3 hub22Label_3) (by decide +kernel)
def hub22Label_4 : Fin (4+5) → ℕ := ![0,3,4,7,5,8,2,6,1]
theorem hub22Label_4_checked : SpiderCertificate 4 hub22Label_4 ∧ hub22Label_4 ⟨0,by decide⟩=0 := by
  refine ⟨?_, by decide⟩
  exact @of_decide_eq_true _ (spiderCertificateDecidable 4 hub22Label_4) (by decide +kernel)
def hub22Label_5 : Fin (5+5) → ℕ := ![0,7,2,9,1,6,3,5,4,8]
theorem hub22Label_5_checked : SpiderCertificate 5 hub22Label_5 ∧ hub22Label_5 ⟨0,by decide⟩=0 := by
  refine ⟨?_, by decide⟩
  exact @of_decide_eq_true _ (spiderCertificateDecidable 5 hub22Label_5) (by decide +kernel)
def hub22Label_6 : Fin (6+5) → ℕ := ![0,10,1,8,4,5,7,6,3,9,2]
theorem hub22Label_6_checked : SpiderCertificate 6 hub22Label_6 ∧ hub22Label_6 ⟨0,by decide⟩=0 := by
  refine ⟨?_, by decide⟩
  exact @of_decide_eq_true _ (spiderCertificateDecidable 6 hub22Label_6) (by decide +kernel)
def hub22Label_7 : Fin (7+5) → ℕ := ![0,9,7,6,5,11,1,4,8,3,10,2]
theorem hub22Label_7_checked : SpiderCertificate 7 hub22Label_7 ∧ hub22Label_7 ⟨0,by decide⟩=0 := by
  refine ⟨?_, by decide⟩
  exact @of_decide_eq_true _ (spiderCertificateDecidable 7 hub22Label_7) (by decide +kernel)
def hub22Label_8 : Fin (8+5) → ℕ := ![0,10,7,6,8,12,1,5,4,9,2,11,3]
theorem hub22Label_8_checked : SpiderCertificate 8 hub22Label_8 ∧ hub22Label_8 ⟨0,by decide⟩=0 := by
  refine ⟨?_, by decide⟩
  exact @of_decide_eq_true _ (spiderCertificateDecidable 8 hub22Label_8) (by decide +kernel)
def hub22Label_9 : Fin (9+5) → ℕ := ![0,11,4,8,7,13,1,10,5,3,9,6,2,12]
theorem hub22Label_9_checked : SpiderCertificate 9 hub22Label_9 ∧ hub22Label_9 ⟨0,by decide⟩=0 := by
  refine ⟨?_, by decide⟩
  exact @of_decide_eq_true _ (spiderCertificateDecidable 9 hub22Label_9) (by decide +kernel)
def hub22Label_10 : Fin (10+5) → ℕ := ![0,8,9,12,5,14,1,6,4,10,7,11,2,13,3]
theorem hub22Label_10_checked : SpiderCertificate 10 hub22Label_10 ∧ hub22Label_10 ⟨0,by decide⟩=0 := by
  refine ⟨?_, by decide⟩
  exact @of_decide_eq_true _ (spiderCertificateDecidable 10 hub22Label_10) (by decide +kernel)
theorem hub22Label_5_alpha : AlphaSpiderCertificate 5 hub22Label_5 4 := by
  exact @of_decide_eq_true _ (alphaSpiderCertificateDecidable 5 hub22Label_5 4) (by decide +kernel)

theorem threeZero22 (c : ℕ) (hc : 2≤c) : ThreeZero 2 2 c := by
  by_cases hsmall : c≤10
  · interval_cases c
    · exact hub22Label_2_checked.1.toNat.toThreeZero (by simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, Bounty.subdivisionLabel_zero, Bounty.threeColor_zero, extendSpiderLabel,hub22Label_2])
    · exact hub22Label_3_checked.1.toNat.toThreeZero (by simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, Bounty.subdivisionLabel_zero, Bounty.threeColor_zero, extendSpiderLabel,hub22Label_3])
    · exact hub22Label_4_checked.1.toNat.toThreeZero (by simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, Bounty.subdivisionLabel_zero, Bounty.threeColor_zero, extendSpiderLabel,hub22Label_4])
    · exact hub22Label_5_checked.1.toNat.toThreeZero (by simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, Bounty.subdivisionLabel_zero, Bounty.threeColor_zero, extendSpiderLabel,hub22Label_5])
    · exact hub22Label_6_checked.1.toNat.toThreeZero (by simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, Bounty.subdivisionLabel_zero, Bounty.threeColor_zero, extendSpiderLabel,hub22Label_6])
    · exact hub22Label_7_checked.1.toNat.toThreeZero (by simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, Bounty.subdivisionLabel_zero, Bounty.threeColor_zero, extendSpiderLabel,hub22Label_7])
    · exact hub22Label_8_checked.1.toNat.toThreeZero (by simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, Bounty.subdivisionLabel_zero, Bounty.threeColor_zero, extendSpiderLabel,hub22Label_8])
    · exact hub22Label_9_checked.1.toNat.toThreeZero (by simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, Bounty.subdivisionLabel_zero, Bounty.threeColor_zero, extendSpiderLabel,hub22Label_9])
    · exact hub22Label_10_checked.1.toNat.toThreeZero (by simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, Bounty.subdivisionLabel_zero, Bounty.threeColor_zero, extendSpiderLabel,hub22Label_10])
  · have hm : max (4+1-extendSpiderLabel hub22Label_5 (5+4)) (extendSpiderLabel hub22Label_5 (5+4)-4)≤c-5 := by
      norm_num [extendSpiderLabel,hub22Label_5]
      omega
    obtain ⟨g,hg,hg0⟩ := hub22Label_5_checked.1.toNat.exists_append (m:=c-5) (by decide)
      hub22Label_5_alpha.toNat (by decide) hm
    have he : 5+(c-5)=c := by omega
    rw [he] at hg
    exact hg.toThreeZero (hg0 0 (by decide) (by simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, Bounty.subdivisionLabel_zero, Bounty.threeColor_zero, extendSpiderLabel,hub22Label_5]))

end Bounty
end

/- ThreePermute -/
section
namespace Bounty

theorem NatParentCertificate.reindex {N M : ℕ} {parent newParent f q : ℕ → ℕ}
    (hf : NatParentCertificate N parent f) (hsize : N=M)
    (hb : ∀ j, j≤M → q j≤N)
    (hi : ∀ i j, i≤M → j≤M → q i=q j → i=j)
    (hp : ∀ j, 0<j → j≤M → 0<q j)
    (hpar : ∀ j, 0<j → j≤M → q (newParent j)=parent (q j)) :
    NatParentCertificate M newParent (fun j => f (q j)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j hib hjb heq
    exact hi i j hib hjb (hf.1 _ _ (hb i hib) (hb j hjb) heq)
  · intro j hj
    change f (q j) ≤ M
    have := hf.2.1 _ (hb j hj)
    omega
  · intro i j hip hib hjp hjb heq
    dsimp only at heq
    rw [hpar i hip hib, hpar j hjp hjb] at heq
    exact hi i j hib hjb (hf.2.2 _ _ (hp i hip hib) (hb i hib) (hp j hjp hjb) (hb j hjb) heq)

def swapFirst (a b j : ℕ) : ℕ :=
  if j=0 then 0 else if j≤b then a+j else if j≤a+b then j-b else j

def swapLast (a b c j : ℕ) : ℕ :=
  if j≤a then j else if j≤a+c then b+j else j-c

lemma swapFirst_bound {a b c j : ℕ} (hj : j≤b+a+c) : swapFirst a b j≤a+b+c := by
  unfold swapFirst
  split_ifs <;> omega

lemma swapFirst_pos {a b j : ℕ} (hj : 0<j) : 0<swapFirst a b j := by
  unfold swapFirst
  split_ifs <;> omega

lemma swapFirst_inj {a b i j : ℕ} (heq : swapFirst a b i=swapFirst a b j) : i=j := by
  unfold swapFirst at heq
  split_ifs at heq <;> omega

lemma swapFirst_parent {a b c j : ℕ} (ha : 0<a) (hb : 0<b)
    (hj : 0<j) (hjb : j≤b+a+c) :
    swapFirst a b (threeParent b a j)=threeParent a b (swapFirst a b j) := by
  by_cases h1 : j≤b
  · by_cases h2 : j=1
    · subst j; simp [threeParent, swapFirst, show ¬1=0 by omega]; omega
    · have h3 : j≠b+1 := by omega
      have h4 : j≠b+a+1 := by omega
      simp (discharger := omega) only [threeParent, swapFirst, ite_eq_left, ite_eq_right, ite_true, ite_false, or_true, true_or]
      omega
  · by_cases h2 : j≤a+b
    · by_cases h3 : j=b+1
      · subst j
        simp (discharger := omega) only [threeParent, swapFirst, ite_eq_left, ite_eq_right, ite_true, ite_false, or_true, true_or]
      · simp (discharger := omega) only [threeParent, swapFirst, ite_eq_left, ite_eq_right, ite_true, ite_false, or_true, true_or]
        omega
    · by_cases h3 : j=b+a+1
      · subst j
        simp (discharger := omega) only [threeParent, swapFirst, ite_eq_left, ite_eq_right, ite_true, ite_false, or_true, true_or]
      · simp (discharger := omega) only [threeParent, swapFirst, ite_eq_left, ite_eq_right, ite_true, ite_false, or_true, true_or]

lemma swapLast_bound {a b c j : ℕ} (hj : j≤a+c+b) : swapLast a b c j≤a+b+c := by
  unfold swapLast
  split_ifs <;> omega

lemma swapLast_pos {a b c j : ℕ} (hj : 0<j) : 0<swapLast a b c j := by
  unfold swapLast
  split_ifs <;> omega

lemma swapLast_inj {a b c i j : ℕ} (hi : i≤a+c+b) (hj : j≤a+c+b)
    (heq : swapLast a b c i=swapLast a b c j) : i=j := by
  unfold swapLast at heq
  split_ifs at heq <;> omega

lemma swapLast_parent {a b c j : ℕ} (ha : 0<a) (hb : 0<b) (hc : 0<c)
    (hj : 0<j) (hjb : j≤a+c+b) :
    swapLast a b c (threeParent a c j)=threeParent a b (swapLast a b c j) := by
  by_cases h1 : j≤a
  · by_cases h2 : j=1
    · subst j
      simp (discharger := omega) only [threeParent, swapLast, ite_eq_left, ite_eq_right, ite_true, ite_false, or_true, true_or]
    · simp (discharger := omega) only [threeParent, swapLast, ite_eq_left, ite_eq_right, ite_true, ite_false, or_true, true_or]
  · by_cases h2 : j≤a+c
    · by_cases h3 : j=a+1
      · subst j
        simp (discharger := omega) only [threeParent, swapLast, ite_eq_left, ite_eq_right, ite_true, ite_false, or_true, true_or]
      · simp (discharger := omega) only [threeParent, swapLast, ite_eq_left, ite_eq_right, ite_true, ite_false, or_true, true_or]
        omega
    · by_cases h3 : j=a+c+1
      · subst j
        simp (discharger := omega) only [threeParent, swapLast, ite_eq_left, ite_eq_right, ite_true, ite_false, or_true, true_or]
      · simp (discharger := omega) only [threeParent, swapLast, ite_eq_left, ite_eq_right, ite_true, ite_false, or_true, true_or]
        omega

theorem ThreeZero.swap12 {a b c : ℕ} (h : ThreeZero a b c) (ha : 0<a) (hb : 0<b) :
    ThreeZero b a c := by
  obtain ⟨f,hf,hzero⟩ := h
  refine ⟨fun j => f (swapFirst a b j), hf.reindex (by omega)
    (fun j hj => swapFirst_bound hj)
    (fun i j _ _ heq => swapFirst_inj heq)
    (fun j hj _ => swapFirst_pos hj)
    (fun j hj hjb => swapFirst_parent ha hb hj hjb), ?_⟩
  simpa [swapFirst] using hzero

theorem ThreeZero.swap23 {a b c : ℕ} (h : ThreeZero a b c) (ha : 0<a) (hb : 0<b) (hc : 0<c) :
    ThreeZero a c b := by
  obtain ⟨f,hf,hzero⟩ := h
  refine ⟨fun j => f (swapLast a b c j), hf.reindex (by omega)
    (fun j hj => swapLast_bound hj)
    (fun i j hi hj heq => swapLast_inj hi hj heq)
    (fun j hj _ => swapLast_pos hj)
    (fun j hj hjb => swapLast_parent ha hb hc hj hjb), ?_⟩
  simpa [swapLast] using hzero

end Bounty
end

/- ThreeComplete -/
section
namespace Bounty

theorem threeZero_symmetric (a : ℕ) (ha : 0<a) : ThreeZero a a a := by
  induction a using Nat.strong_induction_on with
  | h a ih =>
    by_cases hodd : a%2=1
    · obtain ⟨p,k,hp,hp0⟩ := rosa_zero_alpha_path a a ha ha (by left; omega)
      apply ThreeZero.of_alpha_path ha ha hp hp0
      have hh := hp.cut_bound_odd_zero (by omega : a<a+a+1) hodd hp0
      omega
    · have hhalf : 0<a/2 := by omega
      have hlt : a/2<a := by omega
      have hh := (ih (a/2) hlt hhalf).subdivide hhalf hhalf hhalf
      have he : 2*(a/2)=a := by omega
      simpa only [he] using hh

theorem threeZero_sorted (a b c : ℕ) (ha : 0<a) (hb : 0<b) (hc : 0<c)
    (hab : a≤b) (hbc : b≤c) : ThreeZero a b c := by
  by_cases he : a=b ∧ b=c
  · obtain ⟨rfl,rfl⟩ := he
    exact threeZero_symmetric _ (by omega)
  by_cases hex : a=2 ∧ b=2
  · obtain ⟨rfl,rfl⟩ := hex
    exact threeZero22 c hbc
  obtain ⟨p,k,hp,hp0⟩ := rosa_zero_alpha_path a b ha hb (by omega)
  apply ThreeZero.of_alpha_path ha hb hp hp0
  have hh := hp.cut_bound
  omega

theorem threeZero (a b c : ℕ) (ha : 0<a) (hb : 0<b) (hc : 0<c) : ThreeZero a b c := by
  by_cases hab : a≤b
  · by_cases hbc : b≤c
    · exact threeZero_sorted a b c ha hb hc hab hbc
    · by_cases hac : a≤c
      · exact (threeZero_sorted a c b ha hc hb hac (by omega)).swap23 ha hc hb
      · exact ((threeZero_sorted c a b hc ha hb (by omega) hab).swap12 hc ha).swap23 ha hc hb
  · by_cases hac : a≤c
    · exact (threeZero_sorted b a c hb ha hc (by omega) hac).swap12 hb ha
    · by_cases hbc : b≤c
      · exact ((threeZero_sorted b c a hb hc ha hbc (by omega)).swap23 hb hc ha).swap12 hb ha
      · exact (((threeZero_sorted c b a hc hb ha (by omega) (by omega)).swap12 hc hb).swap23 hb hc ha).swap12 hb ha

end Bounty
end

/- Walecki -/
section
namespace Bounty

def cutEndpointPath (d j : ℕ) : ℕ :=
  if j%2=0 then (d-j)/2 else d-(d-j)/2

lemma cutEndpointPath_bound {d j : ℕ} (hj : j≤d) : cutEndpointPath d j≤d := by
  unfold cutEndpointPath
  split_ifs <;> omega

lemma cutEndpointPath_inj {d i j : ℕ} (hi : i≤d) (hj : j≤d)
    (heq : cutEndpointPath d i=cutEndpointPath d j) : i=j := by
  unfold cutEndpointPath at heq
  split_ifs at heq <;> omega

lemma cutEndpointPath_diff {d j : ℕ} (hj : 0<j) (hjb : j≤d) :
    Nat.dist (cutEndpointPath d (j-1)) (cutEndpointPath d j)=j := by
  unfold cutEndpointPath
  split_ifs <;> simp only [Nat.dist] <;> omega

lemma cutEndpointPath_cross {d j : ℕ} (hj : 0<j) (hjb : j≤d) :
    (cutEndpointPath d (j-1)≤d/2 ∧ d/2<cutEndpointPath d j) ∨
      (cutEndpointPath d j≤d/2 ∧ d/2<cutEndpointPath d (j-1)) := by
  unfold cutEndpointPath
  split_ifs <;> omega

theorem cutEndpointPath_alpha {d : ℕ} (hd : 0<d) :
    NatAlphaPath (d+1) (cutEndpointPath d) (d/2) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro i j hi hj heq
    exact cutEndpointPath_inj (by omega) (by omega) heq
  · intro j hj
    have := cutEndpointPath_bound (d:=d) (j:=j) (by omega)
    omega
  · intro i j hi hib hj hjb heq
    rw [cutEndpointPath_diff hi (by omega), cutEndpointPath_diff hj (by omega)] at heq
    exact heq
  · omega
  · intro j hj hjb
    exact cutEndpointPath_cross hj (by omega)

lemma cutEndpointPath_zero (d : ℕ) : cutEndpointPath d 0=d/2 := by
  unfold cutEndpointPath
  split_ifs <;> omega

lemma cutEndpointPath_end (d : ℕ) : cutEndpointPath d d=0 ∨ cutEndpointPath d d=d := by
  unfold cutEndpointPath
  split_ifs <;> simp

theorem exists_cut_endpoint_alpha_path {d : ℕ} (hd : 0<d) :
    ∃ p k, NatAlphaPath (d+1) p k ∧ p 0=k ∧ (p d=0 ∨ p d=d) :=
  ⟨cutEndpointPath d, d/2, cutEndpointPath_alpha hd, cutEndpointPath_zero d, cutEndpointPath_end d⟩

end Bounty
end

/- FourSpider -/
section
namespace Bounty
open Math15.Graceful

def graftPathLabel (N k : ℕ) (f p : ℕ → ℕ) (j : ℕ) : ℕ :=
  if j≤N then k+f j else shiftAboveCut k N (p (j-N))

lemma graftPathLabel_old {N k j : ℕ} (f p : ℕ → ℕ) (hj : j≤N) :
    graftPathLabel N k f p j = k+f j := by simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, Bounty.subdivisionLabel_zero, Bounty.threeColor_zero, graftPathLabel,hj]
lemma graftPathLabel_new {N k j : ℕ} (f p : ℕ → ℕ) (hj : N<j) :
    graftPathLabel N k f p j = shiftAboveCut k N (p (j-N)) := by
  simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, Bounty.subdivisionLabel_zero, Bounty.threeColor_zero, graftPathLabel,show ¬j≤N by omega]

lemma graftPathLabel_injective {N d k : ℕ} {parent f p : ℕ → ℕ}
    (hf : NatParentCertificate N parent f) (hp : NatGracefulPath (d+1) p) (hp0 : p 0=k)
    {i j : ℕ} (hi : i≤N+d) (hj : j≤N+d)
    (he : graftPathLabel N k f p i=graftPathLabel N k f p j) : i=j := by
  by_cases hi0 : i≤N <;> by_cases hj0 : j≤N
  · rw [graftPathLabel_old f p hi0,graftPathLabel_old f p hj0] at he
    exact hf.1 i j hi0 hj0 (by omega)
  · rw [graftPathLabel_old f p hi0,graftPathLabel_new f p (by omega)] at he
    have hx := (shiftAboveCut_eq_translate_iff (hf.2.1 i hi0)).1 he.symm
    have hx' := hp.1 (j-N) 0 (by omega) (by omega) (hx.1.trans hp0.symm)
    omega
  · rw [graftPathLabel_new f p (by omega),graftPathLabel_old f p hj0] at he
    have hx := (shiftAboveCut_eq_translate_iff (hf.2.1 j hj0)).1 he
    have hx' := hp.1 (i-N) 0 (by omega) (by omega) (hx.1.trans hp0.symm)
    omega
  · rw [graftPathLabel_new f p (by omega),graftPathLabel_new f p (by omega)] at he
    have hx := hp.1 (i-N) (j-N) (by omega) (by omega) (shiftAboveCut_injective k N he)
    omega

lemma graftPathLabel_bound {N d k : ℕ} {parent f p : ℕ → ℕ}
    (hf : NatParentCertificate N parent f) (hp : NatGracefulPath (d+1) p) (hk : k≤d)
    {j : ℕ} (hj : j≤N+d) : graftPathLabel N k f p j≤N+d := by
  by_cases hj0 : j≤N
  · rw [graftPathLabel_old f p hj0]
    have := hf.2.1 j hj0
    omega
  · rw [graftPathLabel_new f p (by omega)]
    have hb := hp.2.1 (j-N) (by omega)
    have := shiftAboveCut_le (k:=k) (m:=N) (show p (j-N)≤d by omega)
    omega

lemma graftPathLabel_old_edge {N k : ℕ} {parent f p : ℕ → ℕ}
    (hparent : ∀j,0<j→j≤N→parent j<j) {j : ℕ} (hj : 0<j) (hb : j≤N) :
    Nat.dist (graftPathLabel N k f p (appendParent N parent j)) (graftPathLabel N k f p j) =
      Nat.dist (f (parent j)) (f j) := by
  have he : appendParent N parent j=parent j := by simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, Bounty.subdivisionLabel_zero, Bounty.threeColor_zero, appendParent,hb]
  rw [he,graftPathLabel_old f p (by have := hparent j hj hb; omega),graftPathLabel_old f p hb,translate_dist]

lemma graftPathLabel_new_edge {N d k : ℕ} {parent f p : ℕ → ℕ}
    (hp : NatAlphaPath (d+1) p k) (hp0 : p 0=k) (hf0 : f 0=0)
    {j : ℕ} (hj : N<j) (hb : j≤N+d) :
    Nat.dist (graftPathLabel N k f p (appendParent N parent j)) (graftPathLabel N k f p j) =
      N+Nat.dist (p (j-N-1)) (p (j-N)) := by
  have hpidx : graftPathLabel N k f p (appendParent N parent j)=shiftAboveCut k N (p (j-N-1)) := by
    by_cases he : j=N+1
    · subst j
      simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, Bounty.subdivisionLabel_zero, Bounty.threeColor_zero, appendParent,graftPathLabel,hf0,hp0,shiftAboveCut]
    · have hl : N<j-1 := by omega
      have he' : appendParent N parent j=j-1 := by simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, Bounty.subdivisionLabel_zero, Bounty.threeColor_zero, appendParent,show ¬j≤N by omega,he]
      rw [he',graftPathLabel_new f p hl]
      congr 2
      omega
  rw [hpidx,graftPathLabel_new f p hj]
  rcases hp.2.2 (j-N) (by omega) (by omega) with h|h
  · exact shiftAboveCut_dist h.1 h.2
  · rw [Nat.dist_comm (shiftAboveCut _ _ _),Nat.dist_comm (p (j-N-1))]
    exact shiftAboveCut_dist h.1 h.2

lemma NatParentCertificate.edge_le {N : ℕ} {parent f : ℕ → ℕ}
    (hf : NatParentCertificate N parent f) (hparent : ∀j,0<j→j≤N→parent j<j)
    {j : ℕ} (hj : 0<j) (hb : j≤N) : Nat.dist (f (parent j)) (f j)≤N := by
  have h1 := hf.2.1 j hb
  have h2 := hf.2.1 (parent j) (by have := hparent j hj hb; omega)
  unfold Nat.dist
  omega

lemma NatGracefulPath.edge_pos {n : ℕ} {p : ℕ → ℕ} (hp : NatGracefulPath n p)
    {j : ℕ} (hj : 0<j) (hb : j<n) : 0<Nat.dist (p (j-1)) (p j) := by
  apply Nat.dist_pos_of_ne
  intro he
  have hh := hp.1 (j-1) j (by omega) hb he
  omega

theorem NatParentCertificate.graftPath {N d k : ℕ} {parent f p : ℕ → ℕ}
    (hf : NatParentCertificate N parent f) (hp : NatAlphaPath (d+1) p k)
    (hparent : ∀j,0<j→j≤N→parent j<j) (hp0 : p 0=k) (hf0 : f 0=0) :
    NatParentCertificate (N+d) (appendParent N parent) (graftPathLabel N k f p) := by
  refine ⟨fun i j hi hj he => graftPathLabel_injective hf hp.1 hp0 hi hj he,
    fun j hj => graftPathLabel_bound hf hp.1 (by have := hp.2.1; omega) hj,?_⟩
  intro i j hi hib hj hjb he
  by_cases hi0 : i≤N <;> by_cases hj0 : j≤N
  · rw [graftPathLabel_old_edge hparent hi hi0,graftPathLabel_old_edge hparent hj hj0] at he
    exact hf.2.2 i j hi hi0 hj hj0 he
  · rw [graftPathLabel_old_edge hparent hi hi0,graftPathLabel_new_edge hp hp0 hf0 (by omega) hjb] at he
    have h1 := hf.edge_le hparent hi hi0
    have h2 := hp.1.edge_pos (by omega : 0<j-N) (by omega)
    omega
  · rw [graftPathLabel_new_edge hp hp0 hf0 (by omega) hib,graftPathLabel_old_edge hparent hj hj0] at he
    have h1 := hf.edge_le hparent hj hj0
    have h2 := hp.1.edge_pos (by omega : 0 < i-N) (by omega)
    omega
  · rw [graftPathLabel_new_edge hp hp0 hf0 (by omega) hib,graftPathLabel_new_edge hp hp0 hf0 (by omega) hjb] at he
    have hh := hp.1.2.2 (i-N) (j-N) (by omega) (by omega) (by omega) (by omega) (by omega)
    omega

theorem NatParentCertificate.complement {N : ℕ} {parent f : ℕ → ℕ}
    (hf : NatParentCertificate N parent f) (hparent : ∀j,0<j→j≤N→parent j<j) :
    NatParentCertificate N parent (fun j => N-f j) := by
  refine ⟨?_,?_,?_⟩
  · intro i j hi hj he
    dsimp only at he
    have h1 := hf.2.1 i hi
    have h2 := hf.2.1 j hj
    exact hf.1 i j hi hj (by omega)
  · intro i hi
    dsimp only
    omega
  · intro i j hi hib hj hjb he
    have h1 := hf.2.1 i hib
    have h2 := hf.2.1 j hjb
    have h3 := hf.2.1 (parent i) (by have := hparent i hi hib; omega)
    have h4 := hf.2.1 (parent j) (by have := hparent j hj hjb; omega)
    apply hf.2.2 i j hi hib hj hjb
    dsimp only at he
    unfold Nat.dist at he ⊢
    omega

lemma appendParent_four (a b c : ℕ) : appendParent (a+b+c) (threeParent a b)=fourParent a b c := by
  funext j
  unfold appendParent threeParent fourParent
  split_ifs <;> omega

theorem fourLeafZero (a b c d : ℕ) (ha : 0<a) (hb : 0<b) (hc : 0<c) (hd : 0<d) :
    FourLeafZero a b c d := by
  obtain ⟨f,hf,hf0⟩ := threeZero a b c ha hb hc
  obtain ⟨p,k,hp,hp0,hpd⟩ := exists_cut_endpoint_alpha_path hd
  have hlabel := hf.graftPath hp (fun j hj _ => threeParent_lt a b j hj) hp0 hf0
  rw [appendParent_four] at hlabel
  rcases hpd with hpd|hpd
  · refine ⟨graftPathLabel (a+b+c) k f p,hlabel,?_⟩
    rw [graftPathLabel_new f p (by omega)]
    have he : a+b+c+d-(a+b+c)=d := by omega
    rw [he,hpd]
    simp [Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, Bounty.subdivisionLabel_zero, Bounty.threeColor_zero, shiftAboveCut]
  · refine ⟨fun j => a+b+c+d-graftPathLabel (a+b+c) k f p j,
      hlabel.complement (fun j hj _ => fourParent_lt a b c j hj),?_⟩
    dsimp only
    rw [graftPathLabel_new f p (by omega)]
    have he : a+b+c+d-(a+b+c)=d := by omega
    rw [he,hpd]
    have hk : ¬d≤k := by have := hp.2.1; omega
    simp only [shiftAboveCut,ite_eq_right hk]
    omega

end Bounty
end

/- Structure -/
section
namespace Math15.Graceful

/-- At a vertex of degree at most two, two distinct known neighbors exhaust the neighborhood. -/
theorem neighbors_eq_of_degree_le_two {n : ℕ} (G : SimpleGraph (Fin n))
    {x a b : Fin n} (hdeg : degree G x ≤ 2) (hab : a ≠ b)
    (hxa : G.Adj x a) (hxb : G.Adj x b) :
    ∀ c, G.Adj x c → c = a ∨ c = b := by
  classical
  have hsub : ({a, b} : Finset (Fin n)) ⊆ Finset.univ.filter (G.Adj x) := by
    intro c hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with hc | hc
    · simpa [hc] using hxa
    · simpa [hc] using hxb
  have heq : ({a, b} : Finset (Fin n)) = Finset.univ.filter (G.Adj x) := by
    apply Finset.eq_of_subset_of_card_le hsub
    simpa [degree, Finset.card_pair hab] using hdeg
  intro c hc
  have hmem : c ∈ Finset.univ.filter (G.Adj x) := by simpa using hc
  rw [← heq] at hmem
  simpa using hmem

/-- An internal vertex of a path whose degree is at most two has no neighbor outside the path. -/
theorem internal_path_neighbor_mem {n : ℕ} (G : SimpleGraph (Fin n))
    {u v : Fin n} {p : G.Walk u v} (hp : p.IsPath) {i : ℕ}
    (hlo : 0 < i) (hhi : i < p.length) (hdeg : degree G (p.getVert i) ≤ 2)
    {w : Fin n} (hw : G.Adj (p.getVert i) w) : w ∈ p.support := by
  have hne : p.getVert (i - 1) ≠ p.getVert (i + 1) := by
    intro heq
    have := hp.getVert_injOn (by simp; omega) (by simp; omega) heq
    omega
  have hprev : G.Adj (p.getVert i) (p.getVert (i - 1)) := by
    have h := (p.adj_getVert_succ (i := i - 1) (by omega)).symm
    simpa [Nat.sub_add_cancel hlo] using h
  have hnext := p.adj_getVert_succ hhi
  rcases neighbors_eq_of_degree_le_two G hdeg hne hprev hnext w hw with h | h
  · apply SimpleGraph.Walk.mem_support_iff_exists_getVert.mpr
    exact ⟨i - 1, h.symm, by omega⟩
  · apply SimpleGraph.Walk.mem_support_iff_exists_getVert.mpr
    exact ⟨i + 1, h.symm, by omega⟩

/-- Every edge leaving the central branch-to-branch path is attached at a branch vertex. -/
theorem branch43_central_path_no_internal_attachment {n : ℕ} (G : SimpleGraph (Fin n))
    {u v : Fin n} (hbranch : Branch43 G u v) {p : G.Walk u v} (hp : p.IsPath)
    {x : Fin n} (hx : x ∈ p.support) (hxu : x ≠ u) (hxv : x ≠ v)
    {y : Fin n} (hxy : G.Adj x y) : y ∈ p.support := by
  obtain ⟨i, hi, hib⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hx
  have hlo : 0 < i := by
    by_contra h
    have : i = 0 := by omega
    subst i
    simp only [SimpleGraph.Walk.getVert_zero] at hi
    exact hxu hi.symm
  have hhi : i < p.length := by
    by_contra h
    have : i = p.length := by omega
    subst i
    simp only [SimpleGraph.Walk.getVert_length] at hi
    exact hxv hi.symm
  have hdeg := hbranch.2.2.2 x hxu hxv
  rw [← hi] at hdeg hxy
  exact internal_path_neighbor_mem G hp hlo hhi hdeg hxy

noncomputable def offPathNeighbors {n : ℕ} {G : SimpleGraph (Fin n)}
    {u v : Fin n} (p : G.Walk u v) (x : Fin n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun w => G.Adj x w ∧ w ∉ p.support)

/-- Exactly one neighbor at each endpoint lies on a nonempty path in a tree. -/
theorem offPathNeighbors_card_start {n : ℕ} (G : SimpleGraph (Fin n))
    (hG : G.IsAcyclic) {u v : Fin n} (hne : u ≠ v)
    {p : G.Walk u v} (hp : p.IsPath) :
    (offPathNeighbors p u).card = degree G u - 1 := by
  classical
  have hnil : ¬p.Nil := fun h => hne (hp.nil_iff_eq.mp h)
  have hsnd : p.snd ∈ p.support := List.mem_of_mem_tail (p.snd_mem_tail_support hnil)
  have hsndadj : G.Adj u p.snd := p.adj_snd hnil
  have hfilter : offPathNeighbors p u =
      (Finset.univ.filter (G.Adj u)).erase p.snd := by
    ext x
    simp only [offPathNeighbors, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_erase]
    constructor
    · rintro ⟨hadj, hnmem⟩
      refine ⟨?_, hadj⟩
      intro heq
      exact hnmem (heq ▸ hsnd)
    · rintro ⟨hxne, hadj⟩
      exact ⟨hadj, fun hmem => hxne (hG.eq_snd_of_adj_start hp hadj hmem)⟩
  rw [hfilter, Finset.card_erase_of_mem (by simpa using hsndadj)]
  rfl

theorem branch43_offPathNeighbors_card {n : ℕ} (G : SimpleGraph (Fin n))
    (hG : G.IsTree) {u v : Fin n} (hbranch : Branch43 G u v)
    {p : G.Walk u v} (hp : p.IsPath) :
    (offPathNeighbors p u).card = 3 ∧ (offPathNeighbors p v).card = 2 := by
  constructor
  · rw [offPathNeighbors_card_start G hG.isAcyclic hbranch.1 hp, hbranch.2.1]
  · have heq : offPathNeighbors p v = offPathNeighbors p.reverse v := by
      classical
      ext x
      simp [offPathNeighbors]
    rw [heq, offPathNeighbors_card_start G hG.isAcyclic hbranch.1.symm hp.reverse,
      hbranch.2.2.1]

/-- Deleting the two branch vertices leaves an acyclic graph of maximum degree at most two. -/
theorem branch43_delete_branches {n : ℕ} (G : SimpleGraph (Fin n))
    (hG : G.IsTree) {u v : Fin n} (hbranch : Branch43 G u v) :
    let S : Set (Fin n) := {x | x ≠ u ∧ x ≠ v}
    (G.induce S).IsAcyclic ∧
      ∀ x : S, (by classical exact (G.induce S).degree x) ≤ 2 := by
  classical
  dsimp
  refine ⟨hG.isAcyclic.induce _, ?_⟩
  intro x
  have hle := (SimpleGraph.Embedding.comap (Function.Embedding.subtype _) G).toCopy.degree_le x
  apply le_trans hle
  change G.degree x.val ≤ 2
  rw [← degree_eq_graph_degree]
  exact hbranch.2.2.2 x.val x.property.1 x.property.2

end Math15.Graceful
end

/- PathComponents -/
section
namespace Math15.Graceful

section Generic
variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem neighbors_eq_of_graph_degree_le_two {x a b : V} (hdeg : G.degree x ≤ 2)
    (hab : a ≠ b) (hxa : G.Adj x a) (hxb : G.Adj x b) :
    ∀ c, G.Adj x c → c = a ∨ c = b := by
  classical
  have hsub : ({a, b} : Finset V) ⊆ G.neighborFinset x := by
    intro c hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with hc | hc
    · simpa [hc] using hxa
    · simpa [hc] using hxb
  have heq : ({a, b} : Finset V) = G.neighborFinset x := by
    apply Finset.eq_of_subset_of_card_le hsub
    simpa [Finset.card_pair hab] using hdeg
  intro c hc
  have hmem : c ∈ G.neighborFinset x := by simpa using hc
  rw [← heq] at hmem
  simpa using hmem

private theorem generic_internal_neighbor {u v : V} {p : G.Walk u v}
    (hp : p.IsPath) {i : ℕ} (hlo : 0 < i) (hhi : i < p.length)
    (hdeg : G.degree (p.getVert i) ≤ 2) {w : V} (hw : G.Adj (p.getVert i) w) :
    w ∈ p.support := by
  have hne : p.getVert (i - 1) ≠ p.getVert (i + 1) := by
    intro heq
    have := hp.getVert_injOn (by simp; omega) (by simp; omega) heq
    omega
  have hprev : G.Adj (p.getVert i) (p.getVert (i - 1)) := by
    have h := (p.adj_getVert_succ (i := i - 1) (by omega)).symm
    simpa [Nat.sub_add_cancel hlo] using h
  have hnext := p.adj_getVert_succ hhi
  rcases neighbors_eq_of_graph_degree_le_two G hdeg hne hprev hnext w hw with h | h
  · apply SimpleGraph.Walk.mem_support_iff_exists_getVert.mpr
    exact ⟨i - 1, h.symm, by omega⟩
  · apply SimpleGraph.Walk.mem_support_iff_exists_getVert.mpr
    exact ⟨i + 1, h.symm, by omega⟩

/-- Every finite connected graph of maximum degree two has a spanning path. -/
theorem exists_spanning_path_of_degree_le_two (hconn : G.Connected)
    (hdeg : ∀ x, G.degree x ≤ 2) :
    ∃ (u v : V) (p : G.Walk u v), p.IsPath ∧ ∀ x, x ∈ p.support := by
  classical
  let : Nonempty V := hconn.nonempty
  obtain ⟨u, v, p, hp, hmax⟩ :=
    SimpleGraph.Walk.exists_isPath_forall_isPath_length_le_length G
  refine ⟨u, v, p, hp, ?_⟩
  have hclosed {x y : V} (hx : x ∈ p.support) (hxy : G.Adj x y) : y ∈ p.support := by
    by_cases hxu : x = u
    · subst x
      by_contra hy
      have hnew : (p.cons hxy.symm).IsPath := hp.cons hy
      have := hmax y v (p.cons hxy.symm) hnew
      simp only [SimpleGraph.Walk.length_cons] at this
      omega
    by_cases hxv : x = v
    · subst x
      by_contra hy
      have hnew : (p.concat hxy).IsPath := hp.concat hy hxy
      have := hmax u y (p.concat hxy) hnew
      simp only [SimpleGraph.Walk.length_concat] at this
      omega
    obtain ⟨i, hi, hib⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hx
    have hlo : 0 < i := by
      by_contra h
      have : i = 0 := by omega
      subst i
      simp only [SimpleGraph.Walk.getVert_zero] at hi
      exact hxu hi.symm
    have hhi : i < p.length := by
      by_contra h
      have : i = p.length := by omega
      subst i
      simp only [SimpleGraph.Walk.getVert_length] at hi
      exact hxv hi.symm
    rw [← hi] at hxy
    exact generic_internal_neighbor G hp hlo hhi (hdeg _) hxy
  have hwalk {a b : V} (q : G.Walk a b) : a ∈ p.support → b ∈ p.support := by
    induction q with
    | nil => exact id
    | cons hadj q ih => exact fun ha => ih (hclosed ha hadj)
  intro x
  obtain ⟨q⟩ := hconn.preconnected u x
  exact hwalk q p.start_mem_support

/-- A vertex of degree at most one occurring in a path must be an endpoint. -/
theorem degree_le_one_path_endpoint {u v x : V} {p : G.Walk u v}
    (hp : p.IsPath) (hx : x ∈ p.support) (hdeg : G.degree x ≤ 1) : x = u ∨ x = v := by
  classical
  obtain ⟨i, hi, hib⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hx
  by_cases hzero : i = 0
  · left
    simpa [hzero] using hi.symm
  by_cases hend : i = p.length
  · right
    simpa [hend] using hi.symm
  have hlo : 0 < i := by omega
  have hhi : i < p.length := by omega
  have hne : p.getVert (i - 1) ≠ p.getVert (i + 1) := by
    intro heq
    have := hp.getVert_injOn (by simp; omega) (by simp; omega) heq
    omega
  have hprev : G.Adj x (p.getVert (i - 1)) := by
    rw [← hi]
    have h := (p.adj_getVert_succ (i := i - 1) (by omega)).symm
    simpa [Nat.sub_add_cancel hlo] using h
  have hnext : G.Adj x (p.getVert (i + 1)) := by rw [← hi]; exact p.adj_getVert_succ hhi
  have hsub : ({p.getVert (i - 1), p.getVert (i + 1)} : Finset V) ⊆ G.neighborFinset x := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with hy | hy
    · simpa [hy] using hprev
    · simpa [hy] using hnext
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_pair hne, G.card_neighborFinset_eq_degree] at hcard
  omega

/-- A finite connected graph of maximum degree two has a spanning path starting
at any prescribed vertex of degree at most one. -/
theorem exists_spanning_path_from_leaf (hconn : G.Connected)
    (hdeg : ∀ x, G.degree x ≤ 2) (x : V) (hx : G.degree x ≤ 1) :
    ∃ (y : V) (p : G.Walk x y), p.IsPath ∧ ∀ z, z ∈ p.support := by
  obtain ⟨u, v, p, hp, hspan⟩ := exists_spanning_path_of_degree_le_two G hconn hdeg
  rcases degree_le_one_path_endpoint G hp (hspan x) hx with hxu | hxv
  · subst u
    exact ⟨v, p, hp, hspan⟩
  · subst v
    exact ⟨u, p.reverse, hp.reverse, by simpa using hspan⟩

/-- A finite tree of maximum degree two is a path graph. -/
theorem exists_pathGraph_iso_of_degree_le_two (hG : G.IsTree)
    (hdeg : ∀ x, G.degree x ≤ 2) :
    ∃ k : ℕ, Nonempty (SimpleGraph.pathGraph (k + 1) ≃g G) := by
  classical
  obtain ⟨u, v, p, hp, hspanning⟩ := exists_spanning_path_of_degree_le_two G hG.connected hdeg
  have hspan : p.toSubgraph.IsSpanning := fun x => p.mem_verts_toSubgraph.mpr (hspanning x)
  let e : SimpleGraph.pathGraph (p.length + 1) ≃g p.toSubgraph.spanningCoe :=
    hp.pathGraphIsoToSubgraph.trans
    (p.toSubgraph.spanningCoeEquivCoeOfSpanning hspan).symm
  have hconnected : p.toSubgraph.spanningCoe.Connected :=
    e.connected_iff.mp (SimpleGraph.pathGraph_connected _)
  have heq : p.toSubgraph.spanningCoe = G := by
    apply le_antisymm p.toSubgraph.spanningCoe_le
    exact (SimpleGraph.isTree_iff_minimal_connected.mp hG).2 hconnected
      p.toSubgraph.spanningCoe_le
  let e2 : p.toSubgraph.spanningCoe ≃g G :=
    { toEquiv := Equiv.refl V
      map_rel_iff' := by
        intro a b
        change G.Adj a b ↔ p.toSubgraph.spanningCoe.Adj a b
        rw [heq] }
  exact ⟨p.length, ⟨e.trans e2⟩⟩

/-- A finite tree of maximum degree two is a path with any prescribed leaf at index zero. -/
theorem exists_pathGraph_iso_from_leaf (hG : G.IsTree)
    (hdeg : ∀ x, G.degree x ≤ 2) (x : V) (hx : G.degree x ≤ 1) :
    ∃ (k : ℕ) (e : SimpleGraph.pathGraph (k + 1) ≃g G), e 0 = x := by
  classical
  obtain ⟨y, p, hp, hspanning⟩ := exists_spanning_path_from_leaf G hG.connected hdeg x hx
  have hspan : p.toSubgraph.IsSpanning := fun z => p.mem_verts_toSubgraph.mpr (hspanning z)
  let e : SimpleGraph.pathGraph (p.length + 1) ≃g p.toSubgraph.spanningCoe :=
    hp.pathGraphIsoToSubgraph.trans
      (p.toSubgraph.spanningCoeEquivCoeOfSpanning hspan).symm
  have hconnected : p.toSubgraph.spanningCoe.Connected :=
    e.connected_iff.mp (SimpleGraph.pathGraph_connected _)
  have heq : p.toSubgraph.spanningCoe = G := by
    apply le_antisymm p.toSubgraph.spanningCoe_le
    exact (SimpleGraph.isTree_iff_minimal_connected.mp hG).2 hconnected
      p.toSubgraph.spanningCoe_le
  let e2 : p.toSubgraph.spanningCoe ≃g G :=
    { toEquiv := Equiv.refl V
      map_rel_iff' := by
        intro a b
        change G.Adj a b ↔ p.toSubgraph.spanningCoe.Adj a b
        rw [heq] }
  refine ⟨p.length, e.trans e2, ?_⟩
  change p.support[0] = x
  rw [p.support_getElem_eq_getVert, p.getVert_zero]

/-- Every connected component of a finite acyclic graph of maximum degree two is a path. -/
theorem component_pathGraph_iso_of_degree_le_two (hG : G.IsAcyclic)
    (hdeg : ∀ x, G.degree x ≤ 2) (c : G.ConnectedComponent) :
    ∃ k : ℕ, Nonempty (SimpleGraph.pathGraph (k + 1) ≃g c.toSimpleGraph) := by
  classical
  apply exists_pathGraph_iso_of_degree_le_two _ (hG.isTree_connectedComponent c)
  intro x
  let e : c.toSimpleGraph ↪g G :=
    SimpleGraph.Embedding.comap (Function.Embedding.subtype c.supp) G
  have hle := e.toCopy.degree_le x
  exact hle.trans (hdeg x.val)

end Generic

end Math15.Graceful
end

/- Decomposition -/
section
namespace Math15.Graceful

/-- Removing a vertex; the inequality predicate keeps endpoint proof obligations simple. -/
def deleteVertexGraph {V : Type*} (G : SimpleGraph V) (u : V) :
    SimpleGraph {x : V // x ≠ u} := G.induce {x | x ≠ u}

/-- The component reached by an edge leaving a deleted vertex. -/
def neighborComponent {V : Type*} (G : SimpleGraph V) (u : V)
    (x : G.neighborSet u) : (deleteVertexGraph G u).ConnectedComponent :=
  (deleteVertexGraph G u).connectedComponentMk ⟨x.val, x.property.ne'⟩

theorem neighborComponent_injective {V : Type*} (G : SimpleGraph V) (u : V)
    (hG : G.IsAcyclic) : Function.Injective (neighborComponent G u) := by
  intro x y hxy
  have hreach := SimpleGraph.ConnectedComponent.exact hxy
  obtain ⟨q, hq⟩ := hreach.exists_isPath
  let e : deleteVertexGraph G u ↪g G := SimpleGraph.Embedding.induce _
  let p : G.Walk x.val y.val := q.map e.toHom
  have hp : p.IsPath := SimpleGraph.Walk.IsPath.map e.injective hq
  have hunot : u ∉ p.support := by
    change u ∉ (q.map e.toHom).support
    rw [SimpleGraph.Walk.support_map]
    intro hu
    obtain ⟨z, _, hz⟩ := List.mem_map.mp hu
    exact z.property hz
  have hp' : (p.cons x.property).IsPath := hp.cons hunot
  have heq := hG.eq_snd_of_adj_start hp' y.property (p.cons x.property).end_mem_support
  apply Subtype.ext
  apply Eq.symm
  exact heq.trans (SimpleGraph.Walk.snd_cons p x.property)

theorem neighborComponent_surjective {V : Type*} (G : SimpleGraph V) (u : V)
    (hG : G.Connected) : Function.Surjective (neighborComponent G u) := by
  intro c
  obtain ⟨x, hxc⟩ := c.nonempty_supp
  obtain ⟨p, hp⟩ := hG.exists_isPath u x.val
  have hnil : ¬p.Nil := fun h => x.property (hp.nil_iff_eq.mp h).symm
  have htail : u ∉ p.tail.support := by
    rw [← p.cons_tail_eq hnil] at hp
    exact (SimpleGraph.Walk.cons_isPath_iff _ _).mp hp |>.2
  have hsupp : ∀ z ∈ p.tail.support, z ∈ {z | z ≠ u} := by
    intro z hz hzu
    subst z
    exact htail hz
  let q' := p.tail.induce {z | z ≠ u} hsupp
  refine ⟨⟨p.snd, p.adj_snd hnil⟩, ?_⟩
  have heq := SimpleGraph.ConnectedComponent.sound q'.reachable
  exact heq.trans ((c.mem_supp_iff x).mp hxc)

noncomputable def neighborComponentEquiv {V : Type*} (G : SimpleGraph V) (u : V)
    (hG : G.IsTree) : G.neighborSet u ≃ (deleteVertexGraph G u).ConnectedComponent :=
  Equiv.ofBijective (neighborComponent G u)
    ⟨neighborComponent_injective G u hG.isAcyclic, neighborComponent_surjective G u hG.connected⟩

theorem card_components_deleteVertex {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (hG : G.IsTree) :
    Nat.card (deleteVertexGraph G u).ConnectedComponent = G.degree u := by
  rw [← Nat.card_congr (neighborComponentEquiv G u hG), Nat.card_eq_fintype_card]
  exact G.card_neighborSet_eq_degree u

/-- A neighbor of a deleted vertex becomes a leaf when its original degree is at most two. -/
theorem degree_deleteVertex_le_one {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V)
    [DecidableRel (deleteVertexGraph G u).Adj]
    (x : G.neighborSet u) (hdeg : G.degree x.val ≤ 2) :
    (deleteVertexGraph G u).degree ⟨x.val, x.property.ne'⟩ ≤ 1 := by
  classical
  rw [← SimpleGraph.card_neighborSet_eq_degree, Fintype.card_le_one_iff_subsingleton]
  constructor
  intro y z
  apply Subtype.ext
  apply Subtype.ext
  have hxy : G.Adj x.val y.val.val := y.property
  have hxz : G.Adj x.val z.val.val := z.property
  have hne : u ≠ y.val.val := y.val.property.symm
  have heq := neighbors_eq_of_graph_degree_le_two G hdeg hne x.property.symm hxy z.val.val hxz
  rcases heq with hzu | hzy
  · exact (z.val.property hzu).elim
  · exact hzy.symm

/-- Each component of `G-u` not containing the other branch is an arm,
with its unique neighbor of `u` at index zero. -/
theorem noncentral_component_is_arm {n : ℕ} (G : SimpleGraph (Fin n))
    (hG : G.IsTree) {u v : Fin n} (hne : u ≠ v)
    (hdegrees : ∀ w, w ≠ u → w ≠ v → degree G w ≤ 2)
    (c : (deleteVertexGraph G u).ConnectedComponent)
    (hcentral : c ≠ (deleteVertexGraph G u).connectedComponentMk ⟨v, hne.symm⟩)
    (x : G.neighborSet u) (hxcomp : neighborComponent G u x = c) :
    ∃ (k : ℕ) (e : SimpleGraph.pathGraph (k + 1) ≃g c.toSimpleGraph),
      (e 0).val.val = x.val := by
  classical
  let ec : c.toSimpleGraph ↪g deleteVertexGraph G u := SimpleGraph.Embedding.induce c.supp
  let eG : deleteVertexGraph G u ↪g G := SimpleGraph.Embedding.induce _
  have htree : c.toSimpleGraph.IsTree :=
    (hG.isAcyclic.induce _).isTree_connectedComponent c
  have hrest (z : c) : degree G z.val.val ≤ 2 := by
    apply hdegrees _ z.val.property
    intro hz
    apply hcentral
    have hmem := (c.mem_supp_iff z.val).mp z.property
    have heq : z.val = (⟨v, hne.symm⟩ : {a : Fin n // a ≠ u}) := Subtype.ext hz
    rw [heq] at hmem
    exact hmem.symm
  have hdeg (z : c) : c.toSimpleGraph.degree z ≤ 2 := by
    apply (ec.toCopy.degree_le z).trans
    apply (eG.toCopy.degree_le z.val).trans
    change G.degree z.val.val ≤ 2
    rw [← degree_eq_graph_degree]
    exact hrest z
  let entry : c := ⟨⟨x.val, x.property.ne'⟩, by
    apply (c.mem_supp_iff _).mpr
    exact hxcomp⟩
  have hentry : c.toSimpleGraph.degree entry ≤ 1 := by
    apply (ec.toCopy.degree_le entry).trans
    have hxdeg : G.degree x.val ≤ 2 := by
      rw [← degree_eq_graph_degree]
      exact hrest entry
    exact degree_deleteVertex_le_one G u x hxdeg
  obtain ⟨k, e, he⟩ := exists_pathGraph_iso_from_leaf c.toSimpleGraph htree hdeg entry hentry
  exact ⟨k, e, congrArg (fun z : c => z.val.val) he⟩

/-- All components left after deleting both branch vertices are ordinary path graphs. -/
theorem branch43_deleted_components_are_paths {n : ℕ} (G : SimpleGraph (Fin n))
    (hG : G.IsTree) {u v : Fin n} (hbranch : Branch43 G u v) :
    let S : Set (Fin n) := {x | x ≠ u ∧ x ≠ v}
    ∀ c : (G.induce S).ConnectedComponent,
      ∃ k : ℕ, Nonempty (SimpleGraph.pathGraph (k + 1) ≃g c.toSimpleGraph) := by
  classical
  intro S c
  obtain ⟨hacyclic, hdegree⟩ := branch43_delete_branches G hG hbranch
  exact component_pathGraph_iso_of_degree_le_two (G.induce S) hacyclic hdegree c

end Math15.Graceful
end

/- ArmPartition -/
section
namespace Math15.Graceful

section Partition
variable {V : Type*} (G : SimpleGraph V) {u v : V} (hne : u ≠ v)

/-- The arms attached at `u`, excluding the component leading toward `v`. -/
def InArm (x : V) : Prop := ∃ hx : x ≠ u,
  (deleteVertexGraph G u).connectedComponentMk ⟨x, hx⟩ ≠
    (deleteVertexGraph G u).connectedComponentMk ⟨v, hne.symm⟩

/-- After deleting the initial endpoint, all remaining vertices of a path lie
in the component of its final endpoint. -/
theorem path_mem_deleted_component {p : G.Walk u v} (hp : p.IsPath)
    {x : V} (hx : x ∈ p.support) (hxu : x ≠ u) :
    (deleteVertexGraph G u).connectedComponentMk ⟨x, hxu⟩ =
      (deleteVertexGraph G u).connectedComponentMk ⟨v, hne.symm⟩ := by
  classical
  have hnil : ¬p.Nil := fun h => hne (hp.nil_iff_eq.mp h)
  have htail : u ∉ p.tail.support := by
    rw [← p.cons_tail_eq hnil] at hp
    exact (SimpleGraph.Walk.cons_isPath_iff _ _).mp hp |>.2
  have hxtail : x ∈ p.tail.support := by
    rw [← p.cons_tail_eq hnil, SimpleGraph.Walk.support_cons, List.mem_cons] at hx
    exact hx.resolve_left hxu
  let q := p.tail.dropUntil x hxtail
  have hsupp : ∀ z ∈ q.support, z ∈ {z | z ≠ u} := by
    intro z hz hzu
    subst z
    exact htail (p.tail.support_dropUntil_subset_support hxtail hz)
  exact SimpleGraph.ConnectedComponent.sound (q.induce {z | z ≠ u} hsupp).reachable

theorem not_inArm_of_mem_path {p : G.Walk u v} (hp : p.IsPath)
    {x : V} (hx : x ∈ p.support) : ¬ InArm G hne x := by
  rintro ⟨hxu, hcomp⟩
  exact hcomp (path_mem_deleted_component G hne hp hx hxu)

/-- Every neighbor of a path endpoint lying outside the path belongs to an arm there. -/
theorem adjacent_not_mem_path_inArm (hG : G.IsAcyclic) {p : G.Walk u v} (hp : p.IsPath)
    {x : V} (hadj : G.Adj u x) (hx : x ∉ p.support) : InArm G hne x := by
  have hnil : ¬p.Nil := fun h => hne (hp.nil_iff_eq.mp h)
  have hsndadj := p.adj_snd hnil
  have hsndmem : p.snd ∈ p.support := List.mem_of_mem_tail (p.snd_mem_tail_support hnil)
  refine ⟨hadj.ne', ?_⟩
  intro hcomp
  have hsndcomp := path_mem_deleted_component G hne hp hsndmem hsndadj.ne'
  have heq : neighborComponent G u ⟨x, hadj⟩ = neighborComponent G u ⟨p.snd, hsndadj⟩ :=
    hcomp.trans hsndcomp.symm
  have hx_eq := congrArg Subtype.val (neighborComponent_injective G u hG heq)
  have hx_eq' : x = p.snd := hx_eq
  exact hx (hx_eq'.symm ▸ hsndmem)

/-- An arm can only meet the rest of the tree at its designated branch vertex. -/
theorem adjacent_inArm_or_root {x y : V} (hx : InArm G hne x)
    (hxy : G.Adj x y) : y = u ∨ InArm G hne y := by
  rcases hx with ⟨hxu, hxcomp⟩
  by_cases hyu : y = u
  · exact Or.inl hyu
  right
  refine ⟨hyu, ?_⟩
  intro hycomp
  have hadj : (deleteVertexGraph G u).Adj ⟨x, hxu⟩ ⟨y, hyu⟩ := hxy
  exact hxcomp ((SimpleGraph.ConnectedComponent.sound hadj.reachable).trans hycomp)

/-- The arm families at opposite endpoints are disjoint. -/
theorem inArm_not_reverse (hG : G.Connected) {x : V} (hx : InArm G hne x) :
    ¬ InArm G hne.symm x := by
  rcases hx with ⟨hxu, hxcomp⟩
  obtain ⟨q, hq⟩ := hG.exists_isPath u x
  have hvnot : v ∉ q.support := by
    intro hv
    have heq := path_mem_deleted_component G hxu.symm hq hv hne.symm
    exact hxcomp heq.symm
  have hsupp : ∀ z ∈ q.support, z ∈ {z | z ≠ v} := by
    intro z hz hzv
    subst z
    exact hvnot hz
  have heq := SimpleGraph.ConnectedComponent.sound (q.induce {z | z ≠ v} hsupp).reachable
  rintro ⟨hxv, hxcomp'⟩
  exact hxcomp' heq.symm

/-- The noncentral components, one for each arm at `u`. -/
def ArmComponents :=
  {c : (deleteVertexGraph G u).ConnectedComponent //
    c ≠ (deleteVertexGraph G u).connectedComponentMk ⟨v, hne.symm⟩}

theorem armComponents_card [Fintype V] [DecidableRel G.Adj] (hG : G.IsTree) :
    Nat.card (ArmComponents G hne) = G.degree u - 1 := by
  classical
  let : Fintype (deleteVertexGraph G u).ConnectedComponent := Fintype.ofFinite _
  unfold ArmComponents
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
  have hc := card_components_deleteVertex G u hG
  rw [Nat.card_eq_fintype_card] at hc
  simp [hc]

end Partition

theorem branch43_arm_components_card {n : ℕ} (G : SimpleGraph (Fin n))
    (hG : G.IsTree) {u v : Fin n} (hbranch : Branch43 G u v) :
    Nat.card (ArmComponents G hbranch.1) = 3 ∧
      Nat.card (ArmComponents G hbranch.1.symm) = 2 := by
  classical
  constructor
  · rw [armComponents_card G hbranch.1 hG, ← degree_eq_graph_degree, hbranch.2.1]
  · rw [armComponents_card G hbranch.1.symm hG, ← degree_eq_graph_degree, hbranch.2.2.1]

/-- The central path and the two collections of arms cover all vertices. -/
theorem branch43_spine_and_arms_cover {n : ℕ} (G : SimpleGraph (Fin n))
    (hG : G.IsTree) {u v : Fin n} (hbranch : Branch43 G u v)
    {p : G.Walk u v} (hp : p.IsPath) (x : Fin n) :
    x ∈ p.support ∨ InArm G hbranch.1 x ∨ InArm G hbranch.1.symm x := by
  let S : Fin n → Prop := fun x =>
    x ∈ p.support ∨ InArm G hbranch.1 x ∨ InArm G hbranch.1.symm x
  have hclosed {a b : Fin n} (ha : S a) (hab : G.Adj a b) : S b := by
    rcases ha with ha | ha | ha
    · by_cases hbu : b ∈ p.support
      · exact Or.inl hbu
      by_cases hau : a = u
      · subst a
        exact Or.inr (Or.inl (adjacent_not_mem_path_inArm G hbranch.1 hG.isAcyclic hp hab hbu))
      by_cases hav : a = v
      · subst a
        have hrev : b ∉ p.reverse.support := by simpa using hbu
        exact Or.inr (Or.inr (adjacent_not_mem_path_inArm G hbranch.1.symm hG.isAcyclic hp.reverse hab hrev))
      exact (hbu (branch43_central_path_no_internal_attachment G hbranch hp ha hau hav hab)).elim
    · rcases adjacent_inArm_or_root G hbranch.1 ha hab with rfl | hb
      · exact Or.inl p.start_mem_support
      · exact Or.inr (Or.inl hb)
    · rcases adjacent_inArm_or_root G hbranch.1.symm ha hab with rfl | hb
      · exact Or.inl p.end_mem_support
      · exact Or.inr (Or.inr hb)
  have hwalk {a b : Fin n} (q : G.Walk a b) : S a → S b := by
    induction q with
    | nil => exact id
    | cons hadj q ih => exact fun ha => ih (hclosed ha hadj)
  obtain ⟨q⟩ := hG.connected u x
  exact hwalk q (Or.inl p.start_mem_support)

end Math15.Graceful
end

/- InducedPath -/
section
namespace Math15.Graceful

/-- Every connected subgraph of an acyclic graph is induced on its vertices. -/
theorem connected_subgraph_isInduced {V : Type*} (G : SimpleGraph V)
    (hG : G.IsAcyclic) (H : G.Subgraph) (hH : H.coe.Connected) : H.IsInduced := by
  intro x hx y hy hxy
  obtain ⟨q, hq⟩ := hH.exists_isPath ⟨x, hx⟩ ⟨y, hy⟩
  have hmap : (q.map H.hom).IsPath := SimpleGraph.Walk.IsPath.map H.hom_injective hq
  have hsingle : hxy.toWalk.IsPath := SimpleGraph.Walk.IsPath.of_adj hxy
  have heq := hG.subsingleton_path x y |>.elim ⟨q.map H.hom, hmap⟩ ⟨hxy.toWalk, hsingle⟩
  have hlength := congrArg (fun p : G.Path x y => p.val.length) heq
  have hlen : q.length = 1 :=
    (SimpleGraph.Walk.length_map H.hom q).symm.trans (hlength.trans hxy.length_toWalk)
  exact SimpleGraph.Walk.adj_of_length_eq_one hlen

/-- A path in an acyclic graph is an induced path. -/
theorem path_toSubgraph_isInduced {V : Type*} (G : SimpleGraph V)
    (hG : G.IsAcyclic) {u v : V} (p : G.Walk u v) : p.toSubgraph.IsInduced :=
  connected_subgraph_isInduced G hG p.toSubgraph p.toSubgraph_connected.coe

end Math15.Graceful
end

/- ArmModel -/
section
namespace Math15.Graceful

abbrev ArmModelVertex {A B : Type*} (d : ℕ) (a : A → ℕ) (b : B → ℕ) :=
  Fin (d+1) ⊕ ((i : A) × Fin (a i)) ⊕ ((j : B) × Fin (b j))

def armModelAdj {A B : Type*} (d : ℕ) (a : A → ℕ) (b : B → ℕ) :
    ArmModelVertex d a b → ArmModelVertex d a b → Prop
  | .inl x, .inl y => x.val+1=y.val ∨ y.val+1=x.val
  | .inl x, .inr (.inl y) => x.val=0 ∧ y.2.val=0
  | .inr (.inl x), .inl y => y.val=0 ∧ x.2.val=0
  | .inl x, .inr (.inr y) => x.val=d ∧ y.2.val=0
  | .inr (.inr x), .inl y => y.val=d ∧ x.2.val=0
  | .inr (.inl x), .inr (.inl y) => x.1=y.1 ∧ (x.2.val+1=y.2.val ∨ y.2.val+1=x.2.val)
  | .inr (.inr x), .inr (.inr y) => x.1=y.1 ∧ (x.2.val+1=y.2.val ∨ y.2.val+1=x.2.val)
  | _, _ => False

def armModel {A B : Type*} (d : ℕ) (a : A → ℕ) (b : B → ℕ) :
    SimpleGraph (ArmModelVertex d a b) where
  Adj := armModelAdj d a b
  symm := ⟨by
    intro x y h
    rcases x with x | x | x <;> rcases y with y | y | y <;>
      simpa [armModelAdj, eq_comm, or_comm, and_comm] using h⟩
  loopless := ⟨by
    intro x
    rcases x with x | x | x <;> simp [armModelAdj]
  ⟩


end Math15.Graceful
end

/- ArmData -/
section
namespace Math15.Graceful

structure ArmPath {n : ℕ} (G : SimpleGraph (Fin n)) {u v : Fin n} (hne : u ≠ v)
    (c : ArmComponents G hne) where
  length : ℕ
  positive : 0 < length
  iso : SimpleGraph.pathGraph length ≃g c.val.toSimpleGraph
  rootNeighbor : G.neighborSet u
  rootNeighbor_component : neighborComponent G u rootNeighbor = c.val
  start_val : (iso ⟨0, positive⟩).val.val = rootNeighbor.val

noncomputable def chooseArmPath {n : ℕ} (G : SimpleGraph (Fin n))
    (hG : G.IsTree) {u v : Fin n} (hne : u ≠ v)
    (hdegrees : ∀ w, w ≠ u → w ≠ v → degree G w ≤ 2)
    (c : ArmComponents G hne) : ArmPath G hne c := by
  classical
  let x := (neighborComponentEquiv G u hG).symm c.val
  have hx : neighborComponent G u x = c.val :=
    (neighborComponentEquiv G u hG).apply_symm_apply c.val
  have hex := noncentral_component_is_arm G hG hne hdegrees c.val c.property x hx
  let k := Classical.choose hex
  let e := Classical.choose (Classical.choose_spec hex)
  have he := Classical.choose_spec (Classical.choose_spec hex)
  exact ⟨k+1, Nat.succ_pos _, e, x, hx, he⟩

namespace ArmPath

variable {n : ℕ} {G : SimpleGraph (Fin n)} {u v : Fin n} {hne : u ≠ v}
  {c : ArmComponents G hne} (P : ArmPath G hne c)

def vertex (i : Fin P.length) : Fin n := (P.iso i).val.val

theorem vertex_injective : Function.Injective P.vertex := by
  intro i j hij
  apply P.iso.injective
  apply Subtype.ext
  apply Subtype.ext
  exact hij

theorem vertex_ne_root (i : Fin P.length) : P.vertex i ≠ u := (P.iso i).val.property

theorem vertex_component (i : Fin P.length) :
    (deleteVertexGraph G u).connectedComponentMk ⟨P.vertex i, P.vertex_ne_root i⟩ = c.val :=
  (c.val.mem_supp_iff _).mp (P.iso i).property

theorem vertex_inArm (i : Fin P.length) : InArm G hne (P.vertex i) := by
  refine ⟨P.vertex_ne_root i, ?_⟩
  rw [P.vertex_component]
  exact c.property

theorem vertex_adj_iff (i j : Fin P.length) :
    G.Adj (P.vertex i) (P.vertex j) ↔ i.val+1=j.val ∨ j.val+1=i.val := by
  change c.val.toSimpleGraph.Adj (P.iso i) (P.iso j) ↔ _
  rw [P.iso.map_adj_iff, SimpleGraph.pathGraph_adj]

theorem vertex_root_adj_iff (hG : G.IsAcyclic) (i : Fin P.length) :
    G.Adj u (P.vertex i) ↔ i.val = 0 := by
  constructor
  · intro hadj
    have hcomp : neighborComponent G u ⟨P.vertex i, hadj⟩ =
        neighborComponent G u P.rootNeighbor :=
      (P.vertex_component i).trans P.rootNeighbor_component.symm
    have heq := congrArg Subtype.val (neighborComponent_injective G u hG hcomp)
    have hiv : P.vertex i = P.vertex ⟨0, P.positive⟩ := heq.trans P.start_val.symm
    exact congrArg Fin.val (P.vertex_injective hiv)
  · intro hi
    have hiz : i = (⟨0, P.positive⟩ : Fin P.length) := Fin.ext hi
    rw [hiz]
    change G.Adj u (P.iso ⟨0, P.positive⟩).val.val
    rw [P.start_val]
    exact P.rootNeighbor.property

theorem vertex_surjective_component (x : c.val) : ∃ i, P.vertex i = x.val.val := by
  obtain ⟨i, hi⟩ := P.iso.surjective x
  exact ⟨i, congrArg (fun z : c.val => z.val.val) hi⟩

end ArmPath

lemma inArm_ne_other {V : Type*} {G : SimpleGraph V} {u v : V} {hne : u ≠ v}
    {x : V} (hx : InArm G hne x) : x ≠ v := by
  rintro rfl
  obtain ⟨_, hcomp⟩ := hx
  exact hcomp rfl

lemma inArm_cross_not_adj {V : Type*} {G : SimpleGraph V} (hG : G.Connected)
    {u v : V} {hne : u ≠ v} {x y : V} (hx : InArm G hne x)
    (hy : InArm G hne.symm y) : ¬ G.Adj x y := by
  intro hadj
  rcases adjacent_inArm_or_root G hne hx hadj with hyr | hyarm
  · exact inArm_ne_other hy hyr
  · exact inArm_not_reverse G hne hG hyarm hy

end Math15.Graceful
end

/- SpineData -/
section
namespace Math15.Graceful

namespace ArmPath
variable {n : ℕ} {G : SimpleGraph (Fin n)} {u v : Fin n} {hne : u ≠ v}
  {c d : ArmComponents G hne} (P : ArmPath G hne c) (Q : ArmPath G hne d)

theorem component_eq_of_vertex_eq {i : Fin P.length} {j : Fin Q.length}
    (h : P.vertex i = Q.vertex j) : c = d := by
  apply Subtype.ext
  have hsub : (⟨P.vertex i, P.vertex_ne_root i⟩ : {x : Fin n // x ≠ u}) =
      ⟨Q.vertex j, Q.vertex_ne_root j⟩ := Subtype.ext h
  exact (P.vertex_component i).symm.trans ((congrArg
    (deleteVertexGraph G u).connectedComponentMk hsub).trans (Q.vertex_component j))

theorem component_eq_of_adj {i : Fin P.length} {j : Fin Q.length}
    (h : G.Adj (P.vertex i) (Q.vertex j)) : c = d := by
  apply Subtype.ext
  have hadj : (deleteVertexGraph G u).Adj ⟨P.vertex i, P.vertex_ne_root i⟩
      ⟨Q.vertex j, Q.vertex_ne_root j⟩ := h
  exact (P.vertex_component i).symm.trans
    ((SimpleGraph.ConnectedComponent.sound hadj.reachable).trans (Q.vertex_component j))

end ArmPath

namespace Spine
variable {n : ℕ} {G : SimpleGraph (Fin n)} {u v : Fin n} {p : G.Walk u v} (hp : p.IsPath)

def vertex (i : Fin (p.length+1)) : Fin n := (hp.pathGraphIsoToSubgraph i).val

theorem vertex_eq_getVert (i : Fin (p.length+1)) : vertex hp i = p.getVert i.val := by
  change p.support[i.val] = p.getVert i.val
  exact p.support_getElem_eq_getVert _

theorem vertex_injective : Function.Injective (vertex hp) := by
  intro i j h
  exact hp.pathGraphIsoToSubgraph.injective (Subtype.ext h)

theorem vertex_mem (i : Fin (p.length+1)) : vertex hp i ∈ p.support :=
  p.mem_verts_toSubgraph.mp (hp.pathGraphIsoToSubgraph i).property

theorem vertex_start : vertex hp 0 = u := by rw [vertex_eq_getVert]; exact p.getVert_zero

theorem vertex_end : vertex hp ⟨p.length, by omega⟩ = v := by
  rw [vertex_eq_getVert]
  exact p.getVert_length

theorem vertex_surjective {x : Fin n} (hx : x ∈ p.support) : ∃ i, vertex hp i = x := by
  obtain ⟨i, hi⟩ := hp.pathGraphIsoToSubgraph.surjective ⟨x, p.mem_verts_toSubgraph.mpr hx⟩
  exact ⟨i, congrArg Subtype.val hi⟩

theorem vertex_adj_iff (hG : G.IsAcyclic) (i j : Fin (p.length+1)) :
    G.Adj (vertex hp i) (vertex hp j) ↔ i.val+1=j.val ∨ j.val+1=i.val := by
  have hind := path_toSubgraph_isInduced G hG p
  have hrel := hind.adj (a := hp.pathGraphIsoToSubgraph i) (b := hp.pathGraphIsoToSubgraph j)
  unfold vertex
  rw [← hrel]
  change p.toSubgraph.coe.Adj (hp.pathGraphIsoToSubgraph i) (hp.pathGraphIsoToSubgraph j) ↔ _
  rw [hp.pathGraphIsoToSubgraph.map_adj_iff, SimpleGraph.pathGraph_adj]

theorem vertex_ne_arm {hne : u ≠ v} {c : ArmComponents G hne}
    (P : ArmPath G hne c) (i : Fin (p.length+1)) (j : Fin P.length) :
    vertex hp i ≠ P.vertex j := by
  intro h
  have ha := P.vertex_inArm j
  rw [← h] at ha
  exact not_inArm_of_mem_path G hne hp (vertex_mem hp i) ha

theorem vertex_ne_reverse_arm {hne : u ≠ v} {c : ArmComponents G hne.symm}
    (P : ArmPath G hne.symm c) (i : Fin (p.length+1)) (j : Fin P.length) :
    vertex hp i ≠ P.vertex j := by
  intro h
  have ha := P.vertex_inArm j
  rw [← h] at ha
  have hm : vertex hp i ∈ p.reverse.support := by simpa using vertex_mem hp i
  exact not_inArm_of_mem_path G hne.symm hp.reverse hm ha

theorem vertex_arm_adj_iff (hG : G.IsAcyclic) {hne : u ≠ v} {c : ArmComponents G hne}
    (P : ArmPath G hne c) (i : Fin (p.length+1)) (j : Fin P.length) :
    G.Adj (vertex hp i) (P.vertex j) ↔ i.val=0 ∧ j.val=0 := by
  constructor
  · intro hadj
    have heq : vertex hp i = u := by
      rcases adjacent_inArm_or_root G hne (P.vertex_inArm j) hadj.symm with heq | ha
      · exact heq
      · exact (not_inArm_of_mem_path G hne hp (vertex_mem hp i) ha).elim
    have hi : i = 0 := vertex_injective hp (heq.trans (vertex_start hp).symm)
    refine ⟨congrArg Fin.val hi, ?_⟩
    rw [heq] at hadj
    exact (P.vertex_root_adj_iff hG j).mp hadj
  · rintro ⟨hi, hj⟩
    have hiz : i = 0 := Fin.ext hi
    rw [hiz, vertex_start]
    exact (P.vertex_root_adj_iff hG j).mpr hj

theorem vertex_reverse_arm_adj_iff (hG : G.IsAcyclic) {hne : u ≠ v}
    {c : ArmComponents G hne.symm} (P : ArmPath G hne.symm c)
    (i : Fin (p.length+1)) (j : Fin P.length) :
    G.Adj (vertex hp i) (P.vertex j) ↔ i.val=p.length ∧ j.val=0 := by
  constructor
  · intro hadj
    have heq : vertex hp i = v := by
      rcases adjacent_inArm_or_root G hne.symm (P.vertex_inArm j) hadj.symm with heq | ha
      · exact heq
      · have hm : vertex hp i ∈ p.reverse.support := by simpa using vertex_mem hp i
        exact (not_inArm_of_mem_path G hne.symm hp.reverse hm ha).elim
    have hi : i = ⟨p.length, by omega⟩ := vertex_injective hp (heq.trans (vertex_end hp).symm)
    refine ⟨congrArg Fin.val hi, ?_⟩
    rw [heq] at hadj
    exact (P.vertex_root_adj_iff hG j).mp hadj
  · rintro ⟨hi, hj⟩
    have hiz : i = ⟨p.length, by omega⟩ := Fin.ext hi
    rw [hiz, vertex_end]
    exact (P.vertex_root_adj_iff hG j).mpr hj

end Spine
end Math15.Graceful
end

/- ArmModelIso -/
section
namespace Math15.Graceful

noncomputable def armModelMap {n : ℕ} {G : SimpleGraph (Fin n)} {u v : Fin n}
    {hne : u ≠ v} {p : G.Walk u v} (hp : p.IsPath)
    (A : (c : ArmComponents G hne) → ArmPath G hne c)
    (B : (c : ArmComponents G hne.symm) → ArmPath G hne.symm c) :
    ArmModelVertex p.length (fun c => (A c).length) (fun c => (B c).length) → Fin n
  | .inl i => Spine.vertex hp i
  | .inr (.inl ⟨c, i⟩) => (A c).vertex i
  | .inr (.inr ⟨c, i⟩) => (B c).vertex i

theorem armModelMap_bijective {n : ℕ} {G : SimpleGraph (Fin n)}
    (hG : G.IsTree) {u v : Fin n} (hbranch : Branch43 G u v)
    {p : G.Walk u v} (hp : p.IsPath)
    (A : (c : ArmComponents G hbranch.1) → ArmPath G hbranch.1 c)
    (B : (c : ArmComponents G hbranch.1.symm) → ArmPath G hbranch.1.symm c) :
    Function.Bijective (armModelMap hp A B) := by
  constructor
  · intro x y hxy
    rcases x with x | ⟨c, i⟩ | ⟨c, i⟩ <;>
      rcases y with y | ⟨d, j⟩ | ⟨d, j⟩ <;> dsimp [armModelMap] at hxy
    · exact congrArg Sum.inl (Spine.vertex_injective hp hxy)
    · exact (Spine.vertex_ne_arm hp (A d) x j hxy).elim
    · exact (Spine.vertex_ne_reverse_arm (hne := hbranch.1) hp (B d) x j hxy).elim
    · exact (Spine.vertex_ne_arm hp (A c) y i hxy.symm).elim
    · have hcd := (A c).component_eq_of_vertex_eq (A d) hxy
      subst d
      have hij := (A c).vertex_injective hxy
      subst j
      rfl
    · have hx := (A c).vertex_inArm i
      have hy := (B d).vertex_inArm j
      rw [← hxy] at hy
      exact (inArm_not_reverse G hbranch.1 hG.connected hx hy).elim
    · exact (Spine.vertex_ne_reverse_arm (hne := hbranch.1) hp (B c) y i hxy.symm).elim
    · have hx := (B c).vertex_inArm i
      have hy := (A d).vertex_inArm j
      rw [hxy] at hx
      exact (inArm_not_reverse G hbranch.1 hG.connected hy hx).elim
    · have hcd := (B c).component_eq_of_vertex_eq (B d) hxy
      subst d
      have hij := (B c).vertex_injective hxy
      subst j
      rfl
  · intro x
    rcases branch43_spine_and_arms_cover G hG hbranch hp x with hx | hx | hx
    · obtain ⟨i, hi⟩ := Spine.vertex_surjective hp hx
      exact ⟨.inl i, hi⟩
    · obtain ⟨hxu, hxcomp⟩ := hx
      let c : ArmComponents G hbranch.1 :=
        ⟨(deleteVertexGraph G u).connectedComponentMk ⟨x, hxu⟩, hxcomp⟩
      let z : c.val := ⟨⟨x, hxu⟩, (c.val.mem_supp_iff _).mpr rfl⟩
      obtain ⟨i, hi⟩ := (A c).vertex_surjective_component z
      exact ⟨.inr (.inl ⟨c, i⟩), hi⟩
    · obtain ⟨hxv, hxcomp⟩ := hx
      let c : ArmComponents G hbranch.1.symm :=
        ⟨(deleteVertexGraph G v).connectedComponentMk ⟨x, hxv⟩, hxcomp⟩
      let z : c.val := ⟨⟨x, hxv⟩, (c.val.mem_supp_iff _).mpr rfl⟩
      obtain ⟨i, hi⟩ := (B c).vertex_surjective_component z
      exact ⟨.inr (.inr ⟨c, i⟩), hi⟩

theorem armModelMap_adj_iff {n : ℕ} {G : SimpleGraph (Fin n)}
    (hG : G.IsTree) {u v : Fin n} (hbranch : Branch43 G u v)
    {p : G.Walk u v} (hp : p.IsPath)
    (A : (c : ArmComponents G hbranch.1) → ArmPath G hbranch.1 c)
    (B : (c : ArmComponents G hbranch.1.symm) → ArmPath G hbranch.1.symm c)
    (x y : ArmModelVertex p.length (fun c => (A c).length) (fun c => (B c).length)) :
    G.Adj (armModelMap hp A B x) (armModelMap hp A B y) ↔
      (armModel p.length (fun c => (A c).length) (fun c => (B c).length)).Adj x y := by
  classical
  rcases x with x | ⟨c, i⟩ | ⟨c, i⟩ <;>
    rcases y with y | ⟨d, j⟩ | ⟨d, j⟩ <;>
      dsimp [armModelMap, armModel, armModelAdj]
  · exact Spine.vertex_adj_iff hp hG.isAcyclic x y
  · exact Spine.vertex_arm_adj_iff hp hG.isAcyclic (A d) x j
  · exact Spine.vertex_reverse_arm_adj_iff (hne := hbranch.1) hp hG.isAcyclic (B d) x j
  · rw [G.adj_comm]
    exact Spine.vertex_arm_adj_iff hp hG.isAcyclic (A c) y i
  · by_cases hcd : c = d
    · subst d
      simpa using (A c).vertex_adj_iff i j
    · have hn : ¬ G.Adj ((A c).vertex i) ((A d).vertex j) :=
        fun h => hcd ((A c).component_eq_of_adj (A d) h)
      simp [hn, hcd]
  · exact iff_false_intro (inArm_cross_not_adj hG.connected ((A c).vertex_inArm i) ((B d).vertex_inArm j))
  · rw [G.adj_comm]
    exact Spine.vertex_reverse_arm_adj_iff (hne := hbranch.1) hp hG.isAcyclic (B c) y i
  · rw [G.adj_comm]
    exact iff_false_intro (inArm_cross_not_adj hG.connected ((A d).vertex_inArm j) ((B c).vertex_inArm i))
  · by_cases hcd : c = d
    · subst d
      simpa using (B c).vertex_adj_iff i j
    · have hn : ¬ G.Adj ((B c).vertex i) ((B d).vertex j) :=
        fun h => hcd ((B c).component_eq_of_adj (B d) h)
      simp [hn, hcd]

noncomputable def armModelIso {n : ℕ} {G : SimpleGraph (Fin n)}
    (hG : G.IsTree) {u v : Fin n} (hbranch : Branch43 G u v)
    {p : G.Walk u v} (hp : p.IsPath)
    (A : (c : ArmComponents G hbranch.1) → ArmPath G hbranch.1 c)
    (B : (c : ArmComponents G hbranch.1.symm) → ArmPath G hbranch.1.symm c) :
    armModel p.length (fun c => (A c).length) (fun c => (B c).length) ≃g G where
  toEquiv := Equiv.ofBijective (armModelMap hp A B) (armModelMap_bijective hG hbranch hp A B)
  map_rel_iff' := by
    intro x y
    exact armModelMap_adj_iff hG hbranch hp A B x y

end Math15.Graceful
end

/- ArmReindex -/
section
namespace Math15.Graceful

noncomputable def armModelReindex {A B A' B' : Type*} (d : ℕ)
    (a : A → ℕ) (b : B → ℕ) (eA : A' ≃ A) (eB : B' ≃ B) :
    armModel d (a ∘ eA) (b ∘ eB) ≃g armModel d a b where
  toEquiv := Equiv.sumCongr (Equiv.refl _) <|
    Equiv.sumCongr (Equiv.sigmaCongrLeft (β := fun i => Fin (a i)) eA)
      (Equiv.sigmaCongrLeft (β := fun i => Fin (b i)) eB)
  map_rel_iff' := by
    intro x y
    rcases x with x | ⟨i, x⟩ | ⟨i, x⟩ <;>
      rcases y with y | ⟨j, y⟩ | ⟨j, y⟩ <;>
        simp [armModel, armModelAdj, Equiv.sigmaCongrLeft]

end Math15.Graceful
end

/- ArmIntervals -/
section
namespace Math15.Graceful

open Bounty

def armAOffset (d : ℕ) (a : Fin 3 → ℕ) : Fin 3 → ℕ :=
  ![d+1, d+a 0+1, d+a 0+a 1+1]

def armBOffset (d : ℕ) (a : Fin 3 → ℕ) (b : Fin 2 → ℕ) : Fin 2 → ℕ :=
  ![d+a 0+a 1+a 2+1, d+a 0+a 1+a 2+b 0+1]

def armCode (d : ℕ) (a : Fin 3 → ℕ) (b : Fin 2 → ℕ) : ArmModelVertex d a b → ℕ
  | .inl i => i.val
  | .inr (.inl ⟨i, j⟩) => armAOffset d a i + j.val
  | .inr (.inr ⟨i, j⟩) => armBOffset d a b i + j.val

theorem armCode_lt (d : ℕ) (a : Fin 3 → ℕ) (b : Fin 2 → ℕ)
    (x : ArmModelVertex d a b) :
    armCode d a b x < doubleSpiderEdges (a 0) (a 1) (a 2) d (b 0) (b 1) + 1 := by
  rcases x with x | ⟨i, x⟩ | ⟨i, x⟩
  · simp only [armCode, doubleSpiderEdges]
    omega
  · fin_cases i <;> simp [armCode, armAOffset, doubleSpiderEdges] <;> omega
  · fin_cases i <;> simp [armCode, armBOffset, doubleSpiderEdges] <;> omega

def armEncode (d : ℕ) (a : Fin 3 → ℕ) (b : Fin 2 → ℕ)
    (x : ArmModelVertex d a b) :
    Fin (doubleSpiderEdges (a 0) (a 1) (a 2) d (b 0) (b 1) + 1) :=
  ⟨armCode d a b x, armCode_lt d a b x⟩

theorem armCode_injective (d : ℕ) (a : Fin 3 → ℕ) (b : Fin 2 → ℕ) :
    Function.Injective (armCode d a b) := by
  intro x y h
  rcases x with x | ⟨i, x⟩ | ⟨i, x⟩ <;> rcases y with y | ⟨j, y⟩ | ⟨j, y⟩
  · exact congrArg Sum.inl (Fin.ext h)
  · fin_cases j <;> simp [armCode, armAOffset] at h <;> omega
  · fin_cases j <;> simp [armCode, armBOffset] at h <;> omega
  · fin_cases i <;> simp [armCode, armAOffset] at h <;> omega
  · fin_cases i <;> fin_cases j <;> simp [armCode, armAOffset] at h
    all_goals first | omega | (congr 3; exact Fin.ext (by omega))
  · fin_cases i <;> fin_cases j <;> simp [armCode, armAOffset, armBOffset] at h <;> omega
  · fin_cases i <;> simp [armCode, armBOffset] at h <;> omega
  · fin_cases i <;> fin_cases j <;> simp [armCode, armAOffset, armBOffset] at h <;> omega
  · fin_cases i <;> fin_cases j <;> simp [armCode, armBOffset] at h
    all_goals first | omega | (congr 3; exact Fin.ext (by omega))

theorem armEncode_bijective (d : ℕ) (a : Fin 3 → ℕ) (b : Fin 2 → ℕ) :
    Function.Bijective (armEncode d a b) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · intro x y h
    exact armCode_injective d a b (congrArg Fin.val h)
  · rw [Fintype.card_fin]
    simp [ArmModelVertex, Fintype.card_sigma, Fin.sum_univ_succ, doubleSpiderEdges]
    omega

theorem armEncode_adj_iff_spine_spine (d : ℕ) (a : Fin 3 → ℕ) (b : Fin 2 → ℕ)
    (hd : 0 < d) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (x : Fin (d+1)) (y : Fin (d+1)) :
    (doubleSpider (a 0) (a 1) (a 2) d (b 0) (b 1)).Adj
      (armEncode d a b (.inl x)) (armEncode d a b (.inl y)) ↔
      (armModel d a b).Adj (.inl x) (.inl y) := by
  have ha0 := ha 0
  have ha1 := ha 1
  have ha2 := ha 2
  have hb0 := hb 0
  have hb1 := hb 1

  all_goals simp [doubleSpider, parentGraph, armEncode, armCode, armModel, armModelAdj,
    doubleSpiderParent, armAOffset, armBOffset]
  all_goals try simp only [Fin.ext_iff, Fin.val_zero]
  all_goals split_ifs <;> omega

theorem armEncode_adj_iff_spine_a (d : ℕ) (a : Fin 3 → ℕ) (b : Fin 2 → ℕ)
    (hd : 0 < d) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (x : Fin (d+1)) (j : Fin 3) (y : Fin (a j)) :
    (doubleSpider (a 0) (a 1) (a 2) d (b 0) (b 1)).Adj
      (armEncode d a b (.inl x)) (armEncode d a b (.inr (.inl ⟨j, y⟩))) ↔
      (armModel d a b).Adj (.inl x) (.inr (.inl ⟨j, y⟩)) := by
  have ha0 := ha 0
  have ha1 := ha 1
  have ha2 := ha 2
  have hb0 := hb 0
  have hb1 := hb 1
  all_goals fin_cases j
  all_goals simp [doubleSpider, parentGraph, armEncode, armCode, armModel, armModelAdj,
    doubleSpiderParent, armAOffset, armBOffset]
  all_goals try simp only [Fin.ext_iff, Fin.val_zero]
  all_goals split_ifs <;> omega

theorem armEncode_adj_iff_spine_b (d : ℕ) (a : Fin 3 → ℕ) (b : Fin 2 → ℕ)
    (hd : 0 < d) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (x : Fin (d+1)) (j : Fin 2) (y : Fin (b j)) :
    (doubleSpider (a 0) (a 1) (a 2) d (b 0) (b 1)).Adj
      (armEncode d a b (.inl x)) (armEncode d a b (.inr (.inr ⟨j, y⟩))) ↔
      (armModel d a b).Adj (.inl x) (.inr (.inr ⟨j, y⟩)) := by
  have ha0 := ha 0
  have ha1 := ha 1
  have ha2 := ha 2
  have hb0 := hb 0
  have hb1 := hb 1
  all_goals fin_cases j
  all_goals simp [doubleSpider, parentGraph, armEncode, armCode, armModel, armModelAdj,
    doubleSpiderParent, armAOffset, armBOffset]
  all_goals try simp only [Fin.ext_iff, Fin.val_zero]
  all_goals split_ifs <;> omega

theorem armEncode_adj_iff_a_spine (d : ℕ) (a : Fin 3 → ℕ) (b : Fin 2 → ℕ)
    (hd : 0 < d) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (i : Fin 3) (x : Fin (a i)) (y : Fin (d+1)) :
    (doubleSpider (a 0) (a 1) (a 2) d (b 0) (b 1)).Adj
      (armEncode d a b (.inr (.inl ⟨i, x⟩))) (armEncode d a b (.inl y)) ↔
      (armModel d a b).Adj (.inr (.inl ⟨i, x⟩)) (.inl y) := by
  have ha0 := ha 0
  have ha1 := ha 1
  have ha2 := ha 2
  have hb0 := hb 0
  have hb1 := hb 1
  all_goals fin_cases i
  all_goals simp [doubleSpider, parentGraph, armEncode, armCode, armModel, armModelAdj,
    doubleSpiderParent, armAOffset, armBOffset]
  all_goals try simp only [Fin.ext_iff, Fin.val_zero]
  all_goals split_ifs <;> omega

theorem armEncode_adj_iff_a_a (d : ℕ) (a : Fin 3 → ℕ) (b : Fin 2 → ℕ)
    (hd : 0 < d) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (i : Fin 3) (x : Fin (a i)) (j : Fin 3) (y : Fin (a j)) :
    (doubleSpider (a 0) (a 1) (a 2) d (b 0) (b 1)).Adj
      (armEncode d a b (.inr (.inl ⟨i, x⟩))) (armEncode d a b (.inr (.inl ⟨j, y⟩))) ↔
      (armModel d a b).Adj (.inr (.inl ⟨i, x⟩)) (.inr (.inl ⟨j, y⟩)) := by
  have ha0 := ha 0
  have ha1 := ha 1
  have ha2 := ha 2
  have hb0 := hb 0
  have hb1 := hb 1
  all_goals fin_cases i
  all_goals fin_cases j
  all_goals simp [doubleSpider, parentGraph, armEncode, armCode, armModel, armModelAdj,
    doubleSpiderParent, armAOffset, armBOffset]
  all_goals try simp only [Fin.ext_iff, Fin.val_zero]
  all_goals split_ifs <;> omega

theorem armEncode_adj_iff_a_b (d : ℕ) (a : Fin 3 → ℕ) (b : Fin 2 → ℕ)
    (hd : 0 < d) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (i : Fin 3) (x : Fin (a i)) (j : Fin 2) (y : Fin (b j)) :
    (doubleSpider (a 0) (a 1) (a 2) d (b 0) (b 1)).Adj
      (armEncode d a b (.inr (.inl ⟨i, x⟩))) (armEncode d a b (.inr (.inr ⟨j, y⟩))) ↔
      (armModel d a b).Adj (.inr (.inl ⟨i, x⟩)) (.inr (.inr ⟨j, y⟩)) := by
  have ha0 := ha 0
  have ha1 := ha 1
  have ha2 := ha 2
  have hb0 := hb 0
  have hb1 := hb 1
  all_goals fin_cases i
  all_goals fin_cases j
  all_goals simp [doubleSpider, parentGraph, armEncode, armCode, armModel, armModelAdj,
    doubleSpiderParent, armAOffset, armBOffset]
  all_goals try simp only [Fin.ext_iff, Fin.val_zero]
  all_goals split_ifs <;> omega

theorem armEncode_adj_iff_b_spine (d : ℕ) (a : Fin 3 → ℕ) (b : Fin 2 → ℕ)
    (hd : 0 < d) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (i : Fin 2) (x : Fin (b i)) (y : Fin (d+1)) :
    (doubleSpider (a 0) (a 1) (a 2) d (b 0) (b 1)).Adj
      (armEncode d a b (.inr (.inr ⟨i, x⟩))) (armEncode d a b (.inl y)) ↔
      (armModel d a b).Adj (.inr (.inr ⟨i, x⟩)) (.inl y) := by
  have ha0 := ha 0
  have ha1 := ha 1
  have ha2 := ha 2
  have hb0 := hb 0
  have hb1 := hb 1
  all_goals fin_cases i
  all_goals simp [doubleSpider, parentGraph, armEncode, armCode, armModel, armModelAdj,
    doubleSpiderParent, armAOffset, armBOffset]
  all_goals try simp only [Fin.ext_iff, Fin.val_zero]
  all_goals split_ifs <;> omega

theorem armEncode_adj_iff_b_a (d : ℕ) (a : Fin 3 → ℕ) (b : Fin 2 → ℕ)
    (hd : 0 < d) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (i : Fin 2) (x : Fin (b i)) (j : Fin 3) (y : Fin (a j)) :
    (doubleSpider (a 0) (a 1) (a 2) d (b 0) (b 1)).Adj
      (armEncode d a b (.inr (.inr ⟨i, x⟩))) (armEncode d a b (.inr (.inl ⟨j, y⟩))) ↔
      (armModel d a b).Adj (.inr (.inr ⟨i, x⟩)) (.inr (.inl ⟨j, y⟩)) := by
  have ha0 := ha 0
  have ha1 := ha 1
  have ha2 := ha 2
  have hb0 := hb 0
  have hb1 := hb 1
  all_goals fin_cases i
  all_goals fin_cases j
  all_goals simp [doubleSpider, parentGraph, armEncode, armCode, armModel, armModelAdj,
    doubleSpiderParent, armAOffset, armBOffset]
  all_goals try simp only [Fin.ext_iff, Fin.val_zero]
  all_goals split_ifs <;> omega

theorem armEncode_adj_iff_b_b (d : ℕ) (a : Fin 3 → ℕ) (b : Fin 2 → ℕ)
    (hd : 0 < d) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (i : Fin 2) (x : Fin (b i)) (j : Fin 2) (y : Fin (b j)) :
    (doubleSpider (a 0) (a 1) (a 2) d (b 0) (b 1)).Adj
      (armEncode d a b (.inr (.inr ⟨i, x⟩))) (armEncode d a b (.inr (.inr ⟨j, y⟩))) ↔
      (armModel d a b).Adj (.inr (.inr ⟨i, x⟩)) (.inr (.inr ⟨j, y⟩)) := by
  have ha0 := ha 0
  have ha1 := ha 1
  have ha2 := ha 2
  have hb0 := hb 0
  have hb1 := hb 1
  all_goals fin_cases i
  all_goals fin_cases j
  all_goals simp [doubleSpider, parentGraph, armEncode, armCode, armModel, armModelAdj,
    doubleSpiderParent, armAOffset, armBOffset]
  all_goals try simp only [Fin.ext_iff, Fin.val_zero]
  all_goals split_ifs <;> omega

theorem armEncode_adj_iff (d : ℕ) (a : Fin 3 → ℕ) (b : Fin 2 → ℕ)
    (hd : 0 < d) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (x y : ArmModelVertex d a b) :
    (doubleSpider (a 0) (a 1) (a 2) d (b 0) (b 1)).Adj (armEncode d a b x) (armEncode d a b y) ↔
      (armModel d a b).Adj x y := by
  rcases x with x | ⟨i, x⟩ | ⟨i, x⟩ <;> rcases y with y | ⟨j, y⟩ | ⟨j, y⟩
  · exact armEncode_adj_iff_spine_spine d a b hd ha hb x y
  · exact armEncode_adj_iff_spine_a d a b hd ha hb x j y
  · exact armEncode_adj_iff_spine_b d a b hd ha hb x j y
  · exact armEncode_adj_iff_a_spine d a b hd ha hb i x y
  · exact armEncode_adj_iff_a_a d a b hd ha hb i x j y
  · exact armEncode_adj_iff_a_b d a b hd ha hb i x j y
  · exact armEncode_adj_iff_b_spine d a b hd ha hb i x y
  · exact armEncode_adj_iff_b_a d a b hd ha hb i x j y
  · exact armEncode_adj_iff_b_b d a b hd ha hb i x j y

noncomputable def armIntervalsIso (d : ℕ) (a : Fin 3 → ℕ) (b : Fin 2 → ℕ)
    (hd : 0 < d) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) :
    armModel d a b ≃g doubleSpider (a 0) (a 1) (a 2) d (b 0) (b 1) where
  toEquiv := Equiv.ofBijective (armEncode d a b) (armEncode_bijective d a b)
  map_rel_iff' := by
    intro x y
    exact armEncode_adj_iff d a b hd ha hb x y

end Math15.Graceful
end

/- StructuralReduction -/
section
namespace Math15.Graceful

/-- A tree with the prescribed degree-4 and degree-3 branches is exactly a
six-path double spider, up to its vertex names. -/
theorem branch43_exists_doubleSpider_iso {n : ℕ} (G : SimpleGraph (Fin n))
    (hG : G.IsTree) {u v : Fin n} (hbranch : Branch43 G u v) :
    ∃ a b c d e f : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ 0 < e ∧ 0 < f ∧
      Nonempty (Bounty.doubleSpider a b c d e f ≃g G) := by
  classical
  obtain ⟨p, hp⟩ := hG.connected.exists_isPath u v
  have hd : 0 < p.length := by
    have hnil : ¬p.Nil := fun h => hbranch.1 (hp.nil_iff_eq.mp h)
    exact SimpleGraph.Walk.not_nil_iff_lt_length.mp hnil
  let A : (c : ArmComponents G hbranch.1) → ArmPath G hbranch.1 c :=
    chooseArmPath G hG hbranch.1 hbranch.2.2.2
  let B : (c : ArmComponents G hbranch.1.symm) → ArmPath G hbranch.1.symm c :=
    chooseArmPath G hG hbranch.1.symm (fun w hwv hwu => hbranch.2.2.2 w hwu hwv)
  let : Fintype (deleteVertexGraph G u).ConnectedComponent := Fintype.ofFinite _
  let : Fintype (deleteVertexGraph G v).ConnectedComponent := Fintype.ofFinite _
  let : Fintype (ArmComponents G hbranch.1) := by unfold ArmComponents; infer_instance
  let : Fintype (ArmComponents G hbranch.1.symm) := by unfold ArmComponents; infer_instance
  have hcardA : Fintype.card (ArmComponents G hbranch.1) = 3 := by
    rw [← Nat.card_eq_fintype_card]
    exact (branch43_arm_components_card G hG hbranch).1
  have hcardB : Fintype.card (ArmComponents G hbranch.1.symm) = 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact (branch43_arm_components_card G hG hbranch).2
  let eA : Fin 3 ≃ ArmComponents G hbranch.1 := (Fintype.equivFinOfCardEq hcardA).symm
  let eB : Fin 2 ≃ ArmComponents G hbranch.1.symm := (Fintype.equivFinOfCardEq hcardB).symm
  let aa : Fin 3 → ℕ := fun i => (A (eA i)).length
  let bb : Fin 2 → ℕ := fun i => (B (eB i)).length
  have ha : ∀ i, 0 < aa i := fun i => (A (eA i)).positive
  have hb : ∀ i, 0 < bb i := fun i => (B (eB i)).positive
  let er : armModel p.length aa bb ≃g
      armModel p.length (fun c => (A c).length) (fun c => (B c).length) :=
    armModelReindex p.length (fun c => (A c).length) (fun c => (B c).length) eA eB
  let ef : Bounty.doubleSpider (aa 0) (aa 1) (aa 2) p.length (bb 0) (bb 1) ≃g G :=
    (armIntervalsIso p.length aa bb hd ha hb).symm.trans
      (er.trans (armModelIso hG hbranch hp A B))
  exact ⟨aa 0, aa 1, aa 2, p.length, bb 0, bb 1,
    ha 0, ha 1, ha 2, hd, hb 0, hb 1, ⟨ef⟩⟩

end Math15.Graceful
end

/- IsoTransport -/
section
namespace Math15.Graceful

/-- Equal edge differences in a graceful labeling determine the unordered edge. -/
theorem edge_difference_determines_edge {n : ℕ} (G : SimpleGraph (Fin n))
    (f : Fin n → ℕ) (hinj : Function.Injective f)
    (hbound : ∀ v, f v ≤ edgeCount G)
    (hcover : ∀ d, 1 ≤ d → d ≤ edgeCount G →
      ∃! e : Fin n × Fin n, e.1 < e.2 ∧ G.Adj e.1 e.2 ∧
        Nat.dist (f e.1) (f e.2) = d)
    {a b c d : Fin n} (hab : G.Adj a b) (hcd : G.Adj c d)
    (heq : Nat.dist (f a) (f b) = Nat.dist (f c) (f d)) :
    s(a, b) = s(c, d) := by
  have orient (x y : Fin n) (hxy : G.Adj x y) :
      ∃ p : Fin n × Fin n, p.1 < p.2 ∧ G.Adj p.1 p.2 ∧
        Nat.dist (f p.1) (f p.2) = Nat.dist (f x) (f y) ∧
        s(p.1, p.2) = s(x, y) := by
    rcases lt_or_gt_of_ne hxy.ne with hlt | hgt
    · exact ⟨(x, y), hlt, hxy, rfl, rfl⟩
    · exact ⟨(y, x), hgt, hxy.symm, Nat.dist_comm _ _, Sym2.eq_swap⟩
  obtain ⟨p, hpord, hpadj, hpdiff, hpsym⟩ := orient a b hab
  obtain ⟨q, hqord, hqadj, hqdiff, hqsym⟩ := orient c d hcd
  have hdpos : 1 ≤ Nat.dist (f a) (f b) := Nat.dist_pos_of_ne (hinj.ne hab.ne)
  have hdup : Nat.dist (f a) (f b) ≤ edgeCount G := by
    have := hbound a
    have := hbound b
    unfold Nat.dist
    omega
  obtain ⟨w, _, hwuniq⟩ := hcover _ hdpos hdup
  have hpw := hwuniq p ⟨hpord, hpadj, hpdiff⟩
  have hqw := hwuniq q ⟨hqord, hqadj, hqdiff.trans heq.symm⟩
  rw [← hpsym, ← hqsym, hpw, hqw]

/-- Gracefulness is independent of the names and ordering of the vertices. -/
theorem isGraceful_of_iso {n m : ℕ} {G : SimpleGraph (Fin n)}
    {H : SimpleGraph (Fin m)} (e : G ≃g H) (hH : IsGraceful H) : IsGraceful G := by
  classical
  obtain ⟨f, hinj, hbound, hcover⟩ := hH
  have hcard : edgeCount G = edgeCount H := by
    rw [edgeCount_eq_card_edgeFinset, edgeCount_eq_card_edgeFinset]
    exact e.card_edgeFinset_eq
  apply isGraceful_of_injective_differences G (fun x => f (e x))
  · exact hinj.comp e.injective
  · intro x
    rw [hcard]
    exact hbound _
  · intro p q hp hpAdj hq hqAdj hpq
    have hs := edge_difference_determines_edge H f hinj hbound hcover
      (e.map_adj_iff.mpr hpAdj) (e.map_adj_iff.mpr hqAdj) hpq
    rcases Sym2.eq_iff.mp hs with h | h
    · exact Prod.ext (e.injective h.1) (e.injective h.2)
    · have h1 := e.injective h.1
      have h2 := e.injective h.2
      have hrev : q.2 < q.1 := by simpa [h1, h2] using hp
      exact (lt_asymm hq hrev).elim

theorem isGraceful_iff_of_iso {n m : ℕ} {G : SimpleGraph (Fin n)}
    {H : SimpleGraph (Fin m)} (e : G ≃g H) : IsGraceful G ↔ IsGraceful H :=
  ⟨isGraceful_of_iso e.symm, isGraceful_of_iso e⟩

end Math15.Graceful
end

/- DoubleSpiderPermutations -/
section
namespace Bounty
open Math15.Graceful

/-- The order of arms at either hub has no effect on the underlying graph. -/
noncomputable def doubleSpiderPermute (d : ℕ) (a : Fin 3 → ℕ) (b : Fin 2 → ℕ)
    (hd : 0 < d) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (p : Equiv.Perm (Fin 3)) (q : Equiv.Perm (Fin 2)) :
    doubleSpider (a (p 0)) (a (p 1)) (a (p 2)) d (b (q 0)) (b (q 1)) ≃g
      doubleSpider (a 0) (a 1) (a 2) d (b 0) (b 1) :=
  (armIntervalsIso d (a ∘ p) (b ∘ q) hd (fun i => ha (p i)) (fun i => hb (q i))).symm.trans
    ((armModelReindex d a b p q).trans (armIntervalsIso d a b hd ha hb))

noncomputable def doubleSpider_swap_ab (a b c d e f : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e) (hf : 0 < f) :
    doubleSpider b a c d e f ≃g doubleSpider a b c d e f := by
  have hA : ∀ i : Fin 3, 0 < (![a,b,c] : Fin 3 → ℕ) i := by
    intro i
    fin_cases i <;> simp_all
  have hB : ∀ i : Fin 2, 0 < (![e,f] : Fin 2 → ℕ) i := by
    intro i
    fin_cases i <;> simp_all
  simpa [Equiv.swap_apply_def] using doubleSpiderPermute d ![a,b,c] ![e,f] hd hA hB (Equiv.swap 0 1) (Equiv.refl _)

noncomputable def doubleSpider_swap_bc (a b c d e f : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e) (hf : 0 < f) :
    doubleSpider a c b d e f ≃g doubleSpider a b c d e f := by
  have hA : ∀ i : Fin 3, 0 < (![a,b,c] : Fin 3 → ℕ) i := by
    intro i
    fin_cases i <;> simp_all
  have hB : ∀ i : Fin 2, 0 < (![e,f] : Fin 2 → ℕ) i := by
    intro i
    fin_cases i <;> simp_all
  simpa [Equiv.swap_apply_def] using doubleSpiderPermute d ![a,b,c] ![e,f] hd hA hB (Equiv.swap 1 2) (Equiv.refl _)

noncomputable def doubleSpider_swap_ef (a b c d e f : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e) (hf : 0 < f) :
    doubleSpider a b c d f e ≃g doubleSpider a b c d e f := by
  have hA : ∀ i : Fin 3, 0 < (![a,b,c] : Fin 3 → ℕ) i := by
    intro i
    fin_cases i <;> simp_all
  have hB : ∀ i : Fin 2, 0 < (![e,f] : Fin 2 → ℕ) i := by
    intro i
    fin_cases i <;> simp_all
  simpa [Equiv.swap_apply_def] using doubleSpiderPermute d ![a,b,c] ![e,f] hd hA hB (Equiv.refl _) (Equiv.swap 0 1)

end Bounty
end

/- TargetReduction -/
section
namespace Math15.Graceful

theorem target10_of_doubleSpider_graceful
    (h : ∀ a b c d e f : ℕ, 0 < a → 0 < b → 0 < c → 0 < d → 0 < e → 0 < f →
      IsGraceful (Bounty.doubleSpider a b c d e f)) : Target10 := by
  intro n G hG hbranch
  obtain ⟨u, v, huv⟩ := hbranch
  obtain ⟨a, b, c, d, e, f, ha, hb, hc, hd, he, hf, ⟨iso⟩⟩ :=
    branch43_exists_doubleSpider_iso G hG huv
  exact isGraceful_of_iso iso.symm (h a b c d e f ha hb hc hd he hf)

end Math15.Graceful
end

/- Submission -/
section
namespace Bounty
open Math15.Graceful

theorem all_double_spiders_graceful (a b c d e f : ℕ)
    (ha : 0<a) (hb : 0<b) (hc : 0<c) (hd : 0<d) (he : 0<e) (hf : 0<f) :
    IsGraceful (doubleSpider a b c d e f) := by
  classical
  by_cases he2 : e=2
  · subst e
    by_cases hf2 : f=2
    · subst f
      by_cases ha2 : a=2
      · subst a
        by_cases hb2 : b=2
        · subst b
          by_cases hc2 : c=2
          · subst c
            exact all_two_arms_graceful d
          · apply isGraceful_of_iso (doubleSpider_swap_bc 2 2 c d 2 2 ha hb hc hd he hf).symm
            exact doubleSpider_graceful_twoArms 2 c 2 d ha hc hb hd (Or.inr hc2)
        · exact doubleSpider_graceful_twoArms 2 b c d ha hb hc hd (Or.inr hb2)
      · exact doubleSpider_graceful_twoArms a b c d ha hb hc hd (Or.inl ha2)
    · exact doubleSpider_graceful_of_fourLeafZero a b c d 2 f ha hb hc hd he hf
        (Or.inr hf2) (fourLeafZero a b c d ha hb hc hd)
  · exact doubleSpider_graceful_of_fourLeafZero a b c d e f ha hb hc hd he hf
      (Or.inl he2) (fourLeafZero a b c d ha hb hc hd)

theorem target : fcTypeOfName% "Math15Catalog.source10" := by
  exact target10_of_doubleSpider_graceful all_double_spiders_graceful

end Bounty
end

namespace Bounty
