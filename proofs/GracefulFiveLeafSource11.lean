/- Proof body for Math15Catalog.source11. The verifier supplies its trusted
imports and surrounding namespace. -/
end Bounty

/- A proof of Math15Catalog.source11: trees with exactly three degree-three
vertices and all other degrees at most two admit graceful labelings. -/


/- Supporting module: H1Coverage -/

namespace H1Coverage

def U (a b : Nat) := a/2+b/2
def V (a b : Nat) := a+b-U a b
def Cut (a b d : Nat) := if d%2=0 then U a b+d/2 else V a b+d/2
def R (d c : Nat) := if d%2=1 then (d-1)/2+c/2 else d+c-((d-1)/2+c/2)-2

theorem big_tail_or_graft (a b d c : Nat) (ha : 1≤a) (hb : 1≤b)
    (hd : 1≤d) (hc : 2*d<c) (hnot : c<Cut a b d+1) :
    a+b > 2*R d c := by
  simp only [Cut, V, U, R] at *
  split_ifs at * <;> omega

theorem generic_finite_bound (q d c : Nat) (hd : 1≤d) (hd9 : d≤9)
    (hc : 1≤c) (hc2 : c≤2*d) (hnot : ¬ q>2*R d c) : q≤26 := by
  unfold R at hnot
  split_ifs at hnot <;> omega

theorem bad_path_outer_bound (a b : Nat) (ha : 1≤a) (hab : a≤b)
    (hnot : b<a/2+3) : a+b≤8 := by omega

def SmallShort (d c : Nat) :=
  if (c+1)/2=1 then 6≤d else 3*((c+1)/2)+1≤d

theorem q2_finite_bound (d c : Nat) (hd : 1≤d) (hc : 1≤c)
    (hnotlong : c<Cut 1 1 d+1) (hnotshort : ¬ SmallShort d c) :
    c≤9 ∧ d≤15 := by
  unfold SmallShort Cut U V at *
  split_ifs at * <;> omega

end H1Coverage


/- Supporting module: H1Outer -/

namespace H1Coverage

def OuterAvailable (a b d c : ℕ) : Prop :=
  ¬ (b+d=2 ∧ c=2) ∧
    (if d%2=0 then (b+d)/2+c/2 else b+d+c-((b+d)/2+c/2)) ≤ a

end H1Coverage


/- Supporting module: Foundation -/

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


/- Supporting module: Alpha -/

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
  simp [Math15.Graceful.reverseLabel_at_cut, normalizeHighLabel]

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
    simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, h, reverseLabel]
  · refine ⟨fun x => normalizeHighLabel (edgeCount G) k (f x),
      edgeCount G - k - 1, hf.normalizeHigh, ?_⟩
    simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, h, normalizeHighLabel]

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
  simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, shiftAboveCut]

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


/- Supporting module: SpiderCertificates -/


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
  loopless := ⟨by intro i; simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link]⟩

abbrev spiderAdjDecidable (L : ℕ) : DecidableRel (spider L).Adj := fun _ _ => inferInstanceAs
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
      norm_num [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link] at hj
    · intro hj
      by_contra hzero
      apply hj
      apply Fin.ext
      have : j.val = 0 := by omega
      simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link] using this
  have hcard : verts.card = L + 4 := by rw [hv]; simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link]
  calc
    _ = es.card := rfl
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

abbrev spiderCertificateDecidable (L : ℕ) (f : Fin (L+5) → ℕ) : Decidable (SpiderCertificate L f) := by
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


/- Supporting module: Prefix -/

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

/-- Insert the four-edge prefixExtension from Lemma 5 of the supplied manuscript. -/
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
  · interval_cases i <;> interval_cases j <;> simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, spiderPrefix] at heq ⊢
  · have htail := canonical_tail_bounds hf hc (j := j - 4) (by omega) (by omega)
    rw [spiderPrefix_tail (j := j) f (by omega)] at heq
    interval_cases i <;> simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, spiderPrefix] at heq <;> omega
  · have htail := canonical_tail_bounds hf hc (j := i - 4) (by omega) (by omega)
    rw [spiderPrefix_tail f (by omega)] at heq
    interval_cases j <;> simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, spiderPrefix] at heq <;> omega
  · rw [spiderPrefix_tail f (by omega), spiderPrefix_tail f (by omega)] at heq
    have := hf.1 (i - 4) (j - 4) (by omega) (by omega) (by omega)
    omega

lemma spiderPrefix_bound {L : ℕ} {f : ℕ → ℕ}
    (hf : NatSpiderCertificate L f) {i : ℕ} (hi : i < L + 9) :
    spiderPrefix L f i ≤ L + 8 := by
  by_cases hi9 : i < 9
  · interval_cases i <;> simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, spiderPrefix]
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
  · simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, spiderParent, spiderPrefix, hc.1]
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
    interval_cases j <;> simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, spiderParent, spiderPrefix, prefixOldEdge, hc0, hc1, hc2, hc3, hc4, Nat.dist]
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
  interval_cases j <;> simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, spiderParent, spiderPrefix, Nat.dist]

lemma spiderPrefix_low_edge {L j : ℕ} {f : ℕ → ℕ} (hL : 1 ≤ L)
    (hf : NatSpiderCertificate L f) (hc : CanonicalSpider L f)
    (hj : 5 ≤ j) (hb : j < L + 9) :
    Nat.dist (spiderPrefix L f (spiderParent j)) (spiderPrefix L f j) ≤ L + 4 := by
  rw [spiderPrefix_edge hc hj]
  exact hf.edge_bound (prefixOldEdge_bounds hL hj hb).2

lemma NatSpiderCertificate.prefixExtension {L : ℕ} {f : ℕ → ℕ} (hL : 1 ≤ L)
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
        simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, spiderParent, spiderPrefix, Nat.dist] at heq ⊢
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

lemma CanonicalSpider.prefixExtension {L : ℕ} {f : ℕ → ℕ} :
    CanonicalSpider (L + 4) (spiderPrefix L f) := by
  simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, CanonicalSpider, spiderPrefix]

lemma NatSpiderAlpha.prefixExtension {L k : ℕ} {f : ℕ → ℕ}
    (hc : CanonicalSpider L f) (hα : NatSpiderAlpha L f k)
    (hk0 : 2 ≤ k) (hk1 : k < L + 3) :
    NatSpiderAlpha (L + 4) (spiderPrefix L f) (k + 2) := by
  intro j hj hb
  by_cases h9 : j < 9
  · interval_cases j <;> simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, spiderParent, spiderPrefix] <;> omega
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

/-- Lemma 5: adding the four-edge prefixExtension increases the long leg and pin position by four. -/
theorem CanonicalPinnedSpider.prefixExtension {L d : ℕ} {f : ℕ → ℕ}
    (hL : 1 ≤ L) (hd : 1 ≤ d) (hf : CanonicalPinnedSpider L d f) :
    CanonicalPinnedSpider (L + 4) (d + 4) (spiderPrefix L f) := by
  refine ⟨hf.1.prefixExtension hL hf.2.1, CanonicalSpider.prefixExtension, ?_, spiderPrefix_pin hd hf.2.2.2⟩
  have ha := hf.2.2.1.prefixExtension hf.2.1 (by omega) (by omega)
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
  simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, extendSpiderLabel]

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
      ih.prefixExtension (by omega) (by omega)

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


/- Supporting module: PathAppend -/

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
  simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, appendSpiderLabels, hj]

lemma appendSpiderLabels_new {L k m j : ℕ} (f p : ℕ → ℕ) (hj : L + 5 ≤ j) :
    appendSpiderLabels L k m f p j = k + 1 + p (j - (L + 5)) := by
  simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, appendSpiderLabels, show ¬j < L + 5 by omega]

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
      (y := 1 + p (j - (L + 5))) (by omega)).1 (by simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Nat.add_assoc] using heq)
    omega
  · rw [appendSpiderLabels_new f p (by omega), appendSpiderLabels_old f p hj0] at heq
    have hpb := hp.2.1 (i - (L + 5)) (by omega)
    have hzero := (shiftAboveCut_eq_translate_iff (k := k) (m := m) (x := f j)
      (y := 1 + p (i - (L + 5))) (by omega)).1 (by simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Nat.add_assoc] using heq.symm)
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
  simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at]

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
  simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, shiftAboveCut]

end Bounty


/- Supporting module: EvenAlphaPath -/

namespace Bounty

/-- A bipartite graceful permutation of even length, with its two endpoints specified. -/
structure EvenAlphaPath (L k : ℕ) (p : ℕ → ℕ) : Prop where
  graceful : NatGracefulPath (2*L) p
  low_iff : ∀ i, i < 2*L → (p i < L ↔ i % 2 = 0)
  first : p 0 = k
  last : p (2*L-1) = L+k

lemma EvenAlphaPath.crosses {L k : ℕ} {p : ℕ → ℕ} (hp : EvenAlphaPath L k p)
    {j : ℕ} (hj : 0 < j) (hb : j < 2*L) :
    (p (j-1) < L ∧ L ≤ p j) ∨ (p j < L ∧ L ≤ p (j-1)) := by
  have h₁ := hp.low_iff (j-1) (by omega)
  have h₂ := hp.low_iff j hb
  omega

def evenWalecki (L i : ℕ) : ℕ := if i % 2 = 0 then i/2 else 2*L-1-i/2

lemma evenWalecki_bound {L i : ℕ} (hi : i < 2*L) : evenWalecki L i < 2*L := by
  unfold evenWalecki
  split_ifs <;> omega

lemma evenWalecki_low {L i : ℕ} (hi : i < 2*L) :
    evenWalecki L i < L ↔ i % 2 = 0 := by
  unfold evenWalecki
  split_ifs <;> omega

lemma evenWalecki_inj {L i j : ℕ} (hi : i < 2*L) (hj : j < 2*L)
    (h : evenWalecki L i = evenWalecki L j) : i = j := by
  unfold evenWalecki at h
  split_ifs at h <;> omega

lemma evenWalecki_diff {L i : ℕ} (hi : 0 < i) (hb : i < 2*L) :
    Nat.dist (evenWalecki L (i-1)) (evenWalecki L i) = 2*L-i := by
  unfold evenWalecki Nat.dist
  split_ifs <;> omega

lemma evenWalecki_path {L : ℕ} (hL : 0 < L) : EvenAlphaPath L 0 (evenWalecki L) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · exact fun _ _ => evenWalecki_inj
  · exact fun _ => evenWalecki_bound
  · intro i j hi hib hj hjb heq
    rw [evenWalecki_diff hi hib, evenWalecki_diff hj hjb] at heq
    omega
  · exact fun _ => evenWalecki_low
  · simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, evenWalecki]
  · unfold evenWalecki
    have : (2*L-1)%2 = 1 := by omega
    rw [ite_eq_right (by omega)]
    omega

/-- Reflection separately within the lower and upper halves. -/
def evenHalfReflect (L y : ℕ) : ℕ := if y < L then L-1-y else 3*L-1-y

lemma evenHalfReflect_bound {L y : ℕ} (hy : y < 2*L) : evenHalfReflect L y < 2*L := by
  unfold evenHalfReflect
  split_ifs <;> omega

lemma evenHalfReflect_low {L y : ℕ} (hy : y < 2*L) :
    evenHalfReflect L y < L ↔ y < L := by
  unfold evenHalfReflect
  split_ifs <;> omega

lemma evenHalfReflect_inj {L x y : ℕ} (hx : x < 2*L) (hy : y < 2*L)
    (heq : evenHalfReflect L x = evenHalfReflect L y) : x = y := by
  unfold evenHalfReflect at heq
  split_ifs at heq <;> omega

lemma evenHalfReflect_diff {L x y : ℕ} (hx : x < 2*L) (hy : y < 2*L)
    (hcross : (x < L ∧ L ≤ y) ∨ (y < L ∧ L ≤ x)) :
    Nat.dist (evenHalfReflect L x) (evenHalfReflect L y) = 2*L - Nat.dist x y := by
  unfold evenHalfReflect Nat.dist
  rcases hcross with hcross | hcross <;> split_ifs <;> omega

lemma EvenAlphaPath.reflect {L k : ℕ} {p : ℕ → ℕ} (hp : EvenAlphaPath L k p)
    (hk : k < L) : EvenAlphaPath L (L-1-k) (fun i => evenHalfReflect L (p i)) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro i j hi hj heq
    exact hp.graceful.1 i j hi hj (evenHalfReflect_inj (hp.graceful.2.1 _ hi)
      (hp.graceful.2.1 _ hj) heq)
  · intro i hi
    exact evenHalfReflect_bound (hp.graceful.2.1 _ hi)
  · intro i j hi hib hj hjb heq
    dsimp only at heq
    rw [evenHalfReflect_diff (hp.graceful.2.1 _ (by omega)) (hp.graceful.2.1 _ hib)
        (hp.crosses hi hib),
      evenHalfReflect_diff (hp.graceful.2.1 _ (by omega)) (hp.graceful.2.1 _ hjb)
        (hp.crosses hj hjb)] at heq
    have h₁ := hp.graceful.edge_lt hi hib
    have h₂ := hp.graceful.edge_lt hj hjb
    exact hp.graceful.2.2 i j hi hib hj hjb (by omega)
  · intro i hi
    exact (evenHalfReflect_low (hp.graceful.2.1 _ hi)).trans (hp.low_iff _ hi)
  · rw [hp.first]
    simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, evenHalfReflect, hk]
  · rw [hp.last]
    unfold evenHalfReflect
    rw [ite_eq_right (by omega)]
    omega

/-- Reverse the two halves of the Walecki ordering. -/
def middleEvenIndex (L i : ℕ) : ℕ := if i < L then L-1-i else 3*L-1-i

def middleEvenPath (L i : ℕ) : ℕ := evenWalecki L (middleEvenIndex L i)

lemma middleEvenIndex_bound {L i : ℕ} (hi : i < 2*L) : middleEvenIndex L i < 2*L := by
  unfold middleEvenIndex
  split_ifs <;> omega

lemma middleEvenIndex_inj {L i j : ℕ} (hi : i < 2*L) (hj : j < 2*L)
    (heq : middleEvenIndex L i = middleEvenIndex L j) : i = j := by
  unfold middleEvenIndex at heq
  split_ifs at heq <;> omega

lemma middleEvenPath_diff {L i : ℕ} (hi : 0 < i) (hb : i < 2*L) :
    Nat.dist (middleEvenPath L (i-1)) (middleEvenPath L i) =
      if i < L then L+i else if i = L then L else i-L := by
  by_cases hlt : i < L
  · have hprev : i-1 < L := by omega
    simp only [middleEvenPath, middleEvenIndex, ite_eq_left hlt, ite_eq_left hprev]
    have heq : L-1-(i-1) = L-i := by omega
    have heq' : L-1-i = (L-i)-1 := by omega
    rw [heq, heq', Nat.dist_comm, evenWalecki_diff (by omega) (by omega)]
    omega
  · by_cases heq : i = L
    · subst i
      have hL : 0 < L := hi
      simp only [middleEvenPath, middleEvenIndex, ite_eq_left (show L-1 < L by omega),
        ite_eq_right (show ¬L < L by omega)]
      have h₁ : L-1-(L-1) = 0 := by omega
      have h₂ : 3*L-1-L = 2*L-1 := by omega
      rw [h₁, h₂, (evenWalecki_path hL).first, (evenWalecki_path hL).last]
      simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Nat.dist]
    · have hprev : ¬i-1 < L := by omega
      simp only [middleEvenPath, middleEvenIndex, ite_eq_right hlt, ite_eq_right hprev, ite_eq_right heq]
      have heq₁ : 3*L-1-(i-1) = 3*L-i := by omega
      have heq₂ : 3*L-1-i = (3*L-i)-1 := by omega
      rw [heq₁, heq₂, Nat.dist_comm, evenWalecki_diff (by omega) (by omega)]
      omega

lemma middleEvenPath_alpha {L k : ℕ} (hL : L = 2*k+1) :
    EvenAlphaPath L k (middleEvenPath L) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro i j hi hj heq
    exact middleEvenIndex_inj hi hj (evenWalecki_inj
      (middleEvenIndex_bound hi) (middleEvenIndex_bound hj) heq)
  · intro i hi
    exact evenWalecki_bound (middleEvenIndex_bound hi)
  · intro i j hi hib hj hjb heq
    rw [middleEvenPath_diff hi hib, middleEvenPath_diff hj hjb] at heq
    split_ifs at heq <;> omega
  · intro i hi
    rw [middleEvenPath, evenWalecki_low (middleEvenIndex_bound hi)]
    unfold middleEvenIndex
    split_ifs <;> omega
  · unfold middleEvenPath middleEvenIndex evenWalecki
    split_ifs <;> omega
  · unfold middleEvenPath middleEvenIndex evenWalecki
    split_ifs <;> omega

/-- Put a recursively constructed path in the middle label interval, then
append the outermost pairs of a Walecki ordering. -/
def appendEvenPath (L k : ℕ) (p : ℕ → ℕ) (i : ℕ) : ℕ :=
  if i < 2*k then L-k+p i else evenWalecki L (i-2*k)

lemma appendEvenPath_diff {L k : ℕ} {p : ℕ → ℕ}
    (hk : k < L) (hhalf : L ≤ 2*k) (hp : EvenAlphaPath k (2*k-L) p)
    {i : ℕ} (hi : 0 < i) (hb : i < 2*L) :
    Nat.dist (appendEvenPath L k p (i-1)) (appendEvenPath L k p i) =
      if i < 2*k then Nat.dist (p (i-1)) (p i)
      else if i = 2*k then 2*k else 2*L+2*k-i := by
  by_cases hlt : i < 2*k
  · have hprev : i-1 < 2*k := by omega
    simp only [appendEvenPath, ite_eq_left hlt, ite_eq_left hprev]
    exact Math15.Graceful.translate_dist _ _ _
  · by_cases heq : i = 2*k
    · subst i
      have hprev : 2*k-1 < 2*k := by omega
      simp only [appendEvenPath, ite_eq_left hprev,
        ite_eq_right (show ¬2*k < 2*k by omega), ite_true, Nat.sub_self,
        evenWalecki, Nat.zero_mod, Nat.zero_div, hp.last]
      unfold Nat.dist
      omega
    · have hprev : ¬i-1 < 2*k := by omega
      simp only [appendEvenPath, ite_eq_right hlt, ite_eq_right hprev, ite_eq_right heq]
      have heq' : i-1-2*k = (i-2*k)-1 := by omega
      rw [heq', evenWalecki_diff (by omega) (by omega)]
      omega

lemma EvenAlphaPath.append {L k : ℕ} {p : ℕ → ℕ}
    (hk : k < L) (hhalf : L ≤ 2*k) (hp : EvenAlphaPath k (2*k-L) p) :
    EvenAlphaPath L k (appendEvenPath L k p) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro i j hi hj heq
    by_cases hlt : i < 2*k <;> by_cases hlt' : j < 2*k
    · simp only [appendEvenPath, ite_eq_left hlt, ite_eq_left hlt'] at heq
      exact hp.graceful.1 i j hlt hlt' (by omega)
    · have hpi := hp.graceful.2.1 i hlt
      simp only [appendEvenPath, ite_eq_left hlt, ite_eq_right hlt', evenWalecki] at heq
      split_ifs at heq <;> omega
    · have hpj := hp.graceful.2.1 j hlt'
      simp only [appendEvenPath, ite_eq_right hlt, ite_eq_left hlt', evenWalecki] at heq
      split_ifs at heq <;> omega
    · simp only [appendEvenPath, ite_eq_right hlt, ite_eq_right hlt'] at heq
      have := evenWalecki_inj (by omega : i-2*k < 2*L) (by omega : j-2*k < 2*L) heq
      omega
  · intro i hi
    by_cases hlt : i < 2*k
    · simp only [appendEvenPath, ite_eq_left hlt]
      have := hp.graceful.2.1 i hlt
      omega
    · simp only [appendEvenPath, ite_eq_right hlt]
      exact evenWalecki_bound (by omega)
  · intro i j hi hib hj hjb heq
    rw [appendEvenPath_diff hk hhalf hp hi hib,
      appendEvenPath_diff hk hhalf hp hj hjb] at heq
    by_cases hlt : i < 2*k <;> by_cases hlt' : j < 2*k
    · simp only [ite_eq_left hlt, ite_eq_left hlt'] at heq
      exact hp.graceful.2.2 i j hi hlt hj hlt' heq
    · have hsmall := hp.graceful.edge_lt hi hlt
      simp only [ite_eq_left hlt, ite_eq_right hlt'] at heq
      split_ifs at heq <;> omega
    · have hsmall := hp.graceful.edge_lt hj hlt'
      simp only [ite_eq_right hlt, ite_eq_left hlt'] at heq
      split_ifs at heq <;> omega
    · simp only [ite_eq_right hlt, ite_eq_right hlt'] at heq
      split_ifs at heq <;> omega
  · intro i hi
    by_cases hlt : i < 2*k
    · simp only [appendEvenPath, ite_eq_left hlt]
      have h := hp.low_iff i hlt
      omega
    · simp only [appendEvenPath, ite_eq_right hlt]
      rw [evenWalecki_low (by omega)]
      omega
  · simp only [appendEvenPath, ite_eq_left (show 0 < 2*k by omega), hp.first]
    omega
  · simp only [appendEvenPath, ite_eq_right (show ¬2*L-1 < 2*k by omega), evenWalecki]
    have hodd : (2*L-1-2*k)%2 = 1 := by omega
    rw [ite_eq_right (by omega)]
    omega

/-- Every even path has a bipartite graceful permutation starting at any chosen
lower-half label. The final label is larger by exactly half the number of vertices. -/
theorem exists_evenAlphaPath (L : ℕ) : ∀ k, k < L →
    ∃ p : ℕ → ℕ, EvenAlphaPath L k p := by
  induction L using Nat.strong_induction_on with
  | h L ih =>
    intro k hk
    have upper : ∀ a, a < L → L ≤ 2*a → ∃ p, EvenAlphaPath L a p := by
      intro a ha hhalf
      obtain ⟨p, hp⟩ := ih a ha (2*a-L) (by omega)
      exact ⟨appendEvenPath L a p, hp.append ha hhalf⟩
    by_cases hmiddle : L = 2*k+1
    · exact ⟨middleEvenPath L, middleEvenPath_alpha hmiddle⟩
    by_cases hhalf : L ≤ 2*k
    · exact upper k hk hhalf
    have hmirror : L-1-k < L := by omega
    obtain ⟨p, hp⟩ := upper (L-1-k) hmirror (by omega)
    have h := hp.reflect hmirror
    have heq : L-1-(L-1-k) = k := by omega
    rw [heq] at h
    exact ⟨fun i => evenHalfReflect L (p i), h⟩

/-- The expanded endpoint-and-cut form, convenient for splicing this path into
an existing alpha-labeled graph. -/
theorem exists_even_alpha_path {L k : ℕ} (hk : k < L) :
    ∃ p : ℕ → ℕ, NatGracefulPath (2*L) p ∧ p 0 = k ∧ p (2*L-1) = L+k ∧
      ∀ j, 0 < j → j < 2*L →
        (p (j-1) < L ∧ L ≤ p j) ∨ (p j < L ∧ L ≤ p (j-1)) := by
  obtain ⟨p, hp⟩ := exists_evenAlphaPath L k hk
  exact ⟨p, hp.graceful, hp.first, hp.last, fun _ hj hb => hp.crosses hj hb⟩

end Bounty


/- Supporting module: PathConstruction -/



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
  | nil => simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append]
  | cons x xs ih =>
    intro hp hq
    obtain ⟨ys, rfl⟩ := List.head?_eq_some_iff.mp hq
    cases xs with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at hp
      subst p
      rfl
    | cons y ys' =>
      have hp' : (y :: ys').getLast? = some p := by simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append] using hp
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
  simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, lowBag, List.range_succ]
theorem highBag_succ (n : ℕ) : highBag (n+1) = highBag n + {H n} := by
  simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, highBag, List.range_succ]
theorem rangeBag_succ (n : ℕ) : rangeBag (n+1) = rangeBag n + {n} := by
  simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, rangeBag, List.range_succ]

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

private theorem flat_PathConstruction_cycle_vertices (a b : ℕ) (P Q : List Symbol)
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
  refine ⟨⟨?_, ?_, ?_, flat_PathConstruction_cycle_vertices a b P Q h.vertices, ?_⟩, by omega, ?_, ?_, ?_⟩
  · simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, vhMain, List.head?_append, h.main_start]
  · rw [vhMain, List.isChain_append]
    simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, h.main_alternates, h.main_end, Opposite, List.isChain_cons]
  · simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, vhExtra, List.isChain_append, List.isChain_cons, h.extra_alternates,
      h.extra_start, h.extra_end, List.getLast?_append, Opposite]
  · rw [hmain, hextra]
    have he := congrArg (fun x : Multiset ℕ =>
      x + {a+b} + {a+b+1} + {a+b+2} + {a+b+3} + {a+b+4} + {a+b+5}) h.edges
    have hh : a+3+(b+3) = (a+b)+1+1+1+1+1+1 := by omega
    rw [hh]
    simp only [rangeBag_succ]
    convert he using 1 <;> ac_rfl
  · simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, vhMain, List.getLast?_append]
  · simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, vhExtra, List.head?_append]
  · change ([L (a+3), H (b+1)] ++ Q ++ [L (a+1), H (b+2)]).getLast? = some (H (b+3-1))
    rw [List.getLast?_append]
    simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ]


private theorem flat_PathConstruction_cycle_vertices_vl (a b : ℕ) (P Q : List Symbol)
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
  refine ⟨⟨?_, ?_, ?_, flat_PathConstruction_cycle_vertices_vl a b P Q h.vertices, ?_⟩, by omega, ?_, ?_, ?_⟩
  · simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, vlMain, List.head?_append, h.main_start]
  · rw [vlMain, List.isChain_append]
    simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, h.main_alternates, h.main_end, Opposite, List.isChain_cons]
  · simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, vlExtra, List.isChain_append, List.isChain_cons, h.extra_alternates,
      h.extra_start, h.extra_end, Opposite]
  · rw [hmain, hextra]
    have he := congrArg (fun x : Multiset ℕ =>
      x + {a+b} + {a+b+1} + {a+b+2} + {a+b+3} + {a+b+4} + {a+b+5}) h.edges
    have hh : a+3+(b+3) = (a+b)+1+1+1+1+1+1 := by omega
    rw [hh]
    simp only [rangeBag_succ]
    convert he using 1 <;> ac_rfl
  · simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, vlMain, List.getLast?_append]
  · simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, vlExtra]
  · change ([L (a+2), H (b+1)] ++ Q ++ [L (a+1), H (b+3)]).getLast? = some (H (b+3))
    rw [List.getLast?_append]
    rfl

theorem vh_cycles (t a b : ℕ) (P Q : List Symbol) (h : VH a b P Q) :
    ∃ P' Q', VH (a+3*t) (b+3*t) P' Q' ∧
      P'.length = P.length+2*t ∧ Q'.length = Q.length+4*t := by
  induction t with
  | zero => exact ⟨P, Q, by simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ] using h, by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ], by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ]⟩
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
  | zero => exact ⟨P, Q, by simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ] using h, by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ], by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ]⟩
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
      rw [List.reverse_cons, edgeSums_append _ _ y x (by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse]) rfl, ih]
      simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, edgeSums, Nat.add_comm]

theorem edgeBag_reverse (P : List Symbol) : edgeBag P.reverse = edgeBag P := by
  simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, edgeBag, edgeSums_reverse]

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
  · simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, List.head?_append, h.main_start]
  · rw [List.isChain_append]
    simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, h.main_alternates, h.extra_alternates, h.main_end, h.extra_start, Opposite]
  · simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse] using h.vertices
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
  · simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, List.head?_append, h.main_start]
  · rw [List.isChain_append]
    simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, h.main_alternates, h.extra_alternates, h.main_end, h.extra_end, Opposite]
  · simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse] using h.vertices
  · rw [edgeBag_append _ _ (L a) (H b) h.main_end (by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, h.extra_end])]
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
    simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, edgeBag, edgeSums, index, hh]
  have hfront : ([L (a+1)] ++ Q.reverse).getLast? = some (L a) := by
    rw [List.getLast?_append, List.getLast?_reverse, h.extra_start]
    rfl
  have hextra : edgeBag (halfExtra a b Q) = {a+b} + edgeBag Q + {a+b+1} := by
    rw [halfExtra, edgeBag_append _ _ (L a) (H (b+1)) hfront rfl]
    rw [edgeBag_append _ _ (L (a+1)) (H (b-1)) rfl (by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, h.extra_end])]
    have h1 : a+1+(b-1) = a+b := by omega
    have h2 : a+(b+1) = a+b+1 := by omega
    simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, edgeBag, edgeSums, index, edgeSums_reverse, h1, h2]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, by omega, ?_, ?_, ?_⟩
  · simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, List.head?_append, h.main_start]
  · rw [List.isChain_append]
    simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, h.main_alternates, h.main_end, Opposite]
  · rw [halfExtra, List.isChain_append]
    refine ⟨?_, by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse], ?_⟩
    · rw [List.isChain_append]
      simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, h.extra_alternates, h.extra_end, Opposite]
    · rw [hfront]
      simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Opposite]
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
  · simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse]
  · simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, halfExtra]
  · rw [halfExtra, List.getLast?_append]
    rfl

theorem vl_half (a b : ℕ) (P Q : List Symbol) (h : VL a b P Q) :
    VH (a+1) (b+2) (P ++ [H (b+2)]) (halfExtra a b Q) := by
  have hp := h.low_pos
  have hmain : edgeBag (P ++ [H (b+2)]) = edgeBag P + {a+b+2} := by
    rw [edgeBag_append _ _ (L a) (H (b+2)) h.main_end rfl]
    have hh : a+(b+2) = a+b+2 := by omega
    simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, edgeBag, edgeSums, index, hh]
  have hfront : ([L (a+1)] ++ Q.reverse).getLast? = some (L (a-1)) := by
    rw [List.getLast?_append, List.getLast?_reverse, h.extra_start]
    rfl
  have hextra : edgeBag (halfExtra a b Q) = {a+b+1} + edgeBag Q + {a+b} := by
    rw [halfExtra, edgeBag_append _ _ (L (a-1)) (H (b+1)) hfront rfl]
    rw [edgeBag_append _ _ (L (a+1)) (H b) rfl (by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, h.extra_end])]
    have h1 : a+1+b = a+b+1 := by omega
    have h2 : a-1+(b+1) = a+b := by omega
    simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, edgeBag, edgeSums, index, edgeSums_reverse, h1, h2]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, by omega, ?_, ?_, ?_⟩
  · simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, List.head?_append, h.main_start]
  · rw [List.isChain_append]
    simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, h.main_alternates, h.main_end, Opposite]
  · rw [halfExtra, List.isChain_append]
    refine ⟨?_, by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse], ?_⟩
    · rw [List.isChain_append]
      simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, h.extra_alternates, h.extra_end, Opposite]
    · rw [hfront]
      simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Opposite]
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
  · simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse]
  · simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, halfExtra]
  · rw [halfExtra, List.getLast?_append]
    simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse]


theorem vh_exit_short (a b : ℕ) (P Q : List Symbol) (h : VH a b P Q) :
    TL (a+1) b (P ++ [L (a+1)] ++ Q.reverse) := by
  have hp := h.high_pos
  have hend : (P ++ [L (a+1)]).getLast? = some (L (a+1)) := by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, by omega, ?_⟩
  · simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, List.head?_append, h.main_start]
  · rw [List.isChain_append]
    refine ⟨?_, by simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse] using h.extra_alternates, ?_⟩
    · rw [List.isChain_append]
      simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, h.main_alternates, h.main_end, Opposite]
    · simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, hend, h.extra_end, Opposite]
  · simp only [bag_append, bag_cons, bag_nil, add_zero, bag_reverse, lowBag_succ, highBag_succ]
    have hv := congrArg (fun x : Multiset Symbol => x + {L (a+1)}) h.vertices
    simp only [lowBag_succ, highBag_succ] at hv
    convert hv using 1 <;> ac_rfl
  · rw [edgeBag_append _ _ (L (a+1)) (H (b-1)) hend (by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, h.extra_end])]
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
    simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse]

theorem vl_exit_short (a b : ℕ) (P Q : List Symbol) (h : VL a b P Q) :
    TH a (b+1) (P ++ [H (b+1)] ++ Q) := by
  have hp := h.low_pos
  have hend : (P ++ [H (b+1)]).getLast? = some (H (b+1)) := by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, by omega, ?_⟩
  · simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, List.head?_append, h.main_start]
  · rw [List.isChain_append]
    refine ⟨?_, h.extra_alternates, ?_⟩
    · rw [List.isChain_append]
      simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, h.main_alternates, h.main_end, Opposite]
    · simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, hend, h.extra_start, Opposite]
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
    simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse]

theorem tl_enter (a b : ℕ) (P : List Symbol) (h : TL a b P) :
    VH (a+1) (b+2) (P ++ [H (b+2)]) [L (a+1), H (b+1)] := by
  have hp := h.low_pos
  refine ⟨⟨?_, ?_, by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, List.isChain_cons, Opposite], ?_, ?_⟩, by omega, by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse], rfl, ?_⟩
  · simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, List.head?_append, h.main_start]
  · rw [List.isChain_append]
    simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, h.alternates, h.main_end, Opposite]
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
  · simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse]

theorem th_enter (a b : ℕ) (P : List Symbol) (h : TH a b P) :
    VL (a+2) (b+1) (P ++ [L (a+2)]) [L (a+1), H (b+1)] := by
  have hp := h.high_pos
  refine ⟨⟨?_, ?_, by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, List.isChain_cons, Opposite], ?_, ?_⟩, by omega, by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse], ?_, rfl⟩
  · simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, List.head?_append, h.main_start]
  · rw [List.isChain_append]
    simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, h.alternates, h.main_end, Opposite]
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
  · simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse]

theorem tl_extend (a b : ℕ) (P : List Symbol) (h : TL a b P) :
    TL (a+2) (b+2) (P ++ [H (b+2), L (a+2), H (b+1), L (a+1)]) := by
  simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, List.append_assoc] using vh_exit_short _ _ _ _ (tl_enter a b P h)

theorem th_extend (a b : ℕ) (P : List Symbol) (h : TH a b P) :
    TH (a+2) (b+2) (P ++ [L (a+2), H (b+2), L (a+1), H (b+1)]) := by
  simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, List.append_assoc] using vl_exit_short _ _ _ _ (th_enter a b P h)


theorem Terminal.length {a b : ℕ} {P : List Symbol} (h : Terminal a b P) :
    P.length = a+b+2 := by
  have hv := congrArg Multiset.card h.vertices
  simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, bag, lowBag, highBag, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hv

theorem Terminal.vertex_perm {a b : ℕ} {P : List Symbol} (h : Terminal a b P) :
    P.Perm ((List.range (a+1)).map L ++ (List.range (b+1)).map H) := by
  apply Multiset.coe_eq_coe.mp
  simpa only [lowBag, highBag, bag, Multiset.coe_add] using h.vertices

theorem Terminal.edge_perm {a b : ℕ} {P : List Symbol} (h : Terminal a b P) :
    (edgeSums P).Perm (List.range (a+b+1)) := Multiset.coe_eq_coe.mp h.edges

theorem tl_extend_many (t a b : ℕ) (P : List Symbol) (h : TL a b P) :
    ∃ P', TL (a+2*t) (b+2*t) P' ∧ P'.length = P.length+4*t := by
  induction t with
  | zero => exact ⟨P, by simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse] using h, by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse]⟩
  | succ t ih =>
    obtain ⟨P', hi, hp⟩ := ih
    refine ⟨P' ++ [H (b+2*t+2), L (a+2*t+2), H (b+2*t+1), L (a+2*t+1)], ?_, ?_⟩
    · convert tl_extend _ _ _ hi using 1 <;> omega
    · simp only [List.length_append, List.length_cons, List.length_nil, hp]
      omega

theorem th_extend_many (t a b : ℕ) (P : List Symbol) (h : TH a b P) :
    ∃ P', TH (a+2*t) (b+2*t) P' ∧ P'.length = P.length+4*t := by
  induction t with
  | zero => exact ⟨P, by simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse] using h, by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse]⟩
  | succ t ih =>
    obtain ⟨P', hi, hp⟩ := ih
    refine ⟨P' ++ [L (a+2*t+2), H (b+2*t+2), L (a+2*t+1), H (b+2*t+1)], ?_, ?_⟩
    · convert th_extend _ _ _ hi using 1 <;> omega
    · simp only [List.length_append, List.length_cons, List.length_nil, hp]
      omega

theorem base3 : TL 1 0 [L 1, H 0, L 0] := by
  refine ⟨⟨rfl, by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, List.isChain_cons, Opposite], by decide, by decide⟩, by decide, rfl⟩
theorem base4 : TH 1 1 [L 1, H 1, L 0, H 0] := by
  refine ⟨⟨rfl, by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, List.isChain_cons, Opposite], by decide, by decide⟩, by decide, rfl⟩
theorem base6 : TH 2 2 [L 1, H 0, L 0, H 2, L 2, H 1] := by
  refine ⟨⟨rfl, by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, List.isChain_cons, Opposite], by decide, by decide⟩, by decide, rfl⟩
theorem base9 : TL 4 3 [L 1, H 0, L 0, H 2, L 2, H 1, L 4, H 3, L 3] := by
  refine ⟨⟨rfl, by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, List.isChain_cons, Opposite], by decide, by decide⟩, by decide, rfl⟩

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
  | nil => simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse] using h.main_start
  | cons x xs => simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse]

def HasLow (n k : ℕ) : Prop :=
  ∃ a b P, Terminal a b P ∧ P.length = n ∧ P[k]? = some (L a)
def HasHigh (n k : ℕ) : Prop :=
  ∃ a b P, Terminal a b P ∧ P.length = n ∧ P[k]? = some (H b)

theorem vh_low_direct {a b : ℕ} {P Q : List Symbol} (h : VH a b P Q) :
    HasLow (P.length+Q.length) P.length := by
  refine ⟨a,b,P++Q,(vh_exit _ _ _ _ h).toTerminal, by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse], ?_⟩
  simpa only [get_append_boundary] using h.extra_start

theorem vh_high_direct {a b : ℕ} {P Q : List Symbol} (h : VH a b P Q) :
    HasHigh (P.length+Q.length) (P.length-1) := by
  refine ⟨a,b,P++Q,(vh_exit _ _ _ _ h).toTerminal, by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse], ?_⟩
  simpa only [get_append_last _ _ h.toCore.main_pos] using h.main_end

theorem vl_low_direct {a b : ℕ} {P Q : List Symbol} (h : VL a b P Q) :
    HasLow (P.length+Q.length) (P.length-1) := by
  refine ⟨a,b,P++Q.reverse,(vl_exit _ _ _ _ h).toTerminal, by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse], ?_⟩
  simpa only [get_append_last _ _ h.toCore.main_pos] using h.main_end

theorem vl_high_direct {a b : ℕ} {P Q : List Symbol} (h : VL a b P Q) :
    HasHigh (P.length+Q.length) P.length := by
  refine ⟨a,b,P++Q.reverse,(vl_exit _ _ _ _ h).toTerminal, by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse], ?_⟩
  simpa only [get_append_boundary, List.head?_reverse] using h.extra_end

theorem vl_low_short {a b : ℕ} {P Q : List Symbol} (h : VL a b P Q) :
    HasLow (P.length+Q.length+1) (P.length-1) := by
  refine ⟨a,b+1,P++[H (b+1)]++Q,(vl_exit_short _ _ _ _ h).toTerminal, ?_, ?_⟩
  · simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse]; omega
  · rw [List.append_assoc, get_append_last _ _ h.toCore.main_pos]
    exact h.main_end

theorem vl_high_short {a b : ℕ} {P Q : List Symbol} (h : VL a b P Q) :
    HasHigh (P.length+Q.length+1) P.length := by
  refine ⟨a,b+1,P++[H (b+1)]++Q,(vl_exit_short _ _ _ _ h).toTerminal, ?_, ?_⟩
  · simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse]; omega
  · rw [List.append_assoc, get_append_boundary]
    rfl

theorem vh_high_short {a b : ℕ} {P Q : List Symbol} (h : VH a b P Q) :
    HasHigh (P.length+Q.length+1) (P.length-1) := by
  refine ⟨a+1,b,P++[L (a+1)]++Q.reverse,(vh_exit_short _ _ _ _ h).toTerminal, ?_, ?_⟩
  · simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse]; omega
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
  · simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, hlen] using hP
  · simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse] using hQ

theorem prepared_even (n t : ℕ) (hn : 6 ≤ n) (ho : n%2 = 0) :
    ∃ a b P Q, VL a b P Q ∧ P.length = n+1+2*t ∧ Q.length = 2+4*t := by
  obtain ⟨a,b,P,h,hlen⟩ := starting_even n hn ho
  obtain ⟨P',Q',h',hP,hQ⟩ := vl_cycles t _ _ _ _ (th_enter a b P h)
  refine ⟨_,_,P',Q',h',?_,?_⟩
  · simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, hlen] using hP
  · simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse] using hQ


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


/- Supporting module: NumericConstruction -/



namespace Bounty.PathConstruction

private theorem flat_NumericConstruction_highCount_low (P : List Symbol) :
    P.IsChain Opposite → (∀ i, P.head? ≠ some (H i)) →
    (P.filter Sum.isRight).length = P.length/2 := by
  induction P using List.twoStepInduction with
  | nil => simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse]
  | singleton x =>
    intro hc hh
    cases x with
    | inl i => simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse]
    | inr i => exact False.elim (hh i rfl)
  | cons_cons x y xs ih _ =>
    intro hc hh
    cases x with
    | inr i => exact False.elim (hh i rfl)
    | inl i =>
      cases y with
      | inl j => simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, List.isChain_cons_cons, Opposite] at hc
      | inr j =>
        have hct : xs.IsChain Opposite := ((List.isChain_cons_cons.mp hc).2).tail
        have hht : ∀ k, xs.head? ≠ some (H k) := by
          intro k hk
          have hr := (List.isChain_cons.mp (List.isChain_cons_cons.mp hc).2).1 (H k) (by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, hk])
          simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Opposite] using hr
        have ht := ih hct hht
        simp only [List.filter_cons, Sum.isRight_inl, Sum.isRight_inr, Bool.false_eq_true,
          ite_false, ite_true, List.length_cons]
        omega

theorem Terminal.high_size {a b : ℕ} {P : List Symbol} (h : Terminal a b P) :
    b+1 = P.length/2 := by
  have hc := flat_NumericConstruction_highCount_low P h.alternates (by intro i; simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, h.main_start])
  have hv := (h.vertex_perm.filter Sum.isRight).length_eq
  simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, List.filter_map, Function.comp_def] at hv
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
  cases s <;> simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse] using hm

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
    symbolAt P i = P[i] := by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, symbolAt, List.getElem?_eq_getElem hi]

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
    | cons y ys => simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, edgeSums] using ih

theorem edgeSums_get (P : List Symbol) (i : ℕ) (hi : i+1 < P.length) :
    (edgeSums P)[i]? = some (sumAt P i) := by
  induction P generalizing i with
  | nil => simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse] at hi
  | cons x xs ih =>
    cases xs with
    | nil => simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse] at hi
    | cons y ys =>
      cases i with
      | zero => rfl
      | succ i =>
        simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, edgeSums, sumAt, symbolAt, Nat.add_assoc] using ih i (by simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse] using hi)

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
  simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, CanonicalSpider, pathSpiderLabel, h.main_start, tailLabel]

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
  · interval_cases i <;> interval_cases j <;> simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, pathSpiderLabel] at heq ⊢ <;> omega
  · have hb := pathSpiderLabel_tail_bounds h hn j (by omega) hj
    rw [pathSpiderLabel_tail n P j (by omega)] at heq hb
    interval_cases i <;> simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, pathSpiderLabel] at heq <;> omega
  · have hb := pathSpiderLabel_tail_bounds h hn i (by omega) hi
    rw [pathSpiderLabel_tail n P i (by omega)] at heq hb
    interval_cases j <;> simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, pathSpiderLabel] at heq <;> omega
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
  · interval_cases i <;> simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, pathSpiderLabel]
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
  interval_cases j <;> simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, spiderParent, pathSpiderLabel, h.main_start, tailLabel, Nat.dist]

theorem pathSpiderLabel_edges_injective {a b n : ℕ} {P : List Symbol}
    (h : Terminal a b P) (hn : P.length = n) (hsize : 3 ≤ n)
    (i j : ℕ) (hi : 0 < i) (hib : i < n+5) (hj : 0 < j) (hjb : j < n+5)
    (heq : Nat.dist (pathSpiderLabel n P (spiderParent i)) (pathSpiderLabel n P i) =
      Nat.dist (pathSpiderLabel n P (spiderParent j)) (pathSpiderLabel n P j)) : i = j := by
  by_cases hi6 : i < 6 <;> by_cases hj6 : j < 6
  · interval_cases i <;> interval_cases j <;>
      simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, spiderParent, pathSpiderLabel, h.main_start, tailLabel, Nat.dist] at heq ⊢ <;> omega
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
  · interval_cases j <;> simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, spiderParent, pathSpiderLabel, h.main_start, tailLabel] <;> omega
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


/- Supporting module: AlphaPath -/


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
  have hi : P[a]? = some (if low then L A else H B) := by simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, low] using hpin
  simp only [boundaryPath, symbolAt, hi, Option.getD_some]
  cases low <;> simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, boundaryLabel]

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
  · simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, reverseNatPath] using hpin


def pathPred {n : ℕ} (i : Fin n) : Fin n := ⟨i.val-1, (Nat.sub_le _ _).trans_lt i.isLt⟩

def FiniteAlphaPath (n : ℕ) (p : Fin n → ℕ) (k : ℕ) : Prop :=
  Function.Injective p ∧ (∀ i, p i < n) ∧
  (∀ i j : Fin n, 0 < i.val → 0 < j.val →
    Nat.dist (p (pathPred i)) (p i) = Nat.dist (p (pathPred j)) (p j) → i = j) ∧
  k < n-1 ∧ ∀ j : Fin n, 0 < j.val →
    (p (pathPred j) ≤ k ∧ k < p j) ∨ (p j ≤ k ∧ k < p (pathPred j))

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

private theorem flat_AlphaPath_alphaCase_1_1 : ZeroAlphaPath 1 1 := by
  let p : Fin 3 → ℕ := ![1, 0, 2]
  have hp : FiniteAlphaPath 3 p 0 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 0, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_13_13 : ZeroAlphaPath 13 13 := by
  let p : Fin 27 → ℕ := ![15, 12, 13, 11, 16, 10, 14, 7, 21, 5, 22, 3, 23, 0, 26, 1, 25, 4, 19, 6, 17, 9, 18, 8, 20, 2, 24]
  have hp : FiniteAlphaPath 27 p 12 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 12, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_1_2 : ZeroAlphaPath 1 2 := by
  let p : Fin 4 → ℕ := ![3, 0, 2, 1]
  have hp : FiniteAlphaPath 4 p 1 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 1, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_1_3 : ZeroAlphaPath 1 3 := by
  let p : Fin 5 → ℕ := ![4, 0, 3, 1, 2]
  have hp : FiniteAlphaPath 5 p 1 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 1, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_2_3 : ZeroAlphaPath 2 3 := by
  let p : Fin 6 → ℕ := ![1, 5, 0, 3, 2, 4]
  have hp : FiniteAlphaPath 6 p 2 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 2, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_3_3 : ZeroAlphaPath 3 3 := by
  let p : Fin 7 → ℕ := ![4, 2, 3, 0, 6, 1, 5]
  have hp : FiniteAlphaPath 7 p 2 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 2, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_1_4 : ZeroAlphaPath 1 4 := by
  let p : Fin 6 → ℕ := ![5, 0, 4, 1, 3, 2]
  have hp : FiniteAlphaPath 6 p 2 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 2, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_2_4 : ZeroAlphaPath 2 4 := by
  let p : Fin 7 → ℕ := ![2, 6, 0, 5, 3, 4, 1]
  have hp : FiniteAlphaPath 7 p 3 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 3, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_3_4 : ZeroAlphaPath 3 4 := by
  let p : Fin 8 → ℕ := ![6, 1, 7, 0, 4, 3, 5, 2]
  have hp : FiniteAlphaPath 8 p 3 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 3, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_4_4 : ZeroAlphaPath 4 4 := by
  let p : Fin 9 → ℕ := ![3, 5, 4, 7, 0, 8, 2, 6, 1]
  have hp : FiniteAlphaPath 9 p 4 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 4, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_1_5 : ZeroAlphaPath 1 5 := by
  let p : Fin 7 → ℕ := ![6, 0, 5, 1, 4, 2, 3]
  have hp : FiniteAlphaPath 7 p 2 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 2, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_2_5 : ZeroAlphaPath 2 5 := by
  let p : Fin 8 → ℕ := ![1, 6, 0, 7, 3, 4, 2, 5]
  have hp : FiniteAlphaPath 8 p 3 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 3, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_3_5 : ZeroAlphaPath 3 5 := by
  let p : Fin 9 → ℕ := ![7, 2, 6, 0, 8, 1, 4, 3, 5]
  have hp : FiniteAlphaPath 9 p 3 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 3, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_4_5 : ZeroAlphaPath 4 5 := by
  let p : Fin 10 → ℕ := ![2, 8, 1, 9, 0, 5, 4, 6, 3, 7]
  have hp : FiniteAlphaPath 10 p 4 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 4, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_5_5 : ZeroAlphaPath 5 5 := by
  let p : Fin 11 → ℕ := ![8, 2, 6, 1, 9, 0, 10, 3, 5, 4, 7]
  have hp : FiniteAlphaPath 11 p 4 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 4, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_1_6 : ZeroAlphaPath 1 6 := by
  let p : Fin 8 → ℕ := ![7, 0, 6, 1, 5, 2, 4, 3]
  have hp : FiniteAlphaPath 8 p 3 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 3, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_2_6 : ZeroAlphaPath 2 6 := by
  let p : Fin 9 → ℕ := ![1, 8, 0, 6, 2, 7, 4, 5, 3]
  have hp : FiniteAlphaPath 9 p 4 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 4, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_3_6 : ZeroAlphaPath 3 6 := by
  let p : Fin 10 → ℕ := ![7, 1, 8, 0, 9, 4, 5, 3, 6, 2]
  have hp : FiniteAlphaPath 10 p 4 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 4, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_4_6 : ZeroAlphaPath 4 6 := by
  let p : Fin 11 → ℕ := ![2, 9, 1, 10, 0, 6, 5, 7, 4, 8, 3]
  have hp : FiniteAlphaPath 11 p 5 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 5, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_5_6 : ZeroAlphaPath 5 6 := by
  let p : Fin 12 → ℕ := ![9, 1, 8, 2, 11, 0, 10, 5, 6, 4, 7, 3]
  have hp : FiniteAlphaPath 12 p 5 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 5, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_6_6 : ZeroAlphaPath 6 6 := by
  let p : Fin 13 → ℕ := ![1, 10, 4, 9, 2, 12, 0, 11, 3, 7, 6, 8, 5]
  have hp : FiniteAlphaPath 13 p 6 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 6, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_1_7 : ZeroAlphaPath 1 7 := by
  let p : Fin 9 → ℕ := ![7, 0, 8, 2, 6, 1, 4, 3, 5]
  have hp : FiniteAlphaPath 9 p 3 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 3, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_2_7 : ZeroAlphaPath 2 7 := by
  let p : Fin 10 → ℕ := ![1, 9, 0, 7, 3, 8, 2, 5, 4, 6]
  have hp : FiniteAlphaPath 10 p 4 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 4, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_3_7 : ZeroAlphaPath 3 7 := by
  let p : Fin 11 → ℕ := ![9, 1, 10, 0, 7, 3, 8, 2, 5, 4, 6]
  have hp : FiniteAlphaPath 11 p 4 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 4, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_4_7 : ZeroAlphaPath 4 7 := by
  let p : Fin 12 → ℕ := ![3, 6, 5, 7, 0, 11, 1, 10, 2, 8, 4, 9]
  have hp : FiniteAlphaPath 12 p 5 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 5, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_5_7 : ZeroAlphaPath 5 7 := by
  let p : Fin 13 → ℕ := ![7, 5, 6, 3, 10, 0, 12, 1, 9, 4, 8, 2, 11]
  have hp : FiniteAlphaPath 13 p 5 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 5, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_6_7 : ZeroAlphaPath 6 7 := by
  let p : Fin 14 → ℕ := ![5, 8, 6, 7, 3, 11, 0, 13, 1, 10, 4, 9, 2, 12]
  have hp : FiniteAlphaPath 14 p 6 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 6, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_7_7 : ZeroAlphaPath 7 7 := by
  let p : Fin 15 → ℕ := ![8, 6, 7, 4, 11, 1, 14, 0, 12, 3, 9, 5, 10, 2, 13]
  have hp : FiniteAlphaPath 15 p 6 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 6, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_1_8 : ZeroAlphaPath 1 8 := by
  let p : Fin 10 → ℕ := ![8, 0, 9, 2, 5, 4, 6, 1, 7, 3]
  have hp : FiniteAlphaPath 10 p 4 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 4, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_2_8 : ZeroAlphaPath 2 8 := by
  let p : Fin 11 → ℕ := ![1, 9, 0, 10, 3, 7, 2, 8, 5, 6, 4]
  have hp : FiniteAlphaPath 11 p 5 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 5, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_3_8 : ZeroAlphaPath 3 8 := by
  let p : Fin 12 → ℕ := ![8, 3, 11, 0, 10, 1, 7, 4, 6, 5, 9, 2]
  have hp : FiniteAlphaPath 12 p 5 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 5, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_4_8 : ZeroAlphaPath 4 8 := by
  let p : Fin 13 → ℕ := ![4, 9, 1, 12, 0, 10, 3, 7, 6, 8, 5, 11, 2]
  have hp : FiniteAlphaPath 13 p 6 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 6, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_5_8 : ZeroAlphaPath 5 8 := by
  let p : Fin 14 → ℕ := ![9, 4, 10, 1, 13, 0, 11, 3, 7, 6, 8, 5, 12, 2]
  have hp : FiniteAlphaPath 14 p 6 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 6, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_6_8 : ZeroAlphaPath 6 8 := by
  let p : Fin 15 → ℕ := ![1, 12, 4, 11, 2, 14, 0, 13, 3, 9, 5, 10, 7, 8, 6]
  have hp : FiniteAlphaPath 15 p 7 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 7, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_7_8 : ZeroAlphaPath 7 8 := by
  let p : Fin 16 → ℕ := ![10, 7, 8, 6, 12, 3, 15, 0, 14, 1, 11, 4, 9, 5, 13, 2]
  have hp : FiniteAlphaPath 16 p 7 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 7, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_8_8 : ZeroAlphaPath 8 8 := by
  let p : Fin 17 → ℕ := ![1, 14, 4, 11, 6, 12, 3, 15, 0, 16, 2, 13, 5, 9, 8, 10, 7]
  have hp : FiniteAlphaPath 17 p 8 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 8, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_1_9 : ZeroAlphaPath 1 9 := by
  let p : Fin 11 → ℕ := ![8, 0, 10, 1, 6, 2, 9, 3, 5, 4, 7]
  have hp : FiniteAlphaPath 11 p 4 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 4, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_2_9 : ZeroAlphaPath 2 9 := by
  let p : Fin 12 → ℕ := ![3, 11, 0, 10, 1, 6, 5, 7, 4, 8, 2, 9]
  have hp : FiniteAlphaPath 12 p 5 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 5, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_3_9 : ZeroAlphaPath 3 9 := by
  let p : Fin 13 → ℕ := ![8, 3, 12, 0, 11, 1, 7, 4, 6, 5, 9, 2, 10]
  have hp : FiniteAlphaPath 13 p 5 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 5, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_4_9 : ZeroAlphaPath 4 9 := by
  let p : Fin 14 → ℕ := ![4, 12, 1, 13, 0, 10, 6, 7, 5, 8, 3, 9, 2, 11]
  have hp : FiniteAlphaPath 14 p 6 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 6, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_5_9 : ZeroAlphaPath 5 9 := by
  let p : Fin 15 → ℕ := ![12, 1, 11, 4, 13, 0, 14, 2, 10, 6, 7, 5, 8, 3, 9]
  have hp : FiniteAlphaPath 15 p 6 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 6, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_6_9 : ZeroAlphaPath 6 9 := by
  let p : Fin 16 → ℕ := ![1, 13, 4, 11, 3, 14, 0, 15, 2, 12, 6, 10, 5, 8, 7, 9]
  have hp : FiniteAlphaPath 16 p 7 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 7, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_7_9 : ZeroAlphaPath 7 9 := by
  let p : Fin 17 → ℕ := ![10, 7, 8, 6, 12, 1, 15, 0, 16, 3, 13, 5, 9, 4, 11, 2, 14]
  have hp : FiniteAlphaPath 17 p 7 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 7, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_8_9 : ZeroAlphaPath 8 9 := by
  let p : Fin 18 → ℕ := ![1, 15, 4, 12, 5, 14, 2, 17, 0, 16, 3, 13, 7, 9, 8, 11, 6, 10]
  have hp : FiniteAlphaPath 18 p 8 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 8, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_9_9 : ZeroAlphaPath 9 9 := by
  let p : Fin 19 → ℕ := ![15, 1, 16, 3, 13, 5, 14, 2, 18, 0, 17, 6, 9, 8, 10, 4, 11, 7, 12]
  have hp : FiniteAlphaPath 19 p 8 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 8, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_1_10 : ZeroAlphaPath 1 10 := by
  let p : Fin 12 → ℕ := ![11, 0, 10, 1, 9, 2, 8, 3, 7, 4, 6, 5]
  have hp : FiniteAlphaPath 12 p 5 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 5, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_2_10 : ZeroAlphaPath 2 10 := by
  let p : Fin 13 → ℕ := ![4, 9, 0, 12, 1, 11, 5, 8, 6, 7, 3, 10, 2]
  have hp : FiniteAlphaPath 13 p 6 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 6, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_3_10 : ZeroAlphaPath 3 10 := by
  let p : Fin 14 → ℕ := ![9, 1, 12, 0, 13, 3, 7, 6, 8, 5, 10, 4, 11, 2]
  have hp : FiniteAlphaPath 14 p 6 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 6, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_4_10 : ZeroAlphaPath 4 10 := by
  let p : Fin 15 → ℕ := ![1, 12, 2, 14, 0, 13, 4, 11, 3, 9, 5, 10, 7, 8, 6]
  have hp : FiniteAlphaPath 15 p 7 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 7, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_5_10 : ZeroAlphaPath 5 10 := by
  let p : Fin 16 → ℕ := ![10, 4, 11, 1, 14, 0, 15, 3, 12, 7, 8, 6, 9, 5, 13, 2]
  have hp : FiniteAlphaPath 16 p 7 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 7, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_6_10 : ZeroAlphaPath 6 10 := by
  let p : Fin 17 → ℕ := ![1, 14, 4, 13, 2, 16, 0, 15, 3, 11, 6, 12, 5, 9, 8, 10, 7]
  have hp : FiniteAlphaPath 17 p 8 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 8, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_7_10 : ZeroAlphaPath 7 10 := by
  let p : Fin 18 → ℕ := ![11, 5, 12, 4, 14, 3, 17, 0, 16, 1, 13, 8, 9, 7, 10, 6, 15, 2]
  have hp : FiniteAlphaPath 18 p 8 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 8, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_8_10 : ZeroAlphaPath 8 10 := by
  let p : Fin 19 → ℕ := ![1, 16, 4, 13, 5, 15, 2, 18, 0, 17, 3, 14, 7, 10, 9, 11, 6, 12, 8]
  have hp : FiniteAlphaPath 19 p 9 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 9, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_9_10 : ZeroAlphaPath 9 10 := by
  let p : Fin 20 → ℕ := ![16, 8, 12, 7, 10, 9, 11, 5, 17, 0, 19, 1, 15, 2, 18, 3, 14, 4, 13, 6]
  have hp : FiniteAlphaPath 20 p 9 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 9, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_10_10 : ZeroAlphaPath 10 10 := by
  let p : Fin 21 → ℕ := ![1, 18, 4, 15, 7, 14, 5, 17, 2, 20, 0, 19, 3, 16, 6, 12, 8, 13, 10, 11, 9]
  have hp : FiniteAlphaPath 21 p 10 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 10, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_1_11 : ZeroAlphaPath 1 11 := by
  let p : Fin 13 → ℕ := ![8, 0, 12, 1, 11, 2, 6, 5, 7, 4, 9, 3, 10]
  have hp : FiniteAlphaPath 13 p 5 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 5, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_2_11 : ZeroAlphaPath 2 11 := by
  let p : Fin 14 → ℕ := ![3, 13, 0, 12, 1, 9, 5, 8, 6, 7, 2, 11, 4, 10]
  have hp : FiniteAlphaPath 14 p 6 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 6, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_3_11 : ZeroAlphaPath 3 11 := by
  let p : Fin 15 → ℕ := ![9, 1, 13, 0, 14, 3, 8, 5, 7, 6, 10, 4, 11, 2, 12]
  have hp : FiniteAlphaPath 15 p 6 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 6, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_4_11 : ZeroAlphaPath 4 11 := by
  let p : Fin 16 → ℕ := ![5, 10, 1, 14, 0, 15, 3, 11, 4, 8, 7, 9, 6, 12, 2, 13]
  have hp : FiniteAlphaPath 16 p 7 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 7, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_5_11 : ZeroAlphaPath 5 11 := by
  let p : Fin 17 → ℕ := ![14, 1, 13, 2, 16, 0, 15, 5, 8, 7, 9, 4, 11, 3, 12, 6, 10]
  have hp : FiniteAlphaPath 17 p 7 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 7, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_6_11 : ZeroAlphaPath 6 11 := by
  let p : Fin 18 → ℕ := ![1, 15, 4, 14, 2, 17, 0, 16, 3, 12, 5, 13, 7, 9, 8, 11, 6, 10]
  have hp : FiniteAlphaPath 18 p 8 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 8, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_7_11 : ZeroAlphaPath 7 11 := by
  let p : Fin 19 → ℕ := ![14, 8, 9, 7, 10, 6, 11, 0, 18, 1, 17, 2, 16, 3, 15, 5, 12, 4, 13]
  have hp : FiniteAlphaPath 19 p 8 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 8, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_8_11 : ZeroAlphaPath 8 11 := by
  let p : Fin 20 → ℕ := ![1, 17, 4, 14, 5, 16, 2, 19, 0, 18, 3, 15, 7, 12, 6, 13, 9, 10, 8, 11]
  have hp : FiniteAlphaPath 20 p 9 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 9, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_9_11 : ZeroAlphaPath 9 11 := by
  let p : Fin 21 → ℕ := ![18, 4, 14, 5, 11, 7, 15, 3, 16, 0, 20, 1, 19, 2, 17, 6, 13, 8, 10, 9, 12]
  have hp : FiniteAlphaPath 21 p 9 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 9, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_10_11 : ZeroAlphaPath 10 11 := by
  let p : Fin 22 → ℕ := ![5, 15, 8, 12, 7, 13, 10, 11, 9, 18, 0, 21, 1, 20, 3, 19, 4, 17, 6, 14, 2, 16]
  have hp : FiniteAlphaPath 22 p 10 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 10, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_11_11 : ZeroAlphaPath 11 11 := by
  let p : Fin 23 → ℕ := ![13, 10, 11, 9, 15, 8, 12, 7, 18, 3, 22, 0, 21, 1, 17, 4, 16, 6, 14, 5, 19, 2, 20]
  have hp : FiniteAlphaPath 23 p 10 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 10, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_1_12 : ZeroAlphaPath 1 12 := by
  let p : Fin 14 → ℕ := ![11, 0, 13, 1, 10, 5, 8, 6, 7, 3, 9, 2, 12, 4]
  have hp : FiniteAlphaPath 14 p 6 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 6, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_2_12 : ZeroAlphaPath 2 12 := by
  let p : Fin 15 → ℕ := ![5, 12, 0, 14, 1, 11, 3, 8, 7, 9, 6, 10, 4, 13, 2]
  have hp : FiniteAlphaPath 15 p 7 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 7, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_3_12 : ZeroAlphaPath 3 12 := by
  let p : Fin 16 → ℕ := ![11, 1, 15, 0, 13, 4, 12, 6, 10, 5, 8, 7, 9, 2, 14, 3]
  have hp : FiniteAlphaPath 16 p 7 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 7, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_4_12 : ZeroAlphaPath 4 12 := by
  let p : Fin 17 → ℕ := ![1, 14, 3, 15, 0, 16, 2, 12, 5, 13, 4, 10, 8, 9, 6, 11, 7]
  have hp : FiniteAlphaPath 17 p 8 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 8, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_5_12 : ZeroAlphaPath 5 12 := by
  let p : Fin 18 → ℕ := ![12, 1, 15, 2, 17, 0, 16, 4, 14, 5, 13, 7, 11, 6, 9, 8, 10, 3]
  have hp : FiniteAlphaPath 18 p 8 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 8, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_6_12 : ZeroAlphaPath 6 12 := by
  let p : Fin 19 → ℕ := ![1, 16, 4, 15, 2, 18, 0, 17, 3, 13, 7, 10, 9, 11, 6, 14, 5, 12, 8]
  have hp : FiniteAlphaPath 19 p 9 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 9, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_7_12 : ZeroAlphaPath 7 12 := by
  let p : Fin 20 → ℕ := ![16, 3, 14, 4, 18, 2, 17, 0, 19, 1, 13, 5, 11, 9, 10, 7, 12, 8, 15, 6]
  have hp : FiniteAlphaPath 20 p 9 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 9, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_8_12 : ZeroAlphaPath 8 12 := by
  let p : Fin 21 → ℕ := ![1, 18, 4, 15, 5, 17, 2, 20, 0, 19, 3, 16, 7, 12, 8, 14, 6, 13, 10, 11, 9]
  have hp : FiniteAlphaPath 21 p 10 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 10, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_9_12 : ZeroAlphaPath 9 12 := by
  let p : Fin 22 → ℕ := ![18, 5, 13, 9, 12, 10, 11, 6, 16, 0, 21, 1, 20, 2, 19, 4, 15, 3, 17, 8, 14, 7]
  have hp : FiniteAlphaPath 22 p 10 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 10, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_10_12 : ZeroAlphaPath 10 12 := by
  let p : Fin 23 → ℕ := ![10, 13, 11, 12, 8, 16, 5, 19, 2, 22, 0, 21, 3, 18, 6, 15, 9, 14, 7, 17, 4, 20, 1]
  have hp : FiniteAlphaPath 23 p 11 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 11, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_11_12 : ZeroAlphaPath 11 12 := by
  let p : Fin 24 → ℕ := ![14, 11, 12, 10, 15, 7, 13, 9, 16, 4, 20, 0, 23, 1, 22, 5, 19, 6, 17, 8, 18, 3, 21, 2]
  have hp : FiniteAlphaPath 24 p 11 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 11, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_12_12 : ZeroAlphaPath 12 12 := by
  let p : Fin 25 → ℕ := ![7, 15, 9, 16, 6, 17, 12, 13, 11, 14, 10, 19, 0, 24, 1, 23, 2, 22, 4, 18, 3, 20, 8, 21, 5]
  have hp : FiniteAlphaPath 25 p 12 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 12, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_1_13 : ZeroAlphaPath 1 13 := by
  let p : Fin 15 → ℕ := ![12, 0, 14, 1, 11, 4, 13, 2, 10, 6, 7, 5, 8, 3, 9]
  have hp : FiniteAlphaPath 15 p 6 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 6, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_2_13 : ZeroAlphaPath 2 13 := by
  let p : Fin 16 → ℕ := ![5, 12, 0, 15, 1, 14, 4, 10, 6, 9, 7, 8, 3, 11, 2, 13]
  have hp : FiniteAlphaPath 16 p 7 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 7, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_3_13 : ZeroAlphaPath 3 13 := by
  let p : Fin 17 → ℕ := ![15, 1, 16, 0, 13, 4, 11, 3, 14, 2, 12, 6, 10, 5, 8, 7, 9]
  have hp : FiniteAlphaPath 17 p 7 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 7, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_4_13 : ZeroAlphaPath 4 13 := by
  let p : Fin 18 → ℕ := ![6, 13, 3, 14, 0, 17, 1, 16, 4, 12, 8, 9, 7, 10, 5, 11, 2, 15]
  have hp : FiniteAlphaPath 18 p 8 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 8, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_5_13 : ZeroAlphaPath 5 13 := by
  let p : Fin 19 → ℕ := ![14, 2, 16, 1, 17, 0, 18, 5, 11, 8, 9, 7, 12, 4, 15, 6, 10, 3, 13]
  have hp : FiniteAlphaPath 19 p 8 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 8, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_6_13 : ZeroAlphaPath 6 13 := by
  let p : Fin 20 → ℕ := ![1, 17, 4, 15, 3, 18, 0, 19, 2, 16, 6, 12, 9, 10, 8, 13, 5, 14, 7, 11]
  have hp : FiniteAlphaPath 20 p 9 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 9, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_7_13 : ZeroAlphaPath 7 13 := by
  let p : Fin 21 → ℕ := ![13, 8, 12, 6, 16, 2, 20, 0, 19, 4, 11, 9, 10, 7, 15, 3, 14, 5, 18, 1, 17]
  have hp : FiniteAlphaPath 21 p 9 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 9, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_8_13 : ZeroAlphaPath 8 13 := by
  let p : Fin 22 → ℕ := ![6, 12, 10, 11, 8, 16, 5, 19, 0, 21, 1, 18, 3, 15, 2, 20, 4, 13, 9, 14, 7, 17]
  have hp : FiniteAlphaPath 22 p 10 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 10, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_9_13 : ZeroAlphaPath 9 13 := by
  let p : Fin 23 → ℕ := ![12, 9, 11, 10, 14, 6, 17, 3, 20, 0, 22, 1, 19, 4, 16, 7, 13, 8, 15, 5, 18, 2, 21]
  have hp : FiniteAlphaPath 23 p 10 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 10, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_10_13 : ZeroAlphaPath 10 13 := by
  let p : Fin 24 → ℕ := ![1, 21, 4, 18, 7, 17, 5, 20, 2, 23, 0, 22, 3, 19, 6, 15, 8, 16, 10, 12, 11, 14, 9, 13]
  have hp : FiniteAlphaPath 24 p 11 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 11, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_11_13 : ZeroAlphaPath 11 13 := by
  let p : Fin 25 → ℕ := ![15, 9, 14, 10, 13, 11, 12, 5, 20, 1, 23, 0, 24, 3, 17, 8, 16, 6, 19, 7, 18, 2, 22, 4, 21]
  have hp : FiniteAlphaPath 25 p 11 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 11, hp.toNat, rfl⟩

private theorem flat_AlphaPath_alphaCase_12_13 : ZeroAlphaPath 12 13 := by
  let p : Fin 26 → ℕ := ![10, 15, 11, 14, 12, 13, 7, 17, 6, 22, 3, 25, 0, 24, 1, 21, 4, 19, 5, 18, 9, 16, 8, 20, 2, 23]
  have hp : FiniteAlphaPath 26 p 12 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 12, hp.toNat, rfl⟩

private theorem flat_AlphaPath_zeroAlphaPath_small_1 (a : ℕ) (ha : 1 ≤ a)
    (hab : a ≤ 1) (hex : a ≠ 2 ∨ 1 ≠ 2) : ZeroAlphaPath a 1 := by
  interval_cases a <;> first
    | omega
    | exact flat_AlphaPath_alphaCase_1_1

private theorem flat_AlphaPath_zeroAlphaPath_small_2 (a : ℕ) (ha : 1 ≤ a)
    (hab : a ≤ 2) (hex : a ≠ 2 ∨ 2 ≠ 2) : ZeroAlphaPath a 2 := by
  interval_cases a <;> first
    | omega
    | exact flat_AlphaPath_alphaCase_1_2

private theorem flat_AlphaPath_zeroAlphaPath_small_3 (a : ℕ) (ha : 1 ≤ a)
    (hab : a ≤ 3) (hex : a ≠ 2 ∨ 3 ≠ 2) : ZeroAlphaPath a 3 := by
  interval_cases a <;> first
    | omega
    | exact flat_AlphaPath_alphaCase_1_3
    | exact flat_AlphaPath_alphaCase_2_3
    | exact flat_AlphaPath_alphaCase_3_3

private theorem flat_AlphaPath_zeroAlphaPath_small_4 (a : ℕ) (ha : 1 ≤ a)
    (hab : a ≤ 4) (hex : a ≠ 2 ∨ 4 ≠ 2) : ZeroAlphaPath a 4 := by
  interval_cases a <;> first
    | omega
    | exact flat_AlphaPath_alphaCase_1_4
    | exact flat_AlphaPath_alphaCase_2_4
    | exact flat_AlphaPath_alphaCase_3_4
    | exact flat_AlphaPath_alphaCase_4_4

private theorem flat_AlphaPath_zeroAlphaPath_small_5 (a : ℕ) (ha : 1 ≤ a)
    (hab : a ≤ 5) (hex : a ≠ 2 ∨ 5 ≠ 2) : ZeroAlphaPath a 5 := by
  interval_cases a <;> first
    | omega
    | exact flat_AlphaPath_alphaCase_1_5
    | exact flat_AlphaPath_alphaCase_2_5
    | exact flat_AlphaPath_alphaCase_3_5
    | exact flat_AlphaPath_alphaCase_4_5
    | exact flat_AlphaPath_alphaCase_5_5

private theorem flat_AlphaPath_zeroAlphaPath_small_6 (a : ℕ) (ha : 1 ≤ a)
    (hab : a ≤ 6) (hex : a ≠ 2 ∨ 6 ≠ 2) : ZeroAlphaPath a 6 := by
  interval_cases a <;> first
    | omega
    | exact flat_AlphaPath_alphaCase_1_6
    | exact flat_AlphaPath_alphaCase_2_6
    | exact flat_AlphaPath_alphaCase_3_6
    | exact flat_AlphaPath_alphaCase_4_6
    | exact flat_AlphaPath_alphaCase_5_6
    | exact flat_AlphaPath_alphaCase_6_6

private theorem flat_AlphaPath_zeroAlphaPath_small_7 (a : ℕ) (ha : 1 ≤ a)
    (hab : a ≤ 7) (hex : a ≠ 2 ∨ 7 ≠ 2) : ZeroAlphaPath a 7 := by
  interval_cases a <;> first
    | omega
    | exact flat_AlphaPath_alphaCase_1_7
    | exact flat_AlphaPath_alphaCase_2_7
    | exact flat_AlphaPath_alphaCase_3_7
    | exact flat_AlphaPath_alphaCase_4_7
    | exact flat_AlphaPath_alphaCase_5_7
    | exact flat_AlphaPath_alphaCase_6_7
    | exact flat_AlphaPath_alphaCase_7_7

private theorem flat_AlphaPath_zeroAlphaPath_small_8 (a : ℕ) (ha : 1 ≤ a)
    (hab : a ≤ 8) (hex : a ≠ 2 ∨ 8 ≠ 2) : ZeroAlphaPath a 8 := by
  interval_cases a <;> first
    | omega
    | exact flat_AlphaPath_alphaCase_1_8
    | exact flat_AlphaPath_alphaCase_2_8
    | exact flat_AlphaPath_alphaCase_3_8
    | exact flat_AlphaPath_alphaCase_4_8
    | exact flat_AlphaPath_alphaCase_5_8
    | exact flat_AlphaPath_alphaCase_6_8
    | exact flat_AlphaPath_alphaCase_7_8
    | exact flat_AlphaPath_alphaCase_8_8

private theorem flat_AlphaPath_zeroAlphaPath_small_9 (a : ℕ) (ha : 1 ≤ a)
    (hab : a ≤ 9) (hex : a ≠ 2 ∨ 9 ≠ 2) : ZeroAlphaPath a 9 := by
  interval_cases a <;> first
    | omega
    | exact flat_AlphaPath_alphaCase_1_9
    | exact flat_AlphaPath_alphaCase_2_9
    | exact flat_AlphaPath_alphaCase_3_9
    | exact flat_AlphaPath_alphaCase_4_9
    | exact flat_AlphaPath_alphaCase_5_9
    | exact flat_AlphaPath_alphaCase_6_9
    | exact flat_AlphaPath_alphaCase_7_9
    | exact flat_AlphaPath_alphaCase_8_9
    | exact flat_AlphaPath_alphaCase_9_9

private theorem flat_AlphaPath_zeroAlphaPath_small_10 (a : ℕ) (ha : 1 ≤ a)
    (hab : a ≤ 10) (hex : a ≠ 2 ∨ 10 ≠ 2) : ZeroAlphaPath a 10 := by
  interval_cases a <;> first
    | omega
    | exact flat_AlphaPath_alphaCase_1_10
    | exact flat_AlphaPath_alphaCase_2_10
    | exact flat_AlphaPath_alphaCase_3_10
    | exact flat_AlphaPath_alphaCase_4_10
    | exact flat_AlphaPath_alphaCase_5_10
    | exact flat_AlphaPath_alphaCase_6_10
    | exact flat_AlphaPath_alphaCase_7_10
    | exact flat_AlphaPath_alphaCase_8_10
    | exact flat_AlphaPath_alphaCase_9_10
    | exact flat_AlphaPath_alphaCase_10_10

private theorem flat_AlphaPath_zeroAlphaPath_small_11 (a : ℕ) (ha : 1 ≤ a)
    (hab : a ≤ 11) (hex : a ≠ 2 ∨ 11 ≠ 2) : ZeroAlphaPath a 11 := by
  interval_cases a <;> first
    | omega
    | exact flat_AlphaPath_alphaCase_1_11
    | exact flat_AlphaPath_alphaCase_2_11
    | exact flat_AlphaPath_alphaCase_3_11
    | exact flat_AlphaPath_alphaCase_4_11
    | exact flat_AlphaPath_alphaCase_5_11
    | exact flat_AlphaPath_alphaCase_6_11
    | exact flat_AlphaPath_alphaCase_7_11
    | exact flat_AlphaPath_alphaCase_8_11
    | exact flat_AlphaPath_alphaCase_9_11
    | exact flat_AlphaPath_alphaCase_10_11
    | exact flat_AlphaPath_alphaCase_11_11

private theorem flat_AlphaPath_zeroAlphaPath_small_12 (a : ℕ) (ha : 1 ≤ a)
    (hab : a ≤ 12) (hex : a ≠ 2 ∨ 12 ≠ 2) : ZeroAlphaPath a 12 := by
  interval_cases a <;> first
    | omega
    | exact flat_AlphaPath_alphaCase_1_12
    | exact flat_AlphaPath_alphaCase_2_12
    | exact flat_AlphaPath_alphaCase_3_12
    | exact flat_AlphaPath_alphaCase_4_12
    | exact flat_AlphaPath_alphaCase_5_12
    | exact flat_AlphaPath_alphaCase_6_12
    | exact flat_AlphaPath_alphaCase_7_12
    | exact flat_AlphaPath_alphaCase_8_12
    | exact flat_AlphaPath_alphaCase_9_12
    | exact flat_AlphaPath_alphaCase_10_12
    | exact flat_AlphaPath_alphaCase_11_12
    | exact flat_AlphaPath_alphaCase_12_12

private theorem flat_AlphaPath_zeroAlphaPath_small_13 (a : ℕ) (ha : 1 ≤ a)
    (hab : a ≤ 13) (hex : a ≠ 2 ∨ 13 ≠ 2) : ZeroAlphaPath a 13 := by
  interval_cases a <;> first
    | omega
    | exact flat_AlphaPath_alphaCase_1_13
    | exact flat_AlphaPath_alphaCase_2_13
    | exact flat_AlphaPath_alphaCase_3_13
    | exact flat_AlphaPath_alphaCase_4_13
    | exact flat_AlphaPath_alphaCase_5_13
    | exact flat_AlphaPath_alphaCase_6_13
    | exact flat_AlphaPath_alphaCase_7_13
    | exact flat_AlphaPath_alphaCase_8_13
    | exact flat_AlphaPath_alphaCase_9_13
    | exact flat_AlphaPath_alphaCase_10_13
    | exact flat_AlphaPath_alphaCase_11_13
    | exact flat_AlphaPath_alphaCase_12_13
    | exact flat_AlphaPath_alphaCase_13_13

private theorem flat_AlphaPath_zeroAlphaPath_small (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hab : a ≤ b) (hb13 : b ≤ 13) (hex : a ≠ 2 ∨ b ≠ 2) : ZeroAlphaPath a b := by
  interval_cases b
  · exact flat_AlphaPath_zeroAlphaPath_small_1 a ha hab hex
  · exact flat_AlphaPath_zeroAlphaPath_small_2 a ha hab hex
  · exact flat_AlphaPath_zeroAlphaPath_small_3 a ha hab hex
  · exact flat_AlphaPath_zeroAlphaPath_small_4 a ha hab hex
  · exact flat_AlphaPath_zeroAlphaPath_small_5 a ha hab hex
  · exact flat_AlphaPath_zeroAlphaPath_small_6 a ha hab hex
  · exact flat_AlphaPath_zeroAlphaPath_small_7 a ha hab hex
  · exact flat_AlphaPath_zeroAlphaPath_small_8 a ha hab hex
  · exact flat_AlphaPath_zeroAlphaPath_small_9 a ha hab hex
  · exact flat_AlphaPath_zeroAlphaPath_small_10 a ha hab hex
  · exact flat_AlphaPath_zeroAlphaPath_small_11 a ha hab hex
  · exact flat_AlphaPath_zeroAlphaPath_small_12 a ha hab hex
  · exact flat_AlphaPath_zeroAlphaPath_small_13 a ha hab hex

/-- Rosa's prescribed-zero alpha-path theorem, derived here from the symbolic
construction and explicit finite certificates. The exceptional central P5
corresponds exactly to arm lengths (2,2). -/
theorem rosa_zero_alpha_path (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hex : a ≠ 2 ∨ b ≠ 2) : ZeroAlphaPath a b := by
  by_cases hab : a ≤ b
  · by_cases hb14 : 14 ≤ b
    · exact (zeroAlphaPath_large_left b a hb14 ha hab).symm
    · exact flat_AlphaPath_zeroAlphaPath_small a b ha hb hab (by omega) hex
  · by_cases ha14 : 14 ≤ a
    · exact zeroAlphaPath_large_left a b ha14 hb (by omega)
    · exact (flat_AlphaPath_zeroAlphaPath_small b a hb ha (by omega) (by omega) hex.symm).symm

end Bounty


/- Supporting module: CattellEndpoint -/

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
  root_label := by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, P.top_label]
  top_lt := P.root_lt
  top_label := by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, P.root_label]
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
  simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, evenLift, hi, hb, binaryLabel, hz]

lemma evenLift_top {s r : ℕ} {p : ℕ → ℕ} (hz : p r = 0) :
    evenLift s p (2*r+(1-r%2)) = 2*s-1 := by
  have hi : (2*r+(1-r%2))/2 = r := by omega
  have hb : evenSide (2*r+(1-r%2)) = false := by
    simp only [evenSide, decide_eq_false_iff_not]
    omega
  simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, evenLift, hi, hb, binaryLabel, hz]

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
  simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, SupportedPath.double, SupportedPath.start, evenLift, evenSide, binaryLabel]

lemma SupportedPath.double_parity {s : ℕ} (P : SupportedPath s) :
    P.double.parity = P.parity := by
  dsimp [SupportedPath.double, SupportedPath.parity]
  omega

lemma oddLift_root {s r : ℕ} {p : ℕ → ℕ} (hz : p r = 0) :
    oddLift s p r (2*r) = 0 := by
  have hi : oddIndex r (2*r) = r := by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, oddIndex]
  have hb : oddSide r (2*r) = true := by
    simp only [oddSide, hi, decide_eq_true_eq]
    omega
  simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, oddLift, hi, hb, binaryLabel, hz]

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
  simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, oddLift, hi, hb, binaryLabel, ht]

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
  have hi : oddIndex P.root 0 = 0 := by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, oddIndex]
  have hb : oddSide P.root 0 = true := by
    simp only [oddSide, hi, Nat.zero_mod, zero_add, decide_eq_true_eq]
    exact he.symm
  simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, SupportedPath.oddDouble, SupportedPath.start, oddLift, hi, hb, binaryLabel]

lemma SupportedPath.oddDouble_start_odd {s : ℕ} (P : SupportedPath s) (hs : 1 < s)
    (he : P.parity = 1) : (P.oddDouble hs).start = 2*s-1-2*P.start := by
  have hi : oddIndex P.root 0 = 0 := by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, oddIndex]
  have hb : oddSide P.root 0 = false := by
    simp only [oddSide, hi, Nat.zero_mod, zero_add, decide_eq_false_iff_not]
    dsimp [SupportedPath.parity] at he
    omega
  simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, SupportedPath.oddDouble, SupportedPath.start, oddLift, hi, hb, binaryLabel]

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
  have he' : P.parity = 1 := by simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero] using he
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


/- Supporting module: CattellPath -/


namespace Bounty

/-- A finite certificate for an ordinary graceful permutation. -/
def FiniteGracefulPath (n : ℕ) (p : Fin n → ℕ) : Prop :=
  Function.Injective p ∧ (∀ i, p i < n) ∧
  ∀ i j : Fin n, 0 < i.val → 0 < j.val →
    Nat.dist (p (pathPred i)) (p i) = Nat.dist (p (pathPred j)) (p j) → i = j

lemma FiniteGracefulPath.toNat {n : ℕ} {p : Fin n → ℕ}
    (h : FiniteGracefulPath n p) : NatGracefulPath n (finitePathLabel p) := by
  refine ⟨?_, ?_, ?_⟩
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
    exact congrArg Fin.val (h.2.2 ⟨i,hib⟩ ⟨j,hjb⟩ hi hj heq)

lemma NatGracefulPath.reverse {n : ℕ} {p : ℕ → ℕ} (h : NatGracefulPath n p) :
    NatGracefulPath n (reverseNatPath n p) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j hi hj heq
    have hh := h.1 (n-1-i) (n-1-j) (by omega) (by omega) heq
    omega
  · intro i hi
    exact h.2.1 _ (by omega)
  · intro i j hi hib hj hjb heq
    have h1 : n-1-(i-1) = n-i := by omega
    have h2 : n-1-i = n-i-1 := by omega
    have h3 : n-1-(j-1) = n-j := by omega
    have h4 : n-1-j = n-j-1 := by omega
    simp only [reverseNatPath, h1, h2, h3, h4] at heq
    have hs : Nat.dist (p (n-i-1)) (p (n-i)) = Nat.dist (p (n-j-1)) (p (n-j)) := by
      simpa only [Nat.dist_comm] using heq
    have hij := h.2.2 (n-i) (n-j) (by omega) (by omega) (by omega) (by omega) hs
    omega

/-- Rosa's prescribed-zero theorem, including endpoints and the ordinary graceful
labeling at the central vertex of the exceptional alpha path on five vertices. -/
theorem exists_graceful_path_zero {n i : ℕ} (hi : i < n) :
    ∃ p, NatGracefulPath n p ∧ p i = 0 := by
  by_cases hzero : i=0
  · subst i
    exact exists_graceful_path_endpoint hi
  by_cases hlast : i=n-1
  · obtain ⟨p,hp,hpin⟩ := exists_graceful_path_endpoint (show 0<n by omega)
    refine ⟨reverseNatPath n p,hp.reverse,?_⟩
    simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, reverseNatPath,hlast] using hpin
  by_cases hex : i=2 ∧ n-1-i=2
  · have hn : n=5 := by omega
    obtain ⟨rfl,_⟩ := hex
    subst n
    let p : Fin 5 → ℕ := ![1,4,0,2,3]
    have hp : FiniteGracefulPath 5 p := by
      unfold FiniteGracefulPath Function.Injective
      decide
    exact ⟨finitePathLabel p,hp.toNat,rfl⟩
  obtain ⟨p,k,hp,hpin⟩ := rosa_zero_alpha_path i (n-1-i) (by omega) (by omega)
    (by tauto)
  have heq : i+(n-1-i)+1=n := by omega
  rw [heq] at hp
  exact ⟨p,hp.1,hpin⟩

/-- A prescribed value in a smaller path doubles at either vertex replacing it.
Complementing the result selects which member of the complementary pair is used. -/
theorem exists_graceful_path_double_even {s i t : ℕ} (hi : i < 2*s)
    (h : ∃ p, NatGracefulPath s p ∧ p (i/2)=t) :
    ∃ p, NatGracefulPath (2*s) p ∧ p i=2*t := by
  obtain ⟨p,hp,hpin⟩ := h
  have ht := hp.2.1 (i/2) (by omega)
  rw [hpin] at ht
  by_cases hs : evenSide i=true
  · refine ⟨evenLift s p,hp.evenLift,?_⟩
    simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, evenLift,binaryLabel,hs,hpin]
  · refine ⟨fun j => 2*s-1-evenLift s p j,hp.evenLift.complement,?_⟩
    simp only [evenLift,binaryLabel,hs,hpin, Bool.false_eq_true, ↓reduceIte]
    omega

/-- The complementary odd value is equally available. -/
theorem exists_graceful_path_double_odd {s i t : ℕ} (hi : i < 2*s)
    (h : ∃ p, NatGracefulPath s p ∧ p (i/2)=t) :
    ∃ p, NatGracefulPath (2*s) p ∧ p i=2*s-1-2*t := by
  obtain ⟨p,hp,hpin⟩ := exists_graceful_path_double_even hi h
  exact ⟨fun j => 2*s-1-p j,hp.complement,by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, hpin]⟩

/-- Every marked vertex of an even-order path can receive label one. -/
theorem exists_graceful_even_path_one {s i : ℕ} (hi : i < 2*s) :
    ∃ p, NatGracefulPath (2*s) p ∧ p i=1 := by
  obtain ⟨p,hp,hpin⟩ := exists_graceful_path_zero (show i/2<s by omega)
  have h : ∃ p, NatGracefulPath s p ∧ p (i/2)=s-1 :=
    ⟨fun j => s-1-p j,hp.complement,by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, hpin]⟩
  obtain ⟨p,hp,hpin⟩ := exists_graceful_path_double_odd hi h
  exact ⟨p,hp,by omega⟩

/-- In particular label two is available at every vertex when the order is
a multiple of four. -/
theorem exists_graceful_four_path_two {s i : ℕ} (hi : i < 4*s) :
    ∃ p, NatGracefulPath (4*s) p ∧ p i=2 := by
  have hi' : i < 2*(2*s) := by omega
  have h := exists_graceful_path_double_even hi'
    (exists_graceful_even_path_one (show i/2 < 2*s by omega))
  simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, show 2*(2*s)=4*s by omega] using h

end Bounty


/- Supporting module: OddAlphaEndpoint -/


namespace Bounty

structure OddAlphaPath (L k : ℕ) (p : ℕ → ℕ) : Prop where
  graceful : NatGracefulPath (2*L+1) p
  low_iff : ∀ i, i < 2*L+1 → (p i ≤ L ↔ i%2=0)
  first : p 0=k
  last : p (2*L)=L-k

def oddWalecki (L i : ℕ) : ℕ := if i%2=0 then i/2 else 2*L-i/2

lemma oddWalecki_bound {L i : ℕ} (hi : i < 2*L+1) : oddWalecki L i < 2*L+1 := by
  unfold oddWalecki
  split_ifs <;> omega

lemma oddWalecki_low {L i : ℕ} (hi : i < 2*L+1) :
    oddWalecki L i ≤ L ↔ i%2=0 := by
  unfold oddWalecki
  split_ifs <;> omega

lemma oddWalecki_inj {L i j : ℕ} (hi : i < 2*L+1) (hj : j < 2*L+1)
    (h : oddWalecki L i=oddWalecki L j) : i=j := by
  unfold oddWalecki at h
  split_ifs at h <;> omega

lemma oddWalecki_diff {L i : ℕ} (hi : 0 < i) (hb : i < 2*L+1) :
    Nat.dist (oddWalecki L (i-1)) (oddWalecki L i)=2*L+1-i := by
  unfold oddWalecki Nat.dist
  split_ifs <;> omega

def appendOddPath (L k : ℕ) (p : ℕ → ℕ) (i : ℕ) : ℕ :=
  if i < 2*k then L-k+1+p i else oddWalecki L (i-2*k)

lemma appendOddPath_diff {L k : ℕ} {p : ℕ → ℕ}
    (hk : k ≤ L) (hhalf : L < 2*k) (hp : EvenAlphaPath k (2*k-L-1) p)
    {i : ℕ} (hi : 0 < i) (hb : i < (2*L+1)) :
    Nat.dist (appendOddPath L k p (i-1)) (appendOddPath L k p i) =
      if i < 2*k then Nat.dist (p (i-1)) (p i)
      else if i = 2*k then 2*k else (2*L+1)+2*k-i := by
  by_cases hlt : i < 2*k
  · have hprev : i-1 < 2*k := by omega
    simp only [appendOddPath, ite_eq_left hlt, ite_eq_left hprev]
    exact Math15.Graceful.translate_dist _ _ _
  · by_cases heq : i = 2*k
    · subst i
      have hprev : 2*k-1 < 2*k := by omega
      simp only [appendOddPath, ite_eq_left hprev,
        ite_eq_right (show ¬2*k < 2*k by omega), ite_true, Nat.sub_self,
        oddWalecki, Nat.zero_mod, Nat.zero_div, hp.last]
      unfold Nat.dist
      omega
    · have hprev : ¬i-1 < 2*k := by omega
      simp only [appendOddPath, ite_eq_right hlt, ite_eq_right hprev, ite_eq_right heq]
      have heq' : i-1-2*k = (i-2*k)-1 := by omega
      rw [heq', oddWalecki_diff (by omega) (by omega)]
      omega

lemma appendOddPath_alpha {L k : ℕ} {p : ℕ → ℕ}
    (hk : k ≤ L) (hhalf : L < 2*k) (hp : EvenAlphaPath k (2*k-L-1) p) :
    OddAlphaPath L k (appendOddPath L k p) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro i j hi hj heq
    by_cases hlt : i < 2*k <;> by_cases hlt' : j < 2*k
    · simp only [appendOddPath, ite_eq_left hlt, ite_eq_left hlt'] at heq
      exact hp.graceful.1 i j hlt hlt' (by omega)
    · have hpi := hp.graceful.2.1 i hlt
      simp only [appendOddPath, ite_eq_left hlt, ite_eq_right hlt', oddWalecki] at heq
      split_ifs at heq <;> omega
    · have hpj := hp.graceful.2.1 j hlt'
      simp only [appendOddPath, ite_eq_right hlt, ite_eq_left hlt', oddWalecki] at heq
      split_ifs at heq <;> omega
    · simp only [appendOddPath, ite_eq_right hlt, ite_eq_right hlt'] at heq
      have := oddWalecki_inj (by omega : i-2*k < (2*L+1)) (by omega : j-2*k < (2*L+1)) heq
      omega
  · intro i hi
    by_cases hlt : i < 2*k
    · simp only [appendOddPath, ite_eq_left hlt]
      have := hp.graceful.2.1 i hlt
      omega
    · simp only [appendOddPath, ite_eq_right hlt]
      exact oddWalecki_bound (by omega)
  · intro i j hi hib hj hjb heq
    rw [appendOddPath_diff hk hhalf hp hi hib,
      appendOddPath_diff hk hhalf hp hj hjb] at heq
    by_cases hlt : i < 2*k <;> by_cases hlt' : j < 2*k
    · simp only [ite_eq_left hlt, ite_eq_left hlt'] at heq
      exact hp.graceful.2.2 i j hi hlt hj hlt' heq
    · have hsmall := hp.graceful.edge_lt hi hlt
      simp only [ite_eq_left hlt, ite_eq_right hlt'] at heq
      split_ifs at heq <;> omega
    · have hsmall := hp.graceful.edge_lt hj hlt'
      simp only [ite_eq_right hlt, ite_eq_left hlt'] at heq
      split_ifs at heq <;> omega
    · simp only [ite_eq_right hlt, ite_eq_right hlt'] at heq
      split_ifs at heq <;> omega
  · intro i hi
    by_cases hlt : i < 2*k
    · simp only [appendOddPath, ite_eq_left hlt]
      have h := hp.low_iff i hlt
      omega
    · simp only [appendOddPath, ite_eq_right hlt]
      rw [oddWalecki_low (by omega)]
      omega
  · simp only [appendOddPath, ite_eq_left (show 0 < 2*k by omega), hp.first]
    omega
  · simp only [appendOddPath, ite_eq_right (show ¬2*L < 2*k by omega), oddWalecki]
    have hodd : (2*L-2*k)%2 = 0 := by omega
    rw [ite_eq_left hodd]
    omega


lemma OddAlphaPath.reverse {L k : ℕ} {p : ℕ → ℕ} (hp : OddAlphaPath L k p)
    (hk : k ≤ L) : OddAlphaPath L (L-k) (reverseNatPath (2*L+1) p) := by
  refine ⟨hp.graceful.reverse,?_,?_,?_⟩
  · intro i hi
    have hh := hp.low_iff (2*L-i) (by omega)
    simp only [reverseNatPath,show 2*L+1-1=2*L by omega]
    omega
  · simpa only [reverseNatPath,show 2*L+1-1-0=2*L by omega] using hp.last
  · simpa only [reverseNatPath,show 2*L+1-1-2*L=0 by omega,
      show L-(L-k)=k by omega] using hp.first

theorem exists_oddAlphaPath {L k : ℕ} (hk : k ≤ L) (hne : 2*k ≠ L) :
    ∃ p, OddAlphaPath L k p := by
  have upper (a : ℕ) (ha : a ≤ L) (hhalf : L < 2*a) : ∃ p, OddAlphaPath L a p := by
    obtain ⟨p,hp⟩ := exists_evenAlphaPath a (2*a-L-1) (by omega)
    exact ⟨appendOddPath L a p,appendOddPath_alpha ha hhalf hp⟩
  by_cases hhalf : L < 2*k
  · exact upper k hk hhalf
  · obtain ⟨p,hp⟩ := upper (L-k) (by omega) (by omega)
    have hh := hp.reverse (by omega)
    rw [show L-(L-k)=k by omega] at hh
    exact ⟨_,hh⟩

lemma OddAlphaPath.toNatAlpha {L k : ℕ} {p : ℕ → ℕ} (hp : OddAlphaPath L k p)
    (hL : 0 < L) : NatAlphaPath (2*L+1) p L := by
  refine ⟨hp.graceful,by omega,?_⟩
  intro j hj hjb
  have h1 := hp.low_iff (j-1) (by omega)
  have h2 := hp.low_iff j hjb
  omega

/-- An alpha path can start at any lower-half label except the repeated-endpoint
case. Its other endpoint is given explicitly. -/
theorem exists_lower_endpoint_alpha_path {N k : ℕ}
    (hsize : 2*k+1 ≤ N) (hex : N ≠ 4*k+1) :
    ∃ p, NatAlphaPath N p ((N-1)/2) ∧ p 0=k ∧
      p (N-1) = if N%2=0 then N/2+k else N/2-k := by
  by_cases heven : N%2=0
  · have hN : N=2*(N/2) := by omega
    obtain ⟨p,hp⟩ := exists_evenAlphaPath (N/2) k (by omega)
    refine ⟨p,?_,hp.first,?_⟩
    · rw [hN]
      refine ⟨hp.graceful,by omega,?_⟩
      intro j hj hjb
      have hc := hp.crosses hj hjb
      omega
    · simp only [ite_eq_left heven]
      rw [show N-1=2*(N/2)-1 by omega]
      exact hp.last
  · have hN : N=2*(N/2)+1 := by omega
    obtain ⟨p,hp⟩ := exists_oddAlphaPath (L := N/2) (k := k) (by omega) (by omega)
    refine ⟨p,?_,hp.first,?_⟩
    · convert hp.toNatAlpha (by omega) using 1 <;> omega
    · simp only [ite_eq_right heven]
      rw [show N-1=2*(N/2) by omega]
      exact hp.last

end Bounty


/- Supporting module: ParentGraph -/

namespace Bounty

/-- A graph whose positive vertices each have a single lower-indexed parent. -/
def parentGraph (N : ℕ) (parent : ℕ → ℕ) : SimpleGraph (Fin (N + 1)) where
  Adj i j := (i.val < j.val ∧ parent j.val = i.val) ∨
    (j.val < i.val ∧ parent i.val = j.val)
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by intro i; simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero]⟩

abbrev parentGraphDecidable (N : ℕ) (parent : ℕ → ℕ) : DecidableRel (parentGraph N parent).Adj :=
  fun _ _ => inferInstanceAs (Decidable ((_ ∧ _) ∨ (_ ∧ _)))

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
      norm_num [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero] at hj
    · intro hj
      by_contra hzero
      apply hj
      apply Fin.ext
      have : j.val = 0 := by omega
      simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero] using this
  have hcard : verts.card = N := by rw [hv]; simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero]
  calc
    _ = es.card := rfl
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
  simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero]


end Bounty


/- Supporting module: ParentCertificate -/


namespace Bounty
open Math15.Graceful

/-- A natural-number labeling certificate for a rooted tree in parent order. -/
def NatParentCertificate (N : ℕ) (parent f : ℕ → ℕ) : Prop :=
  (∀ i j, i ≤ N → j ≤ N → f i = f j → i = j) ∧
  (∀ i, i ≤ N → f i ≤ N) ∧
  (∀ i j, 0 < i → i ≤ N → 0 < j → j ≤ N →
    Nat.dist (f (parent i)) (f i) = Nat.dist (f (parent j)) (f j) → i = j)

theorem NatParentCertificate.isGracefulLabeling {N : ℕ} {parent f : ℕ → ℕ}
    (hp : ∀ j, 0 < j → j ≤ N → parent j < j)
    (hf : NatParentCertificate N parent f) :
    IsGracefulLabeling (parentGraph N parent) (fun i => f i.val) := by
  apply labeling_of_injective_differences
  · intro i j h
    exact Fin.ext (hf.1 i.val j.val (by omega) (by omega) h)
  · intro i
    rw [parentGraph_edgeCount N parent hp]
    exact hf.2.1 _ (by omega)
  · intro e e' he ha he' ha' hd
    have hpar : parent e.2.val = e.1.val := by
      rcases ha with h | h
      · exact h.2
      · exact (Nat.lt_asymm he h.1).elim
    have hpar' : parent e'.2.val = e'.1.val := by
      rcases ha' with h | h
      · exact h.2
      · exact (Nat.lt_asymm he' h.1).elim
    have hr : e.2 = e'.2 := by
      apply Fin.ext
      apply hf.2.2 _ _ (by have := e.1.isLt; omega) (by omega)
        (by have := e'.1.isLt; omega) (by omega)
      simpa only [hpar, hpar'] using hd
    exact Prod.ext (Fin.ext (hpar.symm.trans ((congrArg (fun i => parent i.val) hr).trans hpar'))) hr

theorem NatParentCertificate.isGraceful {N : ℕ} {parent f : ℕ → ℕ}
    (hp : ∀ j, 0 < j → j ≤ N → parent j < j)
    (hf : NatParentCertificate N parent f) : IsGraceful (parentGraph N parent) :=
  hf.isGracefulLabeling hp |>.isGraceful

theorem NatParentCertificate.complement {N : ℕ} {parent f : ℕ → ℕ}
    (hp : ∀ j, 0 < j → j ≤ N → parent j < j)
    (hf : NatParentCertificate N parent f) :
    NatParentCertificate N parent (fun i => N - f i) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j hi hj heq
    dsimp only at heq
    have := hf.2.1 i hi
    have := hf.2.1 j hj
    exact hf.1 i j hi hj (by omega)
  · intro i hi; dsimp only; omega
  · intro i j hi hiN hj hjN hd
    dsimp only at hd
    have hpi := hf.2.1 (parent i) (by have := hp i hi hiN; omega)
    have hpj := hf.2.1 (parent j) (by have := hp j hj hjN; omega)
    have hfi := hf.2.1 i hiN
    have hfj := hf.2.1 j hjN
    apply hf.2.2 i j hi hiN hj hjN
    unfold Nat.dist at *
    omega

end Bounty


/- Supporting module: PathGraft -/


namespace Bounty
open Math15.Graceful

/-- Attach a path of new vertices after an existing parent-ordered tree. -/
def graftParent (N root : ℕ) (parent : ℕ → ℕ) (j : ℕ) : ℕ :=
  if j ≤ N then parent j else if j = N+1 then root else j-1

def graftLabel (N k : ℕ) (f p : ℕ → ℕ) (j : ℕ) : ℕ :=
  if j ≤ N then k+1+f j else shiftAboveCut k (N+1) (p (j-(N+1)))

theorem graftParent_lt {N M root : ℕ} {parent : ℕ → ℕ}
    (hr : root ≤ N) (hp : ∀ j, 0 < j → j ≤ N → parent j < j)
    {j : ℕ} (hj : 0 < j) (_hjb : j ≤ N+M) : graftParent N root parent j < j := by
  unfold graftParent
  split_ifs with h
  · exact hp j hj h
  all_goals omega

private theorem flat_PathGraft_graftLabel_old {N k j : ℕ} {f p : ℕ → ℕ} (hj : j ≤ N) :
    graftLabel N k f p j = k+1+f j := by simp only [graftLabel, ite_eq_left hj]

private theorem flat_PathGraft_graftLabel_new {N k j : ℕ} {f p : ℕ → ℕ} (hj : N < j) :
    graftLabel N k f p j = shiftAboveCut k (N+1) (p (j-(N+1))) := by
  simp only [graftLabel, ite_eq_right (by omega : ¬j ≤ N)]

private theorem flat_PathGraft_graftLabel_inj {N M k : ℕ} {parent f p : ℕ → ℕ}
    (hf : NatParentCertificate N parent f) (hp : NatGracefulPath M p)
    {i j : ℕ} (hi : i ≤ N+M) (hj : j ≤ N+M)
    (he : graftLabel N k f p i = graftLabel N k f p j) : i=j := by
  by_cases hiN : i ≤ N <;> by_cases hjN : j ≤ N
  · rw [flat_PathGraft_graftLabel_old hiN, flat_PathGraft_graftLabel_old hjN] at he
    exact hf.1 i j hiN hjN (by omega)
  · rw [flat_PathGraft_graftLabel_old hiN, flat_PathGraft_graftLabel_new (by omega)] at he
    have hb := hf.2.1 i hiN
    unfold shiftAboveCut at he
    split_ifs at he <;> omega
  · rw [flat_PathGraft_graftLabel_new (by omega), flat_PathGraft_graftLabel_old hjN] at he
    have hb := hf.2.1 j hjN
    unfold shiftAboveCut at he
    split_ifs at he <;> omega
  · rw [flat_PathGraft_graftLabel_new (by omega), flat_PathGraft_graftLabel_new (by omega)] at he
    have ht := hp.1 (i-(N+1)) (j-(N+1)) (by omega) (by omega)
      (shiftAboveCut_injective k (N+1) he)
    omega

private theorem flat_PathGraft_graftLabel_bound {N M k : ℕ} {parent f p : ℕ → ℕ}
    (hf : NatParentCertificate N parent f) (hp : NatGracefulPath M p) (hk : k < M)
    {j : ℕ} (hj : j ≤ N+M) : graftLabel N k f p j ≤ N+M := by
  by_cases hjN : j ≤ N
  · rw [flat_PathGraft_graftLabel_old hjN]
    have hb := hf.2.1 j hjN
    omega
  · rw [flat_PathGraft_graftLabel_new (by omega)]
    have hb := hp.2.1 (j-(N+1)) (by omega)
    unfold shiftAboveCut
    split_ifs <;> omega

private theorem flat_PathGraft_graftLabel_old_edge {N root k j : ℕ} {parent f p : ℕ → ℕ}
    (hpar : ∀ j, 0 < j → j ≤ N → parent j < j) (hj : 0 < j) (hjb : j ≤ N) :
    Nat.dist (graftLabel N k f p (graftParent N root parent j)) (graftLabel N k f p j) =
      Nat.dist (f (parent j)) (f j) := by
  have hpj := hpar j hj hjb
  simp only [graftParent, ite_eq_left hjb, flat_PathGraft_graftLabel_old (by omega : parent j ≤ N),
    flat_PathGraft_graftLabel_old hjb, translate_dist]

private theorem flat_PathGraft_graftLabel_join_edge {N root k : ℕ} {parent f p : ℕ → ℕ}
    (hr : root ≤ N) :
    Nat.dist (graftLabel N k f p (graftParent N root parent (N+1)))
      (graftLabel N k f p (N+1)) =
      Nat.dist (k+1+f root) (shiftAboveCut k (N+1) (p 0)) := by
  simp only [graftParent, ite_eq_right (by omega : ¬N+1 ≤ N), ite_true,
    flat_PathGraft_graftLabel_old hr, flat_PathGraft_graftLabel_new (by omega : N < N+1), Nat.sub_self]

private theorem flat_PathGraft_graftLabel_path_edge {N M root k j : ℕ} {parent f p : ℕ → ℕ}
    (hc : ∀ i, 0 < i → i < M →
      (p (i-1) ≤ k ∧ k < p i) ∨ (p i ≤ k ∧ k < p (i-1)))
    (hj : N+1 < j) (hjb : j ≤ N+M) :
    Nat.dist (graftLabel N k f p (graftParent N root parent j)) (graftLabel N k f p j) =
      (N+1)+Nat.dist (p (j-(N+1)-1)) (p (j-(N+1))) := by
  simp only [graftParent, ite_eq_right (by omega : ¬j ≤ N), ite_eq_right (by omega : ¬j=N+1),
    flat_PathGraft_graftLabel_new (by omega : N < j-1), flat_PathGraft_graftLabel_new (by omega : N < j)]
  have he : j-1-(N+1) = j-(N+1)-1 := by omega
  rw [he]
  rcases hc (j-(N+1)) (by omega) (by omega) with h | h
  · exact shiftAboveCut_dist h.1 h.2
  · rw [Nat.dist_comm (shiftAboveCut _ _ _), Nat.dist_comm (p (j-(N+1)-1))]
    exact shiftAboveCut_dist h.1 h.2

/-- The old graph occupies the middle label interval; the new alpha path
occupies the intervals on either side. Its joining edge fills the gap. -/
theorem NatParentCertificate.graftAlphaPath {N M root k : ℕ} {parent f p : ℕ → ℕ}
    (hf : NatParentCertificate N parent f) (hr : root ≤ N)
    (hpar : ∀ j, 0 < j → j ≤ N → parent j < j)
    (hp : NatGracefulPath M p) (hk : k < M)
    (hc : ∀ i, 0 < i → i < M →
      (p (i-1) ≤ k ∧ k < p i) ∨ (p i ≤ k ∧ k < p (i-1)))
    (hjoin : Nat.dist (k+1+f root) (shiftAboveCut k (N+1) (p 0)) = N+1) :
    NatParentCertificate (N+M) (graftParent N root parent) (graftLabel N k f p) := by
  refine ⟨fun _ _ hi hj he => flat_PathGraft_graftLabel_inj hf hp hi hj he,
    fun _ hj => flat_PathGraft_graftLabel_bound hf hp hk hj, ?_⟩
  have hold (i : ℕ) (hi : 0 < i) (hib : i ≤ N) : Nat.dist (f (parent i)) (f i) ≤ N := by
    have h1 := hf.2.1 i hib
    have h2 := hf.2.1 (parent i) (by have := hpar i hi hib; omega)
    unfold Nat.dist
    omega
  have hnew (i : ℕ) (hi : 0 < i) (hib : i < M) :
      1 ≤ Nat.dist (p (i-1)) (p i) := by
    apply Nat.dist_pos_of_ne
    intro he
    have := hp.1 (i-1) i (by omega) hib he
    omega
  intro i j hi hib hj hjb he
  rcases lt_trichotomy i (N+1) with hiN | rfl | hiN <;>
    rcases lt_trichotomy j (N+1) with hjN | rfl | hjN
  · rw [flat_PathGraft_graftLabel_old_edge hpar hi (by omega), flat_PathGraft_graftLabel_old_edge hpar hj (by omega)] at he
    exact hf.2.2 i j hi (by omega) hj (by omega) he
  · rw [flat_PathGraft_graftLabel_old_edge hpar hi (by omega), flat_PathGraft_graftLabel_join_edge hr, hjoin] at he
    have := hold i hi (by omega)
    omega
  · rw [flat_PathGraft_graftLabel_old_edge hpar hi (by omega), flat_PathGraft_graftLabel_path_edge hc hjN hjb] at he
    have := hold i hi (by omega)
    have := hnew (j-(N+1)) (by omega) (by omega)
    omega
  · rw [flat_PathGraft_graftLabel_join_edge hr, hjoin, flat_PathGraft_graftLabel_old_edge hpar hj (by omega)] at he
    have := hold j hj (by omega)
    omega
  · rfl
  · rw [flat_PathGraft_graftLabel_join_edge hr, hjoin, flat_PathGraft_graftLabel_path_edge hc hjN hjb] at he
    have := hnew (j-(N+1)) (by omega) (by omega)
    omega
  · rw [flat_PathGraft_graftLabel_path_edge hc hiN hib, flat_PathGraft_graftLabel_old_edge hpar hj (by omega)] at he
    have := hold j hj (by omega)
    have := hnew (i-(N+1)) (by omega) (by omega)
    omega
  · rw [flat_PathGraft_graftLabel_path_edge hc hiN hib, flat_PathGraft_graftLabel_join_edge hr, hjoin] at he
    have := hnew (i-(N+1)) (by omega) (by omega)
    omega
  · rw [flat_PathGraft_graftLabel_path_edge hc hiN hib, flat_PathGraft_graftLabel_path_edge hc hjN hjb] at he
    have := hp.2.2 (i-(N+1)) (j-(N+1)) (by omega) (by omega) (by omega) (by omega)
      (by omega)
    omega

theorem graftLabel_zero {N k i : ℕ} {f p : ℕ → ℕ} (hz : p i=0) :
    graftLabel N k f p (N+1+i)=0 := by
  rw [flat_PathGraft_graftLabel_new (by omega)]
  have he : N+1+i-(N+1)=i := by omega
  simp only [he, hz, shiftAboveCut, Nat.zero_le, ite_true]

theorem graftJoin_low {N k t s : ℕ} (hs : s ≤ k) (ht : t=N+s-k) (hbound : k ≤ N+s) :
    Nat.dist (k+1+t) (shiftAboveCut k (N+1) s) = N+1 := by
  simp only [shiftAboveCut, ite_eq_left hs]
  unfold Nat.dist
  omega

theorem graftJoin_high {N k t s : ℕ} (hs : k < s) (ht : t=s-k-1) :
    Nat.dist (k+1+t) (shiftAboveCut k (N+1) s) = N+1 := by
  simp only [shiftAboveCut, ite_eq_right (by omega : ¬s ≤ k)]
  unfold Nat.dist
  omega

theorem NatGracefulPath.parentCertificate {N : ℕ} {f : ℕ → ℕ}
    (hf : NatGracefulPath (N+1) f) : NatParentCertificate N Nat.pred f := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j hi hj he
    exact hf.1 i j (by omega) (by omega) he
  · intro i hi
    have := hf.2.1 i (by omega)
    omega
  · intro i j hi hib hj hjb he
    exact hf.2.2 i j hi (by omega) hj (by omega) he

/-- Three arms of lengths a,b,d+c, with the first two in path order. -/
def forkParent (a b : ℕ) : ℕ → ℕ := graftParent (a+b) a Nat.pred

def RootedFork (a b d c : ℕ) : Prop :=
  ∃ f, NatParentCertificate (a+b+(d+c)) (forkParent a b) f ∧ f (a+b+d)=0

theorem rootedFork_of_paths {a b d c k : ℕ} {f p : ℕ → ℕ}
    (hd : 1 ≤ d) (hf : NatGracefulPath (a+b+1) f)
    (hp : NatGracefulPath (d+c) p) (hk : k < d+c)
    (hcross : ∀ i, 0 < i → i < d+c →
      (p (i-1) ≤ k ∧ k < p i) ∨ (p i ≤ k ∧ k < p (i-1)))
    (hzero : p (d-1)=0)
    (hjoin : Nat.dist (k+1+f a) (shiftAboveCut k (a+b+1) (p 0)) = a+b+1) :
    RootedFork a b d c := by
  refine ⟨graftLabel (a+b) k f p, hf.parentCertificate.graftAlphaPath
    (by omega) (by intro j hj _; simpa only [Nat.pred_eq_sub_one] using
      (Nat.sub_lt hj (by omega : 0 < 1))) hp hk hcross hjoin, ?_⟩
  have he : a+b+1+(d-1)=a+b+d := by omega
  simpa only [he] using (graftLabel_zero (N := a+b) (k := k) (f := f) hzero)

end Bounty


/- Supporting module: AlphaParentAppend -/


namespace Bounty
open Math15.Graceful

def NatParentAlpha (N : ℕ) (parent f : ℕ → ℕ) (k : ℕ) : Prop :=
  ∀ j, 0 < j → j ≤ N →
    (f (parent j) ≤ k ∧ k < f j) ∨ (f j ≤ k ∧ k < f (parent j))

def appendAlphaLabel (N m k : ℕ) (f p : ℕ → ℕ) (j : ℕ) : ℕ :=
  if j ≤ N then shiftAboveCut k m (f j) else k+1+p (j-(N+1))

private theorem flat_AlphaParentAppend_appendAlpha_old {N m k j : ℕ} {f p : ℕ → ℕ} (hj : j ≤ N) :
    appendAlphaLabel N m k f p j = shiftAboveCut k m (f j) := by
  simp only [appendAlphaLabel, ite_eq_left hj]

private theorem flat_AlphaParentAppend_appendAlpha_new {N m k j : ℕ} {f p : ℕ → ℕ} (hj : N < j) :
    appendAlphaLabel N m k f p j = k+1+p (j-(N+1)) := by
  simp only [appendAlphaLabel, ite_eq_right (by omega : ¬j ≤ N)]

theorem NatParentCertificate.appendAlphaPath {N m root k : ℕ} {parent f p : ℕ → ℕ}
    (hf : NatParentCertificate N parent f) (ha : NatParentAlpha N parent f k)
    (hpar : ∀ j, 0 < j → j ≤ N → parent j < j) (hr : root ≤ N)
    (hp : NatGracefulPath m p) (hk : k ≤ N)
    (hjoin : Nat.dist (shiftAboveCut k m (f root)) (k+1+p 0)=m) :
    NatParentCertificate (N+m) (graftParent N root parent) (appendAlphaLabel N m k f p) := by
  have hold (j : ℕ) (hj : 0 < j) (hb : j ≤ N) :
      Nat.dist (appendAlphaLabel N m k f p (graftParent N root parent j))
        (appendAlphaLabel N m k f p j) = m+Nat.dist (f (parent j)) (f j) := by
    have hpj := hpar j hj hb
    simp only [graftParent, ite_eq_left hb, flat_AlphaParentAppend_appendAlpha_old hb,
      flat_AlphaParentAppend_appendAlpha_old (by omega : parent j ≤ N)]
    rcases ha j hj hb with h | h
    · exact shiftAboveCut_dist h.1 h.2
    · rw [Nat.dist_comm (shiftAboveCut _ _ _), Nat.dist_comm (f (parent j))]
      exact shiftAboveCut_dist h.1 h.2
  have hlink : Nat.dist (appendAlphaLabel N m k f p (graftParent N root parent (N+1)))
      (appendAlphaLabel N m k f p (N+1))=m := by
    simpa only [graftParent, ite_eq_right (by omega : ¬N+1 ≤ N), ite_true,
      flat_AlphaParentAppend_appendAlpha_old hr, flat_AlphaParentAppend_appendAlpha_new (by omega : N < N+1), Nat.sub_self] using hjoin
  have hnew (j : ℕ) (hj : N+1 < j) :
      Nat.dist (appendAlphaLabel N m k f p (graftParent N root parent j))
        (appendAlphaLabel N m k f p j) =
      Nat.dist (p (j-(N+1)-1)) (p (j-(N+1))) := by
    simp only [graftParent, ite_eq_right (by omega : ¬j ≤ N),
      ite_eq_right (by omega : ¬j=N+1), flat_AlphaParentAppend_appendAlpha_new (by omega : N < j),
      flat_AlphaParentAppend_appendAlpha_new (by omega : N < j-1), translate_dist]
    have he : j-1-(N+1)=j-(N+1)-1 := by omega
    rw [he]
  have hpos (j : ℕ) (hj : 0 < j) (hb : j ≤ N) :
      1 ≤ Nat.dist (f (parent j)) (f j) := by
    apply Nat.dist_pos_of_ne
    intro he
    have hpj := hpar j hj hb
    have := hf.1 (parent j) j (by omega) hb he
    omega
  refine ⟨?_, ?_, ?_⟩
  · intro i j hi hj heq
    by_cases hiN : i ≤ N <;> by_cases hjN : j ≤ N
    · rw [flat_AlphaParentAppend_appendAlpha_old hiN, flat_AlphaParentAppend_appendAlpha_old hjN] at heq
      exact hf.1 i j hiN hjN (shiftAboveCut_injective k m heq)
    · rw [flat_AlphaParentAppend_appendAlpha_old hiN, flat_AlphaParentAppend_appendAlpha_new (by omega)] at heq
      have hb := hp.2.1 (j-(N+1)) (by omega)
      unfold shiftAboveCut at heq
      split_ifs at heq <;> omega
    · rw [flat_AlphaParentAppend_appendAlpha_new (by omega), flat_AlphaParentAppend_appendAlpha_old hjN] at heq
      have hb := hp.2.1 (i-(N+1)) (by omega)
      unfold shiftAboveCut at heq
      split_ifs at heq <;> omega
    · rw [flat_AlphaParentAppend_appendAlpha_new (by omega), flat_AlphaParentAppend_appendAlpha_new (by omega)] at heq
      have := hp.1 (i-(N+1)) (j-(N+1)) (by omega) (by omega) (by omega)
      omega
  · intro j hj
    by_cases hjN : j ≤ N
    · rw [flat_AlphaParentAppend_appendAlpha_old hjN]
      exact shiftAboveCut_le (hf.2.1 j hjN)
    · rw [flat_AlphaParentAppend_appendAlpha_new (by omega)]
      have := hp.2.1 (j-(N+1)) (by omega)
      omega
  · intro i j hi hib hj hjb heq
    rcases lt_trichotomy i (N+1) with hiN | rfl | hiN <;>
      rcases lt_trichotomy j (N+1) with hjN | rfl | hjN
    · rw [hold i hi (by omega), hold j hj (by omega)] at heq
      exact hf.2.2 i j hi (by omega) hj (by omega) (by omega)
    · rw [hold i hi (by omega), hlink] at heq
      have := hpos i hi (by omega)
      omega
    · rw [hold i hi (by omega), hnew j hjN] at heq
      have := hpos i hi (by omega)
      have := hp.edge_lt (j := j-(N+1)) (by omega) (by omega)
      omega
    · rw [hlink, hold j hj (by omega)] at heq
      have := hpos j hj (by omega)
      omega
    · rfl
    · rw [hlink, hnew j hjN] at heq
      have := hp.edge_lt (j := j-(N+1)) (by omega) (by omega)
      omega
    · rw [hnew i hiN, hold j hj (by omega)] at heq
      have := hpos j hj (by omega)
      have := hp.edge_lt (j := i-(N+1)) (by omega) (by omega)
      omega
    · rw [hnew i hiN, hlink] at heq
      have := hp.edge_lt (j := i-(N+1)) (by omega) (by omega)
      omega
    · rw [hnew i hiN, hnew j hjN] at heq
      have := hp.2.2 (i-(N+1)) (j-(N+1)) (by omega) (by omega) (by omega) (by omega) heq
      omega

theorem appendAlphaLabel_preserves_zero {N m k j : ℕ} {f p : ℕ → ℕ}
    (hj : j ≤ N) (hz : f j=0) : appendAlphaLabel N m k f p j=0 := by
  simp only [flat_AlphaParentAppend_appendAlpha_old hj, hz, shiftAboveCut, Nat.zero_le, ite_true]

/-- A sufficiently long appended path retains every old zero label. -/
theorem NatParentCertificate.appendAtZero {N m root k : ℕ} {parent f : ℕ → ℕ}
    (hf : NatParentCertificate N parent f) (ha : NatParentAlpha N parent f k)
    (hpar : ∀ j, 0 < j → j ≤ N → parent j < j) (hr : root ≤ N)
    (hz : f root=0) (hk : k ≤ N) (hm : k+1 ≤ m) :
    ∃ g, NatParentCertificate (N+m) (graftParent N root parent) g ∧
      (∀ j, j ≤ N → f j=0 → g j=0) := by
  obtain ⟨p,hp,hp0⟩ := exists_graceful_path_endpoint (n := m) (a := m-k-1) (by omega)
  refine ⟨appendAlphaLabel N m k f p, hf.appendAlphaPath ha hpar hr hp hk ?_, ?_⟩
  · simp only [hz, hp0, shiftAboveCut, Nat.zero_le, ite_true]
    unfold Nat.dist
    omega
  · intro j hj hzj
    exact appendAlphaLabel_preserves_zero hj hzj

/-- Append at an arbitrary vertex when the new path is long enough for its label. -/
theorem NatParentCertificate.appendAtRoot {N m root k : ℕ} {parent f : ℕ → ℕ}
    (hf : NatParentCertificate N parent f) (ha : NatParentAlpha N parent f k)
    (hpar : ∀ j, 0 < j → j ≤ N → parent j < j) (hr : root ≤ N) (hk : k ≤ N)
    (hl : f root ≤ k → k+1 ≤ m+f root)
    (hu : k < f root → f root ≤ m+k) :
    ∃ g, NatParentCertificate (N+m) (graftParent N root parent) g ∧
      (∀ j, j ≤ N → f j=0 → g j=0) := by
  by_cases hc : f root ≤ k
  · obtain ⟨p,hp,hp0⟩ := exists_graceful_path_endpoint
      (n := m) (a := m+f root-k-1) (by have := hl hc; omega)
    refine ⟨appendAlphaLabel N m k f p,hf.appendAlphaPath ha hpar hr hp hk ?_,?_⟩
    · simp only [shiftAboveCut,if_pos hc,hp0]
      have := hl hc
      unfold Nat.dist
      omega
    · intro j hj hz
      exact appendAlphaLabel_preserves_zero hj hz
  · obtain ⟨p,hp,hp0⟩ := exists_graceful_path_endpoint
      (n := m) (a := f root-k-1) (by have := hu (by omega); omega)
    refine ⟨appendAlphaLabel N m k f p,hf.appendAlphaPath ha hpar hr hp hk ?_,?_⟩
    · simp only [shiftAboveCut,if_neg hc,hp0]
      unfold Nat.dist
      omega
    · intro j hj hz
      exact appendAlphaLabel_preserves_zero hj hz

end Bounty


/- Supporting module: CentralSplice -/


namespace Bounty
open Math15.Graceful

/-- Complementing all labels reverses the two classes of an alpha path. -/
theorem NatAlphaPath.complement {n k : ℕ} {p : ℕ → ℕ} (h : NatAlphaPath n p k) :
    NatAlphaPath n (fun i => n-1-p i) (n-2-k) := by
  refine ⟨h.1.complement,?_,?_⟩
  · have hk := h.2.1
    omega
  · intro j hj hjb
    have hp := h.1.2.1 (j-1) (by omega)
    have hq := h.1.2.1 j hjb
    have hk := h.2.1
    rcases h.2.2 j hj hjb with ha | ha
    · right; dsimp only; omega
    · left; dsimp only; omega

private theorem flat_CentralSplice_centralSplice_parent (N j : ℕ) (hj : 0<j) :
    graftParent N N Nat.pred j=j-1 := by
  unfold graftParent
  simp only [Nat.pred_eq_sub_one]
  split_ifs <;> omega

/-- Concatenate two alpha paths, preserving the old lower labels and inserting
the second path between the old lower and upper intervals. -/
theorem NatAlphaPath.appendAtLower {N m k h : ℕ} {p q : ℕ → ℕ}
    (hp : NatAlphaPath (N+1) p k) (hq : NatAlphaPath m q h)
    (hroot : p N≤k) (hfirst : h<q 0)
    (hjoin : Nat.dist (shiftAboveCut k m (p N)) (k+1+q 0)=m) :
    NatAlphaPath (N+m+1) (appendAlphaLabel N m k p q) (k+1+h) := by
  have hpar (j : ℕ) (hj : 0<j) (_hjb : j≤N) : Nat.pred j<j := by
    simp only [Nat.pred_eq_sub_one]
    omega
  have hpa : NatParentAlpha N Nat.pred p k := by
    intro j hj hjb
    simpa only [Nat.pred_eq_sub_one] using hp.2.2 j hj (by omega)
  have hk : k≤N := by have := hp.2.1; omega
  have hcert := hp.1.parentCertificate.appendAlphaPath hpa hpar (by omega : N≤N) hq.1 hk hjoin
  have hnewk : k+1+h<N+m := by have := hp.2.1; have := hq.2.1; omega
  refine ⟨⟨?_,?_,?_⟩,by omega,?_⟩
  · intro i j hi hj heq
    exact hcert.1 i j (by omega) (by omega) heq
  · intro j hj
    have := hcert.2.1 j (by omega)
    omega
  · intro i j hi hib hj hjb heq
    apply hcert.2.2 i j hi (by omega) hj (by omega)
    simpa only [flat_CentralSplice_centralSplice_parent N i hi,flat_CentralSplice_centralSplice_parent N j hj] using heq
  · intro j hj hjb
    rcases lt_trichotomy j (N+1) with hold | rfl | hnew
    · have hprev : j-1≤N := by omega
      have hcurr : j≤N := by omega
      simp only [appendAlphaLabel,ite_eq_left hprev,ite_eq_left hcurr]
      rcases hp.2.2 j hj (by omega) with hc | hc
      · left
        simp only [shiftAboveCut,ite_eq_left hc.1,ite_eq_right (by omega : ¬p j≤k)]
        have := hq.2.1
        omega
      · right
        simp only [shiftAboveCut,ite_eq_left hc.1,ite_eq_right (by omega : ¬p (j-1)≤k)]
        have := hq.2.1
        omega
    · simp only [Nat.add_sub_cancel,appendAlphaLabel,le_refl,ite_true,
        ite_eq_right (by omega : ¬N+1≤N),Nat.sub_self]
      left
      simp only [shiftAboveCut,ite_eq_left hroot]
      omega
    · have hprev : ¬j-1≤N := by omega
      have hcurr : ¬j≤N := by omega
      simp only [appendAlphaLabel,ite_eq_right hprev,ite_eq_right hcurr]
      have heq : j-1-(N+1)=j-(N+1)-1 := by omega
      rw [heq]
      rcases hq.2.2 (j-(N+1)) (by omega) (by omega) with hc | hc
      · left; omega
      · right; omega

/-- Exact arithmetic conditions for the central two-piece construction. -/
def CentralSplice (l m u : ℕ) : Prop :=
  0<l ∧ 0<m ∧ u≤l/2 ∧ l≠4*u ∧
    2*(l/2-u)+1≤m ∧ m≠4*(l/2-u)+1

/-- A prescribed central lower label obtained entirely from the proved alpha
endpoint constructions. The two arms may have different lengths. -/
theorem centralSplice_alpha {l m u : ℕ} (h : CentralSplice l m u) :
    ∃ p, NatAlphaPath (l+m+1) p (l/2+m/2) ∧ p l=u := by
  obtain ⟨hl,hm,hu,hexl,hroom,hexm⟩ := h
  obtain ⟨p,hp,hp0,_⟩ := exists_lower_endpoint_alpha_path
    (N:=l+1) (k:=u) (by omega) (by omega)
  obtain ⟨q,hq,hq0,_⟩ := exists_lower_endpoint_alpha_path
    (N:=m) (k:=l/2-u) hroom hexm
  have hm2 : 2≤m := by omega
  have hk : (l+1-1)/2=l/2 := by omega
  rw [hk] at hp
  let p' := reverseNatPath (l+1) p
  let q' := fun i => m-1-q i
  have hp' : NatAlphaPath (l+1) p' (l/2) := hp.reverse
  have hq' : NatAlphaPath m q' (m/2-1) := by
    have heq : m-2-(m-1)/2=m/2-1 := by omega
    simpa only [heq] using hq.complement
  have hp'l : p' l=u := by simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, p',reverseNatPath] using hp0
  have hq'0 : q' 0=m-1-(l/2-u) := by simp only [q',hq0]
  have hjoin : Nat.dist (shiftAboveCut (l/2) m (p' l)) (l/2+1+q' 0)=m := by
    rw [hp'l,hq'0]
    simp only [shiftAboveCut,ite_eq_left hu]
    unfold Nat.dist
    omega
  have hs := hp'.appendAtLower hq' (by omega) (by omega) hjoin
  have hcut : l/2+1+(m/2-1)=l/2+m/2 := by omega
  rw [hcut] at hs
  refine ⟨appendAlphaLabel l m (l/2) p' q',hs,?_⟩
  simp only [appendAlphaLabel,le_refl,ite_true,hp'l,shiftAboveCut,ite_eq_left hu]

/-- Reverse a central splice to exchange the two arms. -/
theorem centralSplice_alpha_symm {l m u : ℕ} (h : CentralSplice m l u) :
    ∃ p, NatAlphaPath (l+m+1) p (l/2+m/2) ∧ p l=u := by
  obtain ⟨p,hp,hpin⟩ := centralSplice_alpha h
  refine ⟨reverseNatPath (m+l+1) p,?_,?_⟩
  · simpa only [Nat.add_comm m l,Nat.add_comm (m/2) (l/2)] using hp.reverse
  · simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, reverseNatPath] using hpin

/-- Reflect both label intervals of an alpha path. This retains its cut. -/
theorem NatAlphaPath.reflect {n k : ℕ} {p : ℕ → ℕ} (h : NatAlphaPath n p k) :
    NatAlphaPath n (fun i => reverseLabel (n-1) k (p i)) k := by
  have hk : k≤n-1 := by have := h.2.1; omega
  have bound (i : ℕ) (hi : i<n) : p i≤n-1 := by have := h.1.2.1 i hi; omega
  have diff (j : ℕ) (hj : 0<j) (hjb : j<n) :
      Nat.dist (reverseLabel (n-1) k (p (j-1))) (reverseLabel (n-1) k (p j))=
        n-Nat.dist (p (j-1)) (p j) := by
    rcases h.2.2 j hj hjb with hc | hc
    · have hh := reverseLabel_dist hc.1 hc.2 (bound j hjb)
      simpa only [show n-1+1=n by omega] using hh
    · rw [Nat.dist_comm (reverseLabel _ _ _),Nat.dist_comm (p (j-1))]
      have hh := reverseLabel_dist hc.1 hc.2 (bound (j-1) (by omega))
      simpa only [show n-1+1=n by omega] using hh
  refine ⟨⟨?_,?_,?_⟩,h.2.1,?_⟩
  · intro i j hi hj heq
    exact h.1.1 i j hi hj (reverseLabel_injective (bound i hi) (bound j hj) heq)
  · intro i hi
    change reverseLabel (n-1) k (p i)<n
    have hh := reverseLabel_le hk (bound i hi)
    have hn := h.2.1
    omega
  · intro i j hi hib hj hjb heq
    change Nat.dist (reverseLabel (n-1) k (p (i-1))) (reverseLabel (n-1) k (p i))=
      Nat.dist (reverseLabel (n-1) k (p (j-1))) (reverseLabel (n-1) k (p j)) at heq
    rw [diff i hi hib,diff j hj hjb] at heq
    have hb1 := h.1.edge_lt hi hib
    have hb2 := h.1.edge_lt hj hjb
    exact h.1.2.2 i j hi hib hj hjb (by omega)
  · intro j hj hjb
    have hi := reverseLabel_low_iff (k:=k) (bound (j-1) (by omega))
    have hj' := reverseLabel_low_iff (k:=k) (bound j hjb)
    rcases h.2.2 j hj hjb with hc | hc
    · left; dsimp only; omega
    · right; dsimp only; omega

/-- Reflection makes the symmetric lower label available at the same vertex. -/
theorem centralSplice_alpha_reflect {l m u : ℕ} (h : CentralSplice l m u) :
    ∃ p, NatAlphaPath (l+m+1) p (l/2+m/2) ∧ p l=l/2+m/2-u := by
  obtain ⟨p,hp,hpin⟩ := centralSplice_alpha h
  refine ⟨fun i => reverseLabel (l+m+1-1) (l/2+m/2) (p i),hp.reflect,?_⟩
  have hu : u≤l/2+m/2 := by have := h.2.2.1; omega
  simp only [hpin,reverseLabel,ite_eq_left hu]

/-- The four elementary constructions: either arm order, followed optionally
by reflection within the two alpha intervals. -/
def CentralSpliceAvailable (l m u : ℕ) : Prop :=
  CentralSplice l m u ∨ CentralSplice m l u ∨
    (u≤l/2+m/2 ∧
      (CentralSplice l m (l/2+m/2-u) ∨ CentralSplice m l (l/2+m/2-u)))

theorem centralSpliceAvailable_alpha {l m u : ℕ} (h : CentralSpliceAvailable l m u) :
    ∃ p, NatAlphaPath (l+m+1) p (l/2+m/2) ∧ p l=u := by
  rcases h with h | h | ⟨hu,h | h⟩
  · exact centralSplice_alpha h
  · exact centralSplice_alpha_symm h
  · obtain ⟨p,hp,hpin⟩ := centralSplice_alpha_reflect h
    exact ⟨p,hp,by omega⟩
  · obtain ⟨p,hp,hpin⟩ := centralSplice_alpha_symm h
    refine ⟨fun i => reverseLabel (l+m+1-1) (l/2+m/2) (p i),hp.reflect,?_⟩
    simp only [hpin,reverseLabel,ite_eq_left (show l/2+m/2-u≤l/2+m/2 by omega)]
    omega

/-- The central-splice predicate directly supplies the ordinary graceful path
input needed by the fork construction. -/
theorem centralSpliceAvailable_path {l m u : ℕ} (h : CentralSpliceAvailable l m u) :
    ∃ p, NatGracefulPath (l+m+1) p ∧ p l=u := by
  obtain ⟨p,hp,hpin⟩ := centralSpliceAvailable_alpha h
  exact ⟨p,hp.1,hpin⟩

theorem centralSpliceAvailable_path_complement {l m u : ℕ} (h : CentralSpliceAvailable l m u) :
    ∃ p, NatGracefulPath (l+m+1) p ∧ p l=l+m-u := by
  obtain ⟨p,hp,hpin⟩ := centralSpliceAvailable_path h
  refine ⟨fun i => l+m+1-1-p i,hp.complement,?_⟩
  simp only [hpin,Nat.add_sub_cancel]

end Bounty


/- Supporting module: H1SpliceCoverage -/


namespace Bounty
open H1Coverage

private theorem flat_H1SpliceCoverage_splice_d1_000 (a b c : ℕ) (ha : 1≤a) (hab : a≤b) (hc : 2<c)
    (hnotlong : c<Cut a b 1+1)
    (hnotleft : ¬OuterAvailable a b 1 c)
    (hnotright : ¬OuterAvailable b a 1 c)
    (hexc : ¬(a=4∧b=4∧c=3)∧¬(a=5∧b=5∧c=6))
    (hA : a%2=0) (hB : b%2=0) (hC : c%2=0) :
    CentralSpliceAvailable a b (c/2) := by
  unfold CentralSpliceAvailable CentralSplice
  norm_num [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, Cut,V,U,OuterAvailable] at *
  omega

private theorem flat_H1SpliceCoverage_splice_d1_001 (a b c : ℕ) (ha : 1≤a) (hab : a≤b) (hc : 2<c)
    (hnotlong : c<Cut a b 1+1)
    (hnotleft : ¬OuterAvailable a b 1 c)
    (hnotright : ¬OuterAvailable b a 1 c)
    (hexc : ¬(a=4∧b=4∧c=3)∧¬(a=5∧b=5∧c=6))
    (hA : a%2=0) (hB : b%2=0) (hC : c%2=1) :
    CentralSpliceAvailable a b (c/2) := by
  unfold CentralSpliceAvailable CentralSplice
  norm_num [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, Cut,V,U,OuterAvailable] at *
  omega

private theorem flat_H1SpliceCoverage_splice_d1_010 (a b c : ℕ) (ha : 1≤a) (hab : a≤b) (hc : 2<c)
    (hnotlong : c<Cut a b 1+1)
    (hnotleft : ¬OuterAvailable a b 1 c)
    (hnotright : ¬OuterAvailable b a 1 c)
    (hexc : ¬(a=4∧b=4∧c=3)∧¬(a=5∧b=5∧c=6))
    (hA : a%2=0) (hB : b%2=1) (hC : c%2=0) :
    CentralSpliceAvailable a b (c/2) := by
  unfold CentralSpliceAvailable CentralSplice
  norm_num [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, Cut,V,U,OuterAvailable] at *
  omega

private theorem flat_H1SpliceCoverage_splice_d1_011 (a b c : ℕ) (ha : 1≤a) (hab : a≤b) (hc : 2<c)
    (hnotlong : c<Cut a b 1+1)
    (hnotleft : ¬OuterAvailable a b 1 c)
    (hnotright : ¬OuterAvailable b a 1 c)
    (hexc : ¬(a=4∧b=4∧c=3)∧¬(a=5∧b=5∧c=6))
    (hA : a%2=0) (hB : b%2=1) (hC : c%2=1) :
    CentralSpliceAvailable a b (c/2) := by
  unfold CentralSpliceAvailable CentralSplice
  norm_num [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, Cut,V,U,OuterAvailable] at *
  omega

private theorem flat_H1SpliceCoverage_splice_d1_100 (a b c : ℕ) (ha : 1≤a) (hab : a≤b) (hc : 2<c)
    (hnotlong : c<Cut a b 1+1)
    (hnotleft : ¬OuterAvailable a b 1 c)
    (hnotright : ¬OuterAvailable b a 1 c)
    (hexc : ¬(a=4∧b=4∧c=3)∧¬(a=5∧b=5∧c=6))
    (hA : a%2=1) (hB : b%2=0) (hC : c%2=0) :
    CentralSpliceAvailable a b (c/2) := by
  unfold CentralSpliceAvailable CentralSplice
  norm_num [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, Cut,V,U,OuterAvailable] at *
  omega

private theorem flat_H1SpliceCoverage_splice_d1_101 (a b c : ℕ) (ha : 1≤a) (hab : a≤b) (hc : 2<c)
    (hnotlong : c<Cut a b 1+1)
    (hnotleft : ¬OuterAvailable a b 1 c)
    (hnotright : ¬OuterAvailable b a 1 c)
    (hexc : ¬(a=4∧b=4∧c=3)∧¬(a=5∧b=5∧c=6))
    (hA : a%2=1) (hB : b%2=0) (hC : c%2=1) :
    CentralSpliceAvailable a b (c/2) := by
  unfold CentralSpliceAvailable CentralSplice
  norm_num [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, Cut,V,U,OuterAvailable] at *
  omega

private theorem flat_H1SpliceCoverage_splice_d1_110 (a b c : ℕ) (ha : 1≤a) (hab : a≤b) (hc : 2<c)
    (hnotlong : c<Cut a b 1+1)
    (hnotleft : ¬OuterAvailable a b 1 c)
    (hnotright : ¬OuterAvailable b a 1 c)
    (hexc : ¬(a=4∧b=4∧c=3)∧¬(a=5∧b=5∧c=6))
    (hA : a%2=1) (hB : b%2=1) (hC : c%2=0) :
    CentralSpliceAvailable a b (c/2) := by
  unfold CentralSpliceAvailable CentralSplice
  norm_num [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, Cut,V,U,OuterAvailable] at *
  omega

private theorem flat_H1SpliceCoverage_splice_d1_111 (a b c : ℕ) (ha : 1≤a) (hab : a≤b) (hc : 2<c)
    (hnotlong : c<Cut a b 1+1)
    (hnotleft : ¬OuterAvailable a b 1 c)
    (hnotright : ¬OuterAvailable b a 1 c)
    (hexc : ¬(a=4∧b=4∧c=3)∧¬(a=5∧b=5∧c=6))
    (hA : a%2=1) (hB : b%2=1) (hC : c%2=1) :
    CentralSpliceAvailable a b (c/2) := by
  unfold CentralSpliceAvailable CentralSplice
  norm_num [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, Cut,V,U,OuterAvailable] at *
  omega

private theorem flat_H1SpliceCoverage_splice_d2_0000 (a b d c : ℕ) (ha : 1≤a) (hab : a≤b) (hd : 2≤d) (hc : 2*d<c)
    (hnotlong : c<Cut a b d+1)
    (hnotleft : ¬OuterAvailable a b d c)
    (hnotright : ¬OuterAvailable b a d c)
    (hA : a%2=0) (hB : b%2=0) (hC : c%2=0) (hD : d%2=0) :
    CentralSpliceAvailable a b ((d+c-3)/2) ∨
      CentralSpliceAvailable a b ((d+c-3)/2-1) := by
  unfold CentralSpliceAvailable CentralSplice
  simp only [Cut,V,U,OuterAvailable,hD] at *
  norm_num [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero] at *
  omega

private theorem flat_H1SpliceCoverage_splice_d2_0001 (a b d c : ℕ) (ha : 1≤a) (hab : a≤b) (hd : 2≤d) (hc : 2*d<c)
    (hnotlong : c<Cut a b d+1)
    (hnotleft : ¬OuterAvailable a b d c)
    (hnotright : ¬OuterAvailable b a d c)
    (hA : a%2=0) (hB : b%2=0) (hC : c%2=0) (hD : d%2=1) :
    CentralSpliceAvailable a b ((d+c-3)/2) ∨
      CentralSpliceAvailable a b ((d+c-3)/2-1) := by
  unfold CentralSpliceAvailable CentralSplice
  simp only [Cut,V,U,OuterAvailable,hD] at *
  norm_num [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero] at *
  omega

private theorem flat_H1SpliceCoverage_splice_d2_0010 (a b d c : ℕ) (ha : 1≤a) (hab : a≤b) (hd : 2≤d) (hc : 2*d<c)
    (hnotlong : c<Cut a b d+1)
    (hnotleft : ¬OuterAvailable a b d c)
    (hnotright : ¬OuterAvailable b a d c)
    (hA : a%2=0) (hB : b%2=0) (hC : c%2=1) (hD : d%2=0) :
    CentralSpliceAvailable a b ((d+c-3)/2) ∨
      CentralSpliceAvailable a b ((d+c-3)/2-1) := by
  unfold CentralSpliceAvailable CentralSplice
  simp only [Cut,V,U,OuterAvailable,hD] at *
  norm_num [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero] at *
  omega

private theorem flat_H1SpliceCoverage_splice_d2_0011 (a b d c : ℕ) (ha : 1≤a) (hab : a≤b) (hd : 2≤d) (hc : 2*d<c)
    (hnotlong : c<Cut a b d+1)
    (hnotleft : ¬OuterAvailable a b d c)
    (hnotright : ¬OuterAvailable b a d c)
    (hA : a%2=0) (hB : b%2=0) (hC : c%2=1) (hD : d%2=1) :
    CentralSpliceAvailable a b ((d+c-3)/2) ∨
      CentralSpliceAvailable a b ((d+c-3)/2-1) := by
  unfold CentralSpliceAvailable CentralSplice
  simp only [Cut,V,U,OuterAvailable,hD] at *
  norm_num [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero] at *
  omega

private theorem flat_H1SpliceCoverage_splice_d2_0100 (a b d c : ℕ) (ha : 1≤a) (hab : a≤b) (hd : 2≤d) (hc : 2*d<c)
    (hnotlong : c<Cut a b d+1)
    (hnotleft : ¬OuterAvailable a b d c)
    (hnotright : ¬OuterAvailable b a d c)
    (hA : a%2=0) (hB : b%2=1) (hC : c%2=0) (hD : d%2=0) :
    CentralSpliceAvailable a b ((d+c-3)/2) ∨
      CentralSpliceAvailable a b ((d+c-3)/2-1) := by
  unfold CentralSpliceAvailable CentralSplice
  simp only [Cut,V,U,OuterAvailable,hD] at *
  norm_num [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero] at *
  omega

private theorem flat_H1SpliceCoverage_splice_d2_0101 (a b d c : ℕ) (ha : 1≤a) (hab : a≤b) (hd : 2≤d) (hc : 2*d<c)
    (hnotlong : c<Cut a b d+1)
    (hnotleft : ¬OuterAvailable a b d c)
    (hnotright : ¬OuterAvailable b a d c)
    (hA : a%2=0) (hB : b%2=1) (hC : c%2=0) (hD : d%2=1) :
    CentralSpliceAvailable a b ((d+c-3)/2) ∨
      CentralSpliceAvailable a b ((d+c-3)/2-1) := by
  unfold CentralSpliceAvailable CentralSplice
  simp only [Cut,V,U,OuterAvailable,hD] at *
  norm_num [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero] at *
  omega

private theorem flat_H1SpliceCoverage_splice_d2_0110 (a b d c : ℕ) (ha : 1≤a) (hab : a≤b) (hd : 2≤d) (hc : 2*d<c)
    (hnotlong : c<Cut a b d+1)
    (hnotleft : ¬OuterAvailable a b d c)
    (hnotright : ¬OuterAvailable b a d c)
    (hA : a%2=0) (hB : b%2=1) (hC : c%2=1) (hD : d%2=0) :
    CentralSpliceAvailable a b ((d+c-3)/2) ∨
      CentralSpliceAvailable a b ((d+c-3)/2-1) := by
  unfold CentralSpliceAvailable CentralSplice
  simp only [Cut,V,U,OuterAvailable,hD] at *
  norm_num [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero] at *
  omega

private theorem flat_H1SpliceCoverage_splice_d2_0111 (a b d c : ℕ) (ha : 1≤a) (hab : a≤b) (hd : 2≤d) (hc : 2*d<c)
    (hnotlong : c<Cut a b d+1)
    (hnotleft : ¬OuterAvailable a b d c)
    (hnotright : ¬OuterAvailable b a d c)
    (hA : a%2=0) (hB : b%2=1) (hC : c%2=1) (hD : d%2=1) :
    CentralSpliceAvailable a b ((d+c-3)/2) ∨
      CentralSpliceAvailable a b ((d+c-3)/2-1) := by
  unfold CentralSpliceAvailable CentralSplice
  simp only [Cut,V,U,OuterAvailable,hD] at *
  norm_num [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero] at *
  omega

private theorem flat_H1SpliceCoverage_splice_d2_1000 (a b d c : ℕ) (ha : 1≤a) (hab : a≤b) (hd : 2≤d) (hc : 2*d<c)
    (hnotlong : c<Cut a b d+1)
    (hnotleft : ¬OuterAvailable a b d c)
    (hnotright : ¬OuterAvailable b a d c)
    (hA : a%2=1) (hB : b%2=0) (hC : c%2=0) (hD : d%2=0) :
    CentralSpliceAvailable a b ((d+c-3)/2) ∨
      CentralSpliceAvailable a b ((d+c-3)/2-1) := by
  unfold CentralSpliceAvailable CentralSplice
  simp only [Cut,V,U,OuterAvailable,hD] at *
  norm_num [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero] at *
  omega

private theorem flat_H1SpliceCoverage_splice_d2_1001 (a b d c : ℕ) (ha : 1≤a) (hab : a≤b) (hd : 2≤d) (hc : 2*d<c)
    (hnotlong : c<Cut a b d+1)
    (hnotleft : ¬OuterAvailable a b d c)
    (hnotright : ¬OuterAvailable b a d c)
    (hA : a%2=1) (hB : b%2=0) (hC : c%2=0) (hD : d%2=1) :
    CentralSpliceAvailable a b ((d+c-3)/2) ∨
      CentralSpliceAvailable a b ((d+c-3)/2-1) := by
  unfold CentralSpliceAvailable CentralSplice
  simp only [Cut,V,U,OuterAvailable,hD] at *
  norm_num [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero] at *
  omega

private theorem flat_H1SpliceCoverage_splice_d2_1010 (a b d c : ℕ) (ha : 1≤a) (hab : a≤b) (hd : 2≤d) (hc : 2*d<c)
    (hnotlong : c<Cut a b d+1)
    (hnotleft : ¬OuterAvailable a b d c)
    (hnotright : ¬OuterAvailable b a d c)
    (hA : a%2=1) (hB : b%2=0) (hC : c%2=1) (hD : d%2=0) :
    CentralSpliceAvailable a b ((d+c-3)/2) ∨
      CentralSpliceAvailable a b ((d+c-3)/2-1) := by
  unfold CentralSpliceAvailable CentralSplice
  simp only [Cut,V,U,OuterAvailable,hD] at *
  norm_num [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero] at *
  omega

private theorem flat_H1SpliceCoverage_splice_d2_1011 (a b d c : ℕ) (ha : 1≤a) (hab : a≤b) (hd : 2≤d) (hc : 2*d<c)
    (hnotlong : c<Cut a b d+1)
    (hnotleft : ¬OuterAvailable a b d c)
    (hnotright : ¬OuterAvailable b a d c)
    (hA : a%2=1) (hB : b%2=0) (hC : c%2=1) (hD : d%2=1) :
    CentralSpliceAvailable a b ((d+c-3)/2) ∨
      CentralSpliceAvailable a b ((d+c-3)/2-1) := by
  simp only [Cut,V,U,OuterAvailable,hD] at hnotlong hnotleft hnotright
  norm_num [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero] at hnotlong hnotleft hnotright
  left
  by_cases hS : (d+c-3)/2 ≤ a/2
  · left
    refine ⟨by omega,by omega,hS,by omega,by omega,by omega⟩
  · right; right
    refine ⟨by omega,Or.inl ?_⟩
    refine ⟨by omega,by omega,by omega,by omega,by omega,by omega⟩


private theorem flat_H1SpliceCoverage_splice_d2_1100 (a b d c : ℕ) (ha : 1≤a) (hab : a≤b) (hd : 2≤d) (hc : 2*d<c)
    (hnotlong : c<Cut a b d+1)
    (hnotleft : ¬OuterAvailable a b d c)
    (hnotright : ¬OuterAvailable b a d c)
    (hA : a%2=1) (hB : b%2=1) (hC : c%2=0) (hD : d%2=0) :
    CentralSpliceAvailable a b ((d+c-3)/2) ∨
      CentralSpliceAvailable a b ((d+c-3)/2-1) := by
  unfold CentralSpliceAvailable CentralSplice
  simp only [Cut,V,U,OuterAvailable,hD] at *
  norm_num [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero] at *
  omega

private theorem flat_H1SpliceCoverage_splice_d2_1101 (a b d c : ℕ) (ha : 1≤a) (hab : a≤b) (hd : 2≤d) (hc : 2*d<c)
    (hnotlong : c<Cut a b d+1)
    (hnotleft : ¬OuterAvailable a b d c)
    (hnotright : ¬OuterAvailable b a d c)
    (hA : a%2=1) (hB : b%2=1) (hC : c%2=0) (hD : d%2=1) :
    CentralSpliceAvailable a b ((d+c-3)/2) ∨
      CentralSpliceAvailable a b ((d+c-3)/2-1) := by
  unfold CentralSpliceAvailable CentralSplice
  simp only [Cut,V,U,OuterAvailable,hD] at *
  norm_num [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero] at *
  omega

private theorem flat_H1SpliceCoverage_splice_d2_1110 (a b d c : ℕ) (ha : 1≤a) (hab : a≤b) (hd : 2≤d) (hc : 2*d<c)
    (hnotlong : c<Cut a b d+1)
    (hnotleft : ¬OuterAvailable a b d c)
    (hnotright : ¬OuterAvailable b a d c)
    (hA : a%2=1) (hB : b%2=1) (hC : c%2=1) (hD : d%2=0) :
    CentralSpliceAvailable a b ((d+c-3)/2) ∨
      CentralSpliceAvailable a b ((d+c-3)/2-1) := by
  unfold CentralSpliceAvailable CentralSplice
  simp only [Cut,V,U,OuterAvailable,hD] at *
  norm_num [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero] at *
  omega

private theorem flat_H1SpliceCoverage_splice_d2_1111 (a b d c : ℕ) (ha : 1≤a) (hab : a≤b) (hd : 2≤d) (hc : 2*d<c)
    (hnotlong : c<Cut a b d+1)
    (hnotleft : ¬OuterAvailable a b d c)
    (hnotright : ¬OuterAvailable b a d c)
    (hA : a%2=1) (hB : b%2=1) (hC : c%2=1) (hD : d%2=1) :
    CentralSpliceAvailable a b ((d+c-3)/2) ∨
      CentralSpliceAvailable a b ((d+c-3)/2-1) := by
  unfold CentralSpliceAvailable CentralSplice
  simp only [Cut,V,U,OuterAvailable,hD] at *
  norm_num [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero] at *
  omega

theorem h1_splice_d1 (a b c : ℕ) (ha : 1≤a) (hab : a≤b) (hc : 2<c)
    (hnotlong : c<Cut a b 1+1)
    (hnotleft : ¬OuterAvailable a b 1 c)
    (hnotright : ¬OuterAvailable b a 1 c)
    (hexc : ¬(a=4∧b=4∧c=3)∧¬(a=5∧b=5∧c=6)) :
    CentralSpliceAvailable a b (c/2) := by
  have ha2 : a%2=0 ∨ a%2=1 := by omega
  have hb2 : b%2=0 ∨ b%2=1 := by omega
  have hc2 : c%2=0 ∨ c%2=1 := by omega
  rcases ha2 with hA|hA <;> rcases hb2 with hB|hB <;> rcases hc2 with hC|hC

  · exact flat_H1SpliceCoverage_splice_d1_000 a b c ha hab hc hnotlong hnotleft hnotright hexc hA hB hC

  · exact flat_H1SpliceCoverage_splice_d1_001 a b c ha hab hc hnotlong hnotleft hnotright hexc hA hB hC

  · exact flat_H1SpliceCoverage_splice_d1_010 a b c ha hab hc hnotlong hnotleft hnotright hexc hA hB hC

  · exact flat_H1SpliceCoverage_splice_d1_011 a b c ha hab hc hnotlong hnotleft hnotright hexc hA hB hC

  · exact flat_H1SpliceCoverage_splice_d1_100 a b c ha hab hc hnotlong hnotleft hnotright hexc hA hB hC

  · exact flat_H1SpliceCoverage_splice_d1_101 a b c ha hab hc hnotlong hnotleft hnotright hexc hA hB hC

  · exact flat_H1SpliceCoverage_splice_d1_110 a b c ha hab hc hnotlong hnotleft hnotright hexc hA hB hC

  · exact flat_H1SpliceCoverage_splice_d1_111 a b c ha hab hc hnotlong hnotleft hnotright hexc hA hB hC


theorem h1_splice_d2 (a b d c : ℕ) (ha : 1≤a) (hab : a≤b) (hd : 2≤d) (hc : 2*d<c)
    (hnotlong : c<Cut a b d+1)
    (hnotleft : ¬OuterAvailable a b d c)
    (hnotright : ¬OuterAvailable b a d c) :
    CentralSpliceAvailable a b ((d+c-3)/2) ∨
      CentralSpliceAvailable a b ((d+c-3)/2-1) := by
  have ha2 : a%2=0 ∨ a%2=1 := by omega
  have hb2 : b%2=0 ∨ b%2=1 := by omega
  have hc2 : c%2=0 ∨ c%2=1 := by omega
  have hd2 : d%2=0 ∨ d%2=1 := by omega
  rcases ha2 with hA|hA <;> rcases hb2 with hB|hB <;> rcases hc2 with hC|hC <;> rcases hd2 with hD|hD

  · exact flat_H1SpliceCoverage_splice_d2_0000 a b d c ha hab hd hc hnotlong hnotleft hnotright hA hB hC hD

  · exact flat_H1SpliceCoverage_splice_d2_0001 a b d c ha hab hd hc hnotlong hnotleft hnotright hA hB hC hD

  · exact flat_H1SpliceCoverage_splice_d2_0010 a b d c ha hab hd hc hnotlong hnotleft hnotright hA hB hC hD

  · exact flat_H1SpliceCoverage_splice_d2_0011 a b d c ha hab hd hc hnotlong hnotleft hnotright hA hB hC hD

  · exact flat_H1SpliceCoverage_splice_d2_0100 a b d c ha hab hd hc hnotlong hnotleft hnotright hA hB hC hD

  · exact flat_H1SpliceCoverage_splice_d2_0101 a b d c ha hab hd hc hnotlong hnotleft hnotright hA hB hC hD

  · exact flat_H1SpliceCoverage_splice_d2_0110 a b d c ha hab hd hc hnotlong hnotleft hnotright hA hB hC hD

  · exact flat_H1SpliceCoverage_splice_d2_0111 a b d c ha hab hd hc hnotlong hnotleft hnotright hA hB hC hD

  · exact flat_H1SpliceCoverage_splice_d2_1000 a b d c ha hab hd hc hnotlong hnotleft hnotright hA hB hC hD

  · exact flat_H1SpliceCoverage_splice_d2_1001 a b d c ha hab hd hc hnotlong hnotleft hnotright hA hB hC hD

  · exact flat_H1SpliceCoverage_splice_d2_1010 a b d c ha hab hd hc hnotlong hnotleft hnotright hA hB hC hD

  · exact flat_H1SpliceCoverage_splice_d2_1011 a b d c ha hab hd hc hnotlong hnotleft hnotright hA hB hC hD

  · exact flat_H1SpliceCoverage_splice_d2_1100 a b d c ha hab hd hc hnotlong hnotleft hnotright hA hB hC hD

  · exact flat_H1SpliceCoverage_splice_d2_1101 a b d c ha hab hd hc hnotlong hnotleft hnotright hA hB hC hD

  · exact flat_H1SpliceCoverage_splice_d2_1110 a b d c ha hab hd hc hnotlong hnotleft hnotright hA hB hC hD

  · exact flat_H1SpliceCoverage_splice_d2_1111 a b d c ha hab hd hc hnotlong hnotleft hnotright hA hB hC hD


end Bounty


/- Supporting module: ForkCertificates -/

namespace Bounty

/-- A finite list supplies a total label function, with arbitrary zero extension. -/
def forkListLabel (xs : List ℕ) (i : ℕ) : ℕ := xs[i]?.getD 0

/-- Explicit inverse tables make finite vertex and edge injectivity certificates
linear in the number of table lookups required for kernel verification. -/
def FastFiniteParentCertificate (N : ℕ) (parent : ℕ → ℕ)
    (labels vertexInverse edgeInverse : List ℕ) : Prop :=
  (∀ i : Fin (N+1), forkListLabel labels i.val ≤ N ∧
    forkListLabel vertexInverse (forkListLabel labels i.val) = i.val) ∧
  ∀ i : Fin N, forkListLabel edgeInverse
    (Nat.dist (forkListLabel labels (parent (i.val+1))) (forkListLabel labels (i.val+1))) = i.val

abbrev fastFiniteParentCertificateDecidable (N : ℕ) (parent : ℕ → ℕ)
    (labels vertexInverse edgeInverse : List ℕ) :
    Decidable (FastFiniteParentCertificate N parent labels vertexInverse edgeInverse) := by
  unfold FastFiniteParentCertificate
  infer_instance

theorem FastFiniteParentCertificate.toNat {N : ℕ} {parent : ℕ → ℕ}
    {labels vertexInverse edgeInverse : List ℕ}
    (h : FastFiniteParentCertificate N parent labels vertexInverse edgeInverse) :
    NatParentCertificate N parent (forkListLabel labels) := by
  refine ⟨?_,?_,?_⟩
  · intro i j hi hj heq
    have h1 := (h.1 ⟨i,by omega⟩).2
    have h2 := (h.1 ⟨j,by omega⟩).2
    dsimp only at h1 h2
    rw [heq] at h1
    exact h1.symm.trans h2
  · intro i hi
    exact (h.1 ⟨i,by omega⟩).1
  · intro i j hi hib hj hjb heq
    have h1 := h.2 ⟨i-1,by omega⟩
    have h2 := h.2 ⟨j-1,by omega⟩
    dsimp only at h1 h2
    rw [show i-1+1=i by omega] at h1
    rw [show j-1+1=j by omega] at h2
    rw [heq] at h1
    omega

theorem rootedFork_of_fast_certificate {a b d c : ℕ} {labels vertexInverse edgeInverse : List ℕ}
    (h : FastFiniteParentCertificate (a+b+(d+c)) (forkParent a b)
      labels vertexInverse edgeInverse)
    (hz : forkListLabel labels (a+b+d)=0) : RootedFork a b d c :=
  ⟨forkListLabel labels,h.toNat,hz⟩

end Bounty


/- Supporting module: NeighborFinite -/


namespace Bounty

/-- A path with zero at the graft root and a specified endpoint offset. -/
def NeighborAlphaPath (d c r : ℕ) : Prop :=
  ∃ p k, NatAlphaPath (d+c) p k ∧ p (d-1)=0 ∧
    p 0=(if d%2=1 then r else d+c-1-r)

private theorem flat_NeighborFinite_neighbor_2_5_1 : NeighborAlphaPath 2 5 1 := by
  let p : Fin 7 → ℕ := ![5,0,6,2,3,1,4]
  have hp : FiniteAlphaPath 7 p 2 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 2, hp.toNat, rfl, rfl⟩

private theorem flat_NeighborFinite_neighbor_2_5_2 : NeighborAlphaPath 2 5 2 := by
  let p : Fin 7 → ℕ := ![4,0,6,1,3,2,5]
  have hp : FiniteAlphaPath 7 p 2 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 2, hp.toNat, rfl, rfl⟩

private theorem flat_NeighborFinite_neighbor_2_7_1 : NeighborAlphaPath 2 7 1 := by
  let p : Fin 9 → ℕ := ![7,0,8,2,6,1,4,3,5]
  have hp : FiniteAlphaPath 9 p 3 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 3, hp.toNat, rfl, rfl⟩

private theorem flat_NeighborFinite_neighbor_2_8_1 : NeighborAlphaPath 2 8 1 := by
  let p : Fin 10 → ℕ := ![8,0,9,2,7,1,5,4,6,3]
  have hp : FiniteAlphaPath 10 p 4 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 4, hp.toNat, rfl, rfl⟩

private theorem flat_NeighborFinite_neighbor_2_8_2 : NeighborAlphaPath 2 8 2 := by
  let p : Fin 10 → ℕ := ![7,0,9,1,5,4,6,3,8,2]
  have hp : FiniteAlphaPath 10 p 4 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 4, hp.toNat, rfl, rfl⟩

private theorem flat_NeighborFinite_neighbor_2_9_1 : NeighborAlphaPath 2 9 1 := by
  let p : Fin 11 → ℕ := ![9,0,10,2,7,1,8,4,5,3,6]
  have hp : FiniteAlphaPath 11 p 4 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 4, hp.toNat, rfl, rfl⟩

private theorem flat_NeighborFinite_neighbor_2_9_2 : NeighborAlphaPath 2 9 2 := by
  let p : Fin 11 → ℕ := ![8,0,10,1,6,4,5,2,9,3,7]
  have hp : FiniteAlphaPath 11 p 4 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 4, hp.toNat, rfl, rfl⟩

private theorem flat_NeighborFinite_neighbor_2_10_1 : NeighborAlphaPath 2 10 1 := by
  let p : Fin 12 → ℕ := ![10,0,11,2,9,1,7,3,8,5,6,4]
  have hp : FiniteAlphaPath 12 p 5 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 5, hp.toNat, rfl, rfl⟩

private theorem flat_NeighborFinite_neighbor_2_10_2 : NeighborAlphaPath 2 10 2 := by
  let p : Fin 12 → ℕ := ![9,0,11,1,8,2,10,5,6,4,7,3]
  have hp : FiniteAlphaPath 12 p 5 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 5, hp.toNat, rfl, rfl⟩

private theorem flat_NeighborFinite_neighbor_2_11_1 : NeighborAlphaPath 2 11 1 := by
  let p : Fin 13 → ℕ := ![11,0,12,2,9,1,10,4,6,5,8,3,7]
  have hp : FiniteAlphaPath 13 p 5 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 5, hp.toNat, rfl, rfl⟩

private theorem flat_NeighborFinite_neighbor_2_11_2 : NeighborAlphaPath 2 11 2 := by
  let p : Fin 13 → ℕ := ![10,0,12,1,9,3,7,2,11,4,6,5,8]
  have hp : FiniteAlphaPath 13 p 5 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 5, hp.toNat, rfl, rfl⟩

private theorem flat_NeighborFinite_neighbor_2_12_1 : NeighborAlphaPath 2 12 1 := by
  let p : Fin 14 → ℕ := ![12,0,13,2,10,1,11,4,7,6,8,3,9,5]
  have hp : FiniteAlphaPath 14 p 6 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 6, hp.toNat, rfl, rfl⟩

private theorem flat_NeighborFinite_neighbor_2_12_2 : NeighborAlphaPath 2 12 2 := by
  let p : Fin 14 → ℕ := ![11,0,13,1,10,3,9,5,8,6,7,2,12,4]
  have hp : FiniteAlphaPath 14 p 6 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 6, hp.toNat, rfl, rfl⟩

private theorem flat_NeighborFinite_neighbor_3_7_1 : NeighborAlphaPath 3 7 1 := by
  let p : Fin 10 → ℕ := ![1,9,0,7,3,8,2,5,4,6]
  have hp : FiniteAlphaPath 10 p 4 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 4, hp.toNat, rfl, rfl⟩

private theorem flat_NeighborFinite_neighbor_3_7_2 : NeighborAlphaPath 3 7 2 := by
  let p : Fin 10 → ℕ := ![2,9,0,8,4,5,3,6,1,7]
  have hp : FiniteAlphaPath 10 p 4 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 4, hp.toNat, rfl, rfl⟩

private theorem flat_NeighborFinite_neighbor_3_8_1 : NeighborAlphaPath 3 8 1 := by
  let p : Fin 11 → ℕ := ![1,9,0,10,3,6,5,7,2,8,4]
  have hp : FiniteAlphaPath 11 p 5 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 5, hp.toNat, rfl, rfl⟩

private theorem flat_NeighborFinite_neighbor_3_8_2 : NeighborAlphaPath 3 8 2 := by
  let p : Fin 11 → ℕ := ![2,10,0,9,4,8,1,7,5,6,3]
  have hp : FiniteAlphaPath 11 p 5 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 5, hp.toNat, rfl, rfl⟩

private theorem flat_NeighborFinite_neighbor_3_9_1 : NeighborAlphaPath 3 9 1 := by
  let p : Fin 12 → ℕ := ![1,11,0,9,2,10,4,8,3,6,5,7]
  have hp : FiniteAlphaPath 12 p 5 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 5, hp.toNat, rfl, rfl⟩

private theorem flat_NeighborFinite_neighbor_3_9_2 : NeighborAlphaPath 3 9 2 := by
  let p : Fin 12 → ℕ := ![2,11,0,10,3,6,5,7,1,9,4,8]
  have hp : FiniteAlphaPath 12 p 5 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 5, hp.toNat, rfl, rfl⟩

private theorem flat_NeighborFinite_neighbor_3_10_1 : NeighborAlphaPath 3 10 1 := by
  let p : Fin 13 → ℕ := ![1,11,0,12,3,10,2,8,6,7,4,9,5]
  have hp : FiniteAlphaPath 13 p 6 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 6, hp.toNat, rfl, rfl⟩

private theorem flat_NeighborFinite_neighbor_3_10_2 : NeighborAlphaPath 3 10 2 := by
  let p : Fin 13 → ℕ := ![2,12,0,11,5,7,6,9,1,10,3,8,4]
  have hp : FiniteAlphaPath 13 p 6 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 6, hp.toNat, rfl, rfl⟩

private theorem flat_NeighborFinite_neighbor_3_11_1 : NeighborAlphaPath 3 11 1 := by
  let p : Fin 14 → ℕ := ![1,13,0,11,3,12,2,9,5,10,4,7,6,8]
  have hp : FiniteAlphaPath 14 p 6 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 6, hp.toNat, rfl, rfl⟩

private theorem flat_NeighborFinite_neighbor_3_11_2 : NeighborAlphaPath 3 11 2 := by
  let p : Fin 14 → ℕ := ![2,13,0,12,3,8,5,7,6,10,4,11,1,9]
  have hp : FiniteAlphaPath 14 p 6 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 6, hp.toNat, rfl, rfl⟩

private theorem flat_NeighborFinite_neighbor_3_12_1 : NeighborAlphaPath 3 12 1 := by
  let p : Fin 15 → ℕ := ![1,14,0,12,2,13,4,11,3,9,7,8,5,10,6]
  have hp : FiniteAlphaPath 15 p 7 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 7, hp.toNat, rfl, rfl⟩

private theorem flat_NeighborFinite_neighbor_3_12_2 : NeighborAlphaPath 3 12 2 := by
  let p : Fin 15 → ℕ := ![2,14,0,13,3,10,1,12,4,8,7,9,6,11,5]
  have hp : FiniteAlphaPath 15 p 7 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 7, hp.toNat, rfl, rfl⟩

private theorem flat_NeighborFinite_neighbor_3_13_1 : NeighborAlphaPath 3 13 1 := by
  let p : Fin 16 → ℕ := ![1,14,0,15,3,11,6,8,7,10,4,13,2,12,5,9]
  have hp : FiniteAlphaPath 16 p 7 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 7, hp.toNat, rfl, rfl⟩

private theorem flat_NeighborFinite_neighbor_3_13_2 : NeighborAlphaPath 3 13 2 := by
  let p : Fin 16 → ℕ := ![2,15,0,14,4,8,7,9,6,11,5,13,1,12,3,10]
  have hp : FiniteAlphaPath 16 p 7 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 7, hp.toNat, rfl, rfl⟩

private theorem flat_NeighborFinite_neighbor_4_9_1 : NeighborAlphaPath 4 9 1 := by
  let p : Fin 13 → ℕ := ![11,1,12,0,9,2,10,4,6,5,8,3,7]
  have hp : FiniteAlphaPath 13 p 5 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 5, hp.toNat, rfl, rfl⟩

private theorem flat_NeighborFinite_neighbor_4_9_2 : NeighborAlphaPath 4 9 2 := by
  let p : Fin 13 → ℕ := ![10,2,9,0,12,1,11,5,6,4,7,3,8]
  have hp : FiniteAlphaPath 13 p 5 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 5, hp.toNat, rfl, rfl⟩

private theorem flat_NeighborFinite_neighbor_4_10_1 : NeighborAlphaPath 4 10 1 := by
  let p : Fin 14 → ℕ := ![12,1,13,0,10,2,11,4,9,3,7,6,8,5]
  have hp : FiniteAlphaPath 14 p 6 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 6, hp.toNat, rfl, rfl⟩

private theorem flat_NeighborFinite_neighbor_4_10_2 : NeighborAlphaPath 4 10 2 := by
  let p : Fin 14 → ℕ := ![11,2,10,0,13,1,12,5,9,3,8,6,7,4]
  have hp : FiniteAlphaPath 14 p 6 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 6, hp.toNat, rfl, rfl⟩

private theorem flat_NeighborFinite_neighbor_4_11_1 : NeighborAlphaPath 4 11 1 := by
  let p : Fin 15 → ℕ := ![13,2,12,0,14,1,10,5,7,6,9,3,11,4,8]
  have hp : FiniteAlphaPath 15 p 6 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 6, hp.toNat, rfl, rfl⟩

private theorem flat_NeighborFinite_neighbor_4_11_2 : NeighborAlphaPath 4 11 2 := by
  let p : Fin 15 → ℕ := ![12,1,13,0,14,4,7,6,8,3,10,2,11,5,9]
  have hp : FiniteAlphaPath 15 p 6 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 6, hp.toNat, rfl, rfl⟩

private theorem flat_NeighborFinite_neighbor_4_12_1 : NeighborAlphaPath 4 12 1 := by
  let p : Fin 16 → ℕ := ![14,2,13,0,15,1,11,5,8,7,9,4,12,3,10,6]
  have hp : FiniteAlphaPath 16 p 7 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 7, hp.toNat, rfl, rfl⟩

private theorem flat_NeighborFinite_neighbor_4_12_2 : NeighborAlphaPath 4 12 2 := by
  let p : Fin 16 → ℕ := ![13,1,14,0,15,4,8,7,9,6,12,2,11,3,10,5]
  have hp : FiniteAlphaPath 16 p 7 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 7, hp.toNat, rfl, rfl⟩

private theorem flat_NeighborFinite_neighbor_4_13_1 : NeighborAlphaPath 4 13 1 := by
  let p : Fin 17 → ℕ := ![15,1,16,0,13,4,10,7,8,6,11,3,14,2,12,5,9]
  have hp : FiniteAlphaPath 17 p 7 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 7, hp.toNat, rfl, rfl⟩

private theorem flat_NeighborFinite_neighbor_4_13_2 : NeighborAlphaPath 4 13 2 := by
  let p : Fin 17 → ℕ := ![14,1,15,0,16,4,11,5,9,6,8,7,12,3,13,2,10]
  have hp : FiniteAlphaPath 17 p 7 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 7, hp.toNat, rfl, rfl⟩

private theorem flat_NeighborFinite_neighbor_5_11_1 : NeighborAlphaPath 5 11 1 := by
  let p : Fin 16 → ℕ := ![1,13,2,15,0,14,4,12,3,10,5,11,7,8,6,9]
  have hp : FiniteAlphaPath 16 p 7 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 7, hp.toNat, rfl, rfl⟩

private theorem flat_NeighborFinite_neighbor_5_11_2 : NeighborAlphaPath 5 11 2 := by
  let p : Fin 16 → ℕ := ![2,13,1,14,0,15,5,12,3,11,7,8,6,9,4,10]
  have hp : FiniteAlphaPath 16 p 7 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 7, hp.toNat, rfl, rfl⟩

private theorem flat_NeighborFinite_neighbor_5_12_1 : NeighborAlphaPath 5 12 1 := by
  let p : Fin 17 → ℕ := ![1,14,3,15,0,16,2,12,6,9,8,10,5,13,4,11,7]
  have hp : FiniteAlphaPath 17 p 8 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 8, hp.toNat, rfl, rfl⟩

private theorem flat_NeighborFinite_neighbor_5_12_2 : NeighborAlphaPath 5 12 2 := by
  let p : Fin 17 → ℕ := ![2,15,4,14,0,16,1,13,7,10,8,9,5,12,3,11,6]
  have hp : FiniteAlphaPath 17 p 8 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 8, hp.toNat, rfl, rfl⟩

private theorem flat_NeighborFinite_neighbor_5_13_1 : NeighborAlphaPath 5 13 1 := by
  let p : Fin 18 → ℕ := ![1,15,3,16,0,17,2,13,6,11,5,14,4,12,8,9,7,10]
  have hp : FiniteAlphaPath 18 p 8 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 8, hp.toNat, rfl, rfl⟩

private theorem flat_NeighborFinite_neighbor_5_13_2 : NeighborAlphaPath 5 13 2 := by
  let p : Fin 18 → ℕ := ![2,13,4,14,0,17,1,16,3,15,7,10,8,9,5,12,6,11]
  have hp : FiniteAlphaPath 18 p 8 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 8, hp.toNat, rfl, rfl⟩

private theorem flat_NeighborFinite_neighbor_5_14_1 : NeighborAlphaPath 5 14 1 := by
  let p : Fin 19 → ℕ := ![1,16,2,18,0,17,4,13,5,15,3,14,7,10,9,11,6,12,8]
  have hp : FiniteAlphaPath 19 p 9 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 9, hp.toNat, rfl, rfl⟩

private theorem flat_NeighborFinite_neighbor_5_14_2 : NeighborAlphaPath 5 14 2 := by
  let p : Fin 19 → ℕ := ![2,17,3,16,0,18,1,13,6,12,4,15,5,14,9,10,8,11,7]
  have hp : FiniteAlphaPath 19 p 9 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 9, hp.toNat, rfl, rfl⟩

private theorem flat_NeighborFinite_neighbor_6_13_1 : NeighborAlphaPath 6 13 1 := by
  let p : Fin 19 → ℕ := ![17,2,14,3,16,0,18,1,15,5,13,4,11,7,12,6,9,8,10]
  have hp : FiniteAlphaPath 19 p 8 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 8, hp.toNat, rfl, rfl⟩

private theorem flat_NeighborFinite_neighbor_6_13_2 : NeighborAlphaPath 6 13 2 := by
  let p : Fin 19 → ℕ := ![16,5,12,6,14,0,18,1,17,2,15,3,13,4,9,8,10,7,11]
  have hp : FiniteAlphaPath 19 p 8 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 8, hp.toNat, rfl, rfl⟩

private theorem flat_NeighborFinite_neighbor_6_14_1 : NeighborAlphaPath 6 14 1 := by
  let p : Fin 20 → ℕ := ![18,2,16,1,19,0,17,4,15,3,13,7,10,9,11,6,14,5,12,8]
  have hp : FiniteAlphaPath 20 p 9 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 9, hp.toNat, rfl, rfl⟩

private theorem flat_NeighborFinite_neighbor_6_14_2 : NeighborAlphaPath 6 14 2 := by
  let p : Fin 20 → ℕ := ![17,5,14,4,15,0,19,1,18,2,16,3,11,8,10,9,13,6,12,7]
  have hp : FiniteAlphaPath 20 p 9 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 9, hp.toNat, rfl, rfl⟩

private theorem flat_NeighborFinite_neighbor_7_15_1 : NeighborAlphaPath 7 15 1 := by
  let p : Fin 22 → ℕ := ![1,19,4,18,2,21,0,20,3,16,7,13,9,14,6,17,5,15,8,11,10,12]
  have hp : FiniteAlphaPath 22 p 10 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 10, hp.toNat, rfl, rfl⟩

private theorem flat_NeighborFinite_neighbor_7_15_2 : NeighborAlphaPath 7 15 2 := by
  let p : Fin 22 → ℕ := ![2,20,5,18,1,21,0,19,3,17,7,16,4,15,10,11,9,12,8,14,6,13]
  have hp : FiniteAlphaPath 22 p 10 := by unfold FiniteAlphaPath Function.Injective; decide
  exact ⟨finitePathLabel p, 10, hp.toNat, rfl, rfl⟩

theorem neighbor_finite_one {d c : ℕ} (hd : 2≤d) (hc : 2*d<c)
    (hb : 2*c<d+24) (hne : d≠2 ∨ c≠6) : NeighborAlphaPath d c 1 := by
  have hd' : d≤7 := by omega
  interval_cases d
  · have hc' : c=5 ∨ c=7 ∨ c=8 ∨ c=9 ∨ c=10 ∨ c=11 ∨ c=12 := by omega
    rcases hc' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact flat_NeighborFinite_neighbor_2_5_1
    · exact flat_NeighborFinite_neighbor_2_7_1
    · exact flat_NeighborFinite_neighbor_2_8_1
    · exact flat_NeighborFinite_neighbor_2_9_1
    · exact flat_NeighborFinite_neighbor_2_10_1
    · exact flat_NeighborFinite_neighbor_2_11_1
    · exact flat_NeighborFinite_neighbor_2_12_1
  · have hc' : c=7 ∨ c=8 ∨ c=9 ∨ c=10 ∨ c=11 ∨ c=12 ∨ c=13 := by omega
    rcases hc' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact flat_NeighborFinite_neighbor_3_7_1
    · exact flat_NeighborFinite_neighbor_3_8_1
    · exact flat_NeighborFinite_neighbor_3_9_1
    · exact flat_NeighborFinite_neighbor_3_10_1
    · exact flat_NeighborFinite_neighbor_3_11_1
    · exact flat_NeighborFinite_neighbor_3_12_1
    · exact flat_NeighborFinite_neighbor_3_13_1
  · have hc' : c=9 ∨ c=10 ∨ c=11 ∨ c=12 ∨ c=13 := by omega
    rcases hc' with rfl | rfl | rfl | rfl | rfl
    · exact flat_NeighborFinite_neighbor_4_9_1
    · exact flat_NeighborFinite_neighbor_4_10_1
    · exact flat_NeighborFinite_neighbor_4_11_1
    · exact flat_NeighborFinite_neighbor_4_12_1
    · exact flat_NeighborFinite_neighbor_4_13_1
  · have hc' : c=11 ∨ c=12 ∨ c=13 ∨ c=14 := by omega
    rcases hc' with rfl | rfl | rfl | rfl
    · exact flat_NeighborFinite_neighbor_5_11_1
    · exact flat_NeighborFinite_neighbor_5_12_1
    · exact flat_NeighborFinite_neighbor_5_13_1
    · exact flat_NeighborFinite_neighbor_5_14_1
  · have hc' : c=13 ∨ c=14 := by omega
    rcases hc' with rfl | rfl
    · exact flat_NeighborFinite_neighbor_6_13_1
    · exact flat_NeighborFinite_neighbor_6_14_1
  · have hc' : c=15 := by omega
    subst c
    exact flat_NeighborFinite_neighbor_7_15_1

theorem neighbor_finite_two {d c : ℕ} (hd : 2≤d) (hc : 2*d<c)
    (hb : 2*c<d+24) (hne6 : d≠2 ∨ c≠6) (hne7 : d≠2 ∨ c≠7) : NeighborAlphaPath d c 2 := by
  have hd' : d≤7 := by omega
  interval_cases d
  · have hc' : c=5 ∨ c=8 ∨ c=9 ∨ c=10 ∨ c=11 ∨ c=12 := by omega
    rcases hc' with rfl | rfl | rfl | rfl | rfl | rfl
    · exact flat_NeighborFinite_neighbor_2_5_2
    · exact flat_NeighborFinite_neighbor_2_8_2
    · exact flat_NeighborFinite_neighbor_2_9_2
    · exact flat_NeighborFinite_neighbor_2_10_2
    · exact flat_NeighborFinite_neighbor_2_11_2
    · exact flat_NeighborFinite_neighbor_2_12_2
  · have hc' : c=7 ∨ c=8 ∨ c=9 ∨ c=10 ∨ c=11 ∨ c=12 ∨ c=13 := by omega
    rcases hc' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact flat_NeighborFinite_neighbor_3_7_2
    · exact flat_NeighborFinite_neighbor_3_8_2
    · exact flat_NeighborFinite_neighbor_3_9_2
    · exact flat_NeighborFinite_neighbor_3_10_2
    · exact flat_NeighborFinite_neighbor_3_11_2
    · exact flat_NeighborFinite_neighbor_3_12_2
    · exact flat_NeighborFinite_neighbor_3_13_2
  · have hc' : c=9 ∨ c=10 ∨ c=11 ∨ c=12 ∨ c=13 := by omega
    rcases hc' with rfl | rfl | rfl | rfl | rfl
    · exact flat_NeighborFinite_neighbor_4_9_2
    · exact flat_NeighborFinite_neighbor_4_10_2
    · exact flat_NeighborFinite_neighbor_4_11_2
    · exact flat_NeighborFinite_neighbor_4_12_2
    · exact flat_NeighborFinite_neighbor_4_13_2
  · have hc' : c=11 ∨ c=12 ∨ c=13 ∨ c=14 := by omega
    rcases hc' with rfl | rfl | rfl | rfl
    · exact flat_NeighborFinite_neighbor_5_11_2
    · exact flat_NeighborFinite_neighbor_5_12_2
    · exact flat_NeighborFinite_neighbor_5_13_2
    · exact flat_NeighborFinite_neighbor_5_14_2
  · have hc' : c=13 ∨ c=14 := by omega
    rcases hc' with rfl | rfl
    · exact flat_NeighborFinite_neighbor_6_13_2
    · exact flat_NeighborFinite_neighbor_6_14_2
  · have hc' : c=15 := by omega
    subst c
    exact flat_NeighborFinite_neighbor_7_15_2

theorem neighbor_exception_rooted : RootedFork 6 6 2 6 := by
  let labels : List ℕ := [9,12,7,15,8,14,4,13,11,10,6,17,5,18,0,20,1,16,3,19,2]
  let vi : List ℕ := [14,16,20,18,6,12,10,2,4,0,9,8,1,7,5,3,17,11,13,19,15]
  let ei : List ℕ := [0,8,7,0,9,1,4,3,2,6,5,10,11,17,12,16,18,19,13,15,14]
  have h : FastFiniteParentCertificate 20 (forkParent 6 6) labels vi ei := by
    let _ := fastFiniteParentCertificateDecidable 20 (forkParent 6 6) labels vi ei
    decide
  exact rootedFork_of_fast_certificate h (by decide)

theorem neighbor_exception_4_4_1_3 : RootedFork 4 4 1 3 := by
  let labels : List ℕ := [9,2,11,1,12,4,10,6,3,0,5,7,8]
  let vi : List ℕ := [9,3,1,8,5,10,7,11,12,0,6,2,4]
  let ei : List ℕ := [0,11,10,7,6,9,5,0,4,1,2,3,8]
  have h : FastFiniteParentCertificate 12 (forkParent 4 4) labels vi ei := by
    let _ := fastFiniteParentCertificateDecidable 12 (forkParent 4 4) labels vi ei
    decide
  exact rootedFork_of_fast_certificate h (by decide)

theorem neighbor_exception_5_5_1_6 : RootedFork 5 5 1 6 := by
  let labels : List ℕ := [9,10,7,12,8,15,4,6,14,5,11,0,17,1,13,3,16,2]
  let vi : List ℕ := [11,13,17,15,6,9,7,2,4,0,1,10,3,14,8,5,16,12]
  let ei : List ℕ := [0,0,6,1,3,2,9,4,7,8,14,5,13,15,16,10,12,11]
  have h : FastFiniteParentCertificate 17 (forkParent 5 5) labels vi ei := by
    let _ := fastFiniteParentCertificateDecidable 17 (forkParent 5 5) labels vi ei
    decide
  exact rootedFork_of_fast_certificate h (by decide)


end Bounty


/- Supporting module: ForkFirstRegion -/


namespace Bounty
open Math15.Graceful PathConstruction

/-- A prescribed label at the meeting point of two arms forming a path. -/
def PathVertexLabel (a b t : ℕ) : Prop :=
  ∃ f, NatGracefulPath (a+b+1) f ∧ f a=t

/-- In the first region, only the labels 1 and q-1 are required on the
old path; its labeling does not need to be alpha. -/
theorem rootedFork_first_region {a b d c : ℕ}
    (hd : 1 ≤ d) (hc : 1 ≤ c) (hq : 1 ≤ a+b) (hregion : c ≤ 2*d-16)
    (hbase : PathVertexLabel a b (if d%2=1 then a+b-1 else 1)) :
    RootedFork a b d c := by
  obtain ⟨A,B,P,hP,hlen,hpin⟩ := symbolic_proposition7 d c hd hc hregion
  obtain ⟨f,hf,hfa⟩ := hbase
  let low := decide (d%2=1)
  have hp := boundaryPath_alpha hP hlen low
  have hz : boundaryPath low A B P (d-1)=0 := by
    have hi : P[d-1]? = some (if low then L A else H B) := by
      simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, low] using hpin
    simp only [boundaryPath, symbolAt, hi, Option.getD_some]
    cases low <;> simp only [boundaryLabel, Bool.false_eq_true, ite_false, ite_true,
      Nat.sub_self]
  apply rootedFork_of_paths hd hf hp.1 (by have := hp.2.1; omega) hp.2.2 hz
  have hstart : boundaryPath low A B P 0 = boundaryLabel low A B (L 1) := by
    simp only [boundaryPath, symbolAt_zero, hP.main_start, Option.getD_some]
  rw [hstart, hfa]
  have hA : 1 ≤ A := by
    have hmem : L 1 ∈ P := List.mem_of_head? hP.main_start
    have hb := hP.symbol_bound hmem
    exact hb
  by_cases hd1 : d%2=1
  · simp only [low, hd1, decide_true, boundaryLabel, boundaryCut, ite_true]
    have hs : A-1 ≤ A := by omega
    simp only [shiftAboveCut, ite_eq_left hs]
    unfold Nat.dist
    omega
  · simp only [low, hd1, decide_false, boundaryLabel, boundaryCut, Bool.false_eq_true, ite_false]
    have hs : ¬B+1+1 ≤ B := by omega
    simp only [shiftAboveCut, ite_eq_right hs]
    unfold Nat.dist
    omega

end Bounty


/- Supporting module: CattellTwizzler -/

namespace Bounty

/-- The alternating extreme ordering of a path. -/
def cattellWalecki (n i : ℕ) : ℕ := if i%2=0 then i/2 else n-1-i/2

lemma cattellWalecki_bound {n i : ℕ} (hi : i < n) : cattellWalecki n i < n := by
  unfold cattellWalecki
  split_ifs  <;> omega

lemma cattellWalecki_inj {n i j : ℕ} (hi : i < n) (hj : j < n)
    (h : cattellWalecki n i=cattellWalecki n j) : i=j := by
  unfold cattellWalecki at h
  split_ifs at h  <;> omega

lemma cattellWalecki_diff {n i : ℕ} (hi : 0 < i) (hb : i < n) :
    Nat.dist (cattellWalecki n (i-1)) (cattellWalecki n i)=n-i := by
  unfold cattellWalecki Nat.dist
  split_ifs  <;> omega

lemma cattellWalecki_gap {n P i : ℕ} (hi : i < P) (hP : P ≤ n) :
    cattellWalecki n i < (P+1)/2 ∨ n-P+(P+1)/2 ≤ cattellWalecki n i := by
  unfold cattellWalecki
  split_ifs  <;> omega

/-- Reverse an outer Walecki segment, then fill the inner interval with a path. -/
def cattellTwizzler (n P : ℕ) (p : ℕ → ℕ) (i : ℕ) : ℕ :=
  if i < P then cattellWalecki n (P-1-i) else (P+1)/2+p (i-P)

lemma cattellTwizzler_prefix_diff {n P i : ℕ} {p : ℕ → ℕ}
    (hP : P ≤ n) (hi : 0 < i) (hib : i < P) :
    Nat.dist (cattellTwizzler n P p (i-1)) (cattellTwizzler n P p i)=n-P+i := by
  have hi' : i-1 < P := by omega
  simp only [cattellTwizzler,ite_eq_left hi',ite_eq_left hib]
  have h₁ : P-1-(i-1)=P-i := by omega
  have h₂ : P-1-i=P-i-1 := by omega
  rw [h₁,h₂,Nat.dist_comm,cattellWalecki_diff (by omega) (by omega)]
  omega

lemma cattellTwizzler_bridge_diff {n P : ℕ} {p : ℕ → ℕ}
    (hP : 0 < P) (hs : (P+1)/2 ≤ n-P) (hpin : p 0=n-P-(P+1)/2) :
    Nat.dist (cattellTwizzler n P p (P-1)) (cattellTwizzler n P p P)=n-P := by
  have hP' : P-1 < P := by omega
  simp only [cattellTwizzler,ite_eq_left hP',Nat.lt_irrefl,ite_false,Nat.sub_self,hpin]
  simp only [cattellWalecki,Nat.zero_mod,Nat.zero_div,↓reduceIte,Nat.dist_zero_left]
  omega

lemma cattellTwizzler_tail_diff {n P i : ℕ} {p : ℕ → ℕ} (hi : P < i) :
    Nat.dist (cattellTwizzler n P p (i-1)) (cattellTwizzler n P p i)=
      Nat.dist (p (i-P-1)) (p (i-P)) := by
  have hi' : ¬i-1 < P := by omega
  have hi'' : ¬i < P := by omega
  simp only [cattellTwizzler,ite_eq_right hi',ite_eq_right hi'']
  have heq : i-1-P=i-P-1 := by omega
  rw [heq]
  unfold Nat.dist
  omega

lemma cattellTwizzler_graceful {n P : ℕ} {p : ℕ → ℕ}
    (hP : 0 < P) (hPn : P < n) (hs : (P+1)/2 ≤ n-P)
    (hp : NatGracefulPath (n-P) p) (hpin : p 0=n-P-(P+1)/2) :
    NatGracefulPath n (cattellTwizzler n P p) := by
  refine ⟨?_,?_,?_⟩
  · intro i j hi hj heq
    by_cases hip : i < P  <;> by_cases hjp : j < P
    · simp only [cattellTwizzler,ite_eq_left hip,ite_eq_left hjp] at heq
      have hh := cattellWalecki_inj (by omega : P-1-i < n) (by omega : P-1-j < n) heq
      omega
    · simp only [cattellTwizzler,ite_eq_left hip,ite_eq_right hjp] at heq
      have hg := cattellWalecki_gap (by omega : P-1-i < P) (Nat.le_of_lt hPn)
      have hb := hp.2.1 (j-P) (by omega)
      omega
    · simp only [cattellTwizzler,ite_eq_right hip,ite_eq_left hjp] at heq
      have hg := cattellWalecki_gap (by omega : P-1-j < P) (Nat.le_of_lt hPn)
      have hb := hp.2.1 (i-P) (by omega)
      omega
    · simp only [cattellTwizzler,ite_eq_right hip,ite_eq_right hjp] at heq
      have hh := hp.1 (i-P) (j-P) (by omega) (by omega) (by omega)
      omega
  · intro i hi
    by_cases hip : i < P
    · simp only [cattellTwizzler,ite_eq_left hip]
      exact cattellWalecki_bound (by omega)
    · simp only [cattellTwizzler,ite_eq_right hip]
      have hb := hp.2.1 (i-P) (by omega)
      omega
  · intro i j hi hib hj hjb heq
    rcases lt_trichotomy i P with hip | hip | hip  <;>
      rcases lt_trichotomy j P with hjp | hjp | hjp
    · rw [cattellTwizzler_prefix_diff (by omega) hi hip,
        cattellTwizzler_prefix_diff (by omega) hj hjp] at heq
      omega
    · subst j
      rw [cattellTwizzler_prefix_diff (by omega) hi hip,
        cattellTwizzler_bridge_diff hP hs hpin] at heq
      omega
    · rw [cattellTwizzler_prefix_diff (by omega) hi hip,
        cattellTwizzler_tail_diff hjp] at heq
      have hb := hp.edge_lt (show 0 < j-P by omega) (show j-P < n-P by omega)
      omega
    · subst i
      rw [cattellTwizzler_bridge_diff hP hs hpin,
        cattellTwizzler_prefix_diff (by omega) hj hjp] at heq
      omega
    · omega
    · subst i
      rw [cattellTwizzler_bridge_diff hP hs hpin,cattellTwizzler_tail_diff hjp] at heq
      have hb := hp.edge_lt (show 0 < j-P by omega) (show j-P < n-P by omega)
      omega
    · rw [cattellTwizzler_tail_diff hip,
        cattellTwizzler_prefix_diff (by omega) hj hjp] at heq
      have hb := hp.edge_lt (show 0 < i-P by omega) (show i-P < n-P by omega)
      omega
    · subst j
      rw [cattellTwizzler_tail_diff hip,cattellTwizzler_bridge_diff hP hs hpin] at heq
      have hb := hp.edge_lt (show 0 < i-P by omega) (show i-P < n-P by omega)
      omega
    · rw [cattellTwizzler_tail_diff hip,cattellTwizzler_tail_diff hjp] at heq
      have hh := hp.2.2 (i-P) (j-P) (by omega) (by omega) (by omega) (by omega) heq
      omega

/-- Prescribe a label near an endpoint using an arbitrary graceful inner path. -/
theorem exists_graceful_path_twizzler {n i t : ℕ}
    (hsize : i+2*t+1 < n) (hroom : (i+2*t+2)/2 ≤ n-(i+2*t+1)) :
    ∃ p, NatGracefulPath n p ∧ p i=t := by
  let P := i+2*t+1
  have hP : 0 < P := by dsimp [P]; omega
  have hPn : P < n := hsize
  have hs : (P+1)/2 ≤ n-P := hroom
  have htail : n-P-(P+1)/2 < n-P := by dsimp [P] at *; omega
  obtain ⟨p,hp,hpin⟩ := exists_graceful_path_endpoint htail
  refine ⟨cattellTwizzler n P p,cattellTwizzler_graceful hP hPn hs hp hpin,?_⟩
  have hi : i < P := by dsimp [P]; omega
  simp only [cattellTwizzler,ite_eq_left hi]
  have heq : P-1-i=2*t := by dsimp [P]; omega
  rw [heq]
  simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, cattellWalecki]

/-- Fixed labels are available at every vertex once the order is large enough. -/
theorem exists_graceful_path_fixed_large {n i t : ℕ} (hi : i < n) (hn : 12*t+5 ≤ n) :
    ∃ p, NatGracefulPath n p ∧ p i=t := by
  by_cases hleft : 2*i ≤ n-1
  · exact exists_graceful_path_twizzler (by omega) (by omega)
  · obtain ⟨p,hp,hpin⟩ := exists_graceful_path_twizzler
      (n:=n) (i:=n-1-i) (t:=t) (by omega) (by omega)
    refine ⟨reverseNatPath n p,hp.reverse,?_⟩
    exact hpin

end Bounty


/- Supporting module: CattellFixed -/

namespace Bounty

/- Finite certificates complete the two fixed-label constructions below the
uniform twizzler bound. Every certificate is checked by kernel reduction. -/

private theorem flat_CattellFixed_cattellFixed_1_3_0 : ∃ p, NatGracefulPath 3 p ∧ p 0=1 := by
  let p : Fin 3 → ℕ := ![1,0,2]
  have hp : FiniteGracefulPath 3 p := by
    unfold FiniteGracefulPath Function.Injective
    decide
  exact ⟨finitePathLabel p,hp.toNat,rfl⟩

private theorem flat_CattellFixed_cattellFixed_1_5_1 : ∃ p, NatGracefulPath 5 p ∧ p 1=1 := by
  let p : Fin 5 → ℕ := ![2,1,3,0,4]
  have hp : FiniteGracefulPath 5 p := by
    unfold FiniteGracefulPath Function.Injective
    decide
  exact ⟨finitePathLabel p,hp.toNat,rfl⟩

private theorem flat_CattellFixed_cattellFixed_1_5_2 : ∃ p, NatGracefulPath 5 p ∧ p 2=1 := by
  let p : Fin 5 → ℕ := ![0,4,1,3,2]
  have hp : FiniteGracefulPath 5 p := by
    unfold FiniteGracefulPath Function.Injective
    decide
  exact ⟨finitePathLabel p,hp.toNat,rfl⟩

private theorem flat_CattellFixed_cattellFixed_1_7_2 : ∃ p, NatGracefulPath 7 p ∧ p 2=1 := by
  let p : Fin 7 → ℕ := ![4,2,1,5,0,6,3]
  have hp : FiniteGracefulPath 7 p := by
    unfold FiniteGracefulPath Function.Injective
    decide
  exact ⟨finitePathLabel p,hp.toNat,rfl⟩

private theorem flat_CattellFixed_cattellFixed_1_7_3 : ∃ p, NatGracefulPath 7 p ∧ p 3=1 := by
  let p : Fin 7 → ℕ := ![6,0,5,1,4,2,3]
  have hp : FiniteGracefulPath 7 p := by
    unfold FiniteGracefulPath Function.Injective
    decide
  exact ⟨finitePathLabel p,hp.toNat,rfl⟩

private theorem flat_CattellFixed_cattellFixed_1_9_4 : ∃ p, NatGracefulPath 9 p ∧ p 4=1 := by
  let p : Fin 9 → ℕ := ![5,6,0,8,1,4,2,7,3]
  have hp : FiniteGracefulPath 9 p := by
    unfold FiniteGracefulPath Function.Injective
    decide
  exact ⟨finitePathLabel p,hp.toNat,rfl⟩

private theorem flat_CattellFixed_cattellFixed_1_11_5 : ∃ p, NatGracefulPath 11 p ∧ p 5=1 := by
  let p : Fin 11 → ℕ := ![7,4,8,0,10,1,6,5,3,9,2]
  have hp : FiniteGracefulPath 11 p := by
    unfold FiniteGracefulPath Function.Injective
    decide
  exact ⟨finitePathLabel p,hp.toNat,rfl⟩

private theorem flat_CattellFixed_cattellFixed_1_13_6 : ∃ p, NatGracefulPath 13 p ∧ p 6=1 := by
  let p : Fin 13 → ℕ := ![5,8,4,10,0,12,1,6,7,9,2,11,3]
  have hp : FiniteGracefulPath 13 p := by
    unfold FiniteGracefulPath Function.Injective
    decide
  exact ⟨finitePathLabel p,hp.toNat,rfl⟩

private theorem flat_CattellFixed_cattellFixed_2_3_0 : ∃ p, NatGracefulPath 3 p ∧ p 0=2 := by
  let p : Fin 3 → ℕ := ![2,0,1]
  have hp : FiniteGracefulPath 3 p := by
    unfold FiniteGracefulPath Function.Injective
    decide
  exact ⟨finitePathLabel p,hp.toNat,rfl⟩

private theorem flat_CattellFixed_cattellFixed_2_3_1 : ∃ p, NatGracefulPath 3 p ∧ p 1=2 := by
  let p : Fin 3 → ℕ := ![0,2,1]
  have hp : FiniteGracefulPath 3 p := by
    unfold FiniteGracefulPath Function.Injective
    decide
  exact ⟨finitePathLabel p,hp.toNat,rfl⟩

private theorem flat_CattellFixed_cattellFixed_2_5_0 : ∃ p, NatGracefulPath 5 p ∧ p 0=2 := by
  let p : Fin 5 → ℕ := ![2,3,1,4,0]
  have hp : FiniteGracefulPath 5 p := by
    unfold FiniteGracefulPath Function.Injective
    decide
  exact ⟨finitePathLabel p,hp.toNat,rfl⟩

private theorem flat_CattellFixed_cattellFixed_2_5_1 : ∃ p, NatGracefulPath 5 p ∧ p 1=2 := by
  let p : Fin 5 → ℕ := ![1,2,4,0,3]
  have hp : FiniteGracefulPath 5 p := by
    unfold FiniteGracefulPath Function.Injective
    decide
  exact ⟨finitePathLabel p,hp.toNat,rfl⟩

private theorem flat_CattellFixed_cattellFixed_2_6_0 : ∃ p, NatGracefulPath 6 p ∧ p 0=2 := by
  let p : Fin 6 → ℕ := ![2,4,3,0,5,1]
  have hp : FiniteGracefulPath 6 p := by
    unfold FiniteGracefulPath Function.Injective
    decide
  exact ⟨finitePathLabel p,hp.toNat,rfl⟩

private theorem flat_CattellFixed_cattellFixed_2_6_1 : ∃ p, NatGracefulPath 6 p ∧ p 1=2 := by
  let p : Fin 6 → ℕ := ![4,2,3,0,5,1]
  have hp : FiniteGracefulPath 6 p := by
    unfold FiniteGracefulPath Function.Injective
    decide
  exact ⟨finitePathLabel p,hp.toNat,rfl⟩

private theorem flat_CattellFixed_cattellFixed_2_6_2 : ∃ p, NatGracefulPath 6 p ∧ p 2=2 := by
  let p : Fin 6 → ℕ := ![3,1,2,5,0,4]
  have hp : FiniteGracefulPath 6 p := by
    unfold FiniteGracefulPath Function.Injective
    decide
  exact ⟨finitePathLabel p,hp.toNat,rfl⟩

private theorem flat_CattellFixed_cattellFixed_2_7_0 : ∃ p, NatGracefulPath 7 p ∧ p 0=2 := by
  let p : Fin 7 → ℕ := ![2,4,5,1,6,0,3]
  have hp : FiniteGracefulPath 7 p := by
    unfold FiniteGracefulPath Function.Injective
    decide
  exact ⟨finitePathLabel p,hp.toNat,rfl⟩

private theorem flat_CattellFixed_cattellFixed_2_7_1 : ∃ p, NatGracefulPath 7 p ∧ p 1=2 := by
  let p : Fin 7 → ℕ := ![5,2,3,1,6,0,4]
  have hp : FiniteGracefulPath 7 p := by
    unfold FiniteGracefulPath Function.Injective
    decide
  exact ⟨finitePathLabel p,hp.toNat,rfl⟩

private theorem flat_CattellFixed_cattellFixed_2_7_2 : ∃ p, NatGracefulPath 7 p ∧ p 2=2 := by
  let p : Fin 7 → ℕ := ![3,4,2,5,1,6,0]
  have hp : FiniteGracefulPath 7 p := by
    unfold FiniteGracefulPath Function.Injective
    decide
  exact ⟨finitePathLabel p,hp.toNat,rfl⟩

private theorem flat_CattellFixed_cattellFixed_2_7_3 : ∃ p, NatGracefulPath 7 p ∧ p 3=2 := by
  let p : Fin 7 → ℕ := ![5,0,6,2,3,1,4]
  have hp : FiniteGracefulPath 7 p := by
    unfold FiniteGracefulPath Function.Injective
    decide
  exact ⟨finitePathLabel p,hp.toNat,rfl⟩

private theorem flat_CattellFixed_cattellFixed_2_9_2 : ∃ p, NatGracefulPath 9 p ∧ p 2=2 := by
  let p : Fin 9 → ℕ := ![3,6,2,4,5,0,8,1,7]
  have hp : FiniteGracefulPath 9 p := by
    unfold FiniteGracefulPath Function.Injective
    decide
  exact ⟨finitePathLabel p,hp.toNat,rfl⟩

private theorem flat_CattellFixed_cattellFixed_2_9_3 : ∃ p, NatGracefulPath 9 p ∧ p 3=2 := by
  let p : Fin 9 → ℕ := ![4,3,5,2,6,1,7,0,8]
  have hp : FiniteGracefulPath 9 p := by
    unfold FiniteGracefulPath Function.Injective
    decide
  exact ⟨finitePathLabel p,hp.toNat,rfl⟩

private theorem flat_CattellFixed_cattellFixed_2_9_4 : ∃ p, NatGracefulPath 9 p ∧ p 4=2 := by
  let p : Fin 9 → ℕ := ![0,8,1,7,2,6,3,5,4]
  have hp : FiniteGracefulPath 9 p := by
    unfold FiniteGracefulPath Function.Injective
    decide
  exact ⟨finitePathLabel p,hp.toNat,rfl⟩

private theorem flat_CattellFixed_cattellFixed_2_10_2 : ∃ p, NatGracefulPath 10 p ∧ p 2=2 := by
  let p : Fin 10 → ℕ := ![5,4,2,7,3,6,0,9,1,8]
  have hp : FiniteGracefulPath 10 p := by
    unfold FiniteGracefulPath Function.Injective
    decide
  exact ⟨finitePathLabel p,hp.toNat,rfl⟩

private theorem flat_CattellFixed_cattellFixed_2_10_3 : ∃ p, NatGracefulPath 10 p ∧ p 3=2 := by
  let p : Fin 10 → ℕ := ![4,6,5,2,7,3,9,0,8,1]
  have hp : FiniteGracefulPath 10 p := by
    unfold FiniteGracefulPath Function.Injective
    decide
  exact ⟨finitePathLabel p,hp.toNat,rfl⟩

private theorem flat_CattellFixed_cattellFixed_2_10_4 : ∃ p, NatGracefulPath 10 p ∧ p 4=2 := by
  let p : Fin 10 → ℕ := ![0,9,1,8,2,7,3,6,4,5]
  have hp : FiniteGracefulPath 10 p := by
    unfold FiniteGracefulPath Function.Injective
    decide
  exact ⟨finitePathLabel p,hp.toNat,rfl⟩

private theorem flat_CattellFixed_cattellFixed_2_11_3 : ∃ p, NatGracefulPath 11 p ∧ p 3=2 := by
  let p : Fin 11 → ℕ := ![9,0,10,2,8,1,6,3,7,5,4]
  have hp : FiniteGracefulPath 11 p := by
    unfold FiniteGracefulPath Function.Injective
    decide
  exact ⟨finitePathLabel p,hp.toNat,rfl⟩

private theorem flat_CattellFixed_cattellFixed_2_11_4 : ∃ p, NatGracefulPath 11 p ∧ p 4=2 := by
  let p : Fin 11 → ℕ := ![0,10,1,9,2,8,3,7,4,6,5]
  have hp : FiniteGracefulPath 11 p := by
    unfold FiniteGracefulPath Function.Injective
    decide
  exact ⟨finitePathLabel p,hp.toNat,rfl⟩

private theorem flat_CattellFixed_cattellFixed_2_11_5 : ∃ p, NatGracefulPath 11 p ∧ p 5=2 := by
  let p : Fin 11 → ℕ := ![3,5,9,0,10,2,8,1,6,7,4]
  have hp : FiniteGracefulPath 11 p := by
    unfold FiniteGracefulPath Function.Injective
    decide
  exact ⟨finitePathLabel p,hp.toNat,rfl⟩

private theorem flat_CattellFixed_cattellFixed_2_13_4 : ∃ p, NatGracefulPath 13 p ∧ p 4=2 := by
  let p : Fin 13 → ℕ := ![7,6,4,10,2,9,5,8,3,12,0,11,1]
  have hp : FiniteGracefulPath 13 p := by
    unfold FiniteGracefulPath Function.Injective
    decide
  exact ⟨finitePathLabel p,hp.toNat,rfl⟩

private theorem flat_CattellFixed_cattellFixed_2_13_5 : ∃ p, NatGracefulPath 13 p ∧ p 5=2 := by
  let p : Fin 13 → ℕ := ![5,8,4,6,7,2,10,3,9,0,12,1,11]
  have hp : FiniteGracefulPath 13 p := by
    unfold FiniteGracefulPath Function.Injective
    decide
  exact ⟨finitePathLabel p,hp.toNat,rfl⟩

private theorem flat_CattellFixed_cattellFixed_2_13_6 : ∃ p, NatGracefulPath 13 p ∧ p 6=2 := by
  let p : Fin 13 → ℕ := ![6,7,4,11,0,12,2,8,3,5,9,1,10]
  have hp : FiniteGracefulPath 13 p := by
    unfold FiniteGracefulPath Function.Injective
    decide
  exact ⟨finitePathLabel p,hp.toNat,rfl⟩

private theorem flat_CattellFixed_cattellFixed_2_14_5 : ∃ p, NatGracefulPath 14 p ∧ p 5=2 := by
  let p : Fin 14 → ℕ := ![6,8,7,4,11,2,10,5,9,3,13,0,12,1]
  have hp : FiniteGracefulPath 14 p := by
    unfold FiniteGracefulPath Function.Injective
    decide
  exact ⟨finitePathLabel p,hp.toNat,rfl⟩

private theorem flat_CattellFixed_cattellFixed_2_14_6 : ∃ p, NatGracefulPath 14 p ∧ p 6=2 := by
  let p : Fin 14 → ℕ := ![5,9,4,7,6,8,2,11,3,10,0,13,1,12]
  have hp : FiniteGracefulPath 14 p := by
    unfold FiniteGracefulPath Function.Injective
    decide
  exact ⟨finitePathLabel p,hp.toNat,rfl⟩

private theorem flat_CattellFixed_cattellFixed_2_15_6 : ∃ p, NatGracefulPath 15 p ∧ p 6=2 := by
  let p : Fin 15 → ℕ := ![8,7,5,9,6,11,2,12,4,10,3,14,0,13,1]
  have hp : FiniteGracefulPath 15 p := by
    unfold FiniteGracefulPath Function.Injective
    decide
  exact ⟨finitePathLabel p,hp.toNat,rfl⟩

private theorem flat_CattellFixed_cattellFixed_2_15_7 : ∃ p, NatGracefulPath 15 p ∧ p 7=2 := by
  let p : Fin 15 → ℕ := ![5,7,8,4,13,0,14,2,10,3,9,6,11,1,12]
  have hp : FiniteGracefulPath 15 p := by
    unfold FiniteGracefulPath Function.Injective
    decide
  exact ⟨finitePathLabel p,hp.toNat,rfl⟩

private theorem flat_CattellFixed_cattellFixed_2_17_7 : ∃ p, NatGracefulPath 17 p ∧ p 7=2 := by
  let p : Fin 17 → ℕ := ![9,6,8,7,11,3,14,2,12,5,10,4,13,0,16,1,15]
  have hp : FiniteGracefulPath 17 p := by
    unfold FiniteGracefulPath Function.Injective
    decide
  exact ⟨finitePathLabel p,hp.toNat,rfl⟩

private theorem flat_CattellFixed_cattellFixed_2_17_8 : ∃ p, NatGracefulPath 17 p ∧ p 8=2 := by
  let p : Fin 17 → ℕ := ![9,8,6,12,3,15,0,16,2,13,5,10,7,11,4,14,1]
  have hp : FiniteGracefulPath 17 p := by
    unfold FiniteGracefulPath Function.Injective
    decide
  exact ⟨finitePathLabel p,hp.toNat,rfl⟩

private theorem flat_CattellFixed_cattellFixed_2_18_8 : ∃ p, NatGracefulPath 18 p ∧ p 8=2 := by
  let p : Fin 18 → ℕ := ![9,8,6,10,7,12,3,15,2,13,5,11,4,14,0,17,1,16]
  have hp : FiniteGracefulPath 18 p := by
    unfold FiniteGracefulPath Function.Injective
    decide
  exact ⟨finitePathLabel p,hp.toNat,rfl⟩

private theorem flat_CattellFixed_cattellFixed_2_19_8 : ∃ p, NatGracefulPath 19 p ∧ p 8=2 := by
  let p : Fin 19 → ℕ := ![10,7,11,9,8,13,4,16,2,15,5,12,6,14,3,18,0,17,1]
  have hp : FiniteGracefulPath 19 p := by
    unfold FiniteGracefulPath Function.Injective
    decide
  exact ⟨finitePathLabel p,hp.toNat,rfl⟩

private theorem flat_CattellFixed_cattellFixed_2_19_9 : ∃ p, NatGracefulPath 19 p ∧ p 9=2 := by
  let p : Fin 19 → ℕ := ![9,11,8,7,14,3,17,0,18,2,15,5,10,6,12,4,13,1,16]
  have hp : FiniteGracefulPath 19 p := by
    unfold FiniteGracefulPath Function.Injective
    decide
  exact ⟨finitePathLabel p,hp.toNat,rfl⟩

private theorem flat_CattellFixed_cattellFixed_2_21_10 : ∃ p, NatGracefulPath 21 p ∧ p 10=2 := by
  let p : Fin 21 → ℕ := ![1,19,0,20,3,16,6,15,4,18,2,17,5,13,9,12,7,14,8,10,11]
  have hp : FiniteGracefulPath 21 p := by
    unfold FiniteGracefulPath Function.Injective
    decide
  exact ⟨finitePathLabel p,hp.toNat,rfl⟩

private theorem flat_CattellFixed_cattellFixed_2_22_10 : ∃ p, NatGracefulPath 22 p ∧ p 10=2 := by
  let p : Fin 22 → ℕ := ![11,8,14,7,12,10,9,13,5,17,2,19,3,16,6,15,4,18,0,21,1,20]
  have hp : FiniteGracefulPath 22 p := by
    unfold FiniteGracefulPath Function.Injective
    decide
  exact ⟨finitePathLabel p,hp.toNat,rfl⟩

private theorem flat_CattellFixed_cattellFixed_2_23_11 : ∃ p, NatGracefulPath 23 p ∧ p 11=2 := by
  let p : Fin 23 → ℕ := ![21,1,22,0,19,4,16,6,17,3,20,2,18,5,14,9,11,10,13,7,15,8,12]
  have hp : FiniteGracefulPath 23 p := by
    unfold FiniteGracefulPath Function.Injective
    decide
  exact ⟨finitePathLabel p,hp.toNat,rfl⟩

private theorem flat_CattellFixed_cattellFixed_2_25_12 : ∃ p, NatGracefulPath 25 p ∧ p 12=2 := by
  let p : Fin 25 → ℕ := ![13,17,8,16,6,18,3,24,0,23,1,21,2,19,5,10,12,9,15,14,7,20,4,22,11]
  have hp : FiniteGracefulPath 25 p := by
    unfold FiniteGracefulPath Function.Injective
    decide
  exact ⟨finitePathLabel p,hp.toNat,rfl⟩

private theorem flat_CattellFixed_cattellFixed_1_left_2 (i : ℕ) (hi : 2*i≤2-1)
    (hex : 2≠3 ∨ i≠1) : ∃ p, NatGracefulPath 2 p ∧ p i=1 := by
  have hb : i≤0 := by omega
  interval_cases i
  · exact exists_graceful_even_path_one (s:=1) (by decide)

private theorem flat_CattellFixed_cattellFixed_1_left_3 (i : ℕ) (hi : 2*i≤3-1)
    (hex : 3≠3 ∨ i≠1) : ∃ p, NatGracefulPath 3 p ∧ p i=1 := by
  have hb : i≤1 := by omega
  interval_cases i
  · exact flat_CattellFixed_cattellFixed_1_3_0
  · omega

private theorem flat_CattellFixed_cattellFixed_1_left_4 (i : ℕ) (hi : 2*i≤4-1)
    (hex : 4≠3 ∨ i≠1) : ∃ p, NatGracefulPath 4 p ∧ p i=1 := by
  have hb : i≤1 := by omega
  interval_cases i
  · exact exists_graceful_even_path_one (s:=2) (by decide)
  · exact exists_graceful_even_path_one (s:=2) (by decide)

private theorem flat_CattellFixed_cattellFixed_1_left_5 (i : ℕ) (hi : 2*i≤5-1)
    (hex : 5≠3 ∨ i≠1) : ∃ p, NatGracefulPath 5 p ∧ p i=1 := by
  have hb : i≤2 := by omega
  interval_cases i
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact flat_CattellFixed_cattellFixed_1_5_1
  · exact flat_CattellFixed_cattellFixed_1_5_2

private theorem flat_CattellFixed_cattellFixed_1_left_6 (i : ℕ) (hi : 2*i≤6-1)
    (hex : 6≠3 ∨ i≠1) : ∃ p, NatGracefulPath 6 p ∧ p i=1 := by
  have hb : i≤2 := by omega
  interval_cases i
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_even_path_one (s:=3) (by decide)

private theorem flat_CattellFixed_cattellFixed_1_left_7 (i : ℕ) (hi : 2*i≤7-1)
    (hex : 7≠3 ∨ i≠1) : ∃ p, NatGracefulPath 7 p ∧ p i=1 := by
  have hb : i≤3 := by omega
  interval_cases i
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact flat_CattellFixed_cattellFixed_1_7_2
  · exact flat_CattellFixed_cattellFixed_1_7_3

private theorem flat_CattellFixed_cattellFixed_1_left_8 (i : ℕ) (hi : 2*i≤8-1)
    (hex : 8≠3 ∨ i≠1) : ∃ p, NatGracefulPath 8 p ∧ p i=1 := by
  have hb : i≤3 := by omega
  interval_cases i
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_even_path_one (s:=4) (by decide)

private theorem flat_CattellFixed_cattellFixed_1_left_9 (i : ℕ) (hi : 2*i≤9-1)
    (hex : 9≠3 ∨ i≠1) : ∃ p, NatGracefulPath 9 p ∧ p i=1 := by
  have hb : i≤4 := by omega
  interval_cases i
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact flat_CattellFixed_cattellFixed_1_9_4

private theorem flat_CattellFixed_cattellFixed_1_left_10 (i : ℕ) (hi : 2*i≤10-1)
    (hex : 10≠3 ∨ i≠1) : ∃ p, NatGracefulPath 10 p ∧ p i=1 := by
  have hb : i≤4 := by omega
  interval_cases i
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_even_path_one (s:=5) (by decide)

private theorem flat_CattellFixed_cattellFixed_1_left_11 (i : ℕ) (hi : 2*i≤11-1)
    (hex : 11≠3 ∨ i≠1) : ∃ p, NatGracefulPath 11 p ∧ p i=1 := by
  have hb : i≤5 := by omega
  interval_cases i
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact flat_CattellFixed_cattellFixed_1_11_5

private theorem flat_CattellFixed_cattellFixed_1_left_12 (i : ℕ) (hi : 2*i≤12-1)
    (hex : 12≠3 ∨ i≠1) : ∃ p, NatGracefulPath 12 p ∧ p i=1 := by
  have hb : i≤5 := by omega
  interval_cases i
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)

private theorem flat_CattellFixed_cattellFixed_1_left_13 (i : ℕ) (hi : 2*i≤13-1)
    (hex : 13≠3 ∨ i≠1) : ∃ p, NatGracefulPath 13 p ∧ p i=1 := by
  have hb : i≤6 := by omega
  interval_cases i
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact flat_CattellFixed_cattellFixed_1_13_6

private theorem flat_CattellFixed_cattellFixed_1_left_14 (i : ℕ) (hi : 2*i≤14-1)
    (hex : 14≠3 ∨ i≠1) : ∃ p, NatGracefulPath 14 p ∧ p i=1 := by
  have hb : i≤6 := by omega
  interval_cases i
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)

private theorem flat_CattellFixed_cattellFixed_1_left_15 (i : ℕ) (hi : 2*i≤15-1)
    (hex : 15≠3 ∨ i≠1) : ∃ p, NatGracefulPath 15 p ∧ p i=1 := by
  have hb : i≤7 := by omega
  interval_cases i
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)

private theorem flat_CattellFixed_cattellFixed_1_left_16 (i : ℕ) (hi : 2*i≤16-1)
    (hex : 16≠3 ∨ i≠1) : ∃ p, NatGracefulPath 16 p ∧ p i=1 := by
  have hb : i≤7 := by omega
  interval_cases i
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)

private theorem flat_CattellFixed_cattellFixed_1_small_left (n i : ℕ) (hn : 1<n)
    (hb : n<17) (hi : 2*i≤n-1) (hex : n≠3 ∨ i≠1) :
    ∃ p, NatGracefulPath n p ∧ p i=1 := by
  interval_cases n
  · exact flat_CattellFixed_cattellFixed_1_left_2 i hi hex
  · exact flat_CattellFixed_cattellFixed_1_left_3 i hi hex
  · exact flat_CattellFixed_cattellFixed_1_left_4 i hi hex
  · exact flat_CattellFixed_cattellFixed_1_left_5 i hi hex
  · exact flat_CattellFixed_cattellFixed_1_left_6 i hi hex
  · exact flat_CattellFixed_cattellFixed_1_left_7 i hi hex
  · exact flat_CattellFixed_cattellFixed_1_left_8 i hi hex
  · exact flat_CattellFixed_cattellFixed_1_left_9 i hi hex
  · exact flat_CattellFixed_cattellFixed_1_left_10 i hi hex
  · exact flat_CattellFixed_cattellFixed_1_left_11 i hi hex
  · exact flat_CattellFixed_cattellFixed_1_left_12 i hi hex
  · exact flat_CattellFixed_cattellFixed_1_left_13 i hi hex
  · exact flat_CattellFixed_cattellFixed_1_left_14 i hi hex
  · exact flat_CattellFixed_cattellFixed_1_left_15 i hi hex
  · exact flat_CattellFixed_cattellFixed_1_left_16 i hi hex

/-- Every vertex can receive label 1, apart from the one stated finite exception. -/
theorem exists_graceful_path_one {n i : ℕ} (hi : i<n)
    (hn : 1<n) (hex : n≠3 ∨ i≠1) : ∃ p, NatGracefulPath n p ∧ p i=1 := by
  by_cases hb : 17≤n
  · exact exists_graceful_path_fixed_large hi hb
  by_cases hleft : 2*i≤n-1
  · exact flat_CattellFixed_cattellFixed_1_small_left n i hn (by omega) hleft hex
  · obtain ⟨p,hp,hpin⟩ := flat_CattellFixed_cattellFixed_1_small_left n (n-1-i) hn (by omega)
      (by omega) (by omega)
    exact ⟨reverseNatPath n p,hp.reverse,hpin⟩

private theorem flat_CattellFixed_cattellFixed_2_left_3 (i : ℕ) (hi : 2*i≤3-1)
    (hex : 3≠5 ∨ i≠2) : ∃ p, NatGracefulPath 3 p ∧ p i=2 := by
  have hb : i≤1 := by omega
  interval_cases i
  · exact flat_CattellFixed_cattellFixed_2_3_0
  · exact flat_CattellFixed_cattellFixed_2_3_1

private theorem flat_CattellFixed_cattellFixed_2_left_4 (i : ℕ) (hi : 2*i≤4-1)
    (hex : 4≠5 ∨ i≠2) : ∃ p, NatGracefulPath 4 p ∧ p i=2 := by
  have hb : i≤1 := by omega
  interval_cases i
  · exact exists_graceful_four_path_two (s:=1) (by decide)
  · exact exists_graceful_four_path_two (s:=1) (by decide)

private theorem flat_CattellFixed_cattellFixed_2_left_5 (i : ℕ) (hi : 2*i≤5-1)
    (hex : 5≠5 ∨ i≠2) : ∃ p, NatGracefulPath 5 p ∧ p i=2 := by
  have hb : i≤2 := by omega
  interval_cases i
  · exact flat_CattellFixed_cattellFixed_2_5_0
  · exact flat_CattellFixed_cattellFixed_2_5_1
  · omega

private theorem flat_CattellFixed_cattellFixed_2_left_6 (i : ℕ) (hi : 2*i≤6-1)
    (hex : 6≠5 ∨ i≠2) : ∃ p, NatGracefulPath 6 p ∧ p i=2 := by
  have hb : i≤2 := by omega
  interval_cases i
  · exact flat_CattellFixed_cattellFixed_2_6_0
  · exact flat_CattellFixed_cattellFixed_2_6_1
  · exact flat_CattellFixed_cattellFixed_2_6_2

private theorem flat_CattellFixed_cattellFixed_2_left_7 (i : ℕ) (hi : 2*i≤7-1)
    (hex : 7≠5 ∨ i≠2) : ∃ p, NatGracefulPath 7 p ∧ p i=2 := by
  have hb : i≤3 := by omega
  interval_cases i
  · exact flat_CattellFixed_cattellFixed_2_7_0
  · exact flat_CattellFixed_cattellFixed_2_7_1
  · exact flat_CattellFixed_cattellFixed_2_7_2
  · exact flat_CattellFixed_cattellFixed_2_7_3

private theorem flat_CattellFixed_cattellFixed_2_left_8 (i : ℕ) (hi : 2*i≤8-1)
    (hex : 8≠5 ∨ i≠2) : ∃ p, NatGracefulPath 8 p ∧ p i=2 := by
  have hb : i≤3 := by omega
  interval_cases i
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_four_path_two (s:=2) (by decide)
  · exact exists_graceful_four_path_two (s:=2) (by decide)
  · exact exists_graceful_four_path_two (s:=2) (by decide)

private theorem flat_CattellFixed_cattellFixed_2_left_9 (i : ℕ) (hi : 2*i≤9-1)
    (hex : 9≠5 ∨ i≠2) : ∃ p, NatGracefulPath 9 p ∧ p i=2 := by
  have hb : i≤4 := by omega
  interval_cases i
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact flat_CattellFixed_cattellFixed_2_9_2
  · exact flat_CattellFixed_cattellFixed_2_9_3
  · exact flat_CattellFixed_cattellFixed_2_9_4

private theorem flat_CattellFixed_cattellFixed_2_left_10 (i : ℕ) (hi : 2*i≤10-1)
    (hex : 10≠5 ∨ i≠2) : ∃ p, NatGracefulPath 10 p ∧ p i=2 := by
  have hb : i≤4 := by omega
  interval_cases i
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact flat_CattellFixed_cattellFixed_2_10_2
  · exact flat_CattellFixed_cattellFixed_2_10_3
  · exact flat_CattellFixed_cattellFixed_2_10_4

private theorem flat_CattellFixed_cattellFixed_2_left_11 (i : ℕ) (hi : 2*i≤11-1)
    (hex : 11≠5 ∨ i≠2) : ∃ p, NatGracefulPath 11 p ∧ p i=2 := by
  have hb : i≤5 := by omega
  interval_cases i
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact flat_CattellFixed_cattellFixed_2_11_3
  · exact flat_CattellFixed_cattellFixed_2_11_4
  · exact flat_CattellFixed_cattellFixed_2_11_5

private theorem flat_CattellFixed_cattellFixed_2_left_12 (i : ℕ) (hi : 2*i≤12-1)
    (hex : 12≠5 ∨ i≠2) : ∃ p, NatGracefulPath 12 p ∧ p i=2 := by
  have hb : i≤5 := by omega
  interval_cases i
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_four_path_two (s:=3) (by decide)
  · exact exists_graceful_four_path_two (s:=3) (by decide)

private theorem flat_CattellFixed_cattellFixed_2_left_13 (i : ℕ) (hi : 2*i≤13-1)
    (hex : 13≠5 ∨ i≠2) : ∃ p, NatGracefulPath 13 p ∧ p i=2 := by
  have hb : i≤6 := by omega
  interval_cases i
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact flat_CattellFixed_cattellFixed_2_13_4
  · exact flat_CattellFixed_cattellFixed_2_13_5
  · exact flat_CattellFixed_cattellFixed_2_13_6

private theorem flat_CattellFixed_cattellFixed_2_left_14 (i : ℕ) (hi : 2*i≤14-1)
    (hex : 14≠5 ∨ i≠2) : ∃ p, NatGracefulPath 14 p ∧ p i=2 := by
  have hb : i≤6 := by omega
  interval_cases i
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact flat_CattellFixed_cattellFixed_2_14_5
  · exact flat_CattellFixed_cattellFixed_2_14_6

private theorem flat_CattellFixed_cattellFixed_2_left_15 (i : ℕ) (hi : 2*i≤15-1)
    (hex : 15≠5 ∨ i≠2) : ∃ p, NatGracefulPath 15 p ∧ p i=2 := by
  have hb : i≤7 := by omega
  interval_cases i
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact flat_CattellFixed_cattellFixed_2_15_6
  · exact flat_CattellFixed_cattellFixed_2_15_7

private theorem flat_CattellFixed_cattellFixed_2_left_16 (i : ℕ) (hi : 2*i≤16-1)
    (hex : 16≠5 ∨ i≠2) : ∃ p, NatGracefulPath 16 p ∧ p i=2 := by
  have hb : i≤7 := by omega
  interval_cases i
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_four_path_two (s:=4) (by decide)
  · exact exists_graceful_four_path_two (s:=4) (by decide)

private theorem flat_CattellFixed_cattellFixed_2_left_17 (i : ℕ) (hi : 2*i≤17-1)
    (hex : 17≠5 ∨ i≠2) : ∃ p, NatGracefulPath 17 p ∧ p i=2 := by
  have hb : i≤8 := by omega
  interval_cases i
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact flat_CattellFixed_cattellFixed_2_17_7
  · exact flat_CattellFixed_cattellFixed_2_17_8

private theorem flat_CattellFixed_cattellFixed_2_left_18 (i : ℕ) (hi : 2*i≤18-1)
    (hex : 18≠5 ∨ i≠2) : ∃ p, NatGracefulPath 18 p ∧ p i=2 := by
  have hb : i≤8 := by omega
  interval_cases i
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact flat_CattellFixed_cattellFixed_2_18_8

private theorem flat_CattellFixed_cattellFixed_2_left_19 (i : ℕ) (hi : 2*i≤19-1)
    (hex : 19≠5 ∨ i≠2) : ∃ p, NatGracefulPath 19 p ∧ p i=2 := by
  have hb : i≤9 := by omega
  interval_cases i
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact flat_CattellFixed_cattellFixed_2_19_8
  · exact flat_CattellFixed_cattellFixed_2_19_9

private theorem flat_CattellFixed_cattellFixed_2_left_20 (i : ℕ) (hi : 2*i≤20-1)
    (hex : 20≠5 ∨ i≠2) : ∃ p, NatGracefulPath 20 p ∧ p i=2 := by
  have hb : i≤9 := by omega
  interval_cases i
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_four_path_two (s:=5) (by decide)

private theorem flat_CattellFixed_cattellFixed_2_left_21 (i : ℕ) (hi : 2*i≤21-1)
    (hex : 21≠5 ∨ i≠2) : ∃ p, NatGracefulPath 21 p ∧ p i=2 := by
  have hb : i≤10 := by omega
  interval_cases i
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact flat_CattellFixed_cattellFixed_2_21_10

private theorem flat_CattellFixed_cattellFixed_2_left_22 (i : ℕ) (hi : 2*i≤22-1)
    (hex : 22≠5 ∨ i≠2) : ∃ p, NatGracefulPath 22 p ∧ p i=2 := by
  have hb : i≤10 := by omega
  interval_cases i
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact flat_CattellFixed_cattellFixed_2_22_10

private theorem flat_CattellFixed_cattellFixed_2_left_23 (i : ℕ) (hi : 2*i≤23-1)
    (hex : 23≠5 ∨ i≠2) : ∃ p, NatGracefulPath 23 p ∧ p i=2 := by
  have hb : i≤11 := by omega
  interval_cases i
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact flat_CattellFixed_cattellFixed_2_23_11

private theorem flat_CattellFixed_cattellFixed_2_left_24 (i : ℕ) (hi : 2*i≤24-1)
    (hex : 24≠5 ∨ i≠2) : ∃ p, NatGracefulPath 24 p ∧ p i=2 := by
  have hb : i≤11 := by omega
  interval_cases i
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)

private theorem flat_CattellFixed_cattellFixed_2_left_25 (i : ℕ) (hi : 2*i≤25-1)
    (hex : 25≠5 ∨ i≠2) : ∃ p, NatGracefulPath 25 p ∧ p i=2 := by
  have hb : i≤12 := by omega
  interval_cases i
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact flat_CattellFixed_cattellFixed_2_25_12

private theorem flat_CattellFixed_cattellFixed_2_left_26 (i : ℕ) (hi : 2*i≤26-1)
    (hex : 26≠5 ∨ i≠2) : ∃ p, NatGracefulPath 26 p ∧ p i=2 := by
  have hb : i≤12 := by omega
  interval_cases i
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)

private theorem flat_CattellFixed_cattellFixed_2_left_27 (i : ℕ) (hi : 2*i≤27-1)
    (hex : 27≠5 ∨ i≠2) : ∃ p, NatGracefulPath 27 p ∧ p i=2 := by
  have hb : i≤13 := by omega
  interval_cases i
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)

private theorem flat_CattellFixed_cattellFixed_2_left_28 (i : ℕ) (hi : 2*i≤28-1)
    (hex : 28≠5 ∨ i≠2) : ∃ p, NatGracefulPath 28 p ∧ p i=2 := by
  have hb : i≤13 := by omega
  interval_cases i
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)
  · exact exists_graceful_path_twizzler (by decide) (by decide)

private theorem flat_CattellFixed_cattellFixed_2_small_left (n i : ℕ) (hn : 2<n)
    (hb : n<29) (hi : 2*i≤n-1) (hex : n≠5 ∨ i≠2) :
    ∃ p, NatGracefulPath n p ∧ p i=2 := by
  interval_cases n
  · exact flat_CattellFixed_cattellFixed_2_left_3 i hi hex
  · exact flat_CattellFixed_cattellFixed_2_left_4 i hi hex
  · exact flat_CattellFixed_cattellFixed_2_left_5 i hi hex
  · exact flat_CattellFixed_cattellFixed_2_left_6 i hi hex
  · exact flat_CattellFixed_cattellFixed_2_left_7 i hi hex
  · exact flat_CattellFixed_cattellFixed_2_left_8 i hi hex
  · exact flat_CattellFixed_cattellFixed_2_left_9 i hi hex
  · exact flat_CattellFixed_cattellFixed_2_left_10 i hi hex
  · exact flat_CattellFixed_cattellFixed_2_left_11 i hi hex
  · exact flat_CattellFixed_cattellFixed_2_left_12 i hi hex
  · exact flat_CattellFixed_cattellFixed_2_left_13 i hi hex
  · exact flat_CattellFixed_cattellFixed_2_left_14 i hi hex
  · exact flat_CattellFixed_cattellFixed_2_left_15 i hi hex
  · exact flat_CattellFixed_cattellFixed_2_left_16 i hi hex
  · exact flat_CattellFixed_cattellFixed_2_left_17 i hi hex
  · exact flat_CattellFixed_cattellFixed_2_left_18 i hi hex
  · exact flat_CattellFixed_cattellFixed_2_left_19 i hi hex
  · exact flat_CattellFixed_cattellFixed_2_left_20 i hi hex
  · exact flat_CattellFixed_cattellFixed_2_left_21 i hi hex
  · exact flat_CattellFixed_cattellFixed_2_left_22 i hi hex
  · exact flat_CattellFixed_cattellFixed_2_left_23 i hi hex
  · exact flat_CattellFixed_cattellFixed_2_left_24 i hi hex
  · exact flat_CattellFixed_cattellFixed_2_left_25 i hi hex
  · exact flat_CattellFixed_cattellFixed_2_left_26 i hi hex
  · exact flat_CattellFixed_cattellFixed_2_left_27 i hi hex
  · exact flat_CattellFixed_cattellFixed_2_left_28 i hi hex

/-- Every vertex can receive label 2, apart from the one stated finite exception. -/
theorem exists_graceful_path_two {n i : ℕ} (hi : i<n)
    (hn : 2<n) (hex : n≠5 ∨ i≠2) : ∃ p, NatGracefulPath n p ∧ p i=2 := by
  by_cases hb : 29≤n
  · exact exists_graceful_path_fixed_large hi hb
  by_cases hleft : 2*i≤n-1
  · exact flat_CattellFixed_cattellFixed_2_small_left n i hn (by omega) hleft hex
  · obtain ⟨p,hp,hpin⟩ := flat_CattellFixed_cattellFixed_2_small_left n (n-1-i) hn (by omega)
      (by omega) (by omega)
    exact ⟨reverseNatPath n p,hp.reverse,hpin⟩

end Bounty


/- Supporting module: PathTwoConstruction -/

namespace Bounty.PathTwoConstruction
open PathConstruction

structure Core (a b : ℕ) (P Q : List Symbol) : Prop where
  main_start : P.head? = some (L 2)
  main_alternates : P.IsChain PathConstruction.Opposite
  extra_alternates : Q.IsChain PathConstruction.Opposite
  vertices : bag P + bag Q = lowBag (a+1) + highBag (b+1)
  edges : edgeBag P + edgeBag Q = rangeBag (a+b)

structure VH (a b : ℕ) (P Q : List Symbol) : Prop extends Core a b P Q where
  high_pos : 2 ≤ b
  main_end : P.getLast? = some (H b)
  extra_start : Q.head? = some (L a)
  extra_end : Q.getLast? = some (H (b-2))

structure VL (a b : ℕ) (P Q : List Symbol) : Prop extends Core a b P Q where
  low_pos : 2 ≤ a
  main_end : P.getLast? = some (L a)
  extra_start : Q.head? = some (L (a-2))
  extra_end : Q.getLast? = some (H b)

def vhMain (a b : ℕ) (P : List Symbol) := P ++ [L (a+1), H (b+3)]
def vhExtra (a b : ℕ) (Q : List Symbol) := [L (a+3), H (b+2)] ++ Q ++ [L (a+2), H (b+1)]
def vlMain (a b : ℕ) (P : List Symbol) := P ++ [H (b+1), L (a+3)]
def vlExtra (a b : ℕ) (Q : List Symbol) := [L (a+1), H (b+2)] ++ Q ++ [L (a+2), H (b+3)]

private theorem flat_PathTwoConstruction_cycle_vertices (a b : ℕ) (P Q : List Symbol)
    (h : bag P + bag Q = lowBag (a+1) + highBag (b+1)) :
    bag (vhMain a b P) + bag (vhExtra a b Q) = lowBag (a+3+1) + highBag (b+3+1) := by
  have ha : a+3+1 = (a+1)+1+1+1 := by omega
  have hb : b+3+1 = (b+1)+1+1+1 := by omega
  rw [ha, hb]
  simp only [lowBag_succ, highBag_succ, vhMain, vhExtra, bag_append, bag_cons, bag_nil, add_zero]
  have h' := congrArg (fun x : Multiset Symbol =>
    x + {L (a+1)} + {H (b+3)} + {L (a+3)} + {H (b+2)} + {L (a+2)} + {H (b+1)}) h
  simp only [lowBag_succ, highBag_succ] at h'
  convert h' using 1 <;> ac_rfl

theorem vh_cycle (a b : ℕ) (P Q : List Symbol) (h : VH a b P Q) :
    VH (a+3) (b+3) (vhMain a b P) (vhExtra a b Q) := by
  have hmain : edgeBag (vhMain a b P) =
      edgeBag P + {a+b+1} + {a+b+4} := by
    rw [vhMain, edgeBag_append _ _ (H b) (L (a+1)) h.main_end rfl]
    have h1 : b+(a+1) = a+b+1 := by omega
    have h2 : a+1+(b+3) = a+b+4 := by omega
    simp only [edgeBag, edgeSums, index, bag_cons, bag_nil, add_zero, h1, h2]
  have hfront : ([L (a+3), H (b+2)] ++ Q).getLast? = some (H (b-2)) := by
    rw [List.getLast?_append, h.extra_end]
    rfl
  have hextra : edgeBag (vhExtra a b Q) =
      {a+b+5} + {a+b+2} + edgeBag Q + {a+b} + {a+b+3} := by
    rw [vhExtra, edgeBag_append _ _ (H (b-2)) (L (a+2)) hfront rfl]
    rw [edgeBag_append _ _ (H (b+2)) (L a) rfl h.extra_start]
    have hp := h.high_pos
    have h1 : a+3+(b+2) = a+b+5 := by omega
    have h2 : b+2+a = a+b+2 := by omega
    have h3 : b-2+(a+2) = a+b := by omega
    have h4 : a+2+(b+1) = a+b+3 := by omega
    simp only [edgeBag, edgeSums, index, bag_cons, bag_nil, add_zero, h1, h2, h3, h4]
  refine ⟨⟨?_, ?_, ?_, flat_PathTwoConstruction_cycle_vertices a b P Q h.vertices, ?_⟩, by omega, ?_, ?_, ?_⟩
  · simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, vhMain, List.head?_append, h.main_start]
  · rw [vhMain, List.isChain_append]
    simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, h.main_alternates, h.main_end, PathConstruction.Opposite, List.isChain_cons]
  · simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, vhExtra, List.isChain_append, List.isChain_cons, h.extra_alternates,
      h.extra_start, h.extra_end, List.getLast?_append, PathConstruction.Opposite]
  · rw [hmain, hextra]
    have he := congrArg (fun x : Multiset ℕ =>
      x + {a+b} + {a+b+2} + {a+b+1} + {a+b+3} + {a+b+4} + {a+b+5}) h.edges
    have hh : a+3+(b+3) = (a+b)+1+1+1+1+1+1 := by omega
    rw [hh]
    simp only [rangeBag_succ]
    convert he using 1 <;> ac_rfl
  · simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, vhMain, List.getLast?_append]
  · simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, vhExtra, List.head?_append]
  · change ([L (a+3), H (b+2)] ++ Q ++ [L (a+2), H (b+1)]).getLast? = some (H (b+3-2))
    rw [List.getLast?_append]
    simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero]


private theorem flat_PathTwoConstruction_cycle_vertices_vl (a b : ℕ) (P Q : List Symbol)
    (h : bag P + bag Q = lowBag (a+1) + highBag (b+1)) :
    bag (vlMain a b P) + bag (vlExtra a b Q) = lowBag (a+3+1) + highBag (b+3+1) := by
  simp only [lowBag_succ, highBag_succ, vlMain, vlExtra, bag_append, bag_cons, bag_nil, add_zero]
  have h' := congrArg (fun x : Multiset Symbol =>
    x + {H (b+1)} + {L (a+3)} + {L (a+1)} + {H (b+2)} + {L (a+2)} + {H (b+3)}) h
  simp only [lowBag_succ, highBag_succ] at h'
  convert h' using 1 <;> ac_rfl

theorem vl_cycle (a b : ℕ) (P Q : List Symbol) (h : VL a b P Q) :
    VL (a+3) (b+3) (vlMain a b P) (vlExtra a b Q) := by
  have hmain : edgeBag (vlMain a b P) =
      edgeBag P + {a+b+1} + {a+b+4} := by
    rw [vlMain, edgeBag_append _ _ (L a) (H (b+1)) h.main_end rfl]
    have h1 : a+(b+1) = a+b+1 := by omega
    have h2 : b+1+(a+3) = a+b+4 := by omega
    simp only [edgeBag, edgeSums, index, bag_cons, bag_nil, add_zero, h1, h2]
  have hfront : ([L (a+1), H (b+2)] ++ Q).getLast? = some (H b) := by
    rw [List.getLast?_append, h.extra_end]
    rfl
  have hextra : edgeBag (vlExtra a b Q) =
      {a+b+3} + {a+b} + edgeBag Q + {a+b+2} + {a+b+5} := by
    rw [vlExtra, edgeBag_append _ _ (H b) (L (a+2)) hfront rfl]
    rw [edgeBag_append _ _ (H (b+2)) (L (a-2)) rfl h.extra_start]
    have hp := h.low_pos
    have h1 : a+1+(b+2) = a+b+3 := by omega
    have h2 : b+2+(a-2) = a+b := by omega
    have h3 : b+(a+2) = a+b+2 := by omega
    have h4 : a+2+(b+3) = a+b+5 := by omega
    simp only [edgeBag, edgeSums, index, bag_cons, bag_nil, add_zero, h1, h2, h3, h4]
  refine ⟨⟨?_, ?_, ?_, flat_PathTwoConstruction_cycle_vertices_vl a b P Q h.vertices, ?_⟩, by omega, ?_, ?_, ?_⟩
  · simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, vlMain, List.head?_append, h.main_start]
  · rw [vlMain, List.isChain_append]
    simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, h.main_alternates, h.main_end, PathConstruction.Opposite, List.isChain_cons]
  · simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, vlExtra, List.isChain_append, List.isChain_cons, h.extra_alternates,
      h.extra_start, h.extra_end, PathConstruction.Opposite]
  · rw [hmain, hextra]
    have he := congrArg (fun x : Multiset ℕ =>
      x + {a+b} + {a+b+2} + {a+b+1} + {a+b+3} + {a+b+4} + {a+b+5}) h.edges
    have hh : a+3+(b+3) = (a+b)+1+1+1+1+1+1 := by omega
    rw [hh]
    simp only [rangeBag_succ]
    convert he using 1 <;> ac_rfl
  · simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, vlMain, List.getLast?_append]
  · simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, vlExtra]
  · change ([L (a+1), H (b+2)] ++ Q ++ [L (a+2), H (b+3)]).getLast? = some (H (b+3))
    rw [List.getLast?_append]
    rfl

theorem vh_cycles (t a b : ℕ) (P Q : List Symbol) (h : VH a b P Q) :
    ∃ P' Q', VH (a+3*t) (b+3*t) P' Q' ∧
      P'.length = P.length+2*t ∧ Q'.length = Q.length+4*t := by
  induction t with
  | zero => exact ⟨P, Q, by simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero] using h, by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero], by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero]⟩
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
  | zero => exact ⟨P, Q, by simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero] using h, by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero], by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero]⟩
  | succ t ih =>
    obtain ⟨P', Q', hi, hP, hQ⟩ := ih
    refine ⟨vlMain (a+3*t) (b+3*t) P', vlExtra (a+3*t) (b+3*t) Q', ?_, ?_, ?_⟩
    · convert vl_cycle (a+3*t) (b+3*t) P' Q' hi using 1 <;> omega
    · simp only [vlMain, List.length_append, List.length_cons, List.length_nil, hP]
      omega
    · simp only [vlExtra, List.length_append, List.length_cons, List.length_nil, hQ]
      omega



structure Terminal (a b : ℕ) (P : List Symbol) : Prop where
  main_start : P.head? = some (L 2)
  alternates : P.IsChain PathConstruction.Opposite
  vertices : bag P = lowBag (a+1) + highBag (b+1)
  edges : edgeBag P = rangeBag (a+b+1)

theorem vh_exit (a b : ℕ) (P Q : List Symbol) (h : VH a b P Q) :
    Terminal a b (P ++ Q) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, List.head?_append,h.main_start]
  · rw [List.isChain_append]
    simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, h.main_alternates,h.extra_alternates,h.main_end,h.extra_start,PathConstruction.Opposite]
  · simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero] using h.vertices
  · rw [edgeBag_append _ _ (H b) (L a) h.main_end h.extra_start]
    simp only [index]
    have he := congrArg (fun x : Multiset ℕ => x + {a+b}) h.edges
    rw [rangeBag_succ]
    convert he using 1 <;> simp only [Nat.add_comm b a] <;> ac_rfl

theorem vl_exit (a b : ℕ) (P Q : List Symbol) (h : VL a b P Q) :
    Terminal a b (P ++ Q.reverse) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, List.head?_append,h.main_start]
  · rw [List.isChain_append]
    simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, h.main_alternates,h.extra_alternates,h.main_end,h.extra_end,PathConstruction.Opposite]
  · simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero] using h.vertices
  · rw [edgeBag_append _ _ (L a) (H b) h.main_end (by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, h.extra_end])]
    simp only [index,edgeBag_reverse]
    have he := congrArg (fun x : Multiset ℕ => x + {a+b}) h.edges
    rw [rangeBag_succ]
    convert he using 1 <;> ac_rfl

theorem Core.main_pos {a b : ℕ} {P Q : List Symbol} (h : Core a b P Q) :
    0 < P.length := by
  cases P with
  | nil => simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero] using h.main_start
  | cons x xs => simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero]

def HasLow (n k : ℕ) : Prop :=
  ∃ a b P, Terminal a b P ∧ P.length = n ∧ P[k]? = some (L a)
def HasHigh (n k : ℕ) : Prop :=
  ∃ a b P, Terminal a b P ∧ P.length = n ∧ P[k]? = some (H b)

theorem vh_low_direct {a b : ℕ} {P Q : List Symbol} (h : VH a b P Q) :
    HasLow (P.length+Q.length) P.length := by
  refine ⟨a,b,P++Q,vh_exit _ _ _ _ h,by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero],?_⟩
  simpa only [get_append_boundary] using h.extra_start

theorem vh_high_direct {a b : ℕ} {P Q : List Symbol} (h : VH a b P Q) :
    HasHigh (P.length+Q.length) (P.length-1) := by
  refine ⟨a,b,P++Q,vh_exit _ _ _ _ h,by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero],?_⟩
  simpa only [get_append_last _ _ h.toCore.main_pos] using h.main_end

theorem vl_low_direct {a b : ℕ} {P Q : List Symbol} (h : VL a b P Q) :
    HasLow (P.length+Q.length) (P.length-1) := by
  refine ⟨a,b,P++Q.reverse,vl_exit _ _ _ _ h,by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero],?_⟩
  simpa only [get_append_last _ _ h.toCore.main_pos] using h.main_end

theorem vl_high_direct {a b : ℕ} {P Q : List Symbol} (h : VL a b P Q) :
    HasHigh (P.length+Q.length) P.length := by
  refine ⟨a,b,P++Q.reverse,vl_exit _ _ _ _ h,by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero],?_⟩
  simpa only [get_append_boundary,List.head?_reverse] using h.extra_end

private theorem flat_PathTwoConstruction_seed_vh_0 : VH 4 4 [L 2, H 3, L 0, H 0, L 1, H 1, L 3, H 4] [L 4, H 2] := by
  refine ⟨⟨rfl, by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, List.isChain_cons,PathConstruction.Opposite], by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, List.isChain_cons,PathConstruction.Opposite], by decide, by decide⟩, by decide, rfl, rfl, rfl⟩

private theorem flat_PathTwoConstruction_seed_vh_1 : VH 5 5 [L 2, H 0, L 0, H 1, L 3, H 2, L 1, H 5] [L 5, H 4, L 4, H 3] := by
  refine ⟨⟨rfl, by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, List.isChain_cons,PathConstruction.Opposite], by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, List.isChain_cons,PathConstruction.Opposite], by decide, by decide⟩, by decide, rfl, rfl, rfl⟩

private theorem flat_PathTwoConstruction_seed_vh_2 : VH 6 6 [L 2, H 1, L 3, H 3, L 4, H 5, L 5, H 6] [L 6, H 2, L 0, H 0, L 1, H 4] := by
  refine ⟨⟨rfl, by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, List.isChain_cons,PathConstruction.Opposite], by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, List.isChain_cons,PathConstruction.Opposite], by decide, by decide⟩, by decide, rfl, rfl, rfl⟩

private theorem flat_PathTwoConstruction_seed_vh_3 : VH 4 4 [L 2, H 1, L 1, H 0, L 0, H 4] [L 4, H 3, L 3, H 2] := by
  refine ⟨⟨rfl, by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, List.isChain_cons,PathConstruction.Opposite], by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, List.isChain_cons,PathConstruction.Opposite], by decide, by decide⟩, by decide, rfl, rfl, rfl⟩

private theorem flat_PathTwoConstruction_seed_vh_4 : VH 5 5 [L 2, H 2, L 3, H 4, L 4, H 5] [L 5, H 1, L 1, H 0, L 0, H 3] := by
  refine ⟨⟨rfl, by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, List.isChain_cons,PathConstruction.Opposite], by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, List.isChain_cons,PathConstruction.Opposite], by decide, by decide⟩, by decide, rfl, rfl, rfl⟩

private theorem flat_PathTwoConstruction_seed_vh_5 : VH 6 6 [L 2, H 0, L 0, H 1, L 3, H 6] [L 6, H 5, L 5, H 3, L 4, H 2, L 1, H 4] := by
  refine ⟨⟨rfl, by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, List.isChain_cons,PathConstruction.Opposite], by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, List.isChain_cons,PathConstruction.Opposite], by decide, by decide⟩, by decide, rfl, rfl, rfl⟩

private theorem flat_PathTwoConstruction_seed_vh_6 : VH 4 4 [L 2, H 3, L 3, H 4] [L 4, H 0, L 0, H 1, L 1, H 2] := by
  refine ⟨⟨rfl, by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, List.isChain_cons,PathConstruction.Opposite], by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, List.isChain_cons,PathConstruction.Opposite], by decide, by decide⟩, by decide, rfl, rfl, rfl⟩

private theorem flat_PathTwoConstruction_seed_vh_7 : VH 5 5 [L 2, H 4, L 4, H 5] [L 5, H 2, L 3, H 1, L 1, H 0, L 0, H 3] := by
  refine ⟨⟨rfl, by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, List.isChain_cons,PathConstruction.Opposite], by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, List.isChain_cons,PathConstruction.Opposite], by decide, by decide⟩, by decide, rfl, rfl, rfl⟩

private theorem flat_PathTwoConstruction_seed_vh_8 : VH 6 6 [L 2, H 1, L 4, H 6] [L 6, H 5, L 3, H 3, L 1, H 0, L 0, H 2, L 5, H 4] := by
  refine ⟨⟨rfl, by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, List.isChain_cons,PathConstruction.Opposite], by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, List.isChain_cons,PathConstruction.Opposite], by decide, by decide⟩, by decide, rfl, rfl, rfl⟩

private theorem flat_PathTwoConstruction_seed_vl_0 : VL 6 5 [L 2, H 2, L 3, H 3, L 0, H 0, L 1, H 1, L 6] [L 4, H 4, L 5, H 5] := by
  refine ⟨⟨rfl, by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, List.isChain_cons,PathConstruction.Opposite], by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, List.isChain_cons,PathConstruction.Opposite], by decide, by decide⟩, by decide, rfl, rfl, rfl⟩

private theorem flat_PathTwoConstruction_seed_vl_1 : VL 7 6 [L 2, H 1, L 1, H 0, L 0, H 4, L 6, H 5, L 7] [L 5, H 3, L 4, H 2, L 3, H 6] := by
  refine ⟨⟨rfl, by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, List.isChain_cons,PathConstruction.Opposite], by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, List.isChain_cons,PathConstruction.Opposite], by decide, by decide⟩, by decide, rfl, rfl, rfl⟩

private theorem flat_PathTwoConstruction_seed_vl_2 : VL 5 4 [L 2, H 2, L 1, H 1, L 0, H 0, L 5] [L 3, H 3, L 4, H 4] := by
  refine ⟨⟨rfl, by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, List.isChain_cons,PathConstruction.Opposite], by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, List.isChain_cons,PathConstruction.Opposite], by decide, by decide⟩, by decide, rfl, rfl, rfl⟩

private theorem flat_PathTwoConstruction_seed_vl_3 : VL 3 2 [L 2, H 0, L 0, H 1, L 3] [L 1, H 2] := by
  refine ⟨⟨rfl, by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, List.isChain_cons,PathConstruction.Opposite], by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, List.isChain_cons,PathConstruction.Opposite], by decide, by decide⟩, by decide, rfl, rfl, rfl⟩

private theorem flat_PathTwoConstruction_seed_vl_4 : VL 7 6 [L 2, H 0, L 0, H 1, L 3, H 3, L 7] [L 5, H 2, L 1, H 4, L 4, H 5, L 6, H 6] := by
  refine ⟨⟨rfl, by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, List.isChain_cons,PathConstruction.Opposite], by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, List.isChain_cons,PathConstruction.Opposite], by decide, by decide⟩, by decide, rfl, rfl, rfl⟩

private theorem flat_PathTwoConstruction_seed_vl_5 : VL 5 4 [L 2, H 2, L 4, H 3, L 5] [L 3, H 0, L 0, H 1, L 1, H 4] := by
  refine ⟨⟨rfl, by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, List.isChain_cons,PathConstruction.Opposite], by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, List.isChain_cons,PathConstruction.Opposite], by decide, by decide⟩, by decide, rfl, rfl, rfl⟩

private theorem flat_PathTwoConstruction_seed_vl_6 : VL 3 2 [L 2, H 1, L 3] [L 1, H 0, L 0, H 2] := by
  refine ⟨⟨rfl, by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, List.isChain_cons,PathConstruction.Opposite], by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, List.isChain_cons,PathConstruction.Opposite], by decide, by decide⟩, by decide, rfl, rfl, rfl⟩

private theorem flat_PathTwoConstruction_seed_vl_7 : VL 7 6 [L 2, H 3, L 3, H 4, L 7] [L 5, H 5, L 4, H 0, L 0, H 1, L 1, H 2, L 6, H 6] := by
  refine ⟨⟨rfl, by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, List.isChain_cons,PathConstruction.Opposite], by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, List.isChain_cons,PathConstruction.Opposite], by decide, by decide⟩, by decide, rfl, rfl, rfl⟩

private theorem flat_PathTwoConstruction_seed_vl_8 : VL 5 4 [L 2, H 1, L 5] [L 3, H 2, L 0, H 0, L 1, H 3, L 4, H 4] := by
  refine ⟨⟨rfl, by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, List.isChain_cons,PathConstruction.Opposite], by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, List.isChain_cons,PathConstruction.Opposite], by decide, by decide⟩, by decide, rfl, rfl, rfl⟩

private theorem flat_PathTwoConstruction_prepared_vh_index (p q r : ℕ) (hp : 8 ≤ p) (hpar : p%2=0)
    (hr : r ≤ 8) (hq : q+14=2*p+2*r) :
    ∃ a b P Q, VH a b P Q ∧ P.length=p ∧ Q.length=q := by
  interval_cases r
  · obtain ⟨P,Q,h,hP,hQ⟩ := vh_cycles ((p-8)/2) _ _ _ _ flat_PathTwoConstruction_seed_vh_0
    refine ⟨_,_,P,Q,h,?_,?_⟩ <;>
      simp only [List.length_cons,List.length_nil] at hP hQ <;> omega
  · obtain ⟨P,Q,h,hP,hQ⟩ := vh_cycles ((p-8)/2) _ _ _ _ flat_PathTwoConstruction_seed_vh_1
    refine ⟨_,_,P,Q,h,?_,?_⟩ <;>
      simp only [List.length_cons,List.length_nil] at hP hQ <;> omega
  · obtain ⟨P,Q,h,hP,hQ⟩ := vh_cycles ((p-8)/2) _ _ _ _ flat_PathTwoConstruction_seed_vh_2
    refine ⟨_,_,P,Q,h,?_,?_⟩ <;>
      simp only [List.length_cons,List.length_nil] at hP hQ <;> omega
  · obtain ⟨P,Q,h,hP,hQ⟩ := vh_cycles ((p-6)/2) _ _ _ _ flat_PathTwoConstruction_seed_vh_3
    refine ⟨_,_,P,Q,h,?_,?_⟩ <;>
      simp only [List.length_cons,List.length_nil] at hP hQ <;> omega
  · obtain ⟨P,Q,h,hP,hQ⟩ := vh_cycles ((p-6)/2) _ _ _ _ flat_PathTwoConstruction_seed_vh_4
    refine ⟨_,_,P,Q,h,?_,?_⟩ <;>
      simp only [List.length_cons,List.length_nil] at hP hQ <;> omega
  · obtain ⟨P,Q,h,hP,hQ⟩ := vh_cycles ((p-6)/2) _ _ _ _ flat_PathTwoConstruction_seed_vh_5
    refine ⟨_,_,P,Q,h,?_,?_⟩ <;>
      simp only [List.length_cons,List.length_nil] at hP hQ <;> omega
  · obtain ⟨P,Q,h,hP,hQ⟩ := vh_cycles ((p-4)/2) _ _ _ _ flat_PathTwoConstruction_seed_vh_6
    refine ⟨_,_,P,Q,h,?_,?_⟩ <;>
      simp only [List.length_cons,List.length_nil] at hP hQ <;> omega
  · obtain ⟨P,Q,h,hP,hQ⟩ := vh_cycles ((p-4)/2) _ _ _ _ flat_PathTwoConstruction_seed_vh_7
    refine ⟨_,_,P,Q,h,?_,?_⟩ <;>
      simp only [List.length_cons,List.length_nil] at hP hQ <;> omega
  · obtain ⟨P,Q,h,hP,hQ⟩ := vh_cycles ((p-4)/2) _ _ _ _ flat_PathTwoConstruction_seed_vh_8
    refine ⟨_,_,P,Q,h,?_,?_⟩ <;>
      simp only [List.length_cons,List.length_nil] at hP hQ <;> omega

theorem prepared_vh (p q : ℕ) (hp : 8 ≤ p) (hpar : p%2=0)
    (hq : q%2=0) (hlo : 2*p ≤ q+14) (hhi : q ≤ 2*p+2) :
    ∃ a b P Q, VH a b P Q ∧ P.length=p ∧ Q.length=q := by
  apply flat_PathTwoConstruction_prepared_vh_index p q ((q+14-2*p)/2) hp hpar <;> omega

private theorem flat_PathTwoConstruction_prepared_vl_index (p q r : ℕ) (hp : 9 ≤ p) (hpar : p%2=1)
    (hr : r ≤ 8) (hq : q+14=2*p+2*r) :
    ∃ a b P Q, VL a b P Q ∧ P.length=p ∧ Q.length=q := by
  interval_cases r
  · obtain ⟨P,Q,h,hP,hQ⟩ := vl_cycles ((p-9)/2) _ _ _ _ flat_PathTwoConstruction_seed_vl_0
    refine ⟨_,_,P,Q,h,?_,?_⟩ <;>
      simp only [List.length_cons,List.length_nil] at hP hQ <;> omega
  · obtain ⟨P,Q,h,hP,hQ⟩ := vl_cycles ((p-9)/2) _ _ _ _ flat_PathTwoConstruction_seed_vl_1
    refine ⟨_,_,P,Q,h,?_,?_⟩ <;>
      simp only [List.length_cons,List.length_nil] at hP hQ <;> omega
  · obtain ⟨P,Q,h,hP,hQ⟩ := vl_cycles ((p-7)/2) _ _ _ _ flat_PathTwoConstruction_seed_vl_2
    refine ⟨_,_,P,Q,h,?_,?_⟩ <;>
      simp only [List.length_cons,List.length_nil] at hP hQ <;> omega
  · obtain ⟨P,Q,h,hP,hQ⟩ := vl_cycles ((p-5)/2) _ _ _ _ flat_PathTwoConstruction_seed_vl_3
    refine ⟨_,_,P,Q,h,?_,?_⟩ <;>
      simp only [List.length_cons,List.length_nil] at hP hQ <;> omega
  · obtain ⟨P,Q,h,hP,hQ⟩ := vl_cycles ((p-7)/2) _ _ _ _ flat_PathTwoConstruction_seed_vl_4
    refine ⟨_,_,P,Q,h,?_,?_⟩ <;>
      simp only [List.length_cons,List.length_nil] at hP hQ <;> omega
  · obtain ⟨P,Q,h,hP,hQ⟩ := vl_cycles ((p-5)/2) _ _ _ _ flat_PathTwoConstruction_seed_vl_5
    refine ⟨_,_,P,Q,h,?_,?_⟩ <;>
      simp only [List.length_cons,List.length_nil] at hP hQ <;> omega
  · obtain ⟨P,Q,h,hP,hQ⟩ := vl_cycles ((p-3)/2) _ _ _ _ flat_PathTwoConstruction_seed_vl_6
    refine ⟨_,_,P,Q,h,?_,?_⟩ <;>
      simp only [List.length_cons,List.length_nil] at hP hQ <;> omega
  · obtain ⟨P,Q,h,hP,hQ⟩ := vl_cycles ((p-5)/2) _ _ _ _ flat_PathTwoConstruction_seed_vl_7
    refine ⟨_,_,P,Q,h,?_,?_⟩ <;>
      simp only [List.length_cons,List.length_nil] at hP hQ <;> omega
  · obtain ⟨P,Q,h,hP,hQ⟩ := vl_cycles ((p-3)/2) _ _ _ _ flat_PathTwoConstruction_seed_vl_8
    refine ⟨_,_,P,Q,h,?_,?_⟩ <;>
      simp only [List.length_cons,List.length_nil] at hP hQ <;> omega

theorem prepared_vl (p q : ℕ) (hp : 9 ≤ p) (hpar : p%2=1)
    (hq : q%2=0) (hlo : 2*p ≤ q+14) (hhi : q ≤ 2*p+2) :
    ∃ a b P Q, VL a b P Q ∧ P.length=p ∧ Q.length=q := by
  apply flat_PathTwoConstruction_prepared_vl_index p q ((q+14-2*p)/2) hp hpar <;> omega

/-- The entire width-sixteen strip adjoining the first symbolic region. -/
theorem symbolic_strip (d c : ℕ) (hd : 10 ≤ d) (hc : 1 ≤ c)
    (hlo : 2*d-15 ≤ c) (hhi : c ≤ 2*d) :
    ∃ a b P, Terminal a b P ∧ P.length=d+c ∧
      P[d-1]? = some (if d%2=1 then L a else H b) := by
  by_cases hodd : d%2=1
  · simp only [ite_eq_left hodd]
    change HasLow (d+c) (d-1)
    by_cases hc0 : c%2=0
    · obtain ⟨a,b,P,Q,h,hP,hQ⟩ := prepared_vl d c (by omega) hodd hc0 (by omega) (by omega)
      have hr := vl_low_direct h
      simpa only [hP,hQ] using hr
    · obtain ⟨a,b,P,Q,h,hP,hQ⟩ := prepared_vh (d-1) (c+1) (by omega) (by omega) (by omega) (by omega) (by omega)
      have hr := vh_low_direct h
      rw [hP,hQ] at hr
      convert hr using 1 <;> omega
  · simp only [ite_eq_right hodd]
    change HasHigh (d+c) (d-1)
    by_cases hc0 : c%2=0
    · obtain ⟨a,b,P,Q,h,hP,hQ⟩ := prepared_vh d c (by omega) (by omega) hc0 (by omega) (by omega)
      have hr := vh_high_direct h
      simpa only [hP,hQ] using hr
    · obtain ⟨a,b,P,Q,h,hP,hQ⟩ := prepared_vl (d-1) (c+1) (by omega) (by omega) (by omega) (by omega) (by omega)
      have hr := vl_high_direct h
      rw [hP,hQ] at hr
      convert hr using 1 <;> omega

end Bounty.PathTwoConstruction


/- Supporting module: PathTwoNumeric -/


namespace Bounty.PathTwoConstruction
open PathConstruction

theorem Terminal.length {a b : ℕ} {P : List Symbol} (h : Terminal a b P) :
    P.length = a+b+2 := by
  have hv := congrArg Multiset.card h.vertices
  simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, bag, lowBag, highBag, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hv

theorem Terminal.vertex_perm {a b : ℕ} {P : List Symbol} (h : Terminal a b P) :
    P.Perm ((List.range (a+1)).map L ++ (List.range (b+1)).map H) := by
  apply Multiset.coe_eq_coe.mp
  simpa only [lowBag, highBag, bag, Multiset.coe_add] using h.vertices

theorem Terminal.edge_perm {a b : ℕ} {P : List Symbol} (h : Terminal a b P) :
    (edgeSums P).Perm (List.range (a+b+1)) := Multiset.coe_eq_coe.mp h.edges

theorem Terminal.symbol_bound {a b : ℕ} {P : List Symbol} (h : Terminal a b P)
    {s : Symbol} (hs : s ∈ P) :
    match s with | .inl i => i ≤ a | .inr i => i ≤ b := by
  have hm := h.vertex_perm.mem_iff.mp hs
  cases s <;> simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero] using hm

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


/-- A prescribed-zero alpha path starting two below or three above its cut. -/
theorem alpha_path_strip (d c : ℕ) (hd : 10 ≤ d) (hc : 1 ≤ c)
    (hlo : 2*d-15 ≤ c) (hhi : c ≤ 2*d) :
    ∃ p k, NatAlphaPath (d+c) p k ∧ p (d-1)=0 ∧
      (d%2=1 → p 0=k-2 ∧ 2≤k) ∧ (d%2=0 → p 0=k+3) := by
  obtain ⟨a,b,P,h,hlen,hpin⟩ := symbolic_strip d c hd hc hlo hhi
  have ha : 2 ≤ a := by
    have hm : L 2 ∈ P := List.mem_of_head? h.main_start
    exact h.symbol_bound hm
  by_cases hodd : d%2=1
  · refine ⟨boundaryPath true a b P,a,?_,?_,?_,?_⟩
    · exact boundaryPath_alpha h hlen true
    · simp only [ite_eq_left hodd] at hpin
      simp only [boundaryPath,symbolAt,hpin,Option.getD_some,boundaryLabel,Nat.sub_self]
    · intro _
      refine ⟨?_,ha⟩
      simp only [boundaryPath,symbolAt_zero,h.main_start,Option.getD_some,boundaryLabel]
    · intro heven
      omega
  · refine ⟨boundaryPath false a b P,b,?_,?_,?_,?_⟩
    · exact boundaryPath_alpha h hlen false
    · simp only [ite_eq_right hodd] at hpin
      simp only [boundaryPath,symbolAt,hpin,Option.getD_some,boundaryLabel,Nat.sub_self]
    · intro ho
      exact (hodd ho).elim
    · intro _
      simp only [boundaryPath,symbolAt_zero,h.main_start,Option.getD_some,boundaryLabel]

end Bounty.PathTwoConstruction


/- Supporting module: ForkFixedRegions -/



namespace Bounty
open Math15.Graceful

theorem PathVertexLabel.complement {a b t : ℕ} (h : PathVertexLabel a b t) :
    PathVertexLabel a b (a+b-t) := by
  obtain ⟨f,hf,hft⟩ := h
  refine ⟨_,hf.complement,?_⟩
  rw [hft]
  omega

theorem pathVertexLabel_one {a b : ℕ} (hq : 2 < a+b) : PathVertexLabel a b 1 := by
  exact exists_graceful_path_one (by omega) (by omega) (by left; omega)

theorem pathVertexLabel_two {a b : ℕ} (hq : 2 < a+b) (he : a≠2 ∨ b≠2) :
    PathVertexLabel a b 2 := by
  exact exists_graceful_path_two (by omega) (by omega) (by omega)

theorem rootedFork_short {a b d c : ℕ}
    (hd : 1 ≤ d) (hc : 1 ≤ c) (hq : 2 < a+b) (hregion : c ≤ 2*d-16) :
    RootedFork a b d c := by
  apply rootedFork_first_region hd hc (by omega) hregion
  by_cases he : d%2=1
  · simp only [he, ite_true]
    exact (pathVertexLabel_one hq).complement
  · simp only [he, ite_false]
    exact pathVertexLabel_one hq

theorem rootedFork_strip {a b d c : ℕ}
    (hd : 10 ≤ d) (hc : 1 ≤ c) (hq : 2 < a+b) (he : a≠2 ∨ b≠2)
    (hlo : 2*d-15 ≤ c) (hhi : c ≤ 2*d) : RootedFork a b d c := by
  obtain ⟨p,k,hp,hzero,hlow,hhigh⟩ := PathTwoConstruction.alpha_path_strip d c hd hc hlo hhi
  by_cases hd1 : d%2=1
  · obtain ⟨f,hf,hft⟩ := (pathVertexLabel_two hq he).complement
    apply rootedFork_of_paths (by omega) hf hp.1 (by have := hp.2.1; omega) hp.2.2 hzero
    obtain ⟨hfirst,hk⟩ := hlow hd1
    rw [hft,hfirst]
    apply graftJoin_low (by omega) (by omega) (by omega)
  · obtain ⟨f,hf,hft⟩ := pathVertexLabel_two hq he
    apply rootedFork_of_paths (by omega) hf hp.1 (by have := hp.2.1; omega) hp.2.2 hzero
    have hfirst := hhigh (by omega)
    rw [hft,hfirst]
    apply graftJoin_high (by omega) (by omega)

theorem rootedFork_short_all {a b d c : ℕ}
    (hd : 10 ≤ d) (hc : 1 ≤ c) (hq : 2 < a+b) (he : a≠2 ∨ b≠2)
    (hshort : c ≤ 2*d) : RootedFork a b d c := by
  by_cases h : c ≤ 2*d-16
  · exact rootedFork_short (by omega) hc hq h
  · exact rootedFork_strip hd hc hq he (by omega) hshort

end Bounty


/- Supporting module: AlphaCut -/

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
  | zero => simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero]
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


/- Supporting module: ForkPathCut -/

namespace Bounty

theorem NatAlphaPath.cut_eq_zero {n k z : ℕ} {p : ℕ → ℕ}
    (hp : NatAlphaPath n p k) (hz : z < n) (hzero : p z=0) :
    k+1 = if z%2=0 then (n+1)/2 else n/2 := by
  have hpar := hp.low_parity hz
  have hzk : p z ≤ k := by omega
  by_cases he : z%2=0
  · have hfirst : p 0 ≤ k := by simpa only [he, ite_true] using hpar.mp hzk
    let f (i : Fin ((n+1)/2)) : Fin (k+1) := ⟨p (2*i.val), by
      have hi : 2*i.val < n := by have := i.isLt; omega
      have h := hp.low_parity hi
      have heven : (2*i.val)%2=0 := by omega
      have hh : p (2*i.val) ≤ k := h.mpr (by simpa only [heven, ite_true] using hfirst)
      omega⟩
    have hf : Function.Injective f := by
      intro i j heq
      have hh : p (2*i.val)=p (2*j.val) := congrArg Fin.val heq
      have h := hp.1.1 (2*i.val) (2*j.val) (by have := i.isLt; omega)
        (by have := j.isLt; omega) hh
      apply Fin.ext
      omega
    have hb := Fintype.card_le_of_injective f hf
    simp only [Fintype.card_fin] at hb
    have hu := hp.cut_bound
    have hn := hp.2.1
    simp only [he, ite_true]
    omega
  · have hfirst : ¬ p 0 ≤ k := by simpa only [he, ite_false] using hpar.mp hzk
    let f (i : Fin (n/2)) : Fin (k+1) := ⟨p (2*i.val+1), by
      have hi : 2*i.val+1 < n := by have := i.isLt; omega
      have h := hp.low_parity hi
      have heven : ¬(2*i.val+1)%2=0 := by omega
      have hh : p (2*i.val+1) ≤ k := h.mpr (by simpa only [heven, ite_false] using hfirst)
      omega⟩
    have hf : Function.Injective f := by
      intro i j heq
      have hh : p (2*i.val+1)=p (2*j.val+1) := congrArg Fin.val heq
      have h := hp.1.1 (2*i.val+1) (2*j.val+1) (by have := i.isLt; omega)
        (by have := j.isLt; omega) hh
      apply Fin.ext
      omega
    have hb := Fintype.card_le_of_injective f hf
    simp only [Fintype.card_fin] at hb
    have hu := hp.cut_bound_odd_zero hz (by omega) hzero
    simp only [he, ite_false]
    omega

theorem NatAlphaPath.fork_cut {d c k : ℕ} {p : ℕ → ℕ}
    (hd : 1 ≤ d) (hp : NatAlphaPath (d+c) p k) (hz : p (d-1)=0) :
    k = (d-1)/2+c/2 := by
  have h := hp.cut_eq_zero (by omega) hz
  split_ifs at h <;> omega

theorem NatAlphaPath.fork_first_low {d c k : ℕ} {p : ℕ → ℕ}
    (hd : 1 ≤ d) (hp : NatAlphaPath (d+c) p k) (hz : p (d-1)=0) :
    (p 0 ≤ k ↔ d%2=1) := by
  have h := hp.low_parity (by omega : d-1 < d+c)
  have hh : p (d-1) ≤ k := by omega
  split_ifs at h <;> omega

end Bounty


/- Supporting module: ForkGeneric -/




namespace Bounty

/-- The prescribed-label path input sufficient for the generic fork graft. -/
def PathOffMidpoint : Prop := ∀ a b t : ℕ, 1 ≤ a → 1 ≤ b →
  t ≤ a+b → 2*t ≠ a+b → PathVertexLabel a b t

theorem exists_alpha_path_zero_endpoint {n : ℕ} (hn : 2 ≤ n) :
    ∃ p k, NatAlphaPath n p k ∧ p 0=0 := by
  refine ⟨cattellWalecki n,(n-1)/2,⟨⟨?_,?_,?_⟩,?_,?_⟩,?_⟩
  · exact fun i j hi hj hh => cattellWalecki_inj hi hj hh
  · exact fun i hi => cattellWalecki_bound hi
  · intro i j hi hib hj hjb hh
    rw [cattellWalecki_diff hi hib,cattellWalecki_diff hj hjb] at hh
    omega
  · omega
  · intro i hi hib
    unfold cattellWalecki
    split_ifs <;> omega
  · simp only [cattellWalecki,Nat.zero_mod,ite_true,Nat.zero_div]

theorem rootedFork_generic (hpath : PathOffMidpoint) {a b d c : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hd : 1 ≤ d) (hc : 1 ≤ c)
    (he : d ≠ 3 ∨ c ≠ 2) (hq : 2*H1Coverage.R d c < a+b) : RootedFork a b d c := by
  have halpha : ∃ p k, NatAlphaPath (d+c) p k ∧ p (d-1)=0 := by
    by_cases hd1 : d=1
    · subst d
      exact exists_alpha_path_zero_endpoint (by omega)
    · obtain ⟨p,k,hp,hp0⟩ := rosa_zero_alpha_path (d-1) c (by omega) hc (by omega)
      have hn : d-1+c+1=d+c := by omega
      rw [hn] at hp
      exact ⟨p,k,hp,hp0⟩
  obtain ⟨p,k,hp,hp0⟩ := halpha
  have hk := hp.fork_cut hd hp0
  have hfirst := hp.fork_first_low hd hp0
  have hpbound := hp.1.2.1 0 (by omega)
  have hkb : k < d+c := by have := hp.2.1; omega
  by_cases hdo : d%2=1
  · have hlow := hfirst.mpr hdo
    have hR : H1Coverage.R d c=k := by simp only [H1Coverage.R,ite_eq_left hdo]; omega
    rw [hR] at hq
    obtain ⟨f,hf,hf0⟩ := hpath a b (a+b+p 0-k) ha hb (by omega) (by omega)
    apply rootedFork_of_paths hd hf hp.1 hkb hp.2.2 hp0
    exact graftJoin_low hlow hf0 (by omega)
  · have hhigh : k < p 0 := by omega
    have hR : H1Coverage.R d c=d+c-k-2 := by simp only [H1Coverage.R,ite_eq_right hdo]; omega
    rw [hR] at hq
    obtain ⟨f,hf,hf0⟩ := hpath a b (p 0-k-1) ha hb (by omega) (by omega)
    apply rootedFork_of_paths hd hf hp.1 hkb hp.2.2 hp0
    exact graftJoin_high hhigh hf0

end Bounty


/- Supporting module: ForkNeighborGraft -/


namespace Bounty

theorem rootedFork_of_neighbor {a b d c r k : ℕ} {p : ℕ → ℕ}
    (hd : 1 ≤ d) (hm : 7 ≤ d+c) (hr : r=1 ∨ r=2)
    (hp : NatAlphaPath (d+c) p k) (hz : p (d-1)=0)
    (hfirst : p 0=(if d%2=1 then r else d+c-1-r))
    (hbase : PathVertexLabel a b ((d+c-3)/2+1-r)) : RootedFork a b d c := by
  have hk := hp.fork_cut hd hz
  have hklt : k < d+c := by have := hp.2.1; omega
  obtain ⟨f,hf,hf0⟩ := hbase
  have hb := hf.2.1 a (by omega)
  rw [hf0] at hb
  by_cases hdo : d%2=1
  · rw [ite_eq_left hdo] at hfirst
    have hlow : p 0 ≤ k := by omega
    have hlabel : (fun j => a+b-f j) a=a+b+p 0-k := by
      dsimp only
      rw [hf0]
      omega
    apply rootedFork_of_paths hd hf.complement hp.1 hklt hp.2.2 hz
    exact graftJoin_low hlow hlabel (by omega)
  · rw [ite_eq_right hdo] at hfirst
    have hhigh : k < p 0 := by omega
    have hlabel : f a=p 0-k-1 := by omega
    apply rootedFork_of_paths hd hf hp.1 hklt hp.2.2 hz
    exact graftJoin_high hhigh hlabel

theorem rootedFork_d_one {a b c : ℕ} (hc : 1 ≤ c)
    (hbase : PathVertexLabel a b (c/2)) : RootedFork a b 1 c := by
  obtain ⟨p,k,hp,hp0⟩ := exists_alpha_path_zero_endpoint (n := 1+c) (by omega)
  have hk : k=c/2 := by
    have hz : p (1-1)=0 := hp0
    have := hp.fork_cut (d := 1) (c := c) (by omega) hz
    omega
  obtain ⟨f,hf,hf0⟩ := hbase
  have hb := hf.2.1 a (by omega)
  rw [hf0] at hb
  have hlabel : (fun j => a+b-f j) a=a+b+p 0-k := by
    dsimp only
    rw [hf0,hp0,hk]
    omega
  apply rootedFork_of_paths (by omega) hf.complement hp.1 (by have := hp.2.1; omega)
    hp.2.2 hp0
  exact graftJoin_low (by omega) hlabel (by omega)

end Bounty


/- Supporting module: PathOneEnds -/

namespace Bounty.PathConstruction

def StrongHasLow (n k : ℕ) : Prop :=
  ∃ a b P, Terminal a b P ∧ P.length=n ∧ P[k]?=some (L a) ∧ (TL a b P ∨ TH a b P)
def StrongHasHigh (n k : ℕ) : Prop :=
  ∃ a b P, Terminal a b P ∧ P.length=n ∧ P[k]?=some (H b) ∧ (TL a b P ∨ TH a b P)

theorem strong_vh_low_direct {a b : ℕ} {P Q : List Symbol} (h : VH a b P Q) :
    StrongHasLow (P.length+Q.length) P.length := by
  refine ⟨a,b,P++Q,(vh_exit _ _ _ _ h).toTerminal, by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero], ?_, Or.inr (vh_exit _ _ _ _ h)⟩
  simpa only [get_append_boundary] using h.extra_start

theorem strong_vh_high_direct {a b : ℕ} {P Q : List Symbol} (h : VH a b P Q) :
    StrongHasHigh (P.length+Q.length) (P.length-1) := by
  refine ⟨a,b,P++Q,(vh_exit _ _ _ _ h).toTerminal, by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero], ?_, Or.inr (vh_exit _ _ _ _ h)⟩
  simpa only [get_append_last _ _ h.toCore.main_pos] using h.main_end

theorem strong_vl_low_direct {a b : ℕ} {P Q : List Symbol} (h : VL a b P Q) :
    StrongHasLow (P.length+Q.length) (P.length-1) := by
  refine ⟨a,b,P++Q.reverse,(vl_exit _ _ _ _ h).toTerminal, by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero], ?_, Or.inl (vl_exit _ _ _ _ h)⟩
  simpa only [get_append_last _ _ h.toCore.main_pos] using h.main_end

theorem strong_vl_high_direct {a b : ℕ} {P Q : List Symbol} (h : VL a b P Q) :
    StrongHasHigh (P.length+Q.length) P.length := by
  refine ⟨a,b,P++Q.reverse,(vl_exit _ _ _ _ h).toTerminal, by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero], ?_, Or.inl (vl_exit _ _ _ _ h)⟩
  simpa only [get_append_boundary, List.head?_reverse] using h.extra_end

theorem strong_vl_low_short {a b : ℕ} {P Q : List Symbol} (h : VL a b P Q) :
    StrongHasLow (P.length+Q.length+1) (P.length-1) := by
  refine ⟨a,b+1,P++[H (b+1)]++Q,(vl_exit_short _ _ _ _ h).toTerminal, ?_, ?_, Or.inr (vl_exit_short _ _ _ _ h)⟩
  · simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero]; omega
  · rw [List.append_assoc, get_append_last _ _ h.toCore.main_pos]
    exact h.main_end

theorem strong_vl_high_short {a b : ℕ} {P Q : List Symbol} (h : VL a b P Q) :
    StrongHasHigh (P.length+Q.length+1) P.length := by
  refine ⟨a,b+1,P++[H (b+1)]++Q,(vl_exit_short _ _ _ _ h).toTerminal, ?_, ?_, Or.inr (vl_exit_short _ _ _ _ h)⟩
  · simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero]; omega
  · rw [List.append_assoc, get_append_boundary]
    rfl

theorem strong_vh_high_short {a b : ℕ} {P Q : List Symbol} (h : VH a b P Q) :
    StrongHasHigh (P.length+Q.length+1) (P.length-1) := by
  refine ⟨a+1,b,P++[L (a+1)]++Q.reverse,(vh_exit_short _ _ _ _ h).toTerminal, ?_, ?_, Or.inl (vh_exit_short _ _ _ _ h)⟩
  · simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero]; omega
  · rw [List.append_assoc, get_append_last _ _ h.toCore.main_pos]
    exact h.main_end

theorem strong_vh_low_long {a b : ℕ} {P Q : List Symbol} (h : VH a b P Q) :
    StrongHasLow (P.length+Q.length+3) P.length := by
  have hh := strong_vl_low_direct (vh_half _ _ _ _ h)
  simp only [List.length_append, List.length_cons, List.length_nil, List.length_reverse, halfExtra] at hh
  convert hh using 1 <;> (try simp only [List.length_append, List.length_cons, List.length_nil, List.length_reverse]) <;> omega

theorem strong_vl_high_long {a b : ℕ} {P Q : List Symbol} (h : VL a b P Q) :
    StrongHasHigh (P.length+Q.length+3) P.length := by
  have hh := strong_vh_high_direct (vl_half _ _ _ _ h)
  simp only [List.length_append, List.length_cons, List.length_nil, List.length_reverse, halfExtra] at hh
  convert hh using 1 <;> (try simp only [List.length_append, List.length_cons, List.length_nil, List.length_reverse]) <;> omega

theorem strong_symbolic_proposition7 (d c : ℕ) (hdpos : 1 ≤ d) (hcpos : 1 ≤ c)
    (hregion : c ≤ 2*d-16) :
    ∃ a b P, Terminal a b P ∧ P.length = d+c ∧
      P[d-1]? = some (if d%2 = 1 then L a else H b) ∧ (TL a b P ∨ TH a b P) := by
  let t := (c-1)/4
  have hc : c = 4*t + (c-1)%4 + 1 := by dsimp [t]; omega
  have hs : (c-1)%4 = 0 ∨ (c-1)%4 = 1 ∨ (c-1)%4 = 2 ∨ (c-1)%4 = 3 := by omega
  by_cases hd : d%2 = 1
  · simp only [ite_eq_left hd]
    change StrongHasLow (d+c) (d-1)
    rcases hs with hs | hs | hs | hs
    · obtain ⟨a,b,P,Q,h,hP,hQ⟩ := prepared_odd (d-2-2*t) t (by omega) (by omega)
      have hr := strong_vh_low_direct h
      rw [hP,hQ] at hr
      convert hr using 1 <;> omega
    · obtain ⟨a,b,P,Q,h,hP,hQ⟩ := prepared_even (d-1-2*t) t (by omega) (by omega)
      have hr := strong_vl_low_direct h
      rw [hP,hQ] at hr
      convert hr using 1 <;> omega
    · obtain ⟨a,b,P,Q,h,hP,hQ⟩ := prepared_even (d-1-2*t) t (by omega) (by omega)
      have hr := strong_vl_low_short h
      rw [hP,hQ] at hr
      convert hr using 1 <;> omega
    · obtain ⟨a,b,P,Q,h,hP,hQ⟩ := prepared_odd (d-2-2*t) t (by omega) (by omega)
      have hr := strong_vh_low_long h
      rw [hP,hQ] at hr
      convert hr using 1 <;> omega
  · simp only [ite_eq_right hd]
    change StrongHasHigh (d+c) (d-1)
    have hd0 : d%2 = 0 := by omega
    rcases hs with hs | hs | hs | hs
    · obtain ⟨a,b,P,Q,h,hP,hQ⟩ := prepared_even (d-2-2*t) t (by omega) (by omega)
      have hr := strong_vl_high_direct h
      rw [hP,hQ] at hr
      convert hr using 1 <;> omega
    · obtain ⟨a,b,P,Q,h,hP,hQ⟩ := prepared_even (d-2-2*t) t (by omega) (by omega)
      have hr := strong_vl_high_short h
      rw [hP,hQ] at hr
      convert hr using 1 <;> omega
    · obtain ⟨a,b,P,Q,h,hP,hQ⟩ := prepared_odd (d-1-2*t) t (by omega) (by omega)
      have hr := strong_vh_high_short h
      rw [hP,hQ] at hr
      convert hr using 1 <;> omega
    · obtain ⟨a,b,P,Q,h,hP,hQ⟩ := prepared_even (d-2-2*t) t (by omega) (by omega)
      have hr := strong_vl_high_long h
      rw [hP,hQ] at hr
      convert hr using 1 <;> omega


end Bounty.PathConstruction


/- Supporting module: PathOneReverse -/


namespace Bounty
open PathConstruction

theorem alpha_path_reversed_one {d c : ℕ} (hd : 2 ≤ d) (hc : 1 ≤ c)
    (hregion : d-1 ≤ 2*(c+1)-16) :
    ∃ p k, NatAlphaPath (d+c) p k ∧ p (d-1)=0 ∧
      p 0=(if d%2=1 then 1 else d+c-2) := by
  obtain ⟨a,b,P,h,hlen,hpin,hend⟩ := strong_symbolic_proposition7 (c+1) (d-1)
    (by omega) (by omega) hregion
  have hlen' : P.length=d+c := by omega
  let low := decide ((c+1)%2=1)
  let f := boundaryPath low a b P
  let k := boundaryCut low a b
  have hf : NatAlphaPath (d+c) f k := boundaryPath_alpha h hlen' low
  have hz : f c=0 := by
    have hi : P[c]?=some (if low then L a else H b) := by
      simpa only [Nat.add_sub_cancel,low,Bool.decide_iff] using hpin
    simp only [f,boundaryPath,symbolAt,hi,Option.getD_some]
    cases low <;> simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, boundaryLabel]
  let g := reverseNatPath (d+c) f
  have hg : NatAlphaPath (d+c) g k := hf.reverse
  have hg0 : g (d-1)=0 := by
    have hi : d+c-1-(d-1)=c := by omega
    simpa only [g,reverseNatPath,hi] using hz
  have hlast : f (d+c-1)=1 ∨ f (d+c-1)=d+c-2 := by
    have hl := h.length
    rcases hend with ht | ht
    · have he : P[d+c-1]?=some (L (a-1)) := by
        simpa only [List.getLast?_eq_getElem?,hlen'] using ht.main_end
      simp only [f,boundaryPath,symbolAt,he,Option.getD_some]
      have ha := ht.low_pos
      cases low <;> simp only [boundaryLabel] <;> omega
    · have he : P[d+c-1]?=some (H (b-1)) := by
        simpa only [List.getLast?_eq_getElem?,hlen'] using ht.main_end
      simp only [f,boundaryPath,symbolAt,he,Option.getD_some]
      have hb := ht.high_pos
      cases low <;> simp only [boundaryLabel] <;> omega
  have hfirst : g 0=1 ∨ g 0=d+c-2 := by
    simpa only [g,reverseNatPath,Nat.sub_zero] using hlast
  have hk := hg.fork_cut (by omega) hg0
  have hcolor := hg.fork_first_low (by omega) hg0
  refine ⟨g,k,hg,hg0,?_⟩
  split_ifs <;> omega

end Bounty


/- Supporting module: PathTwoPrefix -/

namespace Bounty.PathTwoConstruction
open PathConstruction

def shiftThree : Symbol → Symbol
  | .inl i => L (i+3)
  | .inr i => H (i+3)

def lowPrefix : List Symbol := [L 2,H 2,L 1,H 1,L 0,H 0]
def prefixMain (P : List Symbol) := lowPrefix++P.map shiftThree
def prefixExtra (Q : List Symbol) := Q.map shiftThree

lemma shiftThree_index (x : Symbol) : index (shiftThree x)=index x+3 := by cases x <;> rfl

lemma shiftThree_opposite (x y : Symbol) :
    PathConstruction.Opposite (shiftThree x) (shiftThree y) ↔ PathConstruction.Opposite x y := by
  cases x <;> cases y <;> rfl

lemma shiftThree_chain {P : List Symbol} (h : P.IsChain PathConstruction.Opposite) :
    (P.map shiftThree).IsChain PathConstruction.Opposite := by
  rw [List.isChain_map]
  exact h.imp (fun {x y} hxy => (shiftThree_opposite x y).2 hxy)

lemma shiftThree_edges (P : List Symbol) :
    edgeSums (P.map shiftThree)=(edgeSums P).map (fun i => i+6) := by
  induction P using List.twoStepInduction with
  | nil => rfl
  | singleton x => rfl
  | cons_cons x y xs _ ih =>
    change (index (shiftThree x)+index (shiftThree y)) :: edgeSums ((y::xs).map shiftThree) =
      (index x+index y+6) :: (edgeSums (y::xs)).map (fun i => i+6)
    rw [ih y,shiftThree_index,shiftThree_index]
    congr 1
    omega

lemma shiftThree_edgeBag (P : List Symbol) :
    edgeBag (P.map shiftThree)=(edgeBag P).map (fun i => i+6) := by
  rw [edgeBag,shiftThree_edges]
  rfl

lemma shiftThree_lowBag (n : ℕ) :
    lowBag 3+(lowBag n).map shiftThree=lowBag (n+3) := by
  induction n with
  | zero => simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, lowBag,bag]
  | succ n ih =>
    rw [lowBag_succ n,Multiset.map_add,Multiset.map_singleton,←add_assoc,ih]
    rw [show n+1+3=(n+3)+1 by omega,lowBag_succ (n+3)]
    rfl

lemma shiftThree_highBag (n : ℕ) :
    highBag 3+(highBag n).map shiftThree=highBag (n+3) := by
  induction n with
  | zero => simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, highBag,bag]
  | succ n ih =>
    rw [highBag_succ n,Multiset.map_add,Multiset.map_singleton,←add_assoc,ih]
    rw [show n+1+3=(n+3)+1 by omega,highBag_succ (n+3)]
    rfl

lemma shiftSix_rangeBag (n : ℕ) :
    rangeBag 6+(rangeBag n).map (fun i => i+6)=rangeBag (n+6) := by
  induction n with
  | zero => simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, rangeBag,bag]
  | succ n ih =>
    rw [rangeBag_succ n,Multiset.map_add,Multiset.map_singleton,←add_assoc,ih]
    rw [show n+1+6=(n+6)+1 by omega,rangeBag_succ (n+6)]

lemma prefixCore_vertices {a b : ℕ} {P Q : List Symbol} (h : Core a b P Q) :
    bag (prefixMain P)+bag (prefixExtra Q)=lowBag (a+3+1)+highBag (b+3+1) := by
  have hp : bag lowPrefix=lowBag 3+highBag 3 := by decide
  have hm := congrArg (fun x : Multiset Symbol => x.map shiftThree) h.vertices
  simp only [Multiset.map_add] at hm
  have hP : bag (P.map shiftThree)=(bag P).map shiftThree := rfl
  have hQ : bag (Q.map shiftThree)=(bag Q).map shiftThree := rfl
  simp only [prefixMain,prefixExtra,bag_append,hp,hP,hQ]
  calc
    _ = lowBag 3+highBag 3+((bag P).map shiftThree+(bag Q).map shiftThree) := by ac_rfl
    _ = lowBag 3+highBag 3+((lowBag (a+1)).map shiftThree+(highBag (b+1)).map shiftThree) := by rw [hm]
    _ = (lowBag 3+(lowBag (a+1)).map shiftThree)+(highBag 3+(highBag (b+1)).map shiftThree) := by ac_rfl
    _ = _ := by rw [shiftThree_lowBag,shiftThree_highBag]

lemma prefixCore_edges {a b : ℕ} {P Q : List Symbol} (h : Core a b P Q) :
    edgeBag (prefixMain P)+edgeBag (prefixExtra Q)=rangeBag (a+3+(b+3)) := by
  have hhead : (P.map shiftThree).head?=some (L 5) := by
    simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, List.head?_map,h.main_start,shiftThree]
  have hp : edgeBag lowPrefix+{5}=rangeBag 6 := by decide
  have hm := congrArg (fun x : Multiset ℕ => x.map (fun i => i+6)) h.edges
  simp only [Multiset.map_add] at hm
  rw [prefixMain,edgeBag_append _ _ (H 0) (L 5) rfl hhead]
  change (edgeBag lowPrefix+{5}+edgeBag (P.map shiftThree))+edgeBag (Q.map shiftThree)=_
  rw [hp,shiftThree_edgeBag,shiftThree_edgeBag,add_assoc,hm,shiftSix_rangeBag]
  congr 1
  omega

lemma prefixCore {a b : ℕ} {P Q : List Symbol} (h : Core a b P Q) :
    Core (a+3) (b+3) (prefixMain P) (prefixExtra Q) := by
  refine ⟨rfl,?_,shiftThree_chain h.extra_alternates,prefixCore_vertices h,prefixCore_edges h⟩
  have hh := shiftThree_chain h.main_alternates
  rw [prefixMain,List.isChain_append]
  simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, lowPrefix,List.isChain_cons,PathConstruction.Opposite,hh,List.head?_map,
    h.main_start,shiftThree]

/-- Add six vertices to the main component while preserving the two-component
invariant and all endpoint offsets. -/
theorem vh_prefix {a b : ℕ} {P Q : List Symbol} (h : VH a b P Q) :
    VH (a+3) (b+3) (prefixMain P) (prefixExtra Q) := by
  refine ⟨prefixCore h.toCore,by omega,?_,?_,?_⟩
  · simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, prefixMain,List.getLast?_append,List.getLast?_map,h.main_end,shiftThree]
  · simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, prefixExtra,List.head?_map,h.extra_start,shiftThree]
  · have hb := h.high_pos
    simp only [prefixExtra,List.getLast?_map,h.extra_end,Option.map_some,shiftThree]
    congr 2
    omega

theorem vl_prefix {a b : ℕ} {P Q : List Symbol} (h : VL a b P Q) :
    VL (a+3) (b+3) (prefixMain P) (prefixExtra Q) := by
  refine ⟨prefixCore h.toCore,by omega,?_,?_,?_⟩
  · simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, prefixMain,List.getLast?_append,List.getLast?_map,h.main_end,shiftThree]
  · have ha := h.low_pos
    simp only [prefixExtra,List.head?_map,h.extra_start,Option.map_some,shiftThree]
    congr 2
    omega
  · simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, prefixExtra,List.getLast?_map,h.extra_end,shiftThree]

theorem vh_prefixes (s a b : ℕ) (P Q : List Symbol) (h : VH a b P Q) :
    ∃ P' Q', VH (a+3*s) (b+3*s) P' Q' ∧ P'.length=P.length+6*s ∧ Q'.length=Q.length := by
  induction s with
  | zero => exact ⟨P,Q,by simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero] using h,by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero],rfl⟩
  | succ s ih =>
    obtain ⟨P',Q',hs,hP,hQ⟩ := ih
    refine ⟨prefixMain P',prefixExtra Q',?_,?_,?_⟩
    · convert vh_prefix hs using 1 <;> omega
    · simp only [prefixMain,lowPrefix,List.length_append,List.length_cons,List.length_nil,List.length_map,hP]
      omega
    · simp only [prefixExtra,List.length_map,hQ]

theorem vl_prefixes (s a b : ℕ) (P Q : List Symbol) (h : VL a b P Q) :
    ∃ P' Q', VL (a+3*s) (b+3*s) P' Q' ∧ P'.length=P.length+6*s ∧ Q'.length=Q.length := by
  induction s with
  | zero => exact ⟨P,Q,by simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero] using h,by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero],rfl⟩
  | succ s ih =>
    obtain ⟨P',Q',hs,hP,hQ⟩ := ih
    refine ⟨prefixMain P',prefixExtra Q',?_,?_,?_⟩
    · convert vl_prefix hs using 1 <;> omega
    · simp only [prefixMain,lowPrefix,List.length_append,List.length_cons,List.length_nil,List.length_map,hP]
      omega
    · simp only [prefixExtra,List.length_map,hQ]

end Bounty.PathTwoConstruction


/- Supporting module: PathTwoShort -/

namespace Bounty.PathTwoConstruction
open PathConstruction

private theorem flat_PathTwoShort_short_seed_0 : VH 6 6 [L 2, H 0, L 0, H 1, L 4, H 5, L 3, H 3, L 1, H 2, L 5, H 6] [L 6, H 4] := by
  refine ⟨⟨rfl, by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, List.isChain_cons,PathConstruction.Opposite],
    by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, List.isChain_cons,PathConstruction.Opposite], by decide, by decide⟩,
    by decide, rfl, rfl, rfl⟩

private theorem flat_PathTwoShort_short_seed_1 : VH 4 4 [L 2, H 3, L 0, H 0, L 1, H 1, L 3, H 4] [L 4, H 2] := by
  refine ⟨⟨rfl, by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, List.isChain_cons,PathConstruction.Opposite],
    by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, List.isChain_cons,PathConstruction.Opposite], by decide, by decide⟩,
    by decide, rfl, rfl, rfl⟩

private theorem flat_PathTwoShort_short_seed_2 : VH 5 5 [L 2, H 1, L 3, H 4, L 1, H 0, L 0, H 2, L 4, H 5] [L 5, H 3] := by
  refine ⟨⟨rfl, by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, List.isChain_cons,PathConstruction.Opposite],
    by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, List.isChain_cons,PathConstruction.Opposite], by decide, by decide⟩,
    by decide, rfl, rfl, rfl⟩

private theorem flat_PathTwoShort_short_seed_3 : VH 4 4 [L 2, H 1, L 1, H 0, L 0, H 4] [L 4, H 3, L 3, H 2] := by
  refine ⟨⟨rfl, by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, List.isChain_cons,PathConstruction.Opposite],
    by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, List.isChain_cons,PathConstruction.Opposite], by decide, by decide⟩,
    by decide, rfl, rfl, rfl⟩

private theorem flat_PathTwoShort_short_seed_4 : VH 5 5 [L 2, H 0, L 0, H 1, L 3, H 2, L 1, H 5] [L 5, H 4, L 4, H 3] := by
  refine ⟨⟨rfl, by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, List.isChain_cons,PathConstruction.Opposite],
    by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, List.isChain_cons,PathConstruction.Opposite], by decide, by decide⟩,
    by decide, rfl, rfl, rfl⟩

private theorem flat_PathTwoShort_short_seed_5 : VH 6 6 [L 2, H 1, L 3, H 2, L 0, H 0, L 1, H 5, L 5, H 6] [L 6, H 3, L 4, H 4] := by
  refine ⟨⟨rfl, by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, List.isChain_cons,PathConstruction.Opposite],
    by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, List.isChain_cons,PathConstruction.Opposite], by decide, by decide⟩,
    by decide, rfl, rfl, rfl⟩

private theorem flat_PathTwoShort_short_seed_6 : VL 7 6 [L 2, H 1, L 1, H 0, L 0, H 4, L 6, H 2, L 3, H 3, L 4, H 5, L 7] [L 5, H 6] := by
  refine ⟨⟨rfl, by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, List.isChain_cons,PathConstruction.Opposite],
    by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, List.isChain_cons,PathConstruction.Opposite], by decide, by decide⟩,
    by decide, rfl, rfl, rfl⟩

private theorem flat_PathTwoShort_short_seed_7 : VL 5 4 [L 2, H 0, L 0, H 1, L 4, H 2, L 1, H 3, L 5] [L 3, H 4] := by
  refine ⟨⟨rfl, by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, List.isChain_cons,PathConstruction.Opposite],
    by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, List.isChain_cons,PathConstruction.Opposite], by decide, by decide⟩,
    by decide, rfl, rfl, rfl⟩

private theorem flat_PathTwoShort_short_seed_8 : VL 3 2 [L 2, H 0, L 0, H 1, L 3] [L 1, H 2] := by
  refine ⟨⟨rfl, by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, List.isChain_cons,PathConstruction.Opposite],
    by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, List.isChain_cons,PathConstruction.Opposite], by decide, by decide⟩,
    by decide, rfl, rfl, rfl⟩

private theorem flat_PathTwoShort_short_seed_9 : VL 5 4 [L 2, H 2, L 1, H 1, L 0, H 0, L 5] [L 3, H 3, L 4, H 4] := by
  refine ⟨⟨rfl, by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, List.isChain_cons,PathConstruction.Opposite],
    by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, List.isChain_cons,PathConstruction.Opposite], by decide, by decide⟩,
    by decide, rfl, rfl, rfl⟩

private theorem flat_PathTwoShort_short_seed_10 : VL 3 2 [L 2, H 1, L 3] [L 1, H 0, L 0, H 2] := by
  refine ⟨⟨rfl, by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, List.isChain_cons,PathConstruction.Opposite],
    by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, List.isChain_cons,PathConstruction.Opposite], by decide, by decide⟩,
    by decide, rfl, rfl, rfl⟩

private theorem flat_PathTwoShort_short_seed_11 : VL 7 6 [L 2, H 0, L 0, H 1, L 4, H 4, L 3, H 3, L 1, H 2, L 7] [L 5, H 5, L 6, H 6] := by
  refine ⟨⟨rfl, by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, List.isChain_cons,PathConstruction.Opposite],
    by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, List.isChain_cons,PathConstruction.Opposite], by decide, by decide⟩,
    by decide, rfl, rfl, rfl⟩

private theorem flat_PathTwoShort_vh_short_extend {a b p q t : ℕ} {P Q : List Symbol}
    (h : VH a b P Q) (ha : 2≤a) (hb : 2≤b)
    (hsmall : P.length≤p-2*t) (hmod : (p-2*t)%6=P.length%6)
    (hp : 2*t≤p) (hq : q=Q.length+4*t) :
    ∃ a b P Q, VH a b P Q ∧ 2≤a ∧ 2≤b ∧ P.length=p ∧ Q.length=q := by
  let s := (p-2*t-P.length)/6
  obtain ⟨P',Q',h',hP',hQ'⟩ := vh_prefixes s a b P Q h
  obtain ⟨P'',Q'',h'',hP'',hQ''⟩ := vh_cycles t (a+3*s) (b+3*s) P' Q' h'
  refine ⟨_,_,P'',Q'',h'',by omega,by omega,?_,by omega⟩
  dsimp [s] at *
  omega

theorem prepared_short_vh (p q : ℕ) (hq : 2≤q) (hqeven : q%2=0)
    (hp : q/2+12≤p) (hpar : p%2=0) :
    ∃ a b P Q, VH a b P Q ∧ 2≤a ∧ 2≤b ∧ P.length=p ∧ Q.length=q := by
  by_cases hq2 : q%4=2

  · let t := (q-2)/4
    have heq : q=2+4*t := by dsimp [t]; omega
    have hsmall : 13≤p-2*t := by omega
    have ht : 2*t≤p := by omega
    have hmod : (p-2*t)%2=0 := by omega
    have hr : (p-2*t)%6<6 := Nat.mod_lt _ (by decide)
    generalize heqr : (p-2*t)%6=r at *
    interval_cases r

    · apply flat_PathTwoShort_vh_short_extend flat_PathTwoShort_short_seed_0 (by decide) (by decide) (t:=t)
      all_goals (try simp only [List.length_cons,List.length_nil]) <;> omega

    · omega

    · apply flat_PathTwoShort_vh_short_extend flat_PathTwoShort_short_seed_1 (by decide) (by decide) (t:=t)
      all_goals (try simp only [List.length_cons,List.length_nil]) <;> omega

    · omega

    · apply flat_PathTwoShort_vh_short_extend flat_PathTwoShort_short_seed_2 (by decide) (by decide) (t:=t)
      all_goals (try simp only [List.length_cons,List.length_nil]) <;> omega

    · omega

  · let t := (q-4)/4
    have heq : q=4+4*t := by dsimp [t]; omega
    have hsmall : 13≤p-2*t := by omega
    have ht : 2*t≤p := by omega
    have hmod : (p-2*t)%2=0 := by omega
    have hr : (p-2*t)%6<6 := Nat.mod_lt _ (by decide)
    generalize heqr : (p-2*t)%6=r at *
    interval_cases r

    · apply flat_PathTwoShort_vh_short_extend flat_PathTwoShort_short_seed_3 (by decide) (by decide) (t:=t)
      all_goals (try simp only [List.length_cons,List.length_nil]) <;> omega

    · omega

    · apply flat_PathTwoShort_vh_short_extend flat_PathTwoShort_short_seed_4 (by decide) (by decide) (t:=t)
      all_goals (try simp only [List.length_cons,List.length_nil]) <;> omega

    · omega

    · apply flat_PathTwoShort_vh_short_extend flat_PathTwoShort_short_seed_5 (by decide) (by decide) (t:=t)
      all_goals (try simp only [List.length_cons,List.length_nil]) <;> omega

    · omega

private theorem flat_PathTwoShort_vl_short_extend {a b p q t : ℕ} {P Q : List Symbol}
    (h : VL a b P Q) (ha : 2≤a) (hb : 2≤b)
    (hsmall : P.length≤p-2*t) (hmod : (p-2*t)%6=P.length%6)
    (hp : 2*t≤p) (hq : q=Q.length+4*t) :
    ∃ a b P Q, VL a b P Q ∧ 2≤a ∧ 2≤b ∧ P.length=p ∧ Q.length=q := by
  let s := (p-2*t-P.length)/6
  obtain ⟨P',Q',h',hP',hQ'⟩ := vl_prefixes s a b P Q h
  obtain ⟨P'',Q'',h'',hP'',hQ''⟩ := vl_cycles t (a+3*s) (b+3*s) P' Q' h'
  refine ⟨_,_,P'',Q'',h'',by omega,by omega,?_,by omega⟩
  dsimp [s] at *
  omega

theorem prepared_short_vl (p q : ℕ) (hq : 2≤q) (hqeven : q%2=0)
    (hp : q/2+12≤p) (hpar : p%2=1) :
    ∃ a b P Q, VL a b P Q ∧ 2≤a ∧ 2≤b ∧ P.length=p ∧ Q.length=q := by
  by_cases hq2 : q%4=2

  · let t := (q-2)/4
    have heq : q=2+4*t := by dsimp [t]; omega
    have hsmall : 13≤p-2*t := by omega
    have ht : 2*t≤p := by omega
    have hmod : (p-2*t)%2=1 := by omega
    have hr : (p-2*t)%6<6 := Nat.mod_lt _ (by decide)
    generalize heqr : (p-2*t)%6=r at *
    interval_cases r

    · omega

    · apply flat_PathTwoShort_vl_short_extend flat_PathTwoShort_short_seed_6 (by decide) (by decide) (t:=t)
      all_goals (try simp only [List.length_cons,List.length_nil]) <;> omega

    · omega

    · apply flat_PathTwoShort_vl_short_extend flat_PathTwoShort_short_seed_7 (by decide) (by decide) (t:=t)
      all_goals (try simp only [List.length_cons,List.length_nil]) <;> omega

    · omega

    · apply flat_PathTwoShort_vl_short_extend flat_PathTwoShort_short_seed_8 (by decide) (by decide) (t:=t)
      all_goals (try simp only [List.length_cons,List.length_nil]) <;> omega

  · let t := (q-4)/4
    have heq : q=4+4*t := by dsimp [t]; omega
    have hsmall : 13≤p-2*t := by omega
    have ht : 2*t≤p := by omega
    have hmod : (p-2*t)%2=1 := by omega
    have hr : (p-2*t)%6<6 := Nat.mod_lt _ (by decide)
    generalize heqr : (p-2*t)%6=r at *
    interval_cases r

    · omega

    · apply flat_PathTwoShort_vl_short_extend flat_PathTwoShort_short_seed_9 (by decide) (by decide) (t:=t)
      all_goals (try simp only [List.length_cons,List.length_nil]) <;> omega

    · omega

    · apply flat_PathTwoShort_vl_short_extend flat_PathTwoShort_short_seed_10 (by decide) (by decide) (t:=t)
      all_goals (try simp only [List.length_cons,List.length_nil]) <;> omega

    · omega

    · apply flat_PathTwoShort_vl_short_extend flat_PathTwoShort_short_seed_11 (by decide) (by decide) (t:=t)
      all_goals (try simp only [List.length_cons,List.length_nil]) <;> omega



def HasTwoEnd (a b : ℕ) (P : List Symbol) : Prop :=
  (2≤a ∧ P.getLast?=some (L (a-2))) ∨ (2≤b ∧ P.getLast?=some (H (b-2)))

def StrongHasLowTwo (n k : ℕ) : Prop :=
  ∃ a b P, Terminal a b P ∧ P.length=n ∧ P[k]?=some (L a) ∧ HasTwoEnd a b P

def StrongHasHighTwo (n k : ℕ) : Prop :=
  ∃ a b P, Terminal a b P ∧ P.length=n ∧ P[k]?=some (H b) ∧ HasTwoEnd a b P

theorem vh_two_low_direct {a b : ℕ} {P Q : List Symbol} (h : VH a b P Q) :
    StrongHasLowTwo (P.length+Q.length) P.length := by
  refine ⟨a,b,P++Q,vh_exit _ _ _ _ h,by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero],?_,Or.inr ⟨h.high_pos,?_⟩⟩
  · simpa only [get_append_boundary] using h.extra_start
  · simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, List.getLast?_append,h.extra_end]

theorem vh_two_high_direct {a b : ℕ} {P Q : List Symbol} (h : VH a b P Q) :
    StrongHasHighTwo (P.length+Q.length) (P.length-1) := by
  refine ⟨a,b,P++Q,vh_exit _ _ _ _ h,by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero],?_,Or.inr ⟨h.high_pos,?_⟩⟩
  · simpa only [get_append_last _ _ h.toCore.main_pos] using h.main_end
  · simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, List.getLast?_append,h.extra_end]

theorem vl_two_low_direct {a b : ℕ} {P Q : List Symbol} (h : VL a b P Q) :
    StrongHasLowTwo (P.length+Q.length) (P.length-1) := by
  refine ⟨a,b,P++Q.reverse,vl_exit _ _ _ _ h,by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero],?_,Or.inl ⟨h.low_pos,?_⟩⟩
  · simpa only [get_append_last _ _ h.toCore.main_pos] using h.main_end
  · simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, List.getLast?_append,List.getLast?_reverse,h.extra_start]

theorem vl_two_high_direct {a b : ℕ} {P Q : List Symbol} (h : VL a b P Q) :
    StrongHasHighTwo (P.length+Q.length) P.length := by
  refine ⟨a,b,P++Q.reverse,vl_exit _ _ _ _ h,by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero],?_,Or.inl ⟨h.low_pos,?_⟩⟩
  · simpa only [get_append_boundary,List.head?_reverse] using h.extra_end
  · simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, List.getLast?_append,List.getLast?_reverse,h.extra_start]

/-- The long main component construction, retaining the terminal offset two. -/
theorem symbolic_short_reverse (d c : ℕ) (hd : 2≤d) (hroom : d+24≤2*c) :
    ∃ a b P, Terminal a b P ∧ P.length=d+c ∧
      P[c]?=some (if c%2=0 then L a else H b) ∧ HasTwoEnd a b P := by
  by_cases hc : c%2=0
  · simp only [ite_eq_left hc]
    change StrongHasLowTwo (d+c) c
    by_cases hdo : d%2=1
    · obtain ⟨a,b,P,Q,h,_,_,hP,hQ⟩ := prepared_short_vl (c+1) (d-1)
        (by omega) (by omega) (by omega) (by omega)
      have hr := vl_two_low_direct h
      rw [hP,hQ] at hr
      convert hr using 1 <;> omega
    · obtain ⟨a,b,P,Q,h,_,_,hP,hQ⟩ := prepared_short_vh c d
        hd (by omega) (by omega) hc
      have hr := vh_two_low_direct h
      rw [hP,hQ] at hr
      convert hr using 1 <;> omega
  · simp only [ite_eq_right hc]
    change StrongHasHighTwo (d+c) c
    by_cases hdo : d%2=1
    · obtain ⟨a,b,P,Q,h,_,_,hP,hQ⟩ := prepared_short_vh (c+1) (d-1)
        (by omega) (by omega) (by omega) (by omega)
      have hr := vh_two_high_direct h
      rw [hP,hQ] at hr
      convert hr using 1 <;> omega
    · obtain ⟨a,b,P,Q,h,_,_,hP,hQ⟩ := prepared_short_vl c d
        hd (by omega) (by omega) (by omega)
      have hr := vl_two_high_direct h
      rw [hP,hQ] at hr
      convert hr using 1 <;> omega

end Bounty.PathTwoConstruction


/- Supporting module: PathReverseEnd -/

namespace Bounty
open PathConstruction

theorem alpha_path_reverse_boundary_end {d c a b r : ℕ} {P : List Symbol} {low : Bool}
    (hd : 1 ≤ d) (hm : 2*r+3 ≤ d+c)
    (hlen : P.length=d+c) (hsize : P.length=a+b+2)
    (ha : NatAlphaPath (d+c) (boundaryPath low a b P) (boundaryCut low a b))
    (hpin : P[c]?=some (if low then L a else H b))
    (hend : (r ≤ a ∧ P.getLast?=some (L (a-r))) ∨
      (r ≤ b ∧ P.getLast?=some (H (b-r)))) :
    ∃ p k, NatAlphaPath (d+c) p k ∧ p (d-1)=0 ∧
      p 0=(if d%2=1 then r else d+c-1-r) := by
  let f := boundaryPath low a b P
  let k := boundaryCut low a b
  have hz : f c=0 := by
    simp only [f,boundaryPath,symbolAt,hpin,Option.getD_some]
    cases low <;> simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, boundaryLabel]
  let g := reverseNatPath (d+c) f
  have hg : NatAlphaPath (d+c) g k := ha.reverse
  have hg0 : g (d-1)=0 := by
    have hi : d+c-1-(d-1)=c := by omega
    simpa only [g,reverseNatPath,hi] using hz
  have hlast : f (d+c-1)=r ∨ f (d+c-1)=d+c-1-r := by
    rcases hend with ⟨hr,ht⟩ | ⟨hr,ht⟩
    · have he : P[d+c-1]?=some (L (a-r)) := by
        simpa only [List.getLast?_eq_getElem?,hlen] using ht
      simp only [f,boundaryPath,symbolAt,he,Option.getD_some]
      cases low <;> simp only [boundaryLabel] <;> omega
    · have he : P[d+c-1]?=some (H (b-r)) := by
        simpa only [List.getLast?_eq_getElem?,hlen] using ht
      simp only [f,boundaryPath,symbolAt,he,Option.getD_some]
      cases low <;> simp only [boundaryLabel] <;> omega
  have hfirst : g 0=r ∨ g 0=d+c-1-r := by
    simpa only [g,reverseNatPath,Nat.sub_zero] using hlast
  have hk := hg.fork_cut hd hg0
  have hcolor := hg.fork_first_low hd hg0
  refine ⟨g,k,hg,hg0,?_⟩
  split_ifs <;> omega

end Bounty


/- Supporting module: PathTwoShortNumeric -/



namespace Bounty.PathTwoConstruction
open PathConstruction

/-- A zero-rooted alpha path whose other end has label two (or its complement). -/
theorem alpha_path_two_short (d c : ℕ) (hd : 2≤d) (hroom : d+24≤2*c) :
    ∃ p k, NatAlphaPath (d+c) p k ∧ p (d-1)=0 ∧
      p 0=(if d%2=1 then 2 else d+c-3) := by
  obtain ⟨a,b,P,h,hlen,hpin,hend⟩ := symbolic_short_reverse d c hd hroom
  have hp := alpha_path_reverse_boundary_end (d:=d) (c:=c) (r:=2)
    (low:=decide (c%2=0)) (by omega) (by omega) hlen h.length
    (boundaryPath_alpha h hlen (decide (c%2=0))) (by simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero] using hpin) hend
  exact hp

end Bounty.PathTwoConstruction


/- Supporting module: H1Tail -/





namespace Bounty
open H1Coverage

theorem neighbor_one {d c : ℕ} (hd : 2≤d) (hc : 2*d<c)
    (hex : d≠2 ∨ c≠6) : NeighborAlphaPath d c 1 := by
  by_cases hlarge : d+24≤2*c
  · obtain ⟨p,k,hp,hz,hfirst⟩ := alpha_path_reversed_one (d:=d) (c:=c) hd (by omega) (by omega)
    refine ⟨p,k,hp,hz,?_⟩
    convert hfirst using 1 <;> split_ifs <;> omega
  · exact neighbor_finite_one hd hc (by omega) hex

theorem neighbor_two {d c : ℕ} (hd : 2≤d) (hc : 2*d<c)
    (hex6 : d≠2 ∨ c≠6) (hex7 : d≠2 ∨ c≠7) : NeighborAlphaPath d c 2 := by
  by_cases hlarge : d+24≤2*c
  · obtain ⟨p,k,hp,hz,hfirst⟩ := PathTwoConstruction.alpha_path_two_short d c hd hlarge
    refine ⟨p,k,hp,hz,?_⟩
    convert hfirst using 1 <;> split_ifs <;> omega
  · exact neighbor_finite_two hd hc (by omega) hex6 hex7

private theorem flat_H1Tail_small_neighbor_arms {a b c : ℕ} (ha : 1≤a) (hab : a≤b)
    (hc : c=6 ∨ c=7) (ht : c<Cut a b 2+1)
    (hl : ¬OuterAvailable a b 2 c) (hr : ¬OuterAvailable b a 2 c) :
    a=6 ∧ b=6 := by
  unfold OuterAvailable Cut U at *
  norm_num [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero] at *
  omega

/-- The remaining long third arm is covered by two neighboring path labels. -/
theorem rootedFork_tail_remaining {a b d c : ℕ}
    (ha : 1≤a) (hab : a≤b) (hd : 1≤d) (hc : 2*d<c)
    (ht : c<Cut a b d+1)
    (hl : ¬OuterAvailable a b d c) (hr : ¬OuterAvailable b a d c) :
    RootedFork a b d c := by
  by_cases hd1 : d=1
  · subst d
    by_cases he4 : a=4 ∧ b=4 ∧ c=3
    · obtain ⟨rfl,rfl,rfl⟩ := he4
      exact neighbor_exception_4_4_1_3
    by_cases he5 : a=5 ∧ b=5 ∧ c=6
    · obtain ⟨rfl,rfl,rfl⟩ := he5
      exact neighbor_exception_5_5_1_6
    exact rootedFork_d_one (by omega)
      (centralSpliceAvailable_path (h1_splice_d1 a b c ha hab (by omega) ht hl hr ⟨he4,he5⟩))
  have hd2 : 2≤d := by omega
  have hm : 7≤d+c := by omega
  by_cases he6 : d=2 ∧ c=6
  · obtain ⟨rfl,rfl⟩ := he6
    obtain ⟨rfl,rfl⟩ := flat_H1Tail_small_neighbor_arms ha hab (Or.inl rfl) ht hl hr
    exact neighbor_exception_rooted
  by_cases he7 : d=2 ∧ c=7
  · obtain ⟨rfl,rfl⟩ := he7
    obtain ⟨rfl,rfl⟩ := flat_H1Tail_small_neighbor_arms ha hab (Or.inr rfl) ht hl hr
    obtain ⟨p,k,hp,hz,hfirst⟩ := neighbor_one hd2 hc (by omega)
    apply rootedFork_of_neighbor hd hm (Or.inl rfl) hp hz hfirst
    apply centralSpliceAvailable_path
    norm_num [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, CentralSpliceAvailable,CentralSplice]
  obtain hs | hs := h1_splice_d2 a b d c ha hab hd2 hc ht hl hr
  · obtain ⟨p,k,hp,hz,hfirst⟩ := neighbor_one hd2 hc (by omega)
    apply rootedFork_of_neighbor hd hm (Or.inl rfl) hp hz hfirst
    simpa only [PathVertexLabel,Nat.add_sub_cancel] using centralSpliceAvailable_path hs
  · obtain ⟨p,k,hp,hz,hfirst⟩ := neighbor_two hd2 hc (by omega) (by omega)
    apply rootedFork_of_neighbor hd hm (Or.inr rfl) hp hz hfirst
    unfold PathVertexLabel
    rw [show (d+c-3)/2+1-2=(d+c-3)/2-1 by omega]
    exact centralSpliceAvailable_path hs

end Bounty


/- Supporting module: SmallShortPaths -/

namespace Bounty

/-- A finite choice among the three fixed base labels suffices. -/
def SmallShortAlpha (d c : ℕ) : Prop :=
  ∃ p k r, r≤2 ∧ NatAlphaPath (d+c) p k ∧ p (d-1)=0 ∧
    ((d%2=1 → r≤k ∧ p 0=k-r) ∧ (d%2≠1 → p 0=k+1+r))

private theorem flat_SmallShortPaths_smallShort_1_1 : SmallShortAlpha 1 1 := by
  let p : Fin 2 → ℕ := ![0,1]
  have hp : FiniteAlphaPath 2 p 0 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 0, 0, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_1_2 : SmallShortAlpha 1 2 := by
  let p : Fin 3 → ℕ := ![0,2,1]
  have hp : FiniteAlphaPath 3 p 1 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 1, 1, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_2_1 : SmallShortAlpha 2 1 := by
  let p : Fin 3 → ℕ := ![1,0,2]
  have hp : FiniteAlphaPath 3 p 0 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 0, 0, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_2_2 : SmallShortAlpha 2 2 := by
  let p : Fin 4 → ℕ := ![3,0,2,1]
  have hp : FiniteAlphaPath 4 p 1 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 1, 1, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_2_3 : SmallShortAlpha 2 3 := by
  let p : Fin 5 → ℕ := ![4,0,3,1,2]
  have hp : FiniteAlphaPath 5 p 1 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 1, 2, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_2_4 : SmallShortAlpha 2 4 := by
  let p : Fin 6 → ℕ := ![4,0,5,2,3,1]
  have hp : FiniteAlphaPath 6 p 2 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 2, 1, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_3_1 : SmallShortAlpha 3 1 := by
  let p : Fin 4 → ℕ := ![1,2,0,3]
  have hp : FiniteAlphaPath 4 p 1 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 1, 0, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_3_3 : SmallShortAlpha 3 3 := by
  let p : Fin 6 → ℕ := ![1,5,0,3,2,4]
  have hp : FiniteAlphaPath 6 p 2 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 2, 1, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_3_4 : SmallShortAlpha 3 4 := by
  let p : Fin 7 → ℕ := ![2,6,0,5,3,4,1]
  have hp : FiniteAlphaPath 7 p 3 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 3, 1, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_3_5 : SmallShortAlpha 3 5 := by
  let p : Fin 8 → ℕ := ![1,6,0,7,3,4,2,5]
  have hp : FiniteAlphaPath 8 p 3 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 3, 2, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_3_6 : SmallShortAlpha 3 6 := by
  let p : Fin 9 → ℕ := ![3,7,0,8,2,5,4,6,1]
  have hp : FiniteAlphaPath 9 p 4 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 4, 1, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_4_1 : SmallShortAlpha 4 1 := by
  let p : Fin 5 → ℕ := ![2,1,3,0,4]
  have hp : FiniteAlphaPath 5 p 1 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 1, 0, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_4_2 : SmallShortAlpha 4 2 := by
  let p : Fin 6 → ℕ := ![4,2,3,0,5,1]
  have hp : FiniteAlphaPath 6 p 2 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 2, 1, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_4_3 : SmallShortAlpha 4 3 := by
  let p : Fin 7 → ℕ := ![4,2,3,0,6,1,5]
  have hp : FiniteAlphaPath 7 p 2 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 2, 1, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_4_4 : SmallShortAlpha 4 4 := by
  let p : Fin 8 → ℕ := ![6,1,7,0,4,3,5,2]
  have hp : FiniteAlphaPath 8 p 3 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 3, 2, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_4_5 : SmallShortAlpha 4 5 := by
  let p : Fin 9 → ℕ := ![5,1,8,0,6,3,4,2,7]
  have hp : FiniteAlphaPath 9 p 3 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 3, 1, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_4_6 : SmallShortAlpha 4 6 := by
  let p : Fin 10 → ℕ := ![6,2,9,0,8,3,5,4,7,1]
  have hp : FiniteAlphaPath 10 p 4 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 4, 1, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_4_7 : SmallShortAlpha 4 7 := by
  let p : Fin 11 → ℕ := ![7,3,9,0,10,2,5,4,6,1,8]
  have hp : FiniteAlphaPath 11 p 4 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 4, 2, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_4_8 : SmallShortAlpha 4 8 := by
  let p : Fin 12 → ℕ := ![7,3,10,0,11,2,8,5,6,4,9,1]
  have hp : FiniteAlphaPath 12 p 5 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 5, 1, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_5_1 : SmallShortAlpha 5 1 := by
  let p : Fin 6 → ℕ := ![2,3,1,4,0,5]
  have hp : FiniteAlphaPath 6 p 2 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 2, 0, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_5_2 : SmallShortAlpha 5 2 := by
  let p : Fin 7 → ℕ := ![2,5,3,4,0,6,1]
  have hp : FiniteAlphaPath 7 p 3 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 3, 1, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_5_3 : SmallShortAlpha 5 3 := by
  let p : Fin 8 → ℕ := ![2,5,3,4,0,7,1,6]
  have hp : FiniteAlphaPath 8 p 3 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 3, 1, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_5_4 : SmallShortAlpha 5 4 := by
  let p : Fin 9 → ℕ := ![3,5,4,7,0,8,2,6,1]
  have hp : FiniteAlphaPath 9 p 4 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 4, 1, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_5_5 : SmallShortAlpha 5 5 := by
  let p : Fin 10 → ℕ := ![3,5,4,7,0,9,1,6,2,8]
  have hp : FiniteAlphaPath 10 p 4 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 4, 1, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_5_6 : SmallShortAlpha 5 6 := by
  let p : Fin 11 → ℕ := ![3,6,5,7,0,10,1,9,4,8,2]
  have hp : FiniteAlphaPath 11 p 5 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 5, 2, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_5_7 : SmallShortAlpha 5 7 := by
  let p : Fin 12 → ℕ := ![4,8,1,11,0,9,3,6,5,7,2,10]
  have hp : FiniteAlphaPath 12 p 5 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 5, 1, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_5_8 : SmallShortAlpha 5 8 := by
  let p : Fin 13 → ℕ := ![5,9,2,12,0,11,3,8,6,7,4,10,1]
  have hp : FiniteAlphaPath 13 p 6 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 6, 1, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_5_9 : SmallShortAlpha 5 9 := by
  let p : Fin 14 → ℕ := ![4,10,3,13,0,12,1,9,5,8,6,7,2,11]
  have hp : FiniteAlphaPath 14 p 6 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 6, 2, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_5_10 : SmallShortAlpha 5 10 := by
  let p : Fin 15 → ℕ := ![6,10,3,13,0,14,2,11,5,8,7,9,4,12,1]
  have hp : FiniteAlphaPath 15 p 7 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 7, 1, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_6_1 : SmallShortAlpha 6 1 := by
  let p : Fin 7 → ℕ := ![3,2,4,1,5,0,6]
  have hp : FiniteAlphaPath 7 p 2 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 2, 0, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_6_2 : SmallShortAlpha 6 2 := by
  let p : Fin 8 → ℕ := ![5,2,4,3,7,0,6,1]
  have hp : FiniteAlphaPath 8 p 3 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 3, 1, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_6_3 : SmallShortAlpha 6 3 := by
  let p : Fin 9 → ℕ := ![5,3,4,1,8,0,6,2,7]
  have hp : FiniteAlphaPath 9 p 3 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 3, 1, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_6_4 : SmallShortAlpha 6 4 := by
  let p : Fin 10 → ℕ := ![6,4,5,2,9,0,8,3,7,1]
  have hp : FiniteAlphaPath 10 p 4 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 4, 1, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_6_5 : SmallShortAlpha 6 5 := by
  let p : Fin 11 → ℕ := ![6,3,5,4,8,0,10,1,7,2,9]
  have hp : FiniteAlphaPath 11 p 4 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 4, 1, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_6_6 : SmallShortAlpha 6 6 := by
  let p : Fin 12 → ℕ := ![7,5,6,3,10,0,11,2,8,4,9,1]
  have hp : FiniteAlphaPath 12 p 5 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 5, 1, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_6_7 : SmallShortAlpha 6 7 := by
  let p : Fin 13 → ℕ := ![7,5,6,3,10,0,12,1,9,4,8,2,11]
  have hp : FiniteAlphaPath 13 p 5 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 5, 1, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_6_8 : SmallShortAlpha 6 8 := by
  let p : Fin 14 → ℕ := ![9,6,7,5,10,0,13,1,12,3,11,4,8,2]
  have hp : FiniteAlphaPath 14 p 6 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 6, 2, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_6_9 : SmallShortAlpha 6 9 := by
  let p : Fin 15 → ℕ := ![8,4,11,1,14,0,12,3,9,6,7,5,10,2,13]
  have hp : FiniteAlphaPath 15 p 6 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 6, 1, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_6_10 : SmallShortAlpha 6 10 := by
  let p : Fin 16 → ℕ := ![9,5,12,2,15,0,14,3,11,6,8,7,10,4,13,1]
  have hp : FiniteAlphaPath 16 p 7 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 7, 1, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_6_11 : SmallShortAlpha 6 11 := by
  let p : Fin 17 → ℕ := ![10,2,15,1,16,0,12,7,8,6,9,5,11,4,13,3,14]
  have hp : FiniteAlphaPath 17 p 7 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 7, 2, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_6_12 : SmallShortAlpha 6 12 := by
  let p : Fin 18 → ℕ := ![10,6,13,3,16,0,17,2,14,5,11,8,9,7,12,4,15,1]
  have hp : FiniteAlphaPath 18 p 8 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 8, 1, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_7_1 : SmallShortAlpha 7 1 := by
  let p : Fin 8 → ℕ := ![3,4,2,5,1,6,0,7]
  have hp : FiniteAlphaPath 8 p 3 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 3, 0, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_7_2 : SmallShortAlpha 7 2 := by
  let p : Fin 9 → ℕ := ![3,5,4,7,2,6,0,8,1]
  have hp : FiniteAlphaPath 9 p 4 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 4, 1, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_7_3 : SmallShortAlpha 7 3 := by
  let p : Fin 10 → ℕ := ![3,5,4,7,2,6,0,9,1,8]
  have hp : FiniteAlphaPath 10 p 4 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 4, 1, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_7_4 : SmallShortAlpha 7 4 := by
  let p : Fin 11 → ℕ := ![4,7,5,6,2,10,0,9,3,8,1]
  have hp : FiniteAlphaPath 11 p 5 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 5, 1, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_7_5 : SmallShortAlpha 7 5 := by
  let p : Fin 12 → ℕ := ![4,6,5,8,1,11,0,9,3,7,2,10]
  have hp : FiniteAlphaPath 12 p 5 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 5, 1, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_7_6 : SmallShortAlpha 7 6 := by
  let p : Fin 13 → ℕ := ![5,8,6,7,3,11,0,12,2,9,4,10,1]
  have hp : FiniteAlphaPath 13 p 6 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 6, 1, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_7_7 : SmallShortAlpha 7 7 := by
  let p : Fin 14 → ℕ := ![5,8,6,7,3,11,0,13,1,10,4,9,2,12]
  have hp : FiniteAlphaPath 14 p 6 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 6, 1, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_7_8 : SmallShortAlpha 7 8 := by
  let p : Fin 15 → ℕ := ![6,8,7,10,3,13,0,14,2,11,5,9,4,12,1]
  have hp : FiniteAlphaPath 15 p 7 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 7, 1, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_7_9 : SmallShortAlpha 7 9 := by
  let p : Fin 16 → ℕ := ![6,8,7,10,3,13,0,15,1,12,4,9,5,11,2,14]
  have hp : FiniteAlphaPath 16 p 7 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 7, 1, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_7_10 : SmallShortAlpha 7 10 := by
  let p : Fin 17 → ℕ := ![6,11,5,14,1,15,0,16,4,12,8,9,7,10,3,13,2]
  have hp : FiniteAlphaPath 17 p 8 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 8, 2, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_7_11 : SmallShortAlpha 7 11 := by
  let p : Fin 18 → ℕ := ![7,11,4,14,1,17,0,15,3,12,6,9,8,10,5,13,2,16]
  have hp : FiniteAlphaPath 18 p 8 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 8, 1, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_7_12 : SmallShortAlpha 7 12 := by
  let p : Fin 19 → ℕ := ![8,12,5,15,2,18,0,17,3,14,6,11,9,10,7,13,4,16,1]
  have hp : FiniteAlphaPath 19 p 9 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 9, 1, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_7_13 : SmallShortAlpha 7 13 := by
  let p : Fin 20 → ℕ := ![7,13,6,14,1,18,0,19,3,12,8,11,9,10,5,15,4,16,2,17]
  have hp : FiniteAlphaPath 20 p 9 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 9, 2, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_7_14 : SmallShortAlpha 7 14 := by
  let p : Fin 21 → ℕ := ![9,13,6,16,3,19,0,20,2,17,5,14,8,11,10,12,7,15,4,18,1]
  have hp : FiniteAlphaPath 21 p 10 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 10, 1, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_8_1 : SmallShortAlpha 8 1 := by
  let p : Fin 9 → ℕ := ![4,3,5,2,6,1,7,0,8]
  have hp : FiniteAlphaPath 9 p 3 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 3, 0, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_8_2 : SmallShortAlpha 8 2 := by
  let p : Fin 10 → ℕ := ![6,4,5,2,7,3,9,0,8,1]
  have hp : FiniteAlphaPath 10 p 4 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 4, 1, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_8_3 : SmallShortAlpha 8 3 := by
  let p : Fin 11 → ℕ := ![6,3,5,4,8,2,7,0,10,1,9]
  have hp : FiniteAlphaPath 11 p 4 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 4, 1, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_8_4 : SmallShortAlpha 8 4 := by
  let p : Fin 12 → ℕ := ![7,5,6,3,8,4,10,0,11,2,9,1]
  have hp : FiniteAlphaPath 12 p 5 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 5, 1, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_8_5 : SmallShortAlpha 8 5 := by
  let p : Fin 13 → ℕ := ![7,5,6,3,8,4,10,0,12,1,9,2,11]
  have hp : FiniteAlphaPath 13 p 5 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 5, 1, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_8_6 : SmallShortAlpha 8 6 := by
  let p : Fin 14 → ℕ := ![8,5,7,6,10,2,13,0,12,3,9,4,11,1]
  have hp : FiniteAlphaPath 14 p 6 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 6, 1, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_8_7 : SmallShortAlpha 8 7 := by
  let p : Fin 15 → ℕ := ![8,6,7,4,11,1,14,0,12,3,9,5,10,2,13]
  have hp : FiniteAlphaPath 15 p 6 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 6, 1, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_8_8 : SmallShortAlpha 8 8 := by
  let p : Fin 16 → ℕ := ![9,7,8,5,12,2,15,0,14,3,11,6,10,4,13,1]
  have hp : FiniteAlphaPath 16 p 7 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 7, 1, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_8_9 : SmallShortAlpha 8 9 := by
  let p : Fin 17 → ℕ := ![9,6,8,7,11,3,14,0,16,1,13,4,10,5,12,2,15]
  have hp : FiniteAlphaPath 17 p 7 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 7, 1, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_8_10 : SmallShortAlpha 8 10 := by
  let p : Fin 18 → ℕ := ![10,8,9,6,13,3,16,0,17,2,14,5,11,7,12,4,15,1]
  have hp : FiniteAlphaPath 18 p 8 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 8, 1, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_8_11 : SmallShortAlpha 8 11 := by
  let p : Fin 19 → ℕ := ![10,8,9,6,13,3,16,0,18,1,15,4,12,7,11,5,14,2,17]
  have hp : FiniteAlphaPath 19 p 8 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 8, 1, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_8_12 : SmallShortAlpha 8 12 := by
  let p : Fin 20 → ℕ := ![12,9,10,8,13,4,16,0,19,1,18,3,17,6,14,7,11,5,15,2]
  have hp : FiniteAlphaPath 20 p 9 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 9, 2, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_8_13 : SmallShortAlpha 8 13 := by
  let p : Fin 21 → ℕ := ![11,7,14,4,17,1,20,0,18,3,15,6,12,9,10,8,13,5,16,2,19]
  have hp : FiniteAlphaPath 21 p 9 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 9, 1, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_8_14 : SmallShortAlpha 8 14 := by
  let p : Fin 22 → ℕ := ![12,8,15,5,18,2,21,0,20,3,17,6,14,9,11,10,13,7,16,4,19,1]
  have hp : FiniteAlphaPath 22 p 10 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 10, 1, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_8_15 : SmallShortAlpha 8 15 := by
  let p : Fin 23 → ℕ := ![13,10,11,9,15,3,22,0,21,1,17,8,12,7,14,6,16,5,18,4,19,2,20]
  have hp : FiniteAlphaPath 23 p 10 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 10, 2, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_8_16 : SmallShortAlpha 8 16 := by
  let p : Fin 24 → ℕ := ![13,9,16,6,19,3,22,0,23,2,20,5,17,8,14,11,12,10,15,7,18,4,21,1]
  have hp : FiniteAlphaPath 24 p 11 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 11, 1, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_9_1 : SmallShortAlpha 9 1 := by
  let p : Fin 10 → ℕ := ![4,5,3,6,2,7,1,8,0,9]
  have hp : FiniteAlphaPath 10 p 4 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 4, 0, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_9_2 : SmallShortAlpha 9 2 := by
  let p : Fin 11 → ℕ := ![4,7,5,6,2,8,3,10,0,9,1]
  have hp : FiniteAlphaPath 11 p 5 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 5, 1, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_9_3 : SmallShortAlpha 9 3 := by
  let p : Fin 12 → ℕ := ![4,7,5,6,2,9,3,8,0,11,1,10]
  have hp : FiniteAlphaPath 12 p 5 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 5, 1, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_9_4 : SmallShortAlpha 9 4 := by
  let p : Fin 13 → ℕ := ![5,9,3,8,6,7,4,11,0,12,2,10,1]
  have hp : FiniteAlphaPath 13 p 6 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 6, 1, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_9_5 : SmallShortAlpha 9 5 := by
  let p : Fin 14 → ℕ := ![5,8,6,7,3,9,4,11,0,13,1,10,2,12]
  have hp : FiniteAlphaPath 14 p 6 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 6, 1, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_9_6 : SmallShortAlpha 9 6 := by
  let p : Fin 15 → ℕ := ![6,8,7,10,5,9,3,13,0,14,2,11,4,12,1]
  have hp : FiniteAlphaPath 15 p 7 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 7, 1, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_9_7 : SmallShortAlpha 9 7 := by
  let p : Fin 16 → ℕ := ![6,10,5,8,7,9,3,13,0,15,1,12,4,11,2,14]
  have hp : FiniteAlphaPath 16 p 7 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 7, 1, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_9_8 : SmallShortAlpha 9 8 := by
  let p : Fin 17 → ℕ := ![7,10,8,9,5,13,2,16,0,15,3,12,6,11,4,14,1]
  have hp : FiniteAlphaPath 17 p 8 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 8, 1, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_9_9 : SmallShortAlpha 9 9 := by
  let p : Fin 18 → ℕ := ![7,9,8,11,4,14,1,17,0,15,3,12,6,10,5,13,2,16]
  have hp : FiniteAlphaPath 18 p 8 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 8, 1, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_9_10 : SmallShortAlpha 9 10 := by
  let p : Fin 19 → ℕ := ![8,11,9,10,6,14,3,17,0,18,2,15,5,12,7,13,4,16,1]
  have hp : FiniteAlphaPath 19 p 9 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 9, 1, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_9_11 : SmallShortAlpha 9 11 := by
  let p : Fin 20 → ℕ := ![8,11,9,10,6,14,3,17,0,19,1,16,4,13,7,12,5,15,2,18]
  have hp : FiniteAlphaPath 20 p 9 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 9, 1, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_9_12 : SmallShortAlpha 9 12 := by
  let p : Fin 21 → ℕ := ![9,11,10,13,6,16,3,19,0,20,2,17,5,14,8,12,7,15,4,18,1]
  have hp : FiniteAlphaPath 21 p 10 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 10, 1, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_9_13 : SmallShortAlpha 9 13 := by
  let p : Fin 22 → ℕ := ![9,11,10,13,6,16,3,19,0,21,1,18,4,15,7,12,8,14,5,17,2,20]
  have hp : FiniteAlphaPath 22 p 10 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 10, 1, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_9_14 : SmallShortAlpha 9 14 := by
  let p : Fin 23 → ℕ := ![9,14,6,20,3,21,1,22,0,19,4,15,8,12,11,13,10,16,7,17,5,18,2]
  have hp : FiniteAlphaPath 23 p 11 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 11, 2, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_9_15 : SmallShortAlpha 9 15 := by
  let p : Fin 24 → ℕ := ![10,14,7,17,4,20,1,23,0,21,3,18,6,15,9,12,11,13,8,16,5,19,2,22]
  have hp : FiniteAlphaPath 24 p 11 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 11, 1, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_9_16 : SmallShortAlpha 9 16 := by
  let p : Fin 25 → ℕ := ![11,15,8,18,5,21,2,24,0,23,3,20,6,17,9,14,12,13,10,16,7,19,4,22,1]
  have hp : FiniteAlphaPath 25 p 12 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 12, 1, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_9_17 : SmallShortAlpha 9 17 := by
  let p : Fin 26 → ℕ := ![10,15,8,16,7,18,3,25,0,24,1,22,2,21,4,20,6,19,9,13,12,14,11,17,5,23]
  have hp : FiniteAlphaPath 26 p 12 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 12, 2, by decide, hp.toNat, rfl, ?_⟩
  decide

private theorem flat_SmallShortPaths_smallShort_9_18 : SmallShortAlpha 9 18 := by
  let p : Fin 27 → ℕ := ![12,16,9,19,6,22,3,25,0,26,2,23,5,20,8,17,11,14,13,15,10,18,7,21,4,24,1]
  have hp : FiniteAlphaPath 27 p 13 := by unfold FiniteAlphaPath Function.Injective; decide
  refine ⟨finitePathLabel p, 13, 1, by decide, hp.toNat, rfl, ?_⟩
  decide

theorem small_short_alpha_path {d c : ℕ} (hd : 1≤d) (hd9 : d≤9)
    (hc : 1≤c) (hcs : c≤2*d) (he : d≠3 ∨ c≠2) :
    ∃ p k r, r≤2 ∧ NatAlphaPath (d+c) p k ∧ p (d-1)=0 ∧
      ((d%2=1 → r≤k ∧ p 0=k-r) ∧ (d%2≠1 → p 0=k+1+r)) := by
  change SmallShortAlpha d c
  interval_cases d
  · have hc' : c=1 ∨ c=2 := by omega
    rcases hc' with rfl | rfl
    · exact flat_SmallShortPaths_smallShort_1_1
    · exact flat_SmallShortPaths_smallShort_1_2
  · have hc' : c=1 ∨ c=2 ∨ c=3 ∨ c=4 := by omega
    rcases hc' with rfl | rfl | rfl | rfl
    · exact flat_SmallShortPaths_smallShort_2_1
    · exact flat_SmallShortPaths_smallShort_2_2
    · exact flat_SmallShortPaths_smallShort_2_3
    · exact flat_SmallShortPaths_smallShort_2_4
  · have hc' : c=1 ∨ c=3 ∨ c=4 ∨ c=5 ∨ c=6 := by omega
    rcases hc' with rfl | rfl | rfl | rfl | rfl
    · exact flat_SmallShortPaths_smallShort_3_1
    · exact flat_SmallShortPaths_smallShort_3_3
    · exact flat_SmallShortPaths_smallShort_3_4
    · exact flat_SmallShortPaths_smallShort_3_5
    · exact flat_SmallShortPaths_smallShort_3_6
  · have hc' : c=1 ∨ c=2 ∨ c=3 ∨ c=4 ∨ c=5 ∨ c=6 ∨ c=7 ∨ c=8 := by omega
    rcases hc' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact flat_SmallShortPaths_smallShort_4_1
    · exact flat_SmallShortPaths_smallShort_4_2
    · exact flat_SmallShortPaths_smallShort_4_3
    · exact flat_SmallShortPaths_smallShort_4_4
    · exact flat_SmallShortPaths_smallShort_4_5
    · exact flat_SmallShortPaths_smallShort_4_6
    · exact flat_SmallShortPaths_smallShort_4_7
    · exact flat_SmallShortPaths_smallShort_4_8
  · have hc' : c=1 ∨ c=2 ∨ c=3 ∨ c=4 ∨ c=5 ∨ c=6 ∨ c=7 ∨ c=8 ∨ c=9 ∨ c=10 := by omega
    rcases hc' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact flat_SmallShortPaths_smallShort_5_1
    · exact flat_SmallShortPaths_smallShort_5_2
    · exact flat_SmallShortPaths_smallShort_5_3
    · exact flat_SmallShortPaths_smallShort_5_4
    · exact flat_SmallShortPaths_smallShort_5_5
    · exact flat_SmallShortPaths_smallShort_5_6
    · exact flat_SmallShortPaths_smallShort_5_7
    · exact flat_SmallShortPaths_smallShort_5_8
    · exact flat_SmallShortPaths_smallShort_5_9
    · exact flat_SmallShortPaths_smallShort_5_10
  · have hc' : c=1 ∨ c=2 ∨ c=3 ∨ c=4 ∨ c=5 ∨ c=6 ∨ c=7 ∨ c=8 ∨ c=9 ∨ c=10 ∨ c=11 ∨ c=12 := by omega
    rcases hc' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact flat_SmallShortPaths_smallShort_6_1
    · exact flat_SmallShortPaths_smallShort_6_2
    · exact flat_SmallShortPaths_smallShort_6_3
    · exact flat_SmallShortPaths_smallShort_6_4
    · exact flat_SmallShortPaths_smallShort_6_5
    · exact flat_SmallShortPaths_smallShort_6_6
    · exact flat_SmallShortPaths_smallShort_6_7
    · exact flat_SmallShortPaths_smallShort_6_8
    · exact flat_SmallShortPaths_smallShort_6_9
    · exact flat_SmallShortPaths_smallShort_6_10
    · exact flat_SmallShortPaths_smallShort_6_11
    · exact flat_SmallShortPaths_smallShort_6_12
  · have hc' : c=1 ∨ c=2 ∨ c=3 ∨ c=4 ∨ c=5 ∨ c=6 ∨ c=7 ∨ c=8 ∨ c=9 ∨ c=10 ∨ c=11 ∨ c=12 ∨ c=13 ∨ c=14 := by omega
    rcases hc' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact flat_SmallShortPaths_smallShort_7_1
    · exact flat_SmallShortPaths_smallShort_7_2
    · exact flat_SmallShortPaths_smallShort_7_3
    · exact flat_SmallShortPaths_smallShort_7_4
    · exact flat_SmallShortPaths_smallShort_7_5
    · exact flat_SmallShortPaths_smallShort_7_6
    · exact flat_SmallShortPaths_smallShort_7_7
    · exact flat_SmallShortPaths_smallShort_7_8
    · exact flat_SmallShortPaths_smallShort_7_9
    · exact flat_SmallShortPaths_smallShort_7_10
    · exact flat_SmallShortPaths_smallShort_7_11
    · exact flat_SmallShortPaths_smallShort_7_12
    · exact flat_SmallShortPaths_smallShort_7_13
    · exact flat_SmallShortPaths_smallShort_7_14
  · have hc' : c=1 ∨ c=2 ∨ c=3 ∨ c=4 ∨ c=5 ∨ c=6 ∨ c=7 ∨ c=8 ∨ c=9 ∨ c=10 ∨ c=11 ∨ c=12 ∨ c=13 ∨ c=14 ∨ c=15 ∨ c=16 := by omega
    rcases hc' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact flat_SmallShortPaths_smallShort_8_1
    · exact flat_SmallShortPaths_smallShort_8_2
    · exact flat_SmallShortPaths_smallShort_8_3
    · exact flat_SmallShortPaths_smallShort_8_4
    · exact flat_SmallShortPaths_smallShort_8_5
    · exact flat_SmallShortPaths_smallShort_8_6
    · exact flat_SmallShortPaths_smallShort_8_7
    · exact flat_SmallShortPaths_smallShort_8_8
    · exact flat_SmallShortPaths_smallShort_8_9
    · exact flat_SmallShortPaths_smallShort_8_10
    · exact flat_SmallShortPaths_smallShort_8_11
    · exact flat_SmallShortPaths_smallShort_8_12
    · exact flat_SmallShortPaths_smallShort_8_13
    · exact flat_SmallShortPaths_smallShort_8_14
    · exact flat_SmallShortPaths_smallShort_8_15
    · exact flat_SmallShortPaths_smallShort_8_16
  · have hc' : c=1 ∨ c=2 ∨ c=3 ∨ c=4 ∨ c=5 ∨ c=6 ∨ c=7 ∨ c=8 ∨ c=9 ∨ c=10 ∨ c=11 ∨ c=12 ∨ c=13 ∨ c=14 ∨ c=15 ∨ c=16 ∨ c=17 ∨ c=18 := by omega
    rcases hc' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact flat_SmallShortPaths_smallShort_9_1
    · exact flat_SmallShortPaths_smallShort_9_2
    · exact flat_SmallShortPaths_smallShort_9_3
    · exact flat_SmallShortPaths_smallShort_9_4
    · exact flat_SmallShortPaths_smallShort_9_5
    · exact flat_SmallShortPaths_smallShort_9_6
    · exact flat_SmallShortPaths_smallShort_9_7
    · exact flat_SmallShortPaths_smallShort_9_8
    · exact flat_SmallShortPaths_smallShort_9_9
    · exact flat_SmallShortPaths_smallShort_9_10
    · exact flat_SmallShortPaths_smallShort_9_11
    · exact flat_SmallShortPaths_smallShort_9_12
    · exact flat_SmallShortPaths_smallShort_9_13
    · exact flat_SmallShortPaths_smallShort_9_14
    · exact flat_SmallShortPaths_smallShort_9_15
    · exact flat_SmallShortPaths_smallShort_9_16
    · exact flat_SmallShortPaths_smallShort_9_17
    · exact flat_SmallShortPaths_smallShort_9_18

end Bounty


/- Supporting module: ForkSmallGraft -/


namespace Bounty

theorem pathVertexLabel_small {a b r : ℕ} (hq : 2 < a+b)
    (he : a ≠ 2 ∨ b ≠ 2) (hr : r ≤ 2) : PathVertexLabel a b r := by
  interval_cases r
  · exact exists_graceful_path_zero (by omega)
  · exact pathVertexLabel_one hq
  · exact pathVertexLabel_two hq he

theorem rootedFork_of_fixed_offset {a b d c k r : ℕ} {p : ℕ → ℕ}
    (hd : 1 ≤ d) (hq : 2 < a+b) (he : a ≠ 2 ∨ b ≠ 2) (hr : r ≤ 2)
    (hp : NatAlphaPath (d+c) p k) (hz : p (d-1)=0)
    (hlow : d%2=1 → r ≤ k ∧ p 0=k-r)
    (hhigh : d%2≠1 → p 0=k+1+r) : RootedFork a b d c := by
  have hbase := pathVertexLabel_small hq he hr
  by_cases hdo : d%2=1
  · obtain ⟨f,hf,hf0⟩ := hbase.complement
    obtain ⟨hrk,hfirst⟩ := hlow hdo
    apply rootedFork_of_paths hd hf hp.1 (by have := hp.2.1; omega) hp.2.2 hz
    exact graftJoin_low (by omega) (by omega) (by omega)
  · obtain ⟨f,hf,hf0⟩ := hbase
    have hfirst := hhigh hdo
    apply rootedFork_of_paths hd hf hp.1 (by have := hp.2.1; omega) hp.2.2 hz
    exact graftJoin_high (by omega) (by omega)

theorem rootedFork_small_short {a b d c : ℕ} (hd : 1 ≤ d) (hd9 : d ≤ 9)
    (hc : 1 ≤ c) (hcs : c ≤ 2*d) (hex : d ≠ 3 ∨ c ≠ 2)
    (hq : 2 < a+b) (he : a ≠ 2 ∨ b ≠ 2) : RootedFork a b d c := by
  obtain ⟨p,k,r,hr,hp,hz,hlow,hhigh⟩ := small_short_alpha_path hd hd9 hc hcs hex
  exact rootedFork_of_fixed_offset hd hq he hr hp hz hlow hhigh

end Bounty


/- Supporting module: StarExtension -/

namespace Bounty

def starParent (N root : ℕ) (parent : ℕ → ℕ) (j : ℕ) : ℕ :=
  if j ≤ N then parent j else root

def starLabels (N : ℕ) (f : ℕ → ℕ) (j : ℕ) : ℕ :=
  if j ≤ N then f j else j

theorem starParent_lt {N root : ℕ} {parent : ℕ → ℕ}
    (hr : root ≤ N) (hp : ∀ j, 0 < j → j ≤ N → parent j < j)
    (j : ℕ) (hj : 0 < j) : starParent N root parent j < j := by
  unfold starParent
  split_ifs with h
  · exact hp j hj h
  · omega

theorem NatParentCertificate.star {N k root : ℕ} {parent f : ℕ → ℕ}
    (hr : root ≤ N) (hz : f root = 0)
    (hp : ∀ j, 0 < j → j ≤ N → parent j < j)
    (hf : NatParentCertificate N parent f) :
    NatParentCertificate (N+k) (starParent N root parent) (starLabels N f) := by
  have old (j : ℕ) (hj : j ≤ N) : starLabels N f j = f j := by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, starLabels, hj]
  have fresh (j : ℕ) (hj : N < j) : starLabels N f j = j := by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, starLabels, Nat.not_le.mpr hj]
  have oldDiff (j : ℕ) (hj : 0 < j) (hjN : j ≤ N) :
      Nat.dist (starLabels N f (starParent N root parent j)) (starLabels N f j) =
      Nat.dist (f (parent j)) (f j) := by
    have hpar : parent j ≤ N := by have := hp j hj hjN; omega
    simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, starParent, hjN, old j hjN, old (parent j) hpar]
  have freshDiff (j : ℕ) (hj : N < j) :
      Nat.dist (starLabels N f (starParent N root parent j)) (starLabels N f j) = j := by
    simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, starParent, Nat.not_le.mpr hj, fresh j hj, old root hr, hz, Nat.dist]
  have oldBound (j : ℕ) (hj : 0 < j) (hjN : j ≤ N) : Nat.dist (f (parent j)) (f j) ≤ N := by
    have := hf.2.1 j hjN
    have := hf.2.1 (parent j) (by have := hp j hj hjN; omega)
    unfold Nat.dist
    omega
  refine ⟨?_, ?_, ?_⟩
  · intro i j hi hj heq
    by_cases hiN : i ≤ N <;> by_cases hjN : j ≤ N
    · rw [old i hiN, old j hjN] at heq
      exact hf.1 i j hiN hjN heq
    · rw [old i hiN, fresh j (by omega)] at heq
      have := hf.2.1 i hiN
      omega
    · rw [fresh i (by omega), old j hjN] at heq
      have := hf.2.1 j hjN
      omega
    · simpa only [fresh i (by omega), fresh j (by omega)] using heq
  · intro i hi
    by_cases hiN : i ≤ N
    · rw [old i hiN]
      exact (hf.2.1 i hiN).trans (Nat.le_add_right _ _)
    · rw [fresh i (by omega)]
      exact hi
  · intro i j hi hiN hj hjN heq
    by_cases hi0 : i ≤ N <;> by_cases hj0 : j ≤ N
    · rw [oldDiff i hi hi0, oldDiff j hj hj0] at heq
      exact hf.2.2 i j hi hi0 hj hj0 heq
    · rw [oldDiff i hi hi0, freshDiff j (by omega)] at heq
      have := oldBound i hi hi0
      omega
    · rw [freshDiff i (by omega), oldDiff j hj hj0] at heq
      have := oldBound j hj hj0
      omega
    · simpa only [freshDiff i (by omega), freshDiff j (by omega)] using heq

/-- Attaching a nonempty star at the zero-labeled root produces a new zero-labeled
root at its last leaf, allowing arbitrary caterpillar backbones to be grown. -/
theorem NatParentCertificate.star_zero {N k root : ℕ} {parent f : ℕ → ℕ}
    (hk : 0 < k) (hr : root ≤ N) (hz : f root = 0)
    (hp : ∀ j, 0 < j → j ≤ N → parent j < j)
    (hf : NatParentCertificate N parent f) :
    NatParentCertificate (N+k) (starParent N root parent)
      (fun j => N+k-starLabels N f j) ∧
    (N+k-starLabels N f (N+k) = 0) := by
  refine ⟨(hf.star hr hz hp).complement (fun j hj _ => starParent_lt hr hp j hj), ?_⟩
  simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, starLabels, show ¬N+k ≤ N by omega]

end Bounty


/- Supporting module: ForkStem -/



namespace Bounty

theorem NatParentCertificate.congrParent {N : ℕ} {parent parent' f : ℕ → ℕ}
    (hf : NatParentCertificate N parent f)
    (he : ∀ j, 0 < j → j ≤ N → parent' j=parent j) : NatParentCertificate N parent' f := by
  refine ⟨hf.1,hf.2.1,?_⟩
  intro i j hi hib hj hjb hh
  rw [he i hi hib,he j hj hjb] at hh
  exact hf.2.2 i j hi hib hj hjb hh

theorem NatParentAlpha.congrParent {N k : ℕ} {parent parent' f : ℕ → ℕ}
    (ha : NatParentAlpha N parent f k)
    (he : ∀ j, 0 < j → j ≤ N → parent' j=parent j) : NatParentAlpha N parent' f k := by
  intro j hj hjb
  rw [he j hj hjb]
  exact ha j hj hjb

theorem NatParentCertificate.alphaZeroLeaf {N root k : ℕ} {parent f : ℕ → ℕ}
    (hf : NatParentCertificate N parent f) (ha : NatParentAlpha N parent f k)
    (hpar : ∀ j, 0 < j → j ≤ N → parent j < j) (hr : root ≤ N)
    (hz : f root=0) (hk : k ≤ N) :
    ∃ g, NatParentCertificate (N+1) (graftParent N root parent) g ∧
      NatParentAlpha (N+1) (graftParent N root parent) g (N-k) ∧ g (N+1)=0 := by
  obtain ⟨hg,hg0⟩ := hf.star_zero (k := 1) (by omega) hr hz hpar
  have hparent (j : ℕ) (_hj : 0 < j) (hjb : j ≤ N+1) :
      graftParent N root parent j=starParent N root parent j := by
    unfold graftParent starParent
    split_ifs <;> omega
  refine ⟨_,hg.congrParent hparent,?_,hg0⟩
  intro j hj hjb
  rw [hparent j hj hjb]
  by_cases hjN : j ≤ N
  · have hpj := hpar j hj hjN
    have hbp := hf.2.1 (parent j) (by omega)
    have hbj := hf.2.1 j hjN
    have hjpN : parent j ≤ N := by omega
    simp only [starParent, ite_eq_left hjN, starLabels, ite_eq_left hjpN]
    rcases ha j hj hjN with h | h
    · right; omega
    · left; omega
  · have he : j=N+1 := by omega
    subst j
    simp only [starParent, ite_eq_right hjN, starLabels, ite_eq_left hr, hz, Nat.sub_zero,
      Nat.sub_self]
    right
    omega

def forkStemCut (q k d : ℕ) : ℕ := if d%2=0 then k+d/2 else q-k+d/2
def forkStemTip (a b d : ℕ) : ℕ := if d=0 then a else a+b+d

theorem forkParent_lt (a b j : ℕ) (hj : 0 < j) : forkParent a b j < j := by
  unfold forkParent graftParent
  split_ifs <;> (try simp only [Nat.pred_eq_sub_one]) <;> omega

theorem forkStemCut_succ {q k d : ℕ} (hk : k ≤ q) :
    q+d-forkStemCut q k d=forkStemCut q k (d+1) := by
  unfold forkStemCut
  split_ifs <;> omega

theorem forkStem_alpha {a b k : ℕ} {f : ℕ → ℕ}
    (hf : NatAlphaPath (a+b+1) f k) (hz : f a=0) (d : ℕ) :
    ∃ g, NatParentCertificate (a+b+d) (forkParent a b) g ∧
      NatParentAlpha (a+b+d) (forkParent a b) g (forkStemCut (a+b) k d) ∧
      g (forkStemTip a b d)=0 := by
  have hk : k ≤ a+b := by have := hf.2.1; omega
  induction d with
  | zero =>
    have hpar (j : ℕ) (_hj : 0 < j) (hjb : j ≤ a+b) : forkParent a b j=Nat.pred j := by
      simp only [forkParent,graftParent,ite_eq_left hjb]
    refine ⟨f,?_,?_,?_⟩
    · simpa only [Nat.add_zero] using hf.1.parentCertificate.congrParent hpar
    · intro j hj hjb
      simp only [Nat.add_zero] at hjb
      simpa only [hpar j hj hjb, Nat.pred_eq_sub_one, forkStemCut, Nat.zero_mod,
        ite_true, Nat.zero_div, Nat.add_zero] using hf.2.2 j hj (by omega)
    · simpa only [forkStemTip,ite_true] using hz
  | succ d ih =>
    obtain ⟨g,hg,hga,hg0⟩ := ih
    have htip : forkStemTip a b d ≤ a+b+d := by unfold forkStemTip; split_ifs <;> omega
    have hk' : forkStemCut (a+b) k d ≤ a+b+d := by unfold forkStemCut; split_ifs <;> omega
    obtain ⟨g',hg',hga',hg0'⟩ := hg.alphaZeroLeaf hga
      (fun j hj _ => forkParent_lt a b j hj) htip hg0 hk'
    have hpar (j : ℕ) (hj : 0 < j) (hjb : j ≤ a+b+d+1) :
        forkParent a b j=graftParent (a+b+d) (forkStemTip a b d) (forkParent a b) j := by
      by_cases hh : j ≤ a+b+d
      · simp only [graftParent,ite_eq_left hh]
      · have he : j=a+b+d+1 := by omega
        subst j
        by_cases hd : d=0
        · subst d
          simp only [Nat.add_zero, forkStemTip, ite_true, forkParent, graftParent,
            ite_eq_right (show ¬a+b+1 ≤ a+b by omega), ite_true]
        · have hn : ¬a+b+d+1 ≤ a+b := by omega
          have he : ¬a+b+d+1 = a+b+1 := by omega
          simp only [forkParent, graftParent, ite_eq_right hn, ite_eq_right he,
            ite_eq_right (show ¬a+b+d+1 ≤ a+b+d by omega), ite_true,
            forkStemTip, ite_eq_right hd]
          omega
    refine ⟨g',?_,?_,?_⟩
    · simpa only [Nat.add_assoc] using hg'.congrParent hpar
    · have ht := hga'.congrParent hpar
      rw [forkStemCut_succ hk] at ht
      simpa only [Nat.add_assoc] using ht
    · simpa only [forkStemTip,ite_eq_right (show ¬d+1=0 by omega),Nat.add_assoc] using hg0'

end Bounty


/- Supporting module: ForkReindex -/

namespace Bounty

theorem NatParentCertificate.reindex {N : ℕ} {parent parent' f v e : ℕ → ℕ}
    (hf : NatParentCertificate N parent f)
    (hv : ∀ i j, i ≤ N → j ≤ N → v i=v j → i=j)
    (hvb : ∀ i, i ≤ N → v i ≤ N)
    (he : ∀ i j, 0 < i → i ≤ N → 0 < j → j ≤ N → e i=e j → i=j)
    (heb : ∀ i, 0 < i → i ≤ N → 0 < e i ∧ e i ≤ N)
    (hadj : ∀ i, 0 < i → i ≤ N →
      (v (parent' i)=parent (e i) ∧ v i=e i) ∨
      (v (parent' i)=e i ∧ v i=parent (e i))) :
    NatParentCertificate N parent' (fun i => f (v i)) := by
  have hdist (i : ℕ) (hi : 0 < i) (hib : i ≤ N) :
      Nat.dist (f (v (parent' i))) (f (v i))=Nat.dist (f (parent (e i))) (f (e i)) := by
    rcases hadj i hi hib with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · rw [h1,h2]
    · rw [h1,h2,Nat.dist_comm]
  refine ⟨?_,?_,?_⟩
  · intro i j hi hj hh
    exact hv i j hi hj (hf.1 (v i) (v j) (hvb i hi) (hvb j hj) hh)
  · intro i hi
    exact hf.2.1 (v i) (hvb i hi)
  · intro i j hi hib hj hjb hh
    rw [hdist i hi hib,hdist j hj hjb] at hh
    exact he i j hi hib hj hjb (hf.2.2 (e i) (e j) (heb i hi hib).1
      (heb i hi hib).2 (heb j hj hjb).1 (heb j hj hjb).2 hh)

def forkSwapVertex (q i : ℕ) : ℕ := if i ≤ q then q-i else i
def forkSwapEdge (q i : ℕ) : ℕ := if i ≤ q then q+1-i else i

theorem rootedFork_swap {a b d c : ℕ} (hd : 1 ≤ d) (hf : RootedFork a b d c) : RootedFork b a d c := by
  obtain ⟨f,hf,hf0⟩ := hf
  have hn : a+b+(d+c)=b+a+(d+c) := by omega
  rw [hn] at hf
  let v := forkSwapVertex (a+b)
  let e := forkSwapEdge (a+b)
  have hv : ∀ i j, i ≤ b+a+(d+c) → j ≤ b+a+(d+c) → v i=v j → i=j := by
    intro i j hi hj hh
    dsimp [v,forkSwapVertex] at hh
    split_ifs at hh <;> omega
  have hvb : ∀ i, i ≤ b+a+(d+c) → v i ≤ b+a+(d+c) := by
    intro i hi
    dsimp [v,forkSwapVertex]
    split_ifs <;> omega
  have he : ∀ i j, 0 < i → i ≤ b+a+(d+c) → 0 < j → j ≤ b+a+(d+c) → e i=e j → i=j := by
    intro i j hi hib hj hjb hh
    dsimp [e,forkSwapEdge] at hh
    split_ifs at hh <;> omega
  have heb : ∀ i, 0 < i → i ≤ b+a+(d+c) → 0 < e i ∧ e i ≤ b+a+(d+c) := by
    intro i hi hib
    dsimp [e,forkSwapEdge]
    split_ifs <;> omega
  have hadj : ∀ i, 0 < i → i ≤ b+a+(d+c) →
      (v (forkParent b a i)=forkParent a b (e i) ∧ v i=e i) ∨
      (v (forkParent b a i)=e i ∧ v i=forkParent a b (e i)) := by
    intro i hi hib
    by_cases hiq : i ≤ a+b
    · right
      have hiq' : i ≤ b+a := by omega
      have hip : i-1 ≤ a+b := by omega
      have hep : a+b+1-i ≤ a+b := by omega
      simp only [v,e,forkSwapVertex,forkSwapEdge,forkParent,graftParent,ite_eq_left hiq,
        ite_eq_left hiq',Nat.pred_eq_sub_one,ite_eq_left hip,ite_eq_left hep]
      omega
    · left
      have hiq' : ¬i ≤ b+a := by omega
      simp only [v,e,forkSwapVertex,forkSwapEdge,forkParent,graftParent,ite_eq_right hiq,
        ite_eq_right hiq']
      by_cases hie : i=a+b+1
      · have hie' : i=b+a+1 := by omega
        simp only [ite_eq_left hie,ite_eq_left hie',ite_eq_left (show b ≤ a+b by omega)]
        exact ⟨by omega,trivial⟩
      · have hie' : ¬i=b+a+1 := by omega
        have hip : ¬i-1 ≤ a+b := by omega
        simp only [ite_eq_right hie,ite_eq_right hie',ite_eq_right hip]
        exact ⟨trivial,trivial⟩
  refine ⟨fun i => f (v i),hf.reindex hv hvb he heb hadj,?_⟩
  change f (v (b+a+d))=0
  have hr : v (b+a+d)=a+b+d := by
    dsimp [v,forkSwapVertex]
    rw [ite_eq_right (by omega)]
    omega
  rw [hr]
  exact hf0

end Bounty


/- Supporting module: ForkOuter -/


namespace Bounty

def forkOuterVertex (a b d c i : ℕ) : ℕ :=
  if i < a then b+d+c+a-i else if i ≤ a+b then a+b-i else i-a

def forkOuterEdge (a b d c i : ℕ) : ℕ :=
  if i ≤ a then b+d+c+a+1-i else if i ≤ a+b then a+b+1-i else i-a

theorem rootedFork_of_outer {a b d c : ℕ} (hd : 1 ≤ d)
    {f : ℕ → ℕ} (hf : NatParentCertificate (b+d+c+a) (graftParent (b+d+c) b Nat.pred) f)
    (hz : f (b+d)=0) : RootedFork a b d c := by
  have hn : b+d+c+a=a+b+(d+c) := by omega
  rw [hn] at hf
  let v := forkOuterVertex a b d c
  let e := forkOuterEdge a b d c
  have hv : ∀ i j, i ≤ a+b+(d+c) → j ≤ a+b+(d+c) → v i=v j → i=j := by
    intro i j hi hj hh
    dsimp [v,forkOuterVertex] at hh
    split_ifs at hh <;> omega
  have hvb : ∀ i, i ≤ a+b+(d+c) → v i ≤ a+b+(d+c) := by
    intro i hi
    dsimp [v,forkOuterVertex]
    split_ifs <;> omega
  have he : ∀ i j, 0 < i → i ≤ a+b+(d+c) → 0 < j → j ≤ a+b+(d+c) → e i=e j → i=j := by
    intro i j hi hib hj hjb hh
    dsimp [e,forkOuterEdge] at hh
    split_ifs at hh <;> omega
  have heb : ∀ i, 0 < i → i ≤ a+b+(d+c) → 0 < e i ∧ e i ≤ a+b+(d+c) := by
    intro i hi hib
    dsimp [e,forkOuterEdge]
    split_ifs <;> omega
  have vlo (j : ℕ) (hj : j < a) : v j=b+d+c+a-j := by
    simp only [v,forkOuterVertex,ite_eq_left hj]
  have vmid (j : ℕ) (hj : a ≤ j) (hjb : j ≤ a+b) : v j=a+b-j := by
    simp only [v,forkOuterVertex,ite_eq_right (by omega : ¬j<a),ite_eq_left hjb]
  have vhi (j : ℕ) (hj : a+b < j) : v j=j-a := by
    simp only [v,forkOuterVertex,ite_eq_right (by omega : ¬j<a),
      ite_eq_right (by omega : ¬j ≤ a+b)]
  have hadj : ∀ i, 0 < i → i ≤ a+b+(d+c) →
      (v (forkParent a b i)=graftParent (b+d+c) b Nat.pred (e i) ∧ v i=e i) ∨
      (v (forkParent a b i)=e i ∧ v i=graftParent (b+d+c) b Nat.pred (e i)) := by
    intro i hi hib
    by_cases hia : i ≤ a
    · right
      have heq : e i=b+d+c+a+1-i := by simp only [e,forkOuterEdge,ite_eq_left hia]
      have hp : forkParent a b i=i-1 := by
        simp only [forkParent,graftParent,ite_eq_left (by omega : i ≤ a+b),Nat.pred_eq_sub_one]
      rw [hp,vlo (i-1) (by omega),heq]
      constructor
      · omega
      · by_cases hia' : i=a
        · subst i
          rw [vmid a (by omega) (by omega)]
          have hh : b+d+c+a+1-a=b+d+c+1 := by omega
          rw [hh]
          simp only [graftParent,ite_eq_right (by omega : ¬b+d+c+1 ≤ b+d+c),ite_true]
          omega
        · rw [vlo i (by omega)]
          simp only [graftParent,ite_eq_right (by omega : ¬b+d+c+a+1-i ≤ b+d+c),
            ite_eq_right (by omega : ¬b+d+c+a+1-i=b+d+c+1)]
          omega
    · by_cases hiq : i ≤ a+b
      · right
        have heq : e i=a+b+1-i := by
          simp only [e,forkOuterEdge,ite_eq_right hia,ite_eq_left hiq]
        have hp : forkParent a b i=i-1 := by
          simp only [forkParent,graftParent,ite_eq_left hiq,Nat.pred_eq_sub_one]
        rw [hp,vmid (i-1) (by omega) (by omega),vmid i (by omega) hiq,heq]
        simp only [graftParent,ite_eq_left (by omega : a+b+1-i ≤ b+d+c),Nat.pred_eq_sub_one]
        omega
      · left
        have heq : e i=i-a := by
          simp only [e,forkOuterEdge,ite_eq_right hia,ite_eq_right hiq]
        rw [heq,vhi i (by omega)]
        simp only [graftParent,ite_eq_left (by omega : i-a ≤ b+d+c)]
        constructor
        · by_cases hfirst : i=a+b+1
          · have hp : forkParent a b i=a := by
              simp only [forkParent,graftParent,ite_eq_right hiq,ite_eq_left hfirst]
            rw [hp,vmid a (by omega) (by omega),Nat.pred_eq_sub_one]
            omega
          · have hp : forkParent a b i=i-1 := by
              simp only [forkParent,graftParent,ite_eq_right hiq,ite_eq_right hfirst]
            rw [hp,vhi (i-1) (by omega),Nat.pred_eq_sub_one]
            omega
        · trivial
  refine ⟨fun i => f (v i),hf.reindex hv hvb he heb hadj,?_⟩
  have hr : v (a+b+d)=b+d := by
    dsimp [v,forkOuterVertex]
    split_ifs <;> omega
  change f (v (a+b+d))=0
  rw [hr]
  exact hz

theorem rootedFork_outer {a b d c : ℕ} (hb : 1 ≤ b) (hd : 1 ≤ d) (hc : 1 ≤ c)
    (he : b+d ≠ 2 ∨ c ≠ 2)
    (hlen : (if d%2=0 then (b+d)/2+c/2 else b+d+c-((b+d)/2+c/2)) ≤ a) :
    RootedFork a b d c := by
  obtain ⟨f,k,hf,hf0⟩ := rosa_zero_alpha_path (b+d) c (by omega) hc he
  have hcert := hf.1.parentCertificate
  have halpha : NatParentAlpha (b+d+c) Nat.pred f k := by
    intro j hj hjb
    simpa only [Nat.pred_eq_sub_one] using hf.2.2 j hj (by omega)
  have hk : k=(b+d)/2+c/2 := by
    have hf' : NatAlphaPath (b+d+1+c) f k := by
      convert hf using 1 <;> omega
    have h := hf'.fork_cut (d := b+d+1) (c := c) (by omega)
      (by simpa only [Nat.add_sub_cancel] using hf0)
    omega
  have hkb : k ≤ b+d+c := by have := hf.2.1; omega
  have hcolor : f b ≤ k ↔ d%2=0 := by
    have h1 := hf.low_parity (by omega : b < b+d+c+1)
    have h2 := hf.low_parity (by omega : b+d < b+d+c+1)
    rw [hf0] at h2
    split_ifs at h1 h2 <;> omega
  have hne : 0 < f b := by
    by_contra hn
    have heq : f b=f (b+d) := by omega
    have := hf.1.1 b (b+d) (by omega) (by omega) heq
    omega
  have hlow : f b ≤ k → k+1 ≤ a+f b := by
    intro hl
    have hde := hcolor.mp hl
    rw [ite_eq_left hde] at hlen
    omega
  have hhigh : k < f b → f b ≤ a+k := by
    intro hu
    have hdo : ¬d%2=0 := by intro hh; have := hcolor.mpr hh; omega
    rw [ite_eq_right hdo] at hlen
    have := hf.1.2.1 b (by omega)
    omega
  obtain ⟨g,hg,hg0⟩ := hcert.appendAtRoot halpha
    (fun j hj _ => by simp only [Nat.pred_eq_sub_one]; omega)
    (by omega : b ≤ b+d+c) hkb hlow hhigh
  exact rootedFork_of_outer hd hg (hg0 (b+d) (by omega) hf0)

end Bounty


/- Supporting module: ForkThreeTwo -/


namespace Bounty

theorem threeTwo_1_2 : RootedFork 1 2 3 2 := by
  let labels : List ℕ := [2,5,4,6,1,7,0,8,3]
  let vi : List ℕ := [6,4,0,8,2,1,3,5,7]
  let ei : List ℕ := [0,1,2,0,3,7,4,5,6]
  have h : FastFiniteParentCertificate 8 (forkParent 1 2) labels vi ei := by
    let _ := fastFiniteParentCertificateDecidable 8 (forkParent 1 2) labels vi ei
    decide
  exact rootedFork_of_fast_certificate h (by decide)

theorem threeTwo_2_3 : RootedFork 2 3 3 2 := by
  let labels : List ℕ := [5,2,8,4,6,7,3,10,0,9,1]
  let vi : List ℕ := [8,10,1,6,3,0,4,5,2,9,7]
  let ei : List ℕ := [0,4,3,0,2,5,1,6,9,8,7]
  have h : FastFiniteParentCertificate 10 (forkParent 2 3) labels vi ei := by
    let _ := fastFiniteParentCertificateDecidable 10 (forkParent 2 3) labels vi ei
    decide
  exact rootedFork_of_fast_certificate h (by decide)

theorem threeTwo_3_3 : RootedFork 3 3 3 2 := by
  let labels : List ℕ := [7,5,9,1,8,3,6,2,11,0,10,4]
  let vi : List ℕ := [9,3,7,5,11,1,6,0,4,2,10,8]
  let ei : List ℕ := [0,6,0,5,1,4,10,3,2,7,9,8]
  have h : FastFiniteParentCertificate 11 (forkParent 3 3) labels vi ei := by
    let _ := fastFiniteParentCertificateDecidable 11 (forkParent 3 3) labels vi ei
    decide
  exact rootedFork_of_fast_certificate h (by decide)

theorem threeTwo_4_4 : RootedFork 4 4 3 2 := by
  let labels : List ℕ := [10,2,11,4,9,5,8,6,7,3,13,0,12,1]
  let vi : List ℕ := [11,13,1,9,3,5,7,8,6,4,0,2,12,10]
  let ei : List ℕ := [0,7,6,5,4,3,8,2,0,1,9,12,11,10]
  have h : FastFiniteParentCertificate 13 (forkParent 4 4) labels vi ei := by
    let _ := fastFiniteParentCertificateDecidable 13 (forkParent 4 4) labels vi ei
    decide
  exact rootedFork_of_fast_certificate h (by decide)

theorem rootedFork_three_two {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b)
    (hq : 2 < a+b) (he : a ≠ 2 ∨ b ≠ 2) : RootedFork a b 3 2 := by
  by_cases h1 : b/2+3 ≤ a
  · apply rootedFork_outer (by omega) (by omega) (by omega) (by omega)
    norm_num [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero]
    omega
  by_cases h2 : a/2+3 ≤ b
  · apply rootedFork_swap (by omega)
    apply rootedFork_outer (by omega) (by omega) (by omega) (by omega)
    norm_num [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero]
    omega
  have hb4 : b ≤ 4 := by omega
  have ha4 : a ≤ 4 := by omega
  interval_cases a <;> interval_cases b
  all_goals first
    | omega
    | exact threeTwo_1_2
    | exact threeTwo_2_3
    | exact threeTwo_3_3
    | exact threeTwo_4_4

end Bounty


/- Supporting module: H2Coverage -/

namespace H2Research

def Exceptional (d c : ℕ) : Prop := d = 1 ∧ (c = 1 ∨ c = 4 ∨ c = 5)
def FirstRegion (d c : ℕ) : Prop := c ≤ 2*d-16
def LongRegion (d c : ℕ) : Prop := 2 ≤ d ∧ 2*(d/2)+9 ≤ c
def SmallLongRegion (d c : ℕ) : Prop :=
  d = 1 ∧ ((c%2 = 0 ∧ 10 ≤ c) ∨ (c%2 = 1 ∧ 13 ≤ c))
def FiniteRegion (d c : ℕ) : Prop :=
  (d = 1 ∧ (c = 2 ∨ c = 3 ∨ c = 6 ∨ c = 7 ∨ c = 8 ∨ c = 9 ∨ c = 11)) ∨
  (2 ≤ d ∧ d ≤ 22 ∧ 1 ≤ c ∧ 2*d-16 < c ∧ c ≤ 2*(d/2)+8)

theorem exhaustive (d c : ℕ) (hd : 1 ≤ d) (hc : 1 ≤ c)
    (hne : ¬Exceptional d c) :
    FirstRegion d c ∨ LongRegion d c ∨ SmallLongRegion d c ∨ FiniteRegion d c := by
  unfold Exceptional at hne
  by_cases hfirst : FirstRegion d c
  · exact Or.inl hfirst
  right
  by_cases hlong : LongRegion d c
  · exact Or.inl hlong
  right
  by_cases hsmall : SmallLongRegion d c
  · exact Or.inl hsmall
  right
  unfold FirstRegion at hfirst
  unfold LongRegion at hlong
  unfold SmallLongRegion at hsmall
  unfold FiniteRegion
  by_cases hd1 : d = 1
  · left
    omega
  · right
    omega

/-- Choosing a seed tail with the parity of c guarantees a sufficiently long,
    even extension in the long region. -/
theorem extension_parameters (d c : ℕ) (hc : 2*(d/2)+9 ≤ c) :
    let c₀ := if c%2 = 1 then 1 else 2
    c₀ ≤ c ∧ (c-c₀)%2 = 0 ∧ 2*(d/2+4) ≤ c-c₀ := by
  dsimp
  split_ifs <;> omega

end H2Research


/- Supporting module: Amalgamation -/


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
    exact hf.ordered_edge_unique huv hyx h₁ h₂.symm (by simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, Nat.dist_comm] using heq)
  · apply Or.inr
    have h := hf.ordered_edge_unique hvu hxy h₁.symm h₂ (by simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, Nat.dist_comm] using heq)
    exact ⟨h.2, h.1⟩
  · apply Or.inl
    have h := hf.ordered_edge_unique hvu hyx h₁.symm h₂.symm (by simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, Nat.dist_comm] using heq)
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

private lemma flat_Amalgamation_mapped_pair_eq {n a : ℕ} (i : Fin a → Fin n) {u v x y : Fin a}
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
      simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, hlinkL, hlinkR, shiftAboveCut])
  have hcross (x : Fin a) (y : Fin b) (heq : h (i x) = h (j y)) : i x = j y := by
    rw [hleft, hright] at heq
    obtain ⟨hx, hy⟩ := (shiftAboveCut_eq_translate_iff (hg.2.1 y)).1 heq
    have hx' : x = linkL := hf.1.1 (hx.trans hlinkL.symm)
    have hy' : y = linkR := hg.1 (hy.trans hlinkR.symm)
    simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, hx', hy'] using hlink
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
      exact flat_Amalgamation_mapped_pair_eq i huv huv' (hf.1.edge_unique hxy hxy' (Nat.add_left_cancel heq))
    · rw [hleftDiff x y hxy, hrightDiff] at heq
      exact False.elim ((amalgamation_edge_intervals_disjoint (hf.1.dist_pos hxy)
        (hg.dist_le x' y')) heq)
    · rw [hrightDiff, hleftDiff x' y' hxy'] at heq
      exact False.elim ((amalgamation_edge_intervals_disjoint (hf.1.dist_pos hxy')
        (hg.dist_le x y)) heq.symm)
    · rw [hrightDiff, hrightDiff] at heq
      exact flat_Amalgamation_mapped_pair_eq j huv huv' (hg.edge_unique hxy hxy' heq)


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
    simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, reverseLabel, hz]
  · exact isGraceful_amalgamation_at_cut K L R i j hi hj linkL linkR
      hoverlap hcover hedges hcount f g k hf hg hk hlinkR

end Math15.Graceful


/- Supporting module: H2Data -/


namespace Bounty

def FiniteAlphaSpider (L : ℕ) (f : Fin (L+5) → ℕ) (k : ℕ) : Prop :=
  SpiderCertificate L f ∧ k < L+4 ∧
  ∀ j : Fin (L+5), 0 < j.val →
    (f (spiderParentFin j) ≤ k ∧ k < f j) ∨
    (f j ≤ k ∧ k < f (spiderParentFin j))

abbrev finiteAlphaSpiderDecidable (L : ℕ) (f : Fin (L+5) → ℕ) (k : ℕ) :
    Decidable (FiniteAlphaSpider L f k) := by
  unfold FiniteAlphaSpider
  let _ := spiderCertificateDecidable L f
  infer_instance

theorem FiniteAlphaSpider.toNat {L k : ℕ} {f : Fin (L+5) → ℕ}
    (h : FiniteAlphaSpider L f k) :
    NatSpiderCertificate L (extendSpiderLabel f) ∧
    NatSpiderAlpha L (extendSpiderLabel f) k ∧ k < L+4 := by
  refine ⟨h.1.toNat, ?_, h.2.1⟩
  intro j hj hjb
  have hpar : spiderParent j < L+5 := (spiderParent_le j).trans_lt hjb
  have hc := h.2.2 ⟨j,hjb⟩ hj
  simpa only [extendSpiderLabel, dite_eq_left hjb, dite_eq_left hpar, spiderParentFin] using hc

theorem FiniteAlphaSpider.ofAlpha {L k : ℕ} {f : Fin (L+5) → ℕ}
    (h : Math15.Graceful.IsAlphaLabeling (spider L) f k) : FiniteAlphaSpider L f k := by
  refine ⟨⟨h.1.1, ?_, ?_⟩, ?_, ?_⟩
  · intro i
    simpa only [spider_edgeCount] using h.1.2.1 i
  · intro i j hi hj heq
    have hiAdj : (spider L).Adj (spiderParentFin i) i := Or.inl ⟨spiderParent_lt hi, rfl⟩
    have hjAdj : (spider L).Adj (spiderParentFin j) j := Or.inl ⟨spiderParent_lt hj, rfl⟩
    rcases h.1.edge_unique hiAdj hjAdj heq with he | he
    · exact he.2
    · have hia := congrArg Fin.val he.1
      have hib := congrArg Fin.val he.2
      have hip := spiderParent_lt hi
      have hjp := spiderParent_lt hj
      dsimp only [spiderParentFin] at hia hib
      omega
  · simpa only [spider_edgeCount] using h.2.1
  · intro j hj
    exact h.2.2 _ _ (Or.inl ⟨spiderParent_lt hj,rfl⟩)

def RootedAlphaSpider (d c : ℕ) : Prop :=
  ∃ (f : ℕ → ℕ) (k : ℕ), NatSpiderCertificate (d+c) f ∧
    NatSpiderAlpha (d+c) f k ∧ k < d+c+4 ∧ f (4+d) = 0

theorem rootedAlphaSpider_of_finite {d c k : ℕ} {f : Fin (d+c+5) → ℕ}
    (h : FiniteAlphaSpider (d+c) f k) (hzero : f ⟨4+d,by omega⟩ = 0) :
    RootedAlphaSpider d c := by
  obtain ⟨hg,ha,hk⟩ := h.toNat
  refine ⟨extendSpiderLabel f,k,hg,ha,hk,?_⟩
  simpa only [extendSpiderLabel, dite_eq_left (show 4+d < d+c+5 by omega)] using hzero

theorem RootedAlphaSpider.toAlpha {d c : ℕ} (h : RootedAlphaSpider d c) :
    ∃ f k, Math15.Graceful.IsAlphaLabeling (spider (d+c)) f k ∧
      f ⟨4+d,by omega⟩ = 0 := by
  obtain ⟨f,k,hf,ha,hk,hzero⟩ := h
  exact ⟨_,_,ha.toAlphaLabeling hf hk,hzero⟩

end Bounty


/- Supporting module: H2Finite -/

namespace Bounty

def h2_1_2_labels : Fin 8 → ℕ := ![5, 3, 4, 2, 6, 0, 7, 1]

theorem h2_1_2_certificate : FiniteAlphaSpider 3 h2_1_2_labels 3 := by
  let _ := finiteAlphaSpiderDecidable 3 h2_1_2_labels 3
  decide

theorem h2_1_2_rooted : RootedAlphaSpider 1 2 :=
  rootedAlphaSpider_of_finite h2_1_2_certificate (by decide)

def h2_1_3_labels : Fin 9 → ℕ := ![5, 3, 4, 2, 6, 0, 8, 1, 7]

theorem h2_1_3_certificate : FiniteAlphaSpider 4 h2_1_3_labels 3 := by
  let _ := finiteAlphaSpiderDecidable 4 h2_1_3_labels 3
  decide

theorem h2_1_3_rooted : RootedAlphaSpider 1 3 :=
  rootedAlphaSpider_of_finite h2_1_3_certificate (by decide)

def h2_1_6_labels : Fin 12 → ℕ := ![9, 2, 10, 4, 8, 0, 11, 1, 7, 5, 6, 3]

theorem h2_1_6_certificate : FiniteAlphaSpider 7 h2_1_6_labels 5 := by
  let _ := finiteAlphaSpiderDecidable 7 h2_1_6_labels 5
  decide

theorem h2_1_6_rooted : RootedAlphaSpider 1 6 :=
  rootedAlphaSpider_of_finite h2_1_6_certificate (by decide)

def h2_1_7_labels : Fin 13 → ℕ := ![12, 1, 9, 2, 11, 0, 6, 5, 7, 4, 8, 3, 10]

theorem h2_1_7_certificate : FiniteAlphaSpider 8 h2_1_7_labels 5 := by
  let _ := finiteAlphaSpiderDecidable 8 h2_1_7_labels 5
  decide

theorem h2_1_7_rooted : RootedAlphaSpider 1 7 :=
  rootedAlphaSpider_of_finite h2_1_7_certificate (by decide)

def h2_1_8_labels : Fin 14 → ℕ := ![13, 3, 10, 1, 12, 0, 8, 6, 7, 4, 9, 5, 11, 2]

theorem h2_1_8_certificate : FiniteAlphaSpider 9 h2_1_8_labels 6 := by
  let _ := finiteAlphaSpiderDecidable 9 h2_1_8_labels 6
  decide

theorem h2_1_8_rooted : RootedAlphaSpider 1 8 :=
  rootedAlphaSpider_of_finite h2_1_8_certificate (by decide)

def h2_1_9_labels : Fin 15 → ℕ := ![14, 2, 12, 1, 10, 0, 11, 4, 7, 6, 8, 3, 9, 5, 13]

theorem h2_1_9_certificate : FiniteAlphaSpider 10 h2_1_9_labels 6 := by
  let _ := finiteAlphaSpiderDecidable 10 h2_1_9_labels 6
  decide

theorem h2_1_9_rooted : RootedAlphaSpider 1 9 :=
  rootedAlphaSpider_of_finite h2_1_9_certificate (by decide)

def h2_1_11_labels : Fin 17 → ℕ := ![15, 5, 13, 1, 12, 0, 16, 3, 8, 7, 9, 6, 10, 4, 11, 2, 14]

theorem h2_1_11_certificate : FiniteAlphaSpider 12 h2_1_11_labels 7 := by
  let _ := finiteAlphaSpiderDecidable 12 h2_1_11_labels 7
  decide

theorem h2_1_11_rooted : RootedAlphaSpider 1 11 :=
  rootedAlphaSpider_of_finite h2_1_11_certificate (by decide)

def h2_2_1_labels : Fin 8 → ℕ := ![2, 4, 3, 5, 1, 7, 0, 6]

theorem h2_2_1_certificate : FiniteAlphaSpider 3 h2_2_1_labels 3 := by
  let _ := finiteAlphaSpiderDecidable 3 h2_2_1_labels 3
  decide

theorem h2_2_1_rooted : RootedAlphaSpider 2 1 :=
  rootedAlphaSpider_of_finite h2_2_1_certificate (by decide)

def h2_2_2_labels : Fin 9 → ℕ := ![3, 5, 4, 6, 2, 8, 0, 7, 1]

theorem h2_2_2_certificate : FiniteAlphaSpider 4 h2_2_2_labels 4 := by
  let _ := finiteAlphaSpiderDecidable 4 h2_2_2_labels 4
  decide

theorem h2_2_2_rooted : RootedAlphaSpider 2 2 :=
  rootedAlphaSpider_of_finite h2_2_2_certificate (by decide)

def h2_2_3_labels : Fin 10 → ℕ := ![3, 5, 4, 7, 2, 6, 0, 9, 1, 8]

theorem h2_2_3_certificate : FiniteAlphaSpider 5 h2_2_3_labels 4 := by
  let _ := finiteAlphaSpiderDecidable 5 h2_2_3_labels 4
  decide

theorem h2_2_3_rooted : RootedAlphaSpider 2 3 :=
  rootedAlphaSpider_of_finite h2_2_3_certificate (by decide)

def h2_2_4_labels : Fin 11 → ℕ := ![4, 6, 5, 7, 3, 9, 0, 10, 2, 8, 1]

theorem h2_2_4_certificate : FiniteAlphaSpider 6 h2_2_4_labels 5 := by
  let _ := finiteAlphaSpiderDecidable 6 h2_2_4_labels 5
  decide

theorem h2_2_4_rooted : RootedAlphaSpider 2 4 :=
  rootedAlphaSpider_of_finite h2_2_4_certificate (by decide)

def h2_2_5_labels : Fin 12 → ℕ := ![4, 6, 5, 7, 2, 8, 0, 11, 1, 10, 3, 9]

theorem h2_2_5_certificate : FiniteAlphaSpider 7 h2_2_5_labels 5 := by
  let _ := finiteAlphaSpiderDecidable 7 h2_2_5_labels 5
  decide

theorem h2_2_5_rooted : RootedAlphaSpider 2 5 :=
  rootedAlphaSpider_of_finite h2_2_5_certificate (by decide)

def h2_2_6_labels : Fin 13 → ℕ := ![4, 8, 3, 11, 2, 10, 0, 12, 1, 9, 6, 7, 5]

theorem h2_2_6_certificate : FiniteAlphaSpider 8 h2_2_6_labels 6 := by
  let _ := finiteAlphaSpiderDecidable 8 h2_2_6_labels 6
  decide

theorem h2_2_6_rooted : RootedAlphaSpider 2 6 :=
  rootedAlphaSpider_of_finite h2_2_6_certificate (by decide)

def h2_2_7_labels : Fin 14 → ℕ := ![3, 10, 4, 11, 1, 12, 0, 13, 2, 7, 6, 8, 5, 9]

theorem h2_2_7_certificate : FiniteAlphaSpider 9 h2_2_7_labels 6 := by
  let _ := finiteAlphaSpiderDecidable 9 h2_2_7_labels 6
  decide

theorem h2_2_7_rooted : RootedAlphaSpider 2 7 :=
  rootedAlphaSpider_of_finite h2_2_7_certificate (by decide)

def h2_2_8_labels : Fin 15 → ℕ := ![2, 12, 1, 9, 5, 14, 0, 13, 4, 10, 7, 8, 6, 11, 3]

theorem h2_2_8_certificate : FiniteAlphaSpider 10 h2_2_8_labels 7 := by
  let _ := finiteAlphaSpiderDecidable 10 h2_2_8_labels 7
  decide

theorem h2_2_8_rooted : RootedAlphaSpider 2 8 :=
  rootedAlphaSpider_of_finite h2_2_8_certificate (by decide)

def h2_2_9_labels : Fin 16 → ℕ := ![1, 12, 3, 11, 4, 15, 0, 13, 7, 8, 6, 9, 5, 10, 2, 14]

theorem h2_2_9_certificate : FiniteAlphaSpider 11 h2_2_9_labels 7 := by
  let _ := finiteAlphaSpiderDecidable 11 h2_2_9_labels 7
  decide

theorem h2_2_9_rooted : RootedAlphaSpider 2 9 :=
  rootedAlphaSpider_of_finite h2_2_9_certificate (by decide)

def h2_2_10_labels : Fin 17 → ℕ := ![1, 11, 3, 15, 4, 16, 0, 13, 8, 9, 7, 10, 6, 12, 5, 14, 2]

theorem h2_2_10_certificate : FiniteAlphaSpider 12 h2_2_10_labels 8 := by
  let _ := finiteAlphaSpiderDecidable 12 h2_2_10_labels 8
  decide

theorem h2_2_10_rooted : RootedAlphaSpider 2 10 :=
  rootedAlphaSpider_of_finite h2_2_10_certificate (by decide)

def h2_3_1_labels : Fin 9 → ℕ := ![5, 3, 4, 2, 7, 1, 8, 0, 6]

theorem h2_3_1_certificate : FiniteAlphaSpider 4 h2_3_1_labels 3 := by
  let _ := finiteAlphaSpiderDecidable 4 h2_3_1_labels 3
  decide

theorem h2_3_1_rooted : RootedAlphaSpider 3 1 :=
  rootedAlphaSpider_of_finite h2_3_1_certificate (by decide)

def h2_3_2_labels : Fin 10 → ℕ := ![5, 4, 6, 1, 7, 2, 9, 0, 8, 3]

theorem h2_3_2_certificate : FiniteAlphaSpider 5 h2_3_2_labels 4 := by
  let _ := finiteAlphaSpiderDecidable 5 h2_3_2_labels 4
  decide

theorem h2_3_2_rooted : RootedAlphaSpider 3 2 :=
  rootedAlphaSpider_of_finite h2_3_2_certificate (by decide)

def h2_3_3_labels : Fin 11 → ℕ := ![6, 4, 5, 2, 9, 3, 8, 0, 10, 1, 7]

theorem h2_3_3_certificate : FiniteAlphaSpider 6 h2_3_3_labels 4 := by
  let _ := finiteAlphaSpiderDecidable 6 h2_3_3_labels 4
  decide

theorem h2_3_3_rooted : RootedAlphaSpider 3 3 :=
  rootedAlphaSpider_of_finite h2_3_3_certificate (by decide)

def h2_3_4_labels : Fin 12 → ℕ := ![6, 5, 7, 1, 9, 3, 10, 0, 11, 2, 8, 4]

theorem h2_3_4_certificate : FiniteAlphaSpider 7 h2_3_4_labels 5 := by
  let _ := finiteAlphaSpiderDecidable 7 h2_3_4_labels 5
  decide

theorem h2_3_4_rooted : RootedAlphaSpider 3 4 :=
  rootedAlphaSpider_of_finite h2_3_4_certificate (by decide)

def h2_3_5_labels : Fin 13 → ℕ := ![7, 5, 6, 3, 8, 4, 10, 0, 12, 1, 9, 2, 11]

theorem h2_3_5_certificate : FiniteAlphaSpider 8 h2_3_5_labels 5 := by
  let _ := finiteAlphaSpiderDecidable 8 h2_3_5_labels 5
  decide

theorem h2_3_5_rooted : RootedAlphaSpider 3 5 :=
  rootedAlphaSpider_of_finite h2_3_5_certificate (by decide)

def h2_3_6_labels : Fin 14 → ℕ := ![9, 1, 11, 4, 10, 2, 13, 0, 12, 3, 7, 6, 8, 5]

theorem h2_3_6_certificate : FiniteAlphaSpider 9 h2_3_6_labels 6 := by
  let _ := finiteAlphaSpiderDecidable 9 h2_3_6_labels 6
  decide

theorem h2_3_6_rooted : RootedAlphaSpider 3 6 :=
  rootedAlphaSpider_of_finite h2_3_6_certificate (by decide)

def h2_3_7_labels : Fin 15 → ℕ := ![8, 6, 7, 5, 9, 3, 12, 0, 14, 1, 11, 4, 10, 2, 13]

theorem h2_3_7_certificate : FiniteAlphaSpider 10 h2_3_7_labels 6 := by
  let _ := finiteAlphaSpiderDecidable 10 h2_3_7_labels 6
  decide

theorem h2_3_7_rooted : RootedAlphaSpider 3 7 :=
  rootedAlphaSpider_of_finite h2_3_7_certificate (by decide)

def h2_3_8_labels : Fin 16 → ℕ := ![8, 7, 11, 6, 9, 3, 14, 0, 15, 2, 12, 5, 13, 1, 10, 4]

theorem h2_3_8_certificate : FiniteAlphaSpider 11 h2_3_8_labels 7 := by
  let _ := finiteAlphaSpiderDecidable 11 h2_3_8_labels 7
  decide

theorem h2_3_8_rooted : RootedAlphaSpider 3 8 :=
  rootedAlphaSpider_of_finite h2_3_8_certificate (by decide)

def h2_3_9_labels : Fin 17 → ℕ := ![12, 1, 14, 4, 13, 2, 16, 0, 15, 3, 10, 6, 11, 5, 8, 7, 9]

theorem h2_3_9_certificate : FiniteAlphaSpider 12 h2_3_9_labels 7 := by
  let _ := finiteAlphaSpiderDecidable 12 h2_3_9_labels 7
  decide

theorem h2_3_9_rooted : RootedAlphaSpider 3 9 :=
  rootedAlphaSpider_of_finite h2_3_9_certificate (by decide)

def h2_3_10_labels : Fin 18 → ℕ := ![15, 1, 13, 4, 14, 2, 17, 0, 16, 8, 9, 7, 10, 6, 11, 5, 12, 3]

theorem h2_3_10_certificate : FiniteAlphaSpider 13 h2_3_10_labels 8 := by
  let _ := finiteAlphaSpiderDecidable 13 h2_3_10_labels 8
  decide

theorem h2_3_10_rooted : RootedAlphaSpider 3 10 :=
  rootedAlphaSpider_of_finite h2_3_10_certificate (by decide)

def h2_4_1_labels : Fin 10 → ℕ := ![4, 5, 3, 7, 2, 8, 1, 9, 0, 6]

theorem h2_4_1_certificate : FiniteAlphaSpider 5 h2_4_1_labels 4 := by
  let _ := finiteAlphaSpiderDecidable 5 h2_4_1_labels 4
  decide

theorem h2_4_1_rooted : RootedAlphaSpider 4 1 :=
  rootedAlphaSpider_of_finite h2_4_1_certificate (by decide)

def h2_4_2_labels : Fin 11 → ℕ := ![4, 6, 5, 7, 3, 9, 2, 8, 0, 10, 1]

theorem h2_4_2_certificate : FiniteAlphaSpider 6 h2_4_2_labels 5 := by
  let _ := finiteAlphaSpiderDecidable 6 h2_4_2_labels 5
  decide

theorem h2_4_2_rooted : RootedAlphaSpider 4 2 :=
  rootedAlphaSpider_of_finite h2_4_2_certificate (by decide)

def h2_4_3_labels : Fin 12 → ℕ := ![5, 6, 4, 9, 2, 8, 3, 11, 0, 10, 1, 7]

theorem h2_4_3_certificate : FiniteAlphaSpider 7 h2_4_3_labels 5 := by
  let _ := finiteAlphaSpiderDecidable 7 h2_4_3_labels 5
  decide

theorem h2_4_3_rooted : RootedAlphaSpider 4 3 :=
  rootedAlphaSpider_of_finite h2_4_3_certificate (by decide)

def h2_4_4_labels : Fin 13 → ℕ := ![4, 8, 3, 10, 2, 11, 1, 12, 0, 9, 6, 7, 5]

theorem h2_4_4_certificate : FiniteAlphaSpider 8 h2_4_4_labels 6 := by
  let _ := finiteAlphaSpiderDecidable 8 h2_4_4_labels 6
  decide

theorem h2_4_4_rooted : RootedAlphaSpider 4 4 :=
  rootedAlphaSpider_of_finite h2_4_4_certificate (by decide)

def h2_4_5_labels : Fin 14 → ℕ := ![4, 9, 3, 11, 2, 12, 1, 13, 0, 10, 6, 7, 5, 8]

theorem h2_4_5_certificate : FiniteAlphaSpider 9 h2_4_5_labels 6 := by
  let _ := finiteAlphaSpiderDecidable 9 h2_4_5_labels 6
  decide

theorem h2_4_5_rooted : RootedAlphaSpider 4 5 :=
  rootedAlphaSpider_of_finite h2_4_5_certificate (by decide)

def h2_4_6_labels : Fin 15 → ℕ := ![6, 8, 7, 9, 5, 11, 2, 14, 0, 13, 3, 10, 4, 12, 1]

theorem h2_4_6_certificate : FiniteAlphaSpider 10 h2_4_6_labels 7 := by
  let _ := finiteAlphaSpiderDecidable 10 h2_4_6_labels 7
  decide

theorem h2_4_6_rooted : RootedAlphaSpider 4 6 :=
  rootedAlphaSpider_of_finite h2_4_6_certificate (by decide)

def h2_4_7_labels : Fin 16 → ℕ := ![5, 10, 4, 14, 2, 12, 1, 15, 0, 13, 3, 11, 7, 8, 6, 9]

theorem h2_4_7_certificate : FiniteAlphaSpider 11 h2_4_7_labels 7 := by
  let _ := finiteAlphaSpiderDecidable 11 h2_4_7_labels 7
  decide

theorem h2_4_7_rooted : RootedAlphaSpider 4 7 :=
  rootedAlphaSpider_of_finite h2_4_7_certificate (by decide)

def h2_4_8_labels : Fin 17 → ℕ := ![4, 12, 3, 14, 2, 15, 1, 16, 0, 13, 6, 10, 5, 11, 8, 9, 7]

theorem h2_4_8_certificate : FiniteAlphaSpider 12 h2_4_8_labels 8 := by
  let _ := finiteAlphaSpiderDecidable 12 h2_4_8_labels 8
  decide

theorem h2_4_8_rooted : RootedAlphaSpider 4 8 :=
  rootedAlphaSpider_of_finite h2_4_8_certificate (by decide)

def h2_4_9_labels : Fin 18 → ℕ := ![7, 9, 8, 10, 4, 11, 6, 16, 0, 17, 2, 13, 5, 12, 3, 15, 1, 14]

theorem h2_4_9_certificate : FiniteAlphaSpider 13 h2_4_9_labels 8 := by
  let _ := finiteAlphaSpiderDecidable 13 h2_4_9_labels 8
  decide

theorem h2_4_9_rooted : RootedAlphaSpider 4 9 :=
  rootedAlphaSpider_of_finite h2_4_9_certificate (by decide)

def h2_4_10_labels : Fin 19 → ℕ := ![9, 10, 4, 11, 8, 13, 2, 18, 0, 17, 3, 15, 7, 12, 5, 14, 1, 16, 6]

theorem h2_4_10_certificate : FiniteAlphaSpider 14 h2_4_10_labels 9 := by
  let _ := finiteAlphaSpiderDecidable 14 h2_4_10_labels 9
  decide

theorem h2_4_10_rooted : RootedAlphaSpider 4 10 :=
  rootedAlphaSpider_of_finite h2_4_10_certificate (by decide)

def h2_4_11_labels : Fin 20 → ℕ := ![8, 10, 9, 11, 6, 12, 4, 18, 0, 19, 2, 13, 7, 14, 5, 15, 3, 16, 1, 17]

theorem h2_4_11_certificate : FiniteAlphaSpider 15 h2_4_11_labels 9 := by
  let _ := finiteAlphaSpiderDecidable 15 h2_4_11_labels 9
  decide

theorem h2_4_11_rooted : RootedAlphaSpider 4 11 :=
  rootedAlphaSpider_of_finite h2_4_11_certificate (by decide)

def h2_4_12_labels : Fin 21 → ℕ := ![2, 18, 5, 16, 4, 19, 1, 20, 0, 15, 10, 11, 9, 12, 8, 17, 6, 14, 7, 13, 3]

theorem h2_4_12_certificate : FiniteAlphaSpider 16 h2_4_12_labels 10 := by
  let _ := finiteAlphaSpiderDecidable 16 h2_4_12_labels 10
  decide

theorem h2_4_12_rooted : RootedAlphaSpider 4 12 :=
  rootedAlphaSpider_of_finite h2_4_12_certificate (by decide)

def h2_5_1_labels : Fin 11 → ℕ := ![6, 4, 5, 3, 7, 1, 8, 2, 10, 0, 9]

theorem h2_5_1_certificate : FiniteAlphaSpider 6 h2_5_1_labels 4 := by
  let _ := finiteAlphaSpiderDecidable 6 h2_5_1_labels 4
  decide

theorem h2_5_1_rooted : RootedAlphaSpider 5 1 :=
  rootedAlphaSpider_of_finite h2_5_1_certificate (by decide)

def h2_5_2_labels : Fin 12 → ℕ := ![8, 3, 7, 1, 9, 5, 6, 4, 10, 0, 11, 2]

theorem h2_5_2_certificate : FiniteAlphaSpider 7 h2_5_2_labels 5 := by
  let _ := finiteAlphaSpiderDecidable 7 h2_5_2_labels 5
  decide

theorem h2_5_2_rooted : RootedAlphaSpider 5 2 :=
  rootedAlphaSpider_of_finite h2_5_2_certificate (by decide)

def h2_5_3_labels : Fin 13 → ℕ := ![7, 5, 6, 4, 8, 2, 10, 3, 9, 0, 12, 1, 11]

theorem h2_5_3_certificate : FiniteAlphaSpider 8 h2_5_3_labels 5 := by
  let _ := finiteAlphaSpiderDecidable 8 h2_5_3_labels 5
  decide

theorem h2_5_3_rooted : RootedAlphaSpider 5 3 :=
  rootedAlphaSpider_of_finite h2_5_3_certificate (by decide)

def h2_5_4_labels : Fin 14 → ℕ := ![9, 3, 10, 4, 8, 6, 7, 5, 13, 0, 12, 1, 11, 2]

theorem h2_5_4_certificate : FiniteAlphaSpider 9 h2_5_4_labels 6 := by
  let _ := finiteAlphaSpiderDecidable 9 h2_5_4_labels 6
  decide

theorem h2_5_4_rooted : RootedAlphaSpider 5 4 :=
  rootedAlphaSpider_of_finite h2_5_4_certificate (by decide)

def h2_5_5_labels : Fin 15 → ℕ := ![8, 6, 7, 5, 10, 4, 11, 2, 14, 0, 13, 3, 9, 1, 12]

theorem h2_5_5_certificate : FiniteAlphaSpider 10 h2_5_5_labels 6 := by
  let _ := finiteAlphaSpiderDecidable 10 h2_5_5_labels 6
  decide

theorem h2_5_5_rooted : RootedAlphaSpider 5 5 :=
  rootedAlphaSpider_of_finite h2_5_5_certificate (by decide)

def h2_5_6_labels : Fin 16 → ℕ := ![8, 7, 10, 6, 11, 1, 13, 2, 15, 0, 14, 4, 12, 3, 9, 5]

theorem h2_5_6_certificate : FiniteAlphaSpider 11 h2_5_6_labels 7 := by
  let _ := finiteAlphaSpiderDecidable 11 h2_5_6_labels 7
  decide

theorem h2_5_6_rooted : RootedAlphaSpider 5 6 :=
  rootedAlphaSpider_of_finite h2_5_6_certificate (by decide)

def h2_5_7_labels : Fin 17 → ℕ := ![9, 7, 8, 6, 11, 5, 12, 3, 13, 0, 16, 1, 15, 4, 10, 2, 14]

theorem h2_5_7_certificate : FiniteAlphaSpider 12 h2_5_7_labels 7 := by
  let _ := finiteAlphaSpiderDecidable 12 h2_5_7_labels 7
  decide

theorem h2_5_7_rooted : RootedAlphaSpider 5 7 :=
  rootedAlphaSpider_of_finite h2_5_7_certificate (by decide)

def h2_5_8_labels : Fin 18 → ℕ := ![9, 8, 13, 6, 10, 7, 14, 1, 16, 0, 17, 3, 15, 4, 12, 2, 11, 5]

theorem h2_5_8_certificate : FiniteAlphaSpider 13 h2_5_8_labels 8 := by
  let _ := finiteAlphaSpiderDecidable 13 h2_5_8_labels 8
  decide

theorem h2_5_8_rooted : RootedAlphaSpider 5 8 :=
  rootedAlphaSpider_of_finite h2_5_8_certificate (by decide)

def h2_5_9_labels : Fin 19 → ℕ := ![10, 8, 9, 7, 12, 6, 14, 1, 17, 0, 18, 3, 15, 5, 11, 4, 13, 2, 16]

theorem h2_5_9_certificate : FiniteAlphaSpider 14 h2_5_9_labels 8 := by
  let _ := finiteAlphaSpiderDecidable 14 h2_5_9_labels 8
  decide

theorem h2_5_9_rooted : RootedAlphaSpider 5 9 :=
  rootedAlphaSpider_of_finite h2_5_9_certificate (by decide)

def h2_5_10_labels : Fin 20 → ℕ := ![10, 9, 12, 8, 13, 1, 17, 2, 19, 0, 18, 4, 15, 3, 16, 6, 14, 7, 11, 5]

theorem h2_5_10_certificate : FiniteAlphaSpider 15 h2_5_10_labels 9 := by
  let _ := finiteAlphaSpiderDecidable 15 h2_5_10_labels 9
  decide

theorem h2_5_10_rooted : RootedAlphaSpider 5 10 :=
  rootedAlphaSpider_of_finite h2_5_10_certificate (by decide)

def h2_5_11_labels : Fin 21 → ℕ := ![10, 9, 11, 7, 15, 5, 19, 1, 20, 0, 17, 8, 12, 6, 13, 2, 18, 3, 16, 4, 14]

theorem h2_5_11_certificate : FiniteAlphaSpider 16 h2_5_11_labels 9 := by
  let _ := finiteAlphaSpiderDecidable 16 h2_5_11_labels 9
  decide

theorem h2_5_11_rooted : RootedAlphaSpider 5 11 :=
  rootedAlphaSpider_of_finite h2_5_11_certificate (by decide)

def h2_5_12_labels : Fin 22 → ℕ := ![11, 10, 12, 8, 15, 1, 19, 2, 21, 0, 20, 4, 17, 3, 18, 6, 14, 9, 13, 7, 16, 5]

theorem h2_5_12_certificate : FiniteAlphaSpider 17 h2_5_12_labels 10 := by
  let _ := finiteAlphaSpiderDecidable 17 h2_5_12_labels 10
  decide

theorem h2_5_12_rooted : RootedAlphaSpider 5 12 :=
  rootedAlphaSpider_of_finite h2_5_12_certificate (by decide)

def h2_6_1_labels : Fin 12 → ℕ := ![4, 6, 5, 10, 2, 7, 3, 8, 1, 11, 0, 9]

theorem h2_6_1_certificate : FiniteAlphaSpider 7 h2_6_1_labels 5 := by
  let _ := finiteAlphaSpiderDecidable 7 h2_6_1_labels 5
  decide

theorem h2_6_1_rooted : RootedAlphaSpider 6 1 :=
  rootedAlphaSpider_of_finite h2_6_1_certificate (by decide)

def h2_6_2_labels : Fin 13 → ℕ := ![5, 7, 6, 9, 4, 8, 2, 10, 3, 12, 0, 11, 1]

theorem h2_6_2_certificate : FiniteAlphaSpider 8 h2_6_2_labels 6 := by
  let _ := finiteAlphaSpiderDecidable 8 h2_6_2_labels 6
  decide

theorem h2_6_2_rooted : RootedAlphaSpider 6 2 :=
  rootedAlphaSpider_of_finite h2_6_2_certificate (by decide)

def h2_6_3_labels : Fin 14 → ℕ := ![5, 7, 6, 8, 4, 10, 3, 9, 1, 13, 0, 11, 2, 12]

theorem h2_6_3_certificate : FiniteAlphaSpider 9 h2_6_3_labels 6 := by
  let _ := finiteAlphaSpiderDecidable 9 h2_6_3_labels 6
  decide

theorem h2_6_3_rooted : RootedAlphaSpider 6 3 :=
  rootedAlphaSpider_of_finite h2_6_3_certificate (by decide)

def h2_6_4_labels : Fin 15 → ℕ := ![4, 10, 6, 11, 3, 9, 7, 8, 5, 14, 0, 13, 1, 12, 2]

theorem h2_6_4_certificate : FiniteAlphaSpider 10 h2_6_4_labels 7 := by
  let _ := finiteAlphaSpiderDecidable 10 h2_6_4_labels 7
  decide

theorem h2_6_4_rooted : RootedAlphaSpider 6 4 :=
  rootedAlphaSpider_of_finite h2_6_4_certificate (by decide)

def h2_6_5_labels : Fin 16 → ℕ := ![6, 8, 7, 12, 4, 9, 5, 10, 3, 14, 0, 15, 2, 11, 1, 13]

theorem h2_6_5_certificate : FiniteAlphaSpider 11 h2_6_5_labels 7 := by
  let _ := finiteAlphaSpiderDecidable 11 h2_6_5_labels 7
  decide

theorem h2_6_5_rooted : RootedAlphaSpider 6 5 :=
  rootedAlphaSpider_of_finite h2_6_5_certificate (by decide)

def h2_6_6_labels : Fin 17 → ℕ := ![8, 9, 4, 11, 7, 10, 2, 15, 1, 16, 0, 12, 6, 13, 3, 14, 5]

theorem h2_6_6_certificate : FiniteAlphaSpider 12 h2_6_6_labels 8 := by
  let _ := finiteAlphaSpiderDecidable 12 h2_6_6_labels 8
  decide

theorem h2_6_6_rooted : RootedAlphaSpider 6 6 :=
  rootedAlphaSpider_of_finite h2_6_6_certificate (by decide)

def h2_6_7_labels : Fin 18 → ℕ := ![8, 9, 6, 14, 4, 10, 1, 15, 3, 16, 0, 17, 2, 13, 5, 12, 7, 11]

theorem h2_6_7_certificate : FiniteAlphaSpider 13 h2_6_7_labels 8 := by
  let _ := finiteAlphaSpiderDecidable 13 h2_6_7_labels 8
  decide

theorem h2_6_7_rooted : RootedAlphaSpider 6 7 :=
  rootedAlphaSpider_of_finite h2_6_7_certificate (by decide)

def h2_6_8_labels : Fin 19 → ℕ := ![9, 10, 7, 16, 5, 11, 3, 17, 1, 18, 0, 15, 2, 14, 4, 13, 8, 12, 6]

theorem h2_6_8_certificate : FiniteAlphaSpider 14 h2_6_8_labels 9 := by
  let _ := finiteAlphaSpiderDecidable 14 h2_6_8_labels 9
  decide

theorem h2_6_8_rooted : RootedAlphaSpider 6 8 :=
  rootedAlphaSpider_of_finite h2_6_8_certificate (by decide)

def h2_6_9_labels : Fin 20 → ℕ := ![9, 10, 7, 13, 8, 11, 4, 15, 5, 18, 0, 19, 2, 14, 6, 12, 3, 17, 1, 16]

theorem h2_6_9_certificate : FiniteAlphaSpider 15 h2_6_9_labels 9 := by
  let _ := finiteAlphaSpiderDecidable 15 h2_6_9_labels 9
  decide

theorem h2_6_9_rooted : RootedAlphaSpider 6 9 :=
  rootedAlphaSpider_of_finite h2_6_9_certificate (by decide)

def h2_6_10_labels : Fin 21 → ℕ := ![10, 11, 7, 12, 9, 16, 1, 18, 2, 20, 0, 19, 6, 14, 3, 17, 5, 15, 8, 13, 4]

theorem h2_6_10_certificate : FiniteAlphaSpider 16 h2_6_10_labels 10 := by
  let _ := finiteAlphaSpiderDecidable 16 h2_6_10_labels 10
  decide

theorem h2_6_10_rooted : RootedAlphaSpider 6 10 :=
  rootedAlphaSpider_of_finite h2_6_10_certificate (by decide)

def h2_6_11_labels : Fin 22 → ℕ := ![8, 18, 4, 12, 6, 17, 1, 19, 2, 21, 0, 20, 5, 16, 3, 15, 7, 14, 9, 11, 10, 13]

theorem h2_6_11_certificate : FiniteAlphaSpider 17 h2_6_11_labels 10 := by
  let _ := finiteAlphaSpiderDecidable 17 h2_6_11_labels 10
  decide

theorem h2_6_11_rooted : RootedAlphaSpider 6 11 :=
  rootedAlphaSpider_of_finite h2_6_11_certificate (by decide)

def h2_6_12_labels : Fin 23 → ℕ := ![11, 12, 9, 17, 3, 13, 8, 15, 7, 20, 0, 22, 1, 19, 4, 21, 2, 18, 6, 16, 5, 14, 10]

theorem h2_6_12_certificate : FiniteAlphaSpider 18 h2_6_12_labels 11 := by
  let _ := finiteAlphaSpiderDecidable 18 h2_6_12_labels 11
  decide

theorem h2_6_12_rooted : RootedAlphaSpider 6 12 :=
  rootedAlphaSpider_of_finite h2_6_12_certificate (by decide)

def h2_6_13_labels : Fin 24 → ℕ := ![10, 12, 11, 14, 6, 13, 8, 18, 2, 23, 0, 22, 5, 17, 3, 21, 1, 20, 7, 16, 9, 15, 4, 19]

theorem h2_6_13_certificate : FiniteAlphaSpider 19 h2_6_13_labels 11 := by
  let _ := finiteAlphaSpiderDecidable 19 h2_6_13_labels 11
  decide

theorem h2_6_13_rooted : RootedAlphaSpider 6 13 :=
  rootedAlphaSpider_of_finite h2_6_13_certificate (by decide)

def h2_6_14_labels : Fin 25 → ℕ := ![11, 15, 10, 17, 7, 14, 12, 13, 1, 23, 0, 24, 3, 21, 2, 22, 5, 20, 4, 18, 9, 16, 8, 19, 6]

theorem h2_6_14_certificate : FiniteAlphaSpider 20 h2_6_14_labels 12 := by
  let _ := finiteAlphaSpiderDecidable 20 h2_6_14_labels 12
  decide

theorem h2_6_14_rooted : RootedAlphaSpider 6 14 :=
  rootedAlphaSpider_of_finite h2_6_14_certificate (by decide)

def h2_7_1_labels : Fin 13 → ℕ := ![10, 1, 9, 3, 8, 4, 7, 5, 6, 2, 12, 0, 11]

theorem h2_7_1_certificate : FiniteAlphaSpider 8 h2_7_1_labels 5 := by
  let _ := finiteAlphaSpiderDecidable 8 h2_7_1_labels 5
  decide

theorem h2_7_1_rooted : RootedAlphaSpider 7 1 :=
  rootedAlphaSpider_of_finite h2_7_1_certificate (by decide)

def h2_7_2_labels : Fin 14 → ℕ := ![8, 6, 7, 4, 9, 5, 11, 2, 10, 3, 13, 0, 12, 1]

theorem h2_7_2_certificate : FiniteAlphaSpider 9 h2_7_2_labels 6 := by
  let _ := finiteAlphaSpiderDecidable 9 h2_7_2_labels 6
  decide

theorem h2_7_2_rooted : RootedAlphaSpider 7 2 :=
  rootedAlphaSpider_of_finite h2_7_2_certificate (by decide)

def h2_7_3_labels : Fin 15 → ℕ := ![8, 6, 7, 4, 9, 5, 11, 3, 10, 1, 14, 0, 12, 2, 13]

theorem h2_7_3_certificate : FiniteAlphaSpider 10 h2_7_3_labels 6 := by
  let _ := finiteAlphaSpiderDecidable 10 h2_7_3_labels 6
  decide

theorem h2_7_3_rooted : RootedAlphaSpider 7 3 :=
  rootedAlphaSpider_of_finite h2_7_3_certificate (by decide)

def h2_7_4_labels : Fin 16 → ℕ := ![10, 3, 11, 5, 9, 7, 8, 6, 12, 1, 15, 0, 13, 4, 14, 2]

theorem h2_7_4_certificate : FiniteAlphaSpider 11 h2_7_4_labels 7 := by
  let _ := finiteAlphaSpiderDecidable 11 h2_7_4_labels 7
  decide

theorem h2_7_4_rooted : RootedAlphaSpider 7 4 :=
  rootedAlphaSpider_of_finite h2_7_4_certificate (by decide)

def h2_7_5_labels : Fin 17 → ℕ := ![11, 4, 13, 5, 10, 7, 8, 6, 9, 1, 15, 0, 16, 3, 14, 2, 12]

theorem h2_7_5_certificate : FiniteAlphaSpider 12 h2_7_5_labels 7 := by
  let _ := finiteAlphaSpiderDecidable 12 h2_7_5_labels 7
  decide

theorem h2_7_5_rooted : RootedAlphaSpider 7 5 :=
  rootedAlphaSpider_of_finite h2_7_5_certificate (by decide)

def h2_7_6_labels : Fin 18 → ℕ := ![10, 8, 9, 7, 12, 6, 14, 5, 11, 4, 15, 0, 17, 1, 13, 3, 16, 2]

theorem h2_7_6_certificate : FiniteAlphaSpider 13 h2_7_6_labels 8 := by
  let _ := finiteAlphaSpiderDecidable 13 h2_7_6_labels 8
  decide

theorem h2_7_6_rooted : RootedAlphaSpider 7 6 :=
  rootedAlphaSpider_of_finite h2_7_6_certificate (by decide)

def h2_7_7_labels : Fin 19 → ℕ := ![10, 8, 9, 7, 12, 6, 13, 4, 17, 1, 18, 0, 15, 5, 11, 3, 14, 2, 16]

theorem h2_7_7_certificate : FiniteAlphaSpider 14 h2_7_7_labels 8 := by
  let _ := finiteAlphaSpiderDecidable 14 h2_7_7_labels 8
  decide

theorem h2_7_7_rooted : RootedAlphaSpider 7 7 :=
  rootedAlphaSpider_of_finite h2_7_7_certificate (by decide)

def h2_7_8_labels : Fin 20 → ℕ := ![11, 9, 10, 8, 13, 7, 14, 5, 15, 3, 16, 0, 19, 1, 18, 4, 12, 6, 17, 2]

theorem h2_7_8_certificate : FiniteAlphaSpider 15 h2_7_8_labels 9 := by
  let _ := finiteAlphaSpiderDecidable 15 h2_7_8_labels 9
  decide

theorem h2_7_8_rooted : RootedAlphaSpider 7 8 :=
  rootedAlphaSpider_of_finite h2_7_8_certificate (by decide)

def h2_7_9_labels : Fin 21 → ℕ := ![10, 5, 12, 6, 15, 9, 11, 8, 16, 1, 19, 0, 20, 3, 17, 4, 14, 2, 18, 7, 13]

theorem h2_7_9_certificate : FiniteAlphaSpider 16 h2_7_9_labels 9 := by
  let _ := finiteAlphaSpiderDecidable 16 h2_7_9_labels 9
  decide

theorem h2_7_9_rooted : RootedAlphaSpider 7 9 :=
  rootedAlphaSpider_of_finite h2_7_9_certificate (by decide)

def h2_7_10_labels : Fin 22 → ℕ := ![11, 7, 14, 9, 12, 10, 16, 3, 18, 6, 20, 0, 21, 2, 19, 1, 17, 8, 13, 5, 15, 4]

theorem h2_7_10_certificate : FiniteAlphaSpider 17 h2_7_10_labels 10 := by
  let _ := finiteAlphaSpiderDecidable 17 h2_7_10_labels 10
  decide

theorem h2_7_10_rooted : RootedAlphaSpider 7 10 :=
  rootedAlphaSpider_of_finite h2_7_10_certificate (by decide)

def h2_7_11_labels : Fin 23 → ℕ := ![12, 10, 11, 9, 14, 8, 15, 6, 16, 3, 19, 0, 22, 1, 21, 4, 18, 7, 13, 5, 17, 2, 20]

theorem h2_7_11_certificate : FiniteAlphaSpider 18 h2_7_11_labels 10 := by
  let _ := finiteAlphaSpiderDecidable 18 h2_7_11_labels 10
  decide

theorem h2_7_11_rooted : RootedAlphaSpider 7 11 :=
  rootedAlphaSpider_of_finite h2_7_11_certificate (by decide)

def h2_7_12_labels : Fin 24 → ℕ := ![21, 1, 20, 3, 19, 4, 18, 5, 17, 2, 23, 0, 22, 11, 12, 10, 13, 9, 14, 8, 15, 7, 16, 6]

theorem h2_7_12_certificate : FiniteAlphaSpider 19 h2_7_12_labels 11 := by
  let _ := finiteAlphaSpiderDecidable 19 h2_7_12_labels 11
  decide

theorem h2_7_12_rooted : RootedAlphaSpider 7 12 :=
  rootedAlphaSpider_of_finite h2_7_12_certificate (by decide)

def h2_7_13_labels : Fin 25 → ℕ := ![12, 11, 14, 8, 13, 10, 17, 6, 16, 4, 23, 0, 24, 2, 20, 7, 15, 9, 18, 3, 19, 5, 22, 1, 21]

theorem h2_7_13_certificate : FiniteAlphaSpider 20 h2_7_13_labels 11 := by
  let _ := finiteAlphaSpiderDecidable 20 h2_7_13_labels 11
  decide

theorem h2_7_13_rooted : RootedAlphaSpider 7 13 :=
  rootedAlphaSpider_of_finite h2_7_13_certificate (by decide)

def h2_7_14_labels : Fin 26 → ℕ := ![22, 1, 23, 5, 20, 3, 21, 7, 16, 4, 24, 0, 25, 2, 18, 10, 14, 9, 19, 6, 17, 11, 13, 12, 15, 8]

theorem h2_7_14_certificate : FiniteAlphaSpider 21 h2_7_14_labels 12 := by
  let _ := finiteAlphaSpiderDecidable 21 h2_7_14_labels 12
  decide

theorem h2_7_14_rooted : RootedAlphaSpider 7 14 :=
  rootedAlphaSpider_of_finite h2_7_14_certificate (by decide)

def h2_8_1_labels : Fin 14 → ℕ := ![3, 11, 2, 8, 4, 9, 6, 7, 5, 12, 1, 13, 0, 10]

theorem h2_8_1_certificate : FiniteAlphaSpider 9 h2_8_1_labels 6 := by
  let _ := finiteAlphaSpiderDecidable 9 h2_8_1_labels 6
  decide

theorem h2_8_1_rooted : RootedAlphaSpider 8 1 :=
  rootedAlphaSpider_of_finite h2_8_1_certificate (by decide)

def h2_8_2_labels : Fin 15 → ℕ := ![6, 8, 7, 9, 5, 11, 4, 10, 2, 12, 3, 14, 0, 13, 1]

theorem h2_8_2_certificate : FiniteAlphaSpider 10 h2_8_2_labels 7 := by
  let _ := finiteAlphaSpiderDecidable 10 h2_8_2_labels 7
  decide

theorem h2_8_2_rooted : RootedAlphaSpider 8 2 :=
  rootedAlphaSpider_of_finite h2_8_2_certificate (by decide)

def h2_8_3_labels : Fin 16 → ℕ := ![3, 10, 5, 12, 4, 9, 6, 8, 7, 11, 1, 15, 0, 13, 2, 14]

theorem h2_8_3_certificate : FiniteAlphaSpider 11 h2_8_3_labels 7 := by
  let _ := finiteAlphaSpiderDecidable 11 h2_8_3_labels 7
  decide

theorem h2_8_3_rooted : RootedAlphaSpider 8 3 :=
  rootedAlphaSpider_of_finite h2_8_3_certificate (by decide)

def h2_8_4_labels : Fin 17 → ℕ := ![7, 9, 8, 10, 6, 12, 3, 13, 5, 11, 4, 15, 0, 16, 2, 14, 1]

theorem h2_8_4_certificate : FiniteAlphaSpider 12 h2_8_4_labels 8 := by
  let _ := finiteAlphaSpiderDecidable 12 h2_8_4_labels 8
  decide

theorem h2_8_4_rooted : RootedAlphaSpider 8 4 :=
  rootedAlphaSpider_of_finite h2_8_4_certificate (by decide)

def h2_8_5_labels : Fin 18 → ℕ := ![7, 9, 8, 11, 6, 10, 4, 12, 5, 14, 1, 17, 0, 15, 3, 13, 2, 16]

theorem h2_8_5_certificate : FiniteAlphaSpider 13 h2_8_5_labels 8 := by
  let _ := finiteAlphaSpiderDecidable 13 h2_8_5_labels 8
  decide

theorem h2_8_5_rooted : RootedAlphaSpider 8 5 :=
  rootedAlphaSpider_of_finite h2_8_5_certificate (by decide)

def h2_8_6_labels : Fin 19 → ℕ := ![9, 16, 4, 11, 6, 10, 7, 13, 5, 14, 3, 18, 0, 17, 1, 15, 2, 12, 8]

theorem h2_8_6_certificate : FiniteAlphaSpider 14 h2_8_6_labels 9 := by
  let _ := finiteAlphaSpiderDecidable 14 h2_8_6_labels 9
  decide

theorem h2_8_6_rooted : RootedAlphaSpider 8 6 :=
  rootedAlphaSpider_of_finite h2_8_6_certificate (by decide)

def h2_8_7_labels : Fin 20 → ℕ := ![8, 10, 9, 11, 6, 12, 4, 15, 2, 16, 1, 18, 0, 19, 3, 13, 7, 14, 5, 17]

theorem h2_8_7_certificate : FiniteAlphaSpider 15 h2_8_7_labels 9 := by
  let _ := finiteAlphaSpiderDecidable 15 h2_8_7_labels 9
  decide

theorem h2_8_7_rooted : RootedAlphaSpider 8 7 :=
  rootedAlphaSpider_of_finite h2_8_7_certificate (by decide)

def h2_8_8_labels : Fin 21 → ℕ := ![10, 11, 9, 13, 8, 14, 5, 12, 6, 16, 4, 20, 0, 19, 1, 18, 7, 15, 2, 17, 3]

theorem h2_8_8_certificate : FiniteAlphaSpider 16 h2_8_8_labels 10 := by
  let _ := finiteAlphaSpiderDecidable 16 h2_8_8_labels 10
  decide

theorem h2_8_8_rooted : RootedAlphaSpider 8 8 :=
  rootedAlphaSpider_of_finite h2_8_8_certificate (by decide)

def h2_8_9_labels : Fin 22 → ℕ := ![10, 11, 6, 13, 7, 12, 8, 15, 5, 20, 1, 21, 0, 18, 9, 17, 4, 16, 2, 19, 3, 14]

theorem h2_8_9_certificate : FiniteAlphaSpider 17 h2_8_9_labels 10 := by
  let _ := finiteAlphaSpiderDecidable 17 h2_8_9_labels 10
  decide

theorem h2_8_9_rooted : RootedAlphaSpider 8 9 :=
  rootedAlphaSpider_of_finite h2_8_9_certificate (by decide)

def h2_8_10_labels : Fin 23 → ℕ := ![11, 12, 9, 16, 7, 13, 3, 21, 2, 19, 4, 20, 0, 22, 1, 15, 8, 14, 10, 18, 5, 17, 6]

theorem h2_8_10_certificate : FiniteAlphaSpider 18 h2_8_10_labels 11 := by
  let _ := finiteAlphaSpiderDecidable 18 h2_8_10_labels 11
  decide

theorem h2_8_10_rooted : RootedAlphaSpider 8 10 :=
  rootedAlphaSpider_of_finite h2_8_10_certificate (by decide)

def h2_8_11_labels : Fin 24 → ℕ := ![11, 12, 9, 17, 4, 13, 3, 21, 2, 19, 5, 20, 0, 23, 1, 22, 6, 18, 7, 16, 8, 15, 10, 14]

theorem h2_8_11_certificate : FiniteAlphaSpider 19 h2_8_11_labels 11 := by
  let _ := finiteAlphaSpiderDecidable 19 h2_8_11_labels 11
  decide

theorem h2_8_11_rooted : RootedAlphaSpider 8 11 :=
  rootedAlphaSpider_of_finite h2_8_11_certificate (by decide)

def h2_8_12_labels : Fin 25 → ℕ := ![1, 21, 3, 20, 4, 22, 7, 14, 12, 13, 10, 23, 0, 24, 2, 19, 5, 16, 11, 15, 9, 17, 8, 18, 6]

theorem h2_8_12_certificate : FiniteAlphaSpider 20 h2_8_12_labels 12 := by
  let _ := finiteAlphaSpiderDecidable 20 h2_8_12_labels 12
  decide

theorem h2_8_12_rooted : RootedAlphaSpider 8 12 :=
  rootedAlphaSpider_of_finite h2_8_12_certificate (by decide)

def h2_8_13_labels : Fin 26 → ℕ := ![8, 22, 3, 18, 7, 14, 12, 13, 10, 19, 6, 24, 0, 25, 2, 23, 1, 21, 4, 20, 5, 17, 9, 16, 11, 15]

theorem h2_8_13_certificate : FiniteAlphaSpider 21 h2_8_13_labels 12 := by
  let _ := finiteAlphaSpiderDecidable 21 h2_8_13_labels 12
  decide

theorem h2_8_13_rooted : RootedAlphaSpider 8 13 :=
  rootedAlphaSpider_of_finite h2_8_13_certificate (by decide)

def h2_8_14_labels : Fin 27 → ℕ := ![6, 20, 3, 21, 5, 24, 4, 23, 2, 25, 1, 26, 0, 22, 9, 18, 10, 17, 7, 19, 8, 14, 13, 15, 12, 16, 11]

theorem h2_8_14_certificate : FiniteAlphaSpider 22 h2_8_14_labels 13 := by
  let _ := finiteAlphaSpiderDecidable 22 h2_8_14_labels 13
  decide

theorem h2_8_14_rooted : RootedAlphaSpider 8 14 :=
  rootedAlphaSpider_of_finite h2_8_14_certificate (by decide)

def h2_8_15_labels : Fin 28 → ℕ := ![13, 23, 8, 15, 10, 14, 11, 17, 6, 24, 1, 27, 0, 25, 3, 22, 2, 26, 5, 18, 9, 16, 12, 20, 4, 21, 7, 19]

theorem h2_8_15_certificate : FiniteAlphaSpider 23 h2_8_15_labels 13 := by
  let _ := finiteAlphaSpiderDecidable 23 h2_8_15_labels 13
  decide

theorem h2_8_15_rooted : RootedAlphaSpider 8 15 :=
  rootedAlphaSpider_of_finite h2_8_15_certificate (by decide)

def h2_8_16_labels : Fin 29 → ℕ := ![4, 24, 6, 23, 7, 25, 3, 26, 2, 27, 1, 28, 0, 15, 14, 16, 13, 17, 12, 18, 11, 19, 10, 20, 9, 21, 8, 22, 5]

theorem h2_8_16_certificate : FiniteAlphaSpider 24 h2_8_16_labels 14 := by
  let _ := finiteAlphaSpiderDecidable 24 h2_8_16_labels 14
  decide

theorem h2_8_16_rooted : RootedAlphaSpider 8 16 :=
  rootedAlphaSpider_of_finite h2_8_16_certificate (by decide)

def h2_9_3_labels : Fin 17 → ℕ := ![9, 7, 8, 6, 10, 4, 11, 5, 13, 3, 12, 1, 16, 0, 14, 2, 15]

theorem h2_9_3_certificate : FiniteAlphaSpider 12 h2_9_3_labels 7 := by
  let _ := finiteAlphaSpiderDecidable 12 h2_9_3_labels 7
  decide

theorem h2_9_3_rooted : RootedAlphaSpider 9 3 :=
  rootedAlphaSpider_of_finite h2_9_3_certificate (by decide)

def h2_9_4_labels : Fin 18 → ℕ := ![9, 8, 11, 7, 12, 1, 15, 4, 10, 6, 13, 3, 16, 0, 17, 2, 14, 5]

theorem h2_9_4_certificate : FiniteAlphaSpider 13 h2_9_4_labels 8 := by
  let _ := finiteAlphaSpiderDecidable 13 h2_9_4_labels 8
  decide

theorem h2_9_4_rooted : RootedAlphaSpider 9 4 :=
  rootedAlphaSpider_of_finite h2_9_4_certificate (by decide)

def h2_9_5_labels : Fin 19 → ℕ := ![9, 8, 11, 3, 13, 7, 16, 4, 15, 2, 17, 1, 18, 0, 14, 6, 10, 5, 12]

theorem h2_9_5_certificate : FiniteAlphaSpider 14 h2_9_5_labels 8 := by
  let _ := finiteAlphaSpiderDecidable 14 h2_9_5_labels 8
  decide

theorem h2_9_5_rooted : RootedAlphaSpider 9 5 :=
  rootedAlphaSpider_of_finite h2_9_5_certificate (by decide)

def h2_9_6_labels : Fin 20 → ℕ := ![14, 4, 17, 7, 12, 8, 11, 9, 10, 6, 15, 3, 19, 0, 18, 1, 16, 2, 13, 5]

theorem h2_9_6_certificate : FiniteAlphaSpider 15 h2_9_6_labels 9 := by
  let _ := finiteAlphaSpiderDecidable 15 h2_9_6_labels 9
  decide

theorem h2_9_6_rooted : RootedAlphaSpider 9 6 :=
  rootedAlphaSpider_of_finite h2_9_6_certificate (by decide)

def h2_9_7_labels : Fin 21 → ℕ := ![11, 6, 15, 4, 14, 9, 10, 7, 13, 5, 17, 1, 20, 0, 18, 3, 16, 2, 19, 8, 12]

theorem h2_9_7_certificate : FiniteAlphaSpider 16 h2_9_7_labels 9 := by
  let _ := finiteAlphaSpiderDecidable 16 h2_9_7_labels 9
  decide

theorem h2_9_7_rooted : RootedAlphaSpider 9 7 :=
  rootedAlphaSpider_of_finite h2_9_7_certificate (by decide)

def h2_9_8_labels : Fin 22 → ℕ := ![11, 8, 12, 9, 14, 10, 16, 7, 15, 5, 18, 2, 21, 0, 20, 3, 17, 6, 13, 1, 19, 4]

theorem h2_9_8_certificate : FiniteAlphaSpider 17 h2_9_8_labels 10 := by
  let _ := finiteAlphaSpiderDecidable 17 h2_9_8_labels 10
  decide

theorem h2_9_8_rooted : RootedAlphaSpider 9 8 :=
  rootedAlphaSpider_of_finite h2_9_8_certificate (by decide)

def h2_9_9_labels : Fin 23 → ℕ := ![11, 10, 13, 9, 16, 1, 20, 4, 17, 6, 18, 3, 21, 0, 22, 2, 19, 5, 14, 8, 12, 7, 15]

theorem h2_9_9_certificate : FiniteAlphaSpider 18 h2_9_9_labels 10 := by
  let _ := finiteAlphaSpiderDecidable 18 h2_9_9_labels 10
  decide

theorem h2_9_9_rooted : RootedAlphaSpider 9 9 :=
  rootedAlphaSpider_of_finite h2_9_9_certificate (by decide)

def h2_9_10_labels : Fin 24 → ℕ := ![12, 11, 13, 9, 16, 8, 14, 3, 20, 2, 22, 1, 23, 0, 19, 10, 15, 7, 17, 4, 18, 6, 21, 5]

theorem h2_9_10_certificate : FiniteAlphaSpider 19 h2_9_10_labels 11 := by
  let _ := finiteAlphaSpiderDecidable 19 h2_9_10_labels 11
  decide

theorem h2_9_10_rooted : RootedAlphaSpider 9 10 :=
  rootedAlphaSpider_of_finite h2_9_10_certificate (by decide)

def h2_9_11_labels : Fin 25 → ℕ := ![13, 11, 12, 7, 15, 10, 14, 9, 16, 4, 23, 1, 24, 0, 21, 6, 17, 8, 18, 5, 19, 3, 20, 2, 22]

theorem h2_9_11_certificate : FiniteAlphaSpider 20 h2_9_11_labels 11 := by
  let _ := finiteAlphaSpiderDecidable 20 h2_9_11_labels 11
  decide

theorem h2_9_11_rooted : RootedAlphaSpider 9 11 :=
  rootedAlphaSpider_of_finite h2_9_11_certificate (by decide)

def h2_9_12_labels : Fin 26 → ℕ := ![23, 4, 21, 1, 22, 3, 19, 9, 14, 12, 13, 10, 24, 0, 25, 2, 20, 5, 18, 6, 17, 11, 15, 8, 16, 7]

theorem h2_9_12_certificate : FiniteAlphaSpider 21 h2_9_12_labels 12 := by
  let _ := finiteAlphaSpiderDecidable 21 h2_9_12_labels 12
  decide

theorem h2_9_12_rooted : RootedAlphaSpider 9 12 :=
  rootedAlphaSpider_of_finite h2_9_12_certificate (by decide)

def h2_9_13_labels : Fin 27 → ℕ := ![13, 7, 21, 11, 14, 12, 16, 8, 18, 9, 20, 1, 26, 0, 24, 4, 19, 6, 22, 5, 23, 2, 25, 3, 15, 10, 17]

theorem h2_9_13_certificate : FiniteAlphaSpider 22 h2_9_13_labels 12 := by
  let _ := finiteAlphaSpiderDecidable 22 h2_9_13_labels 12
  decide

theorem h2_9_13_rooted : RootedAlphaSpider 9 13 :=
  rootedAlphaSpider_of_finite h2_9_13_certificate (by decide)

def h2_9_14_labels : Fin 28 → ℕ := ![18, 6, 22, 9, 20, 5, 24, 1, 25, 3, 23, 2, 27, 0, 26, 8, 16, 11, 17, 7, 21, 4, 19, 12, 15, 13, 14, 10]

theorem h2_9_14_certificate : FiniteAlphaSpider 23 h2_9_14_labels 13 := by
  let _ := finiteAlphaSpiderDecidable 23 h2_9_14_labels 13
  decide

theorem h2_9_14_rooted : RootedAlphaSpider 9 14 :=
  rootedAlphaSpider_of_finite h2_9_14_certificate (by decide)

def h2_9_15_labels : Fin 29 → ℕ := ![14, 13, 17, 12, 15, 9, 16, 10, 18, 8, 21, 3, 25, 0, 28, 1, 27, 4, 19, 7, 23, 2, 26, 6, 20, 11, 22, 5, 24]

theorem h2_9_15_certificate : FiniteAlphaSpider 24 h2_9_15_labels 13 := by
  let _ := finiteAlphaSpiderDecidable 24 h2_9_15_labels 13
  decide

theorem h2_9_15_rooted : RootedAlphaSpider 9 15 :=
  rootedAlphaSpider_of_finite h2_9_15_certificate (by decide)

def h2_9_16_labels : Fin 30 → ℕ := ![27, 2, 21, 3, 25, 6, 20, 12, 15, 14, 16, 10, 26, 0, 29, 1, 28, 5, 23, 8, 17, 13, 18, 11, 22, 9, 19, 7, 24, 4]

theorem h2_9_16_certificate : FiniteAlphaSpider 25 h2_9_16_labels 14 := by
  let _ := finiteAlphaSpiderDecidable 25 h2_9_16_labels 14
  decide

theorem h2_9_16_rooted : RootedAlphaSpider 9 16 :=
  rootedAlphaSpider_of_finite h2_9_16_certificate (by decide)

def h2_10_5_labels : Fin 20 → ℕ := ![6, 12, 7, 16, 3, 10, 9, 11, 8, 15, 4, 18, 2, 17, 0, 19, 1, 13, 5, 14]

theorem h2_10_5_certificate : FiniteAlphaSpider 15 h2_10_5_labels 9 := by
  let _ := finiteAlphaSpiderDecidable 15 h2_10_5_labels 9
  decide

theorem h2_10_5_rooted : RootedAlphaSpider 10 5 :=
  rootedAlphaSpider_of_finite h2_10_5_certificate (by decide)

def h2_10_6_labels : Fin 21 → ℕ := ![7, 15, 5, 16, 3, 12, 8, 14, 2, 18, 4, 19, 1, 20, 0, 17, 6, 13, 10, 11, 9]

theorem h2_10_6_certificate : FiniteAlphaSpider 16 h2_10_6_labels 10 := by
  let _ := finiteAlphaSpiderDecidable 16 h2_10_6_labels 10
  decide

theorem h2_10_6_rooted : RootedAlphaSpider 10 6 :=
  rootedAlphaSpider_of_finite h2_10_6_certificate (by decide)

def h2_10_7_labels : Fin 22 → ℕ := ![6, 13, 8, 15, 7, 12, 9, 11, 10, 14, 4, 18, 1, 21, 0, 19, 3, 16, 5, 17, 2, 20]

theorem h2_10_7_certificate : FiniteAlphaSpider 17 h2_10_7_labels 10 := by
  let _ := finiteAlphaSpiderDecidable 17 h2_10_7_labels 10
  decide

theorem h2_10_7_rooted : RootedAlphaSpider 10 7 :=
  rootedAlphaSpider_of_finite h2_10_7_certificate (by decide)

def h2_10_8_labels : Fin 23 → ℕ := ![9, 14, 10, 16, 8, 12, 11, 13, 7, 17, 5, 18, 3, 19, 0, 22, 1, 21, 4, 15, 6, 20, 2]

theorem h2_10_8_certificate : FiniteAlphaSpider 18 h2_10_8_labels 11 := by
  let _ := finiteAlphaSpiderDecidable 18 h2_10_8_labels 11
  decide

theorem h2_10_8_rooted : RootedAlphaSpider 10 8 :=
  rootedAlphaSpider_of_finite h2_10_8_certificate (by decide)

def h2_10_9_labels : Fin 24 → ℕ := ![8, 15, 7, 18, 2, 17, 6, 19, 5, 20, 3, 21, 1, 22, 0, 23, 4, 16, 10, 14, 9, 12, 11, 13]

theorem h2_10_9_certificate : FiniteAlphaSpider 19 h2_10_9_labels 11 := by
  let _ := finiteAlphaSpiderDecidable 19 h2_10_9_labels 11
  decide

theorem h2_10_9_rooted : RootedAlphaSpider 10 9 :=
  rootedAlphaSpider_of_finite h2_10_9_certificate (by decide)

def h2_10_10_labels : Fin 25 → ℕ := ![11, 13, 12, 14, 10, 16, 8, 15, 9, 18, 5, 21, 2, 24, 0, 23, 3, 20, 6, 17, 7, 19, 4, 22, 1]

theorem h2_10_10_certificate : FiniteAlphaSpider 20 h2_10_10_labels 12 := by
  let _ := finiteAlphaSpiderDecidable 20 h2_10_10_labels 12
  decide

theorem h2_10_10_rooted : RootedAlphaSpider 10 10 :=
  rootedAlphaSpider_of_finite h2_10_10_certificate (by decide)

def h2_10_11_labels : Fin 26 → ℕ := ![11, 15, 9, 16, 7, 14, 12, 13, 5, 21, 3, 24, 1, 25, 0, 22, 2, 19, 8, 23, 4, 17, 10, 20, 6, 18]

theorem h2_10_11_certificate : FiniteAlphaSpider 21 h2_10_11_labels 12 := by
  let _ := finiteAlphaSpiderDecidable 21 h2_10_11_labels 12
  decide

theorem h2_10_11_rooted : RootedAlphaSpider 10 11 :=
  rootedAlphaSpider_of_finite h2_10_11_certificate (by decide)

def h2_10_12_labels : Fin 27 → ℕ := ![12, 14, 13, 16, 11, 15, 9, 17, 10, 19, 6, 22, 3, 25, 0, 26, 2, 23, 5, 20, 8, 18, 7, 21, 4, 24, 1]

theorem h2_10_12_certificate : FiniteAlphaSpider 22 h2_10_12_labels 13 := by
  let _ := finiteAlphaSpiderDecidable 22 h2_10_12_labels 13
  decide

theorem h2_10_12_rooted : RootedAlphaSpider 10 12 :=
  rootedAlphaSpider_of_finite h2_10_12_certificate (by decide)

def h2_10_13_labels : Fin 28 → ℕ := ![10, 17, 9, 15, 11, 16, 13, 14, 12, 21, 6, 20, 3, 27, 0, 26, 1, 22, 4, 23, 7, 19, 8, 18, 5, 25, 2, 24]

theorem h2_10_13_certificate : FiniteAlphaSpider 23 h2_10_13_labels 13 := by
  let _ := finiteAlphaSpiderDecidable 23 h2_10_13_labels 13
  decide

theorem h2_10_13_rooted : RootedAlphaSpider 10 13 :=
  rootedAlphaSpider_of_finite h2_10_13_certificate (by decide)

def h2_10_14_labels : Fin 29 → ℕ := ![12, 17, 13, 18, 11, 15, 14, 16, 8, 23, 5, 24, 1, 27, 0, 28, 3, 25, 4, 21, 7, 20, 9, 19, 10, 22, 6, 26, 2]

theorem h2_10_14_certificate : FiniteAlphaSpider 24 h2_10_14_labels 14 := by
  let _ := finiteAlphaSpiderDecidable 24 h2_10_14_labels 14
  decide

theorem h2_10_14_rooted : RootedAlphaSpider 10 14 :=
  rootedAlphaSpider_of_finite h2_10_14_certificate (by decide)

def h2_10_15_labels : Fin 30 → ℕ := ![5, 22, 7, 24, 6, 25, 4, 26, 3, 27, 2, 28, 1, 29, 0, 16, 14, 15, 12, 18, 13, 17, 10, 21, 8, 20, 11, 19, 9, 23]

theorem h2_10_15_certificate : FiniteAlphaSpider 25 h2_10_15_labels 14 := by
  let _ := finiteAlphaSpiderDecidable 25 h2_10_15_labels 14
  decide

theorem h2_10_15_rooted : RootedAlphaSpider 10 15 :=
  rootedAlphaSpider_of_finite h2_10_15_certificate (by decide)

def h2_10_16_labels : Fin 31 → ℕ := ![14, 18, 12, 22, 7, 19, 9, 23, 11, 20, 13, 16, 15, 17, 0, 30, 1, 29, 2, 28, 3, 27, 4, 26, 5, 25, 6, 24, 8, 21, 10]

theorem h2_10_16_certificate : FiniteAlphaSpider 26 h2_10_16_labels 15 := by
  let _ := finiteAlphaSpiderDecidable 26 h2_10_16_labels 15
  decide

theorem h2_10_16_rooted : RootedAlphaSpider 10 16 :=
  rootedAlphaSpider_of_finite h2_10_16_certificate (by decide)

def h2_10_17_labels : Fin 32 → ℕ := ![6, 22, 9, 25, 7, 23, 8, 28, 3, 29, 2, 30, 1, 31, 0, 24, 12, 16, 15, 17, 14, 21, 10, 20, 11, 19, 13, 18, 4, 27, 5, 26]

theorem h2_10_17_certificate : FiniteAlphaSpider 27 h2_10_17_labels 15 := by
  let _ := finiteAlphaSpiderDecidable 27 h2_10_17_labels 15
  decide

theorem h2_10_17_rooted : RootedAlphaSpider 10 17 :=
  rootedAlphaSpider_of_finite h2_10_17_certificate (by decide)

def h2_10_18_labels : Fin 33 → ℕ := ![15, 17, 16, 19, 14, 18, 12, 22, 9, 25, 6, 28, 3, 31, 0, 32, 2, 29, 5, 26, 8, 23, 11, 20, 13, 21, 10, 24, 7, 27, 4, 30, 1]

theorem h2_10_18_certificate : FiniteAlphaSpider 28 h2_10_18_labels 16 := by
  let _ := finiteAlphaSpiderDecidable 28 h2_10_18_labels 16
  decide

theorem h2_10_18_rooted : RootedAlphaSpider 10 18 :=
  rootedAlphaSpider_of_finite h2_10_18_certificate (by decide)

def h2_11_7_labels : Fin 23 → ℕ := ![12, 9, 16, 8, 14, 10, 11, 6, 18, 7, 17, 3, 19, 1, 22, 0, 20, 5, 13, 4, 21, 2, 15]

theorem h2_11_7_certificate : FiniteAlphaSpider 18 h2_11_7_labels 10 := by
  let _ := finiteAlphaSpiderDecidable 18 h2_11_7_labels 10
  decide

theorem h2_11_7_rooted : RootedAlphaSpider 11 7 :=
  rootedAlphaSpider_of_finite h2_11_7_certificate (by decide)

def h2_11_8_labels : Fin 24 → ℕ := ![19, 8, 18, 5, 17, 6, 14, 9, 16, 7, 13, 10, 12, 11, 15, 0, 23, 1, 22, 2, 21, 3, 20, 4]

theorem h2_11_8_certificate : FiniteAlphaSpider 19 h2_11_8_labels 11 := by
  let _ := finiteAlphaSpiderDecidable 19 h2_11_8_labels 11
  decide

theorem h2_11_8_rooted : RootedAlphaSpider 11 8 :=
  rootedAlphaSpider_of_finite h2_11_8_certificate (by decide)

def h2_11_9_labels : Fin 25 → ℕ := ![17, 6, 19, 5, 20, 8, 18, 4, 21, 3, 22, 2, 23, 1, 24, 0, 16, 9, 12, 11, 13, 7, 15, 10, 14]

theorem h2_11_9_certificate : FiniteAlphaSpider 20 h2_11_9_labels 11 := by
  let _ := finiteAlphaSpiderDecidable 20 h2_11_9_labels 11
  decide

theorem h2_11_9_rooted : RootedAlphaSpider 11 9 :=
  rootedAlphaSpider_of_finite h2_11_9_certificate (by decide)

def h2_11_10_labels : Fin 26 → ℕ := ![14, 12, 13, 10, 15, 11, 17, 8, 16, 9, 19, 5, 22, 2, 25, 0, 24, 3, 21, 6, 18, 7, 20, 4, 23, 1]

theorem h2_11_10_certificate : FiniteAlphaSpider 21 h2_11_10_labels 12 := by
  let _ := finiteAlphaSpiderDecidable 21 h2_11_10_labels 12
  decide

theorem h2_11_10_rooted : RootedAlphaSpider 11 10 :=
  rootedAlphaSpider_of_finite h2_11_10_certificate (by decide)

def h2_11_11_labels : Fin 27 → ℕ := ![14, 12, 13, 11, 16, 10, 18, 9, 15, 8, 19, 7, 17, 4, 25, 0, 26, 2, 22, 3, 21, 5, 20, 6, 23, 1, 24]

theorem h2_11_11_certificate : FiniteAlphaSpider 22 h2_11_11_labels 12 := by
  let _ := finiteAlphaSpiderDecidable 22 h2_11_11_labels 12
  decide

theorem h2_11_11_rooted : RootedAlphaSpider 11 11 :=
  rootedAlphaSpider_of_finite h2_11_11_certificate (by decide)

def h2_11_12_labels : Fin 28 → ℕ := ![20, 9, 19, 7, 21, 8, 17, 10, 18, 12, 16, 11, 14, 13, 15, 0, 27, 1, 26, 2, 25, 3, 24, 4, 23, 5, 22, 6]

theorem h2_11_12_certificate : FiniteAlphaSpider 23 h2_11_12_labels 13 := by
  let _ := finiteAlphaSpiderDecidable 23 h2_11_12_labels 13
  decide

theorem h2_11_12_rooted : RootedAlphaSpider 11 12 :=
  rootedAlphaSpider_of_finite h2_11_12_certificate (by decide)

def h2_11_13_labels : Fin 29 → ℕ := ![20, 6, 24, 4, 23, 7, 22, 5, 25, 3, 26, 2, 27, 1, 28, 0, 21, 9, 17, 12, 16, 10, 19, 8, 18, 11, 14, 13, 15]

theorem h2_11_13_certificate : FiniteAlphaSpider 24 h2_11_13_labels 13 := by
  let _ := finiteAlphaSpiderDecidable 24 h2_11_13_labels 13
  decide

theorem h2_11_13_rooted : RootedAlphaSpider 11 13 :=
  rootedAlphaSpider_of_finite h2_11_13_certificate (by decide)

def h2_11_14_labels : Fin 30 → ℕ := ![21, 6, 23, 9, 20, 8, 18, 11, 17, 12, 16, 13, 15, 14, 22, 0, 29, 1, 28, 2, 27, 3, 26, 10, 19, 5, 24, 4, 25, 7]

theorem h2_11_14_certificate : FiniteAlphaSpider 25 h2_11_14_labels 14 := by
  let _ := finiteAlphaSpiderDecidable 25 h2_11_14_labels 14
  decide

theorem h2_11_14_rooted : RootedAlphaSpider 11 14 :=
  rootedAlphaSpider_of_finite h2_11_14_certificate (by decide)

def h2_11_15_labels : Fin 31 → ℕ := ![22, 5, 25, 9, 23, 7, 26, 4, 27, 3, 28, 2, 29, 1, 30, 0, 21, 10, 20, 8, 24, 6, 15, 14, 16, 13, 17, 12, 18, 11, 19]

theorem h2_11_15_certificate : FiniteAlphaSpider 26 h2_11_15_labels 14 := by
  let _ := finiteAlphaSpiderDecidable 26 h2_11_15_labels 14
  decide

theorem h2_11_15_rooted : RootedAlphaSpider 11 15 :=
  rootedAlphaSpider_of_finite h2_11_15_certificate (by decide)

def h2_11_16_labels : Fin 32 → ℕ := ![30, 3, 27, 4, 25, 2, 22, 12, 20, 13, 16, 15, 17, 11, 29, 0, 31, 1, 26, 10, 21, 8, 23, 9, 18, 14, 19, 7, 24, 5, 28, 6]

theorem h2_11_16_certificate : FiniteAlphaSpider 27 h2_11_16_labels 15 := by
  let _ := finiteAlphaSpiderDecidable 27 h2_11_16_labels 15
  decide

theorem h2_11_16_rooted : RootedAlphaSpider 11 16 :=
  rootedAlphaSpider_of_finite h2_11_16_certificate (by decide)

def h2_11_17_labels : Fin 33 → ℕ := ![18, 9, 27, 12, 20, 13, 24, 3, 26, 6, 25, 8, 22, 7, 29, 0, 32, 1, 31, 4, 28, 2, 30, 5, 21, 11, 23, 10, 17, 14, 16, 15, 19]

theorem h2_11_17_certificate : FiniteAlphaSpider 28 h2_11_17_labels 15 := by
  let _ := finiteAlphaSpiderDecidable 28 h2_11_17_labels 15
  decide

theorem h2_11_17_rooted : RootedAlphaSpider 11 17 :=
  rootedAlphaSpider_of_finite h2_11_17_certificate (by decide)

def h2_11_18_labels : Fin 34 → ℕ := ![25, 7, 30, 9, 26, 6, 27, 5, 29, 3, 28, 1, 31, 2, 33, 0, 32, 4, 24, 10, 22, 11, 20, 12, 19, 15, 21, 8, 23, 13, 18, 16, 17, 14]

theorem h2_11_18_certificate : FiniteAlphaSpider 29 h2_11_18_labels 16 := by
  let _ := finiteAlphaSpiderDecidable 29 h2_11_18_labels 16
  decide

theorem h2_11_18_rooted : RootedAlphaSpider 11 18 :=
  rootedAlphaSpider_of_finite h2_11_18_certificate (by decide)

def h2_12_9_labels : Fin 26 → ℕ := ![11, 13, 12, 15, 7, 14, 9, 18, 5, 20, 8, 19, 2, 24, 4, 23, 0, 25, 1, 22, 6, 16, 10, 17, 3, 21]

theorem h2_12_9_certificate : FiniteAlphaSpider 21 h2_12_9_labels 12 := by
  let _ := finiteAlphaSpiderDecidable 21 h2_12_9_labels 12
  decide

theorem h2_12_9_rooted : RootedAlphaSpider 12 9 :=
  rootedAlphaSpider_of_finite h2_12_9_certificate (by decide)

def h2_12_10_labels : Fin 27 → ℕ := ![12, 14, 13, 19, 9, 15, 11, 16, 10, 18, 5, 21, 7, 22, 1, 26, 0, 24, 4, 23, 6, 17, 8, 20, 2, 25, 3]

theorem h2_12_10_certificate : FiniteAlphaSpider 22 h2_12_10_labels 13 := by
  let _ := finiteAlphaSpiderDecidable 22 h2_12_10_labels 13
  decide

theorem h2_12_10_rooted : RootedAlphaSpider 12 10 :=
  rootedAlphaSpider_of_finite h2_12_10_certificate (by decide)

def h2_12_11_labels : Fin 28 → ℕ := ![4, 24, 5, 22, 6, 18, 7, 19, 9, 16, 13, 14, 12, 20, 3, 27, 0, 26, 1, 23, 2, 25, 10, 15, 11, 17, 8, 21]

theorem h2_12_11_certificate : FiniteAlphaSpider 23 h2_12_11_labels 13 := by
  let _ := finiteAlphaSpiderDecidable 23 h2_12_11_labels 13
  decide

theorem h2_12_11_rooted : RootedAlphaSpider 12 11 :=
  rootedAlphaSpider_of_finite h2_12_11_certificate (by decide)

def h2_12_12_labels : Fin 29 → ℕ := ![14, 15, 12, 18, 6, 16, 11, 20, 13, 19, 9, 17, 3, 26, 1, 27, 0, 28, 4, 22, 7, 23, 2, 24, 5, 25, 8, 21, 10]

theorem h2_12_12_certificate : FiniteAlphaSpider 24 h2_12_12_labels 14 := by
  let _ := finiteAlphaSpiderDecidable 24 h2_12_12_labels 14
  decide

theorem h2_12_12_rooted : RootedAlphaSpider 12 12 :=
  rootedAlphaSpider_of_finite h2_12_12_certificate (by decide)

def h2_12_13_labels : Fin 30 → ℕ := ![8, 22, 7, 20, 9, 21, 11, 18, 10, 19, 13, 17, 12, 15, 14, 16, 0, 29, 1, 28, 2, 27, 3, 26, 4, 25, 5, 24, 6, 23]

theorem h2_12_13_certificate : FiniteAlphaSpider 25 h2_12_13_labels 14 := by
  let _ := finiteAlphaSpiderDecidable 25 h2_12_13_labels 14
  decide

theorem h2_12_13_rooted : RootedAlphaSpider 12 13 :=
  rootedAlphaSpider_of_finite h2_12_13_certificate (by decide)

def h2_12_14_labels : Fin 31 → ℕ := ![1, 26, 3, 27, 5, 28, 4, 25, 6, 24, 7, 23, 9, 22, 2, 30, 0, 29, 14, 16, 15, 18, 11, 21, 10, 19, 13, 17, 12, 20, 8]

theorem h2_12_14_certificate : FiniteAlphaSpider 26 h2_12_14_labels 15 := by
  let _ := finiteAlphaSpiderDecidable 26 h2_12_14_labels 15
  decide

theorem h2_12_14_rooted : RootedAlphaSpider 12 14 :=
  rootedAlphaSpider_of_finite h2_12_14_certificate (by decide)

def h2_12_15_labels : Fin 32 → ℕ := ![13, 22, 8, 21, 9, 19, 12, 23, 7, 24, 11, 16, 15, 17, 14, 18, 0, 31, 1, 30, 2, 29, 3, 28, 4, 27, 5, 26, 6, 25, 10, 20]

theorem h2_12_15_certificate : FiniteAlphaSpider 27 h2_12_15_labels 15 := by
  let _ := finiteAlphaSpiderDecidable 27 h2_12_15_labels 15
  decide

theorem h2_12_15_rooted : RootedAlphaSpider 12 15 :=
  rootedAlphaSpider_of_finite h2_12_15_certificate (by decide)

def h2_12_16_labels : Fin 33 → ℕ := ![6, 25, 7, 28, 4, 23, 8, 24, 12, 21, 10, 20, 15, 19, 13, 27, 0, 32, 1, 31, 2, 30, 5, 26, 3, 29, 9, 22, 14, 17, 16, 18, 11]

theorem h2_12_16_certificate : FiniteAlphaSpider 28 h2_12_16_labels 16 := by
  let _ := finiteAlphaSpiderDecidable 28 h2_12_16_labels 16
  decide

theorem h2_12_16_rooted : RootedAlphaSpider 12 16 :=
  rootedAlphaSpider_of_finite h2_12_16_certificate (by decide)

def h2_12_17_labels : Fin 34 → ℕ := ![9, 27, 7, 28, 6, 26, 5, 29, 4, 30, 3, 31, 2, 32, 1, 33, 0, 23, 12, 22, 10, 25, 11, 24, 8, 17, 16, 18, 15, 19, 14, 20, 13, 21]

theorem h2_12_17_certificate : FiniteAlphaSpider 29 h2_12_17_labels 16 := by
  let _ := finiteAlphaSpiderDecidable 29 h2_12_17_labels 16
  decide

theorem h2_12_17_rooted : RootedAlphaSpider 12 17 :=
  rootedAlphaSpider_of_finite h2_12_17_certificate (by decide)

def h2_12_18_labels : Fin 35 → ℕ := ![2, 30, 4, 33, 3, 31, 7, 29, 6, 27, 9, 28, 11, 25, 5, 32, 0, 34, 1, 26, 15, 22, 10, 23, 8, 24, 14, 20, 16, 19, 17, 18, 13, 21, 12]

theorem h2_12_18_certificate : FiniteAlphaSpider 30 h2_12_18_labels 17 := by
  let _ := finiteAlphaSpiderDecidable 30 h2_12_18_labels 17
  decide

theorem h2_12_18_rooted : RootedAlphaSpider 12 18 :=
  rootedAlphaSpider_of_finite h2_12_18_certificate (by decide)

def h2_12_19_labels : Fin 36 → ℕ := ![13, 28, 6, 20, 12, 27, 10, 22, 17, 18, 16, 19, 15, 21, 11, 24, 0, 35, 1, 34, 2, 33, 3, 32, 4, 31, 5, 30, 7, 26, 8, 29, 9, 25, 14, 23]

theorem h2_12_19_certificate : FiniteAlphaSpider 31 h2_12_19_labels 17 := by
  let _ := finiteAlphaSpiderDecidable 31 h2_12_19_labels 17
  decide

theorem h2_12_19_rooted : RootedAlphaSpider 12 19 :=
  rootedAlphaSpider_of_finite h2_12_19_certificate (by decide)

def h2_12_20_labels : Fin 37 → ℕ := ![9, 26, 12, 27, 11, 24, 13, 23, 14, 22, 10, 29, 8, 31, 2, 36, 0, 35, 3, 30, 6, 28, 15, 21, 16, 20, 17, 19, 18, 25, 5, 33, 7, 32, 1, 34, 4]

theorem h2_12_20_certificate : FiniteAlphaSpider 32 h2_12_20_labels 18 := by
  let _ := finiteAlphaSpiderDecidable 32 h2_12_20_labels 18
  decide

theorem h2_12_20_rooted : RootedAlphaSpider 12 20 :=
  rootedAlphaSpider_of_finite h2_12_20_certificate (by decide)

def h2_13_11_labels : Fin 29 → ℕ := ![26, 1, 25, 4, 23, 3, 24, 6, 19, 9, 15, 11, 16, 13, 14, 12, 27, 0, 28, 2, 22, 5, 21, 7, 18, 10, 17, 8, 20]

theorem h2_13_11_certificate : FiniteAlphaSpider 24 h2_13_11_labels 13 := by
  let _ := finiteAlphaSpiderDecidable 24 h2_13_11_labels 13
  decide

theorem h2_13_11_rooted : RootedAlphaSpider 13 11 :=
  rootedAlphaSpider_of_finite h2_13_11_certificate (by decide)

def h2_13_12_labels : Fin 30 → ℕ := ![15, 14, 17, 13, 18, 11, 19, 8, 22, 6, 26, 3, 25, 1, 27, 2, 29, 0, 28, 7, 20, 10, 16, 9, 24, 12, 21, 4, 23, 5]

theorem h2_13_12_certificate : FiniteAlphaSpider 25 h2_13_12_labels 14 := by
  let _ := finiteAlphaSpiderDecidable 25 h2_13_12_labels 14
  decide

theorem h2_13_12_rooted : RootedAlphaSpider 13 12 :=
  rootedAlphaSpider_of_finite h2_13_12_certificate (by decide)

def h2_13_13_labels : Fin 31 → ℕ := ![19, 8, 20, 12, 16, 10, 18, 13, 15, 14, 17, 11, 21, 7, 26, 1, 29, 0, 30, 3, 27, 5, 23, 6, 22, 9, 24, 4, 25, 2, 28]

theorem h2_13_13_certificate : FiniteAlphaSpider 26 h2_13_13_labels 14 := by
  let _ := finiteAlphaSpiderDecidable 26 h2_13_13_labels 14
  decide

theorem h2_13_13_rooted : RootedAlphaSpider 13 13 :=
  rootedAlphaSpider_of_finite h2_13_13_certificate (by decide)

def h2_13_14_labels : Fin 32 → ℕ := ![17, 15, 16, 14, 19, 13, 20, 11, 21, 7, 24, 6, 26, 5, 28, 4, 29, 0, 31, 1, 27, 8, 23, 12, 18, 10, 22, 9, 25, 3, 30, 2]

theorem h2_13_14_certificate : FiniteAlphaSpider 27 h2_13_14_labels 15 := by
  let _ := finiteAlphaSpiderDecidable 27 h2_13_14_labels 15
  decide

theorem h2_13_14_rooted : RootedAlphaSpider 13 14 :=
  rootedAlphaSpider_of_finite h2_13_14_certificate (by decide)

def h2_13_15_labels : Fin 33 → ℕ := ![19, 11, 22, 12, 21, 13, 18, 14, 17, 15, 16, 2, 30, 6, 28, 3, 29, 0, 32, 1, 31, 4, 27, 8, 20, 10, 23, 7, 25, 5, 26, 9, 24]

theorem h2_13_15_certificate : FiniteAlphaSpider 28 h2_13_15_labels 15 := by
  let _ := finiteAlphaSpiderDecidable 28 h2_13_15_labels 15
  decide

theorem h2_13_15_rooted : RootedAlphaSpider 13 15 :=
  rootedAlphaSpider_of_finite h2_13_15_certificate (by decide)

def h2_13_16_labels : Fin 34 → ℕ := ![25, 9, 26, 7, 27, 6, 28, 5, 29, 4, 30, 3, 31, 2, 32, 1, 33, 0, 21, 13, 20, 14, 19, 15, 18, 16, 17, 8, 23, 12, 22, 10, 24, 11]

theorem h2_13_16_certificate : FiniteAlphaSpider 29 h2_13_16_labels 16 := by
  let _ := finiteAlphaSpiderDecidable 29 h2_13_16_labels 16
  decide

theorem h2_13_16_rooted : RootedAlphaSpider 13 16 :=
  rootedAlphaSpider_of_finite h2_13_16_certificate (by decide)

def h2_13_17_labels : Fin 35 → ℕ := ![19, 11, 21, 10, 24, 14, 18, 15, 17, 16, 22, 9, 28, 5, 30, 1, 33, 0, 34, 3, 31, 7, 27, 12, 23, 6, 32, 2, 29, 8, 26, 4, 20, 13, 25]

theorem h2_13_17_certificate : FiniteAlphaSpider 30 h2_13_17_labels 16 := by
  let _ := finiteAlphaSpiderDecidable 30 h2_13_17_labels 16
  decide

theorem h2_13_17_rooted : RootedAlphaSpider 13 17 :=
  rootedAlphaSpider_of_finite h2_13_17_certificate (by decide)

def h2_13_18_labels : Fin 36 → ℕ := ![33, 2, 32, 4, 30, 5, 29, 8, 21, 15, 18, 17, 19, 14, 28, 1, 34, 0, 35, 3, 26, 10, 25, 6, 31, 9, 27, 7, 24, 12, 20, 16, 23, 13, 22, 11]

theorem h2_13_18_certificate : FiniteAlphaSpider 31 h2_13_18_labels 17 := by
  let _ := finiteAlphaSpiderDecidable 31 h2_13_18_labels 17
  decide

theorem h2_13_18_rooted : RootedAlphaSpider 13 18 :=
  rootedAlphaSpider_of_finite h2_13_18_certificate (by decide)

def h2_13_19_labels : Fin 37 → ℕ := ![19, 14, 23, 15, 21, 16, 18, 17, 28, 8, 34, 1, 32, 5, 33, 3, 35, 0, 36, 2, 31, 9, 30, 6, 24, 7, 26, 13, 20, 12, 22, 10, 25, 11, 27, 4, 29]

theorem h2_13_19_certificate : FiniteAlphaSpider 32 h2_13_19_labels 17 := by
  let _ := finiteAlphaSpiderDecidable 32 h2_13_19_labels 17
  decide

theorem h2_13_19_rooted : RootedAlphaSpider 13 19 :=
  rootedAlphaSpider_of_finite h2_13_19_certificate (by decide)

def h2_13_20_labels : Fin 38 → ℕ := ![21, 13, 27, 12, 24, 18, 19, 17, 22, 9, 28, 10, 30, 14, 20, 16, 23, 0, 37, 1, 36, 2, 35, 3, 34, 4, 33, 5, 32, 6, 31, 7, 29, 8, 25, 15, 26, 11]

theorem h2_13_20_certificate : FiniteAlphaSpider 33 h2_13_20_labels 18 := by
  let _ := finiteAlphaSpiderDecidable 33 h2_13_20_labels 18
  decide

theorem h2_13_20_rooted : RootedAlphaSpider 13 20 :=
  rootedAlphaSpider_of_finite h2_13_20_certificate (by decide)

def h2_14_13_labels : Fin 32 → ℕ := ![15, 16, 14, 20, 9, 18, 2, 28, 3, 25, 6, 23, 8, 26, 5, 29, 1, 30, 0, 31, 4, 27, 7, 21, 12, 22, 10, 17, 13, 19, 11, 24]

theorem h2_14_13_certificate : FiniteAlphaSpider 27 h2_14_13_labels 15 := by
  let _ := finiteAlphaSpiderDecidable 27 h2_14_13_labels 15
  decide

theorem h2_14_13_rooted : RootedAlphaSpider 14 13 :=
  rootedAlphaSpider_of_finite h2_14_13_certificate (by decide)

def h2_14_14_labels : Fin 33 → ℕ := ![5, 26, 8, 28, 6, 17, 16, 18, 15, 19, 14, 20, 13, 21, 12, 22, 11, 24, 0, 32, 1, 31, 2, 30, 3, 29, 4, 23, 9, 25, 10, 27, 7]

theorem h2_14_14_certificate : FiniteAlphaSpider 28 h2_14_14_labels 16 := by
  let _ := finiteAlphaSpiderDecidable 28 h2_14_14_labels 16
  decide

theorem h2_14_14_rooted : RootedAlphaSpider 14 14 :=
  rootedAlphaSpider_of_finite h2_14_14_certificate (by decide)

def h2_14_15_labels : Fin 34 → ℕ := ![11, 23, 12, 25, 9, 24, 7, 28, 5, 29, 4, 30, 3, 31, 2, 32, 1, 33, 0, 22, 13, 19, 16, 17, 15, 20, 10, 18, 14, 21, 6, 26, 8, 27]

theorem h2_14_15_certificate : FiniteAlphaSpider 29 h2_14_15_labels 16 := by
  let _ := finiteAlphaSpiderDecidable 29 h2_14_15_labels 16
  decide

theorem h2_14_15_rooted : RootedAlphaSpider 14 15 :=
  rootedAlphaSpider_of_finite h2_14_15_certificate (by decide)

def h2_14_16_labels : Fin 35 → ℕ := ![16, 18, 17, 19, 15, 21, 14, 20, 12, 22, 13, 24, 9, 27, 6, 30, 3, 33, 0, 34, 2, 31, 5, 28, 8, 25, 11, 23, 10, 26, 7, 29, 4, 32, 1]

theorem h2_14_16_certificate : FiniteAlphaSpider 30 h2_14_16_labels 17 := by
  let _ := finiteAlphaSpiderDecidable 30 h2_14_16_labels 17
  decide

theorem h2_14_16_rooted : RootedAlphaSpider 14 16 :=
  rootedAlphaSpider_of_finite h2_14_16_certificate (by decide)

def h2_14_17_labels : Fin 36 → ℕ := ![9, 20, 13, 23, 11, 27, 8, 28, 6, 29, 4, 30, 3, 32, 2, 34, 1, 35, 0, 31, 7, 24, 15, 21, 17, 18, 16, 19, 14, 22, 12, 25, 10, 26, 5, 33]

theorem h2_14_17_certificate : FiniteAlphaSpider 31 h2_14_17_labels 17 := by
  let _ := finiteAlphaSpiderDecidable 31 h2_14_17_labels 17
  decide

theorem h2_14_17_rooted : RootedAlphaSpider 14 17 :=
  rootedAlphaSpider_of_finite h2_14_17_certificate (by decide)

def h2_14_18_labels : Fin 37 → ℕ := ![3, 27, 8, 31, 6, 33, 1, 34, 5, 28, 12, 32, 10, 23, 9, 30, 4, 35, 0, 36, 2, 29, 11, 26, 15, 25, 13, 22, 17, 19, 18, 21, 14, 20, 16, 24, 7]

theorem h2_14_18_certificate : FiniteAlphaSpider 32 h2_14_18_labels 18 := by
  let _ := finiteAlphaSpiderDecidable 32 h2_14_18_labels 18
  decide

theorem h2_14_18_rooted : RootedAlphaSpider 14 18 :=
  rootedAlphaSpider_of_finite h2_14_18_certificate (by decide)

def h2_14_19_labels : Fin 38 → ℕ := ![8, 28, 9, 29, 7, 31, 6, 32, 5, 33, 4, 34, 3, 35, 2, 36, 1, 37, 0, 24, 17, 20, 18, 19, 15, 26, 11, 25, 12, 30, 14, 23, 13, 21, 16, 22, 10, 27]

theorem h2_14_19_certificate : FiniteAlphaSpider 33 h2_14_19_labels 18 := by
  let _ := finiteAlphaSpiderDecidable 33 h2_14_19_labels 18
  decide

theorem h2_14_19_rooted : RootedAlphaSpider 14 19 :=
  rootedAlphaSpider_of_finite h2_14_19_certificate (by decide)

def h2_14_20_labels : Fin 39 → ℕ := ![12, 28, 15, 29, 10, 20, 19, 21, 18, 22, 17, 23, 16, 25, 5, 34, 2, 38, 0, 37, 11, 26, 14, 24, 13, 27, 9, 30, 8, 31, 7, 32, 4, 35, 1, 36, 3, 33, 6]

theorem h2_14_20_certificate : FiniteAlphaSpider 34 h2_14_20_labels 19 := by
  let _ := finiteAlphaSpiderDecidable 34 h2_14_20_labels 19
  decide

theorem h2_14_20_rooted : RootedAlphaSpider 14 20 :=
  rootedAlphaSpider_of_finite h2_14_20_certificate (by decide)

def h2_14_21_labels : Fin 40 → ℕ := ![2, 35, 5, 38, 3, 36, 4, 33, 8, 31, 15, 21, 19, 20, 17, 28, 11, 37, 0, 39, 1, 32, 12, 25, 10, 29, 7, 34, 6, 30, 9, 27, 13, 22, 18, 23, 16, 24, 14, 26]

theorem h2_14_21_certificate : FiniteAlphaSpider 35 h2_14_21_labels 19 := by
  let _ := finiteAlphaSpiderDecidable 35 h2_14_21_labels 19
  decide

theorem h2_14_21_rooted : RootedAlphaSpider 14 21 :=
  rootedAlphaSpider_of_finite h2_14_21_certificate (by decide)

def h2_14_22_labels : Fin 41 → ℕ := ![16, 27, 9, 29, 14, 28, 11, 30, 8, 32, 12, 26, 18, 22, 19, 21, 20, 25, 0, 40, 1, 39, 2, 38, 3, 37, 4, 36, 5, 35, 6, 34, 7, 33, 10, 31, 15, 24, 17, 23, 13]

theorem h2_14_22_certificate : FiniteAlphaSpider 36 h2_14_22_labels 20 := by
  let _ := finiteAlphaSpiderDecidable 36 h2_14_22_labels 20
  decide

theorem h2_14_22_rooted : RootedAlphaSpider 14 22 :=
  rootedAlphaSpider_of_finite h2_14_22_certificate (by decide)

def h2_15_15_labels : Fin 35 → ℕ := ![29, 6, 25, 7, 28, 9, 26, 10, 23, 5, 30, 4, 31, 3, 32, 2, 33, 1, 34, 0, 24, 15, 17, 16, 19, 13, 18, 14, 21, 11, 22, 8, 20, 12, 27]

theorem h2_15_15_certificate : FiniteAlphaSpider 30 h2_15_15_labels 16 := by
  let _ := finiteAlphaSpiderDecidable 30 h2_15_15_labels 16
  decide

theorem h2_15_15_rooted : RootedAlphaSpider 15 15 :=
  rootedAlphaSpider_of_finite h2_15_15_certificate (by decide)

def h2_15_16_labels : Fin 36 → ℕ := ![24, 11, 28, 10, 26, 9, 29, 8, 27, 5, 31, 4, 32, 3, 33, 2, 34, 1, 35, 0, 25, 7, 30, 6, 18, 17, 19, 16, 20, 15, 21, 14, 22, 13, 23, 12]

theorem h2_15_16_certificate : FiniteAlphaSpider 31 h2_15_16_labels 17 := by
  let _ := finiteAlphaSpiderDecidable 31 h2_15_16_labels 17
  decide

theorem h2_15_16_rooted : RootedAlphaSpider 15 16 :=
  rootedAlphaSpider_of_finite h2_15_16_certificate (by decide)

def h2_15_17_labels : Fin 37 → ℕ := ![22, 11, 27, 10, 23, 13, 21, 14, 24, 9, 28, 7, 25, 8, 31, 5, 32, 1, 36, 0, 34, 12, 18, 17, 19, 16, 20, 15, 29, 4, 33, 3, 35, 2, 30, 6, 26]

theorem h2_15_17_certificate : FiniteAlphaSpider 32 h2_15_17_labels 17 := by
  let _ := finiteAlphaSpiderDecidable 32 h2_15_17_labels 17
  decide

theorem h2_15_17_rooted : RootedAlphaSpider 15 17 :=
  rootedAlphaSpider_of_finite h2_15_17_certificate (by decide)

def h2_15_18_labels : Fin 38 → ℕ := ![19, 18, 20, 15, 25, 16, 22, 17, 28, 10, 31, 6, 30, 8, 35, 1, 33, 2, 37, 0, 36, 3, 29, 12, 24, 5, 34, 4, 32, 9, 23, 14, 21, 13, 26, 11, 27, 7]

theorem h2_15_18_certificate : FiniteAlphaSpider 33 h2_15_18_labels 18 := by
  let _ := finiteAlphaSpiderDecidable 33 h2_15_18_labels 18
  decide

theorem h2_15_18_rooted : RootedAlphaSpider 15 18 :=
  rootedAlphaSpider_of_finite h2_15_18_certificate (by decide)

def h2_15_19_labels : Fin 39 → ℕ := ![19, 18, 22, 17, 24, 16, 21, 12, 28, 11, 34, 4, 35, 3, 36, 2, 37, 1, 38, 0, 29, 15, 23, 13, 26, 7, 27, 9, 33, 5, 32, 6, 31, 10, 25, 14, 20, 8, 30]

theorem h2_15_19_certificate : FiniteAlphaSpider 34 h2_15_19_labels 18 := by
  let _ := finiteAlphaSpiderDecidable 34 h2_15_19_labels 18
  decide

theorem h2_15_19_rooted : RootedAlphaSpider 15 19 :=
  rootedAlphaSpider_of_finite h2_15_19_certificate (by decide)

def h2_15_20_labels : Fin 40 → ℕ := ![37, 4, 33, 3, 35, 2, 32, 5, 31, 13, 22, 16, 23, 15, 28, 7, 38, 1, 39, 0, 36, 12, 26, 9, 34, 6, 29, 17, 21, 18, 20, 19, 24, 14, 25, 10, 30, 8, 27, 11]

theorem h2_15_20_certificate : FiniteAlphaSpider 35 h2_15_20_labels 19 := by
  let _ := finiteAlphaSpiderDecidable 35 h2_15_20_labels 19
  decide

theorem h2_15_20_rooted : RootedAlphaSpider 15 20 :=
  rootedAlphaSpider_of_finite h2_15_20_certificate (by decide)

def h2_15_21_labels : Fin 41 → ℕ := ![31, 7, 32, 9, 30, 8, 34, 6, 33, 4, 37, 3, 35, 5, 36, 1, 38, 2, 40, 0, 39, 19, 20, 18, 21, 17, 22, 16, 23, 15, 24, 14, 25, 13, 26, 12, 27, 11, 28, 10, 29]

theorem h2_15_21_certificate : FiniteAlphaSpider 36 h2_15_21_labels 19 := by
  let _ := finiteAlphaSpiderDecidable 36 h2_15_21_labels 19
  decide

theorem h2_15_21_rooted : RootedAlphaSpider 15 21 :=
  rootedAlphaSpider_of_finite h2_15_21_certificate (by decide)

def h2_15_22_labels : Fin 42 → ℕ := ![38, 12, 29, 7, 35, 2, 39, 4, 36, 6, 31, 9, 33, 10, 30, 15, 34, 1, 40, 0, 41, 3, 37, 8, 26, 13, 22, 20, 21, 18, 25, 17, 23, 19, 24, 14, 28, 16, 27, 11, 32, 5]

theorem h2_15_22_certificate : FiniteAlphaSpider 37 h2_15_22_labels 20 := by
  let _ := finiteAlphaSpiderDecidable 37 h2_15_22_labels 20
  decide

theorem h2_15_22_rooted : RootedAlphaSpider 15 22 :=
  rootedAlphaSpider_of_finite h2_15_22_certificate (by decide)

def h2_16_17_labels : Fin 38 → ℕ := ![18, 21, 14, 24, 15, 19, 17, 22, 9, 23, 13, 25, 4, 36, 2, 33, 7, 34, 1, 37, 0, 35, 5, 27, 16, 20, 12, 28, 11, 26, 8, 32, 3, 31, 6, 29, 10, 30]

theorem h2_16_17_certificate : FiniteAlphaSpider 33 h2_16_17_labels 18 := by
  let _ := finiteAlphaSpiderDecidable 33 h2_16_17_labels 18
  decide

theorem h2_16_17_rooted : RootedAlphaSpider 16 17 :=
  rootedAlphaSpider_of_finite h2_16_17_certificate (by decide)

def h2_16_18_labels : Fin 39 → ℕ := ![18, 24, 10, 22, 15, 27, 14, 29, 6, 35, 1, 36, 5, 32, 11, 28, 8, 30, 4, 37, 0, 38, 2, 34, 9, 33, 3, 31, 13, 25, 17, 20, 19, 21, 16, 26, 7, 23, 12]

theorem h2_16_18_certificate : FiniteAlphaSpider 34 h2_16_18_labels 19 := by
  let _ := finiteAlphaSpiderDecidable 34 h2_16_18_labels 19
  decide

theorem h2_16_18_rooted : RootedAlphaSpider 16 18 :=
  rootedAlphaSpider_of_finite h2_16_18_certificate (by decide)

def h2_16_19_labels : Fin 40 → ℕ := ![19, 21, 18, 23, 12, 20, 15, 22, 16, 28, 7, 30, 10, 27, 14, 24, 9, 36, 6, 35, 0, 39, 1, 38, 2, 34, 3, 37, 4, 29, 13, 32, 8, 26, 17, 25, 11, 33, 5, 31]

theorem h2_16_19_certificate : FiniteAlphaSpider 35 h2_16_19_labels 19 := by
  let _ := finiteAlphaSpiderDecidable 35 h2_16_19_labels 19
  decide

theorem h2_16_19_rooted : RootedAlphaSpider 16 19 :=
  rootedAlphaSpider_of_finite h2_16_19_certificate (by decide)

def h2_16_20_labels : Fin 41 → ℕ := ![16, 27, 11, 26, 17, 22, 19, 21, 20, 24, 12, 25, 18, 23, 15, 32, 10, 35, 1, 39, 0, 40, 3, 38, 2, 30, 9, 28, 14, 29, 6, 36, 5, 37, 4, 33, 13, 31, 7, 34, 8]

theorem h2_16_20_certificate : FiniteAlphaSpider 36 h2_16_20_labels 20 := by
  let _ := finiteAlphaSpiderDecidable 36 h2_16_20_labels 20
  decide

theorem h2_16_20_rooted : RootedAlphaSpider 16 20 :=
  rootedAlphaSpider_of_finite h2_16_20_certificate (by decide)

def h2_16_21_labels : Fin 42 → ℕ := ![19, 21, 20, 23, 18, 22, 16, 24, 17, 26, 13, 29, 10, 32, 7, 35, 4, 38, 1, 41, 0, 39, 3, 36, 6, 33, 9, 30, 12, 27, 15, 25, 14, 28, 11, 31, 8, 34, 5, 37, 2, 40]

theorem h2_16_21_certificate : FiniteAlphaSpider 37 h2_16_21_labels 20 := by
  let _ := finiteAlphaSpiderDecidable 37 h2_16_21_labels 20
  decide

theorem h2_16_21_rooted : RootedAlphaSpider 16 21 :=
  rootedAlphaSpider_of_finite h2_16_21_certificate (by decide)

def h2_16_22_labels : Fin 43 → ℕ := ![21, 22, 20, 25, 16, 24, 13, 28, 18, 23, 17, 30, 12, 36, 4, 38, 5, 35, 7, 42, 0, 41, 1, 40, 2, 39, 3, 32, 11, 34, 8, 33, 14, 31, 9, 29, 15, 27, 19, 26, 10, 37, 6]

theorem h2_16_22_certificate : FiniteAlphaSpider 38 h2_16_22_labels 21 := by
  let _ := finiteAlphaSpiderDecidable 38 h2_16_22_labels 21
  decide

theorem h2_16_22_rooted : RootedAlphaSpider 16 22 :=
  rootedAlphaSpider_of_finite h2_16_22_certificate (by decide)

def h2_16_23_labels : Fin 44 → ℕ := ![13, 31, 9, 33, 12, 32, 15, 24, 20, 26, 1, 41, 4, 38, 7, 37, 5, 40, 2, 43, 0, 42, 3, 39, 6, 35, 8, 36, 10, 34, 11, 27, 16, 28, 14, 29, 19, 22, 21, 23, 18, 25, 17, 30]

theorem h2_16_23_certificate : FiniteAlphaSpider 39 h2_16_23_labels 21 := by
  let _ := finiteAlphaSpiderDecidable 39 h2_16_23_labels 21
  decide

theorem h2_16_23_rooted : RootedAlphaSpider 16 23 :=
  rootedAlphaSpider_of_finite h2_16_23_certificate (by decide)

def h2_16_24_labels : Fin 45 → ℕ := ![3, 36, 10, 38, 6, 42, 4, 41, 5, 39, 8, 37, 13, 33, 11, 32, 2, 43, 1, 44, 0, 40, 22, 23, 21, 24, 20, 25, 19, 26, 18, 27, 17, 28, 16, 29, 15, 30, 14, 31, 12, 35, 7, 34, 9]

theorem h2_16_24_certificate : FiniteAlphaSpider 40 h2_16_24_labels 22 := by
  let _ := finiteAlphaSpiderDecidable 40 h2_16_24_labels 22
  decide

theorem h2_16_24_rooted : RootedAlphaSpider 16 24 :=
  rootedAlphaSpider_of_finite h2_16_24_certificate (by decide)

def h2_17_19_labels : Fin 41 → ℕ := ![26, 16, 23, 15, 24, 14, 22, 17, 21, 18, 20, 19, 25, 12, 29, 9, 32, 6, 35, 3, 38, 0, 40, 1, 37, 4, 34, 7, 31, 10, 28, 13, 27, 11, 30, 8, 33, 5, 36, 2, 39]

theorem h2_17_19_certificate : FiniteAlphaSpider 36 h2_17_19_labels 19 := by
  let _ := finiteAlphaSpiderDecidable 36 h2_17_19_labels 19
  decide

theorem h2_17_19_rooted : RootedAlphaSpider 17 19 :=
  rootedAlphaSpider_of_finite h2_17_19_certificate (by decide)

def h2_17_20_labels : Fin 42 → ℕ := ![33, 9, 31, 13, 30, 10, 35, 8, 34, 6, 36, 5, 37, 4, 38, 3, 39, 2, 40, 1, 41, 0, 29, 16, 27, 15, 24, 17, 25, 19, 23, 18, 21, 20, 22, 12, 28, 14, 32, 11, 26, 7]

theorem h2_17_20_certificate : FiniteAlphaSpider 37 h2_17_20_labels 20 := by
  let _ := finiteAlphaSpiderDecidable 37 h2_17_20_labels 20
  decide

theorem h2_17_20_rooted : RootedAlphaSpider 17 20 :=
  rootedAlphaSpider_of_finite h2_17_20_certificate (by decide)

def h2_17_21_labels : Fin 43 → ℕ := ![34, 5, 37, 10, 31, 8, 33, 11, 30, 12, 32, 9, 36, 6, 39, 3, 40, 2, 41, 1, 42, 0, 35, 7, 38, 4, 21, 20, 22, 19, 23, 18, 24, 17, 25, 16, 26, 15, 27, 14, 28, 13, 29]

theorem h2_17_21_certificate : FiniteAlphaSpider 38 h2_17_21_labels 20 := by
  let _ := finiteAlphaSpiderDecidable 38 h2_17_21_labels 20
  decide

theorem h2_17_21_rooted : RootedAlphaSpider 17 21 :=
  rootedAlphaSpider_of_finite h2_17_21_certificate (by decide)

def h2_17_22_labels : Fin 44 → ℕ := ![22, 18, 30, 20, 26, 21, 24, 19, 28, 15, 33, 8, 35, 9, 37, 7, 36, 5, 40, 2, 43, 0, 42, 3, 39, 6, 38, 4, 41, 1, 23, 16, 27, 17, 25, 11, 34, 10, 31, 14, 29, 13, 32, 12]

theorem h2_17_22_certificate : FiniteAlphaSpider 39 h2_17_22_labels 21 := by
  let _ := finiteAlphaSpiderDecidable 39 h2_17_22_labels 21
  decide

theorem h2_17_22_rooted : RootedAlphaSpider 17 22 :=
  rootedAlphaSpider_of_finite h2_17_22_certificate (by decide)

def h2_17_23_labels : Fin 45 → ℕ := ![43, 3, 39, 2, 37, 5, 38, 7, 41, 4, 32, 18, 23, 21, 22, 19, 25, 15, 34, 10, 42, 0, 44, 1, 40, 11, 27, 20, 24, 16, 29, 14, 26, 17, 28, 8, 30, 13, 31, 6, 36, 9, 35, 12, 33]

theorem h2_17_23_certificate : FiniteAlphaSpider 40 h2_17_23_labels 21 := by
  let _ := finiteAlphaSpiderDecidable 40 h2_17_23_labels 21
  decide

theorem h2_17_23_rooted : RootedAlphaSpider 17 23 :=
  rootedAlphaSpider_of_finite h2_17_23_certificate (by decide)

def h2_17_24_labels : Fin 46 → ℕ := ![26, 16, 33, 14, 34, 13, 37, 6, 42, 1, 43, 5, 38, 10, 32, 11, 36, 7, 41, 2, 45, 0, 44, 4, 39, 9, 28, 17, 31, 15, 30, 12, 35, 8, 40, 3, 29, 20, 23, 22, 24, 19, 27, 21, 25, 18]

theorem h2_17_24_certificate : FiniteAlphaSpider 41 h2_17_24_labels 22 := by
  let _ := finiteAlphaSpiderDecidable 41 h2_17_24_labels 22
  decide

theorem h2_17_24_rooted : RootedAlphaSpider 17 24 :=
  rootedAlphaSpider_of_finite h2_17_24_certificate (by decide)

def h2_18_21_labels : Fin 44 → ℕ := ![18, 27, 17, 23, 19, 25, 14, 26, 20, 22, 21, 24, 16, 31, 9, 36, 5, 37, 4, 39, 1, 43, 0, 41, 7, 32, 13, 30, 10, 33, 12, 28, 15, 29, 11, 35, 6, 34, 8, 38, 2, 42, 3, 40]

theorem h2_18_21_certificate : FiniteAlphaSpider 39 h2_18_21_labels 21 := by
  let _ := finiteAlphaSpiderDecidable 39 h2_18_21_labels 21
  decide

theorem h2_18_21_rooted : RootedAlphaSpider 18 21 :=
  rootedAlphaSpider_of_finite h2_18_21_certificate (by decide)

def h2_18_22_labels : Fin 45 → ℕ := ![16, 32, 11, 26, 17, 34, 8, 37, 7, 38, 6, 39, 5, 40, 4, 41, 3, 42, 2, 43, 1, 44, 0, 28, 20, 23, 22, 24, 19, 30, 13, 33, 9, 36, 14, 29, 15, 27, 21, 25, 18, 31, 12, 35, 10]

theorem h2_18_22_certificate : FiniteAlphaSpider 40 h2_18_22_labels 22 := by
  let _ := finiteAlphaSpiderDecidable 40 h2_18_22_labels 22
  decide

theorem h2_18_22_rooted : RootedAlphaSpider 18 22 :=
  rootedAlphaSpider_of_finite h2_18_22_certificate (by decide)

def h2_18_23_labels : Fin 46 → ℕ := ![22, 23, 19, 28, 11, 24, 21, 29, 14, 34, 9, 35, 13, 26, 17, 36, 1, 43, 4, 42, 2, 45, 0, 44, 3, 40, 8, 38, 10, 37, 6, 39, 5, 41, 12, 33, 15, 27, 16, 32, 18, 25, 20, 30, 7, 31]

theorem h2_18_23_certificate : FiniteAlphaSpider 41 h2_18_23_labels 22 := by
  let _ := finiteAlphaSpiderDecidable 41 h2_18_23_labels 22
  decide

theorem h2_18_23_rooted : RootedAlphaSpider 18 23 :=
  rootedAlphaSpider_of_finite h2_18_23_certificate (by decide)

def h2_18_24_labels : Fin 47 → ℕ := ![22, 24, 23, 25, 20, 26, 18, 29, 17, 27, 21, 28, 19, 32, 14, 36, 8, 39, 4, 43, 1, 46, 0, 44, 3, 41, 9, 38, 12, 33, 13, 30, 16, 31, 15, 34, 11, 35, 10, 37, 7, 40, 6, 42, 5, 45, 2]

theorem h2_18_24_certificate : FiniteAlphaSpider 42 h2_18_24_labels 23 := by
  let _ := finiteAlphaSpiderDecidable 42 h2_18_24_labels 23
  decide

theorem h2_18_24_rooted : RootedAlphaSpider 18 24 :=
  rootedAlphaSpider_of_finite h2_18_24_certificate (by decide)

def h2_18_25_labels : Fin 48 → ℕ := ![3, 33, 12, 44, 5, 43, 6, 40, 4, 39, 8, 41, 9, 37, 10, 36, 7, 45, 2, 46, 1, 47, 0, 42, 23, 24, 22, 25, 21, 26, 20, 27, 19, 28, 18, 29, 17, 30, 16, 31, 15, 32, 14, 34, 11, 35, 13, 38]

theorem h2_18_25_certificate : FiniteAlphaSpider 43 h2_18_25_labels 23 := by
  let _ := finiteAlphaSpiderDecidable 43 h2_18_25_labels 23
  decide

theorem h2_18_25_rooted : RootedAlphaSpider 18 25 :=
  rootedAlphaSpider_of_finite h2_18_25_certificate (by decide)

def h2_18_26_labels : Fin 49 → ℕ := ![12, 38, 8, 39, 10, 40, 9, 41, 7, 42, 6, 43, 5, 44, 4, 45, 3, 46, 2, 47, 1, 48, 0, 33, 17, 32, 15, 35, 16, 34, 13, 37, 14, 36, 11, 25, 24, 26, 23, 27, 22, 28, 21, 29, 20, 30, 19, 31, 18]

theorem h2_18_26_certificate : FiniteAlphaSpider 44 h2_18_26_labels 24 := by
  let _ := finiteAlphaSpiderDecidable 44 h2_18_26_labels 24
  decide

theorem h2_18_26_rooted : RootedAlphaSpider 18 26 :=
  rootedAlphaSpider_of_finite h2_18_26_certificate (by decide)

def h2_19_23_labels : Fin 47 → ℕ := ![23, 22, 25, 17, 33, 21, 26, 19, 27, 16, 31, 14, 35, 13, 32, 12, 30, 18, 28, 15, 29, 20, 24, 0, 46, 1, 45, 2, 44, 3, 43, 4, 42, 5, 41, 6, 40, 7, 39, 8, 38, 9, 37, 10, 36, 11, 34]

theorem h2_19_23_certificate : FiniteAlphaSpider 42 h2_19_23_labels 22 := by
  let _ := finiteAlphaSpiderDecidable 42 h2_19_23_labels 22
  decide

theorem h2_19_23_rooted : RootedAlphaSpider 19 23 :=
  rootedAlphaSpider_of_finite h2_19_23_certificate (by decide)

def h2_19_24_labels : Fin 48 → ℕ := ![24, 23, 25, 15, 37, 21, 28, 9, 41, 2, 46, 3, 44, 4, 33, 17, 35, 5, 42, 6, 40, 7, 45, 0, 47, 1, 43, 8, 39, 12, 32, 20, 26, 22, 27, 19, 29, 18, 31, 16, 30, 13, 34, 11, 36, 10, 38, 14]

theorem h2_19_24_certificate : FiniteAlphaSpider 43 h2_19_24_labels 23 := by
  let _ := finiteAlphaSpiderDecidable 43 h2_19_24_labels 23
  decide

theorem h2_19_24_rooted : RootedAlphaSpider 19 24 :=
  rootedAlphaSpider_of_finite h2_19_24_certificate (by decide)

def h2_19_25_labels : Fin 49 → ℕ := ![35, 12, 38, 10, 43, 14, 34, 17, 27, 21, 25, 20, 28, 19, 30, 18, 32, 13, 37, 7, 45, 3, 47, 0, 48, 2, 41, 9, 36, 8, 39, 4, 44, 1, 46, 5, 42, 6, 40, 11, 33, 15, 31, 16, 29, 22, 24, 23, 26]

theorem h2_19_25_certificate : FiniteAlphaSpider 44 h2_19_25_labels 23 := by
  let _ := finiteAlphaSpiderDecidable 44 h2_19_25_labels 23
  decide

theorem h2_19_25_rooted : RootedAlphaSpider 19 25 :=
  rootedAlphaSpider_of_finite h2_19_25_certificate (by decide)

def h2_19_26_labels : Fin 50 → ℕ := ![33, 16, 34, 8, 42, 14, 36, 13, 39, 2, 44, 5, 40, 10, 43, 7, 45, 4, 47, 3, 48, 1, 49, 0, 46, 6, 37, 9, 41, 12, 32, 20, 35, 11, 38, 17, 30, 22, 26, 19, 28, 23, 25, 24, 27, 21, 31, 15, 29, 18]

theorem h2_19_26_certificate : FiniteAlphaSpider 45 h2_19_26_labels 24 := by
  let _ := finiteAlphaSpiderDecidable 45 h2_19_26_labels 24
  decide

theorem h2_19_26_rooted : RootedAlphaSpider 19 26 :=
  rootedAlphaSpider_of_finite h2_19_26_certificate (by decide)

def h2_20_25_labels : Fin 50 → ℕ := ![23, 27, 21, 30, 14, 28, 20, 33, 16, 36, 15, 34, 12, 35, 17, 32, 18, 29, 19, 31, 22, 25, 24, 26, 0, 49, 1, 48, 2, 47, 3, 46, 4, 45, 5, 44, 6, 43, 7, 42, 8, 41, 9, 40, 10, 39, 11, 38, 13, 37]

theorem h2_20_25_certificate : FiniteAlphaSpider 45 h2_20_25_labels 24 := by
  let _ := finiteAlphaSpiderDecidable 45 h2_20_25_labels 24
  decide

theorem h2_20_25_rooted : RootedAlphaSpider 20 25 :=
  rootedAlphaSpider_of_finite h2_20_25_certificate (by decide)

def h2_20_26_labels : Fin 51 → ℕ := ![24, 31, 19, 29, 21, 28, 22, 36, 14, 41, 5, 49, 2, 45, 10, 40, 15, 32, 16, 35, 7, 47, 1, 50, 0, 48, 3, 44, 12, 33, 18, 27, 25, 26, 23, 34, 11, 42, 8, 46, 4, 43, 6, 39, 13, 37, 17, 30, 20, 38, 9]

theorem h2_20_26_certificate : FiniteAlphaSpider 46 h2_20_26_labels 25 := by
  let _ := finiteAlphaSpiderDecidable 46 h2_20_26_labels 25
  decide

theorem h2_20_26_rooted : RootedAlphaSpider 20 26 :=
  rootedAlphaSpider_of_finite h2_20_26_certificate (by decide)

def h2_20_27_labels : Fin 52 → ℕ := ![6, 48, 5, 43, 10, 45, 9, 36, 21, 32, 23, 28, 24, 27, 25, 26, 20, 34, 16, 37, 12, 42, 4, 49, 0, 51, 1, 47, 7, 41, 13, 33, 17, 39, 8, 40, 14, 31, 18, 30, 22, 29, 19, 38, 15, 44, 3, 50, 2, 46, 11, 35]

theorem h2_20_27_certificate : FiniteAlphaSpider 47 h2_20_27_labels 25 := by
  let _ := finiteAlphaSpiderDecidable 47 h2_20_27_labels 25
  decide

theorem h2_20_27_rooted : RootedAlphaSpider 20 27 :=
  rootedAlphaSpider_of_finite h2_20_27_certificate (by decide)

def h2_20_28_labels : Fin 53 → ℕ := ![22, 28, 24, 31, 23, 29, 26, 27, 25, 30, 20, 34, 17, 37, 14, 40, 11, 43, 8, 46, 5, 49, 2, 52, 0, 51, 3, 48, 6, 45, 9, 42, 12, 39, 15, 36, 18, 33, 21, 32, 19, 35, 16, 38, 13, 41, 10, 44, 7, 47, 4, 50, 1]

theorem h2_20_28_certificate : FiniteAlphaSpider 48 h2_20_28_labels 26 := by
  let _ := finiteAlphaSpiderDecidable 48 h2_20_28_labels 26
  decide

theorem h2_20_28_rooted : RootedAlphaSpider 20 28 :=
  rootedAlphaSpider_of_finite h2_20_28_certificate (by decide)

def h2_21_27_labels : Fin 53 → ℕ := ![30, 24, 28, 17, 34, 20, 29, 22, 27, 25, 26, 23, 31, 16, 36, 12, 43, 5, 42, 15, 41, 8, 44, 9, 49, 0, 52, 1, 51, 3, 50, 6, 45, 11, 40, 10, 38, 13, 35, 19, 37, 14, 33, 21, 32, 18, 39, 7, 48, 2, 47, 4, 46]

theorem h2_21_27_certificate : FiniteAlphaSpider 48 h2_21_27_labels 25 := by
  let _ := finiteAlphaSpiderDecidable 48 h2_21_27_labels 25
  decide

theorem h2_21_27_rooted : RootedAlphaSpider 21 27 :=
  rootedAlphaSpider_of_finite h2_21_27_certificate (by decide)

def h2_21_28_labels : Fin 54 → ℕ := ![43, 11, 42, 14, 40, 10, 44, 9, 45, 8, 46, 7, 47, 6, 48, 5, 49, 4, 50, 3, 51, 2, 52, 1, 53, 0, 30, 22, 33, 19, 29, 25, 31, 24, 27, 26, 28, 23, 32, 20, 36, 21, 34, 15, 38, 16, 41, 13, 37, 17, 35, 18, 39, 12]

theorem h2_21_28_certificate : FiniteAlphaSpider 49 h2_21_28_labels 26 := by
  let _ := finiteAlphaSpiderDecidable 49 h2_21_28_labels 26
  decide

theorem h2_21_28_rooted : RootedAlphaSpider 21 28 :=
  rootedAlphaSpider_of_finite h2_21_28_certificate (by decide)

def h2_22_29_labels : Fin 56 → ℕ := ![27, 28, 25, 35, 14, 29, 23, 30, 26, 31, 1, 53, 4, 50, 7, 47, 10, 44, 12, 45, 9, 48, 6, 51, 3, 54, 0, 55, 2, 52, 5, 49, 8, 46, 11, 42, 13, 41, 16, 43, 17, 36, 22, 37, 19, 39, 15, 38, 21, 32, 20, 33, 24, 34, 18, 40]

theorem h2_22_29_certificate : FiniteAlphaSpider 51 h2_22_29_labels 27 := by
  let _ := finiteAlphaSpiderDecidable 51 h2_22_29_labels 27
  decide

theorem h2_22_29_rooted : RootedAlphaSpider 22 29 :=
  rootedAlphaSpider_of_finite h2_22_29_certificate (by decide)

def h2_22_30_labels : Fin 57 → ℕ := ![9, 44, 18, 49, 3, 45, 21, 37, 23, 31, 13, 47, 10, 43, 12, 41, 11, 50, 6, 48, 7, 52, 2, 54, 5, 53, 0, 56, 1, 55, 4, 51, 8, 46, 14, 42, 15, 40, 20, 35, 22, 34, 24, 33, 26, 32, 27, 30, 28, 29, 25, 36, 19, 38, 17, 39, 16]

theorem h2_22_30_certificate : FiniteAlphaSpider 52 h2_22_30_labels 28 := by
  let _ := finiteAlphaSpiderDecidable 52 h2_22_30_labels 28
  decide

theorem h2_22_30_rooted : RootedAlphaSpider 22 30 :=
  rootedAlphaSpider_of_finite h2_22_30_certificate (by decide)

end Bounty


/- Supporting module: H2Seeds -/

namespace Bounty

def h2_seed_8_1_labels : Fin 14 → ℕ := ![1, 13, 0, 12, 2, 10, 5, 9, 3, 11, 4, 7, 6, 8]

theorem h2_seed_8_1_certificate : FiniteAlphaSpider 9 h2_seed_8_1_labels 6 := by
  let _ := finiteAlphaSpiderDecidable 9 h2_seed_8_1_labels 6
  decide

theorem h2_seed_8_1_canonical : CanonicalPinnedSpider 9 8 (extendSpiderLabel h2_seed_8_1_labels) := by
  refine ⟨h2_seed_8_1_certificate.toNat.1, ?_, h2_seed_8_1_certificate.toNat.2.1, ?_⟩
  · norm_num [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, CanonicalSpider, extendSpiderLabel, h2_seed_8_1_labels]
  · norm_num [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, extendSpiderLabel, h2_seed_8_1_labels]

def h2_seed_9_1_labels : Fin 15 → ℕ := ![1, 14, 0, 13, 2, 11, 4, 12, 3, 9, 5, 10, 7, 8, 6]

theorem h2_seed_9_1_certificate : FiniteAlphaSpider 10 h2_seed_9_1_labels 7 := by
  let _ := finiteAlphaSpiderDecidable 10 h2_seed_9_1_labels 7
  decide

theorem h2_seed_9_1_canonical : CanonicalPinnedSpider 10 9 (extendSpiderLabel h2_seed_9_1_labels) := by
  refine ⟨h2_seed_9_1_certificate.toNat.1, ?_, h2_seed_9_1_certificate.toNat.2.1, ?_⟩
  · norm_num [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, CanonicalSpider, extendSpiderLabel, h2_seed_9_1_labels]
  · norm_num [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, extendSpiderLabel, h2_seed_9_1_labels]

def h2_seed_10_1_labels : Fin 16 → ℕ := ![1, 15, 0, 14, 2, 12, 4, 13, 3, 10, 6, 11, 5, 8, 7, 9]

theorem h2_seed_10_1_certificate : FiniteAlphaSpider 11 h2_seed_10_1_labels 7 := by
  let _ := finiteAlphaSpiderDecidable 11 h2_seed_10_1_labels 7
  decide

theorem h2_seed_10_1_canonical : CanonicalPinnedSpider 11 10 (extendSpiderLabel h2_seed_10_1_labels) := by
  refine ⟨h2_seed_10_1_certificate.toNat.1, ?_, h2_seed_10_1_certificate.toNat.2.1, ?_⟩
  · norm_num [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, CanonicalSpider, extendSpiderLabel, h2_seed_10_1_labels]
  · norm_num [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, extendSpiderLabel, h2_seed_10_1_labels]

def h2_seed_11_1_labels : Fin 17 → ℕ := ![1, 16, 0, 15, 2, 13, 5, 12, 3, 14, 4, 10, 6, 11, 8, 9, 7]

theorem h2_seed_11_1_certificate : FiniteAlphaSpider 12 h2_seed_11_1_labels 8 := by
  let _ := finiteAlphaSpiderDecidable 12 h2_seed_11_1_labels 8
  decide

theorem h2_seed_11_1_canonical : CanonicalPinnedSpider 12 11 (extendSpiderLabel h2_seed_11_1_labels) := by
  refine ⟨h2_seed_11_1_certificate.toNat.1, ?_, h2_seed_11_1_certificate.toNat.2.1, ?_⟩
  · norm_num [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, CanonicalSpider, extendSpiderLabel, h2_seed_11_1_labels]
  · norm_num [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, extendSpiderLabel, h2_seed_11_1_labels]

def h2_seed_8_2_labels : Fin 15 → ℕ := ![1, 14, 0, 13, 2, 11, 4, 12, 3, 9, 5, 10, 7, 8, 6]

theorem h2_seed_8_2_certificate : FiniteAlphaSpider 10 h2_seed_8_2_labels 7 := by
  let _ := finiteAlphaSpiderDecidable 10 h2_seed_8_2_labels 7
  decide

theorem h2_seed_8_2_canonical : CanonicalPinnedSpider 10 8 (extendSpiderLabel h2_seed_8_2_labels) := by
  refine ⟨h2_seed_8_2_certificate.toNat.1, ?_, h2_seed_8_2_certificate.toNat.2.1, ?_⟩
  · norm_num [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, CanonicalSpider, extendSpiderLabel, h2_seed_8_2_labels]
  · norm_num [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, extendSpiderLabel, h2_seed_8_2_labels]

def h2_seed_9_2_labels : Fin 16 → ℕ := ![1, 15, 0, 14, 2, 12, 4, 13, 3, 10, 6, 11, 5, 8, 7, 9]

theorem h2_seed_9_2_certificate : FiniteAlphaSpider 11 h2_seed_9_2_labels 7 := by
  let _ := finiteAlphaSpiderDecidable 11 h2_seed_9_2_labels 7
  decide

theorem h2_seed_9_2_canonical : CanonicalPinnedSpider 11 9 (extendSpiderLabel h2_seed_9_2_labels) := by
  refine ⟨h2_seed_9_2_certificate.toNat.1, ?_, h2_seed_9_2_certificate.toNat.2.1, ?_⟩
  · norm_num [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, CanonicalSpider, extendSpiderLabel, h2_seed_9_2_labels]
  · norm_num [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, extendSpiderLabel, h2_seed_9_2_labels]

def h2_seed_10_2_labels : Fin 17 → ℕ := ![1, 16, 0, 15, 2, 13, 5, 10, 6, 12, 3, 14, 4, 11, 8, 9, 7]

theorem h2_seed_10_2_certificate : FiniteAlphaSpider 12 h2_seed_10_2_labels 8 := by
  let _ := finiteAlphaSpiderDecidable 12 h2_seed_10_2_labels 8
  decide

theorem h2_seed_10_2_canonical : CanonicalPinnedSpider 12 10 (extendSpiderLabel h2_seed_10_2_labels) := by
  refine ⟨h2_seed_10_2_certificate.toNat.1, ?_, h2_seed_10_2_certificate.toNat.2.1, ?_⟩
  · norm_num [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, CanonicalSpider, extendSpiderLabel, h2_seed_10_2_labels]
  · norm_num [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, extendSpiderLabel, h2_seed_10_2_labels]

def h2_seed_11_2_labels : Fin 18 → ℕ := ![1, 17, 0, 16, 2, 14, 3, 15, 5, 11, 6, 13, 4, 12, 8, 9, 7, 10]

theorem h2_seed_11_2_certificate : FiniteAlphaSpider 13 h2_seed_11_2_labels 8 := by
  let _ := finiteAlphaSpiderDecidable 13 h2_seed_11_2_labels 8
  decide

theorem h2_seed_11_2_canonical : CanonicalPinnedSpider 13 11 (extendSpiderLabel h2_seed_11_2_labels) := by
  refine ⟨h2_seed_11_2_certificate.toNat.1, ?_, h2_seed_11_2_certificate.toNat.2.1, ?_⟩
  · norm_num [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, CanonicalSpider, extendSpiderLabel, h2_seed_11_2_labels]
  · norm_num [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, extendSpiderLabel, h2_seed_11_2_labels]

end Bounty


/- Supporting module: H2Canonical -/

namespace Bounty
open Math15.Graceful

theorem h2_canonical_short_tail (d b : ℕ) (hd : 8 ≤ d) (hb : b=1 ∨ b=2) :
    ∃ f, CanonicalPinnedSpider (d+b) d f := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    by_cases hs : d < 12
    · rcases hb with rfl | rfl
      · interval_cases d
        · exact ⟨_,h2_seed_8_1_canonical⟩
        · exact ⟨_,h2_seed_9_1_canonical⟩
        · exact ⟨_,h2_seed_10_1_canonical⟩
        · exact ⟨_,h2_seed_11_1_canonical⟩
      · interval_cases d
        · exact ⟨_,h2_seed_8_2_canonical⟩
        · exact ⟨_,h2_seed_9_2_canonical⟩
        · exact ⟨_,h2_seed_10_2_canonical⟩
        · exact ⟨_,h2_seed_11_2_canonical⟩
    · obtain ⟨f,hf⟩ := ih (d-4) (by omega) (by omega)
      refine ⟨spiderPrefix (d-4+b) f,?_⟩
      convert hf.prefixExtension (by omega) (by omega) using 1 <;> omega

theorem h2_normalized_short_tail (d b : ℕ) (hd : 8 ≤ d) (hb : b=1 ∨ b=2) :
    ∃ f k, NatSpiderCertificate (d+b) f ∧ NatSpiderAlpha (d+b) f k ∧
      k < d+b+4 ∧ f (4+d)=0 ∧ k+1 ≤ d/2+4 ∧ (d+b+4)-k ≤ d/2+4 := by
  obtain ⟨f,hf⟩ := h2_canonical_short_tail d b hd hb
  have ha := hf.2.2.1.toAlphaLabeling hf.1 (by omega)
  by_cases he : d%2=0
  · let g : Fin (d+b+5) → ℕ := fun x => reverseLabel (edgeCount (spider (d+b)))
      (2+(d+b)/2) (f x.val)
    have hg : IsAlphaLabeling (spider (d+b)) g (2+(d+b)/2) := ha.reverse
    have hz : g ⟨4+d,by omega⟩=0 := by
      change reverseLabel _ _ (f (4+d))=0
      have hp : f (4+d) = 2+(d+b)/2 := by have := hf.2.2.2; omega
      rw [hp]
      exact reverseLabel_at_cut _ _
    obtain ⟨hgn,hga,hgk⟩ := (FiniteAlphaSpider.ofAlpha hg).toNat
    refine ⟨extendSpiderLabel g,_,hgn,hga,hgk,?_,?_,?_⟩
    · simpa only [extendSpiderLabel, dite_eq_left (show 4+d < d+b+5 by omega)] using hz
    · rcases hb with rfl | rfl <;> omega
    · rcases hb with rfl | rfl <;> omega
  · have he1 : d%2=1 := by omega
    let g : Fin (d+b+5) → ℕ := fun x => normalizeHighLabel (edgeCount (spider (d+b)))
      (2+(d+b)/2) (f x.val)
    have hg : IsAlphaLabeling (spider (d+b)) g
        (edgeCount (spider (d+b))-(2+(d+b)/2)-1) := ha.normalizeHigh
    have hz : g ⟨4+d,by omega⟩=0 := by
      change normalizeHighLabel _ _ (f (4+d))=0
      have hp : f (4+d) = 2+(d+b)/2+1 := by have := hf.2.2.2; omega
      rw [hp]
      exact normalizeHighLabel_at_cut _ _
    obtain ⟨hgn,hga,hgk⟩ := (FiniteAlphaSpider.ofAlpha hg).toNat
    refine ⟨extendSpiderLabel g,_,hgn,hga,hgk,?_,?_,?_⟩
    · simpa only [extendSpiderLabel, dite_eq_left (show 4+d < d+b+5 by omega)] using hz
    · rw [spider_edgeCount]
      rcases hb with rfl | rfl <;> omega
    · rw [spider_edgeCount]
      rcases hb with rfl | rfl <;> omega

end Bounty


/- Supporting module: H2FiniteCover -/



namespace Bounty
theorem h2_finite_region {d c : ℕ} (h : H2Research.FiniteRegion d c) : RootedAlphaSpider d c := by
  rcases h with ⟨rfl,hc⟩ | ⟨hd2,hd22,hc1,hlo,hhi⟩
  · rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact h2_1_2_rooted
    · exact h2_1_3_rooted
    · exact h2_1_6_rooted
    · exact h2_1_7_rooted
    · exact h2_1_8_rooted
    · exact h2_1_9_rooted
    · exact h2_1_11_rooted
  · interval_cases d
    · have hcmin : 1 ≤ c := by omega
      have hcmax : c ≤ 10 := by omega
      interval_cases c
      · exact h2_2_1_rooted
      · exact h2_2_2_rooted
      · exact h2_2_3_rooted
      · exact h2_2_4_rooted
      · exact h2_2_5_rooted
      · exact h2_2_6_rooted
      · exact h2_2_7_rooted
      · exact h2_2_8_rooted
      · exact h2_2_9_rooted
      · exact h2_2_10_rooted
    · have hcmin : 1 ≤ c := by omega
      have hcmax : c ≤ 10 := by omega
      interval_cases c
      · exact h2_3_1_rooted
      · exact h2_3_2_rooted
      · exact h2_3_3_rooted
      · exact h2_3_4_rooted
      · exact h2_3_5_rooted
      · exact h2_3_6_rooted
      · exact h2_3_7_rooted
      · exact h2_3_8_rooted
      · exact h2_3_9_rooted
      · exact h2_3_10_rooted
    · have hcmin : 1 ≤ c := by omega
      have hcmax : c ≤ 12 := by omega
      interval_cases c
      · exact h2_4_1_rooted
      · exact h2_4_2_rooted
      · exact h2_4_3_rooted
      · exact h2_4_4_rooted
      · exact h2_4_5_rooted
      · exact h2_4_6_rooted
      · exact h2_4_7_rooted
      · exact h2_4_8_rooted
      · exact h2_4_9_rooted
      · exact h2_4_10_rooted
      · exact h2_4_11_rooted
      · exact h2_4_12_rooted
    · have hcmin : 1 ≤ c := by omega
      have hcmax : c ≤ 12 := by omega
      interval_cases c
      · exact h2_5_1_rooted
      · exact h2_5_2_rooted
      · exact h2_5_3_rooted
      · exact h2_5_4_rooted
      · exact h2_5_5_rooted
      · exact h2_5_6_rooted
      · exact h2_5_7_rooted
      · exact h2_5_8_rooted
      · exact h2_5_9_rooted
      · exact h2_5_10_rooted
      · exact h2_5_11_rooted
      · exact h2_5_12_rooted
    · have hcmin : 1 ≤ c := by omega
      have hcmax : c ≤ 14 := by omega
      interval_cases c
      · exact h2_6_1_rooted
      · exact h2_6_2_rooted
      · exact h2_6_3_rooted
      · exact h2_6_4_rooted
      · exact h2_6_5_rooted
      · exact h2_6_6_rooted
      · exact h2_6_7_rooted
      · exact h2_6_8_rooted
      · exact h2_6_9_rooted
      · exact h2_6_10_rooted
      · exact h2_6_11_rooted
      · exact h2_6_12_rooted
      · exact h2_6_13_rooted
      · exact h2_6_14_rooted
    · have hcmin : 1 ≤ c := by omega
      have hcmax : c ≤ 14 := by omega
      interval_cases c
      · exact h2_7_1_rooted
      · exact h2_7_2_rooted
      · exact h2_7_3_rooted
      · exact h2_7_4_rooted
      · exact h2_7_5_rooted
      · exact h2_7_6_rooted
      · exact h2_7_7_rooted
      · exact h2_7_8_rooted
      · exact h2_7_9_rooted
      · exact h2_7_10_rooted
      · exact h2_7_11_rooted
      · exact h2_7_12_rooted
      · exact h2_7_13_rooted
      · exact h2_7_14_rooted
    · have hcmin : 1 ≤ c := by omega
      have hcmax : c ≤ 16 := by omega
      interval_cases c
      · exact h2_8_1_rooted
      · exact h2_8_2_rooted
      · exact h2_8_3_rooted
      · exact h2_8_4_rooted
      · exact h2_8_5_rooted
      · exact h2_8_6_rooted
      · exact h2_8_7_rooted
      · exact h2_8_8_rooted
      · exact h2_8_9_rooted
      · exact h2_8_10_rooted
      · exact h2_8_11_rooted
      · exact h2_8_12_rooted
      · exact h2_8_13_rooted
      · exact h2_8_14_rooted
      · exact h2_8_15_rooted
      · exact h2_8_16_rooted
    · have hcmin : 3 ≤ c := by omega
      have hcmax : c ≤ 16 := by omega
      interval_cases c
      · exact h2_9_3_rooted
      · exact h2_9_4_rooted
      · exact h2_9_5_rooted
      · exact h2_9_6_rooted
      · exact h2_9_7_rooted
      · exact h2_9_8_rooted
      · exact h2_9_9_rooted
      · exact h2_9_10_rooted
      · exact h2_9_11_rooted
      · exact h2_9_12_rooted
      · exact h2_9_13_rooted
      · exact h2_9_14_rooted
      · exact h2_9_15_rooted
      · exact h2_9_16_rooted
    · have hcmin : 5 ≤ c := by omega
      have hcmax : c ≤ 18 := by omega
      interval_cases c
      · exact h2_10_5_rooted
      · exact h2_10_6_rooted
      · exact h2_10_7_rooted
      · exact h2_10_8_rooted
      · exact h2_10_9_rooted
      · exact h2_10_10_rooted
      · exact h2_10_11_rooted
      · exact h2_10_12_rooted
      · exact h2_10_13_rooted
      · exact h2_10_14_rooted
      · exact h2_10_15_rooted
      · exact h2_10_16_rooted
      · exact h2_10_17_rooted
      · exact h2_10_18_rooted
    · have hcmin : 7 ≤ c := by omega
      have hcmax : c ≤ 18 := by omega
      interval_cases c
      · exact h2_11_7_rooted
      · exact h2_11_8_rooted
      · exact h2_11_9_rooted
      · exact h2_11_10_rooted
      · exact h2_11_11_rooted
      · exact h2_11_12_rooted
      · exact h2_11_13_rooted
      · exact h2_11_14_rooted
      · exact h2_11_15_rooted
      · exact h2_11_16_rooted
      · exact h2_11_17_rooted
      · exact h2_11_18_rooted
    · have hcmin : 9 ≤ c := by omega
      have hcmax : c ≤ 20 := by omega
      interval_cases c
      · exact h2_12_9_rooted
      · exact h2_12_10_rooted
      · exact h2_12_11_rooted
      · exact h2_12_12_rooted
      · exact h2_12_13_rooted
      · exact h2_12_14_rooted
      · exact h2_12_15_rooted
      · exact h2_12_16_rooted
      · exact h2_12_17_rooted
      · exact h2_12_18_rooted
      · exact h2_12_19_rooted
      · exact h2_12_20_rooted
    · have hcmin : 11 ≤ c := by omega
      have hcmax : c ≤ 20 := by omega
      interval_cases c
      · exact h2_13_11_rooted
      · exact h2_13_12_rooted
      · exact h2_13_13_rooted
      · exact h2_13_14_rooted
      · exact h2_13_15_rooted
      · exact h2_13_16_rooted
      · exact h2_13_17_rooted
      · exact h2_13_18_rooted
      · exact h2_13_19_rooted
      · exact h2_13_20_rooted
    · have hcmin : 13 ≤ c := by omega
      have hcmax : c ≤ 22 := by omega
      interval_cases c
      · exact h2_14_13_rooted
      · exact h2_14_14_rooted
      · exact h2_14_15_rooted
      · exact h2_14_16_rooted
      · exact h2_14_17_rooted
      · exact h2_14_18_rooted
      · exact h2_14_19_rooted
      · exact h2_14_20_rooted
      · exact h2_14_21_rooted
      · exact h2_14_22_rooted
    · have hcmin : 15 ≤ c := by omega
      have hcmax : c ≤ 22 := by omega
      interval_cases c
      · exact h2_15_15_rooted
      · exact h2_15_16_rooted
      · exact h2_15_17_rooted
      · exact h2_15_18_rooted
      · exact h2_15_19_rooted
      · exact h2_15_20_rooted
      · exact h2_15_21_rooted
      · exact h2_15_22_rooted
    · have hcmin : 17 ≤ c := by omega
      have hcmax : c ≤ 24 := by omega
      interval_cases c
      · exact h2_16_17_rooted
      · exact h2_16_18_rooted
      · exact h2_16_19_rooted
      · exact h2_16_20_rooted
      · exact h2_16_21_rooted
      · exact h2_16_22_rooted
      · exact h2_16_23_rooted
      · exact h2_16_24_rooted
    · have hcmin : 19 ≤ c := by omega
      have hcmax : c ≤ 24 := by omega
      interval_cases c
      · exact h2_17_19_rooted
      · exact h2_17_20_rooted
      · exact h2_17_21_rooted
      · exact h2_17_22_rooted
      · exact h2_17_23_rooted
      · exact h2_17_24_rooted
    · have hcmin : 21 ≤ c := by omega
      have hcmax : c ≤ 26 := by omega
      interval_cases c
      · exact h2_18_21_rooted
      · exact h2_18_22_rooted
      · exact h2_18_23_rooted
      · exact h2_18_24_rooted
      · exact h2_18_25_rooted
      · exact h2_18_26_rooted
    · have hcmin : 23 ≤ c := by omega
      have hcmax : c ≤ 26 := by omega
      interval_cases c
      · exact h2_19_23_rooted
      · exact h2_19_24_rooted
      · exact h2_19_25_rooted
      · exact h2_19_26_rooted
    · have hcmin : 25 ≤ c := by omega
      have hcmax : c ≤ 28 := by omega
      interval_cases c
      · exact h2_20_25_rooted
      · exact h2_20_26_rooted
      · exact h2_20_27_rooted
      · exact h2_20_28_rooted
    · have hcmin : 27 ≤ c := by omega
      have hcmax : c ≤ 28 := by omega
      interval_cases c
      · exact h2_21_27_rooted
      · exact h2_21_28_rooted
    · have hcmin : 29 ≤ c := by omega
      have hcmax : c ≤ 30 := by omega
      interval_cases c
      · exact h2_22_29_rooted
      · exact h2_22_30_rooted

theorem h2_normalized_seed (d b : ℕ) (hd : 2 ≤ d) (hb : b=1 ∨ b=2) :
    ∃ f k, NatSpiderCertificate (d+b) f ∧ NatSpiderAlpha (d+b) f k ∧
      k < d+b+4 ∧ f (4+d)=0 ∧ k+1 ≤ d/2+4 ∧ (d+b+4)-k ≤ d/2+4 := by
  by_cases hd8 : 8 ≤ d
  · exact h2_normalized_short_tail d b hd8 hb
  · have hd7 : d ≤ 7 := by omega
    interval_cases d
    · rcases hb with rfl | rfl
      · obtain ⟨hg,ha,hk⟩ := h2_2_1_certificate.toNat
        refine ⟨extendSpiderLabel h2_2_1_labels,3,hg,ha,hk,?_,by decide,by decide⟩
        norm_num [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, extendSpiderLabel, h2_2_1_labels]
      · obtain ⟨hg,ha,hk⟩ := h2_2_2_certificate.toNat
        refine ⟨extendSpiderLabel h2_2_2_labels,4,hg,ha,hk,?_,by decide,by decide⟩
        norm_num [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, extendSpiderLabel, h2_2_2_labels]
    · rcases hb with rfl | rfl
      · obtain ⟨hg,ha,hk⟩ := h2_3_1_certificate.toNat
        refine ⟨extendSpiderLabel h2_3_1_labels,3,hg,ha,hk,?_,by decide,by decide⟩
        norm_num [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, extendSpiderLabel, h2_3_1_labels]
      · obtain ⟨hg,ha,hk⟩ := h2_3_2_certificate.toNat
        refine ⟨extendSpiderLabel h2_3_2_labels,4,hg,ha,hk,?_,by decide,by decide⟩
        norm_num [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, extendSpiderLabel, h2_3_2_labels]
    · rcases hb with rfl | rfl
      · obtain ⟨hg,ha,hk⟩ := h2_4_1_certificate.toNat
        refine ⟨extendSpiderLabel h2_4_1_labels,4,hg,ha,hk,?_,by decide,by decide⟩
        norm_num [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, extendSpiderLabel, h2_4_1_labels]
      · obtain ⟨hg,ha,hk⟩ := h2_4_2_certificate.toNat
        refine ⟨extendSpiderLabel h2_4_2_labels,5,hg,ha,hk,?_,by decide,by decide⟩
        norm_num [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, extendSpiderLabel, h2_4_2_labels]
    · rcases hb with rfl | rfl
      · obtain ⟨hg,ha,hk⟩ := h2_5_1_certificate.toNat
        refine ⟨extendSpiderLabel h2_5_1_labels,4,hg,ha,hk,?_,by decide,by decide⟩
        norm_num [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, extendSpiderLabel, h2_5_1_labels]
      · obtain ⟨hg,ha,hk⟩ := h2_5_2_certificate.toNat
        refine ⟨extendSpiderLabel h2_5_2_labels,5,hg,ha,hk,?_,by decide,by decide⟩
        norm_num [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, extendSpiderLabel, h2_5_2_labels]
    · rcases hb with rfl | rfl
      · obtain ⟨hg,ha,hk⟩ := h2_6_1_certificate.toNat
        refine ⟨extendSpiderLabel h2_6_1_labels,5,hg,ha,hk,?_,by decide,by decide⟩
        norm_num [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, extendSpiderLabel, h2_6_1_labels]
      · obtain ⟨hg,ha,hk⟩ := h2_6_2_certificate.toNat
        refine ⟨extendSpiderLabel h2_6_2_labels,6,hg,ha,hk,?_,by decide,by decide⟩
        norm_num [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, extendSpiderLabel, h2_6_2_labels]
    · rcases hb with rfl | rfl
      · obtain ⟨hg,ha,hk⟩ := h2_7_1_certificate.toNat
        refine ⟨extendSpiderLabel h2_7_1_labels,5,hg,ha,hk,?_,by decide,by decide⟩
        norm_num [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, extendSpiderLabel, h2_7_1_labels]
      · obtain ⟨hg,ha,hk⟩ := h2_7_2_certificate.toNat
        refine ⟨extendSpiderLabel h2_7_2_labels,6,hg,ha,hk,?_,by decide,by decide⟩
        norm_num [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, extendSpiderLabel, h2_7_2_labels]

end Bounty


/- Supporting module: AlphaAppend -/

namespace Bounty
open Math15.Graceful

/-- Appending a balanced alpha path preserves the old zero labels and the
alpha property when the joining edge crosses the enlarged cut. -/
theorem NatSpiderAlpha.appendEvenPath {L k s : ℕ} {f p : ℕ → ℕ}
    (hL : 1 ≤ L) (hs : 0 < s) (hf : NatSpiderAlpha L f k)
    (hp : ∀ j, 0 < j → j < 2*s →
      (p (j-1) < s ∧ s ≤ p j) ∨ (p j < s ∧ s ≤ p (j-1)))
    (hjoin : (f (L+4) ≤ k ∧ s ≤ p 0) ∨ (k < f (L+4) ∧ p 0 < s)) :
    NatSpiderAlpha (L+2*s) (appendSpiderLabels L k (2*s) f p) (k+s) := by
  intro j hj hjb
  rcases lt_trichotomy j (L+5) with hold | rfl | hnew
  · rw [appendSpiderLabels_old f p ((spiderParent_le j).trans_lt hold),
      appendSpiderLabels_old f p hold]
    rcases hf j hj hold with h | h
    · left
      simp only [shiftAboveCut]
      split_ifs <;> omega
    · right
      simp only [shiftAboveCut]
      split_ifs <;> omega
  · have hpar : spiderParent (L+5) = L+4 := by
      unfold spiderParent
      split_ifs <;> omega
    rw [hpar, appendSpiderLabels_old f p (by omega),
      appendSpiderLabels_new f p (by omega)]
    simp only [Nat.sub_self]
    rcases hjoin with h | h
    · left
      simp only [shiftAboveCut, ite_eq_left h.1]
      omega
    · right
      simp only [shiftAboveCut, ite_eq_right (by omega : ¬f (L+4) ≤ k)]
      omega
  · have hpar : spiderParent j = j-1 := by
      unfold spiderParent
      split_ifs <;> omega
    rw [hpar, appendSpiderLabels_new f p (by omega),
      appendSpiderLabels_new f p (by omega)]
    have heq : j-1-(L+5) = j-(L+5)-1 := by omega
    rw [heq]
    rcases hp (j-(L+5)) (by omega) (by omega) with h | h
    · left; omega
    · right; omega

def appendRootDistance (k t : ℕ) : ℕ := if t ≤ k then k+1-t else t-k

theorem appendRootDistance_pos (k t : ℕ) : 0 < appendRootDistance k t := by
  unfold appendRootDistance
  split_ifs <;> omega

def appendFirstLabel (k s t : ℕ) : ℕ :=
  if t ≤ k then 2*s-appendRootDistance k t else appendRootDistance k t-1

theorem appendFirstLabel_lt {k s t : ℕ}
    (hr : appendRootDistance k t ≤ s) : appendFirstLabel k s t < 2*s := by
  have hp := appendRootDistance_pos k t
  unfold appendFirstLabel
  split_ifs <;> omega

theorem appendFirstLabel_join {k s t : ℕ}
    (hr : appendRootDistance k t ≤ s) :
    Nat.dist (shiftAboveCut k (2*s) t) (k+1+appendFirstLabel k s t) = 2*s := by
  unfold appendRootDistance at hr
  unfold appendFirstLabel appendRootDistance shiftAboveCut
  split_ifs at * <;> unfold Nat.dist <;> omega

theorem appendFirstLabel_cross {k s t : ℕ}
    (hr : appendRootDistance k t ≤ s) :
    (t ≤ k ∧ s ≤ appendFirstLabel k s t) ∨ (k < t ∧ appendFirstLabel k s t < s) := by
  unfold appendRootDistance at hr
  unfold appendFirstLabel appendRootDistance
  split_ifs at * <;> omega

theorem NatSpiderCertificate.appendEvenAlpha {L k s : ℕ} {f p : ℕ → ℕ}
    (hL : 1 ≤ L) (hf : NatSpiderCertificate L f) (hα : NatSpiderAlpha L f k)
    (hk : k ≤ L+4) (hr : appendRootDistance k (f (L+4)) ≤ s)
    (hp : NatGracefulPath (2*s) p)
    (hpa : ∀ j, 0 < j → j < 2*s →
      (p (j-1) < s ∧ s ≤ p j) ∨ (p j < s ∧ s ≤ p (j-1)))
    (hp0 : p 0 = appendFirstLabel k s (f (L+4))) :
    NatSpiderCertificate (L+2*s) (appendSpiderLabels L k (2*s) f p) ∧
    NatSpiderAlpha (L+2*s) (appendSpiderLabels L k (2*s) f p) (k+s) := by
  have hs : 0 < s := (appendRootDistance_pos k (f (L+4))).trans_le hr
  constructor
  · exact hf.appendPath hL hα hp hk (by rw [hp0]; exact appendFirstLabel_join hr)
  · exact hα.appendEvenPath hL hs hpa (by rw [hp0]; exact appendFirstLabel_cross hr)

end Bounty


/- Supporting module: H2Append -/



namespace Bounty
open Math15.Graceful

/-- An even balanced alpha path can start at any label in its full range.
For an upper-half endpoint, complement a lower-half construction. -/
theorem exists_balanced_alpha_path_endpoint {s a : ℕ} (ha : a < 2*s) :
    ∃ p : ℕ → ℕ, NatGracefulPath (2*s) p ∧
      (∀ j, 0 < j → j < 2*s →
        (p (j-1) < s ∧ s ≤ p j) ∨ (p j < s ∧ s ≤ p (j-1))) ∧ p 0 = a := by
  by_cases halow : a < s
  · obtain ⟨p, hp⟩ := exists_evenAlphaPath s a halow
    exact ⟨p, hp.graceful, fun _ hj hb => hp.crosses hj hb, hp.first⟩
  · obtain ⟨p, hp⟩ := exists_evenAlphaPath s (2*s-1-a) (by omega)
    let q : ℕ → ℕ := fun i => 2*s-1-p i
    have hdiff (i j : ℕ) (hi : i < 2*s) (hj : j < 2*s) :
        Nat.dist (q i) (q j) = Nat.dist (p i) (p j) := by
      have h₁ := hp.graceful.2.1 i hi
      have h₂ := hp.graceful.2.1 j hj
      unfold q Nat.dist
      omega
    refine ⟨q, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · intro i j hi hj heq
      have h₁ := hp.graceful.2.1 i hi
      have h₂ := hp.graceful.2.1 j hj
      dsimp only [q] at heq
      exact hp.graceful.1 i j hi hj (by omega)
    · intro i hi
      dsimp only [q]
      omega
    · intro i j hi hib hj hjb heq
      rw [hdiff _ _ (by omega) hib, hdiff _ _ (by omega) hjb] at heq
      exact hp.graceful.2.2 i j hi hib hj hjb heq
    · intro j hj hb
      have h₁ := hp.graceful.2.1 (j-1) (by omega)
      have h₂ := hp.graceful.2.1 j hb
      have hc := hp.crosses hj hb
      dsimp only [q]
      omega
    · dsimp only [q]
      rw [hp.first]
      omega

/-- Append any sufficiently long even segment to the long leg of S(2,2,L).
The threshold is the distance of the old endpoint from the alpha cut. -/
theorem NatSpiderCertificate.exists_appendEvenAlpha {L k s : ℕ} {f : ℕ → ℕ}
    (hL : 1 ≤ L) (hf : NatSpiderCertificate L f) (hα : NatSpiderAlpha L f k)
    (hk : k ≤ L+4) (hr : appendRootDistance k (f (L+4)) ≤ s) :
    ∃ g : ℕ → ℕ, NatSpiderCertificate (L+2*s) g ∧
      NatSpiderAlpha (L+2*s) g (k+s) ∧
      (∀ z, z < L+5 → g z = shiftAboveCut k (2*s) (f z)) ∧
      (∀ z, z < L+5 → f z = 0 → g z = 0) := by
  obtain ⟨p, hp, hpa, hp0⟩ := exists_balanced_alpha_path_endpoint (appendFirstLabel_lt hr)
  have hg := hf.appendEvenAlpha hL hα hk hr hp hpa hp0
  refine ⟨appendSpiderLabels L k (2*s) f p, hg.1, hg.2, ?_, ?_⟩
  · intro z hz
    exact appendSpiderLabels_old f p hz
  · intro z hz hzero
    exact appendSpiderLabels_preserves_zero hz hzero

lemma appendRootDistance_le_uniform {L k t : ℕ} (ht : t ≤ L+4) :
    appendRootDistance k t ≤ max (k+1) (L+4-k) := by
  have h₁ : k+1 ≤ max (k+1) (L+4-k) := le_max_left _ _
  have h₂ : L+4-k ≤ max (k+1) (L+4-k) := le_max_right _ _
  unfold appendRootDistance
  split_ifs <;> omega

/-- A label-independent sufficient bound for the even extension. -/
theorem NatSpiderCertificate.exists_appendEvenAlpha_uniform {L k s : ℕ} {f : ℕ → ℕ}
    (hL : 1 ≤ L) (hf : NatSpiderCertificate L f) (hα : NatSpiderAlpha L f k)
    (hk : k ≤ L+4) (hs : max (k+1) (L+4-k) ≤ s) :
    ∃ g : ℕ → ℕ, NatSpiderCertificate (L+2*s) g ∧
      NatSpiderAlpha (L+2*s) g (k+s) ∧
      (∀ z, z < L+5 → g z = shiftAboveCut k (2*s) (f z)) ∧
      (∀ z, z < L+5 → f z = 0 → g z = 0) := by
  apply hf.exists_appendEvenAlpha hL hα hk
  exact (appendRootDistance_le_uniform (hf.2.1 (L+4) (by omega))).trans hs

/-- Once a rooted alpha spider exists, appending a sufficiently long even
segment to its long leg preserves the specified old zero vertex. -/
theorem RootedAlphaSpider.append_even {d c s : ℕ} (h : RootedAlphaSpider d c)
    (hL : 1 ≤ d+c) (hs : d+c+4 ≤ s) : RootedAlphaSpider d (c+2*s) := by
  obtain ⟨f, k, hf, hα, hk, hz⟩ := h
  have hbound : max (k+1) (d+c+4-k) ≤ s := by omega
  obtain ⟨g, hg, hga, _, hzero⟩ :=
    hf.exists_appendEvenAlpha_uniform hL hα (by omega) hbound
  refine ⟨g, k+s, ?_, ?_, ?_, ?_⟩
  · simpa only [Nat.add_assoc] using hg
  · simpa only [Nat.add_assoc] using hga
  · omega
  · exact hzero (4+d) (by omega) hz

end Bounty


/- Supporting module: H2Theorem -/




namespace Bounty

/-- The canonical first-region pin can be normalized to zero. -/
theorem h2_first_region {d c : ℕ} (hd : 1 ≤ d) (hc : 1 ≤ c)
    (hregion : H2Research.FirstRegion d c) : RootedAlphaSpider d c := by
  obtain ⟨f, hf⟩ := PathConstruction.canonical_pinned_first_region d c hd hc hregion
  obtain ⟨g, k, hg, hz⟩ := hf.zeroPin (by omega)
  exact rootedAlphaSpider_of_finite (FiniteAlphaSpider.ofAlpha hg) hz

private theorem flat_H2Theorem_h2_append_from_data {d b s k : ℕ} {f : ℕ → ℕ}
    (hL : 1 ≤ d+b) (hf : NatSpiderCertificate (d+b) f)
    (ha : NatSpiderAlpha (d+b) f k) (hk : k < d+b+4) (hz : f (4+d) = 0)
    (hs : max (k+1) (d+b+4-k) ≤ s) : RootedAlphaSpider d (b+2*s) := by
  obtain ⟨g, hg, hga, _, hzero⟩ := hf.exists_appendEvenAlpha_uniform hL ha (by omega) hs
  refine ⟨g, k+s, ?_, ?_, ?_, ?_⟩
  · simpa only [Nat.add_assoc] using hg
  · simpa only [Nat.add_assoc] using hga
  · omega
  · exact hzero (4+d) (by omega) hz

/-- The long region follows from normalized short-tail seeds and the even
path extension, with its half-length chosen to match the desired tail. -/
theorem h2_long_region {d c : ℕ} (hregion : H2Research.LongRegion d c) :
    RootedAlphaSpider d c := by
  obtain ⟨hd, hc⟩ := hregion
  let b := if c%2 = 1 then 1 else 2
  have hb : b = 1 ∨ b = 2 := by unfold b; split_ifs <;> simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero]
  have hpar := H2Research.extension_parameters d c hc
  change b ≤ c ∧ (c-b)%2 = 0 ∧ 2*(d/2+4) ≤ c-b at hpar
  obtain ⟨f, k, hf, ha, hk, hz, hk₁, hk₂⟩ := h2_normalized_seed d b hd hb
  have hs : max (k+1) (d+b+4-k) ≤ (c-b)/2 := by omega
  have h := flat_H2Theorem_h2_append_from_data (by omega) hf ha hk hz hs
  have heq : b+2*((c-b)/2) = c := by omega
  rwa [heq] at h

/-- The two normalized seeds at d=1 cover all sufficiently long tails. -/
theorem h2_small_long_region {d c : ℕ} (hregion : H2Research.SmallLongRegion d c) :
    RootedAlphaSpider d c := by
  obtain ⟨rfl, hc⟩ := hregion
  rcases hc with ⟨hpar, hmin⟩ | ⟨hpar, hmin⟩
  · obtain ⟨hf, ha, hk⟩ := h2_1_2_certificate.toNat
    have hz : extendSpiderLabel h2_1_2_labels (4+1) = 0 := by
      norm_num [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, extendSpiderLabel, h2_1_2_labels]
    have hs : max (3+1) (1+2+4-3) ≤ (c-2)/2 := by omega
    have h := flat_H2Theorem_h2_append_from_data (d := 1) (b := 2) (s := (c-2)/2)
      (by omega) hf ha hk hz hs
    have heq : 2+2*((c-2)/2) = c := by omega
    rwa [heq] at h
  · obtain ⟨hf, ha, hk⟩ := h2_1_3_certificate.toNat
    have hz : extendSpiderLabel h2_1_3_labels (4+1) = 0 := by
      norm_num [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, extendSpiderLabel, h2_1_3_labels]
    have hs : max (3+1) (1+3+4-3) ≤ (c-3)/2 := by omega
    have h := flat_H2Theorem_h2_append_from_data (d := 1) (b := 3) (s := (c-3)/2)
      (by omega) hf ha hk hz hs
    have heq : 3+2*((c-3)/2) = c := by omega
    rwa [heq] at h

/-- S(2,2,d+c) has an alpha labeling with zero at the vertex distance d along
its long leg, outside the three exceptional parameter pairs. -/
theorem h2_rooted_alpha_spider (d c : ℕ) (hd : 1 ≤ d) (hc : 1 ≤ c)
    (hne : ¬H2Research.Exceptional d c) : RootedAlphaSpider d c := by
  rcases H2Research.exhaustive d c hd hc hne with h | h | h | h
  · exact h2_first_region hd hc h
  · exact h2_long_region h
  · exact h2_small_long_region h
  · exact h2_finite_region h

end Bounty


/- Supporting module: H1FiniteExceptions -/

namespace Bounty

theorem h1_2_2_1_1_rooted : RootedFork 2 2 1 1 := by
  let labels : List ℕ := [1,4,6,2,3,0,5]
  let vi : List ℕ := [5,0,3,4,1,6,2]
  let ei : List ℕ := [0,3,1,0,2,5,4]
  have h : FastFiniteParentCertificate 6 (forkParent 2 2) labels vi ei := by
    let _ := fastFiniteParentCertificateDecidable 6 (forkParent 2 2) labels vi ei
    decide
  exact rootedFork_of_fast_certificate h (by decide)

theorem h1_2_2_1_4_rooted : RootedFork 2 2 1 4 := by
  let labels : List ℕ := [4,1,9,2,8,0,5,3,7,6]
  let vi : List ℕ := [5,1,3,7,0,6,9,8,4,2]
  let ei : List ℕ := [0,8,6,0,7,5,3,2,1,4]
  have h : FastFiniteParentCertificate 9 (forkParent 2 2) labels vi ei := by
    let _ := fastFiniteParentCertificateDecidable 9 (forkParent 2 2) labels vi ei
    decide
  exact rootedFork_of_fast_certificate h (by decide)

theorem h1_2_2_1_5_rooted : RootedFork 2 2 1 5 := by
  let labels : List ℕ := [6,1,9,2,8,0,10,7,3,5,4]
  let vi : List ℕ := [5,1,3,8,10,9,0,7,4,2,6]
  let ei : List ℕ := [0,9,8,6,7,0,3,2,1,4,5]
  have h : FastFiniteParentCertificate 10 (forkParent 2 2) labels vi ei := by
    let _ := fastFiniteParentCertificateDecidable 10 (forkParent 2 2) labels vi ei
    decide
  exact rootedFork_of_fast_certificate h (by decide)

end Bounty


/- Supporting module: ForkTwos -/



namespace Bounty

theorem RootedAlphaSpider.toRootedFork {d c : ℕ} (hd : 1 ≤ d)
    (h : RootedAlphaSpider d c) : RootedFork 2 2 d c := by
  obtain ⟨f,k,hf,ha,hk,hz⟩ := h
  have hcert : NatParentCertificate (2+2+(d+c)) spiderParent f := by
    refine ⟨?_,?_,?_⟩
    · intro i j hi hj hh
      exact hf.1 i j (by omega) (by omega) hh
    · intro i hi
      have := hf.2.1 i (by omega)
      omega
    · intro i j hi hib hj hjb hh
      exact hf.2.2 i j hi (by omega) hj (by omega) hh
  let v (i : ℕ) := if i=0 then 2 else if i=2 then 0 else i
  let e (i : ℕ) := if i=1 then 2 else if i=2 then 1 else i
  have hv : ∀ i j, i ≤ 2+2+(d+c) → j ≤ 2+2+(d+c) → v i=v j → i=j := by
    intro i j hi hj hh
    dsimp [v] at hh
    split_ifs at hh <;> omega
  have hvb : ∀ i, i ≤ 2+2+(d+c) → v i ≤ 2+2+(d+c) := by
    intro i hi
    dsimp [v]
    split_ifs <;> omega
  have he : ∀ i j, 0 < i → i ≤ 2+2+(d+c) → 0 < j → j ≤ 2+2+(d+c) → e i=e j → i=j := by
    intro i j hi hib hj hjb hh
    dsimp [e] at hh
    split_ifs at hh <;> omega
  have heb : ∀ i, 0 < i → i ≤ 2+2+(d+c) → 0 < e i ∧ e i ≤ 2+2+(d+c) := by
    intro i hi hib
    dsimp [e]
    split_ifs <;> omega
  have hadj : ∀ i, 0 < i → i ≤ 2+2+(d+c) →
      (v (forkParent 2 2 i)=spiderParent (e i) ∧ v i=e i) ∨
      (v (forkParent 2 2 i)=e i ∧ v i=spiderParent (e i)) := by
    intro i hi hib
    by_cases his : i ≤ 5
    · interval_cases i <;> norm_num [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, v,e,forkParent,graftParent,spiderParent]
    · left
      have hi4 : ¬i ≤ 2+2 := by omega
      have hifive : ¬i=2+2+1 := by omega
      have hi0 : ¬i=0 := by omega
      have hi1 : ¬i=1 := by omega
      have hi2 : ¬i=2 := by omega
      have hi3 : ¬i=3 := by omega
      have hi5 : ¬i=5 := by omega
      have hip0 : ¬i-1=0 := by omega
      have hip2 : ¬i-1=2 := by omega
      simp only [v,e,forkParent,graftParent,spiderParent,ite_eq_right hi4,
        ite_eq_right hifive,ite_eq_right hi0,ite_eq_right hi1,ite_eq_right hi2,
        ite_eq_right hip0,ite_eq_right hip2,hi1,hi3,hi5,or_self,ite_false]
      exact ⟨trivial,trivial⟩
  refine ⟨fun i => f (v i),hcert.reindex hv hvb he heb hadj,?_⟩
  simpa only [v,ite_eq_right (show ¬2+2+d=0 by omega),
    ite_eq_right (show ¬2+2+d=2 by omega)] using hz

theorem rootedFork_twos {d c : ℕ} (hd : 1 ≤ d) (hc : 1 ≤ c) : RootedFork 2 2 d c := by
  by_cases he : H2Research.Exceptional d c
  · rcases he with ⟨rfl,hc⟩
    rcases hc with rfl | rfl | rfl
    · exact h1_2_2_1_1_rooted
    · exact h1_2_2_1_4_rooted
    · exact h1_2_2_1_5_rooted
  · exact (h2_rooted_alpha_spider d c hd hc he).toRootedFork hd

end Bounty


/- Supporting module: ForkLong -/


namespace Bounty

theorem rootedFork_long {a b d c : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hd : 1 ≤ d) (he : a ≠ 2 ∨ b ≠ 2)
    (hc : H1Coverage.Cut a b d + 1 ≤ c) : RootedFork a b d c := by
  obtain ⟨p,k,hp,hp0⟩ := rosa_zero_alpha_path a b ha hb he
  have hk : k=a/2+b/2 := by
    have hp' : NatAlphaPath (a+1+b) p k := by
      simpa only [Nat.add_right_comm] using hp
    have h := hp'.fork_cut (d := a+1) (c := b) (by omega)
      (by simpa only [Nat.add_sub_cancel] using hp0)
    omega
  obtain ⟨f,hf,hfa,hf0⟩ := forkStem_alpha hp hp0 d
  have hcut : forkStemCut (a+b) k d=H1Coverage.Cut a b d := by
    simp only [forkStemCut, H1Coverage.Cut, H1Coverage.V, H1Coverage.U, hk]
  have hzero : f (a+b+d)=0 := by
    simpa only [forkStemTip,ite_eq_right (by omega : ¬d=0)] using hf0
  have hbound : forkStemCut (a+b) k d ≤ a+b+d := by
    unfold forkStemCut
    have := hp.2.1
    split_ifs <;> omega
  obtain ⟨g,hg,hg0⟩ := hf.appendAtZero hfa
    (fun j hj _ => forkParent_lt a b j hj) (by omega : a+b+d ≤ a+b+d) hzero hbound
    (by omega : forkStemCut (a+b) k d+1 ≤ c)
  have hparent (j : ℕ) (hj : 0 < j) (_hjb : j ≤ a+b+d+c) :
      forkParent a b j=graftParent (a+b+d) (a+b+d) (forkParent a b) j := by
    by_cases hj0 : j ≤ a+b+d
    · simp only [graftParent,ite_eq_left hj0]
    · have hj1 : ¬j ≤ a+b := by omega
      have hj2 : ¬j=a+b+1 := by omega
      unfold forkParent graftParent
      simp only [ite_eq_right hj0,ite_eq_right hj1,ite_eq_right hj2]
      split_ifs <;> omega
  refine ⟨g,?_,hg0 (a+b+d) (by omega) hzero⟩
  simpa only [Nat.add_assoc] using hg.congrParent hparent

end Bounty


/- Supporting module: H1FiniteQ2 -/

namespace Bounty

theorem h1_1_1_1_1_rooted : RootedFork 1 1 1 1 := by
  let labels : List ℕ := [1,4,3,0,2]
  let vi : List ℕ := [3,0,4,2,1]
  let ei : List ℕ := [0,1,3,0,2]
  have h : FastFiniteParentCertificate 4 (forkParent 1 1) labels vi ei := by
    let _ := fastFiniteParentCertificateDecidable 4 (forkParent 1 1) labels vi ei
    decide
  exact rootedFork_of_fast_certificate h (by decide)

theorem h1_1_1_2_1_rooted : RootedFork 1 1 2 1 := by
  let labels : List ℕ := [3,1,2,4,0,5]
  let vi : List ℕ := [4,1,2,0,3,5]
  let ei : List ℕ := [0,1,0,2,3,4]
  have h : FastFiniteParentCertificate 5 (forkParent 1 1) labels vi ei := by
    let _ := fastFiniteParentCertificateDecidable 5 (forkParent 1 1) labels vi ei
    decide
  exact rootedFork_of_fast_certificate h (by decide)

theorem h1_1_1_3_1_rooted : RootedFork 1 1 3 1 := by
  let labels : List ℕ := [3,4,2,1,5,0,6]
  let vi : List ℕ := [5,3,2,0,1,4,6]
  let ei : List ℕ := [0,0,1,2,3,4,5]
  have h : FastFiniteParentCertificate 6 (forkParent 1 1) labels vi ei := by
    let _ := fastFiniteParentCertificateDecidable 6 (forkParent 1 1) labels vi ei
    decide
  exact rootedFork_of_fast_certificate h (by decide)

theorem h1_1_1_3_2_rooted : RootedFork 1 1 3 2 := by
  let labels : List ℕ := [4,1,3,5,6,0,7,2]
  let vi : List ℕ := [5,1,7,2,0,3,4,6]
  let ei : List ℕ := [0,3,1,0,2,6,4,5]
  have h : FastFiniteParentCertificate 7 (forkParent 1 1) labels vi ei := by
    let _ := fastFiniteParentCertificateDecidable 7 (forkParent 1 1) labels vi ei
    decide
  exact rootedFork_of_fast_certificate h (by decide)

theorem h1_1_1_3_3_rooted : RootedFork 1 1 3 3 := by
  let labels : List ℕ := [2,5,3,4,8,0,7,1,6]
  let vi : List ℕ := [5,7,0,2,3,1,8,6,4]
  let ei : List ℕ := [0,2,1,0,3,7,6,5,4]
  have h : FastFiniteParentCertificate 8 (forkParent 1 1) labels vi ei := by
    let _ := fastFiniteParentCertificateDecidable 8 (forkParent 1 1) labels vi ei
    decide
  exact rootedFork_of_fast_certificate h (by decide)

theorem h1_1_1_4_1_rooted : RootedFork 1 1 4 1 := by
  let labels : List ℕ := [4,1,5,3,2,7,0,6]
  let vi : List ℕ := [6,1,4,3,0,2,7,5]
  let ei : List ℕ := [0,3,2,0,1,4,6,5]
  have h : FastFiniteParentCertificate 7 (forkParent 1 1) labels vi ei := by
    let _ := fastFiniteParentCertificateDecidable 7 (forkParent 1 1) labels vi ei
    decide
  exact rootedFork_of_fast_certificate h (by decide)

theorem h1_1_1_4_2_rooted : RootedFork 1 1 4 2 := by
  let labels : List ℕ := [5,2,6,4,3,8,0,7,1]
  let vi : List ℕ := [6,8,1,4,3,0,2,7,5]
  let ei : List ℕ := [0,3,2,0,1,4,7,6,5]
  have h : FastFiniteParentCertificate 8 (forkParent 1 1) labels vi ei := by
    let _ := fastFiniteParentCertificateDecidable 8 (forkParent 1 1) labels vi ei
    decide
  exact rootedFork_of_fast_certificate h (by decide)

theorem h1_1_1_5_1_rooted : RootedFork 1 1 5 1 := by
  let labels : List ℕ := [6,3,5,2,7,1,8,0,4]
  let vi : List ℕ := [7,5,3,1,8,2,0,4,6]
  let ei : List ℕ := [0,2,1,0,7,3,4,5,6]
  have h : FastFiniteParentCertificate 8 (forkParent 1 1) labels vi ei := by
    let _ := fastFiniteParentCertificateDecidable 8 (forkParent 1 1) labels vi ei
    decide
  exact rootedFork_of_fast_certificate h (by decide)

theorem h1_1_1_5_2_rooted : RootedFork 1 1 5 2 := by
  let labels : List ℕ := [3,1,7,6,5,2,9,0,8,4]
  let vi : List ℕ := [7,1,5,0,9,4,3,2,8,6]
  let ei : List ℕ := [0,3,0,4,8,2,1,5,7,6]
  have h : FastFiniteParentCertificate 9 (forkParent 1 1) labels vi ei := by
    let _ := fastFiniteParentCertificateDecidable 9 (forkParent 1 1) labels vi ei
    decide
  exact rootedFork_of_fast_certificate h (by decide)

theorem h1_1_1_5_3_rooted : RootedFork 1 1 5 3 := by
  let labels : List ℕ := [7,1,8,3,6,2,10,0,9,4,5]
  let vi : List ℕ := [7,1,5,3,9,10,4,0,2,8,6]
  let ei : List ℕ := [0,9,2,3,4,8,0,1,5,7,6]
  have h : FastFiniteParentCertificate 10 (forkParent 1 1) labels vi ei := by
    let _ := fastFiniteParentCertificateDecidable 10 (forkParent 1 1) labels vi ei
    decide
  exact rootedFork_of_fast_certificate h (by decide)

theorem h1_1_1_5_4_rooted : RootedFork 1 1 5 4 := by
  let labels : List ℕ := [8,3,7,6,4,5,11,0,10,1,9,2]
  let vi : List ℕ := [7,9,11,1,4,5,3,2,0,10,8,6]
  let ei : List ℕ := [0,4,3,2,1,0,5,10,9,8,7,6]
  have h : FastFiniteParentCertificate 11 (forkParent 1 1) labels vi ei := by
    let _ := fastFiniteParentCertificateDecidable 11 (forkParent 1 1) labels vi ei
    decide
  exact rootedFork_of_fast_certificate h (by decide)

theorem h1_1_1_6_3_rooted : RootedFork 1 1 6 3 := by
  let labels : List ℕ := [7,2,8,6,3,5,4,11,0,10,1,9]
  let vi : List ℕ := [8,10,1,4,6,5,3,0,2,11,9,7]
  let ei : List ℕ := [0,5,4,3,2,0,1,6,10,9,8,7]
  have h : FastFiniteParentCertificate 11 (forkParent 1 1) labels vi ei := by
    let _ := fastFiniteParentCertificateDecidable 11 (forkParent 1 1) labels vi ei
    decide
  exact rootedFork_of_fast_certificate h (by decide)

theorem h1_1_1_7_5_rooted : RootedFork 1 1 7 5 := by
  let labels : List ℕ := [8,10,5,6,7,4,11,3,9,0,14,1,13,2,12]
  let vi : List ℕ := [9,11,13,7,5,2,3,4,0,8,1,6,14,12,10]
  let ei : List ℕ := [0,3,0,4,2,1,7,5,6,8,13,12,11,10,9]
  have h : FastFiniteParentCertificate 14 (forkParent 1 1) labels vi ei := by
    let _ := fastFiniteParentCertificateDecidable 14 (forkParent 1 1) labels vi ei
    decide
  exact rootedFork_of_fast_certificate h (by decide)

theorem h1_1_1_9_5_rooted : RootedFork 1 1 9 5 := by
  let labels : List ℕ := [14,1,10,11,5,12,4,9,13,2,16,0,15,3,6,8,7]
  let vi : List ℕ := [11,1,9,13,6,4,14,16,15,7,2,3,5,8,0,12,10]
  let ei : List ℕ := [0,15,14,13,7,6,3,4,5,1,2,8,12,0,9,11,10]
  have h : FastFiniteParentCertificate 16 (forkParent 1 1) labels vi ei := by
    let _ := fastFiniteParentCertificateDecidable 16 (forkParent 1 1) labels vi ei
    decide
  exact rootedFork_of_fast_certificate h (by decide)

theorem h1_1_1_9_6_rooted : RootedFork 1 1 9 6 := by
  let labels : List ℕ := [10,6,11,9,7,8,14,5,12,4,15,0,17,1,13,3,16,2]
  let vi : List ℕ := [11,13,17,15,9,7,1,4,5,3,0,2,8,14,6,10,16,12]
  let ei : List ℕ := [0,4,3,2,0,1,5,7,8,6,14,9,13,15,16,10,12,11]
  have h : FastFiniteParentCertificate 17 (forkParent 1 1) labels vi ei := by
    let _ := fastFiniteParentCertificateDecidable 17 (forkParent 1 1) labels vi ei
    decide
  exact rootedFork_of_fast_certificate h (by decide)

theorem h1_1_1_11_7_rooted : RootedFork 1 1 11 7 := by
  let labels : List ℕ := [11,9,10,6,12,8,13,5,16,7,14,4,19,0,20,2,15,3,17,1,18]
  let vi : List ℕ := [13,19,15,17,11,7,3,9,5,1,2,0,4,6,10,16,8,18,20,12,14]
  let ei : List ℕ := [0,1,0,2,4,5,3,9,6,8,10,7,16,15,17,11,18,19,14,12,13]
  have h : FastFiniteParentCertificate 20 (forkParent 1 1) labels vi ei := by
    let _ := fastFiniteParentCertificateDecidable 20 (forkParent 1 1) labels vi ei
    decide
  exact rootedFork_of_fast_certificate h (by decide)

theorem h1_1_1_15_9_rooted : RootedFork 1 1 15 9 := by
  let labels : List ℕ := [14,16,11,12,13,10,19,8,15,9,17,7,21,3,22,2,26,0,25,4,20,5,18,6,23,1,24]
  let vi : List ℕ := [17,25,15,13,19,21,23,11,7,9,5,2,3,4,0,8,1,10,22,6,20,12,14,24,26,18,16]
  let ei : List ℕ := [0,3,0,4,2,1,8,7,9,5,10,6,22,21,11,20,19,23,12,13,14,18,24,25,15,17,16]
  have h : FastFiniteParentCertificate 26 (forkParent 1 1) labels vi ei := by
    let _ := fastFiniteParentCertificateDecidable 26 (forkParent 1 1) labels vi ei
    decide
  exact rootedFork_of_fast_certificate h (by decide)

end Bounty


/- Supporting module: Q2Endpoint -/


namespace Bounty
open Math15.Graceful

def q2Tip (b : ℕ) : ℕ := if b=0 then 1 else 2+b

def EndpointFork (b k : ℕ) : Prop :=
  ∃ f, NatParentCertificate (2+b) (forkParent 1 1) f ∧ f (q2Tip b)=k

lemma q2Tip_bound (b : ℕ) : q2Tip b ≤ 2+b := by
  unfold q2Tip
  split_ifs <;> omega

lemma q2Parent_lt (j : ℕ) (hj : 0 < j) : forkParent 1 1 j < j := by
  unfold forkParent graftParent
  simp only [Nat.pred_eq_sub_one]
  split_ifs <;> omega

lemma q2Parent_graft (b : ℕ) :
    graftParent (2+b) (q2Tip b) (forkParent 1 1) = forkParent 1 1 := by
  funext j
  unfold forkParent graftParent q2Tip
  simp only [Nat.pred_eq_sub_one]
  split_ifs <;> omega

lemma EndpointFork.complement {b k : ℕ} (h : EndpointFork b k) :
    EndpointFork b (2+b-k) := by
  obtain ⟨f,hf,hk⟩ := h
  exact ⟨_,hf.complement (fun j hj _ => q2Parent_lt j hj),by simpa only [hk]⟩

lemma EndpointFork.extend {b k N : ℕ} (h : EndpointFork b k)
    (hN : 2*k+1 ≤ N) (hex : N ≠ 4*k+1) : EndpointFork (b+N) k := by
  obtain ⟨f,hf,hfk⟩ := h
  obtain ⟨p,hp,hfirst,hlast⟩ := exists_lower_endpoint_alpha_path hN hex
  let r := reverseNatPath N p
  have hr : NatAlphaPath N r ((N-1)/2) := hp.reverse
  have hrfirst : r 0 = if N%2=0 then N/2+k else N/2-k := by
    simpa only [r,reverseNatPath,Nat.sub_zero] using hlast
  have hrlast : r (N-1)=k := by simpa only [r,reverseNatPath,Nat.sub_self] using hfirst
  have hpar : ∀ j, 0<j → j≤2+b → forkParent 1 1 j<j := fun j hj _ => q2Parent_lt j hj
  have finish (g : ℕ → ℕ) (hg : NatParentCertificate (2+b) (forkParent 1 1) g)
      (hjoin : Nat.dist ((N-1)/2+1+g (q2Tip b))
        (shiftAboveCut ((N-1)/2) (2+b+1) (r 0)) = 2+b+1) : EndpointFork (b+N) k := by
    have hc := hg.graftAlphaPath (q2Tip_bound b) hpar hr.1 (by omega) hr.2.2 hjoin
    rw [q2Parent_graft] at hc
    refine ⟨graftLabel (2+b) ((N-1)/2) g r,?_,?_⟩
    · convert hc using 1 <;> omega
    · have htip : q2Tip (b+N)=2+b+N := by
        unfold q2Tip
        split_ifs <;> omega
      rw [htip]
      unfold graftLabel
      rw [ite_eq_right (by omega)]
      have hi : 2+b+N-(2+b+1)=N-1 := by omega
      rw [hi,hrlast]
      simp only [shiftAboveCut,ite_eq_left (show k≤(N-1)/2 by omega)]
  by_cases heven : N%2=0
  · apply finish f hf
    rw [hfk,hrfirst,ite_eq_left heven]
    apply graftJoin_high (by omega)
    omega
  · apply finish (fun i => 2+b-f i) (hf.complement hpar)
    rw [hfk,hrfirst,ite_eq_right heven]
    apply graftJoin_low (by omega) (by omega)
    have hk := hf.2.1 (q2Tip b) (q2Tip_bound b)
    omega

lemma EndpointFork.zero_step {b : ℕ} (h : EndpointFork b 0) : EndpointFork (b+1) 0 := by
  obtain ⟨f,hf,hzero⟩ := h
  let g := fun i => 2+b-f i
  have hg : NatParentCertificate (2+b) (forkParent 1 1) g :=
    hf.complement (fun j hj _ => q2Parent_lt j hj)
  have hp : NatGracefulPath 1 (fun _ => 0) := by
    refine ⟨?_,by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero],?_⟩
    · intro i j hi hj _; omega
    · intro i j hi hib hj hjb _; omega
  have hc := hg.graftAlphaPath (M := 1) (k := 0) (q2Tip_bound b)
    (fun j hj _ => q2Parent_lt j hj) hp (by omega)
    (by intro i hi hib; omega) (by
      simp only [g,hzero,shiftAboveCut,Nat.zero_le,ite_true]
      unfold Nat.dist
      omega)
  rw [q2Parent_graft] at hc
  refine ⟨graftLabel (2+b) 0 g (fun _ => 0),?_,?_⟩
  · convert hc using 1 <;> omega
  · change graftLabel (2+b) 0 g (fun _ => 0) (q2Tip (b+1))=0
    simp only [q2Tip,show b+1≠0 by omega,ite_false,graftLabel]
    rw [ite_eq_right (by omega)]
    simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, shiftAboveCut]

private lemma flat_Q2Endpoint_endpoint_seed_0 : EndpointFork 0 0 := by
  let f : List ℕ := [1,0,2]
  have h : FastFiniteParentCertificate 2 (forkParent 1 1) f [1,0,2] [0,0,1] := by
    let _ := fastFiniteParentCertificateDecidable 2 (forkParent 1 1) f [1,0,2] [0,0,1]
    decide
  exact ⟨forkListLabel f,h.toNat,by decide⟩

private lemma flat_Q2Endpoint_endpoint_seed_1 : EndpointFork 1 1 := by
  let f : List ℕ := [0,3,2,1]
  have h : FastFiniteParentCertificate 3 (forkParent 1 1) f [0,3,2,1] [0,1,2,0] := by
    let _ := fastFiniteParentCertificateDecidable 3 (forkParent 1 1) f [0,3,2,1] [0,1,2,0]
    decide
  exact ⟨forkListLabel f,h.toNat,by decide⟩

private lemma flat_Q2Endpoint_endpoint_seed_2 : EndpointFork 2 1 := by
  let f : List ℕ := [4,0,3,2,1]
  have h : FastFiniteParentCertificate 4 (forkParent 1 1) f [1,4,3,2,0] [0,3,2,1,0] := by
    let _ := fastFiniteParentCertificateDecidable 4 (forkParent 1 1) f [1,4,3,2,0] [0,3,2,1,0]
    decide
  exact ⟨forkListLabel f,h.toNat,by decide⟩

private lemma flat_Q2Endpoint_endpoint_seed_3 : EndpointFork 3 1 := by
  let f : List ℕ := [5,0,3,4,2,1]
  have h : FastFiniteParentCertificate 5 (forkParent 1 1) f [1,5,4,2,3,0] [0,4,3,1,2,0] := by
    let _ := fastFiniteParentCertificateDecidable 5 (forkParent 1 1) f [1,5,4,2,3,0] [0,4,3,1,2,0]
    decide
  exact ⟨forkListLabel f,h.toNat,by decide⟩

private lemma flat_Q2Endpoint_endpoint_seed_6 : EndpointFork 6 1 := by
  let f : List ℕ := [6,2,5,4,3,8,0,7,1]
  have h : FastFiniteParentCertificate 8 (forkParent 1 1) f [6,8,1,4,3,2,0,7,5] [0,3,2,1,0,4,7,6,5] := by
    let _ := fastFiniteParentCertificateDecidable 8 (forkParent 1 1) f [6,8,1,4,3,2,0,7,5] [0,3,2,1,0,4,7,6,5]
    decide
  exact ⟨forkListLabel f,h.toNat,by decide⟩

theorem endpointFork_zero (b : ℕ) : EndpointFork b 0 := by
  induction b with
  | zero => exact flat_Q2Endpoint_endpoint_seed_0
  | succ b ih => exact ih.zero_step

theorem endpointFork_one {b : ℕ} (hb : 1≤b) : EndpointFork b 1 := by
  by_cases hb1 : b=1
  · subst b; exact flat_Q2Endpoint_endpoint_seed_1
  by_cases hb2 : b=2
  · subst b; exact flat_Q2Endpoint_endpoint_seed_2
  by_cases hb3 : b=3
  · subst b; exact flat_Q2Endpoint_endpoint_seed_3
  by_cases hb6 : b=6
  · subst b; exact flat_Q2Endpoint_endpoint_seed_6
  have h := flat_Q2Endpoint_endpoint_seed_1.extend (N := b-1) (by omega) (by omega)
  convert h using 1 <;> omega

theorem endpointFork_large {k d : ℕ} (hk : 1≤k)
    (hd : if k=1 then 6≤d else 3*k+1≤d) : EndpointFork (d-2) k := by
  by_cases hk1 : k=1
  · subst k
    simp only [ite_true] at hd
    exact endpointFork_one (by omega)
  · simp only [ite_eq_right hk1] at hd
    by_cases hex : d-k=4*k+1
    · have h := (endpointFork_one (b := k-1) (by omega)).complement
      have hlabel : 2+(k-1)-1=k := by omega
      rw [hlabel] at h
      have hh := h.extend (N := d-k-1) (by omega) (by omega)
      convert hh using 1 <;> omega
    · have h := (endpointFork_zero (k-2)).complement
      have hlabel : 2+(k-2)-0=k := by omega
      rw [hlabel] at h
      have hh := h.extend (N := d-k) (by omega) hex
      convert hh using 1 <;> omega

end Bounty


/- Supporting module: Q2Short -/


namespace Bounty
open Math15.Graceful

def q2FinalPath (c i : ℕ) : ℕ := if i%2=0 then c+1-i/2 else i/2

lemma q2FinalPath_diff {c i : ℕ} (hi : 0 < i) (hib : i<c+2) :
    Nat.dist (q2FinalPath c (i-1)) (q2FinalPath c i)=c+2-i := by
  unfold q2FinalPath Nat.dist
  split_ifs <;> omega

lemma q2FinalPath_alpha (c : ℕ) : NatAlphaPath (c+2) (q2FinalPath c) (c/2) := by
  refine ⟨⟨?_,?_,?_⟩,by omega,?_⟩
  · intro i j hi hj heq
    unfold q2FinalPath at heq
    split_ifs at heq <;> omega
  · intro i hi
    unfold q2FinalPath
    split_ifs <;> omega
  · intro i j hi hib hj hjb heq
    rw [q2FinalPath_diff hi hib,q2FinalPath_diff hj hjb] at heq
    omega
  · intro j hj hjb
    unfold q2FinalPath
    split_ifs <;> omega

/-- The short-tail construction for the two unit outer arms. -/
theorem rootedFork_q2_short {d c : ℕ} (hc : 1≤c) (hshort : H1Coverage.SmallShort d c) :
    RootedFork 1 1 d c := by
  have hd : 2≤d := by
    unfold H1Coverage.SmallShort at hshort
    split_ifs at hshort <;> omega
  obtain ⟨f,hf,hk⟩ := endpointFork_large (k := (c+1)/2) (d := d) (by omega) hshort
  have hp := q2FinalPath_alpha c
  have hjoin : Nat.dist (c/2+1+f (q2Tip (d-2)))
      (shiftAboveCut (c/2) (2+(d-2)+1) (q2FinalPath c 0)) = 2+(d-2)+1 := by
    rw [hk]
    simp only [q2FinalPath,Nat.zero_mod,ite_true,Nat.zero_div,Nat.sub_zero]
    exact graftJoin_high (by omega) (by omega)
  have hg := hf.graftAlphaPath (q2Tip_bound (d-2)) (fun j hj _ => q2Parent_lt j hj)
    hp.1 (by omega) hp.2.2 hjoin
  rw [q2Parent_graft] at hg
  refine ⟨graftLabel (2+(d-2)) (c/2) f (q2FinalPath c),?_,?_⟩
  · convert hg using 1 <;> omega
  · have hz := graftLabel_zero (N := 2+(d-2)) (k := c/2) (f := f)
      (i := 1) (p := q2FinalPath c) (by rfl)
    have heq : 2+(d-2)+1+1=1+1+d := by omega
    rw [heq] at hz
    exact hz

end Bounty


/- Supporting module: Q2FiniteCover -/




namespace Bounty
open H1Coverage

theorem h1_q2_residual_small {d c : ℕ} (hd : 1 ≤ d) (hc : 1 ≤ c)
    (hlong : c<Cut 1 1 d+1) (hshort : ¬SmallShort d c) (hex : ¬(d=1 ∧ c=2)) :
    RootedFork 1 1 d c := by
  have hb := q2_finite_bound d c hd hc hlong hshort
  obtain ⟨hc9,hd15⟩ := hb
  interval_cases d
  · have hcset : c=1 := by
      norm_num [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, SmallShort,Cut,U,V] at * <;> omega
    subst c
    exact h1_1_1_1_1_rooted
  · have hcset : c=1 := by
      norm_num [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, SmallShort,Cut,U,V] at * <;> omega
    subst c
    exact h1_1_1_2_1_rooted
  · have hcset : c=1 ∨ c=2 ∨ c=3 := by
      norm_num [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, SmallShort,Cut,U,V] at * <;> omega
    rcases hcset with rfl | rfl | rfl
    · exact h1_1_1_3_1_rooted
    · exact h1_1_1_3_2_rooted
    · exact h1_1_1_3_3_rooted
  · have hcset : c=1 ∨ c=2 := by
      norm_num [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, SmallShort,Cut,U,V] at * <;> omega
    rcases hcset with rfl | rfl
    · exact h1_1_1_4_1_rooted
    · exact h1_1_1_4_2_rooted
  · have hcset : c=1 ∨ c=2 ∨ c=3 ∨ c=4 := by
      norm_num [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, SmallShort,Cut,U,V] at * <;> omega
    rcases hcset with rfl | rfl | rfl | rfl
    · exact h1_1_1_5_1_rooted
    · exact h1_1_1_5_2_rooted
    · exact h1_1_1_5_3_rooted
    · exact h1_1_1_5_4_rooted
  · have hcset : c=3 := by
      norm_num [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, SmallShort,Cut,U,V] at * <;> omega
    subst c
    exact h1_1_1_6_3_rooted
  · have hcset : c=5 := by
      norm_num [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, SmallShort,Cut,U,V] at * <;> omega
    subst c
    exact h1_1_1_7_5_rooted
  · norm_num [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, SmallShort,Cut,U,V] at * <;> omega
  · have hcset : c=5 ∨ c=6 := by
      norm_num [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, SmallShort,Cut,U,V] at * <;> omega
    rcases hcset with rfl | rfl
    · exact h1_1_1_9_5_rooted
    · exact h1_1_1_9_6_rooted
  · norm_num [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, SmallShort,Cut,U,V] at * <;> omega
  · have hcset : c=7 := by
      norm_num [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, SmallShort,Cut,U,V] at * <;> omega
    subst c
    exact h1_1_1_11_7_rooted
  · norm_num [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, SmallShort,Cut,U,V] at * <;> omega
  · norm_num [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, SmallShort,Cut,U,V] at * <;> omega
  · norm_num [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, SmallShort,Cut,U,V] at * <;> omega
  · have hcset : c=9 := by
      norm_num [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, SmallShort,Cut,U,V] at * <;> omega
    subst c
    exact h1_1_1_15_9_rooted


theorem rootedFork_q2_complete {d c : ℕ} (hd : 1 ≤ d) (hc : 1 ≤ c)
    (hex : ¬(d=1 ∧ c=2)) : RootedFork 1 1 d c := by
  by_cases hl : Cut 1 1 d+1 ≤ c
  · exact rootedFork_long (by omega) (by omega) hd (by omega) hl
  by_cases hs : SmallShort d c
  · exact rootedFork_q2_short hc hs
  exact h1_q2_residual_small hd hc (by omega) hs hex

end Bounty


/- Supporting module: H1Theorem -/






namespace Bounty
open H1Coverage

private theorem flat_H1Theorem_rootedFork_ordered (a b d c : ℕ)
    (ha : 1≤a) (hb : 1≤b) (hd : 1≤d) (hc : 1≤c)
    (hab : a≤b) (hex : ¬(a=1 ∧ b=1 ∧ d=1 ∧ c=2)) : RootedFork a b d c := by
  by_cases h22 : a=2 ∧ b=2
  · obtain ⟨rfl,rfl⟩ := h22
    exact rootedFork_twos hd hc
  have hne22 : a≠2 ∨ b≠2 := by omega
  by_cases h11 : a=1 ∧ b=1
  · obtain ⟨rfl,rfl⟩ := h11
    exact rootedFork_q2_complete hd hc (by omega)
  have hq : 2<a+b := by omega
  by_cases hshort : c≤2*d
  · by_cases hd10 : 10≤d
    · exact rootedFork_short_all hd10 hc hq hne22 hshort
    by_cases he : d≠3 ∨ c≠2
    · exact rootedFork_small_short hd (by omega) hc hshort he hq hne22
    · have hd3 : d=3 := by omega
      have hc2 : c=2 := by omega
      subst d
      subst c
      exact rootedFork_three_two ha hab hq hne22
  by_cases hlong : Cut a b d+1≤c
  · exact rootedFork_long ha hb hd hne22 hlong
  by_cases hleft : OuterAvailable a b d c
  · exact rootedFork_outer hb hd hc (by have := hleft.1; omega) hleft.2
  by_cases hright : OuterAvailable b a d c
  · exact rootedFork_swap hd
      (rootedFork_outer ha hd hc (by have := hright.1; omega) hright.2)
  exact rootedFork_tail_remaining ha hab hd (by omega) (by omega) hleft hright

/-- Every positive fork has a graceful labeling with zero at the prescribed
long-arm vertex, apart from the unique stated obstruction. -/
theorem rootedFork_all (a b d c : ℕ)
    (ha : 0<a) (hb : 0<b) (hd : 0<d) (hc : 0<c)
    (hex : ¬(a=1 ∧ b=1 ∧ d=1 ∧ c=2)) : RootedFork a b d c := by
  by_cases hab : a≤b
  · exact flat_H1Theorem_rootedFork_ordered a b d c ha hb hd hc hab hex
  · exact rootedFork_swap hd
      (flat_H1Theorem_rootedFork_ordered b a d c hb ha hd hc (by omega) (by omega))

end Bounty


/- Supporting module: LeafExtension -/

namespace Math15.Graceful

/-- Adjoining a leaf to a zero-labeled vertex preserves gracefulness, with the
new leaf labeled zero. The old labels are reflected in the new edge count. -/
theorem leaf_extension_labeling {n m : ℕ}
    (G : SimpleGraph (Fin n)) (K : SimpleGraph (Fin m))
    (j : Fin n → Fin m) (hj : Function.Injective j)
    (root : Fin n) (z : Fin m)
    (hz : ∀ x, j x ≠ z)
    (hcover : ∀ v, (∃ x, j x = v) ∨ v = z)
    (hedges : ∀ u v, K.Adj u v ↔
      (∃ x y, G.Adj x y ∧ j x = u ∧ j y = v) ∨
      (u = z ∧ v = j root) ∨ (u = j root ∧ v = z))
    (hcount : edgeCount K = edgeCount G + 1)
    (f : Fin n → ℕ) (hf : IsGracefulLabeling G f) (hroot : f root = 0) :
    ∃ g : Fin m → ℕ, IsGracefulLabeling K g ∧ g z = 0 ∧
      ∀ x, g (j x) = edgeCount G + 1 - f x := by
  classical
  let g : Fin m → ℕ := fun v =>
    if hv : ∃ x, j x = v then edgeCount G + 1 - f hv.choose else 0
  have hold (x : Fin n) : g (j x) = edgeCount G + 1 - f x := by
    have hx : ∃ y, j y = j x := ⟨x, rfl⟩
    simp only [g, dite_eq_left hx]
    exact congrArg (fun t => edgeCount G + 1 - f t) (hj hx.choose_spec)
  have hzero : g z = 0 := by
    have hnone : ¬ ∃ x, j x = z := by simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero] using hz
    simp only [g, dite_eq_right hnone]
  have hpos (x : Fin n) : 0 < g (j x) := by
    rw [hold]
    have := hf.2.1 x
    omega
  have hinj : Function.Injective g := by
    intro u v heq
    rcases hcover u with ⟨x, rfl⟩ | rfl <;>
      rcases hcover v with ⟨y, rfl⟩ | rfl
    · rw [hold, hold] at heq
      have hx := hf.2.1 x
      have hy := hf.2.1 y
      exact congrArg j (hf.1 (by omega))
    · have := hpos x
      rw [hzero] at heq
      omega
    · have := hpos y
      rw [hzero] at heq
      omega
    · rfl
  have hbound (v : Fin m) : g v ≤ edgeCount K := by
    rw [hcount]
    rcases hcover v with ⟨x, rfl⟩ | rfl
    · rw [hold]
      omega
    · rw [hzero]
      omega
  have holdDiff (x y : Fin n) :
      Nat.dist (g (j x)) (g (j y)) = Nat.dist (f x) (f y) := by
    rw [hold, hold]
    have hx := hf.2.1 x
    have hy := hf.2.1 y
    unfold Nat.dist
    omega
  have hnewDiff (u v : Fin m)
      (h : (u = z ∧ v = j root) ∨ (u = j root ∧ v = z)) :
      Nat.dist (g u) (g v) = edgeCount G + 1 := by
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, hzero, hold, hroot, Nat.dist]
  have hunique (u v x y : Fin m) (huv : K.Adj u v) (hxy : K.Adj x y)
      (heq : Nat.dist (g u) (g v) = Nat.dist (g x) (g y)) :
      (u = x ∧ v = y) ∨ (u = y ∧ v = x) := by
    rcases (hedges u v).1 huv with ⟨a, b, hab, rfl, rfl⟩ | huv'
    · rcases (hedges x y).1 hxy with ⟨c, d, hcd, rfl, rfl⟩ | hxy'
      · rw [holdDiff, holdDiff] at heq
        rcases hf.edge_unique hab hcd heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl ⟨rfl, rfl⟩
        · exact Or.inr ⟨rfl, rfl⟩
      · rw [holdDiff, hnewDiff x y hxy'] at heq
        have := hf.dist_le a b
        omega
    · rcases (hedges x y).1 hxy with ⟨c, d, hcd, rfl, rfl⟩ | hxy'
      · rw [hnewDiff u v huv', holdDiff] at heq
        have := hf.dist_le c d
        omega
      · rcases huv' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          rcases hxy' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero]
  refine ⟨g, ?_, hzero, hold⟩
  apply labeling_of_injective_differences K g hinj hbound
  rintro ⟨u, v⟩ ⟨x, y⟩ huv hadj hxy hadj' heq
  dsimp only at *
  rcases hunique u v x y hadj hadj' heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact (lt_asymm huv hxy).elim

/-- The same leaf extension preserves an alpha labeling. Reflection swaps the
old cut classes, and the new zero-labeled leaf joins the new lower class. -/
theorem alpha_leaf_extension_labeling {n m : ℕ}
    (G : SimpleGraph (Fin n)) (K : SimpleGraph (Fin m))
    (j : Fin n → Fin m) (hj : Function.Injective j)
    (root : Fin n) (z : Fin m)
    (hz : ∀ x, j x ≠ z)
    (hcover : ∀ v, (∃ x, j x = v) ∨ v = z)
    (hedges : ∀ u v, K.Adj u v ↔
      (∃ x y, G.Adj x y ∧ j x = u ∧ j y = v) ∨
      (u = z ∧ v = j root) ∨ (u = j root ∧ v = z))
    (hcount : edgeCount K = edgeCount G + 1)
    (f : Fin n → ℕ) (k : ℕ) (hf : IsAlphaLabeling G f k) (hroot : f root = 0) :
    ∃ g : Fin m → ℕ, IsAlphaLabeling K g (edgeCount G - k) ∧ g z = 0 ∧
      ∀ x, g (j x) = edgeCount G + 1 - f x := by
  obtain ⟨g, hg, hzero, hold⟩ :=
    leaf_extension_labeling G K j hj root z hz hcover hedges hcount f hf.1 hroot
  refine ⟨g, ⟨hg, ?_, ?_⟩, hzero, hold⟩
  · rw [hcount]
    omega
  · intro u v huv
    rcases (hedges u v).1 huv with ⟨a, b, hab, rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [hold, hold]
      have ha := hf.1.2.1 a
      have hb := hf.1.2.1 b
      have hk := hf.2.1
      rcases hf.2.2 a b hab with hab' | hba'
      · right
        omega
      · left
        omega
    · rw [hzero, hold, hroot]
      left
      omega
    · rw [hzero, hold, hroot]
      right
      omega

/-- Existence-only alpha form, retaining zero at the newly adjoined leaf. -/
theorem exists_alpha_leaf_extension {n m : ℕ}
    (G : SimpleGraph (Fin n)) (K : SimpleGraph (Fin m))
    (j : Fin n → Fin m) (hj : Function.Injective j)
    (root : Fin n) (z : Fin m)
    (hz : ∀ x, j x ≠ z)
    (hcover : ∀ v, (∃ x, j x = v) ∨ v = z)
    (hedges : ∀ u v, K.Adj u v ↔
      (∃ x y, G.Adj x y ∧ j x = u ∧ j y = v) ∨
      (u = z ∧ v = j root) ∨ (u = j root ∧ v = z))
    (hcount : edgeCount K = edgeCount G + 1)
    (k : ℕ) (hlabel : ∃ f, IsAlphaLabeling G f k ∧ f root = 0) :
    ∃ g, IsAlphaLabeling K g (edgeCount G - k) ∧ g z = 0 := by
  obtain ⟨f, hf, hroot⟩ := hlabel
  obtain ⟨g, hg, hzero, _⟩ :=
    alpha_leaf_extension_labeling G K j hj root z hz hcover hedges hcount f k hf hroot
  exact ⟨g, hg, hzero⟩

/-- Existence-only form of the leaf extension construction. -/
theorem isGraceful_leaf_extension {n m : ℕ}
    (G : SimpleGraph (Fin n)) (K : SimpleGraph (Fin m))
    (j : Fin n → Fin m) (hj : Function.Injective j)
    (root : Fin n) (z : Fin m)
    (hz : ∀ x, j x ≠ z)
    (hcover : ∀ v, (∃ x, j x = v) ∨ v = z)
    (hedges : ∀ u v, K.Adj u v ↔
      (∃ x y, G.Adj x y ∧ j x = u ∧ j y = v) ∨
      (u = z ∧ v = j root) ∨ (u = j root ∧ v = z))
    (hcount : edgeCount K = edgeCount G + 1)
    (hlabel : ∃ f, IsGracefulLabeling G f ∧ f root = 0) :
    ∃ g, IsGracefulLabeling K g ∧ g z = 0 := by
  obtain ⟨f, hf, hroot⟩ := hlabel
  obtain ⟨g, hg, hz, _⟩ :=
    leaf_extension_labeling G K j hj root z hz hcover hedges hcount f hf hroot
  exact ⟨g, hg, hz⟩

end Math15.Graceful


/- Supporting module: ForkTripleStem -/



namespace Bounty
open Math15.Graceful

def forkTripleSize (a b e c : ℕ) : ℕ := a+b+(e+c)

def forkTripleStemParent (a b e c j : ℕ) : ℕ :=
  if j≤forkTripleSize a b e c then forkParent a b j
  else if j=forkTripleSize a b e c+1 then a+b+e else j-1

def forkTripleStem (a b e c d : ℕ) : SimpleGraph (Fin (forkTripleSize a b e c+d+1)) :=
  parentGraph (forkTripleSize a b e c+d) (forkTripleStemParent a b e c)

lemma forkTriple_forkParent_lt (a b j : ℕ) (hj : 0<j) : forkParent a b j<j := by
  unfold forkParent graftParent
  simp only [Nat.pred_eq_sub_one]
  split_ifs <;> omega

lemma forkTripleStemParent_lt (a b e c j : ℕ) (hj : 0<j) :
    forkTripleStemParent a b e c j<j := by
  unfold forkTripleStemParent forkTripleSize
  split_ifs
  · exact forkTriple_forkParent_lt _ _ _ hj
  all_goals omega

lemma forkTripleStem_edgeCount (a b e c d : ℕ) :
    edgeCount (forkTripleStem a b e c d)=forkTripleSize a b e c+d :=
  parentGraph_edgeCount _ _ (fun j hj _ => forkTripleStemParent_lt _ _ _ _ j hj)

lemma forkTripleStem_isTree (a b e c d : ℕ) : (forkTripleStem a b e c d).IsTree :=
  parentGraph_isTree _ _ (fun j hj _ => forkTripleStemParent_lt _ _ _ _ j hj)

lemma forkTripleStem_zero (a b e c : ℕ) :
    forkTripleStem a b e c 0=parentGraph (forkTripleSize a b e c) (forkParent a b) := by
  ext u v
  have hu : u.val≤forkTripleSize a b e c := by have := u.isLt; omega
  have hv : v.val≤forkTripleSize a b e c := by have := v.isLt; omega
  change ((_ ∧ _) ∨ (_ ∧ _)) ↔ ((_ ∧ _) ∨ (_ ∧ _))
  simp only [forkTripleStemParent,ite_eq_left hu,ite_eq_left hv]

def forkTripleStemTip (a b e c d : ℕ) : Fin (forkTripleSize a b e c+d+1) :=
  ⟨if d=0 then a+b+e else forkTripleSize a b e c+d, by
    unfold forkTripleSize
    split_ifs <;> omega⟩

private lemma flat_ForkTripleStem_forkTriple_leaf_edges {a b : ℕ}
    (G : SimpleGraph (Fin a)) (K : SimpleGraph (Fin b))
    (j : Fin a → Fin b) (r : Fin a) (z : Fin b)
    (hcover : ∀ v, (∃ x, j x=v) ∨ v=z)
    (hold : ∀ x y, K.Adj (j x) (j y) ↔ G.Adj x y)
    (hnew : ∀ x, K.Adj z (j x) ↔ x=r) :
    ∀ u v, K.Adj u v ↔
      (∃ x y, G.Adj x y ∧ j x=u ∧ j y=v) ∨
      (u=z ∧ v=j r) ∨ (u=j r ∧ v=z) := by
  intro u v
  constructor
  · intro h
    rcases hcover u with ⟨x,rfl⟩ | rfl <;> rcases hcover v with ⟨y,rfl⟩ | rfl
    · exact Or.inl ⟨x,y,(hold x y).1 h,rfl,rfl⟩
    · have hx := (hnew x).1 h.symm
      exact Or.inr (Or.inr ⟨congrArg j hx,rfl⟩)
    · have hy := (hnew y).1 h
      exact Or.inr (Or.inl ⟨rfl,congrArg j hy⟩)
    · exact (K.irrefl h).elim
  · rintro (⟨x,y,hxy,rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
    · exact (hold x y).2 hxy
    · exact (hnew r).2 rfl
    · exact ((hnew r).2 rfl).symm

/-- Extend the prescribed zero of an ordinary graceful fork along an arbitrary stem. -/
theorem RootedFork.extendStem {a b e c : ℕ} (h : RootedFork a b e c) (d : ℕ) :
    ∃ f, IsGracefulLabeling (forkTripleStem a b e c d) f ∧
      f (forkTripleStemTip a b e c d)=0 := by
  induction d with
  | zero =>
    obtain ⟨f,hf,hpin⟩ := h
    have hg := hf.isGracefulLabeling (fun j hj _ => forkTriple_forkParent_lt a b j hj)
    refine ⟨fun i => f i.val,?_,hpin⟩
    simpa only [forkTripleStem_zero, forkTripleSize, Nat.add_zero] using hg
  | succ d ih =>
    obtain ⟨f,hf,hzero⟩ := ih
    let N := forkTripleSize a b e c
    let j : Fin (N+d+1) → Fin (N+(d+1)+1) := fun x => ⟨x.val,by have := x.isLt; omega⟩
    let z : Fin (N+(d+1)+1) := ⟨N+d+1,by omega⟩
    have hj : Function.Injective j := by
      intro x y h
      apply Fin.ext
      exact congrArg (fun t : Fin (N+(d+1)+1) => t.val) h
    have hz : ∀ x, j x≠z := by
      intro x h
      have := congrArg Fin.val h
      have := x.isLt
      dsimp [j,z] at *
      omega
    have hcover : ∀ v, (∃ x, j x=v) ∨ v=z := by
      intro v
      by_cases hv : v.val<N+d+1
      · exact Or.inl ⟨⟨v.val,hv⟩,rfl⟩
      · right
        apply Fin.ext
        have := v.isLt
        dsimp [z]
        omega
    have hold (x y : Fin (N+d+1)) : (forkTripleStem a b e c (d+1)).Adj (j x) (j y) ↔
        (forkTripleStem a b e c d).Adj x y := Iff.rfl
    have hparent : forkTripleStemParent a b e c (N+d+1)=(forkTripleStemTip a b e c d).val := by
      change forkTripleStemParent a b e c (N+d+1)=if d=0 then a+b+e else N+d
      unfold forkTripleStemParent
      dsimp [N]
      split_ifs <;> omega
    have hnew (x : Fin (N+d+1)) : (forkTripleStem a b e c (d+1)).Adj z (j x) ↔
        x=forkTripleStemTip a b e c d := by
      have hx := x.isLt
      change ((N+d+1<x.val ∧ _) ∨ (x.val<N+d+1 ∧ _)) ↔ _
      rw [hparent]
      constructor
      · rintro (h | h)
        · omega
        · exact Fin.ext h.2.symm
      · intro h
        exact Or.inr ⟨hx,(congrArg Fin.val h).symm⟩
    have hcount : edgeCount (forkTripleStem a b e c (d+1))=
        edgeCount (forkTripleStem a b e c d)+1 := by
      rw [forkTripleStem_edgeCount,forkTripleStem_edgeCount]
      omega
    obtain ⟨g,hg,hgz,_⟩ := leaf_extension_labeling (forkTripleStem a b e c d)
      (forkTripleStem a b e c (d+1)) j hj (forkTripleStemTip a b e c d) z hz hcover
      (flat_ForkTripleStem_forkTriple_leaf_edges _ _ j _ z hcover hold hnew) hcount f hf hzero
    refine ⟨g,hg,?_⟩
    have heq : forkTripleStemTip a b e c (d+1)=z := by
      apply Fin.ext
      simp only [forkTripleStemTip,ite_eq_right (show ¬d+1=0 by omega)]
      dsimp [z,N]
      omega
    rwa [heq]

/-- Transfer the numeric alpha certificate to the usual parent-ordered path graph. -/
theorem NatAlphaPath.toParent {N k : ℕ} {p : ℕ → ℕ} (h : NatAlphaPath (N+1) p k) :
    IsAlphaLabeling (parentGraph N Nat.pred) (fun i => p i.val) k := by
  refine ⟨h.1.parentCertificate.isGracefulLabeling (fun j hj _ => by simp only [Nat.pred_eq_sub_one]; omega),?_,?_⟩
  · rw [parentGraph_edgeCount N Nat.pred (fun j hj _ => by simp only [Nat.pred_eq_sub_one]; omega)]
    have := h.2.1
    omega
  · intro u v huv
    rcases huv with ⟨huv,hpar⟩ | ⟨hvu,hpar⟩
    · have hc := h.2.2 v.val (by omega) v.isLt
      simpa only [Nat.pred_eq_sub_one] using hpar ▸ hc
    · have hc := h.2.2 u.val (by omega) u.isLt
      have hh : (p v.val≤k ∧ k<p u.val) ∨ (p u.val≤k ∧ k<p v.val) := by
        simpa only [Nat.pred_eq_sub_one] using hpar ▸ hc
      exact hh.symm

end Bounty


/- Supporting module: TripleSpider -/

namespace Bounty

/-- The two connecting paths have lengths `d,e`; the five pendant paths
have lengths `a,b,c,f,g`. Vertices of the connecting path are indexed first. -/
def tripleSpiderEdges (a b c d e f g : ℕ) : ℕ := d+e+a+b+c+f+g

def tripleSpiderParent (a b c d e f _g j : ℕ) : ℕ :=
  if j = d+e+1 ∨ j = d+e+a+1 then 0
  else if j = d+e+a+b+1 then d
  else if j = d+e+a+b+c+1 ∨ j = d+e+a+b+c+f+1 then d+e
  else j-1

def tripleSpider (a b c d e f g : ℕ) :
    SimpleGraph (Fin (tripleSpiderEdges a b c d e f g+1)) :=
  parentGraph (tripleSpiderEdges a b c d e f g) (tripleSpiderParent a b c d e f g)

theorem tripleSpiderParent_lt (a b c d e f g j : ℕ) (hj : 0 < j) :
    tripleSpiderParent a b c d e f g j < j := by
  unfold tripleSpiderParent
  split_ifs <;> omega

theorem tripleSpider_edgeCount (a b c d e f g : ℕ) :
    Math15.Graceful.edgeCount (tripleSpider a b c d e f g) =
      tripleSpiderEdges a b c d e f g :=
  parentGraph_edgeCount _ _ (fun j hj _ => tripleSpiderParent_lt _ _ _ _ _ _ _ j hj)

theorem tripleSpider_isTree (a b c d e f g : ℕ) :
    (tripleSpider a b c d e f g).IsTree :=
  parentGraph_isTree _ _ (fun j hj _ => tripleSpiderParent_lt _ _ _ _ _ _ _ j hj)

theorem tripleSpider_isGraceful_of_certificate {a b c d e f g : ℕ} {label : ℕ → ℕ}
    (h : NatParentCertificate (tripleSpiderEdges a b c d e f g)
      (tripleSpiderParent a b c d e f g) label) :
    Math15.Graceful.IsGraceful (tripleSpider a b c d e f g) :=
  h.isGraceful (fun j hj _ => tripleSpiderParent_lt _ _ _ _ _ _ _ j hj)

end Bounty


/- Supporting module: IsoTransport -/

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
      have hrev : q.2 < q.1 := by simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, h1, h2] using hp
      exact (lt_asymm hq hrev).elim

theorem isGraceful_iff_of_iso {n m : ℕ} {G : SimpleGraph (Fin n)}
    {H : SimpleGraph (Fin m)} (e : G ≃g H) : IsGraceful G ↔ IsGraceful H :=
  ⟨isGraceful_of_iso e.symm, isGraceful_of_iso e⟩

end Math15.Graceful


/- Supporting module: ForkTripleSymmetry -/


namespace Bounty
open Math15.Graceful

def forkTripleSwapNat (a b c d e f g i : ℕ) : ℕ :=
  if i ≤ d+e then d+e-i
  else if i ≤ d+e+a+b then i+c+f+g
  else if i ≤ d+e+a+b+c then i+f+g-(a+b)
  else i-(a+b+c)

def forkTripleSwap (a b c d e f g : ℕ) (i : Fin (tripleSpiderEdges a b c d e f g+1)) :
    Fin (tripleSpiderEdges f g c e d a b+1) :=
  ⟨forkTripleSwapNat a b c d e f g i.val, by
    have hi := i.isLt
    unfold forkTripleSwapNat tripleSpiderEdges at *
    split_ifs <;> omega⟩

lemma forkTripleSwap_inverse (a b c d e f g : ℕ) (i : Fin (tripleSpiderEdges a b c d e f g+1)) :
    forkTripleSwap f g c e d a b (forkTripleSwap a b c d e f g i) = i := by
  apply Fin.ext
  have hi := i.isLt
  change forkTripleSwapNat f g c e d a b (forkTripleSwapNat a b c d e f g i.val) = i.val
  dsimp only [tripleSpiderEdges] at hi
  unfold forkTripleSwapNat
  split_ifs <;> omega

lemma forkTripleParent_spine {a b c d e f g i : ℕ} (hi : i≤d+e) :
    tripleSpiderParent a b c d e f g i=i-1 := by
  unfold tripleSpiderParent
  split_ifs <;> omega

lemma forkTripleSwap_parent_edge {a b c d e f g i : ℕ} (ha : 0<a) (hb : 0<b) (hc : 0<c) (hd : 0<d) (he : 0<e) (hf : 0<f) (hg : 0<g)
    (hi : 0 < i) (hib : i ≤ tripleSpiderEdges a b c d e f g) :
    (forkTripleSwapNat a b c d e f g (tripleSpiderParent a b c d e f g i) < forkTripleSwapNat a b c d e f g i ∧
      tripleSpiderParent f g c e d a b (forkTripleSwapNat a b c d e f g i) =
        forkTripleSwapNat a b c d e f g (tripleSpiderParent a b c d e f g i)) ∨
    (forkTripleSwapNat a b c d e f g i < forkTripleSwapNat a b c d e f g (tripleSpiderParent a b c d e f g i) ∧
      tripleSpiderParent f g c e d a b (forkTripleSwapNat a b c d e f g (tripleSpiderParent a b c d e f g i)) =
        forkTripleSwapNat a b c d e f g i) := by
  dsimp only [tripleSpiderEdges] at hib
  have hs (j : ℕ) (hj : j ≤ d+e) : forkTripleSwapNat a b c d e f g j = d+e-j := by
    simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, forkTripleSwapNat,hj]
  have ha (j : ℕ) (hj : d+e < j) (hjb : j ≤ d+e+a+b) :
      forkTripleSwapNat a b c d e f g j = j+c+f+g := by
    simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, forkTripleSwapNat,show ¬j ≤ d+e by omega,hjb]
  have hb (j : ℕ) (hj : d+e+a+b < j) (hjb : j ≤ d+e+a+b+c) :
      forkTripleSwapNat a b c d e f g j = j+f+g-(a+b) := by
    simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, forkTripleSwapNat,show ¬j ≤ d+e by omega,show ¬j ≤ d+e+a+b by omega,hjb]
  have hz (j : ℕ) (hj : d+e+a+b+c < j) : forkTripleSwapNat a b c d e f g j = j-(a+b+c) := by
    simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, forkTripleSwapNat,show ¬j ≤ d+e by omega,show ¬j ≤ d+e+a+b by omega,
      show ¬j ≤ d+e+a+b+c by omega]
  by_cases hsp : i ≤ d+e
  · rw [forkTripleParent_spine hsp,hs i hsp,hs (i-1) (by omega)]
    right
    rw [forkTripleParent_spine (by omega)]
    omega
  by_cases har : i ≤ d+e+a+b
  · rw [ha i (by omega) har]
    by_cases hf : i=d+e+1 ∨ i=d+e+a+1
    · have hp : tripleSpiderParent a b c d e f g i = 0 := by
        unfold tripleSpiderParent
        split_ifs <;> omega
      rw [hp,hs 0 (by omega)]
      left
      constructor
      · omega
      · unfold tripleSpiderParent
        split_ifs <;> omega
    · have hp : tripleSpiderParent a b c d e f g i = i-1 := by
        unfold tripleSpiderParent
        split_ifs <;> omega
      rw [hp,ha (i-1) (by omega) (by omega)]
      left
      constructor
      · omega
      · unfold tripleSpiderParent
        split_ifs <;> omega
  by_cases htail : i ≤ d+e+a+b+c
  · rw [hb i (by omega) htail]
    by_cases hf : i=d+e+a+b+1
    · have hp : tripleSpiderParent a b c d e f g i = d := by
        unfold tripleSpiderParent
        split_ifs <;> omega
      rw [hp,hs d (by omega)]
      left
      constructor
      · omega
      · unfold tripleSpiderParent
        split_ifs <;> omega
    · have hp : tripleSpiderParent a b c d e f g i = i-1 := by
        unfold tripleSpiderParent
        split_ifs <;> omega
      rw [hp,hb (i-1) (by omega) (by omega)]
      left
      constructor
      · omega
      · unfold tripleSpiderParent
        split_ifs <;> omega
  · rw [hz i (by omega)]
    by_cases hf : i=d+e+a+b+c+1 ∨ i=d+e+a+b+c+f+1
    · have hp : tripleSpiderParent a b c d e f g i = d+e := by
        unfold tripleSpiderParent
        split_ifs <;> omega
      rw [hp,hs (d+e) (by omega)]
      left
      constructor
      · omega
      · unfold tripleSpiderParent
        split_ifs <;> omega
    · have hp : tripleSpiderParent a b c d e f g i = i-1 := by
        unfold tripleSpiderParent
        split_ifs <;> omega
      rw [hp,hz (i-1) (by omega)]
      left
      constructor
      · omega
      · unfold tripleSpiderParent
        split_ifs <;> omega

lemma forkTripleSwap_hom {a b c d e f g : ℕ} (ha : 0<a) (hb : 0<b) (hc : 0<c) (hd : 0<d) (he : 0<e) (hf : 0<f) (hg : 0<g)
    (x y : Fin (tripleSpiderEdges a b c d e f g+1)) (h : (tripleSpider a b c d e f g).Adj x y) :
    (tripleSpider f g c e d a b).Adj (forkTripleSwap a b c d e f g x) (forkTripleSwap a b c d e f g y) := by
  change (_ < _ ∧ _ = _) ∨ (_ < _ ∧ _ = _)
  rcases h with ⟨hxy,hp⟩ | ⟨hyx,hp⟩
  · have h := forkTripleSwap_parent_edge ha hb hc hd he hf hg (i := y.val) (by omega) (by have := y.isLt; omega)
    rw [hp] at h
    exact h
  · have h := forkTripleSwap_parent_edge ha hb hc hd he hf hg (i := x.val) (by omega) (by have := x.isLt; omega)
    rw [hp] at h
    exact h.symm

def forkTripleSwapIso {a b c d e f g : ℕ} (ha : 0<a) (hb : 0<b) (hc : 0<c) (hd : 0<d) (he : 0<e) (hf : 0<f) (hg : 0<g) :
    tripleSpider a b c d e f g ≃g tripleSpider f g c e d a b where
  toFun := forkTripleSwap a b c d e f g
  invFun := forkTripleSwap f g c e d a b
  left_inv := forkTripleSwap_inverse a b c d e f g
  right_inv := forkTripleSwap_inverse f g c e d a b
  map_rel_iff' := by
    intro x y
    constructor
    · intro h
      have hr := forkTripleSwap_hom hf hg hc he hd ha hb _ _ h
      change (tripleSpider a b c d e f g).Adj
        (forkTripleSwap f g c e d a b (forkTripleSwap a b c d e f g x)) (forkTripleSwap f g c e d a b (forkTripleSwap a b c d e f g y)) at hr
      simpa only [forkTripleSwap_inverse] using hr
    · exact forkTripleSwap_hom ha hb hc hd he hf hg x y


end Bounty


/- Supporting module: H2TripleUnion -/


namespace Math15.Graceful

/-- Connected pieces that cover a tree and share a vertex cover all its edges. -/
theorem tree_union_edges {n a b : ℕ}
    (K : SimpleGraph (Fin n)) (L : SimpleGraph (Fin a)) (R : SimpleGraph (Fin b))
    (i : Fin a → Fin n) (j : Fin b → Fin n)
    (hi : Function.Injective i) (hj : Function.Injective j)
    (hK : K.IsTree) (hL : L.Connected) (hR : R.Connected)
    (linkL : Fin a) (linkR : Fin b) (hlink : i linkL = j linkR)
    (hcover : ∀ v, (∃ x, i x = v) ∨ (∃ y, j y = v))
    (hmapL : ∀ x y, L.Adj x y → K.Adj (i x) (i y))
    (hmapR : ∀ x y, R.Adj x y → K.Adj (j x) (j y)) :
    ∀ u v, K.Adj u v ↔
      (∃ x y, L.Adj x y ∧ i x = u ∧ i y = v) ∨
      (∃ x y, R.Adj x y ∧ j x = u ∧ j y = v) := by
  let U : SimpleGraph (Fin n) := {
    Adj := fun u v =>
      (∃ x y, L.Adj x y ∧ i x = u ∧ i y = v) ∨
      (∃ x y, R.Adj x y ∧ j x = u ∧ j y = v)
    symm := by
      constructor
      intro u v h
      rcases h with ⟨x,y,hxy,hx,hy⟩ | ⟨x,y,hxy,hx,hy⟩
      · exact Or.inl ⟨y,x,hxy.symm,hy,hx⟩
      · exact Or.inr ⟨y,x,hxy.symm,hy,hx⟩
    loopless := by
      constructor
      intro u h
      rcases h with ⟨x,y,hxy,hx,hy⟩ | ⟨x,y,hxy,hx,hy⟩
      · exact hxy.ne (hi (hx.trans hy.symm))
      · exact hxy.ne (hj (hx.trans hy.symm)) }
  let li : L →g U := ⟨i, fun {x y} h => Or.inl ⟨x,y,h,rfl,rfl⟩⟩
  let rj : R →g U := ⟨j, fun {x y} h => Or.inr ⟨x,y,h,rfl,rfl⟩⟩
  have hreach (v : Fin n) : U.Reachable v (i linkL) := by
    rcases hcover v with ⟨x,rfl⟩ | ⟨y,rfl⟩
    · exact (hL.preconnected x linkL).map li
    · rw [hlink]
      exact (hR.preconnected y linkR).map rj
  have hU : U.Connected := by
    letI : Nonempty (Fin n) := ⟨i linkL⟩
    exact ⟨fun u v => (hreach u).trans (hreach v).symm⟩
  have hle : U ≤ K := by
    intro u v h
    rcases h with ⟨x,y,hxy,rfl,rfl⟩ | ⟨x,y,hxy,rfl,rfl⟩
    · exact hmapL x y hxy
    · exact hmapR x y hxy
  have hge : K ≤ U := (SimpleGraph.isTree_iff_minimal_connected.mp hK).2 hU hle
  exact fun u v => ⟨fun h => hge h, fun h => hle h⟩

end Math15.Graceful


/- Supporting module: ForkTripleGeometry -/



namespace Bounty
open Math15.Graceful

def forkTripleMapNat (a b c d e f g i : ℕ) : ℕ :=
  if i<f then d+e+a+b+c+f-i
  else if i=f then d+e
  else if i≤f+g then d+e+a+b+c+i
  else if i≤f+g+e then d+e+f+g-i
  else if i≤forkTripleSize f g e c then d+e+a+b+i-(f+g+e)
  else d+forkTripleSize f g e c-i

def forkTripleMap (a b c d e f g : ℕ) (i : Fin (forkTripleSize f g e c+d+1)) :
    Fin (tripleSpiderEdges a b c d e f g+1) :=
  ⟨forkTripleMapNat a b c d e f g i.val, by
    have hi := i.isLt
    unfold forkTripleMapNat forkTripleSize tripleSpiderEdges at *
    split_ifs <;> omega⟩

def forkTriplePairNat (a d e i : ℕ) : ℕ :=
  if i<a then d+e+a-i else if i=a then 0 else d+e+i

def forkTriplePair (a b c d e f g : ℕ) (i : Fin (a+b+1)) :
    Fin (tripleSpiderEdges a b c d e f g+1) :=
  ⟨forkTriplePairNat a d e i.val, by
    have hi := i.isLt
    unfold forkTriplePairNat tripleSpiderEdges at *
    split_ifs <;> omega⟩

lemma forkTripleMap_injective (a b c d e f g : ℕ) :
    Function.Injective (forkTripleMap a b c d e f g) := by
  intro i j heq
  apply Fin.ext
  have hi := i.isLt
  have hj := j.isLt
  have h := congrArg Fin.val heq
  change forkTripleMapNat a b c d e f g i.val=forkTripleMapNat a b c d e f g j.val at h
  unfold forkTripleMapNat forkTripleSize at h hi hj
  split_ifs at h <;> omega

lemma forkTriplePair_injective (a b c d e f g : ℕ) :
    Function.Injective (forkTriplePair a b c d e f g) := by
  intro i j heq
  apply Fin.ext
  have hi := i.isLt
  have hj := j.isLt
  have h := congrArg Fin.val heq
  change forkTriplePairNat a d e i.val=forkTriplePairNat a d e j.val at h
  unfold forkTriplePairNat at h
  split_ifs at h <;> omega

lemma forkTripleMap_tip {a b c d e f g : ℕ} (hd : 0<d) :
    forkTripleMap a b c d e f g (forkTripleStemTip f g e c d)=
      forkTriplePair a b c d e f g ⟨a,by omega⟩ := by
  apply Fin.ext
  change forkTripleMapNat a b c d e f g (if d=0 then f+g+e else forkTripleSize f g e c+d)=
    forkTriplePairNat a d e a
  simp only [ite_eq_right (show d≠0 by omega)]
  unfold forkTripleMapNat forkTriplePairNat forkTripleSize
  split_ifs <;> omega

lemma forkTripleMap_overlap {a b c d e f g : ℕ} (hd : 0<d)
    (i : Fin (forkTripleSize f g e c+d+1)) (j : Fin (a+b+1)) :
    forkTripleMap a b c d e f g i=forkTriplePair a b c d e f g j ↔
      i=forkTripleStemTip f g e c d ∧ j=⟨a,by omega⟩ := by
  constructor
  · intro heq
    have hi := i.isLt
    have hj := j.isLt
    have h := congrArg Fin.val heq
    change forkTripleMapNat a b c d e f g i.val=forkTriplePairNat a d e j.val at h
    have houtside : forkTripleMapNat a b c d e f g i.val≤d+e ∨
        d+e+a+b<forkTripleMapNat a b c d e f g i.val := by
      unfold forkTripleMapNat forkTripleSize
      split_ifs <;> omega
    have hj' : j.val=a := by
      by_contra hne
      have hinside : d+e<forkTriplePairNat a d e j.val ∧
          forkTriplePairNat a d e j.val≤d+e+a+b := by
        unfold forkTriplePairNat
        split_ifs <;> omega
      omega
    have hjeq : j=⟨a,by omega⟩ := Fin.ext hj'
    refine ⟨?_,hjeq⟩
    apply forkTripleMap_injective a b c d e f g
    rw [heq,hjeq]
    exact (forkTripleMap_tip hd).symm
  · rintro ⟨rfl,rfl⟩
    exact forkTripleMap_tip hd

def forkTripleInverse (a b c d e f g v : ℕ) : ℕ :=
  if v≤d+e then
    if v=d+e then f else if d≤v then d+e+f+g-v else d+forkTripleSize f g e c-v
  else if v≤d+e+a+b+c then f+g+e+v-(d+e+a+b)
  else if v≤d+e+a+b+c+f then d+e+a+b+c+f-v
  else v-(d+e+a+b+c)

lemma forkTripleMap_cover (a b c d e f g : ℕ)
    (v : Fin (tripleSpiderEdges a b c d e f g+1)) :
    (∃ i, forkTripleMap a b c d e f g i=v) ∨
      (∃ j, forkTriplePair a b c d e f g j=v) := by
  have hv := v.isLt
  dsimp only [tripleSpiderEdges] at hv
  by_cases hpair : d+e<v.val ∧ v.val≤d+e+a+b
  · right
    by_cases ha : v.val≤d+e+a
    · refine ⟨⟨d+e+a-v.val,by omega⟩,?_⟩
      apply Fin.ext
      change forkTriplePairNat a d e (d+e+a-v.val)=v.val
      unfold forkTriplePairNat
      split_ifs <;> omega
    · refine ⟨⟨v.val-(d+e),by omega⟩,?_⟩
      apply Fin.ext
      change forkTriplePairNat a d e (v.val-(d+e))=v.val
      unfold forkTriplePairNat
      split_ifs <;> omega
  · have hbound : forkTripleInverse a b c d e f g v.val<forkTripleSize f g e c+d+1 := by
      unfold forkTripleInverse forkTripleSize
      split_ifs <;> omega
    left
    refine ⟨⟨forkTripleInverse a b c d e f g v.val,hbound⟩,?_⟩
    apply Fin.ext
    change forkTripleMapNat a b c d e f g (forkTripleInverse a b c d e f g v.val)=v.val
    unfold forkTripleInverse forkTripleMapNat forkTripleSize
    split_ifs <;> omega

lemma forkTriplePair_parent_edge {a b c d e f g i : ℕ}
    (ha : 0<a) (hb : 0<b) (hd : 0<d) (he : 0<e)
    (hi : 0 < i) (hib : i≤a+b) :
    (forkTriplePairNat a d e (i-1)<forkTriplePairNat a d e i ∧
      tripleSpiderParent a b c d e f g (forkTriplePairNat a d e i)=forkTriplePairNat a d e (i-1)) ∨
    (forkTriplePairNat a d e i<forkTriplePairNat a d e (i-1) ∧
      tripleSpiderParent a b c d e f g (forkTriplePairNat a d e (i-1))=forkTriplePairNat a d e i) := by
  rcases lt_trichotomy i a with hia | hia | hia
  · simp only [forkTriplePairNat,ite_eq_left hia,ite_eq_left (show i-1<a by omega)]
    right
    constructor
    · omega
    · unfold tripleSpiderParent
      split_ifs <;> omega
  · subst i
    simp only [forkTriplePairNat,Nat.lt_irrefl,ite_false,ite_true,
      ite_eq_left (show a-1<a by omega)]
    right
    constructor
    · omega
    · unfold tripleSpiderParent
      split_ifs <;> omega
  · have hval : forkTriplePairNat a d e i=d+e+i := by
      simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, forkTriplePairNat,show ¬i<a by omega,show i≠a by omega]
    rw [hval]
    by_cases hfirst : i=a+1
    · subst i
      simp only [Nat.add_sub_cancel,forkTriplePairNat,Nat.lt_irrefl,ite_false,ite_true]
      left
      constructor
      · omega
      · unfold tripleSpiderParent
        split_ifs <;> omega
    · have hprev : forkTriplePairNat a d e (i-1)=d+e+(i-1) := by
        simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, forkTriplePairNat,show ¬i-1<a by omega,show i-1≠a by omega]
      rw [hprev]
      left
      constructor
      · omega
      · unfold tripleSpiderParent
        split_ifs <;> omega

lemma forkTriplePair_hom {a b c d e f g : ℕ}
    (ha : 0<a) (hb : 0<b) (hd : 0<d) (he : 0<e)
    (x y : Fin (a+b+1)) (h : (parentGraph (a+b) Nat.pred).Adj x y) :
    (tripleSpider a b c d e f g).Adj (forkTriplePair a b c d e f g x)
      (forkTriplePair a b c d e f g y) := by
  change (_<_ ∧ _=_) ∨ (_<_ ∧ _=_)
  rcases h with ⟨hxy,hp⟩ | ⟨hyx,hp⟩
  · have hh := forkTriplePair_parent_edge (c:=c) (f:=f) (g:=g) ha hb hd he
      (i:=y.val) (by omega) (by have := y.isLt; omega)
    simp only [Nat.pred_eq_sub_one] at hp
    rw [hp] at hh
    exact hh
  · have hh := forkTriplePair_parent_edge (c:=c) (f:=f) (g:=g) ha hb hd he
      (i:=x.val) (by omega) (by have := x.isLt; omega)
    simp only [Nat.pred_eq_sub_one] at hp
    rw [hp] at hh
    exact hh.symm

lemma forkTripleMapNat_hub (a b c d e f g : ℕ) :
    forkTripleMapNat a b c d e f g f=d+e := by
  simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, forkTripleMapNat]

lemma forkTripleMapNat_F {a b c d e f g i : ℕ} (hi : i<f) :
    forkTripleMapNat a b c d e f g i=d+e+a+b+c+f-i := by
  simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, forkTripleMapNat,hi]

lemma forkTripleMapNat_G {a b c d e f g i : ℕ} (hi : f < i) (hib : i≤f+g) :
    forkTripleMapNat a b c d e f g i=d+e+a+b+c+i := by
  simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, forkTripleMapNat,show ¬i<f by omega,show i≠f by omega,hib]

lemma forkTripleMapNat_long {a b c d e f g i : ℕ} (hi : f+g < i) (hib : i≤f+g+e) :
    forkTripleMapNat a b c d e f g i=d+e+f+g-i := by
  simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, forkTripleMapNat,show ¬i<f by omega,show i≠f by omega,
    show ¬i≤f+g by omega,hib]

lemma forkTripleMapNat_C {a b c d e f g i : ℕ}
    (hi : f+g+e < i) (hib : i≤forkTripleSize f g e c) :
    forkTripleMapNat a b c d e f g i=d+e+a+b+i-(f+g+e) := by
  simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, forkTripleMapNat,show ¬i<f by omega,show i≠f by omega,
    show ¬i≤f+g by omega,show ¬i≤f+g+e by omega,hib]

lemma forkTripleMapNat_stem {a b c d e f g i : ℕ} (hi : forkTripleSize f g e c < i) :
    forkTripleMapNat a b c d e f g i=d+forkTripleSize f g e c-i := by
  have hN : f+g+e≤forkTripleSize f g e c := by unfold forkTripleSize; omega
  simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, forkTripleMapNat,show ¬i<f by omega,show i≠f by omega,
    show ¬i≤f+g by omega,show ¬i≤f+g+e by omega,show ¬i≤forkTripleSize f g e c by omega]

lemma forkTripleMap_parent_edge {a b c d e f g i : ℕ}
    (ha : 0<a) (hb : 0<b) (hc : 0<c) (hd : 0<d) (he : 0<e) (hf : 0<f) (hg : 0<g)
    (hi : 0 < i) (hib : i≤forkTripleSize f g e c+d) :
    (forkTripleMapNat a b c d e f g (forkTripleStemParent f g e c i)<forkTripleMapNat a b c d e f g i ∧
      tripleSpiderParent a b c d e f g (forkTripleMapNat a b c d e f g i)=
        forkTripleMapNat a b c d e f g (forkTripleStemParent f g e c i)) ∨
    (forkTripleMapNat a b c d e f g i<forkTripleMapNat a b c d e f g (forkTripleStemParent f g e c i) ∧
      tripleSpiderParent a b c d e f g (forkTripleMapNat a b c d e f g (forkTripleStemParent f g e c i))=
        forkTripleMapNat a b c d e f g i) := by
  have hN : f+g+e≤forkTripleSize f g e c := by unfold forkTripleSize; omega
  have hSize : forkTripleSize f g e c=f+g+e+c := by unfold forkTripleSize; omega
  by_cases hbase : i≤f+g
  · have hparent : forkTripleStemParent f g e c i=i-1 := by
      unfold forkTripleStemParent forkParent graftParent
      simp only [Nat.pred_eq_sub_one]
      split_ifs <;> omega
    rw [hparent]
    rcases lt_trichotomy i f with hif | rfl | hif
    · rw [forkTripleMapNat_F hif,forkTripleMapNat_F (by omega)]
      right
      constructor
      · omega
      · unfold tripleSpiderParent
        split_ifs <;> omega
    · rw [forkTripleMapNat_hub,forkTripleMapNat_F (by omega)]
      right
      constructor
      · omega
      · unfold tripleSpiderParent
        split_ifs <;> omega
    · rw [forkTripleMapNat_G hif hbase]
      by_cases hfirst : i=f+1
      · subst i
        simp only [Nat.add_sub_cancel]
        rw [forkTripleMapNat_hub]
        left
        constructor
        · omega
        · unfold tripleSpiderParent
          split_ifs <;> omega
      · rw [forkTripleMapNat_G (by omega) (by omega)]
        left
        constructor
        · omega
        · unfold tripleSpiderParent
          split_ifs <;> omega
  by_cases hold : i≤forkTripleSize f g e c
  · have hparent : forkTripleStemParent f g e c i=if i=f+g+1 then f else i-1 := by
      unfold forkTripleStemParent forkParent graftParent
      split_ifs <;> omega
    rw [hparent]
    by_cases hlong : i≤f+g+e
    · rw [forkTripleMapNat_long (by omega) hlong]
      by_cases hfirst : i=f+g+1
      · rw [ite_eq_left hfirst,forkTripleMapNat_hub]
        right
        rw [forkTripleParent_spine (by omega)]
        omega
      · rw [ite_eq_right hfirst,forkTripleMapNat_long (by omega) (by omega)]
        right
        rw [forkTripleParent_spine (by omega)]
        omega
    · rw [ite_eq_right (show ¬i=f+g+1 by omega),forkTripleMapNat_C (by omega) hold]
      by_cases hfirst : i=f+g+e+1
      · rw [forkTripleMapNat_long (by omega) (by omega)]
        left
        constructor
        · omega
        · unfold tripleSpiderParent
          split_ifs <;> omega
      · rw [forkTripleMapNat_C (by omega) (by omega)]
        left
        constructor
        · omega
        · unfold tripleSpiderParent
          split_ifs <;> omega
  · rw [forkTripleMapNat_stem (i:=i) (by omega)]
    by_cases hfirst : i=forkTripleSize f g e c+1
    · have hparent : forkTripleStemParent f g e c i=f+g+e := by
        unfold forkTripleStemParent
        simp only [ite_eq_right hold,ite_eq_left hfirst]
      rw [hparent,forkTripleMapNat_long (by omega) (by omega)]
      right
      rw [forkTripleParent_spine (by omega)]
      omega
    · have hparent : forkTripleStemParent f g e c i=i-1 := by
        simp only [forkTripleStemParent,ite_eq_right hold,ite_eq_right hfirst]
      rw [hparent,forkTripleMapNat_stem (by omega)]
      right
      rw [forkTripleParent_spine (by omega)]
      omega

lemma forkTripleMap_hom {a b c d e f g : ℕ}
    (ha : 0<a) (hb : 0<b) (hc : 0<c) (hd : 0<d) (he : 0<e) (hf : 0<f) (hg : 0<g)
    (x y : Fin (forkTripleSize f g e c+d+1))
    (h : (forkTripleStem f g e c d).Adj x y) :
    (tripleSpider a b c d e f g).Adj (forkTripleMap a b c d e f g x)
      (forkTripleMap a b c d e f g y) := by
  change (_<_ ∧ _=_) ∨ (_<_ ∧ _=_)
  rcases h with ⟨hxy,hp⟩ | ⟨hyx,hp⟩
  · have hh := forkTripleMap_parent_edge ha hb hc hd he hf hg
      (i:=y.val) (by omega) (by have := y.isLt; omega)
    rw [hp] at hh
    exact hh
  · have hh := forkTripleMap_parent_edge ha hb hc hd he hf hg
      (i:=x.val) (by omega) (by have := x.isLt; omega)
    rw [hp] at hh
    exact hh.symm

end Bounty


/- Supporting module: H2TripleStem -/



namespace Bounty
open Math15.Graceful

/-- The old spider is listed first, followed by a stem starting at its prescribed pin. -/
def h2StemParent (L e j : ℕ) : ℕ :=
  if j < L+5 then spiderParent j else if j = L+5 then 4+e else j-1

def h2Stem (L e d : ℕ) : SimpleGraph (Fin (L+d+5)) where
  Adj u v := (u.val < v.val ∧ h2StemParent L e v.val = u.val) ∨
    (v.val < u.val ∧ h2StemParent L e u.val = v.val)
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by intro i; simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero]⟩

lemma h2StemParent_lt {L e j : ℕ} (he : e ≤ L) (hj : 0 < j) :
    h2StemParent L e j < j := by
  unfold h2StemParent
  split_ifs with h h'
  · exact spiderParent_lt hj
  · omega
  · omega

lemma h2Stem_edgeCount {L e d : ℕ} (he : e ≤ L) : edgeCount (h2Stem L e d) = L+d+4 := by
  have h := parentGraph_edgeCount (L+d+4) (h2StemParent L e)
    (fun _ hj _ => h2StemParent_lt he hj)
  exact h

lemma h2Stem_zero (L e : ℕ) : h2Stem L e 0 = spider L := by
  ext u v
  have hu := u.isLt
  have hv := v.isLt
  change ((_ ∧ _) ∨ (_ ∧ _)) ↔ ((_ ∧ _) ∨ (_ ∧ _))
  simp only [h2StemParent, Nat.add_zero, ite_eq_left hu, ite_eq_left hv]

def h2StemTip (L e d : ℕ) (he : e ≤ L) : Fin (L+d+5) :=
  ⟨if d = 0 then 4+e else L+d+4, by split_ifs <;> omega⟩

private lemma flat_H2TripleStem_leaf_edges_from_parts {a b : ℕ}
    (G : SimpleGraph (Fin a)) (K : SimpleGraph (Fin b))
    (j : Fin a → Fin b) (r : Fin a) (z : Fin b)
    (hcover : ∀ v, (∃ x, j x = v) ∨ v = z)
    (hold : ∀ x y, K.Adj (j x) (j y) ↔ G.Adj x y)
    (hnew : ∀ x, K.Adj z (j x) ↔ x = r) :
    ∀ u v, K.Adj u v ↔
      (∃ x y, G.Adj x y ∧ j x = u ∧ j y = v) ∨
      (u = z ∧ v = j r) ∨ (u = j r ∧ v = z) := by
  intro u v
  constructor
  · intro h
    rcases hcover u with ⟨x,rfl⟩ | rfl <;> rcases hcover v with ⟨y,rfl⟩ | rfl
    · exact Or.inl ⟨x,y,(hold x y).1 h,rfl,rfl⟩
    · have hx := (hnew x).1 h.symm
      exact Or.inr (Or.inr ⟨congrArg j hx,rfl⟩)
    · have hy := (hnew y).1 h
      exact Or.inr (Or.inl ⟨rfl,congrArg j hy⟩)
    · exact (K.irrefl h).elim
  · rintro (⟨x,y,hxy,rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
    · exact (hold x y).2 hxy
    · exact (hnew r).2 rfl
    · exact ((hnew r).2 rfl).symm

/-- Repeated zero-leaf extension preserves alpha labelings all along a new stem. -/
theorem h2Stem_alpha {L e : ℕ} (he : e ≤ L)
    (hstart : ∃ f k, IsAlphaLabeling (spider L) f k ∧ f ⟨4+e,by omega⟩ = 0)
    (d : ℕ) :
    ∃ f k, IsAlphaLabeling (h2Stem L e d) f k ∧ f (h2StemTip L e d he) = 0 := by
  induction d with
  | zero =>
    simpa only [h2Stem_zero, h2StemTip, ite_true] using hstart
  | succ d ih =>
    obtain ⟨f,k,hf,hzero⟩ := ih
    let j : Fin (L+d+5) → Fin (L+(d+1)+5) := fun x => ⟨x.val,by have := x.isLt; omega⟩
    let z : Fin (L+(d+1)+5) := ⟨L+d+5,by omega⟩
    have hj : Function.Injective j := by
      intro x y h
      apply Fin.ext
      exact congrArg (fun t : Fin (L+(d+1)+5) => t.val) h
    have hz : ∀ x, j x ≠ z := by intro x h; have := congrArg Fin.val h; have := x.isLt; dsimp [j,z] at *; omega
    have hcover : ∀ v, (∃ x, j x = v) ∨ v = z := by
      intro v
      by_cases hv : v.val < L+d+5
      · exact Or.inl ⟨⟨v.val,hv⟩,rfl⟩
      · right; apply Fin.ext; have := v.isLt; dsimp [z]; omega
    have hold (x y : Fin (L+d+5)) : (h2Stem L e (d+1)).Adj (j x) (j y) ↔
        (h2Stem L e d).Adj x y := Iff.rfl
    have hparent : h2StemParent L e (L+d+5) = (h2StemTip L e d he).val := by
      change h2StemParent L e (L+d+5) = if d = 0 then 4+e else L+d+4
      unfold h2StemParent
      split_ifs <;> omega
    have hnew (x : Fin (L+d+5)) : (h2Stem L e (d+1)).Adj z (j x) ↔
        x = h2StemTip L e d he := by
      have hx := x.isLt
      change ((L+d+5 < x.val ∧ _) ∨ (x.val < L+d+5 ∧ _)) ↔ _
      rw [hparent]
      constructor
      · rintro (h | h)
        · omega
        · exact Fin.ext h.2.symm
      · intro h
        right
        exact ⟨hx,(congrArg Fin.val h).symm⟩
    have hcount : edgeCount (h2Stem L e (d+1)) = edgeCount (h2Stem L e d)+1 := by
      rw [h2Stem_edgeCount he,h2Stem_edgeCount he]
      omega
    obtain ⟨g,hg,hgz,_⟩ := alpha_leaf_extension_labeling (h2Stem L e d) (h2Stem L e (d+1))
      j hj (h2StemTip L e d he) z hz hcover
      (flat_H2TripleStem_leaf_edges_from_parts _ _ j _ z hcover hold hnew) hcount f k hf hzero
    refine ⟨g,_,hg,?_⟩
    have heq : h2StemTip L e (d+1) he = z := by
      apply Fin.ext
      simp only [h2StemTip, ite_eq_right (show ¬d+1=0 by omega)]
      dsimp [z]
      omega
    rwa [heq]

/-- The complete H2 theorem supplies the starting spider for every nonexceptional pin. -/
theorem h2Stem_alpha_of_nonexceptional {e c : ℕ} (he : 1 ≤ e) (hc : 1 ≤ c)
    (hne : ¬H2Research.Exceptional e c) (d : ℕ) :
    ∃ f k, IsAlphaLabeling (h2Stem (e+c) e d) f k ∧
      f (h2StemTip (e+c) e d (by omega)) = 0 :=
  h2Stem_alpha (by omega) (h2_rooted_alpha_spider e c he hc hne).toAlpha d

end Bounty


/- Supporting module: FiniteParentCertificate -/

namespace Bounty

/-- A finite-domain form permitting kernel reduction of explicit labelings. -/
def FiniteParentCertificate (N : ℕ) (parent : ℕ → ℕ) (f : Fin (N+1) → ℕ) : Prop :=
  Function.Injective f ∧ (∀ i, f i ≤ N) ∧
  ∀ i j : Fin (N+1), 0 < i.val → 0 < j.val →
    ∀ hi : parent i.val < N+1, ∀ hj : parent j.val < N+1,
    Nat.dist (f ⟨parent i.val,hi⟩) (f i) =
      Nat.dist (f ⟨parent j.val,hj⟩) (f j) → i = j

def finiteParentCertificateDecidable (N : ℕ) (parent : ℕ → ℕ) (f : Fin (N+1) → ℕ) :
    Decidable (FiniteParentCertificate N parent f) := by
  unfold FiniteParentCertificate Function.Injective
  infer_instance

theorem FiniteParentCertificate.isGracefulLabeling {N : ℕ} {parent : ℕ → ℕ}
    {f : Fin (N+1) → ℕ}
    (hp : ∀ j, 0 < j → j ≤ N → parent j < j)
    (hf : FiniteParentCertificate N parent f) :
    Math15.Graceful.IsGracefulLabeling (parentGraph N parent) f := by
  apply Math15.Graceful.labeling_of_injective_differences _ f hf.1
  · intro i
    rw [parentGraph_edgeCount N parent hp]
    exact hf.2.1 i
  · intro e e' he ha he' ha' hd
    have hpar : parent e.2.val = e.1.val := by
      rcases ha with h | h
      · exact h.2
      · exact (Nat.lt_asymm he h.1).elim
    have hpar' : parent e'.2.val = e'.1.val := by
      rcases ha' with h | h
      · exact h.2
      · exact (Nat.lt_asymm he' h.1).elim
    have hpi : parent e.2.val < N+1 := by rw [hpar]; exact e.1.isLt
    have hpj : parent e'.2.val < N+1 := by rw [hpar']; exact e'.1.isLt
    have hr : e.2 = e'.2 := by
      apply hf.2.2 _ _ (by omega) (by omega) hpi hpj
      have hp0 : (⟨parent e.2.val,hpi⟩ : Fin (N+1)) = e.1 := Fin.ext hpar
      have hp1 : (⟨parent e'.2.val,hpj⟩ : Fin (N+1)) = e'.1 := Fin.ext hpar'
      simpa only [hp0, hp1] using hd
    exact Prod.ext (Fin.ext (hpar.symm.trans ((congrArg (fun i => parent i.val) hr).trans hpar'))) hr

end Bounty


/- Supporting module: Source11Exceptions -/

namespace Bounty

def exception_1_2_labels : Fin 9 → ℕ := ![6, 0, 5, 3, 2, 8, 1, 7, 4]

theorem exception_1_2_certificate :
    FiniteParentCertificate 8 (tripleSpiderParent 1 1 2 1 1 1 1) exception_1_2_labels := by
  letI := finiteParentCertificateDecidable 8 (tripleSpiderParent 1 1 2 1 1 1 1) exception_1_2_labels
  decide

theorem exception_1_2_graceful : Math15.Graceful.IsGraceful (tripleSpider 1 1 2 1 1 1 1) := by
  exact (exception_1_2_certificate.isGracefulLabeling
    (fun j hj _ => tripleSpiderParent_lt 1 1 2 1 1 1 1 j hj)).isGraceful

def exception_2_1_labels : Fin 12 → ℕ := ![10, 0, 11, 1, 8, 5, 6, 2, 7, 4, 3, 9]

theorem exception_2_1_certificate :
    FiniteParentCertificate 11 (tripleSpiderParent 2 2 1 1 1 2 2) exception_2_1_labels := by
  letI := finiteParentCertificateDecidable 11 (tripleSpiderParent 2 2 1 1 1 2 2) exception_2_1_labels
  decide

theorem exception_2_1_graceful : Math15.Graceful.IsGraceful (tripleSpider 2 2 1 1 1 2 2) := by
  exact (exception_2_1_certificate.isGracefulLabeling
    (fun j hj _ => tripleSpiderParent_lt 2 2 1 1 1 2 2 j hj)).isGraceful

def exception_2_4_labels : Fin 15 → ℕ := ![9, 0, 10, 7, 12, 6, 5, 14, 1, 13, 2, 3, 11, 4, 8]

theorem exception_2_4_certificate :
    FiniteParentCertificate 14 (tripleSpiderParent 2 2 4 1 1 2 2) exception_2_4_labels := by
  letI := finiteParentCertificateDecidable 14 (tripleSpiderParent 2 2 4 1 1 2 2) exception_2_4_labels
  decide

theorem exception_2_4_graceful : Math15.Graceful.IsGraceful (tripleSpider 2 2 4 1 1 2 2) := by
  exact (exception_2_4_certificate.isGracefulLabeling
    (fun j hj _ => tripleSpiderParent_lt 2 2 4 1 1 2 2 j hj)).isGraceful

def exception_2_5_labels : Fin 16 → ℕ := ![10, 0, 8, 6, 9, 4, 11, 15, 1, 14, 2, 13, 7, 5, 3, 12]

theorem exception_2_5_certificate :
    FiniteParentCertificate 15 (tripleSpiderParent 2 2 5 1 1 2 2) exception_2_5_labels := by
  letI := finiteParentCertificateDecidable 15 (tripleSpiderParent 2 2 5 1 1 2 2) exception_2_5_labels
  decide

theorem exception_2_5_graceful : Math15.Graceful.IsGraceful (tripleSpider 2 2 5 1 1 2 2) := by
  exact (exception_2_5_certificate.isGracefulLabeling
    (fun j hj _ => tripleSpiderParent_lt 2 2 5 1 1 2 2 j hj)).isGraceful

end Bounty


/- Supporting module: H2TripleAmalgam -/




namespace Bounty
open Math15.Graceful

def h2TripleMapNat (c d e i : ℕ) : ℕ :=
  if i = 0 then d+e
  else if i ≤ 4 then d+e+c+4+i
  else if i ≤ e+4 then d+e+4-i
  else if i ≤ e+c+4 then d+i
  else d+e+c+4-i

def h2TripleMap (c d e : ℕ) (i : Fin (e+c+d+5)) :
    Fin (tripleSpiderEdges 2 2 c d e 2 2+1) :=
  ⟨h2TripleMapNat c d e i.val, by
    have hi := i.isLt
    unfold h2TripleMapNat tripleSpiderEdges
    split_ifs <;> omega⟩

def h2PairMap (c d e : ℕ) (i : Fin 5) :
    Fin (tripleSpiderEdges 2 2 c d e 2 2+1) :=
  ⟨if i.val = 0 then 0 else d+e+i.val, by
    have hi := i.isLt
    unfold tripleSpiderEdges
    split_ifs <;> omega⟩

lemma h2TripleMap_injective (c d e : ℕ) : Function.Injective (h2TripleMap c d e) := by
  intro i j heq
  apply Fin.ext
  have hi := i.isLt
  have hj := j.isLt
  have h := congrArg Fin.val heq
  change h2TripleMapNat c d e i.val = h2TripleMapNat c d e j.val at h
  unfold h2TripleMapNat at h
  split_ifs at h <;> omega

lemma h2PairMap_injective (c d e : ℕ) : Function.Injective (h2PairMap c d e) := by
  intro i j heq
  apply Fin.ext
  have hi := i.isLt
  have hj := j.isLt
  have h := congrArg Fin.val heq
  change (if i.val = 0 then 0 else d+e+i.val) = (if j.val = 0 then 0 else d+e+j.val) at h
  split_ifs at h <;> omega

lemma h2TripleMap_tip {c d e : ℕ} (hd : 0 < d) :
    h2TripleMap c d e (h2StemTip (e+c) e d (by omega)) = h2PairMap c d e 0 := by
  apply Fin.ext
  change h2TripleMapNat c d e (if d=0 then 4+e else e+c+d+4) = 0
  simp only [ite_eq_right (show d ≠ 0 by omega)]
  unfold h2TripleMapNat
  split_ifs <;> first | contradiction | omega

lemma h2TripleMap_overlap {c d e : ℕ} (hd : 0 < d)
    (i : Fin (e+c+d+5)) (j : Fin 5) :
    h2TripleMap c d e i = h2PairMap c d e j ↔
      i = h2StemTip (e+c) e d (by omega) ∧ j = 0 := by
  constructor
  · intro heq
    have hi := i.isLt
    have hj := j.isLt
    have h := congrArg Fin.val heq
    change h2TripleMapNat c d e i.val = (if j.val=0 then 0 else d+e+j.val) at h
    have hi' : i.val = e+c+d+4 := by
      unfold h2TripleMapNat at h
      split_ifs at h <;> omega
    have hj' : j.val = 0 := by
      unfold h2TripleMapNat at h
      split_ifs at h <;> omega
    constructor
    · apply Fin.ext
      change i.val = if d=0 then 4+e else e+c+d+4
      rw [ite_eq_right (by omega)]
      exact hi'
    · exact Fin.ext hj'
  · rintro ⟨rfl,rfl⟩
    exact h2TripleMap_tip hd

def h2TripleInverse (c d e v : ℕ) : ℕ :=
  if v ≤ d+e then
    if v = d+e then 0 else if d ≤ v then d+e+4-v else d+e+c+4-v
  else if v ≤ d+e+c+4 then v-d else v-(d+e+c+4)

lemma h2TripleMap_cover (c d e : ℕ) (v : Fin (tripleSpiderEdges 2 2 c d e 2 2+1)) :
    (∃ i, h2TripleMap c d e i = v) ∨ (∃ j, h2PairMap c d e j = v) := by
  have hv := v.isLt
  dsimp only [tripleSpiderEdges] at hv
  by_cases hpair : d+e < v.val ∧ v.val ≤ d+e+4
  · right
    refine ⟨⟨v.val-(d+e),by omega⟩,?_⟩
    apply Fin.ext
    change (if v.val-(d+e)=0 then 0 else d+e+(v.val-(d+e))) = v.val
    rw [ite_eq_right (by omega)]
    omega
  · have hbound : h2TripleInverse c d e v.val < e+c+d+5 := by
      unfold h2TripleInverse
      split_ifs <;> omega
    left
    refine ⟨⟨h2TripleInverse c d e v.val,hbound⟩,?_⟩
    apply Fin.ext
    change h2TripleMapNat c d e (h2TripleInverse c d e v.val) = v.val
    unfold h2TripleInverse h2TripleMapNat
    split_ifs <;> omega

lemma h2TripleMapNat_long {c d e i : ℕ} (hi : 4 < i) (hib : i ≤ e+4) :
    h2TripleMapNat c d e i = d+e+4-i := by
  simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, h2TripleMapNat, show i ≠ 0 by omega, show ¬i ≤ 4 by omega, hib]

lemma h2TripleMapNat_tail {c d e i : ℕ} (hi : e+4 < i) (hib : i ≤ e+c+4) :
    h2TripleMapNat c d e i = d+i := by
  simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, h2TripleMapNat, show i ≠ 0 by omega, show ¬i ≤ 4 by omega,
    show ¬i ≤ e+4 by omega, hib]

lemma h2TripleMapNat_stem {c d e i : ℕ} (hi : e+c+4 < i) :
    h2TripleMapNat c d e i = d+e+c+4-i := by
  simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, h2TripleMapNat, show i ≠ 0 by omega, show ¬i ≤ 4 by omega,
    show ¬i ≤ e+4 by omega, show ¬i ≤ e+c+4 by omega]

lemma h2TripleParent_spine {c d e i : ℕ} (hi : i ≤ d+e) :
    tripleSpiderParent 2 2 c d e 2 2 i = i-1 := by
  unfold tripleSpiderParent
  split_ifs <;> omega

lemma h2TripleMap_parent_edge {c d e i : ℕ} (he : 0 < e) (hc : 0 < c)
    (hi : 0 < i) (hib : i < e+c+d+5) :
    (h2TripleMapNat c d e (h2StemParent (e+c) e i) < h2TripleMapNat c d e i ∧
      tripleSpiderParent 2 2 c d e 2 2 (h2TripleMapNat c d e i) =
        h2TripleMapNat c d e (h2StemParent (e+c) e i)) ∨
    (h2TripleMapNat c d e i < h2TripleMapNat c d e (h2StemParent (e+c) e i) ∧
      tripleSpiderParent 2 2 c d e 2 2 (h2TripleMapNat c d e (h2StemParent (e+c) e i)) =
        h2TripleMapNat c d e i) := by
  by_cases hi4 : i ≤ 4
  · interval_cases i <;> simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, h2StemParent, spiderParent, h2TripleMapNat, tripleSpiderParent] <;> split_ifs <;> omega
  by_cases hold : i ≤ e+c+4
  · have hparent : h2StemParent (e+c) e i = if i=5 then 0 else i-1 := by
      unfold h2StemParent spiderParent
      split_ifs <;> omega
    rw [hparent]
    by_cases hi5 : i=5
    · subst i
      simp only [ite_true]
      rw [h2TripleMapNat_long (i := 5) (by omega) (by omega)]
      have hm0 : h2TripleMapNat c d e 0 = d+e := by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, h2TripleMapNat]
      rw [hm0]
      right
      rw [h2TripleParent_spine (by omega)]
      omega
    · rw [ite_eq_right hi5]
      by_cases hlong : i ≤ e+4
      · rw [h2TripleMapNat_long (by omega) hlong,
          h2TripleMapNat_long (by omega) (by omega)]
        right
        rw [h2TripleParent_spine (by omega)]
        omega
      · rw [h2TripleMapNat_tail (by omega) hold]
        by_cases hfirst : i=e+5
        · rw [h2TripleMapNat_long (by omega) (by omega)]
          left
          constructor
          · omega
          · unfold tripleSpiderParent
            split_ifs <;> omega
        · rw [h2TripleMapNat_tail (by omega) (by omega)]
          left
          constructor
          · omega
          · unfold tripleSpiderParent
            split_ifs <;> omega
  · by_cases hfirst : i=e+c+5
    · have hparent : h2StemParent (e+c) e i = 4+e := by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, h2StemParent,hfirst]
      rw [hparent, h2TripleMapNat_long (by omega) (by omega),
        h2TripleMapNat_stem (by omega)]
      right
      rw [h2TripleParent_spine (by omega)]
      omega
    · have hparent : h2StemParent (e+c) e i = i-1 := by
        unfold h2StemParent
        split_ifs <;> omega
      rw [hparent, h2TripleMapNat_stem (by omega), h2TripleMapNat_stem (by omega)]
      right
      rw [h2TripleParent_spine (by omega)]
      omega

lemma h2TripleMap_hom {c d e : ℕ} (he : 0 < e) (hc : 0 < c)
    (x y : Fin (e+c+d+5)) (h : (h2Stem (e+c) e d).Adj x y) :
    (tripleSpider 2 2 c d e 2 2).Adj (h2TripleMap c d e x) (h2TripleMap c d e y) := by
  change (_ < _ ∧ _ = _) ∨ (_ < _ ∧ _ = _)
  rcases h with ⟨hxy,hp⟩ | ⟨hyx,hp⟩
  · have h := h2TripleMap_parent_edge he hc (i := y.val) (by omega) y.isLt
    rw [hp] at h
    exact h
  · have h := h2TripleMap_parent_edge he hc (i := x.val) (by omega) x.isLt
    rw [hp] at h
    exact h.symm

lemma h2PairMap_hom {c d e : ℕ} (he : 0 < e) (hc : 0 < c) (hd : 0 < d)
    (x y : Fin 5) (h : (spider 0).Adj x y) :
    (tripleSpider 2 2 c d e 2 2).Adj (h2PairMap c d e x) (h2PairMap c d e y) := by
  fin_cases x <;> fin_cases y <;>
    norm_num [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, spider,spiderParent] at h <;>
    dsimp only [tripleSpider,parentGraph,h2PairMap] <;>
    norm_num only <;> simp only [tripleSpiderParent] <;> split_ifs <;> first | contradiction | omega

lemma h2Stem_isTree {L e d : ℕ} (he : e ≤ L) : (h2Stem L e d).IsTree := by
  change (parentGraph (L+d+4) (h2StemParent L e)).IsTree
  exact parentGraph_isTree _ _ (fun j hj _ => h2StemParent_lt he hj)

lemma h2Pair_isTree : (spider 0).IsTree := by
  change (parentGraph 4 spiderParent).IsTree
  exact parentGraph_isTree _ _ (fun j hj _ => spiderParent_lt hj)

def h2PairLabels : Fin 5 → ℕ := ![0,4,1,2,3]

lemma h2Pair_graceful : IsGracefulLabeling (spider 0) h2PairLabels := by
  have h : FiniteParentCertificate 4 spiderParent h2PairLabels := by
    letI := finiteParentCertificateDecidable 4 spiderParent h2PairLabels
    decide
  exact h.isGracefulLabeling (fun j hj _ => spiderParent_lt hj)

theorem tripleSpider_twos_of_nonexceptional {c d e : ℕ}
    (hc : 0 < c) (hd : 0 < d) (he : 0 < e) (hne : ¬ H2Research.Exceptional e c) :
    IsGraceful (tripleSpider 2 2 c d e 2 2) := by
  obtain ⟨f,k,hf,hzero⟩ := h2Stem_alpha_of_nonexceptional he hc hne d
  have hedges := tree_union_edges (tripleSpider 2 2 c d e 2 2) (h2Stem (e+c) e d) (spider 0)
    (h2TripleMap c d e) (h2PairMap c d e) (h2TripleMap_injective c d e)
    (h2PairMap_injective c d e) (tripleSpider_isTree _ _ _ _ _ _ _)
    (h2Stem_isTree (by omega)).connected h2Pair_isTree.connected
    (h2StemTip (e+c) e d (by omega)) 0 (h2TripleMap_tip hd)
    (h2TripleMap_cover c d e) (h2TripleMap_hom he hc) (h2PairMap_hom he hc hd)
  apply isGraceful_amalgamation (tripleSpider 2 2 c d e 2 2) (h2Stem (e+c) e d) (spider 0)
    (h2TripleMap c d e) (h2PairMap c d e) (h2TripleMap_injective c d e)
    (h2PairMap_injective c d e) (h2StemTip (e+c) e d (by omega)) 0
    (h2TripleMap_overlap hd) (h2TripleMap_cover c d e) hedges ?_
    f h2PairLabels k hf h2Pair_graceful (Or.inl hzero) rfl
  rw [tripleSpider_edgeCount,h2Stem_edgeCount (by omega),spider_edgeCount]
  unfold tripleSpiderEdges
  omega

end Bounty


/- Supporting module: H2TripleSymmetry -/


namespace Bounty
open Math15.Graceful

def h2SwapNat (c d e i : ℕ) : ℕ :=
  if i ≤ d+e then d+e-i
  else if i ≤ d+e+4 then i+c+4
  else if i ≤ d+e+c+4 then i
  else i-(c+4)

def h2Swap (c d e : ℕ) (i : Fin (tripleSpiderEdges 2 2 c d e 2 2+1)) :
    Fin (tripleSpiderEdges 2 2 c e d 2 2+1) :=
  ⟨h2SwapNat c d e i.val, by
    have hi := i.isLt
    unfold h2SwapNat tripleSpiderEdges at *
    split_ifs <;> omega⟩

lemma h2Swap_inverse (c d e : ℕ) (i : Fin (tripleSpiderEdges 2 2 c d e 2 2+1)) :
    h2Swap c e d (h2Swap c d e i) = i := by
  apply Fin.ext
  have hi := i.isLt
  change h2SwapNat c e d (h2SwapNat c d e i.val) = i.val
  dsimp only [tripleSpiderEdges] at hi
  unfold h2SwapNat
  split_ifs <;> omega

lemma h2Swap_parent_edge {c d e i : ℕ} (hc : 0 < c) (hd : 0 < d) (he : 0 < e)
    (hi : 0 < i) (hib : i ≤ tripleSpiderEdges 2 2 c d e 2 2) :
    (h2SwapNat c d e (tripleSpiderParent 2 2 c d e 2 2 i) < h2SwapNat c d e i ∧
      tripleSpiderParent 2 2 c e d 2 2 (h2SwapNat c d e i) =
        h2SwapNat c d e (tripleSpiderParent 2 2 c d e 2 2 i)) ∨
    (h2SwapNat c d e i < h2SwapNat c d e (tripleSpiderParent 2 2 c d e 2 2 i) ∧
      tripleSpiderParent 2 2 c e d 2 2 (h2SwapNat c d e (tripleSpiderParent 2 2 c d e 2 2 i)) =
        h2SwapNat c d e i) := by
  dsimp only [tripleSpiderEdges] at hib
  have hs (j : ℕ) (hj : j ≤ d+e) : h2SwapNat c d e j = d+e-j := by
    simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, h2SwapNat,hj]
  have ha (j : ℕ) (hj : d+e < j) (hjb : j ≤ d+e+4) :
      h2SwapNat c d e j = j+c+4 := by
    simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, h2SwapNat,show ¬j ≤ d+e by omega,hjb]
  have hb (j : ℕ) (hj : d+e+4 < j) (hjb : j ≤ d+e+c+4) :
      h2SwapNat c d e j = j := by
    simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, h2SwapNat,show ¬j ≤ d+e by omega,show ¬j ≤ d+e+4 by omega,hjb]
  have hz (j : ℕ) (hj : d+e+c+4 < j) : h2SwapNat c d e j = j-(c+4) := by
    simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, h2SwapNat,show ¬j ≤ d+e by omega,show ¬j ≤ d+e+4 by omega,
      show ¬j ≤ d+e+c+4 by omega]
  by_cases hsp : i ≤ d+e
  · rw [h2TripleParent_spine hsp,hs i hsp,hs (i-1) (by omega)]
    right
    rw [h2TripleParent_spine (by omega)]
    omega
  by_cases har : i ≤ d+e+4
  · rw [ha i (by omega) har]
    by_cases hf : i=d+e+1 ∨ i=d+e+3
    · have hp : tripleSpiderParent 2 2 c d e 2 2 i = 0 := by
        unfold tripleSpiderParent
        split_ifs <;> omega
      rw [hp,hs 0 (by omega)]
      left
      constructor
      · omega
      · unfold tripleSpiderParent
        split_ifs <;> omega
    · have hp : tripleSpiderParent 2 2 c d e 2 2 i = i-1 := by
        unfold tripleSpiderParent
        split_ifs <;> omega
      rw [hp,ha (i-1) (by omega) (by omega)]
      left
      constructor
      · omega
      · unfold tripleSpiderParent
        split_ifs <;> omega
  by_cases htail : i ≤ d+e+c+4
  · rw [hb i (by omega) htail]
    by_cases hf : i=d+e+5
    · have hp : tripleSpiderParent 2 2 c d e 2 2 i = d := by
        unfold tripleSpiderParent
        split_ifs <;> omega
      rw [hp,hs d (by omega)]
      left
      constructor
      · omega
      · unfold tripleSpiderParent
        split_ifs <;> omega
    · have hp : tripleSpiderParent 2 2 c d e 2 2 i = i-1 := by
        unfold tripleSpiderParent
        split_ifs <;> omega
      rw [hp,hb (i-1) (by omega) (by omega)]
      left
      constructor
      · omega
      · unfold tripleSpiderParent
        split_ifs <;> omega
  · rw [hz i (by omega)]
    by_cases hf : i=d+e+c+5 ∨ i=d+e+c+7
    · have hp : tripleSpiderParent 2 2 c d e 2 2 i = d+e := by
        unfold tripleSpiderParent
        split_ifs <;> omega
      rw [hp,hs (d+e) (by omega)]
      left
      constructor
      · omega
      · unfold tripleSpiderParent
        split_ifs <;> omega
    · have hp : tripleSpiderParent 2 2 c d e 2 2 i = i-1 := by
        unfold tripleSpiderParent
        split_ifs <;> omega
      rw [hp,hz (i-1) (by omega)]
      left
      constructor
      · omega
      · unfold tripleSpiderParent
        split_ifs <;> omega

lemma h2Swap_hom {c d e : ℕ} (hc : 0 < c) (hd : 0 < d) (he : 0 < e)
    (x y : Fin (tripleSpiderEdges 2 2 c d e 2 2+1)) (h : (tripleSpider 2 2 c d e 2 2).Adj x y) :
    (tripleSpider 2 2 c e d 2 2).Adj (h2Swap c d e x) (h2Swap c d e y) := by
  change (_ < _ ∧ _ = _) ∨ (_ < _ ∧ _ = _)
  rcases h with ⟨hxy,hp⟩ | ⟨hyx,hp⟩
  · have h := h2Swap_parent_edge hc hd he (i := y.val) (by omega) (by have := y.isLt; omega)
    rw [hp] at h
    exact h
  · have h := h2Swap_parent_edge hc hd he (i := x.val) (by omega) (by have := x.isLt; omega)
    rw [hp] at h
    exact h.symm

def h2SwapIso {c d e : ℕ} (hc : 0 < c) (hd : 0 < d) (he : 0 < e) :
    tripleSpider 2 2 c d e 2 2 ≃g tripleSpider 2 2 c e d 2 2 where
  toFun := h2Swap c d e
  invFun := h2Swap c e d
  left_inv := h2Swap_inverse c d e
  right_inv := h2Swap_inverse c e d
  map_rel_iff' := by
    intro x y
    constructor
    · intro h
      have hr := h2Swap_hom hc he hd _ _ h
      change (tripleSpider 2 2 c d e 2 2).Adj
        (h2Swap c e d (h2Swap c d e x)) (h2Swap c e d (h2Swap c d e y)) at hr
      simpa only [h2Swap_inverse] using hr
    · exact h2Swap_hom hc hd he x y

/-- The entire three-parameter family with all four outer arms of length two. -/
theorem tripleSpider_twos_graceful {c d e : ℕ} (hc : 0 < c) (hd : 0 < d) (he : 0 < e) :
    IsGraceful (tripleSpider 2 2 c d e 2 2) := by
  by_cases hright : H2Research.Exceptional e c
  · by_cases hleft : H2Research.Exceptional d c
    · obtain ⟨rfl,hc'⟩ := hleft
      obtain ⟨rfl,_⟩ := hright
      rcases hc' with rfl | rfl | rfl
      · exact exception_2_1_graceful
      · exact exception_2_4_graceful
      · exact exception_2_5_graceful
    · exact isGraceful_of_iso (h2SwapIso hc hd he)
        (tripleSpider_twos_of_nonexceptional hc he hd hleft)
  · exact tripleSpider_twos_of_nonexceptional hc hd he hright

end Bounty


/- Supporting module: Structure -/

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
    · simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, hc] using hxa
    · simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, hc] using hxb
  have heq : ({a, b} : Finset (Fin n)) = Finset.univ.filter (G.Adj x) := by
    apply Finset.eq_of_subset_of_card_le hsub
    simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, degree, Finset.card_pair hab] using hdeg
  intro c hc
  have hmem : c ∈ Finset.univ.filter (G.Adj x) := by simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero] using hc
  rw [← heq] at hmem
  simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero] using hmem

/-- An internal vertex of a path whose degree is at most two has no neighbor outside the path. -/
theorem internal_path_neighbor_mem {n : ℕ} (G : SimpleGraph (Fin n))
    {u v : Fin n} {p : G.Walk u v} (hp : p.IsPath) {i : ℕ}
    (hlo : 0 < i) (hhi : i < p.length) (hdeg : degree G (p.getVert i) ≤ 2)
    {w : Fin n} (hw : G.Adj (p.getVert i) w) : w ∈ p.support := by
  have hne : p.getVert (i - 1) ≠ p.getVert (i + 1) := by
    intro heq
    have := hp.getVert_injOn (by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero]; omega) (by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero]; omega) heq
    omega
  have hprev : G.Adj (p.getVert i) (p.getVert (i - 1)) := by
    have h := (p.adj_getVert_succ (i := i - 1) (by omega)).symm
    simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, Nat.sub_add_cancel hlo] using h
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
  rw [hfilter, Finset.card_erase_of_mem (by simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero] using hsndadj)]
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
      simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, offPathNeighbors]
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


/- Supporting module: PathComponents -/


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
    · simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, hc] using hxa
    · simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, hc] using hxb
  have heq : ({a, b} : Finset V) = G.neighborFinset x := by
    apply Finset.eq_of_subset_of_card_le hsub
    simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, Finset.card_pair hab] using hdeg
  intro c hc
  have hmem : c ∈ G.neighborFinset x := by simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero] using hc
  rw [← heq] at hmem
  simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero] using hmem

private theorem flat_PathComponents_generic_internal_neighbor {u v : V} {p : G.Walk u v}
    (hp : p.IsPath) {i : ℕ} (hlo : 0 < i) (hhi : i < p.length)
    (hdeg : G.degree (p.getVert i) ≤ 2) {w : V} (hw : G.Adj (p.getVert i) w) :
    w ∈ p.support := by
  have hne : p.getVert (i - 1) ≠ p.getVert (i + 1) := by
    intro heq
    have := hp.getVert_injOn (by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero]; omega) (by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero]; omega) heq
    omega
  have hprev : G.Adj (p.getVert i) (p.getVert (i - 1)) := by
    have h := (p.adj_getVert_succ (i := i - 1) (by omega)).symm
    simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, Nat.sub_add_cancel hlo] using h
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
    exact flat_PathComponents_generic_internal_neighbor G hp hlo hhi (hdeg _) hxy
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
    simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, hzero] using hi.symm
  by_cases hend : i = p.length
  · right
    simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, hend] using hi.symm
  have hlo : 0 < i := by omega
  have hhi : i < p.length := by omega
  have hne : p.getVert (i - 1) ≠ p.getVert (i + 1) := by
    intro heq
    have := hp.getVert_injOn (by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero]; omega) (by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero]; omega) heq
    omega
  have hprev : G.Adj x (p.getVert (i - 1)) := by
    rw [← hi]
    have h := (p.adj_getVert_succ (i := i - 1) (by omega)).symm
    simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, Nat.sub_add_cancel hlo] using h
  have hnext : G.Adj x (p.getVert (i + 1)) := by rw [← hi]; exact p.adj_getVert_succ hhi
  have hsub : ({p.getVert (i - 1), p.getVert (i + 1)} : Finset V) ⊆ G.neighborFinset x := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with hy | hy
    · simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, hy] using hprev
    · simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, hy] using hnext
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
    exact ⟨u, p.reverse, hp.reverse, by simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero] using hspan⟩

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


/- Supporting module: Decomposition -/


namespace Math15.Graceful

/-- Removing a vertex; the inequality predicate keeps endpoint proof obligations simple. -/
abbrev deleteVertexGraph {V : Type*} (G : SimpleGraph V) (u : V) :
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


/- Supporting module: ArmPartition -/

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
  simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, hc]

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
        have hrev : b ∉ p.reverse.support := by simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero] using hbu
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


/- Supporting module: InducedPath -/

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


/- Supporting module: ArmModel -/

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
      simp only [armModelAdj] at h ⊢
    all_goals first | contradiction | simpa only [eq_comm, or_comm, and_comm] using h⟩
  loopless := ⟨by
    intro x
    rcases x with x | x | x <;> simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, armModelAdj]
  ⟩

end Math15.Graceful


/- Supporting module: ArmData -/

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


/- Supporting module: SpineData -/

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
  have hm : vertex hp i ∈ p.reverse.support := by simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero] using vertex_mem hp i
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
      · have hm : vertex hp i ∈ p.reverse.support := by simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero] using vertex_mem hp i
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


/- Supporting module: Branch333Structure -/


namespace Math15.Graceful

/-- A tree with exactly three vertices of degree three and no larger degrees
has five leaves. -/
theorem branch333_leaf_count {n : ℕ} (G : SimpleGraph (Fin n))
    (hG : G.IsTree) {u v w : Fin n} (hbranch : Branch333 G u v w) :
    (Finset.univ.filter (fun x => degree G x = 1)).card = 5 := by
  classical
  obtain ⟨huv, huw, hvw, hu, hv, hw, hrest⟩ := hbranch
  let : Nontrivial (Fin n) := ⟨⟨u, v, huv⟩⟩
  have hpos (x : Fin n) : 1 ≤ degree G x := by
    rw [degree_eq_graph_degree]
    exact hG.preconnected.degree_pos_of_nontrivial x
  have hpoint (x : Fin n) :
      degree G x + (if degree G x = 1 then 1 else 0) =
        2 + (if x = u then 1 else 0) + (if x = v then 1 else 0) +
          (if x = w then 1 else 0) := by
    by_cases hxu : x = u
    · subst x
      simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, hu, huv, huw]
    by_cases hxv : x = v
    · subst x
      simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, hv, huv.symm, hvw]
    by_cases hxw : x = w
    · subst x
      simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, hw, huw.symm, hvw.symm]
    have := hrest x hxu hxv hxw
    have := hpos x
    split_ifs <;> omega
  have hsum := congrArg (fun f : Fin n → ℕ => ∑ x, f x) (funext hpoint)
  have hdegrees : ∑ x : Fin n, degree G x = 2 * edgeCount G := by
    simp_rw [degree_eq_graph_degree, edgeCount_eq_card_edgeFinset]
    exact G.sum_degrees_eq_twice_card_edges
  have htree := edgeCount_add_one_eq_of_isTree G hG
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    Finset.sum_boole] at hsum
  rw [hdegrees] at hsum
  norm_num [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero] at hsum
  omega

/-- The three named branch vertices are precisely the vertices of degree three. -/
theorem Branch333.degree_eq_three_iff {n : ℕ} {G : SimpleGraph (Fin n)}
    {u v w : Fin n} (h : Branch333 G u v w) (x : Fin n) :
    degree G x = 3 ↔ x = u ∨ x = v ∨ x = w := by
  obtain ⟨huv, huw, hvw, hu, hv, hw, hrest⟩ := h
  constructor
  · intro hx
    by_contra hne
    push Not at hne
    have := hrest x hne.1 hne.2.1 hne.2.2
    omega
  · rintro (rfl | rfl | rfl) <;> assumption

/-- Every remaining vertex in the tree is either a leaf or a subdivision vertex. -/
theorem Branch333.degree_eq_one_or_two {n : ℕ} {G : SimpleGraph (Fin n)}
    (hG : G.IsTree) {u v w : Fin n} (h : Branch333 G u v w)
    {x : Fin n} (hxu : x ≠ u) (hxv : x ≠ v) (hxw : x ≠ w) :
    degree G x = 1 ∨ degree G x = 2 := by
  classical
  let : Nontrivial (Fin n) := ⟨⟨u, v, h.1⟩⟩
  have hpos : 1 ≤ degree G x := by
    rw [degree_eq_graph_degree]
    exact hG.preconnected.degree_pos_of_nontrivial x
  have := h.2.2.2.2.2.2 x hxu hxv hxw
  omega

/-- The branch set has exactly three elements. -/
theorem Branch333.branch_count {n : ℕ} {G : SimpleGraph (Fin n)}
    {u v w : Fin n} (h : Branch333 G u v w) :
    (Finset.univ.filter (fun x => degree G x = 3)).card = 3 := by
  classical
  have hset : Finset.univ.filter (fun x => degree G x = 3) = {u, v, w} := by
    ext x
    simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, h.degree_eq_three_iff x]
  rw [hset]
  simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, h.1, h.2.1, h.2.2.1]

/-- A source11 tree has exactly eight essential vertices: its three branch
vertices and its five leaves. All other vertices have degree two. -/
theorem branch333_subdivision_count {n : ℕ} (G : SimpleGraph (Fin n))
    (hG : G.IsTree) {u v w : Fin n} (h : Branch333 G u v w) :
    (Finset.univ.filter (fun x => degree G x = 2)).card + 8 = n := by
  classical
  have hpoint (x : Fin n) :
      (if degree G x = 1 then 1 else 0) +
      (if degree G x = 2 then 1 else 0) +
      (if degree G x = 3 then 1 else 0) = (1 : ℕ) := by
    by_cases hxu : x = u
    · subst x; simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, h.2.2.2.1]
    by_cases hxv : x = v
    · subst x; simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, h.2.2.2.2.1]
    by_cases hxw : x = w
    · subst x; simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, h.2.2.2.2.2.1]
    rcases h.degree_eq_one_or_two hG hxu hxv hxw with hx | hx <;> simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, hx]
  have hsum := congrArg (fun f : Fin n → ℕ => ∑ x, f x) (funext hpoint)
  simp only [Finset.sum_add_distrib, Finset.sum_boole, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at hsum
  rw [branch333_leaf_count G hG h, h.branch_count] at hsum
  norm_num [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero] at hsum
  omega

/-- Every source11 instance has at least eight vertices. -/
theorem branch333_eight_le {n : ℕ} (G : SimpleGraph (Fin n))
    (hG : G.IsTree) {u v w : Fin n} (h : Branch333 G u v w) : 8 ≤ n := by
  have := branch333_subdivision_count G hG h
  omega

/-- An internal vertex of a simple path has two distinct neighbors on that path. -/
theorem internal_path_two_neighbors {n : ℕ} {G : SimpleGraph (Fin n)}
    {u v x : Fin n} {p : G.Walk u v} (hp : p.IsPath)
    (hx : x ∈ p.support) (hxu : x ≠ u) (hxv : x ≠ v) :
    ∃ a b, a ≠ b ∧ G.Adj x a ∧ G.Adj x b ∧
      a ∈ p.support ∧ b ∈ p.support := by
  obtain ⟨i, hi, hil⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hx
  have hi0 : 0 < i := by
    by_contra hzero
    have : i = 0 := by omega
    subst i
    simp only [SimpleGraph.Walk.getVert_zero] at hi
    exact hxu hi.symm
  have hit : i < p.length := by
    by_contra hnot
    have : i = p.length := by omega
    subst i
    simp only [SimpleGraph.Walk.getVert_length] at hi
    exact hxv hi.symm
  refine ⟨p.getVert (i - 1), p.getVert (i + 1), ?_, ?_, ?_,
    p.getVert_mem_support _, p.getVert_mem_support _⟩
  · intro heq
    have := hp.getVert_injOn (by simp only [Set.mem_ofPred_eq]; omega)
      (by simp only [Set.mem_ofPred_eq]; omega) heq
    omega
  · have hadj := (p.adj_getVert_succ (i := i - 1) (by omega)).symm
    simpa only [Nat.sub_add_cancel hi0, hi] using hadj
  · simpa only [hi] using p.adj_getVert_succ hit

/-- An internal path vertex with an extra neighbor outside the path has degree
at least three. -/
theorem three_le_degree_of_off_path_neighbor {n : ℕ} {G : SimpleGraph (Fin n)}
    {u v x y : Fin n} {p : G.Walk u v} (hp : p.IsPath)
    (hx : x ∈ p.support) (hxu : x ≠ u) (hxv : x ≠ v)
    (hxy : G.Adj x y) (hy : y ∉ p.support) : 3 ≤ degree G x := by
  classical
  obtain ⟨a, b, hab, hxa, hxb, ha, hb⟩ := internal_path_two_neighbors hp hx hxu hxv
  have hay : a ≠ y := by rintro rfl; exact hy ha
  have hby : b ≠ y := by rintro rfl; exact hy hb
  have hsub : ({a, b, y} : Finset (Fin n)) ⊆ G.neighborFinset x := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl
    · simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero] using hxa
    · simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero] using hxb
    · simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero] using hxy
  have hcard := Finset.card_le_card hsub
  rw [degree_eq_graph_degree]
  simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, hab, hay, hby] using hcard

/-- Any extra edge leaving an internal vertex of a path must leave at one of
the three named branch vertices. -/
theorem Branch333.off_path_neighbor_is_branch {n : ℕ} {G : SimpleGraph (Fin n)}
    {a b c u v x y : Fin n} (h : Branch333 G a b c) {p : G.Walk u v}
    (hp : p.IsPath) (hx : x ∈ p.support) (hxu : x ≠ u) (hxv : x ≠ v)
    (hxy : G.Adj x y) (hy : y ∉ p.support) : x = a ∨ x = b ∨ x = c := by
  have hdeg := three_le_degree_of_off_path_neighbor hp hx hxu hxv hxy hy
  by_contra hne
  push Not at hne
  have := h.2.2.2.2.2.2 x hne.1 hne.2.1 hne.2.2
  omega

/-- A path from an arbitrary vertex can be chosen to meet a given walk for
the first time at its terminal vertex. -/
theorem exists_path_first_meeting {n : ℕ} {G : SimpleGraph (Fin n)}
    (hconn : G.Connected) {u v : Fin n} (p : G.Walk u v) (w : Fin n) :
    ∃ x, x ∈ p.support ∧ ∃ q : G.Walk w x, q.IsPath ∧
      ∀ y, y ∈ q.support → y ∈ p.support → y = x := by
  classical
  have hex : ∃ k : ℕ, ∃ x, x ∈ p.support ∧
      ∃ q : G.Walk w x, q.IsPath ∧ q.length = k := by
    obtain ⟨q, hq⟩ := hconn.exists_isPath w u
    exact ⟨q.length, u, p.start_mem_support, q, hq, rfl⟩
  obtain ⟨x, hxp, q, hq, hlen⟩ := Nat.find_spec hex
  refine ⟨x, hxp, q, hq, ?_⟩
  intro y hyq hyp
  by_contra hyx
  have hlt := SimpleGraph.Walk.length_takeUntil_lt_length hyq hyx
  have hmin := Nat.find_min' hex
    (show ∃ x, x ∈ p.support ∧ ∃ r : G.Walk w x,
        r.IsPath ∧ r.length = (q.takeUntil y hyq).length from
      ⟨y, hyp, q.takeUntil y hyq, hq.takeUntil hyq, rfl⟩)
  omega

/-- Joining paths whose only common vertex is the joining vertex gives a path. -/
theorem isPath_append_of_intersection {n : ℕ} {G : SimpleGraph (Fin n)}
    {u v w : Fin n} {p : G.Walk u v} {q : G.Walk v w}
    (hp : p.IsPath) (hq : q.IsPath)
    (hmeet : ∀ x, x ∈ p.support → x ∈ q.support → x = v) :
    (p.append q).IsPath := by
  rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_append, List.nodup_append']
  refine ⟨hp.support_nodup, hq.support_nodup.tail, ?_⟩
  apply List.disjoint_left.mpr
  intro x hxp hxq
  have hxv := hmeet x hxp (List.mem_of_mem_tail hxq)
  have hstart : v ∉ q.support.tail := by
    have := hq.support_nodup
    rw [← q.cons_tail_support, List.nodup_cons] at this
    exact this.1
  exact hstart (hxv ▸ hxq)

/-- The three branch vertices lie on one simple path. Equivalently, one of
them is between the other two. -/
theorem Branch333.exists_spine {n : ℕ} {G : SimpleGraph (Fin n)}
    (hG : G.IsTree) {u v w : Fin n} (h : Branch333 G u v w) :
    (∃ p : G.Walk u v, p.IsPath ∧ w ∈ p.support) ∨
    (∃ p : G.Walk u w, p.IsPath ∧ v ∈ p.support) ∨
    (∃ p : G.Walk v w, p.IsPath ∧ u ∈ p.support) := by
  classical
  obtain ⟨p, hp⟩ := hG.connected.exists_isPath u v
  by_cases hwp : w ∈ p.support
  · exact Or.inl ⟨p, hp, hwp⟩
  obtain ⟨x, hxp, q, hq, hmeet⟩ := exists_path_first_meeting hG.connected p w
  have hwx : w ≠ x := by
    intro heq
    exact hwp (heq ▸ hxp)
  have hnil : ¬q.Nil := SimpleGraph.Walk.not_nil_of_ne hwx
  have hadj : G.Adj x q.penultimate := (q.adj_penultimate hnil).symm
  have hy : q.penultimate ∉ p.support := by
    intro hy
    exact hadj.ne (hmeet _ (q.getVert_mem_support _) hy).symm
  have hxuv : x = u ∨ x = v := by
    by_cases hxu : x = u
    · exact Or.inl hxu
    by_cases hxv : x = v
    · exact Or.inr hxv
    have hbranch := h.off_path_neighbor_is_branch hp hxp hxu hxv hadj hy
    rcases hbranch with hxu' | hxv' | hxw
    · exact (hxu hxu').elim
    · exact (hxv hxv').elim
    · exact (hwx hxw.symm).elim
  rcases hxuv with rfl | rfl
  · right; right
    refine ⟨p.reverse.append q.reverse, ?_, ?_⟩
    · apply isPath_append_of_intersection hp.reverse hq.reverse
      intro z hzp hzq
      exact hmeet z (by simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero] using hzq) (by simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero] using hzp)
    · exact (p.reverse.support_subset_support_append_left q.reverse)
        p.reverse.end_mem_support
  · right; left
    refine ⟨p.append q.reverse, ?_, ?_⟩
    · apply isPath_append_of_intersection hp hq.reverse
      intro z hzp hzq
      exact hmeet z (by simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero] using hzq) hzp
    · exact (p.support_subset_support_append_left q.reverse) p.end_mem_support

/-- The degree pattern is invariant under swapping the first two branch vertices. -/
theorem Branch333.swap_left {n : ℕ} {G : SimpleGraph (Fin n)}
    {u v w : Fin n} (h : Branch333 G u v w) : Branch333 G v u w := by
  obtain ⟨huv, huw, hvw, hu, hv, hw, hrest⟩ := h
  exact ⟨huv.symm, hvw, huw, hv, hu, hw,
    fun x hxv hxu hxw => hrest x hxu hxv hxw⟩

/-- The degree pattern is invariant under swapping the last two branch vertices. -/
theorem Branch333.swap_right {n : ℕ} {G : SimpleGraph (Fin n)}
    {u v w : Fin n} (h : Branch333 G u v w) : Branch333 G u w v := by
  obtain ⟨huv, huw, hvw, hu, hv, hw, hrest⟩ := h
  exact ⟨huw, huv, hvw.symm, hu, hw, hv,
    fun x hxu hxw hxv => hrest x hxu hxv hxw⟩

/-- The branch vertices can be ordered along a spine, with the middle one
listed second. -/
theorem Branch333.exists_ordered_spine {n : ℕ} {G : SimpleGraph (Fin n)}
    (hG : G.IsTree) {u v w : Fin n} (h : Branch333 G u v w) :
    ∃ a b c, Branch333 G a b c ∧ ∃ p : G.Walk a c, p.IsPath ∧ b ∈ p.support := by
  rcases h.exists_spine hG with ⟨p, hp, hw⟩ | ⟨p, hp, hv⟩ | ⟨p, hp, hu⟩
  · exact ⟨u, w, v, h.swap_right, p, hp, hw⟩
  · exact ⟨u, v, w, h, p, hp, hv⟩
  · exact ⟨v, u, w, h.swap_left, p, hp, hu⟩

/-- Away from the three branch vertices, no edge leaves the spine. -/
theorem Branch333.spine_neighbor_mem {n : ℕ} {G : SimpleGraph (Fin n)}
    {a b c : Fin n} (h : Branch333 G a b c) {p : G.Walk a c} (hp : p.IsPath)
    {x y : Fin n} (hx : x ∈ p.support) (hxa : x ≠ a) (hxb : x ≠ b) (hxc : x ≠ c)
    (hxy : G.Adj x y) : y ∈ p.support := by
  by_contra hy
  rcases h.off_path_neighbor_is_branch hp hx hxa hxc hxy hy with ha | hb | hc
  · exact hxa ha
  · exact hxb hb
  · exact hxc hc

/-- A path endpoint in a tree has exactly one neighbor on the path. -/
theorem path_start_neighbor_count {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj]
    (hG : G.IsTree) {u v : Fin n} {p : G.Walk u v} (hp : p.IsPath) (huv : u ≠ v) :
    ((G.neighborFinset u).filter (fun x => x ∈ p.support)).card = 1 := by
  classical
  have hnil : ¬p.Nil := SimpleGraph.Walk.not_nil_of_ne huv
  have heq : (G.neighborFinset u).filter (fun x => x ∈ p.support) = {p.snd} := by
    ext x
    simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset, Finset.mem_singleton]
    constructor
    · rintro ⟨hadj, hx⟩
      exact hG.isAcyclic.eq_snd_of_adj_start hp hadj hx
    · rintro rfl
      exact ⟨p.adj_snd hnil, p.getVert_mem_support 1⟩
  rw [heq]
  simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero]

/-- An internal vertex of a tree path has exactly two neighbors on that path. -/
theorem path_internal_neighbor_count {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] (hG : G.IsTree) {u v x : Fin n} {p : G.Walk u v}
    (hp : p.IsPath) (hx : x ∈ p.support) (hxu : x ≠ u) (hxv : x ≠ v) :
    ((G.neighborFinset x).filter (fun y => y ∈ p.support)).card = 2 := by
  classical
  obtain ⟨q, r, hq, hr, hqr⟩ := hp.mem_support_iff_exists_append.mp hx
  let s := (G.neighborFinset x).filter (fun y => y ∈ p.support)
  have hsub : s ⊆ {q.penultimate, r.snd} := by
    intro y hy
    obtain ⟨hadj, hymem⟩ : G.Adj x y ∧ y ∈ p.support := by simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, s] using hy
    rw [hqr, SimpleGraph.Walk.mem_support_append_iff] at hymem
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases hymem with hyq | hyr
    · exact Or.inl (hG.isAcyclic.eq_penultimate_of_adj_end hq hadj hyq)
    · exact Or.inr (hG.isAcyclic.eq_snd_of_adj_start hr hadj hyr)
  have hupper : s.card ≤ 2 := (Finset.card_le_card hsub).trans (by
    calc ({q.penultimate, r.snd} : Finset (Fin n)).card ≤
        ({r.snd} : Finset (Fin n)).card + 1 := Finset.card_insert_le _ _
      _ = 2 := by simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero])
  obtain ⟨a, b, hab, hxa, hxb, ha, hb⟩ := internal_path_two_neighbors hp hx hxu hxv
  have hsub' : ({a, b} : Finset (Fin n)) ⊆ s := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    · simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, s, hxa, ha]
    · simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, s, hxb, hb]
  have hlower : 2 ≤ s.card := by simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, hab] using Finset.card_le_card hsub'
  exact Nat.le_antisymm hupper hlower

/-- There are two pendant directions at either endpoint of the branch spine. -/
theorem branch_spine_start_outside_count {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] (hG : G.IsTree) {u v : Fin n} {p : G.Walk u v}
    (hp : p.IsPath) (huv : u ≠ v) (hdeg : degree G u = 3) :
    ((G.neighborFinset u).filter (fun x => x ∉ p.support)).card = 2 := by
  classical
  have hsum := Finset.card_filter_add_card_filter_not
    (s := G.neighborFinset u) (fun x => x ∈ p.support)
  have hon := path_start_neighbor_count hG hp huv
  have hcard : (G.neighborFinset u).card = 3 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree, ← degree_eq_graph_degree, hdeg]
  omega

/-- There is one pendant direction at the middle vertex of the branch spine. -/
theorem branch_spine_internal_outside_count {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] (hG : G.IsTree) {u v x : Fin n} {p : G.Walk u v}
    (hp : p.IsPath) (hx : x ∈ p.support) (hxu : x ≠ u) (hxv : x ≠ v)
    (hdeg : degree G x = 3) :
    ((G.neighborFinset x).filter (fun y => y ∉ p.support)).card = 1 := by
  classical
  have hsum := Finset.card_filter_add_card_filter_not
    (s := G.neighborFinset x) (fun y => y ∈ p.support)
  have hon := path_internal_neighbor_count hG hp hx hxu hxv
  have hcard : (G.neighborFinset x).card = 3 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree, ← degree_eq_graph_degree, hdeg]
  omega

/-- A component obtained by deleting a vertex is an arm whenever all its
original vertices have degree at most two. -/
theorem deleted_component_is_arm_of_degrees {n : ℕ} (G : SimpleGraph (Fin n))
    (hG : G.IsTree) (u : Fin n)
    (c : (deleteVertexGraph G u).ConnectedComponent)
    (hdegrees : ∀ z : c, degree G z.val.val ≤ 2)
    (x : G.neighborSet u) (hxcomp : neighborComponent G u x = c) :
    ∃ (k : ℕ) (e : SimpleGraph.pathGraph (k + 1) ≃g c.toSimpleGraph),
      (e 0).val.val = x.val := by
  classical
  let ec : c.toSimpleGraph ↪g deleteVertexGraph G u := SimpleGraph.Embedding.induce c.supp
  let eG : deleteVertexGraph G u ↪g G := SimpleGraph.Embedding.induce _
  have htree : c.toSimpleGraph.IsTree :=
    (hG.isAcyclic.induce _).isTree_connectedComponent c
  have hdeg (z : c) : c.toSimpleGraph.degree z ≤ 2 := by
    apply (ec.toCopy.degree_le z).trans
    apply (eG.toCopy.degree_le z.val).trans
    change G.degree z.val.val ≤ 2
    rw [← degree_eq_graph_degree]
    exact hdegrees z
  let entry : c := ⟨⟨x.val, x.property.ne'⟩, by
    apply (c.mem_supp_iff _).mpr
    exact hxcomp⟩
  have hentry : c.toSimpleGraph.degree entry ≤ 1 := by
    apply (ec.toCopy.degree_le entry).trans
    have hxdeg : G.degree x.val ≤ 2 := by
      rw [← degree_eq_graph_degree]
      exact hdegrees entry
    exact degree_deleteVertex_le_one G u x hxdeg
  obtain ⟨k, e, he⟩ := exists_pathGraph_iso_from_leaf c.toSimpleGraph htree hdeg entry hentry
  exact ⟨k, e, congrArg (fun z : c => z.val.val) he⟩

noncomputable def chooseArmPathOfDegrees {n : ℕ} (G : SimpleGraph (Fin n))
    (hG : G.IsTree) {u v : Fin n} (hne : u ≠ v) (c : ArmComponents G hne)
    (hdegrees : ∀ z : c.val, degree G z.val.val ≤ 2) : ArmPath G hne c := by
  classical
  let x := (neighborComponentEquiv G u hG).symm c.val
  have hx : neighborComponent G u x = c.val :=
    (neighborComponentEquiv G u hG).apply_symm_apply c.val
  have hex := deleted_component_is_arm_of_degrees G hG u c.val hdegrees x hx
  let k := Classical.choose hex
  let e := Classical.choose (Classical.choose_spec hex)
  have he := Classical.choose_spec (Classical.choose_spec hex)
  exact ⟨k + 1, Nat.succ_pos _, e, x, hx, he⟩

/-- At an endpoint of the ordered branch spine, every noncentral component
is a path even though the tree has a third branch vertex. -/
noncomputable def chooseEndpointArmPath333 {n : ℕ} {G : SimpleGraph (Fin n)}
    (hG : G.IsTree) {a b c : Fin n} (h : Branch333 G a b c)
    {p : G.Walk a c} (hp : p.IsPath) (hb : b ∈ p.support)
    (s : ArmComponents G h.2.1) : ArmPath G h.2.1 s := by
  apply chooseArmPathOfDegrees G hG h.2.1 s
  intro z
  apply h.2.2.2.2.2.2 _ z.val.property
  · intro hzb
    have hzcomp := (s.val.mem_supp_iff z.val).mp z.property
    have hbccomp := path_mem_deleted_component G h.2.1 hp hb h.1.symm
    have heq : z.val = (⟨b, h.1.symm⟩ : {x : Fin n // x ≠ a}) := Subtype.ext hzb
    rw [heq, hbccomp] at hzcomp
    exact s.property hzcomp.symm
  · intro hzc
    have hzcomp := (s.val.mem_supp_iff z.val).mp z.property
    have heq : z.val = (⟨c, h.2.1.symm⟩ : {x : Fin n // x ≠ a}) := Subtype.ext hzc
    rw [heq] at hzcomp
    exact s.property hzcomp.symm

/-- Removing an internal vertex of a tree path separates its endpoints. -/
theorem path_internal_deleted_component_ne {n : ℕ} {G : SimpleGraph (Fin n)}
    (hG : G.IsTree) {u v x : Fin n} {p : G.Walk u v} (hp : p.IsPath)
    (hx : x ∈ p.support) (hxu : x ≠ u) (hxv : x ≠ v) :
    (deleteVertexGraph G x).connectedComponentMk ⟨u, hxu.symm⟩ ≠
      (deleteVertexGraph G x).connectedComponentMk ⟨v, hxv.symm⟩ := by
  intro heq
  obtain ⟨q, hq⟩ := (SimpleGraph.ConnectedComponent.exact heq).exists_isPath
  let e : deleteVertexGraph G x ↪g G := SimpleGraph.Embedding.induce _
  let q' : G.Walk u v := q.map e.toHom
  have hqm : q'.IsPath := hq.map e.injective
  have hxnot : x ∉ q'.support := by
    change x ∉ (q.map e.toHom).support
    rw [SimpleGraph.Walk.support_map]
    intro hxmap
    obtain ⟨z, hz, hzx⟩ := List.mem_map.mp hxmap
    exact z.property hzx
  have heqp : q' = p :=
    Subtype.mk.inj (hG.isAcyclic.subsingleton_path u v |>.elim ⟨q', hqm⟩ ⟨p, hp⟩)
  rw [heqp] at hxnot
  exact hxnot hx

/-- The component at the middle branch that points toward neither endpoint. -/
def CenterArmComponents333 {n : ℕ} (G : SimpleGraph (Fin n))
    {a b c : Fin n} (hba : b ≠ a) (hbc : b ≠ c) :=
  {s : ArmComponents G hba //
    s.val ≠ (deleteVertexGraph G b).connectedComponentMk ⟨c, hbc.symm⟩}

noncomputable def chooseCenterArmPath333 {n : ℕ} {G : SimpleGraph (Fin n)}
    (hG : G.IsTree) {a b c : Fin n} (h : Branch333 G a b c)
    (s : CenterArmComponents333 G h.1.symm h.2.2.1) : ArmPath G h.1.symm s.val := by
  apply chooseArmPathOfDegrees G hG h.1.symm s.val
  intro z
  apply h.2.2.2.2.2.2 _
  · intro hza
    have hzcomp := (s.val.val.mem_supp_iff z.val).mp z.property
    have heq : z.val = (⟨a, h.1⟩ : {x : Fin n // x ≠ b}) := Subtype.ext hza
    rw [heq] at hzcomp
    exact s.val.property hzcomp.symm
  · exact z.val.property
  · intro hzc
    have hzcomp := (s.val.val.mem_supp_iff z.val).mp z.property
    have heq : z.val = (⟨c, h.2.2.1.symm⟩ : {x : Fin n // x ≠ b}) := Subtype.ext hzc
    rw [heq] at hzcomp
    exact s.property hzcomp.symm

/-- The two endpoints each have two arm components. -/
theorem endpoint_arm_components333_card {n : ℕ} {G : SimpleGraph (Fin n)}
    (hG : G.IsTree) {a b c : Fin n} (h : Branch333 G a b c) :
    Nat.card (ArmComponents G h.2.1) = 2 ∧
      Nat.card (ArmComponents G h.2.1.symm) = 2 := by
  classical
  constructor
  · rw [armComponents_card G h.2.1 hG, ← degree_eq_graph_degree, h.2.2.2.1]
  · rw [armComponents_card G h.2.1.symm hG, ← degree_eq_graph_degree, h.2.2.2.2.2.1]

/-- Exactly one component remains at the middle branch after excluding the
two directions along the spine. -/
theorem center_arm_components333_card {n : ℕ} {G : SimpleGraph (Fin n)}
    (hG : G.IsTree) {a b c : Fin n} (h : Branch333 G a b c)
    {p : G.Walk a c} (hp : p.IsPath) (hb : b ∈ p.support) :
    Nat.card (CenterArmComponents333 G h.1.symm h.2.2.1) = 1 := by
  classical
  let : Fintype (deleteVertexGraph G b).ConnectedComponent := Fintype.ofFinite _
  let : Fintype (ArmComponents G h.1.symm) := by unfold ArmComponents; infer_instance
  have hsep := path_internal_deleted_component_ne hG hp hb h.1.symm h.2.2.1
  let c0 : ArmComponents G h.1.symm :=
    ⟨(deleteVertexGraph G b).connectedComponentMk ⟨c, h.2.2.1.symm⟩, hsep.symm⟩
  let e : CenterArmComponents333 G h.1.symm h.2.2.1 ≃
      {s : ArmComponents G h.1.symm // s ≠ c0} :=
    Equiv.subtypeEquivRight (fun s => by
      change (s.val ≠ c0.val) ↔ s ≠ c0
      constructor
      · intro hn heq
        exact hn (congrArg Subtype.val heq)
      · intro hn heq
        exact hn (Subtype.ext heq))
  have hcard : Fintype.card (ArmComponents G h.1.symm) = 2 := by
    rw [← Nat.card_eq_fintype_card, armComponents_card G h.1.symm hG,
      ← degree_eq_graph_degree, h.2.2.2.2.1]
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
  simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, hcard]

def InCenterArm333 {n : ℕ} (G : SimpleGraph (Fin n))
    {a b c : Fin n} (hba : b ≠ a) (hbc : b ≠ c) (x : Fin n) : Prop :=
  InArm G hba x ∧ InArm G hbc x

/-- The spine and its five arm components cover every vertex. -/
theorem branch333_spine_and_arms_cover {n : ℕ} {G : SimpleGraph (Fin n)}
    (hG : G.IsTree) {a b c : Fin n} (h : Branch333 G a b c)
    {p : G.Walk a c} (hp : p.IsPath) (hb : b ∈ p.support) (x : Fin n) :
    x ∈ p.support ∨ InArm G h.2.1 x ∨ InArm G h.2.1.symm x ∨
      InCenterArm333 G h.1.symm h.2.2.1 x := by
  obtain ⟨q, r, hq, hr, hqr⟩ := hp.mem_support_iff_exists_append.mp hb
  let S : Fin n → Prop := fun x =>
    x ∈ p.support ∨ InArm G h.2.1 x ∨ InArm G h.2.1.symm x ∨
      InCenterArm333 G h.1.symm h.2.2.1 x
  have hclosed {u v : Fin n} (hu : S u) (huv : G.Adj u v) : S v := by
    rcases hu with hu | hu | hu | hu
    · by_cases hvp : v ∈ p.support
      · exact Or.inl hvp
      by_cases hua : u = a
      · subst u
        exact Or.inr (Or.inl (adjacent_not_mem_path_inArm G h.2.1 hG.isAcyclic hp huv hvp))
      by_cases huc : u = c
      · subst u
        exact Or.inr (Or.inr (Or.inl (adjacent_not_mem_path_inArm G h.2.1.symm
          hG.isAcyclic hp.reverse huv (by simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero] using hvp))))
      have hub : u = b := by
        rcases h.off_path_neighbor_is_branch hp hu hua huc huv hvp with heq | heq | heq
        · exact (hua heq).elim
        · exact heq
        · exact (huc heq).elim
      subst u
      right; right; right
      constructor
      · apply adjacent_not_mem_path_inArm G h.1.symm hG.isAcyclic hq.reverse huv
        intro hvq
        apply hvp
        rw [hqr, SimpleGraph.Walk.mem_support_append_iff]
        exact Or.inl (by simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero] using hvq)
      · apply adjacent_not_mem_path_inArm G h.2.2.1 hG.isAcyclic hr huv
        intro hvr
        apply hvp
        rw [hqr, SimpleGraph.Walk.mem_support_append_iff]
        exact Or.inr hvr
    · rcases adjacent_inArm_or_root G h.2.1 hu huv with rfl | hv
      · exact Or.inl p.start_mem_support
      · exact Or.inr (Or.inl hv)
    · rcases adjacent_inArm_or_root G h.2.1.symm hu huv with rfl | hv
      · exact Or.inl p.end_mem_support
      · exact Or.inr (Or.inr (Or.inl hv))
    · rcases adjacent_inArm_or_root G h.1.symm hu.1 huv with rfl | hv
      · exact Or.inl hb
      rcases adjacent_inArm_or_root G h.2.2.1 hu.2 huv with rfl | hv'
      · exact Or.inl hb
      exact Or.inr (Or.inr (Or.inr ⟨hv, hv'⟩))
  have hwalk {u v : Fin n} (q : G.Walk u v) : S u → S v := by
    induction q with
    | nil => exact id
    | cons hadj q ih => exact fun hu => ih (hclosed hu hadj)
  obtain ⟨q⟩ := hG.connected a x
  exact hwalk q (Or.inl p.start_mem_support)

theorem center_arm_not_mem_spine333 {n : ℕ} {G : SimpleGraph (Fin n)}
    {a b c : Fin n} (h : Branch333 G a b c) {p : G.Walk a c}
    (hp : p.IsPath) (hb : b ∈ p.support) {x : Fin n}
    (hx : InCenterArm333 G h.1.symm h.2.2.1 x) : x ∉ p.support := by
  obtain ⟨q, r, hq, hr, hqr⟩ := hp.mem_support_iff_exists_append.mp hb
  intro hxp
  rw [hqr, SimpleGraph.Walk.mem_support_append_iff] at hxp
  rcases hxp with hxq | hxr
  · exact not_inArm_of_mem_path G h.1.symm hq.reverse (by simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero] using hxq) hx.1
  · exact not_inArm_of_mem_path G h.2.2.1 hr hxr hx.2

/-- Changing the far endpoint along a path does not change the arms at its start. -/
theorem inArm_along_path_iff {n : ℕ} {G : SimpleGraph (Fin n)}
    {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c) {p : G.Walk a c}
    (hp : p.IsPath) (hb : b ∈ p.support) (x : Fin n) :
    InArm G hab x ↔ InArm G hac x := by
  have hcomp := path_mem_deleted_component G hac hp hb hab.symm
  unfold InArm
  simp only [hcomp]

theorem endpoint_arm_not_center333 {n : ℕ} {G : SimpleGraph (Fin n)}
    (hG : G.Connected) {a b c : Fin n} (h : Branch333 G a b c)
    {p : G.Walk a c} (hp : p.IsPath) (hb : b ∈ p.support) {x : Fin n}
    (hx : InArm G h.2.1 x) : ¬ InCenterArm333 G h.1.symm h.2.2.1 x := by
  intro hcenter
  apply inArm_not_reverse G h.1 hG ((inArm_along_path_iff h.1 h.2.1 hp hb x).mpr hx)
  exact hcenter.1

/-- Arm-path vertices in the central family satisfy both component exclusions. -/
theorem center_arm_vertex_in_center333 {n : ℕ} {G : SimpleGraph (Fin n)}
    {a b c : Fin n} (hba : b ≠ a) (hbc : b ≠ c)
    {s : CenterArmComponents333 G hba hbc} (P : ArmPath G hba s.val)
    (i : Fin P.length) : InCenterArm333 G hba hbc (P.vertex i) := by
  refine ⟨P.vertex_inArm i, P.vertex_ne_root i, ?_⟩
  rw [P.vertex_component]
  exact s.property

theorem Branch333.reverse {n : ℕ} {G : SimpleGraph (Fin n)}
    {a b c : Fin n} (h : Branch333 G a b c) : Branch333 G c b a :=
  h.swap_left.swap_right.swap_left

theorem far_endpoint_arm_not_center333 {n : ℕ} {G : SimpleGraph (Fin n)}
    (hG : G.Connected) {a b c : Fin n} (h : Branch333 G a b c)
    {p : G.Walk a c} (hp : p.IsPath) (hb : b ∈ p.support) {x : Fin n}
    (hx : InArm G h.2.1.symm x) : ¬ InCenterArm333 G h.1.symm h.2.2.1 x := by
  intro hcenter
  exact endpoint_arm_not_center333 hG h.reverse hp.reverse (by simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero] using hb) hx
    ⟨hcenter.2, hcenter.1⟩

abbrev TripleArmModelVertex {A B C : Type*} (d : ℕ) (a : A → ℕ)
    (b : B → ℕ) (c : C → ℕ) :=
  Fin (d + 1) ⊕ ((i : A) × Fin (a i)) ⊕ ((j : B) × Fin (b j)) ⊕ ((k : C) × Fin (c k))

noncomputable def tripleArmModelMap {n : ℕ} {G : SimpleGraph (Fin n)}
    {a b c : Fin n} (h : Branch333 G a b c) {p : G.Walk a c} (hp : p.IsPath)
    (A : (s : ArmComponents G h.2.1) → ArmPath G h.2.1 s)
    (B : (s : ArmComponents G h.2.1.symm) → ArmPath G h.2.1.symm s)
    (C : (s : CenterArmComponents333 G h.1.symm h.2.2.1) → ArmPath G h.1.symm s.val) :
    TripleArmModelVertex p.length (fun s => (A s).length)
      (fun s => (B s).length) (fun s => (C s).length) → Fin n
  | .inl i => Spine.vertex hp i
  | .inr (.inl ⟨s, i⟩) => (A s).vertex i
  | .inr (.inr (.inl ⟨s, i⟩)) => (B s).vertex i
  | .inr (.inr (.inr ⟨s, i⟩)) => (C s).vertex i

theorem tripleArmModelMap_bijective {n : ℕ} {G : SimpleGraph (Fin n)}
    (hG : G.IsTree) {a b c : Fin n} (h : Branch333 G a b c)
    {p : G.Walk a c} (hp : p.IsPath) (hb : b ∈ p.support)
    (A : (s : ArmComponents G h.2.1) → ArmPath G h.2.1 s)
    (B : (s : ArmComponents G h.2.1.symm) → ArmPath G h.2.1.symm s)
    (C : (s : CenterArmComponents333 G h.1.symm h.2.2.1) → ArmPath G h.1.symm s.val) :
    Function.Bijective (tripleArmModelMap h hp A B C) := by
  have hcenter (s) (i) := center_arm_vertex_in_center333 h.1.symm h.2.2.1 (C s) i
  have hpc (i) (s) (j) : Spine.vertex hp i ≠ (C s).vertex j := by
    intro heq
    exact center_arm_not_mem_spine333 h hp hb (hcenter s j)
      (heq ▸ Spine.vertex_mem hp i)
  have hac (s) (i) (t) (j) : (A s).vertex i ≠ (C t).vertex j := by
    intro heq
    exact endpoint_arm_not_center333 hG.connected h hp hb
      (heq ▸ (A s).vertex_inArm i) (hcenter t j)
  have hbc (s) (i) (t) (j) : (B s).vertex i ≠ (C t).vertex j := by
    intro heq
    exact far_endpoint_arm_not_center333 hG.connected h hp hb
      (heq ▸ (B s).vertex_inArm i) (hcenter t j)
  have hab (s) (i) (t) (j) : (A s).vertex i ≠ (B t).vertex j := by
    intro heq
    exact inArm_not_reverse G h.2.1 hG.connected
      (heq ▸ (A s).vertex_inArm i) ((B t).vertex_inArm j)
  constructor
  · intro x y hxy
    rcases x with x | ⟨s, i⟩ | ⟨s, i⟩ | ⟨s, i⟩ <;>
      rcases y with y | ⟨t, j⟩ | ⟨t, j⟩ | ⟨t, j⟩ <;>
        dsimp [tripleArmModelMap] at hxy
    · exact congrArg Sum.inl (Spine.vertex_injective hp hxy)
    · exact (Spine.vertex_ne_arm hp (A t) x j hxy).elim
    · exact (Spine.vertex_ne_reverse_arm (hne := h.2.1) hp (B t) x j hxy).elim
    · exact (hpc x t j hxy).elim
    · exact (Spine.vertex_ne_arm hp (A s) y i hxy.symm).elim
    · have hst := (A s).component_eq_of_vertex_eq (A t) hxy
      subst t
      have hij := (A s).vertex_injective hxy
      subst j
      rfl
    · exact (hab s i t j hxy).elim
    · exact (hac s i t j hxy).elim
    · exact (Spine.vertex_ne_reverse_arm (hne := h.2.1) hp (B s) y i hxy.symm).elim
    · exact (hab t j s i hxy.symm).elim
    · have hst := (B s).component_eq_of_vertex_eq (B t) hxy
      subst t
      have hij := (B s).vertex_injective hxy
      subst j
      rfl
    · exact (hbc s i t j hxy).elim
    · exact (hpc y s i hxy.symm).elim
    · exact (hac t j s i hxy.symm).elim
    · exact (hbc t j s i hxy.symm).elim
    · have hst : s = t := Subtype.ext ((C s).component_eq_of_vertex_eq (C t) hxy)
      subst t
      have hij := (C s).vertex_injective hxy
      subst j
      rfl
  · intro x
    rcases branch333_spine_and_arms_cover hG h hp hb x with hx | hx | hx | hx
    · obtain ⟨i, hi⟩ := Spine.vertex_surjective hp hx
      exact ⟨.inl i, hi⟩
    · obtain ⟨hxa, hxcomp⟩ := hx
      let s : ArmComponents G h.2.1 :=
        ⟨(deleteVertexGraph G a).connectedComponentMk ⟨x, hxa⟩, hxcomp⟩
      let z : s.val := ⟨⟨x, hxa⟩, (s.val.mem_supp_iff _).mpr rfl⟩
      obtain ⟨i, hi⟩ := (A s).vertex_surjective_component z
      exact ⟨.inr (.inl ⟨s, i⟩), hi⟩
    · obtain ⟨hxc, hxcomp⟩ := hx
      let s : ArmComponents G h.2.1.symm :=
        ⟨(deleteVertexGraph G c).connectedComponentMk ⟨x, hxc⟩, hxcomp⟩
      let z : s.val := ⟨⟨x, hxc⟩, (s.val.mem_supp_iff _).mpr rfl⟩
      obtain ⟨i, hi⟩ := (B s).vertex_surjective_component z
      exact ⟨.inr (.inr (.inl ⟨s, i⟩)), hi⟩
    · obtain ⟨⟨hxb, hxcompa⟩, ⟨_, hxcompc⟩⟩ := hx
      let s : CenterArmComponents333 G h.1.symm h.2.2.1 :=
        ⟨⟨(deleteVertexGraph G b).connectedComponentMk ⟨x, hxb⟩, hxcompa⟩, hxcompc⟩
      let z : s.val.val := ⟨⟨x, hxb⟩, (s.val.val.mem_supp_iff _).mpr rfl⟩
      obtain ⟨i, hi⟩ := (C s).vertex_surjective_component z
      exact ⟨.inr (.inr (.inr ⟨s, i⟩)), hi⟩

theorem center_adj_or_root333 {n : ℕ} {G : SimpleGraph (Fin n)}
    {a b c x y : Fin n} {hba : b ≠ a} {hbc : b ≠ c}
    (hx : InCenterArm333 G hba hbc x) (hxy : G.Adj x y) :
    y = b ∨ InCenterArm333 G hba hbc y := by
  rcases adjacent_inArm_or_root G hba hx.1 hxy with heq | hy
  · exact Or.inl heq
  rcases adjacent_inArm_or_root G hbc hx.2 hxy with heq | hy'
  · exact Or.inl heq
  exact Or.inr ⟨hy, hy'⟩

theorem endpoint_center_not_adj333 {n : ℕ} {G : SimpleGraph (Fin n)}
    (hG : G.Connected) {a b c : Fin n} (h : Branch333 G a b c)
    {p : G.Walk a c} (hp : p.IsPath) (hb : b ∈ p.support) {x y : Fin n}
    (hx : InArm G h.2.1 x) (hy : InCenterArm333 G h.1.symm h.2.2.1 y) :
    ¬ G.Adj x y := by
  intro hxy
  rcases adjacent_inArm_or_root G h.2.1 hx hxy with heq | hy'
  · exact inArm_ne_other hy.1 heq
  · exact endpoint_arm_not_center333 hG h hp hb hy' hy

theorem far_endpoint_center_not_adj333 {n : ℕ} {G : SimpleGraph (Fin n)}
    (hG : G.Connected) {a b c : Fin n} (h : Branch333 G a b c)
    {p : G.Walk a c} (hp : p.IsPath) (hb : b ∈ p.support) {x y : Fin n}
    (hx : InArm G h.2.1.symm x) (hy : InCenterArm333 G h.1.symm h.2.2.1 y) :
    ¬ G.Adj x y :=
  endpoint_center_not_adj333 hG h.reverse hp.reverse (by simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero] using hb) hx ⟨hy.2, hy.1⟩

theorem spine_center_adj_iff333 {n : ℕ} {G : SimpleGraph (Fin n)}
    (hG : G.IsTree) {a b c : Fin n} (h : Branch333 G a b c)
    {p : G.Walk a c} (hp : p.IsPath) (hb : b ∈ p.support)
    {s : CenterArmComponents333 G h.1.symm h.2.2.1} (P : ArmPath G h.1.symm s.val)
    (m : Fin (p.length + 1)) (hm : Spine.vertex hp m = b)
    (i : Fin (p.length + 1)) (j : Fin P.length) :
    G.Adj (Spine.vertex hp i) (P.vertex j) ↔ i.val = m.val ∧ j.val = 0 := by
  constructor
  · intro hadj
    have heq : Spine.vertex hp i = b := by
      rcases center_adj_or_root333 (center_arm_vertex_in_center333 h.1.symm h.2.2.1 P j)
          hadj.symm with heq | hcenter
      · exact heq
      · exact (center_arm_not_mem_spine333 h hp hb hcenter (Spine.vertex_mem hp i)).elim
    have hi := congrArg Fin.val (Spine.vertex_injective hp (heq.trans hm.symm))
    refine ⟨hi, ?_⟩
    rw [heq] at hadj
    exact (P.vertex_root_adj_iff hG.isAcyclic j).mp hadj
  · rintro ⟨hi, hj⟩
    have him : i = m := Fin.ext hi
    rw [him, hm]
    exact (P.vertex_root_adj_iff hG.isAcyclic j).mpr hj

def tripleArmModelAdj {A B C : Type*} (d m : ℕ) (a : A → ℕ)
    (b : B → ℕ) (c : C → ℕ) :
    TripleArmModelVertex d a b c → TripleArmModelVertex d a b c → Prop
  | .inl x, .inl y => x.val + 1 = y.val ∨ y.val + 1 = x.val
  | .inl x, .inr (.inl y) => x.val = 0 ∧ y.2.val = 0
  | .inr (.inl x), .inl y => y.val = 0 ∧ x.2.val = 0
  | .inl x, .inr (.inr (.inl y)) => x.val = d ∧ y.2.val = 0
  | .inr (.inr (.inl x)), .inl y => y.val = d ∧ x.2.val = 0
  | .inl x, .inr (.inr (.inr y)) => x.val = m ∧ y.2.val = 0
  | .inr (.inr (.inr x)), .inl y => y.val = m ∧ x.2.val = 0
  | .inr (.inl x), .inr (.inl y) =>
      x.1 = y.1 ∧ (x.2.val + 1 = y.2.val ∨ y.2.val + 1 = x.2.val)
  | .inr (.inr (.inl x)), .inr (.inr (.inl y)) =>
      x.1 = y.1 ∧ (x.2.val + 1 = y.2.val ∨ y.2.val + 1 = x.2.val)
  | .inr (.inr (.inr x)), .inr (.inr (.inr y)) =>
      x.1 = y.1 ∧ (x.2.val + 1 = y.2.val ∨ y.2.val + 1 = x.2.val)
  | _, _ => False

def tripleArmModel {A B C : Type*} (d m : ℕ) (a : A → ℕ)
    (b : B → ℕ) (c : C → ℕ) : SimpleGraph (TripleArmModelVertex d a b c) where
  Adj := tripleArmModelAdj d m a b c
  symm := ⟨by
    intro x y h
    rcases x with x | x | x | x <;> rcases y with y | y | y | y <;>
      simp only [tripleArmModelAdj] at h ⊢
    all_goals first | contradiction | simpa only [eq_comm, or_comm, and_comm] using h⟩
  loopless := ⟨by
    intro x
    rcases x with x | x | x | x <;> simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, tripleArmModelAdj]⟩

theorem tripleArmModelMap_adj_iff {n : ℕ} {G : SimpleGraph (Fin n)}
    (hG : G.IsTree) {a b c : Fin n} (h : Branch333 G a b c)
    {p : G.Walk a c} (hp : p.IsPath) (hb : b ∈ p.support)
    (m : Fin (p.length + 1)) (hm : Spine.vertex hp m = b)
    (A : (s : ArmComponents G h.2.1) → ArmPath G h.2.1 s)
    (B : (s : ArmComponents G h.2.1.symm) → ArmPath G h.2.1.symm s)
    (C : (s : CenterArmComponents333 G h.1.symm h.2.2.1) → ArmPath G h.1.symm s.val)
    (x y : TripleArmModelVertex p.length (fun s => (A s).length)
      (fun s => (B s).length) (fun s => (C s).length)) :
    G.Adj (tripleArmModelMap h hp A B C x) (tripleArmModelMap h hp A B C y) ↔
      (tripleArmModel p.length m.val (fun s => (A s).length)
        (fun s => (B s).length) (fun s => (C s).length)).Adj x y := by
  classical
  have hcenter (s) (i) := center_arm_vertex_in_center333 h.1.symm h.2.2.1 (C s) i
  rcases x with x | ⟨s, i⟩ | ⟨s, i⟩ | ⟨s, i⟩ <;>
    rcases y with y | ⟨t, j⟩ | ⟨t, j⟩ | ⟨t, j⟩ <;>
      dsimp [tripleArmModelMap, tripleArmModel, tripleArmModelAdj]
  · exact Spine.vertex_adj_iff hp hG.isAcyclic x y
  · exact Spine.vertex_arm_adj_iff hp hG.isAcyclic (A t) x j
  · exact Spine.vertex_reverse_arm_adj_iff (hne := h.2.1) hp hG.isAcyclic (B t) x j
  · exact spine_center_adj_iff333 hG h hp hb (C t) m hm x j
  · rw [G.adj_comm]
    exact Spine.vertex_arm_adj_iff hp hG.isAcyclic (A s) y i
  · by_cases hst : s = t
    · subst t; simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero] using (A s).vertex_adj_iff i j
    · have hn : ¬ G.Adj ((A s).vertex i) ((A t).vertex j) :=
        fun ha => hst ((A s).component_eq_of_adj (A t) ha)
      simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, hst, hn]
  · exact iff_false_intro (inArm_cross_not_adj hG.connected ((A s).vertex_inArm i) ((B t).vertex_inArm j))
  · exact iff_false_intro (endpoint_center_not_adj333 hG.connected h hp hb ((A s).vertex_inArm i) (hcenter t j))
  · rw [G.adj_comm]
    exact Spine.vertex_reverse_arm_adj_iff (hne := h.2.1) hp hG.isAcyclic (B s) y i
  · rw [G.adj_comm]
    exact iff_false_intro (inArm_cross_not_adj hG.connected ((A t).vertex_inArm j) ((B s).vertex_inArm i))
  · by_cases hst : s = t
    · subst t; simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero] using (B s).vertex_adj_iff i j
    · have hn : ¬ G.Adj ((B s).vertex i) ((B t).vertex j) :=
        fun ha => hst ((B s).component_eq_of_adj (B t) ha)
      simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, hst, hn]
  · exact iff_false_intro (far_endpoint_center_not_adj333 hG.connected h hp hb ((B s).vertex_inArm i) (hcenter t j))
  · rw [G.adj_comm]
    exact spine_center_adj_iff333 hG h hp hb (C s) m hm y i
  · rw [G.adj_comm]
    exact iff_false_intro (endpoint_center_not_adj333 hG.connected h hp hb ((A t).vertex_inArm j) (hcenter s i))
  · rw [G.adj_comm]
    exact iff_false_intro (far_endpoint_center_not_adj333 hG.connected h hp hb ((B t).vertex_inArm j) (hcenter s i))
  · by_cases hst : s = t
    · subst t; simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero] using (C s).vertex_adj_iff i j
    · have hn : ¬ G.Adj ((C s).vertex i) ((C t).vertex j) :=
        fun ha => hst (Subtype.ext ((C s).component_eq_of_adj (C t) ha))
      simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, hst, hn]

noncomputable def tripleArmModelIso {n : ℕ} {G : SimpleGraph (Fin n)}
    (hG : G.IsTree) {a b c : Fin n} (h : Branch333 G a b c)
    {p : G.Walk a c} (hp : p.IsPath) (hb : b ∈ p.support)
    (m : Fin (p.length + 1)) (hm : Spine.vertex hp m = b)
    (A : (s : ArmComponents G h.2.1) → ArmPath G h.2.1 s)
    (B : (s : ArmComponents G h.2.1.symm) → ArmPath G h.2.1.symm s)
    (C : (s : CenterArmComponents333 G h.1.symm h.2.2.1) → ArmPath G h.1.symm s.val) :
    tripleArmModel p.length m.val (fun s => (A s).length)
      (fun s => (B s).length) (fun s => (C s).length) ≃g G where
  toEquiv := Equiv.ofBijective (tripleArmModelMap h hp A B C)
    (tripleArmModelMap_bijective hG h hp hb A B C)
  map_rel_iff' := by
    intro x y
    exact tripleArmModelMap_adj_iff hG h hp hb m hm A B C x y

end Math15.Graceful


/- Supporting module: TripleReindex -/



namespace Math15.Graceful

noncomputable def tripleArmModelReindex {A B C A' B' C' : Type*} (d m : ℕ)
    (a : A → ℕ) (b : B → ℕ) (c : C → ℕ)
    (eA : A' ≃ A) (eB : B' ≃ B) (eC : C' ≃ C) :
    tripleArmModel d m (a ∘ eA) (b ∘ eB) (c ∘ eC) ≃g tripleArmModel d m a b c where
  toEquiv := Equiv.sumCongr (Equiv.refl _) <|
    Equiv.sumCongr (Equiv.sigmaCongrLeft (β := fun i => Fin (a i)) eA) <|
      Equiv.sumCongr (Equiv.sigmaCongrLeft (β := fun i => Fin (b i)) eB)
        (Equiv.sigmaCongrLeft (β := fun i => Fin (c i)) eC)
  map_rel_iff' := by
    intro x y
    rcases x with x | ⟨i, x⟩ | ⟨i, x⟩ | ⟨i, x⟩ <;>
      rcases y with y | ⟨j, y⟩ | ⟨j, y⟩ | ⟨j, y⟩ <;>
        simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, tripleArmModel, tripleArmModelAdj, Equiv.sigmaCongrLeft]

open Bounty

def tripleArmAOffset (d : ℕ) (a : Fin 2 → ℕ) : Fin 2 → ℕ :=
  ![d + 1, d + a 0 + 1]

def tripleArmBOffset (d : ℕ) (a b : Fin 2 → ℕ) (c : Fin 1 → ℕ) : Fin 2 → ℕ :=
  ![d + a 0 + a 1 + c 0 + 1, d + a 0 + a 1 + c 0 + b 0 + 1]

def tripleArmCOffset (d : ℕ) (a : Fin 2 → ℕ) : ℕ := d + a 0 + a 1 + 1

def tripleArmCode (d : ℕ) (a b : Fin 2 → ℕ) (c : Fin 1 → ℕ) :
    TripleArmModelVertex d a b c → ℕ
  | .inl i => i.val
  | .inr (.inl ⟨i, j⟩) => tripleArmAOffset d a i + j.val
  | .inr (.inr (.inl ⟨i, j⟩)) => tripleArmBOffset d a b c i + j.val
  | .inr (.inr (.inr ⟨_, j⟩)) => tripleArmCOffset d a + j.val

theorem tripleArmCode_lt (d e : ℕ) (a b : Fin 2 → ℕ) (c : Fin 1 → ℕ)
    (x : TripleArmModelVertex (d + e) a b c) :
    tripleArmCode (d + e) a b c x <
      tripleSpiderEdges (a 0) (a 1) (c 0) d e (b 0) (b 1) + 1 := by
  rcases x with x | ⟨i, x⟩ | ⟨i, x⟩ | ⟨i, x⟩
  · simp only [tripleArmCode, tripleSpiderEdges]; omega
  · fin_cases i <;> simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, tripleArmCode, tripleArmAOffset, tripleSpiderEdges] <;> omega
  · fin_cases i <;> simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, tripleArmCode, tripleArmBOffset, tripleSpiderEdges] <;> omega
  · fin_cases i
    simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, tripleArmCode, tripleArmCOffset, tripleSpiderEdges]
    omega

def tripleArmEncode (d e : ℕ) (a b : Fin 2 → ℕ) (c : Fin 1 → ℕ)
    (x : TripleArmModelVertex (d + e) a b c) :
    Fin (tripleSpiderEdges (a 0) (a 1) (c 0) d e (b 0) (b 1) + 1) :=
  ⟨tripleArmCode (d + e) a b c x, tripleArmCode_lt d e a b c x⟩

theorem tripleArmCode_injective (d : ℕ) (a b : Fin 2 → ℕ) (c : Fin 1 → ℕ) :
    Function.Injective (tripleArmCode d a b c) := by
  intro x y h
  rcases x with x | ⟨i, x⟩ | ⟨i, x⟩ | ⟨i, x⟩ <;>
    rcases y with y | ⟨j, y⟩ | ⟨j, y⟩ | ⟨j, y⟩
  · exact congrArg Sum.inl (Fin.ext h)
  all_goals try fin_cases i
  all_goals try fin_cases j
  all_goals simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, tripleArmCode, tripleArmAOffset, tripleArmBOffset, tripleArmCOffset] at h
  all_goals first | omega | (congr 4; exact Fin.ext (by omega))

theorem tripleArmEncode_bijective (d e : ℕ) (a b : Fin 2 → ℕ) (c : Fin 1 → ℕ) :
    Function.Bijective (tripleArmEncode d e a b c) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · intro x y h
    exact tripleArmCode_injective (d + e) a b c (congrArg Fin.val h)
  · rw [Fintype.card_fin]
    simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, TripleArmModelVertex, Fintype.card_sigma, Fin.sum_univ_succ, tripleSpiderEdges]
    omega

private theorem flat_TripleReindex_tripleArmEncode_adj_spine (d e : ℕ) (a b : Fin 2 → ℕ) (c : Fin 1 → ℕ)
    (hd : 0 < d) (he : 0 < e) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hc : ∀ i, 0 < c i)
    (x : Fin (d + e + 1)) (y : TripleArmModelVertex (d + e) a b c) :
    (tripleSpider (a 0) (a 1) (c 0) d e (b 0) (b 1)).Adj
      (tripleArmEncode d e a b c (.inl x)) (tripleArmEncode d e a b c y) ↔
      (tripleArmModel (d + e) d a b c).Adj (.inl x) y := by
  have ha0 := ha 0
  have ha1 := ha 1
  have hb0 := hb 0
  have hb1 := hb 1
  have hc0 := hc 0
  rcases y with y | ⟨j, y⟩ | ⟨j, y⟩ | ⟨j, y⟩
  all_goals try fin_cases j
  all_goals simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, tripleSpider, parentGraph, tripleArmEncode, tripleArmCode,
    tripleArmModel, tripleArmModelAdj, tripleSpiderParent,
    tripleArmAOffset, tripleArmBOffset, tripleArmCOffset]
  all_goals try simp only [Fin.ext_iff, Fin.val_zero]
  all_goals split_ifs <;> omega

private theorem flat_TripleReindex_tripleArmEncode_adj_a (d e : ℕ) (a b : Fin 2 → ℕ) (c : Fin 1 → ℕ)
    (hd : 0 < d) (he : 0 < e) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hc : ∀ i, 0 < c i)
    (i : Fin 2) (x : Fin (a i)) (y : TripleArmModelVertex (d + e) a b c) :
    (tripleSpider (a 0) (a 1) (c 0) d e (b 0) (b 1)).Adj
      (tripleArmEncode d e a b c (.inr (.inl ⟨i, x⟩))) (tripleArmEncode d e a b c y) ↔
      (tripleArmModel (d + e) d a b c).Adj (.inr (.inl ⟨i, x⟩)) y := by
  have ha0 := ha 0
  have ha1 := ha 1
  have hb0 := hb 0
  have hb1 := hb 1
  have hc0 := hc 0
  rcases y with y | ⟨j, y⟩ | ⟨j, y⟩ | ⟨j, y⟩
  all_goals try fin_cases i
  all_goals try fin_cases j
  all_goals simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, tripleSpider, parentGraph, tripleArmEncode, tripleArmCode,
    tripleArmModel, tripleArmModelAdj, tripleSpiderParent,
    tripleArmAOffset, tripleArmBOffset, tripleArmCOffset]
  all_goals try simp only [Fin.ext_iff, Fin.val_zero]
  all_goals split_ifs <;> omega

private theorem flat_TripleReindex_tripleArmEncode_adj_b (d e : ℕ) (a b : Fin 2 → ℕ) (c : Fin 1 → ℕ)
    (hd : 0 < d) (he : 0 < e) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hc : ∀ i, 0 < c i)
    (i : Fin 2) (x : Fin (b i)) (y : TripleArmModelVertex (d + e) a b c) :
    (tripleSpider (a 0) (a 1) (c 0) d e (b 0) (b 1)).Adj
      (tripleArmEncode d e a b c (.inr (.inr (.inl ⟨i, x⟩)))) (tripleArmEncode d e a b c y) ↔
      (tripleArmModel (d + e) d a b c).Adj (.inr (.inr (.inl ⟨i, x⟩))) y := by
  have ha0 := ha 0
  have ha1 := ha 1
  have hb0 := hb 0
  have hb1 := hb 1
  have hc0 := hc 0
  rcases y with y | ⟨j, y⟩ | ⟨j, y⟩ | ⟨j, y⟩
  all_goals try fin_cases i
  all_goals try fin_cases j
  all_goals simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, tripleSpider, parentGraph, tripleArmEncode, tripleArmCode,
    tripleArmModel, tripleArmModelAdj, tripleSpiderParent,
    tripleArmAOffset, tripleArmBOffset, tripleArmCOffset]
  all_goals split_ifs <;> omega

private theorem flat_TripleReindex_tripleArmEncode_adj_c (d e : ℕ) (a b : Fin 2 → ℕ) (c : Fin 1 → ℕ)
    (hd : 0 < d) (he : 0 < e) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hc : ∀ i, 0 < c i)
    (i : Fin 1) (x : Fin (c i)) (y : TripleArmModelVertex (d + e) a b c) :
    (tripleSpider (a 0) (a 1) (c 0) d e (b 0) (b 1)).Adj
      (tripleArmEncode d e a b c (.inr (.inr (.inr ⟨i, x⟩)))) (tripleArmEncode d e a b c y) ↔
      (tripleArmModel (d + e) d a b c).Adj (.inr (.inr (.inr ⟨i, x⟩))) y := by
  have ha0 := ha 0
  have ha1 := ha 1
  have hb0 := hb 0
  have hb1 := hb 1
  have hc0 := hc 0
  rcases y with y | ⟨j, y⟩ | ⟨j, y⟩ | ⟨j, y⟩
  all_goals try fin_cases i
  all_goals try fin_cases j
  all_goals simp [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero, tripleSpider, parentGraph, tripleArmEncode, tripleArmCode,
    tripleArmModel, tripleArmModelAdj, tripleSpiderParent,
    tripleArmAOffset, tripleArmBOffset, tripleArmCOffset]
  all_goals split_ifs <;> omega

theorem tripleArmEncode_adj_iff (d e : ℕ) (a b : Fin 2 → ℕ) (c : Fin 1 → ℕ)
    (hd : 0 < d) (he : 0 < e) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hc : ∀ i, 0 < c i)
    (x y : TripleArmModelVertex (d + e) a b c) :
    (tripleSpider (a 0) (a 1) (c 0) d e (b 0) (b 1)).Adj
      (tripleArmEncode d e a b c x) (tripleArmEncode d e a b c y) ↔
      (tripleArmModel (d + e) d a b c).Adj x y := by
  rcases x with x | ⟨i, x⟩ | ⟨i, x⟩ | ⟨i, x⟩
  · exact flat_TripleReindex_tripleArmEncode_adj_spine d e a b c hd he ha hb hc x y
  · exact flat_TripleReindex_tripleArmEncode_adj_a d e a b c hd he ha hb hc i x y
  · exact flat_TripleReindex_tripleArmEncode_adj_b d e a b c hd he ha hb hc i x y
  · exact flat_TripleReindex_tripleArmEncode_adj_c d e a b c hd he ha hb hc i x y

noncomputable def tripleArmIntervalsIso (d e : ℕ) (a b : Fin 2 → ℕ) (c : Fin 1 → ℕ)
    (hd : 0 < d) (he : 0 < e) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hc : ∀ i, 0 < c i) :
    tripleArmModel (d + e) d a b c ≃g tripleSpider (a 0) (a 1) (c 0) d e (b 0) (b 1) where
  toEquiv := Equiv.ofBijective (tripleArmEncode d e a b c) (tripleArmEncode_bijective d e a b c)
  map_rel_iff' := by
    intro x y
    exact tripleArmEncode_adj_iff d e a b c hd he ha hb hc x y

/-- Every tree in source11 is a seven-path triple spider with all seven
lengths positive, up to vertex names. -/
theorem branch333_exists_tripleSpider_iso {n : ℕ} (G : SimpleGraph (Fin n))
    (hG : G.IsTree) {u v w : Fin n} (hbranch : Branch333 G u v w) :
    ∃ a b c d e f g : ℕ,
      0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ 0 < e ∧ 0 < f ∧ 0 < g ∧
        Nonempty (tripleSpider a b c d e f g ≃g G) := by
  classical
  obtain ⟨u, v, w, h, p, hp, hv⟩ := hbranch.exists_ordered_spine hG
  obtain ⟨m, hm⟩ := Spine.vertex_surjective hp hv
  have hd : 0 < m.val := by
    by_contra hn
    have hm0 : m = 0 := by
      apply Fin.ext
      change m.val = 0
      omega
    rw [hm0, Spine.vertex_start] at hm
    exact h.1 hm
  have hmlt : m.val < p.length := by
    have hle : m.val ≤ p.length := by omega
    by_contra hn
    have hmeq : m = ⟨p.length, by omega⟩ := by
      apply Fin.ext
      change m.val = p.length
      omega
    rw [hmeq, Spine.vertex_end] at hm
    exact h.2.2.1 hm.symm
  have he : 0 < p.length - m.val := Nat.sub_pos_of_lt hmlt
  have hsum : m.val + (p.length - m.val) = p.length := by omega
  let A : (s : ArmComponents G h.2.1) → ArmPath G h.2.1 s :=
    chooseEndpointArmPath333 hG h hp hv
  let B : (s : ArmComponents G h.2.1.symm) → ArmPath G h.2.1.symm s :=
    chooseEndpointArmPath333 hG h.reverse hp.reverse (by simpa [Math15.Graceful.reverseLabel_at_cut, Math15.Graceful.normalizeHighLabel_at_cut, Math15.Graceful.shiftAboveCut_link, Bounty.extendSpiderLabel_at, Bounty.PathConstruction.bag_nil, Bounty.PathConstruction.bag_cons, Bounty.PathConstruction.bag_append, Bounty.PathConstruction.lowBag_succ, Bounty.PathConstruction.highBag_succ, Bounty.PathConstruction.rangeBag_succ, Bounty.PathConstruction.bag_reverse, Bounty.PathConstruction.edgeBag_reverse, Bounty.PathConstruction.opposite_reverse, Bounty.PathConstruction.alternates_reverse, Bounty.PathConstruction.symbolAt_zero] using hv)
  let C : (s : CenterArmComponents333 G h.1.symm h.2.2.1) → ArmPath G h.1.symm s.val :=
    chooseCenterArmPath333 hG h
  let : Fintype (deleteVertexGraph G u).ConnectedComponent := Fintype.ofFinite _
  let : Fintype (deleteVertexGraph G v).ConnectedComponent := Fintype.ofFinite _
  let : Fintype (deleteVertexGraph G w).ConnectedComponent := Fintype.ofFinite _
  let : Fintype (ArmComponents G h.2.1) := by unfold ArmComponents; infer_instance
  let : Fintype (ArmComponents G h.2.1.symm) := by unfold ArmComponents; infer_instance
  let : Fintype (ArmComponents G h.1.symm) := by unfold ArmComponents; infer_instance
  let : Fintype (CenterArmComponents333 G h.1.symm h.2.2.1) := by
    unfold CenterArmComponents333; infer_instance
  have hcardA : Fintype.card (ArmComponents G h.2.1) = 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact (endpoint_arm_components333_card hG h).1
  have hcardB : Fintype.card (ArmComponents G h.2.1.symm) = 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact (endpoint_arm_components333_card hG h).2
  have hcardC : Fintype.card (CenterArmComponents333 G h.1.symm h.2.2.1) = 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact center_arm_components333_card hG h hp hv
  let eA : Fin 2 ≃ ArmComponents G h.2.1 := (Fintype.equivFinOfCardEq hcardA).symm
  let eB : Fin 2 ≃ ArmComponents G h.2.1.symm := (Fintype.equivFinOfCardEq hcardB).symm
  let eC : Fin 1 ≃ CenterArmComponents333 G h.1.symm h.2.2.1 :=
    (Fintype.equivFinOfCardEq hcardC).symm
  let aa : Fin 2 → ℕ := fun i => (A (eA i)).length
  let bb : Fin 2 → ℕ := fun i => (B (eB i)).length
  let cc : Fin 1 → ℕ := fun i => (C (eC i)).length
  have ha : ∀ i, 0 < aa i := fun i => (A (eA i)).positive
  have hb : ∀ i, 0 < bb i := fun i => (B (eB i)).positive
  have hc : ∀ i, 0 < cc i := fun i => (C (eC i)).positive
  let er : tripleArmModel p.length m.val aa bb cc ≃g
      tripleArmModel p.length m.val (fun s => (A s).length)
        (fun s => (B s).length) (fun s => (C s).length) :=
    tripleArmModelReindex p.length m.val (fun s => (A s).length)
      (fun s => (B s).length) (fun s => (C s).length) eA eB eC
  let ef : tripleSpider (aa 0) (aa 1) (cc 0) m.val (p.length - m.val) (bb 0) (bb 1) ≃g G := by
    have ei := tripleArmIntervalsIso m.val (p.length - m.val) aa bb cc hd he ha hb hc
    rw [hsum] at ei
    exact ei.symm.trans (er.trans (tripleArmModelIso hG h hp hv m hm A B C))
  exact ⟨aa 0, aa 1, cc 0, m.val, p.length - m.val, bb 0, bb 1,
    ha 0, ha 1, hc 0, hd, he, hb 0, hb 1, ⟨ef⟩⟩

/-- The exact source11 target reduces to graceful labelings of the canonical
seven positive path lengths. -/
theorem target11_of_positive_tripleSpider
    (h : ∀ a b c d e f g : ℕ, 0 < a → 0 < b → 0 < c → 0 < d →
      0 < e → 0 < f → 0 < g → IsGraceful (tripleSpider a b c d e f g)) : Target11 := by
  intro n G hG hbranch
  obtain ⟨u, v, w, hbranch⟩ := hbranch
  obtain ⟨a, b, c, d, e, f, g, ha, hb, hc, hd, he, hf, hg, ⟨iso⟩⟩ :=
    branch333_exists_tripleSpider_iso G hG hbranch
  exact isGraceful_of_iso iso.symm (h a b c d e f g ha hb hc hd he hf hg)

end Math15.Graceful


/- Supporting module: ForkTripleReduction -/



namespace Bounty
open Math15.Graceful

/-- Peel off one nonexceptional alpha-labeled pair of arms and glue it to the
ordinary graceful fork on the other side, extended along the remaining stem. -/
theorem tripleSpider_of_right_rootedFork {a b c d e f g : ℕ}
    (ha : 0<a) (hb : 0<b) (hc : 0<c) (hd : 0<d) (he : 0<e) (hf : 0<f) (hg : 0<g)
    (hpair : a≠2 ∨ b≠2) (hfork : RootedFork f g e c) :
    IsGraceful (tripleSpider a b c d e f g) := by
  obtain ⟨p,k,hp,hpin⟩ := rosa_zero_alpha_path a b ha hb hpair
  obtain ⟨q,hq,hqpin⟩ := hfork.extendStem d
  have hptree : (parentGraph (a+b) Nat.pred).IsTree :=
    parentGraph_isTree _ _ (fun j hj _ => by simp only [Nat.pred_eq_sub_one]; omega)
  have hlink : forkTriplePair a b c d e f g ⟨a,by omega⟩=
      forkTripleMap a b c d e f g (forkTripleStemTip f g e c d) := (forkTripleMap_tip hd).symm
  have hcover : ∀ v, (∃ i, forkTriplePair a b c d e f g i=v) ∨
      (∃ j, forkTripleMap a b c d e f g j=v) := fun v => (forkTripleMap_cover a b c d e f g v).symm
  have hoverlap : ∀ i j, forkTriplePair a b c d e f g i=forkTripleMap a b c d e f g j ↔
      i=⟨a,by omega⟩ ∧ j=forkTripleStemTip f g e c d := by
    intro i j
    rw [eq_comm,forkTripleMap_overlap hd,and_comm]
  have hedges := tree_union_edges (tripleSpider a b c d e f g) (parentGraph (a+b) Nat.pred)
    (forkTripleStem f g e c d) (forkTriplePair a b c d e f g) (forkTripleMap a b c d e f g)
    (forkTriplePair_injective a b c d e f g) (forkTripleMap_injective a b c d e f g)
    (tripleSpider_isTree _ _ _ _ _ _ _) hptree.connected (forkTripleStem_isTree f g e c d).connected
    ⟨a,by omega⟩ (forkTripleStemTip f g e c d) hlink hcover
    (forkTriplePair_hom ha hb hd he) (forkTripleMap_hom ha hb hc hd he hf hg)
  apply isGraceful_amalgamation (tripleSpider a b c d e f g) (parentGraph (a+b) Nat.pred)
    (forkTripleStem f g e c d) (forkTriplePair a b c d e f g) (forkTripleMap a b c d e f g)
    (forkTriplePair_injective a b c d e f g) (forkTripleMap_injective a b c d e f g)
    ⟨a,by omega⟩ (forkTripleStemTip f g e c d) hoverlap hcover hedges ?_
    (fun i => p i.val) q k hp.toParent hq (Or.inl hpin) hqpin
  rw [tripleSpider_edgeCount,forkTripleStem_edgeCount,
    parentGraph_edgeCount (a+b) Nat.pred (fun j hj _ => by simp only [Nat.pred_eq_sub_one]; omega)]
  unfold tripleSpiderEdges forkTripleSize
  omega

/-- The symmetric peeling choice uses the fork on the left side. -/
theorem tripleSpider_of_left_rootedFork {a b c d e f g : ℕ}
    (ha : 0<a) (hb : 0<b) (hc : 0<c) (hd : 0<d) (he : 0<e) (hf : 0<f) (hg : 0<g)
    (hpair : f≠2 ∨ g≠2) (hfork : RootedFork a b d c) :
    IsGraceful (tripleSpider a b c d e f g) := by
  exact isGraceful_of_iso (forkTripleSwapIso ha hb hc hd he hf hg)
    (tripleSpider_of_right_rootedFork hf hg hc he hd ha hb hpair hfork)

/-- All positive canonical models follow from the precise rooted-fork statement.
The exceptional fork on both sides gives the already certified finite tree. -/
theorem positive_tripleSpider_of_rootedFork
    (H : ∀ a b d c : ℕ, 0<a → 0<b → 0<d → 0<c →
      ¬(a=1 ∧ b=1 ∧ d=1 ∧ c=2) → RootedFork a b d c)
    (a b c d e f g : ℕ)
    (ha : 0<a) (hb : 0<b) (hc : 0<c) (hd : 0<d) (he : 0<e) (hf : 0<f) (hg : 0<g) :
    IsGraceful (tripleSpider a b c d e f g) := by
  by_cases hleft22 : a=2 ∧ b=2
  · by_cases hright22 : f=2 ∧ g=2
    · obtain ⟨rfl,rfl⟩ := hleft22
      obtain ⟨rfl,rfl⟩ := hright22
      exact tripleSpider_twos_graceful hc hd he
    · apply tripleSpider_of_left_rootedFork ha hb hc hd he hf hg (by tauto)
      exact H a b d c ha hb hd hc (by omega)
  · by_cases hrightEx : f=1 ∧ g=1 ∧ e=1 ∧ c=2
    · by_cases hleftEx : a=1 ∧ b=1 ∧ d=1 ∧ c=2
      · obtain ⟨rfl,rfl,rfl,rfl⟩ := hleftEx
        obtain ⟨rfl,rfl,rfl,_⟩ := hrightEx
        exact exception_1_2_graceful
      · apply tripleSpider_of_left_rootedFork ha hb hc hd he hf hg (by omega)
        exact H a b d c ha hb hd hc hleftEx
    · apply tripleSpider_of_right_rootedFork ha hb hc hd he hf hg (by tauto)
      exact H f g e c hf hg he hc hrightEx

/-- Exact source11 reduction. This theorem is conditional on the remaining
rooted-fork theorem; it does not assert that theorem as an axiom. -/
theorem target11_of_rootedFork
    (H : ∀ a b d c : ℕ, 0<a → 0<b → 0<d → 0<c →
      ¬(a=1 ∧ b=1 ∧ d=1 ∧ c=2) → RootedFork a b d c) : Target11 :=
  target11_of_positive_tripleSpider (positive_tripleSpider_of_rootedFork H)

end Bounty


/- Supporting module: Source11Theorem -/




namespace Bounty

/-- Every finite tree with exactly three vertices of degree three and no other
vertices of degree above two admits a graceful labeling. -/
theorem target11_proved : Math15.Graceful.Target11 :=
  target11_of_rootedFork rootedFork_all

/-- The exact catalog target, without additional hypotheses. -/
theorem target : fcTypeOfName% "Math15Catalog.source11" := target11_proved

end Bounty

namespace Bounty
