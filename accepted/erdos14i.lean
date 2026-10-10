/- Erdős problem 14, part I: formalized submission.
   The task supplies the imports and the enclosing Bounty namespace. -/

/- Core -/
open Finset
open scoped BigOperators

namespace Erdos14Verification

def pairs (s : Finset ℕ) (n : ℕ) : Finset (ℕ × ℕ) :=
  (s ×ˢ s).filter (fun p => p.1 + p.2 = n)

def diagonal (s : Finset ℕ) (n : ℕ) : Finset ℕ :=
  s.filter (fun b => b + b = n)

def weightedPairs (s : Finset ℕ) (n : ℕ) : Finset (ℕ × ℕ) :=
  (s ×ˢ s).filter (fun p => p.1 + 2 * p.2 = n)

def triples (s : Finset ℕ) (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (s ×ˢ (s ×ˢ s)).filter (fun p => p.1 + p.2.1 + p.2.2 = n)

def Unique (s : Finset ℕ) (n : ℕ) : Prop :=
  ∃ b ∈ s, ∃ c ∈ s, b + c = n ∧ pairs s n = {(b,c), (c,b)}

lemma mem_pairs {s : Finset ℕ} {n a b : ℕ} :
    (a,b) ∈ pairs s n ↔ a ∈ s ∧ b ∈ s ∧ a+b=n := by
  simp [pairs, and_assoc]

lemma mem_weightedPairs {s : Finset ℕ} {n a b : ℕ} :
    (a,b) ∈ weightedPairs s n ↔ a ∈ s ∧ b ∈ s ∧ a+2*b=n := by
  simp [weightedPairs, and_assoc]

lemma mem_triples {s : Finset ℕ} {n a b c : ℕ} :
    (a,b,c) ∈ triples s n ↔ a ∈ s ∧ b ∈ s ∧ c ∈ s ∧ a+b+c=n := by
  simp [triples, and_assoc]

lemma unique_iff_unordered (s : Finset ℕ) (n : ℕ) :
    Unique s n ↔ ∃ b ∈ s, ∃ c ∈ s, b+c=n ∧
      ∀ u ∈ s, ∀ v ∈ s, u+v=n → (u=b ∧ v=c) ∨ (u=c ∧ v=b) := by
  constructor
  · rintro ⟨b,hb,c,hc,hs,hp⟩
    refine ⟨b,hb,c,hc,hs,?_⟩
    intro u hu v hv huv
    have hmem : (u,v) ∈ pairs s n := by simp [mem_pairs,hu,hv,huv]
    rw [hp] at hmem
    simpa only [mem_insert, mem_singleton, Prod.mk.injEq] using hmem
  · rintro ⟨b,hb,c,hc,hs,hu⟩
    refine ⟨b,hb,c,hc,hs,?_⟩
    ext ⟨u,v⟩
    simp only [mem_pairs, mem_insert, mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨hus,hvs,hsum⟩
      exact hu u hus v hvs hsum
    · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
      · exact ⟨hb,hc,hs⟩
      · exact ⟨hc,hb,by omega⟩

lemma pairs_card_le (s : Finset ℕ) (n : ℕ) :
    (pairs s n).card ≤ s.card := by
  apply Finset.card_le_card_of_injOn (fun p : ℕ × ℕ => p.1)
  · intro p hp
    exact (Finset.mem_filter.mp hp).1 |> Finset.mem_product.mp |> And.left
  · intro p hp q hq heq
    change p.1 = q.1 at heq
    have hp' := (Finset.mem_filter.mp hp).2
    have hq' := (Finset.mem_filter.mp hq).2
    apply Prod.ext heq
    omega

lemma unique_pairs_card_add_diagonal (s : Finset ℕ) (n : ℕ)
    (h : Unique s n) : (pairs s n).card + (diagonal s n).card = 2 := by
  obtain ⟨b,hb,c,hc,hs,hp⟩ := h
  by_cases hbc : b=c
  · subst c
    have hd : diagonal s n = {b} := by
      ext a
      simp only [diagonal, mem_filter, mem_singleton]
      constructor
      · rintro ⟨ha,he⟩
        omega
      · intro he
        subst a
        exact ⟨hb,hs⟩
    simp [hp,hd]
  · have hd : diagonal s n = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro a ha
      obtain ⟨has,hasum⟩ := Finset.mem_filter.mp ha
      have hpair : (a,a) ∈ pairs s n := by simp [mem_pairs,has,hasum]
      rw [hp] at hpair
      simp only [mem_insert, mem_singleton, Prod.mk.injEq] at hpair
      rcases hpair with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> omega
    simp [hp,hd,Prod.ext_iff,hbc]

lemma sum_triples_first (s : Finset ℕ) (n : ℕ) (f : ℕ → ℕ)
    (hs : ∀ a ∈ s, a ≤ n) :
    (∑ t ∈ triples s n, f t.1) = ∑ a ∈ s, f a * (pairs s (n-a)).card := by
  simp only [triples, Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro a ha
  rw [pairs, Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]
  simp only [Finset.mul_sum, mul_ite, mul_one, mul_zero]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro c hc
  have he : a+b+c=n ↔ b+c=n-a := by have := hs a ha; omega
  simp [he]

lemma sum_weighted_first (s : Finset ℕ) (n : ℕ) (f : ℕ → ℕ)
    (hs : ∀ a ∈ s, a ≤ n) :
    (∑ t ∈ weightedPairs s n, f t.1) = ∑ a ∈ s, f a * (diagonal s (n-a)).card := by
  simp only [weightedPairs, Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro a ha
  rw [diagonal, Finset.card_eq_sum_ones, Finset.sum_filter]
  simp only [Finset.mul_sum, mul_ite, mul_one, mul_zero]
  apply Finset.sum_congr rfl
  intro b hb
  have he : a+2*b=n ↔ b+b=n-a := by have := hs a ha; omega
  simp [he]

lemma clean_sum_identity (s : Finset ℕ) (n : ℕ) (f : ℕ → ℕ)
    (hs : ∀ a ∈ s, a ≤ n) (hu : ∀ a ∈ s, Unique s (n-a)) :
    (∑ t ∈ triples s n, f t.1) + (∑ p ∈ weightedPairs s n, f p.1)
      = 2 * ∑ a ∈ s, f a := by
  rw [sum_triples_first s n f hs, sum_weighted_first s n f hs,
    ← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  have hd := unique_pairs_card_add_diagonal s (n-a) (hu a ha)
  nlinarith

private def swap12 (p : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ := (p.2.1,p.1,p.2.2)
private def swap13 (p : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ := (p.2.2,p.2.1,p.1)

private lemma swap12_mem (s : Finset ℕ) (n : ℕ) (p : ℕ × ℕ × ℕ) :
    swap12 p ∈ triples s n ↔ p ∈ triples s n := by
  rcases p with ⟨a,b,c⟩
  simp only [swap12, mem_triples]
  constructor
  · rintro ⟨hb,ha,hc,he⟩
    exact ⟨ha,hb,hc,by omega⟩
  · rintro ⟨ha,hb,hc,he⟩
    exact ⟨hb,ha,hc,by omega⟩

private lemma swap13_mem (s : Finset ℕ) (n : ℕ) (p : ℕ × ℕ × ℕ) :
    swap13 p ∈ triples s n ↔ p ∈ triples s n := by
  rcases p with ⟨a,b,c⟩
  simp only [swap13, mem_triples]
  constructor
  · rintro ⟨hc,hb,ha,he⟩
    exact ⟨ha,hb,hc,by omega⟩
  · rintro ⟨ha,hb,hc,he⟩
    exact ⟨hc,hb,ha,by omega⟩

lemma triple_coordinate_sums (s : Finset ℕ) (n : ℕ) :
    (∑ t ∈ triples s n, t.1) = (∑ t ∈ triples s n, t.2.1) ∧
    (∑ t ∈ triples s n, t.1) = (∑ t ∈ triples s n, t.2.2) := by
  constructor
  · apply Finset.sum_nbij' swap12 swap12
    · intro p hp; exact (swap12_mem s n p).mpr hp
    · intro p hp; exact (swap12_mem s n p).mpr hp
    · intro p hp; rfl
    · intro p hp; rfl
    · intro p hp; rfl
  · apply Finset.sum_nbij' swap13 swap13
    · intro p hp; exact (swap13_mem s n p).mpr hp
    · intro p hp; exact (swap13_mem s n p).mpr hp
    · intro p hp; rfl
    · intro p hp; rfl
    · intro p hp; rfl

lemma triple_first_moment (s : Finset ℕ) (n : ℕ) :
    3 * (∑ t ∈ triples s n, t.1) = n * (triples s n).card := by
  obtain ⟨h2,h3⟩ := triple_coordinate_sums s n
  have htotal : (∑ t ∈ triples s n, (t.1+t.2.1+t.2.2))
      = n * (triples s n).card := by
    calc
      _ = ∑ _t ∈ triples s n, n := by
        apply Finset.sum_congr rfl
        intro t ht
        exact (Finset.mem_filter.mp ht).2
      _ = _ := by simp [Nat.mul_comm]
  simp only [Finset.sum_add_distrib] at htotal
  omega

lemma weighted_first_moment (s : Finset ℕ) (n : ℕ) :
    (∑ p ∈ weightedPairs s n, p.1) + 2*(∑ p ∈ weightedPairs s n, p.2)
      = n * (weightedPairs s n).card := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  calc
    _ = ∑ _p ∈ weightedPairs s n, n := by
      apply Finset.sum_congr rfl
      intro p hp
      exact (Finset.mem_filter.mp hp).2
    _ = _ := by simp [Nat.mul_comm]

/-- The central triple-moment identity, including all diagonal cases. -/
theorem clean_triple_moment (s : Finset ℕ) (n : ℕ)
    (hs : ∀ a ∈ s, a ≤ n) (hu : ∀ a ∈ s, Unique s (n-a)) :
    3*(∑ a ∈ s, a) + 3*(∑ p ∈ weightedPairs s n, p.2)
      = n*(s.card + (weightedPairs s n).card) := by
  have hcount := clean_sum_identity s n (fun _ => 1) hs hu
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at hcount
  have hfirst := clean_sum_identity s n id hs hu
  have hsym := triple_first_moment s n
  have hweighted := weighted_first_moment s n
  dsimp only [id] at hfirst
  nlinarith

end Erdos14Verification

/- Counting -/
open Finset
open scoped BigOperators

namespace Erdos14Verification

lemma unique_pairs_card_le_two (s : Finset ℕ) (n : ℕ)
    (h : Unique s n) : (pairs s n).card ≤ 2 := by
  have := unique_pairs_card_add_diagonal s n h
  omega

/-- Pair counting with an arbitrary set of possible sums and an arbitrary
exceptional set. The exceptional set is not redefined for a subset. -/
theorem pair_count_bound (s e targets : Finset ℕ)
    (hcover : ∀ a ∈ s, ∀ b ∈ s, a+b ∈ targets)
    (hgood : ∀ n ∈ targets, n ∉ e → (pairs s n).card ≤ 2) :
    s.card * s.card ≤ 2 * targets.card + e.card * s.card := by
  have hfiber : s.card * s.card = ∑ n ∈ targets, (pairs s n).card := by
    have hm : ((s ×ˢ s : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)).MapsTo
        (fun p => p.1+p.2) targets := by
      intro p hp
      obtain ⟨ha,hb⟩ := Finset.mem_product.mp hp
      exact hcover p.1 ha p.2 hb
    simpa only [Finset.card_product, pairs] using
      (Finset.card_eq_sum_card_fiberwise hm)
  rw [hfiber]
  calc
    _ ≤ ∑ n ∈ targets, (2 + if n ∈ e then s.card else 0) := by
      apply Finset.sum_le_sum
      intro n hn
      by_cases he : n ∈ e
      · simp only [he, if_true]
        have := pairs_card_le s n
        omega
      · simp only [he, if_false, add_zero]
        exact hgood n hn he
    _ = 2 * targets.card + (targets.filter (fun n => n ∈ e)).card * s.card := by
      rw [Finset.sum_add_distrib, ← Finset.sum_filter]
      simp [Nat.mul_comm]
    _ ≤ _ := by
      have hc : (targets.filter (fun n => n ∈ e)).card ≤ e.card := by
        apply Finset.card_le_card
        intro n hn
        exact (Finset.mem_filter.mp hn).2
      nlinarith

theorem interval_pair_count (s e : Finset ℕ) (X : ℕ)
    (hs : ∀ a ∈ s, a ≤ X)
    (hgood : ∀ n ≤ 2*X, n ∉ e → (pairs s n).card ≤ 2) :
    s.card * s.card ≤ 4*X+2 + e.card * s.card := by
  have h := pair_count_bound s e (Finset.range (2*X+1))
    (by intro a ha b hb; simp only [Finset.mem_range];
        have := hs a ha; have := hs b hb; omega)
    (by intro n hn he; exact hgood n (by simpa using hn) he)
  simp only [Finset.card_range] at h
  omega

/-- The progression bound needed by the argument, with ordered pair counts. -/
theorem progression_pair_count (s e : Finset ℕ) (X p r : ℕ)
    (hs : ∀ a ∈ s, a ≤ X)
    (hres : ∀ a ∈ s, a % p = r)
    (hgood : ∀ n, n ∉ e → (pairs s n).card ≤ 2) :
    s.card * s.card ≤ 4*(X/p)+2 + e.card * s.card := by
  let targets := (Finset.range (2*(X/p)+1)).image (fun q => p*q+2*r)
  have hcover : ∀ a ∈ s, ∀ b ∈ s, a+b ∈ targets := by
    intro a ha b hb
    apply Finset.mem_image.mpr
    refine ⟨a/p+b/p, ?_, ?_⟩
    · simp only [Finset.mem_range]
      have h1 : a/p ≤ X/p := Nat.div_le_div_right (hs a ha)
      have h2 : b/p ≤ X/p := Nat.div_le_div_right (hs b hb)
      omega
    · have h1 := Nat.mod_add_div a p
      have h2 := Nat.mod_add_div b p
      rw [hres a ha] at h1
      rw [hres b hb] at h2
      nlinarith
  have hc : targets.card ≤ 2*(X/p)+1 := by
    exact (Finset.card_image_le).trans_eq (Finset.card_range _)
  have h := pair_count_bound s e targets hcover (fun n _ he => hgood n he)
  nlinarith

/-- Subsets inherit the upper bound away from the original exceptions. -/
lemma pairs_mono {s t : Finset ℕ} (h : t ⊆ s) (n : ℕ) :
    pairs t n ⊆ pairs s n := by
  intro ⟨a,b⟩ hp
  obtain ⟨ha,hb,hn⟩ := mem_pairs.mp hp
  exact mem_pairs.mpr ⟨h ha, h hb, hn⟩

end Erdos14Verification

/- Structure -/
open Finset
open scoped BigOperators

namespace Erdos14Verification

lemma clean_zero_moment (s : Finset ℕ) (n : ℕ)
    (hs : ∀ a ∈ s, a ≤ n) (hu : ∀ a ∈ s, Unique s (n-a))
    (hg : (weightedPairs s n).card = 0) :
    3*(∑ a ∈ s, a) = n*s.card := by
  have he := Finset.card_eq_zero.mp hg
  simpa only [he, Finset.sum_empty, mul_zero, add_zero, Finset.card_empty]
    using clean_triple_moment s n hs hu

lemma clean_one_moment (s : Finset ℕ) (n : ℕ)
    (hs : ∀ a ∈ s, a ≤ n) (hu : ∀ a ∈ s, Unique s (n-a))
    (hg : (weightedPairs s n).card = 1) :
    ∃ b ∈ s, 3*(∑ a ∈ s, a) + 3*b = n*(s.card+1) := by
  obtain ⟨p,hp⟩ := Finset.card_eq_one.mp hg
  have hm : p ∈ weightedPairs s n := by rw [hp]; simp
  have hb : p.2 ∈ s := (Finset.mem_product.mp (Finset.mem_filter.mp hm).1).2
  refine ⟨p.2,hb,?_⟩
  simpa only [hp, Finset.sum_singleton, Finset.card_singleton]
    using clean_triple_moment s n hs hu

lemma clean_zero_target_unique (s : Finset ℕ) (n₁ n₂ : ℕ)
    (hne : s.Nonempty)
    (h₁ : 3*(∑ a ∈ s, a) = n₁*s.card)
    (h₂ : 3*(∑ a ∈ s, a) = n₂*s.card) : n₁=n₂ := by
  have hpos := Finset.card_pos.mpr hne
  nlinarith

lemma one_target_injective (H q n₁ n₂ b₁ b₂ : ℕ) (hq : 0<q)
    (h₁ : 3*H+3*b₁=n₁*q) (h₂ : 3*H+3*b₂=n₂*q)
    (hb : b₁=b₂) : n₁=n₂ := by
  nlinarith

/-- Multiplying the repeated summands by three avoids a divisibility case split. -/
lemma one_target_congruence (H q n₁ n₂ b₁ b₂ : ℕ)
    (h₁ : 3*H+3*b₁=n₁*q) (h₂ : 3*H+3*b₂=n₂*q) :
    (3*b₁) % q = (3*b₂) % q := by
  have he : Nat.ModEq q (3*H+3*b₁) (3*H+3*b₂) := by
    rw [h₁,h₂]
    simp only [Nat.ModEq, Nat.mul_mod_left]
  exact Nat.ModEq.add_left_cancel' (3*H) he

def dilate (c : ℕ) (s : Finset ℕ) : Finset ℕ := s.image (fun a => c*a)

lemma card_dilate (c : ℕ) (hc : 0<c) (s : Finset ℕ) :
    (dilate c s).card = s.card := by
  apply Finset.card_image_of_injective
  intro a b h
  nlinarith

lemma pairs_dilate (c : ℕ) (hc : 0<c) (s : Finset ℕ) (n : ℕ) :
    pairs (dilate c s) (c*n) =
      (pairs s n).image (fun p => (c*p.1,c*p.2)) := by
  ext ⟨u,v⟩
  simp only [mem_pairs, dilate, Finset.mem_image]
  constructor
  · rintro ⟨⟨a,ha,hau⟩,⟨b,hb,hbv⟩,he⟩
    refine ⟨(a,b), ?_, ?_⟩
    · exact mem_pairs.mpr ⟨ha,hb,by nlinarith⟩
    · exact Prod.ext hau hbv
  · rintro ⟨⟨a,b⟩,hp,he⟩
    obtain ⟨ha,hb,hn⟩ := mem_pairs.mp hp
    have hau : c*a=u := congrArg Prod.fst he
    have hbv : c*b=v := congrArg Prod.snd he
    refine ⟨⟨a,ha,hau⟩,⟨b,hb,hbv⟩,?_⟩
    nlinarith

lemma card_pairs_dilate (c : ℕ) (hc : 0<c) (s : Finset ℕ) (n : ℕ) :
    (pairs (dilate c s) (c*n)).card = (pairs s n).card := by
  rw [pairs_dilate c hc s n]
  apply Finset.card_image_of_injective
  intro p q he
  apply Prod.ext
  · have h := congrArg Prod.fst he
    dsimp at h
    nlinarith
  · have h := congrArg Prod.snd he
    dsimp at h
    nlinarith

lemma dilate_good (c : ℕ) (hc : 0<c) (s e : Finset ℕ)
    (hgood : ∀ n, n ∉ e → (pairs s n).card ≤ 2) :
    ∀ n, n ∉ dilate c e → (pairs (dilate c s) n).card ≤ 2 := by
  intro n hn
  by_cases he : pairs (dilate c s) n = ∅
  · simp [he]
  · obtain ⟨⟨u,v⟩,hp⟩ := Finset.nonempty_iff_ne_empty.mpr he
    obtain ⟨hu,hv,huv⟩ := mem_pairs.mp hp
    obtain ⟨a,ha,hau⟩ := Finset.mem_image.mp hu
    obtain ⟨b,hb,hbv⟩ := Finset.mem_image.mp hv
    have hsum : c*(a+b)=n := by nlinarith
    have hne : a+b ∉ e := by
      intro hab
      apply hn
      exact Finset.mem_image.mpr ⟨a+b,hab,hsum⟩
    rw [← hsum,card_pairs_dilate c hc s (a+b)]
    exact hgood (a+b) hne

/-- Counts all targets in a fixed-prefix class with a single weighted pair.
The repeated summand may equal the other summand; no singleton exception is needed. -/
theorem linear_targets_pair_bound (s e u : Finset ℕ) (b : ℕ → ℕ)
    (X H q : ℕ) (hq : 0<q)
    (hs : ∀ a ∈ s, a ≤ X)
    (hgood : ∀ n, n ∉ e → (pairs s n).card ≤ 2)
    (hb : ∀ n ∈ u, b n ∈ s)
    (hmoment : ∀ n ∈ u, 3*H+3*b n=n*q) :
    u.card*u.card ≤ 4*((3*X)/q)+2+e.card*u.card := by
  by_cases he : u = ∅
  · simp [he]
  obtain ⟨n₀,hn₀⟩ := Finset.nonempty_iff_ne_empty.mpr he
  let t := u.image b
  have ht : t ⊆ s := by
    intro a ha
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp ha
    exact hb n hn
  have hcard : t.card = u.card := by
    apply Finset.card_image_of_injOn
    intro n₁ hn₁ n₂ hn₂ heq
    exact one_target_injective H q n₁ n₂ (b n₁) (b n₂) hq
      (hmoment n₁ hn₁) (hmoment n₂ hn₂) heq
  have htgood : ∀ n, n ∉ e → (pairs t n).card ≤ 2 := by
    intro n hn
    exact (Finset.card_le_card (pairs_mono ht n)).trans (hgood n hn)
  have hbound : ∀ a ∈ dilate 3 t, a ≤ 3*X := by
    intro a ha
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp ha
    have := hs v (ht hv)
    omega
  have hres : ∀ a ∈ dilate 3 t, a % q = (3*b n₀) % q := by
    intro a ha
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hv
    exact one_target_congruence H q n n₀ (b n) (b n₀)
      (hmoment n hn) (hmoment n₀ hn₀)
  have h := progression_pair_count (dilate 3 t) (dilate 3 e)
    (3*X) q ((3*b n₀)%q) hbound hres (dilate_good 3 (by decide) t e htgood)
  simpa only [card_dilate 3 (by decide), hcard] using h

end Erdos14Verification

/- Prefix -/
open Finset
open scoped BigOperators

namespace Erdos14Verification

def initial (s : Finset ℕ) (n : ℕ) : Finset ℕ := s.filter (fun a => a ≤ n)

lemma mem_prefix {s : Finset ℕ} {n a : ℕ} :
    a ∈ initial s n ↔ a ∈ s ∧ a ≤ n := by simp [initial]

lemma prefix_subset (s : Finset ℕ) (n : ℕ) : initial s n ⊆ s := by
  intro a ha; exact (mem_prefix.mp ha).1

lemma prefix_mono (s : Finset ℕ) {n m : ℕ} (h : n ≤ m) :
    initial s n ⊆ initial s m := by
  intro a ha
  obtain ⟨has,han⟩ := mem_prefix.mp ha
  exact mem_prefix.mpr ⟨has,han.trans h⟩

lemma prefix_eq_of_card_eq (s : Finset ℕ) (n m : ℕ)
    (h : (initial s n).card = (initial s m).card) : initial s n = initial s m := by
  rcases le_total n m with hnm | hmn
  · exact Finset.eq_of_subset_of_card_le (prefix_mono s hnm) h.ge
  · exact (Finset.eq_of_subset_of_card_le (prefix_mono s hmn) h.le).symm

lemma pairs_prefix (s : Finset ℕ) (n m : ℕ) (h : m ≤ n) :
    pairs (initial s n) m = pairs s m := by
  ext ⟨a,b⟩
  simp only [mem_pairs,mem_prefix]
  constructor
  · rintro ⟨⟨ha,_⟩,⟨hb,_⟩,he⟩; exact ⟨ha,hb,he⟩
  · rintro ⟨ha,hb,he⟩; exact ⟨⟨ha,by omega⟩,⟨hb,by omega⟩,he⟩

lemma weightedPairs_prefix (s : Finset ℕ) (n : ℕ) :
    weightedPairs (initial s n) n = weightedPairs s n := by
  ext ⟨a,b⟩
  simp only [mem_weightedPairs,mem_prefix]
  constructor
  · rintro ⟨⟨ha,_⟩,⟨hb,_⟩,he⟩; exact ⟨ha,hb,he⟩
  · rintro ⟨ha,hb,he⟩; exact ⟨⟨ha,by omega⟩,⟨hb,by omega⟩,he⟩

lemma unique_prefix (s : Finset ℕ) (n m : ℕ) (hm : m ≤ n)
    (h : Unique s m) : Unique (initial s n) m := by
  obtain ⟨a,ha,b,hb,hab,hpairs⟩ := h
  refine ⟨a,mem_prefix.mpr ⟨ha,by omega⟩,
    b,mem_prefix.mpr ⟨hb,by omega⟩,hab,?_⟩
  rwa [pairs_prefix s n m hm]

def dirty (s e : Finset ℕ) : Finset ℕ :=
  (s ×ˢ e).image (fun p => p.1+p.2)

lemma dirty_card_le (s e : Finset ℕ) : (dirty s e).card ≤ s.card*e.card := by
  exact Finset.card_image_le.trans_eq (Finset.card_product _ _)

lemma prefix_clean (s e : Finset ℕ) (X n : ℕ)
    (hcoverage : ∀ m ≤ X, m ∉ e → Unique s m)
    (hn : n ≤ X) (hclean : n ∉ dirty s e) :
    ∀ a ∈ initial s n, Unique (initial s n) (n-a) := by
  intro a ha
  obtain ⟨has,han⟩ := mem_prefix.mp ha
  have he : n-a ∉ e := by
    intro hna
    apply hclean
    exact Finset.mem_image.mpr ⟨(a,n-a),Finset.mem_product.mpr ⟨has,hna⟩,
      by dsimp; omega⟩
  exact unique_prefix s n (n-a) (Nat.sub_le _ _)
    (hcoverage (n-a) (by omega) he)

/-- Almost all smaller sums being represented forces a large initial. -/
theorem prefix_card_lower (s e : Finset ℕ) (X n : ℕ)
    (hcoverage : ∀ m ≤ X, m ∉ e → Unique s m) (hn : n ≤ X) :
    n+1 ≤ (initial s n).card*(initial s n).card + e.card := by
  let t := initial s n
  let sums := (t ×ˢ t).image (fun p => p.1+p.2)
  have hcover : Finset.range (n+1) ⊆ sums ∪ e := by
    intro m hm
    have hmn : m ≤ n := by simpa using hm
    by_cases he : m ∈ e
    · exact Finset.mem_union_right _ he
    · obtain ⟨a,ha,b,hb,hab,_⟩ := unique_prefix s n m hmn
        (hcoverage m (hmn.trans hn) he)
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨(a,b),Finset.mem_product.mpr ⟨ha,hb⟩,hab⟩
  have h1 := Finset.card_le_card hcover
  have h2 := Finset.card_union_le sums e
  have h3 : sums.card ≤ t.card*t.card :=
    Finset.card_image_le.trans_eq (Finset.card_product _ _)
  simp only [Finset.card_range] at h1
  change n+1 ≤ t.card*t.card+e.card
  omega

lemma quadratic_card_bound (k m L : ℕ) (h : k*k ≤ L*L+m*k) : k ≤ m+L := by
  by_contra hnot
  have hmk : m ≤ k := by omega
  have he := Nat.sub_add_cancel hmk
  have hlt : L+1 ≤ k-m := by omega
  have hs := Nat.mul_self_le_mul_self hlt
  nlinarith

end Erdos14Verification

/- Scale -/
namespace Erdos14Verification

lemma scale_card_upper (T k e : ℕ) (hT : 1000000 ≤ T)
    (he : 1000*e ≤ T^2) (hk : k*k ≤ 4*T^4+2+e*k) : k ≤ 3*T^2 := by
  have hbase : k*k ≤ (2*T^2+1)*(2*T^2+1)+e*k := by nlinarith
  have h := quadratic_card_bound k e (2*T^2+1) hbase
  nlinarith

lemma scale_prefix_lower (T K e n : ℕ) (_hT : 1000000 ≤ T)
    (he : 1000*e ≤ T^2) (hn : T^4/1000 < n)
    (hK : n+1 ≤ K*K+e) : T^2 ≤ 32*(K+1) := by
  have hn' : T^4 < 1000*n := by omega
  by_contra hnot
  have hsmall : 32*(K+1) ≤ T^2 := by omega
  have hsq := Nat.mul_self_le_mul_self hsmall
  have hu : 1000000 ≤ T^2 := by nlinarith
  have hlarge := Nat.mul_le_mul_right (T^2) hu
  nlinarith

lemma scale_prefix_nonempty (T K e n : ℕ) (hT : 1000000 ≤ T)
    (he : 1000*e ≤ T^2) (hn : T^4/1000 < n)
    (hK : n+1 ≤ K*K+e) : 0<K := by
  have h := scale_prefix_lower T K e n hT he hn hK
  by_contra hnot
  have : K=0 := by omega
  subst K
  nlinarith

lemma scale_one_bound (T q e d : ℕ) (hT : 1000000 ≤ T)
    (hq : T^2 ≤ 32*q)
    (hd : d*d ≤ 4*((3*T^4)/q)+2+e*d) : d ≤ e+20*T := by
  have hmul := Nat.mul_le_mul_right (3*T^2) hq
  have hprod : 3*T^4 ≤ q*(96*T^2) := by nlinarith
  have hdiv : (3*T^4)/q ≤ 96*T^2 := Nat.div_le_of_le_mul hprod
  have hbase : d*d ≤ (20*T)*(20*T)+e*d := by nlinarith
  exact quadratic_card_bound d e (20*T) hbase

lemma scale_low_count (T k e d : ℕ) (hT : 1000000 ≤ T)
    (he : 1000*e ≤ T^2) (hk : k ≤ 3*T^2)
    (hd : d ≤ T^4/1000+1+k*e+(k+1)*(1+e+20*T)) : 100*d ≤ T^4 := by
  have hk₁ := Nat.mul_le_mul_right e hk
  have hk₂ := Nat.mul_le_mul_right (1+e+20*T) (Nat.add_le_add_right hk 1)
  have he₁ := Nat.mul_le_mul_right (6*T^2+1) he
  have hdiv : 1000*(T^4/1000) ≤ T^4 := by omega
  have hT₁ : 60000 ≤ T := by omega
  have hT₂ : 3001 ≤ T^2 := by nlinarith
  have hlarge₁ := Nat.mul_le_mul_right (T^3) hT₁
  have hlarge₂ := Nat.mul_le_mul_right (T^2) hT₂
  have hT₃ : 1000000 ≤ T^2 := by nlinarith
  have hlarge₃ := Nat.mul_le_mul_right (T^2) hT₃
  nlinarith

end Erdos14Verification

/- Density -/
open Finset
open scoped BigOperators

namespace Erdos14Verification

theorem fixed_prefix_low_bound (s e u : Finset ℕ) (T K : ℕ)
    (hT : 1000000 ≤ T) (he : 1000*e.card ≤ T^2)
    (hs : ∀ a ∈ s, a ≤ T^4)
    (hgood : ∀ n, n ∉ e → (pairs s n).card ≤ 2)
    (hcoverage : ∀ n ≤ T^4, n ∉ e → Unique s n)
    (hu : ∀ n ∈ u, T^4/1000 < n ∧ n ≤ T^4 ∧
      n ∉ dirty s e ∧ (weightedPairs s n).card ≤ 1 ∧ (initial s n).card=K) :
    u.card ≤ 1+e.card+20*T := by
  classical
  by_cases hempty : u=∅
  · simp [hempty]
  obtain ⟨n₀,hn₀⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  obtain ⟨hlo₀,hhi₀,hclean₀,hg₀,hK₀⟩ := hu n₀ hn₀
  let t := initial s n₀
  let H := ∑ a ∈ t, a
  have htcard : t.card=K := hK₀
  have htEq : ∀ n ∈ u, initial s n = t := by
    intro n hn
    exact prefix_eq_of_card_eq s n n₀ ((hu n hn).2.2.2.2.trans hK₀.symm)
  have hKlow : n₀+1 ≤ K*K+e.card := by
    simpa only [hK₀] using prefix_card_lower s e (T^4) n₀ hcoverage hhi₀
  have hKpos := scale_prefix_nonempty T K e.card n₀ hT he hlo₀ hKlow
  have hq := scale_prefix_lower T K e.card n₀ hT he hlo₀ hKlow
  let u₀ := u.filter (fun n => (weightedPairs s n).card=0)
  let u₁ := u.filter (fun n => (weightedPairs s n).card=1)
  have hzero : ∀ n ∈ u₀, 3*H=n*K := by
    intro n hn
    obtain ⟨hnu,hg⟩ := Finset.mem_filter.mp hn
    obtain ⟨_,hhi,hclean,_,_⟩ := hu n hnu
    have hcg := prefix_clean s e (T^4) n hcoverage hhi hclean
    have hpg : (weightedPairs (initial s n) n).card=0 := by
      rwa [weightedPairs_prefix]
    have hm := clean_zero_moment (initial s n) n
      (fun a ha => (mem_prefix.mp ha).2) hcg hpg
    simpa only [htEq n hnu,htcard] using hm
  have hc₀ : u₀.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro n hn m hm
    have h₁ := hzero n hn
    have h₂ := hzero m hm
    nlinarith
  have hchoose : ∀ n, ∃ b, n ∈ u₁ → b ∈ s ∧ 3*H+3*b=n*(K+1) := by
    intro n
    by_cases hn : n ∈ u₁
    · obtain ⟨hnu,hg⟩ := Finset.mem_filter.mp hn
      obtain ⟨_,hhi,hclean,_,_⟩ := hu n hnu
      have hcg := prefix_clean s e (T^4) n hcoverage hhi hclean
      have hpg : (weightedPairs (initial s n) n).card=1 := by
        rwa [weightedPairs_prefix]
      obtain ⟨b,hb,hm⟩ := clean_one_moment (initial s n) n
        (fun a ha => (mem_prefix.mp ha).2) hcg hpg
      refine ⟨b,fun _ => ⟨(mem_prefix.mp hb).1,?_⟩⟩
      simpa only [htEq n hnu,htcard] using hm
    · exact ⟨0,fun h => (hn h).elim⟩
  choose b hb using hchoose
  have hpairs := linear_targets_pair_bound s e u₁ b (T^4) H (K+1)
    (by omega) hs hgood (fun n hn => (hb n hn).1) (fun n hn => (hb n hn).2)
  have hc₁ := scale_one_bound T (K+1) e.card u₁.card hT hq hpairs
  have hcover : u ⊆ u₀ ∪ u₁ := by
    intro n hn
    have hg := (hu n hn).2.2.2.1
    have hcases : (weightedPairs s n).card=0 ∨ (weightedPairs s n).card=1 := by omega
    rcases hcases with hz | ho
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hn,hz⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hn,ho⟩)
  have hcu := (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
  omega

def lowTargets (s : Finset ℕ) (X : ℕ) : Finset ℕ :=
  (Finset.range (X+1)).filter (fun n => (weightedPairs s n).card ≤ 1)

theorem low_targets_density (s e : Finset ℕ) (T : ℕ)
    (hT : 1000000 ≤ T) (he : 1000*e.card ≤ T^2)
    (hs : ∀ a ∈ s, a ≤ T^4)
    (hgood : ∀ n, n ∉ e → (pairs s n).card ≤ 2)
    (hcoverage : ∀ n ≤ T^4, n ∉ e → Unique s n) :
    100*(lowTargets s (T^4)).card ≤ T^4 := by
  let u := (lowTargets s (T^4)).filter (fun n => T^4/1000<n ∧ n ∉ dirty s e)
  have hk : s.card ≤ 3*T^2 := by
    exact scale_card_upper T s.card e.card hT he
      (interval_pair_count s e (T^4) hs (fun n _ hn => hgood n hn))
  have hfiber : u.card = ∑ K ∈ Finset.range (s.card+1),
      (u.filter (fun n => (initial s n).card=K)).card := by
    apply Finset.card_eq_sum_card_fiberwise
    intro n hn
    have hc := Finset.card_le_card (prefix_subset s n)
    change (initial s n).card ∈ Finset.range (s.card+1)
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hc)
  have hfibound : ∀ K ∈ Finset.range (s.card+1),
      (u.filter (fun n => (initial s n).card=K)).card ≤ 1+e.card+20*T := by
    intro K hK
    apply fixed_prefix_low_bound s e _ T K hT he hs hgood hcoverage
    intro n hn
    obtain ⟨hnu,hcard⟩ := Finset.mem_filter.mp hn
    obtain ⟨hnlow,hlo,hclean⟩ := Finset.mem_filter.mp hnu
    obtain ⟨hnrange,hg⟩ := Finset.mem_filter.mp hnlow
    exact ⟨hlo,by simpa using hnrange,hclean,hg,hcard⟩
  have hu : u.card ≤ (s.card+1)*(1+e.card+20*T) := by
    rw [hfiber]
    calc
      _ ≤ ∑ _K ∈ Finset.range (s.card+1), (1+e.card+20*T) :=
        Finset.sum_le_sum hfibound
      _ = _ := by simp
  have hcover : lowTargets s (T^4) ⊆
      (Finset.range (T^4/1000+1) ∪ dirty s e) ∪ u := by
    intro n hn
    by_cases hlo : n ≤ T^4/1000
    · apply Finset.mem_union_left
      apply Finset.mem_union_left
      simpa using hlo
    · by_cases hc : n ∈ dirty s e
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ hc)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hn,by omega,hc⟩)
  have hc₁ := Finset.card_le_card hcover
  have hc₂ := Finset.card_union_le (Finset.range (T^4/1000+1) ∪ dirty s e) u
  have hc₃ := Finset.card_union_le (Finset.range (T^4/1000+1)) (dirty s e)
  have hc₄ := dirty_card_le s e
  simp only [Finset.card_range] at hc₃
  apply scale_low_count T s.card e.card (lowTargets s (T^4)).card hT he hk
  omega

end Erdos14Verification

/- Generating -/
open Finset
open scoped BigOperators

namespace Erdos14Verification

def generating (s : Finset ℕ) (z : ℝ) : ℝ := ∑ a ∈ s, z^a

lemma generating_nonneg (s : Finset ℕ) (z : ℝ) (hz : 0≤z) :
    0 ≤ generating s z := Finset.sum_nonneg (fun _ _ => pow_nonneg hz _)

lemma generating_square (s : Finset ℕ) (X : ℕ) (z : ℝ)
    (hs : ∀ a ∈ s, a ≤ X) :
    generating s z ^ 2 =
      ∑ n ∈ Finset.range (2*X+1), ((pairs s n).card : ℝ)*z^n := by
  have hcover : ∀ p ∈ s ×ˢ s, p.1+p.2 ∈ Finset.range (2*X+1) := by
    intro p hp
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hp
    have := hs p.1 ha; have := hs p.2 hb
    simp only [Finset.mem_range]; omega
  have hfiber := Finset.sum_fiberwise_of_maps_to hcover
    (fun p : ℕ × ℕ => z^(p.1+p.2))
  calc
    _ = ∑ p ∈ s ×ˢ s, z^(p.1+p.2) := by
      simp only [generating,pow_two,Finset.sum_mul_sum,Finset.sum_product,pow_add]
    _ = ∑ n ∈ Finset.range (2*X+1), ∑ p ∈ pairs s n, z^(p.1+p.2) := hfiber.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hn
      calc
        _ = ∑ _p ∈ pairs s n, z^n := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [(Finset.mem_filter.mp hp).2]
        _ = _ := by simp

lemma generating_weighted (s : Finset ℕ) (X : ℕ) (z : ℝ)
    (hs : ∀ a ∈ s, a ≤ X) :
    generating s z * generating s (z^2) =
      ∑ n ∈ Finset.range (3*X+1), ((weightedPairs s n).card : ℝ)*z^n := by
  have hcover : ∀ p ∈ s ×ˢ s, p.1+2*p.2 ∈ Finset.range (3*X+1) := by
    intro p hp
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hp
    have := hs p.1 ha; have := hs p.2 hb
    simp only [Finset.mem_range]; omega
  have hfiber := Finset.sum_fiberwise_of_maps_to hcover
    (fun p : ℕ × ℕ => z^(p.1+2*p.2))
  calc
    _ = ∑ p ∈ s ×ˢ s, z^(p.1+2*p.2) := by
      simp only [generating,Finset.sum_mul_sum,Finset.sum_product,pow_add,pow_mul]
    _ = ∑ n ∈ Finset.range (3*X+1),
        ∑ p ∈ weightedPairs s n, z^(p.1+2*p.2) := hfiber.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hn
      calc
        _ = ∑ _p ∈ weightedPairs s n, z^n := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [(Finset.mem_filter.mp hp).2]
        _ = _ := by simp

lemma geometric_upper (z : ℝ) (N : ℕ) (hz : 0≤z) (hz1 : z<1) :
    (∑ n ∈ Finset.range N, z^n) ≤ 1/(1-z) := by
  apply (le_div_iff₀ (by linarith : 0<1-z)).mpr
  rw [geom_sum_mul_neg]
  have := pow_nonneg hz N
  linarith

theorem generating_upper (s e : Finset ℕ) (X : ℕ) (z : ℝ)
    (hs : ∀ a ∈ s, a ≤ X)
    (hgood : ∀ n, n ∉ e → (pairs s n).card ≤ 2)
    (hz : 0≤z) (hz1 : z<1) :
    generating s z ^ 2 ≤ 2/(1-z)+(e.card : ℝ)*s.card := by
  rw [generating_square s X z hs]
  have hterm : ∀ n ∈ Finset.range (2*X+1),
      ((pairs s n).card : ℝ)*z^n ≤ 2*z^n + if n ∈ e then (s.card : ℝ) else 0 := by
    intro n hn
    have hpow0 := pow_nonneg hz n
    have hpow1 : z^n ≤ 1 := pow_le_one₀ hz hz1.le
    by_cases he : n ∈ e
    · simp only [he,if_true]
      have hc : ((pairs s n).card : ℝ) ≤ s.card := by exact_mod_cast pairs_card_le s n
      have hc0 : (0 : ℝ) ≤ (pairs s n).card := by positivity
      nlinarith
    · simp only [he,if_false,add_zero]
      have hc : ((pairs s n).card : ℝ) ≤ 2 := by exact_mod_cast hgood n he
      nlinarith
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.sum_filter] at hsum
  simp only [Finset.sum_const,nsmul_eq_mul] at hsum
  have hcard : (((Finset.range (2*X+1)).filter (fun n => n ∈ e)).card : ℝ) ≤ e.card := by
    exact_mod_cast Finset.card_le_card (show
      (Finset.range (2*X+1)).filter (fun n => n ∈ e) ⊆ e from
        fun _ hn => (Finset.mem_filter.mp hn).2)
  have hgeom := geometric_upper z (2*X+1) hz hz1
  have hk0 : (0 : ℝ) ≤ s.card := by positivity
  have hprod := mul_le_mul_of_nonneg_right hcard hk0
  simp only [div_eq_mul_inv,one_mul] at hgeom ⊢
  nlinarith

end Erdos14Verification

/- Analysis -/
open Finset
open scoped BigOperators

namespace Erdos14Verification

theorem generating_lower (s : Finset ℕ) (X : ℕ) (z : ℝ)
    (hs : ∀ a ∈ s, a ≤ X) (hz : 0≤z) (hz1 : z≤1) :
    2*(∑ n ∈ Finset.range X, z^n) ≤ generating s z * generating s (z^2)
      +2*(lowTargets s X).card := by
  have hterm : ∀ n ∈ Finset.range X, 2*z^n ≤
      ((weightedPairs s n).card : ℝ)*z^n + if n ∈ lowTargets s X then 2 else 0 := by
    intro n hn
    have hpow0 := pow_nonneg hz n
    have hpow1 : z^n ≤ 1 := pow_le_one₀ hz hz1
    have hcard0 : (0 : ℝ) ≤ (weightedPairs s n).card := by positivity
    by_cases hl : n ∈ lowTargets s X
    · simp only [hl,if_true]
      nlinarith
    · have hgn : 2 ≤ (weightedPairs s n).card := by
        have hnX : n ∈ Finset.range (X+1) :=
          Finset.mem_range.mpr (by have := Finset.mem_range.mp hn; omega)
        have hnle : ¬(weightedPairs s n).card ≤ 1 := by
          intro hg
          exact hl (Finset.mem_filter.mpr ⟨hnX,hg⟩)
        omega
      have hgr : (2 : ℝ) ≤ (weightedPairs s n).card := by exact_mod_cast hgn
      simp only [hl,if_false,add_zero]
      exact mul_le_mul_of_nonneg_right hgr hpow0
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.mul_sum,Finset.sum_add_distrib,← Finset.sum_filter] at hsum
  simp only [Finset.sum_const,nsmul_eq_mul] at hsum
  have hcard : (((Finset.range X).filter (fun n => n ∈ lowTargets s X)).card : ℝ)
      ≤ (lowTargets s X).card := by
    exact_mod_cast Finset.card_le_card (show
      (Finset.range X).filter (fun n => n ∈ lowTargets s X) ⊆ lowTargets s X from
        fun _ hn => (Finset.mem_filter.mp hn).2)
  have hsub : (∑ n ∈ Finset.range X, ((weightedPairs s n).card : ℝ)*z^n)
      ≤ generating s z * generating s (z^2) := by
    rw [generating_weighted s X z hs]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.range_mono (by omega)
    · intro n hn hnot
      positivity
  nlinarith

lemma rational_point (X : ℕ) (hX : 1000 ≤ X) :
    let z : ℝ := 1-4/(X : ℝ)
    0<z ∧ z<1 ∧ z^X ≤ 1/5 := by
  have hx : (1000 : ℝ) ≤ X := by exact_mod_cast hX
  have hx0 : (0 : ℝ) < X := by linarith
  let z : ℝ := 1-4/(X : ℝ)
  have ha0 : (0 : ℝ) < 4/(X : ℝ) := div_pos (by norm_num) hx0
  have ha1 : (4 : ℝ)/(X : ℝ) < 1 := (div_lt_one hx0).mpr (by linarith)
  have hz0 : 0<z := by dsimp [z]; linarith
  have hz1 : z<1 := by dsimp [z]; linarith
  refine ⟨hz0,hz1,?_⟩
  have hrecip : 1+4/(X : ℝ) ≤ z⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ hz0).mpr
    dsimp [z]
    nlinarith [sq_nonneg ((4 : ℝ)/(X : ℝ))]
  have hber := one_add_mul_le_pow (by linarith : (-2 : ℝ) ≤ 4/(X : ℝ)) X
  have hcancel : (X : ℝ)*(4/(X : ℝ))=4 := by field_simp
  rw [hcancel] at hber
  have hpow := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ 1+4/(X : ℝ)) hrecip X
  have hfive : (5 : ℝ) ≤ (z^X)⁻¹ := by
    rw [← inv_pow]
    linarith
  rw [inv_eq_one_div] at hfive
  have h := (le_div_iff₀ (pow_pos hz0 X)).mp hfive
  linarith

lemma geometric_at_rational_point (X : ℕ) (hX : 1000 ≤ X) :
    let z : ℝ := 1-4/(X : ℝ)
    (2/5 : ℝ)*X ≤ 2*(∑ n ∈ Finset.range X, z^n) := by
  let z : ℝ := 1-4/(X : ℝ)
  have hx : (1000 : ℝ) ≤ X := by exact_mod_cast hX
  obtain ⟨hz0,hz1,hpow⟩ := rational_point X hX
  have hfactor : (1-z)*(X : ℝ)=4 := by dsimp [z]; field_simp; ring
  have hgeom : 4*(∑ n ∈ Finset.range X, z^n) = (1-z^X)*(X : ℝ) := by
    calc
      _ = (∑ n ∈ Finset.range X, z^n)*((1-z)*(X : ℝ)) := by rw [hfactor]; ring
      _ = _ := by rw [← mul_assoc,geom_sum_mul_neg]
  have hp := mul_le_mul_of_nonneg_right hpow (by linarith : (0 : ℝ) ≤ X)
  change (2/5 : ℝ)*X ≤ 2*(∑ n ∈ Finset.range X, z^n)
  nlinarith

lemma product_upper_at_rational_point (X : ℕ) (hX : 1000 ≤ X)
    (F G c : ℝ) (hc : c ≤ (3/1000 : ℝ)*X)
    (hF : F^2 ≤ 2/(1-(1-4/(X : ℝ)))+c)
    (hG : G^2 ≤ 2/(1-(1-4/(X : ℝ))^2)+c) :
    F*G < (37/100 : ℝ)*X := by
  have hx : (1000 : ℝ) ≤ X := by exact_mod_cast hX
  have hx0 : (0 : ℝ) < X := by linarith
  have hx2 : (0 : ℝ) < (X : ℝ)-2 := by linarith
  have hfirst : (2 : ℝ)/(1-(1-4/(X : ℝ))) = (X : ℝ)/2 := by
    field_simp
    ring
  have hden : (1 : ℝ)-(1-4/(X : ℝ))^2 = 8*((X : ℝ)-2)/(X : ℝ)^2 := by
    field_simp
    ring
  have hsecond : (2 : ℝ)/(1-(1-4/(X : ℝ))^2)
      = (X : ℝ)/4 + (X : ℝ)/(2*((X : ℝ)-2)) := by
    rw [hden]
    field_simp
    ring
  have hrem : (X : ℝ)/(2*((X : ℝ)-2)) ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    linarith
  rw [hfirst] at hF
  rw [hsecond] at hG
  have hFb : F^2 ≤ (51/100 : ℝ)*X := by linarith
  have hGb : G^2 ≤ (26/100 : ℝ)*X := by linarith
  have hprod : (F*G)^2 ≤ (51/100 : ℝ)*(26/100)*(X : ℝ)^2 := by
    calc
      _ = F^2*G^2 := by ring
      _ ≤ ((51/100 : ℝ)*X)*G^2 := mul_le_mul_of_nonneg_right hFb (sq_nonneg G)
      _ ≤ ((51/100 : ℝ)*X)*((26/100 : ℝ)*X) :=
        mul_le_mul_of_nonneg_left hGb (by positivity)
      _ = _ := by ring
  by_contra hnot
  have hnonneg : 0 ≤ F*G-(37/100 : ℝ)*X := by linarith
  have hmul := mul_nonneg hnonneg (show 0≤F*G+(37/100 : ℝ)*X by linarith)
  nlinarith

end Erdos14Verification

/- Finite -/
namespace Erdos14Verification

/-- A fully finite obstruction. Exceptions include zero. It only assumes an
upper representation bound beyond the prefix, not coverage there. -/
theorem finite_obstruction (s e : Finset ℕ) (T : ℕ)
    (hT : 1000000 ≤ T)
    (hs : ∀ a ∈ s, a ≤ T^4)
    (hgood : ∀ n, n ∉ e → (pairs s n).card ≤ 2)
    (hcoverage : ∀ n ≤ T^4, n ∉ e → Unique s n) :
    T^2 < 1000*e.card := by
  by_contra hnot
  have he : 1000*e.card ≤ T^2 := by omega
  have hk : s.card ≤ 3*T^2 := scale_card_upper T s.card e.card hT he
    (interval_pair_count s e (T^4) hs (fun n _ hn => hgood n hn))
  have hd := low_targets_density s e T hT he hs hgood hcoverage
  have hX : 1000 ≤ T^4 := by
    have h₂ : 1000 ≤ T^2 := by nlinarith
    have h₄ := Nat.le_mul_self (T^2)
    nlinarith
  have hXr : (1000 : ℝ) ≤ (T^4 : ℕ) := by exact_mod_cast hX
  let z : ℝ := 1-4/((T^4 : ℕ) : ℝ)
  obtain ⟨hz0,hz1,_⟩ := rational_point (T^4) hX
  have hz2 : z^2<1 := by
    have hpos := mul_pos (sub_pos.mpr hz1) (show 0<1+z by linarith)
    nlinarith
  have hF := generating_upper s e (T^4) z hs hgood hz0.le hz1
  have hG := generating_upper s e (T^4) (z^2) hs hgood (sq_nonneg z) hz2
  have heprod : 1000*(e.card*s.card) ≤ 3*T^4 := by
    have h₁ := Nat.mul_le_mul_right s.card he
    have h₂ := Nat.mul_le_mul_right (T^2) hk
    nlinarith
  have her : (1000 : ℝ)*((e.card : ℝ)*s.card) ≤ 3*(T^4 : ℕ) := by
    exact_mod_cast heprod
  have hc : (e.card : ℝ)*s.card ≤ (3/1000 : ℝ)*(T^4 : ℕ) := by linarith
  have hup := product_upper_at_rational_point (T^4) hX
    (generating s z) (generating s (z^2)) ((e.card : ℝ)*s.card) hc hF hG
  have hlo := generating_lower s (T^4) z hs hz0.le hz1.le
  have hgeom := geometric_at_rational_point (T^4) hX
  have hdr : (100 : ℝ)*(lowTargets s (T^4)).card ≤ (T^4 : ℕ) := by exact_mod_cast hd
  nlinarith

end Erdos14Verification

/- Sets -/
open Finset

namespace Erdos14Verification

/-- The same definition of unique sums used in the Formal Conjectures project:
order is ignored, and equal summands are allowed. -/
def allUniqueSums (A : Set ℕ) : Set ℕ :=
  {n | ∃ p : ℕ × ℕ, p.1 ∈ A ∧ p.2 ∈ A ∧ p.1+p.2=n ∧
    ∀ a₁ ∈ A, ∀ a₂ ∈ A, a₁+a₂=n →
      (a₁=p.1 ∧ a₂=p.2) ∨ (a₁=p.2 ∧ a₂=p.1)}

/-- Exactly the count in the statement of Erdős 14. -/
noncomputable def nonUniqueSumCount (A : Set ℕ) (N : ℕ) : ℝ :=
  ((Set.Icc 1 N) \ allUniqueSums A).ncard

noncomputable def setPrefix (A : Set ℕ) (X : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (X+1)).filter (fun a => a ∈ A)

noncomputable def exceptions (A : Set ℕ) (X : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (X+1)).filter (fun n => n ∉ allUniqueSums A)

lemma mem_setPrefix {A : Set ℕ} {X a : ℕ} :
    a ∈ setPrefix A X ↔ a ≤ X ∧ a ∈ A := by
  classical
  simp [setPrefix]

lemma mem_exceptions {A : Set ℕ} {X n : ℕ} :
    n ∈ exceptions A X ↔ n ≤ X ∧ n ∉ allUniqueSums A := by
  classical
  simp [exceptions]

lemma unique_set_pairs_upper (A : Set ℕ) (s : Finset ℕ) (n : ℕ)
    (hs : ∀ a ∈ s, a ∈ A) (hn : n ∈ allUniqueSums A) :
    (pairs s n).card ≤ 2 := by
  obtain ⟨⟨b,c⟩,hb,hc,hbc,hu⟩ := hn
  have hsub : pairs s n ⊆ {(b,c),(c,b)} := by
    intro ⟨u,v⟩ hp
    obtain ⟨hus,hvs,huv⟩ := mem_pairs.mp hp
    have h := hu u (hs u hus) v (hs v hvs) huv
    simpa only [Finset.mem_insert,Finset.mem_singleton,Prod.mk.injEq] using h
  have hcard := Finset.card_le_card hsub
  have htwo := Finset.card_insert_le (b,c) {(c,b)}
  simp only [Finset.card_singleton] at htwo
  omega

lemma unique_set_prefix (A : Set ℕ) (X n : ℕ) (hn : n ≤ X)
    (hu : n ∈ allUniqueSums A) : Unique (setPrefix A X) n := by
  obtain ⟨⟨b,c⟩,hb,hc,hbc,hunique⟩ := hu
  apply (unique_iff_unordered _ _).mpr
  refine ⟨b,mem_setPrefix.mpr ⟨by omega,hb⟩,
    c,mem_setPrefix.mpr ⟨by omega,hc⟩,hbc,?_⟩
  intro u hu v hv huv
  exact hunique u (mem_setPrefix.mp hu).2 v (mem_setPrefix.mp hv).2 huv

lemma set_prefix_data (A : Set ℕ) (X : ℕ) :
    (∀ a ∈ setPrefix A X, a ≤ X) ∧
    (∀ n, n ∉ exceptions A (2*X) → (pairs (setPrefix A X) n).card ≤ 2) ∧
    (∀ n ≤ X, n ∉ exceptions A (2*X) → Unique (setPrefix A X) n) := by
  classical
  have hs : ∀ a ∈ setPrefix A X, a ≤ X := fun a ha => (mem_setPrefix.mp ha).1
  have hsa : ∀ a ∈ setPrefix A X, a ∈ A := fun a ha => (mem_setPrefix.mp ha).2
  refine ⟨hs,?_,?_⟩
  · intro n hn
    by_cases hnx : n ≤ 2*X
    · have hu : n ∈ allUniqueSums A := by
        by_contra hnot
        exact hn (mem_exceptions.mpr ⟨hnx,hnot⟩)
      exact unique_set_pairs_upper A _ n hsa hu
    · have hempty : pairs (setPrefix A X) n = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro ⟨a,b⟩ hp
        obtain ⟨ha,hb,hab⟩ := mem_pairs.mp hp
        have := hs a ha; have := hs b hb
        omega
      simp [hempty]
  · intro n hnx hn
    apply unique_set_prefix A X n hnx
    by_contra hnot
    exact hn (mem_exceptions.mpr ⟨by omega,hnot⟩)

lemma exceptions_card_bound (A : Set ℕ) (N : ℕ) :
    ((exceptions A N).card : ℝ) ≤ nonUniqueSumCount A N+1 := by
  classical
  let p := (Finset.Icc 1 N).filter (fun n => n ∉ allUniqueSums A)
  have hp : (p : Set ℕ) = (Set.Icc 1 N) \ allUniqueSums A := by
    ext n
    simp [p]
  have hcount : (p.card : ℝ) = nonUniqueSumCount A N := by
    rw [nonUniqueSumCount,← hp,Set.ncard_coe_finset]
  have hsub : exceptions A N ⊆ p ∪ {0} := by
    intro n hn
    obtain ⟨hnN,hnunique⟩ := mem_exceptions.mp hn
    by_cases hn0 : n=0
    · exact Finset.mem_union_right _ (by simpa using hn0)
    · apply Finset.mem_union_left
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega,hnN⟩,hnunique⟩
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  simp only [Finset.card_singleton] at hcard
  have hreal : ((exceptions A N).card : ℝ) ≤ (p.card : ℝ)+1 := by exact_mod_cast hcard
  rwa [hcount] at hreal

/-- The finite lower bound applies to every infinite or finite set of naturals. -/
theorem set_scale_obstruction (A : Set ℕ) (T : ℕ) (hT : 1000000 ≤ T) :
    ((T^2 : ℕ) : ℝ) < 1000*(nonUniqueSumCount A (2*T^4)+1) := by
  obtain ⟨hs,hgood,hcoverage⟩ := set_prefix_data A (T^4)
  have hfinite := finite_obstruction (setPrefix A (T^4))
    (exceptions A (2*T^4)) T hT hs hgood hcoverage
  have hreal : ((T^2 : ℕ) : ℝ) < 1000*(exceptions A (2*T^4)).card := by
    exact_mod_cast hfinite
  have hcard := exceptions_card_bound A (2*T^4)
  linarith

end Erdos14Verification

/- PartI -/
namespace Erdos14Verification

noncomputable def positiveExceptions (A : Set ℕ) (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 N).filter (fun n => n ∉ allUniqueSums A)

lemma count_as_finset (A : Set ℕ) (N : ℕ) :
    nonUniqueSumCount A N = ((positiveExceptions A N).card : ℝ) := by
  classical
  have hp : (positiveExceptions A N : Set ℕ) = (Set.Icc 1 N) \ allUniqueSums A := by
    ext n
    simp [positiveExceptions]
  rw [nonUniqueSumCount,← hp,Set.ncard_coe_finset]

lemma count_mono (A : Set ℕ) {M N : ℕ} (hMN : M ≤ N) :
    nonUniqueSumCount A M ≤ nonUniqueSumCount A N := by
  classical
  rw [count_as_finset,count_as_finset]
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro n hn
  obtain ⟨hnI,hnU⟩ := Finset.mem_filter.mp hn
  obtain ⟨hn1,hnM⟩ := Finset.mem_Icc.mp hnI
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hn1,hnM.trans hMN⟩,hnU⟩

lemma count_nonneg (A : Set ℕ) (N : ℕ) : 0 ≤ nonUniqueSumCount A N := by
  unfold nonUniqueSumCount
  positivity

/-- Choosing the scale needs only two integer square roots. -/
lemma fourth_scale (N : ℕ) (hN : 2*1000000^4 ≤ N) :
    ∃ T : ℕ, 1000000 ≤ T ∧ 2*T^4 ≤ N ∧ N < 32*T^4 := by
  let u := Nat.sqrt (N/2)
  let T := Nat.sqrt u
  have hTu : T^2 ≤ u := Nat.sqrt_le' _
  have huN : u^2 ≤ N/2 := Nat.sqrt_le' _
  have hsq := Nat.mul_self_le_mul_self hTu
  have hlo : T^4 ≤ N/2 := by nlinarith only [hsq,huN]
  have hlo' : 2*T^4 ≤ N := by omega
  have huup : N/2 < (u+1)^2 := Nat.lt_succ_sqrt' _
  have hTup : u < (T+1)^2 := Nat.lt_succ_sqrt' _
  have hupSq := Nat.mul_self_le_mul_self (Nat.succ_le_of_lt hTup)
  have hup : N/2 < (T+1)^4 := by nlinarith only [huup,hupSq]
  have hup' : N < 2*(T+1)^4 := by omega
  have huBig : 1000000^2 ≤ u := by
    apply Nat.le_sqrt'.mpr
    norm_num at hN ⊢
    omega
  have hTBig : 1000000 ≤ T := Nat.le_sqrt'.mpr huBig
  have hdouble : T+1 ≤ 2*T := by omega
  have hfour := pow_le_pow_left₀ (Nat.zero_le (T+1)) hdouble 4
  refine ⟨T,hTBig,hlo',?_⟩
  nlinarith only [hup',hfour]

/-- A uniform square-root lower bound, stronger than part I. -/
theorem uniform_sqrt_bound (A : Set ℕ) (N : ℕ) (hN : 2*1000000^4 ≤ N) :
    Real.sqrt (N : ℝ) < 12000*nonUniqueSumCount A N := by
  obtain ⟨T,hT,hlo,hhi⟩ := fourth_scale N hN
  have hscale := set_scale_obstruction A T hT
  have hmono := count_mono A hlo
  have hbigNat : 2000 ≤ T^2 := by nlinarith only [hT,Nat.zero_le T]
  have hbig : (2000 : ℝ) ≤ (T^2 : ℕ) := by exact_mod_cast hbigNat
  have hcard : ((T^2 : ℕ) : ℝ) < 2000*nonUniqueSumCount A N := by
    linarith only [hscale,hmono,hbig]
  have hhiR : (N : ℝ) < 32*(((T^2 : ℕ) : ℝ)^2) := by
    have h : (N : ℝ) < 32*(T : ℝ)^4 := by exact_mod_cast hhi
    push_cast
    nlinarith only [h]
  have hsqrt : Real.sqrt (N : ℝ) ≤ 6*((T^2 : ℕ) : ℝ) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    nlinarith only [hhiR,sq_nonneg (((T^2 : ℕ) : ℝ))]
  linarith only [hsqrt,hcard]

noncomputable def almostSquareRoot (ε : ℝ) (N : ℕ) : ℝ :=
  (N : ℝ) ^ (1/2-ε)

/-- An affirmative answer to Erdős problem 14, part I. -/
theorem part_i_positive :
    ∀ A : Set ℕ, ∀ ε : ℝ, 0<ε → Asymptotics.IsBigO Filter.atTop
      (almostSquareRoot ε) (nonUniqueSumCount A) := by
  intro A ε hε
  apply Asymptotics.IsBigO.of_bound 12000
  apply Filter.eventually_atTop.mpr
  refine ⟨2*1000000^4,?_⟩
  intro N hN
  have hN1 : (1 : ℝ) ≤ N := by
    have hn : 1 ≤ N := by norm_num at hN; omega
    exact_mod_cast hn
  have hp : almostSquareRoot ε N ≤ Real.sqrt (N : ℝ) := by
    rw [almostSquareRoot,Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hp0 : 0 ≤ almostSquareRoot ε N := by
    exact Real.rpow_nonneg (by positivity) _
  simp only [Real.norm_eq_abs,abs_of_nonneg hp0,abs_of_nonneg (count_nonneg A N)]
  exact hp.trans (uniform_sqrt_bound A N hN).le


end Erdos14Verification

theorem target : fcTypeOfName% "Erdos14.erdos_14.parts.i" := by
  constructor
  · intro _
    exact Erdos14Verification.part_i_positive
  · intro _
    trivial
