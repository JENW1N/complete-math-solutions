import FormalConjectures.GreensOpenProblems.«51»
import TaskSupport

namespace Bounty

/- A variance bound for a ternary vertex separator of a Boolean cube. -/

open scoped BigOperators

namespace Green51Proof

abbrev Cube (n : ℕ) := Fin n → Bool

noncomputable def mean {X : Type*} [Fintype X] (f : X → ℝ) : ℝ := 𝔼 x, f x

noncomputable def variance {X : Type*} [Fintype X] (f : X → ℝ) : ℝ :=
  mean (fun x => f x ^ 2) - mean f ^ 2

noncomputable def zeroIndicator (a : ℝ) : ℝ := by
  classical
  exact if a = 0 then 1 else 0

noncomputable def zeroMass {X : Type*} [Fintype X] (f : X → ℝ) : ℝ :=
  mean (fun x => zeroIndicator (f x))

def Ternary {X : Type*} (f : X → ℝ) : Prop :=
  ∀ x, f x = -1 ∨ f x = 0 ∨ f x = 1

def Separated {n : ℕ} (f : Cube n → ℝ) : Prop :=
  ∀ x y, (∃ i, ∀ j, j ≠ i → x j = y j) → f x * f y ≠ -1

lemma mean_congr {X : Type*} [Fintype X] {f g : X → ℝ}
    (h : ∀ x, f x = g x) : mean f = mean g := by
  exact Finset.expect_congr rfl (fun x _ => h x)

lemma mean_const {X : Type*} [Fintype X] [Nonempty X] (a : ℝ) :
    mean (fun _ : X => a) = a := Fintype.expect_const a

lemma mean_add {X : Type*} [Fintype X] (f g : X → ℝ) :
    mean (fun x => f x + g x) = mean f + mean g :=
  Finset.expect_add_distrib _ f g

lemma mean_sub {X : Type*} [Fintype X] (f g : X → ℝ) :
    mean (fun x => f x - g x) = mean f - mean g :=
  Finset.expect_sub_distrib _ f g

lemma mean_mono {X : Type*} [Fintype X] {f g : X → ℝ}
    (h : ∀ x, f x ≤ g x) : mean f ≤ mean g :=
  Finset.expect_le_expect (fun x _ => h x)

lemma mean_nonneg {X : Type*} [Fintype X] {f : X → ℝ}
    (h : ∀ x, 0 ≤ f x) : 0 ≤ mean f :=
  Finset.expect_nonneg (fun x _ => h x)

lemma zeroMass_nonneg {X : Type*} [Fintype X] (f : X → ℝ) : 0 ≤ zeroMass f := by
  apply mean_nonneg
  intro x
  unfold zeroIndicator
  split_ifs <;> norm_num

lemma variance_le_one {X : Type*} [Fintype X] [Nonempty X]
    {f : X → ℝ} (hf : Ternary f) : variance f ≤ 1 := by
  have hs : mean (fun x => f x ^ 2) ≤ 1 := by
    apply Finset.expect_le Finset.univ_nonempty
    intro x _
    rcases hf x with h | h | h <;> rw [h] <;> norm_num
  unfold variance
  nlinarith [sq_nonneg (mean f)]

lemma ternary_abs_sub_le (a b : ℝ)
    (ha : a = -1 ∨ a = 0 ∨ a = 1) (hb : b = -1 ∨ b = 0 ∨ b = 1)
    (hab : a * b ≠ -1) : |a-b| ≤ zeroIndicator a + zeroIndicator b := by
  rcases ha with rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl <;> norm_num [zeroIndicator] at *

lemma mean_difference_bound {X : Type*} [Fintype X] {f g : X → ℝ}
    (hf : Ternary f) (hg : Ternary g) (hfg : ∀ x, f x * g x ≠ -1) :
    |mean f - mean g| ≤ zeroMass f + zeroMass g := by
  rw [← mean_sub]
  calc
    |mean (fun x => f x - g x)| ≤ mean (fun x => |f x - g x|) :=
      Finset.abs_expect_le _ _
    _ ≤ mean (fun x => zeroIndicator (f x) + zeroIndicator (g x)) :=
      mean_mono (fun x => ternary_abs_sub_le _ _ (hf x) (hg x) (hfg x))
    _ = zeroMass f + zeroMass g := mean_add _ _

def splitCube (n : ℕ) : Cube (n+1) ≃ Bool × Cube n where
  toFun x := (x 0, fun i => x i.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv x := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  right_inv p := by
    cases p
    rfl

lemma mean_bool (f : Bool → ℝ) : mean f = (f false + f true) / 2 := by
  rw [mean, Finset.expect_eq_sum_div_card]
  simp [add_comm]

lemma mean_split {n : ℕ} (f : Cube (n+1) → ℝ) :
    mean f = (mean (fun x => f (Fin.cons false x)) +
      mean (fun x => f (Fin.cons true x))) / 2 := by
  change (𝔼 x, f x) = _
  rw [Fintype.expect_equiv (splitCube n) f
    (fun p => f (Fin.cons p.1 p.2)) (fun x => congrArg f ((splitCube n).left_inv x).symm)]
  rw [← Finset.univ_product_univ, Finset.expect_product]
  exact mean_bool _

lemma variance_split {n : ℕ} (f : Cube (n+1) → ℝ) :
    variance f =
      (variance (fun x => f (Fin.cons false x)) +
       variance (fun x => f (Fin.cons true x))) / 2 +
      (mean (fun x => f (Fin.cons false x)) -
       mean (fun x => f (Fin.cons true x))) ^ 2 / 4 := by
  unfold variance
  rw [mean_split (fun x => f x ^ 2), mean_split f]
  ring

lemma zeroMass_split {n : ℕ} (f : Cube (n+1) → ℝ) :
    zeroMass f = (zeroMass (fun x => f (Fin.cons false x)) +
      zeroMass (fun x => f (Fin.cons true x))) / 2 := by
  exact mean_split _

lemma separated_slice {n : ℕ} {f : Cube (n+1) → ℝ} (hf : Separated f) (b : Bool) :
    Separated (fun x => f (Fin.cons b x)) := by
  intro x y hxy
  apply hf
  rcases hxy with ⟨i, hi⟩
  refine ⟨i.succ, ?_⟩
  intro j hj
  rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨l, rfl⟩
  · rfl
  · simp only [Fin.cons_succ]
    apply hi
    intro heq
    subst l
    exact hj rfl

lemma separated_across {n : ℕ} {f : Cube (n+1) → ℝ} (hf : Separated f)
    (x : Cube n) : f (Fin.cons false x) * f (Fin.cons true x) ≠ -1 := by
  apply hf
  refine ⟨0, ?_⟩
  intro j hj
  rcases Fin.eq_zero_or_eq_succ j with h | ⟨i, rfl⟩
  · exact (hj h).elim
  · rfl

lemma variance_zero_cube (f : Cube 0 → ℝ) : variance f = 0 := by
  have h (x : Cube 0) : x = (fun i => Fin.elim0 i) := by
    funext i
    exact Fin.elim0 i
  unfold variance
  have hmean : mean f = f (fun i => Fin.elim0 i) := by
    rw [mean_congr (fun x => congrArg f (h x)), mean_const]
  have hsq : mean (fun x => f x ^ 2) = f (fun i => Fin.elim0 i) ^ 2 := by
    rw [mean_congr (fun x => congrArg (fun y => f y ^ 2) (h x)), mean_const]
  rw [hmean, hsq]
  ring

theorem cube_separator_variance (n : ℕ) (f : Cube n → ℝ)
    (ht : Ternary f) (hs : Separated f) :
    variance f ≤ 2 * Real.sqrt n * zeroMass f := by
  induction n with
  | zero => simp [variance_zero_cube]
  | succ n ih =>
    let f0 : Cube n → ℝ := fun x => f (Fin.cons false x)
    let f1 : Cube n → ℝ := fun x => f (Fin.cons true x)
    have ht0 : Ternary f0 := fun x => ht _
    have ht1 : Ternary f1 := fun x => ht _
    have hv0 := ih f0 ht0 (separated_slice hs false)
    have hv1 := ih f1 ht1 (separated_slice hs true)
    have hd := zeroMass_nonneg f
    have hd0 := zeroMass_nonneg f0
    have hd1 := zeroMass_nonneg f1
    have hdiff : |mean f0 - mean f1| ≤ zeroMass f0 + zeroMass f1 :=
      mean_difference_bound ht0 ht1 (separated_across hs)
    have hdiffsq : (mean f0 - mean f1)^2 ≤ (zeroMass f0 + zeroMass f1)^2 := by
      nlinarith [sq_abs (mean f0 - mean f1), abs_nonneg (mean f0 - mean f1)]
    have hsplit : zeroMass f = (zeroMass f0 + zeroMass f1) / 2 := zeroMass_split f
    have hvsplit : variance f = (variance f0 + variance f1) / 2 +
        (mean f0 - mean f1)^2 / 4 := variance_split f
    have hrec : variance f ≤ 2 * Real.sqrt n * zeroMass f + zeroMass f ^ 2 := by
      rw [hsplit]
      nlinarith
    have hb : 0 < Real.sqrt (n+1 : ℝ) := Real.sqrt_pos.2 (by positivity)
    have ha : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
    have hb2 : Real.sqrt (n+1 : ℝ)^2 = (n : ℝ)+1 := Real.sq_sqrt (by positivity)
    have ha2 : Real.sqrt (n : ℝ)^2 = (n : ℝ) := Real.sq_sqrt (by positivity)
    have hv : variance f ≤ 1 := variance_le_one ht
    rw [Nat.cast_add, Nat.cast_one]
    by_cases hlarge : 1 ≤ Real.sqrt (n+1 : ℝ) * zeroMass f
    · nlinarith [mul_nonneg (le_of_lt hb) hd]
    · have hsmall : Real.sqrt (n+1 : ℝ) * zeroMass f < 1 := lt_of_not_ge hlarge
      have hstep : 1 ≤ Real.sqrt (n+1 : ℝ) *
          (2 * (Real.sqrt (n+1 : ℝ) - Real.sqrt (n : ℝ))) := by
        nlinarith [sq_nonneg (Real.sqrt (n+1 : ℝ) - Real.sqrt (n : ℝ))]
      have hdstep : zeroMass f ≤ 2 * (Real.sqrt (n+1 : ℝ) - Real.sqrt (n : ℝ)) := by
        nlinarith [hsmall.le.trans hstep]
      nlinarith [mul_nonneg hd (sub_nonneg.2 hdstep)]

end Green51Proof

/- Finite real Walsh transforms on Boolean cubes. -/

open scoped BigOperators

namespace Green51Proof

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev BinaryCube (ι : Type*) := ι → Bool

def bxor (a b : BinaryCube ι) : BinaryCube ι := fun i => Bool.xor (a i) (b i)

def bzero : BinaryCube ι := fun _ => false

noncomputable def walshChar (a x : BinaryCube ι) : ℝ :=
  ∏ i, if a i && x i then -1 else 1

noncomputable def walsh (f : BinaryCube ι → ℝ) (a : BinaryCube ι) : ℝ :=
  mean (fun x => f x * walshChar a x)

lemma mean_neg {X : Type*} [Fintype X] (f : X → ℝ) :
    mean (fun x => -f x) = -mean f := Finset.expect_neg_distrib _ _

lemma mean_mul_const {X : Type*} [Fintype X] (f : X → ℝ) (c : ℝ) :
    mean (fun x => f x * c) = mean f * c := (Finset.expect_mul _ _ _).symm

lemma mean_const_mul {X : Type*} [Fintype X] (f : X → ℝ) (c : ℝ) :
    mean (fun x => c * f x) = c * mean f := (Finset.mul_expect _ _ _).symm

lemma mean_sum {X Y : Type*} [Fintype X] [Fintype Y] (f : X → Y → ℝ) :
    mean (fun x => ∑ y, f x y) = ∑ y, mean (fun x => f x y) :=
  Finset.expect_sum_comm _ _ _

lemma mean_equiv {X Y : Type*} [Fintype X] [Fintype Y]
    (e : X ≃ Y) (f : Y → ℝ) : mean (fun x => f (e x)) = mean f :=
  Fintype.expect_equiv e _ f (fun _ => rfl)

omit [Fintype ι] [DecidableEq ι] in
lemma bxor_comm (a b : BinaryCube ι) : bxor a b = bxor b a := by
  funext i
  cases ha : a i <;> cases hb : b i <;> simp [bxor, ha, hb]

omit [Fintype ι] [DecidableEq ι] in
lemma bxor_self (a : BinaryCube ι) : bxor a a = bzero := by
  funext i
  cases ha : a i <;> simp [bxor, bzero, ha]

omit [Fintype ι] [DecidableEq ι] in
lemma bxor_bzero (a : BinaryCube ι) : bxor a bzero = a := by
  funext i
  cases ha : a i <;> simp [bxor, bzero, ha]

omit [Fintype ι] [DecidableEq ι] in
lemma bxor_bxor_right (a b : BinaryCube ι) : bxor (bxor a b) b = a := by
  funext i
  cases ha : a i <;> cases hb : b i <;> simp [bxor, ha, hb]

omit [Fintype ι] [DecidableEq ι] in
lemma bxor_eq_bzero_iff (a b : BinaryCube ι) : bxor a b = bzero ↔ a = b := by
  constructor
  · intro h
    funext i
    have hi := congrFun h i
    cases ha : a i <;> cases hb : b i <;> simp_all [bxor, bzero]
  · rintro rfl
    exact bxor_self _

def xorEquiv (b : BinaryCube ι) : BinaryCube ι ≃ BinaryCube ι where
  toFun a := bxor a b
  invFun a := bxor a b
  left_inv a := bxor_bxor_right a b
  right_inv a := bxor_bxor_right a b

lemma mean_xor (f : BinaryCube ι → ℝ) (b : BinaryCube ι) :
    mean (fun x => f (bxor x b)) = mean f := mean_equiv (xorEquiv b) f

omit [DecidableEq ι] in
lemma walshChar_comm (a x : BinaryCube ι) : walshChar a x = walshChar x a := by
  unfold walshChar
  apply Finset.prod_congr rfl
  intro i _
  cases ha : a i <;> cases hx : x i <;> rfl

omit [DecidableEq ι] in
lemma walshChar_bzero (x : BinaryCube ι) : walshChar bzero x = 1 := by
  simp [walshChar, bzero]

omit [DecidableEq ι] in
lemma walshChar_bzero_right (a : BinaryCube ι) : walshChar a bzero = 1 := by
  rw [walshChar_comm, walshChar_bzero]

omit [DecidableEq ι] in
lemma walshChar_bxor (a b x : BinaryCube ι) :
    walshChar (bxor a b) x = walshChar a x * walshChar b x := by
  unfold walshChar
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  cases ha : a i <;> cases hb : b i <;> cases hx : x i <;> norm_num [bxor, ha, hb, hx]

omit [DecidableEq ι] in
lemma walshChar_bxor_right (a x y : BinaryCube ι) :
    walshChar a (bxor x y) = walshChar a x * walshChar a y := by
  rw [walshChar_comm, walshChar_bxor, walshChar_comm x, walshChar_comm y]

omit [DecidableEq ι] in
lemma walshChar_sq (a x : BinaryCube ι) : walshChar a x ^ 2 = 1 := by
  rw [pow_two, ← walshChar_bxor, bxor_self, walshChar_bzero]

lemma walshChar_single (a : BinaryCube ι) (i : ι) :
    walshChar a (Function.update bzero i true) = if a i then -1 else 1 := by
  classical
  unfold walshChar
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hji
    simp [Function.update_of_ne hji, bzero]
  · simp

lemma mean_walshChar (a : BinaryCube ι) :
    mean (walshChar a) = if a = bzero then 1 else 0 := by
  classical
  split_ifs with ha
  · subst a
    rw [mean_congr (fun x => walshChar_bzero x), mean_const]
  · have hex : ∃ i, a i = true := by
      by_contra hn
      apply ha
      funext i
      have hi : a i ≠ true := fun hi => hn ⟨i, hi⟩
      cases hai : a i <;> simp_all [bzero]
    obtain ⟨i, hi⟩ := hex
    let b : BinaryCube ι := Function.update bzero i true
    have hb : walshChar a b = -1 := by simp [b, walshChar_single, hi]
    have he := mean_xor (walshChar a) b
    have hh : mean (fun x => walshChar a (bxor x b)) = -mean (walshChar a) := by
      simp_rw [walshChar_bxor_right, hb, mul_neg_one]
      exact mean_neg _
    linarith

lemma mean_char_product (a b : BinaryCube ι) :
    mean (fun x => walshChar a x * walshChar b x) = if a = b then 1 else 0 := by
  classical
  simp_rw [← walshChar_bxor]
  rw [mean_walshChar]
  simp only [bxor_eq_bzero_iff]

lemma sum_char_product (a b : BinaryCube ι) :
    (∑ x, walshChar a x * walshChar b x) =
      if a = b then (Fintype.card (BinaryCube ι) : ℝ) else 0 := by
  classical
  rw [← Fintype.card_mul_expect]
  change (Fintype.card (BinaryCube ι) : ℝ) * mean _ = _
  rw [mean_char_product]
  split_ifs <;> ring

lemma walsh_bzero (f : BinaryCube ι → ℝ) : walsh f bzero = mean f := by
  simp [walsh, walshChar_bzero]

lemma walsh_inversion (f : BinaryCube ι → ℝ) (x : BinaryCube ι) :
    (∑ a, walsh f a * walshChar a x) = f x := by
  classical
  simp_rw [walsh, ← mean_mul_const]
  rw [← mean_sum]
  have hk (y : BinaryCube ι) :
      (∑ a, (f y * walshChar a y) * walshChar a x) =
        (if y = x then (Fintype.card (BinaryCube ι) : ℝ) else 0) * f y := by
    calc
      _ = f y * ∑ a, walshChar y a * walshChar x a := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        rw [walshChar_comm a y, walshChar_comm a x]
        ring
      _ = _ := by rw [sum_char_product]; ring
  rw [mean_congr hk]
  exact Finset.expect_boole_mul' f x

lemma walsh_parseval (f : BinaryCube ι → ℝ) :
    mean (fun x => f x ^ 2) = ∑ a, walsh f a ^ 2 := by
  classical
  calc
    _ = mean (fun x => ∑ a, walsh f a * (f x * walshChar a x)) := by
      apply mean_congr
      intro x
      have h : (∑ a, walsh f a * (f x * walshChar a x)) =
          f x * (∑ a, walsh f a * walshChar a x) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        ring
      rw [h, walsh_inversion]
      ring
    _ = ∑ a, mean (fun x => walsh f a * (f x * walshChar a x)) := mean_sum _
    _ = _ := by
      simp_rw [mean_const_mul]
      apply Finset.sum_congr rfl
      intro a _
      change walsh f a * walsh f a = walsh f a ^ 2
      ring

end Green51Proof

/- Restrictions to coordinate faces and their Fourier energy. -/

open scoped BigOperators

namespace Green51Proof

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def BinarySeparated (f : BinaryCube ι → ℝ) : Prop :=
  ∀ x y, (∃ i, ∀ j, j ≠ i → x j = y j) → f x * f y ≠ -1

noncomputable def reindexCube (e : ι ≃ Fin (Fintype.card ι)) :
    BinaryCube ι ≃ Cube (Fintype.card ι) where
  toFun x := fun i => x (e.symm i)
  invFun x := fun i => x (e i)
  left_inv x := by funext i; simp
  right_inv x := by funext i; simp

lemma binary_separator_variance (f : BinaryCube ι → ℝ)
    (ht : Ternary f) (hs : BinarySeparated f) :
    variance f ≤ 2 * Real.sqrt (Fintype.card ι) * zeroMass f := by
  classical
  let e := Fintype.equivFin ι
  let q := reindexCube e
  have ht' : Ternary (fun x => f (q.symm x)) := fun x => ht _
  have hs' : Separated (fun x => f (q.symm x)) := by
    intro x y hxy
    apply hs
    obtain ⟨i, hi⟩ := hxy
    refine ⟨e.symm i, ?_⟩
    intro j hj
    apply hi
    intro hji
    apply hj
    exact e.injective (by simpa using hji)
  have h := cube_separator_variance (Fintype.card ι) _ ht' hs'
  have hsq := mean_equiv q.symm (fun x => f x ^ 2)
  have hz := mean_equiv q.symm (fun x => zeroIndicator (f x))
  simpa only [variance, zeroMass, hsq, hz, mean_equiv] using h

lemma mean_comm {X Y : Type*} [Fintype X] [Fintype Y] (f : X → Y → ℝ) :
    mean (fun x => mean (f x)) = mean (fun y => mean (fun x => f x y)) :=
  Finset.expect_comm _ _ _

abbrev FaceIndex (J : BinaryCube ι) := {i : ι // J i = true}


def embedFace (J : BinaryCube ι) (z : BinaryCube (FaceIndex J)) : BinaryCube ι :=
  fun i => if hi : J i = true then z ⟨i, hi⟩ else false

def restrictFace (f : BinaryCube ι → ℝ) (J x : BinaryCube ι)
    (z : BinaryCube (FaceIndex J)) : ℝ := f (bxor x (embedFace J z))

noncomputable def faceMean (J : BinaryCube ι) (f : BinaryCube ι → ℝ)
    (x : BinaryCube ι) : ℝ := mean (restrictFace f J x)

def charRestrict (J a : BinaryCube ι) : BinaryCube (FaceIndex J) := fun i => a i

omit [DecidableEq ι] in
lemma walshChar_embedFace (J a : BinaryCube ι) (z : BinaryCube (FaceIndex J)) :
    walshChar a (embedFace J z) = walshChar (charRestrict J a) z := by
  classical
  unfold walshChar
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun i => J i = true)]
  have h0 : (∏ i : {i // ¬ J i = true},
      if a i && embedFace J z i then (-1 : ℝ) else 1) = 1 := by
    apply Finset.prod_eq_one
    intro i _
    simp [embedFace, i.property]
  rw [h0, mul_one]
  apply Finset.prod_congr rfl
  intro i _
  simp [embedFace, i.property, charRestrict]

omit [Fintype ι] [DecidableEq ι] in
lemma restrictFace_ternary {f : BinaryCube ι → ℝ} (ht : Ternary f)
    (J x : BinaryCube ι) : Ternary (restrictFace f J x) := fun _z => ht _

omit [Fintype ι] [DecidableEq ι] in
lemma restrictFace_separated {f : BinaryCube ι → ℝ} (hs : BinarySeparated f)
    (J x : BinaryCube ι) : BinarySeparated (restrictFace f J x) := by
  intro z w hzw
  apply hs
  obtain ⟨i, hi⟩ := hzw
  refine ⟨i.val, ?_⟩
  intro j hj
  unfold bxor embedFace
  by_cases hjJ : J j = true
  · simp only [dif_pos hjJ]
    rw [hi ⟨j, hjJ⟩ (fun heq => hj (congrArg Subtype.val heq))]
  · simp only [dif_neg hjJ]

lemma mean_faceMean (J : BinaryCube ι) (f : BinaryCube ι → ℝ) :
    mean (faceMean J f) = mean f := by
  unfold faceMean restrictFace
  rw [mean_comm]
  simp_rw [mean_xor]
  exact mean_const _

lemma mean_faceZeroMass (J : BinaryCube ι) (f : BinaryCube ι → ℝ) :
    mean (fun x => zeroMass (restrictFace f J x)) = zeroMass f :=
  mean_faceMean J (fun x => zeroIndicator (f x))

noncomputable def faceKeeps (J a : BinaryCube ι) : ℝ := by
  classical
  exact if charRestrict J a = bzero then 1 else 0

lemma faceMean_char (J a : BinaryCube ι) (x : BinaryCube ι) :
    faceMean J (walshChar a) x = walshChar a x * faceKeeps J a := by
  unfold faceMean restrictFace
  simp_rw [walshChar_bxor_right, walshChar_embedFace]
  rw [mean_const_mul, mean_walshChar]
  rfl

lemma faceMean_expansion (J : BinaryCube ι) (f : BinaryCube ι → ℝ)
    (x : BinaryCube ι) :
    faceMean J f x = ∑ a, (walsh f a * faceKeeps J a) * walshChar a x := by
  classical
  unfold faceMean
  calc
    _ = mean (fun z => ∑ a, walsh f a *
        walshChar a (bxor x (embedFace J z))) := by
      apply mean_congr
      intro z
      exact (walsh_inversion f _).symm
    _ = ∑ a, walsh f a * faceMean J (walshChar a) x := by
      rw [mean_sum]
      simp_rw [mean_const_mul]
      rfl
    _ = _ := by
      simp_rw [faceMean_char]
      apply Finset.sum_congr rfl
      intro a _
      ring

lemma walsh_sum_chars (v : BinaryCube ι → ℝ) (b : BinaryCube ι) :
    walsh (fun x => ∑ a, v a * walshChar a x) b = v b := by
  classical
  unfold walsh
  simp_rw [Finset.sum_mul]
  rw [mean_sum]
  have h (a : BinaryCube ι) :
      mean (fun x => (v a * walshChar a x) * walshChar b x) =
        if a = b then v a else 0 := by
    calc
      _ = v a * mean (fun x => walshChar a x * walshChar b x) := by
        rw [← mean_const_mul]
        apply mean_congr
        intro x
        ring
      _ = _ := by rw [mean_char_product]; split_ifs <;> ring
  simp_rw [h]
  simp

lemma walsh_faceMean (J : BinaryCube ι) (f : BinaryCube ι → ℝ)
    (a : BinaryCube ι) : walsh (faceMean J f) a = walsh f a * faceKeeps J a := by
  have h : faceMean J f = fun x => ∑ b, (walsh f b * faceKeeps J b) * walshChar b x :=
    funext (faceMean_expansion J f)
  rw [h, walsh_sum_chars]

omit [DecidableEq ι] in
lemma faceKeeps_sq (J a : BinaryCube ι) : faceKeeps J a ^ 2 = faceKeeps J a := by
  unfold faceKeeps
  split_ifs <;> norm_num

lemma mean_face_variance (J : BinaryCube ι) (f : BinaryCube ι → ℝ) :
    mean (fun x => variance (restrictFace f J x)) =
      ∑ a, walsh f a ^ 2 * (1 - faceKeeps J a) := by
  classical
  unfold variance
  rw [mean_sub]
  change mean (faceMean J (fun x => f x ^ 2)) - mean (fun x => faceMean J f x ^ 2) = _
  rw [mean_faceMean, walsh_parseval, walsh_parseval]
  simp_rw [walsh_faceMean, mul_pow, faceKeeps_sq]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem face_energy_bound (J : BinaryCube ι) (f : BinaryCube ι → ℝ)
    (ht : Ternary f) (hs : BinarySeparated f) :
    (∑ a, walsh f a ^ 2 * (1 - faceKeeps J a)) ≤
      2 * Real.sqrt (Fintype.card (FaceIndex J)) * zeroMass f := by
  rw [← mean_face_variance]
  calc
    _ ≤ mean (fun x => 2 * Real.sqrt (Fintype.card (FaceIndex J)) *
        zeroMass (restrictFace f J x)) :=
      mean_mono (fun x => binary_separator_variance _
        (restrictFace_ternary ht J x) (restrictFace_separated hs J x))
    _ = _ := by rw [mean_const_mul, mean_faceZeroMass]

end Green51Proof

/- Independent random coordinate faces. -/

open scoped BigOperators

namespace Green51Proof

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def maskWeight (t : ℝ) (J : BinaryCube ι) : ℝ :=
  ∏ i, if J i then t else 1 - t

noncomputable def maskMean (t : ℝ) (f : BinaryCube ι → ℝ) : ℝ :=
  ∑ J, maskWeight t J * f J

def degree (a : BinaryCube ι) : ℕ := Fintype.card (FaceIndex a)

omit [DecidableEq ι] in
lemma maskWeight_nonneg {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) (J : BinaryCube ι) :
    0 ≤ maskWeight t J := by
  apply Finset.prod_nonneg
  intro i _
  split_ifs <;> linarith

lemma maskMean_congr (t : ℝ) {f g : BinaryCube ι → ℝ} (h : ∀ J, f J = g J) :
    maskMean t f = maskMean t g := by
  unfold maskMean
  apply Finset.sum_congr rfl
  intro J _
  rw [h]

lemma maskMean_add (t : ℝ) (f g : BinaryCube ι → ℝ) :
    maskMean t (fun J => f J + g J) = maskMean t f + maskMean t g := by
  simp [maskMean, mul_add, Finset.sum_add_distrib]

lemma maskMean_sub (t : ℝ) (f g : BinaryCube ι → ℝ) :
    maskMean t (fun J => f J - g J) = maskMean t f - maskMean t g := by
  simp [maskMean, mul_sub, Finset.sum_sub_distrib]

lemma maskMean_mul_const (t : ℝ) (f : BinaryCube ι → ℝ) (c : ℝ) :
    maskMean t (fun J => f J * c) = maskMean t f * c := by
  simp [maskMean, Finset.sum_mul, mul_assoc]

lemma maskMean_const_mul (t c : ℝ) (f : BinaryCube ι → ℝ) :
    maskMean t (fun J => c * f J) = c * maskMean t f := by
  simp [maskMean, Finset.mul_sum, mul_left_comm]

lemma maskMean_sum {X : Type*} [Fintype X] (t : ℝ) (f : BinaryCube ι → X → ℝ) :
    maskMean t (fun J => ∑ x, f J x) = ∑ x, maskMean t (fun J => f J x) := by
  simp only [maskMean, Finset.mul_sum]
  exact Finset.sum_comm

lemma maskMean_mono {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1)
    {f g : BinaryCube ι → ℝ} (h : ∀ J, f J ≤ g J) :
    maskMean t f ≤ maskMean t g := by
  apply Finset.sum_le_sum
  intro J _
  exact mul_le_mul_of_nonneg_left (h J) (maskWeight_nonneg h0 h1 J)

lemma maskMean_prod (t : ℝ) (f : ι → Bool → ℝ) :
    maskMean t (fun J => ∏ i, f i (J i)) =
      ∏ i, ((1-t) * f i false + t * f i true) := by
  unfold maskMean maskWeight
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i b => (if b then t else 1-t) * f i b)]
  apply Finset.prod_congr rfl
  intro i _
  simp [add_comm]

lemma maskMean_const (t c : ℝ) : maskMean t (fun _ : BinaryCube ι => c) = c := by
  have h : maskMean t (fun _ : BinaryCube ι => 1) = 1 := by
    have hp := maskMean_prod t (fun (_ : ι) (_ : Bool) => (1 : ℝ))
    simpa using hp
  calc
    _ = maskMean t (fun J : BinaryCube ι => 1 * c) := by simp
    _ = maskMean t (fun _ : BinaryCube ι => 1) * c := maskMean_mul_const _ _ _
    _ = c := by rw [h, one_mul]

lemma maskMean_eval (t : ℝ) (i : ι) (f : Bool → ℝ) :
    maskMean t (fun J : BinaryCube ι => f (J i)) = (1-t)*f false + t*f true := by
  classical
  let g : ι → Bool → ℝ := fun j b => if j = i then f b else 1
  have hg (J : BinaryCube ι) : (∏ j, g j (J j)) = f (J i) := by
    rw [Finset.prod_eq_single i]
    · simp [g]
    · intro j _ hji
      simp [g, hji]
    · simp
  rw [← maskMean_congr t hg, maskMean_prod]
  rw [Finset.prod_eq_single i]
  · simp [g]
  · intro j _ hji
    simp [g, hji]
  · simp

omit [DecidableEq ι] in
lemma degree_eq_sum (a : BinaryCube ι) :
    (degree a : ℝ) = ∑ i, if a i then (1 : ℝ) else 0 := by
  classical
  simp [degree, Fintype.card_subtype, Finset.sum_boole]

lemma maskMean_degree (t : ℝ) :
    maskMean t (fun J : BinaryCube ι => (degree J : ℝ)) = Fintype.card ι * t := by
  simp_rw [degree_eq_sum]
  rw [maskMean_sum]
  have h (i : ι) : maskMean t (fun J : BinaryCube ι => if J i then 1 else 0) = t := by
    simpa using maskMean_eval t i (fun b => if b then (1 : ℝ) else 0)
  simp_rw [h]
  simp

omit [DecidableEq ι] in
lemma faceKeeps_prod (J a : BinaryCube ι) :
    faceKeeps J a = ∏ i, if a i && J i then (0 : ℝ) else 1 := by
  classical
  unfold faceKeeps
  split_ifs with h
  · symm
    apply Finset.prod_eq_one
    intro i _
    by_cases hi : J i = true
    · have ha := congrFun h ⟨i, hi⟩
      simp only [charRestrict, bzero] at ha
      simp [ha]
    · simp [hi]
  · symm
    have hex : ∃ i, a i = true ∧ J i = true := by
      by_contra hn
      apply h
      funext i
      have ha : a i ≠ true := fun ha => hn ⟨i, ha, i.property⟩
      cases hai : a i <;> simp_all [charRestrict, bzero]
    obtain ⟨i, ha, hj⟩ := hex
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [ha, hj])

lemma maskMean_faceKeeps (t : ℝ) (a : BinaryCube ι) :
    maskMean t (fun J => faceKeeps J a) = (1-t) ^ degree a := by
  simp_rw [faceKeeps_prod]
  rw [maskMean_prod t (fun i b => if a i && b then (0 : ℝ) else 1)]
  have h (i : ι) :
      (1-t) * (if a i && false then (0 : ℝ) else 1) +
        t * (if a i && true then (0 : ℝ) else 1) =
          if a i then 1-t else 1 := by
    cases a i <;> simp
  simp_rw [h]
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun i => a i = true)]
  have hp : (∏ i : {i // ¬a i = true}, if a i then 1-t else (1 : ℝ)) = 1 := by
    apply Finset.prod_eq_one
    intro i _
    simp [i.property]
  rw [hp, mul_one]
  have hq : (∏ i : FaceIndex a, if a i then 1-t else (1 : ℝ)) =
      ∏ _i : FaceIndex a, (1-t) := by
    apply Finset.prod_congr rfl
    intro i _
    simp [i.property]
  rw [hq]
  simp [degree]

lemma maskMean_sqrt_degree {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    maskMean t (fun J : BinaryCube ι => Real.sqrt (degree J)) ≤
      Real.sqrt (Fintype.card ι * t) := by
  have hw (J : BinaryCube ι) := maskWeight_nonneg h0 h1 J
  have hs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (f := fun J : BinaryCube ι => maskWeight t J)
    (g := fun J : BinaryCube ι => maskWeight t J * degree J)
    (r := fun J : BinaryCube ι => maskWeight t J * Real.sqrt (degree J))
    (fun J _ => hw J) (fun J _ => mul_nonneg (hw J) (Nat.cast_nonneg _))
    (fun J _ => by rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; ring_nf; rfl)
  have hc : (∑ J : BinaryCube ι, maskWeight t J) = 1 := by
    simpa [maskMean] using (maskMean_const (ι := ι) t 1)
  rw [hc, one_mul] at hs
  change maskMean t (fun J : BinaryCube ι => Real.sqrt (degree J)) ^ 2 ≤
    maskMean t (fun J : BinaryCube ι => (degree J : ℝ)) at hs
  rw [maskMean_degree] at hs
  have hb := Real.sq_sqrt (show 0 ≤ (Fintype.card ι : ℝ) * t by positivity)
  have hn := Real.sqrt_nonneg ((Fintype.card ι : ℝ) * t)
  nlinarith

theorem noise_energy_bound (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1)
    (f : BinaryCube ι → ℝ) (ht : Ternary f) (hs : BinarySeparated f) :
    (∑ a, walsh f a ^ 2 * (1 - (1-t)^degree a)) ≤
      2 * Real.sqrt (Fintype.card ι * t) * zeroMass f := by
  have h := maskMean_mono h0 h1 (fun J => face_energy_bound J f ht hs)
  rw [maskMean_sum] at h
  simp_rw [maskMean_const_mul, maskMean_sub, maskMean_const, maskMean_faceKeeps] at h
  have hright : maskMean t (fun J : BinaryCube ι =>
      2 * Real.sqrt (Fintype.card (FaceIndex J)) * zeroMass f) =
        2 * maskMean t (fun J : BinaryCube ι => Real.sqrt (degree J)) * zeroMass f := by
    rw [maskMean_mul_const, maskMean_const_mul]
    rfl
  rw [hright] at h
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (maskMean_sqrt_degree h0 h1) (by norm_num))
    (zeroMass_nonneg f))

end Green51Proof

/- A quadratic bound on the least Walsh degree of a ternary separator. -/

open scoped BigOperators

namespace Green51Proof

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma ternary_square (a : ℝ) (ha : a = -1 ∨ a = 0 ∨ a = 1) :
    a ^ 2 = 1 - zeroIndicator a := by
  rcases ha with rfl | rfl | rfl <;> norm_num [zeroIndicator]

lemma ternary_energy {f : BinaryCube ι → ℝ} (ht : Ternary f) :
    (∑ a, walsh f a ^ 2) = 1 - zeroMass f := by
  rw [← walsh_parseval, mean_congr (fun x => ternary_square _ (ht x))]
  rw [mean_sub, mean_const]
  rfl

lemma power_decay (s : ℕ) {t : ℝ} (_h0 : 0 ≤ t) (h1 : t ≤ 1) :
    (1-t)^s * (1 + s*t) ≤ 1 := by
  induction s with
  | zero => simp
  | succ s ih =>
    have hx : 0 ≤ 1-t := by linarith
    have hinner : (1-t) * (1 + ((s : ℝ)+1)*t) ≤ 1 + (s : ℝ)*t := by
      nlinarith [mul_nonneg (show 0 ≤ (s : ℝ)+1 by positivity) (sq_nonneg t)]
    have hm := mul_le_mul_of_nonneg_left hinner (pow_nonneg hx s)
    calc
      _ = (1-t)^s * ((1-t) * (1 + ((s : ℝ)+1)*t)) := by
        rw [pow_succ, Nat.cast_add, Nat.cast_one]
        ring
      _ ≤ (1-t)^s * (1 + (s : ℝ)*t) := hm
      _ ≤ 1 := ih

lemma half_decay (s l : ℕ) (hs : 0 < s) (hl : s ≤ l) :
    1 / 2 ≤ 1 - (1 - 1/(s : ℝ))^l := by
  have hsR : 0 < (s : ℝ) := by exact_mod_cast hs
  have hs1 : 1 ≤ (s : ℝ) := by exact_mod_cast hs
  have h0 : 0 ≤ 1/(s : ℝ) := by positivity
  have h1 : 1/(s : ℝ) ≤ 1 := by exact (div_le_one hsR).2 hs1
  have h := power_decay s h0 h1
  have hcancel : (s : ℝ) * (1/(s : ℝ)) = 1 := by field_simp
  rw [hcancel] at h
  have hp := pow_le_pow_of_le_one (show 0 ≤ 1-1/(s : ℝ) by linarith)
    (show 1-1/(s : ℝ) ≤ 1 by linarith) hl
  linarith

theorem separator_min_degree_bound (f : BinaryCube ι → ℝ)
    (ht : Ternary f) (hs : BinarySeparated f) (hd : zeroMass f ≤ 1/2)
    (s : ℕ) (hmin : ∀ a, walsh f a ≠ 0 → s ≤ degree a) :
    (s : ℝ) ≤ 64 * Fintype.card ι * zeroMass f ^ 2 := by
  by_cases hsz : s = 0
  · subst s
    simp only [Nat.cast_zero]
    positivity
  have hsp : 0 < s := Nat.pos_of_ne_zero hsz
  have hsR : 0 < (s : ℝ) := by exact_mod_cast hsp
  have hs1 : 1 ≤ (s : ℝ) := by exact_mod_cast hsp
  have ht0 : 0 ≤ 1/(s : ℝ) := by positivity
  have ht1 : 1/(s : ℝ) ≤ 1 := (div_le_one hsR).2 hs1
  have h := noise_energy_bound (1/(s : ℝ)) ht0 ht1 f ht hs
  have hl : (1/2 : ℝ) * (1-zeroMass f) ≤
      ∑ a, walsh f a ^ 2 * (1-(1-1/(s : ℝ))^degree a) := by
    rw [← ternary_energy ht, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a _
    by_cases ha : walsh f a = 0
    · simp [ha]
    · have hb := half_decay s (degree a) hsp (hmin a ha)
      nlinarith [mul_nonneg (sq_nonneg (walsh f a)) (sub_nonneg.2 hb)]
  have htotal := hl.trans h
  have d0 := zeroMass_nonneg f
  have d1 : 0 ≤ 1-zeroMass f := by linarith
  have hroot : 0 ≤ Real.sqrt (Fintype.card ι * (1/(s : ℝ))) := Real.sqrt_nonneg _
  have hsq := Real.sq_sqrt (show 0 ≤ (Fintype.card ι : ℝ) * (1/(s : ℝ)) by positivity)
  have h16 : (1-zeroMass f)^2 ≤
      16 * ((Fintype.card ι : ℝ) * (1/(s : ℝ))) * zeroMass f ^ 2 := by
    nlinarith [sq_nonneg ((2 * Real.sqrt (Fintype.card ι * (1/(s : ℝ))) *
      zeroMass f) + (1/2)*(1-zeroMass f)),
      mul_nonneg (sub_nonneg.2 htotal)
        (show 0 ≤ 2 * Real.sqrt (Fintype.card ι * (1/(s : ℝ))) * zeroMass f +
          (1/2)*(1-zeroMass f) by positivity)]
  have hm := mul_le_mul_of_nonneg_right h16 hsR.le
  have hcancel : 16 * ((Fintype.card ι : ℝ) * (1/(s : ℝ))) * zeroMass f ^ 2 * s =
      16 * Fintype.card ι * zeroMass f ^ 2 := by field_simp
  rw [hcancel] at hm
  have hquarter : (1/4 : ℝ) ≤ (1-zeroMass f)^2 := by nlinarith
  have hlast := mul_le_mul_of_nonneg_right hquarter hsR.le
  nlinarith

theorem exists_low_degree_separator_coefficient (f : BinaryCube ι → ℝ)
    (ht : Ternary f) (hs : BinarySeparated f) (hd : zeroMass f ≤ 1/2) :
    ∃ a, walsh f a ≠ 0 ∧ (degree a : ℝ) ≤
      64 * Fintype.card ι * zeroMass f ^ 2 := by
  classical
  let S := Finset.univ.filter (fun a => walsh f a ≠ 0)
  have hS : S.Nonempty := by
    by_contra hn
    have hz : ∀ a, walsh f a = 0 := by
      intro a
      by_contra ha
      exact hn ⟨a, by simp [S, ha]⟩
    have he := ternary_energy ht
    simp_rw [hz] at he
    simp at he
    linarith
  obtain ⟨a, ha, ham⟩ := Finset.exists_min_image S degree hS
  have hn : walsh f a ≠ 0 := (Finset.mem_filter.mp ha).2
  refine ⟨a, hn, separator_min_degree_bound f ht hs hd (degree a) ?_⟩
  intro b hb
  exact ham b (by simp [S, hb])

end Green51Proof

/- Walsh transforms in coordinates over the field with two elements. -/

open scoped BigOperators

namespace Green51Proof

abbrev F2 := ZMod 2
abbrev Vect (ι : Type*) := ι → F2

lemma f2_cases (a : F2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

def bitField (b : Bool) : F2 := if b then 1 else 0

def fieldBit (a : F2) : Bool := decide (a = 1)

lemma fieldBit_bitField (b : Bool) : fieldBit (bitField b) = b := by
  cases b <;> decide

lemma bitField_fieldBit (a : F2) : bitField (fieldBit a) = a := by
  rcases f2_cases a with rfl | rfl <;> decide

def cubeFieldEquiv (ι : Type*) : BinaryCube ι ≃ Vect ι where
  toFun x := fun i => bitField (x i)
  invFun x := fun i => fieldBit (x i)
  left_inv x := by funext i; exact fieldBit_bitField _
  right_inv x := by funext i; exact bitField_fieldBit _

lemma bitField_xor (a b : Bool) : bitField (Bool.xor a b) = bitField a + bitField b := by
  cases a <;> cases b <;> decide

lemma cubeFieldEquiv_xor {ι : Type*} (a b : BinaryCube ι) :
    cubeFieldEquiv ι (bxor a b) = cubeFieldEquiv ι a + cubeFieldEquiv ι b := by
  funext i
  exact bitField_xor _ _

lemma cubeFieldEquiv_symm_add {ι : Type*} (a b : Vect ι) :
    (cubeFieldEquiv ι).symm (a+b) =
      bxor ((cubeFieldEquiv ι).symm a) ((cubeFieldEquiv ι).symm b) := by
  apply (cubeFieldEquiv ι).injective
  simp only [Equiv.apply_symm_apply, cubeFieldEquiv_xor]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def fieldChar (a x : Vect ι) : ℝ :=
  walshChar ((cubeFieldEquiv ι).symm a) ((cubeFieldEquiv ι).symm x)

noncomputable def fieldWalsh (f : Vect ι → ℝ) (a : Vect ι) : ℝ :=
  mean (fun x => f x * fieldChar a x)

omit [DecidableEq ι] in
lemma fieldChar_add (a x y : Vect ι) :
    fieldChar a (x+y) = fieldChar a x * fieldChar a y := by
  unfold fieldChar
  rw [cubeFieldEquiv_symm_add, walshChar_bxor_right]

omit [DecidableEq ι] in
lemma fieldChar_sq (a x : Vect ι) : fieldChar a x ^ 2 = 1 := walshChar_sq _ _

lemma fieldChar_cases (a x : Vect ι) : fieldChar a x = 1 ∨ fieldChar a x = -1 := by
  exact sq_eq_one_iff.mp (fieldChar_sq a x)

omit [DecidableEq ι] in
lemma fieldChar_zero (a : Vect ι) : fieldChar a 0 = 1 := by
  have h : (cubeFieldEquiv ι).symm (0 : Vect ι) = bzero := by
    funext i
    change fieldBit (0 : F2) = false
    decide
  simp [fieldChar, h, walshChar_bzero_right]

lemma fieldChar_sum {X : Type*} (s : Finset X) (a : Vect ι) (f : X → Vect ι) :
    fieldChar a (∑ i ∈ s, f i) = ∏ i ∈ s, fieldChar a (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [fieldChar_zero]
  | @insert i s hi ih => simp [hi, fieldChar_add, ih]

lemma fieldWalsh_eq_walsh (f : Vect ι → ℝ) (a : Vect ι) :
    fieldWalsh f a = walsh (fun x => f (cubeFieldEquiv ι x))
      ((cubeFieldEquiv ι).symm a) := by
  unfold fieldWalsh walsh fieldChar
  rw [← mean_equiv (cubeFieldEquiv ι)]
  simp only [Equiv.symm_apply_apply]

theorem fieldWalsh_inversion (f : Vect ι → ℝ) (x : Vect ι) :
    (∑ a, fieldWalsh f a * fieldChar a x) = f x := by
  classical
  rw [← Equiv.sum_comp (cubeFieldEquiv ι)]
  simp_rw [fieldWalsh_eq_walsh, fieldChar, Equiv.symm_apply_apply]
  exact (walsh_inversion (fun y => f (cubeFieldEquiv ι y))
    ((cubeFieldEquiv ι).symm x)).trans (by simp)

def fieldDot (a : Vect ι) : Vect ι →ₗ[F2] F2 where
  toFun x := ∑ i, a i * x i
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.mul_sum, mul_left_comm]

noncomputable def fieldSign (x : F2) : ℝ := if x = 0 then 1 else -1

lemma fieldSign_add (x y : F2) : fieldSign (x+y) = fieldSign x * fieldSign y := by
  have h11 : (1 : F2) + 1 = 0 := rfl
  rcases f2_cases x with rfl | rfl <;>
    rcases f2_cases y with rfl | rfl <;>
    simp only [h11, zero_add, add_zero] <;> norm_num [fieldSign]

lemma fieldSign_sum {X : Type*} (s : Finset X) (f : X → F2) :
    fieldSign (∑ i ∈ s, f i) = ∏ i ∈ s, fieldSign (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [fieldSign]
  | @insert i s hi ih => simp [hi, fieldSign_add, ih]

omit [DecidableEq ι] in
lemma fieldChar_eq_sign_dot (a x : Vect ι) : fieldChar a x = fieldSign (fieldDot a x) := by
  change (∏ i, if fieldBit (a i) && fieldBit (x i) then (-1 : ℝ) else 1) =
    fieldSign (∑ i, a i * x i)
  rw [fieldSign_sum]
  apply Finset.prod_congr rfl
  intro i _
  rcases f2_cases (a i) with ha | ha <;>
    rcases f2_cases (x i) with hx | hx <;> simp [ha, hx, fieldBit, fieldSign]

lemma fieldChar_eq_one_iff (a x : Vect ι) : fieldChar a x = 1 ↔ fieldDot a x = 0 := by
  rw [fieldChar_eq_sign_dot]
  unfold fieldSign
  split_ifs <;> norm_num at * <;> assumption

lemma fieldChar_eq_neg_one_iff (a x : Vect ι) : fieldChar a x = -1 ↔ fieldDot a x ≠ 0 := by
  rw [fieldChar_eq_sign_dot]
  unfold fieldSign
  split_ifs <;> norm_num at * <;> assumption

lemma mean_field_translate (f : Vect ι → ℝ) (b : Vect ι) :
    mean (fun x => f (x+b)) = mean f := mean_equiv (Equiv.addRight b) f

omit [Fintype ι] [DecidableEq ι] in
lemma field_add_self (x : Vect ι) : x+x = 0 := by
  exact ZModModule.add_self x

end Green51Proof

/- Lifting functions on a binary vector space to a generator cube. -/

open scoped BigOperators

namespace Green51Proof

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def cubeLift (b : κ → Vect ι) (z : BinaryCube κ) : Vect ι :=
  ∑ i, bitField (z i) • b i

def allBits : BinaryCube κ := fun _ => true

noncomputable def liftFrequency (b : κ → Vect ι) (a : Vect ι) : BinaryCube κ :=
  fun i => decide (fieldChar a (b i) = -1)

noncomputable def defectFrequency (b : κ → Vect ι) (a : Vect ι) : BinaryCube κ :=
  bxor allBits (liftFrequency b a)

noncomputable def lifted (b : κ → Vect ι) (f : Vect ι → ℝ)
    (t : Vect ι) (z : BinaryCube κ) : ℝ :=
  walshChar allBits z * f (t + cubeLift b z)

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
lemma cubeLift_xor (b : κ → Vect ι) (x y : BinaryCube κ) :
    cubeLift b (bxor x y) = cubeLift b x + cubeLift b y := by
  unfold cubeLift
  simp [bxor, bitField_xor, add_smul, Finset.sum_add_distrib]

omit [Fintype ι] [DecidableEq ι] in
lemma cubeLift_single (b : κ → Vect ι) (i : κ) :
    cubeLift b (Function.update bzero i true) = b i := by
  classical
  unfold cubeLift
  rw [Finset.sum_eq_single i]
  · simp [bitField]
  · intro j _ hji
    simp [Function.update_of_ne hji, bzero, bitField]
  · simp

omit [DecidableEq κ] in
lemma fieldChar_cubeLift (b : κ → Vect ι) (a : Vect ι) (z : BinaryCube κ) :
    fieldChar a (cubeLift b z) = walshChar (liftFrequency b a) z := by
  unfold cubeLift walshChar
  rw [fieldChar_sum]
  apply Finset.prod_congr rfl
  intro i _
  cases hz : z i
  · simp [bitField, fieldChar_zero]
  · rcases fieldChar_cases a (b i) with h | h <;>
      simp [bitField, liftFrequency, h]

lemma lifted_expansion (b : κ → Vect ι) (f : Vect ι → ℝ)
    (t : Vect ι) (z : BinaryCube κ) :
    lifted b f t z = ∑ a, (fieldWalsh f a * fieldChar a t) *
      walshChar (defectFrequency b a) z := by
  unfold lifted
  rw [← fieldWalsh_inversion f (t+cubeLift b z), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [fieldChar_add, fieldChar_cubeLift, defectFrequency, walshChar_bxor]
  ring

lemma walsh_expansion {X : Type*} [Fintype X] (v : X → ℝ) (a : X → BinaryCube κ)
    (d : BinaryCube κ) :
    walsh (fun z => ∑ x, v x * walshChar (a x) z) d =
      ∑ x, if a x = d then v x else 0 := by
  classical
  unfold walsh
  simp_rw [Finset.sum_mul]
  rw [mean_sum]
  apply Finset.sum_congr rfl
  intro x _
  calc
    _ = v x * mean (fun z => walshChar (a x) z * walshChar d z) := by
      rw [← mean_const_mul]
      apply mean_congr
      intro z
      ring
    _ = _ := by rw [mean_char_product]; split_ifs <;> ring

theorem lifted_spectrum (b : κ → Vect ι) (f : Vect ι → ℝ)
    (t : Vect ι) (d : BinaryCube κ) (hd : walsh (lifted b f t) d ≠ 0) :
    ∃ a : Vect ι, defectFrequency b a = d := by
  classical
  by_contra hn
  apply hd
  have h : lifted b f t = fun z => ∑ a, (fieldWalsh f a * fieldChar a t) *
      walshChar (defectFrequency b a) z := funext (lifted_expansion b f t)
  rw [h, walsh_expansion]
  apply Finset.sum_eq_zero
  intro a _
  have ha : defectFrequency b a ≠ d := fun ha => hn ⟨a, ha⟩
  simp [ha]

omit [Fintype κ] [DecidableEq κ] in
lemma defectFrequency_true (b : κ → Vect ι) (a : Vect ι) (i : κ) :
    defectFrequency b a i = true ↔ fieldDot a (b i) = 0 := by
  rcases fieldChar_cases a (b i) with h | h
  · simp [defectFrequency, bxor, allBits, liftFrequency, h,
      (fieldChar_eq_one_iff _ _).mp h]
    norm_num
  · have hd := (fieldChar_eq_neg_one_iff _ _).mp h
    simp [defectFrequency, bxor, allBits, liftFrequency, h, hd]

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
lemma lifted_ternary (b : κ → Vect ι) (f : Vect ι → ℝ)
    (ht : Ternary f) (t : Vect ι) : Ternary (lifted b f t) := by
  intro z
  have hc : walshChar (allBits : BinaryCube κ) z = 1 ∨
      walshChar (allBits : BinaryCube κ) z = -1 := sq_eq_one_iff.mp (walshChar_sq _ _)
  rcases hc with hc | hc <;> rcases ht (t+cubeLift b z) with hf | hf | hf <;>
    simp [lifted, hc, hf]

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
lemma lifted_zeroIndicator (b : κ → Vect ι) (f : Vect ι → ℝ)
    (t : Vect ι) (z : BinaryCube κ) :
    zeroIndicator (lifted b f t z) = zeroIndicator (f (t+cubeLift b z)) := by
  have hn : walshChar (allBits : BinaryCube κ) z ≠ 0 := by
    have h := walshChar_sq (allBits : BinaryCube κ) z
    intro h0
    rw [h0] at h
    norm_num at h
  simp [zeroIndicator, lifted, hn]

lemma mean_lifted_zeroMass (b : κ → Vect ι) (f : Vect ι → ℝ) :
    mean (fun t => zeroMass (lifted b f t)) = zeroMass f := by
  unfold zeroMass
  simp_rw [lifted_zeroIndicator]
  rw [mean_comm]
  rw [mean_congr (fun z => mean_field_translate
    (fun x => zeroIndicator (f x)) (cubeLift b z)), mean_const]

omit [Fintype κ] in
lemma binarySeparated_of_flip {f : BinaryCube κ → ℝ} (ht : Ternary f)
    (hf : ∀ x i, f x * f (bxor x (Function.update bzero i true)) ≠ -1) :
    BinarySeparated f := by
  classical
  intro x y hxy
  obtain ⟨i, hi⟩ := hxy
  by_cases hxyi : x i = y i
  · have he : x = y := by
      funext j
      by_cases hj : j = i
      · subst j
        exact hxyi
      · exact hi j hj
    subst y
    rcases ht x with h | h | h <;> rw [h] <;> norm_num
  · have he : y = bxor x (Function.update bzero i true) := by
      funext j
      by_cases hj : j = i
      · subst j
        cases hx : x i <;> cases hy : y i <;> simp_all [bxor]
      · simp [bxor, Function.update_of_ne hj, bzero, ← hi j hj]
    rw [he]
    exact hf x i

theorem lifted_separated (b : κ → Vect ι) (f : Vect ι → ℝ)
    (ht : Ternary f) (he : ∀ x i, f x * f (x+b i) ≠ 1)
    (t : Vect ι) : BinarySeparated (lifted b f t) := by
  apply binarySeparated_of_flip (lifted_ternary b f ht t)
  intro z i
  have hchar : walshChar (allBits : BinaryCube κ) (Function.update bzero i true) = -1 := by
    simp [walshChar_single, allBits]
  have hsq := walshChar_sq (allBits : BinaryCube κ) z
  have hh := he (t+cubeLift b z) i
  unfold lifted
  rw [walshChar_bxor_right, hchar, cubeLift_xor, cubeLift_single, ← add_assoc]
  intro h
  apply hh
  nlinarith [show (walshChar (allBits : BinaryCube κ) z * f (t+cubeLift b z)) *
      (walshChar (allBits : BinaryCube κ) z * -1 * f (t+cubeLift b z+b i)) =
      - (walshChar (allBits : BinaryCube κ) z)^2 *
        (f (t+cubeLift b z) * f (t+cubeLift b z+b i)) by ring]

end Green51Proof

/- A quadratic defect bound for a linear functional on missing sums. -/

open scoped BigOperators

namespace Green51Proof

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def indicator (A : Finset (Vect ι)) (x : Vect ι) : ℝ := if x ∈ A then 1 else 0

noncomputable def density (A : Finset (Vect ι)) : ℝ := mean (indicator A)

def SumIndependent (A : Finset (Vect ι)) (b : Vect ι) : Prop :=
  ∀ x, x ∈ A → x+b ∉ A

noncomputable def differenceIndicator (A : Finset (Vect ι)) (b x : Vect ι) : ℝ :=
  indicator A x - indicator A (x+b)

omit [DecidableEq ι] in
lemma differenceIndicator_ternary (A : Finset (Vect ι)) (b : Vect ι) :
    Ternary (differenceIndicator A b) := by
  classical
  intro x
  by_cases hx : x ∈ A <;> by_cases hy : x+b ∈ A <;>
    simp [differenceIndicator, indicator, hx, hy]

omit [DecidableEq ι] in
lemma differenceIndicator_one (A : Finset (Vect ι)) (b x : Vect ι)
    (h : differenceIndicator A b x = 1) : x ∈ A := by
  classical
  by_cases hx : x ∈ A
  · exact hx
  · by_cases hy : x+b ∈ A <;> norm_num [differenceIndicator, indicator, hx, hy] at h

omit [DecidableEq ι] in
lemma differenceIndicator_neg_one (A : Finset (Vect ι)) (b x : Vect ι)
    (h : differenceIndicator A b x = -1) : x+b ∈ A := by
  classical
  by_cases hx : x+b ∈ A
  · exact hx
  · by_cases hy : x ∈ A <;> norm_num [differenceIndicator, indicator, hx, hy] at h

lemma ternary_product_one (a b : ℝ) (ha : a = -1 ∨ a = 0 ∨ a = 1)
    (hb : b = -1 ∨ b = 0 ∨ b = 1) (hab : a*b = 1) :
    (a = 1 ∧ b = 1) ∨ (a = -1 ∧ b = -1) := by
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;> norm_num at *

lemma differenceIndicator_edge (A : Finset (Vect ι)) (b0 b : Vect ι)
    (hb : SumIndependent A b) (x : Vect ι) :
    differenceIndicator A b0 x * differenceIndicator A b0 (x+b) ≠ 1 := by
  intro hh
  have ht := differenceIndicator_ternary A b0
  rcases ternary_product_one _ _ (ht x) (ht (x+b)) hh with h | h
  · exact hb x (differenceIndicator_one A b0 x h.1)
      (differenceIndicator_one A b0 (x+b) h.2)
  · have h1 := differenceIndicator_neg_one A b0 x h.1
    have h2 := differenceIndicator_neg_one A b0 (x+b) h.2
    apply hb (x+b0) h1
    simpa only [add_assoc, add_comm b b0] using h2

lemma zeroMass_differenceIndicator (A : Finset (Vect ι)) (b : Vect ι)
    (hb : SumIndependent A b) :
    zeroMass (differenceIndicator A b) = 1 - 2 * density A := by
  classical
  have hp (x : Vect ι) : zeroIndicator (differenceIndicator A b x) =
      1 - indicator A x - indicator A (x+b) := by
    by_cases hx : x ∈ A
    · have hy := hb x hx
      simp [differenceIndicator, indicator, zeroIndicator, hx, hy]
    · by_cases hy : x+b ∈ A <;>
        norm_num [differenceIndicator, indicator, zeroIndicator, hx, hy]
  unfold zeroMass
  rw [mean_congr hp, mean_sub, mean_sub, mean_const, mean_field_translate]
  unfold density
  ring

lemma density_nonneg (A : Finset (Vect ι)) : 0 ≤ density A := by
  apply mean_nonneg
  intro x
  unfold indicator
  split_ifs <;> norm_num

lemma density_le_one (A : Finset (Vect ι)) : density A ≤ 1 := by
  apply Finset.expect_le Finset.univ_nonempty
  intro x _
  unfold indicator
  split_ifs <;> norm_num

lemma card_defectFrequency (D : Finset (Vect ι)) (a : Vect ι) :
    degree (defectFrequency (fun b : D => b.val) a) =
      (D.filter (fun b => fieldDot a b = 0)).card := by
  classical
  unfold degree
  let e : FaceIndex (defectFrequency (fun b : D => b.val) a) ≃
      {b // b ∈ D.filter (fun b => fieldDot a b = 0)} := {
    toFun := fun x => ⟨x.val.val, Finset.mem_filter.mpr
      ⟨x.val.property, (defectFrequency_true _ _ _).mp x.property⟩⟩
    invFun := fun x => ⟨⟨x.val, (Finset.mem_filter.mp x.property).1⟩,
      (defectFrequency_true _ _ _).mpr (Finset.mem_filter.mp x.property).2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  simpa only [Fintype.card_coe] using Fintype.card_congr e

theorem exists_good_cut (A D : Finset (Vect ι)) (hD : D.Nonempty)
    (hA : ∀ b ∈ D, SumIndependent A b) (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1/4)
    (hden : 1/2 - ε ≤ density A) :
    ∃ a : Vect ι, ((D.filter (fun b => fieldDot a b = 0)).card : ℝ) ≤
      256 * ε^2 * D.card := by
  classical
  obtain ⟨b0, hb0⟩ := hD
  let f := differenceIndicator A b0
  let b : D → Vect ι := fun i => i.val
  have hf : Ternary f := differenceIndicator_ternary A b0
  have he : ∀ x i, f x * f (x+b i) ≠ 1 :=
    fun x i => differenceIndicator_edge A b0 _ (hA _ i.property) x
  have hz : zeroMass f ≤ 2*ε := by
    rw [zeroMass_differenceIndicator A b0 (hA _ hb0)]
    linarith
  have hmean : mean (fun t => zeroMass (lifted b f t)) ≤ 2*ε := by
    rw [mean_lifted_zeroMass]
    exact hz
  obtain ⟨t, _, ht⟩ := Finset.exists_le_of_expect_le Finset.univ_nonempty hmean
  have hhalf : zeroMass (lifted b f t) ≤ 1/2 := by linarith
  obtain ⟨v, hv, hsmall⟩ := exists_low_degree_separator_coefficient (lifted b f t)
    (lifted_ternary b f hf t) (lifted_separated b f hf he t) hhalf
  obtain ⟨a, ha⟩ := lifted_spectrum b f t v hv
  refine ⟨a, ?_⟩
  rw [← ha, card_defectFrequency, Fintype.card_coe] at hsmall
  have hsq : zeroMass (lifted b f t)^2 ≤ 4*ε^2 := by
    nlinarith [zeroMass_nonneg (lifted b f t)]
  nlinarith [mul_nonneg (show (0 : ℝ) ≤ D.card by positivity) (sub_nonneg.2 hsq)]

end Green51Proof

/- Multilinear polynomial functions over the field with two elements. -/

open scoped BigOperators

namespace Green51Proof

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def monomialFunction (S : Finset ι) (x : Vect ι) : F2 := ∏ i ∈ S, x i

abbrev MonomialIndex (ι : Type*) [Fintype ι] (r : ℕ) :=
  {S : Finset ι // S.card ≤ r}

noncomputable def lowDegree (ι : Type*) [Fintype ι] (r : ℕ) :
    Submodule F2 (Vect ι → F2) :=
  Submodule.span F2 (Set.range (fun S : MonomialIndex ι r => monomialFunction S.val))

omit [DecidableEq ι] in
lemma monomial_mem_lowDegree (S : Finset ι) (r : ℕ) (hS : S.card ≤ r) :
    monomialFunction S ∈ lowDegree ι r :=
  Submodule.subset_span ⟨⟨S, hS⟩, rfl⟩

lemma lowDegree_mono {r s : ℕ} (hrs : r ≤ s) : lowDegree ι r ≤ lowDegree ι s := by
  apply Submodule.span_le.mpr
  rintro _ ⟨S, rfl⟩
  exact monomial_mem_lowDegree S.val s (S.property.trans hrs)

lemma one_mem_lowDegree (r : ℕ) : (fun _ : Vect ι => (1 : F2)) ∈ lowDegree ι r := by
  convert monomial_mem_lowDegree (ι := ι) ∅ r (by simp) using 1
  funext x
  simp [monomialFunction]

lemma f2_mul_self (a : F2) : a*a = a := by
  rcases f2_cases a with rfl | rfl <;> simp

omit [Fintype ι] in
lemma monomial_insert (i : ι) (S : Finset ι) (x : Vect ι) :
    monomialFunction (insert i S) x = monomialFunction S x * x i := by
  classical
  by_cases hi : i ∈ S
  · rw [Finset.insert_eq_of_mem hi]
    unfold monomialFunction
    rw [← Finset.mul_prod_erase S (fun j => x j) hi]
    calc
      _ = (x i * x i) * ∏ j ∈ S.erase i, x j := by rw [f2_mul_self]
      _ = _ := by ring
  · simp [monomialFunction, hi, mul_comm]

lemma mul_coord_mem_lowDegree {r : ℕ} {f : Vect ι → F2}
    (hf : f ∈ lowDegree ι r) (i : ι) :
    (fun x => f x * x i) ∈ lowDegree ι (r+1) := by
  classical
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨S, rfl⟩ := hf
    have he : (fun x => monomialFunction S.val x * x i) = monomialFunction (insert i S.val) :=
      funext (fun x => (monomial_insert i S.val x).symm)
    rw [he]
    exact monomial_mem_lowDegree _ _ ((Finset.card_insert_le _ _).trans (Nat.add_le_add_right S.property 1))
  | zero =>
    convert (lowDegree ι (r+1)).zero_mem using 1
    funext x
    simp
  | add f g hf hg ihf ihg =>
    have h := (lowDegree ι (r+1)).add_mem ihf ihg
    convert h using 1
    funext x
    simp [add_mul]
  | smul c f hf ih =>
    have h := (lowDegree ι (r+1)).smul_mem c ih
    convert h using 1
    funext x
    simp [mul_assoc]

lemma mul_affine_mem_lowDegree {r : ℕ} {f : Vect ι → F2}
    (hf : f ∈ lowDegree ι r) (a : Vect ι) :
    (fun x => f x * (1 + fieldDot a x)) ∈ lowDegree ι (r+1) := by
  have hsum : (fun x => ∑ i, a i * (f x * x i)) ∈ lowDegree ι (r+1) := by
    have h := (lowDegree ι (r+1)).sum_mem (fun i (_ : i ∈ Finset.univ) =>
      (lowDegree ι (r+1)).smul_mem (a i) (mul_coord_mem_lowDegree hf i))
    convert h using 1
    funext x
    simp
  have h := (lowDegree ι (r+1)).add_mem (lowDegree_mono (Nat.le_succ r) hf) hsum
  convert h using 1
  funext x
  change f x * (1 + ∑ i, a i * x i) = f x + ∑ i, a i * (f x * x i)
  rw [mul_add, mul_one, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

noncomputable def cutPolynomial {r : ℕ} (a : Fin r → Vect ι) (x : Vect ι) : F2 :=
  ∏ i, (1 + fieldDot (a i) x)

lemma cutPolynomial_mem_lowDegree {r : ℕ} (a : Fin r → Vect ι) :
    cutPolynomial a ∈ lowDegree ι r := by
  induction r with
  | zero =>
    convert one_mem_lowDegree (ι := ι) 0 using 1
    funext x
    simp [cutPolynomial]
  | succ r ih =>
    have h := mul_affine_mem_lowDegree (ih (fun i => a i.succ)) (a 0)
    convert h using 1
    funext x
    simp [cutPolynomial, Fin.prod_univ_succ, mul_comm]

omit [DecidableEq ι] in
lemma cutPolynomial_eq_one {r : ℕ} (a : Fin r → Vect ι) (x : Vect ι)
    (hx : ∀ i, fieldDot (a i) x = 0) : cutPolynomial a x = 1 := by
  simp [cutPolynomial, hx]

omit [DecidableEq ι] in
lemma cutPolynomial_eq_zero {r : ℕ} (a : Fin r → Vect ι) (x : Vect ι)
    (hx : ∃ i, fieldDot (a i) x ≠ 0) : cutPolynomial a x = 0 := by
  classical
  obtain ⟨i, hi⟩ := hx
  have h1 : fieldDot (a i) x = 1 := (f2_cases _).resolve_left hi
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  rw [h1]
  rfl

omit [DecidableEq ι] in
lemma finrank_lowDegree_le (r : ℕ) :
    Module.finrank F2 (lowDegree ι r) ≤ Fintype.card (MonomialIndex ι r) := by
  exact finrank_range_le_card (R := F2) (fun S : MonomialIndex ι r => monomialFunction S.val)

theorem interpolation_card_bound (D : Finset (Vect ι)) (r : ℕ)
    (h : ∀ b ∈ D, ∃ a : Fin r → Vect ι,
      (∀ i, fieldDot (a i) b = 0) ∧
      ∀ x ∈ D, x ≠ b → ∃ i, fieldDot (a i) x ≠ 0) :
    D.card ≤ Fintype.card (MonomialIndex ι r) := by
  classical
  choose a ha hb using (fun b : D => h b.val b.property)
  let p : D → lowDegree ι r := fun b => ⟨cutPolynomial (a b), cutPolynomial_mem_lowDegree _⟩
  have he (b x : D) : (p b).val x.val = if x = b then 1 else 0 := by
    split_ifs with hx
    · subst x
      exact cutPolynomial_eq_one _ _ (ha b)
    · exact cutPolynomial_eq_zero _ _ (hb b x.val x.property (fun hh => hx (Subtype.ext hh)))
  have hi : LinearIndependent F2 p := by
    rw [Fintype.linearIndependent_iff]
    intro c hc b
    have hv := congrArg (fun q : lowDegree ι r => q.val b.val) hc
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, ZeroMemClass.coe_zero, Pi.zero_apply, he] at hv
    simpa using hv
  have hc := hi.fintype_card_le_finrank
  have hc' : D.card ≤ Module.finrank F2 (lowDegree ι r) := by simpa using hc
  exact hc'.trans (finrank_lowDegree_le r)

end Green51Proof

/- A weighted bound for the number of low degree multilinear monomials. -/

open scoped BigOperators

namespace Green51Proof

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma monomial_weight_sum (t : ℝ) :
    (∑ S : Finset ι, t ^ S.card) = (1+t)^Fintype.card ι := by
  have h := Fintype.prod_add (fun _ : ι => t) (fun _ : ι => (1 : ℝ))
  simpa [add_comm] using h.symm

lemma monomial_weight_bound (r : ℕ) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    (Fintype.card (MonomialIndex ι r) : ℝ) * t^r ≤ (1+t)^Fintype.card ι := by
  classical
  calc
    _ = ∑ _S : MonomialIndex ι r, t^r := by simp
    _ ≤ ∑ S : MonomialIndex ι r, t^S.val.card := by
      apply Finset.sum_le_sum
      intro S _
      exact pow_le_pow_of_le_one h0 h1 S.property
    _ ≤ ∑ S : Finset ι, t^S.card := by
      have h := Fintype.sum_subtype_add_sum_subtype
        (fun S : Finset ι => S.card ≤ r) (fun S => t^S.card)
      have hn : 0 ≤ ∑ S : {S : Finset ι // ¬ S.card ≤ r}, t^S.val.card :=
        Finset.sum_nonneg (fun _ _ => pow_nonneg h0 _)
      linarith
    _ = _ := monomial_weight_sum t

lemma monomial_count_bound (r : ℕ) (hN : 0 < Fintype.card ι)
    (hr : r ≤ Fintype.card ι) :
    (Fintype.card (MonomialIndex ι r) : ℝ) * ((r : ℝ)/Fintype.card ι)^r ≤
      (Real.exp 1)^r := by
  have hNR : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hN
  have hrR : (r : ℝ) ≤ Fintype.card ι := by exact_mod_cast hr
  have ht0 : 0 ≤ (r : ℝ)/Fintype.card ι := by positivity
  have ht1 : (r : ℝ)/Fintype.card ι ≤ 1 := (div_le_one hNR).2 hrR
  calc
    _ ≤ (1 + (r : ℝ)/Fintype.card ι)^Fintype.card ι := monomial_weight_bound r ht0 ht1
    _ ≤ (Real.exp ((r : ℝ)/Fintype.card ι))^Fintype.card ι :=
      pow_le_pow_left₀ (by positivity)
        (by simpa [add_comm] using (Real.add_one_le_exp ((r : ℝ)/Fintype.card ι))) _
    _ = (Real.exp 1)^r := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
      congr 1
      field_simp

theorem codimension_rounding_arithmetic (r : ℕ) (hN : 0 < Fintype.card ι)
    (hr : r ≤ Fintype.card ι) (δ : ℝ) (hδ : 0 ≤ δ)
    (h : 1 ≤ (Fintype.card (MonomialIndex ι r) : ℝ) * δ^r) :
    (r : ℝ) ≤ Real.exp 1 * Fintype.card ι * δ := by
  by_cases hr0 : r = 0
  · subst r
    simp only [Nat.cast_zero]
    positivity
  have hNR : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hN
  have hratio : 0 ≤ (r : ℝ)/Fintype.card ι := by positivity
  have hcount := monomial_count_bound r hN hr
  have hp : ((r : ℝ)/Fintype.card ι)^r ≤ (Real.exp 1 * δ)^r := by
    calc
      _ ≤ ((Fintype.card (MonomialIndex ι r) : ℝ) * δ^r) *
          ((r : ℝ)/Fintype.card ι)^r := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right h (pow_nonneg hratio r)
      _ = ((Fintype.card (MonomialIndex ι r) : ℝ) *
          ((r : ℝ)/Fintype.card ι)^r) * δ^r := by ring
      _ ≤ (Real.exp 1)^r * δ^r := mul_le_mul_of_nonneg_right hcount (pow_nonneg hδ r)
      _ = _ := (mul_pow _ _ _).symm
  have hrat := le_of_pow_le_pow_left₀ hr0 (mul_nonneg (Real.exp_pos 1).le hδ) hp
  have hh := (div_le_iff₀ hNR).mp hrat
  nlinarith

end Green51Proof

/- Critical obstructions and greedy covering by linear functionals. -/

open scoped BigOperators

namespace Green51Proof

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def Covered (D : Finset (Vect ι)) (r : ℕ) : Prop :=
  ∃ a : Fin r → Vect ι, ∀ x ∈ D, ∃ i, fieldDot (a i) x ≠ 0

noncomputable def remaining (D : Finset (Vect ι)) {r : ℕ} (a : Fin r → Vect ι) :
    Finset (Vect ι) := D.filter (fun x => ∀ i, fieldDot (a i) x = 0)

omit [DecidableEq ι] in
lemma remaining_subset (D : Finset (Vect ι)) {r : ℕ} (a : Fin r → Vect ι) :
    remaining D a ⊆ D := Finset.filter_subset _ _

omit [DecidableEq ι] in
lemma remaining_zero (D : Finset (Vect ι)) (a : Fin 0 → Vect ι) : remaining D a = D := by
  simp [remaining]

omit [DecidableEq ι] in
lemma remaining_cons (D : Finset (Vect ι)) {r : ℕ} (a : Vect ι) (b : Fin r → Vect ι) :
    remaining D (Fin.cons a b) = (remaining D b).filter (fun x => fieldDot a x = 0) := by
  classical
  ext x
  simp [remaining, Fin.forall_fin_succ, and_left_comm, and_comm]

omit [DecidableEq ι] in
lemma covered_of_remaining_empty (D : Finset (Vect ι)) {r : ℕ} (a : Fin r → Vect ι)
    (h : remaining D a = ∅) : Covered D r := by
  classical
  refine ⟨a, ?_⟩
  intro x hx
  by_contra hn
  have hzero : ∀ i, fieldDot (a i) x = 0 := by simpa using hn
  have hx' : x ∈ remaining D a := Finset.mem_filter.mpr ⟨hx, hzero⟩
  rw [h] at hx'
  exact Finset.notMem_empty x hx'

lemma remaining_nonempty_of_not_covered (D : Finset (Vect ι)) {r : ℕ}
    (h : ¬ Covered D r) (a : Fin r → Vect ι) : (remaining D a).Nonempty := by
  classical
  by_contra hn
  exact h (covered_of_remaining_empty D a (Finset.not_nonempty_iff_eq_empty.mp hn))

lemma fieldDot_single (i : ι) (x : Vect ι) : fieldDot (Pi.single i 1) x = x i := by
  classical
  change (∑ j, (Pi.single i 1 : Vect ι) j * x j) = x i
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [Pi.single_eq_of_ne hji]
  · simp

lemma covered_by_coordinates (D : Finset (Vect ι)) (h0 : (0 : Vect ι) ∉ D) :
    Covered D (Fintype.card ι) := by
  classical
  let e := Fintype.equivFin ι
  refine ⟨fun i => Pi.single (e.symm i) 1, ?_⟩
  intro x hx
  have hn : x ≠ 0 := fun hh => h0 (hh ▸ hx)
  have hex : ∃ j, x j ≠ 0 := by
    by_contra hh
    apply hn
    funext j
    simpa using not_exists.mp hh j
  obtain ⟨j, hj⟩ := hex
  refine ⟨e j, ?_⟩
  simpa only [Equiv.symm_apply_apply, fieldDot_single] using hj

theorem greedy_remaining_bound (B : Finset (Vect ι)) (δ : ℝ) (hδ : 0 ≤ δ)
    (hcut : ∀ D ⊆ B, ∃ a : Vect ι,
      ((D.filter (fun x => fieldDot a x = 0)).card : ℝ) ≤ δ * D.card)
    (D : Finset (Vect ι)) (hD : D ⊆ B) (r : ℕ) :
    ∃ a : Fin r → Vect ι, ((remaining D a).card : ℝ) ≤ δ^r * D.card := by
  classical
  induction r with
  | zero =>
    refine ⟨fun i => Fin.elim0 i, ?_⟩
    simp [remaining_zero]
  | succ r ih =>
    obtain ⟨a, ha⟩ := ih
    obtain ⟨b, hb⟩ := hcut (remaining D a) ((remaining_subset D a).trans hD)
    refine ⟨Fin.cons b a, ?_⟩
    rw [remaining_cons]
    calc
      _ ≤ δ * (remaining D a).card := hb
      _ ≤ δ * (δ^r * D.card) := mul_le_mul_of_nonneg_left ha hδ
      _ = _ := by rw [pow_succ]; ring

theorem critical_interpolation (B : Finset (Vect ι)) (r : ℕ) (hB : ¬ Covered B r) :
    ∃ D ⊆ B, (¬ Covered D r) ∧ D.card ≤ Fintype.card (MonomialIndex ι r) := by
  classical
  let S := B.powerset.filter (fun D => ¬ Covered D r)
  have hS : S.Nonempty := ⟨B, by simp [S, hB]⟩
  obtain ⟨D, hD, hmin⟩ := Finset.exists_min_image S Finset.card hS
  have hDB : D ⊆ B := Finset.mem_powerset.mp (Finset.mem_filter.mp hD).1
  have hnot : ¬ Covered D r := (Finset.mem_filter.mp hD).2
  refine ⟨D, hDB, hnot, interpolation_card_bound D r ?_⟩
  intro b hb
  have hsmall : Covered (D.erase b) r := by
    by_contra hn
    have hm := hmin (D.erase b) (by
      simp only [S, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨(Finset.erase_subset _ _).trans hDB, hn⟩)
    have hh := Finset.card_erase_lt_of_mem hb
    omega
  obtain ⟨a, ha⟩ := hsmall
  refine ⟨a, ?_, ?_⟩
  · intro i
    by_contra hi
    apply hnot
    refine ⟨a, ?_⟩
    intro x hx
    by_cases hxb : x = b
    · subst x
      exact ⟨i, hi⟩
    · exact ha x (Finset.mem_erase.mpr ⟨hxb, hx⟩)
  · intro x hx hxb
    exact ha x (Finset.mem_erase.mpr ⟨hxb, hx⟩)

theorem small_cover (B : Finset (Vect ι)) (h0 : (0 : Vect ι) ∉ B)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hcut : ∀ D ⊆ B, ∃ a : Vect ι,
      ((D.filter (fun x => fieldDot a x = 0)).card : ℝ) ≤ δ * D.card) :
    ∃ r : ℕ, Covered B r ∧ (r : ℝ) ≤ 1 + Real.exp 1 * Fintype.card ι * δ := by
  classical
  have hex : ∃ r, Covered B r := ⟨_, covered_by_coordinates B h0⟩
  let c := Nat.find hex
  have hc : Covered B c := Nat.find_spec hex
  have hcN : c ≤ Fintype.card ι := Nat.find_min' hex (covered_by_coordinates B h0)
  refine ⟨c, hc, ?_⟩
  by_cases hc0 : c = 0
  · rw [hc0, Nat.cast_zero]
    positivity
  obtain ⟨r, hcr⟩ := Nat.exists_eq_succ_of_ne_zero hc0
  have hrl : r < c := by omega
  have hrB : ¬ Covered B r := Nat.find_min hex hrl
  obtain ⟨D, hDB, hnot, hsize⟩ := critical_interpolation B r hrB
  obtain ⟨a, ha⟩ := greedy_remaining_bound B δ hδ hcut D hDB r
  have hn := remaining_nonempty_of_not_covered D hnot a
  have hncard : (1 : ℝ) ≤ (remaining D a).card := by exact_mod_cast hn.card_pos
  have hsizeR : (D.card : ℝ) ≤ Fintype.card (MonomialIndex ι r) := by exact_mod_cast hsize
  have hprod : 1 ≤ (Fintype.card (MonomialIndex ι r) : ℝ) * δ^r := by
    have hh := mul_le_mul_of_nonneg_left hsizeR (pow_nonneg hδ r)
    nlinarith
  have hN : 0 < Fintype.card ι := by omega
  have hrN : r ≤ Fintype.card ι := by omega
  have hrbound := codimension_rounding_arithmetic r hN hrN δ hδ hprod
  rw [hcr, Nat.cast_succ]
  linarith

end Green51Proof

/- A large linear subspace in a sumset of density near one half. -/

open scoped BigOperators Pointwise

namespace Green51Proof

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma independent_of_missing_sum (A : Finset (Vect ι)) (b : Vect ι)
    (hb : b ∉ A+A) : SumIndependent A b := by
  intro x hx hxb
  apply hb
  have he : x+(x+b) = b := by rw [← add_assoc, field_add_self, zero_add]
  exact Finset.mem_add.mpr ⟨x, hx, x+b, hxb, he⟩

lemma density_empty : density (∅ : Finset (Vect ι)) = 0 := by
  unfold density
  have h : indicator (∅ : Finset (Vect ι)) = fun _ => 0 := by
    funext x
    simp [indicator]
  rw [h, mean_const]

lemma nonempty_of_density_pos (A : Finset (Vect ι)) (h : 0 < density A) : A.Nonempty := by
  classical
  by_contra hn
  rw [Finset.not_nonempty_iff_eq_empty.mp hn, density_empty] at h
  exact lt_irrefl _ h

lemma zero_mem_sumset (A : Finset (Vect ι)) (hA : A.Nonempty) : (0 : Vect ι) ∈ A+A := by
  obtain ⟨a, ha⟩ := hA
  exact Finset.mem_add.mpr ⟨a, ha, a, ha, field_add_self a⟩

noncomputable def commonKernel {r : ℕ} (a : Fin r → Vect ι) : Submodule F2 (Vect ι) :=
  (LinearMap.pi (fun i => fieldDot (a i))).ker

omit [DecidableEq ι] in
lemma mem_commonKernel {r : ℕ} (a : Fin r → Vect ι) (x : Vect ι) :
    x ∈ commonKernel a ↔ ∀ i, fieldDot (a i) x = 0 := by
  simp [commonKernel, LinearMap.mem_ker, funext_iff]

omit [DecidableEq ι] in
lemma commonKernel_rank_bound {r : ℕ} (a : Fin r → Vect ι) :
    Fintype.card ι ≤ Module.finrank F2 (commonKernel a) + r := by
  let L : Vect ι →ₗ[F2] (Fin r → F2) := LinearMap.pi (fun i => fieldDot (a i))
  have he := L.finrank_range_add_finrank_ker
  have hr := Submodule.finrank_le L.range
  simp only [Module.finrank_pi, Fintype.card_fin] at he hr
  change Module.finrank F2 L.range + Module.finrank F2 (commonKernel a) = Fintype.card ι at he
  omega

omit [DecidableEq ι] in
lemma maxCosetDim_ge_submodule (S : Set (Vect ι)) (H : Submodule F2 (Vect ι))
    (hH : (H : Set (Vect ι)) ⊆ S) : Module.finrank F2 H ≤ maxCosetDim F2 (Vect ι) S := by
  unfold maxCosetDim
  apply le_csSup
  · refine ⟨Fintype.card ι, ?_⟩
    rintro m ⟨T, _, rfl⟩
    simpa only [Module.finrank_pi] using Submodule.finrank_le T.direction
  · refine ⟨H.toAffineSubspace, ?_, ?_⟩
    · exact hH
    · rw [Submodule.toAffineSubspace_direction]

theorem sumset_codimension_bound (A : Finset (Vect ι)) (ε : ℝ)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1/4) (hden : 1/2-ε ≤ density A) :
    ∃ r : ℕ, Fintype.card ι ≤ maxCosetDim F2 (Vect ι) ↑(A+A) + r ∧
      (r : ℝ) ≤ 1 + (256 * Real.exp 1) * Fintype.card ι * ε^2 := by
  classical
  let B : Finset (Vect ι) := (A+A)ᶜ
  have hpos : 0 < density A := by linarith
  have h0 : (0 : Vect ι) ∉ B := by
    simpa only [B, Finset.mem_compl, not_not] using zero_mem_sumset A (nonempty_of_density_pos A hpos)
  have hcut : ∀ D ⊆ B, ∃ a : Vect ι,
      ((D.filter (fun x => fieldDot a x = 0)).card : ℝ) ≤ (256*ε^2) * D.card := by
    intro D hD
    rcases D.eq_empty_or_nonempty with rfl | hn
    · exact ⟨0, by simp⟩
    · apply exists_good_cut A D hn
      · intro b hb
        exact independent_of_missing_sum A b (Finset.mem_compl.mp (hD hb))
      · exact hε
      · exact hε1
      · exact hden
  obtain ⟨r, ⟨a, ha⟩, hr⟩ := small_cover B h0 (256*ε^2) (by positivity) hcut
  have hker : (commonKernel a : Set (Vect ι)) ⊆ ↑(A+A) := by
    intro x hx
    by_contra hn
    have hxB : x ∈ B := Finset.mem_compl.mpr hn
    obtain ⟨i, hi⟩ := ha x hxB
    exact hi ((mem_commonKernel a x).mp hx i)
  have hdim := maxCosetDim_ge_submodule ↑(A+A) (commonKernel a) hker
  refine ⟨r, (commonKernel_rank_bound a).trans (Nat.add_le_add_right hdim r), ?_⟩
  nlinarith

end Green51Proof

/- The exact formal-conjectures target for Green's problem 51 at density one half. -/

open scoped BigOperators Pointwise

namespace Green51Proof

lemma density_eq_dens {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Finset (Vect ι)) :
    density A = (A.dens : ℝ) := by
  classical
  unfold density mean
  rw [Finset.expect_eq_sum_div_card]
  simp [indicator, Finset.dens]

lemma guaranteed_bound_of_uniform (n c : ℕ) (α : ℝ) (hα : α ≤ 1)
    (h : ∀ A : Finset (𝔽₂ n), (A.dens : ℝ) ≥ α →
      n ≤ maxCosetDim (ZMod 2) (𝔽₂ n) ↑(A+A) + c) :
    n ≤ Green51.guaranteedMaxCosetDim n α + c := by
  have hne : {maxCosetDim (ZMod 2) (𝔽₂ n) ↑(A+A) |
      (A : Finset (𝔽₂ n)) (_h : (A.dens : ℝ) ≥ α)}.Nonempty := by
    refine ⟨_, Finset.univ, ?_, rfl⟩
    simpa using hα
  have hl : n-c ≤ Green51.guaranteedMaxCosetDim n α := by
    unfold Green51.guaranteedMaxCosetDim
    apply le_csInf hne
    rintro _ ⟨A, hA, rfl⟩
    have hh := h A hA
    omega
  omega

theorem green_one_half :
    ∀ k : ℝ, 0 < k → ∃ c : ℕ, ∀ᶠ n : ℕ in Filter.atTop,
      ∀ α : ℝ, α > 1/2-k/Real.sqrt n → α ≤ 1 →
        n ≤ Green51.guaranteedMaxCosetDim n α + c := by
  intro k hk
  let K : ℝ := 256 * Real.exp 1
  let c : ℕ := ⌈1+K*k^2⌉₊
  refine ⟨c, Filter.eventually_atTop.mpr ⟨⌈16*k^2⌉₊+1, ?_⟩⟩
  intro n hn α hα hα1
  have hnR : 16*k^2 < (n : ℝ) := by
    have hceil := Nat.le_ceil (16*k^2)
    have hn' : (⌈16*k^2⌉₊ : ℝ)+1 ≤ n := by exact_mod_cast hn
    linarith
  have hnpos : (0 : ℝ) < n := by nlinarith [sq_nonneg k]
  have hspos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
  have hs0 : 0 ≤ Real.sqrt (n : ℝ) := hspos.le
  have hs2 : Real.sqrt (n : ℝ)^2 = n := Real.sq_sqrt hnpos.le
  have h4 : 4*k ≤ Real.sqrt (n : ℝ) := by
    apply (sq_le_sq₀ (show 0 ≤ 4*k by positivity) hs0).mp
    nlinarith
  let ε : ℝ := k/Real.sqrt n
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have hε1 : ε ≤ 1/4 := by
    dsimp [ε]
    apply (div_le_iff₀ hspos).mpr
    linarith
  have heq : (n : ℝ)*ε^2 = k^2 := by
    dsimp [ε]
    rw [div_pow, hs2]
    field_simp
  have hc : 1+K*k^2 ≤ (c : ℝ) := Nat.le_ceil _
  apply guaranteed_bound_of_uniform n c α hα1
  intro A hA
  have hden : 1/2-ε ≤ density A := by
    rw [density_eq_dens]
    exact hα.le.trans hA
  obtain ⟨r, hr, hb⟩ := sumset_codimension_bound A ε hε hε1 hden
  simp only [Fintype.card_fin] at hr hb
  have hb' : (r : ℝ) ≤ 1+K*k^2 := by
    calc
      _ ≤ 1+K*(n : ℝ)*ε^2 := hb
      _ = _ := by rw [mul_assoc K, heq]
  have hrc : r ≤ c := by exact_mod_cast hb'.trans hc
  exact hr.trans (Nat.add_le_add_left hrc _)

end Green51Proof


theorem target : fcTypeOfName% "Green51.green_51.one_half" := by
  exact ⟨fun _ => Green51Proof.green_one_half, fun _ => True.intro⟩

end Bounty
