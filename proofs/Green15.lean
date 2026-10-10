/-!
# Green 15: complete submission body

Paper authors: Jensen Kohlmeyer (jenwin@purdue.edu) and Liam Kruer (kruerl@purdue.edu).
AI acknowledgment: OpenAI Codex assisted with the construction, certificate,
proof development, Lean formalization, and manuscript preparation.

Upload this file unchanged for the formalized Green 15 challenge.
The validator supplies its trusted imports and enclosing Bounty namespace.

This file constructs a function from the natural numbers to the integers with
Lipschitz constant 125 and no nontrivial three-term progression in its graph.
The finite invariant is included below and checked by kernel reduction.
No external certificate, native evaluation, or additional axiom is needed.

Checked with Lean 4.33.1 and the challenge's FormalConjectures commit
8432eac998110a563e03df65a28c117e97c8c142.
-/

/- The six-letter substitution, integer weights, and endpoint tags. -/

abbrev Letter := Fin 6
abbrev Digit := Fin 4

def h (a : Letter) (r : Digit) : Letter :=
  ![![0,2,0,1], ![0,4,0,1], ![0,2,5,1],
    ![5,4,0,3], ![5,2,5,3], ![5,4,5,3]] a r

def weight (a : Letter) : ℤ := ![0,1,2,4,5,6] a
def tag (a : Letter) : ℤ := ![0,1,3,4,9,10] a
def bias (a : Letter) (r : Digit) : ℤ :=
  ![![0,-3,-4,-7], ![0,-3,-1,-4], ![0,-3,-4,-1],
    ![0,3,5,2], ![0,3,2,5], ![0,3,5,8]] a r

def letter (n : ℕ) : Letter :=
  if hn : n = 0 then 5 else h (letter (n / 4)) ⟨n % 4, Nat.mod_lt _ (by decide)⟩
termination_by n
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide)

def height (n : ℕ) : ℤ :=
  if hn : n = 0 then 0 else
    3 * height (n / 4) + bias (letter (n / 4)) ⟨n % 4, Nat.mod_lt _ (by decide)⟩
termination_by n
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide)

theorem letter_zero : letter 0 = 5 := by rw [letter]; rfl
theorem height_zero : height 0 = 0 := by rw [height]; rfl

theorem letter_rec (n : ℕ) :
    letter n = h (letter (n / 4)) ⟨n % 4, Nat.mod_lt _ (by decide)⟩ := by
  by_cases hn : n = 0
  · subst n; simp [letter_zero,h]
  · rw [letter]; simp [hn]

theorem height_rec (n : ℕ) :
    height n = 3 * height (n / 4) +
      bias (letter (n / 4)) ⟨n % 4, Nat.mod_lt _ (by decide)⟩ := by
  by_cases hn : n = 0
  · subst n; simp [height_zero,letter_zero,bias]
  · rw [height]; simp [hn]

theorem letter_block (n : ℕ) (r : Digit) :
    letter (4*n+r) = h (letter n) r := by
  rw [letter_rec]
  have hq : (4*n+r.val)/4 = n := by omega
  have hr : (4*n+r.val)%4 = r.val := by omega
  simp only [hq, hr]

theorem height_block (n : ℕ) (r : Digit) :
    height (4*n+r) = 3 * height n + bias (letter n) r := by
  rw [height_rec]
  have hq : (4*n+r.val)/4 = n := by omega
  have hr : (4*n+r.val)%4 = r.val := by omega
  simp only [hq, hr]

theorem bias_bounds : ∀ a r, -7 ≤ bias a r ∧ bias a r ≤ 8 := by decide
theorem tag_bounds : ∀ a, 0 ≤ tag a ∧ tag a ≤ 10 := by decide
theorem weight_bounds : ∀ a, 0 ≤ weight a ∧ weight a ≤ 6 := by decide
theorem tag_ap : ∀ a b c, tag a - 2 * tag b + tag c = 0 → a = b ∧ b = c := by
  decide

/- The explicit function has every adjacent increment between 1 and 125. -/

theorem bias_zero : ∀ a, bias a 0 = 0 := by decide
theorem bias_step : ∀ a (r : Fin 3),
    bias a ⟨r.val+1, by omega⟩ - bias a ⟨r.val, by omega⟩ =
      weight (h a ⟨r.val, by omega⟩) - 3 := by decide
theorem bias_last : ∀ a,
    3 * (weight a - 3) - bias a 3 = weight (h a 3) - 3 := by decide

theorem height_succ (n : ℕ) : height (n+1) - height n = weight (letter n) - 3 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    let q := n / 4
    let r := n % 4
    have hr : r < 4 := Nat.mod_lt _ (by decide)
    have hn : n = 4*q+r := by dsimp [q,r]; omega
    have hN : height n = 3*height q + bias (letter q) ⟨r,hr⟩ := by
      simpa only [← hn] using height_block q ⟨r,hr⟩
    have lN : letter n = h (letter q) ⟨r,hr⟩ := by
      simpa only [← hn] using letter_block q ⟨r,hr⟩
    by_cases hlast : r = 3
    · have hn' : n+1 = 4*(q+1)+(0 : Digit).val := by simp only [Fin.val_zero]; omega
      have ihq := ih q (by dsimp [q]; omega)
      rw [hN, lN, hn', height_block, bias_zero]
      simp only [hlast] at *
      change 3*height (q+1)+0-(3*height q+bias (letter q) 3) =
        weight (h (letter q) 3)-3
      have ht := bias_last (letter q)
      linarith
    · have hr3 : r < 3 := by omega
      have hn' : n+1 = 4*q+(⟨r+1, by omega⟩ : Digit).val := by simp only; omega
      rw [hN, lN, hn', height_block]
      have ht := bias_step (letter q) ⟨r,hr3⟩
      dsimp only at ht
      linarith

def f (n : ℕ) : ℤ := 21 * (height n + 3*n) + tag (letter n) - 10

theorem f_zero : f 0 = 0 := by simp [f,height_zero,letter_zero,tag]

def incrementSet : Finset ℤ := {1,3,4,9,20,30,39,49,80,90,96,106,117,119,120,125}

theorem f_succ (n : ℕ) :
    f (n+1) - f n = 21 * weight (letter n) + tag (letter (n+1)) - tag (letter n) := by
  have ht := height_succ n
  simp only [f, Nat.cast_add, Nat.cast_one]
  linarith

theorem finite_step_bounds : ∀ (a b : Letter) (r s : Digit),
    s.val = (r.val+1)%4 →
    1 ≤ 21*weight (h a r)+tag (h b s)-tag (h a r) ∧
      21*weight (h a r)+tag (h b s)-tag (h a r) ≤ 125 := by decide

theorem f_step_bounds (n : ℕ) : 1 ≤ f (n+1)-f n ∧ f (n+1)-f n ≤ 125 := by
  rw [f_succ]
  have hb := finite_step_bounds (letter (n/4)) (letter ((n+1)/4))
    ⟨n%4, Nat.mod_lt _ (by decide)⟩ ⟨(n+1)%4, Nat.mod_lt _ (by decide)⟩ (by dsimp; omega)
  simpa only [← letter_rec] using hb

theorem finite_increment_mem : ∀ (a b : Letter) (r s : Digit),
    s.val = (r.val+1)%4 →
    21*weight (h a r)+tag (h b s)-tag (h a r) ∈ incrementSet := by decide +kernel

theorem f_increment_mem (n : ℕ) : f (n+1)-f n ∈ incrementSet := by
  rw [f_succ]
  have hb := finite_increment_mem (letter (n/4)) (letter ((n+1)/4))
    ⟨n%4, Nat.mod_lt _ (by decide)⟩ ⟨(n+1)%4, Nat.mod_lt _ (by decide)⟩ (by dsimp; omega)
  simpa only [← letter_rec] using hb

theorem f_strictMono : StrictMono f := by
  apply strictMono_nat_of_lt_succ
  intro n
  have hb := f_step_bounds n
  omega

theorem f_step_dist (n : ℕ) : dist (f n) (f (n+1)) ≤ 125 := by
  have hb : -(125 : ℤ) ≤ f (n+1)-f n ∧ f (n+1)-f n ≤ 125 := by
    have ht := f_step_bounds n
    omega
  rw [dist_comm, Int.dist_eq']
  exact_mod_cast (abs_le.mpr hb)

theorem f_lipschitz : LipschitzWith 125 f := by
  apply LipschitzWith.of_dist_le_mul
  intro m n
  wlog hmn : m ≤ n generalizing m n
  · rw [dist_comm (f m), dist_comm m]
    exact this n m (by omega)
  have hb : dist (f m) (f n) ≤ ∑ _i ∈ Finset.Ico m n, (125 : ℝ) :=
    dist_le_Ico_sum_of_dist_le hmn (fun {_} _ _ => f_step_dist _)
  have hc : (m : ℝ) ≤ n := by exact_mod_cast hmn
  simpa [Nat.dist_eq, abs_of_nonpos (sub_nonpos.mpr hc),
    Nat.cast_sub hmn, mul_comm, sub_mul] using hb

/- Finite certificate. For letters a,b,c and error A in [-1,1], row
   (36*a + 6*b + c)*3 + (A+1) has bit D+15 set precisely for the accepted
   unequal states. Equal-index states are handled by the other Boolean branch.
   The table is data, not an assumption: checkAll0 through checkAll5 verify
   every retained transition by reduction in Lean's kernel. -/

def masks : Array Nat := #[
  0, 2147450879, 0, 920350134, 0, 1533916891, 920350134, 0, 1840700269,
  920350134, 0, 1533916891, 920350134, 0, 1840700269, 0, 2147483647, 0,
  0, 306783378, 0, 1227133513, 0, 306783378, 613566756, 0, 306783378,
  1227133513, 0, 306783378, 613566756, 0, 306783378, 0, 306783378, 0,
  0, 613566756, 0, 306783378, 0, 613566756, 1227133513, 0, 613566756,
  306783378, 0, 613566756, 1227133513, 0, 613566756, 0, 613566756, 0,
  0, 306783378, 0, 1227133513, 0, 306783378, 613566756, 0, 306783378,
  1227133513, 0, 306783378, 613566756, 0, 306783378, 0, 306783378, 0,
  0, 613566756, 0, 306783378, 0, 613566756, 1227133513, 0, 613566756,
  306783378, 0, 613566756, 1227133513, 0, 613566756, 0, 613566756, 0,
  0, 2147483647, 0, 920350134, 0, 1533916891, 920350134, 0, 1840700269,
  920350134, 0, 1533916891, 920350134, 0, 1840700269, 0, 2147483647, 0,
  920350134, 0, 1533916891, 0, 0, 0, 0, 920350134, 0,
  0, 0, 0, 0, 920350134, 0, 920350134, 0, 1533916891,
  1227133513, 0, 306783378, 0, 1227100745, 0, 0, 0, 0,
  0, 1227133513, 0, 0, 0, 0, 1227133513, 0, 306783378,
  306783378, 0, 613566756, 0, 306783378, 0, 0, 0, 0,
  0, 306783378, 0, 0, 0, 0, 306783378, 0, 613566756,
  1227133513, 0, 306783378, 0, 1227133513, 0, 0, 0, 0,
  0, 1227133513, 0, 0, 0, 0, 1227133513, 0, 306783378,
  306783378, 0, 613566756, 0, 306783378, 0, 0, 0, 0,
  0, 306783378, 0, 0, 0, 0, 306783378, 0, 613566756,
  920350134, 0, 1533916891, 0, 0, 0, 0, 920350134, 0,
  0, 0, 0, 0, 920350134, 0, 920350134, 0, 1533916891,
  920350134, 0, 1840700269, 0, 920350134, 0, 0, 0, 0,
  0, 920350134, 0, 0, 0, 0, 920350134, 0, 1840700269,
  613566756, 0, 306783378, 0, 0, 0, 0, 613566756, 0,
  0, 0, 0, 0, 613566756, 0, 613566756, 0, 306783378,
  1227133513, 0, 613566756, 0, 0, 0, 0, 1227100745, 0,
  0, 0, 0, 0, 1227133513, 0, 1227133513, 0, 613566756,
  613566756, 0, 306783378, 0, 0, 0, 0, 613566756, 0,
  0, 0, 0, 0, 613566756, 0, 613566756, 0, 306783378,
  1227133513, 0, 613566756, 0, 0, 0, 0, 1227133513, 0,
  0, 0, 0, 0, 1227133513, 0, 1227133513, 0, 613566756,
  920350134, 0, 1840700269, 0, 920350134, 0, 0, 0, 0,
  0, 920350134, 0, 0, 0, 0, 920350134, 0, 1840700269,
  920350134, 0, 1533916891, 0, 0, 0, 0, 920350134, 0,
  0, 0, 0, 0, 920350134, 0, 920350134, 0, 1533916891,
  1227133513, 0, 306783378, 0, 1227133513, 0, 0, 0, 0,
  0, 1227133513, 0, 0, 0, 0, 1227133513, 0, 306783378,
  306783378, 0, 613566756, 0, 306783378, 0, 0, 0, 0,
  0, 306783378, 0, 0, 0, 0, 306783378, 0, 613566756,
  1227133513, 0, 306783378, 0, 1227133513, 0, 0, 0, 0,
  0, 1227100745, 0, 0, 0, 0, 1227133513, 0, 306783378,
  306783378, 0, 613566756, 0, 306783378, 0, 0, 0, 0,
  0, 306783378, 0, 0, 0, 0, 306783378, 0, 613566756,
  920350134, 0, 1533916891, 0, 0, 0, 0, 920350134, 0,
  0, 0, 0, 0, 920350134, 0, 920350134, 0, 1533916891,
  920350134, 0, 1840700269, 0, 920350134, 0, 0, 0, 0,
  0, 920350134, 0, 0, 0, 0, 920350134, 0, 1840700269,
  613566756, 0, 306783378, 0, 0, 0, 0, 613566756, 0,
  0, 0, 0, 0, 613566756, 0, 613566756, 0, 306783378,
  1227133513, 0, 613566756, 0, 0, 0, 0, 1227133513, 0,
  0, 0, 0, 0, 1227133513, 0, 1227133513, 0, 613566756,
  613566756, 0, 306783378, 0, 0, 0, 0, 613566756, 0,
  0, 0, 0, 0, 613566756, 0, 613566756, 0, 306783378,
  1227133513, 0, 613566756, 0, 0, 0, 0, 1227133513, 0,
  0, 0, 0, 0, 1227100745, 0, 1227133513, 0, 613566756,
  920350134, 0, 1840700269, 0, 920350134, 0, 0, 0, 0,
  0, 920350134, 0, 0, 0, 0, 920350134, 0, 1840700269,
  0, 2147483647, 0, 920350134, 0, 1533916891, 920350134, 0, 1840700269,
  920350134, 0, 1533916891, 920350134, 0, 1840700269, 0, 2147483647, 0,
  0, 306783378, 0, 1227133513, 0, 306783378, 613566756, 0, 306783378,
  1227133513, 0, 306783378, 613566756, 0, 306783378, 0, 306783378, 0,
  0, 613566756, 0, 306783378, 0, 613566756, 1227133513, 0, 613566756,
  306783378, 0, 613566756, 1227133513, 0, 613566756, 0, 613566756, 0,
  0, 306783378, 0, 1227133513, 0, 306783378, 613566756, 0, 306783378,
  1227133513, 0, 306783378, 613566756, 0, 306783378, 0, 306783378, 0,
  0, 613566756, 0, 306783378, 0, 613566756, 1227133513, 0, 613566756,
  306783378, 0, 613566756, 1227133513, 0, 613566756, 0, 613566756, 0,
  0, 2147483647, 0, 920350134, 0, 1533916891, 920350134, 0, 1840700269,
  920350134, 0, 1533916891, 920350134, 0, 1840700269, 0, 2147450879, 0]

def accepted (a b c : Letter) (A D : ℤ) (e : Bool) : Bool :=
  if e then
    (masks[(a.val*36+b.val*6+c.val)*3+(A+1).toNat]!).testBit (D+15).toNat
  else a == b && b == c && A == 0 && D == 0

def stepCheck (a : Letter) : Prop :=
  ∀ (b c : Letter) (p : Fin 3) (q : Fin 31) (e : Bool) (x y z : Digit),
    let A : ℤ := (p : ℕ) - 1
    let D : ℤ := (q : ℕ) - 15
    let A' : ℤ := 4*A + x.val - 2*y.val + z.val
    let D' : ℤ := 3*D + bias a x - 2*bias b y + bias c z
    accepted a b c A D e = true →
    -1 ≤ A' ∧ A' ≤ 1 → -15 ≤ D' ∧ D' ≤ 15 →
    accepted (h a x) (h b y) (h c z) A' D'
      (e || !(x == y && y == z)) = true

def allFin (n : ℕ) (p : Fin n → Bool) : Bool := (List.finRange n).all p

theorem allFin_iff (n : ℕ) (p : Fin n → Bool) :
    allFin n p = true ↔ ∀ x, p x = true := by simp [allFin, List.all_eq_true]

def checkState (a b c : Letter) (p : Fin 3) (q : Fin 31) (e : Bool) : Bool :=
  let A : ℤ := (p : ℕ) - 1
  let D : ℤ := (q : ℕ) - 15
  if accepted a b c A D e then
    allFin 4 fun x => allFin 4 fun y => allFin 4 fun z =>
      let A' : ℤ := 4*A + x.val - 2*y.val + z.val
      let D' : ℤ := 3*D + bias a x - 2*bias b y + bias c z
      if (-1 ≤ A' ∧ A' ≤ 1) ∧ (-15 ≤ D' ∧ D' ≤ 15) then
        accepted (h a x) (h b y) (h c z) A' D' (e || !(x == y && y == z))
      else true
  else true

def checkAll (a : Letter) : Bool :=
  allFin 6 fun b => allFin 6 fun c => allFin 3 fun p => allFin 31 fun q =>
    checkState a b c p q false && checkState a b c p q true

theorem checkAll_sound (a : Letter) (hc : checkAll a = true) : stepCheck a := by
  simp only [checkAll, allFin_iff, Bool.and_eq_true] at hc
  intro b c p q e x y z
  dsimp only
  intro hi hA hD
  have ht : checkState a b c p q e = true := by
    cases e
    · exact (hc b c p q).1
    · exact (hc b c p q).2
  simp only [checkState, hi, if_true, allFin_iff] at ht
  have ht' := ht x y z
  simpa only [if_pos (And.intro hA hD)] using ht'

theorem checkAll0 : checkAll 0 = true := by decide +kernel
theorem stepCheck0 : stepCheck 0 := checkAll_sound 0 checkAll0

theorem checkAll1 : checkAll 1 = true := by decide +kernel
theorem checkAll2 : checkAll 2 = true := by decide +kernel
theorem checkAll3 : checkAll 3 = true := by decide +kernel
theorem checkAll4 : checkAll 4 = true := by decide +kernel
theorem checkAll5 : checkAll 5 = true := by decide +kernel

theorem stepCheck_all (a : Letter) : stepCheck a := by
  apply checkAll_sound
  fin_cases a
  · exact checkAll0
  · exact checkAll1
  · exact checkAll2
  · exact checkAll3
  · exact checkAll4
  · exact checkAll5

theorem accepted_initial : accepted 5 5 5 0 0 false = true := by decide
theorem accepted_forbidden : ∀ a, accepted a a a 0 0 true = false := by decide +kernel

theorem accepted_step (a b c : Letter) (A D : ℤ) (e : Bool) (x y z : Digit)
    (hA : -1 ≤ A ∧ A ≤ 1) (hD : -15 ≤ D ∧ D ≤ 15)
    (hi : accepted a b c A D e = true)
    (hA' : -1 ≤ 4*A+x.val-2*y.val+z.val ∧ 4*A+x.val-2*y.val+z.val ≤ 1)
    (hD' : -15 ≤ 3*D+bias a x-2*bias b y+bias c z ∧
      3*D+bias a x-2*bias b y+bias c z ≤ 15) :
    accepted (h a x) (h b y) (h c z)
      (4*A+x.val-2*y.val+z.val) (3*D+bias a x-2*bias b y+bias c z)
      (e || !(x == y && y == z)) = true := by
  let p : Fin 3 := ⟨(A+1).toNat, by omega⟩
  let q : Fin 31 := ⟨(D+15).toNat, by omega⟩
  have hp : ((p : ℕ) : ℤ)-1 = A := by dsimp [p]; omega
  have hq : ((q : ℕ) : ℤ)-15 = D := by dsimp [q]; omega
  have ht := stepCheck_all a b c p q e x y z
  dsimp only at ht
  rw [hp,hq] at ht
  exact ht hi hA' hD'

/- The bounds are preserved when all three indices are divided by four.
   Strong induction therefore puts every bounded-error triple in the invariant. -/

def indexError (i j k : ℕ) : ℤ := (i : ℤ) - 2*j + k
def heightError (i j k : ℕ) : ℤ := height i - 2*height j + height k
def unequal (i j k : ℕ) : Bool := !(i == j && j == k)

theorem unequal_rec (i j k : ℕ) :
    unequal i j k = (unequal (i/4) (j/4) (k/4) ||
      !(i%4 == j%4 && j%4 == k%4)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [unequal, Bool.not_eq_true', Bool.and_eq_false_iff, beq_eq_false_iff_ne,
    Bool.or_eq_true]
  omega

theorem invariant_descent
    (R : Letter → Letter → Letter → ℤ → ℤ → Bool → Bool)
    (hb : R 5 5 5 0 0 false = true)
    (hs : ∀ (a b c : Letter) (A D : ℤ) (e : Bool) (x y z : Digit),
      -1 ≤ A ∧ A ≤ 1 → -15 ≤ D ∧ D ≤ 15 → R a b c A D e = true →
      -1 ≤ 4*A+x.val-2*y.val+z.val ∧ 4*A+x.val-2*y.val+z.val ≤ 1 →
      -15 ≤ 3*D+bias a x-2*bias b y+bias c z ∧
        3*D+bias a x-2*bias b y+bias c z ≤ 15 →
      R (h a x) (h b y) (h c z)
        (4*A+x.val-2*y.val+z.val) (3*D+bias a x-2*bias b y+bias c z)
        (e || !(x == y && y == z)) = true)
    (i j k : ℕ) (hA : -1 ≤ indexError i j k ∧ indexError i j k ≤ 1)
    (hD : -15 ≤ heightError i j k ∧ heightError i j k ≤ 15) :
    R (letter i) (letter j) (letter k) (indexError i j k) (heightError i j k)
      (unequal i j k) = true := by
  generalize ht : i+j+k = t
  induction t using Nat.strong_induction_on generalizing i j k with
  | h t ih =>
    by_cases hz : i+j+k = 0
    · have hi : i = 0 := by omega
      have hj : j = 0 := by omega
      have hk : k = 0 := by omega
      subst i; subst j; subst k
      simpa [indexError,heightError,unequal,letter_zero,height_zero] using hb
    · let x : Digit := ⟨i%4, Nat.mod_lt _ (by decide)⟩
      let y : Digit := ⟨j%4, Nat.mod_lt _ (by decide)⟩
      let z : Digit := ⟨k%4, Nat.mod_lt _ (by decide)⟩
      have eqA : indexError i j k =
          4*indexError (i/4) (j/4) (k/4)+x.val-2*y.val+z.val := by
        dsimp [indexError,x,y,z]
        omega
      have eqD : heightError i j k =
          3*heightError (i/4) (j/4) (k/4)+
            bias (letter (i/4)) x-2*bias (letter (j/4)) y+bias (letter (k/4)) z := by
        dsimp only [heightError]
        rw [height_rec i, height_rec j, height_rec k]
        dsimp only [x,y,z]
        ring
      have hAp : -1 ≤ indexError (i/4) (j/4) (k/4) ∧
          indexError (i/4) (j/4) (k/4) ≤ 1 := by
        have hx := x.isLt
        have hy := y.isLt
        have hz' := z.isLt
        omega
      have hDp : -15 ≤ heightError (i/4) (j/4) (k/4) ∧
          heightError (i/4) (j/4) (k/4) ≤ 15 := by
        have hx := bias_bounds (letter (i/4)) x
        have hy := bias_bounds (letter (j/4)) y
        have hz' := bias_bounds (letter (k/4)) z
        omega
      have hsmall : i/4+j/4+k/4 < t := by omega
      have hp := ih _ hsmall (i/4) (j/4) (k/4) hAp hDp rfl
      have hv := hs (letter (i/4)) (letter (j/4)) (letter (k/4))
        (indexError (i/4) (j/4) (k/4)) (heightError (i/4) (j/4) (k/4))
        (unequal (i/4) (j/4) (k/4)) x y z hAp hDp hp
        (eqA ▸ hA) (eqD ▸ hD)
      have he : unequal i j k = (unequal (i/4) (j/4) (k/4) ||
          !(x == y && y == z)) := by
        have hxy : (x == y) = (i%4 == j%4) := by
          apply Bool.eq_iff_iff.mpr
          simp [x,y,Fin.ext_iff]
        have hyz : (y == z) = (j%4 == k%4) := by
          apply Bool.eq_iff_iff.mpr
          simp [y,z,Fin.ext_iff]
        rw [hxy,hyz]
        exact unequal_rec i j k
      rw [← eqA, ← eqD, ← he] at hv
      simpa only [x,y,z,← letter_rec] using hv

/- Convert the midpoint criterion into Set.IsAPOfLengthFree. -/

theorem graph_free_of_midpoint (g : ℕ → ℤ)
    (hg : ∀ i j k, indexError i j k = 0 → g i - 2*g j + g k = 0 → i = j) :
    Set.IsAPOfLengthFree {((n,g n) : ℤ × ℤ) | (n : ℕ)} 3 := by
  intro t ht ⟨a,d,hcard,heq⟩
  have h0 : a ∈ t := by
    rw [heq]
    exact ⟨0, by norm_num, by simp⟩
  have h1 : a+d ∈ t := by
    rw [heq]
    exact ⟨1, by norm_num, by simp⟩
  have h2 : a+2 • d ∈ t := by
    rw [heq]
    exact ⟨2, by norm_num, by simp⟩
  obtain ⟨i,hi⟩ := ht h0
  obtain ⟨j,hj⟩ := ht h1
  obtain ⟨k,hk⟩ := ht h2
  have hi1 := congrArg Prod.fst hi
  have hj1 := congrArg Prod.fst hj
  have hk1 := congrArg Prod.fst hk
  have hi2 := congrArg Prod.snd hi
  have hj2 := congrArg Prod.snd hj
  have hk2 := congrArg Prod.snd hk
  simp only [two_smul, Prod.fst_add, Prod.snd_add] at hi1 hj1 hk1 hi2 hj2 hk2
  have hij : i = j := hg i j k (by dsimp [indexError]; linarith) (by linarith)
  have ha : a = a+d := by rw [← hj,← hi,hij]
  have hd : d = 0 := add_left_cancel (show a+d = a+0 by simpa using ha.symm)
  have hs : t = {a} := by
    rw [heq,hd]
    ext x
    constructor
    · rintro ⟨n,hn,hx⟩
      simpa using hx.symm
    · intro hx
      change x = a at hx
      exact ⟨0, by norm_num, by simpa using hx.symm⟩
  rw [hs] at hcard
  norm_num at hcard

/- Multiplication by 21 separates the height difference from the tags.
   The tag difference lies in [-20,20]; equality forces identical endpoint
   letters, which the invariant forbids for a nontrivial progression. -/

theorem no_boundary (i j k : ℕ)
    (hA : indexError i j k = 0) (hD : heightError i j k = 0)
    (hab : letter i = letter j) (hbc : letter j = letter k) : i = j := by
  have hv := invariant_descent accepted accepted_initial accepted_step i j k
    (by omega) (by omega)
  by_contra hij
  have he : unequal i j k = true := by simp [unequal,hij]
  rw [hA,hD,hab,hbc,he,accepted_forbidden] at hv
  contradiction

theorem no_midpoint (i j k : ℕ) (hA : indexError i j k = 0)
    (hf : f i - 2*f j + f k = 0) : i = j := by
  have hi := tag_bounds (letter i)
  have hj := tag_bounds (letter j)
  have hk := tag_bounds (letter k)
  have he : 21*heightError i j k +
      (tag (letter i)-2*tag (letter j)+tag (letter k)) = 0 := by
    dsimp [f] at hf
    dsimp [indexError] at hA
    dsimp [heightError]
    linarith
  have hD : heightError i j k = 0 := by omega
  have htag : tag (letter i)-2*tag (letter j)+tag (letter k) = 0 := by omega
  obtain ⟨hab,hbc⟩ := tag_ap (letter i) (letter j) (letter k) htag
  exact no_boundary i j k hA hD hab hbc

theorem f_graph_free :
    Set.IsAPOfLengthFree {((n,f n) : ℤ × ℤ) | (n : ℕ)} 3 :=
  graph_free_of_midpoint f no_midpoint

theorem main_result : f 0 = 0 ∧ StrictMono f ∧
    (∀ n, f (n+1)-f n ∈ incrementSet) ∧ LipschitzWith 125 f ∧
    Set.IsAPOfLengthFree {((n,f n) : ℤ × ℤ) | (n : ℕ)} 3 :=
  ⟨f_zero,f_strictMono,f_increment_mem,f_lipschitz,f_graph_free⟩

theorem target : fcTypeOfName% "Green15.green_15" := by
  constructor
  · intro _
    exact ⟨125, f, f_lipschitz, f_graph_free⟩
  · intro _
    trivial
