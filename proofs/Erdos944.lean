import FormalConjectures.ErdosProblems.«944»
import TaskSupport

/-!
# A formalized construction criterion for Erdős problem 944

The arguments use cyclic three-colorings, counts of monochromatic edges, and
the criticality definitions from the pinned challenge.

This file proves the full displayed challenge in `Bounty.target` for every
k >= 4 and every r >= 1. The existence lemmas also cover r = 0 and arbitrary
target universes. All supporting arguments are in this file.

The four-color construction uses cyclic colorings, CRT parameters, and an
integer character argument. For k >= 5, the construction and local structure
follow Skottova and Steiner, arXiv:2508.08703v1, with the paired-ring and
overlapping-window counting arguments given below. The parameters are
m = 18*r + 3 for k >= 6 and m = 18*r + 20 for k = 5.

Authors of the accompanying manuscript: Liam Kruer and Jensen Kohlmeyer.
OpenAI Codex assisted with proof development and Lean formalization.
-/

namespace Bounty
namespace Erdos944Proof

/-- Allowed differences in a punctured cyclic three-coloring. -/
def NormalDifference (n s : Nat) : Prop :=
  s = 1 ∨ s = n - 1 ∨ s % 3 = 2

theorem normalDifference_ne_color
    {n x y s : Nat} (hn : n % 3 = 1)
    (hx : 0 < x) (hxn : x < n) (hy : 0 < y) (hyn : y < n)
    (hs : NormalDifference n s) (hxy : y = x + s ∨ y + n = x + s) :
    x % 3 ≠ y % 3 := by
  rcases hs with hs | hs | hs <;> rcases hxy with hxy | hxy <;> omega

theorem normalDifference_neg {n s : Nat} (hn : n % 3 = 1)
    (_hs0 : 0 < s) (hsn : s < n) (hs : NormalDifference n s) :
    NormalDifference n (n - s) := by
  rcases hs with hs | hs | hs
  · exact Or.inr (Or.inl (by omega))
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inr (by omega))

/-- The largest odd lift in {-1,1,3} of the color difference modulo three. -/
def maxStep (a b : Fin 3) : Int :=
  if a = b then 3 else if ((b.val : Int) - a.val) % 3 = 1 then 1 else -1

theorem maxStep_cases (a b : Fin 3) :
    maxStep a b = 3 ∨ maxStep a b = 1 ∨ maxStep a b = -1 := by
  unfold maxStep
  split <;> simp_all
  split <;> simp_all

theorem maxStep_eq_three (a : Fin 3) : maxStep a a = 3 := by
  simp [maxStep]

theorem maxStep_of_ne {a b : Fin 3} (h : a ≠ b) :
    maxStep a b = 1 ∨ maxStep a b = -1 := by
  simp only [maxStep, if_neg h]
  split <;> simp

theorem maxStep_mod_three (a b : Fin 3) :
    maxStep a b % 3 = ((b.val : Int) - a.val) % 3 := by
  have ha := a.isLt
  have hb := b.isLt
  by_cases hab : a = b
  · subst b
    simp [maxStep]
  · have hv : a.val ≠ b.val := fun h => hab (Fin.ext h)
    unfold maxStep
    simp only [if_neg hab]
    split <;> omega

theorem maxStep_reverse {a b : Fin 3} (h : a ≠ b) :
    maxStep a b + maxStep b a = 0 := by
  have h₁ := maxStep_of_ne h
  have h₂ := maxStep_of_ne (Ne.symm h)
  have h₃ := maxStep_mod_three a b
  have h₄ := maxStep_mod_three b a
  omega

theorem proper_square_sum_zero {a b c d : Fin 3}
    (hab : a ≠ b) (hbc : b ≠ c) (hcd : c ≠ d) (hda : d ≠ a) :
    maxStep a b + maxStep b c + maxStep c d + maxStep d a = 0 := by
  have h₁ := maxStep_of_ne hab
  have h₂ := maxStep_of_ne hbc
  have h₃ := maxStep_of_ne hcd
  have h₄ := maxStep_of_ne hda
  have m₁ := maxStep_mod_three a b
  have m₂ := maxStep_mod_three b c
  have m₃ := maxStep_mod_three c d
  have m₄ := maxStep_mod_three d a
  omega

theorem four_step_shortcut {a b c d : Fin 3}
    (hab : a ≠ b) (hbc : b ≠ c) (hcd : c ≠ d) :
    3 + maxStep a b + maxStep b c + maxStep c d - maxStep a d ≤ 3 := by
  have h₁ := maxStep_of_ne hab
  have h₂ := maxStep_of_ne hbc
  have h₃ := maxStep_of_ne hcd
  have h₄ := maxStep_cases a d
  have m₁ := maxStep_mod_three a b
  have m₂ := maxStep_mod_three b c
  have m₃ := maxStep_mod_three c d
  have m₄ := maxStep_mod_three a d
  omega

/-- A discrete antiderivative, with value zero at the initial vertex. -/
def partialSum (f : Nat → Int) : Nat → Int
  | 0 => 0
  | n + 1 => partialSum f n + f n

theorem prefix_add (f g : Nat → Int) (n : Nat) :
    partialSum (fun j => f j + g j) n = partialSum f n + partialSum g n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [partialSum, ih]; omega

theorem prefix_const (a : Int) (n : Nat) :
    partialSum (fun _ => a) n = (n : Int) * a := by
  induction n with
  | zero => simp [partialSum]
  | succ n ih => simp [partialSum, ih, Int.add_mul]

theorem prefix_mod_three (c : Nat → Fin 3) (f : Nat → Int)
    (hf : ∀ j, f j % 3 = ((c (j + 1)).val - (c j).val : Int) % 3) (n : Nat) :
    partialSum f n % 3 = ((c n).val - (c 0).val : Int) % 3 := by
  induction n with
  | zero => simp [partialSum]
  | succ n ih => have hj := hf n; simp only [partialSum]; omega

theorem prefix_mod_two (f : Nat → Int) (hf : ∀ j, f j % 2 = 1) (n : Nat) :
    partialSum f n % 2 = (n : Int) % 2 := by
  induction n with
  | zero => simp [partialSum]
  | succ n ih => have hj := hf n; simp only [partialSum]; omega

theorem cycle_flux_mod_six (c : Nat → Fin 3) (f : Nat → Int)
    (hf₃ : ∀ j, f j % 3 = ((c (j + 1)).val - (c j).val : Int) % 3)
    (hf₂ : ∀ j, f j % 2 = 1) {n : Nat} (hn : c n = c 0) :
    (partialSum f n - 3 * (n : Int)) % 6 = 0 := by
  have h₃ := prefix_mod_three c f hf₃ n
  have h₂ := prefix_mod_two f hf₂ n
  rw [hn] at h₃
  omega

/-- Sum of `s` consecutive increments starting at `v`. -/
def windowSum (f : Nat → Int) (v s : Nat) : Int :=
  partialSum (fun j => f (v + j)) s

theorem windowSum_succ (f : Nat → Int) (v s : Nat) :
    windowSum f v (s + 1) = windowSum f v s + f (v + s) := rfl

theorem windowSum_shift (f : Nat → Int) (v s : Nat) :
    windowSum f (v + 1) s - windowSum f v s = f (v + s) - f v := by
  induction s with
  | zero => simp [windowSum, partialSum]
  | succ s ih =>
    simp only [windowSum_succ]
    have hv : v + 1 + s = v + (s + 1) := by omega
    rw [hv]
    omega

theorem windowSum_period (f : Nat → Int) {n : Nat}
    (hf : ∀ v, f (v + n) = f v) (s : Nat) :
    windowSum f s n = partialSum f n := by
  induction s with
  | zero => simp [windowSum]
  | succ s ih =>
    have hs := windowSum_shift f s n
    rw [hf s, ih] at hs
    omega

theorem windowSum_flux (f : Nat → Int) {n : Nat}
    (hf : ∀ v, f (v + n) = f v) (s : Nat) :
    partialSum (fun v => windowSum f v s) n = (s : Int) * partialSum f n := by
  induction s with
  | zero => simp [windowSum, partialSum, prefix_const]
  | succ s ih =>
    have heq : (fun v => windowSum f v (s + 1)) =
        (fun v => windowSum f v s + f (v + s)) := by funext v; rfl
    rw [heq, prefix_add, ih]
    have hs : partialSum (fun v => f (v + s)) n = partialSum f n := by
      have hp := windowSum_period f hf s
      simpa only [windowSum, Nat.add_comm] using hp
    rw [hs]
    simp [Int.add_mul]

theorem flat_offset_constant (f e : Nat → Int) {s : Nat}
    (hflat : ∀ v, e (v + 1) - e v = f (v + s) - f v) (v : Nat) :
    e v - windowSum f v s = e 0 - partialSum f s := by
  induction v with
  | zero => simp [windowSum]
  | succ v ih =>
    have h₁ := hflat v
    have h₂ := windowSum_shift f v s
    omega

theorem flat_flux (f e : Nat → Int) {n s : Nat}
    (hf : ∀ v, f (v + n) = f v)
    (hflat : ∀ v, e (v + 1) - e v = f (v + s) - f v) :
    partialSum e n = (s : Int) * partialSum f n + (n : Int) * (e 0 - partialSum f s) := by
  have heq : e = (fun v => windowSum f v s + (e 0 - partialSum f s)) := by
    funext v
    have hv := flat_offset_constant f e hflat v
    omega
  calc
    partialSum e n = partialSum (fun v => windowSum f v s + (e 0 - partialSum f s)) n :=
      congrArg (fun g => partialSum g n) heq
    _ = _ := by rw [prefix_add, prefix_const, windowSum_flux f hf s]

theorem flat_offset_mod_six (c : Nat → Fin 3) (f e : Nat → Int) {s : Nat}
    (hf₃ : ∀ j, f j % 3 = ((c (j + 1)).val - (c j).val : Int) % 3)
    (hf₂ : ∀ j, f j % 2 = 1)
    (he₃ : e 0 % 3 = ((c s).val - (c 0).val : Int) % 3)
    (he₂ : e 0 % 2 = 1) :
    (e 0 - partialSum f s - 3 * (1 - (s : Int))) % 6 = 0 := by
  have h₃ := prefix_mod_three c f hf₃ s
  have h₂ := prefix_mod_two f hf₂ s
  omega

theorem exists_flux_character (c : Nat → Fin 3) (f : Nat → Int) {n : Nat}
    (hcn : c n = c 0) (hperiod : ∀ v, f (v + n) = f v)
    (hf₃ : ∀ j, f j % 3 = ((c (j + 1)).val - (c j).val : Int) % 3)
    (hf₂ : ∀ j, f j % 2 = 1) :
    ∃ K : Int, ∀ (s : Nat) (e : Nat → Int),
      (∀ v, e (v + 1) - e v = f (v + s) - f v) →
      e 0 % 3 = ((c s).val - (c 0).val : Int) % 3 →
      e 0 % 2 = 1 →
      ∃ z : Int, partialSum e n = 3 * (n : Int) + 6 * K * s + 6 * n * z := by
  let K : Int := (partialSum f n - 3 * n) / 6
  have hm := cycle_flux_mod_six c f hf₃ hf₂ hcn
  have hK : partialSum f n = 3 * (n : Int) + 6 * K := by dsimp [K]; omega
  refine ⟨K, fun s e hflat he₃ he₂ => ?_⟩
  let z : Int := (e 0 - partialSum f s - 3 * (1 - (s : Int))) / 6
  have hm' := flat_offset_mod_six c f e hf₃ hf₂ he₃ he₂
  have hz : e 0 - partialSum f s = 3 * (1 - (s : Int)) + 6 * z := by
    dsimp [z]
    omega
  refine ⟨z, ?_⟩
  rw [flat_flux f e hperiod hflat, hK, hz]
  grind

theorem maxStep_mod_two (a b : Fin 3) : maxStep a b % 2 = 1 := by
  have h := maxStep_cases a b
  omega

theorem partialSum_le (f : Nat → Int) (bound : Int) (n : Nat)
    (hf : ∀ j < n, f j ≤ bound) : partialSum f n ≤ (n : Int) * bound := by
  induction n with
  | zero => simp [partialSum]
  | succ n ih =>
    have hp := ih (fun j hj => hf j (by omega))
    have hn := hf n (by omega)
    simp only [partialSum, Int.natCast_succ, Int.add_mul, Int.one_mul]
    omega

theorem proper_cycle_winding (c : Nat → Fin 3) (t : Nat)
    (hcyc : c (3 * t + 2) = c 0)
    (hproper : ∀ j < 3 * t + 2, c j ≠ c (j + 1)) :
    partialSum (fun j => maxStep (c j) (c (j + 1))) (3 * t + 2) ≤ 3 * (t : Int) := by
  let f := fun j => maxStep (c j) (c (j + 1))
  have hb := partialSum_le f 1 (3 * t + 2) (fun j hj => by
    have h := maxStep_of_ne (hproper j hj)
    dsimp [f]
    omega)
  have hm := cycle_flux_mod_six c f (fun j => maxStep_mod_three _ _)
    (fun j => maxStep_mod_two _ _) hcyc
  dsimp [f] at hb hm
  omega

/-- The increment assigned to an oriented cyclic connection. -/
def directionStep (c : Nat → Fin 3) (s v : Nat) : Int :=
  maxStep (c v) (c (v + s))

theorem directionStep_flat (c : Nat → Fin 3) {s : Nat}
    (hunit : ∀ v, c v ≠ c (v + 1)) (hs : ∀ v, c v ≠ c (v + s)) (v : Nat) :
    directionStep c s (v + 1) - directionStep c s v =
      directionStep c 1 (v + s) - directionStep c 1 v := by
  have hi : v + 1 + s = v + s + 1 := by omega
  have hsq := proper_square_sum_zero (hunit v) (hs (v + 1))
    (by simpa only [hi] using Ne.symm (hunit (v + s))) (Ne.symm (hs v))
  have hr₁ := maxStep_reverse (hunit (v + s))
  have hr₂ := maxStep_reverse (hs v)
  simp only [hi] at hsq
  simp only [directionStep, hi]
  omega

/-- The height gain along a word of three proper connections. -/
def wordStep (c : Nat → Fin 3) (a b d v : Nat) : Int :=
  directionStep c a v + directionStep c b (v + a) +
    directionStep c d (v + a + b)

theorem wordStep_flat (c : Nat → Fin 3) {a b d : Nat}
    (hunit : ∀ v, c v ≠ c (v + 1))
    (ha : ∀ v, c v ≠ c (v + a)) (hb : ∀ v, c v ≠ c (v + b))
    (hd : ∀ v, c v ≠ c (v + d)) (v : Nat) :
    wordStep c a b d (v + 1) - wordStep c a b d v =
      directionStep c 1 (v + (a + b + d)) - directionStep c 1 v := by
  have h₁ := directionStep_flat c hunit ha v
  have h₂ := directionStep_flat c hunit hb (v + a)
  have h₃ := directionStep_flat c hunit hd (v + a + b)
  simp only [wordStep]
  simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] at h₁ h₂ h₃ ⊢
  omega

theorem wordStep_cases (c : Nat → Fin 3) {a b d : Nat}
    (ha : ∀ v, c v ≠ c (v + a)) (hb : ∀ v, c v ≠ c (v + b))
    (hd : ∀ v, c v ≠ c (v + d)) (v : Nat) :
    wordStep c a b d v = -3 ∨ wordStep c a b d v = -1 ∨
      wordStep c a b d v = 1 ∨ wordStep c a b d v = 3 := by
  have h₁ := maxStep_of_ne (ha v)
  have h₂ := maxStep_of_ne (hb (v + a))
  have h₃ := maxStep_of_ne (hd (v + a + b))
  dsimp [wordStep, directionStep]
  omega

theorem wordStep_mod_three (c : Nat → Fin 3) (a b d v : Nat) :
    wordStep c a b d v % 3 = ((c (v + (a + b + d))).val - (c v).val : Int) % 3 := by
  have h₁ := maxStep_mod_three (c v) (c (v + a))
  have h₂ := maxStep_mod_three (c (v + a)) (c (v + a + b))
  have h₃ := maxStep_mod_three (c (v + a + b)) (c (v + a + b + d))
  have hi : v + (a + b + d) = v + a + b + d := by omega
  simp only [hi, wordStep, directionStep]
  omega

theorem wordStep_mod_two (c : Nat → Fin 3) (a b d v : Nat) :
    wordStep c a b d v % 2 = 1 := by
  have h₁ := maxStep_mod_two (c v) (c (v + a))
  have h₂ := maxStep_mod_two (c (v + a)) (c (v + a + b))
  have h₃ := maxStep_mod_two (c (v + a + b)) (c (v + a + b + d))
  dsimp [wordStep, directionStep]
  omega

theorem wordStep_of_ne (c : Nat → Fin 3) {a b d v : Nat}
    (ha : ∀ v, c v ≠ c (v + a)) (hb : ∀ v, c v ≠ c (v + b))
    (hd : ∀ v, c v ≠ c (v + d)) (hv : c v ≠ c (v + (a + b + d))) :
    wordStep c a b d v = 1 ∨ wordStep c a b d v = -1 := by
  have hc := wordStep_cases c ha hb hd v
  have hm := wordStep_mod_three c a b d v
  have hlo := (c v).isLt
  have hhi := (c (v + (a + b + d))).isLt
  have hne : (c v).val ≠ (c (v + (a + b + d))).val := fun h => hv (Fin.ext h)
  omega

theorem directionStep_period (c : Nat → Fin 3) {n : Nat}
    (hc : ∀ v, c (v + n) = c v) (s v : Nat) :
    directionStep c s (v + n) = directionStep c s v := by
  have hi : v + n + s = v + s + n := by omega
  simp only [directionStep, hi, hc]

/-- One character controls both proper directions and all proper three-step words. -/
theorem exists_coloring_flux_character (c : Nat → Fin 3) {n : Nat}
    (hc : ∀ v, c (v + n) = c v) (hunit : ∀ v, c v ≠ c (v + 1)) :
    ∃ K : Int,
      (∀ s, (∀ v, c v ≠ c (v + s)) → ∃ z : Int,
        partialSum (directionStep c s) n = 3 * (n : Int) + 6 * K * s + 6 * n * z) ∧
      (∀ a b d, (∀ v, c v ≠ c (v + a)) → (∀ v, c v ≠ c (v + b)) →
        (∀ v, c v ≠ c (v + d)) → ∃ z : Int,
        partialSum (wordStep c a b d) n =
          3 * (n : Int) + 6 * K * (a + b + d) + 6 * n * z) := by
  obtain ⟨K, hK⟩ := exists_flux_character c (directionStep c 1)
    (by simpa using hc 0) (directionStep_period c hc 1)
    (fun j => maxStep_mod_three _ _) (fun j => maxStep_mod_two _ _)
  refine ⟨K, ?_, ?_⟩
  · intro s hs
    exact hK s (directionStep c s) (directionStep_flat c hunit hs)
      (by simpa [directionStep] using maxStep_mod_three (c 0) (c s))
      (maxStep_mod_two _ _)
  · intro a b d ha hb hd
    have hm := hK (a + b + d) (wordStep c a b d) (wordStep_flat c hunit ha hb hd)
      (by simpa using wordStep_mod_three c a b d 0) (wordStep_mod_two c a b d 0)
    simpa only [Int.natCast_add] using hm

theorem partialSum_mono (f g : Nat → Int) (n : Nat)
    (h : ∀ v < n, f v ≤ g v) : partialSum f n ≤ partialSum g n := by
  induction n with
  | zero => simp [partialSum]
  | succ n ih =>
    have h₁ := ih (fun v hv => h v (by omega))
    have h₂ := h n (by omega)
    simp only [partialSum]
    omega

theorem partialSum_mul (a : Int) (f : Nat → Int) (n : Nat) :
    partialSum (fun v => a * f v) n = a * partialSum f n := by
  induction n with
  | zero => simp [partialSum]
  | succ n ih => simp only [partialSum, ih, Int.mul_add]

/-- Number of monochromatic oriented edges of a fixed connection in one period. -/
def badCount (c : Nat → Fin 3) (s n : Nat) : Int :=
  partialSum (fun v => if c v = c (v + s) then 1 else 0) n

theorem badCount_nonneg (c : Nat → Fin 3) (s n : Nat) : 0 ≤ badCount c s n := by
  have h := partialSum_mono (fun _ => 0)
    (fun v => if c v = c (v + s) then 1 else 0) n (fun _ _ => by split <;> omega)
  simpa only [badCount, prefix_const, Int.mul_zero] using h

theorem wordStep_bounds (c : Nat → Fin 3) {a b d : Nat}
    (ha : ∀ v, c v ≠ c (v + a)) (hb : ∀ v, c v ≠ c (v + b))
    (hd : ∀ v, c v ≠ c (v + d)) (v : Nat) :
    -1 - 2 * (if c v = c (v + (a + b + d)) then 1 else 0) ≤ wordStep c a b d v ∧
    wordStep c a b d v ≤ 1 + 2 * (if c v = c (v + (a + b + d)) then 1 else 0) := by
  by_cases hv : c v = c (v + (a + b + d))
  · have h := wordStep_cases c ha hb hd v
    simp only [if_pos hv]
    omega
  · have h := wordStep_of_ne c ha hb hd hv
    simp only [if_neg hv]
    omega

theorem wordStep_flux_bounds (c : Nat → Fin 3) {a b d : Nat}
    (ha : ∀ v, c v ≠ c (v + a)) (hb : ∀ v, c v ≠ c (v + b))
    (hd : ∀ v, c v ≠ c (v + d)) (n : Nat) :
    -(n : Int) - 2 * badCount c (a + b + d) n ≤ partialSum (wordStep c a b d) n ∧
    partialSum (wordStep c a b d) n ≤ (n : Int) + 2 * badCount c (a + b + d) n := by
  have hlo := partialSum_mono
    (fun v => -1 + -2 * (if c v = c (v + (a + b + d)) then 1 else 0))
    (wordStep c a b d) n (fun v _ => by have h := (wordStep_bounds c ha hb hd v).1; omega)
  have hhi := partialSum_mono (wordStep c a b d)
    (fun v => 1 + 2 * (if c v = c (v + (a + b + d)) then 1 else 0))
    n (fun v _ => (wordStep_bounds c ha hb hd v).2)
  simp only [prefix_add, prefix_const, partialSum_mul] at hlo hhi
  dsimp [badCount]
  omega

/-- The integral shortfall of a character from the middle third. -/
def characterDeficit (n : Nat) (x : Int) : Int :=
  max 0 ((n : Int) - 3 * min (x % n) ((n : Int) - x % n))

theorem characterDeficit_le_of_flux {n : Nat} (hn : 0 < n) {x z W β : Int}
    (hβ : 0 ≤ β) (hW : W = 3 * (n : Int) + 6 * x + 6 * n * z)
    (hlo : -(n : Int) - 2 * β ≤ W) (hhi : W ≤ (n : Int) + 2 * β) :
    characterDeficit n x ≤ β := by
  let m : Int := x % n
  let q : Int := x / n + z
  have hn' : 0 < (n : Int) := by omega
  have hm₀ : 0 ≤ m := Int.emod_nonneg _ (by omega)
  have hm₁ : m < n := Int.emod_lt_of_pos _ hn'
  have he := Int.emod_add_mul_ediv x n
  have hW' : W = 3 * (n : Int) + 6 * m + 6 * n * q := by
    dsimp [m, q]
    grind
  have hbounds : (n : Int) - 3 * m ≤ β ∧ (n : Int) - 3 * ((n : Int) - m) ≤ β := by
    by_cases hq₀ : 0 ≤ q
    · have hp := Int.mul_nonneg (show 0 ≤ 6 * (n : Int) by omega) hq₀
      omega
    · by_cases hq₁ : q = -1
      · rw [hq₁] at hW'
        omega
      · have hq₂ : q ≤ -2 := by omega
        have hp := Int.mul_le_mul_of_nonneg_left hq₂ (show 0 ≤ 6 * (n : Int) by omega)
        omega
  have hm : (n : Int) - 3 * min m ((n : Int) - m) ≤ β := by
    rw [Int.min_def]
    split <;> omega
  change max 0 ((n : Int) - 3 * min m ((n : Int) - m)) ≤ β
  rw [Int.max_def]
  split <;> omega

theorem wordStep_deficit_bound (c : Nat → Fin 3) {n a b d : Nat} (hn : 0 < n)
    (ha : ∀ v, c v ≠ c (v + a)) (hb : ∀ v, c v ≠ c (v + b))
    (hd : ∀ v, c v ≠ c (v + d)) {K z : Int}
    (hflux : partialSum (wordStep c a b d) n =
      3 * (n : Int) + 6 * K * (a + b + d) + 6 * n * z) :
    characterDeficit n (K * (a + b + d)) ≤ badCount c (a + b + d) n := by
  have hbds := wordStep_flux_bounds c ha hb hd n
  exact characterDeficit_le_of_flux hn (badCount_nonneg c _ _)
    (by simpa only [Int.mul_assoc] using hflux) hbds.1 hbds.2

/-- The undirected monochromatic edges of a vertex assignment. -/
def badEdges {V : Type*} (G : SimpleGraph V) {k : Nat} (c : V → Fin k) : Set (Sym2 V) :=
  {e | ∃ v w, e = s(v, w) ∧ G.Adj v w ∧ c v = c w}

theorem badEdges_eq_empty_iff {V : Type*} (G : SimpleGraph V) {k : Nat} (c : V → Fin k) :
    badEdges G c = ∅ ↔ ∀ v w, G.Adj v w → c v ≠ c w := by
  constructor
  · intro h v w hadj heq
    have he : s(v, w) ∈ badEdges G c := ⟨v, w, rfl, hadj, heq⟩
    rw [h] at he
    exact he
  · intro h
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro e ⟨v, w, rfl, hadj, heq⟩
    exact h v w hadj heq

theorem badEdges_subset_of_deleted {V : Type*} (G : SimpleGraph V) {k : Nat}
    (edges : Set (Sym2 V)) (c : (G.deleteEdges edges).Coloring (Fin k)) :
    badEdges G c ⊆ edges := by
  rintro e ⟨v, w, rfl, hadj, heq⟩
  by_contra hnot
  exact c.valid (SimpleGraph.deleteEdges_adj.mpr ⟨hadj, hnot⟩) heq

theorem not_colorable_of_badEdges_bound {V : Type*} (G : SimpleGraph V) {k r : Nat}
    (hbad : ∀ c : V → Fin k, r < (badEdges G c).ncard) : ¬ G.Colorable k := by
  rintro ⟨c⟩
  have hc := hbad c
  have he := (badEdges_eq_empty_iff G c).mpr (fun _ _ => c.valid)
  simp only [he, Set.ncard_empty, Nat.not_lt_zero] at hc

theorem colorable_succ_of_punctured {V : Type*} (G : SimpleGraph V) {k : Nat}
    (v : V) (c : V → Fin k)
    (hc : ∀ u w, u ≠ v → w ≠ v → G.Adj u w → c u ≠ c w) : G.Colorable (k + 1) := by
  classical
  refine ⟨SimpleGraph.Coloring.mk (fun u => if u = v then 0 else (c u).succ) ?_⟩
  intro u w hadj
  by_cases hu : u = v
  · subst u
    by_cases hw : w = v
    · subst w
      exact False.elim (G.ne_of_adj hadj rfl)
    · simpa only [if_pos rfl, if_neg hw, ite_true] using (Fin.succ_ne_zero (c w)).symm
  · by_cases hw : w = v
    · subst w
      simpa only [if_pos rfl, if_neg hu, ite_true] using Fin.succ_ne_zero (c u)
    · simp only [if_neg hu, if_neg hw]
      exact fun h => hc u w hu hw hadj (Fin.succ_inj.mp h)

theorem colorable_delete_vertex_of_punctured {V : Type*} (G : SimpleGraph V) {k : Nat}
    (v : V) (c : V → Fin k)
    (hc : ∀ u w, u ≠ v → w ≠ v → G.Adj u w → c u ≠ c w) :
    ((⊤ : G.Subgraph).deleteVerts {v}).coe.Colorable k := by
  refine ⟨SimpleGraph.Coloring.mk (fun u => c u.val) ?_⟩
  intro u w hadj
  exact hc u.val w.val (by simpa using u.property.2) (by simpa using w.property.2)
    (SimpleGraph.Subgraph.coe_adj_sub _ _ _ hadj)

/-- Punctured colorings and a lower bound on bad edges imply the exact graph-theoretic
conclusion needed by Erdős 944. -/
theorem critical_robust_of_punctured {V : Type*} [Finite V] [Nonempty V]
    (G : SimpleGraph V) {k r : Nat}
    (hholes : ∀ v, ∃ c : V → Fin k,
      ∀ u w, u ≠ v → w ≠ v → G.Adj u w → c u ≠ c w)
    (hbad : ∀ c : V → Fin k, r < (badEdges G c).ncard) :
    Erdos944.SimpleGraph.IsErdos944 G (k + 1) r := by
  change G.IsCritical (k + 1) ∧
    ∀ edges : Set (Sym2 V), G.IsCriticalEdges edges → r < edges.ncard
  obtain ⟨v⟩ := ‹Nonempty V›
  obtain ⟨c, hc⟩ := hholes v
  have hfull := colorable_succ_of_punctured G v c hc
  have hnot := not_colorable_of_badEdges_bound G hbad
  have hχ : G.chromaticNumber = (k : ENat) + 1 :=
    SimpleGraph.chromaticNumber_eq_iff_colorable_not_colorable.mpr ⟨hfull, hnot⟩
  refine ⟨⟨by simpa using hχ, ?_⟩, ?_⟩
  · intro x
    obtain ⟨cx, hcx⟩ := hholes x
    have hcol := colorable_delete_vertex_of_punctured G x cx hcx
    change ((⊤ : G.Subgraph).deleteVerts {x}).coe.chromaticNumber <
      (⊤ : G.Subgraph).coe.chromaticNumber
    rw [SimpleGraph.chromaticNumber_congr SimpleGraph.Subgraph.topIso, hχ]
    exact lt_of_le_of_lt hcol.chromaticNumber_le (ENat.lt_natCast_add_one_iff.mpr le_rfl)
  · intro edges hcrit
    have hlt : (G.deleteEdges edges).chromaticNumber < (k : ENat) + 1 := by
      simpa only [SimpleGraph.IsCriticalEdges, hχ] using hcrit
    have hle := ENat.lt_natCast_add_one_iff.mp hlt
    obtain ⟨ce⟩ := SimpleGraph.chromaticNumber_le_iff_colorable.mp hle
    exact lt_of_lt_of_le (hbad ce) (Set.ncard_le_ncard (badEdges_subset_of_deleted G edges ce))

/-- With no inverse pair among the chosen directions, oriented connection edges are unique. -/
theorem connection_edge_injective {A : Type*} [AddCommGroup A] {a b v w : A}
    (hab : a ≠ -b) (he : s(v, v + a) = s(w, w + b)) : a = b ∧ v = w := by
  rcases Sym2.eq_iff.mp he with ⟨hv, hs⟩ | ⟨hv, hs⟩
  · subst w
    exact ⟨add_left_cancel hs, rfl⟩
  · exfalso
    apply hab
    have hz : b + a = 0 := by
      apply add_left_cancel (a := w)
      simpa only [← add_assoc, ← hv, add_zero] using hs
    exact eq_neg_of_add_eq_zero_right hz

theorem sum_bad_connections_le {A : Type*} [AddCommGroup A] [Fintype A]
    (G : SimpleGraph A) {k : Nat} (c : A → Fin k) (J : Finset A)
    (hJ : ∀ a ∈ J, ∀ b ∈ J, a ≠ -b)
    (hadj : ∀ a ∈ J, ∀ v, G.Adj v (v + a)) :
    ∑ a ∈ J, {v | c v = c (v + a)}.ncard ≤ (badEdges G c).ncard := by
  classical
  let D := Σ a : J, {v : A // c v = c (v + a.val)}
  let f : D → badEdges G c := fun p =>
    ⟨s(p.2.val, p.2.val + p.1.val), p.2.val, p.2.val + p.1.val, rfl,
      hadj p.1.val p.1.property p.2.val, p.2.property⟩
  have hf : Function.Injective f := by
    rintro ⟨a, v⟩ ⟨b, w⟩ h
    have he := congrArg Subtype.val h
    have he' : s(v.val, v.val + a.val) = s(w.val, w.val + b.val) := he
    have hp := connection_edge_injective (hJ a.val a.property b.val b.property) he'
    have hab : a = b := Subtype.ext hp.1
    subst b
    have hvw : v = w := Subtype.ext hp.2
    subst w
    rfl
  have hcard := Fintype.card_le_of_injective f hf
  simp only [D, Fintype.card_sigma] at hcard
  simp only [← Nat.card_eq_fintype_card] at hcard
  change (∑ a : J, {v | c v = c (v + a.val)}.ncard) ≤ (badEdges G c).ncard at hcard
  rw [Finset.sum_coe_sort J (fun a => {v | c v = c (v + a)}.ncard)] at hcard
  exact hcard

theorem bad_within_three_of_forward_steps (B : Int → Prop) {n : Nat} (hn : 0 < n)
    (hperiod : Function.Periodic B (n : Int)) (hne : ∃ z, B z)
    (hnext : ∀ z, B z → B (z + 1) ∨ B (z + 2) ∨ B (z + 3)) (v : Int) :
    B v ∨ B (v + 1) ∨ B (v + 2) := by
  by_contra h
  have h₀ : ¬ B v := fun hv => h (Or.inl hv)
  have h₁ : ¬ B (v + 1) := fun hv => h (Or.inr (Or.inl hv))
  have h₂ : ¬ B (v + 2) := fun hv => h (Or.inr (Or.inr hv))
  have hall : ∀ m : Nat, ¬ B (v - m) ∧ ¬ B (v - m + 1) ∧ ¬ B (v - m + 2) := by
    intro m
    induction m with
    | zero => simpa only [Nat.cast_zero, sub_zero] using And.intro h₀ (And.intro h₁ h₂)
    | succ m ih =>
      have hi₁ : v - (↑(m + 1) : Int) + 1 = v - m := by omega
      have hi₂ : v - (↑(m + 1) : Int) + 2 = v - m + 1 := by omega
      have hi₃ : v - (↑(m + 1) : Int) + 3 = v - m + 2 := by omega
      refine ⟨?_, ?_, ?_⟩
      · intro hv
        have hx := hnext (v - (m + 1 : Nat)) hv
        rw [hi₁, hi₂, hi₃] at hx
        rcases hx with hx | hx | hx
        · exact ih.1 hx
        · exact ih.2.1 hx
        · exact ih.2.2 hx
      · simpa only [hi₁] using ih.1
      · simpa only [hi₂] using ih.2.1
  obtain ⟨z, hz⟩ := hne
  let m : Nat := ((v - z) % n).toNat
  have hn' : (n : Int) ≠ 0 := by omega
  have hm : (m : Int) = (v - z) % n := Int.toNat_of_nonneg (Int.emod_nonneg _ hn')
  have hdiv := Int.ediv_mul_add_emod (v - z) n
  have he : v - (m : Int) = z + ((v - z) / n) * n := by omega
  have hp : B (v - m) = B z := by
    rw [he]
    exact hperiod.int_mul ((v - z) / n) z
  exact (hall m).1 (hp.mpr hz)

/-- If fewer than a third of the edges of a cycle are bad and some edge is bad,
then a bad edge is followed by three proper edges. -/
theorem exists_bad_followed_three_good (B : Int → Prop) [DecidablePred B]
    {n : Nat} (hn : 0 < n) (hperiod : Function.Periodic B (n : Int))
    (hne : ∃ z, B z)
    (hcount : 3 * partialSum (fun v : Nat => if B v then 1 else 0) n < (n : Int)) :
    ∃ v : Int, B v ∧ ¬ B (v + 1) ∧ ¬ B (v + 2) ∧ ¬ B (v + 3) := by
  classical
  by_contra hnone
  have hnext : ∀ z, B z → B (z + 1) ∨ B (z + 2) ∨ B (z + 3) := by
    intro z hz
    by_contra h
    exact hnone ⟨z, hz, (fun h₁ => h (Or.inl h₁)),
      (fun h₂ => h (Or.inr (Or.inl h₂))), (fun h₃ => h (Or.inr (Or.inr h₃)))⟩
  let f : Nat → Int := fun v => if B v then 1 else 0
  have hf : ∀ v, f (v + n) = f v := by
    intro v
    simp only [f, Nat.cast_add, hperiod v]
  have hbound : ∀ v < n, 1 ≤ f v + f (v + 1) + f (v + 2) := by
    intro v _
    have hv := bad_within_three_of_forward_steps B hn hperiod hne hnext v
    change 1 ≤ (if B (v : Int) then 1 else 0) +
      (if B ((v : Int) + 1) then 1 else 0) + (if B ((v : Int) + 2) then 1 else 0)
    rcases hv with hv | hv | hv
    all_goals split_ifs <;> first | contradiction | omega
  have hsum := partialSum_mono (fun _ => 1) (fun v => f v + f (v + 1) + f (v + 2)) n hbound
  have hshift (a : Nat) : partialSum (fun v => f (v + a)) n = partialSum f n := by
    simpa only [windowSum, Nat.add_comm] using windowSum_period f hf a
  simp only [prefix_const, Int.mul_one, prefix_add, hshift] at hsum
  change 3 * partialSum f n < (n : Int) at hcount
  omega

/-- The normalized cyclic coordinate used after deleting `v`. -/
def normalizedCoordinate {n : Nat} (a : (ZMod n)ˣ) (v u : ZMod n) : Nat :=
  ((↑a⁻¹ : ZMod n) * (u - v)).val

def puncturedColor {n : Nat} (a : (ZMod n)ˣ) (v u : ZMod n) : Fin 3 :=
  ⟨normalizedCoordinate a v u % 3, Nat.mod_lt _ (by omega)⟩

theorem normalizedCoordinate_pos {n : Nat} (a : (ZMod n)ˣ) {v u : ZMod n} (hu : u ≠ v) :
    0 < normalizedCoordinate a v u := by
  apply ZMod.val_pos.mpr
  intro h
  exact hu (sub_eq_zero.mp ((Units.mul_right_eq_zero a⁻¹).mp h))

theorem puncturedColor_ne_of_normalDifference {n : Nat} [NeZero n]
    (hn : n % 3 = 1) (a : (ZMod n)ˣ) {v u w : ZMod n}
    (hu : u ≠ v) (hw : w ≠ v)
    (hnormal : NormalDifference n (normalizedCoordinate a u w)) :
    puncturedColor a v u ≠ puncturedColor a v w := by
  let X : ZMod n := (↑a⁻¹ : ZMod n) * (u - v)
  let Y : ZMod n := (↑a⁻¹ : ZMod n) * (w - v)
  let S : ZMod n := (↑a⁻¹ : ZMod n) * (w - u)
  have hY : Y = X + S := by dsimp [X, Y, S]; ring
  have hwrap : Y.val = X.val + S.val ∨ Y.val + n = X.val + S.val := by
    by_cases hsmall : X.val + S.val < n
    · left
      rw [hY, ZMod.val_add_of_lt hsmall]
    · right
      rw [hY]
      exact (ZMod.val_add_val_of_le (a := X) (b := S) (by omega)).symm
  have hne := normalDifference_ne_color hn (normalizedCoordinate_pos a hu) (ZMod.val_lt X)
    (normalizedCoordinate_pos a hw) (ZMod.val_lt Y) hnormal hwrap
  exact fun h => hne (congrArg Fin.val h)

theorem puncturedColor_ne_of_unwrapped {n : Nat} (a : (ZMod n)ˣ) {v u w : ZMod n}
    {ℓ : Nat} (hℓ : ℓ % 3 = 1)
    (hforward : normalizedCoordinate a v w = normalizedCoordinate a v u + ℓ) :
    puncturedColor a v u ≠ puncturedColor a v w := by
  intro h
  have hc := congrArg Fin.val h
  change normalizedCoordinate a v u % 3 = normalizedCoordinate a v w % 3 at hc
  omega

theorem partialSum_split (f : Nat → Int) (a b : Nat) :
    partialSum f (a + b) = partialSum f a + windowSum f a b := by
  induction b with
  | zero => simp [windowSum, partialSum]
  | succ b ih =>
    calc
      partialSum f (a + (b + 1)) = partialSum f (a + b) + f (a + b) := rfl
      _ = partialSum f a + windowSum f a b + f (a + b) := by rw [ih]
      _ = partialSum f a + windowSum f a (b + 1) := by rw [windowSum_succ]; omega

/-- Delete indices 1, 2, and 3 while preserving the initial vertex. -/
def skipThree : Nat → Nat
  | 0 => 0
  | j + 1 => j + 4

theorem skipThree_strictMono : StrictMono skipThree := by
  intro i j hij
  cases i <;> cases j <;> simp only [skipThree] <;> omega

theorem skipThree_ne_one (j : Nat) : skipThree j ≠ 1 := by
  cases j <;> simp [skipThree]

theorem skipThree_difference_mod_three {i j : Nat} (hij : i < j) :
    (skipThree j - skipThree i) % 3 = (j - i) % 3 := by
  cases i <;> cases j <;> simp only [skipThree] <;> omega

theorem skipThree_flux (c : Nat → Fin 3) (q : Nat) :
    partialSum (fun j => maxStep (c (skipThree j)) (c (skipThree (j + 1)))) (q + 1) =
      partialSum (fun j => maxStep (c j) (c (j + 1))) (q + 4) -
      partialSum (fun j => maxStep (c j) (c (j + 1))) 4 + maxStep (c 0) (c 4) := by
  let f := fun j => maxStep (c j) (c (j + 1))
  let g := fun j => maxStep (c (skipThree j)) (c (skipThree (j + 1)))
  have hshift : windowSum g 1 q = windowSum f 4 q := by
    unfold windowSum
    congr 1
    funext j
    simp only [g, f, Nat.add_comm 1 j, skipThree]
    apply congrArg₂ maxStep
    · apply congrArg c; omega
    · apply congrArg c; omega
  have h₁ := partialSum_split f 4 q
  have h₂ := partialSum_split g 1 q
  have hstart : partialSum g 1 = maxStep (c 0) (c 4) := by simp [g, partialSum, skipThree]
  rw [hshift, hstart] at h₂
  simp only [Nat.add_comm 4 q, Nat.add_comm 1 q] at h₁ h₂
  change partialSum g (q + 1) = partialSum f (q + 4) - partialSum f 4 + maxStep (c 0) (c 4)
  omega

theorem skipThree_flux_bound (c : Nat → Fin 3) (q : Nat)
    (hbad : c 0 = c 1) (h₁ : c 1 ≠ c 2) (h₂ : c 2 ≠ c 3) (h₃ : c 3 ≠ c 4) :
    partialSum (fun j => maxStep (c j) (c (j + 1))) (q + 4) ≤
      partialSum (fun j => maxStep (c (skipThree j)) (c (skipThree (j + 1)))) (q + 1) + 3 := by
  have hshortcut := four_step_shortcut h₁ h₂ h₃
  have hskip := skipThree_flux c q
  have hstart : partialSum (fun j => maxStep (c j) (c (j + 1))) 4 =
      3 + maxStep (c 1) (c 2) + maxStep (c 2) (c 3) + maxStep (c 3) (c 4) := by
    simp [partialSum, hbad, maxStep_eq_three]
  rw [hstart, hbad] at hskip
  omega

/-- Monochromatic edges of the Andrásfai graph in its linear index order. -/
def badIndexPairs (c : Nat → Fin 3) (n : Nat) : Finset (Nat × Nat) :=
  ((Finset.range n).product (Finset.range n)).filter
    (fun p => p.1 < p.2 ∧ (p.2 - p.1) % 3 = 1 ∧ c p.1 = c p.2)

theorem mem_badIndexPairs (c : Nat → Fin 3) (n i j : Nat) :
    (i, j) ∈ badIndexPairs c n ↔ i < n ∧ j < n ∧ i < j ∧ (j - i) % 3 = 1 ∧ c i = c j := by
  simp [badIndexPairs, and_assoc]

theorem skipThree_badPairs_card (c : Nat → Fin 3) (q : Nat) (hbad : c 0 = c 1) :
    (badIndexPairs (fun j => c (skipThree j)) (q + 1)).card + 1 ≤
      (badIndexPairs c (q + 4)).card := by
  let f : Nat × Nat → Nat × Nat := fun p => (skipThree p.1, skipThree p.2)
  have hf : Function.Injective f := by
    intro p p' h
    exact Prod.ext (skipThree_strictMono.injective (congrArg Prod.fst h))
      (skipThree_strictMono.injective (congrArg Prod.snd h))
  let small := badIndexPairs (fun j => c (skipThree j)) (q + 1)
  have hnot : (0, 1) ∉ small.image f := by
    intro h
    obtain ⟨p, _, hp⟩ := Finset.mem_image.mp h
    exact skipThree_ne_one p.2 (congrArg Prod.snd hp)
  have hsub : insert (0, 1) (small.image f) ⊆ badIndexPairs c (q + 4) := by
    intro e he
    rcases Finset.mem_insert.mp he with rfl | he
    · exact (mem_badIndexPairs c (q + 4) 0 1).mpr ⟨by omega, by omega, by omega, by decide, hbad⟩
    · obtain ⟨⟨i, j⟩, hij, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨hi, hj, hij, hmod, hc⟩ := (mem_badIndexPairs _ _ i j).mp hij
      have hbound (a : Nat) (ha : a < q + 1) : skipThree a < q + 4 := by
        cases a <;> simp only [skipThree] <;> omega
      exact (mem_badIndexPairs _ _ _ _).mpr ⟨hbound i hi, hbound j hj,
        skipThree_strictMono hij, (skipThree_difference_mod_three hij).trans hmod, hc⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hnot, Finset.card_image_of_injective _ hf] at hcard
  exact hcard

def cyclicIndex (n v i : Nat) : Nat := (i + v) % n

theorem cyclicIndex_cases {n v i : Nat} (hv : v < n) (hi : i < n) :
    cyclicIndex n v i = i + v ∨ cyclicIndex n v i + n = i + v := by
  by_cases h : i + v < n
  · exact Or.inl (Nat.mod_eq_of_lt h)
  · right
    have hge : n ≤ i + v := by omega
    have hlt : i + v - n < n := by omega
    unfold cyclicIndex
    rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hlt]
    omega

theorem cyclicIndex_injective {n v i j : Nat} (hi : i < n) (hj : j < n)
    (h : cyclicIndex n v i = cyclicIndex n v j) : i = j :=
  (Nat.ModEq.add_right_cancel' v h).eq_of_lt_of_lt hi hj

theorem cyclicIndex_preserves_edges {n v i j : Nat} (hn : n % 3 = 2)
    (hv : v < n) (hi : i < n) (hj : j < n) (hij : i < j) (hd : (j - i) % 3 = 1) :
    (cyclicIndex n v i < cyclicIndex n v j ∧
      (cyclicIndex n v j - cyclicIndex n v i) % 3 = 1) ∨
    (cyclicIndex n v j < cyclicIndex n v i ∧
      (cyclicIndex n v i - cyclicIndex n v j) % 3 = 1) := by
  have h₁ := cyclicIndex_cases hv hi
  have h₂ := cyclicIndex_cases hv hj
  have hi' : cyclicIndex n v i < n := Nat.mod_lt _ (by omega)
  have hj' : cyclicIndex n v j < n := Nat.mod_lt _ (by omega)
  have hne : cyclicIndex n v i ≠ cyclicIndex n v j := by
    intro he
    have := cyclicIndex_injective hi hj he
    omega
  by_cases hlt : cyclicIndex n v i < cyclicIndex n v j
  · left
    refine ⟨hlt, ?_⟩
    rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂ <;> omega
  · right
    refine ⟨by omega, ?_⟩
    rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂ <;> omega

def badIndexEdges (c : Nat → Fin 3) (n : Nat) : Finset (Sym2 Nat) :=
  (badIndexPairs c n).image (fun p => s(p.1, p.2))

theorem card_badIndexEdges (c : Nat → Fin 3) (n : Nat) :
    (badIndexEdges c n).card = (badIndexPairs c n).card := by
  apply Finset.card_image_of_injOn
  rintro ⟨i, j⟩ hp ⟨i', j'⟩ hp' he
  have hlt := ((mem_badIndexPairs c n i j).mp hp).2.2.1
  have hlt' := ((mem_badIndexPairs c n i' j').mp hp').2.2.1
  rcases Sym2.eq_iff.mp he with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact Prod.ext h₁ h₂
  · omega

/-- Rotating the cyclic color word cannot increase its number of bad Andrásfai edges. -/
theorem rotate_badIndexPairs_le (c : Nat → Fin 3) {n v : Nat}
    (hn : n % 3 = 2) (hv : v < n) :
    (badIndexPairs (fun i => c (cyclicIndex n v i)) n).card ≤ (badIndexPairs c n).card := by
  let rot := cyclicIndex n v
  let small := badIndexEdges (fun i => c (rot i)) n
  have hinj : Set.InjOn (Sym2.map rot) small := by
    intro e he e' he' h
    obtain ⟨⟨i, j⟩, hp, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨⟨i', j'⟩, hp', rfl⟩ := Finset.mem_image.mp he'
    obtain ⟨hi, hj, _, _, _⟩ := (mem_badIndexPairs _ _ _ _).mp hp
    obtain ⟨hi', hj', _, _, _⟩ := (mem_badIndexPairs _ _ _ _).mp hp'
    apply Sym2.eq_iff.mpr
    rcases Sym2.eq_iff.mp h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Or.inl ⟨cyclicIndex_injective hi hi' h₁, cyclicIndex_injective hj hj' h₂⟩
    · exact Or.inr ⟨cyclicIndex_injective hi hj' h₁, cyclicIndex_injective hj hi' h₂⟩
  have hsub : small.image (Sym2.map rot) ⊆ badIndexEdges c n := by
    intro e he
    obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp he
    obtain ⟨⟨i, j⟩, hp, rfl⟩ := Finset.mem_image.mp he'
    obtain ⟨hi, hj, hij, hd, hc⟩ := (mem_badIndexPairs _ _ _ _).mp hp
    have hi' : rot i < n := Nat.mod_lt _ (by omega)
    have hj' : rot j < n := Nat.mod_lt _ (by omega)
    rcases cyclicIndex_preserves_edges hn hv hi hj hij hd with ⟨hlt, hmod⟩ | ⟨hlt, hmod⟩
    · exact Finset.mem_image.mpr ⟨(rot i, rot j),
        (mem_badIndexPairs _ _ _ _).mpr ⟨hi', hj', hlt, hmod, hc⟩, rfl⟩
    · exact Finset.mem_image.mpr ⟨(rot j, rot i),
        (mem_badIndexPairs _ _ _ _).mpr ⟨hj', hi', hlt, hmod, hc.symm⟩, Sym2.eq_swap⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj] at hcard
  simpa only [small, card_badIndexEdges] using hcard

theorem partialSum_congr (f g : Nat → Int) (n : Nat)
    (h : ∀ j < n, f j = g j) : partialSum f n = partialSum g n :=
  le_antisymm (partialSum_mono f g n (fun j hj => (h j hj).le))
    (partialSum_mono g f n (fun j hj => (h j hj).ge))

def periodicColor (c : Nat → Fin 3) (n j : Nat) : Fin 3 := c (j % n)

theorem periodicColor_periodic (c : Nat → Fin 3) (n : Nat) :
    Function.Periodic (periodicColor c n) n := by
  intro j
  simp only [periodicColor, Nat.add_mod_right]

theorem periodicColor_eq {c : Nat → Fin 3} {n j : Nat} (hc : c n = c 0) (hj : j ≤ n) :
    periodicColor c n j = c j := by
  by_cases hlt : j < n
  · simp only [periodicColor, Nat.mod_eq_of_lt hlt]
  · have he : j = n := by omega
    subst j
    simpa only [periodicColor, Nat.mod_self] using hc.symm

theorem periodicColor_flux {c : Nat → Fin 3} {n : Nat} (hc : c n = c 0) :
    partialSum (directionStep (periodicColor c n) 1) n = partialSum (directionStep c 1) n := by
  apply partialSum_congr
  intro j hj
  simp only [directionStep, periodicColor_eq hc (by omega : j ≤ n),
    periodicColor_eq hc (by omega : j + 1 ≤ n)]

theorem rotate_cycle_flux {c : Nat → Fin 3} {n : Nat} (hc : c n = c 0) (v : Nat) :
    partialSum (directionStep (fun j => c (cyclicIndex n v j)) 1) n =
      partialSum (directionStep c 1) n := by
  let p := periodicColor c n
  have hp := periodicColor_periodic c n
  calc
    partialSum (directionStep (fun j => c (cyclicIndex n v j)) 1) n =
        windowSum (directionStep p 1) v n := by
      apply partialSum_congr
      intro j _
      simp only [directionStep, p, periodicColor, cyclicIndex, Nat.add_assoc,
        Nat.add_comm]
    _ = partialSum (directionStep p 1) n :=
      windowSum_period _ (directionStep_period p hp 1) v
    _ = partialSum (directionStep c 1) n := periodicColor_flux hc

theorem partialSum_indicator (P : Nat → Prop) [DecidablePred P] (n : Nat) :
    partialSum (fun j => if P j then 1 else 0) n =
      (((Finset.range n).filter P).card : Int) := by
  induction n with
  | zero => simp [partialSum]
  | succ n ih =>
    have hn : n ∉ (Finset.range n).filter P := by simp
    by_cases hp : P n
    · simp [partialSum, ih, Finset.range_add_one, Finset.filter_insert, hp, hn]
    · simp [partialSum, ih, Finset.range_add_one, Finset.filter_insert, hp]

theorem badCycleIndices_le_badIndexPairs (c : Nat → Fin 3) {n : Nat}
    (hn : 3 ≤ n) (hmod : n % 3 = 2) (hc : c n = c 0) :
    ((Finset.range n).filter (fun j => c j = c (j + 1))).card ≤ (badIndexPairs c n).card := by
  let s := (Finset.range n).filter (fun j => c j = c (j + 1))
  let f : Nat → Nat × Nat := fun j => if j + 1 = n then (0, j) else (j, j + 1)
  have hinj : Set.InjOn f s := by
    intro i hi j hj he
    have hi' : i < n := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    have hj' : j < n := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
    dsimp [f] at he
    split_ifs at he
    all_goals
      have hfst := congrArg Prod.fst he
      have hsnd := congrArg Prod.snd he
      dsimp at hfst hsnd
      omega
  have hsub : s.image f ⊆ badIndexPairs c n := by
    intro e he
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hi, hci⟩ := Finset.mem_filter.mp hi
    have hi' : i < n := Finset.mem_range.mp hi
    by_cases hlast : i + 1 = n
    · have hcol : c 0 = c i := by simpa only [hlast, hc] using hci.symm
      simp only [f, if_pos hlast]
      exact (mem_badIndexPairs c n 0 i).mpr ⟨by omega, hi', by omega, by omega, hcol⟩
    · simp only [f, if_neg hlast]
      exact (mem_badIndexPairs c n i (i + 1)).mpr
        ⟨hi', by omega, by omega, by omega, hci⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj] at hcard
  exact hcard

theorem badCount_le_badIndexPairs (c : Nat → Fin 3) {n : Nat}
    (hn : 3 ≤ n) (hmod : n % 3 = 2) (hc : c n = c 0) :
    badCount c 1 n ≤ ((badIndexPairs c n).card : Int) := by
  rw [badCount, partialSum_indicator]
  exact_mod_cast badCycleIndices_le_badIndexPairs c hn hmod hc

def intColor (c : Nat → Fin 3) (n : Nat) (z : Int) : Fin 3 := c ((z % n).toNat)

theorem intColor_nat (c : Nat → Fin 3) {n : Nat} (hc : Function.Periodic c n) (j : Nat) :
    intColor c n j = c j := by
  unfold intColor
  rw [← Int.natCast_emod, Int.toNat_natCast]
  exact hc.map_mod_nat j

theorem intColor_periodic (c : Nat → Fin 3) (n : Nat) :
    Function.Periodic (intColor c n) (n : Int) := by
  intro z
  simp only [intColor, Int.add_emod_right]

theorem int_periodic_emod {α : Type*} {f : Int → α} {n : Int}
    (hf : Function.Periodic f n) (x : Int) : f (x % n) = f x := by
  calc
    f (x % n) = f (x % n + (x / n) * n) := (hf.int_mul (x / n) (x % n)).symm
    _ = f x := congrArg f (by have h := Int.ediv_mul_add_emod x n; omega)

theorem exists_cycle_shortcut_window (c : Nat → Fin 3) {n : Nat} (hn : 0 < n)
    (hc : Function.Periodic c n) (hne : ∃ j < n, c j = c (j + 1))
    (hcount : 3 * badCount c 1 n < (n : Int)) :
    ∃ v < n, c v = c (v + 1) ∧ c (v + 1) ≠ c (v + 2) ∧
      c (v + 2) ≠ c (v + 3) ∧ c (v + 3) ≠ c (v + 4) := by
  classical
  let C := intColor c n
  let B : Int → Prop := fun z => C z = C (z + 1)
  have hpC : Function.Periodic C (n : Int) := intColor_periodic c n
  have hpB : Function.Periodic B (n : Int) := by
    intro z
    change (C (z + n) = C (z + n + 1)) = (C z = C (z + 1))
    have hi : z + (n : Int) + 1 = z + 1 + n := by omega
    rw [hi, hpC z, hpC (z + 1)]
  have hBNat (j : Nat) : B j ↔ c j = c (j + 1) := by
    change intColor c n j = intColor c n ((j : Int) + 1) ↔ c j = c (j + 1)
    rw [intColor_nat c hc j]
    have hj : (j : Int) + 1 = ((j + 1 : Nat) : Int) := by omega
    rw [hj, intColor_nat c hc (j + 1)]
  have hsum : partialSum (fun j : Nat => if B j then 1 else 0) n = badCount c 1 n := by
    apply partialSum_congr
    intro j _
    simp only [hBNat j]
  have hex : ∃ z, B z := by
    obtain ⟨j, _, hj⟩ := hne
    exact ⟨j, (hBNat j).mpr hj⟩
  obtain ⟨z, hz, hz₁, hz₂, hz₃⟩ := exists_bad_followed_three_good B hn hpB hex (by rwa [hsum])
  let v : Nat := (z % n).toNat
  have hn' : (n : Int) ≠ 0 := by omega
  have hv : (v : Int) = z % n := Int.toNat_of_nonneg (Int.emod_nonneg _ hn')
  have hvlt : v < n := by have h := Int.emod_lt_of_pos z (show 0 < (n : Int) by omega); omega
  have htrans (j : Int) : B ((v : Int) + j) = B (z + j) := by
    calc
      B ((v : Int) + j) = B (((v : Int) + j) % n) := (int_periodic_emod hpB _).symm
      _ = B ((z + j) % n) := congrArg B (by rw [hv, Int.emod_add_emod])
      _ = B (z + j) := int_periodic_emod hpB _
  have hP (j : Nat) : (c (v + j) = c (v + j + 1)) ↔ B (z + j) := by
    rw [← hBNat (v + j)]
    apply Iff.of_eq
    simpa only [Nat.cast_add] using htrans j
  refine ⟨v, hvlt, ?_, ?_, ?_, ?_⟩
  · simpa using (hP 0).mpr (by simpa using hz)
  · simpa [Nat.add_assoc] using mt (hP 1).mp hz₁
  · simpa [Nat.add_assoc] using mt (hP 2).mp hz₂
  · simpa [Nat.add_assoc] using mt (hP 3).mp hz₃

theorem badIndexPairs_periodicColor (c : Nat → Fin 3) (n : Nat) :
    badIndexPairs (periodicColor c n) n = badIndexPairs c n := by
  ext ⟨i, j⟩
  rw [mem_badIndexPairs, mem_badIndexPairs]
  constructor <;> rintro ⟨hi, hj, hij, hd, hcol⟩
  all_goals
    refine ⟨hi, hj, hij, hd, ?_⟩
    simpa only [periodicColor, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] using hcol

/-- The full cyclic winding bound for an Andrásfai graph with at most `t` bad edges. -/
theorem andrasfai_cycle_flux_le (t : Nat) (c : Nat → Fin 3)
    (hcyc : c (3 * t + 2) = c 0) (hbad : (badIndexPairs c (3 * t + 2)).card ≤ t) :
    partialSum (directionStep c 1) (3 * t + 2) ≤ 3 * (t : Int) := by
  induction t generalizing c with
  | zero =>
    have h₀₁ : c 0 ≠ c 1 := by
      intro he
      have hmem : (0, 1) ∈ badIndexPairs c 2 :=
        (mem_badIndexPairs c 2 0 1).mpr ⟨by omega, by omega, by omega, by decide, he⟩
      have hpos := Finset.card_pos.mpr ⟨(0, 1), hmem⟩
      change (badIndexPairs c 2).card ≤ 0 at hbad
      omega
    apply proper_cycle_winding c 0 hcyc
    intro j hj
    have hcases : j = 0 ∨ j = 1 := by omega
    rcases hcases with rfl | rfl
    · exact h₀₁
    · simpa only [show c 2 = c 0 from hcyc] using h₀₁.symm
  | succ t ih =>
    let n : Nat := 3 * (t + 1) + 2
    let p := periodicColor c n
    have hn : 3 ≤ n := by dsimp [n]; omega
    have hnmod : n % 3 = 2 := by dsimp [n]; omega
    have hp : Function.Periodic p n := periodicColor_periodic c n
    have hpb : (badIndexPairs p n).card ≤ t + 1 := by
      dsimp [p]
      rw [badIndexPairs_periodicColor]
      exact hbad
    have hfluxp : partialSum (directionStep p 1) n = partialSum (directionStep c 1) n :=
      periodicColor_flux hcyc
    change partialSum (directionStep c 1) n ≤ 3 * ((t + 1 : Nat) : Int)
    by_cases hproper : ∀ j < n, p j ≠ p (j + 1)
    · rw [← hfluxp]
      exact proper_cycle_winding p (t + 1) hp.eq hproper
    · push Not at hproper
      have hcycleBad := badCount_le_badIndexPairs p hn hnmod hp.eq
      have hpb' : ((badIndexPairs p n).card : Int) ≤ (t : Int) + 1 := by exact_mod_cast hpb
      have hcount : 3 * badCount p 1 n < (n : Int) := by
        have hnval : (n : Int) = 3 * (t : Int) + 5 := by dsimp [n]; omega
        omega
      obtain ⟨v, hv, hv₀, hv₁, hv₂, hv₃⟩ :=
        exists_cycle_shortcut_window p (by omega) hp hproper hcount
      let d : Nat → Fin 3 := fun j => p (v + j)
      have hd : Function.Periodic d n := hp.const_add v
      have hrot : (fun j => p (cyclicIndex n v j)) = d := by
        funext j
        simpa only [cyclicIndex, d, Nat.add_comm] using hp.map_mod_nat (j + v)
      have hdb : (badIndexPairs d n).card ≤ t + 1 := by
        have h := rotate_badIndexPairs_le p hnmod hv
        rw [hrot] at h
        exact h.trans hpb
      have hfluxd : partialSum (directionStep d 1) n = partialSum (directionStep p 1) n := by
        have h := rotate_cycle_flux hp.eq v
        rw [hrot] at h
        exact h
      have hd₀ : d 0 = d 1 := by simpa only [d, Nat.add_zero] using hv₀
      have hd₁ : d 1 ≠ d 2 := hv₁
      have hd₂ : d 2 ≠ d 3 := hv₂
      have hd₃ : d 3 ≠ d 4 := hv₃
      let small : Nat → Fin 3 := fun j => d (skipThree j)
      have hnew : 3 * t + 1 + 1 = 3 * t + 2 := by omega
      have hold : 3 * t + 1 + 4 = n := by dsimp [n]; omega
      have hskip : skipThree (3 * t + 2) = n := by
        change 3 * t + 1 + 4 = n
        exact hold
      have hsmallCycle : small (3 * t + 2) = small 0 := by
        change d (skipThree (3 * t + 2)) = d (skipThree 0)
        rw [hskip]
        exact hd.eq
      have hsmallBad : (badIndexPairs small (3 * t + 2)).card ≤ t := by
        have h := skipThree_badPairs_card d (3 * t + 1) hd₀
        rw [hnew, hold] at h
        change (badIndexPairs small (3 * t + 2)).card + 1 ≤ (badIndexPairs d n).card at h
        omega
      have hwind := ih small hsmallCycle hsmallBad
      have hsurgery := skipThree_flux_bound d (3 * t + 1) hd₀ hd₁ hd₂ hd₃
      rw [hnew, hold] at hsurgery
      change partialSum (directionStep d 1) n ≤
        partialSum (directionStep small 1) (3 * t + 2) + 3 at hsurgery
      omega

/-- A path gaining more height than its length forces more than `t` monochromatic edges. -/
theorem winding_forces_bad_edges (t : Nat) (c : Nat → Fin 3) (f : Nat → Int)
    (hcyc : c (3 * t + 2) = c 0)
    (hstep : ∀ j < 3 * t + 1, f j ≤ directionStep c 1 j)
    (hgain : 3 * (t : Int) + 1 < partialSum f (3 * t + 1)) :
    t < (badIndexPairs c (3 * t + 2)).card := by
  by_contra h
  have hbound := andrasfai_cycle_flux_le t c hcyc (by omega)
  have hpath := partialSum_mono f (directionStep c 1) (3 * t + 1) hstep
  have hlast := maxStep_cases (c (3 * t + 1)) (c (3 * t + 2))
  change partialSum (directionStep c 1) ((3 * t + 1) + 1) ≤ 3 * (t : Int) at hbound
  rw [partialSum] at hbound
  change partialSum (directionStep c 1) (3 * t + 1) +
    maxStep (c (3 * t + 1)) (c (3 * t + 2)) ≤ 3 * (t : Int) at hbound
  omega

theorem wordStep_le_maxStep (c : Nat → Fin 3) {a b d : Nat}
    (ha : ∀ v, c v ≠ c (v + a)) (hb : ∀ v, c v ≠ c (v + b))
    (hd : ∀ v, c v ≠ c (v + d)) (v : Nat) :
    wordStep c a b d v ≤ maxStep (c v) (c (v + (a + b + d))) := by
  have hw := wordStep_cases c ha hb hd v
  have hm := wordStep_mod_three c a b d v
  have hx := maxStep_cases (c v) (c (v + (a + b + d)))
  have hy := maxStep_mod_three (c v) (c (v + (a + b + d)))
  omega

theorem badCount_congr (c : Nat → Fin 3) {n a b : Nat} (hc : Function.Periodic c n)
    (hab : a % n = b % n) : badCount c a n = badCount c b n := by
  apply partialSum_congr
  intro j _
  have hmod : (j + a) % n = (j + b) % n := by
    calc
      (j + a) % n = (j % n + a % n) % n := Nat.add_mod _ _ _
      _ = (j % n + b % n) % n := congrArg (fun x => (j % n + x) % n) hab
      _ = (j + b) % n := (Nat.add_mod _ _ _).symm
  have hcolor : c (j + a) = c (j + b) := by
    rw [← hc.map_mod_nat (j + a), hmod, hc.map_mod_nat (j + b)]
  rw [hcolor]

theorem characterDeficit_nat_congr (K : Int) {n a b : Nat} (hab : a % n = b % n) :
    characterDeficit n (K * (a : Int)) = characterDeficit n (K * (b : Int)) := by
  have hm : (a : Int) % n = (b : Int) % n := by
    simpa only [Int.natCast_emod] using congrArg (fun j : Nat => (j : Int)) hab
  have hprod : (K * (a : Int)) % n = (K * (b : Int)) % n := by
    calc
      (K * (a : Int)) % n = ((K % n) * ((a : Int) % n)) % n := Int.mul_emod _ _ _
      _ = ((K % n) * ((b : Int) % n)) % n := congrArg (fun x => ((K % n) * x) % n) hm
      _ = (K * (b : Int)) % n := (Int.mul_emod _ _ _).symm
  simp only [characterDeficit, hprod]

theorem exists_character_with_word_bounds (c : Nat → Fin 3) {n : Nat} (hn : 0 < n)
    (hc : Function.Periodic c n) (hunit : ∀ v, c v ≠ c (v + 1)) :
    ∃ K : Int, ∀ s : Nat,
      (∃ a b d : Nat, (a + b + d) % n = s % n ∧
        (∀ v, c v ≠ c (v + a)) ∧ (∀ v, c v ≠ c (v + b)) ∧ (∀ v, c v ≠ c (v + d))) →
      characterDeficit n (K * (s : Int)) ≤ badCount c s n := by
  obtain ⟨K, _, hwords⟩ := exists_coloring_flux_character c hc hunit
  refine ⟨K, ?_⟩
  rintro s ⟨a, b, d, hsum, ha, hb, hd⟩
  obtain ⟨z, hz⟩ := hwords a b d ha hb hd
  have hbound := wordStep_deficit_bound c hn ha hb hd hz
  have hD := characterDeficit_nat_congr K hsum
  simp only [Int.natCast_add] at hD
  rw [hD, badCount_congr c hc hsum] at hbound
  exact hbound

theorem cyclic_badCount_eq_ncard {n : Nat} [NeZero n] (c : ZMod n → Fin 3) (s : Nat) :
    badCount (fun j => c (j : ZMod n)) s n =
      ({v : ZMod n | c v = c (v + (s : ZMod n))}.ncard : Int) := by
  classical
  let P : Nat → Prop := fun j => c (j : ZMod n) = c ((j + s : Nat) : ZMod n)
  let starts := (Finset.range n).filter P
  let B : Set (ZMod n) := {v | c v = c (v + (s : ZMod n))}
  let cast : Nat → ZMod n := fun j => (j : ZMod n)
  have hinj : Set.InjOn cast starts := by
    intro i hi j hj he
    have hi' : i < n := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    have hj' : j < n := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
    exact ((ZMod.natCast_eq_natCast_iff i j n).mp he).eq_of_lt_of_lt hi' hj'
  have himage : starts.image cast = B.toFinset := by
    ext v
    rw [Set.mem_toFinset]
    constructor
    · intro h
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp h
      have hcol := (Finset.mem_filter.mp hj).2
      simpa only [P, B, cast, Set.mem_ofPred_eq, Nat.cast_add] using hcol
    · intro hv
      refine Finset.mem_image.mpr ⟨v.val, ?_, ZMod.natCast_zmod_val v⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr (ZMod.val_lt v), ?_⟩
      simpa only [P, B, Set.mem_ofPred_eq, Nat.cast_add, ZMod.natCast_zmod_val] using hv
  have hcard := Finset.card_image_of_injOn hinj
  rw [himage] at hcard
  rw [badCount, partialSum_indicator]
  change (starts.card : Int) = (B.ncard : Int)
  rw [Set.ncard_eq_toFinset_card', hcard]

/-- A proper connection is proper at every translate, not just at one selected edge. -/
def GoodDirection {A : Type*} [Add A] (c : A → Fin 3) (s : A) : Prop :=
  ∀ v, c v ≠ c (v + s)

def ThreeStepReachable {A : Type*} [Add A] (c : A → Fin 3) (s : A) : Prop :=
  ∃ a b d : A, a + b + d = s ∧ GoodDirection c a ∧ GoodDirection c b ∧ GoodDirection c d

/-- The total character deficit is bounded by the total number of bad graph edges. -/
theorem coloring_character_deficits_le_badEdges {n : Nat} [NeZero n]
    (G : SimpleGraph (ZMod n)) (c : ZMod n → Fin 3) (J : Finset (ZMod n))
    (hJ : ∀ a ∈ J, ∀ b ∈ J, a ≠ -b)
    (hadj : ∀ a ∈ J, ∀ v, G.Adj v (v + a))
    (hunit : GoodDirection c 1) (hwalk : ∀ s ∈ J, ThreeStepReachable c s) :
    ∃ K : Int, (∑ s ∈ J, characterDeficit n (K * (s.val : Int))) ≤ (badEdges G c).ncard := by
  let C : Nat → Fin 3 := fun j => c (j : ZMod n)
  have hc : Function.Periodic C n := by
    intro j
    simp only [C, Nat.cast_add, ZMod.natCast_self, add_zero]
  have hcunit : ∀ j, C j ≠ C (j + 1) := by
    intro j
    simpa only [C, Nat.cast_add, Nat.cast_one] using hunit (j : ZMod n)
  obtain ⟨K, hK⟩ := exists_character_with_word_bounds C (NeZero.pos n) hc hcunit
  have hbound : ∀ s ∈ J, characterDeficit n (K * (s.val : Int)) ≤ badCount C s.val n := by
    intro s hs
    obtain ⟨a, b, d, hsum, ha, hb, hd⟩ := hwalk s hs
    apply hK s.val
    refine ⟨a.val, b.val, d.val, ?_, ?_, ?_, ?_⟩
    · have hcast : ((a.val + b.val + d.val : Nat) : ZMod n) = s := by
        simpa only [Nat.cast_add, ZMod.natCast_zmod_val] using hsum
      have hv := congrArg ZMod.val hcast
      simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt (ZMod.val_lt s)] using hv
    · intro j
      simpa only [C, Nat.cast_add, ZMod.natCast_zmod_val] using ha (j : ZMod n)
    · intro j
      simpa only [C, Nat.cast_add, ZMod.natCast_zmod_val] using hb (j : ZMod n)
    · intro j
      simpa only [C, Nat.cast_add, ZMod.natCast_zmod_val] using hd (j : ZMod n)
  refine ⟨K, (Finset.sum_le_sum hbound).trans ?_⟩
  have hcard := sum_bad_connections_le G c J hJ hadj
  have hsum : (∑ s ∈ J, badCount C s.val n) =
      ((∑ s ∈ J, {v : ZMod n | c v = c (v + s)}.ncard : Nat) : Int) := by
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro s _
    simpa only [C, ZMod.natCast_zmod_val] using cyclic_badCount_eq_ncard c s.val
  rw [hsum]
  exact_mod_cast hcard

theorem badIndexPairs_le_of_embedding {V : Type*} [Finite V] (G : SimpleGraph V)
    (c : V → Fin 3) (f : Nat → V) (n : Nat)
    (hinj : ∀ i < n, ∀ j < n, f i = f j → i = j)
    (hadj : ∀ i < n, ∀ j < n, i < j → (j - i) % 3 = 1 → G.Adj (f i) (f j)) :
    (badIndexPairs (fun j => c (f j)) n).card ≤ (badEdges G c).ncard := by
  classical
  let : Fintype V := Fintype.ofFinite V
  let S := badIndexPairs (fun j => c (f j)) n
  let edge : S → badEdges G c := fun p => ⟨s(f p.val.1, f p.val.2), by
    obtain ⟨hi, hj, hij, hd, hc⟩ := (mem_badIndexPairs _ _ _ _).mp p.property
    exact ⟨f p.val.1, f p.val.2, rfl, hadj _ hi _ hj hij hd, hc⟩⟩
  have hedge : Function.Injective edge := by
    rintro ⟨⟨i, j⟩, hp⟩ ⟨⟨i', j'⟩, hp'⟩ he
    obtain ⟨hi, hj, hij, _, _⟩ := (mem_badIndexPairs _ _ _ _).mp hp
    obtain ⟨hi', hj', hij', _, _⟩ := (mem_badIndexPairs _ _ _ _).mp hp'
    have hsym : s(f i, f j) = s(f i', f j') := congrArg Subtype.val he
    apply Subtype.ext
    rcases Sym2.eq_iff.mp hsym with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Prod.ext (hinj i hi i' hi' h₁) (hinj j hj j' hj' h₂)
    · have hx := hinj i hi j' hj' h₁
      have hy := hinj j hj i' hi' h₂
      omega
  have hcard := Fintype.card_le_of_injective edge hedge
  simpa only [S, Fintype.card_coe, Set.fintypeCard_eq_ncard] using hcard

/-- The graph-theoretic form of the winding bound, for an embedded gap. -/
theorem path_gain_le_of_badEdges_bound {V : Type*} [Finite V] (G : SimpleGraph V)
    (c : V → Fin 3) (t : Nat) (f : Nat → V) (δ : Nat → Int)
    (hinj : ∀ i < 3 * t + 2, ∀ j < 3 * t + 2, f i = f j → i = j)
    (hadj : ∀ i < 3 * t + 2, ∀ j < 3 * t + 2,
      i < j → (j - i) % 3 = 1 → G.Adj (f i) (f j))
    (hbad : (badEdges G c).ncard ≤ t)
    (hstep : ∀ j < 3 * t + 1, δ j ≤ maxStep (c (f j)) (c (f (j + 1)))) :
    partialSum δ (3 * t + 1) ≤ 3 * (t : Int) + 1 := by
  let C : Nat → Fin 3 := fun j => c (f j)
  let p := periodicColor C (3 * t + 2)
  have hp : p (3 * t + 2) = p 0 := (periodicColor_periodic C (3 * t + 2)).eq
  have hlocal : (badIndexPairs p (3 * t + 2)).card ≤ t := by
    dsimp [p]
    rw [badIndexPairs_periodicColor]
    exact (badIndexPairs_le_of_embedding G c f _ hinj hadj).trans hbad
  have hstep' : ∀ j < 3 * t + 1, δ j ≤ directionStep p 1 j := by
    intro j hj
    simpa only [directionStep, p, periodicColor, Nat.mod_eq_of_lt (by omega : j < 3 * t + 2),
      Nat.mod_eq_of_lt (by omega : j + 1 < 3 * t + 2)] using hstep j hj
  by_contra hg
  have h := winding_forces_bad_edges t p δ hp hstep' (by omega)
  omega

def SignedDistinct {A : Type*} [Neg A] (a b : A) : Prop := a ≠ b ∧ a ≠ -b

theorem SignedDistinct.symm {A : Type*} [InvolutiveNeg A] {a b : A}
    (h : SignedDistinct a b) : SignedDistinct b a := by
  refine ⟨h.1.symm, ?_⟩
  intro he
  apply h.2
  simpa only [neg_neg] using (congrArg Neg.neg he).symm

/-- Distinct inverse direction pairs that are all bad supply distinct bad undirected edges. -/
theorem card_bad_direction_family_le {A I : Type*} [AddCommGroup A] [Finite A] [Fintype I]
    (G : SimpleGraph A) (c : A → Fin 3) (s : I → A)
    (hsep : ∀ i j, i ≠ j → SignedDistinct (s i) (s j))
    (hadj : ∀ i v, G.Adj v (v + s i)) (hbad : ∀ i, ¬ GoodDirection c (s i)) :
    Fintype.card I ≤ (badEdges G c).ncard := by
  classical
  let : Fintype A := Fintype.ofFinite A
  have hex : ∀ i, ∃ v, c v = c (v + s i) := by
    intro i
    have hi := hbad i
    change ¬ ∀ v, c v ≠ c (v + s i) at hi
    push Not at hi
    exact hi
  let v : I → A := fun i => (hex i).choose
  have hv (i : I) : c (v i) = c (v i + s i) := (hex i).choose_spec
  let edge : I → badEdges G c := fun i =>
    ⟨s(v i, v i + s i), v i, v i + s i, rfl, hadj i (v i), hv i⟩
  have hinj : Function.Injective edge := by
    intro i j he
    by_contra hij
    have hsym : s(v i, v i + s i) = s(v j, v j + s j) := congrArg Subtype.val he
    have hdir := connection_edge_injective (hsep i j hij).2 hsym
    exact (hsep i j hij).1 hdir.1
  have hcard := Fintype.card_le_of_injective edge hinj
  simpa only [Set.fintypeCard_eq_ncard] using hcard

theorem exists_good_direction {A I : Type*} [AddCommGroup A] [Finite A] [Fintype I]
    (G : SimpleGraph A) (c : A → Fin 3) (s : I → A)
    (hsep : ∀ i j, i ≠ j → SignedDistinct (s i) (s j))
    (hadj : ∀ i v, G.Adj v (v + s i))
    (hsize : (badEdges G c).ncard < Fintype.card I) : ∃ i, GoodDirection c (s i) := by
  by_contra hnone
  have hbad : ∀ i, ¬ GoodDirection c (s i) := fun i hi => hnone ⟨i, hi⟩
  exact (card_bad_direction_family_le G c s hsep hadj hbad).not_gt hsize

/-- Among `r` disjoint three-step words avoiding a bad target direction, one word is wholly proper. -/
theorem exists_good_word {A : Type*} [AddCommGroup A] [Finite A]
    (G : SimpleGraph A) (c : A → Fin 3) (r : Nat) (target : A) (W : Fin r → Fin 3 → A)
    (htarget : ∀ v, G.Adj v (v + target))
    (hbadTarget : ¬ GoodDirection c target)
    (hadj : ∀ i p v, G.Adj v (v + W i p))
    (havoid : ∀ i p, SignedDistinct target (W i p))
    (hdisjoint : ∀ i j, i ≠ j → ∀ p q, SignedDistinct (W i p) (W j q))
    (hbad : (badEdges G c).ncard ≤ r) : ∃ i, ∀ p, GoodDirection c (W i p) := by
  classical
  by_contra hnone
  have hex : ∀ i, ∃ p, ¬ GoodDirection c (W i p) := by
    intro i
    have hi : ¬ ∀ p, GoodDirection c (W i p) := fun hi => hnone ⟨i, hi⟩
    push Not at hi
    exact hi
  let p : Fin r → Fin 3 := fun i => (hex i).choose
  let s : Option (Fin r) → A
    | none => target
    | some i => W i (p i)
  have hsadj : ∀ i v, G.Adj v (v + s i) := by
    intro i v
    cases i with
    | none => exact htarget v
    | some i => exact hadj i (p i) v
  have hsbad : ∀ i, ¬ GoodDirection c (s i) := by
    intro i
    cases i with
    | none => exact hbadTarget
    | some i => exact (hex i).choose_spec
  have hssep : ∀ i j, i ≠ j → SignedDistinct (s i) (s j) := by
    intro i j hij
    cases i with
    | none =>
      cases j with
      | none => exact False.elim (hij rfl)
      | some j => exact havoid j (p j)
    | some i =>
      cases j with
      | none => exact (havoid i (p i)).symm
      | some j => exact hdisjoint i j (fun he => hij (congrArg some he)) (p i) (p j)
  have hcard := card_bad_direction_family_le G c s hssep hsadj hsbad
  simp only [Fintype.card_option, Fintype.card_fin] at hcard
  omega

theorem GoodDirection.neg {A : Type*} [AddCommGroup A] {c : A → Fin 3} {s : A}
    (hs : GoodDirection c s) : GoodDirection c (-s) := by
  intro v
  have h := hs (v + -s)
  simpa only [add_assoc, neg_add_cancel, add_zero] using h.symm

theorem GoodDirection.threeStepReachable {A : Type*} [AddCommGroup A]
    {c : A → Fin 3} {s : A} (hs : GoodDirection c s) : ThreeStepReachable c s :=
  ⟨s, s, -s, by simp only [add_assoc, add_neg_cancel, add_zero], hs, hs, hs.neg⟩

/-- A family of translated three-step words with mutually disjoint inverse direction pairs. -/
def HasRobustWords {A : Type*} [AddCommGroup A] (G : SimpleGraph A) (r : Nat) (s : A) : Prop :=
  ∃ W : Fin r → Fin 3 → A,
    (∀ i, W i 0 + W i 1 + W i 2 = s) ∧
    (∀ i p v, G.Adj v (v + W i p)) ∧
    (∀ i p, SignedDistinct s (W i p)) ∧
    (∀ i j, i ≠ j → ∀ p q, SignedDistinct (W i p) (W j q))

theorem threeStepReachable_of_robust_words {A : Type*} [AddCommGroup A] [Finite A]
    (G : SimpleGraph A) (c : A → Fin 3) {r : Nat} {s : A}
    (hs : ∀ v, G.Adj v (v + s)) (hwords : HasRobustWords G r s)
    (hbad : (badEdges G c).ncard ≤ r) : ThreeStepReachable c s := by
  by_cases hg : GoodDirection c s
  · exact hg.threeStepReachable
  obtain ⟨W, hsum, hadj, havoid, hdisjoint⟩ := hwords
  obtain ⟨i, hi⟩ := exists_good_word G c r s W hs hg hadj havoid hdisjoint hbad
  exact ⟨W i 0, W i 1, W i 2, hsum i, hi 0, hi 1, hi 2⟩

theorem character_deficits_of_robust_words {n : Nat} [NeZero n]
    (G : SimpleGraph (ZMod n)) (c : ZMod n → Fin 3) (J : Finset (ZMod n)) {r : Nat}
    (hJ : ∀ a ∈ J, ∀ b ∈ J, a ≠ -b)
    (hadj : ∀ a ∈ J, ∀ v, G.Adj v (v + a))
    (hunit : GoodDirection c 1) (hwords : ∀ s ∈ J, HasRobustWords G r s)
    (hbad : (badEdges G c).ncard ≤ r) :
    ∃ K : Int, (∑ s ∈ J, characterDeficit n (K * (s.val : Int))) ≤ (r : Int) := by
  have hreach : ∀ s ∈ J, ThreeStepReachable c s := fun s hs =>
    threeStepReachable_of_robust_words G c (hadj s hs) (hwords s hs) hbad
  obtain ⟨K, hK⟩ := coloring_character_deficits_le_badEdges G c J hJ hadj hunit hreach
  have hbad' : ((badEdges G c).ncard : Int) ≤ r := by exact_mod_cast hbad
  exact ⟨K, hK.trans hbad'⟩

theorem flux_exceeds_period_of_positive_deficit {n : Nat} (hn : 0 < n) {x z W : Int}
    (hflux : W = 3 * (n : Int) + 6 * x + 6 * n * z)
    (hdef : 0 < characterDeficit n x) : (n : Int) < W ∨ W < -(n : Int) := by
  by_contra h
  have hlo : -(n : Int) ≤ W := by omega
  have hhi : W ≤ (n : Int) := by omega
  have hzero := characterDeficit_le_of_flux hn (show (0 : Int) ≤ 0 by omega) hflux
    (by omega : -(n : Int) - 2 * 0 ≤ W) (by omega : W ≤ (n : Int) + 2 * 0)
  omega


theorem partialSum_eq_sum_range (f : Nat → Int) (n : Nat) :
    partialSum f n = ∑ j ∈ Finset.range n, f j := by
  induction n with
  | zero => simp [partialSum]
  | succ n ih => simp only [partialSum, ih, Finset.sum_range_succ]

theorem partialSum_zmod_eq_sum {n : Nat} [NeZero n] (f : ZMod n → Int) :
    partialSum (fun j => f (j : ZMod n)) n = ∑ v : ZMod n, f v := by
  rw [partialSum_eq_sum_range, ← Fin.sum_univ_eq_sum_range]
  apply Fintype.sum_bijective (fun j : Fin n => (j.val : ZMod n)) _ _ _ (fun _ => rfl)
  refine ⟨?_, fun v => ⟨⟨v.val, ZMod.val_lt v⟩, ZMod.natCast_zmod_val v⟩⟩
  intro i j h
  exact Fin.ext (((ZMod.natCast_eq_natCast_iff i.val j.val n).mp h).eq_of_lt_of_lt
    i.isLt j.isLt)

def groupWordStep {A : Type*} [Add A] (c : A → Fin 3) (a b d v : A) : Int :=
  maxStep (c v) (c (v + a)) + maxStep (c (v + a)) (c (v + a + b)) +
    maxStep (c (v + a + b)) (c (v + a + b + d))

theorem groupWordStep_cases {A : Type*} [Add A] (c : A → Fin 3) {a b d : A}
    (ha : GoodDirection c a) (hb : GoodDirection c b) (hd : GoodDirection c d) (v : A) :
    groupWordStep c a b d v = -3 ∨ groupWordStep c a b d v = -1 ∨
      groupWordStep c a b d v = 1 ∨ groupWordStep c a b d v = 3 := by
  have h₁ := maxStep_of_ne (ha v)
  have h₂ := maxStep_of_ne (hb (v + a))
  have h₃ := maxStep_of_ne (hd (v + a + b))
  dsimp [groupWordStep]
  omega

theorem groupWordStep_mod_three {A : Type*} [AddSemigroup A] (c : A → Fin 3)
    (a b d v : A) :
    groupWordStep c a b d v % 3 = ((c (v + (a + b + d))).val - (c v).val : Int) % 3 := by
  have h₁ := maxStep_mod_three (c v) (c (v + a))
  have h₂ := maxStep_mod_three (c (v + a)) (c (v + a + b))
  have h₃ := maxStep_mod_three (c (v + a + b)) (c (v + a + b + d))
  dsimp [groupWordStep]
  simp only [add_assoc] at *
  omega

theorem groupWordStep_max_bounds {A : Type*} [AddSemigroup A] (c : A → Fin 3)
    {a b d : A} (ha : GoodDirection c a) (hb : GoodDirection c b)
    (hd : GoodDirection c d) (v : A) :
    groupWordStep c a b d v ≤ maxStep (c v) (c (v + (a + b + d))) ∧
      -groupWordStep c a b d v ≤ maxStep (c (v + (a + b + d))) (c v) := by
  have hw := groupWordStep_cases c ha hb hd v
  have hm := groupWordStep_mod_three c a b d v
  have h₁ := maxStep_cases (c v) (c (v + (a + b + d)))
  have h₂ := maxStep_mod_three (c v) (c (v + (a + b + d)))
  have h₃ := maxStep_cases (c (v + (a + b + d))) (c v)
  have h₄ := maxStep_mod_three (c (v + (a + b + d))) (c v)
  omega

theorem group_direction_flat {A : Type*} [AddCommGroup A] (c : A → Fin 3)
    {u s : A} (hu : GoodDirection c u) (hs : GoodDirection c s) (v : A) :
    maxStep (c (v + u)) (c (v + u + s)) - maxStep (c v) (c (v + s)) =
      maxStep (c (v + s)) (c (v + s + u)) - maxStep (c v) (c (v + u)) := by
  have hc : v + u + s = v + s + u := by abel
  have hsq := proper_square_sum_zero (hu v) (hs (v + u))
    (by simpa only [hc] using (hu (v + s)).symm) (hs v).symm
  have hr₁ := maxStep_reverse (hs v)
  have hr₂ := maxStep_reverse (hu (v + s))
  rw [hc] at hsq ⊢
  omega

theorem groupWordStep_flat {A : Type*} [AddCommGroup A] (c : A → Fin 3)
    {u a b d : A} (hu : GoodDirection c u) (ha : GoodDirection c a)
    (hb : GoodDirection c b) (hd : GoodDirection c d) (v : A) :
    groupWordStep c a b d (v + u) - groupWordStep c a b d v =
      maxStep (c (v + (a + b + d))) (c (v + (a + b + d) + u)) -
        maxStep (c v) (c (v + u)) := by
  have h₁ := group_direction_flat c hu ha v
  have h₂ := group_direction_flat c hu hb (v + a)
  have h₃ := group_direction_flat c hu hd (v + a + b)
  dsimp [groupWordStep]
  have e₁ : v + a + u = v + u + a := by abel
  have e₂ : v + a + b + u = v + u + a + b := by abel
  simp only [← add_assoc, e₁, e₂] at h₁ h₂ h₃ ⊢
  omega

/-- A three-step height increment, including its compatibility with a proper base direction. -/
structure IsColorLift {A : Type*} [Add A] (c : A → Fin 3) (u s : A) (e : A → Int) : Prop where
  odd : ∀ v, e v % 2 = 1
  mod_three : ∀ v, e v % 3 = ((c (v + s)).val - (c v).val : Int) % 3
  bound : ∀ v, -3 ≤ e v ∧ e v ≤ 3
  flat : ∀ v, e (v + u) - e v =
    maxStep (c (v + s)) (c (v + s + u)) - maxStep (c v) (c (v + u))

theorem exists_colorLift {A : Type*} [AddCommGroup A] (c : A → Fin 3) {u s : A}
    (hu : GoodDirection c u) (hs : ThreeStepReachable c s) :
    ∃ e : A → Int, IsColorLift c u s e := by
  obtain ⟨a, b, d, rfl, ha, hb, hd⟩ := hs
  refine ⟨groupWordStep c a b d, ?_⟩
  refine ⟨?_, groupWordStep_mod_three c a b d, ?_, groupWordStep_flat c hu ha hb hd⟩
  · intro v
    have hw := groupWordStep_cases c ha hb hd v
    omega
  · intro v
    have hw := groupWordStep_cases c ha hb hd v
    omega

theorem IsColorLift.max_bounds {A : Type*} [Add A] {c : A → Fin 3} {u s : A}
    {e : A → Int} (he : IsColorLift c u s e) (v : A) :
    e v ≤ maxStep (c v) (c (v + s)) ∧ -e v ≤ maxStep (c (v + s)) (c v) := by
  have hm := he.mod_three v
  have ho := he.odd v
  have hb := he.bound v
  have h₁ := maxStep_cases (c v) (c (v + s))
  have h₂ := maxStep_mod_three (c v) (c (v + s))
  have h₃ := maxStep_cases (c (v + s)) (c v)
  have h₄ := maxStep_mod_three (c (v + s)) (c v)
  omega

theorem sum_mul_unit {n : Nat} [NeZero n] (f : ZMod n → Int) (u : (ZMod n)ˣ) :
    (∑ v : ZMod n, f (v * (u : ZMod n))) = ∑ v : ZMod n, f v := by
  apply Fintype.sum_bijective (fun v : ZMod n => v * (u : ZMod n)) _ _ _ (fun _ => rfl)
  refine ⟨u.isUnit.mul_left_injective, ?_⟩
  intro v
  refine ⟨v * (↑u⁻¹ : ZMod n), ?_⟩
  simp only [mul_assoc, Units.inv_mul, mul_one]

/-- A single cyclic character controls every compatible lift, for any proper unit direction. -/
theorem exists_group_flux_character {n : Nat} [NeZero n] (c : ZMod n → Fin 3)
    (u : (ZMod n)ˣ) :
    ∃ K : Int, ∀ (s : ZMod n) (e : ZMod n → Int), IsColorLift c u s e →
      ∃ z : Int, (∑ v : ZMod n, e v) = 3 * (n : Int) + 6 * K * s.val + 6 * n * z := by
  let C : Nat → Fin 3 := fun j => c ((j : ZMod n) * (u : ZMod n))
  have hc : Function.Periodic C n := by
    intro j
    simp only [C, Nat.cast_add, ZMod.natCast_self, add_zero]
  obtain ⟨K, hK⟩ := exists_flux_character C (directionStep C 1)
    (by simpa using hc 0) (directionStep_period C hc 1)
    (fun _ => maxStep_mod_three _ _) (fun _ => maxStep_mod_two _ _)
  refine ⟨K * ((↑u⁻¹ : ZMod n).val : Int), ?_⟩
  intro s e he
  let a := (s * (↑u⁻¹ : ZMod n)).val
  let E : Nat → Int := fun j => e ((j : ZMod n) * (u : ZMod n))
  have ha : (a : ZMod n) * (u : ZMod n) = s := by
    simp only [a, ZMod.natCast_zmod_val, mul_assoc, Units.inv_mul, mul_one]
  have hflat : ∀ v, E (v + 1) - E v = directionStep C 1 (v + a) - directionStep C 1 v := by
    intro v
    simpa only [E, C, directionStep, Nat.cast_add, Nat.cast_one, add_mul, one_mul, ha,
      add_assoc] using he.flat ((v : ZMod n) * (u : ZMod n))
  obtain ⟨z, hz⟩ := hK a E hflat
    (by simpa only [E, C, Nat.cast_zero, zero_mul, ha, zero_add] using he.mod_three 0)
    (by simpa only [E, Nat.cast_zero, zero_mul] using he.odd 0)
  have hsum : partialSum E n = ∑ v : ZMod n, e v := by
    exact (partialSum_zmod_eq_sum (fun v => e (v * (u : ZMod n)))).trans (sum_mul_unit e u)
  rw [hsum] at hz
  have hcongr : (a : ZMod n) =
      (((s.val : Int) * ((↑u⁻¹ : ZMod n).val : Int) : Int) : ZMod n) := by
    simp only [a, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val]
  have hdiv : (n : Int) ∣ (s.val : Int) * ((↑u⁻¹ : ZMod n).val : Int) - (a : Int) :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ n).mp (by simpa only [Int.cast_natCast] using hcongr)
  obtain ⟨w, hw⟩ := hdiv
  refine ⟨z - K * w, ?_⟩
  have ha' : (a : Int) = (s.val : Int) * ((↑u⁻¹ : ZMod n).val : Int) - (n : Int) * w := by
    linarith
  rw [hz, ha']
  ring

theorem IsColorLift.bad_bounds {A : Type*} [Add A] {c : A → Fin 3}
    {u s : A} {e : A → Int} (he : IsColorLift c u s e) (v : A) :
    -1 - 2 * (if c v = c (v + s) then (1 : Int) else 0) ≤ e v ∧
      e v ≤ 1 + 2 * (if c v = c (v + s) then (1 : Int) else 0) := by
  by_cases hv : c v = c (v + s)
  · have h := he.bound v
    simp only [if_pos hv]
    omega
  · have hb := he.max_bounds v
    have h₁ := maxStep_of_ne hv
    have h₂ := maxStep_of_ne (Ne.symm hv)
    simp only [if_neg hv]
    omega

theorem IsColorLift.flux_bounds {n : Nat} [NeZero n] {c : ZMod n → Fin 3}
    {u s : ZMod n} {e : ZMod n → Int} (he : IsColorLift c u s e) :
    -(n : Int) - 2 * ({v : ZMod n | c v = c (v + s)}.ncard : Int) ≤ ∑ v, e v ∧
      (∑ v, e v) ≤ (n : Int) + 2 * ({v : ZMod n | c v = c (v + s)}.ncard : Int) := by
  classical
  have hcount : (∑ v : ZMod n, if c v = c (v + s) then (1 : Int) else 0) =
      ({v : ZMod n | c v = c (v + s)}.ncard : Int) := by
    have hset : Finset.univ.filter (fun v : ZMod n => c v = c (v + s)) =
        {v : ZMod n | c v = c (v + s)}.toFinset := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_toFinset, Set.mem_ofPred_eq]
    rw [Finset.sum_boole, hset, Set.ncard_eq_toFinset_card']
  have hlo := Finset.sum_le_sum (fun (v : ZMod n) (_ : v ∈ Finset.univ) => (he.bad_bounds v).1)
  have hhi := Finset.sum_le_sum (fun (v : ZMod n) (_ : v ∈ Finset.univ) => (he.bad_bounds v).2)
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_neg, mul_one, hcount] at hlo hhi
  exact ⟨hlo, hhi⟩

theorem IsColorLift.deficit_le {n : Nat} [NeZero n] {c : ZMod n → Fin 3}
    {u s : ZMod n} {e : ZMod n → Int} (he : IsColorLift c u s e) {K z : Int}
    (hflux : (∑ v : ZMod n, e v) = 3 * (n : Int) + 6 * K * s.val + 6 * n * z) :
    characterDeficit n (K * (s.val : Int)) ≤ {v : ZMod n | c v = c (v + s)}.ncard := by
  have hb := he.flux_bounds
  exact characterDeficit_le_of_flux (NeZero.pos n) (Int.natCast_nonneg _)
    (by simpa only [Int.mul_assoc] using hflux) hb.1 hb.2

/-- Both the total deficit estimate and all compatible flux witnesses use the same character. -/
theorem exists_character_with_lifts {n : Nat} [NeZero n]
    (G : SimpleGraph (ZMod n)) (c : ZMod n → Fin 3) (J : Finset (ZMod n)) (u : (ZMod n)ˣ)
    (hJ : ∀ a ∈ J, ∀ b ∈ J, a ≠ -b)
    (hadj : ∀ a ∈ J, ∀ v, G.Adj v (v + a)) (hu : GoodDirection c u)
    (hwalk : ∀ s ∈ J, ThreeStepReachable c s) :
    ∃ K : Int,
      (∑ s ∈ J, characterDeficit n (K * (s.val : Int))) ≤ (badEdges G c).ncard ∧
      (∀ s, ThreeStepReachable c s → ∃ (e : ZMod n → Int) (z : Int),
        IsColorLift c u s e ∧
          (∑ v : ZMod n, e v) = 3 * (n : Int) + 6 * K * s.val + 6 * n * z) := by
  obtain ⟨K, hK⟩ := exists_group_flux_character c u
  refine ⟨K, ?_, ?_⟩
  · have hb : ∀ s ∈ J, characterDeficit n (K * (s.val : Int)) ≤
        ({v : ZMod n | c v = c (v + s)}.ncard : Int) := by
      intro s hs
      obtain ⟨e, he⟩ := exists_colorLift c hu (hwalk s hs)
      obtain ⟨z, hz⟩ := hK s e he
      exact he.deficit_le hz
    have hsum := Finset.sum_le_sum hb
    have hcard := sum_bad_connections_le G c J hJ hadj
    have hcard' : (∑ s ∈ J, ({v : ZMod n | c v = c (v + s)}.ncard : Int)) ≤
        (badEdges G c).ncard := by exact_mod_cast hcard
    exact hsum.trans hcard'
  · intro s hs
    obtain ⟨e, he⟩ := exists_colorLift c hu hs
    obtain ⟨z, hz⟩ := hK s e he
    exact ⟨e, z, he, hz⟩

theorem ThreeStepReachable.neg {A : Type*} [AddCommGroup A] {c : A → Fin 3} {s : A}
    (hs : ThreeStepReachable c s) : ThreeStepReachable c (-s) := by
  obtain ⟨a, b, d, rfl, ha, hb, hd⟩ := hs
  exact ⟨-a, -b, -d, by abel, ha.neg, hb.neg, hd.neg⟩

theorem partialSum_blocks (f : Nat → Int) (q m : Nat) :
    partialSum f (m * q) = partialSum (fun b => windowSum f (b * q) q) m := by
  induction m with
  | zero => simp [partialSum]
  | succ m ih =>
    rw [Nat.succ_mul, partialSum_split, ih, partialSum]

theorem partialSum_reverse (f : Nat → Int) (n : Nat) :
    partialSum (fun j => f (n - 1 - j)) n = partialSum f n := by
  simp only [partialSum_eq_sum_range]
  exact Finset.sum_range_reflect f n

theorem partialSum_neg (f : Nat → Int) (n : Nat) :
    partialSum (fun j => -f j) n = -partialSum f n := by
  simp only [partialSum_eq_sum_range, Finset.sum_neg_distrib]

/-- The winding bound works in both orientations of an embedded gap. -/
theorem path_gain_bounds_of_badEdges_bound {V : Type*} [Finite V] (G : SimpleGraph V)
    (c : V → Fin 3) (t : Nat) (f : Nat → V) (δ : Nat → Int)
    (hinj : ∀ i < 3 * t + 2, ∀ j < 3 * t + 2, f i = f j → i = j)
    (hadj : ∀ i < 3 * t + 2, ∀ j < 3 * t + 2,
      i < j → (j - i) % 3 = 1 → G.Adj (f i) (f j))
    (hbad : (badEdges G c).ncard ≤ t)
    (hstep : ∀ j < 3 * t + 1,
      δ j ≤ maxStep (c (f j)) (c (f (j + 1))) ∧
        -δ j ≤ maxStep (c (f (j + 1))) (c (f j))) :
    -(3 * (t : Int) + 1) ≤ partialSum δ (3 * t + 1) ∧
      partialSum δ (3 * t + 1) ≤ 3 * (t : Int) + 1 := by
  have hhi := path_gain_le_of_badEdges_bound G c t f δ hinj hadj hbad (fun j hj => (hstep j hj).1)
  let q := 3 * t + 1
  let f' : Nat → V := fun j => f (q - j)
  let δ' : Nat → Int := fun j => -δ (q - 1 - j)
  have hinj' : ∀ i < 3 * t + 2, ∀ j < 3 * t + 2, f' i = f' j → i = j := by
    intro i hi j hj he
    have h := hinj (q - i) (by dsimp [q]; omega) (q - j) (by dsimp [q]; omega) he
    dsimp [q] at h
    omega
  have hadj' : ∀ i < 3 * t + 2, ∀ j < 3 * t + 2,
      i < j → (j - i) % 3 = 1 → G.Adj (f' i) (f' j) := by
    intro i hi j hj hij hm
    apply SimpleGraph.Adj.symm
    apply hadj (q - j) (by dsimp [q]; omega) (q - i) (by dsimp [q]; omega)
      (by dsimp [q]; omega)
    have he : q - i - (q - j) = j - i := by dsimp [q]; omega
    rw [he]
    exact hm
  have hstep' : ∀ j < 3 * t + 1, δ' j ≤ maxStep (c (f' j)) (c (f' (j + 1))) := by
    intro j hj
    have h := (hstep (q - 1 - j) (by dsimp [q]; omega)).2
    have h₁ : q - 1 - j + 1 = q - j := by dsimp [q]; omega
    have h₂ : q - 1 - j = q - (j + 1) := by omega
    rw [h₁] at h
    simpa only [δ', f', h₂] using h
  have hlo := path_gain_le_of_badEdges_bound G c t f' δ' hinj' hadj' hbad hstep'
  have hrev : partialSum δ' (3 * t + 1) = -partialSum δ (3 * t + 1) := by
    change partialSum (fun j => -δ (q - 1 - j)) q = -partialSum δ q
    rw [partialSum_neg, partialSum_reverse]
  rw [hrev] at hlo
  exact ⟨by omega, hhi⟩

theorem sum_affine_unit {n : Nat} [NeZero n] (f : ZMod n → Int)
    (x : ZMod n) (u : (ZMod n)ˣ) :
    partialSum (fun j => f (x + (j : ZMod n) * (u : ZMod n))) n = ∑ v : ZMod n, f v := by
  rw [partialSum_zmod_eq_sum (fun v => f (x + v * (u : ZMod n)))]
  apply Fintype.sum_bijective (fun v : ZMod n => x + v * (u : ZMod n)) _ _ _ (fun _ => rfl)
  refine ⟨fun v w he => u.isUnit.mul_left_injective (add_left_cancel he), ?_⟩
  intro v
  refine ⟨(v - x) * (↑u⁻¹ : ZMod n), ?_⟩
  simp only [mul_assoc, Units.inv_mul, mul_one]
  abel

theorem affine_unit_injective_on_interval {n : Nat} [NeZero n]
    (x : ZMod n) (u : (ZMod n)ˣ) (b : Nat) {i j : Nat} (hi : i < n) (hj : j < n)
    (he : x + ((b + i : Nat) : ZMod n) * (u : ZMod n) =
      x + ((b + j : Nat) : ZMod n) * (u : ZMod n)) : i = j := by
  have hc := u.isUnit.mul_left_injective (add_left_cancel he)
  simp only [Nat.cast_add] at hc
  have hc' : (i : ZMod n) = (j : ZMod n) := add_left_cancel hc
  exact ((ZMod.natCast_eq_natCast_iff i j n).mp hc').eq_of_lt_of_lt hi hj

/-- Consecutive gaps in a unit Hamiltonian order contain their full Andrásfai graphs. -/
def HasAndrasfaiGaps {n : Nat} (G : SimpleGraph (ZMod n)) (a : (ZMod n)ˣ) (t : Nat) : Prop :=
  ∃ (m : Nat) (x : ZMod n), n = m * (3 * t + 1) ∧
    ∀ b < m, ∀ i < 3 * t + 2, ∀ j < 3 * t + 2, i < j → (j - i) % 3 = 1 →
      G.Adj (x + ((b * (3 * t + 1) + i : Nat) : ZMod n) * (a : ZMod n))
        (x + ((b * (3 * t + 1) + j : Nat) : ZMod n) * (a : ZMod n))

/-- Few bad edges bound the flux in any unit direction whose cycle has filled gaps. -/
theorem flux_bounds_of_andrasfai_gaps {n : Nat} [NeZero n]
    (G : SimpleGraph (ZMod n)) (c : ZMod n → Fin 3) (a : (ZMod n)ˣ) {t : Nat}
    (ht : 3 * t + 1 < n) (hgaps : HasAndrasfaiGaps G a t)
    (hbad : (badEdges G c).ncard ≤ t) (e : ZMod n → Int)
    (hstep : ∀ v, e v ≤ maxStep (c v) (c (v + (a : ZMod n))) ∧
      -e v ≤ maxStep (c (v + (a : ZMod n))) (c v)) :
    -(n : Int) ≤ ∑ v : ZMod n, e v ∧ (∑ v : ZMod n, e v) ≤ (n : Int) := by
  obtain ⟨m, x, hn, hg⟩ := hgaps
  let q := 3 * t + 1
  let F : Nat → Int := fun j => e (x + (j : ZMod n) * (a : ZMod n))
  have hgap : ∀ b < m, -(3 * (t : Int) + 1) ≤ windowSum F (b * q) q ∧
      windowSum F (b * q) q ≤ 3 * (t : Int) + 1 := by
    intro b hb
    let f : Nat → ZMod n := fun j => x + ((b * q + j : Nat) : ZMod n) * (a : ZMod n)
    apply path_gain_bounds_of_badEdges_bound G c t f (fun j => F (b * q + j))
    · intro i hi j hj he
      exact affine_unit_injective_on_interval x a (b * q) (by omega) (by omega) he
    · exact hg b hb
    · exact hbad
    · intro j _
      have hnext : f (j + 1) = f j + (a : ZMod n) := by
        dsimp [f]
        simp only [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
        abel
      change e (f j) ≤ maxStep (c (f j)) (c (f (j + 1))) ∧
        -e (f j) ≤ maxStep (c (f (j + 1))) (c (f j))
      rw [hnext]
      exact hstep (f j)
  have hhi := partialSum_le (fun b => windowSum F (b * q) q) (3 * (t : Int) + 1) m
    (fun b hb => (hgap b hb).2)
  have hlo := partialSum_le (fun b => -windowSum F (b * q) q) (3 * (t : Int) + 1) m
    (fun b hb => by have h := (hgap b hb).1; omega)
  rw [partialSum_neg, ← partialSum_blocks, ← hn] at hlo
  rw [← partialSum_blocks, ← hn] at hhi
  have hsum : partialSum F n = ∑ v : ZMod n, e v := sum_affine_unit e x a
  have hn' : (n : Int) = (m : Int) * (3 * (t : Int) + 1) := by exact_mod_cast hn
  rw [hsum, ← hn'] at hlo hhi
  exact ⟨by omega, hhi⟩

/-- A finite construction criterion for the full robustness and vertex criticality at four colors. -/
theorem erdos944_four_of_filled_gaps {n : Nat} [NeZero n] {I : Type*} [Fintype I]
    (G : SimpleGraph (ZMod n)) (J : Finset (ZMod n)) (a : I → (ZMod n)ˣ) {r t : Nat}
    (hrt : r ≤ t) (htn : 3 * t + 1 < n) (hsize : r < Fintype.card I)
    (hholes : ∀ v, ∃ c : ZMod n → Fin 3,
      ∀ u w, u ≠ v → w ≠ v → G.Adj u w → c u ≠ c w)
    (hJ : ∀ s ∈ J, ∀ s' ∈ J, s ≠ -s')
    (hadj : ∀ s ∈ J, ∀ v, G.Adj v (v + s))
    (hsep : ∀ i j, i ≠ j → SignedDistinct (a i : ZMod n) (a j : ZMod n))
    (hrep : ∀ i, (a i : ZMod n) ∈ J ∨ -(a i : ZMod n) ∈ J)
    (hwords : ∀ s ∈ J, HasRobustWords G r s)
    (hgaps : ∀ i, HasAndrasfaiGaps G (a i) t)
    (hcharacter : ∀ K : Int, (∑ s ∈ J, characterDeficit n (K * (s.val : Int))) ≤ (r : Int) →
      ∃ i, 0 < characterDeficit n (K * ((a i : ZMod n).val : Int))) :
    Erdos944.SimpleGraph.IsErdos944 G 4 r := by
  apply critical_robust_of_punctured G hholes
  intro c
  by_contra hmany
  have hbad : (badEdges G c).ncard ≤ r := by omega
  have haadj : ∀ i v, G.Adj v (v + (a i : ZMod n)) := by
    intro i v
    rcases hrep i with hi | hi
    · exact hadj _ hi v
    · have h := (hadj _ hi (v + (a i : ZMod n))).symm
      simpa only [add_assoc, add_neg_cancel, add_zero] using h
  obtain ⟨i₀, hi₀⟩ := exists_good_direction G c (fun i => (a i : ZMod n)) hsep haadj
    (hbad.trans_lt hsize)
  have hwalk : ∀ s ∈ J, ThreeStepReachable c s := fun s hs =>
    threeStepReachable_of_robust_words G c (hadj s hs) (hwords s hs) hbad
  obtain ⟨K, hK, hlifts⟩ := exists_character_with_lifts G c J (a i₀) hJ hadj hi₀ hwalk
  have hKr : (∑ s ∈ J, characterDeficit n (K * (s.val : Int))) ≤ (r : Int) :=
    hK.trans (by exact_mod_cast hbad)
  obtain ⟨i, hi⟩ := hcharacter K hKr
  have hai : ThreeStepReachable c (a i : ZMod n) := by
    rcases hrep i with hi | hi
    · exact hwalk _ hi
    · simpa only [neg_neg] using (hwalk _ hi).neg
  obtain ⟨e, z, he, hz⟩ := hlifts (a i : ZMod n) hai
  have hb := flux_bounds_of_andrasfai_gaps G c (a i) htn (hgaps i) (hbad.trans hrt) e he.max_bounds
  have hlarge := flux_exceeds_period_of_positive_deficit (NeZero.pos n)
    (by simpa only [Int.mul_assoc] using hz) hi
  omega

theorem normalizedCoordinate_dvd_of_same_residue {n q : Nat} [NeZero n]
    (hq : q ∣ n) (a : (ZMod n)ˣ) {v x : ZMod n}
    (hx : ZMod.castHom hq (ZMod q) x = ZMod.castHom hq (ZMod q) v) :
    q ∣ normalizedCoordinate a v x := by
  let π := ZMod.castHom hq (ZMod q)
  have hcast : ((normalizedCoordinate a v x : Nat) : ZMod q) = 0 := by
    have h : π ((↑a⁻¹ : ZMod n) * (x - v)) = 0 := by
      rw [map_mul, map_sub, hx, sub_self, mul_zero]
    simpa only [π, ZMod.castHom_apply, ZMod.cast_eq_val, normalizedCoordinate] using h
  exact (ZMod.natCast_eq_zero_iff _ _).mp hcast

theorem normalizedCoordinate_add_unit {n : Nat} [NeZero n] (a : (ZMod n)ˣ)
    (v x : ZMod n) (j : Nat) :
    normalizedCoordinate a v (x + (j : ZMod n) * (a : ZMod n)) =
      (normalizedCoordinate a v x + j) % n := by
  have he : (↑a⁻¹ : ZMod n) * (x + (j : ZMod n) * (a : ZMod n) - v) =
      (↑a⁻¹ : ZMod n) * (x - v) + (j : ZMod n) := by
    calc
      _ = (↑a⁻¹ : ZMod n) * (x - v) + (j : ZMod n) * ((↑a⁻¹ : ZMod n) * (a : ZMod n)) := by ring
      _ = _ := by rw [Units.inv_mul, mul_one]
  simp only [normalizedCoordinate, he, ZMod.val_add, ZMod.val_natCast, Nat.add_mod_mod]

/-- A puncture in the same residue class as the gap start cannot lie inside that gap. -/
theorem normalizedCoordinate_unwrapped_in_gap {n q : Nat} [NeZero n]
    (hq : q ∣ n) (a : (ZMod n)ˣ) {v x : ZMod n}
    (hx : ZMod.castHom hq (ZMod q) x = ZMod.castHom hq (ZMod q) v)
    {j : Nat} (hj : j ≤ q) (hu : x + (j : ZMod n) * (a : ZMod n) ≠ v) :
    normalizedCoordinate a v (x + (j : ZMod n) * (a : ZMod n)) =
      normalizedCoordinate a v x + j := by
  let b := normalizedCoordinate a v x
  have hb : b < n := ZMod.val_lt _
  have hbd : q ∣ b := normalizedCoordinate_dvd_of_same_residue hq a hx
  have hd : q ∣ n - b := Nat.dvd_sub hq hbd
  have hqle : q ≤ n - b := Nat.le_of_dvd (by omega) hd
  have hle : b + j ≤ n := by omega
  have hcoord := normalizedCoordinate_add_unit a v x j
  have hpos := normalizedCoordinate_pos a hu
  have hlt : b + j < n := by
    by_contra h
    have he : b + j = n := by omega
    change normalizedCoordinate a v (x + (j : ZMod n) * (a : ZMod n)) = (b + j) % n at hcoord
    rw [he, Nat.mod_self] at hcoord
    omega
  exact hcoord.trans (Nat.mod_eq_of_lt hlt)

theorem puncturedColor_ne_in_same_gap {n q : Nat} [NeZero n]
    (hq : q ∣ n) (a : (ZMod n)ˣ) {v x : ZMod n}
    (hx : ZMod.castHom hq (ZMod q) x = ZMod.castHom hq (ZMod q) v)
    {i j : Nat} (hij : i < j) (hj : j ≤ q) (hd : (j - i) % 3 = 1)
    (hi' : x + (i : ZMod n) * (a : ZMod n) ≠ v)
    (hj' : x + (j : ZMod n) * (a : ZMod n) ≠ v) :
    puncturedColor a v (x + (i : ZMod n) * (a : ZMod n)) ≠
      puncturedColor a v (x + (j : ZMod n) * (a : ZMod n)) := by
  apply puncturedColor_ne_of_unwrapped a hd
  rw [normalizedCoordinate_unwrapped_in_gap hq a hx hj hj',
    normalizedCoordinate_unwrapped_in_gap hq a hx (by omega : i ≤ q) hi']
  omega

def FilledGapEdge {n q : Nat} (hq : q ∣ n) (a : ZMod q → (ZMod n)ˣ)
    (u w : ZMod n) : Prop :=
  ∃ (i : ZMod q) (x : ZMod n) (j k : Nat),
    ZMod.castHom hq (ZMod q) x = i ∧ j < k ∧ k ≤ q ∧ (k - j) % 3 = 1 ∧
      u = x + (j : ZMod n) * (a i : ZMod n) ∧ w = x + (k : ZMod n) * (a i : ZMod n)

/-- The cyclic connection graph with an Andrásfai graph inserted into every designated gap. -/
def augmentedGraph {n q : Nat} (hq : q ∣ n) (a : ZMod q → (ZMod n)ˣ)
    (J : Finset (ZMod n)) : SimpleGraph (ZMod n) where
  Adj u w := u ≠ w ∧ (w - u ∈ J ∨ u - w ∈ J ∨ FilledGapEdge hq a u w ∨ FilledGapEdge hq a w u)
  symm.symm u w h := by
    refine ⟨h.1.symm, ?_⟩
    rcases h.2 with h | h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inr (Or.inr (Or.inl h))
  loopless.irrefl u h := h.1 rfl

theorem augmentedGraph_core_adj {n q : Nat} (hq : q ∣ n) (a : ZMod q → (ZMod n)ˣ)
    (J : Finset (ZMod n)) (hJ : ∀ s ∈ J, ∀ s' ∈ J, s ≠ -s') {s : ZMod n} (hs : s ∈ J)
    (v : ZMod n) : (augmentedGraph hq a J).Adj v (v + s) := by
  refine ⟨?_, Or.inl (by simpa only [add_sub_cancel_left] using hs)⟩
  intro he
  have hz : s = 0 := by simpa only [add_eq_left] using he.symm
  exact hJ s hs s hs (by simp only [hz, neg_zero])

theorem filledGapEdge_puncturedColor {n q : Nat} [NeZero n]
    (hn : n % 3 = 1) (hq : q ∣ n) (a : ZMod q → (ZMod n)ˣ)
    (hoff : ∀ i j : ZMod q, i ≠ j → ∀ ℓ : Nat, ℓ ≤ q → ℓ % 3 = 1 →
      NormalDifference n (((↑(a i)⁻¹ : ZMod n) * (ℓ : ZMod n) * (a j : ZMod n)).val))
    {v u w : ZMod n} (hu : u ≠ v) (hw : w ≠ v) (hgap : FilledGapEdge hq a u w) :
    puncturedColor (a (ZMod.castHom hq (ZMod q) v)) v u ≠
      puncturedColor (a (ZMod.castHom hq (ZMod q) v)) v w := by
  obtain ⟨i, x, j, k, hx, hjk, hk, hd, rfl, rfl⟩ := hgap
  let p := ZMod.castHom hq (ZMod q) v
  by_cases hip : i = p
  · simp only [hip] at hx hu hw ⊢
    exact puncturedColor_ne_in_same_gap hq (a p) hx hjk hk hd hu hw
  · apply puncturedColor_ne_of_normalDifference hn (a p) hu hw
    have he : normalizedCoordinate (a p)
        (x + (j : ZMod n) * (a i : ZMod n)) (x + (k : ZMod n) * (a i : ZMod n)) =
        (((↑(a p)⁻¹ : ZMod n) * ((k - j : Nat) : ZMod n) * (a i : ZMod n)).val) := by
      unfold normalizedCoordinate
      congr 1
      rw [Nat.cast_sub (by omega : j ≤ k)]
      ring
    rw [he]
    exact hoff p i (Ne.symm hip) (k - j) (by omega) hd

theorem augmentedGraph_punctured {n q : Nat} [NeZero n]
    (hn : n % 3 = 1) (hq : q ∣ n) (a : ZMod q → (ZMod n)ˣ) (J : Finset (ZMod n))
    (hnormal : ∀ i : ZMod q, ∀ s ∈ J, NormalDifference n (((↑(a i)⁻¹ : ZMod n) * s).val))
    (hoff : ∀ i j : ZMod q, i ≠ j → ∀ ℓ : Nat, ℓ ≤ q → ℓ % 3 = 1 →
      NormalDifference n (((↑(a i)⁻¹ : ZMod n) * (ℓ : ZMod n) * (a j : ZMod n)).val))
    (v : ZMod n) : ∃ c : ZMod n → Fin 3,
      ∀ u w, u ≠ v → w ≠ v → (augmentedGraph hq a J).Adj u w → c u ≠ c w := by
  let p := ZMod.castHom hq (ZMod q) v
  refine ⟨puncturedColor (a p) v, ?_⟩
  intro u w hu hw hedge
  rcases hedge.2 with hs | hs | hg | hg
  · exact puncturedColor_ne_of_normalDifference hn (a p) hu hw (hnormal p (w - u) hs)
  · exact (puncturedColor_ne_of_normalDifference hn (a p) hw hu (hnormal p (u - w) hs)).symm
  · exact filledGapEdge_puncturedColor hn hq a hoff hu hw hg
  · exact (filledGapEdge_puncturedColor hn hq a hoff hw hu hg).symm

theorem augmentedGraph_filled_gaps {n t : Nat} [NeZero n]
    (hq : 3 * t + 1 ∣ n) (hn : 3 * t + 1 < n)
    (a : ZMod (3 * t + 1) → (ZMod n)ˣ) (J : Finset (ZMod n)) (i : ZMod (3 * t + 1)) :
    HasAndrasfaiGaps (augmentedGraph hq a J) (a i) t := by
  let q := 3 * t + 1
  let : NeZero q := ⟨by dsimp [q]; omega⟩
  let x : ZMod n := (i.val : ZMod n)
  have hx : ZMod.castHom hq (ZMod q) x = i := by
    simp only [x, map_natCast, ZMod.natCast_zmod_val]
  refine ⟨n / q, x, (Nat.div_mul_cancel hq).symm, ?_⟩
  intro b _ j hj k hk hjk hd
  refine ⟨?_, Or.inr (Or.inr (Or.inl ?_))⟩
  · intro he
    have h := affine_unit_injective_on_interval x (a i) (b * q) (by omega) (by omega) he
    omega
  · refine ⟨i, x + ((b * q : Nat) : ZMod n) * (a i : ZMod n), j, k, ?_, hjk, by omega, hd, ?_, ?_⟩
    · have hzero : ((b * q : Nat) : ZMod q) = 0 := by
        simp only [Nat.cast_mul, ZMod.natCast_self, mul_zero]
      simpa only [map_add, map_mul, map_natCast, hzero, zero_mul, add_zero] using hx
    · simp only [q, Nat.cast_add, add_mul, add_assoc]
    · simp only [q, Nat.cast_add, add_mul, add_assoc]

/-- An arithmetic version of the robust-word requirement, before a graph is assembled. -/
def HasSignedWords {A : Type*} [AddCommGroup A] (J : Finset A) (r : Nat) (s : A) : Prop :=
  ∃ W : Fin r → Fin 3 → A,
    (∀ i, W i 0 + W i 1 + W i 2 = s) ∧
    (∀ i p, W i p ∈ J ∨ -W i p ∈ J) ∧
    (∀ i p, SignedDistinct s (W i p)) ∧
    (∀ i j, i ≠ j → ∀ p q, SignedDistinct (W i p) (W j q))

theorem HasSignedWords.to_robust_words {A : Type*} [AddCommGroup A]
    {J : Finset A} {r : Nat} {s : A} (hs : HasSignedWords J r s) (G : SimpleGraph A)
    (hadj : ∀ a ∈ J, ∀ v, G.Adj v (v + a)) : HasRobustWords G r s := by
  obtain ⟨W, hsum, hmem, havoid, hsep⟩ := hs
  refine ⟨W, hsum, ?_, havoid, hsep⟩
  intro i p v
  rcases hmem i p with h | h
  · exact hadj _ h v
  · have he := (hadj _ h (v + W i p)).symm
    simpa only [add_assoc, add_neg_cancel, add_zero] using he

/-- The entire graph construction is reduced to finite arithmetic conditions on cyclic data. -/
theorem erdos944_four_of_cyclic_data {n r t : Nat} [NeZero n]
    (hrt : r ≤ t) (hn : n % 3 = 1) (hq : 3 * t + 1 ∣ n) (htn : 3 * t + 1 < n)
    (a : ZMod (3 * t + 1) → (ZMod n)ˣ) (J : Finset (ZMod n))
    (hJ : ∀ s ∈ J, ∀ s' ∈ J, s ≠ -s')
    (hsep : ∀ i j, i ≠ j → SignedDistinct (a i : ZMod n) (a j : ZMod n))
    (hrep : ∀ i, (a i : ZMod n) ∈ J ∨ -(a i : ZMod n) ∈ J)
    (hnormal : ∀ i, ∀ s ∈ J, NormalDifference n (((↑(a i)⁻¹ : ZMod n) * s).val))
    (hoff : ∀ i j, i ≠ j → ∀ ℓ : Nat, ℓ ≤ 3 * t + 1 → ℓ % 3 = 1 →
      NormalDifference n (((↑(a i)⁻¹ : ZMod n) * (ℓ : ZMod n) * (a j : ZMod n)).val))
    (hwords : ∀ s ∈ J, HasSignedWords J r s)
    (hcharacter : ∀ K : Int, (∑ s ∈ J, characterDeficit n (K * (s.val : Int))) ≤ (r : Int) →
      ∃ i, 0 < characterDeficit n (K * ((a i : ZMod n).val : Int))) :
    ∃ G : SimpleGraph (ZMod n), Erdos944.SimpleGraph.IsErdos944 G 4 r := by
  let : NeZero (3 * t + 1) := ⟨by omega⟩
  let G := augmentedGraph hq a J
  have hadj : ∀ s ∈ J, ∀ v, G.Adj v (v + s) := fun s hs v =>
    augmentedGraph_core_adj hq a J hJ hs v
  refine ⟨G, erdos944_four_of_filled_gaps G J a hrt htn ?_ ?_ hJ hadj hsep hrep ?_ ?_ hcharacter⟩
  · rw [ZMod.card]
    omega
  · exact augmentedGraph_punctured hn hq a J hnormal hoff
  · intro s hs
    exact (hwords s hs).to_robust_words G hadj
  · exact augmentedGraph_filled_gaps hq htn a J

theorem normalDifference_pos {n s : Nat} (hn : 1 < n) (hs : NormalDifference n s) :
    0 < s := by
  rcases hs with h | h | h <;> omega

theorem normalDifference_zmod_neg {n : Nat} [NeZero n] (hn : n % 3 = 1) (hn' : 1 < n)
    {s : ZMod n} (hs : NormalDifference n s.val) : NormalDifference n (-s).val := by
  have hspos := normalDifference_pos hn' hs
  let : NeZero s := ⟨fun hz => by simp only [hz, ZMod.val_zero] at hspos; omega⟩
  rw [ZMod.val_neg_of_ne_zero]
  exact normalDifference_neg hn hspos (ZMod.val_lt s) hs

noncomputable def canonicalConnections {n : Nat} [NeZero n] {I : Type*}
    (a : I → (ZMod n)ˣ) : Finset (ZMod n) := by
  classical
  exact Finset.univ.filter (fun s => 0 < s.val ∧ 2 * s.val < n ∧
    ∀ i, NormalDifference n (((↑(a i)⁻¹ : ZMod n) * s).val))

theorem mem_canonicalConnections {n : Nat} [NeZero n] {I : Type*} (a : I → (ZMod n)ˣ)
    (s : ZMod n) : s ∈ canonicalConnections a ↔ 0 < s.val ∧ 2 * s.val < n ∧
      ∀ i, NormalDifference n (((↑(a i)⁻¹ : ZMod n) * s).val) := by
  classical
  simp only [canonicalConnections, Finset.mem_filter, Finset.mem_univ, true_and]

theorem canonicalConnections_no_inverse_pairs {n : Nat} [NeZero n] {I : Type*}
    (a : I → (ZMod n)ˣ) :
    ∀ s ∈ canonicalConnections a, ∀ s' ∈ canonicalConnections a, s ≠ -s' := by
  intro s hs s' hs' he
  obtain ⟨_, hslt, _⟩ := (mem_canonicalConnections a s).mp hs
  obtain ⟨hspos', hslt', _⟩ := (mem_canonicalConnections a s').mp hs'
  let : NeZero s' := ⟨fun hz => by simp only [hz, ZMod.val_zero] at hspos'; omega⟩
  rw [he, ZMod.val_neg_of_ne_zero] at hslt
  have hsn := ZMod.val_lt s'
  omega

theorem canonicalConnections_normal {n : Nat} [NeZero n] {I : Type*}
    (a : I → (ZMod n)ˣ) (i : I) {s : ZMod n} (hs : s ∈ canonicalConnections a) :
    NormalDifference n (((↑(a i)⁻¹ : ZMod n) * s).val) :=
  ((mem_canonicalConnections a s).mp hs).2.2 i

theorem canonicalConnections_rep {n : Nat} [NeZero n] {I : Type*}
    (hn : n % 3 = 1) (hn' : 1 < n) (a : I → (ZMod n)ˣ) {s : ZMod n}
    (hs : s ≠ 0) (hinv : s ≠ -s)
    (hnormal : ∀ i, NormalDifference n (((↑(a i)⁻¹ : ZMod n) * s).val)) :
    s ∈ canonicalConnections a ∨ -s ∈ canonicalConnections a := by
  let : NeZero s := ⟨hs⟩
  have hspos : 0 < s.val := ZMod.val_pos.mpr hs
  have hsn := ZMod.val_lt s
  by_cases hhalf : 2 * s.val < n
  · exact Or.inl ((mem_canonicalConnections a s).mpr ⟨hspos, hhalf, hnormal⟩)
  · apply Or.inr
    apply (mem_canonicalConnections a (-s)).mpr
    have hneq : 2 * s.val ≠ n := by
      intro he
      apply hinv
      apply ZMod.val_injective n
      rw [ZMod.val_neg_of_ne_zero]
      omega
    refine ⟨?_, ?_, ?_⟩
    · rw [ZMod.val_neg_of_ne_zero]
      omega
    · rw [ZMod.val_neg_of_ne_zero]
      omega
    · intro i
      rw [mul_neg]
      exact normalDifference_zmod_neg hn hn' (hnormal i)

theorem unit_ne_neg {n : Nat} [NeZero n] (hn : 2 < n) (a : (ZMod n)ˣ) :
    (a : ZMod n) ≠ -(a : ZMod n) := by
  intro he
  have h : (1 : ZMod n) = -1 := by
    simpa only [mul_neg, Units.inv_mul] using congrArg (fun x => (↑a⁻¹ : ZMod n) * x) he
  have htwo : (2 : ZMod n) = 0 := by
    calc
      (2 : ZMod n) = 1 - -1 := by ring
      _ = 0 := by rw [← h, sub_self]
  have hd : n ∣ 2 := (ZMod.natCast_eq_zero_iff 2 n).mp htwo
  have hle := Nat.le_of_dvd (by omega : 0 < 2) hd
  omega

theorem unit_ne_zero_of_two_lt {n : Nat} [NeZero n] (hn : 2 < n) (a : (ZMod n)ˣ) :
    (a : ZMod n) ≠ 0 := by
  intro he
  exact unit_ne_neg hn a (by simp only [he, neg_zero])

/-- Off-diagonal normalized unit ratios are short and have residue two modulo three. -/
def ShortCompatible {n : Nat} {I : Type*} (q : Nat) (a : I → (ZMod n)ˣ) : Prop :=
  ∀ i j, i ≠ j → q * (((↑(a i)⁻¹ : ZMod n) * (a j : ZMod n)).val) < n ∧
    (((↑(a i)⁻¹ : ZMod n) * (a j : ZMod n)).val) % 3 = 2

theorem ShortCompatible.normal {n : Nat} [NeZero n] {I : Type*} {q : Nat}
    (hn : 1 < n) {a : I → (ZMod n)ˣ} (ha : ShortCompatible q a) (i j : I) :
    NormalDifference n (((↑(a i)⁻¹ : ZMod n) * (a j : ZMod n)).val) := by
  by_cases hij : i = j
  · subst j
    rw [Units.inv_mul, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt hn]
    exact Or.inl rfl
  · exact Or.inr (Or.inr (ha i j hij).2)

theorem ShortCompatible.signedDistinct {n : Nat} [NeZero n] {I : Type*} {q : Nat}
    (hn : n % 3 = 1) (hn' : 2 < n) {a : I → (ZMod n)ˣ} (ha : ShortCompatible q a)
    {i j : I} (hij : i ≠ j) : SignedDistinct (a i : ZMod n) (a j : ZMod n) := by
  have hm := (ha i j hij).2
  have hval : (1 : ZMod n).val = 1 := by
    rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega : 1 < n)]
  have hneone : (1 : ZMod n) ≠ 0 := by
    intro he
    simp only [he, ZMod.val_zero] at hval
    omega
  let : NeZero (1 : ZMod n) := ⟨hneone⟩
  refine ⟨?_, ?_⟩
  · intro he
    rw [← he, Units.inv_mul, hval] at hm
    omega
  · intro he
    have he' : (1 : ZMod n) = -((↑(a i)⁻¹ : ZMod n) * (a j : ZMod n)) := by
      simpa only [mul_neg, Units.inv_mul] using congrArg (fun x => (↑(a i)⁻¹ : ZMod n) * x) he
    have hr : (↑(a i)⁻¹ : ZMod n) * (a j : ZMod n) = -1 := by
      simpa only [neg_neg] using (congrArg Neg.neg he').symm
    rw [hr, ZMod.val_neg_of_ne_zero, hval] at hm
    omega

theorem ShortCompatible.off_lengths {n : Nat} [NeZero n] {I : Type*} {q : Nat}
    (hq : q < n) {a : I → (ZMod n)ˣ} (ha : ShortCompatible q a)
    {i j : I} (hij : i ≠ j) {ℓ : Nat} (hℓ : ℓ ≤ q) (hmod : ℓ % 3 = 1) :
    NormalDifference n (((↑(a i)⁻¹ : ZMod n) * (ℓ : ZMod n) * (a j : ZMod n)).val) := by
  obtain ⟨hsmall, hm⟩ := ha i j hij
  have he : (↑(a i)⁻¹ : ZMod n) * (ℓ : ZMod n) * (a j : ZMod n) =
      (ℓ : ZMod n) * ((↑(a i)⁻¹ : ZMod n) * (a j : ZMod n)) := by ring
  rw [he, ZMod.val_mul, ZMod.val_natCast, Nat.mod_eq_of_lt (hℓ.trans_lt hq),
    Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.mul_le_mul_right _ hℓ) hsmall)]
  apply Or.inr ∘ Or.inr
  rw [Nat.mul_mod, hmod, hm]

theorem ShortCompatible.rep {n : Nat} [NeZero n] {I : Type*} {q : Nat}
    (hn : n % 3 = 1) (hn' : 2 < n) {a : I → (ZMod n)ˣ} (ha : ShortCompatible q a) (i : I) :
    (a i : ZMod n) ∈ canonicalConnections a ∨ -(a i : ZMod n) ∈ canonicalConnections a := by
  exact canonicalConnections_rep hn (by omega) a (unit_ne_zero_of_two_lt hn' (a i))
    (unit_ne_neg hn' (a i)) (fun j => ha.normal (by omega) j i)

/-- Only the word and character conditions remain after constructing short compatible units. -/
theorem erdos944_four_of_short_compatible {n r t : Nat} [NeZero n]
    (hrt : r ≤ t) (hn : n % 3 = 1) (hq : 3 * t + 1 ∣ n) (htn : 3 * t + 1 < n)
    (a : ZMod (3 * t + 1) → (ZMod n)ˣ) (ha : ShortCompatible (3 * t + 1) a)
    (hwords : ∀ s ∈ canonicalConnections a, HasSignedWords (canonicalConnections a) r s)
    (hcharacter : ∀ K : Int,
      (∑ s ∈ canonicalConnections a, characterDeficit n (K * (s.val : Int))) ≤ (r : Int) →
      ∃ i, 0 < characterDeficit n (K * ((a i : ZMod n).val : Int))) :
    ∃ G : SimpleGraph (ZMod n), Erdos944.SimpleGraph.IsErdos944 G 4 r := by
  have hn' : 2 < n := by omega
  apply erdos944_four_of_cyclic_data hrt hn hq htn a (canonicalConnections a)
    (canonicalConnections_no_inverse_pairs a)
    (fun _ _ hij => ha.signedDistinct hn hn' hij) (ha.rep hn hn')
    (fun i _ hs => canonicalConnections_normal a i hs)
    (fun _ _ hij _ hℓ hmod => ha.off_lengths htn hij hℓ hmod) hwords hcharacter

theorem disjoint_words_of_avoidance {A : Type*} [AddCommGroup A] (J : Finset A)
    (s : A) (B r : Nat)
    (hex : ∀ F : Finset A, F.card ≤ B → ∃ w : Fin 3 → A,
      w 0 + w 1 + w 2 = s ∧ (∀ p, w p ∈ J ∨ -w p ∈ J) ∧ (∀ p, w p ∉ F)) :
    ∀ F : Finset A, F.card + 6 * r ≤ B → ∃ W : Fin r → Fin 3 → A,
      (∀ i, W i 0 + W i 1 + W i 2 = s) ∧
      (∀ i p, W i p ∈ J ∨ -W i p ∈ J) ∧ (∀ i p, W i p ∉ F) ∧
      (∀ i j, i ≠ j → ∀ p q, SignedDistinct (W i p) (W j q)) := by
  classical
  induction r with
  | zero =>
    intro F _
    exact ⟨Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i,
      fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  | succ r ih =>
    intro F hF
    obtain ⟨w, hw, hwmem, hwavoid⟩ := hex F (by omega)
    let S : Finset A := Finset.univ.image w ∪ Finset.univ.image (fun p => -w p)
    let F' := F ∪ S
    have hS : S.card ≤ 6 := by
      have h₁ := Finset.card_image_le (s := (Finset.univ : Finset (Fin 3))) (f := w)
      have h₂ := Finset.card_image_le (s := (Finset.univ : Finset (Fin 3))) (f := fun p => -w p)
      have h₃ := Finset.card_union_le (Finset.univ.image w) (Finset.univ.image (fun p => -w p))
      simp only [Finset.card_univ, Fintype.card_fin] at h₁ h₂
      dsimp [S]
      omega
    have hF' : F'.card + 6 * r ≤ B := by
      have h := Finset.card_union_le F S
      dsimp [F']
      omega
    obtain ⟨T, hTsum, hTmem, hTavoid, hTsep⟩ := ih F' hF'
    have hTF : ∀ i p, T i p ∉ F := by
      intro i p h
      exact hTavoid i p (Finset.mem_union_left S h)
    have hTw : ∀ i p q, SignedDistinct (T i p) (w q) := by
      intro i p q
      constructor
      · intro he
        apply hTavoid i p
        apply Finset.mem_union_right
        apply Finset.mem_union_left
        exact Finset.mem_image.mpr ⟨q, Finset.mem_univ _, he.symm⟩
      · intro he
        apply hTavoid i p
        apply Finset.mem_union_right
        apply Finset.mem_union_right
        exact Finset.mem_image.mpr ⟨q, Finset.mem_univ _, he.symm⟩
    let W : Fin (r + 1) → Fin 3 → A := Fin.cases w T
    refine ⟨W, ?_, ?_, ?_, ?_⟩
    · intro i
      exact Fin.cases hw hTsum i
    · intro i
      exact Fin.cases hwmem hTmem i
    · intro i
      exact Fin.cases hwavoid hTF i
    · intro i j
      refine Fin.cases ?_ (fun i' => ?_) i
      · refine Fin.cases ?_ (fun j' => ?_) j
        · intro h
          exact False.elim (h rfl)
        · intro _ p q
          exact (hTw j' q p).symm
      · refine Fin.cases ?_ (fun j' => ?_) j
        · intro _ p q
          exact hTw i' p q
        · intro h p q
          exact hTsep i' j' (fun he => h (congrArg Fin.succ he)) p q

theorem hasSignedWords_of_avoidance {A : Type*} [AddCommGroup A]
    (J : Finset A) (r : Nat) (s : A)
    (hex : ∀ F : Finset A, F.card ≤ 6 * r + 2 → ∃ w : Fin 3 → A,
      w 0 + w 1 + w 2 = s ∧ (∀ p, w p ∈ J ∨ -w p ∈ J) ∧ (∀ p, w p ∉ F)) :
    HasSignedWords J r s := by
  classical
  let F : Finset A := {s, -s}
  have hF : F.card ≤ 2 := Finset.card_le_two
  obtain ⟨W, hsum, hmem, havoid, hsep⟩ :=
    disjoint_words_of_avoidance J s (6 * r + 2) r hex F (by omega)
  refine ⟨W, hsum, hmem, ?_, hsep⟩
  intro i p
  have hw : W i p ≠ s ∧ W i p ≠ -s := by
    simpa only [F, Finset.mem_insert, Finset.mem_singleton, not_or] using havoid i p
  exact (show SignedDistinct (W i p) s from hw).symm

universe u


theorem badEdges_le_of_injective_map {V W : Type*} [Finite W]
    (G : SimpleGraph V) (H : SimpleGraph W) (f : V → W) (hf : Function.Injective f)
    (hadj : ∀ v w, G.Adj v w → H.Adj (f v) (f w)) {k : Nat} (c : W → Fin k) :
    (badEdges G (fun v => c (f v))).ncard ≤ (badEdges H c).ncard := by
  apply Set.ncard_le_ncard_of_injOn (Sym2.map f)
  · rintro e ⟨v, w, rfl, hvw, hc⟩
    exact ⟨f v, f w, Sym2.map_mk f v w, hadj v w hvw, hc⟩
  · exact (Sym2.map.injective hf).injOn

theorem punctured_coloring_of_critical {V : Type*} (G : SimpleGraph V) {k : Nat}
    (hk : 0 < k) (hG : G.IsCritical (k + 1)) (v : V) :
    ∃ c : V → Fin k, ∀ u w, u ≠ v → w ≠ v → G.Adj u w → c u ≠ c w := by
  classical
  have hlt := hG.2 v
  change ((⊤ : G.Subgraph).deleteVerts {v}).coe.chromaticNumber <
    (⊤ : G.Subgraph).coe.chromaticNumber at hlt
  rw [SimpleGraph.chromaticNumber_congr SimpleGraph.Subgraph.topIso, hG.1, Nat.cast_add,
    Nat.cast_one] at hlt
  obtain ⟨C⟩ := SimpleGraph.chromaticNumber_le_iff_colorable.mp (ENat.lt_natCast_add_one_iff.mp hlt)
  let c : V → Fin k := fun w => if h : w = v then ⟨0, hk⟩ else C ⟨w, by simpa using h⟩
  refine ⟨c, ?_⟩
  intro u w hu hw hadj
  simp only [c, dif_neg hu, dif_neg hw]
  apply C.valid
  exact SimpleGraph.Subgraph.deleteVerts_adj.mpr
    ⟨by simp, by simpa using hu, by simp, by simpa using hw, hadj⟩

theorem badEdges_bound_of_erdos944 {V : Type*} (G : SimpleGraph V) {k r : Nat}
    (hG : Erdos944.SimpleGraph.IsErdos944 G (k + 1) r) (c : V → Fin k) :
    r < (badEdges G c).ncard := by
  apply hG.2
  have hcol : (G.deleteEdges (badEdges G c)).Colorable k := by
    refine ⟨SimpleGraph.Coloring.mk c ?_⟩
    intro v w hadj heq
    have h := SimpleGraph.deleteEdges_adj.mp hadj
    exact h.2 ⟨v, w, rfl, h.1, heq⟩
  change (G.deleteEdges (badEdges G c)).chromaticNumber < G.chromaticNumber
  rw [hG.1.1, Nat.cast_add, Nat.cast_one]
  exact lt_of_le_of_lt hcol.chromaticNumber_le (ENat.lt_natCast_add_one_iff.mpr le_rfl)

theorem erdos944_of_equiv {V W : Type*} [Finite V] [Nonempty V]
    (G : SimpleGraph V) (e : W ≃ V) {k r : Nat} (hk : 0 < k)
    (hG : Erdos944.SimpleGraph.IsErdos944 G (k + 1) r) :
    Erdos944.SimpleGraph.IsErdos944 (G.comap e) (k + 1) r := by
  let : Finite W := Finite.of_equiv V e.symm
  let : Nonempty W := ⟨e.symm (Classical.choice (inferInstance : Nonempty V))⟩
  apply critical_robust_of_punctured
  · intro v
    obtain ⟨c, hc⟩ := punctured_coloring_of_critical G hk hG.1 (e v)
    refine ⟨fun w => c (e w), ?_⟩
    intro u w hu hw hadj
    exact hc (e u) (e w) (fun he => hu (e.injective he)) (fun he => hw (e.injective he)) hadj
  · intro c
    have hb := badEdges_bound_of_erdos944 G hG (fun v => c (e.symm v))
    have hle := badEdges_le_of_injective_map G (G.comap e) e.symm e.symm.injective
      (by intro v w h; simpa only [SimpleGraph.comap_adj, Equiv.apply_symm_apply] using h) c
    exact hb.trans_le hle

/-- No universe restriction is imposed by constructing a finite graph on ordinary types. -/
theorem erdos944_universe_lift {V : Type} [Finite V] [Nonempty V]
    (G : SimpleGraph V) {k r : Nat} (hk : 0 < k)
    (hG : Erdos944.SimpleGraph.IsErdos944 G (k + 1) r) :
    ∃ (W : Type u) (H : SimpleGraph W), Erdos944.SimpleGraph.IsErdos944 H (k + 1) r := by
  exact ⟨ULift.{u} V, G.comap ULift.down,
    erdos944_of_equiv G (Equiv.ulift : ULift.{u} V ≃ V) hk hG⟩

theorem exists_large_crt {I : Type*} [Fintype I] (m a : I → Nat)
    (hm : ∀ i, 0 < m i) (hcop : Pairwise (fun i j => (m i).Coprime (m j))) (B : Nat) :
    ∃ x : Nat, B < x ∧ ∀ i, x % m i = a i % m i := by
  classical
  obtain ⟨x, hx⟩ := Nat.chineseRemainderOfFinset a m Finset.univ
    (fun i _ => Nat.ne_of_gt (hm i)) (fun i _ j _ hij => hcop hij)
  let P := ∏ i : I, m i
  have hP : 0 < P := Finset.prod_pos (fun i _ => hm i)
  refine ⟨x + (B + 1) * P, ?_, ?_⟩
  · nlinarith
  · intro i
    have hi : m i ∣ P := Finset.dvd_prod_of_mem m (Finset.mem_univ i)
    change (x + (B + 1) * P) % m i = a i % m i
    rw [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_zero_of_dvd hi, Nat.mul_zero,
      Nat.zero_mod, Nat.add_zero, Nat.mod_mod]
    exact hx i (Finset.mem_univ i)

theorem coprime_fifteen_of_remainders {q : Nat} (hq₃ : q % 3 = 1) (hq₅ : q % 5 ≠ 0) :
    q.Coprime 15 := by
  have hcases : q % 15 = 1 ∨ q % 15 = 4 ∨ q % 15 = 7 ∨ q % 15 = 13 := by omega
  change Nat.gcd q 15 = 1
  rw [Nat.gcd_comm, Nat.gcd_rec]
  rcases hcases with h | h | h | h <;> rw [h] <;> decide

theorem exists_gap_parameter (r : Nat) :
    ∃ t : Nat, r ≤ t ∧ t ≤ r + 1 ∧ (3 * t + 1).Coprime 15 := by
  by_cases h : (3 * r + 1) % 5 = 0
  · exact ⟨r + 1, by omega, le_rfl, coprime_fifteen_of_remainders (by omega) (by omega)⟩
  · exact ⟨r, le_rfl, by omega, coprime_fifteen_of_remainders (by omega) h⟩

theorem canonical_deficit_one (m : Nat) : characterDeficit (3 * m + 1) (m : Int) = 1 := by
  unfold characterDeficit
  rw [Int.emod_eq_of_lt (Int.natCast_nonneg _) (by omega), min_eq_left (by omega)]
  have he : ((3 * m + 1 : Nat) : Int) - 3 * (m : Int) = 1 := by omega
  rw [he]
  decide

def crtFactor (q κ : Nat) : Nat := 30 * q * (κ - 1) + 1

structure ParameterFamily (q N : Nat) where
  kappa : Fin N → Nat
  large : ∀ i, 6 ≤ kappa i
  mod_three : ∀ i, kappa i % 3 = 0
  mod_aux : ∀ i, kappa i % (5 * (30 * q - 1)) = 1
  start : ∀ i, 10 * q < 5 * crtFactor q (kappa i)
  separated : ∀ i j, i < j → 10 * q * (5 * crtFactor q (kappa i)) <
    5 * crtFactor q (kappa j)
  coprime : Pairwise (fun i j => (crtFactor q (kappa i)).Coprime (crtFactor q (kappa j)))
  cross : ∀ i j, i < j → (kappa i * crtFactor q (kappa j)) % crtFactor q (kappa i) = 1

theorem coprime_of_remainder_one {a m : Nat} (h : a % m = 1) : a.Coprime m := by
  change Nat.gcd a m = 1
  rw [Nat.gcd_comm, Nat.gcd_rec, h, Nat.gcd_one_left]

theorem crtFactor_pos (q κ : Nat) : 0 < crtFactor q κ := by
  unfold crtFactor
  omega

theorem crtFactor_mod_fifteen (q κ : Nat) : crtFactor q κ % 15 = 1 := by
  norm_num [crtFactor, Nat.add_mod, Nat.mul_mod]

theorem crtFactor_mod_base {q κ : Nat} (hq : 0 < q) : crtFactor q κ % (30 * q) = 1 := by
  have hD : 1 < 30 * q := by omega
  simp [crtFactor, Nat.add_mod, Nat.mod_eq_of_lt hD]

theorem crtFactor_add {q κ : Nat} (hq : 0 < q) (hk : 1 ≤ κ) :
    crtFactor q κ + (30 * q - 1) = 30 * q * κ := by
  unfold crtFactor
  have hD : 30 * q - 1 + 1 = 30 * q := by omega
  have hκ : κ - 1 + 1 = κ := by omega
  nlinarith

theorem kappa_coprime_crtFactor {q κ : Nat} (hq : 0 < q) (hk : 1 ≤ κ)
    (hκ : κ % (5 * (30 * q - 1)) = 1) : κ.Coprime (crtFactor q κ) := by
  have hc : κ.Coprime (30 * q - 1) :=
    (coprime_of_remainder_one hκ).coprime_mul_left_right
  have hgκ := Nat.gcd_dvd_left κ (crtFactor q κ)
  have hgd := Nat.gcd_dvd_right κ (crtFactor q κ)
  have hgD : Nat.gcd κ (crtFactor q κ) ∣ 30 * q - 1 := by
    have h := Nat.dvd_sub (dvd_mul_of_dvd_right hgκ (30 * q)) hgd
    rwa [← crtFactor_add hq hk, Nat.add_sub_cancel_left] at h
  have h := Nat.dvd_gcd hgκ hgD
  rw [hc.gcd_eq_one] at h
  exact Nat.eq_one_of_dvd_one h

theorem crtFactor_mod_aux {q κ : Nat} (hq : 0 < q) (hk : 1 ≤ κ)
    (hκ : κ % (5 * (30 * q - 1)) = 1) :
    crtFactor q κ % (5 * (30 * q - 1)) = 1 := by
  have hA : 1 < 5 * (30 * q - 1) := by omega
  have he : Nat.ModEq (5 * (30 * q - 1)) 1 κ := by
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt hA] using hκ.symm
  have hd : 5 * (30 * q - 1) ∣ κ - 1 := (Nat.modEq_iff_dvd' hk).mp he
  simp [crtFactor, Nat.add_mod, Nat.mul_mod, Nat.mod_eq_zero_of_dvd hd, Nat.mod_eq_of_lt hA]

theorem kappa_mod_fifteen {q κ : Nat} (h₃ : κ % 3 = 0)
    (hκ : κ % (5 * (30 * q - 1)) = 1) : κ % 15 = 6 := by
  have h₅ : κ % 5 = 1 := by
    have h := Nat.mod_mod_of_dvd κ (dvd_mul_right 5 (30 * q - 1))
    rw [hκ] at h
    exact h.symm
  omega

theorem crtFactor_coprime_aux {q κ : Nat} (hq : 0 < q) (hk : 1 ≤ κ)
    (hκ : κ % (5 * (30 * q - 1)) = 1) :
    (crtFactor q κ).Coprime (3 * (5 * (30 * q - 1))) := by
  have h₃ : crtFactor q κ % 3 = 1 := by
    have h := Nat.mod_mod_of_dvd (crtFactor q κ) (by decide : 3 ∣ 15)
    rw [crtFactor_mod_fifteen] at h
    exact h.symm
  exact (coprime_of_remainder_one h₃).mul_right
    (coprime_of_remainder_one (crtFactor_mod_aux hq hk hκ))

theorem exists_large_crt_with_base {I : Type*} [Fintype I] (b c : Nat) (hb : 0 < b)
    (m a : I → Nat) (hm : ∀ i, 0 < m i)
    (hcop : Pairwise (fun i j => (m i).Coprime (m j)))
    (hbase : ∀ i, (m i).Coprime b) (B : Nat) :
    ∃ x : Nat, B < x ∧ x % b = c % b ∧ ∀ i, x % m i = a i % m i := by
  let m' : Option I → Nat := fun i => match i with | none => b | some j => m j
  let a' : Option I → Nat := fun i => match i with | none => c | some j => a j
  have hm' : ∀ i, 0 < m' i := by
    intro i
    cases i with
    | none => exact hb
    | some i => exact hm i
  have hcop' : Pairwise (fun i j => (m' i).Coprime (m' j)) := by
    intro i j hij
    cases i with
    | none =>
      cases j with
      | none => exact False.elim (hij rfl)
      | some j => exact (hbase j).symm
    | some i =>
      cases j with
      | none => exact hbase i
      | some j => exact hcop (fun he => hij (congrArg some he))
  obtain ⟨x, hx, hmods⟩ := exists_large_crt m' a' hm' hcop' B
  exact ⟨x, hx, hmods none, fun i => hmods (some i)⟩

theorem exists_inverse_residue {a m : Nat} (hm : 1 < m) (ha : a.Coprime m) :
    ∃ b : Nat, (a * b) % m = 1 := by
  let : NeZero m := ⟨by omega⟩
  let b := ((a : ZMod m)⁻¹).val
  have he : (a : ZMod m) * (b : ZMod m) = 1 := by
    simpa only [b, ZMod.natCast_zmod_val] using ZMod.coe_mul_inv_eq_one a ha
  have hr : Nat.ModEq m (a * b) 1 :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mp (by simpa only [Nat.cast_mul, Nat.cast_one] using he)
  exact ⟨b, Eq.trans hr (Nat.mod_eq_of_lt hm)⟩

theorem crtFactor_ge_kappa {q κ : Nat} (hq : 0 < q) (hk : 1 ≤ κ) :
    κ ≤ crtFactor q κ := by
  unfold crtFactor
  have hD : 1 ≤ 30 * q := by omega
  have hκ : κ - 1 + 1 = κ := by omega
  nlinarith [Nat.mul_le_mul_right (κ - 1) hD]

theorem exists_parameter_extension {q N : Nat} (hq : 0 < q)
    (p : ParameterFamily q N) (B : Nat) :
    ∃ κ : Nat, 6 ≤ κ ∧ B < crtFactor q κ ∧ κ % 3 = 0 ∧
      κ % (5 * (30 * q - 1)) = 1 ∧
      ∀ i, (p.kappa i * crtFactor q κ) % crtFactor q (p.kappa i) = 1 := by
  classical
  let D := 30 * q
  let A := 5 * (30 * q - 1)
  let d := fun i => crtFactor q (p.kappa i)
  have hA : 1 < A := by dsimp [A]; omega
  have hA₃ : A % 3 = 1 := by dsimp [A]; omega
  have hbase : (3 : Nat).Coprime A := (coprime_of_remainder_one hA₃).symm
  let c := Nat.chineseRemainder hbase 0 1
  have hd : ∀ i, 1 < d i := by
    intro i
    have hi := p.large i
    dsimp [d, crtFactor]
    have hki : 0 < p.kappa i - 1 := by omega
    have hprod := Nat.mul_pos (show 0 < 30 * q by omega) hki
    omega
  have hi : ∀ i, (D * p.kappa i).Coprime (d i) := by
    intro i
    have hD : D.Coprime (d i) := (coprime_of_remainder_one (crtFactor_mod_base hq)).symm
    exact hD.mul_left (kappa_coprime_crtFactor hq (by have h := p.large i; omega) (p.mod_aux i))
  choose v hv using fun i => exists_inverse_residue (hd i) (hi i)
  let a := fun i => v i * (1 + p.kappa i * (D - 1))
  obtain ⟨κ, hκ, hκbase, hκmods⟩ := exists_large_crt_with_base (3 * A) c.val
    (Nat.mul_pos (by decide) (by omega)) d a (fun i => by have h := hd i; omega)
    p.coprime (fun i => crtFactor_coprime_aux hq (by have h := p.large i; omega) (p.mod_aux i))
    (B + 6)
  have hlarge : 6 ≤ κ := by omega
  have hκge : 1 ≤ κ := by omega
  have hmod : Nat.ModEq (3 * A) κ c.val := hκbase
  have hthree : κ % 3 = 0 := (hmod.of_dvd (dvd_mul_right 3 A)).trans c.property.1
  have haux : κ % A = 1 := by
    have h := (hmod.of_dvd (dvd_mul_left A 3)).trans c.property.2
    exact Eq.trans h (Nat.mod_eq_of_lt hA)
  refine ⟨κ, hlarge, lt_of_lt_of_le (by omega : B < κ) (crtFactor_ge_kappa hq hκge),
    hthree, haux, ?_⟩
  intro i
  have hki : Nat.ModEq (d i) κ (a i) := hκmods i
  have hvi : Nat.ModEq (d i) (D * p.kappa i * v i) 1 := by
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt (hd i)] using hv i
  have hlin : Nat.ModEq (d i) (D * p.kappa i * κ) (1 + p.kappa i * (D - 1)) := by
    calc
      D * p.kappa i * κ ≡ D * p.kappa i * a i [MOD d i] := hki.mul_left _
      _ = (D * p.kappa i * v i) * (1 + p.kappa i * (D - 1)) := by dsimp [a]; ring
      _ ≡ 1 * (1 + p.kappa i * (D - 1)) [MOD d i] := hvi.mul_right _
      _ = 1 + p.kappa i * (D - 1) := one_mul _
  have he : D * p.kappa i * κ = p.kappa i * crtFactor q κ + p.kappa i * (D - 1) := by
    have h := crtFactor_add hq hκge
    dsimp [D]
    nlinarith [congrArg (fun x => p.kappa i * x) h]
  rw [he] at hlin
  exact Eq.trans (hlin.add_right_cancel' _) (Nat.mod_eq_of_lt (hd i))

theorem parameterFamily_extend {q N : Nat} (hq : 0 < q) (p : ParameterFamily q N) :
    Nonempty (ParameterFamily q (N + 1)) := by
  classical
  let B := 10 * q + ∑ i : Fin N, 10 * q * (5 * crtFactor q (p.kappa i))
  obtain ⟨κ, hlarge, hB, hthree, haux, hcross⟩ := exists_parameter_extension hq p B
  have hstart : 10 * q < 5 * crtFactor q κ := by
    dsimp [B] at hB
    omega
  have hsep : ∀ i, 10 * q * (5 * crtFactor q (p.kappa i)) < 5 * crtFactor q κ := by
    intro i
    have hi : 10 * q * (5 * crtFactor q (p.kappa i)) ≤
        ∑ j : Fin N, 10 * q * (5 * crtFactor q (p.kappa j)) :=
      Finset.single_le_sum
        (f := fun j : Fin N => 10 * q * (5 * crtFactor q (p.kappa j)))
        (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    dsimp [B] at hB
    omega
  have hcop : ∀ i, (crtFactor q κ).Coprime (crtFactor q (p.kappa i)) := by
    intro i
    have hi : 1 < crtFactor q (p.kappa i) := by
      have h := crtFactor_ge_kappa (κ := p.kappa i) hq (by have h := p.large i; omega)
      have hlargei := p.large i
      omega
    apply Nat.coprime_of_mul_modEq_one (p.kappa i)
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt hi, Nat.mul_comm] using hcross i
  refine ⟨{
    kappa := Fin.snoc p.kappa κ
    large := ?_
    mod_three := ?_
    mod_aux := ?_
    start := ?_
    separated := ?_
    coprime := ?_
    cross := ?_
  }⟩
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.snoc_last] using hlarge
    · simpa only [Fin.snoc_castSucc] using p.large j
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.snoc_last] using hthree
    · simpa only [Fin.snoc_castSucc] using p.mod_three j
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.snoc_last] using haux
    · simpa only [Fin.snoc_castSucc] using p.mod_aux j
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.snoc_last] using hstart
    · simpa only [Fin.snoc_castSucc] using p.start j
  · intro i j
    refine Fin.lastCases ?_ (fun i' => ?_) i
    · intro h
      have hj := j.isLt
      have hh : N < j.val := h
      omega
    · refine Fin.lastCases ?_ (fun j' => ?_) j
      · intro _
        simpa only [Fin.snoc_castSucc, Fin.snoc_last] using hsep i'
      · intro h
        simpa only [Fin.snoc_castSucc] using p.separated i' j' h
  · intro i j
    refine Fin.lastCases ?_ (fun i' => ?_) i
    · refine Fin.lastCases ?_ (fun j' => ?_) j
      · intro h
        exact False.elim (h rfl)
      · intro _
        simpa only [Fin.snoc_last, Fin.snoc_castSucc] using hcop j'
    · refine Fin.lastCases ?_ (fun j' => ?_) j
      · intro _
        simpa only [Fin.snoc_last, Fin.snoc_castSucc] using (hcop i').symm
      · intro h
        simpa only [Fin.snoc_castSucc] using p.coprime (fun he => h (congrArg Fin.castSucc he))
  · intro i j
    refine Fin.lastCases ?_ (fun i' => ?_) i
    · intro h
      have hj := j.isLt
      have hh : N < j.val := h
      omega
    · refine Fin.lastCases ?_ (fun j' => ?_) j
      · intro _
        simpa only [Fin.snoc_castSucc, Fin.snoc_last] using hcross i'
      · intro h
        simpa only [Fin.snoc_castSucc] using p.cross i' j' h

theorem exists_parameter_family (q : Nat) (hq : 0 < q) (N : Nat) :
    Nonempty (ParameterFamily q N) := by
  induction N with
  | zero =>
    exact ⟨{
      kappa := Fin.elim0
      large := fun i => Fin.elim0 i
      mod_three := fun i => Fin.elim0 i
      mod_aux := fun i => Fin.elim0 i
      start := fun i => Fin.elim0 i
      separated := fun i => Fin.elim0 i
      coprime := fun i => Fin.elim0 i
      cross := fun i => Fin.elim0 i
    }⟩
  | succ N ih =>
    obtain ⟨p⟩ := ih
    exact parameterFamily_extend hq p

theorem exists_negative_inverse_residue {a m : Nat} (hm : 1 < m) (ha : a.Coprime m) :
    ∃ b : Nat, (a * b + 1) % m = 0 := by
  obtain ⟨v, hv⟩ := exists_inverse_residue hm ha
  have hv' : Nat.ModEq m (a * v) 1 := by
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt hm] using hv
  refine ⟨(m - 1) * v, ?_⟩
  have he : Nat.ModEq m (a * ((m - 1) * v) + 1) m := by
    calc
      a * ((m - 1) * v) + 1 = (a * v) * (m - 1) + 1 := by ring
      _ ≡ 1 * (m - 1) + 1 [MOD m] := (hv'.mul_right _).add_right 1
      _ = m := by omega
  exact Eq.trans he (Nat.mod_self m)

theorem coprime_of_dvd_mul_add_one {a κ n : Nat} (h : a ∣ κ * n + 1) :
    a.Coprime n := by
  have hc : n.Coprime (κ * n + 1) :=
    (Nat.coprime_mul_right_add_right n 1 κ).mpr (Nat.coprime_one_right n)
  exact (Nat.Coprime.coprime_dvd_right h hc).symm

theorem exists_graph_order {q N : Nat} (hq : 0 < q) (hq15 : q.Coprime 15)
    (p : ParameterFamily q N) (B : Nat) :
    ∃ n : Nat, B < n ∧ n % 3 = 1 ∧ q ∣ n ∧ n % 5 = 4 ∧
      ∀ i, 5 * crtFactor q (p.kappa i) ∣ p.kappa i * n + 1 := by
  classical
  let d := fun i => crtFactor q (p.kappa i)
  have hd : ∀ i, 1 < d i := by
    intro i
    change 1 < crtFactor q (p.kappa i)
    have h := crtFactor_ge_kappa (κ := p.kappa i) hq (by have h := p.large i; omega)
    have hi := p.large i
    omega
  have hk : ∀ i, (p.kappa i).Coprime (d i) := fun i =>
    kappa_coprime_crtFactor hq (by have h := p.large i; omega) (p.mod_aux i)
  choose a ha using fun i => exists_negative_inverse_residue (hd i) (hk i)
  let c := Nat.chineseRemainder hq15 0 4
  have hbase : ∀ i, (d i).Coprime (q * 15) := by
    intro i
    have hi : (d i).Coprime q :=
      (coprime_of_remainder_one (crtFactor_mod_base hq)).coprime_mul_left_right
    exact hi.mul_right (coprime_of_remainder_one (crtFactor_mod_fifteen q (p.kappa i)))
  obtain ⟨n, hn, hnbase, hnmods⟩ := exists_large_crt_with_base (q * 15) c.val
    (Nat.mul_pos hq (by decide)) d a (fun i => by have h := hd i; omega)
    p.coprime hbase B
  have hbase' : Nat.ModEq (q * 15) n c.val := hnbase
  have hnq : q ∣ n := Nat.dvd_of_mod_eq_zero
    ((hbase'.of_dvd (dvd_mul_right q 15)).trans c.property.1)
  have hn15 : n % 15 = 4 := Eq.trans
    ((hbase'.of_dvd (dvd_mul_left 15 q)).trans c.property.2) (by decide : 4 % 15 = 4)
  have hn3 : n % 3 = 1 := by omega
  have hn5 : n % 5 = 4 := by omega
  refine ⟨n, hn, hn3, hnq, hn5, ?_⟩
  intro i
  have hκ5 : p.kappa i % 5 = 1 := by
    have h := kappa_mod_fifteen (p.mod_three i) (p.mod_aux i)
    omega
  have hfive : 5 ∣ p.kappa i * n + 1 := by
    apply Nat.dvd_of_mod_eq_zero
    simp [Nat.add_mod, Nat.mul_mod, hκ5, hn5]
  have hdi : d i ∣ p.kappa i * n + 1 := by
    have h : Nat.ModEq (d i) n (a i) := hnmods i
    exact Nat.dvd_of_mod_eq_zero (Eq.trans ((h.mul_left (p.kappa i)).add_right 1) (ha i))
  have hcop : (5 : Nat).Coprime (d i) :=
    (Nat.Coprime.coprime_dvd_right (by decide : 5 ∣ 15)
      (coprime_of_remainder_one (crtFactor_mod_fifteen q (p.kappa i)))).symm
  exact hcop.mul_dvd_of_dvd_of_dvd hfive hdi

theorem exists_graph_order_with_units {q N : Nat} (hq : 0 < q) (hq15 : q.Coprime 15)
    (p : ParameterFamily q N) (B : Nat) :
    ∃ n : Nat, B < n ∧ n % 3 = 1 ∧ q ∣ n ∧ n % 5 = 4 ∧
      ∀ i, 5 * crtFactor q (p.kappa i) ∣ p.kappa i * n + 1 ∧
        (5 * crtFactor q (p.kappa i)).Coprime n := by
  obtain ⟨n, hn, hn3, hnq, hn5, ha⟩ := exists_graph_order hq hq15 p B
  exact ⟨n, hn, hn3, hnq, hn5, fun i => ⟨ha i, coprime_of_dvd_mul_add_one (ha i)⟩⟩

def ParameterFamily.period {q N : Nat} (p : ParameterFamily q N) : Nat :=
  15 * ∏ i : Fin N, crtFactor q (p.kappa i)

def ParameterFamily.orientation {q N : Nat} (p : ParameterFamily q N) : Fin (N + 1) → Nat :=
  Fin.cons 1 (fun i => 5 * crtFactor q (p.kappa i))

theorem parameter_period_pos {q N : Nat} (p : ParameterFamily q N) : 0 < p.period := by
  exact Nat.mul_pos (by decide) (Finset.prod_pos (fun i _ => crtFactor_pos q (p.kappa i)))

theorem orientation_pos {q N : Nat} (p : ParameterFamily q N) (i : Fin (N + 1)) :
    0 < p.orientation i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact Nat.zero_lt_one
  · exact Nat.mul_pos (by decide) (crtFactor_pos q (p.kappa j))

theorem orientation_dvd_period {q N : Nat} (p : ParameterFamily q N) (i : Fin (N + 1)) :
    p.orientation i ∣ p.period := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact one_dvd _
  · obtain ⟨v, hv⟩ := Finset.dvd_prod_of_mem (fun j : Fin N => crtFactor q (p.kappa j))
      (Finset.mem_univ j)
    refine ⟨3 * v, ?_⟩
    change 15 * (∏ j : Fin N, crtFactor q (p.kappa j)) = (5 * crtFactor q (p.kappa j)) * (3 * v)
    rw [hv]
    ring

theorem orientation_mod_three {q N : Nat} (p : ParameterFamily q N) (i : Fin N) :
    p.orientation i.succ % 3 = 2 := by
  have h : crtFactor q (p.kappa i) % 3 = 1 := by
    have h := crtFactor_mod_fifteen q (p.kappa i)
    omega
  change (5 * crtFactor q (p.kappa i)) % 3 = 2
  simp [Nat.mul_mod, h]

structure CyclicIntegerData (r : Nat) where
  t : Nat
  gap_lower : r ≤ t
  gap_upper : t ≤ r + 1
  gap_coprime : (3 * t + 1).Coprime 15
  family : ParameterFamily (3 * t + 1) (3 * t)
  n : Nat
  large_order : 1000 * (r + 1) * (3 * t + 1) * family.period ^ 2 < n
  order_three : n % 3 = 1
  gap_divides : 3 * t + 1 ∣ n
  order_five : n % 5 = 4
  inverse_congruence : ∀ i, 5 * crtFactor (3 * t + 1) (family.kappa i) ∣ family.kappa i * n + 1
  direction_coprime : ∀ i, (5 * crtFactor (3 * t + 1) (family.kappa i)).Coprime n

theorem exists_cyclic_integer_data (r : Nat) : Nonempty (CyclicIntegerData r) := by
  obtain ⟨t, hrt, htr, hq15⟩ := exists_gap_parameter r
  obtain ⟨p⟩ := exists_parameter_family (3 * t + 1) (by omega) (3 * t)
  obtain ⟨n, hn, hn3, hnq, hn5, hi⟩ := exists_graph_order_with_units (by omega) hq15 p
    (1000 * (r + 1) * (3 * t + 1) * p.period ^ 2)
  exact ⟨{
    t := t
    gap_lower := hrt
    gap_upper := htr
    gap_coprime := hq15
    family := p
    n := n
    large_order := hn
    order_three := hn3
    gap_divides := hnq
    order_five := hn5
    inverse_congruence := fun i => (hi i).1
    direction_coprime := fun i => (hi i).2
  }⟩

theorem cyclic_data_period_lt_order {r : Nat} (p : CyclicIntegerData r) : p.family.period < p.n := by
  have hP : p.family.period ≤ p.family.period ^ 2 := Nat.le_self_pow (by decide) _
  have hC : 0 < 1000 * (r + 1) * (3 * p.t + 1) :=
    Nat.mul_pos (Nat.mul_pos (by decide) (by omega)) (by omega)
  exact lt_of_le_of_lt (hP.trans (Nat.le_mul_of_pos_left _ hC)) p.large_order

theorem cyclic_data_order_pos {r : Nat} (p : CyclicIntegerData r) : 0 < p.n :=
  (parameter_period_pos p.family).trans (cyclic_data_period_lt_order p)

theorem cyclic_data_orientation_lt_order {r : Nat} (p : CyclicIntegerData r)
    (i : Fin (3 * p.t + 1)) : p.family.orientation i < p.n :=
  lt_of_le_of_lt (Nat.le_of_dvd (parameter_period_pos p.family) (orientation_dvd_period p.family i))
    (cyclic_data_period_lt_order p)

theorem cyclic_data_orientation_coprime {r : Nat} (p : CyclicIntegerData r)
    (i : Fin (3 * p.t + 1)) : (p.family.orientation i).Coprime p.n := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact Nat.coprime_one_left _
  · exact p.direction_coprime j

def CyclicIntegerData.unitDirection {r : Nat} (p : CyclicIntegerData r)
    (i : ZMod (3 * p.t + 1)) : (ZMod p.n)ˣ :=
  ZMod.unitOfCoprime (p.family.orientation ⟨i.val, ZMod.val_lt i⟩)
    (cyclic_data_orientation_coprime p _)

theorem cyclic_data_unitDirection_val {r : Nat} (p : CyclicIntegerData r)
    (i : ZMod (3 * p.t + 1)) :
    ((p.unitDirection i : (ZMod p.n)ˣ) : ZMod p.n).val =
      p.family.orientation ⟨i.val, ZMod.val_lt i⟩ := by
  let : NeZero p.n := ⟨Nat.ne_of_gt (cyclic_data_order_pos p)⟩
  change (p.family.orientation ⟨i.val, ZMod.val_lt i⟩ : ZMod p.n).val = _
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (cyclic_data_orientation_lt_order p _)]

theorem coordinate_numerator_dvd {a κ n s : Nat} (h : a ∣ κ * n + 1) :
    a ∣ s + (κ * s % a) * n := by
  have he : Nat.ModEq a (κ * s % a) (κ * s) := Nat.mod_modEq _ _
  have he' := (he.mul_right n).add_left s
  have hid : s + (κ * s) * n = s * (κ * n + 1) := by ring
  rw [hid] at he'
  exact Nat.dvd_of_mod_eq_zero
    (Eq.trans he' (Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_right h s)))

theorem normalized_coordinate_formula {a κ n s : Nat} (hn : 0 < n) (ha : 0 < a)
    (hs : s < n) (h : a ∣ κ * n + 1) :
    ((a : ZMod n)⁻¹ * (s : ZMod n)).val = (s + (κ * s % a) * n) / a := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let e := κ * s % a
  let R := (s + e * n) / a
  have hR : a * R = s + e * n := Nat.mul_div_cancel' (coordinate_numerator_dvd h)
  have he : e < a := Nat.mod_lt _ ha
  have hRlt : R < n := by
    have hsize : s + e * n < a * n := by nlinarith
    nlinarith
  have hc : a.Coprime n := coprime_of_dvd_mul_add_one h
  have hz : (a : ZMod n) * (R : ZMod n) = (s : ZMod n) := by
    rw [← Nat.cast_mul, hR]
    simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, add_zero]
  have hinv : (a : ZMod n)⁻¹ * (a : ZMod n) = 1 := by
    rw [mul_comm]
    exact ZMod.coe_mul_inv_eq_one a hc
  have hval : (a : ZMod n)⁻¹ * (s : ZMod n) = (R : ZMod n) := by
    rw [← hz, ← mul_assoc, hinv, one_mul]
  rw [hval, ZMod.val_natCast, Nat.mod_eq_of_lt hRlt]

theorem normalized_coordinate_mul {a κ n s : Nat} (hn : 0 < n) (ha : 0 < a)
    (hs : s < n) (h : a ∣ κ * n + 1) :
    a * ((a : ZMod n)⁻¹ * (s : ZMod n)).val = s + (κ * s % a) * n := by
  rw [normalized_coordinate_formula hn ha hs h]
  exact Nat.mul_div_cancel' (coordinate_numerator_dvd h)

theorem normalized_coordinate_mod_three {a κ n s : Nat} (hn : 0 < n) (ha : 0 < a)
    (hs : s < n) (h : a ∣ κ * n + 1) (ha3 : a % 3 = 2) (hn3 : n % 3 = 1)
    (hs3 : s % 3 = 2) (he3 : (κ * s % a) % 3 = 2) :
    ((a : ZMod n)⁻¹ * (s : ZMod n)).val % 3 = 2 := by
  have he := congrArg (fun x : Nat => x % 3) (normalized_coordinate_mul hn ha hs h)
  rw [Nat.mul_mod a _ 3, ha3, Nat.add_mod s _ 3, hs3,
    Nat.mul_mod (κ * s % a) n 3, he3, hn3] at he
  omega

theorem cyclic_data_coordinate_formula {r : Nat} (p : CyclicIntegerData r)
    (i : Fin (3 * p.t)) {s : Nat} (hs : s < p.n) :
    (((p.family.orientation i.succ : Nat) : ZMod p.n)⁻¹ * (s : ZMod p.n)).val =
      (s + (p.family.kappa i * s % p.family.orientation i.succ) * p.n) /
        p.family.orientation i.succ := by
  exact normalized_coordinate_formula (cyclic_data_order_pos p)
    (orientation_pos p.family i.succ) hs (p.inverse_congruence i)

theorem crtFactor_sub_kappa {q κ : Nat} (hq : 0 < q) (hk : 1 ≤ κ) :
    crtFactor q κ - κ = (30 * q - 1) * (κ - 1) := by
  have hD : 30 * q = (30 * q - 1) + 1 := by omega
  unfold crtFactor
  rw [hD, Nat.add_mul, Nat.one_mul, Nat.add_assoc, Nat.sub_add_cancel hk,
    Nat.add_sub_cancel, Nat.add_sub_cancel]

theorem orientation_cross_identity {q κ μ : Nat} (hq : 0 < q) (hk : 1 ≤ κ) (hm : 1 ≤ μ) :
    (5 * crtFactor q κ) * μ = (5 * crtFactor q μ) * (κ - 1) +
      (5 * μ + 5 * (crtFactor q κ - κ)) := by
  rw [crtFactor_sub_kappa hq hk]
  have hD : (30 * q - 1) + 1 = 30 * q := by omega
  have hμ : (μ - 1) + 1 = μ := by omega
  have hD' := congrArg (fun x => 5 * (κ - 1) * x) hD
  have hμ' := congrArg (fun x => 5 * (30 * q) * (κ - 1) * x) hμ
  unfold crtFactor
  nlinarith only [hD', hμ']

theorem kappa_short_bound {q κ : Nat} (hq : 0 < q) (hk : 6 ≤ κ) :
    40 * q * κ < 5 * crtFactor q κ := by
  have he := crtFactor_add (κ := κ) hq (by omega)
  have hD : (30 * q - 1) + 1 = 30 * q := by omega
  have hκq := Nat.mul_le_mul_left q hk
  nlinarith

theorem forward_residual {q N : Nat} (hq : 0 < q) (p : ParameterFamily q N)
    {i j : Fin N} (hij : i < j) :
    (p.orientation i.succ * p.kappa j) % p.orientation j.succ =
      5 * p.kappa j + 5 * (crtFactor q (p.kappa i) - p.kappa i) ∧
    4 * q * ((p.orientation i.succ * p.kappa j) % p.orientation j.succ) <
      p.orientation j.succ := by
  let E := 5 * p.kappa j + 5 * (crtFactor q (p.kappa i) - p.kappa i)
  have hE : E ≤ 5 * p.kappa j + p.orientation i.succ := by
    change 5 * p.kappa j + 5 * (crtFactor q (p.kappa i) - p.kappa i) ≤
      5 * p.kappa j + 5 * crtFactor q (p.kappa i)
    exact Nat.add_le_add_left (Nat.mul_le_mul_left 5 (Nat.sub_le _ _)) _
  have hκ : 40 * q * p.kappa j < p.orientation j.succ := kappa_short_bound hq (p.large j)
  have hsep : 10 * q * p.orientation i.succ < p.orientation j.succ := p.separated i j hij
  have hsmall : 4 * q * E < p.orientation j.succ := by
    nlinarith [Nat.mul_le_mul_left (8 * q) hE]
  have hElt : E < p.orientation j.succ :=
    lt_of_le_of_lt (Nat.le_mul_of_pos_left _ (by omega : 0 < 4 * q)) hsmall
  have he : p.orientation i.succ * p.kappa j =
      p.orientation j.succ * (p.kappa i - 1) + E :=
    orientation_cross_identity (κ := p.kappa i) (μ := p.kappa j) hq
      (by have h := p.large i; omega) (by have h := p.large j; omega)
  have hmod : (p.orientation i.succ * p.kappa j) % p.orientation j.succ = E := by
    rw [he]
    simp [Nat.mod_eq_of_lt hElt]
  exact ⟨hmod, by rw [hmod]; exact hsmall⟩

theorem reverse_residual {q N : Nat} (p : ParameterFamily q N)
    {i j : Fin N} (hji : j < i) :
    (p.orientation i.succ * p.kappa j) % p.orientation j.succ = 5 := by
  change ((5 * crtFactor q (p.kappa i)) * p.kappa j) % (5 * crtFactor q (p.kappa j)) = 5
  rw [Nat.mul_assoc, Nat.mul_mod_mul_left, Nat.mul_comm (crtFactor q (p.kappa i)) (p.kappa j),
    p.cross j i hji, Nat.mul_one]

theorem positive_residual_mod_three {q N : Nat} (hq : 0 < q) (p : ParameterFamily q N)
    {i j : Fin N} (hij : i ≠ j) :
    ((p.orientation i.succ * p.kappa j) % p.orientation j.succ) % 3 = 2 := by
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · rw [(forward_residual hq p hlt).1]
    have hd : crtFactor q (p.kappa i) % 3 = 1 := by
      have h := crtFactor_mod_fifteen q (p.kappa i)
      omega
    have hki := p.mod_three i
    have hkj := p.mod_three j
    have hle := crtFactor_ge_kappa (κ := p.kappa i) hq (by have h := p.large i; omega)
    have hsub : (crtFactor q (p.kappa i) - p.kappa i) % 3 = 1 := by omega
    simp [Nat.add_mod, Nat.mul_mod, hkj, hsub]
  · rw [reverse_residual p hgt]

theorem positive_residual_short {q N : Nat} (hq : 0 < q) (p : ParameterFamily q N)
    {i j : Fin N} (hij : i ≠ j) :
    q * ((p.orientation i.succ * p.kappa j) % p.orientation j.succ) < p.orientation j.succ := by
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have h := (forward_residual hq p hlt).2
    nlinarith
  · rw [reverse_residual p hgt]
    have h : 10 * q < p.orientation j.succ := p.start j
    omega

theorem normalized_coordinate_short {a κ n s q : Nat} (hn : 0 < n) (ha : 0 < a)
    (hs : s < n) (h : a ∣ κ * n + 1) (hqs : q * s < n)
    (he : q * (κ * s % a) < a) :
    q * ((a : ZMod n)⁻¹ * (s : ZMod n)).val < n := by
  have hR := congrArg (fun x => q * x) (normalized_coordinate_mul hn ha hs h)
  have he' := Nat.mul_le_mul_right n (Nat.succ_le_of_lt he)
  apply lt_of_not_ge
  intro hle
  have hm := Nat.mul_le_mul_left a hle
  nlinarith only [hqs, hR, he', hm]

theorem normalized_coordinate_mod_three_of_phase {a κ n s : Nat} (hn : 0 < n) (ha : 0 < a)
    (hs : s < n) (h : a ∣ κ * n + 1) (ha3 : a % 3 = 2) (hn3 : n % 3 = 1)
    (hphase : (s + (κ * s % a)) % 3 = 1) :
    ((a : ZMod n)⁻¹ * (s : ZMod n)).val % 3 = 2 := by
  have he := congrArg (fun x : Nat => x % 3) (normalized_coordinate_mul hn ha hs h)
  rw [Nat.mul_mod a _ 3, ha3, Nat.add_mod s _ 3,
    Nat.mul_mod (κ * s % a) n 3, hn3, Nat.mul_one] at he
  simp only [Nat.mod_mod] at he
  rw [Nat.add_mod] at hphase
  rw [hphase] at he
  omega

theorem cyclic_data_gap_period_lt_order {r : Nat} (p : CyclicIntegerData r) :
    (3 * p.t + 1) * p.family.period < p.n := by
  have hP : p.family.period ≤ p.family.period ^ 2 := Nat.le_self_pow (by decide) _
  have hC : 0 < 1000 * (r + 1) := by omega
  apply lt_of_le_of_lt ?_ p.large_order
  calc
    (3 * p.t + 1) * p.family.period ≤ (3 * p.t + 1) * p.family.period ^ 2 :=
      Nat.mul_le_mul_left _ hP
    _ ≤ (1000 * (r + 1)) * ((3 * p.t + 1) * p.family.period ^ 2) :=
      Nat.le_mul_of_pos_left _ hC
    _ = 1000 * (r + 1) * (3 * p.t + 1) * p.family.period ^ 2 := by ring

theorem cyclic_data_gap_lt_order {r : Nat} (p : CyclicIntegerData r) : 3 * p.t + 1 < p.n :=
  lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (parameter_period_pos p.family))
    (cyclic_data_gap_period_lt_order p)

theorem cyclic_data_orientation_short {r : Nat} (p : CyclicIntegerData r)
    (i : Fin (3 * p.t + 1)) : (3 * p.t + 1) * p.family.orientation i < p.n := by
  have hi := Nat.le_of_dvd (parameter_period_pos p.family) (orientation_dvd_period p.family i)
  exact lt_of_le_of_lt (Nat.mul_le_mul_left _ hi) (cyclic_data_gap_period_lt_order p)

theorem cyclic_data_natural_ratios {r : Nat} (p : CyclicIntegerData r)
    (i j : Fin (3 * p.t + 1)) (hij : i ≠ j) :
    (3 * p.t + 1) * (((p.family.orientation i : Nat) : ZMod p.n)⁻¹ *
      ((p.family.orientation j : Nat) : ZMod p.n)).val < p.n ∧
    ((((p.family.orientation i : Nat) : ZMod p.n)⁻¹ *
      ((p.family.orientation j : Nat) : ZMod p.n)).val) % 3 = 2 := by
  let : NeZero p.n := ⟨Nat.ne_of_gt (cyclic_data_order_pos p)⟩
  have hn := cyclic_data_order_pos p
  have hq : 0 < 3 * p.t + 1 := by omega
  have hz : p.family.orientation (0 : Fin (3 * p.t + 1)) = 1 := by
    simp [ParameterFamily.orientation]
  revert hij
  refine Fin.cases ?_ (fun i' => ?_) i
  · refine Fin.cases ?_ (fun j' => ?_) j
    · intro h
      exact False.elim (h rfl)
    · intro _
      have hv : (((p.family.orientation 0 : Nat) : ZMod p.n)⁻¹ *
          ((p.family.orientation j'.succ : Nat) : ZMod p.n)).val = p.family.orientation j'.succ := by
        rw [hz, Nat.cast_one, ZMod.inv_one, one_mul, ZMod.val_natCast,
          Nat.mod_eq_of_lt (cyclic_data_orientation_lt_order p _)]
      rw [hv]
      exact ⟨cyclic_data_orientation_short p _, orientation_mod_three p.family j'⟩
  · refine Fin.cases ?_ (fun j' => ?_) j
    · intro _
      rw [hz]
      have hκ : (3 * p.t + 1) * p.family.kappa i' < p.family.orientation i'.succ := by
        have h := kappa_short_bound hq (p.family.large i')
        change 40 * (3 * p.t + 1) * p.family.kappa i' < p.family.orientation i'.succ at h
        nlinarith
      have hκlt : p.family.kappa i' < p.family.orientation i'.succ :=
        lt_of_le_of_lt (Nat.le_mul_of_pos_left _ hq) hκ
      have he : (p.family.kappa i' * 1) % p.family.orientation i'.succ = p.family.kappa i' := by
        rw [Nat.mul_one, Nat.mod_eq_of_lt hκlt]
      have hs : 1 < p.n := by have h := cyclic_data_gap_lt_order p; omega
      have hqs : (3 * p.t + 1) * 1 < p.n := by simpa only [Nat.mul_one] using cyclic_data_gap_lt_order p
      have hphase : (1 + (p.family.kappa i' * 1 % p.family.orientation i'.succ)) % 3 = 1 := by
        rw [he, Nat.add_mod, p.family.mod_three i']
      exact ⟨normalized_coordinate_short hn (orientation_pos p.family i'.succ) hs
          (p.inverse_congruence i') hqs (by rw [he]; exact hκ),
        normalized_coordinate_mod_three_of_phase hn (orientation_pos p.family i'.succ) hs
          (p.inverse_congruence i') (orientation_mod_three p.family i') p.order_three hphase⟩
    · intro h
      have hne : j' ≠ i' := by
        intro he
        exact h (congrArg Fin.succ he.symm)
      have heShort : (3 * p.t + 1) * (p.family.kappa i' * p.family.orientation j'.succ %
          p.family.orientation i'.succ) < p.family.orientation i'.succ := by
        rw [Nat.mul_comm (p.family.kappa i') (p.family.orientation j'.succ)]
        exact positive_residual_short hq p.family hne
      have heThree : (p.family.kappa i' * p.family.orientation j'.succ %
          p.family.orientation i'.succ) % 3 = 2 := by
        rw [Nat.mul_comm (p.family.kappa i') (p.family.orientation j'.succ)]
        exact positive_residual_mod_three hq p.family hne
      exact ⟨normalized_coordinate_short hn (orientation_pos p.family i'.succ)
          (cyclic_data_orientation_lt_order p j'.succ) (p.inverse_congruence i')
          (cyclic_data_orientation_short p j'.succ) heShort,
        normalized_coordinate_mod_three hn (orientation_pos p.family i'.succ)
          (cyclic_data_orientation_lt_order p j'.succ) (p.inverse_congruence i')
          (orientation_mod_three p.family i') p.order_three
          (orientation_mod_three p.family j') heThree⟩

theorem cyclic_data_shortCompatible {r : Nat} (p : CyclicIntegerData r) :
    ShortCompatible (3 * p.t + 1) p.unitDirection := by
  intro i j hij
  have hidx : (⟨i.val, ZMod.val_lt i⟩ : Fin (3 * p.t + 1)) ≠ ⟨j.val, ZMod.val_lt j⟩ := by
    intro he
    exact hij (ZMod.val_injective _ (congrArg Fin.val he))
  exact cyclic_data_natural_ratios p _ _ hidx

def ParameterFamily.GenericResidue {q N : Nat} (p : ParameterFamily q N) (s : Nat) : Prop :=
  s % 3 = 2 ∧ ∀ i, (p.kappa i * s % p.orientation i.succ) % 3 = 2

theorem three_dvd_parameter_period {q N : Nat} (p : ParameterFamily q N) : 3 ∣ p.period := by
  refine ⟨5 * ∏ i : Fin N, crtFactor q (p.kappa i), ?_⟩
  unfold ParameterFamily.period
  ring

theorem five_dvd_parameter_period {q N : Nat} (p : ParameterFamily q N) : 5 ∣ p.period := by
  refine ⟨3 * ∏ i : Fin N, crtFactor q (p.kappa i), ?_⟩
  unfold ParameterFamily.period
  ring

theorem genericResidue_modEq {q N : Nat} (p : ParameterFamily q N) {s z : Nat}
    (he : Nat.ModEq p.period s z) : p.GenericResidue s ↔ p.GenericResidue z := by
  have h₃ : s % 3 = z % 3 := he.of_dvd (three_dvd_parameter_period p)
  have hc : ∀ i, p.kappa i * s % p.orientation i.succ =
      p.kappa i * z % p.orientation i.succ := fun i =>
    (he.of_dvd (orientation_dvd_period p i.succ)).mul_left (p.kappa i)
  constructor
  · intro hs
    exact ⟨h₃.symm.trans hs.1, fun i => by rw [← hc i]; exact hs.2 i⟩
  · intro hz
    exact ⟨h₃.trans hz.1, fun i => by rw [hc i]; exact hz.2 i⟩

theorem genericResidue_mod_period {q N : Nat} (p : ParameterFamily q N) (s : Nat) :
    p.GenericResidue (s % p.period) ↔ p.GenericResidue s :=
  genericResidue_modEq p (Nat.mod_modEq _ _)

theorem genericResidue_add_period {q N : Nat} (p : ParameterFamily q N) (s : Nat) :
    p.GenericResidue (s + p.period) ↔ p.GenericResidue s := by
  apply genericResidue_modEq
  simp [Nat.ModEq]

theorem cyclic_data_generic_coordinates {r : Nat} (p : CyclicIntegerData r)
    {s : Nat} (hs : s < p.n) (hgen : p.family.GenericResidue s)
    (i : Fin (3 * p.t + 1)) :
    (((p.family.orientation i : Nat) : ZMod p.n)⁻¹ * (s : ZMod p.n)).val % 3 = 2 := by
  let : NeZero p.n := ⟨Nat.ne_of_gt (cyclic_data_order_pos p)⟩
  refine Fin.cases ?_ (fun j => ?_) i
  · have hz : p.family.orientation (0 : Fin (3 * p.t + 1)) = 1 := by
      simp [ParameterFamily.orientation]
    rw [hz, Nat.cast_one, ZMod.inv_one, one_mul, ZMod.val_natCast, Nat.mod_eq_of_lt hs]
    exact hgen.1
  · exact normalized_coordinate_mod_three (cyclic_data_order_pos p)
      (orientation_pos p.family j.succ) hs (p.inverse_congruence j)
      (orientation_mod_three p.family j) p.order_three hgen.1 (hgen.2 j)

theorem cyclic_data_generic_unit_coordinates {r : Nat} (p : CyclicIntegerData r)
    {s : Nat} (hs : s < p.n) (hgen : p.family.GenericResidue s)
    (i : ZMod (3 * p.t + 1)) :
    ((↑(p.unitDirection i)⁻¹ : ZMod p.n) * (s : ZMod p.n)).val % 3 = 2 :=
  cyclic_data_generic_coordinates p hs hgen ⟨i.val, ZMod.val_lt i⟩

theorem exists_prescribed_coordinates {q N : Nat} (hq : 0 < q) (p : ParameterFamily q N)
    (E : Fin N → Nat) (z : Nat) (hE : ∀ i, E i < p.orientation i.succ)
    (hE5 : ∀ i, E i % 5 = z % 5) (B : Nat) :
    ∃ s : Nat, B < s ∧ s % 3 = 2 ∧ s % 5 = z % 5 ∧
      ∀ i, p.kappa i * s % p.orientation i.succ = E i := by
  classical
  let d := fun i => crtFactor q (p.kappa i)
  have hd : ∀ i, 1 < d i := by
    intro i
    change 1 < crtFactor q (p.kappa i)
    have h := crtFactor_ge_kappa (κ := p.kappa i) hq (by have h := p.large i; omega)
    have hi := p.large i
    omega
  have hk : ∀ i, (p.kappa i).Coprime (d i) := fun i =>
    kappa_coprime_crtFactor hq (by have h := p.large i; omega) (p.mod_aux i)
  choose v hv using fun i => exists_inverse_residue (hd i) (hk i)
  let a := fun i => v i * E i
  let c := Nat.chineseRemainder (by decide : (3 : Nat).Coprime 5) 2 z
  obtain ⟨s, hs, hsbase, hsmods⟩ := exists_large_crt_with_base 15 c.val (by decide) d a
    (fun i => by have h := hd i; omega) p.coprime
    (fun i => coprime_of_remainder_one (crtFactor_mod_fifteen q (p.kappa i))) B
  have hbase : Nat.ModEq 15 s c.val := hsbase
  have hs3 : s % 3 = 2 := (hbase.of_dvd (by decide : 3 ∣ 15)).trans c.property.1
  have hs5 : s % 5 = z % 5 := (hbase.of_dvd (by decide : 5 ∣ 15)).trans c.property.2
  refine ⟨s, hs, hs3, hs5, ?_⟩
  intro i
  have hv' : Nat.ModEq (d i) (p.kappa i * v i) 1 := by
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt (hd i)] using hv i
  have hm : Nat.ModEq (d i) s (a i) := hsmods i
  have hdi : Nat.ModEq (d i) (p.kappa i * s) (E i) := by
    calc
      p.kappa i * s ≡ p.kappa i * a i [MOD d i] := hm.mul_left _
      _ = (p.kappa i * v i) * E i := by dsimp [a]; ring
      _ ≡ 1 * E i [MOD d i] := hv'.mul_right _
      _ = E i := one_mul _
  have hκ5 : p.kappa i % 5 = 1 := by
    have h := kappa_mod_fifteen (p.mod_three i) (p.mod_aux i)
    omega
  have h5 : Nat.ModEq 5 (p.kappa i * s) (E i) := by
    simp [Nat.ModEq, Nat.mul_mod, hκ5, hs5, hE5 i]
  have hcop : (5 : Nat).Coprime (d i) :=
    (Nat.Coprime.coprime_dvd_right (by decide : 5 ∣ 15)
      (coprime_of_remainder_one (crtFactor_mod_fifteen q (p.kappa i)))).symm
  have he : Nat.ModEq (5 * d i) (p.kappa i * s) (E i) :=
    (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨h5, hdi⟩
  exact Eq.trans he (Nat.mod_eq_of_lt (hE i))

theorem exists_generic_with_coordinates {q N : Nat} (hq : 0 < q) (p : ParameterFamily q N)
    (E : Fin N → Nat) (z : Nat) (hE : ∀ i, E i < p.orientation i.succ)
    (hE5 : ∀ i, E i % 5 = z % 5) (hE3 : ∀ i, E i % 3 = 2) (B : Nat) :
    ∃ s : Nat, B < s ∧ p.GenericResidue s ∧ s % 5 = z % 5 ∧
      ∀ i, p.kappa i * s % p.orientation i.succ = E i := by
  obtain ⟨s, hs, hs3, hs5, hc⟩ := exists_prescribed_coordinates hq p E z hE hE5 B
  exact ⟨s, hs, ⟨hs3, fun i => by rw [hc i]; exact hE3 i⟩, hs5, hc⟩

theorem orientation_gt_hundred {q N : Nat} (hq : 0 < q) (p : ParameterFamily q N)
    (i : Fin N) : 100 < p.orientation i.succ := by
  have h := kappa_short_bound hq (p.large i)
  change 40 * q * p.kappa i < p.orientation i.succ at h
  have hκq := Nat.mul_le_mul_left (p.kappa i) (show 1 ≤ q by omega)
  have hk := p.large i
  nlinarith

theorem generic_residue_in_each_block {q N : Nat} (hq : 0 < q) (p : ParameterFamily q N)
    (h : Fin 5) : ∃ ρ : Nat, ρ < p.period ∧ p.GenericResidue ρ ∧ ρ % 5 = (2 + 3 * h.val) % 5 := by
  let E : Fin N → Nat := fun _ => 2 + 3 * h.val
  have hE : ∀ i, E i < p.orientation i.succ := by
    intro i
    have hi := orientation_gt_hundred hq p i
    have hh := h.isLt
    dsimp [E]
    omega
  obtain ⟨s, _, hs, hs5, _⟩ := exists_generic_with_coordinates hq p E (2 + 3 * h.val) hE
    (fun _ => rfl) (fun _ => by dsimp [E]; omega) 0
  refine ⟨s % p.period, Nat.mod_lt _ (parameter_period_pos p),
    (genericResidue_mod_period p s).mpr hs, ?_⟩
  rw [Nat.mod_mod_of_dvd s (five_dvd_parameter_period p)]
  exact hs5

def gridBound (d : Nat) (h : Fin 5) : Nat :=
  if h.val = 0 then (d - 1) / 3 else (d - 1) / 3 - 1

theorem grid_coordinate_range {d y : Nat} (hd : 1 < d) (hd15 : d % 15 = 1) (h : Fin 5) :
    2 + 3 * h.val + 15 * y < 5 * d ↔ y ≤ gridBound d h := by
  have hh := h.isLt
  unfold gridBound
  split_ifs with hz <;> omega

theorem parameter_coordinate_mod_five {q N : Nat} (p : ParameterFamily q N)
    (s : Nat) (i : Fin N) : (p.kappa i * s % p.orientation i.succ) % 5 = s % 5 := by
  have hκ5 : p.kappa i % 5 = 1 := by
    have h := kappa_mod_fifteen (p.mod_three i) (p.mod_aux i)
    omega
  change (p.kappa i * s % (5 * crtFactor q (p.kappa i))) % 5 = s % 5
  rw [Nat.mod_mod_of_dvd _ (dvd_mul_right 5 _), Nat.mul_mod, hκ5, Nat.one_mul, Nat.mod_mod]

theorem generic_grid_representation {q N : Nat} (hq : 0 < q) (p : ParameterFamily q N)
    {s : Nat} (hs : p.GenericResidue s) :
    ∃ h : Fin 5, ∃ y : Fin N → Nat,
      s % 5 = (2 + 3 * h.val) % 5 ∧
      (∀ i, y i ≤ gridBound (crtFactor q (p.kappa i)) h) ∧
      ∀ i, p.kappa i * s % p.orientation i.succ = 2 + 3 * h.val + 15 * y i := by
  let h : Fin 5 := ⟨(2 * s + 1) % 5, Nat.mod_lt _ (by decide)⟩
  let e := fun i => p.kappa i * s % p.orientation i.succ
  let y := fun i => e i / 15
  have hs5 : s % 5 = (2 + 3 * h.val) % 5 := by
    change s % 5 = (2 + 3 * ((2 * s + 1) % 5)) % 5
    omega
  have he15 : ∀ i, e i % 15 = 2 + 3 * h.val := by
    intro i
    have he3 : e i % 3 = 2 := hs.2 i
    have he5 : e i % 5 = s % 5 := parameter_coordinate_mod_five p s i
    have hh := h.isLt
    omega
  have heq : ∀ i, e i = 2 + 3 * h.val + 15 * y i := by
    intro i
    have he := Nat.mod_add_div (e i) 15
    rw [he15 i] at he
    exact he.symm
  refine ⟨h, y, hs5, ?_, heq⟩
  intro i
  have hd : 1 < crtFactor q (p.kappa i) := by
    have hg := crtFactor_ge_kappa (κ := p.kappa i) hq (by have h := p.large i; omega)
    have hi := p.large i
    omega
  apply (grid_coordinate_range hd (crtFactor_mod_fifteen q (p.kappa i)) h).mp
  rw [← heq i]
  exact Nat.mod_lt _ (orientation_pos p i.succ)

theorem exists_generic_grid_class {q N : Nat} (hq : 0 < q) (p : ParameterFamily q N)
    (h : Fin 5) (y : Fin N → Nat) (hy : ∀ i, y i ≤ gridBound (crtFactor q (p.kappa i)) h) :
    ∃ ρ : Nat, ρ < p.period ∧ p.GenericResidue ρ ∧ ρ % 5 = (2 + 3 * h.val) % 5 ∧
      ∀ i, p.kappa i * ρ % p.orientation i.succ = 2 + 3 * h.val + 15 * y i := by
  let E := fun i => 2 + 3 * h.val + 15 * y i
  have hE : ∀ i, E i < p.orientation i.succ := by
    intro i
    have hd : 1 < crtFactor q (p.kappa i) := by
      have hg := crtFactor_ge_kappa (κ := p.kappa i) hq (by have h := p.large i; omega)
      have hi := p.large i
      omega
    exact (grid_coordinate_range hd (crtFactor_mod_fifteen q (p.kappa i)) h).mpr (hy i)
  obtain ⟨s, _, hs, hs5, hc⟩ := exists_generic_with_coordinates hq p E (2 + 3 * h.val) hE
    (fun i => by dsimp [E]; omega) (fun i => by dsimp [E]; omega) 0
  refine ⟨s % p.period, Nat.mod_lt _ (parameter_period_pos p),
    (genericResidue_mod_period p s).mpr hs, ?_, ?_⟩
  · rw [Nat.mod_mod_of_dvd s (five_dvd_parameter_period p)]
    exact hs5
  · intro i
    have hm := (Nat.mod_modEq s p.period).of_dvd (orientation_dvd_period p i.succ)
    exact Eq.trans (hm.mul_left (p.kappa i)) (hc i)

theorem generic_residue_avoids_class {q N : Nat} (hq : 0 < q) (p : ParameterFamily q N) (x : Nat) :
    ∃ ρ : Nat, ρ < p.period ∧ p.GenericResidue ρ ∧ ρ ≠ x := by
  obtain ⟨s, hs, hsg, hs5⟩ := generic_residue_in_each_block hq p (0 : Fin 5)
  obtain ⟨z, hz, hzg, hz5⟩ := generic_residue_in_each_block hq p (1 : Fin 5)
  have hsz : s ≠ z := by
    norm_num at hs5 hz5
    omega
  by_cases hx : s = x
  · exact ⟨z, hz, hzg, fun he => hsz (hx.trans he.symm)⟩
  · exact ⟨s, hs, hsg, hx⟩

theorem genericResidue_iff_grid {q N : Nat} (hq : 0 < q) (p : ParameterFamily q N) (s : Nat) :
    p.GenericResidue s ↔ s % 3 = 2 ∧ ∃ h : Fin 5, ∃ y : Fin N → Nat,
      s % 5 = (2 + 3 * h.val) % 5 ∧
      (∀ i, y i ≤ gridBound (crtFactor q (p.kappa i)) h) ∧
      ∀ i, p.kappa i * s % p.orientation i.succ = 2 + 3 * h.val + 15 * y i := by
  constructor
  · intro hs
    exact ⟨hs.1, generic_grid_representation hq p hs⟩
  · rintro ⟨hs3, h, y, _, _, hc⟩
    refine ⟨hs3, fun i => ?_⟩
    rw [hc i]
    omega

theorem modEq_finset_product {I : Type*} (F : Finset I) (m : I → Nat)
    (hcop : Pairwise (fun i j => (m i).Coprime (m j))) {s z : Nat}
    (hmods : ∀ i ∈ F, Nat.ModEq (m i) s z) : Nat.ModEq (∏ i ∈ F, m i) s z := by
  classical
  induction F using Finset.induction_on with
  | empty => simp [Nat.ModEq, Nat.mod_one]
  | @insert i F hi ih =>
    rw [Finset.prod_insert hi]
    have hc : (m i).Coprime (∏ j ∈ F, m j) := Nat.Coprime.prod_right (fun j hj =>
      hcop (fun he => hi (he ▸ hj)))
    exact (Nat.modEq_and_modEq_iff_modEq_mul hc).mp
      ⟨hmods i (Finset.mem_insert_self _ _), ih (fun j hj => hmods j (Finset.mem_insert_of_mem hj))⟩

theorem parameter_coordinates_determine_class {q N : Nat} (hq : 0 < q)
    (p : ParameterFamily q N) {s z : Nat} (h3 : Nat.ModEq 3 s z) (h5 : Nat.ModEq 5 s z)
    (hc : ∀ i, p.kappa i * s % p.orientation i.succ = p.kappa i * z % p.orientation i.succ) :
    Nat.ModEq p.period s z := by
  let d := fun i => crtFactor q (p.kappa i)
  have hd : ∀ i, Nat.ModEq (d i) s z := by
    intro i
    have hκ := kappa_coprime_crtFactor (κ := p.kappa i) hq (by have h := p.large i; omega)
      (p.mod_aux i)
    have he : Nat.ModEq (5 * d i) (p.kappa i * s) (p.kappa i * z) := hc i
    exact Nat.ModEq.cancel_left_of_coprime hκ.symm (he.of_dvd (dvd_mul_left (d i) 5))
  have hprod : Nat.ModEq (∏ i : Fin N, d i) s z :=
    modEq_finset_product Finset.univ d p.coprime (fun i _ => hd i)
  have h15 : Nat.ModEq 15 s z :=
    (Nat.modEq_and_modEq_iff_modEq_mul (by decide : (3 : Nat).Coprime 5)).mp ⟨h3, h5⟩
  have hcop : (15 : Nat).Coprime (∏ i : Fin N, d i) := Nat.Coprime.prod_right (fun i _ =>
    (coprime_of_remainder_one (crtFactor_mod_fifteen q (p.kappa i))).symm)
  exact (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨h15, hprod⟩

theorem existsUnique_generic_grid_class {q N : Nat} (hq : 0 < q) (p : ParameterFamily q N)
    (h : Fin 5) (y : Fin N → Nat) (hy : ∀ i, y i ≤ gridBound (crtFactor q (p.kappa i)) h) :
    ∃! ρ : Nat, ρ < p.period ∧ p.GenericResidue ρ ∧ ρ % 5 = (2 + 3 * h.val) % 5 ∧
      ∀ i, p.kappa i * ρ % p.orientation i.succ = 2 + 3 * h.val + 15 * y i := by
  obtain ⟨ρ, hρ, hgen, h5, hc⟩ := exists_generic_grid_class hq p h y hy
  refine ⟨ρ, ⟨hρ, hgen, h5, hc⟩, ?_⟩
  intro z hz
  have he := parameter_coordinates_determine_class hq p
    (show Nat.ModEq 3 z ρ from hz.2.1.1.trans hgen.1.symm)
    (show Nat.ModEq 5 z ρ from hz.2.2.1.trans h5.symm)
    (fun i => (hz.2.2.2 i).trans (hc i).symm)
  rw [Nat.ModEq, Nat.mod_eq_of_lt hz.1, Nat.mod_eq_of_lt hρ] at he
  exact he

/-- Explicit arithmetic hypotheses suffice to produce a four-color witness in any universe. -/
theorem erdos944_four_from_arithmetic_conditions {n r t : Nat} [NeZero n]
    (hrt : r ≤ t) (hn : n % 3 = 1) (hq : 3 * t + 1 ∣ n) (htn : 3 * t + 1 < n)
    (a : ZMod (3 * t + 1) → (ZMod n)ˣ) (ha : ShortCompatible (3 * t + 1) a)
    (hwords : ∀ s ∈ canonicalConnections a, ∀ F : Finset (ZMod n), F.card ≤ 6 * r + 2 →
      ∃ w : Fin 3 → ZMod n, w 0 + w 1 + w 2 = s ∧
        (∀ p, w p ∈ canonicalConnections a ∨ -w p ∈ canonicalConnections a) ∧
        (∀ p, w p ∉ F))
    (hcharacter : ∀ K : Int,
      (∑ s ∈ canonicalConnections a, characterDeficit n (K * (s.val : Int))) ≤ (r : Int) →
      ∃ i, 0 < characterDeficit n (K * ((a i : ZMod n).val : Int))) :
    ∃ (V : Type u) (G : SimpleGraph V), Erdos944.SimpleGraph.IsErdos944 G 4 r := by
  have hrobust : ∀ s ∈ canonicalConnections a, HasSignedWords (canonicalConnections a) r s :=
    fun s hs => hasSignedWords_of_avoidance (canonicalConnections a) r s (hwords s hs)
  obtain ⟨G, hG⟩ := erdos944_four_of_short_compatible hrt hn hq htn a ha hrobust hcharacter
  exact erdos944_universe_lift G (by omega : 0 < 3) hG

theorem exists_fin_value_outside {A : Type*} [DecidableEq A] {M : Nat}
    (f : Fin (M + 1) → A) (hf : Function.Injective f) (F : Finset A) (hF : F.card ≤ M) :
    ∃ i, f i ∉ F := by
  classical
  by_contra h
  have hsub : Finset.univ.image f ⊆ F := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    by_contra hi
    exact h ⟨i, hi⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin] at hc
  omega

theorem exists_progression_point_avoiding {L : Nat} (hL : 0 < L) (ρ A M : Nat)
    (F : Finset Nat) (hF : F.card ≤ M) :
    ∃ s : Nat, A < s ∧ s < A + (M + 2) * L ∧ s % L = ρ % L ∧ s ∉ F := by
  let b := ρ % L + L * (A / L + 1)
  let f : Fin (M + 1) → Nat := fun i => b + i.val * L
  have hf : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    dsimp [f] at hij
    nlinarith
  obtain ⟨i, hi⟩ := exists_fin_value_outside f hf F hF
  have hA := Nat.mod_add_div A L
  have hAm := Nat.mod_lt A hL
  have hρ := Nat.mod_lt ρ hL
  have hii := i.isLt
  have himul := Nat.mul_le_mul_right L (show i.val ≤ M by omega)
  refine ⟨f i, ?_, ?_, ?_, hi⟩
  · dsimp [f, b]
    nlinarith only [hA, hAm, Nat.zero_le (ρ % L), Nat.zero_le (i.val * L)]
  · dsimp [f, b]
    nlinarith only [hA, hρ, himul, Nat.zero_le (A % L)]
  · simp [f, b, Nat.add_mod]

theorem split_three_residue_coordinates {a M : Nat} (ha : 100 < a)
    (hlo : a < M) (hhi : M < 2 * a) (hM : M % 3 = 0) :
    ∃ E T : Nat, E % 15 = 2 ∧ 0 < E ∧ E < a ∧ 0 < T ∧ T < a ∧ T % 3 = 2 ∧
      E + E + T = M := by
  let E := 2 + 15 * ((M / 3 - 2) / 15)
  have hQ := Nat.mod_add_div M 3
  rw [hM, Nat.zero_add] at hQ
  have hdiv := Nat.mod_add_div (M / 3 - 2) 15
  have hmod := Nat.mod_lt (M / 3 - 2) (by decide : 0 < 15)
  refine ⟨E, M - 2 * E, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> dsimp [E] <;> omega

theorem fifteen_le_parameter_period {q N : Nat} (p : ParameterFamily q N) : 15 ≤ p.period :=
  Nat.le_mul_of_pos_right _ (Finset.prod_pos (fun i _ => crtFactor_pos q (p.kappa i)))

theorem cyclic_data_twice_period_lt_order {r : Nat} (p : CyclicIntegerData r) :
    2 * p.family.period < p.n := by
  have hp := fifteen_le_parameter_period p.family
  have hP : 2 * p.family.period ≤ p.family.period ^ 2 := by nlinarith
  have hC : 0 < 1000 * (r + 1) * (3 * p.t + 1) :=
    Nat.mul_pos (Nat.mul_pos (by decide) (by omega)) (by omega)
  exact lt_of_le_of_lt (hP.trans (Nat.le_mul_of_pos_left _ hC)) p.large_order

theorem cyclic_data_order_gt_two {r : Nat} (p : CyclicIntegerData r) : 2 < p.n := by
  have h := cyclic_data_twice_period_lt_order p
  have hp := fifteen_le_parameter_period p.family
  omega

theorem cyclic_data_orientation_half {r : Nat} (p : CyclicIntegerData r)
    (i : Fin (3 * p.t + 1)) : 2 * p.family.orientation i < p.n :=
  lt_of_le_of_lt (Nat.mul_le_mul_left 2
    (Nat.le_of_dvd (parameter_period_pos p.family) (orientation_dvd_period p.family i)))
    (cyclic_data_twice_period_lt_order p)

theorem cyclic_data_unitDirection_of_fin {r : Nat} (p : CyclicIntegerData r)
    (i : Fin (3 * p.t + 1)) :
    p.unitDirection (i.val : ZMod (3 * p.t + 1)) =
      ZMod.unitOfCoprime (p.family.orientation i) (cyclic_data_orientation_coprime p i) := by
  unfold CyclicIntegerData.unitDirection
  have he : (⟨(i.val : ZMod (3 * p.t + 1)).val, ZMod.val_lt _⟩ : Fin (3 * p.t + 1)) = i := by
    apply Fin.ext
    change (i.val : ZMod (3 * p.t + 1)).val = i.val
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt i.isLt]
  simp only [he]

theorem cyclic_data_generic_signed_mem {r : Nat} (p : CyclicIntegerData r) [NeZero p.n]
    {s : Nat} (hs : 0 < s) (hsn : s < p.n) (hinv : 2 * s ≠ p.n)
    (hgen : p.family.GenericResidue s) :
    (s : ZMod p.n) ∈ canonicalConnections p.unitDirection ∨
      -(s : ZMod p.n) ∈ canonicalConnections p.unitDirection := by
  have hval : (s : ZMod p.n).val = s := by rw [ZMod.val_natCast, Nat.mod_eq_of_lt hsn]
  have hzero : (s : ZMod p.n) ≠ 0 := by
    intro he
    have h := congrArg ZMod.val he
    rw [hval, ZMod.val_zero] at h
    omega
  let : NeZero (s : ZMod p.n) := ⟨hzero⟩
  apply canonicalConnections_rep p.order_three (by have h := cyclic_data_order_gt_two p; omega)
    p.unitDirection hzero
  · intro he
    have hv := congrArg ZMod.val he
    rw [ZMod.val_neg_of_ne_zero, hval] at hv
    omega
  · intro i
    exact Or.inr (Or.inr (cyclic_data_generic_unit_coordinates p hsn hgen i))

theorem zmod_val_neg_one_of_pos {n : Nat} (hn : 0 < n) : (-1 : ZMod n).val = n - 1 := by
  cases n with
  | zero => omega
  | succ n => simpa only [Nat.add_sub_cancel] using ZMod.val_neg_one n

theorem normalized_val_one_iff {n : Nat} [NeZero n] (hn : 1 < n)
    (a : (ZMod n)ˣ) (s : ZMod n) : ((↑a⁻¹ : ZMod n) * s).val = 1 ↔ s = (a : ZMod n) := by
  constructor
  · intro h
    have he : (↑a⁻¹ : ZMod n) * s = 1 := by
      apply ZMod.val_injective n
      rw [h, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt hn]
    calc
      s = (a : ZMod n) * ((↑a⁻¹ : ZMod n) * s) := by rw [← mul_assoc, Units.mul_inv, one_mul]
      _ = (a : ZMod n) := by rw [he, mul_one]
  · intro h
    rw [h, Units.inv_mul, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt hn]

theorem normalized_val_neg_one_iff {n : Nat} [NeZero n] (hn : 1 < n)
    (a : (ZMod n)ˣ) (s : ZMod n) :
    ((↑a⁻¹ : ZMod n) * s).val = n - 1 ↔ s = -(a : ZMod n) := by
  constructor
  · intro h
    have he : (↑a⁻¹ : ZMod n) * s = -1 := by
      apply ZMod.val_injective n
      rw [h, zmod_val_neg_one_of_pos (by omega : 0 < n)]
    calc
      s = (a : ZMod n) * ((↑a⁻¹ : ZMod n) * s) := by rw [← mul_assoc, Units.mul_inv, one_mul]
      _ = -(a : ZMod n) := by rw [he, mul_neg_one]
  · intro h
    rw [h, mul_neg, Units.inv_mul, zmod_val_neg_one_of_pos (by omega : 0 < n)]

theorem cyclic_data_canonical_ne_neg_unit {r : Nat} (p : CyclicIntegerData r) [NeZero p.n]
    {s : ZMod p.n} (hs : s ∈ canonicalConnections p.unitDirection) (i : ZMod (3 * p.t + 1)) :
    s ≠ -(p.unitDirection i : ZMod p.n) := by
  have hS := ((mem_canonicalConnections p.unitDirection s).mp hs).2.1
  have hu : 2 * (p.unitDirection i : ZMod p.n).val < p.n := by
    rw [cyclic_data_unitDirection_val]
    exact cyclic_data_orientation_half p _
  let : NeZero (p.unitDirection i : ZMod p.n) :=
    ⟨unit_ne_zero_of_two_lt (cyclic_data_order_gt_two p) (p.unitDirection i)⟩
  intro he
  rw [he, ZMod.val_neg_of_ne_zero] at hS
  have hv := ZMod.val_lt (p.unitDirection i : ZMod p.n)
  omega

theorem cyclic_data_canonical_generic_or_unit {r : Nat} (p : CyclicIntegerData r) [NeZero p.n]
    {s : ZMod p.n} (hs : s ∈ canonicalConnections p.unitDirection) :
    p.family.GenericResidue s.val ∨ ∃ i, s = (p.unitDirection i : ZMod p.n) := by
  by_cases hdir : ∃ i, s = (p.unitDirection i : ZMod p.n)
  · exact Or.inr hdir
  have hn : 1 < p.n := by have h := cyclic_data_order_gt_two p; omega
  have hall : ∀ i, ((↑(p.unitDirection i)⁻¹ : ZMod p.n) * s).val % 3 = 2 := by
    intro i
    rcases canonicalConnections_normal p.unitDirection i hs with h1 | hneg | h3
    · exact False.elim (hdir ⟨i, (normalized_val_one_iff hn (p.unitDirection i) s).mp h1⟩)
    · exact False.elim (cyclic_data_canonical_ne_neg_unit p hs i
        ((normalized_val_neg_one_iff hn (p.unitDirection i) s).mp hneg))
    · exact h3
  have hallFin : ∀ i : Fin (3 * p.t + 1),
      (((p.family.orientation i : Nat) : ZMod p.n)⁻¹ * s).val % 3 = 2 := by
    intro i
    have h := hall (i.val : ZMod (3 * p.t + 1))
    rw [cyclic_data_unitDirection_of_fin] at h
    exact h
  have hs3 : s.val % 3 = 2 := by
    have h := hallFin 0
    have hz : p.family.orientation (0 : Fin (3 * p.t + 1)) = 1 := by
      simp [ParameterFamily.orientation]
    rwa [hz, Nat.cast_one, ZMod.inv_one, one_mul] at h
  refine Or.inl ⟨hs3, fun i => ?_⟩
  have he := normalized_coordinate_mul (cyclic_data_order_pos p) (orientation_pos p.family i.succ)
    (ZMod.val_lt s) (p.inverse_congruence i)
  rw [ZMod.natCast_zmod_val] at he
  have hm := congrArg (fun x : Nat => x % 3) he
  rw [Nat.mul_mod (p.family.orientation i.succ) _ 3, orientation_mod_three p.family i,
    hallFin i.succ, Nat.add_mod s.val _ 3, hs3,
    Nat.mul_mod (p.family.kappa i * s.val % p.family.orientation i.succ) p.n 3, p.order_three] at hm
  omega


theorem erdos944_four_of_integer_data {r : Nat} (p : CyclicIntegerData r) [NeZero p.n]
    (hwords : ∀ s ∈ canonicalConnections p.unitDirection, ∀ F : Finset (ZMod p.n), F.card ≤ 6 * r + 2 →
      ∃ w : Fin 3 → ZMod p.n, w 0 + w 1 + w 2 = s ∧
        (∀ j, w j ∈ canonicalConnections p.unitDirection ∨ -w j ∈ canonicalConnections p.unitDirection) ∧
        (∀ j, w j ∉ F))
    (hcharacter : ∀ K : Int,
      (∑ s ∈ canonicalConnections p.unitDirection, characterDeficit p.n (K * (s.val : Int))) ≤ (r : Int) →
      ∃ i, 0 < characterDeficit p.n (K * ((p.unitDirection i : ZMod p.n).val : Int))) :
    ∃ (V : Type u) (G : SimpleGraph V), Erdos944.SimpleGraph.IsErdos944 G 4 r :=
  erdos944_four_from_arithmetic_conditions p.gap_lower p.order_three p.gap_divides
    (cyclic_data_gap_lt_order p) p.unitDirection (cyclic_data_shortCompatible p) hwords hcharacter

theorem cyclic_data_unitDirection_zero {r : Nat} (p : CyclicIntegerData r) :
    p.unitDirection 0 = 1 := by
  have h := cyclic_data_unitDirection_of_fin p 0
  simp only [Fin.val_zero, Nat.cast_zero] at h
  rw [h]
  apply Units.ext
  change (p.family.orientation (0 : Fin (3 * p.t + 1)) : ZMod p.n) = 1
  simp [ParameterFamily.orientation]

theorem cyclic_data_canonical_val_one_or_two {r : Nat} (p : CyclicIntegerData r) [NeZero p.n]
    {s : ZMod p.n} (hs : s ∈ canonicalConnections p.unitDirection) :
    s.val = 1 ∨ s.val % 3 = 2 := by
  have h := canonicalConnections_normal p.unitDirection 0 hs
  simp only [cyclic_data_unitDirection_zero, inv_one, Units.val_one, one_mul] at h
  rcases h with h₁ | hneg | h₃
  · exact Or.inl h₁
  · have hhalf := ((mem_canonicalConnections p.unitDirection s).mp hs).2.1
    have hn := cyclic_data_order_gt_two p
    omega
  · exact Or.inr h₃

theorem cyclic_data_canonical_residual {r : Nat} (p : CyclicIntegerData r) [NeZero p.n]
    {s : ZMod p.n} (hs : s ∈ canonicalConnections p.unitDirection) (hs₃ : s.val % 3 = 2)
    (i : Fin (3 * p.t)) :
    p.family.kappa i * s.val % p.family.orientation i.succ = 0 ∨
      (p.family.kappa i * s.val % p.family.orientation i.succ) % 3 = 2 := by
  have hn : 1 < p.n := by have h := cyclic_data_order_gt_two p; omega
  rcases canonicalConnections_normal p.unitDirection (i.succ.val : ZMod (3 * p.t + 1)) hs
    with h₁ | hneg | h₃
  · have heq := (normalized_val_one_iff hn _ s).mp h₁
    have hv : s.val = p.family.orientation i.succ := by
      rw [heq, cyclic_data_unitDirection_of_fin]
      change (p.family.orientation i.succ : ZMod p.n).val = _
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (cyclic_data_orientation_lt_order p i.succ)]
    exact Or.inl (by rw [hv]; simp)
  · exact False.elim (cyclic_data_canonical_ne_neg_unit p hs _
      ((normalized_val_neg_one_iff hn _ s).mp hneg))
  · rw [cyclic_data_unitDirection_of_fin] at h₃
    have hR : (((p.family.orientation i.succ : Nat) : ZMod p.n)⁻¹ * s).val % 3 = 2 := h₃
    have he := normalized_coordinate_mul (cyclic_data_order_pos p) (orientation_pos p.family i.succ)
      (ZMod.val_lt s) (p.inverse_congruence i)
    rw [ZMod.natCast_zmod_val] at he
    have hm := congrArg (fun x : Nat => x % 3) he
    rw [Nat.mul_mod (p.family.orientation i.succ) _ 3, orientation_mod_three p.family i,
      hR, Nat.add_mod s.val _ 3, hs₃,
      Nat.mul_mod (p.family.kappa i * s.val % p.family.orientation i.succ) p.n 3, p.order_three] at hm
    exact Or.inr (by omega)

theorem exists_three_progression_avoiding {n L W B : Nat} (hL : 0 < L)
    (hn : 24 * (2 * B + 2) * L ≤ n) (hWlo : n < W) (hWhi : W ≤ 2 * n + 1)
    (hW3 : W % 3 = 0) (ρ : Nat) (F : Finset Nat) (hF : F.card ≤ B) :
    ∃ s₁ s₂ s₃ : Nat, s₁ + s₂ + s₃ = W ∧
      0 < s₁ ∧ s₁ < n ∧ 0 < s₂ ∧ s₂ < n ∧ 0 < s₃ ∧ s₃ < n ∧
      s₁ % L = ρ % L ∧ s₂ % L = ρ % L ∧ s₁ ∉ F ∧ s₂ ∉ F ∧ s₃ ∉ F := by
  let C := W / 3
  let b := n / 24
  let A := C - b
  have hW : 3 * C = W := by dsimp [C]; omega
  have hb : (2 * B + 2) * L ≤ b := by
    dsimp [b]
    apply (Nat.le_div_iff_mul_le (by decide : 0 < 24)).2
    nlinarith only [hn]
  have hbn : 24 * b ≤ n := by dsimp [b]; omega
  have hn48 : 48 ≤ n := by nlinarith only [hn, hL, Nat.zero_le (B * L)]
  have hbC : b ≤ C := by omega
  have hAb : A + b = C := Nat.sub_add_cancel hbC
  have hCn : C + 2 * b < n := by omega
  obtain ⟨s₁, h₁A, h₁hi, h₁mod, h₁F⟩ := exists_progression_point_avoiding hL ρ A (2 * B) F
    (by omega)
  have h₁C : s₁ < C := by omega
  let F₂ := F ∪ F.image (fun x => W - s₁ - x)
  have hF₂ : F₂.card ≤ 2 * B := by
    have hc := Finset.card_union_le F (F.image (fun x => W - s₁ - x))
    have hi := Finset.card_image_le (s := F) (f := fun x => W - s₁ - x)
    dsimp [F₂]
    omega
  obtain ⟨s₂, h₂A, h₂hi, h₂mod, h₂F⟩ := exists_progression_point_avoiding hL ρ A (2 * B) F₂ hF₂
  have h₂C : s₂ < C := by omega
  let s₃ := W - s₁ - s₂
  have hsum : s₁ + s₂ + s₃ = W := by dsimp [s₃]; omega
  have h₃pos : 0 < s₃ := by omega
  have h₃hi : s₃ < n := by omega
  have h₂not : s₂ ∉ F := fun h => h₂F (Finset.mem_union_left _ h)
  have h₃not : s₃ ∉ F := by
    intro h
    apply h₂F
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨s₃, h, by omega⟩
  exact ⟨s₁, s₂, s₃, hsum, by omega, by omega, by omega, by omega,
    h₃pos, h₃hi, h₁mod, h₂mod, h₁F, h₂not, h₃not⟩

theorem cyclic_data_word_window_bound {r : Nat} (p : CyclicIntegerData r) :
    24 * (2 * (6 * r + 3) + 2) * p.family.period ≤ p.n := by
  have hL := parameter_period_pos p.family
  have hq : 0 < 3 * p.t + 1 := by omega
  have hcoeff : 24 * (2 * (6 * r + 3) + 2) ≤ 1000 * (r + 1) := by omega
  have hsq : p.family.period ≤ p.family.period ^ 2 := by nlinarith
  have hbase : p.family.period ≤ (3 * p.t + 1) * p.family.period ^ 2 :=
    hsq.trans (Nat.le_mul_of_pos_left _ hq)
  exact (Nat.mul_le_mul hcoeff hbase).trans (Nat.le_of_lt (by
    simpa only [Nat.mul_assoc] using p.large_order))

theorem exists_split_word_coordinate {a κ n z : Nat} (ha : 100 < a)
    (hκ : 6 ≤ κ) (hκa : κ < a) (hκ₃ : κ % 3 = 0) (ha₃ : a % 3 = 2)
    (hinv : a ∣ κ * n + 1)
    (hres : z ≠ 1 → κ * z % a = 0 ∨ (κ * z % a) % 3 = 2) :
    ∃ E T : Nat, E % 15 = 2 ∧ 0 < E ∧ E < a ∧ 0 < T ∧ T < a ∧ T % 3 = 2 ∧
      Nat.ModEq a (E + E + T) (κ * (z + (if z = 1 then 2 else 1) * n)) := by
  let c := if z = 1 then 2 else 1
  let M := if z = 1 then a + κ - 2 else if κ * z % a = 0 then 2 * a - 1 else a + κ * z % a - 1
  have he_lt : κ * z % a < a := Nat.mod_lt _ (by omega)
  have hM : a < M ∧ M < 2 * a ∧ M % 3 = 0 := by
    by_cases hz : z = 1
    · simp only [M, if_pos hz]
      omega
    · rcases hres hz with he | he
      · simp only [M, if_neg hz, if_pos he]
        omega
      · have he0 : κ * z % a ≠ 0 := by omega
        simp only [M, if_neg hz, if_neg he0]
        omega
  have hMc : Nat.ModEq a (M + c) (κ * z) := by
    by_cases hz : z = 1
    · have hsum : M + c = a + κ := by simp only [M, c, if_pos hz]; omega
      change (M + c) % a = κ * z % a
      rw [hsum, hz, mul_one]
      simp
    · by_cases he : κ * z % a = 0
      · have hsum : M + c = 2 * a := by simp only [M, c, if_neg hz, if_pos he]; omega
        change (M + c) % a = κ * z % a
        rw [hsum, he]
        simp
      · have hsum : M + c = a + κ * z % a := by
          simp only [M, c, if_neg hz, if_neg he]
          omega
        change (M + c) % a = κ * z % a
        rw [hsum]
        simp
  have hi : Nat.ModEq a (κ * n + 1) 0 := by
    exact (Nat.mod_eq_zero_of_dvd hinv).trans (Nat.zero_mod a).symm
  have hkc : Nat.ModEq a (κ * (z + c * n) + c) (κ * z) := by
    calc
      κ * (z + c * n) + c = κ * z + c * (κ * n + 1) := by ring
      _ ≡ κ * z + c * 0 [MOD a] := (hi.mul_left c).add_left (κ * z)
      _ = κ * z := by simp
  have hmod : Nat.ModEq a M (κ * (z + c * n)) :=
    Nat.ModEq.add_right_cancel' c (hMc.trans hkc.symm)
  obtain ⟨E, T, hE15, hEpos, hEa, hTpos, hTa, hT3, hsum⟩ :=
    split_three_residue_coordinates ha hM.1 hM.2.1 hM.2.2
  exact ⟨E, T, hE15, hEpos, hEa, hTpos, hTa, hT3, by rw [hsum]; exact hmod⟩

theorem cyclic_data_generic_word {r : Nat} (p : CyclicIntegerData r) (z : Nat)
    (hzpos : 0 < z) (hzhalf : 2 * z < p.n) (hz₃ : z = 1 ∨ z % 3 = 2)
    (hres : z ≠ 1 → ∀ i, p.family.kappa i * z % p.family.orientation i.succ = 0 ∨
      (p.family.kappa i * z % p.family.orientation i.succ) % 3 = 2)
    (F : Finset Nat) (hF : F.card ≤ 6 * r + 3) :
    ∃ s₁ s₂ s₃ : Nat, s₁ + s₂ + s₃ = z + (if z = 1 then 2 else 1) * p.n ∧
      0 < s₁ ∧ s₁ < p.n ∧ 0 < s₂ ∧ s₂ < p.n ∧ 0 < s₃ ∧ s₃ < p.n ∧
      p.family.GenericResidue s₁ ∧ p.family.GenericResidue s₂ ∧ p.family.GenericResidue s₃ ∧
      s₁ ∉ F ∧ s₂ ∉ F ∧ s₃ ∉ F := by
  classical
  let W := z + (if z = 1 then 2 else 1) * p.n
  have hq : 0 < 3 * p.t + 1 := by omega
  have hWlo : p.n < W := by dsimp [W]; split_ifs <;> omega
  have hWhi : W ≤ 2 * p.n + 1 := by dsimp [W]; split_ifs <;> omega
  have hW₃ : W % 3 = 0 := by
    have hn₃ := p.order_three
    dsimp [W]
    split_ifs <;> omega
  have hsplit : ∀ i : Fin (3 * p.t), ∃ E T : Nat,
      E % 15 = 2 ∧ 0 < E ∧ E < p.family.orientation i.succ ∧
      0 < T ∧ T < p.family.orientation i.succ ∧ T % 3 = 2 ∧
      Nat.ModEq (p.family.orientation i.succ) (E + E + T) (p.family.kappa i * W) := by
    intro i
    have hshort : 40 * (3 * p.t + 1) * p.family.kappa i < p.family.orientation i.succ :=
      kappa_short_bound hq (p.family.large i)
    have hκa : p.family.kappa i < p.family.orientation i.succ :=
      lt_of_le_of_lt (Nat.le_mul_of_pos_left _ (by omega : 0 < 40 * (3 * p.t + 1))) hshort
    exact exists_split_word_coordinate (orientation_gt_hundred hq p.family i)
      (p.family.large i) hκa (p.family.mod_three i) (orientation_mod_three p.family i)
      (p.inverse_congruence i) (fun h => hres h i)
  choose E T hE15 _hEpos hEa _hTpos hTa hT₃ hmod using hsplit
  obtain ⟨ρ, _, hρgen, _, hρcoords⟩ := exists_generic_with_coordinates hq p.family E 2 hEa
    (fun i => by have h := hE15 i; omega) (fun i => by have h := hE15 i; omega) 0
  obtain ⟨s₁, s₂, s₃, hsum, h₁pos, h₁n, h₂pos, h₂n, h₃pos, h₃n,
      h₁mod, h₂mod, h₁F, h₂F, h₃F⟩ := exists_three_progression_avoiding
    (parameter_period_pos p.family) (cyclic_data_word_window_bound p) hWlo hWhi hW₃ ρ F hF
  have h₁gen : p.family.GenericResidue s₁ :=
    (genericResidue_modEq p.family h₁mod).mpr hρgen
  have h₂gen : p.family.GenericResidue s₂ :=
    (genericResidue_modEq p.family h₂mod).mpr hρgen
  have h₁coords : ∀ i, p.family.kappa i * s₁ % p.family.orientation i.succ = E i := by
    intro i
    have h : Nat.ModEq p.family.period s₁ ρ := h₁mod
    exact Eq.trans ((h.of_dvd (orientation_dvd_period p.family i.succ)).mul_left _) (hρcoords i)
  have h₂coords : ∀ i, p.family.kappa i * s₂ % p.family.orientation i.succ = E i := by
    intro i
    have h : Nat.ModEq p.family.period s₂ ρ := h₂mod
    exact Eq.trans ((h.of_dvd (orientation_dvd_period p.family i.succ)).mul_left _) (hρcoords i)
  have h₃gen : p.family.GenericResidue s₃ := by
    refine ⟨?_, fun i => ?_⟩
    · have h₁ := h₁gen.1
      have h₂ := h₂gen.1
      omega
    · have h₁ : Nat.ModEq (p.family.orientation i.succ) (p.family.kappa i * s₁) (E i) := by
        change _ % _ = _ % _
        rw [h₁coords i, Nat.mod_eq_of_lt (hEa i)]
      have h₂ : Nat.ModEq (p.family.orientation i.succ) (p.family.kappa i * s₂) (E i) := by
        change _ % _ = _ % _
        rw [h₂coords i, Nat.mod_eq_of_lt (hEa i)]
      have hall : Nat.ModEq (p.family.orientation i.succ)
          (p.family.kappa i * s₁ + p.family.kappa i * s₂ + p.family.kappa i * s₃)
          (E i + E i + T i) := by
        calc
          p.family.kappa i * s₁ + p.family.kappa i * s₂ + p.family.kappa i * s₃ =
              p.family.kappa i * (s₁ + s₂ + s₃) := by ring
          _ = p.family.kappa i * W := by rw [hsum]
          _ ≡ E i + E i + T i [MOD p.family.orientation i.succ] := (hmod i).symm
      have h₃ := (h₁.add h₂).add_left_cancel hall
      have heq := Eq.trans h₃ (Nat.mod_eq_of_lt (hTa i))
      rw [heq]
      exact hT₃ i
  exact ⟨s₁, s₂, s₃, hsum, h₁pos, h₁n, h₂pos, h₂n, h₃pos, h₃n,
    h₁gen, h₂gen, h₃gen, h₁F, h₂F, h₃F⟩

theorem cyclic_data_word_avoidance {r : Nat} (p : CyclicIntegerData r) [NeZero p.n]
    {s : ZMod p.n} (hs : s ∈ canonicalConnections p.unitDirection)
    (F : Finset (ZMod p.n)) (hF : F.card ≤ 6 * r + 2) :
    ∃ w : Fin 3 → ZMod p.n, w 0 + w 1 + w 2 = s ∧
      (∀ j, w j ∈ canonicalConnections p.unitDirection ∨
        -w j ∈ canonicalConnections p.unitDirection) ∧ (∀ j, w j ∉ F) := by
  classical
  let FNat := insert (p.n / 2) (F.image ZMod.val)
  have hFNat : FNat.card ≤ 6 * r + 3 := by
    have hi := Finset.card_image_le (s := F) (f := ZMod.val)
    have h := Finset.card_insert_le (p.n / 2) (F.image ZMod.val)
    dsimp [FNat]
    omega
  obtain ⟨hspos, hshalf, _⟩ := (mem_canonicalConnections p.unitDirection s).mp hs
  have hs₃ := cyclic_data_canonical_val_one_or_two p hs
  obtain ⟨s₁, s₂, s₃, hsum, h₁pos, h₁n, h₂pos, h₂n, h₃pos, h₃n,
      h₁gen, h₂gen, h₃gen, h₁F, h₂F, h₃F⟩ := cyclic_data_generic_word p s.val hspos hshalf hs₃
    (fun h i => cyclic_data_canonical_residual p hs (by omega) i) FNat hFNat
  have hmem : ∀ v : Nat, 0 < v → v < p.n → p.family.GenericResidue v → v ∉ FNat →
      (v : ZMod p.n) ∈ canonicalConnections p.unitDirection ∨
        -(v : ZMod p.n) ∈ canonicalConnections p.unitDirection := by
    intro v hvpos hvn hvgen hvF
    apply cyclic_data_generic_signed_mem p hvpos hvn _ hvgen
    intro he
    apply hvF
    simp only [FNat, Finset.mem_insert]
    exact Or.inl (by omega)
  have havoid : ∀ v : Nat, v < p.n → v ∉ FNat → (v : ZMod p.n) ∉ F := by
    intro v hvn hvF hv
    apply hvF
    simp only [FNat, Finset.mem_insert]
    right
    exact Finset.mem_image.mpr ⟨(v : ZMod p.n), hv, by
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt hvn]⟩
  refine ⟨![(s₁ : ZMod p.n), (s₂ : ZMod p.n), (s₃ : ZMod p.n)], ?_, ?_, ?_⟩
  · change (s₁ : ZMod p.n) + (s₂ : ZMod p.n) + (s₃ : ZMod p.n) = s
    have h := congrArg (fun x : Nat => (x : ZMod p.n)) hsum
    simpa only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, add_zero,
      ZMod.natCast_zmod_val] using h
  · intro j
    fin_cases j
    · exact hmem s₁ h₁pos h₁n h₁gen h₁F
    · exact hmem s₂ h₂pos h₂n h₂gen h₂F
    · exact hmem s₃ h₃pos h₃n h₃gen h₃F
  · intro j
    fin_cases j
    · exact havoid s₁ h₁n h₁F
    · exact havoid s₂ h₂n h₂F
    · exact havoid s₃ h₃n h₃F

theorem int_modEq_eq_in_short_interval {n A B x y : Int} (hwidth : B - A < n)
    (hx : A ≤ x ∧ x ≤ B) (hy : A ≤ y ∧ y ≤ B) (he : Int.ModEq n x y) : x = y := by
  have h : Int.ModEq n (x - A) (y - A) := he.sub (Int.ModEq.refl A)
  change (x - A) % n = (y - A) % n at h
  rw [Int.emod_eq_of_lt (by omega : 0 ≤ x - A) (by omega : x - A < n),
    Int.emod_eq_of_lt (by omega : 0 ≤ y - A) (by omega : y - A < n)] at h
  omega

theorem int_modular_steps_eq_in_short_arc {n A B x y x' y' : Int}
    (hwidth : 2 * (B - A) < n) (hx : A ≤ x ∧ x ≤ B) (hy : A ≤ y ∧ y ≤ B)
    (hx' : A ≤ x' ∧ x' ≤ B) (hy' : A ≤ y' ∧ y' ≤ B)
    (he : Int.ModEq n (y - x) (y' - x')) : y - x = y' - x' :=
  int_modEq_eq_in_short_interval (A := A - B) (B := B - A) (by omega)
    (by omega) (by omega) he

theorem integer_progression_affine_in_short_arc {n A B d : Int} {M : Nat} (hM : 0 < M)
    (hwidth : 2 * (B - A) < n) (f : Nat → Int)
    (hf : ∀ i, i ≤ M → A ≤ f i ∧ f i ≤ B)
    (hstep : ∀ i, i < M → Int.ModEq n (f (i + 1) - f i) d) :
    ∃ δ : Int, Int.ModEq n δ d ∧ (∀ i, i ≤ M → f i = f 0 + (i : Int) * δ) ∧
      -(B - A) ≤ (M : Int) * δ ∧ (M : Int) * δ ≤ B - A := by
  let δ := f 1 - f 0
  have hfirst : Int.ModEq n δ d := hstep 0 hM
  have hconst : ∀ i, i < M → f (i + 1) - f i = δ := by
    intro i hi
    exact int_modular_steps_eq_in_short_arc hwidth (hf i (by omega)) (hf (i + 1) (by omega))
      (hf 0 (by omega)) (hf 1 (by omega)) ((hstep i hi).trans hfirst.symm)
  have hval : ∀ i, i ≤ M → f i = f 0 + (i : Int) * δ := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ i ih =>
        intro hi
        have hp := ih (by omega)
        have hs := hconst i (by omega)
        calc
          f (i + 1) = f i + δ := by omega
          _ = f 0 + (i : Int) * δ + δ := by rw [hp]
          _ = f 0 + ((i + 1 : Nat) : Int) * δ := by rw [Nat.cast_add, Nat.cast_one]; ring
  have h0 := hf 0 (by omega)
  have hN := hf M le_rfl
  have hv := hval M le_rfl
  exact ⟨δ, hfirst, hval, by omega, by omega⟩

theorem affine_integer_box_width {I : Type*} [Fintype I] (m : I → Nat) (δ : I → Int)
    (c A B : Int)
    (hbox : ∀ v : I → Nat, (∀ i, v i ≤ m i) →
      A ≤ c + ∑ i, (v i : Int) * δ i ∧ c + ∑ i, (v i : Int) * δ i ≤ B) :
    ∑ i, (m i : Int) * |δ i| ≤ B - A := by
  classical
  let vhi : I → Nat := fun i => if 0 ≤ δ i then m i else 0
  let vlo : I → Nat := fun i => if 0 ≤ δ i then 0 else m i
  have hhi := hbox vhi (fun i => by dsimp [vhi]; split_ifs <;> omega)
  have hlo := hbox vlo (fun i => by dsimp [vlo]; split_ifs <;> omega)
  calc
    ∑ i, (m i : Int) * |δ i| =
        ∑ i, ((vhi i : Int) * δ i - (vlo i : Int) * δ i) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases h : 0 ≤ δ i
      · simp [vhi, vlo, h, abs_of_nonneg h]
      · simp [vhi, vlo, h, abs_of_neg (by omega : δ i < 0)]
    _ = (c + ∑ i, (vhi i : Int) * δ i) - (c + ∑ i, (vlo i : Int) * δ i) := by
      rw [Finset.sum_sub_distrib]
      ring
    _ ≤ B - A := sub_le_sub hhi.2 hlo.1

theorem crt_grid_weight_large {L d m : Nat} (hd : 2 < d) (hdL : d ∣ L)
    (hL : 0 < L) (hm : 3 * m + 1 = d) : L < 6 * (m * (L / d)) := by
  have he : d * (L / d) = L := Nat.mul_div_cancel' hdL
  have hquot : 0 < L / d := by nlinarith only [he, hL]
  nlinarith only [he, hquot, hd, hm]

theorem sparse_integer_coefficients_of_weighted_bound {I : Type*} [Fintype I]
    (L : Nat) (w : I → Nat) (z : I → Int) (hw : ∀ i, L < 6 * w i)
    (hbound : 3 * ∑ i, w i * (z i).natAbs ≤ L) :
    (∀ i, (z i).natAbs ≤ 1) ∧ (∀ i j, z i ≠ 0 → z j ≠ 0 → i = j) := by
  classical
  have hsingle : ∀ i, w i * (z i).natAbs ≤ ∑ j, w j * (z j).natAbs := by
    intro i
    exact Finset.single_le_sum (fun j _ => Nat.zero_le (w j * (z j).natAbs)) (Finset.mem_univ i)
  have habs : ∀ i, (z i).natAbs ≤ 1 := by
    intro i
    by_contra h
    have htwo := Nat.mul_le_mul_left (w i) (show 2 ≤ (z i).natAbs by omega)
    have hi := hsingle i
    have hw' := hw i
    omega
  refine ⟨habs, ?_⟩
  intro i j hi hj
  by_contra hij
  have hi' : 1 ≤ (z i).natAbs := Int.natAbs_pos.mpr hi
  have hj' : 1 ≤ (z j).natAbs := Int.natAbs_pos.mpr hj
  have hpair : w i * (z i).natAbs + w j * (z j).natAbs ≤ ∑ k, w k * (z k).natAbs := by
    have h := Finset.sum_le_sum_of_subset (f := fun k => w k * (z k).natAbs)
      (Finset.subset_univ ({i, j} : Finset I))
    simpa only [Finset.sum_pair hij] using h
  have hwi := Nat.mul_le_mul_left (w i) hi'
  have hwj := Nat.mul_le_mul_left (w j) hj'
  have hiw := hw i
  have hjw := hw j
  omega

theorem int_eq_zero_or_unit_of_natAbs_le_one {z : Int} (h : z.natAbs ≤ 1) :
    z = 0 ∨ z = 1 ∨ z = -1 := by
  cases z with
  | ofNat n =>
      change n ≤ 1 at h
      rcases (show n = 0 ∨ n = 1 by omega) with rfl | rfl <;> decide
  | negSucc n => change n + 1 ≤ 1 at h; omega

theorem erdos944_four_of_character_condition {r : Nat} (p : CyclicIntegerData r) [NeZero p.n]
    (hcharacter : ∀ K : Int,
      (∑ s ∈ canonicalConnections p.unitDirection, characterDeficit p.n (K * (s.val : Int))) ≤ (r : Int) →
      ∃ i, 0 < characterDeficit p.n (K * ((p.unitDirection i : ZMod p.n).val : Int))) :
    ∃ (V : Type u) (G : SimpleGraph V), Erdos944.SimpleGraph.IsErdos944 G 4 r :=
  erdos944_four_of_integer_data p
    (fun _ hs F hF => cyclic_data_word_avoidance p hs F hF) hcharacter

theorem characterDeficit_nonneg (n : Nat) (x : Int) : 0 ≤ characterDeficit n x :=
  le_max_left _ _

theorem characterDeficit_congr {n : Nat} {x y : Int} (h : Int.ModEq n x y) :
    characterDeficit n x = characterDeficit n y := by
  change x % n = y % n at h
  simp only [characterDeficit, h]

theorem characterDeficit_neg (n : Nat) (x : Int) : characterDeficit n (-x) = characterDeficit n x := by
  by_cases h : (n : Int) ∣ x
  · simp [characterDeficit, Int.neg_emod, h, Int.emod_eq_zero_of_dvd h]
  · simp [characterDeficit, Int.neg_emod, h, min_comm]

theorem characterDeficit_le_iff_interval {n : Nat} {x R : Int} (hR : 0 ≤ R) :
    characterDeficit n x ≤ R ↔ (n : Int) - R ≤ 3 * (x % n) ∧
      3 * (x % n) ≤ 2 * (n : Int) + R := by
  unfold characterDeficit
  rw [Int.min_def]
  split <;> rw [Int.max_def] <;> split <;> omega

theorem characterDeficit_zmod_neg {n : Nat} [NeZero n] (K : Int) (s : ZMod n) :
    characterDeficit n (K * ((-s).val : Int)) = characterDeficit n (K * (s.val : Int)) := by
  by_cases hs : s = 0
  · simp [hs]
  · let : NeZero s := ⟨hs⟩
    have he : Int.ModEq n (K * ((-s).val : Int)) (-(K * (s.val : Int))) := by
      rw [ZMod.val_neg_of_ne_zero, Int.natCast_sub (Nat.le_of_lt (ZMod.val_lt s))]
      have hbase : Int.ModEq n (n : Int) 0 := by simp [Int.ModEq]
      simpa only [zero_sub, mul_neg] using (hbase.sub (Int.ModEq.refl (s.val : Int))).mul_left K
    exact (characterDeficit_congr he).trans (characterDeficit_neg n _)

theorem characterDeficit_le_connection_sum {n : Nat} [NeZero n] {I : Type*}
    (a : I → (ZMod n)ˣ) (K : Int) {s : ZMod n} (hs : s ∈ canonicalConnections a) :
    characterDeficit n (K * (s.val : Int)) ≤
      ∑ z ∈ canonicalConnections a, characterDeficit n (K * (z.val : Int)) :=
  Finset.single_le_sum (fun z _ => characterDeficit_nonneg n (K * (z.val : Int))) hs

theorem cyclic_data_generic_deficit_le {r : Nat} (p : CyclicIntegerData r) [NeZero p.n]
    (K : Int) (hK : (∑ s ∈ canonicalConnections p.unitDirection,
      characterDeficit p.n (K * (s.val : Int))) ≤ (r : Int))
    {s : Nat} (hs : 0 < s) (hsn : s < p.n) (hinv : 2 * s ≠ p.n)
    (hgen : p.family.GenericResidue s) : characterDeficit p.n (K * (s : Int)) ≤ (r : Int) := by
  have hv : (s : ZMod p.n).val = s := by rw [ZMod.val_natCast, Nat.mod_eq_of_lt hsn]
  rcases cyclic_data_generic_signed_mem p hs hsn hinv hgen with h | h
  · have hb := (characterDeficit_le_connection_sum p.unitDirection K h).trans hK
    rwa [hv] at hb
  · have hb := (characterDeficit_le_connection_sum p.unitDirection K h).trans hK
    rwa [characterDeficit_zmod_neg, hv] at hb

theorem cyclic_data_generic_phase_bounds {r : Nat} (p : CyclicIntegerData r) [NeZero p.n]
    (K : Int) (hK : (∑ s ∈ canonicalConnections p.unitDirection,
      characterDeficit p.n (K * (s.val : Int))) ≤ (r : Int))
    {s : Nat} (hs : 0 < s) (hsn : s < p.n) (hinv : 2 * s ≠ p.n)
    (hgen : p.family.GenericResidue s) :
    (p.n : Int) - r ≤ 3 * ((K * (s : Int)) % p.n) ∧
      3 * ((K * (s : Int)) % p.n) ≤ 2 * (p.n : Int) + r :=
  (characterDeficit_le_iff_interval (by omega : (0 : Int) ≤ r)).mp
    (cyclic_data_generic_deficit_le p K hK hs hsn hinv hgen)

theorem full_residue_progression {n L ρ : Nat} (hL : 0 < L) (hρ : 0 < ρ) (hρL : ρ < L)
    (hn : 2 * L < n) :
    ∃ M : Nat, 0 < M ∧ (∀ i, i ≤ M → 0 < ρ + i * L ∧ ρ + i * L < n ∧
      (ρ + i * L) % L = ρ) ∧ n < M * L + 2 * L ∧ n ≤ ρ + M * L + L := by
  let M := (n - 1 - ρ) / L
  have he := Nat.mod_add_div (n - 1 - ρ) L
  have hr := Nat.mod_lt (n - 1 - ρ) hL
  have hsub : n - 1 - ρ + ρ + 1 = n := by omega
  have hlast : ρ + M * L < n := by
    dsimp [M]
    nlinarith only [he, hsub, Nat.zero_le ((n - 1 - ρ) % L)]
  have hnext : n ≤ ρ + M * L + L := by dsimp [M]; nlinarith only [he, hr, hsub]
  have hM : 0 < M := by
    by_contra h
    have hz : M = 0 := Nat.eq_zero_of_not_pos h
    rw [hz, zero_mul, add_zero] at hnext
    omega
  refine ⟨M, hM, ?_, by omega, hnext⟩
  intro i hi
  have hmul := Nat.mul_le_mul_right L hi
  refine ⟨by omega, by omega, ?_⟩
  simp [Nat.add_mod, Nat.mod_eq_of_lt hρL]

theorem middle_third_rounding {n L R f T E : Int} (hn : 0 < n) (hL : 0 < L)
    (hL₃ : L % 3 = 0) (herr : R * L + 3 * E < 3 * n)
    (hf : n - R ≤ 3 * f ∧ 3 * f ≤ 2 * n + R)
    (hrel : -E ≤ L * f - n * T ∧ L * f - n * T ≤ E) :
    L ≤ 3 * T ∧ 3 * T ≤ 2 * L := by
  have hlo := mul_le_mul_of_nonneg_right hf.1 hL.le
  have hhi := mul_le_mul_of_nonneg_right hf.2 hL.le
  have hTlo : L - 3 < 3 * T := by
    by_contra h
    have hm := mul_le_mul_of_nonneg_left (show 3 * T ≤ L - 3 by omega) hn.le
    nlinarith only [hm, hlo, hrel.2, herr]
  have hThi : 3 * T < 2 * L + 3 := by
    by_contra h
    have hm := mul_le_mul_of_nonneg_left (show 2 * L + 3 ≤ 3 * T by omega) hn.le
    nlinarith only [hm, hhi, hrel.1, herr]
  omega

theorem cyclic_data_phase_largeness {r : Nat} (p : CyclicIntegerData r) :
    6 * p.family.period + 4 * r < p.n := by
  have hw := cyclic_data_word_window_bound p
  have hL := parameter_period_pos p.family
  have hR : r ≤ r * p.family.period := Nat.le_mul_of_pos_right r hL
  nlinarith only [hw, hL, hR, Nat.zero_le (r * p.family.period)]

theorem cyclic_data_small_character_slope {r : Nat} (p : CyclicIntegerData r) [NeZero p.n]
    (K : Int) (hK : (∑ s ∈ canonicalConnections p.unitDirection,
      characterDeficit p.n (K * (s.val : Int))) ≤ (r : Int)) :
    ∃ P b : Int, K * p.family.period = P * p.n + b ∧ 2 * |b| < (p.family.period : Int) := by
  have hL := parameter_period_pos p.family
  have hlarge : 6 * (p.family.period : Int) + 4 * r < (p.n : Int) := by
    exact_mod_cast cyclic_data_phase_largeness p
  obtain ⟨ρ, hρL, hρgen, hρavoid⟩ := generic_residue_avoids_class
    (by omega : 0 < 3 * p.t + 1) p.family ((p.n / 2) % p.family.period)
  have hρ : 0 < ρ := by have h := hρgen.1; omega
  obtain ⟨M, hM, hs, hML, _⟩ := full_residue_progression hL hρ hρL (cyclic_data_twice_period_lt_order p)
  let f : Nat → Int := fun i => (K * ((ρ + i * p.family.period : Nat) : Int)) % p.n
  have hphase : ∀ i, i ≤ M → (p.n : Int) - r ≤ 3 * f i ∧
      3 * f i ≤ 2 * (p.n : Int) + r := by
    intro i hi
    obtain ⟨hpos, hlt, hmod⟩ := hs i hi
    have hgen : p.family.GenericResidue (ρ + i * p.family.period) := by
      apply (genericResidue_modEq p.family (show Nat.ModEq p.family.period
        (ρ + i * p.family.period) ρ from hmod.trans (Nat.mod_eq_of_lt hρL).symm)).mpr hρgen
    have hinv : 2 * (ρ + i * p.family.period) ≠ p.n := by
      intro h
      have he : ρ + i * p.family.period = p.n / 2 := by omega
      rw [he] at hmod
      exact hρavoid hmod.symm
    exact cyclic_data_generic_phase_bounds p K hK hpos hlt hinv hgen
  let A : Int := ((p.n : Int) - r + 2) / 3
  let B : Int := (2 * (p.n : Int) + r) / 3
  have hf : ∀ i, i ≤ M → A ≤ f i ∧ f i ≤ B := by
    intro i hi
    have h := hphase i hi
    dsimp [A, B]
    omega
  have hwidth : 2 * (B - A) < (p.n : Int) := by dsimp [A, B]; omega
  have hstep : ∀ i, i < M → Int.ModEq p.n (f (i + 1) - f i) (K * p.family.period) := by
    intro i _
    have h₁ : Int.ModEq p.n (f (i + 1)) (K * ((ρ + (i + 1) * p.family.period : Nat) : Int)) :=
      Int.mod_modEq _ _
    have h₀ : Int.ModEq p.n (f i) (K * ((ρ + i * p.family.period : Nat) : Int)) :=
      Int.mod_modEq _ _
    convert h₁.sub h₀ using 1
    push_cast
    ring
  obtain ⟨b, hbmod, hval, _, _⟩ := integer_progression_affine_in_short_arc hM hwidth f hf hstep
  have h0 := hphase 0 (by omega)
  have hlast := hphase M le_rfl
  have hv := hval M le_rfl
  have hb : 3 * (M : Int) * |b| ≤ (p.n : Int) + 2 * r := by
    by_cases h : 0 ≤ b
    · rw [abs_of_nonneg h]
      nlinarith only [h0.1, hlast.2, hv]
    · rw [abs_of_neg (by omega : b < 0)]
      nlinarith only [h0.2, hlast.1, hv]
  have hML' : (p.n : Int) < (M : Int) * p.family.period + 2 * p.family.period := by
    exact_mod_cast hML
  have hbsmall : 2 * |b| < (p.family.period : Int) := by
    by_contra h
    have hm := mul_le_mul_of_nonneg_left (show (p.family.period : Int) ≤ 2 * |b| by omega)
      (show (0 : Int) ≤ M by omega)
    nlinarith only [hm, hML', hb, hlarge]
  obtain ⟨P, hP⟩ := hbmod.dvd
  exact ⟨P, b, by nlinarith only [hP], hbsmall⟩

theorem cyclic_data_rounding_margin {r : Nat} (p : CyclicIntegerData r) :
    (2 * r + 3 * p.family.period) * p.family.period < p.n := by
  have hsq : p.family.period ≤ p.family.period ^ 2 := Nat.le_self_pow (by decide) _
  have hr := Nat.mul_le_mul_left r hsq
  have hsmall : (2 * r + 3 * p.family.period) * p.family.period ≤
      (2 * r + 3) * p.family.period ^ 2 := by nlinarith only [hr]
  have hc : 2 * r + 3 ≤ 1000 * (r + 1) * (3 * p.t + 1) :=
    (show 2 * r + 3 ≤ 1000 * (r + 1) by omega).trans
      (Nat.le_mul_of_pos_right _ (by omega : 0 < 3 * p.t + 1))
  exact lt_of_le_of_lt (hsmall.trans (Nat.mul_le_mul_right (p.family.period ^ 2) hc)) p.large_order

theorem cyclic_data_endpoint_phase {r : Nat} (p : CyclicIntegerData r) [NeZero p.n]
    (K P b : Int) (hK : (∑ s ∈ canonicalConnections p.unitDirection,
      characterDeficit p.n (K * (s.val : Int))) ≤ (r : Int))
    (he : K * p.family.period = P * p.n + b) (hb : 2 * |b| < (p.family.period : Int))
    {x : Nat} (hx : 0 < x) (hxn : x < p.n) (hinv : 2 * x ≠ p.n)
    (hgen : p.family.GenericResidue x) (a : Int)
    (hnear : -(p.family.period : Int) ≤ (x : Int) - a * p.n ∧
      (x : Int) - a * p.n ≤ p.family.period) :
    (p.family.period : Int) ≤ 3 * ((P * (x : Int) + a * b) % p.family.period) ∧
      3 * ((P * (x : Int) + a * b) % p.family.period) ≤ 2 * (p.family.period : Int) := by
  let L : Int := p.family.period
  let N : Int := p.n
  let T : Int := P * (x : Int) - L * ((K * (x : Int)) / N) + a * b
  have hL : 0 < L := by dsimp [L]; exact_mod_cast parameter_period_pos p.family
  have hN : 0 < N := by dsimp [N]; exact_mod_cast cyclic_data_order_pos p
  have hL₃ : L % 3 = 0 := by
    dsimp [L]
    exact_mod_cast Nat.mod_eq_zero_of_dvd (three_dvd_parameter_period p.family)
  have hmargin : ((2 * r : Int) + 3 * L) * L < N := by
    dsimp [L, N]
    exact_mod_cast cyclic_data_rounding_margin p
  have hbe : (r : Int) * L + 3 * (|b| * L) < 3 * N := by
    have hm := mul_lt_mul_of_pos_right hb hL
    change 2 * |b| * L < L * L at hm
    nlinarith only [hm, hmargin, hN]
  have hxhe := congrArg (fun z : Int => z * (x : Int)) he
  have hdiv := congrArg (fun z : Int => L * z) (Int.emod_add_mul_ediv (K * (x : Int)) N)
  have hidentity : L * ((K * (x : Int)) % N) - N * T = b * ((x : Int) - a * N) := by
    dsimp [T, L, N] at *
    nlinarith only [hxhe, hdiv]
  have habs : |L * ((K * (x : Int)) % N) - N * T| ≤ |b| * L := by
    rw [hidentity, abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_le.mpr hnear) (abs_nonneg b)
  have hT := middle_third_rounding hN hL hL₃ hbe
    (cyclic_data_generic_phase_bounds p K hK hx hxn hinv hgen) (abs_le.mp habs)
  have htmod : T % L = T := Int.emod_eq_of_lt (by omega) (by omega)
  have hemod : Int.ModEq L T (P * (x : Int) + a * b) := by
    have hm : Int.ModEq L (L * ((K * (x : Int)) / N)) 0 := by simp [Int.ModEq]
    simpa only [T, sub_zero] using
      ((Int.ModEq.refl (P * (x : Int))).sub hm).add_right (a * b)
  have ht : T = (P * (x : Int) + a * b) % L := htmod.symm.trans hemod
  rwa [ht] at hT

theorem cyclic_data_rounded_endpoints {r : Nat} (p : CyclicIntegerData r) [NeZero p.n]
    (K P b : Int) (hK : (∑ s ∈ canonicalConnections p.unitDirection,
      characterDeficit p.n (K * (s.val : Int))) ≤ (r : Int))
    (he : K * p.family.period = P * p.n + b) (hb : 2 * |b| < (p.family.period : Int))
    {ρ : Nat} (hρL : ρ < p.family.period) (hρgen : p.family.GenericResidue ρ) :
    ((p.family.period : Int) ≤ 3 * ((P * (ρ : Int)) % p.family.period) ∧
      3 * ((P * (ρ : Int)) % p.family.period) ≤ 2 * (p.family.period : Int)) ∧
    ((p.family.period : Int) ≤ 3 * ((P * (ρ : Int) + b) % p.family.period) ∧
      3 * ((P * (ρ : Int) + b) % p.family.period) ≤ 2 * (p.family.period : Int)) := by
  have hρ : 0 < ρ := by have h := hρgen.1; omega
  have hL := parameter_period_pos p.family
  have hn := cyclic_data_twice_period_lt_order p
  have hfirst := cyclic_data_endpoint_phase p K P b hK he hb hρ (by omega) (by omega) hρgen 0
    (by simp only [zero_mul, sub_zero]; constructor <;> omega)
  simp only [zero_mul, add_zero] at hfirst
  obtain ⟨M, _, hs, _, hlast⟩ := full_residue_progression hL hρ hρL hn
  obtain ⟨hx, hxn, hxmod⟩ := hs M le_rfl
  have hxgen : p.family.GenericResidue (ρ + M * p.family.period) :=
    (genericResidue_modEq p.family (show Nat.ModEq p.family.period
      (ρ + M * p.family.period) ρ from hxmod.trans (Nat.mod_eq_of_lt hρL).symm)).mpr hρgen
  have hnear : -(p.family.period : Int) ≤ ((ρ + M * p.family.period : Nat) : Int) - 1 * p.n ∧
      ((ρ + M * p.family.period : Nat) : Int) - 1 * p.n ≤ p.family.period := by
    have hlast' : (p.n : Int) ≤ ((ρ + M * p.family.period : Nat) : Int) + p.family.period := by
      exact_mod_cast hlast
    omega
  have hend := cyclic_data_endpoint_phase p K P b hK he hb hx hxn (by omega) hxgen 1 hnear
  simp only [one_mul] at hend
  have hxm : Int.ModEq p.family.period ((ρ + M * p.family.period : Nat) : Int) (ρ : Int) := by
    have hm : Int.ModEq p.family.period ((M : Int) * p.family.period) 0 := by simp [Int.ModEq]
    simpa only [Nat.cast_add, Nat.cast_mul, add_zero] using hm.add_left (ρ : Int)
  have hphase : (P * ((ρ + M * p.family.period : Nat) : Int) + b) % p.family.period =
      (P * (ρ : Int) + b) % p.family.period := (hxm.mul_left P).add_right b
  rw [hphase] at hend
  exact ⟨hfirst, hend⟩

theorem cyclic_data_rounded_character {r : Nat} (p : CyclicIntegerData r) [NeZero p.n]
    (K : Int) (hK : (∑ s ∈ canonicalConnections p.unitDirection,
      characterDeficit p.n (K * (s.val : Int))) ≤ (r : Int)) :
    ∃ P b : Int, K * p.family.period = P * p.n + b ∧ 2 * |b| < (p.family.period : Int) ∧
      ∀ ρ : Nat, ρ < p.family.period → p.family.GenericResidue ρ →
        ((p.family.period : Int) ≤ 3 * ((P * (ρ : Int)) % p.family.period) ∧
          3 * ((P * (ρ : Int)) % p.family.period) ≤ 2 * (p.family.period : Int)) ∧
        ((p.family.period : Int) ≤ 3 * ((P * (ρ : Int) + b) % p.family.period) ∧
          3 * ((P * (ρ : Int) + b) % p.family.period) ≤ 2 * (p.family.period : Int)) := by
  obtain ⟨P, b, he, hb⟩ := cyclic_data_small_character_slope p K hK
  exact ⟨P, b, he, hb, fun _ hρ hgen => cyclic_data_rounded_endpoints p K P b hK he hb hρ hgen⟩

def ParameterFamily.MiddleThirdCharacter {q N : Nat} (p : ParameterFamily q N) (P b : Int) : Prop :=
  ∀ ρ : Nat, ρ < p.period → p.GenericResidue ρ →
    ((p.period : Int) ≤ 3 * ((P * (ρ : Int)) % p.period) ∧
      3 * ((P * (ρ : Int)) % p.period) ≤ 2 * (p.period : Int)) ∧
    ((p.period : Int) ≤ 3 * ((P * (ρ : Int) + b) % p.period) ∧
      3 * ((P * (ρ : Int) + b) % p.period) ≤ 2 * (p.period : Int))

theorem int_modEq_eq_of_twice_abs_lt {n x y : Int} (hx : 2 * |x| < n) (hy : 2 * |y| < n)
    (he : Int.ModEq n x y) : x = y := by
  have hx0 := neg_abs_le x
  have hx1 := le_abs_self x
  have hy0 := neg_abs_le y
  have hy1 := le_abs_self y
  exact int_modEq_eq_in_short_interval (A := -((n - 1) / 2)) (B := (n - 1) / 2)
    (by omega) (by omega) (by omega) he

theorem middle_third_phase_shift {L X b : Int} (hL : 0 < L) (hb : 2 * |b| < L)
    (hx : L ≤ 3 * (X % L) ∧ 3 * (X % L) ≤ 2 * L)
    (hy : L ≤ 3 * ((X + b) % L) ∧ 3 * ((X + b) % L) ≤ 2 * L) :
    (X + b) % L = X % L + b := by
  have hdiff : 2 * |(X + b) % L - X % L| < L := by
    by_cases hd : 0 ≤ (X + b) % L - X % L
    · rw [abs_of_nonneg hd]
      omega
    · rw [abs_of_neg (by omega : (X + b) % L - X % L < 0)]
      omega
  have hmod : Int.ModEq L ((X + b) % L - X % L) b := by
    have h := (Int.mod_modEq (X + b) L).sub (Int.mod_modEq X L)
    simpa only [add_sub_cancel_left] using h
  have he := int_modEq_eq_of_twice_abs_lt hdiff hb hmod
  omega

theorem middleThirdCharacter_common_bounds {q N : Nat} (p : ParameterFamily q N)
    {P b : Int} (hb : 2 * |b| < (p.period : Int)) (h : p.MiddleThirdCharacter P b)
    {ρ : Nat} (hρ : ρ < p.period) (hgen : p.GenericResidue ρ) :
    (p.period : Int) - min 0 (3 * b) ≤ 3 * ((P * (ρ : Int)) % p.period) ∧
      3 * ((P * (ρ : Int)) % p.period) ≤ 2 * (p.period : Int) - max 0 (3 * b) := by
  obtain ⟨hx, hy⟩ := h ρ hρ hgen
  have hshift := middle_third_phase_shift (by exact_mod_cast parameter_period_pos p) hb hx hy
  rw [hshift] at hy
  rw [Int.min_def, Int.max_def]
  split <;> omega

theorem erdos944_four_of_periodic_rigidity {r : Nat} (p : CyclicIntegerData r) [NeZero p.n]
    (hrigidity : ∀ K P b : Int, K * p.family.period = P * p.n + b →
      2 * |b| < (p.family.period : Int) → p.family.MiddleThirdCharacter P b →
      ∃ i, 0 < characterDeficit p.n (K * ((p.unitDirection i : ZMod p.n).val : Int))) :
    ∃ (V : Type u) (G : SimpleGraph V), Erdos944.SimpleGraph.IsErdos944 G 4 r := by
  apply erdos944_four_of_character_condition p
  intro K hK
  obtain ⟨P, b, he, hb, hphases⟩ := cyclic_data_rounded_character p K hK
  exact hrigidity K P b he hb hphases

theorem integer_box_affine_of_constant_steps {I : Type*} [Fintype I] [DecidableEq I]
    (m : I → Nat) (f : (I → Nat) → Int) (δ : I → Int)
    (hstep : ∀ v : I → Nat, (∀ i, v i ≤ m i) → ∀ i, v i < m i →
      f (Function.update v i (v i + 1)) - f v = δ i) :
    ∀ v : I → Nat, (∀ i, v i ≤ m i) →
      f v = f (fun _ => 0) + ∑ i, (v i : Int) * δ i := by
  classical
  have hmain : ∀ n : Nat, ∀ v : I → Nat, (∑ i, v i) = n → (∀ i, v i ≤ m i) →
      f v = f (fun _ => 0) + ∑ i, (v i : Int) * δ i := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro v hvn hv
      by_cases hz : ∀ i, v i = 0
      · have he : v = fun _ => 0 := funext hz
        simp [he]
      · obtain ⟨i, hi⟩ := not_forall.mp hz
        have hipos : 0 < v i := Nat.pos_of_ne_zero hi
        let w : I → Nat := Function.update v i (v i - 1)
        have hwi : w i = v i - 1 := by simp [w]
        have hwle : ∀ j, w j ≤ v j := by
          intro j
          by_cases hj : j = i
          · subst j; simp [w]
          · simp [w, Function.update_of_ne hj]
        have hwm : ∀ j, w j ≤ m j := fun j => (hwle j).trans (hv j)
        have hsumlt : (∑ j, w j) < n := by
          rw [← hvn]
          apply Finset.sum_lt_sum (fun j _ => hwle j)
          exact ⟨i, Finset.mem_univ i, by omega⟩
        have hw := ih _ hsumlt w rfl hwm
        have hup : Function.update w i (w i + 1) = v := by
          ext j
          by_cases hj : j = i
          · subst j; simp [w, Nat.sub_add_cancel hipos]
          · simp [w, hj]
        have hs := hstep w hwm i (by have h := hv i; omega)
        rw [hup] at hs
        have hsum : (∑ j, (v j : Int) * δ j) =
            (∑ j, (w j : Int) * δ j) + δ i := by
          rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i),
            ← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
          have he : (∑ j ∈ Finset.univ.erase i, (v j : Int) * δ j) =
              ∑ j ∈ Finset.univ.erase i, (w j : Int) * δ j := by
            apply Finset.sum_congr rfl
            intro j hj
            simp [w, (Finset.mem_erase.mp hj).1]
          rw [he, hwi]
          have hc : (v i : Int) = ((v i - 1 : Nat) : Int) + 1 := by omega
          rw [hc]
          ring
        rw [hsum]
        omega
  intro v hv
  exact hmain _ v rfl hv

theorem integer_box_affine_in_short_arc {I : Type*} [Fintype I] [DecidableEq I]
    (m : I → Nat) (hm : ∀ i, 0 < m i) (f : (I → Nat) → Int)
    (n A B : Int) (hwidth : 2 * (B - A) < n)
    (hf : ∀ v : I → Nat, (∀ i, v i ≤ m i) → A ≤ f v ∧ f v ≤ B)
    (hstep : ∀ v : I → Nat, (∀ i, v i ≤ m i) → ∀ i, v i < m i →
      Int.ModEq n (f (Function.update v i (v i + 1)) - f v)
        (f (Function.update (fun _ => 0) i 1) - f (fun _ => 0))) :
    ∃ δ : I → Int,
      (∀ i, δ i = f (Function.update (fun _ => 0) i 1) - f (fun _ => 0)) ∧
      (∀ v : I → Nat, (∀ i, v i ≤ m i) →
        f v = f (fun _ => 0) + ∑ i, (v i : Int) * δ i) ∧
      ∑ i, (m i : Int) * |δ i| ≤ B - A := by
  classical
  let δ : I → Int := fun i => f (Function.update (fun _ => 0) i 1) - f (fun _ => 0)
  have hzero : ∀ i, (0 : Nat) ≤ m i := fun _ => Nat.zero_le _
  have hunit : ∀ i j, Function.update (fun _ : I => 0) i 1 j ≤ m j := by
    intro i j
    by_cases hj : j = i
    · subst j; simpa using Nat.succ_le_of_lt (hm i)
    · simp [hj]
  have hconst : ∀ v : I → Nat, (∀ i, v i ≤ m i) → ∀ i, v i < m i →
      f (Function.update v i (v i + 1)) - f v = δ i := by
    intro v hv i hi
    have hup : ∀ j, Function.update v i (v i + 1) j ≤ m j := by
      intro j
      by_cases hj : j = i
      · subst j; simpa using hi
      · simpa [hj] using hv j
    exact int_modular_steps_eq_in_short_arc hwidth (hf v hv) (hf _ hup)
      (hf _ hzero) (hf _ (hunit i)) (hstep v hv i hi)
  have ha := integer_box_affine_of_constant_steps m f δ hconst
  refine ⟨δ, fun _ => rfl, ha, ?_⟩
  apply affine_integer_box_width m δ (f (fun _ => 0)) A B
  intro v hv
  rw [← ha v hv]
  exact hf v hv

def ParameterFamily.IsGridMap {q N : Nat} (p : ParameterFamily q N) (h : Fin 5)
    (ρ : (Fin N → Nat) → Nat) : Prop :=
  ∀ y : Fin N → Nat, (∀ i, y i ≤ gridBound (crtFactor q (p.kappa i)) h) →
    ρ y < p.period ∧ p.GenericResidue (ρ y) ∧ (ρ y) % 5 = (2 + 3 * h.val) % 5 ∧
      ∀ i, p.kappa i * ρ y % p.orientation i.succ = 2 + 3 * h.val + 15 * y i

theorem exists_generic_grid_map {q N : Nat} (hq : 0 < q) (p : ParameterFamily q N)
    (h : Fin 5) : ∃ ρ : (Fin N → Nat) → Nat, p.IsGridMap h ρ := by
  classical
  choose ρ hρ using fun y : Fin N → Nat => exists_generic_grid_class hq p h
    (fun i => min (y i) (gridBound (crtFactor q (p.kappa i)) h)) (fun _ => min_le_right _ _)
  refine ⟨ρ, ?_⟩
  intro y hy
  have hmin : ∀ i, min (y i) (gridBound (crtFactor q (p.kappa i)) h) = y i :=
    fun i => min_eq_left (hy i)
  simpa only [hmin] using hρ y

theorem parameter_grid_parallelogram {q N : Nat} (hq : 0 < q) (p : ParameterFamily q N)
    {h : Fin 5} {ρ : (Fin N → Nat) → Nat} (hρ : p.IsGridMap h ρ)
    {v₁ v₂ v₃ v₄ : Fin N → Nat}
    (h₁ : ∀ i, v₁ i ≤ gridBound (crtFactor q (p.kappa i)) h)
    (h₂ : ∀ i, v₂ i ≤ gridBound (crtFactor q (p.kappa i)) h)
    (h₃ : ∀ i, v₃ i ≤ gridBound (crtFactor q (p.kappa i)) h)
    (h₄ : ∀ i, v₄ i ≤ gridBound (crtFactor q (p.kappa i)) h)
    (hadd : ∀ i, v₁ i + v₂ i = v₃ i + v₄ i) :
    Nat.ModEq p.period (ρ v₁ + ρ v₂) (ρ v₃ + ρ v₄) := by
  obtain ⟨_, hg₁, hb₁, hc₁⟩ := hρ v₁ h₁
  obtain ⟨_, hg₂, hb₂, hc₂⟩ := hρ v₂ h₂
  obtain ⟨_, hg₃, hb₃, hc₃⟩ := hρ v₃ h₃
  obtain ⟨_, hg₄, hb₄, hc₄⟩ := hρ v₄ h₄
  apply parameter_coordinates_determine_class hq p
  · change (ρ v₁ + ρ v₂) % 3 = (ρ v₃ + ρ v₄) % 3
    rw [Nat.add_mod (ρ v₁) (ρ v₂), Nat.add_mod (ρ v₃) (ρ v₄),
      hg₁.1, hg₂.1, hg₃.1, hg₄.1]
  · change (ρ v₁ + ρ v₂) % 5 = (ρ v₃ + ρ v₄) % 5
    rw [Nat.add_mod (ρ v₁) (ρ v₂), Nat.add_mod (ρ v₃) (ρ v₄), hb₁, hb₂, hb₃, hb₄]
  · intro i
    simp only [Nat.mul_add]
    rw [Nat.add_mod (p.kappa i * ρ v₁) (p.kappa i * ρ v₂),
      Nat.add_mod (p.kappa i * ρ v₃) (p.kappa i * ρ v₄), hc₁ i, hc₂ i, hc₃ i, hc₄ i]
    congr 1
    have he := hadd i
    omega

theorem parameter_grid_step_congr {q N : Nat} (hq : 0 < q) (p : ParameterFamily q N)
    {h : Fin 5} {ρ : (Fin N → Nat) → Nat} (hρ : p.IsGridMap h ρ)
    {v : Fin N → Nat} (hv : ∀ i, v i ≤ gridBound (crtFactor q (p.kappa i)) h)
    (i : Fin N) (hi : v i < gridBound (crtFactor q (p.kappa i)) h) :
    Nat.ModEq p.period
      (ρ (Function.update v i (v i + 1)) + ρ (fun _ => 0))
      (ρ v + ρ (Function.update (fun _ => 0) i 1)) := by
  classical
  apply parameter_grid_parallelogram hq p hρ
  · intro j
    by_cases hj : j = i
    · subst j; simpa using hi
    · simpa [hj] using hv j
  · exact fun _ => Nat.zero_le _
  · exact hv
  · intro j
    by_cases hj : j = i
    · subst j; simp; omega
    · simp [hj]
  · intro j
    by_cases hj : j = i
    · subst j; simp
    · simp [hj]

theorem int_residue_step_congr {n x y z w P : Int}
    (he : Int.ModEq n (y + z) (x + w)) :
    Int.ModEq n ((P * y) % n - (P * x) % n)
      ((P * w) % n - (P * z) % n) := by
  have hm := (he.mul_left P).sub (Int.ModEq.refl (P * x + P * z))
  have hs : Int.ModEq n (P * y - P * x) (P * w - P * z) := by
    convert hm using 1 <;> ring
  exact ((Int.mod_modEq _ _).sub (Int.mod_modEq _ _)).trans
    (hs.trans ((Int.mod_modEq _ _).sub (Int.mod_modEq _ _)).symm)

theorem parameter_grid_bounds_pos {q N : Nat} (hq : 0 < q) (p : ParameterFamily q N)
    (h : Fin 5) (i : Fin N) : 0 < gridBound (crtFactor q (p.kappa i)) h := by
  have hd := crtFactor_ge_kappa (κ := p.kappa i) hq (by have hi := p.large i; omega)
  have hlarge := p.large i
  have hd15 := crtFactor_mod_fifteen q (p.kappa i)
  unfold gridBound
  split_ifs <;> omega

theorem middleThirdCharacter_grid_affine {q N : Nat} (hq : 0 < q) (p : ParameterFamily q N)
    {P b : Int} (hc : p.MiddleThirdCharacter P b) (h : Fin 5)
    {ρ : (Fin N → Nat) → Nat} (hρ : p.IsGridMap h ρ) :
    ∃ δ : Fin N → Int,
      (∀ i, δ i = (P * (ρ (Function.update (fun _ => 0) i 1) : Int)) % p.period -
        (P * (ρ (fun _ => 0) : Int)) % p.period) ∧
      (∀ v : Fin N → Nat, (∀ i, v i ≤ gridBound (crtFactor q (p.kappa i)) h) →
        (P * (ρ v : Int)) % p.period = (P * (ρ (fun _ => 0) : Int)) % p.period +
          ∑ i, (v i : Int) * δ i) ∧
      3 * ∑ i, (gridBound (crtFactor q (p.kappa i)) h : Int) * |δ i| ≤ p.period := by
  classical
  let L : Int := p.period
  let A : Int := L / 3
  let B : Int := 2 * L / 3
  let f : (Fin N → Nat) → Int := fun v => (P * (ρ v : Int)) % L
  have hL : 0 < L := by dsimp [L]; exact_mod_cast parameter_period_pos p
  have hdiv : L % 3 = 0 := by
    exact Int.emod_eq_zero_of_dvd (by dsimp [L]; exact_mod_cast three_dvd_parameter_period p)
  have hA : 3 * A = L := by dsimp [A]; omega
  have hB : 3 * B = 2 * L := by dsimp [B]; omega
  have hf : ∀ v : Fin N → Nat,
      (∀ i, v i ≤ gridBound (crtFactor q (p.kappa i)) h) → A ≤ f v ∧ f v ≤ B := by
    intro v hv
    have hr := hρ v hv
    have he := (hc (ρ v) hr.1 hr.2.1).1
    change L ≤ 3 * f v ∧ 3 * f v ≤ 2 * L at he
    omega
  obtain ⟨δ, hδ, ha, hw⟩ := integer_box_affine_in_short_arc
    (fun i => gridBound (crtFactor q (p.kappa i)) h) (parameter_grid_bounds_pos hq p h)
    f L A B (by omega) hf (by
      intro v hv i hi
      apply int_residue_step_congr
      simpa only [Nat.cast_add] using
        (Int.natCast_modEq_iff.mpr (parameter_grid_step_congr hq p hρ hv i hi)))
  exact ⟨δ, hδ, ha, by change 3 * _ ≤ L; omega⟩

def ParameterFamily.complementFactor {q N : Nat} (p : ParameterFamily q N) (i : Fin N) : Nat :=
  ∏ j ∈ Finset.univ.erase i, crtFactor q (p.kappa j)

theorem parameter_complement_pos {q N : Nat} (p : ParameterFamily q N) (i : Fin N) :
    0 < p.complementFactor i :=
  Finset.prod_pos (fun j _ => crtFactor_pos q (p.kappa j))

theorem parameter_period_complement {q N : Nat} (p : ParameterFamily q N) (i : Fin N) :
    p.period = 15 * p.complementFactor i * crtFactor q (p.kappa i) := by
  unfold ParameterFamily.period ParameterFamily.complementFactor
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  ring

theorem parameter_complement_coprime {q N : Nat} (p : ParameterFamily q N) (i : Fin N) :
    (crtFactor q (p.kappa i)).Coprime (p.complementFactor i) :=
  Nat.Coprime.prod_right (fun _ hj => p.coprime (Finset.mem_erase.mp hj).1.symm)

theorem parameter_step_divisible {q N : Nat} (hq : 0 < q) (p : ParameterFamily q N)
    (i : Fin N) {s₀ s₁ : Nat} (h15 : Nat.ModEq 15 s₀ s₁)
    (hoff : ∀ j, j ≠ i →
      p.kappa j * s₀ % p.orientation j.succ = p.kappa j * s₁ % p.orientation j.succ) :
    ((15 * p.complementFactor i : Nat) : Int) ∣ ((s₁ : Int) - (s₀ : Int)) := by
  have hd : ∀ j ∈ Finset.univ.erase i, Nat.ModEq (crtFactor q (p.kappa j)) s₀ s₁ := by
    intro j hj
    have hκ := kappa_coprime_crtFactor (κ := p.kappa j) hq
      (by have h := p.large j; omega) (p.mod_aux j)
    have he : Nat.ModEq (5 * crtFactor q (p.kappa j)) (p.kappa j * s₀) (p.kappa j * s₁) :=
      hoff j (Finset.mem_erase.mp hj).1
    exact Nat.ModEq.cancel_left_of_coprime hκ.symm
      (he.of_dvd (dvd_mul_left (crtFactor q (p.kappa j)) 5))
  have hprod : Nat.ModEq (p.complementFactor i) s₀ s₁ :=
    modEq_finset_product (Finset.univ.erase i) (fun j => crtFactor q (p.kappa j)) p.coprime hd
  have hcop : (15 : Nat).Coprime (p.complementFactor i) :=
    Nat.Coprime.prod_right (fun j _ =>
      (coprime_of_remainder_one (crtFactor_mod_fifteen q (p.kappa j))).symm)
  exact (Int.natCast_modEq_iff.mpr ((Nat.modEq_and_modEq_iff_modEq_mul hcop).mp
    ⟨h15, hprod⟩)).dvd

theorem parameter_step_inverse {q N : Nat} (p : ParameterFamily q N) (i : Fin N)
    {η τ : Int} (hη : η = (15 * p.complementFactor i : Nat) * τ)
    (hstep : Int.ModEq (5 * crtFactor q (p.kappa i)) ((p.kappa i : Int) * η) 15) :
    Int.ModEq (crtFactor q (p.kappa i))
      ((p.kappa i : Int) * p.complementFactor i * τ) 1 := by
  let d := crtFactor q (p.kappa i)
  let Q := p.complementFactor i
  have hcancel : Int.ModEq (d : Int) (3 * ((p.kappa i : Int) * Q * τ)) 3 := by
    apply Int.ModEq.mul_left_cancel' (by norm_num : (5 : Int) ≠ 0)
    rw [hη] at hstep
    convert hstep using 1 <;> push_cast
    ring
  have hcop : (d : Int).gcd 3 = 1 := by
    have hd3 : d % 3 = 1 := by have h := crtFactor_mod_fifteen q (p.kappa i); dsimp [d]; omega
    have hc : d.Coprime 3 := coprime_of_remainder_one hd3
    exact_mod_cast hc
  change Int.ModEq (d : Int) (3 * ((p.kappa i : Int) * Q * τ)) (3 * 1) at hcancel
  have h := Int.ModEq.cancel_left_div_gcd
    (show (0 : Int) < d by exact_mod_cast crtFactor_pos q (p.kappa i)) hcancel
  simpa only [hcop, Nat.cast_one, Int.ediv_one] using h

theorem parameter_phase_difference_coefficient {q N : Nat} (hq : 0 < q)
    (p : ParameterFamily q N) (i : Fin N) {s₀ s₁ : Nat} (P : Int)
    (h15 : Nat.ModEq 15 s₀ s₁)
    (hoff : ∀ j, j ≠ i →
      p.kappa j * s₀ % p.orientation j.succ = p.kappa j * s₁ % p.orientation j.succ)
    (hstep : Int.ModEq (5 * crtFactor q (p.kappa i))
      ((p.kappa i : Int) * ((s₁ : Int) - s₀)) 15) :
    ∃ z : Int,
      (P * (s₁ : Int)) % p.period - (P * (s₀ : Int)) % p.period =
        ((15 * p.complementFactor i : Nat) : Int) * z ∧
      Int.ModEq (crtFactor q (p.kappa i)) P
        (z * (p.kappa i : Int) * p.complementFactor i) := by
  let c : Int := (15 * p.complementFactor i : Nat)
  let d : Int := crtFactor q (p.kappa i)
  let δ : Int := (P * (s₁ : Int)) % p.period - (P * (s₀ : Int)) % p.period
  obtain ⟨τ, hτ⟩ := parameter_step_divisible hq p i h15 hoff
  have hinv := parameter_step_inverse p i hτ hstep
  have hL : (p.period : Int) = c * d := by
    dsimp [c, d]
    exact_mod_cast parameter_period_complement p i
  have hc : c ≠ 0 := by
    dsimp [c]
    have h := parameter_complement_pos p i
    positivity
  have he : Int.ModEq (p.period : Int) δ (c * (P * τ)) := by
    have h := (Int.mod_modEq (P * (s₁ : Int)) p.period).sub
      (Int.mod_modEq (P * (s₀ : Int)) p.period)
    convert h using 1
    rw [← mul_sub, hτ]
    dsimp [c]
    ring
  have hdvd : c ∣ δ := by
    apply ((he.of_dvd (by rw [hL]; exact dvd_mul_right c d)).dvd_iff).mpr
    exact dvd_mul_right c (P * τ)
  obtain ⟨z, hz⟩ := hdvd
  have hzmod : Int.ModEq d z (P * τ) := by
    apply Int.ModEq.mul_left_cancel' hc
    rwa [← hL, ← hz]
  have hP : Int.ModEq d P (z * (p.kappa i : Int) * p.complementFactor i) := by
    have h₁ := hzmod.mul_right ((p.kappa i : Int) * p.complementFactor i)
    have h₂ := hinv.mul_left P
    have h₃ : Int.ModEq d (z * (p.kappa i : Int) * p.complementFactor i) P := by
      convert h₁.trans (by convert h₂ using 1; ring) using 1 <;> ring
    exact h₃.symm
  exact ⟨z, hz, hP⟩

theorem parameter_grid_unit_coefficient {q N : Nat} (hq : 0 < q)
    (p : ParameterFamily q N) {h : Fin 5} {ρ : (Fin N → Nat) → Nat}
    (hρ : p.IsGridMap h ρ) (P : Int) (i : Fin N) :
    ∃ z : Int,
      (P * (ρ (Function.update (fun _ => 0) i 1) : Int)) % p.period -
        (P * (ρ (fun _ => 0) : Int)) % p.period =
        ((15 * p.complementFactor i : Nat) : Int) * z ∧
      Int.ModEq (crtFactor q (p.kappa i)) P
        (z * (p.kappa i : Int) * p.complementFactor i) := by
  classical
  have hzero := hρ (fun _ => 0) (fun _ => Nat.zero_le _)
  have hunit := hρ (Function.update (fun _ => 0) i 1) (by
    intro j
    by_cases hj : j = i
    · subst j
      simpa using Nat.succ_le_of_lt (parameter_grid_bounds_pos hq p h i)
    · simp [hj])
  apply parameter_phase_difference_coefficient hq p i P
  · apply (Nat.modEq_and_modEq_iff_modEq_mul (by decide : (3 : Nat).Coprime 5)).mp
    exact ⟨hzero.2.1.1.trans hunit.2.1.1.symm, hzero.2.2.1.trans hunit.2.2.1.symm⟩
  · intro j hj
    rw [hzero.2.2.2 j, hunit.2.2.2 j]
    simp [hj]
  · have h₀ := (Int.natCast_modEq_iff.mpr
        (Nat.mod_modEq (p.kappa i * ρ (fun _ => 0)) (p.orientation i.succ))).symm
    have h₁ := (Int.natCast_modEq_iff.mpr
        (Nat.mod_modEq (p.kappa i * ρ (Function.update (fun _ => 0) i 1))
          (p.orientation i.succ))).symm
    rw [hzero.2.2.2 i] at h₀
    rw [hunit.2.2.2 i] at h₁
    simp only [Function.update_self] at h₁
    have he := h₁.sub h₀
    change Int.ModEq ((5 * crtFactor q (p.kappa i) : Nat) : Int) _ _ at he
    convert he using 1 <;> push_cast <;> ring

theorem parameter_grid_weight_large {q N : Nat} (hq : 0 < q) (p : ParameterFamily q N)
    (i : Fin N) :
    p.period < 6 * (gridBound (crtFactor q (p.kappa i)) 0 * (15 * p.complementFactor i)) := by
  let d := crtFactor q (p.kappa i)
  let c := 15 * p.complementFactor i
  have hd : 2 < d := by
    have he := crtFactor_ge_kappa (κ := p.kappa i) hq (by have hi := p.large i; omega)
    have hi := p.large i
    dsimp [d]
    omega
  have hm : 3 * gridBound d 0 + 1 = d := by
    have hd15 := crtFactor_mod_fifteen q (p.kappa i)
    dsimp [gridBound, d]
    omega
  have he : p.period = c * d := parameter_period_complement p i
  have hc : 0 < c := Nat.mul_pos (by decide) (parameter_complement_pos p i)
  change p.period < 6 * (gridBound d 0 * c)
  nlinarith only [hm, he, hc, hd]

theorem middleThirdCharacter_sparse_coefficients {q N : Nat} (hq : 0 < q)
    (p : ParameterFamily q N) {P b : Int} (hchar : p.MiddleThirdCharacter P b) :
    ∃ z : Fin N → Int,
      (∀ i, z i = 0 ∨ z i = 1 ∨ z i = -1) ∧
      (∀ i j, z i ≠ 0 → z j ≠ 0 → i = j) ∧
      (∀ i, Int.ModEq (crtFactor q (p.kappa i)) P
        (z i * (p.kappa i : Int) * p.complementFactor i)) ∧
      (∀ i, z i = 0 → (crtFactor q (p.kappa i) : Int) ∣ P) := by
  classical
  obtain ⟨ρ, hρ⟩ := exists_generic_grid_map hq p 0
  obtain ⟨δ, hδ, _, hwidth⟩ := middleThirdCharacter_grid_affine hq p hchar 0 hρ
  choose z hz hzmod using parameter_grid_unit_coefficient hq p hρ P
  have hd : ∀ i, δ i = ((15 * p.complementFactor i : Nat) : Int) * z i := by
    intro i
    exact (hδ i).trans (hz i)
  let w : Fin N → Nat := fun i =>
    gridBound (crtFactor q (p.kappa i)) 0 * (15 * p.complementFactor i)
  have hsum : (∑ i, (gridBound (crtFactor q (p.kappa i)) 0 : Int) * |δ i|) =
      ((∑ i, w i * (z i).natAbs : Nat) : Int) := by
    push_cast
    apply Finset.sum_congr rfl
    intro i _
    rw [hd i, abs_mul]
    simp only [abs_of_nonneg (Int.natCast_nonneg _)]
    dsimp [w]
    ring
  rw [hsum] at hwidth
  have hnat : 3 * ∑ i, w i * (z i).natAbs ≤ p.period := by exact_mod_cast hwidth
  obtain ⟨habs, hone⟩ := sparse_integer_coefficients_of_weighted_bound p.period w z
    (parameter_grid_weight_large hq p) hnat
  refine ⟨z, fun i => int_eq_zero_or_unit_of_natAbs_le_one (habs i), hone, hzmod, ?_⟩
  intro i hi
  have he := hzmod i
  rw [hi, zero_mul, zero_mul] at he
  exact Int.modEq_zero_iff_dvd.mp he

theorem middleThirdCharacter_coefficient_cases {q N : Nat} (hq : 0 < q)
    (p : ParameterFamily q N) {P b : Int} (hchar : p.MiddleThirdCharacter P b) :
    (∀ i, (crtFactor q (p.kappa i) : Int) ∣ P) ∨
      ∃ i, (∀ j, j ≠ i → (crtFactor q (p.kappa j) : Int) ∣ P) ∧
        (Int.ModEq (crtFactor q (p.kappa i)) P
          ((p.kappa i : Int) * p.complementFactor i) ∨
         Int.ModEq (crtFactor q (p.kappa i)) P
          (-((p.kappa i : Int) * p.complementFactor i))) := by
  classical
  obtain ⟨z, hz, hone, hmod, hdiv⟩ := middleThirdCharacter_sparse_coefficients hq p hchar
  by_cases hall : ∀ i, z i = 0
  · exact Or.inl (fun i => hdiv i (hall i))
  · obtain ⟨i, hi⟩ := not_forall.mp hall
    refine Or.inr ⟨i, ?_, ?_⟩
    · intro j hj
      apply hdiv j
      by_contra hjz
      exact hj (hone j i hjz hi)
    · rcases hz i with hzero | hpos | hneg
      · exact False.elim (hi hzero)
      · left; simpa only [hpos, one_mul] using hmod i
      · right; simpa only [hneg, neg_one_mul, neg_mul, one_mul] using hmod i

theorem first_phase_coefficient_fifteen {d t : Int} (hd : 8 < d)
    (hzero : 5 * d ≤ (10 * d + 2 * t * d + 2) % (15 * d) ∧
      (10 * d + 2 * t * d + 2) % (15 * d) ≤ 5 * d + 20)
    (hone : 5 * d ≤ (10 * d + 5 * t * d + 5) % (15 * d) ∧
      (10 * d + 5 * t * d + 5) % (15 * d) ≤ 5 * d + 20) :
    t % 15 = 5 := by
  let a := (10 * d + 2 * t * d + 2) % (15 * d)
  let c := (10 * d + 5 * t * d + 5) % (15 * d)
  let qa := (10 * d + 2 * t * d + 2) / (15 * d)
  let qc := (10 * d + 5 * t * d + 5) / (15 * d)
  have ha : a + 15 * d * qa = 10 * d + 2 * t * d + 2 :=
    Int.emod_add_mul_ediv _ _
  have hc : c + 15 * d * qc = 10 * d + 5 * t * d + 5 :=
    Int.emod_add_mul_ediv _ _
  change 5 * d ≤ a ∧ a ≤ 5 * d + 20 at hzero
  change 5 * d ≤ c ∧ c ≤ 5 * d + 20 at hone
  let u := qc - qa
  have he : 3 * d * (t - 5 * u) = c - a - 3 := by dsimp [u]; nlinarith only [ha, hc]
  have hz : t - 5 * u = 0 := by
    rcases lt_trichotomy (t - 5 * u) 0 with hneg | hzero | hpos
    · have hle : t - 5 * u ≤ -1 := by omega
      nlinarith
    · exact hzero
    · have hle : 1 ≤ t - 5 * u := by omega
      nlinarith
  have ht : t = 5 * u := by omega
  have he' : 5 * d * (2 + 2 * u - 3 * qa) = a - 2 := by
    rw [ht] at ha
    nlinarith only [ha]
  have hv : 2 + 2 * u - 3 * qa = 1 := by
    rcases lt_trichotomy (2 + 2 * u - 3 * qa) 1 with hneg | heq | hpos
    · have hle : 2 + 2 * u - 3 * qa ≤ 0 := by omega
      nlinarith
    · exact heq
    · have hle : 2 ≤ 2 + 2 * u - 3 * qa := by omega
      nlinarith
  omega

theorem middle_third_progression_first_bound {d A : Int} (hd : 8 < d) {M : Nat}
    (hM : 0 < M) (hf : ∀ y : Nat, y ≤ M →
      5 * d ≤ (A + 15 * (y : Int)) % (15 * d) ∧
      (A + 15 * (y : Int)) % (15 * d) ≤ 10 * d) :
    A % (15 * d) + 15 * (M : Int) ≤ 10 * d := by
  let f : Nat → Int := fun y => (A + 15 * (y : Int)) % (15 * d)
  obtain ⟨δ, hδ, ha, _⟩ := integer_progression_affine_in_short_arc hM
    (n := 15 * d) (A := 5 * d) (B := 10 * d) (d := 15) (by omega) f hf (by
      intro y _
      have he := (Int.mod_modEq (A + 15 * ((y + 1 : Nat) : Int)) (15 * d)).sub
        (Int.mod_modEq (A + 15 * (y : Int)) (15 * d))
      convert he using 1
      push_cast
      ring)
  have hzero := hf 0 (by omega)
  have hone := hf 1 (by omega)
  have heone := ha 1 (by omega)
  have he : δ = 15 := by
    apply int_modEq_eq_in_short_interval (A := -(5 * d)) (B := 5 * d)
      (by omega) ?_ (by omega) hδ
    dsimp [f] at heone
    norm_num at hzero hone heone
    omega
  have heM := ha M le_rfl
  have hlast := hf M le_rfl
  rw [he] at heM
  dsimp [f] at heM
  norm_num at heM
  nlinarith only [heM, hlast.2]

theorem middle_third_grid_first_bound {d : Nat} (hd : 8 < d) (hd15 : d % 15 = 1)
    (h : Fin 5) (A : Int)
    (hf : ∀ y : Nat, y ≤ gridBound d h →
      5 * (d : Int) ≤ (A + 15 * (y : Int)) % (15 * (d : Int)) ∧
      (A + 15 * (y : Int)) % (15 * (d : Int)) ≤ 10 * (d : Int)) :
    5 * (d : Int) ≤ A % (15 * (d : Int)) ∧ A % (15 * (d : Int)) ≤ 5 * (d : Int) + 20 := by
  have hM : 0 < gridBound d h := by unfold gridBound; split_ifs <;> omega
  have hwidth : 5 * (d : Int) - 20 ≤ 15 * (gridBound d h : Int) := by
    unfold gridBound
    split_ifs <;> omega
  have he := middle_third_progression_first_bound (by exact_mod_cast hd) hM hf
  have hzero := hf 0 (Nat.zero_le _)
  norm_num at hzero
  exact ⟨hzero.1, by omega⟩

theorem one_coordinate_frequency_parameter {d : Nat} (hd : 8 < d) (hd15 : d % 15 = 1)
    (t : Int) (hf : ∀ h : Fin 5, ∀ y : Nat, y ≤ gridBound d h →
      5 * (d : Int) ≤ (10 * (d : Int) + t * (2 + 3 * (h.val : Int)) * d +
        (2 + 3 * (h.val : Int)) + 15 * (y : Int)) % (15 * (d : Int)) ∧
      (10 * (d : Int) + t * (2 + 3 * (h.val : Int)) * d +
        (2 + 3 * (h.val : Int)) + 15 * (y : Int)) % (15 * (d : Int)) ≤ 10 * (d : Int)) :
    t % 15 = 5 := by
  have hzero := middle_third_grid_first_bound hd hd15 0
    (10 * (d : Int) + t * 2 * d + 2) (by simpa using hf 0)
  have hone := middle_third_grid_first_bound hd hd15 1
    (10 * (d : Int) + t * 5 * d + 5) (by simpa using hf 1)
  apply first_phase_coefficient_fifteen (d := (d : Int)) (by exact_mod_cast hd)
  · simpa only [mul_comm t 2] using hzero
  · simpa only [mul_comm t 5] using hone

theorem parameter_product_dvd_integer {q N : Nat} (p : ParameterFamily q N)
    (S : Finset (Fin N)) {P : Int}
    (hdiv : ∀ i ∈ S, (crtFactor q (p.kappa i) : Int) ∣ P) :
    ((∏ i ∈ S, crtFactor q (p.kappa i) : Nat) : Int) ∣ P := by
  rw [Nat.cast_prod]
  apply Finset.prod_dvd_of_coprime
  · intro i _ j _ hij
    exact (p.coprime hij).isCoprime
  · exact hdiv

theorem middleThirdCharacter_inactive_frequency {q N : Nat} (hq : 0 < q)
    (p : ParameterFamily q N) {P b : Int} (hchar : p.MiddleThirdCharacter P b)
    (hdiv : ∀ i, (crtFactor q (p.kappa i) : Int) ∣ P) :
    Int.ModEq p.period P ((5 * ∏ i : Fin N, crtFactor q (p.kappa i) : Nat) : Int) ∨
      Int.ModEq p.period P ((10 * ∏ i : Fin N, crtFactor q (p.kappa i) : Nat) : Int) := by
  let D := ∏ i : Fin N, crtFactor q (p.kappa i)
  have hD : (0 : Int) < D := by
    exact_mod_cast (Finset.prod_pos (fun i (_ : i ∈ (Finset.univ : Finset (Fin N))) =>
      crtFactor_pos q (p.kappa i)))
  obtain ⟨T, hP⟩ := parameter_product_dvd_integer p Finset.univ (fun i _ => hdiv i)
  change P = (D : Int) * T at hP
  have hphase : ∀ h : Fin 5, 5 ≤ (T * (2 + 3 * (h.val : Int))) % 15 ∧
      (T * (2 + 3 * (h.val : Int))) % 15 ≤ 10 := by
    intro h
    obtain ⟨ρ, hρ, hgen, hρ5⟩ := generic_residue_in_each_block hq p h
    have hρ15 : Nat.ModEq 15 ρ (2 + 3 * h.val) := by
      apply (Nat.modEq_and_modEq_iff_modEq_mul (by decide : (3 : Nat).Coprime 5)).mp
      refine ⟨?_, hρ5⟩
      change ρ % 3 = (2 + 3 * h.val) % 3
      rw [hgen.1]
      omega
    have he : (P * (ρ : Int)) % p.period = (D : Int) * ((T * (ρ : Int)) % 15) := by
      rw [hP]
      change ((D : Int) * T * (ρ : Int)) % ((15 * D : Nat) : Int) = _
      rw [Nat.cast_mul, Nat.cast_ofNat, mul_assoc, mul_comm (15 : Int) (D : Int)]
      exact Int.mul_emod_mul_of_pos _ _ hD
    have hm : (T * (ρ : Int)) % 15 = (T * (2 + 3 * (h.val : Int))) % 15 := by
      have hm := (Int.natCast_modEq_iff.mpr hρ15).mul_left T
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hm.eq
    have hb := (hchar ρ hρ hgen).1
    rw [he, hm] at hb
    change (15 * D : Nat) ≤ 3 * ((D : Int) * _) ∧
      3 * ((D : Int) * _) ≤ 2 * ((15 * D : Nat) : Int) at hb
    push_cast at hb
    constructor <;> nlinarith
  have h₀ := hphase 0
  have h₁ := hphase 1
  have h₂ := hphase 2
  norm_num at h₀ h₁ h₂
  have hT : T % 15 = 5 ∨ T % 15 = 10 := by
    rw [((Int.mod_modEq T 15).mul_right 2).symm.eq] at h₀
    rw [((Int.mod_modEq T 15).mul_right 5).symm.eq] at h₁
    rw [((Int.mod_modEq T 15).mul_right 8).symm.eq] at h₂
    have hlo := Int.emod_nonneg T (by decide : (15 : Int) ≠ 0)
    have hhi := Int.emod_lt_of_pos T (by decide : (0 : Int) < 15)
    interval_cases hr : T % 15 <;> omega
  rcases hT with hT | hT
  · left
    have hm : Int.ModEq 15 T 5 := by simpa [Int.ModEq] using hT
    have he := hm.mul_left' (c := (D : Int))
    rw [hP]
    convert he using 1 <;> dsimp [ParameterFamily.period, D] <;> push_cast <;> ring
  · right
    have hm : Int.ModEq 15 T 10 := by simpa [Int.ModEq] using hT
    have he := hm.mul_left' (c := (D : Int))
    rw [hP]
    convert he using 1 <;> dsimp [ParameterFamily.period, D] <;> push_cast <;> ring

theorem characterDeficit_three_mul_neg_one {n : Nat} (hn : n % 3 = 1) {K : Int}
    (hK : Int.ModEq n (3 * K) (-1)) : characterDeficit n K = 1 := by
  have hn' : (n : Int) = 3 * ((n / 3 : Nat) : Int) + 1 := by omega
  have hcanon : Int.ModEq n (3 * ((n / 3 : Nat) : Int)) (-1) := by
    apply Int.modEq_of_dvd
    refine ⟨-1, ?_⟩
    nlinarith only [hn']
  have hcop : (n : Int).gcd 3 = 1 := by exact_mod_cast coprime_of_remainder_one hn
  have hmod : Int.ModEq n K ((n / 3 : Nat) : Int) := by
    have he := Int.ModEq.cancel_left_div_gcd (show (0 : Int) < n by omega)
      (hK.trans hcanon.symm)
    simpa only [hcop, Nat.cast_one, Int.ediv_one] using he
  rw [characterDeficit_congr hmod]
  convert canonical_deficit_one (n / 3) using 1
  congr 1
  omega

theorem constant_frequency_three_mul {n C K P b : Int} (hC : 0 < C) (hn : n % 3 = 1)
    (hfreq : Int.ModEq (3 * C) P C) (hidentity : K * (3 * C) = P * n + b)
    (hb : 2 * |b| < 3 * C) : Int.ModEq n (3 * K) (-1) := by
  obtain ⟨a, ha⟩ := hfreq.dvd
  have hP : P = C - 3 * C * a := by omega
  let z := 3 * (K + a * n) - n
  have hbz : b = C * z := by
    dsimp [z]
    rw [hP] at hidentity
    nlinarith only [hidentity]
  have hb' : 2 * (C * |z|) < 3 * C := by
    rwa [hbz, abs_mul, abs_of_pos hC] at hb
  have habs : 2 * |z| < 3 := by nlinarith only [hC, hb']
  have hz : z = -1 := by
    have hz3 : z % 3 = 2 := by dsimp [z]; omega
    have hlo := neg_le_abs z
    have hhi := le_abs_self z
    omega
  apply Int.modEq_of_dvd
  refine ⟨3 * a - 1, ?_⟩
  dsimp [z] at hz
  nlinarith only [hz]

theorem constant_frequency_deficit {n : Nat} (hn : n % 3 = 1) {C K P b : Int}
    (hC : 0 < C) (hidentity : K * (3 * C) = P * (n : Int) + b)
    (hb : 2 * |b| < 3 * C)
    (hfreq : Int.ModEq (3 * C) P C ∨ Int.ModEq (3 * C) P (2 * C)) :
    characterDeficit n K = 1 := by
  have hn' : (n : Int) % 3 = 1 := by exact_mod_cast hn
  rcases hfreq with hf | hf
  · exact characterDeficit_three_mul_neg_one hn
      (constant_frequency_three_mul hC hn' hf hidentity hb)
  · have hf' : Int.ModEq (3 * C) (-P) C := by
      have he : Int.ModEq (3 * C) (-(2 * C)) C := by
        apply Int.modEq_of_dvd
        refine ⟨1, ?_⟩
        ring
      exact hf.neg.trans he
    have hid : (-K) * (3 * C) = (-P) * (n : Int) + (-b) := by nlinarith only [hidentity]
    have hb' : 2 * |-b| < 3 * C := by simpa only [abs_neg] using hb
    have he := characterDeficit_three_mul_neg_one hn
      (constant_frequency_three_mul hC hn' hf' hid hb')
    simpa only [characterDeficit_neg] using he

theorem cyclic_data_inactive_character {r : Nat} (p : CyclicIntegerData r) {K P b : Int}
    (hidentity : K * p.family.period = P * p.n + b)
    (hb : 2 * |b| < (p.family.period : Int)) (hchar : p.family.MiddleThirdCharacter P b)
    (hdiv : ∀ i, (crtFactor (3 * p.t + 1) (p.family.kappa i) : Int) ∣ P) :
    ∃ i, 0 < characterDeficit p.n (K * ((p.unitDirection i : ZMod p.n).val : Int)) := by
  let C : Int := (5 * ∏ i, crtFactor (3 * p.t + 1) (p.family.kappa i) : Nat)
  have hC : 0 < C := by
    dsimp [C]
    have hprod : 0 < ∏ i, crtFactor (3 * p.t + 1) (p.family.kappa i) :=
      Finset.prod_pos (fun i _ => crtFactor_pos _ (p.family.kappa i))
    positivity
  have hL : (p.family.period : Int) = 3 * C := by
    dsimp [C, ParameterFamily.period]
    push_cast
    ring
  have hf := middleThirdCharacter_inactive_frequency (by omega : 0 < 3 * p.t + 1)
    p.family hchar hdiv
  have hf' : Int.ModEq (3 * C) P C ∨ Int.ModEq (3 * C) P (2 * C) := by
    rw [hL] at hf
    have he : ((10 * ∏ i, crtFactor (3 * p.t + 1) (p.family.kappa i) : Nat) : Int) = 2 * C := by
      dsimp [C]
      push_cast
      ring
    rw [he] at hf
    exact hf
  have hd := constant_frequency_deficit p.order_three hC (by rwa [← hL]) (by rwa [← hL]) hf'
  refine ⟨0, ?_⟩
  rw [cyclic_data_unitDirection_val]
  have hz : p.family.orientation ⟨(0 : ZMod (3 * p.t + 1)).val, ZMod.val_lt 0⟩ = 1 := by
    simp [ParameterFamily.orientation]
  rw [hz, Nat.cast_one, mul_one, hd]
  decide

theorem active_frequency_parameter_form {q N : Nat} (p : ParameterFamily q N)
    (i : Fin N) {P : Int}
    (hoff : ∀ j, j ≠ i → (crtFactor q (p.kappa j) : Int) ∣ P)
    (hmod : Int.ModEq (crtFactor q (p.kappa i)) P
      ((p.kappa i : Int) * p.complementFactor i)) :
    ∃ t : Int, P = (p.complementFactor i : Int) *
      ((p.kappa i : Int) + (crtFactor q (p.kappa i) : Int) * t) := by
  obtain ⟨v, hv⟩ := parameter_product_dvd_integer p (Finset.univ.erase i)
    (fun j hj => hoff j (Finset.mem_erase.mp hj).1)
  change P = (p.complementFactor i : Int) * v at hv
  have hcancel : Int.ModEq (crtFactor q (p.kappa i)) v (p.kappa i) := by
    apply Int.modEq_of_dvd
    apply (parameter_complement_coprime p i).isCoprime.dvd_of_dvd_mul_left
    have he := hmod.dvd
    rw [hv] at he
    rw [show (p.complementFactor i : Int) * ((p.kappa i : Int) - v) =
      (p.kappa i : Int) * p.complementFactor i - (p.complementFactor i : Int) * v by ring]
    exact he
  obtain ⟨a, ha⟩ := hcancel.dvd
  refine ⟨-a, ?_⟩
  rw [hv]
  congr 1
  nlinarith only [ha]

theorem parameter_coordinate_phase_modEq {q N : Nat} (p : ParameterFamily q N)
    {s : Nat} (hgen : p.GenericResidue s) (i : Fin N) :
    Int.ModEq (15 * crtFactor q (p.kappa i)) ((p.kappa i : Int) * (s : Int))
      (10 * (crtFactor q (p.kappa i) : Int) +
        ((p.kappa i * s % p.orientation i.succ : Nat) : Int)) := by
  let d := crtFactor q (p.kappa i)
  let e := p.kappa i * s % p.orientation i.succ
  have hd3 : d % 3 = 1 := by have he := crtFactor_mod_fifteen q (p.kappa i); dsimp [d]; omega
  have he3 : e % 3 = 2 := hgen.2 i
  have h3 : Nat.ModEq 3 (p.kappa i * s) (10 * d + e) := by
    change (p.kappa i * s) % 3 = (10 * d + e) % 3
    rw [Nat.mul_mod (p.kappa i) s 3, p.mod_three i]
    omega
  have he : Nat.ModEq (5 * d) (p.kappa i * s) e :=
    (Nat.mod_modEq _ _).symm
  have h5d : Nat.ModEq (5 * d) (p.kappa i * s) (10 * d + e) := by
    apply he.trans
    convert (Nat.ModEq.modulus_mul_add (m := 5 * d) (a := 2) (b := e)).symm using 1
    ring
  have hcop : (3 : Nat).Coprime (5 * d) := by
    change Nat.gcd 3 (5 * d) = 1
    rw [Nat.gcd_rec]
    have ha3 : (5 * d) % 3 = 2 := by omega
    rw [ha3]
    decide
  have hall := (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨h3, h5d⟩
  have hc := Int.natCast_modEq_iff.mpr hall
  push_cast at hc
  convert hc using 1
  dsimp [d, e]
  ring

theorem parameter_active_phase_formula {q N : Nat} (p : ParameterFamily q N)
    (i : Fin N) {P t : Int}
    (hP : P = (p.complementFactor i : Int) *
      ((p.kappa i : Int) + (crtFactor q (p.kappa i) : Int) * t))
    {s y : Nat} {h : Fin 5} (hgen : p.GenericResidue s)
    (hs5 : s % 5 = (2 + 3 * h.val) % 5)
    (hcoord : p.kappa i * s % p.orientation i.succ = 2 + 3 * h.val + 15 * y) :
    (P * (s : Int)) % p.period = (p.complementFactor i : Int) *
      ((10 * (crtFactor q (p.kappa i) : Int) + t * (2 + 3 * (h.val : Int)) *
        crtFactor q (p.kappa i) + (2 + 3 * (h.val : Int)) + 15 * (y : Int)) %
          (15 * (crtFactor q (p.kappa i) : Int))) := by
  let d : Int := crtFactor q (p.kappa i)
  let Q : Int := p.complementFactor i
  have hQ : 0 < Q := by dsimp [Q]; exact_mod_cast parameter_complement_pos p i
  have hs15 : Nat.ModEq 15 s (2 + 3 * h.val) := by
    apply (Nat.modEq_and_modEq_iff_modEq_mul (by decide : (3 : Nat).Coprime 5)).mp
    refine ⟨?_, hs5⟩
    change s % 3 = (2 + 3 * h.val) % 3
    rw [hgen.1]
    omega
  have ht := ((Int.natCast_modEq_iff.mpr hs15).mul_left' (c := d)).mul_left t
  have hk := parameter_coordinate_phase_modEq p hgen i
  rw [hcoord] at hk
  have ht' : Int.ModEq (15 * d) (t * d * (s : Int))
      (t * (2 + 3 * (h.val : Int)) * d) := by
    convert ht using 1 <;> push_cast <;> ring
  have he : Int.ModEq (15 * d) (((p.kappa i : Int) + d * t) * (s : Int))
      (10 * d + t * (2 + 3 * (h.val : Int)) * d +
        (2 + 3 * (h.val : Int)) + 15 * (y : Int)) := by
    convert hk.add ht' using 1 <;> push_cast <;> ring
  have hL : (p.period : Int) = Q * (15 * d) := by
    rw [parameter_period_complement p i]
    dsimp [Q, d]
    ring
  rw [hP, hL, mul_assoc, Int.mul_emod_mul_of_pos _ _ hQ, he.eq]

theorem middleThirdCharacter_active_frequency {q N : Nat} (hq : 0 < q)
    (p : ParameterFamily q N) {P b : Int} (hchar : p.MiddleThirdCharacter P b)
    (i : Fin N) (hoff : ∀ j, j ≠ i → (crtFactor q (p.kappa j) : Int) ∣ P)
    (hmod : Int.ModEq (crtFactor q (p.kappa i)) P
      ((p.kappa i : Int) * p.complementFactor i)) :
    Int.ModEq p.period P ((p.complementFactor i : Int) *
      (5 * (crtFactor q (p.kappa i) : Int) + (p.kappa i : Int))) := by
  classical
  let d := crtFactor q (p.kappa i)
  let Q := p.complementFactor i
  have hd : 8 < d := by
    have he := orientation_gt_hundred hq p i
    change 100 < 5 * d at he
    omega
  have hQ : (0 : Int) < Q := by dsimp [Q]; exact_mod_cast parameter_complement_pos p i
  obtain ⟨t, ht⟩ := active_frequency_parameter_form p i hoff hmod
  have hphases : ∀ h : Fin 5, ∀ y : Nat, y ≤ gridBound d h →
      5 * (d : Int) ≤ (10 * (d : Int) + t * (2 + 3 * (h.val : Int)) * d +
        (2 + 3 * (h.val : Int)) + 15 * (y : Int)) % (15 * (d : Int)) ∧
      (10 * (d : Int) + t * (2 + 3 * (h.val : Int)) * d +
        (2 + 3 * (h.val : Int)) + 15 * (y : Int)) % (15 * (d : Int)) ≤ 10 * (d : Int) := by
    intro h y hy
    obtain ⟨s, hs, hgen, hs5, hcoord⟩ := exists_generic_grid_class hq p h
      (Function.update (fun _ => 0) i y) (by
        intro j
        by_cases hj : j = i
        · subst j; simpa using hy
        · simp [hj])
    have hc : p.kappa i * s % p.orientation i.succ = 2 + 3 * h.val + 15 * y := by
      simpa only [Function.update_self] using hcoord i
    have he := parameter_active_phase_formula p i ht hgen hs5 hc
    have hb := (hchar s hs hgen).1
    rw [he, parameter_period_complement p i] at hb
    change ((15 * Q * d : Nat) : Int) ≤ 3 * ((Q : Int) * _) ∧
      3 * ((Q : Int) * _) ≤ 2 * ((15 * Q * d : Nat) : Int) at hb
    push_cast at hb
    constructor <;> nlinarith
  have ht15 := one_coordinate_frequency_parameter hd (crtFactor_mod_fifteen q (p.kappa i)) t hphases
  have hm : Int.ModEq 15 t 5 := by simpa [Int.ModEq] using ht15
  have he : Int.ModEq (15 * (d : Int)) ((p.kappa i : Int) + (d : Int) * t)
      (5 * (d : Int) + (p.kappa i : Int)) := by
    have he := (hm.mul_left' (c := (d : Int))).add_left (p.kappa i)
    convert he using 1 <;> ring
  have he' := he.mul_left' (c := (Q : Int))
  rw [ht, parameter_period_complement p i]
  convert he' using 1
  dsimp [Q, d]
  ring

theorem active_grid_extreme_phases {q N : Nat} (hq : 0 < q) (p : ParameterFamily q N)
    (i : Fin N) {P : Int}
    (hfreq : Int.ModEq p.period P ((p.complementFactor i : Int) *
      (5 * (crtFactor q (p.kappa i) : Int) + (p.kappa i : Int)))) :
    ∃ s₀ s₁ : Nat, s₀ < p.period ∧ p.GenericResidue s₀ ∧
      s₁ < p.period ∧ p.GenericResidue s₁ ∧
      (P * (s₀ : Int)) % p.period = (p.complementFactor i : Int) *
        (5 * (crtFactor q (p.kappa i) : Int) + 2) ∧
      (P * (s₁ : Int)) % p.period = (p.complementFactor i : Int) *
        (10 * (crtFactor q (p.kappa i) : Int) - 3) := by
  classical
  let d := crtFactor q (p.kappa i)
  let m := gridBound d 0
  let P₀ : Int := (p.complementFactor i : Int) * (5 * (d : Int) + (p.kappa i : Int))
  have hd : 8 < d := by
    have h := orientation_gt_hundred hq p i
    change 100 < 5 * d at h
    omega
  have hm : 3 * m + 1 = d := by
    have h := crtFactor_mod_fifteen q (p.kappa i)
    dsimp [m, gridBound, d]
    omega
  have hP₀ : P₀ = (p.complementFactor i : Int) * ((p.kappa i : Int) + (d : Int) * 5) := by
    dsimp [P₀]
    ring
  obtain ⟨s₀, hs₀, hg₀, hb₀, hc₀⟩ := exists_generic_grid_class hq p 0
    (fun _ => 0) (fun _ => Nat.zero_le _)
  obtain ⟨s₁, hs₁, hg₁, hb₁, hc₁⟩ := exists_generic_grid_class hq p 0
    (Function.update (fun _ => 0) i m) (by
      intro j
      by_cases hj : j = i
      · subst j; simp [m, d]
      · simp [hj])
  have he₀ : p.kappa i * s₀ % p.orientation i.succ = 2 + 3 * (0 : Fin 5).val + 15 * 0 :=
    hc₀ i
  have he₁ : p.kappa i * s₁ % p.orientation i.succ = 2 + 3 * (0 : Fin 5).val + 15 * m := by
    simpa only [Function.update_self] using hc₁ i
  have hf₀ := parameter_active_phase_formula p i hP₀ hg₀ hb₀ he₀
  have hf₁ := parameter_active_phase_formula p i hP₀ hg₁ hb₁ he₁
  norm_num only [Fin.val_zero, Nat.cast_zero, mul_zero, add_zero] at hf₀ hf₁
  have hz₀ : (10 * (d : Int) + 10 * d + 2) % (15 * (d : Int)) = 5 * (d : Int) + 2 := by
    have he : Int.ModEq (15 * (d : Int)) (10 * (d : Int) + 10 * d + 2) (5 * (d : Int) + 2) := by
      apply Int.modEq_of_dvd
      refine ⟨-1, ?_⟩
      ring
    exact he.eq.trans (Int.emod_eq_of_lt (by omega) (by omega))
  have hz₁ : (10 * (d : Int) + 10 * d + 2 + 15 * (m : Int)) % (15 * (d : Int)) =
      10 * (d : Int) - 3 := by
    have hm' : 3 * (m : Int) + 1 = d := by exact_mod_cast hm
    have he : Int.ModEq (15 * (d : Int))
        (10 * (d : Int) + 10 * d + 2 + 15 * (m : Int)) (10 * (d : Int) - 3) := by
      apply Int.modEq_of_dvd
      refine ⟨-1, ?_⟩
      nlinarith only [hm']
    exact he.eq.trans (Int.emod_eq_of_lt (by omega) (by omega))
  refine ⟨s₀, s₁, hs₀, hg₀, hs₁, hg₁, ?_, ?_⟩
  · rw [(hfreq.mul_right (s₀ : Int)).eq]
    change (P₀ * (s₀ : Int)) % p.period = _
    rw [hf₀, hz₀]
  · rw [(hfreq.mul_right (s₁ : Int)).eq]
    change (P₀ * (s₁ : Int)) % p.period = _
    rw [hf₁, hz₁]

theorem middleThirdCharacter_active_shift_bounds {q N : Nat} (hq : 0 < q)
    (p : ParameterFamily q N) {P b : Int} (hb : 2 * |b| < (p.period : Int))
    (hchar : p.MiddleThirdCharacter P b) (i : Fin N)
    (hfreq : Int.ModEq p.period P ((p.complementFactor i : Int) *
      (5 * (crtFactor q (p.kappa i) : Int) + (p.kappa i : Int)))) :
    -2 * (p.complementFactor i : Int) ≤ b ∧ b ≤ 3 * (p.complementFactor i : Int) := by
  obtain ⟨s₀, s₁, hs₀, hg₀, hs₁, hg₁, he₀, he₁⟩ := active_grid_extreme_phases hq p i hfreq
  have hzero := hchar s₀ hs₀ hg₀
  have hone := hchar s₁ hs₁ hg₁
  have hL : (0 : Int) < p.period := by exact_mod_cast parameter_period_pos p
  have hz := middle_third_phase_shift hL hb hzero.1 hzero.2
  have ho := middle_third_phase_shift hL hb hone.1 hone.2
  rw [hz, he₀] at hzero
  rw [ho, he₁] at hone
  have he : (p.period : Int) = 15 * (p.complementFactor i : Int) * crtFactor q (p.kappa i) := by
    exact_mod_cast parameter_period_complement p i
  constructor <;> nlinarith only [he, hzero.2.1, hone.2.2]

theorem cyclic_data_active_inverse_congruence {r : Nat} (p : CyclicIntegerData r)
    (i : Fin (3 * p.t)) :
    3 * (5 * crtFactor (3 * p.t + 1) (p.family.kappa i)) ∣
      (5 * crtFactor (3 * p.t + 1) (p.family.kappa i) + p.family.kappa i) * p.n + 1 := by
  let a := 5 * crtFactor (3 * p.t + 1) (p.family.kappa i)
  have ha3 : a % 3 = 2 := orientation_mod_three p.family i
  have hcop : (3 : Nat).Coprime a := by
    change Nat.gcd 3 a = 1
    rw [Nat.gcd_rec, ha3]
    decide
  have hthree : 3 ∣ (a + p.family.kappa i) * p.n + 1 := by
    apply Nat.dvd_of_mod_eq_zero
    simp [Nat.add_mod, Nat.mul_mod, ha3, p.family.mod_three i, p.order_three]
  have ha : a ∣ (a + p.family.kappa i) * p.n + 1 := by
    have he := dvd_add (dvd_mul_right a p.n) (p.inverse_congruence i)
    rw [show (a + p.family.kappa i) * p.n + 1 = a * p.n + (p.family.kappa i * p.n + 1) by ring]
    exact he
  exact hcop.mul_dvd_of_dvd_of_dvd hthree ha

theorem cyclic_data_active_shift {r : Nat} (p : CyclicIntegerData r) {K P b : Int}
    (hidentity : K * p.family.period = P * p.n + b)
    (hb : 2 * |b| < (p.family.period : Int)) (hchar : p.family.MiddleThirdCharacter P b)
    (i : Fin (3 * p.t))
    (hfreq : Int.ModEq p.family.period P ((p.family.complementFactor i : Int) *
      (5 * (crtFactor (3 * p.t + 1) (p.family.kappa i) : Int) + (p.family.kappa i : Int)))) :
    b = (p.family.complementFactor i : Int) := by
  let Q : Int := p.family.complementFactor i
  let a : Int := 5 * crtFactor (3 * p.t + 1) (p.family.kappa i)
  have hQ : 0 < Q := by dsimp [Q]; exact_mod_cast parameter_complement_pos p.family i
  have ha : 5 < a := by
    have he := orientation_gt_hundred (by omega : 0 < 3 * p.t + 1) p.family i
    change 100 < 5 * crtFactor (3 * p.t + 1) (p.family.kappa i) at he
    dsimp [a]
    omega
  have hL : (p.family.period : Int) = Q * (3 * a) := by
    rw [parameter_period_complement p.family i]
    dsimp [Q, a]
    ring
  have hinv : 3 * a ∣ (a + (p.family.kappa i : Int)) * (p.n : Int) + 1 := by
    dsimp [a]
    exact_mod_cast cyclic_data_active_inverse_congruence p i
  have href : Int.ModEq p.family.period
      (Q * (a + (p.family.kappa i : Int)) * (p.n : Int)) (-Q) := by
    apply Int.modEq_of_dvd
    obtain ⟨v, hv⟩ := hinv
    refine ⟨-v, ?_⟩
    rw [hL]
    nlinarith only [congrArg (fun x : Int => Q * x) hv]
  have hPn := (hfreq.mul_right (p.n : Int)).trans href
  have hKL : Int.ModEq p.family.period (K * p.family.period) 0 := by simp [Int.ModEq]
  have hbmod : Int.ModEq p.family.period b Q := by
    have he := hKL.sub hPn
    convert he using 1 <;> omega
  have hbounds := middleThirdCharacter_active_shift_bounds (by omega : 0 < 3 * p.t + 1)
    p.family hb hchar i hfreq
  apply int_modEq_eq_in_short_interval (A := -2 * Q) (B := 3 * Q) ?_ hbounds (by omega) hbmod
  rw [hL]
  nlinarith only [hQ, ha]

theorem cyclic_data_active_character {r : Nat} (p : CyclicIntegerData r) {K P b : Int}
    (hidentity : K * p.family.period = P * p.n + b)
    (hb : 2 * |b| < (p.family.period : Int)) (hchar : p.family.MiddleThirdCharacter P b)
    (i : Fin (3 * p.t))
    (hfreq : Int.ModEq p.family.period P ((p.family.complementFactor i : Int) *
      (5 * (crtFactor (3 * p.t + 1) (p.family.kappa i) : Int) + (p.family.kappa i : Int)))) :
    ∃ j, 0 < characterDeficit p.n (K * ((p.unitDirection j : ZMod p.n).val : Int)) := by
  let Q : Int := p.family.complementFactor i
  let a : Int := 5 * crtFactor (3 * p.t + 1) (p.family.kappa i)
  have hQ : 0 < Q := by dsimp [Q]; exact_mod_cast parameter_complement_pos p.family i
  have hL : (p.family.period : Int) = Q * (3 * a) := by
    rw [parameter_period_complement p.family i]
    dsimp [Q, a]
    ring
  have hbQ := cyclic_data_active_shift p hidentity hb hchar i hfreq
  have hdiv : Q ∣ P := by
    apply ((hfreq.of_dvd (by rw [hL]; exact dvd_mul_right Q (3 * a))).dvd_iff).mpr
    exact dvd_mul_right Q _
  obtain ⟨v, hv⟩ := hdiv
  have he : 3 * (K * a) = v * (p.n : Int) + 1 := by
    rw [hL, hbQ, hv] at hidentity
    nlinarith only [hQ, hidentity]
  have hneg : Int.ModEq p.n (3 * (-(K * a))) (-1) := by
    apply Int.modEq_of_dvd
    refine ⟨v, ?_⟩
    nlinarith only [he]
  have hd := characterDeficit_three_mul_neg_one p.order_three hneg
  rw [characterDeficit_neg] at hd
  refine ⟨(i.succ.val : ZMod (3 * p.t + 1)), ?_⟩
  rw [cyclic_data_unitDirection_val]
  have hindex : (⟨(i.succ.val : ZMod (3 * p.t + 1)).val, ZMod.val_lt _⟩ : Fin (3 * p.t + 1)) = i.succ := by
    apply Fin.ext
    change (i.succ.val : ZMod (3 * p.t + 1)).val = i.succ.val
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt i.succ.isLt]
  rw [hindex]
  change 0 < characterDeficit p.n (K * a)
  rw [hd]
  decide

theorem middleThirdCharacter_neg {q N : Nat} (p : ParameterFamily q N)
    {P b : Int} (hchar : p.MiddleThirdCharacter P b) : p.MiddleThirdCharacter (-P) (-b) := by
  have hneg : ∀ x : Int, ((p.period : Int) ≤ 3 * (x % p.period) ∧
      3 * (x % p.period) ≤ 2 * (p.period : Int)) →
      ((p.period : Int) ≤ 3 * ((-x) % p.period) ∧
        3 * ((-x) % p.period) ≤ 2 * (p.period : Int)) := by
    intro x hx
    have hd : characterDeficit p.period x ≤ 0 :=
      (characterDeficit_le_iff_interval (by omega : (0 : Int) ≤ 0)).mpr (by simpa using hx)
    have hd' : characterDeficit p.period (-x) ≤ 0 := by
      rw [characterDeficit_neg]
      exact hd
    simpa using (characterDeficit_le_iff_interval (by omega : (0 : Int) ≤ 0)).mp hd'
  intro ρ hρ hg
  obtain ⟨hzero, hone⟩ := hchar ρ hρ hg
  simpa only [neg_mul, ← neg_add] using
    And.intro (hneg (P * (ρ : Int)) hzero) (hneg (P * (ρ : Int) + b) hone)

theorem cyclic_data_periodic_rigidity {r : Nat} (p : CyclicIntegerData r) {K P b : Int}
    (hidentity : K * p.family.period = P * p.n + b)
    (hb : 2 * |b| < (p.family.period : Int)) (hchar : p.family.MiddleThirdCharacter P b) :
    ∃ i, 0 < characterDeficit p.n (K * ((p.unitDirection i : ZMod p.n).val : Int)) := by
  have hq : 0 < 3 * p.t + 1 := by omega
  rcases middleThirdCharacter_coefficient_cases hq p.family hchar with hnone | ⟨i, hoff, hf⟩
  · exact cyclic_data_inactive_character p hidentity hb hchar hnone
  · rcases hf with hpos | hneg
    · exact cyclic_data_active_character p hidentity hb hchar i
        (middleThirdCharacter_active_frequency hq p.family hchar i hoff hpos)
    · have hchar' := middleThirdCharacter_neg p.family hchar
      have hoff' : ∀ j, j ≠ i → (crtFactor (3 * p.t + 1) (p.family.kappa j) : Int) ∣ -P :=
        fun j hj => dvd_neg.mpr (hoff j hj)
      have hmod : Int.ModEq (crtFactor (3 * p.t + 1) (p.family.kappa i)) (-P)
          ((p.family.kappa i : Int) * p.family.complementFactor i) := by
        simpa only [neg_neg] using hneg.neg
      have hf' := middleThirdCharacter_active_frequency hq p.family hchar' i hoff' hmod
      have hid : (-K) * p.family.period = (-P) * p.n + (-b) := by nlinarith only [hidentity]
      have hb' : 2 * |-b| < (p.family.period : Int) := by simpa only [abs_neg] using hb
      obtain ⟨j, hj⟩ := cyclic_data_active_character p hid hb' hchar' i hf'
      exact ⟨j, by simpa only [neg_mul, characterDeficit_neg] using hj⟩

theorem erdos944_four (r : Nat) :
    ∃ (V : Type u) (G : SimpleGraph V), Erdos944.SimpleGraph.IsErdos944 G 4 r := by
  obtain ⟨p⟩ := exists_cyclic_integer_data r
  let : NeZero p.n := ⟨Nat.ne_of_gt (cyclic_data_order_pos p)⟩
  apply erdos944_four_of_periodic_rigidity p
  intro K P b hidentity hb hchar
  exact cyclic_data_periodic_rigidity p hidentity hb hchar

/-
## Higher colors

The circulants and punctured colorings below follow Skottová and Steiner,
Critical edge sets in vertex-critical graphs, arXiv:2508.08703v1, Section 4
and Appendix A. Their local propagation argument is not yet proved here.
-/

/-- The period in the higher-color construction. -/
def higherPeriod (k m : Nat) : Nat :=
  if k % 2 = 1 then (k - 1) * m else 2 * (k - 1) * m

/-- Positive connection distances, before taking their negatives. -/
def HigherDistance (k m q d : Nat) : Prop :=
  (0 < d ∧ d < 2 * m ∧ d % 2 = 1) ∨
  (∃ a : Nat, a < q / 2 ∧
    a * higherPeriod k m + 2 * m ≤ d ∧
    d ≤ a * higherPeriod k m +
      (if k % 2 = 1 then (k - 3) * m + 1 else (k - 4) * m + 2)) ∨
  (k % 2 ≠ 1 ∧ ∃ a : Nat, a < q / 2 ∧
    a * higherPeriod k m + (k + 2) * m - 1 ≤ d ∧
    d ≤ a * higherPeriod k m + (2 * k - 4) * m + 1)

/-- The circulant graph with the three prescribed families of distances. -/
def higherGraph (k m q : Nat) : SimpleGraph (ZMod (q * higherPeriod k m + 1)) where
  Adj u v := u ≠ v ∧
    (HigherDistance k m q (v - u).val ∨ HigherDistance k m q (u - v).val)
  symm.symm _ _ h := ⟨h.1.symm, h.2.symm⟩
  loopless.irrefl _ h := h.1 rfl

theorem higherGraph_translation (k m q : Nat)
    (u v a : ZMod (q * higherPeriod k m + 1)) :
    (higherGraph k m q).Adj (u - a) (v - a) ↔ (higherGraph k m q).Adj u v := by
  change ((u - a ≠ v - a) ∧ _) ↔ ((u ≠ v) ∧ _)
  simp only [sub_sub_sub_cancel_right]
  have heq : (u - a = v - a) ↔ u = v := by
    constructor
    · intro h
      calc
        u = (u - a) + a := by abel
        _ = (v - a) + a := by rw [h]
        _ = v := by abel
    · intro h
      rw [h]
  exact and_congr_left (fun _ => not_congr heq)

theorem higherPeriod_pos {k m : Nat} (hk : 5 ≤ k) (hm : 0 < m) :
    0 < higherPeriod k m := by
  have hkpos : 0 < k - 1 := by omega
  unfold higherPeriod
  split <;> positivity

theorem higherPeriod_even {k m : Nat} (hk : 5 ≤ k) : higherPeriod k m % 2 = 0 := by
  unfold higherPeriod
  split
  · have h : (k - 1) % 2 = 0 := by omega
    simp [Nat.mul_mod, h]
  · simp [Nat.mul_mod]

theorem higherPeriod_lower {k m : Nat} (hk : 5 ≤ k) :
    4 * m ≤ higherPeriod k m := by
  have hklow : 4 ≤ k - 1 := by omega
  unfold higherPeriod
  split <;> nlinarith

/-- Two alternating colors on each consecutive row of length `2*m`. -/
def higherRowCode (m x : Nat) : Nat :=
  2 * (x / (2 * m)) + (x % (2 * m)) % 2

/-- The value of the periodic coloring with its hole at zero. -/
def higherColorValue (k m x : Nat) : Nat :=
  higherRowCode m ((x - 1) % higherPeriod k m) % (k - 1)

/-- The coloring as an assignment to the `k-1` available colors. -/
def higherColor (k m q : Nat) (hk : 5 ≤ k)
    (v : ZMod (q * higherPeriod k m + 1)) : Fin (k - 1) :=
  ⟨higherColorValue k m v.val, Nat.mod_lt _ (by omega)⟩

theorem higher_row_decomposition {m x : Nat} (hm : 0 < m) :
    ∃ t s b : Nat, s < m ∧ b < 2 ∧
      x = 2 * m * t + 2 * s + b ∧ higherRowCode m x = 2 * t + b := by
  let t := x / (2 * m)
  let s := (x % (2 * m)) / 2
  let b := (x % (2 * m)) % 2
  have hx := Nat.mod_add_div x (2 * m)
  have hy := Nat.mod_add_div (x % (2 * m)) 2
  have hz := Nat.mod_lt x (show 0 < 2 * m by omega)
  refine ⟨t, s, b, ?_, Nat.mod_lt _ (by omega), ?_, rfl⟩
  · dsimp [s]
    omega
  · dsimp [t, s, b]
    nlinarith

theorem higher_rowCode_bound {k m x : Nat} (hk : 5 ≤ k) (hm : 0 < m)
    (hx : x < higherPeriod k m) :
    higherRowCode m x < (if k % 2 = 1 then k - 1 else 2 * (k - 1)) := by
  obtain ⟨t, s, b, _, hb, he, hc⟩ := higher_row_decomposition (x := x) hm
  rw [hc]
  unfold higherPeriod at hx
  split_ifs at hx ⊢ with h
  · have hp : (k - 1) % 2 = 0 := by omega
    have ht : 2 * t < k - 1 := by nlinarith
    omega
  · have ht : t < k - 1 := by nlinarith
    omega

theorem higher_index_decomposition {k m q x : Nat} (hk : 5 ≤ k) (hm : 0 < m)
    (hx : 0 < x) (hxn : x ≤ q * higherPeriod k m) :
    ∃ a t s b : Nat, a < q ∧ s < m ∧ b < 2 ∧
      x = a * higherPeriod k m + 2 * m * t + 2 * s + b + 1 ∧
      2 * t + b < (if k % 2 = 1 then k - 1 else 2 * (k - 1)) ∧
      higherColorValue k m x = (2 * t + b) % (k - 1) := by
  have hL := higherPeriod_pos hk hm
  let a := (x - 1) / higherPeriod k m
  let z := (x - 1) % higherPeriod k m
  obtain ⟨t, s, b, hs, hb, hz, hc⟩ := higher_row_decomposition (x := z) hm
  have hzlt : z < higherPeriod k m := Nat.mod_lt _ hL
  have hcode := higher_rowCode_bound hk hm hzlt
  rw [hc] at hcode
  refine ⟨a, t, s, b, ?_, hs, hb, ?_, hcode, ?_⟩
  · dsimp [a]
    apply (Nat.div_lt_iff_lt_mul hL).mpr
    omega
  · have hdiv := Nat.mod_add_div (x - 1) (higherPeriod k m)
    change z + higherPeriod k m * a = x - 1 at hdiv
    have hx' : x - 1 + 1 = x := by omega
    nlinarith
  · change higherRowCode m z % (k - 1) = _
    rw [hc]

theorem integer_periodic_intervals_disjoint {L lo hi x y a b : Int}
    (hL : 0 < L) (hx₁ : lo ≤ x) (hx₂ : x ≤ hi)
    (hy₁ : hi < y) (hy₂ : y < lo + L) : a * L + x ≠ b * L + y := by
  intro he
  by_cases hab : a ≤ b
  · have hmul : a * L ≤ b * L := mul_le_mul_of_nonneg_right hab (le_of_lt hL)
    omega
  · have hab' : b + 1 ≤ a := by omega
    have hmul := mul_le_mul_of_nonneg_right hab' (le_of_lt hL)
    nlinarith

theorem higher_odd_same_color_difference {k m q i j : Nat}
    (hk : 5 ≤ k) (hm : 0 < m) (hodd : k % 2 = 1)
    (hi : 0 < i) (hin : i ≤ q * higherPeriod k m)
    (hj : 0 < j) (hjn : j ≤ q * higherPeriod k m)
    (hc : higherColorValue k m i = higherColorValue k m j) :
    ∃ a b s t : Nat, a < q ∧ b < q ∧ s < m ∧ t < m ∧
      (j : Int) - i = ((b : Int) - a) * higherPeriod k m + 2 * ((t : Int) - s) := by
  obtain ⟨a, ti, s, bi, haq, hsm, hbi, hei, hci, hvi⟩ :=
    higher_index_decomposition hk hm hi hin
  obtain ⟨b, tj, t, bj, hbq, htm, hbj, hej, hcj, hvj⟩ :=
    higher_index_decomposition hk hm hj hjn
  simp only [hodd, if_true] at hci hcj
  rw [hvi, hvj, Nat.mod_eq_of_lt hci, Nat.mod_eq_of_lt hcj] at hc
  have hti : ti = tj := by omega
  have hbij : bi = bj := by omega
  refine ⟨a, b, s, t, haq, hbq, hsm, htm, ?_⟩
  rw [hti, hbij] at hei
  rw [hei, hej]
  push_cast
  ring

theorem higher_odd_long_distance_impossible {k m q d : Nat} {A x : Int}
    (hk : 5 ≤ k) (hm : 0 < m) (hodd : k % 2 = 1)
    (hx₁ : -(2 * (m : Int)) + 2 ≤ x) (hx₂ : x ≤ 2 * (m : Int) - 1)
    (hd : (d : Int) = A * higherPeriod k m + x) :
    ¬ (∃ a : Nat, a < q / 2 ∧ a * higherPeriod k m + 2 * m ≤ d ∧
      d ≤ a * higherPeriod k m + (k - 3) * m + 1) := by
  rintro ⟨a, _, hlo, hhi⟩
  have hL : (higherPeriod k m : Int) = ((k : Int) - 1) * m := by
    simp only [higherPeriod, hodd, if_true]
    rw [Int.natCast_mul, Int.natCast_sub (by omega)]
    norm_num
  have hlo' : (a : Int) * higherPeriod k m + 2 * m ≤ d := by exact_mod_cast hlo
  have hhi' : (d : Int) ≤ a * higherPeriod k m + ((k : Int) - 3) * m + 1 := by
    have hhi' : (d : Int) ≤ a * higherPeriod k m + (k - 3 : Nat) * m + 1 := by
      exact_mod_cast hhi
    have hks : ((k - 3 : Nat) : Int) = (k : Int) - 3 := by omega
    simpa only [hks] using hhi'
  have hpos : (0 : Int) < higherPeriod k m := by exact_mod_cast higherPeriod_pos hk hm
  apply integer_periodic_intervals_disjoint hpos hx₁ hx₂
    (y := (d : Int) - a * higherPeriod k m) (a := A) (b := a)
    (by linarith) (by rw [hL] at *; nlinarith)
  linarith

theorem higher_odd_gap_not_distance {k m q i j : Nat}
    (hk : 5 ≤ k) (hm : 0 < m) (hodd : k % 2 = 1)
    (hi : 0 < i) (hin : i ≤ q * higherPeriod k m)
    (hj : 0 < j) (hjn : j ≤ q * higherPeriod k m) (hij : i < j)
    (hc : higherColorValue k m i = higherColorValue k m j) :
    ¬ HigherDistance k m q (j - i) ∧
      ¬ HigherDistance k m q (q * higherPeriod k m + 1 - (j - i)) := by
  obtain ⟨a, b, s, t, haq, hbq, hsm, htm, he⟩ :=
    higher_odd_same_color_difference hk hm hodd hi hin hj hjn hc
  have hLpos : (0 : Int) < higherPeriod k m := by exact_mod_cast higherPeriod_pos hk hm
  have hLlow : 4 * (m : Int) ≤ higherPeriod k m := by exact_mod_cast higherPeriod_lower hk
  have hs : (0 : Int) ≤ s ∧ (s : Int) < m := by exact_mod_cast (And.intro (Nat.zero_le s) hsm)
  have ht : (0 : Int) ≤ t ∧ (t : Int) < m := by exact_mod_cast (And.intro (Nat.zero_le t) htm)
  have hfwd : ((j - i : Nat) : Int) =
      ((b : Int) - a) * higherPeriod k m + 2 * ((t : Int) - s) := by
    rw [Int.natCast_sub (Nat.le_of_lt hij)]
    exact he
  have hwrap : ((q * higherPeriod k m + 1 - (j - i) : Nat) : Int) =
      ((q : Int) - b + a) * higherPeriod k m + (1 - 2 * ((t : Int) - s)) := by
    rw [Int.natCast_sub (by omega), Int.natCast_add, Int.natCast_mul, hfwd]
    norm_num
    ring
  have hfwdlong := higher_odd_long_distance_impossible (q := q) hk hm hodd
    (by omega : -(2 * (m : Int)) + 2 ≤ 2 * ((t : Int) - s))
    (by omega : 2 * ((t : Int) - s) ≤ 2 * (m : Int) - 1) hfwd
  have hwraplong := higher_odd_long_distance_impossible (q := q) hk hm hodd
    (by omega : -(2 * (m : Int)) + 2 ≤ 1 - 2 * ((t : Int) - s))
    (by omega : 1 - 2 * ((t : Int) - s) ≤ 2 * (m : Int) - 1) hwrap
  constructor
  · intro hd
    rcases hd with hd | hd | hd
    · have hLtwo : (higherPeriod k m : Int) % 2 = 0 := by
        exact_mod_cast higherPeriod_even (m := m) hk
      have hemod := congrArg (fun z : Int => z % 2) hfwd
      simp [Int.add_emod, Int.mul_emod, hLtwo] at hemod
      have hdmod : ((j - i : Nat) : Int) % 2 = 1 := by exact_mod_cast hd.2.2
      omega
    · exact hfwdlong (by simpa only [hodd, if_true, Nat.add_assoc] using hd)
    · exact hd.1 hodd
  · intro hd
    rcases hd with hd | hd | hd
    · have hcoef : (1 : Int) ≤ q - b + a := by omega
      have hmul := mul_le_mul_of_nonneg_right hcoef (le_of_lt hLpos)
      have hshort : ((q * higherPeriod k m + 1 - (j - i) : Nat) : Int) < 2 * m := by
        exact_mod_cast hd.2.1
      nlinarith
    · exact hwraplong (by simpa only [hodd, if_true, Nat.add_assoc] using hd)
    · exact hd.1 hodd

/-- A single arithmetic gap check supplies colorings after deleting every vertex. -/
theorem higher_punctured_of_gap_avoidance {k m q : Nat} (hk : 5 ≤ k)
    (hgap : ∀ i j : Nat, 0 < i → i ≤ q * higherPeriod k m →
      0 < j → j ≤ q * higherPeriod k m → i < j →
      higherColorValue k m i = higherColorValue k m j →
      ¬ HigherDistance k m q (j - i) ∧
        ¬ HigherDistance k m q (q * higherPeriod k m + 1 - (j - i))) :
    ∀ v : ZMod (q * higherPeriod k m + 1),
      ∃ c : ZMod (q * higherPeriod k m + 1) → Fin (k - 1),
        ∀ u w, u ≠ v → w ≠ v → (higherGraph k m q).Adj u w → c u ≠ c w := by
  have hordered : ∀ u w : ZMod (q * higherPeriod k m + 1),
      u ≠ 0 → w ≠ 0 → u.val < w.val → (higherGraph k m q).Adj u w →
      higherColor k m q hk u ≠ higherColor k m q hk w := by
    intro u w hu hw huw hadj hc
    have hval := congrArg Fin.val hc
    change higherColorValue k m u.val = higherColorValue k m w.val at hval
    have hnot := hgap u.val w.val (ZMod.val_pos.mpr hu)
      (by have h := ZMod.val_lt u; omega) (ZMod.val_pos.mpr hw)
      (by have h := ZMod.val_lt w; omega) huw hval
    have hfwd : (w - u).val = w.val - u.val := ZMod.val_sub (Nat.le_of_lt huw)
    have hrev : (u - w).val = q * higherPeriod k m + 1 - (w.val - u.val) := by
      rw [show u - w = -(w - u) by abel, ZMod.neg_val,
        if_neg (sub_ne_zero.mpr hadj.1.symm), hfwd]
    rcases hadj.2 with h | h
    · exact hnot.1 (by simpa only [hfwd] using h)
    · exact hnot.2 (by simpa only [hrev] using h)
  have hzero : ∀ u w : ZMod (q * higherPeriod k m + 1),
      u ≠ 0 → w ≠ 0 → (higherGraph k m q).Adj u w →
      higherColor k m q hk u ≠ higherColor k m q hk w := by
    intro u w hu hw hadj
    have hne : u.val ≠ w.val := fun h => hadj.1 (ZMod.val_injective _ h)
    rcases lt_or_gt_of_ne hne with h | h
    · exact hordered u w hu hw h hadj
    · exact (hordered w u hw hu h hadj.symm).symm
  intro v
  refine ⟨fun u => higherColor k m q hk (u - v), ?_⟩
  intro u w hu hw hadj
  exact hzero (u - v) (w - v) (sub_ne_zero.mpr hu) (sub_ne_zero.mpr hw)
    ((higherGraph_translation k m q u w v).mpr hadj)

theorem higher_odd_punctured {k m q : Nat} (hk : 5 ≤ k) (hm : 0 < m)
    (hodd : k % 2 = 1) :
    ∀ v : ZMod (q * higherPeriod k m + 1),
      ∃ c : ZMod (q * higherPeriod k m + 1) → Fin (k - 1),
        ∀ u w, u ≠ v → w ≠ v → (higherGraph k m q).Adj u w → c u ≠ c w := by
  apply higher_punctured_of_gap_avoidance hk
  intro i j hi hin hj hjn hij hc
  exact higher_odd_gap_not_distance hk hm hodd hi hin hj hjn hij hc

theorem mod_eq_cases_below_twice {c x y : Nat} (hx : x < 2 * c) (hy : y < 2 * c)
    (hxy : x % c = y % c) : x = y ∨ x + c = y ∨ y + c = x := by
  have hmod (z : Nat) (hz : z < 2 * c) : z % c = z ∨ z % c + c = z := by
    by_cases hzc : z < c
    · exact Or.inl (Nat.mod_eq_of_lt hzc)
    · right
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
  have hx' := hmod x hx
  have hy' := hmod y hy
  omega

theorem higher_even_start_differences {k m ti tj bi bj : Nat}
    (hk : 5 ≤ k) (heven : k % 2 ≠ 1)
    (hbi : bi < 2) (hbj : bj < 2)
    (hci : 2 * ti + bi < 2 * (k - 1)) (hcj : 2 * tj + bj < 2 * (k - 1))
    (hc : (2 * ti + bi) % (k - 1) = (2 * tj + bj) % (k - 1)) :
    let δ := 2 * (m : Int) * ((tj : Int) - ti) + ((bj : Int) - bi)
    δ = 0 ∨ δ = ((k : Int) - 2) * m + 1 ∨ δ = (k : Int) * m - 1 ∨
      δ = -(((k : Int) - 2) * m + 1) ∨ δ = -((k : Int) * m - 1) := by
  dsimp only
  have hk2 : k % 2 = 0 := by omega
  rcases mod_eq_cases_below_twice hci hcj hc with h | h | h
  · have hti : ti = tj := by omega
    have hb : bi = bj := by omega
    left
    rw [hti, hb]
    ring
  · have hb : (bi = 0 ∧ bj = 1) ∨ (bi = 1 ∧ bj = 0) := by omega
    have h' : 2 * (ti : Int) + bi + ((k : Int) - 1) = 2 * (tj : Int) + bj := by
      have hh : ((k - 1 : Nat) : Int) = (k : Int) - 1 := by omega
      have hh' : 2 * (ti : Int) + bi + (k - 1 : Nat) = 2 * (tj : Int) + bj := by
        exact_mod_cast h
      simpa only [hh] using hh'
    rcases hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · right; left
      push_cast at h' ⊢
      nlinarith
    · right; right; left
      push_cast at h' ⊢
      nlinarith
  · have hb : (bi = 0 ∧ bj = 1) ∨ (bi = 1 ∧ bj = 0) := by omega
    have h' : 2 * (tj : Int) + bj + ((k : Int) - 1) = 2 * (ti : Int) + bi := by
      have hh : ((k - 1 : Nat) : Int) = (k : Int) - 1 := by omega
      have hh' : 2 * (tj : Int) + bj + (k - 1 : Nat) = 2 * (ti : Int) + bi := by
        exact_mod_cast h
      simpa only [hh] using hh'
    rcases hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · right; right; right; right
      push_cast at h' ⊢
      nlinarith
    · right; right; right; left
      push_cast at h' ⊢
      nlinarith

theorem higher_even_same_color_difference {k m q i j : Nat}
    (hk : 5 ≤ k) (hm : 0 < m) (heven : k % 2 ≠ 1)
    (hi : 0 < i) (hin : i ≤ q * higherPeriod k m)
    (hj : 0 < j) (hjn : j ≤ q * higherPeriod k m)
    (hc : higherColorValue k m i = higherColorValue k m j) :
    ∃ a b s t : Nat, ∃ δ : Int, a < q ∧ b < q ∧ s < m ∧ t < m ∧
      (δ = 0 ∨ δ = ((k : Int) - 2) * m + 1 ∨ δ = (k : Int) * m - 1 ∨
        δ = -(((k : Int) - 2) * m + 1) ∨ δ = -((k : Int) * m - 1)) ∧
      (j : Int) - i = ((b : Int) - a) * higherPeriod k m + δ + 2 * ((t : Int) - s) := by
  obtain ⟨a, ti, s, bi, haq, hsm, hbi, hei, hci, hvi⟩ :=
    higher_index_decomposition hk hm hi hin
  obtain ⟨b, tj, t, bj, hbq, htm, hbj, hej, hcj, hvj⟩ :=
    higher_index_decomposition hk hm hj hjn
  simp only [heven, if_false] at hci hcj
  rw [hvi, hvj] at hc
  refine ⟨a, b, s, t, 2 * (m : Int) * ((tj : Int) - ti) + ((bj : Int) - bi),
    haq, hbq, hsm, htm, higher_even_start_differences hk heven hbi hbj hci hcj hc, ?_⟩
  rw [hei, hej]
  push_cast
  ring

theorem higher_even_period_int {k m : Nat} (hk : 5 ≤ k) (heven : k % 2 ≠ 1) :
    (higherPeriod k m : Int) = 2 * ((k : Int) - 1) * m := by
  simp only [higherPeriod, heven, if_false]
  rw [Int.natCast_mul, Int.natCast_mul, Int.natCast_sub (by omega)]
  norm_num

theorem higher_even_normalize_start {k m : Nat} {a δ : Int}
    (hk : 5 ≤ k) (heven : k % 2 ≠ 1)
    (hδ : δ = 0 ∨ δ = ((k : Int) - 2) * m + 1 ∨ δ = (k : Int) * m - 1 ∨
      δ = -(((k : Int) - 2) * m + 1) ∨ δ = -((k : Int) * m - 1)) :
    ∃ b z : Int,
      (z = 0 ∨ z = ((k : Int) - 2) * m + 1 ∨ z = (k : Int) * m - 1) ∧
      a * higherPeriod k m + δ = b * higherPeriod k m + z := by
  rcases hδ with rfl | rfl | rfl | rfl | rfl
  · exact ⟨a, 0, Or.inl rfl, rfl⟩
  · exact ⟨a, ((k : Int) - 2) * m + 1, Or.inr (Or.inl rfl), rfl⟩
  · exact ⟨a, (k : Int) * m - 1, Or.inr (Or.inr rfl), rfl⟩
  · refine ⟨a - 1, (k : Int) * m - 1, Or.inr (Or.inr rfl), ?_⟩
    rw [higher_even_period_int hk heven]
    ring
  · refine ⟨a - 1, ((k : Int) - 2) * m + 1, Or.inr (Or.inl rfl), ?_⟩
    rw [higher_even_period_int hk heven]
    ring

/-- The two long-distance bands in one period when `k` is even. -/
def HigherEvenBand (k m y : Int) : Prop :=
  (2 * m ≤ y ∧ y ≤ (k - 4) * m + 2) ∨
  ((k + 2) * m - 1 ≤ y ∧ y ≤ (2 * k - 4) * m + 1)

theorem higher_even_distance_int {k m q d : Nat} (hk : 5 ≤ k)
    (heven : k % 2 ≠ 1) (hd : HigherDistance k m q d) :
    ((0 : Int) < d ∧ (d : Int) < 2 * m ∧ (d : Int) % 2 = 1) ∨
    ∃ a y : Int, (d : Int) = a * higherPeriod k m + y ∧ HigherEvenBand k m y := by
  rcases hd with hd | ⟨a, _, hlo, hhi⟩ | ⟨_, a, _, hlo, hhi⟩
  · left
    exact_mod_cast hd
  · right
    refine ⟨a, (d : Int) - a * higherPeriod k m, by ring, Or.inl ⟨?_, ?_⟩⟩
    · have hh : (a : Int) * higherPeriod k m + 2 * m ≤ d := by exact_mod_cast hlo
      linarith
    · simp only [heven, if_false] at hhi
      have hh : (d : Int) ≤ a * higherPeriod k m + (k - 4 : Nat) * m + 2 := by
        exact_mod_cast hhi
      have hk4 : ((k - 4 : Nat) : Int) = (k : Int) - 4 := by omega
      rw [hk4] at hh
      linarith
  · right
    refine ⟨a, (d : Int) - a * higherPeriod k m, by ring, Or.inr ⟨?_, ?_⟩⟩
    · have hlo' : a * higherPeriod k m + (k + 2) * m ≤ d + 1 := by omega
      have hh : (a : Int) * higherPeriod k m + ((k : Int) + 2) * m ≤ d + 1 := by
        exact_mod_cast hlo'
      linarith
    · have hh : (d : Int) ≤ a * higherPeriod k m + (2 * k - 4 : Nat) * m + 1 := by
        exact_mod_cast hhi
      have hk4 : ((2 * k - 4 : Nat) : Int) = 2 * (k : Int) - 4 := by omega
      rw [hk4] at hh
      linarith

theorem integer_even_outer_interval_avoids {k m a b x y : Int}
    (hk : 6 ≤ k) (hm : 1 ≤ m)
    (hx₁ : -2 * m + 2 ≤ x) (hx₂ : x ≤ 2 * m - 1) (hy : HigherEvenBand k m y) :
    a * (2 * (k - 1) * m) + x ≠ b * (2 * (k - 1) * m) + y := by
  have hpos : 0 < 2 * (k - 1) * m := mul_pos (mul_pos (by norm_num) (by omega)) (by omega)
  have hy₁ : 2 * m ≤ y := by rcases hy with hy | hy <;> nlinarith
  have hy₂ : y ≤ 2 * (k - 1) * m - 2 * m + 1 := by
    rcases hy with hy | hy <;> nlinarith
  exact integer_periodic_intervals_disjoint hpos hx₁ hx₂ (by omega) (by linarith)

theorem integer_even_middle_interval_avoids {k m a b x y : Int}
    (hk : 6 ≤ k) (hm : 1 ≤ m)
    (hx₁ : (k - 4) * m + 3 ≤ x) (hx₂ : x ≤ (k + 2) * m - 2)
    (hy : HigherEvenBand k m y) :
    a * (2 * (k - 1) * m) + x ≠ b * (2 * (k - 1) * m) + y := by
  have hpos : 0 < 2 * (k - 1) * m := mul_pos (mul_pos (by norm_num) (by omega)) (by omega)
  rcases hy with ⟨hy₁, hy₂⟩ | ⟨hy₁, hy₂⟩
  · intro he
    have hne := integer_periodic_intervals_disjoint hpos hx₁ hx₂
      (y := y + 2 * (k - 1) * m) (a := a) (b := b - 1) (by nlinarith) (by linarith)
    apply hne
    nlinarith
  · exact integer_periodic_intervals_disjoint hpos hx₁ hx₂ (by linarith) (by nlinarith)

theorem integer_even_middle_interval_avoids_short {k m a b x y : Int}
    (hk : 6 ≤ k) (hm : 1 ≤ m)
    (hx₁ : (k - 4) * m + 3 ≤ x) (hx₂ : x ≤ (k + 2) * m - 2)
    (hy₁ : 0 < y) (hy₂ : y < 2 * m) :
    a * (2 * (k - 1) * m) + x ≠ b * (2 * (k - 1) * m) + y := by
  have hpos : 0 < 2 * (k - 1) * m := mul_pos (mul_pos (by norm_num) (by omega)) (by omega)
  exact (integer_periodic_intervals_disjoint hpos (lo := 0) (hi := 2 * m - 1)
    (le_of_lt hy₁) (by omega) (by nlinarith) (by nlinarith)).symm

theorem higher_even_normalized_avoids_long {k m : Nat} {a b z ε y : Int}
    (hk : 5 ≤ k) (hm : 0 < m) (heven : k % 2 ≠ 1)
    (hz : z = 0 ∨ z = ((k : Int) - 2) * m + 1 ∨ z = (k : Int) * m - 1)
    (hε₁ : -2 * (m : Int) + 2 ≤ ε) (hε₂ : ε ≤ 2 * (m : Int) - 1)
    (hy : HigherEvenBand k m y) :
    a * higherPeriod k m + z + ε ≠ b * higherPeriod k m + y := by
  have hk' : (6 : Int) ≤ k := by omega
  have hm' : (1 : Int) ≤ m := by omega
  rw [higher_even_period_int hk heven]
  rcases hz with rfl | rfl | rfl
  · simpa only [add_zero] using integer_even_outer_interval_avoids hk' hm' hε₁ hε₂ hy
  · have hne := integer_even_middle_interval_avoids (a := a) (b := b) hk' hm'
      (x := ((k : Int) - 2) * m + 1 + ε) (by linarith) (by nlinarith) hy
    simpa only [add_assoc] using hne
  · have hne := integer_even_middle_interval_avoids (a := a) (b := b) hk' hm'
      (x := (k : Int) * m - 1 + ε) (by nlinarith) (by linarith) hy
    simpa only [add_assoc] using hne

set_option maxHeartbeats 800000 in
theorem higher_even_gap_not_distance {k m q i j : Nat}
    (hk : 5 ≤ k) (hm : 0 < m) (heven : k % 2 ≠ 1)
    (hi : 0 < i) (hin : i ≤ q * higherPeriod k m)
    (hj : 0 < j) (hjn : j ≤ q * higherPeriod k m) (hij : i < j)
    (hc : higherColorValue k m i = higherColorValue k m j) :
    ¬ HigherDistance k m q (j - i) ∧
      ¬ HigherDistance k m q (q * higherPeriod k m + 1 - (j - i)) := by
  obtain ⟨a, b, s, t, δ, haq, hbq, hsm, htm, hδ, he⟩ :=
    higher_even_same_color_difference hk hm heven hi hin hj hjn hc
  have hk' : (6 : Int) ≤ k := by omega
  have hm' : (1 : Int) ≤ m := by omega
  have hkm : 6 * (m : Int) ≤ (k : Int) * m :=
    mul_le_mul_of_nonneg_right hk' (by omega)
  have hs : (0 : Int) ≤ s ∧ (s : Int) < m := by exact_mod_cast (And.intro (Nat.zero_le s) hsm)
  have ht : (0 : Int) ≤ t ∧ (t : Int) < m := by exact_mod_cast (And.intro (Nat.zero_le t) htm)
  have hL := higher_even_period_int (m := m) hk heven
  have hLpos : (0 : Int) < higherPeriod k m := by exact_mod_cast higherPeriod_pos hk hm
  have hfwd : ((j - i : Nat) : Int) =
      ((b : Int) - a) * higherPeriod k m + δ + 2 * ((t : Int) - s) := by
    rw [Int.natCast_sub (Nat.le_of_lt hij)]
    exact he
  have hwrap : ((q * higherPeriod k m + 1 - (j - i) : Nat) : Int) =
      ((q : Int) - b + a) * higherPeriod k m - δ + (1 - 2 * ((t : Int) - s)) := by
    rw [Int.natCast_sub (by omega), Int.natCast_add, Int.natCast_mul, hfwd]
    norm_num
    ring
  obtain ⟨af, zf, hzf, hef⟩ := higher_even_normalize_start (a := (b : Int) - a) hk heven hδ
  rw [hef] at hfwd
  have hδneg : -δ = 0 ∨ -δ = ((k : Int) - 2) * m + 1 ∨ -δ = (k : Int) * m - 1 ∨
      -δ = -(((k : Int) - 2) * m + 1) ∨ -δ = -((k : Int) * m - 1) := by
    rcases hδ with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl (by ring)
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
    · exact Or.inr (Or.inl (by ring))
    · exact Or.inr (Or.inr (Or.inl (by ring)))
  obtain ⟨aw, zw, hzw, hew⟩ :=
    higher_even_normalize_start (a := (q : Int) - b + a) hk heven hδneg
  have hwrap' : ((q * higherPeriod k m + 1 - (j - i) : Nat) : Int) =
      aw * higherPeriod k m + zw + (1 - 2 * ((t : Int) - s)) := by
    rw [hwrap, sub_eq_add_neg, hew]
  constructor
  · intro hd
    rcases higher_even_distance_int hk heven hd with ⟨hdpos, hdshort, hdmod⟩ | ⟨b', y, hdy, hy⟩
    · by_cases hz0 : zf = 0
      · have hLtwo : (higherPeriod k m : Int) % 2 = 0 := by
          exact_mod_cast higherPeriod_even (m := m) hk
        have hemod := congrArg (fun z : Int => z % 2) hfwd
        simp [Int.add_emod, Int.mul_emod, hLtwo, hz0] at hemod
        omega
      · have hmid : ((k : Int) - 4) * m + 3 ≤ zf + 2 * ((t : Int) - s) ∧
            zf + 2 * ((t : Int) - s) ≤ ((k : Int) + 2) * m - 2 := by
          rcases hzf with h | rfl | rfl
          · exact False.elim (hz0 h)
          · constructor <;> nlinarith only [hm', hs.1, hs.2, ht.1, ht.2]
          · constructor <;> nlinarith only [hm', hs.1, hs.2, ht.1, ht.2]
        have hne := integer_even_middle_interval_avoids_short (a := af) (b := 0)
          hk' hm' hmid.1 hmid.2 hdpos hdshort
        apply hne
        rw [hL] at hfwd
        simpa only [zero_mul, zero_add, add_assoc] using hfwd.symm
    · have hne := higher_even_normalized_avoids_long (a := af) (b := b') hk hm heven hzf
        (by omega : -2 * (m : Int) + 2 ≤ 2 * ((t : Int) - s))
        (by omega : 2 * ((t : Int) - s) ≤ 2 * (m : Int) - 1) hy
      exact hne (hfwd.symm.trans hdy)
  · intro hd
    rcases higher_even_distance_int hk heven hd with ⟨_, hdshort, _⟩ | ⟨b', y, hdy, hy⟩
    · have hcoef : (1 : Int) ≤ q - b + a := by omega
      have hmul := mul_le_mul_of_nonneg_right hcoef (le_of_lt hLpos)
      have hδbound : δ ≤ (k : Int) * m - 1 := by
        rcases hδ with rfl | rfl | rfl | rfl | rfl <;> nlinarith only [hm', hkm]
      have hLδ : 4 * (m : Int) + 1 ≤ higherPeriod k m - δ := by
        rw [hL]
        nlinarith only [hδbound, hkm]
      linarith
    · have hne := higher_even_normalized_avoids_long (a := aw) (b := b') hk hm heven hzw
        (by omega : -2 * (m : Int) + 2 ≤ 1 - 2 * ((t : Int) - s))
        (by omega : 1 - 2 * ((t : Int) - s) ≤ 2 * (m : Int) - 1) hy
      exact hne (hwrap'.symm.trans hdy)

theorem higher_even_punctured {k m q : Nat} (hk : 5 ≤ k) (hm : 0 < m)
    (heven : k % 2 ≠ 1) :
    ∀ v : ZMod (q * higherPeriod k m + 1),
      ∃ c : ZMod (q * higherPeriod k m + 1) → Fin (k - 1),
        ∀ u w, u ≠ v → w ≠ v → (higherGraph k m q).Adj u w → c u ≠ c w := by
  apply higher_punctured_of_gap_avoidance hk
  intro i j hi hin hj hjn hij hc
  exact higher_even_gap_not_distance hk hm heven hi hin hj hjn hij hc

theorem higher_punctured {k m q : Nat} (hk : 5 ≤ k) (hm : 0 < m) :
    ∀ v : ZMod (q * higherPeriod k m + 1),
      ∃ c : ZMod (q * higherPeriod k m + 1) → Fin (k - 1),
        ∀ u w, u ≠ v → w ≠ v → (higherGraph k m q).Adj u w → c u ≠ c w := by
  by_cases hodd : k % 2 = 1
  · exact higher_odd_punctured hk hm hodd
  · exact higher_even_punctured hk hm hodd

theorem higher_colorable {k m q : Nat} (hk : 5 ≤ k) (hm : 0 < m) :
    (higherGraph k m q).Colorable k := by
  obtain ⟨c, hc⟩ := higher_punctured (q := q) hk hm 0
  have hcol := colorable_succ_of_punctured (higherGraph k m q) 0 c hc
  simpa only [Nat.sub_add_cancel (by omega : 1 ≤ k)] using hcol

theorem higher_delete_vertex_colorable {k m q : Nat} (hk : 5 ≤ k) (hm : 0 < m)
    (v : ZMod (q * higherPeriod k m + 1)) :
    ((⊤ : (higherGraph k m q).Subgraph).deleteVerts {v}).coe.Colorable (k - 1) := by
  obtain ⟨c, hc⟩ := higher_punctured hk hm v
  exact colorable_delete_vertex_of_punctured (higherGraph k m q) v c hc

/-- The remaining obligation for these explicit witnesses is an edge-robustness bound. -/
theorem higher_erdos944_of_badEdges {k m q r : Nat} (hk : 5 ≤ k) (hm : 0 < m)
    (hbad : ∀ c : ZMod (q * higherPeriod k m + 1) → Fin (k - 1),
      r < (badEdges (higherGraph k m q) c).ncard) :
    Erdos944.SimpleGraph.IsErdos944 (higherGraph k m q) k r := by
  have hG := critical_robust_of_punctured (higherGraph k m q) (higher_punctured hk hm) hbad
  simpa only [Nat.sub_add_cancel (by omega : 1 ≤ k)] using hG

theorem equal_window_color_counts_force_period {α : Type*} [DecidableEq α]
    (c : Nat → α) {i L : Nat}
    (hc : windowSum (fun j => if c j = c i then 1 else 0) i L =
      windowSum (fun j => if c j = c i then 1 else 0) (i + 1) L) :
    c (i + L) = c i := by
  have hs := windowSum_shift (fun j => if c j = c i then 1 else 0) i L
  by_contra hne
  simp only [hne, if_false, if_true] at hs
  omega

theorem cyclic_period_dividing_order_pred_is_constant {α : Type*} (q L : Nat)
    (c : ZMod (q * L + 1) → α)
    (hperiod : ∀ v, c (v + (L : ZMod (q * L + 1))) = c v) :
    ∀ v w, c v = c w := by
  have hmul : ∀ t : Nat, ∀ v : ZMod (q * L + 1), c (v + (t * L : Nat)) = c v := by
    intro t
    induction t with
    | zero => intro v; simp
    | succ t ih =>
      intro v
      rw [Nat.succ_mul, Nat.cast_add, ← add_assoc, hperiod, ih]
  have hneg : ((q * L : Nat) : ZMod (q * L + 1)) = -1 := by
    have hz := ZMod.natCast_self (q * L + 1)
    rw [Nat.cast_add, Nat.cast_one] at hz
    exact eq_neg_iff_add_eq_zero.mpr hz
  have hone : ∀ v : ZMod (q * L + 1), c (v + 1) = c v := by
    intro v
    have h := hmul q (v + 1)
    rw [hneg] at h
    have he : v + 1 + -1 = v := by abel
    rw [he] at h
    exact h.symm
  have hnat : ∀ t : Nat, c (t : ZMod (q * L + 1)) = c 0 := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih => simpa only [Nat.cast_add, Nat.cast_one, hone] using ih
  intro v w
  have hv := hnat v.val
  have hw := hnat w.val
  simpa only [ZMod.natCast_zmod_val] using hv.trans hw.symm

theorem higher_cycle_adj {k m q : Nat} (hk : 5 ≤ k) (hm : 0 < m) (hq : 0 < q)
    (v : ZMod (q * higherPeriod k m + 1)) : (higherGraph k m q).Adj v (v + 1) := by
  have hL := higherPeriod_lower (m := m) hk
  have hn : 1 < q * higherPeriod k m + 1 := by nlinarith
  let : Fact (1 < q * higherPeriod k m + 1) := ⟨hn⟩
  refine ⟨?_, Or.inl ?_⟩
  · intro he
    have hz : (1 : ZMod (q * higherPeriod k m + 1)) = 0 := by
      simpa only [add_eq_left] using he.symm
    exact one_ne_zero hz
  · rw [add_sub_cancel_left, ZMod.val_one]
    exact Or.inl ⟨by omega, by omega, by omega⟩

theorem higher_periodic_coloring_has_bad_cycle_edge {α : Type*} {k m q : Nat}
    (hk : 5 ≤ k) (hm : 0 < m) (hq : 0 < q)
    (c : ZMod (q * higherPeriod k m + 1) → α)
    (hperiod : ∀ v, c (v + (higherPeriod k m : ZMod (q * higherPeriod k m + 1))) = c v)
    (v : ZMod (q * higherPeriod k m + 1)) :
    (higherGraph k m q).Adj v (v + 1) ∧ c v = c (v + 1) := by
  exact ⟨higher_cycle_adj hk hm hq v,
    cyclic_period_dividing_order_pred_is_constant q (higherPeriod k m) c hperiod v (v + 1)⟩

/-- A vertex is affected when it is incident to a monochromatic edge. -/
def badVertices {V : Type*} (G : SimpleGraph V) {k : Nat} (c : V → Fin k) : Set V :=
  {v | ∃ w, G.Adj v w ∧ c v = c w}

theorem badVertices_ncard_le {V : Type*} [Finite V] (G : SimpleGraph V)
    {k : Nat} (c : V → Fin k) : (badVertices G c).ncard ≤ 2 * (badEdges G c).ncard := by
  classical
  let : Fintype V := Fintype.ofFinite V
  let E := (badEdges G c).toFinset
  have hsub : (badVertices G c).toFinset ⊆ E.biUnion Sym2.toFinset := by
    intro v hv
    obtain ⟨w, hadj, heq⟩ := Set.mem_toFinset.mp hv
    apply Finset.mem_biUnion.mpr
    refine ⟨s(v, w), Set.mem_toFinset.mpr ⟨v, w, rfl, hadj, heq⟩, ?_⟩
    simp [Sym2.toFinset_mk_eq]
  have hcard : (E.biUnion Sym2.toFinset).card ≤ E.card * 2 := by
    apply Finset.card_biUnion_le_card_mul
    intro e _
    rw [Sym2.card_toFinset]
    split <;> omega
  rw [Set.ncard_eq_toFinset_card', Set.ncard_eq_toFinset_card']
  simpa only [E, Nat.mul_comm] using (Finset.card_le_card hsub).trans hcard

theorem edge_proper_at_unaffected_vertex {V : Type*} (G : SimpleGraph V) {k : Nat}
    (c : V → Fin k) {v w : V} (hv : v ∉ badVertices G c) (hvw : G.Adj v w) :
    c v ≠ c w := by
  exact fun heq => hv ⟨w, hvw, heq⟩

theorem exists_clean_finite_block {V I J : Type*} [Finite V] [Fintype I]
    (B : Set V) (f : I × J → V) (hf : Function.Injective f)
    (hcard : B.ncard < Fintype.card I) : ∃ i : I, ∀ j : J, f (i, j) ∉ B := by
  classical
  let : Fintype B := Fintype.ofFinite B
  by_contra hnone
  have hhit : ∀ i : I, ∃ j : J, f (i, j) ∈ B := by
    simpa only [not_exists, not_forall, not_not] using hnone
  choose j hj using hhit
  let g : I → B := fun i => ⟨f (i, j i), hj i⟩
  have hg : Function.Injective g := by
    intro i i' he
    have hpair := hf (congrArg Subtype.val he)
    exact congrArg Prod.fst hpair
  have hle := Fintype.card_le_of_injective g hg
  rw [Set.fintypeCard_eq_ncard] at hle
  omega

theorem exists_unaffected_finite_block {V I J : Type*} [Finite V] [Fintype I]
    (G : SimpleGraph V) {k r : Nat} (c : V → Fin k)
    (f : I × J → V) (hf : Function.Injective f)
    (hbad : (badEdges G c).ncard ≤ r) (hsize : 2 * r < Fintype.card I) :
    ∃ i : I, ∀ j : J, f (i, j) ∉ badVertices G c := by
  apply exists_clean_finite_block (badVertices G c) f hf
  have hbound := badVertices_ncard_le G c
  omega

theorem cyclic_block_index_injective {n C B : Nat} [NeZero n] (hsize : C * B ≤ n)
    (v : ZMod n) :
    Function.Injective (fun p : Fin C × Fin B => v + ((p.2.val + B * p.1.val : Nat) : ZMod n)) := by
  intro p p' hp
  have hz : (((finProdFinEquiv p).val : Nat) : ZMod n) =
      (((finProdFinEquiv p').val : Nat) : ZMod n) := by
    have he := congrArg (fun z : ZMod n => z - v) hp
    simpa [finProdFinEquiv] using he
  have hv := congrArg ZMod.val hz
  rw [ZMod.val_natCast, ZMod.val_natCast,
    Nat.mod_eq_of_lt ((finProdFinEquiv p).isLt.trans_le hsize),
    Nat.mod_eq_of_lt ((finProdFinEquiv p').isLt.trans_le hsize)] at hv
  exact finProdFinEquiv.injective (Fin.ext hv)

theorem exists_unaffected_cyclic_block {n B p r : Nat} [NeZero n]
    (G : SimpleGraph (ZMod n)) (c : ZMod n → Fin p)
    (hbad : (badEdges G c).ncard ≤ r) (hfit : (2 * r + 1) * B ≤ n) (v : ZMod n) :
    ∃ a : Fin (2 * r + 1), ∀ j : Fin B,
      v + ((j.val + B * a.val : Nat) : ZMod n) ∉ badVertices G c := by
  apply exists_unaffected_finite_block G c _ (cyclic_block_index_injective hfit v) hbad
  simp only [Fintype.card_fin]
  omega

theorem higher_exists_unaffected_block {k m p r : Nat}
    (c : ZMod ((24 * r + 12) * higherPeriod k m + 1) → Fin p)
    (hbad : (badEdges (higherGraph k m (24 * r + 12)) c).ncard ≤ r)
    (v : ZMod ((24 * r + 12) * higherPeriod k m + 1)) :
    ∃ a : Nat, a + 3 * higherPeriod k m ≤ (6 * r + 3) * higherPeriod k m ∧
      ∀ j : Nat, j < 3 * higherPeriod k m →
        v + ((a + j : Nat) : ZMod ((24 * r + 12) * higherPeriod k m + 1)) ∉
          badVertices (higherGraph k m (24 * r + 12)) c := by
  have hfit : (2 * r + 1) * (3 * higherPeriod k m) ≤
      (24 * r + 12) * higherPeriod k m + 1 := by nlinarith
  obtain ⟨a, ha⟩ := exists_unaffected_cyclic_block
    (higherGraph k m (24 * r + 12)) c hbad hfit v
  refine ⟨3 * higherPeriod k m * a.val, ?_, ?_⟩
  · have hle := Nat.mul_le_mul_left (3 * higherPeriod k m) a.isLt
    nlinarith
  · intro j hj
    simpa only [Nat.add_comm] using ha ⟨j, hj⟩

/-- A local color constraint sufficient for the robustness proof.
The window has `(6*r+3)*L` vertices and contains a clean block of length `3*L`.
The graph order is `(24*r+12)*L+1`. -/
def HigherLocalPropagation (k m r : Nat) : Prop :=
  ∀ c : ZMod ((24 * r + 12) * higherPeriod k m + 1) → Fin (k - 1),
    (badEdges (higherGraph k m (24 * r + 12)) c).ncard ≤ r →
    ∀ v : ZMod ((24 * r + 12) * higherPeriod k m + 1), ∀ a : Nat,
      a + 3 * higherPeriod k m ≤ (6 * r + 3) * higherPeriod k m →
      (∀ j : Nat, j < 3 * higherPeriod k m →
        v + ((a + j : Nat) : ZMod ((24 * r + 12) * higherPeriod k m + 1)) ∉
          badVertices (higherGraph k m (24 * r + 12)) c) →
      c (v + (higherPeriod k m : ZMod ((24 * r + 12) * higherPeriod k m + 1))) = c v

theorem higher_badEdges_bound_of_local_propagation {k m r : Nat}
    (hk : 5 ≤ k) (hm : 0 < m) (hlocal : HigherLocalPropagation k m r) :
    ∀ c : ZMod ((24 * r + 12) * higherPeriod k m + 1) → Fin (k - 1),
      r < (badEdges (higherGraph k m (24 * r + 12)) c).ncard := by
  intro c
  by_contra hnone
  have hbad : (badEdges (higherGraph k m (24 * r + 12)) c).ncard ≤ r := by omega
  have hperiod : ∀ v : ZMod ((24 * r + 12) * higherPeriod k m + 1),
      c (v + (higherPeriod k m : ZMod ((24 * r + 12) * higherPeriod k m + 1))) = c v := by
    intro v
    obtain ⟨a, ha, hclean⟩ := higher_exists_unaffected_block c hbad v
    exact hlocal c hbad v a ha hclean
  obtain ⟨a, _, hclean⟩ := higher_exists_unaffected_block c hbad 0
  have hL := higherPeriod_pos hk hm
  have ha := hclean 0 (by omega)
  simp only [Nat.add_zero, zero_add] at ha
  obtain ⟨hadj, heq⟩ := higher_periodic_coloring_has_bad_cycle_edge hk hm
    (by omega : 0 < 24 * r + 12) c hperiod (a : ZMod ((24 * r + 12) * higherPeriod k m + 1))
  exact ha ⟨_, hadj, heq⟩

theorem higher_erdos944_of_local_propagation {k m r : Nat}
    (hk : 5 ≤ k) (hm : 0 < m) (hlocal : HigherLocalPropagation k m r) :
    Erdos944.SimpleGraph.IsErdos944 (higherGraph k m (24 * r + 12)) k r := by
  exact higher_erdos944_of_badEdges hk hm (higher_badEdges_bound_of_local_propagation hk hm hlocal)

/-
## Local periodicity in the higher-color construction

The clique and ten-vertex counting arguments below formalize Claim 4.4
of Skottová and Steiner, arXiv:2508.08703v1. The two-color-option result
formalizes the odd case of Claim 4.8. The proof of Claim 4.9 here uses an
unaffected vertex in a color class of size greater than 2*r. The local
structure and the full propagation argument are proved below.
-/

theorem higher_distance_adj {k m q d : Nat} (hdpos : 0 < d)
    (hdlt : d < q * higherPeriod k m + 1) (hd : HigherDistance k m q d)
    (v : ZMod (q * higherPeriod k m + 1)) :
    (higherGraph k m q).Adj v (v + (d : ZMod (q * higherPeriod k m + 1))) := by
  have hval : (d : ZMod (q * higherPeriod k m + 1)).val = d := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hdlt]
  refine ⟨?_, Or.inl ?_⟩
  · intro he
    have hz : (d : ZMod (q * higherPeriod k m + 1)) = 0 := by
      simpa only [add_eq_left] using he.symm
    have hv := congrArg ZMod.val hz
    rw [hval, ZMod.val_zero] at hv
    omega
  · simpa only [add_sub_cancel_left, hval] using hd

theorem higher_adj_nat_indices {k m q i j : Nat} (hij : i < j)
    (hjn : j < q * higherPeriod k m + 1) (hd : HigherDistance k m q (j - i))
    (v : ZMod (q * higherPeriod k m + 1)) :
    (higherGraph k m q).Adj (v + (i : ZMod (q * higherPeriod k m + 1)))
      (v + (j : ZMod (q * higherPeriod k m + 1))) := by
  have he : v + (j : ZMod (q * higherPeriod k m + 1)) =
      (v + (i : ZMod (q * higherPeriod k m + 1))) + (j - i : Nat) := by
    rw [Nat.cast_sub (Nat.le_of_lt hij)]
    abel
  rw [he]
  exact higher_distance_adj (by omega) (by omega) hd _

/-- The distance constraints on a finite interval, without choosing its cyclic origin. -/
def HigherProperOn {α : Type*} (k m q : Nat) (c : Nat → α) (len : Nat) : Prop :=
  ∀ i j : Nat, i < j → j < len → HigherDistance k m q (j - i) → c i ≠ c j

theorem higherProperOn_of_clean {k m q p len : Nat}
    (c : ZMod (q * higherPeriod k m + 1) → Fin p)
    (v : ZMod (q * higherPeriod k m + 1)) (hlen : len ≤ q * higherPeriod k m + 1)
    (hclean : ∀ j : Nat, j < len →
      v + (j : ZMod (q * higherPeriod k m + 1)) ∉ badVertices (higherGraph k m q) c) :
    HigherProperOn k m q (fun j => c (v + (j : ZMod (q * higherPeriod k m + 1)))) len := by
  intro i j hij hj hd
  exact edge_proper_at_unaffected_vertex (higherGraph k m q) c
    (hclean i (by omega)) (higher_adj_nat_indices hij (hj.trans_le hlen) hd v)

theorem higherProperOn_shift {α : Type*} {k m q a len len' : Nat} {c : Nat → α}
    (hc : HigherProperOn k m q c len) (ha : a + len' ≤ len) :
    HigherProperOn k m q (fun j => c (a + j)) len' := by
  intro i j hij hj hd
  apply hc (a + i) (a + j) (by omega) (by omega)
  simpa only [Nat.add_sub_add_left] using hd

/-- Fixing `s` gives one clique; fixing `a` gives a color class in the model coloring. -/
def higherPairedIndex (m s a : Nat) : Nat :=
  2 * m * (a / 2) + 2 * s + a % 2

theorem higherPairedIndex_strictMono {m s : Nat} (hm : 0 < m) :
    StrictMono (higherPairedIndex m s) := by
  intro a b hab
  have ha := Nat.mod_add_div a 2
  have hb := Nat.mod_add_div b 2
  have harem := Nat.mod_lt a (by omega : 0 < 2)
  have hbrem := Nat.mod_lt b (by omega : 0 < 2)
  by_cases hdiv : a / 2 = b / 2
  · have hbits : a % 2 < b % 2 := by omega
    unfold higherPairedIndex
    rw [hdiv]
    omega
  · have hrows : a / 2 + 1 ≤ b / 2 := by omega
    have hmul := Nat.mul_le_mul_left (2 * m) hrows
    unfold higherPairedIndex
    nlinarith only [hm, hmul, harem, hbrem, Nat.zero_le (a % 2), Nat.zero_le (b % 2)]

theorem higherPairedIndex_rowCode {m s a : Nat} (hm : 0 < m) (hs : s < m) :
    higherRowCode m (higherPairedIndex m s a) = a := by
  have hrem : 2 * s + a % 2 < 2 * m := by omega
  have hform : higherPairedIndex m s a = (2 * s + a % 2) + (2 * m) * (a / 2) := by
    unfold higherPairedIndex
    ring
  have hdiv : higherPairedIndex m s a / (2 * m) = a / 2 := by
    rw [hform, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hrem, zero_add]
  have hmod : higherPairedIndex m s a % (2 * m) = 2 * s + a % 2 := by
    have he := Nat.mod_add_div (higherPairedIndex m s a) (2 * m)
    rw [hdiv] at he
    nlinarith only [he, hform]
  unfold higherRowCode
  rw [hdiv, hmod]
  omega

theorem higherPairedIndex_lt_period {k m s a : Nat} (hk : 5 ≤ k) (_hm : 0 < m)
    (hodd : k % 2 = 1) (hs : s < m) (ha : a < k - 1) :
    higherPairedIndex m s a < higherPeriod k m := by
  have hc : (k - 1) % 2 = 0 := by omega
  have hrows : 2 * (a / 2) + 2 ≤ k - 1 := by omega
  have hmul := Nat.mul_le_mul_right m hrows
  have hrem : 2 * s + a % 2 < 2 * m := by omega
  simp only [higherPeriod, hodd, if_true]
  unfold higherPairedIndex
  nlinarith only [hmul, hrem]

theorem higherPairedIndex_injective {m c : Nat} (hm : 0 < m) :
    Function.Injective (fun p : Fin m × Fin c => higherPairedIndex m p.1.val p.2.val) := by
  intro p p' he
  have hc := congrArg (higherRowCode m) he
  rw [higherPairedIndex_rowCode hm p.1.isLt,
    higherPairedIndex_rowCode hm p'.1.isLt] at hc
  have hcolor : p.2 = p'.2 := Fin.ext hc
  have hs : p.1 = p'.1 := by
    apply Fin.ext
    dsimp only [higherPairedIndex] at he
    rw [hc] at he
    omega
  exact Prod.ext hs hcolor

theorem higherPairedIndex_surjective {k m : Nat} (hk : 5 ≤ k) (hm : 0 < m)
    (hodd : k % 2 = 1) (x : Fin (higherPeriod k m)) :
    ∃ p : Fin m × Fin (k - 1), higherPairedIndex m p.1.val p.2.val = x.val := by
  obtain ⟨t, s, b, hs, hb, hx, hc⟩ := higher_row_decomposition (x := x.val) hm
  have ha := higher_rowCode_bound hk hm x.isLt
  rw [hc] at ha
  simp only [hodd, if_true] at ha
  refine ⟨(⟨s, hs⟩, ⟨2 * t + b, ha⟩), ?_⟩
  have hdiv : (2 * t + b) / 2 = t := by omega
  have hmod : (2 * t + b) % 2 = b := by omega
  change higherPairedIndex m s (2 * t + b) = _
  simp only [higherPairedIndex, hdiv, hmod]
  exact hx.symm

noncomputable def higherOddPeriodEquiv {k m : Nat} (hk : 5 ≤ k) (hm : 0 < m)
    (hodd : k % 2 = 1) : Fin m × Fin (k - 1) ≃ Fin (higherPeriod k m) :=
  Equiv.ofBijective
    (fun p => ⟨higherPairedIndex m p.1.val p.2.val,
      higherPairedIndex_lt_period hk hm hodd p.1.isLt p.2.isLt⟩)
    ⟨fun _ _ h => higherPairedIndex_injective hm (congrArg Fin.val h),
      fun x => by
        obtain ⟨p, hp⟩ := higherPairedIndex_surjective hk hm hodd x
        exact ⟨p, Fin.ext hp⟩⟩

theorem higher_odd_clique_distance {k m q s a b : Nat}
    (hk : 5 ≤ k) (hm : 0 < m) (hq : 2 ≤ q) (hodd : k % 2 = 1)
    (hab : a < b) (hb : b < k - 1) :
    HigherDistance k m q (higherPairedIndex m s b - higherPairedIndex m s a) := by
  have hi := higherPairedIndex_strictMono (s := s) hm hab
  have hsub : higherPairedIndex m s b - higherPairedIndex m s a + higherPairedIndex m s a =
      higherPairedIndex m s b := Nat.sub_add_cancel (Nat.le_of_lt hi)
  have hba : a % 2 < 2 := Nat.mod_lt _ (by omega)
  have hbb : b % 2 < 2 := Nat.mod_lt _ (by omega)
  have hrows : a / 2 ≤ b / 2 := by omega
  have he : higherPairedIndex m s b + 2 * m * (a / 2) + a % 2 =
      higherPairedIndex m s a + 2 * m * (b / 2) + b % 2 := by
    unfold higherPairedIndex
    ring
  by_cases hroweq : a / 2 = b / 2
  · have hbits : a % 2 = 0 ∧ b % 2 = 1 := by omega
    have hd : higherPairedIndex m s b - higherPairedIndex m s a = 1 := by
      rw [hroweq, hbits.1, hbits.2] at he
      omega
    rw [hd]
    exact Or.inl ⟨by omega, by omega, by omega⟩
  · have hrows' : a / 2 + 1 ≤ b / 2 := by omega
    have hstep := Nat.mul_le_mul_left (2 * m) hrows'
    have hlow : 2 * m ≤ higherPairedIndex m s b - higherPairedIndex m s a + 1 := by
      nlinarith only [hsub, he, hstep, hba, Nat.zero_le (b % 2)]
    have hdiff : 2 * m - 1 ≤ higherPairedIndex m s b - higherPairedIndex m s a := by omega
    by_cases hshort : higherPairedIndex m s b - higherPairedIndex m s a < 2 * m
    · exact Or.inl ⟨by omega, hshort, by omega⟩
    · right; left
      refine ⟨0, by omega, by simpa using Nat.le_of_not_gt hshort, ?_⟩
      simp only [zero_mul, zero_add, hodd, if_true]
      have hbrows : 2 * (b / 2) ≤ k - 3 := by omega
      have hmax := Nat.mul_le_mul_right m hbrows
      have hamin : 0 ≤ 2 * m * (a / 2) := Nat.zero_le _
      nlinarith only [hsub, he, hmax, hamin, hbb, Nat.zero_le (a % 2)]

theorem higher_odd_clique_coloring_injective {k m q : Nat} (hk : 5 ≤ k) (hm : 0 < m)
    (hq : 2 ≤ q) (hodd : k % 2 = 1) {c : Nat → Fin (k - 1)}
    (hc : HigherProperOn k m q c (higherPeriod k m)) (s : Fin m) :
    Function.Injective (fun a : Fin (k - 1) => c (higherPairedIndex m s.val a.val)) := by
  intro a b he
  by_contra hab
  have hval : a.val ≠ b.val := fun h => hab (Fin.ext h)
  rcases lt_or_gt_of_ne hval with h | h
  · exact hc _ _ (higherPairedIndex_strictMono hm h)
      (higherPairedIndex_lt_period hk hm hodd s.isLt b.isLt)
      (higher_odd_clique_distance hk hm hq hodd h b.isLt) he
  · exact hc _ _ (higherPairedIndex_strictMono hm h)
      (higherPairedIndex_lt_period hk hm hodd s.isLt a.isLt)
      (higher_odd_clique_distance hk hm hq hodd h a.isLt) he.symm

theorem finite_injective_indicator_sum {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → α) (hf : Function.Injective f) (a : α) :
    (∑ b : α, if f b = a then (1 : Int) else 0) = 1 := by
  have hbij : Function.Bijective f := ⟨hf, Finite.surjective_of_injective hf⟩
  rw [hbij.sum_comp (fun b => if b = a then (1 : Int) else 0)]
  simp

theorem higher_odd_period_color_sum {k m q : Nat} (hk : 5 ≤ k) (hm : 0 < m)
    (hq : 2 ≤ q) (hodd : k % 2 = 1) {c : Nat → Fin (k - 1)}
    (hc : HigherProperOn k m q c (higherPeriod k m)) (a : Fin (k - 1)) :
    (∑ j : Fin (higherPeriod k m), if c j.val = a then (1 : Int) else 0) = m := by
  have he := (higherOddPeriodEquiv hk hm hodd).sum_comp
    (fun j => if c j.val = a then (1 : Int) else 0)
  rw [← he, Fintype.sum_prod_type]
  change (∑ s : Fin m, ∑ b : Fin (k - 1),
    if c (higherPairedIndex m s.val b.val) = a then (1 : Int) else 0) = m
  have hsum (s : Fin m) : (∑ b : Fin (k - 1),
      if c (higherPairedIndex m s.val b.val) = a then (1 : Int) else 0) = 1 :=
    finite_injective_indicator_sum _ (higher_odd_clique_coloring_injective hk hm hq hodd hc s) a
  simp only [hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

theorem higher_odd_window_color_count {k m q len : Nat} (hk : 5 ≤ k) (hm : 0 < m)
    (hq : 2 ≤ q) (hodd : k % 2 = 1) {c : Nat → Fin (k - 1)}
    (hc : HigherProperOn k m q c len) {i : Nat} (hi : i + higherPeriod k m ≤ len)
    (a : Fin (k - 1)) :
    windowSum (fun j => if c j = a then (1 : Int) else 0) i (higherPeriod k m) = m := by
  have hs := higher_odd_period_color_sum hk hm hq hodd (higherProperOn_shift hc hi) a
  unfold windowSum
  rw [partialSum_eq_sum_range, ← Fin.sum_univ_eq_sum_range]
  exact hs

theorem higher_odd_local_periodicity {k m q : Nat} (hk : 5 ≤ k) (hm : 0 < m)
    (hq : 2 ≤ q) (hodd : k % 2 = 1) {c : Nat → Fin (k - 1)}
    (hc : HigherProperOn k m q c (3 * higherPeriod k m)) {i : Nat}
    (hi : i < 2 * higherPeriod k m) : c (i + higherPeriod k m) = c i := by
  have h₁ := higher_odd_window_color_count hk hm hq hodd hc
    (i := i) (by omega) (c i)
  have h₂ := higher_odd_window_color_count hk hm hq hodd hc
    (i := i + 1) (by omega) (c i)
  exact equal_window_color_counts_force_period c (h₁.trans h₂.symm)

theorem higher_odd_clean_block_periodic {k m q : Nat} (hk : 5 ≤ k) (hm : 0 < m)
    (hq : 3 ≤ q) (hodd : k % 2 = 1)
    (c : ZMod (q * higherPeriod k m + 1) → Fin (k - 1))
    (v : ZMod (q * higherPeriod k m + 1))
    (hclean : ∀ j : Nat, j < 3 * higherPeriod k m →
      v + (j : ZMod (q * higherPeriod k m + 1)) ∉ badVertices (higherGraph k m q) c)
    {i : Nat} (hi : i < 2 * higherPeriod k m) :
    c (v + ((i + higherPeriod k m : Nat) : ZMod (q * higherPeriod k m + 1))) =
      c (v + (i : ZMod (q * higherPeriod k m + 1))) := by
  have hlen : 3 * higherPeriod k m ≤ q * higherPeriod k m + 1 :=
    (Nat.mul_le_mul_right (higherPeriod k m) hq).trans (Nat.le_succ _)
  exact higher_odd_local_periodicity hk hm (by omega) hodd
    (higherProperOn_of_clean c v hlen hclean) hi

/-- Replace every vertex of a five-cycle by an adjacent pair. -/
def FivePairAdjacent (a b : Fin 5 × Fin 2) : Prop :=
  a ≠ b ∧ (a.1 = b.1 ∨ Nat.dist a.1.val b.1.val = 1 ∨ Nat.dist a.1.val b.1.val = 4)

theorem five_pairs_three_have_edge : ∀ a b c : Fin 5 × Fin 2,
    a ≠ b → a ≠ c → b ≠ c →
      FivePairAdjacent a b ∨ FivePairAdjacent a c ∨ FivePairAdjacent b c := by
  simp only [Prod.forall, FivePairAdjacent]
  decide

theorem five_pair_color_class_card_le_two {α : Type*} [DecidableEq α]
    (φ : Fin 5 × Fin 2 → α)
    (hφ : ∀ a b, FivePairAdjacent a b → φ a ≠ φ b) (color : α) :
    (Finset.univ.filter (fun a => φ a = color)).card ≤ 2 := by
  by_contra hnone
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ :=
    Finset.two_lt_card_iff.mp (show 2 < (Finset.univ.filter (fun a => φ a = color)).card by omega)
  have ha' := (Finset.mem_filter.mp ha).2
  have hb' := (Finset.mem_filter.mp hb).2
  have hc' := (Finset.mem_filter.mp hc).2
  rcases five_pairs_three_have_edge a b c hab hac hbc with h | h | h
  · exact hφ a b h (ha'.trans hb'.symm)
  · exact hφ a c h (ha'.trans hc'.symm)
  · exact hφ b c h (hb'.trans hc'.symm)

theorem five_pair_color_indicator_sum_le_two {α : Type*} [DecidableEq α]
    (φ : Fin 5 × Fin 2 → α)
    (hφ : ∀ a b, FivePairAdjacent a b → φ a ≠ φ b) (color : α) :
    (∑ a : Fin 5 × Fin 2, if φ a = color then (1 : Int) else 0) ≤ 2 := by
  rw [Finset.sum_boole]
  exact_mod_cast five_pair_color_class_card_le_two φ hφ color

/-- The five pair offsets, with `T=(k-4)*m` in the circulant application. -/
def fivePairBase (m T : Nat) (a : Fin 5) : Nat :=
  match a.val with
  | 0 => 0
  | 1 => T
  | 2 => T + 2 * m
  | 3 => T + 4 * m
  | _ => 2 * T + 4 * m

def fivePairIndex (m T s : Nat) (a : Fin 5 × Fin 2) : Nat :=
  fivePairBase m T a.1 + 2 * s + a.2.val

set_option maxHeartbeats 800000 in
theorem fivePairIndex_gap_cases (m T s : Nat) (a b : Fin 5 × Fin 2)
    (hab : FivePairAdjacent a b) :
    let d := Nat.dist (fivePairIndex m T s a) (fivePairIndex m T s b)
    d = 1 ∨ (2 * m - 1 ≤ d ∧ d ≤ 2 * m + 1) ∨
      (T - 1 ≤ d ∧ d ≤ T + 1) ∨ (2 * T + 4 * m - 1 ≤ d ∧ d ≤ 2 * T + 4 * m + 1) := by
  rcases a with ⟨a, u⟩
  rcases b with ⟨b, v⟩
  fin_cases a <;> fin_cases b <;> fin_cases u <;> fin_cases v <;>
    norm_num [FivePairAdjacent, Nat.dist] at hab
  all_goals
    simp only [fivePairIndex, fivePairBase, Nat.dist]
    omega

theorem fivePairIndex_lt {m s : Nat} (_hm : 0 < m) (hs : s < m) (T : Nat)
    (a : Fin 5 × Fin 2) : fivePairIndex m T s a < 2 * T + 6 * m := by
  rcases a with ⟨a, b⟩
  have hb := b.isLt
  fin_cases a <;> simp only [fivePairIndex, fivePairBase] <;> omega

theorem fivePairIndex_dist_pos {m T s : Nat} (hm : 0 < m) (hT : 2 * m ≤ T)
    {a b : Fin 5 × Fin 2} (hab : FivePairAdjacent a b) :
    0 < Nat.dist (fivePairIndex m T s a) (fivePairIndex m T s b) := by
  rcases fivePairIndex_gap_cases m T s a b hab with h | h | h | h <;> omega

theorem higher_even_width_identity {k m : Nat} (hk : 5 ≤ k) (heven : k % 2 ≠ 1) :
    2 * ((k - 4) * m) + 6 * m = higherPeriod k m := by
  have hK : 2 * (k - 4) + 6 = 2 * (k - 1) := by omega
  simp only [higherPeriod, heven, if_false]
  calc
    2 * ((k - 4) * m) + 6 * m = (2 * (k - 4) + 6) * m := by ring
    _ = 2 * (k - 1) * m := by rw [hK]

theorem higher_even_width_lower {k m : Nat} (hk : 5 ≤ k) (heven : k % 2 ≠ 1) :
    2 * m ≤ (k - 4) * m := by
  have hK : 2 ≤ k - 4 := by omega
  exact Nat.mul_le_mul_right m hK

theorem higher_even_first_distance_band {k m q d : Nat} (hm : 0 < m) (hq : 2 ≤ q)
    (heven : k % 2 ≠ 1) (hlo : 2 * m - 1 ≤ d) (hhi : d ≤ (k - 4) * m + 1) :
    HigherDistance k m q d := by
  by_cases hshort : d < 2 * m
  · exact Or.inl ⟨by omega, hshort, by omega⟩
  · refine Or.inr (Or.inl ⟨0, by omega, by simpa using Nat.le_of_not_gt hshort, ?_⟩)
    simp only [zero_mul, zero_add, heven, if_false]
    omega

theorem higher_even_aux_distance {k m q s : Nat} (hk : 5 ≤ k) (hm : 0 < m)
    (hq : 2 ≤ q) (heven : k % 2 ≠ 1) {a b : Fin 5 × Fin 2}
    (hab : FivePairAdjacent a b) :
    HigherDistance k m q (Nat.dist (fivePairIndex m ((k - 4) * m) s a)
      (fivePairIndex m ((k - 4) * m) s b)) := by
  have hT := higher_even_width_lower (m := m) hk heven
  rcases fivePairIndex_gap_cases m ((k - 4) * m) s a b hab with h | h | h | h
  · rw [h]
    exact Or.inl ⟨by omega, by omega, by omega⟩
  · exact higher_even_first_distance_band hm hq heven h.1 (by omega)
  · exact higher_even_first_distance_band hm hq heven (by omega) h.2
  · refine Or.inr (Or.inr ⟨heven, 0, by omega, ?_, ?_⟩)
    · simp only [zero_mul, zero_add]
      have hK : k + 2 = (k - 4) + 6 := by omega
      rw [hK, Nat.add_mul]
      omega
    · simp only [zero_mul, zero_add]
      have hK : 2 * k - 4 = 2 * (k - 4) + 4 := by omega
      rw [hK, Nat.add_mul, Nat.mul_assoc]
      exact h.2

theorem higher_even_aux_color_proper {α : Type*} {k m q s : Nat}
    (hk : 5 ≤ k) (hm : 0 < m) (hq : 2 ≤ q) (heven : k % 2 ≠ 1)
    {c : Nat → α} (hc : HigherProperOn k m q c (higherPeriod k m)) (hs : s < m) :
    ∀ a b : Fin 5 × Fin 2, FivePairAdjacent a b →
      c (fivePairIndex m ((k - 4) * m) s a) ≠ c (fivePairIndex m ((k - 4) * m) s b) := by
  intro a b hab
  have hdist := higher_even_aux_distance (s := s) hk hm hq heven hab
  have hpos := fivePairIndex_dist_pos (s := s) hm (higher_even_width_lower (m := m) hk heven) hab
  have ha := fivePairIndex_lt hm hs ((k - 4) * m) a
  have hb := fivePairIndex_lt hm hs ((k - 4) * m) b
  rw [higher_even_width_identity hk heven] at ha hb
  rcases lt_trichotomy (fivePairIndex m ((k - 4) * m) s a)
      (fivePairIndex m ((k - 4) * m) s b) with h | h | h
  · rw [Nat.dist_eq_sub_of_le (Nat.le_of_lt h)] at hdist
    exact hc _ _ h hb hdist
  · rw [h, Nat.dist_self] at hpos
    omega
  · rw [Nat.dist_eq_sub_of_le_right (Nat.le_of_lt h)] at hdist
    exact (hc _ _ h ha hdist).symm

theorem higher_even_aux_color_sum_le_two {α : Type*} [DecidableEq α] {k m q s : Nat}
    (hk : 5 ≤ k) (hm : 0 < m) (hq : 2 ≤ q) (heven : k % 2 ≠ 1)
    {c : Nat → α} (hc : HigherProperOn k m q c (higherPeriod k m)) (hs : s < m) (color : α) :
    (∑ a : Fin 5 × Fin 2,
      if c (fivePairIndex m ((k - 4) * m) s a) = color then (1 : Int) else 0) ≤ 2 := by
  exact five_pair_color_indicator_sum_le_two _ (higher_even_aux_color_proper hk hm hq heven hc hs) color

theorem two_stride_interval_decomposition {m base j : Nat} (hlo : base ≤ j)
    (hhi : j < base + 2 * m) :
    ∃ s : Fin m, ∃ b : Fin 2, base + 2 * s.val + b.val = j := by
  refine ⟨⟨(j - base) / 2, by omega⟩, ⟨(j - base) % 2, Nat.mod_lt _ (by omega)⟩, ?_⟩
  dsimp only
  omega

theorem fivePairIndex_cover {m T j : Nat}
    (hj : j < 2 * m ∨ (T ≤ j ∧ j < T + 6 * m) ∨
      (2 * T + 4 * m ≤ j ∧ j < 2 * T + 6 * m)) :
    ∃ p : Fin m × (Fin 5 × Fin 2), fivePairIndex m T p.1.val p.2 = j := by
  have hcover (a : Fin 5) (hlo : fivePairBase m T a ≤ j)
      (hhi : j < fivePairBase m T a + 2 * m) :
      ∃ p : Fin m × (Fin 5 × Fin 2), fivePairIndex m T p.1.val p.2 = j := by
    obtain ⟨s, b, he⟩ := two_stride_interval_decomposition hlo hhi
    exact ⟨(s, (a, b)), he⟩
  rcases hj with hj | ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩
  · exact hcover 0 (by simp [fivePairBase]) (by simpa [fivePairBase] using hj)
  · by_cases h₁ : j < T + 2 * m
    · exact hcover 1 (by simpa [fivePairBase] using hlo) (by simpa [fivePairBase] using h₁)
    · by_cases h₂ : j < T + 4 * m
      · apply hcover 2
        · change T + 2 * m ≤ j
          omega
        · change j < T + 2 * m + 2 * m
          omega
      · apply hcover 3
        · change T + 4 * m ≤ j
          omega
        · change j < T + 4 * m + 2 * m
          omega
  · apply hcover 4
    · exact hlo
    · change j < 2 * T + 4 * m + 2 * m
      omega

theorem higher_even_anchored_color_cover {α : Type*} {k m q : Nat}
    (hk : 5 ≤ k) (hm : 0 < m) (hq : 2 ≤ q) (heven : k % 2 ≠ 1)
    {c : Nat → α} (hc : HigherProperOn k m q c (higherPeriod k m))
    {j : Nat} (hj : j < higherPeriod k m) (hcolor : c j = c 0) :
    ∃ p : Fin m × (Fin 5 × Fin 2), fivePairIndex m ((k - 4) * m) p.1.val p.2 = j := by
  let T := (k - 4) * m
  have hL : higherPeriod k m = 2 * T + 6 * m := (higher_even_width_identity hk heven).symm
  apply fivePairIndex_cover
  by_cases hsmall : j < 2 * m
  · exact Or.inl hsmall
  have hnot : ¬ HigherDistance k m q j := by
    intro hd
    exact hc 0 j (by omega) hj (by simpa only [Nat.sub_zero] using hd) hcolor.symm
  by_cases hlo : T ≤ j
  · by_cases hhi : j < T + 6 * m
    · exact Or.inr (Or.inl ⟨hlo, hhi⟩)
    · by_cases hhigh : 2 * T + 4 * m ≤ j
      · exact Or.inr (Or.inr ⟨hhigh, by omega⟩)
      · exfalso
        apply hnot
        refine Or.inr (Or.inr ⟨heven, 0, by omega, ?_, ?_⟩)
        · simp only [zero_mul, zero_add]
          have hK : k + 2 = (k - 4) + 6 := by omega
          rw [hK, Nat.add_mul]
          change T + 6 * m - 1 ≤ j
          omega
        · simp only [zero_mul, zero_add]
          have hK : 2 * k - 4 = 2 * (k - 4) + 4 := by omega
          rw [hK, Nat.add_mul, Nat.mul_assoc]
          change j ≤ 2 * T + 4 * m + 1
          omega
  · exact False.elim (hnot (higher_even_first_distance_band hm hq heven (by omega) (by omega)))

theorem higher_even_anchored_color_card_le {α : Type*} [DecidableEq α] {k m q : Nat}
    (hk : 5 ≤ k) (hm : 0 < m) (hq : 2 ≤ q) (heven : k % 2 ≠ 1)
    {c : Nat → α} (hc : HigherProperOn k m q c (higherPeriod k m)) :
    (Finset.univ.filter (fun j : Fin (higherPeriod k m) => c j.val = c 0)).card ≤ 2 * m := by
  classical
  let A := Finset.univ.filter (fun j : Fin (higherPeriod k m) => c j.val = c 0)
  let B := Finset.univ.filter (fun p : Fin m × (Fin 5 × Fin 2) =>
    c (fivePairIndex m ((k - 4) * m) p.1.val p.2) = c 0)
  let f : Fin m × (Fin 5 × Fin 2) → Fin (higherPeriod k m) := fun p =>
    ⟨fivePairIndex m ((k - 4) * m) p.1.val p.2,
      by simpa only [higher_even_width_identity hk heven] using
        fivePairIndex_lt hm p.1.isLt ((k - 4) * m) p.2⟩
  have hAB : A ⊆ B.image f := by
    intro j hj
    have hcolor := (Finset.mem_filter.mp hj).2
    obtain ⟨p, hp⟩ := higher_even_anchored_color_cover hk hm hq heven hc j.isLt hcolor
    apply Finset.mem_image.mpr
    refine ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, Fin.ext hp⟩
    rw [hp]
    exact hcolor
  have hsum : (∑ p : Fin m × (Fin 5 × Fin 2),
      if c (fivePairIndex m ((k - 4) * m) p.1.val p.2) = c 0 then (1 : Int) else 0) ≤ 2 * m := by
    rw [Fintype.sum_prod_type]
    have hle := Finset.sum_le_sum (s := Finset.univ) (fun s (_ : s ∈ (Finset.univ : Finset (Fin m))) =>
      higher_even_aux_color_sum_le_two hk hm hq heven hc s.isLt (c 0))
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm] using hle
  have hcard : B.card ≤ 2 * m := by
    rw [Finset.sum_boole] at hsum
    exact_mod_cast hsum
  exact (Finset.card_le_card hAB).trans ((Finset.card_image_le).trans hcard)

theorem higherProperOn_reverse {α : Type*} {k m q last len span : Nat} {c : Nat → α}
    (hc : HigherProperOn k m q c len) (hlast : last < len) (hspan : span ≤ last + 1) :
    HigherProperOn k m q (fun j => c (last - j)) span := by
  intro i j hij hj hd
  have he : last - i - (last - j) = j - i := by omega
  exact (hc (last - j) (last - i) (by omega) (by omega) (he.symm ▸ hd)).symm

theorem finite_fiber_card_le_of_injOn {α β γ : Type*} [Fintype α] [Fintype β]
    [DecidableEq β] [DecidableEq γ] (c : α → γ) (d : β → γ) (color : γ)
    (f : α → β) (B : Nat)
    (hbound : (Finset.univ.filter (fun b => d b = color)).card ≤ B)
    (hmap : ∀ a, c a = color → d (f a) = color)
    (hinj : Set.InjOn f {a | c a = color}) :
    (Finset.univ.filter (fun a => c a = color)).card ≤ B := by
  let A := Finset.univ.filter (fun a => c a = color)
  have hf : Set.InjOn f A := by
    intro a ha b hb he
    exact hinj (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2 he
  have hsub : A.image f ⊆ Finset.univ.filter (fun b => d b = color) := by
    intro b hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmap a (Finset.mem_filter.mp ha).2⟩
  calc
    A.card = (A.image f).card := (Finset.card_image_of_injOn hf).symm
    _ ≤ (Finset.univ.filter (fun b => d b = color)).card := Finset.card_le_card hsub
    _ ≤ B := hbound

theorem interval_fiber_card_le_of_anchored {α : Type*} [DecidableEq α]
    (c : Nat → α) (L B : Nat)
    (hforward : ∀ a, a + L ≤ 3 * L →
      (Finset.univ.filter (fun j : Fin L => c (a + j.val) = c a)).card ≤ B)
    (hbackward : ∀ a, L ≤ a + 1 → a < 3 * L →
      (Finset.univ.filter (fun j : Fin L => c (a - j.val) = c a)).card ≤ B)
    {i : Nat} (hi : i + L ≤ 3 * L) (color : α) :
    (Finset.univ.filter (fun j : Fin L => c (i + j.val) = color)).card ≤ B := by
  let A := Finset.univ.filter (fun j : Fin L => c (i + j.val) = color)
  by_cases hA : A.Nonempty
  · let lo : Fin L := A.min' hA
    let up : Fin L := A.max' hA
    have hlocolor : c (i + lo.val) = color := (Finset.mem_filter.mp (A.min'_mem hA)).2
    have hupcolor : c (i + up.val) = color := (Finset.mem_filter.mp (A.max'_mem hA)).2
    have hlo : ∀ j : Fin L, c (i + j.val) = color → lo.val ≤ j.val := by
      intro j hj
      exact A.min'_le j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)
    have hup : ∀ j : Fin L, c (i + j.val) = color → j.val ≤ up.val := by
      intro j hj
      exact A.le_max' j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)
    by_cases hfit : i + lo.val + L ≤ 3 * L
    · let f : Fin L → Fin L := fun j => ⟨j.val - lo.val, by have := j.isLt; omega⟩
      apply finite_fiber_card_le_of_injOn (fun j : Fin L => c (i + j.val))
        (fun j : Fin L => c (i + lo.val + j.val)) color f B
      · simpa only [hlocolor] using hforward (i + lo.val) hfit
      · intro j hj
        have hle := hlo j hj
        have he : i + lo.val + (j.val - lo.val) = i + j.val := by omega
        change c (i + lo.val + (j.val - lo.val)) = color
        rw [he]
        exact hj
      · intro a ha b hb he
        have hla := hlo a ha
        have hlb := hlo b hb
        have hev : a.val - lo.val = b.val - lo.val := congrArg Fin.val he
        apply Fin.ext
        omega
    · have hupfit : i + up.val < 3 * L := by have := up.isLt; omega
      have hrev : L ≤ i + up.val + 1 := by
        have hle := hlo up hupcolor
        omega
      let f : Fin L → Fin L := fun j => ⟨up.val - j.val, by have := up.isLt; omega⟩
      apply finite_fiber_card_le_of_injOn (fun j : Fin L => c (i + j.val))
        (fun j : Fin L => c (i + up.val - j.val)) color f B
      · simpa only [hupcolor] using hbackward (i + up.val) hrev hupfit
      · intro j hj
        have hle := hup j hj
        have he : i + up.val - (up.val - j.val) = i + j.val := by omega
        change c (i + up.val - (up.val - j.val)) = color
        rw [he]
        exact hj
      · intro a ha b hb he
        have hua := hup a ha
        have hub := hup b hb
        have hev : up.val - a.val = up.val - b.val := congrArg Fin.val he
        apply Fin.ext
        omega
  · have he : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    change A.card ≤ B
    rw [he, Finset.card_empty]
    exact Nat.zero_le _

theorem finite_fibers_eq_of_le {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (M : Nat) (hcard : Fintype.card α = Fintype.card β * M)
    (hupper : ∀ b, (Finset.univ.filter (fun a => f a = b)).card ≤ M) :
    ∀ b, (Finset.univ.filter (fun a => f a = b)).card = M := by
  have hsum : (∑ b : β, (Finset.univ.filter (fun a => f a = b)).card) = Fintype.card α := by
    calc
      _ = ∑ b : β, ∑ a : α, if f a = b then (1 : Nat) else 0 := by
        simp only [Finset.sum_boole, Nat.cast_id]
      _ = ∑ a : α, ∑ b : β, if f a = b then (1 : Nat) else 0 := Finset.sum_comm
      _ = Fintype.card α := by simp
  intro b
  by_contra hne
  have hlt : (Finset.univ.filter (fun a => f a = b)).card < M := lt_of_le_of_ne (hupper b) hne
  have hstrict := Finset.sum_lt_sum (fun b (_ : b ∈ (Finset.univ : Finset β)) => hupper b)
    ⟨b, Finset.mem_univ _, hlt⟩
  simp only [hsum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id] at hstrict
  omega

theorem higher_even_window_color_card_le {α : Type*} [DecidableEq α] {k m q : Nat}
    (hk : 5 ≤ k) (hm : 0 < m) (hq : 2 ≤ q) (heven : k % 2 ≠ 1)
    {c : Nat → α} (hc : HigherProperOn k m q c (3 * higherPeriod k m))
    {i : Nat} (hi : i + higherPeriod k m ≤ 3 * higherPeriod k m) (color : α) :
    (Finset.univ.filter (fun j : Fin (higherPeriod k m) => c (i + j.val) = color)).card ≤ 2 * m := by
  apply interval_fiber_card_le_of_anchored c (higherPeriod k m) (2 * m) ?_ ?_ hi color
  · intro a ha
    simpa only [Nat.add_zero] using
      higher_even_anchored_color_card_le hk hm hq heven (higherProperOn_shift hc ha)
  · intro a ha hb
    simpa only [Nat.sub_zero] using
      higher_even_anchored_color_card_le hk hm hq heven (higherProperOn_reverse hc hb ha)

theorem higher_even_window_color_card {k m q : Nat}
    (hk : 5 ≤ k) (hm : 0 < m) (hq : 2 ≤ q) (heven : k % 2 ≠ 1)
    {c : Nat → Fin (k - 1)} (hc : HigherProperOn k m q c (3 * higherPeriod k m))
    {i : Nat} (hi : i + higherPeriod k m ≤ 3 * higherPeriod k m) (color : Fin (k - 1)) :
    (Finset.univ.filter (fun j : Fin (higherPeriod k m) => c (i + j.val) = color)).card = 2 * m := by
  apply finite_fibers_eq_of_le (fun j : Fin (higherPeriod k m) => c (i + j.val)) (2 * m)
  · simp only [Fintype.card_fin, higherPeriod, heven, if_false]
    ring
  · exact fun a => higher_even_window_color_card_le hk hm hq heven hc hi a

theorem higher_even_window_color_count {k m q : Nat}
    (hk : 5 ≤ k) (hm : 0 < m) (hq : 2 ≤ q) (heven : k % 2 ≠ 1)
    {c : Nat → Fin (k - 1)} (hc : HigherProperOn k m q c (3 * higherPeriod k m))
    {i : Nat} (hi : i + higherPeriod k m ≤ 3 * higherPeriod k m) (color : Fin (k - 1)) :
    windowSum (fun j => if c j = color then (1 : Int) else 0) i (higherPeriod k m) = 2 * m := by
  unfold windowSum
  rw [partialSum_eq_sum_range, ← Fin.sum_univ_eq_sum_range, Finset.sum_boole]
  exact_mod_cast higher_even_window_color_card hk hm hq heven hc hi color

theorem higher_even_local_periodicity {k m q : Nat} (hk : 5 ≤ k) (hm : 0 < m)
    (hq : 2 ≤ q) (heven : k % 2 ≠ 1) {c : Nat → Fin (k - 1)}
    (hc : HigherProperOn k m q c (3 * higherPeriod k m)) {i : Nat}
    (hi : i < 2 * higherPeriod k m) : c (i + higherPeriod k m) = c i := by
  have h₁ := higher_even_window_color_count hk hm hq heven hc (i := i) (by omega) (c i)
  have h₂ := higher_even_window_color_count hk hm hq heven hc (i := i + 1) (by omega) (c i)
  exact equal_window_color_counts_force_period c (h₁.trans h₂.symm)

theorem higher_local_periodicity {k m q : Nat} (hk : 5 ≤ k) (hm : 0 < m)
    (hq : 2 ≤ q) {c : Nat → Fin (k - 1)}
    (hc : HigherProperOn k m q c (3 * higherPeriod k m)) {i : Nat}
    (hi : i < 2 * higherPeriod k m) : c (i + higherPeriod k m) = c i := by
  by_cases hodd : k % 2 = 1
  · exact higher_odd_local_periodicity hk hm hq hodd hc hi
  · exact higher_even_local_periodicity hk hm hq hodd hc hi

theorem higher_clean_block_periodic {k m q : Nat} (hk : 5 ≤ k) (hm : 0 < m)
    (hq : 3 ≤ q) (c : ZMod (q * higherPeriod k m + 1) → Fin (k - 1))
    (v : ZMod (q * higherPeriod k m + 1))
    (hclean : ∀ j : Nat, j < 3 * higherPeriod k m →
      v + (j : ZMod (q * higherPeriod k m + 1)) ∉ badVertices (higherGraph k m q) c)
    {i : Nat} (hi : i < 2 * higherPeriod k m) :
    c (v + ((i + higherPeriod k m : Nat) : ZMod (q * higherPeriod k m + 1))) =
      c (v + (i : ZMod (q * higherPeriod k m + 1))) := by
  have hlen : 3 * higherPeriod k m ≤ q * higherPeriod k m + 1 :=
    (Nat.mul_le_mul_right (higherPeriod k m) hq).trans (Nat.le_succ _)
  exact higher_local_periodicity hk hm (by omega) (higherProperOn_of_clean c v hlen hclean) hi

theorem exists_unaffected_of_large_finset {V : Type*} [Finite V] [DecidableEq V]
    (G : SimpleGraph V) {p r : Nat} (c : V → Fin p)
    (hbad : (badEdges G c).ncard ≤ r) (S : Finset V) (hS : 2 * r < S.card) :
    ∃ v ∈ S, v ∉ badVertices G c := by
  classical
  let : Fintype V := Fintype.ofFinite V
  have hb : (badVertices G c).toFinset.card ≤ 2 * r := by
    rw [← Set.ncard_eq_toFinset_card']
    exact (badVertices_ncard_le G c).trans (Nat.mul_le_mul_left 2 hbad)
  obtain ⟨v, hv, hnot⟩ := Finset.exists_mem_notMem_of_card_lt_card (hb.trans_lt hS)
  exact ⟨v, hv, by simpa only [Set.mem_toFinset] using hnot⟩

theorem color_class_single_parity_of_many {V : Type*} [Finite V]
    (G : SimpleGraph V) {p r len : Nat} (c : V → Fin p)
    (f : Fin len → V) (hf : Function.Injective f)
    (hadj : ∀ a b : Fin len, a.val % 2 ≠ b.val % 2 → G.Adj (f a) (f b))
    (hbad : (badEdges G c).ncard ≤ r) (color : Fin p)
    (hcount : 2 * r < (Finset.univ.filter (fun j : Fin len => c (f j) = color)).card) :
    ∀ a b : Fin len, c (f a) = color → c (f b) = color → a.val % 2 = b.val % 2 := by
  classical
  let A := Finset.univ.filter (fun j : Fin len => c (f j) = color)
  have hA : 2 * r < (A.image f).card := by
    rw [Finset.card_image_of_injective A hf]
    exact hcount
  obtain ⟨v, hv, hclean⟩ := exists_unaffected_of_large_finset G c hbad (A.image f) hA
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hv
  have hcolor := (Finset.mem_filter.mp hj).2
  have hall : ∀ b : Fin len, c (f b) = color → j.val % 2 = b.val % 2 := by
    intro b hb
    by_contra he
    exact edge_proper_at_unaffected_vertex G c hclean (hadj j b he) (hcolor.trans hb.symm)
  intro a b ha hb
  exact (hall a ha).symm.trans (hall b hb)

theorem cyclic_interval_index_injective {n len : Nat} [NeZero n] (hfit : len ≤ n)
    (v : ZMod n) : Function.Injective (fun j : Fin len => v + (j.val : ZMod n)) := by
  intro a b he
  have hz : (a.val : ZMod n) = (b.val : ZMod n) := add_left_cancel he
  have hv := congrArg ZMod.val hz
  rw [ZMod.val_natCast, ZMod.val_natCast,
    Nat.mod_eq_of_lt (a.isLt.trans_le hfit), Nat.mod_eq_of_lt (b.isLt.trans_le hfit)] at hv
  exact Fin.ext hv

theorem higher_short_opposite_parity_adj {k m q : Nat}
    (hfit : 2 * m ≤ q * higherPeriod k m + 1)
    (v : ZMod (q * higherPeriod k m + 1)) (a b : Fin (2 * m))
    (hpar : a.val % 2 ≠ b.val % 2) :
    (higherGraph k m q).Adj (v + (a.val : ZMod (q * higherPeriod k m + 1)))
      (v + (b.val : ZMod (q * higherPeriod k m + 1))) := by
  have ha := a.isLt
  have hb := b.isLt
  rcases lt_trichotomy a.val b.val with h | h | h
  · apply higher_adj_nat_indices h (hb.trans_le hfit)
    exact Or.inl ⟨by omega, by omega, by omega⟩
  · exact False.elim (hpar (congrArg (fun j : Nat => j % 2) h))
  · apply SimpleGraph.Adj.symm
    apply higher_adj_nat_indices h (ha.trans_le hfit)
    exact Or.inl ⟨by omega, by omega, by omega⟩

theorem higher_short_color_class_single_parity {k m q p r : Nat}
    (hfit : 2 * m ≤ q * higherPeriod k m + 1)
    (c : ZMod (q * higherPeriod k m + 1) → Fin p)
    (hbad : (badEdges (higherGraph k m q) c).ncard ≤ r)
    (v : ZMod (q * higherPeriod k m + 1)) (color : Fin p)
    (hcount : 2 * r < (Finset.univ.filter (fun j : Fin (2 * m) =>
      c (v + (j.val : ZMod (q * higherPeriod k m + 1))) = color)).card) :
    ∀ a b : Fin (2 * m),
      c (v + (a.val : ZMod (q * higherPeriod k m + 1))) = color →
      c (v + (b.val : ZMod (q * higherPeriod k m + 1))) = color → a.val % 2 = b.val % 2 := by
  apply color_class_single_parity_of_many (higherGraph k m q) c _
    (cyclic_interval_index_injective hfit v) ?_ hbad color hcount
  exact fun a b => higher_short_opposite_parity_adj hfit v a b

theorem local_period_eq_mod {α : Type*} {L len : Nat} (hL : 0 < L) (c : Nat → α)
    (hc : ∀ j, j + L < len → c (j + L) = c j) {i : Nat} (hi : i < len) :
    c i = c (i % L) := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
    by_cases hsmall : i < L
    · rw [Nat.mod_eq_of_lt hsmall]
    · have hle : L ≤ i := by omega
      have hsub : i - L + L = i := by omega
      have hstep : c i = c (i - L) := by
        have hs := hc (i - L) (by omega)
        rwa [hsub] at hs
      rw [Nat.mod_eq_sub_mod hle]
      exact hstep.trans (ih (i - L) (by omega) (by omega))

def higherExpectedColor {α : Type*} (k m : Nat) (c : Nat → α) (i : Int) : α :=
  c ((i % (higherPeriod k m : Int)).toNat)

theorem higherExpectedColor_periodic {α : Type*} (k m : Nat) (c : Nat → α) (i : Int) :
    higherExpectedColor k m c (i + higherPeriod k m) = higherExpectedColor k m c i := by
  simp only [higherExpectedColor, Int.add_emod_right]

theorem higherExpectedColor_of_nat {α : Type*} (k m : Nat) (c : Nat → α) (i : Nat) :
    higherExpectedColor k m c i = c (i % higherPeriod k m) := by
  simp only [higherExpectedColor, ← Int.natCast_emod, Int.toNat_natCast]

theorem higherExpectedColor_eq_of_mod_eq {α : Type*} (k m : Nat) (c : Nat → α)
    {i j : Int} (hij : i % (higherPeriod k m : Int) = j % (higherPeriod k m : Int)) :
    higherExpectedColor k m c i = higherExpectedColor k m c j := by
  simp only [higherExpectedColor, hij]

theorem higherExpectedColor_residue_bound {k m : Nat} (hk : 5 ≤ k) (hm : 0 < m) (i : Int) :
    (i % (higherPeriod k m : Int)).toNat < higherPeriod k m := by
  have hL := higherPeriod_pos hk hm
  have hpos : (0 : Int) < higherPeriod k m := by exact_mod_cast hL
  have hlo := Int.emod_nonneg i (ne_of_gt hpos)
  have hhi := Int.emod_lt_of_pos i hpos
  omega

theorem higherExpectedColor_agrees {k m q : Nat} (hk : 5 ≤ k) (hm : 0 < m)
    (hq : 2 ≤ q) {c : Nat → Fin (k - 1)}
    (hc : HigherProperOn k m q c (3 * higherPeriod k m)) {i : Nat}
    (hi : i < 3 * higherPeriod k m) : higherExpectedColor k m c i = c i := by
  rw [higherExpectedColor_of_nat]
  apply (local_period_eq_mod (higherPeriod_pos hk hm) c ?_ hi).symm
  intro j hj
  exact higher_local_periodicity hk hm hq hc (by omega)

theorem higherExpectedColor_nat_distance {k m q d : Nat} (hk : 5 ≤ k) (hm : 0 < m)
    (hq : 2 ≤ q) {c : Nat → Fin (k - 1)}
    (hc : HigherProperOn k m q c (3 * higherPeriod k m))
    (hdpos : 0 < d) (hdle : d ≤ 2 * higherPeriod k m) (hd : HigherDistance k m q d) (i : Nat) :
    higherExpectedColor k m c i ≠ higherExpectedColor k m c (i + d : Nat) := by
  let a := i % higherPeriod k m
  have ha : a < higherPeriod k m := Nat.mod_lt _ (higherPeriod_pos hk hm)
  have he : higherExpectedColor k m c i = higherExpectedColor k m c a := by
    simp only [higherExpectedColor_of_nat, a, Nat.mod_mod]
  have he' : higherExpectedColor k m c (i + d : Nat) = higherExpectedColor k m c (a + d : Nat) := by
    simp only [higherExpectedColor_of_nat, a, Nat.add_mod, Nat.mod_mod]
  rw [he, he', higherExpectedColor_agrees hk hm hq hc (by omega : a < 3 * higherPeriod k m),
    higherExpectedColor_agrees hk hm hq hc (by omega : a + d < 3 * higherPeriod k m)]
  exact hc a (a + d) (by omega) (by omega) (by simpa only [Nat.add_sub_cancel_left] using hd)

theorem higherExpectedColor_int_distance {k m q d : Nat} (hk : 5 ≤ k) (hm : 0 < m)
    (hq : 2 ≤ q) {c : Nat → Fin (k - 1)}
    (hc : HigherProperOn k m q c (3 * higherPeriod k m))
    (hdpos : 0 < d) (hdle : d ≤ 2 * higherPeriod k m) (hd : HigherDistance k m q d) (i : Int) :
    higherExpectedColor k m c i ≠ higherExpectedColor k m c (i + d) := by
  let a := (i % (higherPeriod k m : Int)).toNat
  have hL : (0 : Int) < higherPeriod k m := by exact_mod_cast higherPeriod_pos hk hm
  have ha : (a : Int) = i % (higherPeriod k m : Int) :=
    Int.toNat_of_nonneg (Int.emod_nonneg i (ne_of_gt hL))
  have he : higherExpectedColor k m c i = higherExpectedColor k m c a := by
    apply higherExpectedColor_eq_of_mod_eq
    rw [ha, Int.emod_emod]
  have he' : higherExpectedColor k m c (i + d) = higherExpectedColor k m c (a + d : Nat) := by
    apply higherExpectedColor_eq_of_mod_eq
    simp only [Nat.cast_add, ha, Int.add_emod, Int.emod_emod]
  rw [he, he']
  exact higherExpectedColor_nat_distance hk hm hq hc hdpos hdle hd a

theorem higher_window_color_count {k m q : Nat} (hk : 5 ≤ k) (hm : 0 < m) (hq : 2 ≤ q)
    {c : Nat → Fin (k - 1)} (hc : HigherProperOn k m q c (3 * higherPeriod k m))
    {i : Nat} (hi : i + higherPeriod k m ≤ 3 * higherPeriod k m) (color : Fin (k - 1)) :
    windowSum (fun j => if c j = color then (1 : Int) else 0) i (higherPeriod k m) =
      (if k % 2 = 1 then (m : Int) else 2 * m) := by
  by_cases hodd : k % 2 = 1
  · simpa only [hodd, if_true] using higher_odd_window_color_count hk hm hq hodd hc hi color
  · simpa only [hodd, if_false] using higher_even_window_color_count hk hm hq hodd hc hi color

theorem higherExpectedColor_window_count {k m q : Nat} (hk : 5 ≤ k) (hm : 0 < m) (hq : 2 ≤ q)
    {c : Nat → Fin (k - 1)} (hc : HigherProperOn k m q c (3 * higherPeriod k m))
    (i : Nat) (color : Fin (k - 1)) :
    windowSum (fun j => if higherExpectedColor k m c j = color then (1 : Int) else 0)
      i (higherPeriod k m) = (if k % 2 = 1 then (m : Int) else 2 * m) := by
  have hp : ∀ j : Nat, higherExpectedColor k m c (j + higherPeriod k m : Nat) =
      higherExpectedColor k m c j := by
    intro j
    simpa only [Nat.cast_add] using higherExpectedColor_periodic k m c j
  have hw := windowSum_period (fun j => if higherExpectedColor k m c j = color then (1 : Int) else 0)
    (fun j => by rw [hp j]) i
  have hbase : partialSum (fun j => if higherExpectedColor k m c j = color then (1 : Int) else 0)
      (higherPeriod k m) = windowSum (fun j => if c j = color then (1 : Int) else 0) 0
        (higherPeriod k m) := by
    unfold windowSum
    apply partialSum_congr
    intro j hj
    rw [Nat.zero_add, higherExpectedColor_agrees hk hm hq hc (by omega)]
  exact hw.trans (hbase.trans (higher_window_color_count hk hm hq hc (i := 0) (by omega) color))

theorem higherPairedIndex_middle_band {k m a : Nat} (hk : 5 ≤ k) (hodd : k % 2 = 1)
    (ha : 2 ≤ a) (hak : a < k - 1) :
    2 * m ≤ higherPairedIndex m 0 a ∧ higherPairedIndex m 0 a ≤ (k - 3) * m + 1 := by
  have hrowlo : 1 ≤ a / 2 := by omega
  have hrowhi : 2 * (a / 2) ≤ k - 3 := by omega
  have hb : a % 2 < 2 := Nat.mod_lt _ (by omega)
  have hlo := Nat.mul_le_mul_left (2 * m) hrowlo
  have hhi := Nat.mul_le_mul_right m hrowhi
  simp only [higherPairedIndex, mul_zero, add_zero]
  constructor
  · nlinarith only [hlo, Nat.zero_le (a % 2)]
  · nlinarith only [hhi, hb]

set_option maxHeartbeats 800000 in
theorem higher_odd_two_options_sequence {k m q : Nat} (hk : 5 ≤ k) (hm : 0 < m)
    (hq : 2 ≤ q) (hodd : k % 2 = 1) {c : Nat → Fin (k - 1)}
    (hc : HigherProperOn k m q c (3 * higherPeriod k m))
    (hcross : ∀ j i : Nat, j < 3 * higherPeriod k m → i < (q / 2) * higherPeriod k m →
      j < i → HigherDistance k m q (i - j) → c j ≠ c i)
    {i : Nat} (hi : i < (q / 2) * higherPeriod k m) :
    c i = higherExpectedColor k m c i ∨ c i = higherExpectedColor k m c (i - 1 : Nat) := by
  let L := higherPeriod k m
  have hL : 0 < L := higherPeriod_pos hk hm
  by_cases hclean : i < 3 * L
  · exact Or.inl (higherExpectedColor_agrees hk hm hq hc hclean).symm
  let i₀ := L + i % L
  let b := i / L - 1
  have hmod : i % L < L := Nat.mod_lt _ hL
  have hi₀lo : L ≤ i₀ := by omega
  have hi₀hi : i₀ < 2 * L := by omega
  have hdiv : 1 ≤ i / L := (Nat.le_div_iff_mul_le hL).mpr (by omega)
  have hsum : b * L + i₀ = i := by
    have hd := Nat.mod_add_div i L
    have hb : b + 1 = i / L := by omega
    dsimp only [i₀]
    nlinarith only [hd, hb]
  have hbq : b < q / 2 := by
    have hd : i / L < q / 2 := (Nat.div_lt_iff_lt_mul hL).mpr hi
    omega
  have hr : HigherProperOn k m q (fun j => c (i₀ - j)) L :=
    higherProperOn_reverse hc (by omega) (by omega)
  have hinj := higher_odd_clique_coloring_injective hk hm hq hodd hr (⟨0, hm⟩ : Fin m)
  obtain ⟨a, ha⟩ := Finite.surjective_of_injective hinj (c i)
  change c (i₀ - higherPairedIndex m 0 a.val) = c i at ha
  have he₀ : higherExpectedColor k m c i = higherExpectedColor k m c i₀ := by
    simp only [higherExpectedColor_of_nat]
    change c (i % L) = c (i₀ % L)
    rw [← hsum]
    rw [Nat.mul_add_mod_self_right]
  have he₁ : higherExpectedColor k m c (i - 1 : Nat) =
      higherExpectedColor k m c (i₀ - 1 : Nat) := by
    simp only [higherExpectedColor_of_nat]
    change c ((i - 1) % L) = c ((i₀ - 1) % L)
    rw [← hsum, Nat.add_sub_assoc (by omega : 1 ≤ i₀)]
    rw [Nat.mul_add_mod_self_right]
  by_cases ha₀ : a.val = 0
  · left
    rw [ha₀] at ha
    simp only [higherPairedIndex, Nat.zero_div, Nat.zero_mod, mul_zero, add_zero, Nat.sub_zero] at ha
    rw [he₀, higherExpectedColor_agrees hk hm hq hc (by omega)]
    exact ha.symm
  · by_cases ha₁ : a.val = 1
    · right
      rw [ha₁] at ha
      norm_num [higherPairedIndex] at ha
      rw [he₁, higherExpectedColor_agrees hk hm hq hc (by omega)]
      exact ha.symm
    · have hadim : 2 ≤ a.val := by omega
      have haband := higherPairedIndex_middle_band (m := m) hk hodd hadim a.isLt
      have halt : higherPairedIndex m 0 a.val < L :=
        higherPairedIndex_lt_period hk hm hodd hm a.isLt
      let j := i₀ - higherPairedIndex m 0 a.val
      have hdiff : i - j = b * L + higherPairedIndex m 0 a.val := by omega
      have hd : HigherDistance k m q (i - j) := by
        rw [hdiff]
        refine Or.inr (Or.inl ⟨b, hbq, ?_, ?_⟩)
        · exact Nat.add_le_add_left haband.1 _
        · simpa only [hodd, if_true, Nat.add_assoc] using Nat.add_le_add_left haband.2 (b * L)
      exact False.elim (hcross j i (by omega) hi (by omega) hd ha)

theorem higher_odd_clean_prefix_two_options {k m q : Nat} (hk : 5 ≤ k) (hm : 0 < m)
    (hq : 3 ≤ q) (hodd : k % 2 = 1)
    (c : ZMod (q * higherPeriod k m + 1) → Fin (k - 1))
    (v : ZMod (q * higherPeriod k m + 1))
    (hclean : ∀ j : Nat, j < 3 * higherPeriod k m →
      v + (j : ZMod (q * higherPeriod k m + 1)) ∉ badVertices (higherGraph k m q) c)
    {i : Nat} (hi : i < (q / 2) * higherPeriod k m) :
    c (v + (i : ZMod (q * higherPeriod k m + 1))) =
      higherExpectedColor k m (fun j => c (v + (j : ZMod (q * higherPeriod k m + 1)))) i ∨
    c (v + (i : ZMod (q * higherPeriod k m + 1))) =
      higherExpectedColor k m (fun j => c (v + (j : ZMod (q * higherPeriod k m + 1)))) (i - 1 : Nat) := by
  have hlen : 3 * higherPeriod k m ≤ q * higherPeriod k m + 1 :=
    (Nat.mul_le_mul_right (higherPeriod k m) hq).trans (Nat.le_succ _)
  apply higher_odd_two_options_sequence hk hm (by omega) hodd
    (higherProperOn_of_clean c v hlen hclean) ?_ hi
  intro j i hj hi hji hd
  have hhalf : (q / 2) * higherPeriod k m ≤ q * higherPeriod k m :=
    Nat.mul_le_mul_right (higherPeriod k m) (Nat.div_le_self q 2)
  exact edge_proper_at_unaffected_vertex (higherGraph k m q) c (hclean j hj)
    (higher_adj_nat_indices hji (by omega) hd v)

/-
## Local color structure, including the exceptional cases

The following development formalizes Claims 4.6 and 4.7 and Appendix B
of Skottova and Steiner, arXiv:2508.08703v1. For k=6 and k=8, finite ring
certificates give the two local color options. Ringwise periodicity of
changes and injectivity of the ring coloring then reduce the argument to
an exact count of changes along one parity. This completes local color
structure for every k >= 6. Robust propagation is proved in the final sections.
-/

def evenProgression (t m : Nat) : Finset Nat :=
  (Finset.range m).image (fun s => t + 2 * s)

theorem evenProgression_card (t m : Nat) : (evenProgression t m).card = m := by
  unfold evenProgression
  have hinj : Function.Injective (fun s : Nat => t + 2 * s) := by
    intro a b h
    dsimp only at h
    omega
  rw [Finset.card_image_of_injective _ hinj, Finset.card_range]

theorem mem_evenProgression {t m x : Nat} :
    x ∈ evenProgression t m ↔ ∃ s < m, t + 2 * s = x := by
  simp only [evenProgression, Finset.mem_image, Finset.mem_range]

theorem finset_subset_evenProgression {S : Finset Nat} {t m : Nat}
    (hlo : ∀ x ∈ S, t ≤ x)
    (hgap : ∀ x ∈ S, x - t < 2 * m ∧ (x - t) % 2 = 0) :
    S ⊆ evenProgression t m := by
  intro x hx
  have h₁ := hlo x hx
  have h₂ := hgap x hx
  apply mem_evenProgression.mpr
  refine ⟨(x - t) / 2, by omega, by omega⟩

theorem finset_eq_evenProgression_of_card {S : Finset Nat} {t m : Nat}
    (hcard : S.card = m) (hlo : ∀ x ∈ S, t ≤ x)
    (hgap : ∀ x ∈ S, x - t < 2 * m ∧ (x - t) % 2 = 0) :
    S = evenProgression t m := by
  apply Finset.eq_of_subset_of_card_le (finset_subset_evenProgression hlo hgap)
  rw [evenProgression_card, hcard]

theorem finset_evenProgression_of_differences {S : Finset Nat} {m : Nat} (hm : 0 < m)
    (hcard : S.card = m)
    (hdiff : ∀ x ∈ S, ∀ y ∈ S, x ≤ y → y - x < 2 * m ∧ (y - x) % 2 = 0) :
    ∃ t ∈ S, S = evenProgression t m := by
  have hS : S.Nonempty := Finset.card_pos.mp (by omega)
  refine ⟨S.min' hS, S.min'_mem hS, ?_⟩
  apply finset_eq_evenProgression_of_card hcard
  · exact fun x hx => S.min'_le x hx
  · exact fun x hx => hdiff _ (S.min'_mem hS) x hx (S.min'_le x hx)

def higherFirstBandUpper (k m : Nat) : Nat :=
  if k % 2 = 1 then (k - 3) * m + 1 else (k - 4) * m + 2

theorem higher_first_band_distance {k m q d : Nat} (hq : 2 ≤ q)
    (hlo : 2 * m ≤ d) (hhi : d ≤ higherFirstBandUpper k m) : HigherDistance k m q d := by
  refine Or.inr (Or.inl ⟨0, by omega, ?_, ?_⟩)
  · simpa only [zero_mul, zero_add] using hlo
  · simpa only [zero_mul, zero_add, higherFirstBandUpper] using hhi

theorem higherExpectedColor_gap_constraints {k m q d : Nat} (hk : 5 ≤ k) (hm : 0 < m)
    (hq : 2 ≤ q) {c : Nat → Fin (k - 1)}
    (hc : HigherProperOn k m q c (3 * higherPeriod k m))
    (hdle : d ≤ 2 * higherPeriod k m) (hband : d ≤ higherFirstBandUpper k m) (i : Int)
    (he : higherExpectedColor k m c i = higherExpectedColor k m c (i + d)) :
    d < 2 * m ∧ d % 2 = 0 := by
  have hshort : d < 2 * m := by
    by_contra hnot
    have hlo : 2 * m ≤ d := by omega
    exact higherExpectedColor_int_distance hk hm hq hc (by omega) hdle
      (higher_first_band_distance hq hlo hband) i he
  refine ⟨hshort, ?_⟩
  by_contra hnot
  have hodd : d % 2 = 1 := by omega
  exact higherExpectedColor_int_distance hk hm hq hc (by omega) hdle
    (Or.inl ⟨by omega, hshort, hodd⟩) i he

theorem higherExpectedColor_odd_small_gap {k m q d : Nat} (hk : 7 ≤ k) (hm : 0 < m)
    (hq : 2 ≤ q) (hodd : k % 2 = 1) {c : Nat → Fin (k - 1)}
    (hc : HigherProperOn k m q c (3 * higherPeriod k m)) (hd : d < 4 * m) (i : Int)
    (he : higherExpectedColor k m c i = higherExpectedColor k m c (i + d)) :
    d < 2 * m ∧ d % 2 = 0 := by
  have hL := higherPeriod_lower (m := m) (by omega : 5 ≤ k)
  apply higherExpectedColor_gap_constraints (by omega) hm hq hc (by omega) ?_ i he
  have hbase := Nat.mul_le_mul_right m (by omega : 4 ≤ k - 3)
  simp only [higherFirstBandUpper, hodd, if_true]
  omega

theorem higherExpectedColor_even_small_gap {k m q d : Nat} (hk : 10 ≤ k) (hm : 0 < m)
    (hq : 2 ≤ q) (heven : k % 2 ≠ 1) {c : Nat → Fin (k - 1)}
    (hc : HigherProperOn k m q c (3 * higherPeriod k m)) (hd : d < 6 * m) (i : Int)
    (he : higherExpectedColor k m c i = higherExpectedColor k m c (i + d)) :
    d < 2 * m ∧ d % 2 = 0 := by
  have hL := higherPeriod_lower (m := m) (by omega : 5 ≤ k)
  apply higherExpectedColor_gap_constraints (by omega) hm hq hc (by omega) ?_ i he
  have hbase := Nat.mul_le_mul_right m (by omega : 6 ≤ k - 4)
  simp only [higherFirstBandUpper, heven, if_false]
  omega

def expectedColorOffsets (k m : Nat) (c : Nat → Fin (k - 1)) (start : Nat)
    (color : Fin (k - 1)) : Finset Nat :=
  (Finset.range (higherPeriod k m)).filter
    (fun j => higherExpectedColor k m c (start + j : Nat) = color)

def expectedColorWindow (k m : Nat) (c : Nat → Fin (k - 1)) (start : Nat)
    (color : Fin (k - 1)) : Finset Nat :=
  (expectedColorOffsets k m c start color).image (fun j => start + j)

theorem mem_expectedColorOffsets {k m start j : Nat} {c : Nat → Fin (k - 1)}
    {color : Fin (k - 1)} : j ∈ expectedColorOffsets k m c start color ↔
    j < higherPeriod k m ∧ higherExpectedColor k m c (start + j : Nat) = color := by
  simp only [expectedColorOffsets, Finset.mem_filter, Finset.mem_range]

theorem mem_expectedColorWindow {k m start x : Nat} {c : Nat → Fin (k - 1)}
    {color : Fin (k - 1)} : x ∈ expectedColorWindow k m c start color ↔
    start ≤ x ∧ x < start + higherPeriod k m ∧ higherExpectedColor k m c x = color := by
  constructor
  · intro hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hj, he⟩ := mem_expectedColorOffsets.mp hj
    exact ⟨by omega, by omega, he⟩
  · rintro ⟨hlo, hhi, he⟩
    have hx : start + (x - start) = x := by omega
    refine Finset.mem_image.mpr ⟨x - start, ?_, hx⟩
    apply mem_expectedColorOffsets.mpr
    refine ⟨by omega, ?_⟩
    rwa [hx]

theorem expectedColorWindow_card {k m q : Nat} (hk : 5 ≤ k) (hm : 0 < m) (hq : 2 ≤ q)
    {c : Nat → Fin (k - 1)} (hc : HigherProperOn k m q c (3 * higherPeriod k m))
    (start : Nat) (color : Fin (k - 1)) :
    (expectedColorWindow k m c start color).card = (if k % 2 = 1 then m else 2 * m) := by
  unfold expectedColorWindow
  have hinj : Function.Injective (fun j : Nat => start + j) := by
    intro a b h
    dsimp only at h
    omega
  rw [Finset.card_image_of_injective _ hinj]
  have hw := higherExpectedColor_window_count hk hm hq hc start color
  unfold windowSum at hw
  rw [partialSum_eq_sum_range, Finset.sum_boole] at hw
  unfold expectedColorOffsets
  by_cases hodd : k % 2 = 1
  · simp only [hodd, if_true] at hw ⊢
    exact_mod_cast hw
  · simp only [hodd, if_false] at hw ⊢
    exact_mod_cast hw

theorem expectedColorWindow_nonempty {k m q : Nat} (hk : 5 ≤ k) (hm : 0 < m) (hq : 2 ≤ q)
    {c : Nat → Fin (k - 1)} (hc : HigherProperOn k m q c (3 * higherPeriod k m))
    (start : Nat) (color : Fin (k - 1)) : (expectedColorWindow k m c start color).Nonempty := by
  apply Finset.card_pos.mp
  rw [expectedColorWindow_card hk hm hq hc]
  split <;> omega

theorem higherExpectedColor_exists_nat {k m q : Nat} (hk : 5 ≤ k) (hm : 0 < m) (hq : 2 ≤ q)
    {c : Nat → Fin (k - 1)} (hc : HigherProperOn k m q c (3 * higherPeriod k m))
    (color : Fin (k - 1)) :
    ∃ j < higherPeriod k m, higherExpectedColor k m c j = color := by
  obtain ⟨j, hj⟩ := expectedColorWindow_nonempty hk hm hq hc 0 color
  have hj' := mem_expectedColorWindow.mp hj
  exact ⟨j, by simpa only [Nat.zero_add] using hj'.2.1, hj'.2.2⟩

theorem int_residue_in_nat_window (L start : Nat) (hL : 0 < L) (i : Int) :
    ∃ x : Nat, start ≤ x ∧ x < start + L ∧ (x : Int) % L = i % L := by
  let a := ((i - start) % (L : Int)).toNat
  have hL' : (0 : Int) < L := by exact_mod_cast hL
  have hnonneg := Int.emod_nonneg (i - start) (ne_of_gt hL')
  have hlt := Int.emod_lt_of_pos (i - start) hL'
  have ha : (a : Int) = (i - start) % (L : Int) := Int.toNat_of_nonneg hnonneg
  have hal : a < L := by omega
  refine ⟨start + a, by omega, by omega, ?_⟩
  rw [Nat.cast_add, ha]
  calc
    ((start : Int) + (i - start) % L) % L = ((start : Int) + (i - start)) % L := by
      simp only [Int.add_emod, Int.emod_emod]
    _ = i % L := by congr 1; omega

theorem expectedColorWindow_full_class {k m : Nat} (hk : 5 ≤ k) (hm : 0 < m)
    (c : Nat → Fin (k - 1)) (start : Nat) (color : Fin (k - 1)) (i : Int) :
    higherExpectedColor k m c i = color ↔
      ∃ x ∈ expectedColorWindow k m c start color,
        i % (higherPeriod k m : Int) = (x : Int) % (higherPeriod k m : Int) := by
  constructor
  · intro he
    obtain ⟨x, hxlo, hxhi, hxmod⟩ := int_residue_in_nat_window (higherPeriod k m) start
      (higherPeriod_pos hk hm) i
    refine ⟨x, mem_expectedColorWindow.mpr ⟨hxlo, hxhi, ?_⟩, hxmod.symm⟩
    exact (higherExpectedColor_eq_of_mod_eq k m c hxmod).trans he
  · rintro ⟨x, hx, hxmod⟩
    exact (higherExpectedColor_eq_of_mod_eq k m c hxmod).trans (mem_expectedColorWindow.mp hx).2.2

theorem higher_odd_anchor_window_lower {k m q j x : Nat} (hk : 5 ≤ k) (hm : 0 < m)
    (hq : 2 ≤ q) (hodd : k % 2 = 1) {c : Nat → Fin (k - 1)}
    (hc : HigherProperOn k m q c (3 * higherPeriod k m))
    (hlo : j + 2 * m ≤ x) (hhi : x < j + 2 * m + higherPeriod k m)
    (he : higherExpectedColor k m c x = higherExpectedColor k m c j) :
    j + (k - 3) * m + 2 ≤ x := by
  have hL := higherPeriod_lower (m := m) hk
  have hx : j + (x - j) = x := by omega
  by_contra hnot
  have hd : HigherDistance k m q (x - j) := by
    apply higher_first_band_distance hq (by omega)
    simp only [higherFirstBandUpper, hodd, if_true]
    omega
  have hne := higherExpectedColor_nat_distance hk hm hq hc (by omega : 0 < x - j)
    (by omega : x - j ≤ 2 * higherPeriod k m) hd j
  rw [hx] at hne
  exact hne he.symm

theorem higher_odd_window_evenProgression {k m q j : Nat} (hk : 7 ≤ k) (hm : 0 < m)
    (hq : 2 ≤ q) (hodd : k % 2 = 1) {c : Nat → Fin (k - 1)}
    (hc : HigherProperOn k m q c (3 * higherPeriod k m)) (color : Fin (k - 1))
    (hj : higherExpectedColor k m c j = color) :
    ∃ t ∈ expectedColorWindow k m c (j + 2 * m) color,
      expectedColorWindow k m c (j + 2 * m) color = evenProgression t m := by
  have hk5 : 5 ≤ k := by omega
  have hcard : (expectedColorWindow k m c (j + 2 * m) color).card = m := by
    simpa only [hodd, if_true] using expectedColorWindow_card hk5 hm hq hc (j + 2 * m) color
  apply finset_evenProgression_of_differences hm hcard
  intro x hx y hy hxy
  have hx' := mem_expectedColorWindow.mp hx
  have hy' := mem_expectedColorWindow.mp hy
  have hxlo := higher_odd_anchor_window_lower hk5 hm hq hodd hc hx'.1 hx'.2.1
    (hx'.2.2.trans hj.symm)
  have hL : higherPeriod k m = (k - 3) * m + 2 * m := by
    simp only [higherPeriod, hodd, if_true]
    have hK : k - 1 = (k - 3) + 2 := by omega
    rw [hK, Nat.add_mul]
  have hsmall : y - x < 4 * m := by omega
  have heq : (x : Int) + (y - x : Nat) = y := by omega
  apply higherExpectedColor_odd_small_gap hk hm hq hodd hc hsmall x
  rw [heq]
  exact hx'.2.2.trans hy'.2.2.symm

theorem higher_odd_expected_color_class {k m q : Nat} (hk : 7 ≤ k) (hm : 0 < m)
    (hq : 2 ≤ q) (hodd : k % 2 = 1) {c : Nat → Fin (k - 1)}
    (hc : HigherProperOn k m q c (3 * higherPeriod k m)) (color : Fin (k - 1)) :
    ∃ t : Nat, ∀ i : Int, higherExpectedColor k m c i = color ↔
      ∃ s < m, i % (higherPeriod k m : Int) = ((t + 2 * s : Nat) : Int) % (higherPeriod k m : Int) := by
  obtain ⟨j, _, hj⟩ := higherExpectedColor_exists_nat (by omega : 5 ≤ k) hm hq hc color
  obtain ⟨t, _, ht⟩ := higher_odd_window_evenProgression hk hm hq hodd hc color hj
  refine ⟨t, ?_⟩
  intro i
  rw [expectedColorWindow_full_class (by omega : 5 ≤ k) hm c (j + 2 * m) color i, ht]
  constructor
  · rintro ⟨x, hx, hmod⟩
    obtain ⟨s, hs, hxs⟩ := mem_evenProgression.mp hx
    exact ⟨s, hs, by rwa [hxs]⟩
  · rintro ⟨s, hs, hmod⟩
    exact ⟨t + 2 * s, mem_evenProgression.mpr ⟨s, hs, rfl⟩, hmod⟩

theorem finset_card_le_of_even_differences {S : Finset Nat} {m : Nat}
    (hdiff : ∀ x ∈ S, ∀ y ∈ S, x ≤ y → y - x < 2 * m ∧ (y - x) % 2 = 0) :
    S.card ≤ m := by
  by_cases hS : S.Nonempty
  · have hsub : S ⊆ evenProgression (S.min' hS) m :=
      finset_subset_evenProgression (fun x hx => S.min'_le x hx)
        (fun x hx => hdiff _ (S.min'_mem hS) x hx (S.min'_le x hx))
    have hcard := Finset.card_le_card hsub
    rwa [evenProgression_card] at hcard
  · rw [Finset.not_nonempty_iff_eq_empty.mp hS, Finset.card_empty]
    exact Nat.zero_le _

theorem finset_two_evenProgressions {S : Finset Nat} {m : Nat} (hm : 0 < m)
    (hcard : S.card = 2 * m) (P : Nat → Prop) [DecidablePred P]
    (hleft : ∀ x ∈ S, ∀ y ∈ S, P x → P y → x ≤ y →
      y - x < 2 * m ∧ (y - x) % 2 = 0)
    (hright : ∀ x ∈ S, ∀ y ∈ S, ¬ P x → ¬ P y → x ≤ y →
      y - x < 2 * m ∧ (y - x) % 2 = 0) :
    ∃ t t' : Nat, t ≠ t' ∧ S = evenProgression t m ∪ evenProgression t' m := by
  let A := S.filter P
  let B := S.filter (fun x => ¬ P x)
  have hA : ∀ x ∈ A, ∀ y ∈ A, x ≤ y → y - x < 2 * m ∧ (y - x) % 2 = 0 := by
    intro x hx y hy hxy
    have hx' := Finset.mem_filter.mp hx
    have hy' := Finset.mem_filter.mp hy
    exact hleft x hx'.1 y hy'.1 hx'.2 hy'.2 hxy
  have hB : ∀ x ∈ B, ∀ y ∈ B, x ≤ y → y - x < 2 * m ∧ (y - x) % 2 = 0 := by
    intro x hx y hy hxy
    have hx' := Finset.mem_filter.mp hx
    have hy' := Finset.mem_filter.mp hy
    exact hright x hx'.1 y hy'.1 hx'.2 hy'.2 hxy
  have hAle := finset_card_le_of_even_differences hA
  have hBle := finset_card_le_of_even_differences hB
  have hsum : A.card + B.card = S.card := Finset.card_filter_add_card_filter_not (s := S) P
  obtain ⟨t, ht, heA⟩ := finset_evenProgression_of_differences hm (by omega : A.card = m) hA
  obtain ⟨t', ht', heB⟩ := finset_evenProgression_of_differences hm (by omega : B.card = m) hB
  refine ⟨t, t', ?_, ?_⟩
  · intro he
    have hp : P t := (Finset.mem_filter.mp ht).2
    have hnp : ¬ P t' := (Finset.mem_filter.mp ht').2
    exact hnp (he ▸ hp)
  · have hcover : A ∪ B = S := by
      ext x
      simp only [Finset.mem_union, A, B, Finset.mem_filter]
      tauto
    rw [heA, heB] at hcover
    exact hcover.symm

theorem higher_even_anchor_window_bands {k m q j x : Nat} (hk : 5 ≤ k) (hm : 0 < m)
    (hq : 2 ≤ q) (heven : k % 2 ≠ 1) {c : Nat → Fin (k - 1)}
    (hc : HigherProperOn k m q c (3 * higherPeriod k m))
    (hlo : j + 2 * m ≤ x) (hhi : x < j + 2 * m + higherPeriod k m)
    (he : higherExpectedColor k m c x = higherExpectedColor k m c j) :
    (j + (k - 4) * m + 3 ≤ x ∧ x + 1 < j + (k + 2) * m) ∨
    (j + (2 * k - 4) * m + 2 ≤ x ∧ x < j + 2 * k * m) := by
  have hL := higherPeriod_lower (m := m) hk
  have hx : j + (x - j) = x := by omega
  have hnot : ¬ HigherDistance k m q (x - j) := by
    intro hd
    have hne := higherExpectedColor_nat_distance hk hm hq hc (by omega : 0 < x - j)
      (by omega : x - j ≤ 2 * higherPeriod k m) hd j
    rw [hx] at hne
    exact hne he.symm
  have hlow : j + (k - 4) * m + 3 ≤ x := by
    by_contra hbad
    apply hnot
    apply higher_first_band_distance hq (by omega)
    simp only [higherFirstBandUpper, heven, if_false]
    omega
  by_cases hfirst : x + 1 < j + (k + 2) * m
  · exact Or.inl ⟨hlow, hfirst⟩
  · right
    constructor
    · by_contra hbad
      apply hnot
      refine Or.inr (Or.inr ⟨heven, 0, by omega, ?_, ?_⟩)
      · simp only [zero_mul, zero_add]
        omega
      · simp only [zero_mul, zero_add]
        omega
    · have hLen : 2 * m + higherPeriod k m = 2 * k * m := by
        simp only [higherPeriod, heven, if_false]
        have hK : 2 * (k - 1) + 2 = 2 * k := by omega
        nlinarith only [hK]
      omega

set_option maxHeartbeats 800000 in
theorem higher_even_window_two_evenProgressions {k m q j : Nat} (hk : 10 ≤ k) (hm : 0 < m)
    (hq : 2 ≤ q) (heven : k % 2 ≠ 1) {c : Nat → Fin (k - 1)}
    (hc : HigherProperOn k m q c (3 * higherPeriod k m)) (color : Fin (k - 1))
    (hj : higherExpectedColor k m c j = color) :
    ∃ t t' : Nat, t ≠ t' ∧ expectedColorWindow k m c (j + 2 * m) color =
      evenProgression t m ∪ evenProgression t' m := by
  have hk5 : 5 ≤ k := by omega
  have hcard : (expectedColorWindow k m c (j + 2 * m) color).card = 2 * m := by
    simpa only [heven, if_false] using expectedColorWindow_card hk5 hm hq hc (j + 2 * m) color
  have hbands (x : Nat) (hx : x ∈ expectedColorWindow k m c (j + 2 * m) color) :=
    higher_even_anchor_window_bands hk5 hm hq heven hc (mem_expectedColorWindow.mp hx).1
      (mem_expectedColorWindow.mp hx).2.1 ((mem_expectedColorWindow.mp hx).2.2.trans hj.symm)
  have hmid : (k + 2) * m ≤ (2 * k - 4) * m :=
    Nat.mul_le_mul_right m (by omega)
  have hfirstLen : (k + 2) * m = (k - 4) * m + 6 * m := by
    have hK : k + 2 = (k - 4) + 6 := by omega
    rw [hK, Nat.add_mul]
  have hlastLen : 2 * k * m = (2 * k - 4) * m + 4 * m := by
    have hK : 2 * k = (2 * k - 4) + 4 := by omega
    calc
      2 * k * m = ((2 * k - 4) + 4) * m := congrArg (fun a : Nat => a * m) hK
      _ = (2 * k - 4) * m + 4 * m := by ring
  apply finset_two_evenProgressions hm hcard (fun x => x < j + (k + 2) * m)
  · intro x hx y hy hxp hyp hxy
    have hbx := hbands x hx
    have hby := hbands y hy
    have hxlo : j + (k - 4) * m + 3 ≤ x := by rcases hbx with h | h <;> omega
    have hyhi : y + 1 < j + (k + 2) * m := by rcases hby with h | h <;> omega
    have hsmall : y - x < 6 * m := by omega
    have heq : (x : Int) + (y - x : Nat) = y := by omega
    apply higherExpectedColor_even_small_gap hk hm hq heven hc hsmall x
    rw [heq]
    exact (mem_expectedColorWindow.mp hx).2.2.trans (mem_expectedColorWindow.mp hy).2.2.symm
  · intro x hx y hy hxp hyp hxy
    have hbx := hbands x hx
    have hby := hbands y hy
    have hxlo : j + (2 * k - 4) * m + 2 ≤ x := by rcases hbx with h | h <;> omega
    have hyhi : y < j + 2 * k * m := by rcases hby with h | h <;> omega
    have hsmall : y - x < 6 * m := by omega
    have heq : (x : Int) + (y - x : Nat) = y := by omega
    apply higherExpectedColor_even_small_gap hk hm hq heven hc hsmall x
    rw [heq]
    exact (mem_expectedColorWindow.mp hx).2.2.trans (mem_expectedColorWindow.mp hy).2.2.symm

theorem higher_even_expected_color_class {k m q : Nat} (hk : 10 ≤ k) (hm : 0 < m)
    (hq : 2 ≤ q) (heven : k % 2 ≠ 1) {c : Nat → Fin (k - 1)}
    (hc : HigherProperOn k m q c (3 * higherPeriod k m)) (color : Fin (k - 1)) :
    ∃ t t' : Nat, t ≠ t' ∧ ∀ i : Int, higherExpectedColor k m c i = color ↔
      (∃ s < m, i % (higherPeriod k m : Int) = ((t + 2 * s : Nat) : Int) % (higherPeriod k m : Int)) ∨
      (∃ s < m, i % (higherPeriod k m : Int) = ((t' + 2 * s : Nat) : Int) % (higherPeriod k m : Int)) := by
  obtain ⟨j, _, hj⟩ := higherExpectedColor_exists_nat (by omega : 5 ≤ k) hm hq hc color
  obtain ⟨t, t', hne, ht⟩ := higher_even_window_two_evenProgressions hk hm hq heven hc color hj
  refine ⟨t, t', hne, ?_⟩
  intro i
  rw [expectedColorWindow_full_class (by omega : 5 ≤ k) hm c (j + 2 * m) color i, ht]
  constructor
  · rintro ⟨x, hx, hmod⟩
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨s, hs, hxs⟩ := mem_evenProgression.mp hx
      exact Or.inl ⟨s, hs, by rwa [hxs]⟩
    · obtain ⟨s, hs, hxs⟩ := mem_evenProgression.mp hx
      exact Or.inr ⟨s, hs, by rwa [hxs]⟩
  · rintro (⟨s, hs, hmod⟩ | ⟨s, hs, hmod⟩)
    · exact ⟨t + 2 * s, Finset.mem_union.mpr (Or.inl (mem_evenProgression.mpr ⟨s, hs, rfl⟩)), hmod⟩
    · exact ⟨t' + 2 * s, Finset.mem_union.mpr (Or.inr (mem_evenProgression.mpr ⟨s, hs, rfl⟩)), hmod⟩

def ColorChange {α : Type*} (f : Int → α) (i : Int) : Prop := f i ≠ f (i - 2)

def EvenRunProperty {α : Type*} (m : Nat) (f : Int → α) : Prop :=
  ∀ i : Int, ColorChange f i → ∀ s : Nat, s < m → f (i + 2 * s) = f i

theorem evenRunProperty_of_block_classes {α : Type*} {L m : Nat} (f : Int → α)
    (hclasses : ∀ color : α, ∃ T : Set Int, ∀ i : Int, f i = color ↔
      ∃ t ∈ T, ∃ s < m, i % (L : Int) = (t + 2 * s) % (L : Int)) :
    EvenRunProperty m f := by
  intro i hi
  obtain ⟨T, hT⟩ := hclasses (f i)
  obtain ⟨t, ht, s, hs, hmod⟩ := (hT i).mp rfl
  have hs0 : s = 0 := by
    by_contra hsnot
    have hprev : (i - 2) % (L : Int) = (t + 2 * (s - 1 : Nat)) % (L : Int) := by
      have he : t + 2 * (s - 1 : Nat) = t + 2 * (s : Int) - 2 := by omega
      rw [he]
      simp only [Int.sub_emod, Int.emod_emod, hmod]
    have hcolor := (hT (i - 2)).mpr ⟨t, ht, s - 1, by omega, hprev⟩
    exact hi hcolor.symm
  have htmod : i % (L : Int) = t % (L : Int) := by simpa only [hs0, Nat.cast_zero, mul_zero, add_zero] using hmod
  intro u hu
  apply (hT (i + 2 * u)).mpr
  refine ⟨t, ht, u, hu, ?_⟩
  simp only [Int.add_emod, Int.emod_emod, htmod]

theorem color_change_exists {α : Type*} (f : Int → α) (m : Nat) (x : Int)
    (hne : f (x + 2 * m) ≠ f x) :
    ∃ s < m, ColorChange f (x + 2 * (s + 1 : Nat)) := by
  by_contra hnone
  have hnot (s : Nat) (hs : s < m) :
      f (x + 2 * (s + 1 : Nat)) = f (x + 2 * (s + 1 : Nat) - 2) := by
    by_contra h
    exact hnone ⟨s, hs, h⟩
  have hflat : ∀ n : Nat, n ≤ m → f (x + 2 * n) = f x := by
    intro n
    induction n with
    | zero => intro _; simp only [Nat.cast_zero, mul_zero, add_zero]
    | succ n ih =>
      intro hn
      have hs := hnot n (by omega)
      have he : x + 2 * (n + 1 : Nat) - 2 = x + 2 * (n : Int) := by omega
      rw [he] at hs
      exact hs.trans (ih (by omega))
  exact hne (hflat m (Nat.le_refl _))

theorem even_run_no_change_inside {α : Type*} {m : Nat} {f : Int → α}
    (hrun : EvenRunProperty m f) {i : Int} (hi : ColorChange f i)
    {s : Nat} (hs0 : 0 < s) (hsm : s < m) : ¬ ColorChange f (i + 2 * s) := by
  intro hchange
  have hsame := hrun i hi s hsm
  have hprev := hrun i hi (s - 1) (by omega)
  have he : i + 2 * (s : Int) - 2 = i + 2 * (s - 1 : Nat) := by omega
  apply hchange
  rw [he]
  exact hsame.trans hprev.symm

theorem even_run_change_spacing {α : Type*} {m : Nat} {f : Int → α}
    (hrun : EvenRunProperty m f) {i j : Int} (hi : ColorChange f i) (hj : ColorChange f j)
    (hij : i < j) (hpar : i % 2 = j % 2) : 2 * (m : Int) ≤ j - i := by
  by_contra hnot
  let s := (j - i).toNat / 2
  have hs0 : 0 < s := by omega
  have hsm : s < m := by omega
  have he : j = i + 2 * s := by omega
  rw [he] at hj
  exact even_run_no_change_inside hrun hi hs0 hsm hj

theorem even_run_change_forward {α : Type*} {m : Nat} {f : Int → α} (hm : 0 < m)
    (hrun : EvenRunProperty m f) (havoid : ∀ i : Int, f (i + 2 * m) ≠ f i)
    {i : Int} (hi : ColorChange f i) : ColorChange f (i + 2 * m) := by
  have hprev := hrun i hi (m - 1) (by omega)
  have he : i + 2 * (m : Int) - 2 = i + 2 * (m - 1 : Nat) := by omega
  intro hsame
  apply havoid i
  exact hsame.trans (by rw [he]; exact hprev)

theorem even_run_change_backward {α : Type*} {m : Nat} {f : Int → α}
    (hrun : EvenRunProperty m f) (havoid : ∀ i : Int, f (i + 2 * m) ≠ f i)
    {i : Int} (hi : ColorChange f i) : ColorChange f (i - 2 * m) := by
  obtain ⟨s, hs, ht⟩ := color_change_exists f m (i - 2 * m - 2) (havoid _)
  have hlt : i - 2 * (m : Int) - 2 + 2 * (s + 1 : Nat) < i := by omega
  have hpar : (i - 2 * (m : Int) - 2 + 2 * (s + 1 : Nat)) % 2 = i % 2 := by omega
  have hgap := even_run_change_spacing hrun ht hi hlt hpar
  have he : i - 2 * (m : Int) - 2 + 2 * (s + 1 : Nat) = i - 2 * m := by omega
  rwa [he] at ht

theorem even_run_changes_periodic {α : Type*} {m : Nat} {f : Int → α} (hm : 0 < m)
    (hrun : EvenRunProperty m f) (havoid : ∀ i : Int, f (i + 2 * m) ≠ f i) (i : Int) :
    ColorChange f (i + 2 * m) ↔ ColorChange f i := by
  constructor
  · intro hi
    have hback := even_run_change_backward hrun havoid hi
    simpa only [add_sub_cancel_right] using hback
  · exact even_run_change_forward hm hrun havoid

theorem higher_distance_two_m {k m q : Nat} (hk : 5 ≤ k) (hq : 2 ≤ q) :
    HigherDistance k m q (2 * m) := by
  apply higher_first_band_distance hq (Nat.le_refl _)
  unfold higherFirstBandUpper
  split
  · have h := Nat.mul_le_mul_right m (by omega : 2 ≤ k - 3)
    omega
  · have h := Nat.mul_le_mul_right m (by omega : 2 ≤ k - 4)
    omega

theorem higherExpectedColor_ne_two_m {k m q : Nat} (hk : 5 ≤ k) (hm : 0 < m) (hq : 2 ≤ q)
    {c : Nat → Fin (k - 1)} (hc : HigherProperOn k m q c (3 * higherPeriod k m)) (i : Int) :
    higherExpectedColor k m c (i + 2 * m) ≠ higherExpectedColor k m c i := by
  have hL := higherPeriod_lower (m := m) hk
  have hne := higherExpectedColor_int_distance hk hm hq hc (by omega : 0 < 2 * m)
    (by omega : 2 * m ≤ 2 * higherPeriod k m) (higher_distance_two_m hk hq) i
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using hne.symm

theorem evenRunProperty_of_one_block {α : Type*} {L m : Nat} (f : Int → α)
    (hclasses : ∀ color : α, ∃ t : Nat, ∀ i : Int, f i = color ↔
      ∃ s < m, i % (L : Int) = ((t + 2 * s : Nat) : Int) % (L : Int)) :
    EvenRunProperty m f := by
  apply evenRunProperty_of_block_classes (L := L) f
  intro color
  obtain ⟨t, ht⟩ := hclasses color
  refine ⟨{(t : Int)}, ?_⟩
  intro i
  constructor
  · intro hi
    obtain ⟨s, hs, hmod⟩ := (ht i).mp hi
    refine ⟨t, by simp, s, hs, ?_⟩
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hmod
  · rintro ⟨t₀, ht₀, s, hs, hmod⟩
    have he : t₀ = (t : Int) := Set.mem_singleton_iff.mp ht₀
    subst t₀
    apply (ht i).mpr
    exact ⟨s, hs, by simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hmod⟩

theorem evenRunProperty_of_two_blocks {α : Type*} {L m : Nat} (f : Int → α)
    (hclasses : ∀ color : α, ∃ t t' : Nat, ∀ i : Int, f i = color ↔
      (∃ s < m, i % (L : Int) = ((t + 2 * s : Nat) : Int) % (L : Int)) ∨
      (∃ s < m, i % (L : Int) = ((t' + 2 * s : Nat) : Int) % (L : Int))) :
    EvenRunProperty m f := by
  apply evenRunProperty_of_block_classes (L := L) f
  intro color
  obtain ⟨t, t', ht⟩ := hclasses color
  refine ⟨{(t : Int), (t' : Int)}, ?_⟩
  intro i
  constructor
  · intro hi
    rcases (ht i).mp hi with ⟨s, hs, hmod⟩ | ⟨s, hs, hmod⟩
    · refine ⟨t, by simp, s, hs, ?_⟩
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hmod
    · refine ⟨t', by simp, s, hs, ?_⟩
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hmod
  · rintro ⟨t₀, ht₀, s, hs, hmod⟩
    apply (ht i).mpr
    rcases Set.mem_insert_iff.mp ht₀ with h | h
    · subst t₀
      exact Or.inl ⟨s, hs, by simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hmod⟩
    · have he : t₀ = (t' : Int) := Set.mem_singleton_iff.mp h
      subst t₀
      exact Or.inr ⟨s, hs, by simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hmod⟩

theorem higher_odd_expected_even_runs {k m q : Nat} (hk : 7 ≤ k) (hm : 0 < m)
    (hq : 2 ≤ q) (hodd : k % 2 = 1) {c : Nat → Fin (k - 1)}
    (hc : HigherProperOn k m q c (3 * higherPeriod k m)) :
    EvenRunProperty m (higherExpectedColor k m c) := by
  exact evenRunProperty_of_one_block _ (higher_odd_expected_color_class hk hm hq hodd hc)

theorem higher_even_expected_even_runs {k m q : Nat} (hk : 10 ≤ k) (hm : 0 < m)
    (hq : 2 ≤ q) (heven : k % 2 ≠ 1) {c : Nat → Fin (k - 1)}
    (hc : HigherProperOn k m q c (3 * higherPeriod k m)) :
    EvenRunProperty m (higherExpectedColor k m c) := by
  apply evenRunProperty_of_two_blocks (L := higherPeriod k m) _
  intro color
  obtain ⟨t, t', _, ht⟩ := higher_even_expected_color_class hk hm hq heven hc color
  exact ⟨t, t', ht⟩

theorem higher_expected_even_runs {k m q : Nat} (hk : 7 ≤ k) (hk8 : k ≠ 8) (hm : 0 < m)
    (hq : 2 ≤ q) {c : Nat → Fin (k - 1)}
    (hc : HigherProperOn k m q c (3 * higherPeriod k m)) :
    EvenRunProperty m (higherExpectedColor k m c) := by
  by_cases hodd : k % 2 = 1
  · exact higher_odd_expected_even_runs hk hm hq hodd hc
  · exact higher_even_expected_even_runs (by omega) hm hq hodd hc

theorem int_periodic_eq_mod {α : Type*} {p : Int} (f : Int → α)
    (hp : Function.Periodic f p) (i : Int) : f i = f (i % p) := by
  have h := hp.int_mul (i / p) (i % p)
  simp only [Int.cast_id] at h
  rwa [Int.emod_add_ediv_mul] at h

theorem even_run_change_unique_in_period {α : Type*} {m : Nat} {f : Int → α}
    (hrun : EvenRunProperty m f) {i j : Int} (hi : ColorChange f i) (hj : ColorChange f j)
    (hi0 : 0 ≤ i) (him : i < 2 * m) (hj0 : 0 ≤ j) (hjm : j < 2 * m)
    (hpar : i % 2 = j % 2) : i = j := by
  rcases lt_trichotomy i j with h | h | h
  · have hs := even_run_change_spacing hrun hi hj h hpar
    omega
  · exact h
  · have hs := even_run_change_spacing hrun hj hi h hpar.symm
    omega

theorem even_run_change_exists_parity {α : Type*} {m : Nat} {f : Int → α}
    (havoid : ∀ i : Int, f (i + 2 * m) ≠ f i) {b : Nat} (hb : b < 2) :
    ∃ t : Nat, t < 2 * m ∧ t % 2 = b ∧ ColorChange f t := by
  obtain ⟨s, hs, ht⟩ := color_change_exists f m ((b : Int) - 2) (havoid _)
  have he : (b : Int) - 2 + 2 * (s + 1 : Nat) = (2 * s + b : Nat) := by omega
  refine ⟨2 * s + b, by omega, by omega, ?_⟩
  rwa [he] at ht

theorem even_run_phase_structure {α : Type*} {m : Nat} {f : Int → α} (hm : 0 < m)
    (hrun : EvenRunProperty m f) (havoid : ∀ i : Int, f (i + 2 * m) ≠ f i) :
    ∃ tEven tOdd : Nat, tEven < 2 * m ∧ tOdd < 2 * m ∧ tEven % 2 = 0 ∧ tOdd % 2 = 1 ∧
      ∀ i : Int, ColorChange f i ↔ i % (2 * m : Int) = tEven ∨ i % (2 * m : Int) = tOdd := by
  obtain ⟨te, hte, htepar, hechange⟩ := even_run_change_exists_parity havoid (by omega : 0 < 2)
  obtain ⟨td, hto, htopar, hochange⟩ := even_run_change_exists_parity havoid (by omega : 1 < 2)
  refine ⟨te, td, hte, hto, htepar, htopar, ?_⟩
  have hp : Function.Periodic (ColorChange f) (2 * m : Int) :=
    fun i => propext (even_run_changes_periodic hm hrun havoid i)
  have hepar : (te : Int) % 2 = 0 := by exact_mod_cast htepar
  have hopar : (td : Int) % 2 = 1 := by exact_mod_cast htopar
  have hpos : (0 : Int) < 2 * m := by omega
  intro i
  rw [int_periodic_eq_mod (ColorChange f) hp i]
  have hlo := Int.emod_nonneg i (ne_of_gt hpos)
  have hhi := Int.emod_lt_of_pos i hpos
  constructor
  · intro hc
    by_cases hpar : (i % (2 * m : Int)) % 2 = 0
    · left
      exact even_run_change_unique_in_period hrun hc hechange hlo hhi (by omega) (by omega)
        (hpar.trans hepar.symm)
    · right
      have hpar' : (i % (2 * m : Int)) % 2 = 1 := by omega
      exact even_run_change_unique_in_period hrun hc hochange hlo hhi (by omega) (by omega)
        (hpar'.trans hopar.symm)
  · rintro (he | ho)
    · rwa [he]
    · rwa [ho]

def HigherExpectedLocalStructure (k m : Nat) (c : Nat → Fin (k - 1)) : Prop :=
  ∃ tEven tOdd : Nat, tEven < 2 * m ∧ tOdd < 2 * m ∧ tEven % 2 = 0 ∧ tOdd % 2 = 1 ∧
    ∀ i : Int, higherExpectedColor k m c i ≠ higherExpectedColor k m c (i - 2) ↔
      i % (2 * m : Int) = tEven ∨ i % (2 * m : Int) = tOdd

theorem higher_expected_structure_of_even_runs {k m q : Nat} (hk : 5 ≤ k) (hm : 0 < m)
    (hq : 2 ≤ q) {c : Nat → Fin (k - 1)}
    (hc : HigherProperOn k m q c (3 * higherPeriod k m))
    (hrun : EvenRunProperty m (higherExpectedColor k m c)) : HigherExpectedLocalStructure k m c := by
  exact even_run_phase_structure hm hrun (higherExpectedColor_ne_two_m hk hm hq hc)

theorem higher_expected_local_structure {k m q : Nat} (hk : 7 ≤ k) (hk8 : k ≠ 8)
    (hm : 0 < m) (hq : 2 ≤ q) {c : Nat → Fin (k - 1)}
    (hc : HigherProperOn k m q c (3 * higherPeriod k m)) : HigherExpectedLocalStructure k m c := by
  exact higher_expected_structure_of_even_runs (by omega) hm hq hc
    (higher_expected_even_runs hk hk8 hm hq hc)

def SmallRingAdjacent (n : Nat) (a b : Fin n × Fin 3) : Prop :=
  (a.1 = b.1 ∧ Nat.dist a.2.val b.2.val = 1) ∨
  ((b.1.val + n - a.1.val) % n = 1 ∧ a.2.val ≤ b.2.val + 1) ∨
  ((a.1.val + n - b.1.val) % n = 1 ∧ b.2.val ≤ a.2.val + 1) ∨
  (n = 7 ∧ ((b.1.val + n - a.1.val) % n = 2 ∨
    (a.1.val + n - b.1.val) % n = 2))

instance {n : Nat} (a b : Fin n × Fin 3) : Decidable (SmallRingAdjacent n a b) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))

def smallRingLift {n : Nat} (a : Fin n × Fin 2) : Fin n × Fin 3 :=
  (a.1, ⟨a.2.val, by have := a.2.isLt; omega⟩)

def SmallRingBaseOption {n : Nat} (a : Fin n × Fin 2) : Prop :=
  a.2.val = 0 ∧ a.1.val ≤ 1

instance {n : Nat} (a : Fin n × Fin 2) : Decidable (SmallRingBaseOption a) :=
  inferInstanceAs (Decidable (_ ∧ _))

set_option maxRecDepth 100000 in
theorem small_rings_three_have_edge {n : Nat} (hn : n = 5 ∨ n = 7) :
    ∀ a b c : Fin n × Fin 2, a ≠ b → a ≠ c → b ≠ c →
      SmallRingAdjacent n (smallRingLift a) (smallRingLift b) ∨
      SmallRingAdjacent n (smallRingLift a) (smallRingLift c) ∨
      SmallRingAdjacent n (smallRingLift b) (smallRingLift c) := by
  rcases hn with rfl | rfl <;> decide

set_option maxRecDepth 100000 in
theorem small_ring_two_options_certificate {n : Nat} (hn : n = 5 ∨ n = 7)
    (hnpos : 0 < n) :
    ∀ a b : Fin n × Fin 2, a ≠ b →
      ¬ SmallRingAdjacent n (smallRingLift a) (smallRingLift b) →
      ¬ SmallRingAdjacent n (⟨0, hnpos⟩, 2) (smallRingLift a) →
      ¬ SmallRingAdjacent n (⟨0, hnpos⟩, 2) (smallRingLift b) →
      SmallRingBaseOption a ∨ SmallRingBaseOption b := by
  rcases hn with rfl | rfl <;> decide +revert

theorem small_ring_color_class_card_le_two {n : Nat} (hn : n = 5 ∨ n = 7)
    {α : Type*} [DecidableEq α] (f : Fin n × Fin 2 → α)
    (hf : ∀ a b, SmallRingAdjacent n (smallRingLift a) (smallRingLift b) → f a ≠ f b)
    (color : α) : (Finset.univ.filter (fun a => f a = color)).card ≤ 2 := by
  by_contra hnone
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ :=
    Finset.two_lt_card_iff.mp (show 2 < (Finset.univ.filter (fun a => f a = color)).card by omega)
  have ha' := (Finset.mem_filter.mp ha).2
  have hb' := (Finset.mem_filter.mp hb).2
  have hc' := (Finset.mem_filter.mp hc).2
  rcases small_rings_three_have_edge hn a b c hab hac hbc with h | h | h
  · exact hf a b h (ha'.trans hb'.symm)
  · exact hf a c h (ha'.trans hc'.symm)
  · exact hf b c h (hb'.trans hc'.symm)

theorem small_ring_color_class_card {n : Nat} (hn : n = 5 ∨ n = 7)
    (f : Fin n × Fin 2 → Fin n)
    (hf : ∀ a b, SmallRingAdjacent n (smallRingLift a) (smallRingLift b) → f a ≠ f b)
    (color : Fin n) : (Finset.univ.filter (fun a => f a = color)).card = 2 := by
  apply finite_fibers_eq_of_le f 2 (by simp)
  exact small_ring_color_class_card_le_two hn f hf

theorem small_ring_coloring_two_options {n : Nat} (hn : n = 5 ∨ n = 7) (hnpos : 0 < n)
    (f : Fin n × Fin 3 → Fin n)
    (hf : ∀ a b, SmallRingAdjacent n a b → f a ≠ f b) :
    ∃ a : Fin n × Fin 2, SmallRingBaseOption a ∧ f (smallRingLift a) = f (⟨0, hnpos⟩, 2) := by
  have hcard := small_ring_color_class_card hn (fun a => f (smallRingLift a))
    (fun a b => hf _ _) (f (⟨0, hnpos⟩, 2))
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (show 1 <
      (Finset.univ.filter (fun a : Fin n × Fin 2 =>
        f (smallRingLift a) = f (⟨0, hnpos⟩, 2))).card by omega)
  have ha' := (Finset.mem_filter.mp ha).2
  have hb' := (Finset.mem_filter.mp hb).2
  have hop := small_ring_two_options_certificate hn hnpos a b hab
    (fun h => hf _ _ h (ha'.trans hb'.symm))
    (fun h => hf _ _ h ha'.symm) (fun h => hf _ _ h hb'.symm)
  rcases hop with hop | hop
  · exact ⟨a, hop, ha'⟩
  · exact ⟨b, hop, hb'⟩

def smallRingIndex {n : Nat} (m : Nat) (a : Fin n × Fin 3) : Int :=
  2 * m * a.1.val + a.2.val

theorem higherExpectedColor_int_difference {k m q : Nat} (hk : 5 ≤ k) (hm : 0 < m)
    (hq : 2 ≤ q) {c : Nat → Fin (k - 1)}
    (hc : HigherProperOn k m q c (3 * higherPeriod k m)) {i j : Int}
    (hpos : 0 < j - i) (hle : j - i ≤ 2 * higherPeriod k m)
    (hd : HigherDistance k m q (j - i).toNat) :
    higherExpectedColor k m c i ≠ higherExpectedColor k m c j := by
  have he : i + ((j - i).toNat : Int) = j := by omega
  have h := higherExpectedColor_int_distance hk hm hq hc (by omega) (by omega) hd i
  rwa [he] at h

theorem higherExpectedColor_ne_one {k m q : Nat} (hk : 5 ≤ k) (hm : 0 < m)
    (hq : 2 ≤ q) {c : Nat → Fin (k - 1)}
    (hc : HigherProperOn k m q c (3 * higherPeriod k m)) (i : Int) :
    higherExpectedColor k m c i ≠ higherExpectedColor k m c (i + 1) := by
  exact higherExpectedColor_int_distance (d := 1) hk hm hq hc (by omega)
    (by have := higherPeriod_lower (m := m) hk; omega)
    (Or.inl ⟨by omega, by omega, by omega⟩) i

theorem higherExpectedColor_small_ring_step {k m q : Nat} (hk : 6 ≤ k) (hm : 0 < m)
    (hq : 2 ≤ q) (heven : k % 2 ≠ 1) {c : Nat → Fin (k - 1)}
    (hc : HigherProperOn k m q c (3 * higherPeriod k m)) (x : Int)
    (a b : Fin 3) (hab : a.val ≤ b.val + 1) :
    higherExpectedColor k m c (x + a.val) ≠ higherExpectedColor k m c (x + 2 * m + b.val) := by
  let d : Int := 2 * m + b.val - a.val
  have ha := a.isLt
  have hb := b.isLt
  have hdlo : 2 * m - 1 ≤ d := by omega
  have hdhi : d ≤ 2 * m + 2 := by omega
  have hL := higherPeriod_lower (m := m) (by omega : 5 ≤ k)
  have hcast : (d.toNat : Int) = d := by omega
  apply higherExpectedColor_int_difference (by omega) hm hq hc (by omega) (by omega)
  have he : x + 2 * m + b.val - (x + a.val) = d := by dsimp only [d]; ring
  rw [he]
  by_cases hs : d.toNat < 2 * m
  · exact Or.inl ⟨by omega, hs, by omega⟩
  · apply higher_first_band_distance hq (by omega)
    have hmul := Nat.mul_le_mul_right m (by omega : 2 ≤ k - 4)
    simp only [higherFirstBandUpper, heven, if_false]
    omega

theorem higherExpectedColor_second_ring_step {m q : Nat} (hm : 0 < m) (hq : 2 ≤ q)
    {c : Nat → Fin (8 - 1)}
    (hc : HigherProperOn 8 m q c (3 * higherPeriod 8 m)) (x : Int) (a b : Fin 3) :
    higherExpectedColor 8 m c (x + a.val) ≠ higherExpectedColor 8 m c (x + 4 * m + b.val) := by
  have ha := a.isLt
  have hb := b.isLt
  have hL := higherPeriod_lower (m := m) (by omega : 5 ≤ 8)
  apply higherExpectedColor_int_difference (by omega) hm hq hc (by omega) (by omega)
  apply higher_first_band_distance hq (by omega)
  norm_num [higherFirstBandUpper]
  omega

theorem higherExpectedColor_ring_shift {α : Type*} {k m a b r : Nat}
    (heven : k % 2 ≠ 1) (c : Nat → α) (x : Int) (s : Nat)
    (hrow : Int.ModEq (k - 1 : Nat) (b : Int) ((a + r : Nat) : Int)) :
    higherExpectedColor k m c (x + 2 * m * b + s) =
      higherExpectedColor k m c (x + 2 * m * a + 2 * m * r + s) := by
  have hL : (higherPeriod k m : Int) = 2 * m * (k - 1 : Nat) := by
    simp only [higherPeriod, heven, if_false, Nat.cast_mul, Nat.cast_ofNat]
    ring
  apply higherExpectedColor_eq_of_mod_eq
  rw [hL]
  change Int.ModEq (2 * (m : Int) * (k - 1 : Nat))
    (x + 2 * m * b + s) (x + 2 * m * a + 2 * m * r + s)
  have h := (hrow.mul_left' (c := 2 * (m : Int))).add_left (x + s)
  convert h using 1 <;> push_cast <;> ring

theorem small_ring_rows_consecutive {n : Nat} (hn : n = 5 ∨ n = 7)
    (a b : Fin n) (hr : (b.val + n - a.val) % n = 1) :
    Int.ModEq (n : Int) (b : Int) ((a.val + 1 : Nat) : Int) := by
  have ha := a.isLt
  have hb := b.isLt
  change (b.val : Int) % n = ((a.val + 1 : Nat) : Int) % n
  rcases hn with rfl | rfl <;> omega

theorem small_ring_rows_second (a b : Fin 7) (hr : (b.val + 7 - a.val) % 7 = 2) :
    Int.ModEq (7 : Int) (b : Int) ((a.val + 2 : Nat) : Int) := by
  have ha := a.isLt
  have hb := b.isLt
  change (b.val : Int) % 7 = ((a.val + 2 : Nat) : Int) % 7
  omega

theorem small_ring_expected_adjacent {k m q : Nat} (hk : k = 6 ∨ k = 8) (hm : 0 < m)
    (hq : 2 ≤ q) {c : Nat → Fin (k - 1)}
    (hc : HigherProperOn k m q c (3 * higherPeriod k m)) (i : Int)
    (a b : Fin (k - 1) × Fin 3) (hab : SmallRingAdjacent (k - 1) a b) :
    higherExpectedColor k m c (i + smallRingIndex m a) ≠
      higherExpectedColor k m c (i + smallRingIndex m b) := by
  have hk6 : 6 ≤ k := by omega
  have heven : k % 2 ≠ 1 := by omega
  have hn : k - 1 = 5 ∨ k - 1 = 7 := by omega
  have hstep : ∀ u v : Fin (k - 1) × Fin 3,
      (v.1.val + (k - 1) - u.1.val) % (k - 1) = 1 → u.2.val ≤ v.2.val + 1 →
      higherExpectedColor k m c (i + smallRingIndex m u) ≠
        higherExpectedColor k m c (i + smallRingIndex m v) := by
    intro u v hr hb
    have hrow := small_ring_rows_consecutive hn u.1 v.1 hr
    have he := higherExpectedColor_ring_shift (m := m) heven c i v.2.val hrow
    have hne := higherExpectedColor_small_ring_step hk6 hm hq heven hc
      (i + 2 * m * u.1.val) u.2 v.2 hb
    simp only [Nat.cast_one, mul_one] at he
    simp only [smallRingIndex, ← add_assoc]
    rw [he]
    exact hne
  rcases hab with ⟨hr, hb⟩ | ⟨hr, hb⟩ | ⟨hr, hb⟩ | ⟨hn7, hr⟩
  · have hrow : a.1.val = b.1.val := congrArg Fin.val hr
    have hd : a.2.val + 1 = b.2.val ∨ b.2.val + 1 = a.2.val := by
      simp only [Nat.dist] at hb
      omega
    rcases hd with hd | hd
    · have he : i + smallRingIndex m b = i + smallRingIndex m a + 1 := by
        simp only [smallRingIndex, hrow]
        omega
      rw [he]
      exact higherExpectedColor_ne_one (by omega) hm hq hc _
    · have he : i + smallRingIndex m a = i + smallRingIndex m b + 1 := by
        simp only [smallRingIndex, hrow]
        omega
      rw [he]
      exact (higherExpectedColor_ne_one (by omega) hm hq hc _).symm
  · exact hstep a b hr hb
  · exact (hstep b a hr hb).symm
  · have hk8 : k = 8 := by omega
    subst k
    have hsecond : ∀ u v : Fin 7 × Fin 3, (v.1.val + 7 - u.1.val) % 7 = 2 →
        higherExpectedColor 8 m c (i + smallRingIndex m u) ≠
          higherExpectedColor 8 m c (i + smallRingIndex m v) := by
      intro u v hr
      have hrow := small_ring_rows_second u.1 v.1 hr
      have he := higherExpectedColor_ring_shift (k := 8) (m := m) (by omega) c i v.2.val hrow
      have hne := higherExpectedColor_second_ring_step hm hq hc
        (i + 2 * m * u.1.val) u.2 v.2
      have hmul : 2 * (m : Int) * 2 = 4 * m := by ring
      simp only [Nat.cast_ofNat] at he
      rw [hmul] at he
      simp only [smallRingIndex, ← add_assoc]
      rw [he]
      exact hne
    rcases hr with hr | hr
    · exact hsecond a b hr
    · exact (hsecond b a hr).symm

def IntColorTwoOptions {α : Type*} (m : Nat) (f : Int → α) : Prop :=
  ∀ i : Int, f i = f (i - 2) ∨ f i = f (i + 2 * m - 2)

theorem color_change_forward_of_two_options {α : Type*} {m : Nat} {f : Int → α}
    (hop : IntColorTwoOptions m f) (hne : ∀ i : Int, f (i + 2 * m) ≠ f i)
    {i : Int} (hi : ColorChange f i) : ColorChange f (i + 2 * m) := by
  intro hsame
  rcases hop i with h | h
  · exact hi h
  · exact hne i (hsame.trans h.symm)

theorem color_change_iterate {α : Type*} {p : Int} {f : Int → α}
    (hforward : ∀ i, ColorChange f i → ColorChange f (i + p))
    (i : Int) (n : Nat) (hi : ColorChange f i) : ColorChange f (i + n * p) := by
  induction n with
  | zero => simpa only [Nat.cast_zero, zero_mul, add_zero] using hi
  | succ n ih =>
    have h := hforward (i + n * p) ih
    convert h using 1
    push_cast
    ring

theorem color_change_periodic_of_periodic {α : Type*} {p : Int} {f : Int → α}
    (hp : Function.Periodic f p) : Function.Periodic (ColorChange f) p := by
  intro i
  apply propext
  have he : i + p - 2 = (i - 2) + p := by ring
  simp only [ColorChange, he, hp i, hp (i - 2)]

theorem color_change_periodic_of_forward {α : Type*} {p : Int} {n : Nat} {f : Int → α}
    (hn : 0 < n) (hp : Function.Periodic f (n * p))
    (hforward : ∀ i, ColorChange f i → ColorChange f (i + p)) :
    Function.Periodic (ColorChange f) p := by
  have hlong := color_change_periodic_of_periodic hp
  intro i
  apply propext
  constructor
  · intro hi
    have h := color_change_iterate hforward (i + p) (n - 1) hi
    have hncast : ((n - 1 : Nat) : Int) + 1 = n := by omega
    have he : i + p + (n - 1 : Nat) * p = i + n * p := by rw [← hncast]; ring
    rw [he, hlong i] at h
    exact h
  · exact hforward i

theorem color_change_periodic_of_two_options {α : Type*} {m n : Nat} {f : Int → α}
    (hn : 0 < n) (hp : Function.Periodic f (n * (2 * m : Int)))
    (hop : IntColorTwoOptions m f) (hne : ∀ i : Int, f (i + 2 * m) ≠ f i) :
    Function.Periodic (ColorChange f) (2 * m : Int) := by
  apply color_change_periodic_of_forward hn hp
  intro i hi
  exact color_change_forward_of_two_options hop hne hi

theorem higher_small_expected_two_options {k m q : Nat} (hk : k = 6 ∨ k = 8)
    (hm : 0 < m) (hq : 2 ≤ q) {c : Nat → Fin (k - 1)}
    (hc : HigherProperOn k m q c (3 * higherPeriod k m)) :
    IntColorTwoOptions m (higherExpectedColor k m c) := by
  intro i
  let f : Fin (k - 1) × Fin 3 → Fin (k - 1) := fun a =>
    higherExpectedColor k m c ((i - 2) + smallRingIndex m a)
  obtain ⟨a, ha, he⟩ := small_ring_coloring_two_options (by omega : k - 1 = 5 ∨ k - 1 = 7)
    (by omega : 0 < k - 1) f (small_ring_expected_adjacent hk hm hq hc (i - 2))
  have htop : f (⟨0, by omega⟩, 2) = higherExpectedColor k m c i := by
    dsimp only [f, smallRingIndex]
    congr 1
    norm_num
  rw [htop] at he
  have hzero : a.2.val = 0 := ha.1
  have hrow : a.1.val = 0 ∨ a.1.val = 1 := by have := ha.2; omega
  dsimp only [f, smallRingIndex, smallRingLift] at he
  rcases hrow with hr | hr
  · left
    simpa only [hr, hzero, Nat.cast_zero, mul_zero, add_zero] using he.symm
  · right
    have hx : (i - 2) + (2 * (m : Int) * 1 + 0) = i + 2 * m - 2 := by ring
    simpa only [hr, hzero, Nat.cast_one, Nat.cast_zero, hx] using he.symm

theorem higher_small_color_changes_periodic {k m q : Nat} (hk : k = 6 ∨ k = 8)
    (hm : 0 < m) (hq : 2 ≤ q) {c : Nat → Fin (k - 1)}
    (hc : HigherProperOn k m q c (3 * higherPeriod k m)) :
    Function.Periodic (ColorChange (higherExpectedColor k m c)) (2 * m : Int) := by
  have heven : k % 2 ≠ 1 := by omega
  have hL : (higherPeriod k m : Int) = (k - 1 : Nat) * (2 * m : Int) := by
    simp only [higherPeriod, heven, if_false, Nat.cast_mul, Nat.cast_ofNat]
    ring
  have hp : Function.Periodic (higherExpectedColor k m c) ((k - 1 : Nat) * (2 * m : Int)) := by
    rw [← hL]
    exact higherExpectedColor_periodic k m c
  exact color_change_periodic_of_two_options (by omega : 0 < k - 1) hp
    (higher_small_expected_two_options hk hm hq hc)
    (higherExpectedColor_ne_two_m (by omega) hm hq hc)

theorem periodic_color_change_multiple {α : Type*} {p A : Int} {f : Int → α}
    (hp : Function.Periodic (ColorChange f) p) (hA : ∃ t : Int, A = t * p) (i : Int) :
    ColorChange f (i + A) = ColorChange f i := by
  obtain ⟨t, rfl⟩ := hA
  simpa only [Int.cast_id] using hp.int_mul t i

theorem ring_duplicate_freezes {α : Type*} {m : Nat} {A : Int} {f : Int → α}
    (hop : IntColorTwoOptions m f)
    (hp : Function.Periodic (ColorChange f) (2 * m : Int))
    (hA : ∃ t : Int, A = t * (2 * m))
    (hcross : ∀ i : Int, f (i + A + 2 - 2 * m) ≠ f i)
    (i : Int) (hi : f (i + A) = f i) (s : Nat) :
    f (i + 2 * s) = f i ∧ f (i + A + 2 * s) = f i := by
  induction s with
  | zero =>
    simpa only [Nat.cast_zero, mul_zero, add_zero] using And.intro (rfl : f i = f i) hi
  | succ s ih =>
    let y : Int := i + A + 2 * (s + 1 : Nat) - 2 * m
    have hy : y + 2 * m - 2 = i + A + 2 * s := by dsimp only [y]; push_cast; ring
    have hx : y = (i + 2 * s) + A + 2 - 2 * m := by dsimp only [y]; push_cast; ring
    have hne : f y ≠ f (y + 2 * m - 2) := by
      rw [hy, hx, ih.2, ← ih.1]
      exact hcross (i + 2 * s)
    have hynot : ¬ ColorChange f y := by
      intro hchange
      rcases hop y with h | h
      · exact hchange h
      · exact hne h
    have hnext : y + 2 * m = i + A + 2 * (s + 1 : Nat) := by dsimp only [y]; ring
    have hright : ¬ ColorChange f (i + A + 2 * (s + 1 : Nat)) := by
      rw [← hnext, hp y]
      exact hynot
    have hleft : ¬ ColorChange f (i + 2 * (s + 1 : Nat)) := by
      have he : i + A + 2 * (s + 1 : Nat) = (i + 2 * (s + 1 : Nat)) + A := by ring
      rw [he, periodic_color_change_multiple hp hA] at hright
      exact hright
    simp only [ColorChange, not_not] at hleft hright
    have hlprev : i + 2 * (s + 1 : Nat) - 2 = i + 2 * s := by push_cast; ring
    have hrprev : i + A + 2 * (s + 1 : Nat) - 2 = i + A + 2 * s := by push_cast; ring
    rw [hlprev] at hleft
    rw [hrprev] at hright
    exact ⟨hleft.trans ih.1, hright.trans ih.2⟩

theorem ring_gap_color_ne {α : Type*} {m : Nat} {A : Int} {f : Int → α}
    (hop : IntColorTwoOptions m f)
    (hp : Function.Periodic (ColorChange f) (2 * m : Int))
    (hA : ∃ t : Int, A = t * (2 * m))
    (hcross : ∀ i : Int, f (i + A + 2 - 2 * m) ≠ f i)
    (hne : ∀ i : Int, f (i + 2 * m) ≠ f i) (i : Int) : f (i + A) ≠ f i := by
  intro hi
  exact hne i (ring_duplicate_freezes hop hp hA hcross i hi m).1

theorem small_ring_distinct_rows {n : Nat} (hn : n = 5 ∨ n = 7) :
    ∀ a b : Fin n, a ≠ b → SmallRingAdjacent n (a, 0) (b, 0) ∨
      (b.val + n - a.val) % n = (n - 1) / 2 ∨
      (a.val + n - b.val) % n = (n - 1) / 2 := by
  rcases hn with rfl | rfl <;> decide

theorem small_ring_rows_mod {n r : Nat} (hn : n = 5 ∨ n = 7)
    (a b : Fin n) (hr : (b.val + n - a.val) % n = r) :
    Int.ModEq (n : Int) (b : Int) ((a.val + r : Nat) : Int) := by
  have ha := a.isLt
  have hb := b.isLt
  change (b.val : Int) % n = ((a.val + r : Nat) : Int) % n
  rcases hn with rfl | rfl <;> omega

theorem higher_small_half_ring_ne {k m q : Nat} (hk : k = 6 ∨ k = 8)
    (hm : 0 < m) (hq : 2 ≤ q) {c : Nat → Fin (k - 1)}
    (hc : HigherProperOn k m q c (3 * higherPeriod k m)) (i : Int) :
    higherExpectedColor k m c (i + (k - 2 : Nat) * m) ≠ higherExpectedColor k m c i := by
  apply ring_gap_color_ne (higher_small_expected_two_options hk hm hq hc)
    (higher_small_color_changes_periodic hk hm hq hc) ?_ ?_
    (higherExpectedColor_ne_two_m (by omega) hm hq hc) i
  · rcases hk with rfl | rfl
    · exact ⟨2, by norm_num; ring⟩
    · exact ⟨3, by norm_num; ring⟩
  · intro x
    have heven : k % 2 ≠ 1 := by omega
    have hk6 : 6 ≤ k := by omega
    let d := (k - 4) * m + 2
    have hd : HigherDistance k m q d := by
      apply higher_first_band_distance hq
      · have hmul := Nat.mul_le_mul_right m (by omega : 2 ≤ k - 4)
        dsimp only [d]
        omega
      · simp only [higherFirstBandUpper, heven, if_false, d, le_refl]
    have hdpos : 0 < d := by dsimp only [d]; omega
    have hdle : d ≤ 2 * higherPeriod k m := by
      rcases hk with rfl | rfl <;> norm_num [higherPeriod, d] <;> omega
    have hne := (higherExpectedColor_int_distance (by omega : 5 ≤ k) hm hq hc hdpos hdle hd x).symm
    have he : x + (k - 2 : Nat) * m + 2 - 2 * m = x + d := by
      rcases hk with rfl | rfl <;> norm_num [d] <;> ring
    rwa [he]

theorem higher_small_ring_color_injective {k m q : Nat} (hk : k = 6 ∨ k = 8)
    (hm : 0 < m) (hq : 2 ≤ q) {c : Nat → Fin (k - 1)}
    (hc : HigherProperOn k m q c (3 * higherPeriod k m)) (i : Int) :
    Function.Injective (fun a : Fin (k - 1) => higherExpectedColor k m c (i + 2 * m * a.val)) := by
  have hn : k - 1 = 5 ∨ k - 1 = 7 := by omega
  have heven : k % 2 ≠ 1 := by omega
  have hhalf : ∀ a b : Fin (k - 1),
      (b.val + (k - 1) - a.val) % (k - 1) = ((k - 1) - 1) / 2 →
      higherExpectedColor k m c (i + 2 * m * b.val) ≠
        higherExpectedColor k m c (i + 2 * m * a.val) := by
    intro a b hr
    have hrow := small_ring_rows_mod hn a b hr
    have he := higherExpectedColor_ring_shift (m := m) heven c i 0 hrow
    simp only [Nat.cast_zero, add_zero] at he
    have hmul : 2 * (m : Int) * (((k - 1) - 1) / 2 : Nat) = (k - 2 : Nat) * m := by
      rcases hk with rfl | rfl <;> norm_num <;> ring
    rw [hmul] at he
    rw [he]
    exact higher_small_half_ring_ne hk hm hq hc (i + 2 * m * a.val)
  intro a b he
  by_contra hab
  rcases small_ring_distinct_rows hn a b hab with hd | hd | hd
  · have hne := small_ring_expected_adjacent hk hm hq hc i (a, 0) (b, 0) hd
    simp only [smallRingIndex, Fin.val_zero, Nat.cast_zero, add_zero] at hne
    exact hne he
  · exact hhalf a b hd he.symm
  · exact hhalf b a hd he

theorem higher_small_ring_color_surjective {k m q : Nat} (hk : k = 6 ∨ k = 8)
    (hm : 0 < m) (hq : 2 ≤ q) {c : Nat → Fin (k - 1)}
    (hc : HigherProperOn k m q c (3 * higherPeriod k m)) (i : Int) :
    Function.Surjective (fun a : Fin (k - 1) => higherExpectedColor k m c (i + 2 * m * a.val)) :=
  Finite.surjective_of_injective (higher_small_ring_color_injective hk hm hq hc i)

instance {α : Type*} [DecidableEq α] (f : Int → α) (i : Int) : Decidable (ColorChange f i) :=
  inferInstanceAs (Decidable (f i ≠ f (i - 2)))

def parityChangeCount {α : Type*} [DecidableEq α] (f : Int → α) (x : Int) : Nat → Nat
  | 0 => 0
  | s + 1 => parityChangeCount f x s + if ColorChange f (x + 2 * (s + 1 : Nat)) then 1 else 0

theorem parityChangeCount_step {α : Type*} [DecidableEq α] (f : Int → α) (x : Int) (s : Nat) :
    parityChangeCount f x s ≤ parityChangeCount f x (s + 1) ∧
      parityChangeCount f x (s + 1) ≤ parityChangeCount f x s + 1 := by
  simp only [parityChangeCount]
  split_ifs <;> omega

theorem parityChangeCount_mono {α : Type*} [DecidableEq α] (f : Int → α) (x : Int) :
    Monotone (parityChangeCount f x) :=
  monotone_nat_of_le_succ (fun s => (parityChangeCount_step f x s).1)

theorem parityChangeCount_hits {α : Type*} [DecidableEq α] (f : Int → α) (x : Int)
    (t a : Nat) (ha : a ≤ parityChangeCount f x t) :
    ∃ s : Nat, s ≤ t ∧ parityChangeCount f x s = a := by
  induction t with
  | zero =>
    refine ⟨0, by omega, ?_⟩
    simp only [parityChangeCount] at ha ⊢
    omega
  | succ t ih =>
    by_cases hle : a ≤ parityChangeCount f x t
    · obtain ⟨s, hs, he⟩ := ih hle
      exact ⟨s, by omega, he⟩
    · have hstep := (parityChangeCount_step f x t).2
      exact ⟨t + 1, by omega, by omega⟩

theorem parity_color_from_count {α : Type*} [DecidableEq α] {m : Nat} {f : Int → α}
    (hop : IntColorTwoOptions m f)
    (hp : Function.Periodic (ColorChange f) (2 * m : Int)) (x : Int) (s : Nat) :
    ∀ j : Int, f (x + 2 * s + 2 * m * j) =
      f (x + 2 * m * (j + parityChangeCount f x s)) := by
  induction s with
  | zero => intro j; simp only [parityChangeCount, Nat.cast_zero, mul_zero, add_zero]
  | succ s ih =>
    intro j
    let y : Int := x + 2 * (s + 1 : Nat)
    have hperiod : ColorChange f (y + 2 * m * j) = ColorChange f y :=
      periodic_color_change_multiple hp ⟨j, by ring⟩ y
    by_cases hchange : ColorChange f y
    · have hnow : ColorChange f (y + 2 * m * j) := by rw [hperiod]; exact hchange
      have he := (hop (y + 2 * m * j)).resolve_left hnow
      have harg : y + 2 * m * j + 2 * m - 2 = x + 2 * s + 2 * m * (j + 1) := by
        dsimp only [y]
        push_cast
        ring
      rw [harg, ih (j + 1)] at he
      change f (y + 2 * m * j) = _
      rw [he]
      simp only [parityChangeCount, show ColorChange f (x + 2 * (s + 1 : Nat)) from hchange, if_true]
      congr 1
      push_cast
      ring
    · have hnow : ¬ ColorChange f (y + 2 * m * j) := by rw [hperiod]; exact hchange
      have he : f (y + 2 * m * j) = f (y + 2 * m * j - 2) := not_not.mp hnow
      have harg : y + 2 * m * j - 2 = x + 2 * s + 2 * m * j := by
        dsimp only [y]
        push_cast
        ring
      rw [harg, ih j] at he
      change f (y + 2 * m * j) = _
      rw [he]
      simp only [parityChangeCount, show ¬ ColorChange f (x + 2 * (s + 1 : Nat)) from hchange,
        if_false, add_zero]

theorem int_periodic_mul_nat_mod {α : Type*} {p : Int} {n : Nat} {f : Int → α}
    (hp : Function.Periodic f (n * p)) (x : Int) (a : Nat) :
    f (x + p * a) = f (x + p * (a % n : Nat)) := by
  have h := hp.int_mul (a / n : Nat) (x + p * (a % n : Nat))
  simp only [Int.cast_id] at h
  have ha : (a % n : Nat) + (n : Int) * (a / n : Nat) = a := by
    exact_mod_cast Nat.mod_add_div a n
  have he : x + p * (a % n : Nat) + (a / n : Nat) * (n * p) = x + p * a := by
    rw [← ha]
    ring
  rwa [he] at h

theorem ring_color_equality_mod {n : Nat} {p : Int} {f : Int → Fin n}
    (hn : 0 < n) (hp : Function.Periodic f (n * p)) (x : Int)
    (hinj : Function.Injective (fun a : Fin n => f (x + p * a.val)))
    {a b : Nat} (he : f (x + p * a) = f (x + p * b)) : a % n = b % n := by
  rw [int_periodic_mul_nat_mod hp x a, int_periodic_mul_nat_mod hp x b] at he
  have h := hinj (a₁ := ⟨a % n, Nat.mod_lt _ hn⟩) (a₂ := ⟨b % n, Nat.mod_lt _ hn⟩) he
  exact congrArg Fin.val h

theorem parityChangeCount_eq_one {m n : Nat} (hn : 2 ≤ n) {f : Int → Fin n}
    (hop : IntColorTwoOptions m f)
    (hp : Function.Periodic (ColorChange f) (2 * m : Int))
    (hlong : Function.Periodic f (n * (2 * m : Int))) (x : Int)
    (hinj : Function.Injective (fun a : Fin n => f (x + 2 * m * a.val)))
    (havoid : ∀ s : Nat, s ≤ m → f (x + 2 * s) ≠ f (x + 1)) :
    parityChangeCount f x m = 1 := by
  obtain ⟨a, ha⟩ := Finite.surjective_of_injective hinj (f (x + 1))
  have hbound : parityChangeCount f x m < a.val := by
    by_contra hnot
    obtain ⟨s, hs, he⟩ := parityChangeCount_hits f x m a.val (by omega)
    have hcolor := parity_color_from_count hop hp x s 0
    simp only [mul_zero, add_zero, zero_add, he] at hcolor
    exact havoid s hs (hcolor.trans ha)
  have hcolor := parity_color_from_count hop hp x m 0
  simp only [mul_zero, add_zero, zero_add] at hcolor
  have he : f (x + 2 * m * (1 : Nat)) = f (x + 2 * m * parityChangeCount f x m) := by
    simpa only [Nat.cast_one, mul_one] using hcolor
  have hmod := ring_color_equality_mod (by omega : 0 < n) hlong x hinj he
  have halt := a.isLt
  rw [Nat.mod_eq_of_lt (by omega : 1 < n), Nat.mod_eq_of_lt (by omega)] at hmod
  omega

theorem evenRunProperty_of_unit_change_counts {α : Type*} [DecidableEq α] {m : Nat}
    {f : Int → α} (hop : IntColorTwoOptions m f)
    (hp : Function.Periodic (ColorChange f) (2 * m : Int))
    (hcount : ∀ x : Int, parityChangeCount f x m = 1) : EvenRunProperty m f := by
  intro i hi s hs
  let x : Int := i - 2
  have hfirstarg : x + 2 * (0 + 1 : Nat) = i := by dsimp only [x]; norm_num
  have hfirst : parityChangeCount f x 1 = 1 := by
    simp only [parityChangeCount, hfirstarg, hi, if_true, zero_add]
  have hle := parityChangeCount_mono f x (by omega : 1 ≤ s + 1)
  have hup := parityChangeCount_mono f x (by omega : s + 1 ≤ m)
  have htotal := hcount x
  have hcs : parityChangeCount f x (s + 1) = 1 := by omega
  have hcolor := parity_color_from_count hop hp x (s + 1) 0
  have hbase := parity_color_from_count hop hp x 1 0
  simp only [mul_zero, add_zero, zero_add, hcs, hfirst] at hcolor hbase
  have hsarg : x + 2 * (s + 1 : Nat) = i + 2 * s := by dsimp only [x]; push_cast; ring
  have hiarg : x + 2 * (1 : Nat) = i := by dsimp only [x]; norm_num
  rw [hsarg] at hcolor
  rw [hiarg] at hbase
  exact hcolor.trans hbase.symm

theorem higherExpectedColor_avoids_intermediate_parity {k m q : Nat} (hk : 5 ≤ k)
    (hm : 0 < m) (hq : 2 ≤ q) {c : Nat → Fin (k - 1)}
    (hc : HigherProperOn k m q c (3 * higherPeriod k m)) (x : Int) {s : Nat} (hs : s ≤ m) :
    higherExpectedColor k m c (x + 2 * s) ≠ higherExpectedColor k m c (x + 1) := by
  by_cases hs0 : s = 0
  · subst s
    simpa only [Nat.cast_zero, mul_zero, add_zero] using higherExpectedColor_ne_one hk hm hq hc x
  · have hd : HigherDistance k m q (2 * s - 1) := Or.inl ⟨by omega, by omega, by omega⟩
    have hL := higherPeriod_lower (m := m) hk
    have hne := (higherExpectedColor_int_distance hk hm hq hc (by omega) (by omega) hd (x + 1)).symm
    have he : x + 1 + ((2 * s - 1 : Nat) : Int) = x + 2 * s := by omega
    rwa [he] at hne

theorem higher_small_parityChangeCount_one {k m q : Nat} (hk : k = 6 ∨ k = 8)
    (hm : 0 < m) (hq : 2 ≤ q) {c : Nat → Fin (k - 1)}
    (hc : HigherProperOn k m q c (3 * higherPeriod k m)) (x : Int) :
    parityChangeCount (higherExpectedColor k m c) x m = 1 := by
  have heven : k % 2 ≠ 1 := by omega
  have hL : (higherPeriod k m : Int) = (k - 1 : Nat) * (2 * m : Int) := by
    simp only [higherPeriod, heven, if_false, Nat.cast_mul, Nat.cast_ofNat]
    ring
  have hlong : Function.Periodic (higherExpectedColor k m c)
      ((k - 1 : Nat) * (2 * m : Int)) := by
    rw [← hL]
    exact higherExpectedColor_periodic k m c
  apply parityChangeCount_eq_one (by omega : 2 ≤ k - 1)
    (higher_small_expected_two_options hk hm hq hc)
    (higher_small_color_changes_periodic hk hm hq hc) hlong x
    (higher_small_ring_color_injective hk hm hq hc x)
  intro s hs
  exact higherExpectedColor_avoids_intermediate_parity (by omega) hm hq hc x hs

theorem higher_small_expected_even_runs {k m q : Nat} (hk : k = 6 ∨ k = 8)
    (hm : 0 < m) (hq : 2 ≤ q) {c : Nat → Fin (k - 1)}
    (hc : HigherProperOn k m q c (3 * higherPeriod k m)) :
    EvenRunProperty m (higherExpectedColor k m c) := by
  exact evenRunProperty_of_unit_change_counts (higher_small_expected_two_options hk hm hq hc)
    (higher_small_color_changes_periodic hk hm hq hc) (higher_small_parityChangeCount_one hk hm hq hc)

theorem higher_expected_even_runs_all {k m q : Nat} (hk : 6 ≤ k) (hm : 0 < m)
    (hq : 2 ≤ q) {c : Nat → Fin (k - 1)}
    (hc : HigherProperOn k m q c (3 * higherPeriod k m)) :
    EvenRunProperty m (higherExpectedColor k m c) := by
  by_cases hsmall : k = 6 ∨ k = 8
  · exact higher_small_expected_even_runs hsmall hm hq hc
  · exact higher_expected_even_runs (by omega) (by omega) hm hq hc

theorem higher_expected_local_structure_all {k m q : Nat} (hk : 6 ≤ k) (hm : 0 < m)
    (hq : 2 ≤ q) {c : Nat → Fin (k - 1)}
    (hc : HigherProperOn k m q c (3 * higherPeriod k m)) : HigherExpectedLocalStructure k m c := by
  exact higher_expected_structure_of_even_runs (by omega) hm hq hc
    (higher_expected_even_runs_all hk hm hq hc)

/-
## Robust propagation and the complete target

The following lemmas finish propagation from an unaffected block. Two adjacent
rings establish the two available colors for every even k >= 6. The k = 5
case uses integer-valued color counts in overlapping intervals and chooses
m = 18*r + 20 to absorb boundary terms. These arguments complete the cited
higher-color construction and then combine it with the four-color theorem.
-/

def ShortColorParity {α : Type*} [DecidableEq α] (m r : Nat) (c : Nat → α) : Prop :=
  ∀ color : α,
    2 * r < (Finset.univ.filter (fun j : Fin (2 * m) => c j.val = color)).card →
    ∀ a b : Fin (2 * m), c a.val = color → c b.val = color → a.val % 2 = b.val % 2

theorem finite_window_color_card_le {α : Type*} [DecidableEq α]
    {start len span : Nat} (hfit : start + len ≤ span) (c : Nat → α) (color : α) :
    (Finset.univ.filter (fun j : Fin len => c (start + j.val) = color)).card ≤
      (Finset.univ.filter (fun j : Fin span => c j.val = color)).card := by
  let f : Fin len → Fin span := fun j => ⟨start + j.val, by have := j.isLt; omega⟩
  apply finite_fiber_card_le_of_injOn (fun j : Fin len => c (start + j.val))
    (fun j : Fin span => c j.val) color f _ (le_refl _)
  · intro j hj
    exact hj
  · intro a ha b hb he
    have hev : start + a.val = start + b.val := congrArg Fin.val he
    apply Fin.ext
    omega

theorem finite_window_color_card_le_half {α : Type*} [DecidableEq α]
    (c : Nat → α) (start len : Nat) (color : α)
    (hpar : ∀ a b : Fin len, c (start + a.val) = color → c (start + b.val) = color →
      (start + a.val) % 2 = (start + b.val) % 2) :
    (Finset.univ.filter (fun j : Fin len => c (start + j.val) = color)).card ≤ (len + 1) / 2 := by
  let f : Fin len → Fin ((len + 1) / 2) := fun j => ⟨j.val / 2, by have := j.isLt; omega⟩
  apply finite_fiber_card_le_of_injOn (fun j : Fin len => c (start + j.val))
    (fun _ : Fin ((len + 1) / 2) => color) color f ((len + 1) / 2)
  · simp
  · intro j hj
    rfl
  · intro a ha b hb he
    have hparity := hpar a b ha hb
    have hev : a.val / 2 = b.val / 2 := congrArg Fin.val he
    apply Fin.ext
    omega

theorem two_color_fibers_cover {α : Type*} [DecidableEq α] {n : Nat}
    (f : Fin n → α) (color other : α) (hcolors : ∀ j, f j = color ∨ f j = other) :
    n ≤ (Finset.univ.filter (fun j => f j = color)).card +
      (Finset.univ.filter (fun j => f j = other)).card := by
  let A := Finset.univ.filter (fun j => f j = color)
  let B := Finset.univ.filter (fun j => f j = other)
  have hcover : Finset.univ ⊆ A ∪ B := by
    intro j hj
    rcases hcolors j with h | h
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hj, h⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hj, h⟩))
  calc
    n = (Finset.univ : Finset (Fin n)).card := by simp
    _ ≤ (A ∪ B).card := Finset.card_le_card hcover
    _ ≤ A.card + B.card := Finset.card_union_le A B

theorem short_bicolor_obstruction {α : Type*} [DecidableEq α] {m r a start : Nat}
    (hm : 4 * r + 3 ≤ m) {c : Nat → α} (hpar : ShortColorParity m r c)
    (ha : a + 1 < 2 * m) (color other : α) (hca : c a = color) (hcb : c (a + 1) = color)
    (hfit : start + m ≤ 2 * m)
    (hcolors : ∀ j : Nat, j < m → c (start + j) = color ∨ c (start + j) = other) : False := by
  have hfull : (Finset.univ.filter (fun j : Fin (2 * m) => c j.val = color)).card ≤ 2 * r := by
    by_contra hnot
    have h := hpar color (by omega) ⟨a, by omega⟩ ⟨a + 1, ha⟩ hca hcb
    dsimp only at h
    omega
  have hfirst := (finite_window_color_card_le hfit c color).trans hfull
  have hsecond := finite_window_color_card_le hfit c other
  have hcover := two_color_fibers_cover (fun j : Fin m => c (start + j.val)) color other
    (fun j => hcolors j.val j.isLt)
  have hlarge : 2 * r < (Finset.univ.filter (fun j : Fin (2 * m) => c j.val = other)).card := by
    omega
  have hsmall := finite_window_color_card_le_half c start m other (by
    intro x y hx hy
    exact hpar other hlarge ⟨start + x.val, by have := x.isLt; omega⟩
      ⟨start + y.val, by have := y.isLt; omega⟩ hx hy)
  omega

theorem higher_shortColorParity {k m q p r : Nat}
    (hfit : 2 * m ≤ q * higherPeriod k m + 1)
    (c : ZMod (q * higherPeriod k m + 1) → Fin p)
    (hbad : (badEdges (higherGraph k m q) c).ncard ≤ r)
    (v : ZMod (q * higherPeriod k m + 1)) :
    ShortColorParity m r (fun j => c (v + (j : ZMod (q * higherPeriod k m + 1)))) := by
  intro color hcount a b ha hb
  exact higher_short_color_class_single_parity hfit c hbad v color hcount a b ha hb

theorem colorChange_shift {α : Type*} (f : Int → α) (t i : Int) :
    ColorChange (fun j => f (t + j)) i ↔ ColorChange f (t + i) := by
  unfold ColorChange
  dsimp only
  rw [show t + (i - 2) = t + i - 2 by ring]

theorem evenRunProperty_shift {α : Type*} {m : Nat} {f : Int → α}
    (hrun : EvenRunProperty m f) (t : Int) : EvenRunProperty m (fun i => f (t + i)) := by
  intro i hi s hs
  change f (t + (i + 2 * s)) = f (t + i)
  rw [show t + (i + 2 * s) = (t + i) + 2 * s by ring]
  exact hrun (t + i) ((colorChange_shift f t i).mp hi) s hs

theorem even_run_color_between {α : Type*} {m : Nat} {f : Int → α}
    (hrun : EvenRunProperty m f) {t i : Int} (ht : ColorChange f t)
    (hlo : t ≤ i) (hhi : i < t + 2 * m) (hpar : i % 2 = t % 2) : f i = f t := by
  have hp : (i - t) % 2 = 0 := by omega
  obtain ⟨s, hs, he⟩ : ∃ s : Nat, s < m ∧ t + 2 * s = i := by
    refine ⟨((i - t) / 2).toNat, ?_, ?_⟩ <;> omega
  rw [← he]
  exact hrun t ht s hs

theorem even_run_start_before {α : Type*} {m : Nat} {f : Int → α}
    (hrun : EvenRunProperty m f) (hne : ∀ i : Int, f (i + 2 * m) ≠ f i) (i : Int) :
    ∃ t : Int, t ≤ i ∧ i < t + 2 * m ∧ i % 2 = t % 2 ∧ ColorChange f t ∧ f i = f t := by
  obtain ⟨s, hs, ht⟩ := color_change_exists f m (i - 2 * m) (hne _)
  let t : Int := i - 2 * m + 2 * (s + 1 : Nat)
  have hlo : t ≤ i := by dsimp only [t]; omega
  have hhi : i < t + 2 * m := by dsimp only [t]; omega
  have hpar : i % 2 = t % 2 := by dsimp only [t]; omega
  exact ⟨t, hlo, hhi, hpar, ht, even_run_color_between hrun ht hlo hhi hpar⟩

theorem even_run_two_color_interval {α : Type*} {m : Nat} {f : Int → α} (hm : 0 < m)
    (hrun : EvenRunProperty m f) (hne : ∀ i : Int, f (i + 2 * m) ≠ f i)
    (hzero : ColorChange f 0) :
    ∃ start : Nat, 0 < start ∧ start + m ≤ 2 * m ∧ ∃ other : α,
      ∀ i : Int, (start : Int) - 1 ≤ i → i < start + m → f i = f 0 ∨ f i = other := by
  obtain ⟨t, ht, htpar, hchange⟩ := even_run_change_exists_parity hne (by omega : 1 < 2)
  have htp : (t : Int) % 2 = 1 := by exact_mod_cast htpar
  have htpos : 0 < t := by omega
  have hback := even_run_change_backward hrun hne hchange
  have heven : ∀ i : Int, 0 ≤ i → i < 2 * m → i % 2 = 0 → f i = f 0 := by
    intro i hi hbound hpar
    exact even_run_color_between hrun hzero hi (by omega) (by omega)
  by_cases hleft : m < t
  · refine ⟨1, by omega, by omega, f ((t : Int) - 2 * m), ?_⟩
    intro i hi hbound
    by_cases hpar : i % 2 = 0
    · exact Or.inl (heven i (by omega) (by omega) hpar)
    · apply Or.inr
      exact even_run_color_between hrun hback (by omega) (by omega) (by omega)
  · refine ⟨t, htpos, by omega, f t, ?_⟩
    intro i hi hbound
    by_cases hpar : i % 2 = 0
    · exact Or.inl (heven i (by omega) (by omega) hpar)
    · apply Or.inr
      exact even_run_color_between hrun hchange (by omega) (by omega) (by omega)

theorem two_options_on_even_run {α : Type*} {m : Nat} {f : Int → α} {c : Nat → α}
    (hm : 0 < m) (hrun : EvenRunProperty m f) (hne : ∀ i : Int, f (i + 2 * m) ≠ f i)
    (hzero : ColorChange f 0)
    (hop : ∀ j : Nat, j < 2 * m → c j = f j ∨ c j = f ((j : Int) - 1)) :
    ∃ start : Nat, start + m ≤ 2 * m ∧ ∃ other : α,
      ∀ j : Nat, j < m → c (start + j) = f 0 ∨ c (start + j) = other := by
  obtain ⟨start, hstart, hfit, other, hcolors⟩ := even_run_two_color_interval hm hrun hne hzero
  refine ⟨start, hfit, other, ?_⟩
  intro j hj
  rcases hop (start + j) (by omega) with h | h
  · exact (hcolors (start + j : Nat) (by omega) (by omega)).imp
      (fun he => h.trans he) (fun he => h.trans he)
  · exact (hcolors ((start + j : Nat) - 1 : Int) (by omega) (by omega)).imp
      (fun he => h.trans he) (fun he => h.trans he)

theorem even_run_bad_pair_impossible {α : Type*} [DecidableEq α] {m r a : Nat}
    {f : Int → α} {c : Nat → α} (hm : 4 * r + 3 ≤ m)
    (hrun : EvenRunProperty m f) (hne : ∀ i : Int, f (i + 2 * m) ≠ f i)
    (hzero : ColorChange f 0) (hpar : ShortColorParity m r c)
    (hop : ∀ j : Nat, j < 2 * m → c j = f j ∨ c j = f ((j : Int) - 1))
    (ha : a + 1 < 2 * m) (hca : c a = f 0) (hcb : c (a + 1) = f 0) : False := by
  obtain ⟨start, hfit, other, hcolors⟩ := two_options_on_even_run (by omega) hrun hne hzero hop
  exact short_bicolor_obstruction hm hpar ha (f 0) other hca hcb hfit hcolors

theorem expected_agreement_of_two_options {α : Type*} [DecidableEq α]
    {m r initial len span : Nat} {f : Int → α} {c : Nat → α}
    (hm : 4 * r + 3 ≤ m) (hinitial : 2 * m ≤ initial) (hmargin : len + 2 * m ≤ span)
    (hrun : EvenRunProperty m f) (hne : ∀ i : Int, f (i + 2 * m) ≠ f i)
    (hclean : ∀ i : Nat, i < initial → c i = f i)
    (hop : ∀ i : Nat, i < span → c i = f i ∨ c i = f ((i : Int) - 1))
    (hpar : ∀ start : Nat, start + 2 * m ≤ span →
      ShortColorParity m r (fun j => c (start + j))) :
    ∀ i : Nat, i < len → c i = f i := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro hi
    by_cases hic : i < initial
    · exact hclean i hic
    by_contra hwrong
    have hi0 : 0 < i := by omega
    have hother : c i = f ((i : Int) - 1) := (hop i (by omega)).resolve_left hwrong
    have hpredcast : ((i - 1 : Nat) : Int) = (i : Int) - 1 := by omega
    have hprev : c (i - 1) = f ((i : Int) - 1) := by
      simpa only [hpredcast] using ih (i - 1) (by omega) (by omega)
    obtain ⟨t, htlo, hthi, htpar, htchange, htcolor⟩ := even_run_start_before hrun hne ((i : Int) - 1)
    have ht0 : 0 ≤ t := by omega
    let start := t.toNat
    have hstart : (start : Int) = t := Int.toNat_of_nonneg ht0
    have hstartle : start ≤ i - 1 := by omega
    have hfit : start + 2 * m ≤ span := by omega
    let a := i - 1 - start
    have hapos : start + a = i - 1 := by dsimp only [a]; omega
    have haplus : start + (a + 1) = i := by omega
    have hbound : a + 1 < 2 * m := by omega
    have hzero : ColorChange (fun j => f (t + j)) 0 := by
      apply (colorChange_shift f t 0).mpr
      simpa only [add_zero] using htchange
    have hshiftne : ∀ j : Int, f (t + (j + 2 * m)) ≠ f (t + j) := by
      intro j
      simpa only [add_assoc] using hne (t + j)
    have hoptions : ∀ j : Nat, j < 2 * m →
        c (start + j) = f (t + j) ∨ c (start + j) = f (t + ((j : Int) - 1)) := by
      intro j hj
      have h := hop (start + j) (by omega)
      simpa only [Nat.cast_add, hstart, add_sub_assoc] using h
    have hca : c (start + a) = f (t + 0) := by
      rw [hapos, add_zero]
      exact hprev.trans htcolor
    have hcb : c (start + (a + 1)) = f (t + 0) := by
      rw [haplus, add_zero]
      exact hother.trans htcolor
    exact even_run_bad_pair_impossible (a := a) (f := fun j => f (t + j))
      (c := fun j => c (start + j)) hm (evenRunProperty_shift hrun t) hshiftne hzero
      (hpar start hfit) hoptions hbound hca hcb

def HigherPrefixAgreement (k m r : Nat) : Prop :=
  ∀ c : ZMod ((24 * r + 12) * higherPeriod k m + 1) → Fin (k - 1),
    (badEdges (higherGraph k m (24 * r + 12)) c).ncard ≤ r →
    ∀ v : ZMod ((24 * r + 12) * higherPeriod k m + 1),
      (∀ j : Nat, j < 3 * higherPeriod k m →
        v + (j : ZMod ((24 * r + 12) * higherPeriod k m + 1)) ∉
          badVertices (higherGraph k m (24 * r + 12)) c) →
      ∀ i : Nat, i < (6 * r + 3) * higherPeriod k m →
        c (v + (i : ZMod ((24 * r + 12) * higherPeriod k m + 1))) =
          higherExpectedColor k m
            (fun j => c (v + (j : ZMod ((24 * r + 12) * higherPeriod k m + 1)))) i

theorem higher_clean_prefix_agreement_of_two_options {k m r : Nat}
    (hk : 6 ≤ k) (hm : 4 * r + 3 ≤ m)
    (c : ZMod ((24 * r + 12) * higherPeriod k m + 1) → Fin (k - 1))
    (hbad : (badEdges (higherGraph k m (24 * r + 12)) c).ncard ≤ r)
    (v : ZMod ((24 * r + 12) * higherPeriod k m + 1))
    (hclean : ∀ j : Nat, j < 3 * higherPeriod k m →
      v + (j : ZMod ((24 * r + 12) * higherPeriod k m + 1)) ∉
        badVertices (higherGraph k m (24 * r + 12)) c)
    (hop : ∀ i : Nat, i < ((24 * r + 12) / 2) * higherPeriod k m →
      c (v + (i : ZMod ((24 * r + 12) * higherPeriod k m + 1))) =
        higherExpectedColor k m
          (fun j => c (v + (j : ZMod ((24 * r + 12) * higherPeriod k m + 1)))) i ∨
      c (v + (i : ZMod ((24 * r + 12) * higherPeriod k m + 1))) =
        higherExpectedColor k m
          (fun j => c (v + (j : ZMod ((24 * r + 12) * higherPeriod k m + 1)))) (i - 1 : Nat)) :
    ∀ i : Nat, i < (6 * r + 3) * higherPeriod k m →
      c (v + (i : ZMod ((24 * r + 12) * higherPeriod k m + 1))) =
        higherExpectedColor k m
          (fun j => c (v + (j : ZMod ((24 * r + 12) * higherPeriod k m + 1)))) i := by
  let L := higherPeriod k m
  let q := 24 * r + 12
  let B := (6 * r + 3) * L
  let d : Nat → Fin (k - 1) := fun j => c (v + (j : ZMod (q * L + 1)))
  have hmpos : 0 < m := by omega
  have hq : 3 ≤ q := by dsimp only [q]; omega
  have hLpos : 0 < L := higherPeriod_pos (by omega) hmpos
  have hLlower : 4 * m ≤ L := higherPeriod_lower (by omega)
  have hQL : 3 * L ≤ q * L := Nat.mul_le_mul_right L hq
  have hlen : 3 * L ≤ q * L + 1 := by omega
  have hproper : HigherProperOn k m q d (3 * L) := higherProperOn_of_clean c v hlen hclean
  have hLB : L ≤ B := by
    have h := Nat.mul_le_mul_right L (by omega : 1 ≤ 6 * r + 3)
    simpa only [one_mul] using h
  have hhalf : (q / 2) * L = 2 * B := by
    have hdiv : q / 2 = 12 * r + 6 := by dsimp only [q]; omega
    rw [hdiv]
    dsimp only [B]
    ring
  change ∀ i : Nat, i < B → d i = higherExpectedColor k m d i
  apply expected_agreement_of_two_options (initial := 3 * L) (len := B) (span := 2 * B) hm
    (by omega) (by omega) (higher_expected_even_runs_all hk hmpos (by omega) hproper)
    (higherExpectedColor_ne_two_m (by omega) hmpos (by omega) hproper)
  · intro i hi
    exact (higherExpectedColor_agrees (by omega) hmpos (by omega) hproper hi).symm
  · intro i hi
    by_cases hi0 : i = 0
    · subst i
      left
      exact (higherExpectedColor_agrees (by omega) hmpos (by omega) hproper (by omega)).symm
    · have hi' : i < (q / 2) * L := by rw [hhalf]; exact hi
      have hpred : ((i - 1 : Nat) : Int) = (i : Int) - 1 := by omega
      simpa only [hpred] using hop i hi'
  · intro start _hfit
    have h := higher_shortColorParity (by omega : 2 * m ≤ q * L + 1) c hbad
      (v + (start : ZMod (q * L + 1)))
    simpa only [ShortColorParity, d, Nat.cast_add, add_assoc] using h

theorem higher_odd_prefix_agreement {k m r : Nat} (hk : 7 ≤ k) (hodd : k % 2 = 1)
    (hm : 4 * r + 3 ≤ m) : HigherPrefixAgreement k m r := by
  intro c hbad v hclean
  apply higher_clean_prefix_agreement_of_two_options (by omega) hm c hbad v hclean
  intro i hi
  exact higher_odd_clean_prefix_two_options (by omega) (by omega) (by omega) hodd c v hclean hi

theorem higherGraph_neg (k m q : Nat) (u v : ZMod (q * higherPeriod k m + 1)) :
    (higherGraph k m q).Adj (-u) (-v) ↔ (higherGraph k m q).Adj u v := by
  change ((-u ≠ -v) ∧ _) ↔ ((u ≠ v) ∧ _)
  have h₁ : -v - -u = u - v := by abel
  have h₂ : -u - -v = v - u := by abel
  simp only [h₁, h₂, ne_eq, neg_inj, or_comm]

theorem not_badVertices_of_map {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W)
    (f : V → W) (hadj : ∀ v w, G.Adj v w → H.Adj (f v) (f w)) {p : Nat}
    (c : W → Fin p) {v : V} (hv : f v ∉ badVertices H c) :
    v ∉ badVertices G (fun x => c (f x)) := by
  rintro ⟨w, hw, he⟩
  exact hv ⟨f w, hadj v w hw, he⟩

theorem higher_badEdges_neg_le {k m q p : Nat}
    (c : ZMod (q * higherPeriod k m + 1) → Fin p) :
    (badEdges (higherGraph k m q) (fun x => c (-x))).ncard ≤
      (badEdges (higherGraph k m q) c).ncard := by
  apply badEdges_le_of_injective_map (higherGraph k m q) (higherGraph k m q)
    (fun x => -x) neg_injective
  intro v w h
  exact (higherGraph_neg k m q v w).mpr h

theorem higher_local_propagation_of_prefix {k m r : Nat} (hk : 5 ≤ k) (hm : 0 < m)
    (hprefix : HigherPrefixAgreement k m r) : HigherLocalPropagation k m r := by
  intro c hbad v a hafit hclean
  let L := higherPeriod k m
  let q := 24 * r + 12
  let N := q * L + 1
  let B := (6 * r + 3) * L
  let b := a + 3 * L - 1
  let z : ZMod N := v + (b : ZMod N)
  let d : ZMod N → Fin (k - 1) := fun x => c (-x)
  have hL : 0 < L := higherPeriod_pos hk hm
  have hb : b < B := by dsimp only [b, B, L]; omega
  have hbL : L ≤ b := by dsimp only [b]; omega
  have hdbad : (badEdges (higherGraph k m q) d).ncard ≤ r :=
    (higher_badEdges_neg_le c).trans hbad
  have hdclean : ∀ j : Nat, j < 3 * L →
      -z + (j : ZMod N) ∉ badVertices (higherGraph k m q) d := by
    intro j hj
    apply not_badVertices_of_map (higherGraph k m q) (higherGraph k m q) (fun x => -x)
      (fun x y h => (higherGraph_neg k m q x y).mpr h) c
    have hbj : b = j + (a + (3 * L - 1 - j)) := by dsimp only [b]; omega
    have he : -(-z + (j : ZMod N)) = v + ((a + (3 * L - 1 - j) : Nat) : ZMod N) := by
      dsimp only [z]
      rw [hbj, Nat.cast_add]
      ring
    rw [he]
    exact hclean (3 * L - 1 - j) (by omega)
  have hagree := hprefix d hdbad (-z) hdclean
  have hright := hagree b hb
  have hleft := hagree (b - L) (by omega)
  have heright : d (-z + (b : ZMod N)) = c v := by
    dsimp only [d, z]
    congr 1
    ring
  have heleft : d (-z + ((b - L : Nat) : ZMod N)) = c (v + (L : ZMod N)) := by
    dsimp only [d, z]
    rw [Nat.cast_sub hbL]
    congr 1
    ring
  rw [heright] at hright
  rw [heleft] at hleft
  have hperiod : higherExpectedColor k m (fun j => d (-z + (j : ZMod N))) (b - L : Nat) =
      higherExpectedColor k m (fun j => d (-z + (j : ZMod N))) b := by
    simp only [higherExpectedColor_of_nat]
    exact congrArg (fun j : Nat => d (-z + (j : ZMod N))) (Nat.mod_eq_sub_mod hbL).symm
  exact hleft.trans (hperiod.trans hright.symm)

theorem higher_odd_local_propagation {k m r : Nat} (hk : 7 ≤ k) (hodd : k % 2 = 1)
    (hm : 4 * r + 3 ≤ m) : HigherLocalPropagation k m r := by
  exact higher_local_propagation_of_prefix (by omega) (by omega) (higher_odd_prefix_agreement hk hodd hm)

theorem higher_odd_erdos944 {k r : Nat} (hk : 7 ≤ k) (hodd : k % 2 = 1) :
    Erdos944.SimpleGraph.IsErdos944 (higherGraph k (18 * r + 3) (24 * r + 12)) k r := by
  exact higher_erdos944_of_local_propagation (by omega) (by omega)
    (higher_odd_local_propagation hk hodd (by omega))

universe uOdd

theorem erdos944_odd {k : Nat} (hk : 7 ≤ k) (hodd : k % 2 = 1) (r : Nat) :
    ∃ (V : Type uOdd) (G : SimpleGraph V), Erdos944.SimpleGraph.IsErdos944 G k r := by
  have hsucc : k - 1 + 1 = k := by omega
  have hG := higher_odd_erdos944 (r := r) hk hodd
  have h := erdos944_universe_lift (k := k - 1) (higherGraph k (18 * r + 3) (24 * r + 12))
    (by omega) (by simpa only [hsucc] using hG)
  simpa only [hsucc] using h

def PairedRingAdjacent (n : Nat) (a b : Fin n × Fin 2) : Prop :=
  a ≠ b ∧ Nat.dist a.1.val b.1.val ≠ n / 2 ∧ Nat.dist a.1.val b.1.val ≠ n / 2 + 1

theorem paired_ring_three_have_edge {n : Nat} (hn : 5 ≤ n) (a b c : Fin n × Fin 2)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    PairedRingAdjacent n a b ∨ PairedRingAdjacent n a c ∨ PairedRingAdjacent n b c := by
  by_contra hnot
  have h₁ : Nat.dist a.1.val b.1.val = n / 2 ∨ Nat.dist a.1.val b.1.val = n / 2 + 1 := by
    by_contra h
    push Not at h
    exact hnot (Or.inl ⟨hab, h.1, h.2⟩)
  have h₂ : Nat.dist a.1.val c.1.val = n / 2 ∨ Nat.dist a.1.val c.1.val = n / 2 + 1 := by
    by_contra h
    push Not at h
    exact hnot (Or.inr (Or.inl ⟨hac, h.1, h.2⟩))
  have h₃ : Nat.dist b.1.val c.1.val = n / 2 ∨ Nat.dist b.1.val c.1.val = n / 2 + 1 := by
    by_contra h
    push Not at h
    exact hnot (Or.inr (Or.inr ⟨hbc, h.1, h.2⟩))
  simp only [Nat.dist] at h₁ h₂ h₃
  omega

theorem paired_ring_color_class_card_le_two {n : Nat} (hn : 5 ≤ n)
    {α : Type*} [DecidableEq α] (f : Fin n × Fin 2 → α)
    (hf : ∀ a b, PairedRingAdjacent n a b → f a ≠ f b) (color : α) :
    (Finset.univ.filter (fun a => f a = color)).card ≤ 2 := by
  by_contra hnot
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := Finset.two_lt_card_iff.mp
    (show 2 < (Finset.univ.filter (fun a => f a = color)).card by omega)
  have ha' := (Finset.mem_filter.mp ha).2
  have hb' := (Finset.mem_filter.mp hb).2
  have hc' := (Finset.mem_filter.mp hc).2
  rcases paired_ring_three_have_edge hn a b c hab hac hbc with h | h | h
  · exact hf a b h (ha'.trans hb'.symm)
  · exact hf a c h (ha'.trans hc'.symm)
  · exact hf b c h (hb'.trans hc'.symm)

theorem paired_ring_color_class_card {n : Nat} (hn : 5 ≤ n)
    (f : Fin n × Fin 2 → Fin n)
    (hf : ∀ a b, PairedRingAdjacent n a b → f a ≠ f b) (color : Fin n) :
    (Finset.univ.filter (fun a => f a = color)).card = 2 := by
  apply finite_fibers_eq_of_le f 2 (by simp)
  exact paired_ring_color_class_card_le_two hn f hf

theorem paired_ring_middle_adjacent {n : Nat} (hn : 5 ≤ n) {a b : Fin n × Fin 2}
    (hab : a ≠ b) (ha : a.1.val = n / 2 ∨ a.1.val = n / 2 + 1)
    (hb : b.1.val = n / 2 ∨ b.1.val = n / 2 + 1) : PairedRingAdjacent n a b := by
  refine ⟨hab, ?_, ?_⟩ <;> simp only [Nat.dist] <;> omega

theorem paired_ring_color_at_base {n : Nat} (hn : 5 ≤ n)
    (f : Fin n × Fin 2 → Fin n)
    (hf : ∀ a b, PairedRingAdjacent n a b → f a ≠ f b) (color : Fin n)
    (hexcluded : ∀ a : Fin n × Fin 2, a.1.val ≠ 0 → a.1.val ≠ n / 2 →
      a.1.val ≠ n / 2 + 1 → f a ≠ color) :
    ∃ a : Fin n × Fin 2, a.1.val = 0 ∧ f a = color := by
  have hcard := paired_ring_color_class_card hn f hf color
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp
    (show 1 < (Finset.univ.filter (fun a => f a = color)).card by omega)
  have ha' := (Finset.mem_filter.mp ha).2
  have hb' := (Finset.mem_filter.mp hb).2
  by_cases ha0 : a.1.val = 0
  · exact ⟨a, ha0, ha'⟩
  by_cases hb0 : b.1.val = 0
  · exact ⟨b, hb0, hb'⟩
  have hamid : a.1.val = n / 2 ∨ a.1.val = n / 2 + 1 := by
    by_contra h
    push Not at h
    exact hexcluded a ha0 h.1 h.2 ha'
  have hbmid : b.1.val = n / 2 ∨ b.1.val = n / 2 + 1 := by
    by_contra h
    push Not at h
    exact hexcluded b hb0 h.1 h.2 hb'
  exact False.elim (hf a b (paired_ring_middle_adjacent hn hab hamid hbmid) (ha'.trans hb'.symm))

def higherRingIndex {n : Nat} (m : Nat) (a : Fin n × Fin 2) : Nat := 2 * m * a.1.val + a.2.val

theorem higherRingIndex_row_mono {n m : Nat} (hm : 0 < m) {a b : Fin n × Fin 2}
    (hab : a.1.val < b.1.val) : higherRingIndex m a < higherRingIndex m b := by
  have hmul := Nat.mul_le_mul_left (2 * m) (by omega : a.1.val + 1 ≤ b.1.val)
  have ha := a.2.isLt
  have hb := b.2.isLt
  dsimp only [higherRingIndex]
  nlinarith

theorem higherRingIndex_injective {n m : Nat} (hm : 0 < m) :
    Function.Injective (higherRingIndex (n := n) m) := by
  intro a b he
  have hr : a.1.val = b.1.val := by
    rcases lt_trichotomy a.1.val b.1.val with h | h | h
    · have := higherRingIndex_row_mono hm h
      omega
    · exact h
    · have := higherRingIndex_row_mono hm h
      omega
  apply Prod.ext (Fin.ext hr)
  apply Fin.ext
  dsimp only [higherRingIndex] at he
  rw [hr] at he
  omega

theorem higherRingIndex_lt_period {k m : Nat} (hk : 6 ≤ k) (hm : 0 < m)
    (heven : k % 2 ≠ 1) (a : Fin (k - 1) × Fin 2) : higherRingIndex m a < higherPeriod k m := by
  have ha := a.1.isLt
  have hb := a.2.isLt
  have hmul := Nat.mul_le_mul_left (2 * m) (by omega : a.1.val ≤ k - 2)
  have hperiod : higherPeriod k m = 2 * m * (k - 2) + 2 * m := by
    simp only [higherPeriod, heven, if_false]
    have hpred : k - 1 = (k - 2) + 1 := by omega
    rw [hpred]
    ring
  rw [hperiod]
  dsimp only [higherRingIndex]
  nlinarith

theorem higher_even_row_gap_distance {k m q a d : Nat} (hk : 6 ≤ k) (_hm : 0 < m)
    (hq : 2 ≤ q) (heven : k % 2 ≠ 1) (ha : 1 ≤ a) (hak : a < k - 1)
    (ha₀ : a ≠ (k - 1) / 2) (ha₁ : a ≠ (k - 1) / 2 + 1)
    (hdlo : 2 * m * a ≤ d + 1) (hdhi : d ≤ 2 * m * a + 1) : HigherDistance k m q d := by
  by_cases hlow : a < (k - 1) / 2
  · have hmullo := Nat.mul_le_mul_left (2 * m) ha
    have hlo : 2 * m ≤ d + 1 := by nlinarith
    have hmulhi := Nat.mul_le_mul_right m (by omega : 2 * a ≤ k - 4)
    have hhi : d ≤ (k - 4) * m + 2 := by nlinarith
    by_cases hs : d < 2 * m
    · exact Or.inl ⟨by omega, hs, by omega⟩
    · apply higher_first_band_distance hq (by omega)
      simpa only [higherFirstBandUpper, heven, if_false] using hhi
  · have hmullo := Nat.mul_le_mul_right m (by omega : k + 2 ≤ 2 * a)
    have hlo' : (k + 2) * m ≤ d + 1 := by nlinarith
    have hlo : (k + 2) * m - 1 ≤ d := by omega
    have hmulhi := Nat.mul_le_mul_right m (by omega : 2 * a ≤ 2 * k - 4)
    have hhi : d ≤ (2 * k - 4) * m + 1 := by nlinarith
    refine Or.inr (Or.inr ⟨heven, 0, by omega, ?_, ?_⟩)
    · simpa only [zero_mul, zero_add] using hlo
    · simpa only [zero_mul, zero_add] using hhi

theorem higher_ring_pair_distance {k m q : Nat} (hk : 6 ≤ k) (hm : 0 < m)
    (hq : 2 ≤ q) (heven : k % 2 ≠ 1) {a b : Fin (k - 1) × Fin 2}
    (hab : PairedRingAdjacent (k - 1) a b) (hlt : higherRingIndex m a < higherRingIndex m b) :
    HigherDistance k m q (higherRingIndex m b - higherRingIndex m a) := by
  have hrow : a.1.val ≤ b.1.val := by
    by_contra h
    have hrev := higherRingIndex_row_mono hm (show b.1.val < a.1.val by omega)
    omega
  have ha := a.2.isLt
  have hb := b.2.isLt
  by_cases hr : a.1.val = b.1.val
  · have hd : higherRingIndex m b - higherRingIndex m a = 1 := by
      dsimp only [higherRingIndex] at hlt ⊢
      rw [hr] at hlt ⊢
      omega
    rw [hd]
    exact Or.inl ⟨by omega, by omega, by omega⟩
  · let d := higherRingIndex m b - higherRingIndex m a
    let t := b.1.val - a.1.val
    have hrows : a.1.val + t = b.1.val := by dsimp only [t]; omega
    have hrowmul := congrArg (fun x : Nat => 2 * m * x) hrows
    have hdiff : d + higherRingIndex m a = higherRingIndex m b := Nat.sub_add_cancel (Nat.le_of_lt hlt)
    have hd : d + a.2.val = 2 * m * t + b.2.val := by
      dsimp only [higherRingIndex] at hdiff
      nlinarith only [hdiff, hrowmul]
    have hdist : Nat.dist a.1.val b.1.val = t := by simp only [Nat.dist]; dsimp only [t]; omega
    apply higher_even_row_gap_distance (a := t) (d := d) hk hm hq heven (by omega)
      (by have := b.1.isLt; omega)
      (by simpa only [hdist] using hab.2.1) (by simpa only [hdist] using hab.2.2)
    · nlinarith
    · nlinarith

theorem higher_ring_pair_proper {k m q : Nat} (hk : 6 ≤ k) (hm : 0 < m)
    (hq : 2 ≤ q) (heven : k % 2 ≠ 1) {c : Nat → Fin (k - 1)}
    (hc : HigherProperOn k m q c (higherPeriod k m)) (a b : Fin (k - 1) × Fin 2)
    (hab : PairedRingAdjacent (k - 1) a b) : c (higherRingIndex m a) ≠ c (higherRingIndex m b) := by
  rcases lt_trichotomy (higherRingIndex m a) (higherRingIndex m b) with h | h | h
  · exact hc _ _ h (higherRingIndex_lt_period hk hm heven b)
      (higher_ring_pair_distance hk hm hq heven hab h)
  · exact False.elim (hab.1 (higherRingIndex_injective hm h))
  · have hba : PairedRingAdjacent (k - 1) b a := by
      exact ⟨hab.1.symm, by simpa only [Nat.dist_comm] using hab.2.1,
        by simpa only [Nat.dist_comm] using hab.2.2⟩
    exact (hc _ _ h (higherRingIndex_lt_period hk hm heven a)
      (higher_ring_pair_distance hk hm hq heven hba h)).symm

theorem higherDistance_add_period_of_lt {k m q d b : Nat} (_hk : 5 ≤ k) (hm : 0 < m)
    (hd : HigherDistance k m q d) (hbig : 2 * m ≤ d) (hsmall : d < higherPeriod k m)
    (hb : b < q / 2) : HigherDistance k m q (b * higherPeriod k m + d) := by
  rcases hd with hd | ⟨a, ha, hlo, hhi⟩ | ⟨heven, a, ha, hlo, hhi⟩
  · omega
  · have ha0 : a = 0 := by
      by_contra h
      have hmul := Nat.mul_le_mul_right (higherPeriod k m) (by omega : 1 ≤ a)
      omega
    subst a
    simp only [zero_mul, zero_add] at hlo hhi
    exact Or.inr (Or.inl ⟨b, hb, by omega, by omega⟩)
  · have hpos : 1 ≤ (k + 2) * m := by nlinarith
    have ha0 : a = 0 := by
      by_contra h
      have hmul := Nat.mul_le_mul_right (higherPeriod k m) (by omega : 1 ≤ a)
      omega
    subst a
    simp only [zero_mul, zero_add] at hlo hhi
    exact Or.inr (Or.inr ⟨heven, b, hb, by omega, by omega⟩)

theorem higher_even_two_options_sequence {k m q : Nat} (hk : 6 ≤ k) (hm : 0 < m)
    (hq : 2 ≤ q) (heven : k % 2 ≠ 1) {c : Nat → Fin (k - 1)}
    (hc : HigherProperOn k m q c (3 * higherPeriod k m))
    (hcross : ∀ j i : Nat, j < 3 * higherPeriod k m → i < (q / 2) * higherPeriod k m →
      j < i → HigherDistance k m q (i - j) → c j ≠ c i)
    {i : Nat} (hi : i < (q / 2) * higherPeriod k m) :
    c i = higherExpectedColor k m c i ∨ c i = higherExpectedColor k m c (i - 1 : Nat) := by
  let L := higherPeriod k m
  have hL : 0 < L := higherPeriod_pos (by omega) hm
  by_cases hclean : i < 3 * L
  · exact Or.inl (higherExpectedColor_agrees (by omega) hm hq hc hclean).symm
  let i₀ := L + i % L
  let b := i / L - 1
  have hmod : i % L < L := Nat.mod_lt _ hL
  have hi₀lo : L ≤ i₀ := by omega
  have hi₀hi : i₀ < 2 * L := by omega
  have hdiv : 1 ≤ i / L := (Nat.le_div_iff_mul_le hL).mpr (by omega)
  have hsum : b * L + i₀ = i := by
    have hd := Nat.mod_add_div i L
    have hb : b + 1 = i / L := by omega
    dsimp only [i₀]
    nlinarith only [hd, hb]
  have hbq : b < q / 2 := by
    have hd : i / L < q / 2 := (Nat.div_lt_iff_lt_mul hL).mpr hi
    omega
  have hr : HigherProperOn k m q (fun j => c (i₀ - j)) L :=
    higherProperOn_reverse hc (by omega) (by omega)
  let φ : Fin (k - 1) × Fin 2 → Fin (k - 1) := fun a => c (i₀ - higherRingIndex m a)
  have hφ : ∀ a b, PairedRingAdjacent (k - 1) a b → φ a ≠ φ b :=
    higher_ring_pair_proper hk hm hq heven hr
  have hexcluded : ∀ a : Fin (k - 1) × Fin 2, a.1.val ≠ 0 → a.1.val ≠ (k - 1) / 2 →
      a.1.val ≠ (k - 1) / 2 + 1 → φ a ≠ c i := by
    intro a ha0 ha₀ ha₁
    have ha := a.2.isLt
    have hindex : 2 * m ≤ higherRingIndex m a := by
      have hmul := Nat.mul_le_mul_left (2 * m) (by omega : 1 ≤ a.1.val)
      dsimp only [higherRingIndex]
      nlinarith
    have hindexlt : higherRingIndex m a < L := higherRingIndex_lt_period hk hm heven a
    have hd : HigherDistance k m q (higherRingIndex m a) :=
      higher_even_row_gap_distance (a := a.1.val) hk hm hq heven (by omega) a.1.isLt ha₀ ha₁
        (by dsimp only [higherRingIndex]; omega) (by dsimp only [higherRingIndex]; omega)
    have hshift := higherDistance_add_period_of_lt (by omega) hm hd hindex hindexlt hbq
    have hdiff : i - (i₀ - higherRingIndex m a) = b * L + higherRingIndex m a := by omega
    apply hcross (i₀ - higherRingIndex m a) i (by omega) hi (by omega)
    rwa [hdiff]
  obtain ⟨a, ha0, ha⟩ := paired_ring_color_at_base (by omega : 5 ≤ k - 1) φ hφ (c i) hexcluded
  dsimp only [φ, higherRingIndex] at ha
  rw [ha0] at ha
  simp only [mul_zero, zero_add] at ha
  have he₀ : higherExpectedColor k m c i = higherExpectedColor k m c i₀ := by
    simp only [higherExpectedColor_of_nat]
    change c (i % L) = c (i₀ % L)
    rw [← hsum, Nat.mul_add_mod_self_right]
  have he₁ : higherExpectedColor k m c (i - 1 : Nat) =
      higherExpectedColor k m c (i₀ - 1 : Nat) := by
    simp only [higherExpectedColor_of_nat]
    change c ((i - 1) % L) = c ((i₀ - 1) % L)
    rw [← hsum, Nat.add_sub_assoc (by omega : 1 ≤ i₀), Nat.mul_add_mod_self_right]
  have hab : a.2.val = 0 ∨ a.2.val = 1 := by have := a.2.isLt; omega
  rcases hab with hab | hab
  · left
    rw [hab, Nat.sub_zero] at ha
    rw [he₀, higherExpectedColor_agrees (by omega) hm hq hc (by omega)]
    exact ha.symm
  · right
    rw [hab] at ha
    rw [he₁, higherExpectedColor_agrees (by omega) hm hq hc (by omega)]
    exact ha.symm

theorem higher_even_clean_prefix_two_options {k m q : Nat} (hk : 6 ≤ k) (hm : 0 < m)
    (hq : 3 ≤ q) (heven : k % 2 ≠ 1)
    (c : ZMod (q * higherPeriod k m + 1) → Fin (k - 1))
    (v : ZMod (q * higherPeriod k m + 1))
    (hclean : ∀ j : Nat, j < 3 * higherPeriod k m →
      v + (j : ZMod (q * higherPeriod k m + 1)) ∉ badVertices (higherGraph k m q) c)
    {i : Nat} (hi : i < (q / 2) * higherPeriod k m) :
    c (v + (i : ZMod (q * higherPeriod k m + 1))) =
      higherExpectedColor k m (fun j => c (v + (j : ZMod (q * higherPeriod k m + 1)))) i ∨
    c (v + (i : ZMod (q * higherPeriod k m + 1))) =
      higherExpectedColor k m (fun j => c (v + (j : ZMod (q * higherPeriod k m + 1)))) (i - 1 : Nat) := by
  have hlen : 3 * higherPeriod k m ≤ q * higherPeriod k m + 1 :=
    (Nat.mul_le_mul_right (higherPeriod k m) hq).trans (Nat.le_succ _)
  apply higher_even_two_options_sequence hk hm (by omega) heven
    (higherProperOn_of_clean c v hlen hclean) ?_ hi
  intro j i hj hi hji hd
  have hhalf : (q / 2) * higherPeriod k m ≤ q * higherPeriod k m :=
    Nat.mul_le_mul_right (higherPeriod k m) (Nat.div_le_self q 2)
  exact edge_proper_at_unaffected_vertex (higherGraph k m q) c (hclean j hj)
    (higher_adj_nat_indices hji (by omega) hd v)

theorem higher_even_prefix_agreement {k m r : Nat} (hk : 6 ≤ k) (heven : k % 2 ≠ 1)
    (hm : 4 * r + 3 ≤ m) : HigherPrefixAgreement k m r := by
  intro c hbad v hclean
  apply higher_clean_prefix_agreement_of_two_options hk hm c hbad v hclean
  intro i hi
  exact higher_even_clean_prefix_two_options hk (by omega) (by omega) heven c v hclean hi

theorem higher_prefix_agreement {k m r : Nat} (hk : 6 ≤ k) (hm : 4 * r + 3 ≤ m) :
    HigherPrefixAgreement k m r := by
  by_cases hodd : k % 2 = 1
  · exact higher_odd_prefix_agreement (by omega) hodd hm
  · exact higher_even_prefix_agreement hk hodd hm

theorem higher_ge_six_local_propagation {k m r : Nat} (hk : 6 ≤ k) (hm : 4 * r + 3 ≤ m) :
    HigherLocalPropagation k m r := by
  exact higher_local_propagation_of_prefix (by omega) (by omega) (higher_prefix_agreement hk hm)

theorem higher_ge_six_erdos944 {k r : Nat} (hk : 6 ≤ k) :
    Erdos944.SimpleGraph.IsErdos944 (higherGraph k (18 * r + 3) (24 * r + 12)) k r := by
  exact higher_erdos944_of_local_propagation (by omega) (by omega)
    (higher_ge_six_local_propagation hk (by omega))

universe uSix

theorem erdos944_ge_six {k : Nat} (hk : 6 ≤ k) (r : Nat) :
    ∃ (V : Type uSix) (G : SimpleGraph V), Erdos944.SimpleGraph.IsErdos944 G k r := by
  have hsucc : k - 1 + 1 = k := by omega
  have hG := higher_ge_six_erdos944 (r := r) hk
  have h := erdos944_universe_lift (k := k - 1) (higherGraph k (18 * r + 3) (24 * r + 12))
    (by omega) (by simpa only [hsucc] using hG)
  simpa only [hsucc] using h

theorem higher_five_expected_parity {m q : Nat} (hm : 0 < m) (hq : 2 ≤ q)
    {c : Nat → Fin 4} (hc : HigherProperOn 5 m q c (3 * higherPeriod 5 m))
    {i j : Int} (hpar : i % 2 ≠ j % 2) :
    higherExpectedColor 5 m c i ≠ higherExpectedColor 5 m c j := by
  let L : Int := higherPeriod 5 m
  let d : Int := (j - i) % L
  have hL : L = 4 * (m : Int) := by norm_num [L, higherPeriod]
  have hLpos : 0 < L := by omega
  have hdlo : 0 ≤ d := Int.emod_nonneg _ (ne_of_gt hLpos)
  have hdhi : d < L := Int.emod_lt_of_pos _ hLpos
  have hdpar : d % 2 = 1 := by
    have hdiv : (2 : Int) ∣ L := ⟨2 * m, by omega⟩
    have hmod := Int.emod_emod_of_dvd (j - i) hdiv
    dsimp only [d]
    rw [hmod]
    omega
  have he : higherExpectedColor 5 m c (i + d) = higherExpectedColor 5 m c j := by
    apply higherExpectedColor_eq_of_mod_eq
    change (i + d) % L = j % L
    calc
      _ = (i + (j - i)) % L := by simp only [d, Int.add_emod, Int.emod_emod]
      _ = j % L := by congr 1; ring
  by_cases hsmall : d < 2 * m
  · have hdist : HigherDistance 5 m q d.toNat := Or.inl ⟨by omega, by omega, by omega⟩
    have hn := higherExpectedColor_int_difference (by omega : 5 ≤ 5) hm hq hc
      (i := i) (j := i + d) (by omega) (by omega) (by simpa only [add_sub_cancel_left] using hdist)
    rwa [he] at hn
  · have hdist : HigherDistance 5 m q (L - d).toNat :=
      Or.inl ⟨by omega, by omega, by omega⟩
    have hn := higherExpectedColor_int_difference (by omega : 5 ≤ 5) hm hq hc
      (i := i + d) (j := i + L) (by omega) (by omega)
      (by convert hdist using 1; congr 1; ring)
    rw [he, higherExpectedColor_periodic] at hn
    exact hn.symm

theorem fin_four_palette (a b c d x : Fin 4) (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    x = a ∨ x = b ∨ x = c ∨ x = d := by
  simp only [ne_eq, Fin.ext_iff] at *
  omega

theorem higher_five_expected_same_parity {m q : Nat} (hm : 0 < m) (hq : 2 ≤ q)
    {c : Nat → Fin 4} (hc : HigherProperOn 5 m q c (3 * higherPeriod 5 m))
    (base i : Int) (hpar : i % 2 = base % 2) :
    higherExpectedColor 5 m c i = higherExpectedColor 5 m c base ∨
      higherExpectedColor 5 m c i = higherExpectedColor 5 m c (base + 2 * m) := by
  let f := higherExpectedColor 5 m c
  have hne : f base ≠ f (base + 2 * m) := (higherExpectedColor_ne_two_m (by omega) hm hq hc base).symm
  have hne' : f (base + 1) ≠ f (base + 1 + 2 * m) :=
    (higherExpectedColor_ne_two_m (by omega) hm hq hc (base + 1)).symm
  have hp : ∀ x y : Int, x % 2 ≠ y % 2 → f x ≠ f y :=
    fun _ _ h => higher_five_expected_parity hm hq hc h
  have h := fin_four_palette (f base) (f (base + 2 * m)) (f (base + 1))
    (f (base + 1 + 2 * m)) (f i) hne (hp _ _ (by omega)) (hp _ _ (by omega))
    (hp _ _ (by omega)) (hp _ _ (by omega)) hne'
  rcases h with h | h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact False.elim (hp _ _ (by omega) h)
  · exact False.elim (hp _ _ (by omega) h)

def colorBit {α : Type*} [DecidableEq α] (a color : α) : Int := if a = color then 1 else 0

def colorMass {α : Type*} [DecidableEq α] (c : Nat → α) (start len : Nat) (color : α) : Int :=
  windowSum (fun j => colorBit (c j) color) start len

theorem colorBit_bounds {α : Type*} [DecidableEq α] (a color : α) :
    0 ≤ colorBit a color ∧ colorBit a color ≤ 1 := by
  unfold colorBit
  split <;> omega

theorem windowSum_mono (f g : Nat → Int) (start len : Nat)
    (h : ∀ j : Nat, start ≤ j → j < start + len → f j ≤ g j) :
    windowSum f start len ≤ windowSum g start len := by
  exact partialSum_mono _ _ _ (fun j hj => h (start + j) (by omega) (by omega))

theorem windowSum_congr (f g : Nat → Int) (start len : Nat)
    (h : ∀ j : Nat, start ≤ j → j < start + len → f j = g j) :
    windowSum f start len = windowSum g start len := by
  apply partialSum_congr
  intro j hj
  exact h (start + j) (by omega) (by omega)

theorem windowSum_add (f g : Nat → Int) (start len : Nat) :
    windowSum (fun j => f j + g j) start len = windowSum f start len + windowSum g start len :=
  prefix_add _ _ _

theorem windowSum_const (a : Int) (start len : Nat) :
    windowSum (fun _ => a) start len = (len : Int) * a := prefix_const _ _

theorem windowSum_append (f : Nat → Int) (start a b : Nat) :
    windowSum f start (a + b) = windowSum f start a + windowSum f (start + a) b := by
  induction b with
  | zero => simp only [windowSum, partialSum, add_zero]
  | succ b ih =>
    rw [Nat.add_succ, windowSum_succ, ih, windowSum_succ]
    rw [Nat.add_assoc]
    ring

theorem colorMass_eq_card {α : Type*} [DecidableEq α] (c : Nat → α)
    (start len : Nat) (color : α) : colorMass c start len color =
      ((Finset.univ.filter (fun j : Fin len => c (start + j.val) = color)).card : Int) := by
  unfold colorMass colorBit windowSum
  rw [partialSum_eq_sum_range, ← Fin.sum_univ_eq_sum_range, Finset.sum_boole]

theorem colorMass_nonneg {α : Type*} [DecidableEq α] (c : Nat → α)
    (start len : Nat) (color : α) : 0 ≤ colorMass c start len color := by
  rw [colorMass_eq_card]
  omega

theorem colorMass_shift_bounds {α : Type*} [DecidableEq α] (c : Nat → α)
    (start len : Nat) (color : α) :
    colorMass c start len color - 1 ≤ colorMass c (start + 1) len color ∧
      colorMass c (start + 1) len color ≤ colorMass c start len color + 1 := by
  have h := windowSum_shift (fun j => colorBit (c j) color) start len
  have h₁ := colorBit_bounds (c start) color
  have h₂ := colorBit_bounds (c (start + len)) color
  change colorMass c (start + 1) len color - colorMass c start len color = _ at h
  omega

theorem colorMass_start_change_le {α : Type*} [DecidableEq α] (c : Nat → α)
    (start offset len : Nat) (color : α) :
    colorMass c (start + offset) len color ≤ colorMass c start len color + offset := by
  induction offset with
  | zero => simp only [Nat.cast_zero, add_zero, le_refl]
  | succ offset ih =>
    have h := (colorMass_shift_bounds c (start + offset) len color).2
    rw [Nat.add_assoc] at h
    push_cast
    omega

theorem colorMass_predecessor {α : Type*} [DecidableEq α] (c : Nat → α)
    {start len : Nat} (hstart : 0 < start) (color : α) :
    colorMass (fun j => c (j - 1)) start len color = colorMass c (start - 1) len color := by
  apply partialSum_congr
  intro j _hj
  have he : start + j - 1 = start - 1 + j := by omega
  change colorBit (c (start + j - 1)) color = colorBit (c (start - 1 + j)) color
  rw [he]

theorem colorMass_mixed_parity_le {α : Type*} [DecidableEq α] {m r start a b : Nat}
    {c : Nat → α} (hpar : ShortColorParity m r (fun j => c (start + j)))
    (ha : a < 2 * m) (hb : b < 2 * m) (hab : a % 2 ≠ b % 2)
    (color : α) (hca : c (start + a) = color) (hcb : c (start + b) = color) :
    colorMass c start (2 * m) color ≤ 2 * r := by
  rw [colorMass_eq_card]
  by_contra h
  have hn : 2 * r < (Finset.univ.filter
      (fun j : Fin (2 * m) => c (start + j.val) = color)).card := by omega
  exact hab (hpar color hn ⟨a, ha⟩ ⟨b, hb⟩ hca hcb)

theorem colorMass_short_le {α : Type*} [DecidableEq α] {m r start : Nat}
    (hm : 2 * r ≤ m) {c : Nat → α}
    (hpar : ShortColorParity m r (fun j => c (start + j))) (color : α) :
    colorMass c start (2 * m) color ≤ m := by
  dsimp only [ShortColorParity] at hpar
  rw [colorMass_eq_card]
  by_cases hsmall : (Finset.univ.filter
      (fun j : Fin (2 * m) => c (start + j.val) = color)).card ≤ 2 * r
  · omega
  · have hbound := finite_window_color_card_le_half c start (2 * m) color (by
      intro a b ha hb
      have h := hpar color (by omega) a b ha hb
      omega)
    omega

theorem colorMass_off_start_le {α : Type*} [DecidableEq α] {m r start : Nat}
    {c : Nat → α} (hpar : ShortColorParity m r (fun j => c (start + j)))
    (color : α) (hstart : c start = color) (hm : 0 < m) :
    windowSum (fun j => if c j = color ∧ j % 2 ≠ start % 2 then (1 : Int) else 0)
      start (2 * m) ≤ 2 * r := by
  dsimp only [ShortColorParity] at hpar
  let A := (Finset.univ.filter (fun j : Fin (2 * m) => c (start + j.val) = color)).card
  by_cases hsmall : A ≤ 2 * r
  · have h := windowSum_mono
      (fun j => if c j = color ∧ j % 2 ≠ start % 2 then (1 : Int) else 0)
      (fun j => colorBit (c j) color) start (2 * m) (by
        intro j _ _
        unfold colorBit
        split_ifs <;> simp_all)
    have hc := colorMass_eq_card c start (2 * m) color
    change colorMass c start (2 * m) color = (A : Int) at hc
    change _ ≤ colorMass c start (2 * m) color at h
    omega
  · have he := windowSum_congr
      (fun j => if c j = color ∧ j % 2 ≠ start % 2 then (1 : Int) else 0)
      (fun _ => 0) start (2 * m) (by
        intro j hj hj'
        by_cases hcol : c j = color
        · have hzero : c (start + 0) = color := by simpa only [Nat.add_zero] using hstart
          have hshift : c (start + (j - start)) = color := by
            rwa [Nat.add_sub_of_le hj]
          have hp := hpar color (by omega) ⟨0, by omega⟩ ⟨j - start, by omega⟩ hzero hshift
          have hsame : j % 2 = start % 2 := by dsimp only at hp; omega
          simp only [hsame, ne_eq, not_true_eq_false, and_false, if_false]
        · simp only [hcol, false_and, if_false])
    rw [he, windowSum_const]
    omega

theorem colorBit_two_options_inequality {α : Type*} [DecidableEq α]
    (a b actual color other : α) (hne : color ≠ other)
    (hop : actual = a ∨ actual = b) :
    colorBit a color + colorBit b color + (colorBit a other + colorBit b other) ≤
      1 + colorBit actual color + colorBit actual other := by
  rcases hop with rfl | rfl <;> unfold colorBit <;> split_ifs <;> simp_all

set_option maxHeartbeats 1200000 in
theorem five_first_deviation_impossible {α : Type*} [DecidableEq α]
    {m r i : Nat} {c e : Nat → α} (hm : 18 * r + 20 ≤ m) (hi : 2 * m ≤ i)
    (hclean : ∀ j : Nat, j < i → c j = e j) (hwrong : c i ≠ e i)
    (hop : ∀ j : Nat, j < i + 2 * m → c j = e j ∨ c j = e (j - 1))
    (hpar : ∀ start : Nat, start + 2 * m ≤ i + 2 * m →
      ShortColorParity m r (fun j => c (start + j)))
    (hepar : ∀ a b : Nat, e a = e b → a % 2 = b % 2)
    (heoptions : ∀ base j : Nat, j % 2 = base % 2 →
      e j = e base ∨ e j = e (base + 2 * m))
    (hecount : ∀ start : Nat, ∀ color : α, colorMass e start (4 * m) color = m) : False := by
  let left := i - 2 * m + 1
  let right := i - 2
  let gamma := e (i - 1)
  let delta := e right
  let epsilon := e (right + 2 * m)
  have hleft : left + 2 * m = i + 1 := by dsimp only [left]; omega
  have hright : right + 2 = i := by dsimp only [right]; omega
  have hrightpos : 0 < right := by omega
  have hleftfit : left + 2 * m ≤ i + 2 * m := by omega
  have hrightfit : right + 2 * m ≤ i + 2 * m := by omega
  have hgamma₀ : c (i - 1) = gamma := hclean (i - 1) (by omega)
  have hgamma₁ : c i = gamma := (hop i (by omega)).resolve_left hwrong
  have hdelta : c right = delta := hclean right (by omega)
  have hCgL : colorMass c left (2 * m) gamma ≤ 2 * r := by
    apply colorMass_mixed_parity_le (a := 2 * m - 2) (b := 2 * m - 1)
      (hpar left hleftfit) (by omega) (by omega) (by omega) gamma
    · have heq : left + (2 * m - 2) = i - 1 := by omega
      rwa [heq]
    · have heq : left + (2 * m - 1) = i := by omega
      rwa [heq]
  have hCgR : colorMass c right (2 * m) gamma ≤ 2 * r := by
    apply colorMass_mixed_parity_le (a := 1) (b := 2)
      (hpar right hrightfit) (by omega) (by omega) (by omega) gamma
    · have heq : right + 1 = i - 1 := by omega
      rwa [heq]
    · rwa [hright]
  have hEL : colorMass e left (2 * m) gamma ≤ colorMass c left (2 * m) gamma := by
    apply windowSum_mono
    intro j hj hj'
    by_cases hji : j < i
    · rw [hclean j hji]
    · have hji' : j = i := by omega
      subst j
      rw [hgamma₁]
      simpa only [colorBit, if_true] using (colorBit_bounds (e i) gamma).2
  let A := colorMass e right (2 * m) gamma
  let B := colorMass e right (2 * m) epsilon
  have hA : (m : Int) ≤ A + 2 * r + 3 := by
    have hsum := windowSum_append (fun j => colorBit (e j) gamma) left (2 * m) (2 * m)
    have hfour : 2 * m + 2 * m = 4 * m := by omega
    change colorMass e left (2 * m + 2 * m) gamma =
      colorMass e left (2 * m) gamma + colorMass e (left + 2 * m) (2 * m) gamma at hsum
    rw [hfour, hecount left gamma] at hsum
    have hshift := colorMass_start_change_le e right 3 (2 * m) gamma
    have heq : right + 3 = left + 2 * m := by omega
    rw [heq] at hshift
    change _ ≤ A + (3 : Nat) at hshift
    omega
  have hoff := colorMass_off_start_le (hpar right hrightfit) delta hdelta (by omega : 0 < m)
  have hgamma_par : ∀ j : Nat, e j = gamma → j % 2 ≠ right % 2 := by
    intro j hj
    have hp := hepar j (i - 1) hj
    omega
  have htransfer : ∀ j : Nat, right ≤ j → j < right + 2 * m →
      colorBit (e j) gamma ≤ colorBit (c j) gamma +
        (if c j = delta ∧ j % 2 ≠ right % 2 then (1 : Int) else 0) +
        colorBit (e (j - 1)) epsilon := by
    intro j hj hj'
    by_cases heg : e j = gamma
    · have hjpar := hgamma_par j heg
      have hprev := heoptions right (j - 1) (by omega)
      have hactual := hop j (by omega)
      rcases hactual with hactual | hactual
      · have hcg : c j = gamma := hactual.trans heg
        unfold colorBit
        split_ifs <;> simp_all
      · rcases hprev with hprev | hprev
        · have hcd : c j = delta := hactual.trans hprev
          unfold colorBit
          split_ifs <;> simp_all
        · change e (j - 1) = epsilon at hprev
          unfold colorBit
          split_ifs <;> simp_all
    · unfold colorBit
      split_ifs <;> simp_all
  have hB : A ≤ B + 4 * r + 1 := by
    have hsum := windowSum_mono _ _ right (2 * m) htransfer
    rw [windowSum_add, windowSum_add] at hsum
    change A ≤ colorMass c right (2 * m) gamma + _ +
      colorMass (fun j => e (j - 1)) right (2 * m) epsilon at hsum
    rw [colorMass_predecessor e hrightpos epsilon] at hsum
    have hshift := (colorMass_shift_bounds e (right - 1) (2 * m) epsilon).1
    have heq : right - 1 + 1 = right := by omega
    rw [heq] at hshift
    change _ ≤ B at hshift
    omega
  have hge : gamma ≠ epsilon := by
    intro he
    have hp := hepar (i - 1) (right + 2 * m) he
    omega
  have hcombined := windowSum_mono
    (fun j => colorBit (e j) gamma + colorBit (e (j - 1)) gamma +
      (colorBit (e j) epsilon + colorBit (e (j - 1)) epsilon))
    (fun j => 1 + colorBit (c j) gamma + colorBit (c j) epsilon) right (2 * m) (by
      intro j _hj hj'
      exact colorBit_two_options_inequality _ _ _ _ _ hge (hop j (by omega)))
  simp only [windowSum_add, windowSum_const, mul_one] at hcombined
  change A + colorMass (fun j => e (j - 1)) right (2 * m) gamma +
    (B + colorMass (fun j => e (j - 1)) right (2 * m) epsilon) ≤
    (2 * m : Nat) + colorMass c right (2 * m) gamma + colorMass c right (2 * m) epsilon at hcombined
  rw [colorMass_predecessor e hrightpos gamma, colorMass_predecessor e hrightpos epsilon] at hcombined
  have hgshift := (colorMass_shift_bounds e (right - 1) (2 * m) gamma).2
  have heshift := (colorMass_shift_bounds e (right - 1) (2 * m) epsilon).2
  have hreq : right - 1 + 1 = right := by omega
  rw [hreq] at hgshift heshift
  change A ≤ _ at hgshift
  change B ≤ _ at heshift
  have hCe := colorMass_short_le (by omega : 2 * r ≤ m) (hpar right hrightfit) epsilon
  omega

theorem five_expected_agreement {α : Type*} [DecidableEq α]
    {m r initial len span : Nat} {c e : Nat → α} (hm : 18 * r + 20 ≤ m)
    (hinitial : 2 * m ≤ initial) (hmargin : len + 2 * m ≤ span)
    (hclean : ∀ j : Nat, j < initial → c j = e j)
    (hop : ∀ j : Nat, j < span → c j = e j ∨ c j = e (j - 1))
    (hpar : ∀ start : Nat, start + 2 * m ≤ span →
      ShortColorParity m r (fun j => c (start + j)))
    (hepar : ∀ a b : Nat, e a = e b → a % 2 = b % 2)
    (heoptions : ∀ base j : Nat, j % 2 = base % 2 →
      e j = e base ∨ e j = e (base + 2 * m))
    (hecount : ∀ start : Nat, ∀ color : α, colorMass e start (4 * m) color = m) :
    ∀ j : Nat, j < len → c j = e j := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro hi
    by_cases hic : i < initial
    · exact hclean i hic
    by_contra hwrong
    exact five_first_deviation_impossible hm (by omega)
      (fun j hj => ih j hj (by omega)) hwrong (fun j hj => hop j (by omega))
      (fun start hs => hpar start (by omega)) hepar heoptions hecount

theorem higher_five_prefix_agreement {m r : Nat} (hm : 18 * r + 20 ≤ m) :
    HigherPrefixAgreement 5 m r := by
  intro c hbad v hclean
  let L := higherPeriod 5 m
  let q := 24 * r + 12
  let B := (6 * r + 3) * L
  let d : Nat → Fin 4 := fun j => c (v + (j : ZMod (q * L + 1)))
  have hmpos : 0 < m := by omega
  have hq : 3 ≤ q := by dsimp only [q]; omega
  have hL : L = 4 * m := by norm_num [L, higherPeriod]
  have hQL : 3 * L ≤ q * L := Nat.mul_le_mul_right L hq
  have hlen : 3 * L ≤ q * L + 1 := by omega
  have hproper : HigherProperOn 5 m q d (3 * L) := higherProperOn_of_clean c v hlen hclean
  have hLB : L ≤ B := by
    have h := Nat.mul_le_mul_right L (by omega : 1 ≤ 6 * r + 3)
    simpa only [one_mul] using h
  have hhalf : (q / 2) * L = 2 * B := by
    have hdiv : q / 2 = 12 * r + 6 := by dsimp only [q]; omega
    rw [hdiv]
    dsimp only [B]
    ring
  change ∀ i : Nat, i < B → d i = higherExpectedColor 5 m d i
  apply five_expected_agreement (initial := 3 * L) (len := B) (span := 2 * B) hm
    (by omega) (by omega)
  · intro i hi
    exact (higherExpectedColor_agrees (by omega) hmpos (by omega) hproper hi).symm
  · intro i hi
    have hi' : i < (q / 2) * L := by rw [hhalf]; exact hi
    exact higher_odd_clean_prefix_two_options (by omega) hmpos (by omega) (by omega) c v hclean hi'
  · intro start _hfit
    have h := higher_shortColorParity (by omega : 2 * m ≤ q * L + 1) c hbad
      (v + (start : ZMod (q * L + 1)))
    simpa only [ShortColorParity, d, Nat.cast_add, add_assoc] using h
  · intro a b he
    by_contra hpar
    exact higher_five_expected_parity hmpos (by omega) hproper (by omega) he
  · intro base j hpar
    have h := higher_five_expected_same_parity hmpos (by omega) hproper base j (by omega)
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using h
  · intro start color
    have h := higherExpectedColor_window_count (by omega : 5 ≤ 5) hmpos (by omega) hproper start color
    simpa only [higherPeriod, Nat.reduceSub, Nat.reduceMod, if_true, colorMass, colorBit] using h

theorem higher_five_local_propagation {m r : Nat} (hm : 18 * r + 20 ≤ m) :
    HigherLocalPropagation 5 m r := by
  exact higher_local_propagation_of_prefix (by omega) (by omega) (higher_five_prefix_agreement hm)

theorem higher_five_erdos944 (r : Nat) :
    Erdos944.SimpleGraph.IsErdos944 (higherGraph 5 (18 * r + 20) (24 * r + 12)) 5 r := by
  exact higher_erdos944_of_local_propagation (by omega) (by omega)
    (higher_five_local_propagation (by omega))

universe uFive uAll

theorem erdos944_five (r : Nat) :
    ∃ (V : Type uFive) (G : SimpleGraph V), Erdos944.SimpleGraph.IsErdos944 G 5 r := by
  exact erdos944_universe_lift (k := 4) (higherGraph 5 (18 * r + 20) (24 * r + 12))
    (by omega) (higher_five_erdos944 r)

theorem erdos944_all {k : Nat} (hk : 4 ≤ k) (r : Nat) :
    ∃ (V : Type uAll) (G : SimpleGraph V), Erdos944.SimpleGraph.IsErdos944 G k r := by
  by_cases hfour : k = 4
  · subst k
    exact erdos944_four r
  by_cases hfive : k = 5
  · subst k
    exact erdos944_five r
  exact erdos944_ge_six (by omega) r

end Erdos944Proof

theorem target : fcTypeOfName% "Erdos944.erdos_944" := by
  constructor
  · intro _ k hk r _hr
    exact Erdos944Proof.erdos944_all hk r
  · intro _
    trivial

end Bounty
