import Combined

/-!
# Separating the two variable-base statements

This file formalizes the parity obstruction and the exact consequence of an
all-even counterexample. It does NOT assert or assume as an axiom that such
real parameters exist. Their existence is the additional analytic/number
field input in Geneson, Corollary 12 (arXiv:2609.25107v1).
-/

open Finset Filter

namespace Erdos354Combined

/-- A sequence of even integers cannot represent every sufficiently large integer. -/
theorem not_complete_of_all_even {a : ℕ → ℤ} (ha : ∀ n, Even (a n)) :
    ¬ IsAddCompleteNatSeq' a := by
  intro hcomplete
  obtain ⟨L, hL⟩ := eventually_atTop.mp hcomplete
  let z : ℤ := 2 * max L 0 + 1
  have hz : L ≤ z := by dsimp [z]; omega
  obtain ⟨s, hs⟩ := hL z hz
  have hsum : ∀ t : Finset ℕ, Even (∑ i ∈ t, a i) := by
    classical
    intro t
    induction t using Finset.induction_on with
    | empty => exact ⟨0, by simp⟩
    | @insert i t hi ih =>
        rw [sum_insert hi]
        exact (ha i).add ih
  obtain ⟨k, hk⟩ := hsum s
  rw [← hs] at hk
  dsimp [z] at hk
  omega

/-- The parity conclusion of Geneson's example suffices for incompleteness. -/
theorem interleave_not_complete_of_all_even {α β γ : ℝ}
    (ha : ∀ n : ℕ, Even (⌊γ ^ n * α⌋ : ℤ))
    (hb : ∀ n : ℕ, Even (⌊γ ^ n * β⌋ : ℤ)) :
    ¬ IsAddCompleteNatSeq' (Erdos354.FloorMultiples.interleave α β γ) := by
  apply not_complete_of_all_even
  intro n
  unfold Erdos354.FloorMultiples.interleave Erdos354.FloorMultiples
  split
  · exact ha _
  · exact hb _

/-- This is the existential counterexample input still needed for a full
formal disproof of the universal variable-base question. -/
def EvenCounterexampleExists : Prop :=
  ∃ γ ∈ Set.Ioo (1 : ℝ) 2, ∃ α > 0, ∃ β > 0,
    Irrational (α / β) ∧
    (∀ n : ℕ, Even (⌊γ ^ n * α⌋ : ℤ)) ∧
    (∀ n : ℕ, Even (⌊γ ^ n * β⌋ : ℤ))

/-- Conditional only: once the real-parameter counterexample is formalized,
the universal variable-base statement is formally refuted. -/
theorem universal_false_of_even_counterexample (h : EvenCounterexampleExists) :
    ¬ (∀ γ ∈ Set.Ioo (1 : ℝ) 2, CompleteAtBase γ) := by
  obtain ⟨γ, hγ, α, hα, β, hβ, hirr, ha, hb⟩ := h
  intro hall
  exact interleave_not_complete_of_all_even ha hb (hall γ hγ α hα β hβ hirr)

/-- A half-unit interval above an integer forces the doubled floor to be even. -/
lemma even_floor_twice_of_window (x : ℝ) (k : ℤ)
    (hl : (k : ℝ) ≤ x) (hu : x < (k : ℝ) + 1 / 2) :
    Even (⌊2 * x⌋ : ℤ) := by
  refine ⟨k, ?_⟩
  apply Int.floor_eq_iff.mpr
  constructor <;> push_cast <;> linarith

/-- The elementary part of the counterexample construction, with its analytic
input made explicit. The lower fractional-part bound in the paper is not
needed once positivity and irrationality are available. -/
theorem even_counterexample_of_small_fractional_parts
    {γ η : ℝ} (hγ : γ ∈ Set.Ioo (1 : ℝ) 2) (hirr : Irrational γ)
    (hη : 0 < η)
    (hfrac : ∀ j : ℕ, 1 ≤ j → Int.fract (η * γ ^ j) < 1 / 4) :
    EvenCounterexampleExists := by
  let α : ℝ := 2 * η * γ
  let β : ℝ := α * (1 + γ)
  have hgpos : 0 < γ := lt_trans zero_lt_one hγ.1
  have ha : 0 < α := by dsimp [α]; positivity
  have hb : 0 < β := by dsimp [β]; positivity
  have hratio : α / β = (1 + γ)⁻¹ := by
    dsimp [β]
    field_simp [ne_of_gt ha]
  have hi : Irrational (α / β) := by
    rw [hratio]
    have h : Irrational (γ + (1 : ℤ)) := hirr.add_intCast 1
    simpa [add_comm] using h.inv
  refine ⟨γ, hγ, α, ha, β, hb, hi, ?_, ?_⟩
  · intro n
    have heq : γ ^ n * α = 2 * (η * γ ^ (n + 1)) := by
      dsimp [α]
      rw [pow_succ]
      ring
    rw [heq]
    apply even_floor_twice_of_window _ ⌊η * γ ^ (n + 1)⌋
    · exact Int.floor_le _
    · have h := hfrac (n + 1) (by omega)
      unfold Int.fract at h
      linarith
  · intro n
    have heq : γ ^ n * β =
        2 * (η * γ ^ (n + 1) + η * γ ^ (n + 2)) := by
      dsimp [β, α]
      simp only [pow_succ]
      ring
    rw [heq]
    apply even_floor_twice_of_window _
      (⌊η * γ ^ (n + 1)⌋ + ⌊η * γ ^ (n + 2)⌋)
    · push_cast
      exact add_le_add (Int.floor_le _) (Int.floor_le _)
    · have h1 := hfrac (n + 1) (by omega)
      have h2 := hfrac (n + 2) (by omega)
      unfold Int.fract at h1 h2
      push_cast
      linarith

/-- Exact remaining existence input: a positive coefficient whose fractional
parts stay below one quarter for an irrational base in (1,2). -/
def SmallFractionalPartsExist : Prop :=
  ∃ γ ∈ Set.Ioo (1 : ℝ) 2, Irrational γ ∧
    ∃ η > 0, ∀ j : ℕ, 1 ≤ j → Int.fract (η * γ ^ j) < 1 / 4

/-- This reduction is unconditional as a logical implication; the premise is
not supplied by the combined affirmative proofs. -/
theorem universal_false_of_small_fractional_parts (h : SmallFractionalPartsExist) :
    ¬ (∀ γ ∈ Set.Ioo (1 : ℝ) 2, CompleteAtBase γ) := by
  obtain ⟨γ, hγ, hi, η, hη, hf⟩ := h
  exact universal_false_of_even_counterexample
    (even_counterexample_of_small_fractional_parts hγ hi hη hf)

end Erdos354Combined

#print axioms Erdos354Combined.not_complete_of_all_even
#print axioms Erdos354Combined.universal_false_of_even_counterexample

#print axioms Erdos354Combined.universal_false_of_small_fractional_parts
