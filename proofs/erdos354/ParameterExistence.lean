import MultinacciIntegers
import QuantifierObstruction

/-!
# Closing the parameter-existence premise for Erdős Problem 354

The six-term recurrence provides the positive fractional-part witness needed
by the parity argument. This gives a base in (1,2). It uses a different base
from Geneson's stronger Salem-number construction in (1,φ).
-/

namespace Erdos354Parameters

theorem small_fractional_parts_exist : Erdos354Combined.SmallFractionalPartsExist := by
  obtain ⟨η, hη, hf⟩ := exists_positive_fractional_part_witness
  exact ⟨base, base_bounds, base_irrational, η, hη, fun j hj => (hf j hj).2⟩

theorem even_counterexample_exists : Erdos354Combined.EvenCounterexampleExists := by
  obtain ⟨γ, hγ, hi, η, hη, hf⟩ := small_fractional_parts_exist
  exact Erdos354Combined.even_counterexample_of_small_fractional_parts hγ hi hη hf

/-- An unconditional counterexample with all the hypotheses required by #354. -/
theorem universal_counterexample :
    ∃ γ ∈ Set.Ioo (1 : ℝ) 2, ∃ α > 0, ∃ β > 0,
      Irrational (α / β) ∧
      ¬ IsAddCompleteNatSeq' (Erdos354.FloorMultiples.interleave α β γ) := by
  obtain ⟨γ, hγ, α, hα, β, hβ, hi, ha, hb⟩ := even_counterexample_exists
  exact ⟨γ, hγ, α, hα, β, hβ, hi,
    Erdos354Combined.interleave_not_complete_of_all_even ha hb⟩

theorem universal_variable_base_false :
    ¬ (∀ γ ∈ Set.Ioo (1 : ℝ) 2, Erdos354Combined.CompleteAtBase γ) :=
  Erdos354Combined.universal_false_of_small_fractional_parts small_fractional_parts_exist

end Erdos354Parameters

#print axioms Erdos354Parameters.small_fractional_parts_exist
#print axioms Erdos354Parameters.even_counterexample_exists
#print axioms Erdos354Parameters.universal_counterexample
#print axioms Erdos354Parameters.universal_variable_base_false
