import ParameterExistence

/-!
# Complete formal answers for Erdős Problem 354 and both variable-base readings

The base-two proof is due to Jensen Kohlmeyer and Liam Kruer. The affirmative
existential result is due to Kenta Kitamura. The negative universal result
uses the independently verified recurrence construction in ParameterExistence.
All three statements use the same original floor/interleaving/completeness
definitions, with no unproved parameter-existence assumption.
-/

namespace Erdos354Full

/-- The universal variable-base reading has the negative answer. -/
theorem variable_base_answer : False ↔
    ∀ γ ∈ Set.Ioo (1 : ℝ) 2,
      ∀ α > 0, ∀ β > 0, Irrational (α / β) →
        IsAddCompleteNatSeq' (Erdos354.FloorMultiples.interleave α β γ) := by
  constructor
  · exact False.elim
  · exact Erdos354Parameters.universal_variable_base_false

/-- All three unconditional results: the base-two theorem, a universally
working base in (1,2), and a counterexample to the every-base claim. -/
theorem full_solution :
    (∀ α > 0, ∀ β > 0, Irrational (α / β) →
      IsAddCompleteNatSeq' (Erdos354.FloorMultiples.interleave α β 2)) ∧
    (∃ γ ∈ Set.Ioo (1 : ℝ) 2,
      ∀ α > 0, ∀ β > 0, Irrational (α / β) →
        IsAddCompleteNatSeq' (Erdos354.FloorMultiples.interleave α β γ)) ∧
    (∃ γ ∈ Set.Ioo (1 : ℝ) 2, ∃ α > 0, ∃ β > 0,
      Irrational (α / β) ∧
      ¬ IsAddCompleteNatSeq' (Erdos354.FloorMultiples.interleave α β γ)) :=
  ⟨Erdos354Combined.part_i, Erdos354Combined.part_ii_exists,
    Erdos354Parameters.universal_counterexample⟩

end Erdos354Full

#print axioms Erdos354Full.variable_base_answer
#print axioms Erdos354Full.full_solution
