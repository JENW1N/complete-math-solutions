import KohlmeyerKruerPartI
import KitamuraPartII

/-!
# The two currently formalized targets of Erdős Problem 354

Part (i) is due to Jensen Kohlmeyer and Liam Kruer.
The existential variant of part (ii) is due to Kenta Kitamura.
The common definitions are copied from Formal Conjectures; neither admitted
problem theorem is imported. This file does not assert the universal
variable-base statement from the source discussion.
-/

namespace Erdos354Combined

/-- Completeness for every positive coefficient pair with irrational ratio,
with the base fixed in advance. -/
def CompleteAtBase (γ : ℝ) : Prop :=
  ∀ α > 0, ∀ β > 0, Irrational (α / β) →
    IsAddCompleteNatSeq' (Erdos354.FloorMultiples.interleave α β γ)

/-- The base-two question: Kohlmeyer–Kruer. -/
theorem part_i : CompleteAtBase 2 :=
  Bounty.target.mp trivial

/-- The existential variable-base question: Kitamura. -/
theorem part_ii_exists : ∃ γ ∈ Set.Ioo (1 : ℝ) 2, CompleteAtBase γ :=
  Erdos354PartIIProof.erdos_354_part_ii_solved.mp trivial

/-- The stronger single-sequence result behind the existential answer. -/
theorem single_sqrt_phi_complete (α : ℝ) (hα : 0 < α) :
    ∃ L : ℤ, ∀ z ≥ L, ∃ t : Finset ℕ,
      ∑ i ∈ t, ⌊Erdos354PartIIProof.gamma ^ i * α⌋ = z :=
  Erdos354PartIIProof.single_complete α hα

/-- Both current Formal Conjectures targets, stated with explicit answers
and no admitted source theorems. The second conjunct is existential. -/
theorem combined_current_targets :
    (True ↔ ∀ α > 0, ∀ β > 0, Irrational (α / β) →
      IsAddCompleteNatSeq' (Erdos354.FloorMultiples.interleave α β 2)) ∧
    (True ↔ ∃ γ ∈ Set.Ioo (1 : ℝ) 2,
      ∀ α > 0, ∀ β > 0, Irrational (α / β) →
        IsAddCompleteNatSeq' (Erdos354.FloorMultiples.interleave α β γ)) :=
  ⟨Bounty.target, Erdos354PartIIProof.erdos_354_part_ii_solved⟩

end Erdos354Combined

#print axioms Erdos354Combined.part_i
#print axioms Erdos354Combined.part_ii_exists
#print axioms Erdos354Combined.single_sqrt_phi_complete
#print axioms Erdos354Combined.combined_current_targets
