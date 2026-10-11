import Erdos354Definitions

/-!
# An explicit algebraic base for the parameter-existence theorem

The base is a real root in (1,2) of X^6 - X^5 - X^4 - X^3 - X^2 - X - 1.
The rational root theorem proves that it is irrational.
-/

noncomputable section

open Polynomial

namespace Erdos354Parameters

def basePolynomial : ℤ[X] := X ^ 6 - X ^ 5 - X ^ 4 - X ^ 3 - X ^ 2 - X - 1

def baseEquation (x : ℝ) : ℝ := x ^ 6 - x ^ 5 - x ^ 4 - x ^ 3 - x ^ 2 - x - 1

theorem exists_base : ∃ x ∈ Set.Ioo (1 : ℝ) 2, baseEquation x = 0 := by
  have hc : Continuous baseEquation := by unfold baseEquation; fun_prop
  have h1 : baseEquation 1 < 0 := by norm_num [baseEquation]
  have h2 : 0 < baseEquation 2 := by norm_num [baseEquation]
  obtain ⟨x, hx, heq⟩ := intermediate_value_Icc (by norm_num : (1 : ℝ) ≤ 2)
    hc.continuousOn (show (0 : ℝ) ∈ Set.Icc (baseEquation 1) (baseEquation 2) from
      ⟨h1.le, h2.le⟩)
  refine ⟨x, ⟨?_, ?_⟩, heq⟩
  · exact lt_of_le_of_ne hx.1 (by intro h; subst x; linarith)
  · exact lt_of_le_of_ne hx.2 (by intro h; subst x; linarith)

noncomputable def base : ℝ := Classical.choose exists_base

theorem base_bounds : base ∈ Set.Ioo (1 : ℝ) 2 :=
  (Classical.choose_spec exists_base).1

theorem base_equation : baseEquation base = 0 :=
  (Classical.choose_spec exists_base).2

theorem base_irrational : Irrational base := by
  rintro ⟨q, hq⟩
  have hroot : q ^ 6 - q ^ 5 - q ^ 4 - q ^ 3 - q ^ 2 - q - 1 = (0 : ℚ) := by
    have h := base_equation
    rw [← hq] at h
    unfold baseEquation at h
    exact_mod_cast h
  have hi : IsLocalization.IsInteger ℤ q := by
    apply isInteger_of_is_root_of_monic (p := basePolynomial)
    · unfold basePolynomial
      monicity!
    · simpa [basePolynomial] using hroot
  obtain ⟨m, hm⟩ := hi
  change (m : ℚ) = q at hm
  have hbounds := base_bounds
  rw [← hq, ← hm] at hbounds
  norm_num at hbounds
  have hmlo : (1 : ℤ) < m := by exact_mod_cast hbounds.1
  have hmhi : m < (2 : ℤ) := by exact_mod_cast hbounds.2
  omega

#print axioms base_irrational

end Erdos354Parameters
