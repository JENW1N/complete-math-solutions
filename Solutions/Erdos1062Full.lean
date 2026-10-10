import Solutions.Erdos1062

/-!
# Erdős problem 1062: the exact extremal function and its irrational density

This file exports both parts of the problem.  The finite formula below uses
explicit arithmetic definitions, independently of the extremal function `f`.
It is the manuscript's formula, with integer division representing the floor
and with the natural extension `R 0 = 0`.  Its proof uses the combinatorial
theorems in `Solutions.Erdos1062`; the density proof uses that module's ordinary
Lean proof of the explicit coefficient series and its irrationality.

No theorem containing an `answer` placeholder occurs in the statements below.
The axiom audits at the end cover the exported results, including the combined
statement `full_scope`.
-/

open Filter
open scoped Topology Classical

namespace Erdos1062Full

/-- The manuscript's local rank bound, extended to the empty interval. -/
def R (n : ℕ) : ℕ :=
  if n = 0 then 0 else
    Nat.log 3 n + 1 + Nat.log 2 n / 2 +
      if Nat.log 2 n % 2 = 1 ∧ 2 * 3 ^ Nat.log 3 n ≤ n then 1 else 0

/-- The manuscript's exceptional window; all inequalities are integral. -/
def B (n : ℕ) : Prop :=
  ∃ j b : ℕ, 4 ^ j ≤ n ∧ 4 * n < 5 * 4 ^ j ∧
    10 * 3 ^ b ≤ n ∧ n < 12 * 3 ^ b

/-- The manuscript's signed local contribution `R(n) - 1_B(n)`. -/
noncomputable def g (n : ℕ) : ℤ := by
  classical
  exact (R n : ℤ) - if B n then 1 else 0

/-- The real cast of the explicit integer contribution agrees with the
contribution used in the verified combinatorial convolution. -/
theorem g_cast (n : ℕ) : (g n : ℝ) = Bounty.signedRank n := by
  classical
  change (((R n : ℤ) - (if B n then 1 else 0) : ℤ) : ℝ) =
    (R n : ℝ) - if B n then 1 else 0
  split_ifs <;> norm_cast

/-- Exact formula for every natural number, including zero.  The summation is
over precisely the positive integers at most `n` coprime to six. -/
theorem exact_formula_real (n : ℕ) :
    (Erdos1062.f n : ℝ) =
      ∑ q ∈ (Finset.Icc 1 n).filter (fun q => q.Coprime 6), (g (n / q) : ℝ) := by
  classical
  calc
    (Erdos1062.f n : ℝ) = (Bounty.globalUpper n : ℝ) :=
      congrArg (fun m : ℕ => (m : ℝ)) (Bounty.f_eq_globalUpper n)
    _ = ∑ q ∈ (Finset.Icc 1 n).filter (fun q => q.Coprime 6), (g (n / q) : ℝ) := by
      simpa only [Bounty.coprimeCores, g_cast] using Bounty.globalUpper_cast_sum n

/-- The exact integer value of the extremal function for every `n`. -/
theorem exact_formula (n : ℕ) :
    (Erdos1062.f n : ℤ) =
      ∑ q ∈ (Finset.Icc 1 n).filter (fun q => q.Coprime 6), g (n / q) := by
  exact_mod_cast exact_formula_real n

/-- The same exact formula as a natural sum minus the number of exceptional
components.  The subtraction here is natural-number subtraction. -/
theorem exact_formula_nat (n : ℕ) :
    Erdos1062.f n =
      (∑ q ∈ (Finset.Icc 1 n).filter (fun q => q.Coprime 6), R (n / q)) -
        (((Finset.Icc 1 n).filter (fun q => q.Coprime 6)).filter
          (fun q => B (n / q))).card := by
  change Erdos1062.f n = Bounty.globalUpper n
  exact Bounty.f_eq_globalUpper n

/-- Part (i): the exact formula, with the correction inside the integer sum. -/
theorem part_i (n : ℕ) :
    (Erdos1062.f n : ℤ) =
      ∑ q ∈ (Finset.Icc 1 n).filter (fun q => q.Coprime 6), g (n / q) :=
  exact_formula n

/-- The extremal densities converge to the manuscript's explicit series. -/
theorem density_converges :
    Tendsto (fun n : ℕ => (Erdos1062.f n : ℝ) / n)
      atTop (𝓝 Bounty.explicitDensity) := by
  simpa only [Bounty.jumpDensity_eq_explicitDensity] using Bounty.tendsto_f_jumpDensity

/-- The limit in the preceding theorem is irrational. -/
theorem density_irrational : Irrational Bounty.explicitDensity :=
  Bounty.target_iff_irrational_explicitDensity.mp Bounty.target

/-- Part (ii), stated directly without a FormalConjectures answer placeholder. -/
theorem part_ii :
    ∃ l : ℝ, Tendsto (fun n : ℕ => (Erdos1062.f n : ℝ) / n) atTop (𝓝 l) ∧
      Irrational l :=
  ⟨Bounty.explicitDensity, density_converges, density_irrational⟩

/-- The full problem: an exact finite formula and convergence to the explicitly
identified irrational density. -/
theorem full_scope :
    (∀ n : ℕ, (Erdos1062.f n : ℤ) =
      ∑ q ∈ (Finset.Icc 1 n).filter (fun q => q.Coprime 6), g (n / q)) ∧
    Tendsto (fun n : ℕ => (Erdos1062.f n : ℝ) / n)
      atTop (𝓝 Bounty.explicitDensity) ∧
    Irrational Bounty.explicitDensity :=
  ⟨part_i, density_converges, density_irrational⟩

end Erdos1062Full

#print axioms Erdos1062Full.g_cast
#print axioms Erdos1062Full.exact_formula_real
#print axioms Erdos1062Full.exact_formula
#print axioms Erdos1062Full.exact_formula_nat
#print axioms Erdos1062Full.part_i
#print axioms Erdos1062Full.density_converges
#print axioms Erdos1062Full.density_irrational
#print axioms Erdos1062Full.part_ii
#print axioms Erdos1062Full.full_scope
