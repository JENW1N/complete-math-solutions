import Erdos354Definitions

/-!
# Decay of a strictly subconvex finite-memory recurrence

This is the analytic estimate used in the parameter-existence construction.
All coefficients are nonnegative and their sum is strictly less than one.
-/

open Finset Filter
open scoped Topology

namespace Erdos354Parameters

theorem tendsto_zero_of_subconvex_recurrence
    {d : ℕ} (_hd : 0 < d) (u : ℕ → ℝ) (w : Fin d → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i < 1)
    (hu : ∀ n, u (n + d) = ∑ i : Fin d, w i * u (n + i)) :
    Tendsto u atTop (nhds 0) := by
  let C : ℝ := (∑ i : Fin d, |u i|) + 1
  let q : ℝ := ∑ i, w i
  have hC : 0 < C := by
    dsimp [C]
    positivity
  have hq : 0 ≤ q := sum_nonneg (fun i _ => hw i)
  have hq1 : q < 1 := hs
  have hinit : ∀ n < d, |u n| ≤ C := by
    intro n hn
    have hh := single_le_sum (fun i (_ : i ∈ (univ : Finset (Fin d))) => abs_nonneg (u i))
      (mem_univ (⟨n, hn⟩ : Fin d))
    dsimp [C]
    simpa using hh.trans (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1))
  have hglobal : ∀ n, |u n| ≤ C := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hn : n < d
      · exact hinit n hn
      · have hdn : d ≤ n := by omega
        rw [show n = (n - d) + d by omega, hu]
        calc
          |∑ i : Fin d, w i * u (n - d + i)| ≤
              ∑ i : Fin d, |w i * u (n - d + i)| := abs_sum_le_sum_abs _ _
          _ = ∑ i : Fin d, w i * |u (n - d + i)| := by
            simp only [abs_mul, abs_of_nonneg (hw _)]
          _ ≤ ∑ i : Fin d, w i * C := by
            apply sum_le_sum
            intro i _
            exact mul_le_mul_of_nonneg_left (ih _ (by omega)) (hw i)
          _ = q * C := by rw [← sum_mul]
          _ ≤ C := by nlinarith
  have hblock : ∀ k n, d * k ≤ n → |u n| ≤ C * q ^ k := by
    intro k
    induction k with
    | zero => simpa using hglobal
    | succ k ih =>
      intro n hn
      have hn' : d * k + d ≤ n := by simpa only [Nat.mul_succ] using hn
      have hdn : d ≤ n := by omega
      rw [show n = (n - d) + d by omega, hu]
      calc
        |∑ i : Fin d, w i * u (n - d + i)| ≤
            ∑ i : Fin d, |w i * u (n - d + i)| := abs_sum_le_sum_abs _ _
        _ = ∑ i : Fin d, w i * |u (n - d + i)| := by
          simp only [abs_mul, abs_of_nonneg (hw _)]
        _ ≤ ∑ i : Fin d, w i * (C * q ^ k) := by
          apply sum_le_sum
          intro i _
          apply mul_le_mul_of_nonneg_left _ (hw i)
          exact ih _ (by omega)
        _ = C * q ^ (k + 1) := by rw [← sum_mul, pow_succ]; dsimp [q]; ring
  have hp : Tendsto (fun k : ℕ => C * q ^ k) atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one hq hq1)
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨K, hK⟩ := eventually_atTop.mp (hp.eventually (gt_mem_nhds hε))
  refine ⟨d * K, ?_⟩
  intro n hn
  simpa [Real.dist_eq] using lt_of_le_of_lt (hblock K n hn) (hK K le_rfl)

#print axioms tendsto_zero_of_subconvex_recurrence

end Erdos354Parameters
