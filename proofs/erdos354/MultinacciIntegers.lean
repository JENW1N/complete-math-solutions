import MultinacciAsymptotic

/-!
# Integer recurrence and a uniform fractional-part witness

Start with six ones and repeatedly sum the preceding six terms. Every term
is 1 modulo 5. The geometric approximation therefore has fractional parts
approaching 1/5 after division by 5. A shift makes the estimate uniform.
-/

open Finset Filter
open scoped Topology

namespace Erdos354Parameters

noncomputable def integerRecurrence : LinearRecurrence ℤ where
  order := 6
  coeffs := fun _ => 1

noncomputable def integerSequence : ℕ → ℤ :=
  integerRecurrence.mkSol (fun _ => 1)

lemma integerSequence_recurrence (n : ℕ) :
    integerSequence (n + 6) = ∑ i : Fin 6, integerSequence (n + i) := by
  have h := integerRecurrence.is_sol_mkSol (fun _ => (1 : ℤ)) n
  change integerSequence (n + 6) = ∑ i : Fin 6, (1 : ℤ) * integerSequence (n + i) at h
  simpa only [one_mul] using h

lemma integerSequence_initial (n : ℕ) (hn : n < 6) : integerSequence n = 1 := by
  exact integerRecurrence.mkSol_eq_init (fun _ => (1 : ℤ)) ⟨n, hn⟩

lemma integerSequence_residue (n : ℕ) : ∃ k : ℤ, integerSequence n = 5 * k + 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 6
    · exact ⟨0, by rw [integerSequence_initial n hn]; norm_num⟩
    · have hdn : 6 ≤ n := by omega
      have hh : ∀ i : Fin 6, ∃ k : ℤ, integerSequence (n - 6 + i) = 5 * k + 1 := by
        intro i
        exact ih _ (by omega)
      choose k hk using hh
      refine ⟨1 + ∑ i, k i, ?_⟩
      calc
        integerSequence n = ∑ i : Fin 6, integerSequence (n - 6 + i) := by
          exact (congrArg integerSequence (by omega : n = n - 6 + 6)).trans
            (integerSequence_recurrence (n - 6))
        _ = ∑ i : Fin 6, (5 * k i + 1) := sum_congr rfl (fun i _ => hk i)
        _ = 5 * (1 + ∑ i : Fin 6, k i) + 1 := by
          simp only [sum_add_distrib, ← mul_sum]
          norm_num
          ring

lemma integerSequence_asymptote :
    ∃ A > 0, Tendsto (fun n => (integerSequence n : ℝ) - A * base ^ n)
      atTop (nhds 0) := by
  apply exists_geometric_asymptote
  · intro n
    exact_mod_cast integerSequence_recurrence n
  · intro i
    rw [integerSequence_initial i i.is_lt]
    norm_num

/-- The missing parameter-existence statement, with the stronger lower bound
3/20 on every fractional part as well as the required upper bound 1/4. -/
theorem exists_positive_fractional_part_witness :
    ∃ η > 0, ∀ j : ℕ, 1 ≤ j →
      (3 / 20 : ℝ) < Int.fract (η * base ^ j) ∧
        Int.fract (η * base ^ j) < 1 / 4 := by
  obtain ⟨A, hA, hlim⟩ := integerSequence_asymptote
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hlim (1 / 4) (by norm_num)
  let η : ℝ := (A / 5) * base ^ N
  have hb : 0 < base := lt_trans zero_lt_one base_bounds.1
  refine ⟨η, by dsimp [η]; positivity, ?_⟩
  intro j _
  obtain ⟨k, hk⟩ := integerSequence_residue (N + j)
  have herr : |(integerSequence (N + j) : ℝ) - A * base ^ (N + j)| < 1 / 4 := by
    simpa [Real.dist_eq] using hN (N + j) (by omega)
  rw [hk] at herr
  push_cast at herr
  have hη : η * base ^ j = A * base ^ (N + j) / 5 := by
    dsimp [η]
    rw [pow_add]
    ring
  have hl : (3 / 20 : ℝ) < η * base ^ j - k := by
    rw [hη]
    have hh := (abs_lt.mp herr).2
    linarith
  have hu : η * base ^ j - k < (1 / 4 : ℝ) := by
    rw [hη]
    have hh := (abs_lt.mp herr).1
    linarith
  have hfloor : ⌊η * base ^ j⌋ = k := by
    apply Int.floor_eq_iff.mpr
    constructor <;> linarith
  simpa [Int.fract, hfloor] using And.intro hl hu

#print axioms exists_positive_fractional_part_witness

end Erdos354Parameters
