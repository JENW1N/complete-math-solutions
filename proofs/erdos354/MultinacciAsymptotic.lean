import RecurrenceDecay
import MultinacciBase

/-!
# The six-term recurrence has a vanishing-error geometric asymptote

The quotient of the characteristic polynomial by X - base has positive,
increasing coefficients c₀,...,c₅=1. On the kernel of the corresponding
linear functional, the recurrence has coefficients 1-cᵢ whose sum is less
than one. This gives decay using only a real finite-memory estimate.
-/

open Finset Filter
open scoped Topology

namespace Erdos354Parameters

noncomputable def coefficients : Fin 6 → ℝ :=
  ![base ^ 5 - base ^ 4 - base ^ 3 - base ^ 2 - base - 1,
    base ^ 4 - base ^ 3 - base ^ 2 - base - 1,
    base ^ 3 - base ^ 2 - base - 1,
    base ^ 2 - base - 1, base - 1, 1]

lemma coefficient_zero : base * coefficients 0 = 1 := by
  have h := base_equation
  unfold baseEquation at h
  dsimp [coefficients]
  linear_combination h

lemma coefficient_last : coefficients 5 = 1 := rfl

lemma coefficients_strictMono : StrictMono coefficients := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  have hb : 0 < base := lt_trans zero_lt_one base_bounds.1
  have hp : 0 < (2 - base) * base ^ (4 - i.val) :=
    mul_pos (sub_pos.mpr base_bounds.2) (pow_pos hb _)
  have heq : coefficients i.succ - coefficients i.castSucc =
      (2 - base) * base ^ (4 - i.val) := by
    fin_cases i <;> norm_num [coefficients, Matrix.cons_val_two] <;> ring
  linarith

lemma coefficients_pos (i : Fin 6) : 0 < coefficients i := by
  have hz : 0 < coefficients 0 := by
    have hb := base_bounds.1
    have h := coefficient_zero
    nlinarith
  exact lt_of_lt_of_le hz (coefficients_strictMono.monotone (Fin.zero_le i))

lemma coefficients_le_one (i : Fin 6) : coefficients i ≤ 1 := by
  simpa only [coefficient_last] using
    coefficients_strictMono.monotone (show i ≤ (5 : Fin 6) from Fin.le_last i)

lemma coefficients_sum_identity : (base - 1) * (∑ i, coefficients i) = 5 := by
  have h := base_equation
  unfold baseEquation at h
  norm_num [coefficients, Fin.sum_univ_succ]
  linear_combination h

lemma coefficients_sum_gt_five : (5 : ℝ) < ∑ i, coefficients i := by
  have hp : 0 < ∑ i, coefficients i :=
    sum_pos (fun i _ => coefficients_pos i) univ_nonempty
  have hb := base_bounds.2
  have heq := coefficients_sum_identity
  nlinarith

noncomputable def weightedSum (u : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i : Fin 6, coefficients i * u (n + i)

lemma weightedSum_succ (u : ℕ → ℝ)
    (hu : ∀ n, u (n + 6) = ∑ i : Fin 6, u (n + i)) (n : ℕ) :
    weightedSum u (n + 1) = base * weightedSum u n := by
  have h := base_equation
  unfold baseEquation at h
  have hr := hu n
  norm_num [Fin.sum_univ_succ] at hr
  norm_num [weightedSum, coefficients, Fin.sum_univ_succ, Nat.add_assoc]
  rw [hr]
  linear_combination -(u n) * h

lemma weightedSum_eq (u : ℕ → ℝ)
    (hu : ∀ n, u (n + 6) = ∑ i : Fin 6, u (n + i)) (n : ℕ) :
    weightedSum u n = weightedSum u 0 * base ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [weightedSum_succ u hu, ih, pow_succ]; ring

lemma geometric_recurrence (n : ℕ) :
    base ^ (n + 6) = ∑ i : Fin 6, base ^ (n + i) := by
  have h := base_equation
  unfold baseEquation at h
  have hsum : base ^ 6 = ∑ i : Fin 6, base ^ (i : ℕ) := by
    norm_num [Fin.sum_univ_succ]
    linarith
  simp only [pow_add, ← mul_sum]
  rw [hsum]

lemma weightedSum_geometric (n : ℕ) :
    weightedSum (fun j => base ^ j) n =
      weightedSum (fun j => base ^ j) 0 * base ^ n :=
  weightedSum_eq _ geometric_recurrence n

lemma geometric_weight_pos : 0 < weightedSum (fun j => base ^ j) 0 := by
  apply sum_pos _ univ_nonempty
  intro i _
  exact mul_pos (coefficients_pos i)
    (pow_pos (lt_trans zero_lt_one base_bounds.1) _)

/-- Every six-term recurrence with positive initial values has a positive
geometric asymptote and an absolute error tending to zero. -/
theorem exists_geometric_asymptote (u : ℕ → ℝ)
    (hu : ∀ n, u (n + 6) = ∑ i : Fin 6, u (n + i))
    (hpos : ∀ i : Fin 6, 0 < u i) :
    ∃ A > 0, Tendsto (fun n => u n - A * base ^ n) atTop (nhds 0) := by
  let B := weightedSum (fun j => base ^ j) 0
  let A := weightedSum u 0 / B
  have hB : 0 < B := geometric_weight_pos
  have hA : 0 < A := by
    apply div_pos _ hB
    apply sum_pos _ univ_nonempty
    intro i _
    simpa using mul_pos (coefficients_pos i) (hpos i)
  refine ⟨A, hA, ?_⟩
  let e : ℕ → ℝ := fun n => u n - A * base ^ n
  have he : ∀ n, e (n + 6) = ∑ i : Fin 6, e (n + i) := by
    intro n
    dsimp [e]
    rw [hu, geometric_recurrence]
    simp only [sum_sub_distrib, mul_sum]
  have hq : ∀ n, weightedSum e n = 0 := by
    intro n
    have heq : weightedSum e n = weightedSum u n -
        A * weightedSum (fun j => base ^ j) n := by
      simp [weightedSum, e, mul_sub, sum_sub_distrib, mul_sum, mul_left_comm]
    rw [heq, weightedSum_eq u hu, weightedSum_geometric]
    change weightedSum u 0 * base ^ n - A * (B * base ^ n) = 0
    have hcancel : A * B = weightedSum u 0 := div_mul_cancel₀ _ (ne_of_gt hB)
    rw [← mul_assoc, hcancel, sub_self]
  apply tendsto_zero_of_subconvex_recurrence (by norm_num : 0 < 6) e
    (fun i => 1 - coefficients i)
  · intro i
    exact sub_nonneg.mpr (coefficients_le_one i)
  · simp only [sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_ofNat, mul_one]
    linarith [coefficients_sum_gt_five]
  · intro n
    rw [he]
    have hh := hq n
    unfold weightedSum at hh
    simp only [sub_mul, one_mul, sum_sub_distrib]
    linarith

#print axioms exists_geometric_asymptote

end Erdos354Parameters
