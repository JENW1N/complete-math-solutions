/- Polynomial minimal graphs of degree at most four are affine.
   Submission body for Math30Catalog.source28.
   The challenge supplies its imports and the surrounding Bounty namespace. -/


/- Component: Compatibility -/
section ComponentCompatibility

/-
The extensionality proofs below are adapted from Mathlib/Algebra/MvPolynomial/Funext.lean.
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in Mathlib's LICENSE.
Authors: Johan Commelin.

The evaluation compatibility proofs are adapted from
Mathlib/Algebra/MvPolynomial/Polynomial.lean.
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in Mathlib's LICENSE.
Authors: Kim Morrison.

The homogeneous derivative and Euler proofs are adapted from
Mathlib/RingTheory/MvPolynomial/EulerIdentity.lean.
Copyright (c) 2024 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in Mathlib's LICENSE.
Authors: Junyan Xu.
-/

namespace QuarticCompatibility

open MvPolynomial

theorem polynomial_eval_eval₂ {R S σ : Type*} [CommSemiring R] [CommSemiring S]
    {x : S} (f : R →+* Polynomial S) (g : σ → Polynomial S) (p : MvPolynomial σ R) :
    Polynomial.eval x (eval₂ f g p) =
      eval₂ ((Polynomial.evalRingHom x).comp f) (fun s => Polynomial.eval x (g s)) p := by
  apply induction_on p
  · simp
  · intro p q hp hq
    simp [hp, hq]
  · intro p n hp
    simp [hp]

theorem eval_polynomial_eval_finSuccEquiv {R : Type*} {n : ℕ} {x : Fin n → R}
    [CommSemiring R] (f : MvPolynomial (Fin (n + 1)) R) (q : MvPolynomial (Fin n) R) :
    (eval x) (Polynomial.eval q (finSuccEquiv R n f)) = eval (Fin.cases (eval x q) x) f := by
  simp only [finSuccEquiv_apply, coe_eval₂Hom, polynomial_eval_eval₂, eval_eval₂]
  conv in RingHom.comp _ _ =>
    refine @RingHom.ext _ _ _ _ _ (RingHom.id _) fun r => ?_
    simp
  simp only [eval₂_id]
  congr
  funext i
  refine Fin.cases (by simp) (by simp) i

section Extensionality

variable {R : Type*} [CommRing R] [IsDomain R]

theorem polynomial_funext_fin {n : ℕ} {p : MvPolynomial (Fin n) R}
    (s : Fin n → Set R) (hs : ∀ i, (s i).Infinite)
    (h : ∀ x ∈ Set.pi .univ s, eval x p = 0) : p = 0 := by
  induction n with
  | zero =>
    have hp := h 0 finZeroElim
    rw [eq_C_of_isEmpty p, eval_C] at hp
    rw [eq_C_of_isEmpty p, hp, map_zero]
  | succ n ih =>
    apply (finSuccEquiv R n).injective
    rw [map_zero]
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply ((hs 0).image (C_injective ..).injOn).mono
    rintro _ ⟨r, hr, rfl⟩
    refine ih (s ·.succ) (fun _ ↦ hs _) fun x hx ↦ ?_
    rw [eval_polynomial_eval_finSuccEquiv]
    exact h _ fun i _ ↦ i.cases (by simpa [eval_C] using hr) (by simpa using hx)

theorem polynomial_funext_set {σ : Type*} {p q : MvPolynomial σ R}
    (s : σ → Set R) (hs : ∀ i, (s i).Infinite)
    (h : ∀ x ∈ Set.pi .univ s, eval x p = eval x q) : p = q := by
  suffices ∀ p, (∀ x ∈ Set.pi .univ s, eval x p = 0) → p = 0 by
    rw [← sub_eq_zero, this (p - q)]
    intro x hx
    simp_rw [map_sub, h x hx, sub_self]
  intro p h
  obtain ⟨n, f, hf, p, rfl⟩ := exists_fin_rename p
  suffices p = 0 by rw [this, map_zero]
  refine polynomial_funext_fin (s ∘ f) (fun _ ↦ hs _) fun x hx ↦ ?_
  choose g hg using fun i ↦ (hs i).nonempty
  convert! h (Function.extend f x g) fun i _ ↦ ?_
  · simp only [eval, eval₂Hom_rename, Function.extend_comp hf]
  obtain ⟨i, rfl⟩ | nex := em (∃ x, f x = i)
  · rw [hf.extend_apply]; exact hx _ ⟨⟩
  · simp_rw [Function.extend, dite_eq_right nex, hg]

theorem polynomial_funext [Infinite R] {σ : Type*} {p q : MvPolynomial σ R}
    (h : ∀ x : σ → R, eval x p = eval x q) : p = q :=
  polynomial_funext_set _ (fun _ ↦ Set.infinite_univ) fun _ _ ↦ h _

end Extensionality

section Homogeneity

open Finsupp

variable {R σ M : Type*} [CommSemiring R] {φ : MvPolynomial σ R}

theorem weighted_homogeneous_pderiv [AddCancelCommMonoid M] {w : σ → M}
    {n n' : M} {i : σ} (h : φ.IsWeightedHomogeneous w n) (h' : n' + w i = n) :
    (pderiv i φ).IsWeightedHomogeneous w n' := by
  rw [← mem_weightedHomogeneousSubmodule, weightedHomogeneousSubmodule_eq_finsupp_supported,
    AddMonoidAlgebra.supported_eq_span_single] at h
  refine Submodule.span_induction ?_ ?_ (fun p q _ _ hp hq ↦ ?_) (fun r p _ h ↦ ?_) h
  · rintro _ ⟨m, hm, rfl⟩
    simp_rw [single_eq_monomial, pderiv_monomial, one_mul]
    by_cases hi : m i = 0
    · rw [hi, Nat.cast_zero, monomial_zero]; apply isWeightedHomogeneous_zero
    convert! isWeightedHomogeneous_monomial ..
    rw [← add_right_cancel_iff (a := w i), h', ← hm, weight_sub_single_add hi]
  · rw [map_zero]; apply isWeightedHomogeneous_zero
  · rw [map_add]; exact hp.add hq
  · rw [(pderiv i).map_smul]; exact (weightedHomogeneousSubmodule ..).smul_mem _ h

theorem homogeneous_pderiv {n : ℕ} {i : σ} (h : φ.IsHomogeneous n) :
    (pderiv i φ).IsHomogeneous (n - 1) := by
  obtain _ | n := n
  · rw [← totalDegree_zero_iff_isHomogeneous, totalDegree_eq_zero_iff_eq_C] at h
    rw [h, pderiv_C]; apply isHomogeneous_zero
  · exact weighted_homogeneous_pderiv h rfl

variable [Fintype σ] {n : ℕ}

open Finset in
theorem weighted_sum_X_mul_pderiv {w : σ → ℕ} (h : φ.IsWeightedHomogeneous w n) :
    ∑ i : σ, w i • (X i * pderiv i φ) = n • φ := by
  rw [← mem_weightedHomogeneousSubmodule, weightedHomogeneousSubmodule_eq_finsupp_supported,
    AddMonoidAlgebra.supported_eq_span_single] at h
  refine Submodule.span_induction ?_ ?_ (fun p q _ _ hp hq ↦ ?_) (fun r p _ h ↦ ?_) h
  · rintro _ ⟨m, hm, rfl⟩
    simp_rw [single_eq_monomial, X_mul_pderiv_monomial, smul_smul, ← sum_smul, mul_comm (w _)]
    congr
    rwa [Set.mem_ofPred, weight_apply, sum_fintype] at hm
    intro; apply zero_smul
  · simp
  · simp_rw [map_add, left_distrib, smul_add, sum_add_distrib, hp, hq]
  · simp_rw [(pderiv _).map_smul, nsmul_eq_mul, mul_smul_comm, ← Finset.smul_sum,
      ← nsmul_eq_mul, h]

theorem sum_X_mul_pderiv (h : φ.IsHomogeneous n) :
    ∑ i : σ, X i * pderiv i φ = n • φ := by
  simp_rw [← weighted_sum_X_mul_pderiv h, Pi.one_apply, one_smul]

end Homogeneity

end QuarticCompatibility
end ComponentCompatibility


/- Component: MatrixAlgebra -/
section ComponentMatrixAlgebra

/-!
Algebraic invariance of the minimal-graph numerator under a matrix whose rows
are orthonormal.  The identities hold over any commutative ring, including a
multivariate polynomial ring.
-/

namespace QuarticMinimal.MatrixAlgebra

open Matrix

variable {R : Type*} [CommRing R]
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]

theorem dot_transpose_mulVec (A : Matrix m n R) (hA : A * Aᵀ = 1) (v w : m → R) :
    (Aᵀ *ᵥ v) ⬝ᵥ (Aᵀ *ᵥ w) = v ⬝ᵥ w := by
  rw [dotProduct_transpose_mulVec, mulVec_mulVec, hA, one_mulVec, dotProduct_comm]

theorem trace_conjugate (A : Matrix m n R) (hA : A * Aᵀ = 1) (H : Matrix m m R) :
    trace (Aᵀ * H * A) = trace H := by
  rw [trace_mul_cycle, hA, one_mul]

theorem conjugate_mulVec (A : Matrix m n R) (hA : A * Aᵀ = 1)
    (H : Matrix m m R) (v : m → R) :
    (Aᵀ * H * A) *ᵥ (Aᵀ *ᵥ v) = Aᵀ *ᵥ (H *ᵥ v) := by
  calc
    (Aᵀ * H * A) *ᵥ (Aᵀ *ᵥ v) = (Aᵀ * H * (A * Aᵀ)) *ᵥ v := by
      rw [mulVec_mulVec, Matrix.mul_assoc]
    _ = (Aᵀ * H) *ᵥ v := by rw [hA, Matrix.mul_one]
    _ = Aᵀ *ᵥ (H *ᵥ v) := (mulVec_mulVec v Aᵀ H).symm

theorem contraction_conjugate (A : Matrix m n R) (hA : A * Aᵀ = 1)
    (H : Matrix m m R) (v : m → R) :
    (Aᵀ *ᵥ v) ⬝ᵥ ((Aᵀ * H * A) *ᵥ (Aᵀ *ᵥ v)) = v ⬝ᵥ (H *ᵥ v) := by
  rw [conjugate_mulVec A hA, dot_transpose_mulVec A hA]

theorem minimal_expression_invariant (A : Matrix m n R) (hA : A * Aᵀ = 1)
    (H : Matrix m m R) (v : m → R) :
    (1 + (Aᵀ *ᵥ v) ⬝ᵥ (Aᵀ *ᵥ v)) * trace (Aᵀ * H * A) -
      (Aᵀ *ᵥ v) ⬝ᵥ ((Aᵀ * H * A) *ᵥ (Aᵀ *ᵥ v)) =
    (1 + v ⬝ᵥ v) * trace H - v ⬝ᵥ (H *ᵥ v) := by
  rw [dot_transpose_mulVec A hA, trace_conjugate A hA, contraction_conjugate A hA]

omit [Fintype m] in
theorem map_mul_transpose {S : Type*} [CommRing S] (f : R →+* S)
    (A : Matrix m n R) (hA : A * Aᵀ = 1) :
    A.map f * (A.map f)ᵀ = 1 := by
  have hm := congrArg (fun M : Matrix m m R => M.map f) hA
  simpa [Matrix.transpose_map] using hm

omit [Fintype m] in
theorem algebraMap_mul_transpose [Algebra ℝ R]
    (A : Matrix m n ℝ) (hA : A * Aᵀ = 1) :
    A.map (algebraMap ℝ R) * (A.map (algebraMap ℝ R))ᵀ = 1 :=
  map_mul_transpose (algebraMap ℝ R) A hA

end QuarticMinimal.MatrixAlgebra
end ComponentMatrixAlgebra


/- Component: PolynomialBasics -/
section ComponentPolynomialBasics

noncomputable section
open scoped BigOperators
open MvPolynomial

namespace QuarticPolynomialBasics

variable {σ : Type*}

lemma exponent_decompose_one (m : σ →₀ ℕ) (h : 1 ≤ m.degree) :
    ∃ (i : σ) (r : σ →₀ ℕ), r + Finsupp.single i 1 = m := by
  classical
  have hm : m ≠ 0 := by intro hm; simp [hm] at h
  obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
    by_contra hh
    push Not at hh
    exact hm (Finsupp.ext hh)
  exact ⟨i, m - Finsupp.single i 1, Finsupp.sub_add_single_one_cancel hi⟩

lemma exponent_decompose_two (m : σ →₀ ℕ) (h : 2 ≤ m.degree) :
    ∃ (i j : σ) (r : σ →₀ ℕ), r + Finsupp.single i 1 + Finsupp.single j 1 = m := by
  obtain ⟨j, s, hs⟩ := exponent_decompose_one m (by omega)
  have hsdeg : 1 ≤ s.degree := by
    have hh := congrArg Finsupp.degree hs
    simp only [map_add, Finsupp.degree_single] at hh
    omega
  obtain ⟨i, r, hr⟩ := exponent_decompose_one s hsdeg
  exact ⟨i, j, r, by rw [hr, hs]⟩

lemma coeff_second_partial (P : MvPolynomial σ ℝ) (i j : σ) (r : σ →₀ ℕ) :
    (pderiv i (pderiv j P)).coeff r =
      P.coeff (r + Finsupp.single i 1 + Finsupp.single j 1) *
        (((r + Finsupp.single i 1 : σ →₀ ℕ) j : ℝ) + 1) * (r i + 1) := by
  rw [coeff_pderiv, coeff_pderiv]

lemma second_partial_comm (P : MvPolynomial σ ℝ) (i j : σ) :
    pderiv i (pderiv j P) = pderiv j (pderiv i P) := by
  classical
  ext r
  rw [coeff_second_partial, coeff_second_partial]
  by_cases h : i = j
  · subst j; rfl
  · simp [h, Ne.symm h, add_right_comm, mul_right_comm]

lemma totalDegree_le_one_of_second_partials_zero (P : MvPolynomial σ ℝ)
    (h : ∀ i j, pderiv i (pderiv j P) = 0) : P.totalDegree ≤ 1 := by
  classical
  apply Finset.sup_le
  intro m hm
  change m.degree ≤ 1
  by_contra hh
  obtain ⟨i, j, r, hr⟩ := exponent_decompose_two m (by omega)
  have hc := congrArg (fun Q : MvPolynomial σ ℝ ↦ Q.coeff r) (h i j)
  rw [coeff_second_partial, hr, AddMonoidAlgebra.coeff_zero] at hc
  have hn : P.coeff m ≠ 0 := mem_support_iff.mp hm
  have ha : (((r + Finsupp.single i 1 : σ →₀ ℕ) j : ℕ) : ℝ) + 1 ≠ 0 := by positivity
  have hb : ((r i : ℕ) : ℝ) + 1 ≠ 0 := by positivity
  exact (mul_ne_zero (mul_ne_zero hn ha) hb) hc

lemma second_partials_zero_of_totalDegree_le_one (P : MvPolynomial σ ℝ)
    (h : P.totalDegree ≤ 1) (i j : σ) : pderiv i (pderiv j P) = 0 := by
  classical
  ext r
  rw [coeff_second_partial, AddMonoidAlgebra.coeff_zero]
  have hc : P.coeff (r + Finsupp.single i 1 + Finsupp.single j 1) = 0 := by
    apply coeff_eq_zero_of_totalDegree_lt
    change P.totalDegree < (r + Finsupp.single i 1 + Finsupp.single j 1).degree
    simp only [map_add, Finsupp.degree_single]
    omega
  simp [hc]

lemma totalDegree_le_one_iff_second_partials_zero (P : MvPolynomial σ ℝ) :
    P.totalDegree ≤ 1 ↔ ∀ i j, pderiv i (pderiv j P) = 0 :=
  ⟨second_partials_zero_of_totalDegree_le_one P,
    totalDegree_le_one_of_second_partials_zero P⟩

lemma totalDegree_pderiv_le_of_totalDegree_le (P : MvPolynomial σ ℝ)
    (i : σ) (d : ℕ) (h : P.totalDegree ≤ d + 1) :
    (pderiv i P).totalDegree ≤ d := by
  classical
  apply Finset.sup_le
  intro m hm
  change m.degree ≤ d
  have hc : P.coeff (m + Finsupp.single i 1) ≠ 0 := by
    have hh := mem_support_iff.mp hm
    rw [coeff_pderiv] at hh
    exact (mul_ne_zero_iff.mp hh).1
  have hd := le_totalDegree (mem_support_iff.mpr hc)
  change (m + Finsupp.single i 1).degree ≤ P.totalDegree at hd
  simp only [map_add, Finsupp.degree_single] at hd
  omega

lemma totalDegree_pderiv_le (P : MvPolynomial σ ℝ) (i : σ) :
    (pderiv i P).totalDegree ≤ P.totalDegree - 1 :=
  totalDegree_pderiv_le_of_totalDegree_le P i _ (by omega)

lemma pderiv_homogeneousComponent (P : MvPolynomial σ ℝ) (i : σ) (d : ℕ) :
    pderiv i (homogeneousComponent (d + 1) P) =
      homogeneousComponent d (pderiv i P) := by
  classical
  ext m
  simp only [coeff_pderiv, coeff_homogeneousComponent, map_add, Finsupp.degree_single]
  by_cases h : m.degree = d <;> simp [h]

lemma isHomogeneous_pderiv_succ (P : MvPolynomial σ ℝ) (i : σ) (d : ℕ)
    (h : P.IsHomogeneous (d + 1)) : (pderiv i P).IsHomogeneous d := by
  have hh := pderiv_homogeneousComponent P i d
  rw [homogeneousComponent_eq_self h] at hh
  rw [hh]
  exact homogeneousComponent_isHomogeneous _ _

lemma totalDegree_sub_homogeneousComponent_le (P : MvPolynomial σ ℝ)
    (d : ℕ) (h : P.totalDegree ≤ d) :
    (P - homogeneousComponent d P).totalDegree ≤ d - 1 := by
  classical
  apply Finset.sup_le
  intro m hm
  change m.degree ≤ d - 1
  have hc := mem_support_iff.mp hm
  simp only [coeff_sub, coeff_homogeneousComponent] at hc
  split_ifs at hc with hd
  · exact False.elim (hc (sub_self _))
  · simp only [sub_zero] at hc
    have hh := le_totalDegree (mem_support_iff.mpr hc)
    change m.degree ≤ P.totalDegree at hh
    omega

lemma top_homogeneousComponent_ne_zero (P : MvPolynomial σ ℝ)
    (h : 0 < P.totalDegree) : homogeneousComponent P.totalDegree P ≠ 0 := by
  intro hh
  have hdeg := totalDegree_sub_homogeneousComponent_le P P.totalDegree le_rfl
  rw [hh, sub_zero] at hdeg
  omega

lemma totalDegree_sub_top_homogeneousComponent_lt (P : MvPolynomial σ ℝ)
    (h : 0 < P.totalDegree) :
    (P - homogeneousComponent P.totalDegree P).totalDegree < P.totalDegree := by
  have hdeg := totalDegree_sub_homogeneousComponent_le P P.totalDegree le_rfl
  omega

lemma homogeneousComponent_mul_top (P Q : MvPolynomial σ ℝ) (d e : ℕ)
    (hP : P.totalDegree ≤ d) (hQ : Q.totalDegree ≤ e) :
    homogeneousComponent (d + e) (P * Q) =
      homogeneousComponent d P * homogeneousComponent e Q := by
  by_cases hd : d = 0
  · subst d
    have hp0 : P.totalDegree = 0 := Nat.eq_zero_of_le_zero hP
    rw [(totalDegree_eq_zero_iff_eq_C.mp hp0)]
    simp [homogeneousComponent_C_mul, homogeneousComponent_zero]
  by_cases he : e = 0
  · subst e
    have hq0 : Q.totalDegree = 0 := Nat.eq_zero_of_le_zero hQ
    rw [(totalDegree_eq_zero_iff_eq_C.mp hq0)]
    rw [mul_comm P (C (Q.coeff 0)), homogeneousComponent_C_mul]
    simp [homogeneousComponent_zero, mul_comm]
  have hdp := totalDegree_sub_homogeneousComponent_le P d hP
  have hdq := totalDegree_sub_homogeneousComponent_le Q e hQ
  have htp : (homogeneousComponent d P).totalDegree ≤ d :=
    (homogeneousComponent_isHomogeneous d P).totalDegree_le
  have hz1 : homogeneousComponent (d + e) ((P - homogeneousComponent d P) * Q) = 0 := by
    apply homogeneousComponent_eq_zero
    have hh := totalDegree_mul (P - homogeneousComponent d P) Q
    omega
  have hz2 : homogeneousComponent (d + e)
      (homogeneousComponent d P * (Q - homogeneousComponent e Q)) = 0 := by
    apply homogeneousComponent_eq_zero
    have hh := totalDegree_mul (homogeneousComponent d P) (Q - homogeneousComponent e Q)
    omega
  have heq : P * Q = homogeneousComponent d P * homogeneousComponent e Q +
      ((P - homogeneousComponent d P) * Q +
        homogeneousComponent d P * (Q - homogeneousComponent e Q)) := by ring
  rw [heq, map_add, map_add, hz1, hz2, add_zero, add_zero]
  exact homogeneousComponent_eq_self
    ((homogeneousComponent_isHomogeneous d P).mul (homogeneousComponent_isHomogeneous e Q))

/-- The polynomial numerator of the scalar minimal graph equation. This is
definitionally equal to the corresponding operator in the challenge. -/
def minimalGraphOperator {n : ℕ} (P : MvPolynomial (Fin n) ℝ) :
    MvPolynomial (Fin n) ℝ :=
  (1 + ∑ i : Fin n, (pderiv i P) ^ 2) *
      (∑ i : Fin n, pderiv i (pderiv i P)) -
    ∑ i : Fin n, ∑ j : Fin n,
      pderiv i P * pderiv j P * pderiv i (pderiv j P)

lemma minimalGraphOperator_zero_variables (P : MvPolynomial (Fin 0) ℝ) :
    minimalGraphOperator P = 0 := by
  simp [minimalGraphOperator]

lemma totalDegree_zero_variables (P : MvPolynomial (Fin 0) ℝ) :
    P.totalDegree = 0 := by
  rw [MvPolynomial.eq_C_of_isEmpty P, totalDegree_C]

lemma minimalGraphOperator_one_variable (P : MvPolynomial (Fin 1) ℝ) :
    minimalGraphOperator P = pderiv 0 (pderiv 0 P) := by
  simp only [minimalGraphOperator, Fin.sum_univ_one]
  ring

lemma affine_of_minimalGraphOperator_eq_zero_one_variable
    (P : MvPolynomial (Fin 1) ℝ) (h : minimalGraphOperator P = 0) :
    P.totalDegree ≤ 1 := by
  apply totalDegree_le_one_of_second_partials_zero
  intro i j
  have hi : i = 0 := Subsingleton.elim _ _
  have hj : j = 0 := Subsingleton.elim _ _
  subst i; subst j
  rwa [minimalGraphOperator_one_variable] at h

lemma minimalGraphOperator_eq_zero_of_totalDegree_le_one
    {n : ℕ} (P : MvPolynomial (Fin n) ℝ) (h : P.totalDegree ≤ 1) :
    minimalGraphOperator P = 0 := by
  simp [minimalGraphOperator, second_partials_zero_of_totalDegree_le_one P h]

def polynomialLaplacian {n : ℕ} (P : MvPolynomial (Fin n) ℝ) :
    MvPolynomial (Fin n) ℝ := ∑ i : Fin n, pderiv i (pderiv i P)

def cubicOperator {n : ℕ} (P : MvPolynomial (Fin n) ℝ) :
    MvPolynomial (Fin n) ℝ :=
  (∑ i : Fin n, (pderiv i P) ^ 2) * polynomialLaplacian P -
    ∑ i : Fin n, ∑ j : Fin n,
      pderiv i P * pderiv j P * pderiv i (pderiv j P)

lemma minimalGraphOperator_eq_laplacian_add_cubic {n : ℕ}
    (P : MvPolynomial (Fin n) ℝ) :
    minimalGraphOperator P = polynomialLaplacian P + cubicOperator P := by
  unfold minimalGraphOperator cubicOperator polynomialLaplacian
  ring

lemma totalDegree_second_partial_le (P : MvPolynomial σ ℝ) (d : ℕ)
    (h : P.totalDegree ≤ d + 2) (i j : σ) :
    (pderiv i (pderiv j P)).totalDegree ≤ d := by
  apply totalDegree_pderiv_le_of_totalDegree_le
  exact totalDegree_pderiv_le_of_totalDegree_le P j (d + 1) (by omega)

lemma homogeneousComponent_second_partial (P : MvPolynomial σ ℝ) (d : ℕ)
    (i j : σ) : homogeneousComponent d (pderiv i (pderiv j P)) =
      pderiv i (pderiv j (homogeneousComponent (d + 2) P)) := by
  rw [← pderiv_homogeneousComponent, ← pderiv_homogeneousComponent]

lemma homogeneousComponent_derivative_triple (P : MvPolynomial σ ℝ) (d : ℕ)
    (h : P.totalDegree ≤ d + 2) (i j k l : σ) :
    homogeneousComponent (3 * d + 2)
      (pderiv i P * pderiv j P * pderiv k (pderiv l P)) =
      pderiv i (homogeneousComponent (d + 2) P) *
        pderiv j (homogeneousComponent (d + 2) P) *
        pderiv k (pderiv l (homogeneousComponent (d + 2) P)) := by
  have hgi : (pderiv i P).totalDegree ≤ d + 1 :=
    totalDegree_pderiv_le_of_totalDegree_le P i (d + 1) (by omega)
  have hgj : (pderiv j P).totalDegree ≤ d + 1 :=
    totalDegree_pderiv_le_of_totalDegree_le P j (d + 1) (by omega)
  have hpair : (pderiv i P * pderiv j P).totalDegree ≤ (d + 1) + (d + 1) :=
    (totalDegree_mul _ _).trans (Nat.add_le_add hgi hgj)
  have hkl := totalDegree_second_partial_le P d h k l
  rw [show 3 * d + 2 = ((d + 1) + (d + 1)) + d by omega,
    homogeneousComponent_mul_top _ _ _ _ hpair hkl,
    homogeneousComponent_mul_top _ _ _ _ hgi hgj,
    ← pderiv_homogeneousComponent, ← pderiv_homogeneousComponent,
    homogeneousComponent_second_partial]

lemma homogeneousComponent_cubicOperator_top {n : ℕ}
    (P : MvPolynomial (Fin n) ℝ) (d : ℕ) (h : P.totalDegree ≤ d + 2) :
    homogeneousComponent (3 * d + 2) (cubicOperator P) =
      cubicOperator (homogeneousComponent (d + 2) P) := by
  unfold cubicOperator polynomialLaplacian
  simp only [Finset.sum_mul, Finset.mul_sum, map_sub, map_sum, pow_two]
  simp_rw [homogeneousComponent_derivative_triple P d h]

lemma homogeneousComponent_minimalGraphOperator_top {n : ℕ}
    (P : MvPolynomial (Fin n) ℝ) (d : ℕ) (h : P.totalDegree ≤ d + 2) :
    homogeneousComponent (3 * d + 2) (minimalGraphOperator P) =
      cubicOperator (homogeneousComponent (d + 2) P) := by
  rw [minimalGraphOperator_eq_laplacian_add_cubic, map_add,
    homogeneousComponent_cubicOperator_top P d h]
  have hlap : (polynomialLaplacian P).totalDegree ≤ d := by
    apply totalDegree_finsetSum_le
    intro i hi
    exact totalDegree_second_partial_le P d h i i
  have hz : homogeneousComponent (3 * d + 2) (polynomialLaplacian P) = 0 := by
    apply homogeneousComponent_eq_zero
    omega
  rw [hz, zero_add]

lemma cubicOperator_top_eq_zero {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (m : ℕ) (hm : 2 ≤ m) (hdeg : P.totalDegree ≤ m)
    (h : minimalGraphOperator P = 0) :
    cubicOperator (homogeneousComponent m P) = 0 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  have ht := homogeneousComponent_minimalGraphOperator_top P d (by omega)
  rw [h, map_zero] at ht
  simpa [Nat.add_comm] using ht.symm

lemma eq_zero_of_weighted_sum_sq_eq_zero {ι : Type*} (s : Finset ι)
    (w : ι → ℝ) (P : ι → MvPolynomial σ ℝ)
    (hw : ∀ i ∈ s, 0 < w i)
    (h : ∑ i ∈ s, C (w i) * (P i) ^ 2 = 0) :
    ∀ i ∈ s, P i = 0 := by
  intro i hi
  apply QuarticCompatibility.polynomial_funext
  intro x
  have he := congrArg (eval x) h
  simp only [map_sum, map_mul, eval_C, map_pow, map_zero] at he
  have hn : ∀ j ∈ s, 0 ≤ w j * eval x (P j) ^ 2 := by
    intro j hj
    exact mul_nonneg (le_of_lt (hw j hj)) (sq_nonneg _)
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hn).mp he i hi
  have hiw : w i ≠ 0 := ne_of_gt (hw i hi)
  have hp : eval x (P i) ^ 2 = 0 := (mul_eq_zero.mp hz).resolve_left hiw
  simpa only [map_zero] using (sq_eq_zero_iff.mp hp)

lemma eq_zero_of_sum_sq_eq_zero {ι : Type*} (s : Finset ι)
    (P : ι → MvPolynomial σ ℝ) (h : ∑ i ∈ s, (P i) ^ 2 = 0) :
    ∀ i ∈ s, P i = 0 := by
  apply eq_zero_of_weighted_sum_sq_eq_zero s (fun _ ↦ 1) P
  · intros; norm_num
  · simpa using h

lemma eq_zero_of_scalar_weighted_sum_sq_eq_zero {ι : Type*} (s : Finset ι)
    (a : ℝ) (ha : a ≠ 0) (P : ι → MvPolynomial σ ℝ)
    (h : C a * (∑ i ∈ s, (P i) ^ 2) = 0) :
    ∀ i ∈ s, P i = 0 := by
  apply eq_zero_of_sum_sq_eq_zero s P
  exact (mul_eq_zero.mp h).resolve_left (by simpa using ha)

section Analysis

variable [Fintype σ]

def evalFDeriv (P : MvPolynomial σ ℝ) (x : σ → ℝ) : (σ → ℝ) →L[ℝ] ℝ :=
  ∑ i, eval x (pderiv i P) • ContinuousLinearMap.proj i

lemma evalFDeriv_apply (P : MvPolynomial σ ℝ) (x v : σ → ℝ) :
    evalFDeriv P x v = ∑ i, eval x (pderiv i P) * v i := by
  simp [evalFDeriv]

lemma evalFDeriv_C (a : ℝ) (x : σ → ℝ) : evalFDeriv (C a) x = 0 := by
  simp [evalFDeriv]

lemma evalFDeriv_X (i : σ) (x : σ → ℝ) :
    evalFDeriv (X i) x = ContinuousLinearMap.proj i := by
  classical
  simp [evalFDeriv, pderiv_X, Pi.single_apply]

lemma evalFDeriv_add (P Q : MvPolynomial σ ℝ) (x : σ → ℝ) :
    evalFDeriv (P + Q) x = evalFDeriv P x + evalFDeriv Q x := by
  simp [evalFDeriv, add_smul, Finset.sum_add_distrib]

lemma evalFDeriv_mul (P Q : MvPolynomial σ ℝ) (x : σ → ℝ) :
    evalFDeriv (P * Q) x = eval x P • evalFDeriv Q x + eval x Q • evalFDeriv P x := by
  ext v
  simp only [evalFDeriv_apply, add_apply,
    smul_apply, smul_eq_mul, pderiv_mul, map_add, map_mul,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma hasFDerivAt_eval (P : MvPolynomial σ ℝ) (x : σ → ℝ) :
    HasFDerivAt (fun y : σ → ℝ ↦ eval y P) (evalFDeriv P x) x := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa [evalFDeriv_C] using (hasFDerivAt_const (𝕜 := ℝ) a x)
  | add P Q hp hq => simpa [evalFDeriv_add] using hp.fun_add hq
  | mul_X P i hp =>
    simpa [evalFDeriv_mul, evalFDeriv_X] using hp.fun_mul (hasFDerivAt_apply i x)

lemma hasStrictFDerivAt_eval (P : MvPolynomial σ ℝ) (x : σ → ℝ) :
    HasStrictFDerivAt (fun y : σ → ℝ ↦ eval y P) (evalFDeriv P x) x := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa [evalFDeriv_C] using (hasStrictFDerivAt_const (𝕜 := ℝ) a x)
  | add P Q hp hq => simpa [evalFDeriv_add] using hp.fun_add hq
  | mul_X P i hp =>
    simpa [evalFDeriv_mul, evalFDeriv_X] using hp.fun_mul (hasStrictFDerivAt_apply i x)

lemma evalFDeriv_self_of_isHomogeneous (P : MvPolynomial σ ℝ) (d : ℕ)
    (h : P.IsHomogeneous d) (x : σ → ℝ) : evalFDeriv P x x = d * eval x P := by
  have hh := congrArg (eval x) (QuarticCompatibility.sum_X_mul_pderiv h)
  simpa [evalFDeriv_apply, mul_comm] using hh

def spherePolynomial : MvPolynomial σ ℝ := ∑ i : σ, (X i) ^ 2

lemma eval_spherePolynomial (x : σ → ℝ) :
    eval x spherePolynomial = ∑ i : σ, (x i) ^ 2 := by
  simp [spherePolynomial]

lemma pderiv_spherePolynomial (i : σ) :
    pderiv i (spherePolynomial : MvPolynomial σ ℝ) = 2 * X i := by
  classical
  simp [spherePolynomial, pderiv_X, Pi.single_apply]

lemma evalFDeriv_spherePolynomial (x v : σ → ℝ) :
    evalFDeriv spherePolynomial x v = 2 * ∑ i : σ, x i * v i := by
  simp [evalFDeriv_apply, pderiv_spherePolynomial, Finset.mul_sum, mul_assoc]

lemma evalFDeriv_basis [DecidableEq σ] (P : MvPolynomial σ ℝ) (x : σ → ℝ) (i : σ) :
    evalFDeriv P x (Pi.single i 1) = eval x (pderiv i P) := by
  classical
  simp [evalFDeriv_apply, Pi.single_apply]

lemma exists_gradient_multiplier_of_local_extremum_on_sphere
    (P : MvPolynomial σ ℝ) (x : σ → ℝ) (hx : ∑ i, (x i) ^ 2 = 1)
    (he : IsLocalExtrOn (fun y : σ → ℝ ↦ eval y P) {y | ∑ i, (y i) ^ 2 = 1} x) :
    ∃ c : ℝ, ∀ i, eval x (pderiv i P) = c * x i := by
  classical
  have he' : IsLocalExtrOn (fun y : σ → ℝ ↦ eval y P)
      {y | eval y spherePolynomial = eval x spherePolynomial} x := by
    simpa only [eval_spherePolynomial, hx] using he
  obtain ⟨a, b, hab, hd⟩ := he'.exists_multipliers_of_hasStrictFDerivAt_1d
    (hasStrictFDerivAt_eval spherePolynomial x) (hasStrictFDerivAt_eval P x)
  have hdx := congrArg (fun f : (σ → ℝ) →L[ℝ] ℝ ↦ f x) hd
  simp only [add_apply, smul_apply, smul_eq_mul, zero_apply,
    evalFDeriv_spherePolynomial, ← pow_two, hx] at hdx
  have hb : b ≠ 0 := by
    intro hb
    have ha : a = 0 := by simp [hb] at hdx; linarith
    exact hab (by simp [ha, hb])
  refine ⟨-2 * a / b, fun i ↦ ?_⟩
  have hdi := congrArg (fun f : (σ → ℝ) →L[ℝ] ℝ ↦ f (Pi.single i 1)) hd
  simp only [add_apply, smul_apply, smul_eq_mul, zero_apply,
    evalFDeriv_basis, pderiv_spherePolynomial, map_mul, map_ofNat, eval_X] at hdi
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hb).2
  nlinarith

lemma gradient_at_homogeneous_sphere_extremum
    (P : MvPolynomial σ ℝ) (d : ℕ) (hP : P.IsHomogeneous d)
    (x : σ → ℝ) (hx : ∑ i, (x i) ^ 2 = 1)
    (he : IsLocalExtrOn (fun y : σ → ℝ ↦ eval y P) {y | ∑ i, (y i) ^ 2 = 1} x) :
    ∀ i, eval x (pderiv i P) = (d * eval x P) * x i := by
  obtain ⟨c, hc⟩ := exists_gradient_multiplier_of_local_extremum_on_sphere P x hx he
  have hh := evalFDeriv_self_of_isHomogeneous P d hP x
  rw [evalFDeriv_apply] at hh
  simp_rw [hc, mul_assoc, ← pow_two] at hh
  rw [← Finset.mul_sum, hx, mul_one] at hh
  simpa only [hh] using hc

lemma fderiv_eval (P : MvPolynomial σ ℝ) (x : σ → ℝ) :
    fderiv ℝ (fun y : σ → ℝ ↦ eval y P) x = evalFDeriv P x :=
  (hasFDerivAt_eval P x).fderiv

lemma differentiable_eval (P : MvPolynomial σ ℝ) :
    Differentiable ℝ (fun x : σ → ℝ ↦ eval x P) :=
  fun x ↦ (hasFDerivAt_eval P x).differentiableAt

end Analysis

end QuarticPolynomialBasics
end

end ComponentPolynomialBasics


/- Component: LowDegree -/
section ComponentLowDegree

/- Requires PolynomialBasics.lean. -/
noncomputable section
open scoped BigOperators Matrix
open MvPolynomial

namespace QuarticMinimal

variable {ι : Type*}

theorem eq_C_of_pderiv_eq_zero (P : MvPolynomial ι ℝ)
    (hP : ∀ i, pderiv i P = 0) : P = C (P.coeff 0) := by
  classical
  apply totalDegree_eq_zero_iff_eq_C.mp
  apply Nat.eq_zero_of_le_zero
  apply Finset.sup_le
  intro m hm
  change m.degree ≤ 0
  by_contra hn
  obtain ⟨i, r, hr⟩ := QuarticPolynomialBasics.exponent_decompose_one m (by omega)
  have hc := congrArg (fun Q : MvPolynomial ι ℝ => Q.coeff r) (hP i)
  rw [coeff_pderiv, hr, AddMonoidAlgebra.coeff_zero] at hc
  have hcoeff : P.coeff m ≠ 0 := mem_support_iff.mp hm
  have hnat : (r i : ℝ) + 1 ≠ 0 := by positivity
  exact (mul_ne_zero hcoeff hnat) hc

theorem pderiv_eq_C_of_totalDegree_le_one (P : MvPolynomial ι ℝ)
    (hP : P.totalDegree ≤ 1) (i : ι) :
    pderiv i P = C ((pderiv i P).coeff 0) := by
  apply eq_C_of_pderiv_eq_zero
  intro j
  exact QuarticPolynomialBasics.second_partials_zero_of_totalDegree_le_one P hP j i

variable [Fintype ι]

theorem affine_expansion (P : MvPolynomial ι ℝ) (hP : P.totalDegree ≤ 1) :
    P = C (P.coeff 0) + ∑ i, C ((pderiv i P).coeff 0) * X i := by
  classical
  let L : MvPolynomial ι ℝ := ∑ i, C ((pderiv i P).coeff 0) * X i
  have hL (j : ι) : pderiv j L = C ((pderiv j P).coeff 0) := by
    simp [L, pderiv_X, Pi.single_apply]
  have hQ : P - L = C ((P - L).coeff 0) := by
    apply eq_C_of_pderiv_eq_zero
    intro j
    rw [map_sub, hL]
    exact sub_eq_zero.mpr (pderiv_eq_C_of_totalDegree_le_one P hP j)
  have hLc : L.coeff 0 = 0 := by
    simp [L, coeff_C_mul]
  rw [coeff_sub, hLc, sub_zero] at hQ
  exact sub_eq_iff_eq_add.mp hQ

theorem eval_affine_expansion (P : MvPolynomial ι ℝ) (hP : P.totalDegree ≤ 1)
    (x : ι → ℝ) :
    eval x P = P.coeff 0 + ∑ i, (pderiv i P).coeff 0 * x i := by
  conv_lhs => rw [affine_expansion P hP]
  simp

def hessianCoeff (P : MvPolynomial ι ℝ) : Matrix ι ι ℝ :=
  fun i j => (pderiv i (pderiv j P)).coeff 0

omit [Fintype ι] in
theorem hessianCoeff_symmetric (P : MvPolynomial ι ℝ) :
    (hessianCoeff P).IsSymm := by
  ext i j
  simp only [hessianCoeff, Matrix.transpose_apply]
  rw [QuarticPolynomialBasics.second_partial_comm]

omit [Fintype ι] in
theorem second_partial_eq_C_of_totalDegree_le_two (P : MvPolynomial ι ℝ)
    (hP : P.totalDegree ≤ 2) (i j : ι) :
    pderiv i (pderiv j P) = C (hessianCoeff P i j) := by
  exact pderiv_eq_C_of_totalDegree_le_one (pderiv j P)
    (QuarticPolynomialBasics.totalDegree_pderiv_le_of_totalDegree_le P j 1 hP) i

theorem eval_quadratic_gradient (P : MvPolynomial ι ℝ) (hP : P.totalDegree ≤ 2)
    (x : ι → ℝ) (j : ι) :
    eval x (pderiv j P) = (hessianCoeff P *ᵥ x) j + (pderiv j P).coeff 0 := by
  rw [eval_affine_expansion (pderiv j P)
    (QuarticPolynomialBasics.totalDegree_pderiv_le_of_totalDegree_le P j 1 hP)]
  rw [add_comm]
  simp only [Matrix.mulVec, dotProduct, hessianCoeff]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [QuarticPolynomialBasics.second_partial_comm]

theorem homogeneous_linear_expansion (P : MvPolynomial ι ℝ)
    (hP : P.IsHomogeneous 1) :
    P = ∑ i, C ((pderiv i P).coeff 0) * X i := by
  have hc : P.coeff 0 = 0 := hP.coeff_eq_zero (by simp)
  simpa only [hc, map_zero, zero_add] using affine_expansion P hP.totalDegree_le

theorem homogeneous_quadratic_expansion (P : MvPolynomial ι ℝ)
    (hP : P.IsHomogeneous 2) :
    P = C (1 / 2 : ℝ) * ∑ i, ∑ j, C (hessianCoeff P i j) * X i * X j := by
  have he := QuarticCompatibility.sum_X_mul_pderiv hP
  have hp (i : ι) : pderiv i P = ∑ j, C (hessianCoeff P j i) * X j := by
    exact homogeneous_linear_expansion (pderiv i P)
      (by simpa using QuarticCompatibility.homogeneous_pderiv (i := i) hP)
  simp_rw [hp, Finset.mul_sum] at he
  norm_num [nsmul_eq_mul] at he
  have he' : (∑ i, ∑ j, C (hessianCoeff P i j) * X i * X j) = 2 * P := by
    rw [← he]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    have hs : hessianCoeff P i j = hessianCoeff P j i := by
      simp only [hessianCoeff]
      rw [QuarticPolynomialBasics.second_partial_comm]
    rw [hs]
    ring
  rw [he']
  have hc : C (1 / 2 : ℝ) * (2 : MvPolynomial ι ℝ) = 1 := by
    calc
      C (1 / 2 : ℝ) * 2 = C (1 / 2 : ℝ) * C (2 : ℝ) := by rw [map_ofNat]
      _ = C ((1 / 2 : ℝ) * 2) := (map_mul C _ _).symm
      _ = 1 := by norm_num
  rw [← mul_assoc, hc, one_mul]

end QuarticMinimal
end

end ComponentLowDegree


/- Component: ChangeVariables -/
section ComponentChangeVariables

noncomputable section

open scoped BigOperators Matrix
open MvPolynomial

namespace QuarticMinimal

variable {ι κ : Type*} [Fintype ι]

theorem pderiv_aeval_chain (f : ι → MvPolynomial κ ℝ)
    (P : MvPolynomial ι ℝ) (j : κ) :
    pderiv j (aeval f P) =
      ∑ i, aeval f (pderiv i P) * pderiv j (f i) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C r => simp
  | add P Q hP hQ =>
    simp only [map_add, hP, hQ, add_mul, Finset.sum_add_distrib]
  | mul_X P k hP =>
    have hterm (i : ι) :
        aeval f (pderiv i (P * X k)) * pderiv j (f i) =
          (aeval f (pderiv i P) * pderiv j (f i)) * f k +
            if i = k then aeval f P * pderiv j (f k) else 0 := by
      by_cases hi : i = k
      · subst i
        simp only [pderiv_mul, pderiv_X_self, map_add, map_mul, aeval_X,
          mul_one, ite_true]
        ring
      · simp only [pderiv_mul, pderiv_X_of_ne (Ne.symm hi), mul_zero, add_zero,
          map_mul, aeval_X, hi, ite_false]
        ring
    calc
      pderiv j (aeval f (P * X k)) =
          (∑ i, aeval f (pderiv i P) * pderiv j (f i)) * f k +
            aeval f P * pderiv j (f k) := by
        rw [map_mul, aeval_X, pderiv_mul, hP]
      _ = ∑ i, aeval f (pderiv i (P * X k)) * pderiv j (f i) := by
        symm
        simp_rw [hterm]
        simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
          ite_true, Finset.sum_mul]

variable [Fintype κ]

def linearSubstitution (A : Matrix ι κ ℝ) (i : ι) : MvPolynomial κ ℝ :=
  ∑ j, C (A i j) * X j

omit [Fintype ι] in
theorem pderiv_linearSubstitution (A : Matrix ι κ ℝ) (i : ι) (j : κ) :
    pderiv j (linearSubstitution A i) = C (A i j) := by
  classical
  simp [linearSubstitution, pderiv_X, Pi.single_apply]

def changeVariables (A : Matrix ι κ ℝ) :
    MvPolynomial ι ℝ →ₐ[ℝ] MvPolynomial κ ℝ :=
  aeval (linearSubstitution A)

theorem pderiv_changeVariables (A : Matrix ι κ ℝ)
    (P : MvPolynomial ι ℝ) (j : κ) :
    pderiv j (changeVariables A P) =
      ∑ i, changeVariables A (pderiv i P) * C (A i j) := by
  simp only [changeVariables, pderiv_aeval_chain, pderiv_linearSubstitution]

theorem pderiv_pderiv_changeVariables (A : Matrix ι κ ℝ)
    (P : MvPolynomial ι ℝ) (j k : κ) :
    pderiv j (pderiv k (changeVariables A P)) =
      ∑ i, ∑ l, changeVariables A (pderiv l (pderiv i P)) *
        C (A l j) * C (A i k) := by
  simp only [pderiv_changeVariables, map_sum, pderiv_mul, pderiv_C,
    mul_zero, add_zero, Finset.sum_mul]

def gradient (P : MvPolynomial ι ℝ) (i : ι) : MvPolynomial ι ℝ := pderiv i P

def hessian (P : MvPolynomial ι ℝ) : Matrix ι ι (MvPolynomial ι ℝ) :=
  fun i j => pderiv i (pderiv j P)

theorem gradient_changeVariables (A : Matrix ι κ ℝ) (P : MvPolynomial ι ℝ) :
    gradient (changeVariables A P) =
      (A.map (C : ℝ →+* MvPolynomial κ ℝ)).transpose *ᵥ
        (fun i => changeVariables A (gradient P i)) := by
  funext j
  simp only [gradient, pderiv_changeVariables, Matrix.mulVec, dotProduct,
    Matrix.transpose_apply, Matrix.map_apply]
  apply Finset.sum_congr rfl
  intro i hi
  exact mul_comm _ _

theorem hessian_changeVariables (A : Matrix ι κ ℝ) (P : MvPolynomial ι ℝ) :
    hessian (changeVariables A P) =
      (A.map (C : ℝ →+* MvPolynomial κ ℝ)).transpose *
        ((hessian P).map (changeVariables A)) *
          (A.map (C : ℝ →+* MvPolynomial κ ℝ)) := by
  funext j k
  simp only [hessian, pderiv_pderiv_changeVariables, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro l hl
  ring

def minimalOperator (P : MvPolynomial ι ℝ) : MvPolynomial ι ℝ :=
  (1 + ∑ i, (pderiv i P) ^ 2) * (∑ i, pderiv i (pderiv i P)) -
    ∑ i, ∑ j, pderiv i P * pderiv j P * pderiv i (pderiv j P)

theorem minimalOperator_eq_matrix (P : MvPolynomial ι ℝ) :
    minimalOperator P =
      (1 + dotProduct (gradient P) (gradient P)) * Matrix.trace (hessian P) -
        dotProduct (gradient P) ((hessian P) *ᵥ (gradient P)) := by
  have hc : dotProduct (gradient P) ((hessian P) *ᵥ (gradient P)) =
      ∑ i, ∑ j, pderiv i P * pderiv j P * pderiv i (pderiv j P) := by
    simp only [dotProduct, Matrix.mulVec, gradient, hessian, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hc]
  simp only [minimalOperator, dotProduct, Matrix.trace, Matrix.diag,
    gradient, hessian, pow_two]

end QuarticMinimal
end

end ComponentChangeVariables


/- Component: OperatorInvariance -/
section ComponentOperatorInvariance

/- This development component follows MatrixAlgebra and ChangeVariables in the single-file build. -/

noncomputable section
open MvPolynomial
open scoped BigOperators Matrix

namespace QuarticMinimal

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]

theorem minimalOperator_changeVariables (A : Matrix ι κ ℝ)
    (hA : A * A.transpose = 1) (P : MvPolynomial ι ℝ) :
    minimalOperator (changeVariables A P) = changeVariables A (minimalOperator P) := by
  have hAc := MatrixAlgebra.map_mul_transpose (C : ℝ →+* MvPolynomial κ ℝ) A hA
  rw [minimalOperator_eq_matrix, gradient_changeVariables, hessian_changeVariables,
    MatrixAlgebra.minimal_expression_invariant _ hAc]
  rw [minimalOperator_eq_matrix]
  simp only [dotProduct, Matrix.trace, Matrix.diag, Matrix.map_apply, Matrix.mulVec,
    map_sub, map_mul, map_add, map_one, map_sum]

theorem minimalOperator_changeVariables_eq_zero (A : Matrix ι κ ℝ)
    (hA : A * A.transpose = 1) (P : MvPolynomial ι ℝ)
    (hP : minimalOperator P = 0) :
    minimalOperator (changeVariables A P) = 0 := by
  rw [minimalOperator_changeVariables A hA, hP, map_zero]

def laplacian (P : MvPolynomial ι ℝ) : MvPolynomial ι ℝ :=
  ∑ i, pderiv i (pderiv i P)

def leadingOperator (P : MvPolynomial ι ℝ) : MvPolynomial ι ℝ :=
  (∑ i, (pderiv i P) ^ 2) * laplacian P -
    ∑ i, ∑ j, pderiv i P * pderiv j P * pderiv i (pderiv j P)

omit [DecidableEq ι] in
theorem minimalOperator_eq_laplacian_add_leading (P : MvPolynomial ι ℝ) :
    minimalOperator P = laplacian P + leadingOperator P := by
  simp only [minimalOperator, leadingOperator, laplacian]
  ring

omit [DecidableEq ι] in
theorem laplacian_eq_trace_hessian (P : MvPolynomial ι ℝ) :
    laplacian P = Matrix.trace (hessian P) := rfl

theorem laplacian_changeVariables (A : Matrix ι κ ℝ)
    (hA : A * A.transpose = 1) (P : MvPolynomial ι ℝ) :
    laplacian (changeVariables A P) = changeVariables A (laplacian P) := by
  have hAc := MatrixAlgebra.map_mul_transpose (C : ℝ →+* MvPolynomial κ ℝ) A hA
  rw [laplacian_eq_trace_hessian, hessian_changeVariables,
    MatrixAlgebra.trace_conjugate _ hAc]
  simp only [Matrix.trace, Matrix.diag, Matrix.map_apply, laplacian, hessian, map_sum]

theorem leadingOperator_changeVariables (A : Matrix ι κ ℝ)
    (hA : A * A.transpose = 1) (P : MvPolynomial ι ℝ) :
    leadingOperator (changeVariables A P) = changeVariables A (leadingOperator P) := by
  have hm := minimalOperator_changeVariables A hA P
  rw [minimalOperator_eq_laplacian_add_leading,
    minimalOperator_eq_laplacian_add_leading, map_add, laplacian_changeVariables A hA] at hm
  exact add_left_cancel hm

theorem leadingOperator_changeVariables_eq_zero (A : Matrix ι κ ℝ)
    (hA : A * A.transpose = 1) (P : MvPolynomial ι ℝ)
    (hP : leadingOperator P = 0) :
    leadingOperator (changeVariables A P) = 0 := by
  rw [leadingOperator_changeVariables A hA, hP, map_zero]

end QuarticMinimal
end

end ComponentOperatorInvariance


/- Component: LinearSubstitution -/
section ComponentLinearSubstitution

/- Requires ChangeVariables.lean in the single-file assembly. -/
noncomputable section
open scoped BigOperators Matrix
open MvPolynomial

namespace QuarticMinimal

variable {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]

omit [Fintype ι] in
theorem eval_linearSubstitution (A : Matrix ι κ ℝ) (x : κ → ℝ) (i : ι) :
    eval x (linearSubstitution A i) = (A *ᵥ x) i := by
  simp [linearSubstitution, Matrix.mulVec, dotProduct]

omit [Fintype ι] in
theorem eval_changeVariables (A : Matrix ι κ ℝ) (x : κ → ℝ)
    (P : MvPolynomial ι ℝ) :
    eval x (changeVariables A P) = eval (A *ᵥ x) P := by
  change aeval x (aeval (linearSubstitution A) P) = aeval (A *ᵥ x) P
  rw [comp_aeval_apply]
  have hf : (fun i => aeval x (linearSubstitution A i)) = A *ᵥ x := by
    funext i
    exact eval_linearSubstitution A x i
  rw [hf]

omit [Fintype ι] in
theorem changeVariables_linearSubstitution (A : Matrix ι κ ℝ)
    (B : Matrix κ ν ℝ) (i : ι) :
    changeVariables B (linearSubstitution A i) = linearSubstitution (A * B) i := by
  simp only [linearSubstitution, map_sum, map_mul, changeVariables, aeval_C,
    algebraMap_eq, aeval_X, Matrix.mul_apply, map_sum, Finset.sum_mul,
    map_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  ring

omit [Fintype ι] in
theorem changeVariables_comp (A : Matrix ι κ ℝ) (B : Matrix κ ν ℝ)
    (P : MvPolynomial ι ℝ) :
    changeVariables B (changeVariables A P) = changeVariables (A * B) P := by
  change (changeVariables B) (aeval (linearSubstitution A) P) = _
  rw [comp_aeval_apply]
  change aeval _ P = aeval _ P
  have hf : (fun i => changeVariables B (linearSubstitution A i)) =
      linearSubstitution (A * B) := by
    funext i
    exact changeVariables_linearSubstitution A B i
  rw [hf]

theorem linearSubstitution_one [DecidableEq ι] (i : ι) :
    linearSubstitution (1 : Matrix ι ι ℝ) i = X i := by
  simp [linearSubstitution, Matrix.one_apply]

theorem changeVariables_one [DecidableEq ι] (P : MvPolynomial ι ℝ) :
    changeVariables (1 : Matrix ι ι ℝ) P = P := by
  have hf : linearSubstitution (1 : Matrix ι ι ℝ) = X :=
    funext linearSubstitution_one
  simp only [changeVariables, hf, aeval_X_left_apply]

theorem changeVariables_transpose_leftInverse [DecidableEq ι]
    (A : Matrix ι κ ℝ) (hA : A * A.transpose = 1) :
    Function.LeftInverse (changeVariables A.transpose) (changeVariables A) := by
  intro P
  rw [changeVariables_comp, hA, changeVariables_one]

theorem changeVariables_injective [DecidableEq ι]
    (A : Matrix ι κ ℝ) (hA : A * A.transpose = 1) :
    Function.Injective (changeVariables A) :=
  (changeVariables_transpose_leftInverse A hA).injective

omit [Fintype ι] in
theorem isHomogeneous_linearSubstitution (A : Matrix ι κ ℝ) (i : ι) :
    (linearSubstitution A i).IsHomogeneous 1 := by
  apply IsHomogeneous.sum
  intro j hj
  exact isHomogeneous_C_mul_X _ _

omit [Fintype ι] in
theorem isHomogeneous_changeVariables (A : Matrix ι κ ℝ)
    (P : MvPolynomial ι ℝ) (d : ℕ) (hP : P.IsHomogeneous d) :
    (changeVariables A P).IsHomogeneous d := by
  simpa only [one_mul, changeVariables] using hP.aeval (linearSubstitution A)
    (isHomogeneous_linearSubstitution A)

omit [Fintype ι] in
theorem totalDegree_changeVariables_le (A : Matrix ι κ ℝ)
    (P : MvPolynomial ι ℝ) :
    (changeVariables A P).totalDegree ≤ P.totalDegree := by
  classical
  conv_lhs => rw [← sum_homogeneousComponent P]
  rw [map_sum]
  apply totalDegree_finsetSum_le
  intro d hd
  exact (isHomogeneous_changeVariables A _ d (homogeneousComponent_isHomogeneous d P)).totalDegree_le.trans
    (Nat.lt_succ_iff.mp (Finset.mem_range.mp hd))

theorem totalDegree_changeVariables [DecidableEq ι]
    (A : Matrix ι κ ℝ) (hA : A * A.transpose = 1) (P : MvPolynomial ι ℝ) :
    (changeVariables A P).totalDegree = P.totalDegree := by
  apply le_antisymm (totalDegree_changeVariables_le A P)
  calc
    P.totalDegree = (changeVariables A.transpose (changeVariables A P)).totalDegree := by
      rw [changeVariables_transpose_leftInverse A hA P]
    _ ≤ (changeVariables A P).totalDegree := totalDegree_changeVariables_le _ _

end QuarticMinimal
end

end ComponentLinearSubstitution


/- Component: DistinguishedVariable -/
section ComponentDistinguishedVariable

namespace QuarticMinimal.DistinguishedVariable

open MvPolynomial

variable {R : Type*} [CommSemiring R] {n : ℕ}

theorem cons_add_single_zero (m : Fin n →₀ ℕ) (k : ℕ) :
    m.cons k + Finsupp.single 0 1 = m.cons (k + 1) := by
  ext i
  cases i using Fin.cases <;> simp

theorem cons_add_single_succ (m : Fin n →₀ ℕ) (k : ℕ) (i : Fin n) :
    m.cons k + Finsupp.single i.succ 1 = (m + Finsupp.single i 1).cons k := by
  ext j
  cases j using Fin.cases <;> simp [Finsupp.single_apply, Fin.succ_inj]

theorem finSuccEquiv_pderiv_zero (P : MvPolynomial (Fin (n + 1)) R) :
    finSuccEquiv R n (pderiv 0 P) = Polynomial.derivative (finSuccEquiv R n P) := by
  apply Polynomial.ext
  intro k
  apply MvPolynomial.ext
  intro m
  rw [finSuccEquiv_coeff_coeff, coeff_pderiv, Polynomial.coeff_derivative]
  have hcast : (k : MvPolynomial (Fin n) R) + 1 = C ((k : R) + 1) := by simp
  rw [hcast, mul_comm _ (C _), coeff_C_mul, finSuccEquiv_coeff_coeff]
  simp [cons_add_single_zero, mul_comm]

theorem coeff_finSuccEquiv_pderiv_succ (P : MvPolynomial (Fin (n + 1)) R)
    (i : Fin n) (k : ℕ) :
    (finSuccEquiv R n (pderiv i.succ P)).coeff k =
      pderiv i ((finSuccEquiv R n P).coeff k) := by
  apply MvPolynomial.ext
  intro m
  rw [finSuccEquiv_coeff_coeff, coeff_pderiv, coeff_pderiv, finSuccEquiv_coeff_coeff]
  simp [cons_add_single_succ]

/-- Differentiate the multivariate coefficients while leaving the distinguished
univariate variable fixed. -/
noncomputable def coefficientPartial (i : Fin n)
    (Q : Polynomial (MvPolynomial (Fin n) R)) : Polynomial (MvPolynomial (Fin n) R) :=
  Polynomial.ofFinsupp (AddMonoidAlgebra.ofCoeff
    (Q.coeff.mapRange (pderiv i) (map_zero (pderiv i))))


theorem coeff_coefficientPartial (i : Fin n)
    (Q : Polynomial (MvPolynomial (Fin n) R)) (k : ℕ) :
    (coefficientPartial i Q).coeff k = pderiv i (Q.coeff k) := rfl

theorem finSuccEquiv_pderiv_succ (P : MvPolynomial (Fin (n + 1)) R) (i : Fin n) :
    finSuccEquiv R n (pderiv i.succ P) = coefficientPartial i (finSuccEquiv R n P) := by
  apply Polynomial.ext
  intro k
  exact coeff_finSuccEquiv_pderiv_succ P i k

theorem coefficientPartial_eq_transport (i : Fin n)
    (Q : Polynomial (MvPolynomial (Fin n) R)) :
    coefficientPartial i Q =
      finSuccEquiv R n (pderiv i.succ ((finSuccEquiv R n).symm Q)) := by
  rw [finSuccEquiv_pderiv_succ, AlgEquiv.apply_symm_apply]


theorem coefficientPartial_add (i : Fin n)
    (Q T : Polynomial (MvPolynomial (Fin n) R)) :
    coefficientPartial i (Q + T) = coefficientPartial i Q + coefficientPartial i T := by
  ext k
  simp [coeff_coefficientPartial]


theorem coefficientPartial_mul (i : Fin n)
    (Q T : Polynomial (MvPolynomial (Fin n) R)) :
    coefficientPartial i (Q * T) =
      Q * coefficientPartial i T + T * coefficientPartial i Q := by
  simp only [coefficientPartial_eq_transport, map_mul, pderiv_mul, map_add]
  simp only [AlgEquiv.apply_symm_apply]
  ring


theorem coefficientPartial_C (i : Fin n) (a : MvPolynomial (Fin n) R) :
    coefficientPartial i (Polynomial.C a) = Polynomial.C (pderiv i a) := by
  ext k
  simp only [coeff_coefficientPartial, Polynomial.coeff_C]
  split_ifs <;> simp


theorem coefficientPartial_X (i : Fin n) :
    coefficientPartial i (Polynomial.X : Polynomial (MvPolynomial (Fin n) R)) = 0 := by
  ext k
  simp only [coeff_coefficientPartial, Polynomial.coeff_X, Polynomial.coeff_zero]
  split_ifs <;> simp


theorem coefficientPartial_zero (i : Fin n) :
    coefficientPartial i (0 : Polynomial (MvPolynomial (Fin n) R)) = 0 := by
  ext k
  simp [coeff_coefficientPartial]


theorem coefficientPartial_pow (i : Fin n)
    (Q : Polynomial (MvPolynomial (Fin n) R)) (k : ℕ) :
    coefficientPartial i (Q ^ k) = k * Q ^ (k - 1) * coefficientPartial i Q := by
  simp only [coefficientPartial_eq_transport, map_pow, pderiv_pow, map_mul, map_natCast,
    AlgEquiv.apply_symm_apply]

theorem coefficientPartial_derivative (i : Fin n)
    (Q : Polynomial (MvPolynomial (Fin n) R)) :
    coefficientPartial i (Polynomial.derivative Q) =
      Polynomial.derivative (coefficientPartial i Q) := by
  apply Polynomial.ext
  intro k
  simp only [coeff_coefficientPartial, Polynomial.coeff_derivative]
  have hcast : (k : MvPolynomial (Fin n) R) + 1 = C ((k : R) + 1) := by simp
  rw [hcast, pderiv_mul, pderiv_C, mul_zero, add_zero]

theorem finSuccEquiv_pderiv_zero_zero (P : MvPolynomial (Fin (n + 1)) R) :
    finSuccEquiv R n (pderiv 0 (pderiv 0 P)) =
      Polynomial.derivative (Polynomial.derivative (finSuccEquiv R n P)) := by
  rw [finSuccEquiv_pderiv_zero, finSuccEquiv_pderiv_zero]

theorem coeff_finSuccEquiv_pderiv_succ_succ (P : MvPolynomial (Fin (n + 1)) R)
    (i j : Fin n) (k : ℕ) :
    (finSuccEquiv R n (pderiv i.succ (pderiv j.succ P))).coeff k =
      pderiv i (pderiv j ((finSuccEquiv R n P).coeff k)) := by
  rw [coeff_finSuccEquiv_pderiv_succ, coeff_finSuccEquiv_pderiv_succ]

theorem coeff_finSuccEquiv_totalDegree_le (P : MvPolynomial (Fin (n + 1)) R)
    {m : ℕ} (hP : P.totalDegree ≤ m) (k : ℕ) :
    ((finSuccEquiv R n P).coeff k).totalDegree ≤ m - k := by
  by_cases hk : (finSuccEquiv R n P).coeff k = 0
  · simp [hk]
  · have h := totalDegree_coeff_finSuccEquiv_add_le P k hk
    omega

theorem coeff_finSuccEquiv_eq_zero (P : MvPolynomial (Fin (n + 1)) R)
    {m k : ℕ} (hP : P.totalDegree ≤ m) (hk : m < k) :
    (finSuccEquiv R n P).coeff k = 0 := by
  by_contra hne
  have h := totalDegree_coeff_finSuccEquiv_add_le P k hne
  omega

theorem finSuccEquiv_natDegree_le (P : MvPolynomial (Fin (n + 1)) R)
    {m : ℕ} (hP : P.totalDegree ≤ m) :
    (finSuccEquiv R n P).natDegree ≤ m := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  exact coeff_finSuccEquiv_eq_zero P hP hk

theorem finSuccEquiv_eq_sum (P : MvPolynomial (Fin (n + 1)) R)
    {m : ℕ} (hP : P.totalDegree ≤ m) :
    finSuccEquiv R n P = ∑ k ∈ Finset.range (m + 1),
      Polynomial.C ((finSuccEquiv R n P).coeff k) * Polynomial.X ^ k := by
  exact Polynomial.as_sum_range_C_mul_X_pow' _ (Nat.lt_succ_of_le (finSuccEquiv_natDegree_le P hP))

theorem finSuccEquiv_quartic (P : MvPolynomial (Fin (n + 1)) R)
    (hP : P.totalDegree ≤ 4) :
    finSuccEquiv R n P =
      Polynomial.C ((finSuccEquiv R n P).coeff 4) * Polynomial.X ^ 4 +
      Polynomial.C ((finSuccEquiv R n P).coeff 3) * Polynomial.X ^ 3 +
      Polynomial.C ((finSuccEquiv R n P).coeff 2) * Polynomial.X ^ 2 +
      Polynomial.C ((finSuccEquiv R n P).coeff 1) * Polynomial.X +
      Polynomial.C ((finSuccEquiv R n P).coeff 0) := by
  conv_lhs => rw [finSuccEquiv_eq_sum P hP]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, mul_one, zero_add]
  ring

theorem coeff_finSuccEquiv_isHomogeneous (P : MvPolynomial (Fin (n + 1)) R)
    {m : ℕ} (hP : P.IsHomogeneous m) (k : ℕ) :
    ((finSuccEquiv R n P).coeff k).IsHomogeneous (m - k) := by
  by_cases hk : k ≤ m
  · exact hP.finSuccEquiv_coeff_isHomogeneous k (m - k) (Nat.add_sub_of_le hk)
  · rw [coeff_finSuccEquiv_eq_zero P hP.totalDegree_le (Nat.lt_of_not_ge hk)]
    exact isHomogeneous_zero (Fin n) R _

section MinimalExpression

variable {S : Type*} [CommRing S]

/-- Separating one coordinate in the algebraic minimal-graph expression. -/
theorem minimal_expression_split {ι : Type*} [Fintype ι]
    (d dd : S) (v dv : ι → S) (h : ι → ι → S) :
    (1 + (d ^ 2 + ∑ i, v i ^ 2)) * (dd + ∑ i, h i i) -
      (d * d * dd + (∑ i, d * v i * dv i) +
        ∑ i, (v i * d * dv i + ∑ j, v i * v j * h i j)) =
    (1 + ∑ i, v i ^ 2) * dd +
      (1 + d ^ 2 + ∑ i, v i ^ 2) * (∑ i, h i i) -
      2 * d * (∑ i, dv i * v i) - ∑ i, ∑ j, v i * v j * h i j := by
  rw [Finset.sum_add_distrib]
  have hc : (∑ i, d * v i * dv i) = d * ∑ i, dv i * v i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hc' : (∑ i, v i * d * dv i) = d * ∑ i, dv i * v i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hc, hc']
  ring

/-- The minimal-graph numerator after separating the zeroth variable. -/
noncomputable def splitMinimalExpression
    (Q : Polynomial (MvPolynomial (Fin n) S)) : Polynomial (MvPolynomial (Fin n) S) :=
  (1 + ∑ i, coefficientPartial i Q ^ 2) *
      Polynomial.derivative (Polynomial.derivative Q) +
    (1 + Polynomial.derivative Q ^ 2 + ∑ i, coefficientPartial i Q ^ 2) *
      (∑ i, coefficientPartial i (coefficientPartial i Q)) -
    2 * Polynomial.derivative Q *
      (∑ i, Polynomial.derivative (coefficientPartial i Q) * coefficientPartial i Q) -
    ∑ i, ∑ j, coefficientPartial i Q * coefficientPartial j Q *
      coefficientPartial i (coefficientPartial j Q)

theorem finSuccEquiv_minimalExpression (P : MvPolynomial (Fin (n + 1)) S) :
    finSuccEquiv S n
      ((1 + ∑ i, pderiv i P ^ 2) * (∑ i, pderiv i (pderiv i P)) -
        ∑ i, ∑ j, pderiv i P * pderiv j P * pderiv i (pderiv j P)) =
      splitMinimalExpression (finSuccEquiv S n P) := by
  simp only [map_sub, map_mul, map_add, map_one, map_sum, map_pow, Fin.sum_univ_succ,
    finSuccEquiv_pderiv_zero, finSuccEquiv_pderiv_succ, coefficientPartial_derivative]
  exact minimal_expression_split
    (Polynomial.derivative (finSuccEquiv S n P))
    (Polynomial.derivative (Polynomial.derivative (finSuccEquiv S n P)))
    (fun i : Fin n => coefficientPartial i (finSuccEquiv S n P))
    (fun i : Fin n => Polynomial.derivative (coefficientPartial i (finSuccEquiv S n P)))
    (fun i j : Fin n => coefficientPartial i (coefficientPartial j (finSuccEquiv S n P)))

end MinimalExpression

end QuarticMinimal.DistinguishedVariable
end ComponentDistinguishedVariable


/- Component: HomogeneousHessian -/
section ComponentHomogeneousHessian

/- Requires PolynomialBasics and LowDegree. -/
noncomputable section
open scoped BigOperators Matrix
open MvPolynomial

namespace QuarticMinimal

variable {ι : Type*} [Fintype ι]

theorem eval_homogeneous_quadratic_expansion (P : MvPolynomial ι ℝ)
    (hP : P.IsHomogeneous 2) (x : ι → ℝ) :
    eval x P = (1 / 2 : ℝ) * ∑ i, ∑ j, hessianCoeff P i j * x i * x j := by
  conv_lhs => rw [homogeneous_quadratic_expansion P hP]
  simp only [map_mul, map_sum, eval_C, eval_X]

omit [Fintype ι] in
theorem fourth_partial_pair_comm (P : MvPolynomial ι ℝ) (i j k l : ι) :
    pderiv k (pderiv l (pderiv i (pderiv j P))) =
      pderiv i (pderiv j (pderiv k (pderiv l P))) := by
  simp only [QuarticPolynomialBasics.second_partial_comm]

theorem sum_four_swap (f : ι → ι → ι → ι → ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ l, f i j k l) = ∑ k, ∑ l, ∑ i, ∑ j, f i j k l := by
  simpa only [Fintype.sum_prod_type] using
    (Finset.sum_comm (s := (Finset.univ : Finset (ι × ι)))
      (t := (Finset.univ : Finset (ι × ι)))
      (f := fun ij : ι × ι => fun kl : ι × ι => f ij.1 ij.2 kl.1 kl.2))

theorem quartic_mixed_hessian_symmetry (P : MvPolynomial ι ℝ)
    (hP : P.IsHomogeneous 4) (x y : ι → ℝ) :
    (∑ i, ∑ j, y i * y j * eval x (pderiv i (pderiv j P))) =
      ∑ i, ∑ j, x i * x j * eval y (pderiv i (pderiv j P)) := by
  have hp (i j : ι) : (pderiv i (pderiv j P)).IsHomogeneous 2 := by
    simpa only [Nat.reduceSub] using QuarticCompatibility.homogeneous_pderiv (i := i)
      (QuarticCompatibility.homogeneous_pderiv (i := j) hP)
  simp_rw [eval_homogeneous_quadratic_expansion _ (hp _ _), Finset.mul_sum]
  conv_lhs => rw [sum_four_swap]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp only [hessianCoeff, fourth_partial_pair_comm]
  ring

end QuarticMinimal
end

end ComponentHomogeneousHessian


/- Component: HomogeneousQuarticCoefficients -/
section ComponentHomogeneousQuarticCoefficients


open scoped BigOperators
open Polynomial

namespace HomogeneousQuarticCoefficients

variable {R : Type*} [CommRing R]

noncomputable def longitudinal (a A B : R) : R[X] :=
  C (4*a)*X^3+C (2*A)*X+C B

noncomputable def longitudinalSecond (a A : R) : R[X] := C (12*a)*X^2+C (2*A)

noncomputable def transverse (α β γ : R) : R[X] := C α*X^2+C β*X+C γ

noncomputable def mixedSecond (α β : R) : R[X] := C (2*α)*X+C β

noncomputable def transverseTrace (h k l : R) : R[X] := C h*X^2+C k*X+C l

noncomputable def baseTerm (a A B h k l : R) : R[X] :=
  longitudinal a A B^2*transverseTrace h k l

noncomputable def singleTerm (a A B h k l α β γ : R) : R[X] :=
  transverse α β γ^2*(longitudinalSecond a A+transverseTrace h k l)-
    2*longitudinal a A B*mixedSecond α β*transverse α β γ

noncomputable def hessianTerm (α β γ α' β' γ' H K L : R) : R[X] :=
  transverse α β γ*transverse α' β' γ'*(C H*X^2+C K*X+C L)

theorem base_coeff8 (a A B h k l : R) :
    (baseTerm a A B h k l).coeff 8 = 16*a^2*h := by
  unfold baseTerm longitudinal transverseTrace
  ring_nf
  simp [mul_assoc, ← map_mul, ← map_pow, Polynomial.coeff_X, Polynomial.coeff_C]
  ring


theorem base_coeff7 (a A B h k l : R) :
    (baseTerm a A B h k l).coeff 7 = 16*a^2*k := by
  unfold baseTerm longitudinal transverseTrace
  ring_nf
  simp [mul_assoc, ← map_mul, ← map_pow, Polynomial.coeff_X, Polynomial.coeff_C]
  ring


theorem base_coeff6 (a A B h k l : R) :
    (baseTerm a A B h k l).coeff 6 = 16*a^2*l+16*a*A*h := by
  unfold baseTerm longitudinal transverseTrace
  ring_nf
  simp [mul_assoc, ← map_mul, ← map_pow, Polynomial.coeff_X, Polynomial.coeff_C]
  ring

theorem single_coeff8 (a A B h k l α β γ : R) :
    (singleTerm a A B h k l α β γ).coeff 8 = 0 := by
  unfold singleTerm transverse longitudinalSecond longitudinal mixedSecond transverseTrace
  ring_nf
  simp [mul_assoc, ← map_mul, ← map_pow, Polynomial.coeff_X, Polynomial.coeff_C]

theorem single_coeff7 (a A B h k l α β γ : R) :
    (singleTerm a A B h k l α β γ).coeff 7 = 0 := by
  unfold singleTerm transverse longitudinalSecond longitudinal mixedSecond transverseTrace
  ring_nf
  simp [mul_assoc, ← map_mul, ← map_pow, Polynomial.coeff_X, Polynomial.coeff_C]

theorem single_coeff6 (a A B h k l α β γ : R) :
    (singleTerm a A B h k l α β γ).coeff 6 = (h-4*a)*α^2 := by
  unfold singleTerm transverse longitudinalSecond longitudinal mixedSecond transverseTrace
  ring_nf
  simp [mul_assoc, ← map_mul, ← map_pow, Polynomial.coeff_X, Polynomial.coeff_C]
  ring

theorem hessian_coeff8 (α β γ α' β' γ' H K L : R) :
    (hessianTerm α β γ α' β' γ' H K L).coeff 8 = 0 := by
  unfold hessianTerm transverse
  ring_nf
  simp [mul_assoc, ← map_mul, Polynomial.coeff_X, Polynomial.coeff_C]

theorem hessian_coeff7 (α β γ α' β' γ' H K L : R) :
    (hessianTerm α β γ α' β' γ' H K L).coeff 7 = 0 := by
  unfold hessianTerm transverse
  ring_nf
  simp [mul_assoc, ← map_mul, Polynomial.coeff_X, Polynomial.coeff_C]

theorem hessian_coeff6 (α β γ α' β' γ' H K L : R) :
    (hessianTerm α β γ α' β' γ' H K L).coeff 6 = α*α'*H := by
  unfold hessianTerm transverse
  ring_nf
  simp [mul_assoc, ← map_mul, Polynomial.coeff_X, Polynomial.coeff_C]

variable {ι : Type*} [Fintype ι]

/-- The cubic part of the minimal-graph operator for homogeneous quartic data. -/
noncomputable def operator (a A B h k l : R) (α β γ : ι → R)
    (H K L : ι → ι → R) : R[X] :=
  (∑ i, transverse (α i) (β i) (γ i)^2)*longitudinalSecond a A+
    (longitudinal a A B^2+∑ i, transverse (α i) (β i) (γ i)^2)*transverseTrace h k l-
    2*longitudinal a A B*(∑ i, mixedSecond (α i) (β i)*transverse (α i) (β i) (γ i))-
    ∑ i, ∑ j, hessianTerm (α i) (β i) (γ i) (α j) (β j) (γ j) (H i j) (K i j) (L i j)

theorem operator_decomposition (a A B h k l : R) (α β γ : ι → R)
    (H K L : ι → ι → R) :
    operator a A B h k l α β γ H K L = baseTerm a A B h k l+
      (∑ i, singleTerm a A B h k l (α i) (β i) (γ i))-
      ∑ i, ∑ j, hessianTerm (α i) (β i) (γ i) (α j) (β j) (γ j) (H i j) (K i j) (L i j) := by
  unfold operator baseTerm singleTerm
  simp only [mul_add, add_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.mul_sum, Finset.sum_mul, mul_assoc]
  abel

theorem operator_coeff8 (a A B h k l : R) (α β γ : ι → R)
    (H K L : ι → ι → R) :
    (operator a A B h k l α β γ H K L).coeff 8=16*a^2*h := by
  simp [operator_decomposition, base_coeff8, single_coeff8, hessian_coeff8]

theorem operator_coeff7 (a A B h k l : R) (α β γ : ι → R)
    (H K L : ι → ι → R) :
    (operator a A B h k l α β γ H K L).coeff 7=16*a^2*k := by
  simp [operator_decomposition, base_coeff7, single_coeff7, hessian_coeff7]

theorem operator_coeff6 (a A B h k l : R) (α β γ : ι → R)
    (H K L : ι → ι → R) :
    (operator a A B h k l α β γ H K L).coeff 6=
      16*a^2*l+16*a*A*h+(h-4*a)*(∑ i, (α i)^2)-
      ∑ i, ∑ j, α i*α j*H i j := by
  simp only [operator_decomposition, coeff_add, coeff_sub, finsetSum_coeff,
    base_coeff6, single_coeff6, hessian_coeff6, ← Finset.mul_sum]

theorem operator_coeff6_of_trace_zero (a A B k l : R) (α β γ : ι → R)
    (H K L : ι → ι → R) :
    (operator a A B 0 k l α β γ H K L).coeff 6=
      16*a^2*l-4*a*(∑ i, (α i)^2)-∑ i, ∑ j, α i*α j*H i j := by
  rw [operator_coeff6]
  ring


section Domain
variable {F : Type*} [CommRing F] [IsDomain F] [CharZero F]

theorem traces_zero_of_operator_zero (a A B h k l : F) (ha : a ≠ 0)
    (α β γ : ι → F) (H K L : ι → ι → F)
    (hop : operator a A B h k l α β γ H K L = 0) : h = 0 ∧ k = 0 := by
  have h8 := congrArg (fun p : F[X] => p.coeff 8) hop
  have h7 := congrArg (fun p : F[X] => p.coeff 7) hop
  rw [operator_coeff8, coeff_zero] at h8
  rw [operator_coeff7, coeff_zero] at h7
  have hn : (16:F)*a^2 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 2 ha)
  exact ⟨(mul_eq_zero.mp h8).resolve_left hn, (mul_eq_zero.mp h7).resolve_left hn⟩

theorem laplacian_scalar_relation (a A B h k l : F) (ha : a ≠ 0)
    (α β γ : ι → F) (H K L : ι → ι → F)
    (hop : operator a A B h k l α β γ H K L = 0) :
    16*a^2*l-4*a*(∑ i, (α i)^2)-∑ i, ∑ j, α i*α j*H i j = 0 := by
  obtain ⟨hh, _⟩ := traces_zero_of_operator_zero a A B h k l ha α β γ H K L hop
  subst h
  have h6 := congrArg (fun p : F[X] => p.coeff 6) hop
  simpa only [operator_coeff6_of_trace_zero, coeff_zero] using h6
end Domain

open Matrix

theorem dot_move_symmetric (S : Matrix ι ι R) (hS : S.IsSymm) (x y : ι → R) :
    (S *ᵥ x) ⬝ᵥ y = x ⬝ᵥ (S *ᵥ y) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hS]

theorem sum_pairing_eq_dot (H : Matrix ι ι R) (x y : ι → R) :
    (∑ i, ∑ j, x i*y j*H i j) = x ⬝ᵥ (H *ᵥ y) := by
  simp only [dotProduct, mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

variable [DecidableEq ι]

theorem gradient_square_relation (S : Matrix ι ι R) (hS : S.IsSymm) (y : ι → R) :
    (∑ i, (2*(S *ᵥ y) i)^2) = 4*(y ⬝ᵥ (S^2 *ᵥ y)) := by
  calc
    _ = ((2:R) • (S *ᵥ y)) ⬝ᵥ ((2:R) • (S *ᵥ y)) := by
      simp [dotProduct, Pi.smul_apply, smul_eq_mul, pow_two]
    _ = 4*((S *ᵥ y) ⬝ᵥ (S *ᵥ y)) := by
      rw [smul_dotProduct, dotProduct_smul]
      simp only [smul_eq_mul]
      ring
    _ = 4*(y ⬝ᵥ (S^2 *ᵥ y)) := by
      rw [dot_move_symmetric S hS]
      simp only [pow_two, mulVec_mulVec]

theorem gradient_hessian_relation (S : Matrix ι ι R) (hS : S.IsSymm) (y : ι → R) :
    (∑ i, ∑ j, (2*(S *ᵥ y) i)*(2*(S *ᵥ y) j)*(2*S i j)) =
      8*(y ⬝ᵥ (S^3 *ᵥ y)) := by
  change (∑ i, ∑ j, (((2:R) • (S *ᵥ y)) i)*(((2:R) • (S *ᵥ y)) j)*
    (((2:R) • S) i j)) = _
  rw [sum_pairing_eq_dot, smul_mulVec, mulVec_smul, smul_dotProduct,
    dotProduct_smul, dotProduct_smul]
  simp only [smul_eq_mul]
  rw [dot_move_symmetric S hS]
  simp only [pow_succ, pow_zero, Matrix.one_mul, Matrix.mul_assoc, mulVec_mulVec]
  ring


section Field
variable {F : Type*} [Field F] [CharZero F]

/-- The tangential Laplacian identity after writing `A(y)=yᵀ S y`. The assumptions
are the polynomial operator equation and the explicit gradient/Hessian of `A`. -/
theorem laplacian_matrix_relation (a A B h k l : F) (ha : a ≠ 0)
    (S : Matrix ι ι F) (hS : S.IsSymm) (y β γ : ι → F)
    (K L : ι → ι → F)
    (hop : operator a A B h k l (fun i => 2*(S *ᵥ y) i) β γ
      (fun i j => 2*S i j) K L = 0) :
    l = y ⬝ᵥ ((a⁻¹ • S^2+(2*a^2)⁻¹ • S^3) *ᵥ y) := by
  have hc := laplacian_scalar_relation a A B h k l ha
    (fun i => 2*(S *ᵥ y) i) β γ (fun i j => 2*S i j) K L hop
  rw [gradient_square_relation S hS y, gradient_hessian_relation S hS y] at hc
  simp only [add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul]
  field_simp [ha]
  linear_combination (1/8:F)*hc


/-- The full Laplacian polynomial in the distinguished variable, in matrix form. -/
theorem laplacian_polynomial_relation (a B h k l : F) (ha : a ≠ 0)
    (S : Matrix ι ι F) (hS : S.IsSymm) (y β γ : ι → F)
    (K L : ι → ι → F)
    (hop : operator a (y ⬝ᵥ (S *ᵥ y)) B h k l (fun i => 2*(S *ᵥ y) i) β γ
      (fun i j => 2*S i j) K L = 0) :
    longitudinalSecond a (y ⬝ᵥ (S *ᵥ y))+transverseTrace h k l =
      C (12*a)*X^2+
        C (y ⬝ᵥ (((2:F) • S+a⁻¹ • S^2+(2*a^2)⁻¹ • S^3) *ᵥ y)) := by
  obtain ⟨hh, hk⟩ := traces_zero_of_operator_zero a (y ⬝ᵥ (S *ᵥ y)) B h k l ha
    (fun i => 2*(S *ᵥ y) i) β γ (fun i j => 2*S i j) K L hop
  have hl := laplacian_matrix_relation a (y ⬝ᵥ (S *ᵥ y)) B h k l ha S hS y β γ K L hop
  simp [longitudinalSecond, transverseTrace, hh, hk, hl, add_mulVec, smul_mulVec,
    dotProduct_add, dotProduct_smul, smul_eq_mul, C_add, add_assoc]

end Field

end HomogeneousQuarticCoefficients

end ComponentHomogeneousQuarticCoefficients


/- Component: QuarticNormalForm -/
section ComponentQuarticNormalForm

/- This component follows DistinguishedVariable and HomogeneousQuarticCoefficients. -/
namespace QuarticMinimal.QuarticNormalForm

open MvPolynomial
open QuarticMinimal.DistinguishedVariable

variable {n : ℕ}

noncomputable def laplacian (A : MvPolynomial (Fin n) ℝ) : MvPolynomial (Fin n) ℝ :=
  ∑ i, pderiv i (pderiv i A)

noncomputable def leadingExpression (P : MvPolynomial (Fin n) ℝ) : MvPolynomial (Fin n) ℝ :=
  (∑ i, pderiv i P ^ 2) * (∑ i, pderiv i (pderiv i P)) -
    ∑ i, ∑ j, pderiv i P * pderiv j P * pderiv i (pderiv j P)

noncomputable def splitLeadingExpression
    (Q : Polynomial (MvPolynomial (Fin n) ℝ)) : Polynomial (MvPolynomial (Fin n) ℝ) :=
  (∑ i, coefficientPartial i Q ^ 2) * Polynomial.derivative (Polynomial.derivative Q) +
    (Polynomial.derivative Q ^ 2 + ∑ i, coefficientPartial i Q ^ 2) *
      (∑ i, coefficientPartial i (coefficientPartial i Q)) -
    2 * Polynomial.derivative Q *
      (∑ i, Polynomial.derivative (coefficientPartial i Q) * coefficientPartial i Q) -
    ∑ i, ∑ j, coefficientPartial i Q * coefficientPartial j Q *
      coefficientPartial i (coefficientPartial j Q)

theorem leading_expression_split {S ι : Type*} [CommRing S] [Fintype ι]
    (d dd : S) (v dv : ι → S) (h : ι → ι → S) :
    (d ^ 2 + ∑ i, v i ^ 2) * (dd + ∑ i, h i i) -
      (d * d * dd + (∑ i, d * v i * dv i) +
        ∑ i, (v i * d * dv i + ∑ j, v i * v j * h i j)) =
    (∑ i, v i ^ 2) * dd +
      (d ^ 2 + ∑ i, v i ^ 2) * (∑ i, h i i) -
      2 * d * (∑ i, dv i * v i) - ∑ i, ∑ j, v i * v j * h i j := by
  have hm := minimal_expression_split d dd v dv h
  linear_combination hm

theorem finSuccEquiv_leadingExpression (P : MvPolynomial (Fin (n + 1)) ℝ) :
    finSuccEquiv ℝ n (leadingExpression P) = splitLeadingExpression (finSuccEquiv ℝ n P) := by
  simp only [leadingExpression, map_sub, map_mul, map_add, map_sum, map_pow,
    Fin.sum_univ_succ, finSuccEquiv_pderiv_zero, finSuccEquiv_pderiv_succ,
    coefficientPartial_derivative]
  exact leading_expression_split
    (Polynomial.derivative (finSuccEquiv ℝ n P))
    (Polynomial.derivative (Polynomial.derivative (finSuccEquiv ℝ n P)))
    (fun i : Fin n => coefficientPartial i (finSuccEquiv ℝ n P))
    (fun i : Fin n => Polynomial.derivative (coefficientPartial i (finSuccEquiv ℝ n P)))
    (fun i j : Fin n => coefficientPartial i (coefficientPartial j (finSuccEquiv ℝ n P)))

noncomputable def normalForm (a : ℝ) (A B D : MvPolynomial (Fin n) ℝ) :
    Polynomial (MvPolynomial (Fin n) ℝ) :=
  Polynomial.C (C a) * Polynomial.X ^ 4 + Polynomial.C A * Polynomial.X ^ 2 +
    Polynomial.C B * Polynomial.X + Polynomial.C D

theorem finSuccEquiv_normalForm (P : MvPolynomial (Fin (n + 1)) ℝ) (a : ℝ)
    (hP : P.totalDegree ≤ 4) (h4 : (finSuccEquiv ℝ n P).coeff 4 = C a)
    (h3 : (finSuccEquiv ℝ n P).coeff 3 = 0) :
    finSuccEquiv ℝ n P = normalForm a ((finSuccEquiv ℝ n P).coeff 2)
      ((finSuccEquiv ℝ n P).coeff 1) ((finSuccEquiv ℝ n P).coeff 0) := by
  conv_lhs => rw [finSuccEquiv_quartic P hP]
  simp only [h4, h3, map_zero, zero_mul, add_zero, normalForm]

theorem derivative_normalForm (a : ℝ) (A B D : MvPolynomial (Fin n) ℝ) :
    Polynomial.derivative (normalForm a A B D) =
      HomogeneousQuarticCoefficients.longitudinal (C a) A B := by
  simp [normalForm, HomogeneousQuarticCoefficients.longitudinal, Polynomial.C_ofNat]
  ring

theorem second_derivative_normalForm (a : ℝ) (A B D : MvPolynomial (Fin n) ℝ) :
    Polynomial.derivative (Polynomial.derivative (normalForm a A B D)) =
      HomogeneousQuarticCoefficients.longitudinalSecond (C a) A := by
  rw [derivative_normalForm]
  simp [HomogeneousQuarticCoefficients.longitudinal,
    HomogeneousQuarticCoefficients.longitudinalSecond, Polynomial.C_ofNat]
  ring

theorem coefficientPartial_normalForm (a : ℝ) (A B D : MvPolynomial (Fin n) ℝ) (i : Fin n) :
    coefficientPartial i (normalForm a A B D) =
      HomogeneousQuarticCoefficients.transverse (pderiv i A) (pderiv i B) (pderiv i D) := by
  simp [normalForm, HomogeneousQuarticCoefficients.transverse,
    coefficientPartial_add, coefficientPartial_mul, coefficientPartial_C,
    coefficientPartial_pow, coefficientPartial_X]

theorem derivative_transverse (α β γ : MvPolynomial (Fin n) ℝ) :
    Polynomial.derivative (HomogeneousQuarticCoefficients.transverse α β γ) =
      HomogeneousQuarticCoefficients.mixedSecond α β := by
  simp [HomogeneousQuarticCoefficients.transverse, HomogeneousQuarticCoefficients.mixedSecond,
    Polynomial.C_ofNat]
  ring

theorem coefficientPartial_transverse (α β γ : MvPolynomial (Fin n) ℝ) (i : Fin n) :
    coefficientPartial i (HomogeneousQuarticCoefficients.transverse α β γ) =
      HomogeneousQuarticCoefficients.transverse (pderiv i α) (pderiv i β) (pderiv i γ) := by
  simp [HomogeneousQuarticCoefficients.transverse,
    coefficientPartial_add, coefficientPartial_mul, coefficientPartial_C,
    coefficientPartial_pow, coefficientPartial_X]

theorem sum_transverse (α β γ : Fin n → MvPolynomial (Fin n) ℝ) :
    (∑ i, HomogeneousQuarticCoefficients.transverse (α i) (β i) (γ i)) =
      HomogeneousQuarticCoefficients.transverseTrace (∑ i, α i) (∑ i, β i) (∑ i, γ i) := by
  simp only [HomogeneousQuarticCoefficients.transverse, HomogeneousQuarticCoefficients.transverseTrace,
    Finset.sum_add_distrib, ← Finset.sum_mul, ← map_sum]

theorem splitLeadingExpression_normalForm (a : ℝ) (A B D : MvPolynomial (Fin n) ℝ) :
    splitLeadingExpression (normalForm a A B D) =
      HomogeneousQuarticCoefficients.operator (C a) A B (laplacian A) (laplacian B) (laplacian D)
        (fun i => pderiv i A) (fun i => pderiv i B) (fun i => pderiv i D)
        (fun i j => pderiv i (pderiv j A)) (fun i j => pderiv i (pderiv j B))
        (fun i j => pderiv i (pderiv j D)) := by
  simp only [splitLeadingExpression, coefficientPartial_normalForm, derivative_normalForm,
    derivative_transverse, coefficientPartial_transverse, sum_transverse]
  rw [show Polynomial.derivative (HomogeneousQuarticCoefficients.longitudinal (C a) A B) =
    HomogeneousQuarticCoefficients.longitudinalSecond (C a) A from by
      simpa only [derivative_normalForm] using second_derivative_normalForm a A B D]
  rfl

theorem finSuccEquiv_leadingExpression_normalForm
    (P : MvPolynomial (Fin (n + 1)) ℝ) (a : ℝ) (A B D : MvPolynomial (Fin n) ℝ)
    (hQ : finSuccEquiv ℝ n P = normalForm a A B D) :
    finSuccEquiv ℝ n (leadingExpression P) =
      HomogeneousQuarticCoefficients.operator (C a) A B (laplacian A) (laplacian B) (laplacian D)
        (fun i => pderiv i A) (fun i => pderiv i B) (fun i => pderiv i D)
        (fun i j => pderiv i (pderiv j A)) (fun i j => pderiv i (pderiv j B))
        (fun i j => pderiv i (pderiv j D)) := by
  rw [finSuccEquiv_leadingExpression, hQ, splitLeadingExpression_normalForm]

theorem actual_constraints_of_normalForm
    (P : MvPolynomial (Fin (n + 1)) ℝ) (a : ℝ) (A B D : MvPolynomial (Fin n) ℝ)
    (ha : a ≠ 0) (hQ : finSuccEquiv ℝ n P = normalForm a A B D)
    (hP : leadingExpression P = 0) :
    laplacian A = 0 ∧ laplacian B = 0 ∧
      16 * C a ^ 2 * laplacian D - 4 * C a * (∑ i, pderiv i A ^ 2) -
        ∑ i, ∑ j, pderiv i A * pderiv j A * pderiv i (pderiv j A) = 0 := by
  have hop := finSuccEquiv_leadingExpression_normalForm P a A B D hQ
  rw [hP, map_zero] at hop
  have hCa : (C a : MvPolynomial (Fin n) ℝ) ≠ 0 := C_ne_zero.mpr ha
  obtain ⟨hA, hB⟩ := HomogeneousQuarticCoefficients.traces_zero_of_operator_zero
    (C a) A B (laplacian A) (laplacian B) (laplacian D) hCa
    (fun i => pderiv i A) (fun i => pderiv i B) (fun i => pderiv i D)
    (fun i j => pderiv i (pderiv j A)) (fun i j => pderiv i (pderiv j B))
    (fun i j => pderiv i (pderiv j D)) hop.symm
  refine ⟨hA, hB, ?_⟩
  exact HomogeneousQuarticCoefficients.laplacian_scalar_relation
    (C a) A B (laplacian A) (laplacian B) (laplacian D) hCa
    (fun i => pderiv i A) (fun i => pderiv i B) (fun i => pderiv i D)
    (fun i j => pderiv i (pderiv j A)) (fun i j => pderiv i (pderiv j B))
    (fun i j => pderiv i (pderiv j D)) hop.symm

theorem finSuccEquiv_laplacian_normalForm
    (P : MvPolynomial (Fin (n + 1)) ℝ) (a : ℝ) (A B D : MvPolynomial (Fin n) ℝ)
    (hQ : finSuccEquiv ℝ n P = normalForm a A B D)
    (hA : laplacian A = 0) (hB : laplacian B = 0) :
    finSuccEquiv ℝ n (laplacian P) =
      Polynomial.C (12 * C a) * Polynomial.X ^ 2 + Polynomial.C (2 * A + laplacian D) := by
  conv_lhs =>
    simp only [laplacian, map_add, map_sum, Fin.sum_univ_succ, finSuccEquiv_pderiv_zero,
      finSuccEquiv_pderiv_succ]
  rw [hQ]
  simp only [second_derivative_normalForm, coefficientPartial_normalForm,
    coefficientPartial_transverse, sum_transverse]
  change HomogeneousQuarticCoefficients.longitudinalSecond (C a) A +
    HomogeneousQuarticCoefficients.transverseTrace (laplacian A) (laplacian B) (laplacian D) =
      Polynomial.C (12 * C a) * Polynomial.X ^ 2 + Polynomial.C (2 * A + laplacian D)
  simp [HomogeneousQuarticCoefficients.longitudinalSecond,
    HomogeneousQuarticCoefficients.transverseTrace, hA, hB, add_assoc]

theorem homogeneous_coefficients (P : MvPolynomial (Fin (n + 1)) ℝ)
    (hP : P.IsHomogeneous 4) :
    ((finSuccEquiv ℝ n P).coeff 2).IsHomogeneous 2 ∧
      ((finSuccEquiv ℝ n P).coeff 1).IsHomogeneous 3 ∧
      ((finSuccEquiv ℝ n P).coeff 0).IsHomogeneous 4 := by
  exact ⟨coeff_finSuccEquiv_isHomogeneous P hP 2,
    coeff_finSuccEquiv_isHomogeneous P hP 1, coeff_finSuccEquiv_isHomogeneous P hP 0⟩

theorem homogeneous_quartic_constraints
    (P : MvPolynomial (Fin (n + 1)) ℝ) (a : ℝ) (ha : a ≠ 0)
    (hP : P.IsHomogeneous 4) (h4 : (finSuccEquiv ℝ n P).coeff 4 = C a)
    (h3 : (finSuccEquiv ℝ n P).coeff 3 = 0) (hL : leadingExpression P = 0) :
    let A := (finSuccEquiv ℝ n P).coeff 2
    let B := (finSuccEquiv ℝ n P).coeff 1
    let D := (finSuccEquiv ℝ n P).coeff 0
    laplacian A = 0 ∧ laplacian B = 0 ∧
      16 * C a ^ 2 * laplacian D - 4 * C a * (∑ i, pderiv i A ^ 2) -
        ∑ i, ∑ j, pderiv i A * pderiv j A * pderiv i (pderiv j A) = 0 := by
  exact actual_constraints_of_normalForm P a _ _ _ ha
    (finSuccEquiv_normalForm P a hP.totalDegree_le h4 h3) hL

theorem laplacian_relation_at
    (P : MvPolynomial (Fin (n + 1)) ℝ) (a : ℝ) (A B D : MvPolynomial (Fin n) ℝ)
    (ha : a ≠ 0) (hQ : finSuccEquiv ℝ n P = normalForm a A B D)
    (hP : leadingExpression P = 0) (y : Fin n → ℝ) :
    16 * a ^ 2 * eval y (laplacian D) - 4 * a * (∑ i, eval y (pderiv i A) ^ 2) -
      ∑ i, ∑ j, eval y (pderiv i A) * eval y (pderiv j A) *
        eval y (pderiv i (pderiv j A)) = 0 := by
  have h := (actual_constraints_of_normalForm P a A B D ha hQ hP).2.2
  have he := congrArg (eval y) h
  simpa only [map_sub, map_mul, map_pow, map_sum, map_ofNat, eval_C, map_zero] using he

/- The remaining lemmas also use LowDegree.lean. -/
open Matrix

noncomputable def quadraticMatrix (A : MvPolynomial (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (1 / 2 : ℝ) • QuarticMinimal.hessianCoeff A

theorem quadraticMatrix_symmetric (A : MvPolynomial (Fin n) ℝ) :
    (quadraticMatrix A).IsSymm :=
  (QuarticMinimal.hessianCoeff_symmetric A).smul (1 / 2 : ℝ)

theorem eval_homogeneous_quadratic_gradient (A : MvPolynomial (Fin n) ℝ)
    (hA : A.IsHomogeneous 2) (y : Fin n → ℝ) (i : Fin n) :
    eval y (pderiv i A) = 2 * (quadraticMatrix A *ᵥ y) i := by
  rw [QuarticMinimal.eval_quadratic_gradient A hA.totalDegree_le]
  have hc : (pderiv i A).coeff 0 = 0 :=
    (QuarticCompatibility.homogeneous_pderiv (i := i) hA).coeff_eq_zero (by simp)
  simp only [hc, add_zero, quadraticMatrix, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul]
  ring

theorem eval_homogeneous_quadratic_hessian (A : MvPolynomial (Fin n) ℝ)
    (hA : A.IsHomogeneous 2) (y : Fin n → ℝ) (i j : Fin n) :
    eval y (pderiv i (pderiv j A)) = 2 * quadraticMatrix A i j := by
  rw [QuarticMinimal.second_partial_eq_C_of_totalDegree_le_two A hA.totalDegree_le]
  simp [quadraticMatrix]

theorem eval_homogeneous_quadratic (A : MvPolynomial (Fin n) ℝ)
    (hA : A.IsHomogeneous 2) (y : Fin n → ℝ) :
    eval y A = y ⬝ᵥ (quadraticMatrix A *ᵥ y) := by
  conv_lhs => rw [QuarticMinimal.homogeneous_quadratic_expansion A hA]
  simp only [map_mul, map_sum, eval_C, eval_X, quadraticMatrix, Matrix.smul_mulVec,
    dotProduct_smul, smul_eq_mul]
  congr 1
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem actual_laplacian_matrix_relation
    (P : MvPolynomial (Fin (n + 1)) ℝ) (a : ℝ) (A B D : MvPolynomial (Fin n) ℝ)
    (ha : a ≠ 0) (hA : A.IsHomogeneous 2)
    (hQ : finSuccEquiv ℝ n P = normalForm a A B D)
    (hP : leadingExpression P = 0) (y : Fin n → ℝ) :
    eval y (laplacian D) = y ⬝ᵥ
      ((a⁻¹ • quadraticMatrix A ^ 2 + (2 * a ^ 2)⁻¹ • quadraticMatrix A ^ 3) *ᵥ y) := by
  have hc := laplacian_relation_at P a A B D ha hQ hP y
  simp_rw [eval_homogeneous_quadratic_gradient A hA y,
    eval_homogeneous_quadratic_hessian A hA y] at hc
  rw [HomogeneousQuarticCoefficients.gradient_square_relation (quadraticMatrix A)
      (quadraticMatrix_symmetric A) y,
    HomogeneousQuarticCoefficients.gradient_hessian_relation (quadraticMatrix A)
      (quadraticMatrix_symmetric A) y] at hc
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul]
  field_simp [ha]
  linear_combination (1 / 8 : ℝ) * hc

theorem actual_full_laplacian_at
    (P : MvPolynomial (Fin (n + 1)) ℝ) (a : ℝ) (A B D : MvPolynomial (Fin n) ℝ)
    (ha : a ≠ 0) (hA : A.IsHomogeneous 2)
    (hQ : finSuccEquiv ℝ n P = normalForm a A B D)
    (hP : leadingExpression P = 0) (y : Fin n → ℝ) (t : ℝ) :
    eval (Fin.cons t y) (laplacian P) = 12 * a * t ^ 2 + y ⬝ᵥ
      (((2 : ℝ) • quadraticMatrix A + a⁻¹ • quadraticMatrix A ^ 2 +
        (2 * a ^ 2)⁻¹ • quadraticMatrix A ^ 3) *ᵥ y) := by
  obtain ⟨hAz, hBz, _⟩ := actual_constraints_of_normalForm P a A B D ha hQ hP
  rw [eval_eq_eval_mv_eval' y t,
    finSuccEquiv_laplacian_normalForm P a A B D hQ hAz hBz]
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_C, Polynomial.map_X, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, map_mul, map_add,
    Polynomial.map_ofNat, Polynomial.eval_ofNat, map_ofNat, eval_C]
  rw [eval_homogeneous_quadratic A hA y,
    actual_laplacian_matrix_relation P a A B D ha hA hQ hP y]
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add, dotProduct_smul,
    smul_eq_mul]
  ring

theorem homogeneous_quartic_laplacian_at
    (P : MvPolynomial (Fin (n + 1)) ℝ) (a : ℝ) (ha : a ≠ 0)
    (hP : P.IsHomogeneous 4) (h4 : (finSuccEquiv ℝ n P).coeff 4 = C a)
    (h3 : (finSuccEquiv ℝ n P).coeff 3 = 0) (hL : leadingExpression P = 0)
    (y : Fin n → ℝ) (t : ℝ) :
    let A := (finSuccEquiv ℝ n P).coeff 2
    eval (Fin.cons t y) (laplacian P) = 12 * a * t ^ 2 + y ⬝ᵥ
      (((2 : ℝ) • quadraticMatrix A + a⁻¹ • quadraticMatrix A ^ 2 +
        (2 * a ^ 2)⁻¹ • quadraticMatrix A ^ 3) *ᵥ y) := by
  exact actual_full_laplacian_at P a _ _ _ ha (homogeneous_coefficients P hP).1
    (finSuccEquiv_normalForm P a hP.totalDegree_le h4 h3) hL y t

end QuarticMinimal.QuarticNormalForm
end ComponentQuarticNormalForm


/- Component: AmbientQuartic -/
section ComponentAmbientQuartic

/- Requires ChangeVariables, LinearSubstitution, LowDegree, and QuarticNormalForm. -/
noncomputable section
open scoped BigOperators Matrix
open MvPolynomial
open QuarticMinimal.QuarticNormalForm

namespace QuarticMinimal.AmbientQuartic

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def realHessian (P : MvPolynomial ι ℝ) (x : ι → ℝ) : Matrix ι ι ℝ :=
  (QuarticMinimal.hessian P).map (eval x)

omit [Fintype ι] in
theorem realHessian_apply (P : MvPolynomial ι ℝ) (x : ι → ℝ) (i j : ι) :
    realHessian P x i j = eval x (pderiv i (pderiv j P)) := rfl

omit [Fintype ι] in
theorem realHessian_symmetric (P : MvPolynomial ι ℝ) (x : ι → ℝ) :
    (realHessian P x).IsSymm := by
  ext i j
  simp only [realHessian_apply, Matrix.transpose_apply]
  rw [QuarticPolynomialBasics.second_partial_comm]

omit [Fintype ι] in
theorem realHessian_zero (P : MvPolynomial ι ℝ) :
    realHessian P 0 = QuarticMinimal.hessianCoeff P := by
  ext i j
  simp only [realHessian_apply, eval_zero, constantCoeff_eq, QuarticMinimal.hessianCoeff]

theorem realHessian_changeVariables (U : Matrix ι κ ℝ) (P : MvPolynomial ι ℝ) (x : κ → ℝ) :
    realHessian (changeVariables U P) x = U.transpose * realHessian P (U *ᵥ x) * U := by
  ext j k
  simp only [realHessian_apply, pderiv_pderiv_changeVariables, map_sum, map_mul,
    eval_changeVariables, eval_C, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem hessianCoeff_changeVariables (U : Matrix ι κ ℝ) (P : MvPolynomial ι ℝ) :
    hessianCoeff (changeVariables U P) = U.transpose * hessianCoeff P * U := by
  have h := realHessian_changeVariables U P 0
  simpa only [Matrix.mulVec_zero, realHessian_zero] using h

variable {n m : ℕ}

theorem quadraticMatrix_changeVariables (U : Matrix (Fin n) (Fin m) ℝ)
    (P : MvPolynomial (Fin n) ℝ) :
    quadraticMatrix (changeVariables U P) = U.transpose * quadraticMatrix P * U := by
  rw [quadraticMatrix, hessianCoeff_changeVariables, quadraticMatrix]
  simp only [Matrix.mul_smul, Matrix.smul_mul]

def canonicalS (P : MvPolynomial ι ℝ) (a : ℝ) (e : ι → ℝ) : Matrix ι ι ℝ :=
  (1 / 2 : ℝ) • realHessian P e - (6 * a) • Matrix.vecMulVec e e

omit [Fintype ι] in
theorem canonicalS_symmetric (P : MvPolynomial ι ℝ) (a : ℝ) (e : ι → ℝ) :
    (canonicalS P a e).IsSymm := by
  apply Matrix.IsSymm.sub ((realHessian_symmetric P e).smul _)
  apply Matrix.IsSymm.smul
  ext i j
  simp only [Matrix.transpose_apply, Matrix.vecMulVec_apply]
  ring

omit [Fintype κ] in
theorem outer_conjugate (U : Matrix ι κ ℝ) (e : ι → ℝ) :
    U.transpose * Matrix.vecMulVec e e * U =
      Matrix.vecMulVec (U.transpose *ᵥ e) (U.transpose *ᵥ e) := by
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, ← Matrix.mulVec_transpose]

theorem canonicalS_changeVariables [DecidableEq ι]
    (U : Matrix ι ι ℝ) (hU : U * U.transpose = 1)
    (P : MvPolynomial ι ℝ) (a : ℝ) (x : ι → ℝ) :
    canonicalS (changeVariables U P) a x =
      U.transpose * canonicalS P a (U *ᵥ x) * U := by
  have hUt : U.transpose * U = 1 := mul_eq_one_comm.mp hU
  simp only [canonicalS, realHessian_changeVariables, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_smul, Matrix.smul_mul, outer_conjugate]
  rw [Matrix.mulVec_mulVec, hUt, Matrix.one_mulVec]

theorem symmetric_matrix_ext [DecidableEq ι] (A B : Matrix ι ι ℝ)
    (hA : A.IsSymm) (hB : B.IsSymm)
    (h : ∀ x, x ⬝ᵥ (A *ᵥ x) = x ⬝ᵥ (B *ᵥ x)) : A = B := by
  ext i j
  have hi := h (Pi.single i 1)
  have hj := h (Pi.single j 1)
  have hij := h (Pi.single i 1 + Pi.single j 1)
  simp only [Matrix.mulVec_single_one, single_one_dotProduct] at hi hj
  simp only [Matrix.mulVec_add, dotProduct_add, add_dotProduct,
    Matrix.mulVec_single_one, single_one_dotProduct] at hij
  change A i i = B i i at hi
  change A j j = B j j at hj
  change A i i + A j i + (A i j + A j j) =
    B i i + B j i + (B i j + B j j) at hij
  rw [hA.apply i j, hB.apply i j] at hij
  linarith

theorem conjugate_mul [DecidableEq ι] (U S T : Matrix ι ι ℝ)
    (hU : U * U.transpose = 1) :
    (U.transpose * S * U) * (U.transpose * T * U) = U.transpose * (S * T) * U := by
  calc
    _ = U.transpose * S * (U * U.transpose) * T * U := by noncomm_ring
    _ = _ := by rw [hU]; simp only [Matrix.mul_one, Matrix.mul_assoc]

theorem conjugate_pow [DecidableEq ι] (U S : Matrix ι ι ℝ)
    (hU : U * U.transpose = 1) (k : ℕ) :
    (U.transpose * S * U) ^ k = U.transpose * S ^ k * U := by
  have hUt : U.transpose * U = 1 := mul_eq_one_comm.mp hU
  induction k with
  | zero => simp [hUt]
  | succ k hk => rw [pow_succ, hk, conjugate_mul U (S ^ k) S hU, pow_succ]

def cubicMatrix [DecidableEq ι] (a : ℝ) (S : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  (2 : ℝ) • S + a⁻¹ • S ^ 2 + (2 * a ^ 2)⁻¹ • S ^ 3

theorem cubicMatrix_symmetric [DecidableEq ι] (a : ℝ) (S : Matrix ι ι ℝ)
    (hS : S.IsSymm) : (cubicMatrix a S).IsSymm :=
  ((hS.smul _).add ((hS.pow 2).smul _)).add ((hS.pow 3).smul _)

theorem cubicMatrix_conjugate [DecidableEq ι] (a : ℝ) (U S : Matrix ι ι ℝ)
    (hU : U * U.transpose = 1) :
    cubicMatrix a (U.transpose * S * U) = U.transpose * cubicMatrix a S * U := by
  simp only [cubicMatrix, conjugate_pow U S hU, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_smul, Matrix.smul_mul]

def axis (n : ℕ) : Fin (n + 1) → ℝ := Fin.cons 1 0

def liftMatrix (S : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun i j => Fin.cases 0 (fun i => Fin.cases 0 (fun j => S i j) j) i

theorem liftMatrix_symmetric (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.IsSymm) :
    (liftMatrix S).IsSymm := by
  ext i j
  cases i using Fin.cases <;> cases j using Fin.cases <;>
    simp [liftMatrix, Matrix.transpose_apply, hS.apply]

theorem liftMatrix_mulVec (S : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) (y : Fin n → ℝ) :
    liftMatrix S *ᵥ Fin.cons t y = Fin.cons 0 (S *ᵥ y) := by
  funext i
  cases i using Fin.cases <;> simp [liftMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem liftMatrix_quadratic (S : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) (y : Fin n → ℝ) :
    (Fin.cons t y) ⬝ᵥ (liftMatrix S *ᵥ Fin.cons t y) = y ⬝ᵥ (S *ᵥ y) := by
  rw [liftMatrix_mulVec]
  simp [dotProduct, Fin.sum_univ_succ]

theorem outer_mulVec (e x : ι → ℝ) :
    Matrix.vecMulVec e e *ᵥ x = (e ⬝ᵥ x) • e := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem outer_quadratic (e x : ι → ℝ) :
    x ⬝ᵥ (Matrix.vecMulVec e e *ᵥ x) = (e ⬝ᵥ x) ^ 2 := by
  rw [outer_mulVec, dotProduct_smul, dotProduct_comm x e]
  simp only [smul_eq_mul, pow_two]

theorem axis_dot_cons (t : ℝ) (y : Fin n → ℝ) :
    axis n ⬝ᵥ Fin.cons t y = t := by
  simp [axis, dotProduct, Fin.sum_univ_succ]

theorem liftMatrix_mul (S T : Matrix (Fin n) (Fin n) ℝ) :
    liftMatrix (S * T) = liftMatrix S * liftMatrix T := by
  ext i j
  cases i using Fin.cases <;> cases j using Fin.cases <;>
    simp [liftMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

theorem liftMatrix_add (S T : Matrix (Fin n) (Fin n) ℝ) :
    liftMatrix (S + T) = liftMatrix S + liftMatrix T := by
  ext i j
  cases i using Fin.cases <;> cases j using Fin.cases <;> simp [liftMatrix]

theorem liftMatrix_smul (r : ℝ) (S : Matrix (Fin n) (Fin n) ℝ) :
    liftMatrix (r • S) = r • liftMatrix S := by
  ext i j
  cases i using Fin.cases <;> cases j using Fin.cases <;> simp [liftMatrix]

theorem cubicMatrix_lift (a : ℝ) (S : Matrix (Fin n) (Fin n) ℝ) :
    cubicMatrix a (liftMatrix S) = liftMatrix (cubicMatrix a S) := by
  simp only [cubicMatrix, pow_succ, pow_zero, Matrix.one_mul, ← liftMatrix_mul,
    liftMatrix_add, liftMatrix_smul]

omit [Fintype ι] in
theorem eval_zero_of_homogeneous (P : MvPolynomial ι ℝ) {d : ℕ}
    (hP : P.IsHomogeneous d) (hd : 0 < d) : eval 0 P = 0 := by
  rw [eval_zero, constantCoeff_eq]
  exact hP.coeff_eq_zero (by simp; omega)

theorem realHessian_normalForm_zero_zero
    (P : MvPolynomial (Fin (n + 1)) ℝ) (a : ℝ) (A B D : MvPolynomial (Fin n) ℝ)
    (hQ : finSuccEquiv ℝ n P = normalForm a A B D) (t : ℝ) (y : Fin n → ℝ) :
    realHessian P (Fin.cons t y) 0 0 = 12 * a * t ^ 2 + 2 * eval y A := by
  rw [realHessian_apply, eval_eq_eval_mv_eval' y t,
    DistinguishedVariable.finSuccEquiv_pderiv_zero_zero, hQ, second_derivative_normalForm]
  simp [HomogeneousQuarticCoefficients.longitudinalSecond, Polynomial.C_ofNat]

theorem realHessian_normalForm_zero_succ
    (P : MvPolynomial (Fin (n + 1)) ℝ) (a : ℝ) (A B D : MvPolynomial (Fin n) ℝ)
    (hQ : finSuccEquiv ℝ n P = normalForm a A B D) (t : ℝ) (y : Fin n → ℝ) (j : Fin n) :
    realHessian P (Fin.cons t y) 0 j.succ =
      2 * eval y (pderiv j A) * t + eval y (pderiv j B) := by
  rw [realHessian_apply, eval_eq_eval_mv_eval' y t,
    DistinguishedVariable.finSuccEquiv_pderiv_zero, DistinguishedVariable.finSuccEquiv_pderiv_succ,
    hQ, coefficientPartial_normalForm, derivative_transverse]
  simp [HomogeneousQuarticCoefficients.mixedSecond, Polynomial.C_ofNat]

theorem realHessian_normalForm_succ_succ
    (P : MvPolynomial (Fin (n + 1)) ℝ) (a : ℝ) (A B D : MvPolynomial (Fin n) ℝ)
    (hQ : finSuccEquiv ℝ n P = normalForm a A B D) (t : ℝ) (y : Fin n → ℝ) (i j : Fin n) :
    realHessian P (Fin.cons t y) i.succ j.succ =
      eval y (pderiv i (pderiv j A)) * t ^ 2 +
      eval y (pderiv i (pderiv j B)) * t + eval y (pderiv i (pderiv j D)) := by
  rw [realHessian_apply, eval_eq_eval_mv_eval' y t,
    DistinguishedVariable.finSuccEquiv_pderiv_succ, DistinguishedVariable.finSuccEquiv_pderiv_succ,
    hQ, coefficientPartial_normalForm, coefficientPartial_transverse]
  simp [HomogeneousQuarticCoefficients.transverse]

theorem realHessian_at_axis
    (P : MvPolynomial (Fin (n + 1)) ℝ) (a : ℝ) (A B D : MvPolynomial (Fin n) ℝ)
    (hA : A.IsHomogeneous 2) (hB : B.IsHomogeneous 3) (hD : D.IsHomogeneous 4)
    (hQ : finSuccEquiv ℝ n P = normalForm a A B D) :
    realHessian P (axis n) = (12 * a) • Matrix.vecMulVec (axis n) (axis n) +
      (2 : ℝ) • liftMatrix (quadraticMatrix A) := by
  have h00 : realHessian P (axis n) 0 0 = 12 * a := by
    rw [axis, realHessian_normalForm_zero_zero P a A B D hQ]
    rw [eval_zero_of_homogeneous A hA (by decide)]
    ring
  have h0j (j : Fin n) : realHessian P (axis n) 0 j.succ = 0 := by
    rw [axis, realHessian_normalForm_zero_succ P a A B D hQ]
    rw [eval_zero_of_homogeneous (pderiv j A) (QuarticCompatibility.homogeneous_pderiv hA) (by decide),
      eval_zero_of_homogeneous (pderiv j B) (QuarticCompatibility.homogeneous_pderiv hB) (by decide)]
    ring
  have hij (i j : Fin n) :
      realHessian P (axis n) i.succ j.succ = 2 * quadraticMatrix A i j := by
    rw [axis, realHessian_normalForm_succ_succ P a A B D hQ]
    rw [eval_zero_of_homogeneous (pderiv i (pderiv j B))
        (QuarticCompatibility.homogeneous_pderiv (QuarticCompatibility.homogeneous_pderiv hB)) (by decide),
      eval_zero_of_homogeneous (pderiv i (pderiv j D))
        (QuarticCompatibility.homogeneous_pderiv (QuarticCompatibility.homogeneous_pderiv hD)) (by decide),
      eval_homogeneous_quadratic_hessian A hA]
    ring
  ext i j
  cases i using Fin.cases <;> cases j using Fin.cases
  · simpa [axis, liftMatrix, Matrix.vecMulVec_apply] using h00
  · simpa [axis, liftMatrix, Matrix.vecMulVec_apply] using h0j _
  · rw [(realHessian_symmetric P (axis n)).apply 0]
    simpa [axis, liftMatrix, Matrix.vecMulVec_apply] using h0j _
  · simpa [axis, liftMatrix, Matrix.vecMulVec_apply] using hij _ _

theorem canonicalS_at_axis
    (P : MvPolynomial (Fin (n + 1)) ℝ) (a : ℝ) (A B D : MvPolynomial (Fin n) ℝ)
    (hA : A.IsHomogeneous 2) (hB : B.IsHomogeneous 3) (hD : D.IsHomogeneous 4)
    (hQ : finSuccEquiv ℝ n P = normalForm a A B D) :
    canonicalS P a (axis n) = liftMatrix (quadraticMatrix A) := by
  rw [canonicalS, realHessian_at_axis P a A B D hA hB hD hQ]
  ext i j
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

omit [Fintype ι] in
theorem outer_symmetric (e : ι → ℝ) : (Matrix.vecMulVec e e).IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply, Matrix.vecMulVec_apply]
  ring

theorem laplacian_isHomogeneous (P : MvPolynomial (Fin n) ℝ) (hP : P.IsHomogeneous 4) :
    (QuarticNormalForm.laplacian P).IsHomogeneous 2 := by
  unfold QuarticNormalForm.laplacian
  apply IsHomogeneous.sum
  intro i _
  simpa using QuarticCompatibility.homogeneous_pderiv (i := i)
    (QuarticCompatibility.homogeneous_pderiv hP)

theorem local_Q_normalForm
    (P : MvPolynomial (Fin (n + 1)) ℝ) (a : ℝ) (A B D : MvPolynomial (Fin n) ℝ)
    (ha : a ≠ 0) (hP : P.IsHomogeneous 4) (hA : A.IsHomogeneous 2)
    (hQ : finSuccEquiv ℝ n P = normalForm a A B D)
    (hL : leadingExpression P = 0) :
    quadraticMatrix (QuarticNormalForm.laplacian P) =
      (12 * a) • Matrix.vecMulVec (axis n) (axis n) +
        liftMatrix (cubicMatrix a (quadraticMatrix A)) := by
  apply symmetric_matrix_ext _ _ (quadraticMatrix_symmetric _)
    (((outer_symmetric (axis n)).smul _).add
      (liftMatrix_symmetric _ (cubicMatrix_symmetric _ _ (quadraticMatrix_symmetric _))))
  intro x
  have hx : x = Fin.cons (x 0) (fun i => x i.succ) := by
    funext i
    cases i using Fin.cases <;> rfl
  rw [hx, ← eval_homogeneous_quadratic _ (laplacian_isHomogeneous P hP)]
  rw [actual_full_laplacian_at P a A B D ha hA hQ hL]
  simp only [cubicMatrix, Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add, dotProduct_smul,
    outer_quadratic, axis_dot_cons, liftMatrix_quadratic, smul_eq_mul]

theorem local_Q_canonical
    (P : MvPolynomial (Fin (n + 1)) ℝ) (a : ℝ) (ha : a ≠ 0)
    (hP : P.IsHomogeneous 4) (h4 : (finSuccEquiv ℝ n P).coeff 4 = C a)
    (h3 : (finSuccEquiv ℝ n P).coeff 3 = 0) (hL : leadingExpression P = 0) :
    quadraticMatrix (QuarticNormalForm.laplacian P) =
      (12 * a) • Matrix.vecMulVec (axis n) (axis n) + cubicMatrix a (canonicalS P a (axis n)) := by
  obtain ⟨hA, hB, hD⟩ := homogeneous_coefficients P hP
  have hQ := finSuccEquiv_normalForm P a hP.totalDegree_le h4 h3
  rw [local_Q_normalForm P a _ _ _ ha hP hA hQ hL,
    canonicalS_at_axis P a _ _ _ hA hB hD hQ, cubicMatrix_lift]

theorem conjugate_injective [DecidableEq ι] (U : Matrix ι ι ℝ)
    (hU : U * U.transpose = 1) :
    Function.Injective (fun M : Matrix ι ι ℝ => U.transpose * M * U) := by
  intro A B h
  have hh := congrArg (fun M => U * M * U.transpose) h
  have hc (M : Matrix ι ι ℝ) : U * (U.transpose * M * U) * U.transpose = M := by
    calc
      _ = (U * U.transpose) * M * (U * U.transpose) := by noncomm_ring
      _ = M := by rw [hU]; simp
  simpa only [hc] using hh

theorem ambient_Q_identity
    (P : MvPolynomial (Fin (n + 1)) ℝ) (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hU : U * U.transpose = 1) (a : ℝ) (ha : a ≠ 0) (hP : P.IsHomogeneous 4)
    (h4 : (finSuccEquiv ℝ n (changeVariables U P)).coeff 4 = C a)
    (h3 : (finSuccEquiv ℝ n (changeVariables U P)).coeff 3 = 0)
    (hL : leadingExpression P = 0) :
    quadraticMatrix (QuarticNormalForm.laplacian P) =
      (12 * a) • Matrix.vecMulVec (U *ᵥ axis n) (U *ᵥ axis n) +
        cubicMatrix a (canonicalS P a (U *ᵥ axis n)) := by
  have hUt : U.transpose * U = 1 := mul_eq_one_comm.mp hU
  have hR := isHomogeneous_changeVariables U P 4 hP
  have hLR : leadingExpression (changeVariables U P) = 0 :=
    leadingOperator_changeVariables_eq_zero U hU P hL
  have hh := local_Q_canonical (changeVariables U P) a ha hR h4 h3 hLR
  have hLap : QuarticNormalForm.laplacian (changeVariables U P) =
      changeVariables U (QuarticNormalForm.laplacian P) :=
    laplacian_changeVariables U hU P
  rw [hLap, quadraticMatrix_changeVariables,
    canonicalS_changeVariables U hU, cubicMatrix_conjugate a U _ hU] at hh
  apply conjugate_injective U hU
  dsimp only
  rw [hh]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, outer_conjugate]
  rw [Matrix.mulVec_mulVec, hUt, Matrix.one_mulVec]

theorem canonicalS_axis_kernel
    (P : MvPolynomial (Fin (n + 1)) ℝ) (a : ℝ)
    (hP : P.IsHomogeneous 4) (h4 : (finSuccEquiv ℝ n P).coeff 4 = C a)
    (h3 : (finSuccEquiv ℝ n P).coeff 3 = 0) :
    canonicalS P a (axis n) *ᵥ axis n = 0 := by
  obtain ⟨hA, hB, hD⟩ := homogeneous_coefficients P hP
  have hQ := finSuccEquiv_normalForm P a hP.totalDegree_le h4 h3
  rw [canonicalS_at_axis P a _ _ _ hA hB hD hQ, axis, liftMatrix_mulVec]
  simp only [Matrix.mulVec_zero]
  funext i
  cases i using Fin.cases <;> rfl

theorem canonicalS_ambient_kernel
    (P : MvPolynomial (Fin (n + 1)) ℝ) (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hU : U * U.transpose = 1) (a : ℝ) (hP : P.IsHomogeneous 4)
    (h4 : (finSuccEquiv ℝ n (changeVariables U P)).coeff 4 = C a)
    (h3 : (finSuccEquiv ℝ n (changeVariables U P)).coeff 3 = 0) :
    canonicalS P a (U *ᵥ axis n) *ᵥ (U *ᵥ axis n) = 0 := by
  have hk := canonicalS_axis_kernel (changeVariables U P) a
    (isHomogeneous_changeVariables U P 4 hP) h4 h3
  rw [canonicalS_changeVariables U hU] at hk
  have hv : U.transpose *ᵥ (canonicalS P a (U *ᵥ axis n) *ᵥ (U *ᵥ axis n)) = 0 := by
    simpa only [Matrix.mulVec_mulVec, Matrix.mul_assoc] using hk
  have hh := congrArg (fun v => U *ᵥ v) hv
  rwa [Matrix.mulVec_mulVec, hU, Matrix.one_mulVec, Matrix.mulVec_zero] at hh

theorem ambient_axis_unit (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hU : U * U.transpose = 1) : (U *ᵥ axis n) ⬝ᵥ (U *ᵥ axis n) = 1 := by
  have hUt : U.transpose * U = 1 := mul_eq_one_comm.mp hU
  have h := MatrixAlgebra.dot_transpose_mulVec U.transpose (by simpa using hUt) (axis n) (axis n)
  have hn : axis n ⬝ᵥ axis n = 1 := axis_dot_cons 1 0
  simpa only [Matrix.transpose_transpose, hn] using h

theorem cubicMatrix_kernel [DecidableEq ι] (a : ℝ) (S : Matrix ι ι ℝ) (v : ι → ℝ)
    (hS : S *ᵥ v = 0) : cubicMatrix a S *ᵥ v = 0 := by
  simp [cubicMatrix, Matrix.add_mulVec, Matrix.smul_mulVec, pow_succ,
    ← Matrix.mulVec_mulVec, hS]

theorem ambient_Q_action
    (P : MvPolynomial (Fin (n + 1)) ℝ) (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hU : U * U.transpose = 1) (a : ℝ) (ha : a ≠ 0) (hP : P.IsHomogeneous 4)
    (h4 : (finSuccEquiv ℝ n (changeVariables U P)).coeff 4 = C a)
    (h3 : (finSuccEquiv ℝ n (changeVariables U P)).coeff 3 = 0)
    (hL : leadingExpression P = 0) :
    let e := U *ᵥ axis n
    let Q := quadraticMatrix (QuarticNormalForm.laplacian P)
    let S := canonicalS P a e
    Q *ᵥ e = (12 * a) • e ∧ ∀ v, e ⬝ᵥ v = 0 → cubicMatrix a S *ᵥ v = Q *ᵥ v := by
  dsimp only
  have hQ := ambient_Q_identity P U hU a ha hP h4 h3 hL
  constructor
  · rw [hQ, Matrix.add_mulVec, Matrix.smul_mulVec, outer_mulVec,
      ambient_axis_unit U hU, one_smul,
      cubicMatrix_kernel a _ _ (canonicalS_ambient_kernel P U hU a hP h4 h3), add_zero]
  · intro v hv
    rw [hQ, Matrix.add_mulVec, Matrix.smul_mulVec, outer_mulVec, hv, zero_smul,
      smul_zero, zero_add]

theorem realHessian_mixed_symmetry (P : MvPolynomial ι ℝ)
    (hP : P.IsHomogeneous 4) (e f : ι → ℝ) :
    f ⬝ᵥ (realHessian P e *ᵥ f) = e ⬝ᵥ (realHessian P f *ᵥ e) := by
  have hm := QuarticMinimal.quartic_mixed_hessian_symmetry P hP e f
  change (∑ i, ∑ j, f i * f j * realHessian P e i j) =
    ∑ i, ∑ j, e i * e j * realHessian P f i j at hm
  simpa only [HomogeneousQuarticCoefficients.sum_pairing_eq_dot] using hm

theorem canonicalS_mixed_symmetry (P : MvPolynomial ι ℝ)
    (hP : P.IsHomogeneous 4) (a b : ℝ) (e f : ι → ℝ) (hef : e ⬝ᵥ f = 0) :
    f ⬝ᵥ (canonicalS P a e *ᵥ f) = e ⬝ᵥ (canonicalS P b f *ᵥ e) := by
  have hfe : f ⬝ᵥ e = 0 := by rw [dotProduct_comm, hef]
  simp only [canonicalS, Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub,
    dotProduct_smul, outer_quadratic, smul_eq_mul, hef, hfe, zero_pow (by decide : 2 ≠ 0),
    mul_zero, sub_zero]
  rw [realHessian_mixed_symmetry P hP e f]

end QuarticMinimal.AmbientQuartic
end

end ComponentAmbientQuartic


/- Component: OrthogonalNormalization -/
section ComponentOrthogonalNormalization

noncomputable section

open scoped BigOperators Matrix
open MvPolynomial

namespace QuarticNormalization

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A Euclidean unit vector may be chosen as any specified column of an
orthogonal matrix. The convention is that new coordinates `x` map to `A *ᵥ x`. -/
theorem exists_orthogonal_with_column (j : ι) (e : ι → ℝ)
    (he : ∑ i, (e i) ^ 2 = 1) :
    ∃ A : Matrix ι ι ℝ, A.transpose * A = 1 ∧ A * A.transpose = 1 ∧
      ∀ i, A i j = e i := by
  let b := EuclideanSpace.basisFun ι ℝ
  let w : EuclideanSpace ℝ ι := WithLp.toLp 2 e
  have hw : ‖w‖ = 1 := by
    have h := EuclideanSpace.real_norm_sq_eq w
    have hh : ‖w‖ ^ 2 = 1 := by simpa [w, he] using h
    nlinarith [norm_nonneg w]
  let R := Submodule.reflection (ℝ ∙ (b j - w))ᗮ
  have hR : R (b j) = w :=
    Submodule.reflection_sub (by rw [b.norm_eq_one, hw])
  let c := b.map R
  let A : Matrix ι ι ℝ := b.toBasis.toMatrix c
  refine ⟨A, ?_, ?_, ?_⟩
  · simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      b.toMatrix_orthonormalBasis_conjTranspose_mul_self c
  · simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      b.toMatrix_orthonormalBasis_self_mul_conjTranspose c
  · intro i
    change b.toBasis.repr (R (b j)) i = e i
    rw [hR]
    rfl

omit [DecidableEq ι] in
/-- The Euclidean unit sphere is compact in the ordinary finite function-space topology. -/
theorem isCompact_coordinate_sphere :
    IsCompact {x : ι → ℝ | ∑ i, (x i) ^ 2 = 1} := by
  have hc : IsClosed {x : ι → ℝ | ∑ i, (x i) ^ 2 = 1} := by
    apply isClosed_eq <;> fun_prop
  apply (isCompact_Icc : IsCompact (Set.Icc (fun _ : ι => (-1 : ℝ)) (fun _ => 1))).of_isClosed_subset hc
  intro x hx
  constructor <;> intro i
  · have hi : (x i) ^ 2 ≤ ∑ j, (x j) ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    change ∑ j, (x j) ^ 2 = 1 at hx
    nlinarith
  · have hi : (x i) ^ 2 ≤ ∑ j, (x j) ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    change ∑ j, (x j) ^ 2 = 1 at hx
    nlinarith

omit [DecidableEq ι] in
/-- Every polynomial with a positive value on the sphere has a positive spherical maximum. -/
theorem exists_positive_sphere_maximum (P : MvPolynomial ι ℝ)
    (y : ι → ℝ) (hy : ∑ i, (y i) ^ 2 = 1) (hPy : 0 < eval y P) :
    ∃ e : ι → ℝ, (∑ i, (e i) ^ 2 = 1) ∧ 0 < eval e P ∧
      IsLocalExtrOn (fun x : ι → ℝ => eval x P) {x | ∑ i, (x i) ^ 2 = 1} e := by
  obtain ⟨e, he, hmax⟩ := isCompact_coordinate_sphere.exists_isMaxOn
    ⟨y, hy⟩ (QuarticPolynomialBasics.differentiable_eval P).continuous.continuousOn
  exact ⟨e, he, lt_of_lt_of_le hPy (hmax hy), Or.inr hmax.isLocalMaxOn⟩

omit [DecidableEq ι] in
/-- Substitution by a matrix evaluates as multiplication by that matrix. -/
theorem eval_changeVariables (A : Matrix ι ι ℝ) (P : MvPolynomial ι ℝ) (x : ι → ℝ) :
    eval x (QuarticMinimal.changeVariables A P) = eval (A *ᵥ x) P := by
  induction P using MvPolynomial.induction_on with
  | C r => simp [QuarticMinimal.changeVariables]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
    simp only [map_mul, hP]
    congr 1
    simp [QuarticMinimal.changeVariables, QuarticMinimal.linearSubstitution,
      Matrix.mulVec, dotProduct]

omit [DecidableEq ι] in
theorem isHomogeneous_changeVariables (A : Matrix ι ι ℝ)
    (P : MvPolynomial ι ℝ) (d : ℕ) (hP : P.IsHomogeneous d) :
    (QuarticMinimal.changeVariables A P).IsHomogeneous d := by
  simpa only [QuarticMinimal.changeVariables, one_mul] using hP.aeval
    (QuarticMinimal.linearSubstitution A) (fun i =>
      IsHomogeneous.sum _ _ _ (fun j _ => isHomogeneous_C_mul_X (A i j) j))

/-- A critical direction becomes the selected coordinate axis; all tangential
first derivatives vanish there. -/
theorem normalized_gradient (P : MvPolynomial ι ℝ) (e : ι → ℝ)
    (j : ι) (A : Matrix ι ι ℝ) (hA : A.transpose * A = 1)
    (hcol : ∀ i, A i j = e i) (c : ℝ)
    (hg : ∀ i, eval e (pderiv i P) = c * e i) :
    ∀ k, eval (Pi.single j 1) (pderiv k (QuarticMinimal.changeVariables A P)) =
      if j = k then c else 0 := by
  intro k
  have hx : A *ᵥ Pi.single j 1 = e := by
    ext i
    simp [Matrix.mulVec, dotProduct, Pi.single_apply, hcol]
  have hik := congrArg (fun B : Matrix ι ι ℝ => B j k) hA
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] at hik
  simp only [QuarticMinimal.pderiv_changeVariables, map_sum, map_mul,
    eval_changeVariables, hx, hg, eval_C]
  simp_rw [← hcol, mul_assoc]
  rw [← Finset.mul_sum, hik]
  split_ifs <;> simp_all

/-- Evaluating a homogeneous polynomial at a coordinate unit vector extracts
its pure-power coefficient. -/
theorem eval_basis_of_isHomogeneous (P : MvPolynomial ι ℝ) (d : ℕ)
    (hP : P.IsHomogeneous d) (j : ι) :
    eval (Pi.single j 1) P = P.coeff (Finsupp.single j d) := by
  rw [eval_eq']
  rw [Finset.sum_eq_single (Finsupp.single j d)]
  · have hprod : (∏ i, (Pi.single j (1 : ℝ) i) ^ (Finsupp.single j d i)) = (1 : ℝ) := by
      apply Finset.prod_eq_one
      intro i _
      by_cases hi : i = j
      · subst i; simp
      · simp [hi]
    rw [hprod, mul_one]
  · intro r hr hne
    have hd : r.degree = d := by
      simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hP (mem_support_iff.mp hr)
    have hex : ∃ i, i ≠ j ∧ r i ≠ 0 := by
      by_contra h
      push Not at h
      have heq : r = Finsupp.single j (r j) := by
        ext i
        by_cases hi : i = j
        · subst i; simp
        · simp [h i hi, Ne.symm hi]
      have hd' : r j = d := by
        have hh := congrArg (fun r : ι →₀ ℕ => r.degree) heq
        rw [Finsupp.degree_single] at hh
        exact hh.symm.trans hd
      exact hne (heq.trans (congrArg (Finsupp.single j) hd'))
    obtain ⟨i, hij, hri⟩ := hex
    have hz : (∏ k, (Pi.single j (1 : ℝ) k) ^ (r k)) = (0 : ℝ) := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [Ne.symm hij, hri]
    rw [hz, mul_zero]
  · intro hn
    have hz : P.coeff (Finsupp.single j d) = 0 := by
      by_contra hh
      exact hn (mem_support_iff.mpr hh)
    simp only [hz, zero_mul]

/-- A tangential derivative on the coordinate axis extracts the coefficient
of the monomial with one tangential variable. -/
theorem eval_pderiv_basis_of_isHomogeneous (P : MvPolynomial ι ℝ) (d : ℕ)
    (hP : P.IsHomogeneous (d + 1)) (j k : ι) (hjk : j ≠ k) :
    eval (Pi.single j 1) (pderiv k P) =
      P.coeff (Finsupp.single j d + Finsupp.single k 1) := by
  rw [eval_basis_of_isHomogeneous (pderiv k P) d
    (QuarticPolynomialBasics.isHomogeneous_pderiv_succ P k d hP) j, coeff_pderiv]
  simp [hjk]

theorem normalized_tangential_coeff_zero (P : MvPolynomial ι ℝ) (d : ℕ)
    (hP : P.IsHomogeneous (d + 1)) (e : ι → ℝ) (j : ι)
    (A : Matrix ι ι ℝ) (hA : A.transpose * A = 1)
    (hcol : ∀ i, A i j = e i) (c : ℝ)
    (hg : ∀ i, eval e (pderiv i P) = c * e i) :
    ∀ k, j ≠ k → (QuarticMinimal.changeVariables A P).coeff
      (Finsupp.single j d + Finsupp.single k 1) = 0 := by
  intro k hjk
  have hh := normalized_gradient P e j A hA hcol c hg k
  rw [eval_pderiv_basis_of_isHomogeneous _ d
    (isHomogeneous_changeVariables A P (d + 1) hP) j k hjk] at hh
  simpa [hjk] using hh

/-- Normal form at a positive spherical maximum, including the vanishing of
all coefficients with exactly one tangential variable. -/
theorem exists_normalized_positive_direction (P : MvPolynomial ι ℝ) (d : ℕ)
    (hP : P.IsHomogeneous (d + 1)) (j : ι)
    (y : ι → ℝ) (hy : ∑ i, (y i) ^ 2 = 1) (hPy : 0 < eval y P) :
    ∃ A : Matrix ι ι ℝ, A.transpose * A = 1 ∧ A * A.transpose = 1 ∧
      0 < (QuarticMinimal.changeVariables A P).coeff (Finsupp.single j (d + 1)) ∧
      ∀ k, j ≠ k → (QuarticMinimal.changeVariables A P).coeff
        (Finsupp.single j d + Finsupp.single k 1) = 0 := by
  obtain ⟨e, he, hPe, hmax⟩ := exists_positive_sphere_maximum P y hy hPy
  obtain ⟨A, hA, hA', hcol⟩ := exists_orthogonal_with_column j e he
  refine ⟨A, hA, hA', ?_, ?_⟩
  · rw [← eval_basis_of_isHomogeneous _ (d + 1)
      (isHomogeneous_changeVariables A P (d + 1) hP) j, eval_changeVariables]
    have hx : A *ᵥ Pi.single j 1 = e := by
      ext i
      simp [Matrix.mulVec, dotProduct, Pi.single_apply, hcol]
    simpa only [hx] using hPe
  · exact normalized_tangential_coeff_zero P d hP e j A hA hcol
      ((d + 1 : ℕ) * eval e P)
      (QuarticPolynomialBasics.gradient_at_homogeneous_sphere_extremum P (d + 1) hP e he hmax)

omit [Fintype ι] [DecidableEq ι] in
/-- Real homogeneity as a scaling identity for polynomial evaluation. -/
theorem eval_scale_of_isHomogeneous (P : MvPolynomial ι ℝ) (d : ℕ)
    (hP : P.IsHomogeneous d) (x : ι → ℝ) (c : ℝ) :
    eval (fun i => c * x i) P = c ^ d * eval x P := by
  rw [eval_eq, eval_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    ← hP.degree_eq_sum_deg_support hr]
  ring

omit [DecidableEq ι] in
/-- A positive value of a positive-degree homogeneous polynomial can be
moved to the Euclidean unit sphere by a positive scaling. -/
theorem exists_positive_sphere_value (P : MvPolynomial ι ℝ) (d : ℕ)
    (hP : P.IsHomogeneous (d + 1)) (x : ι → ℝ) (hPx : 0 < eval x P) :
    ∃ y : ι → ℝ, (∑ i, (y i) ^ 2 = 1) ∧ 0 < eval y P := by
  have hzero : eval (0 : ι → ℝ) P = 0 := by
    simpa using eval_scale_of_isHomogeneous P (d + 1) hP x 0
  have hx : x ≠ 0 := by
    intro hh
    rw [hh, hzero] at hPx
    exact (lt_irrefl 0) hPx
  have hsnonneg : 0 ≤ ∑ i, (x i) ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg (x i))
  have hsne : (∑ i, (x i) ^ 2) ≠ 0 := by
    intro hh
    apply hx
    ext i
    have hi : (x i) ^ 2 ≤ ∑ j, (x j) ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    simp only [Pi.zero_apply]
    nlinarith
  let r := Real.sqrt (∑ i, (x i) ^ 2)
  have hr : 0 < r := Real.sqrt_pos.mpr (lt_of_le_of_ne hsnonneg (Ne.symm hsne))
  have hr2 : r ^ 2 = ∑ i, (x i) ^ 2 := Real.sq_sqrt hsnonneg
  refine ⟨fun i => r⁻¹ * x i, ?_, ?_⟩
  · simp only [mul_pow, ← Finset.mul_sum, inv_pow, ← hr2]
    exact inv_mul_cancel₀ (pow_ne_zero 2 (ne_of_gt hr))
  · rw [eval_scale_of_isHomogeneous P (d + 1) hP x r⁻¹]
    exact mul_pos (pow_pos (inv_pos.mpr hr) _) hPx

theorem exists_normalized_positive_direction_of_value (P : MvPolynomial ι ℝ) (d : ℕ)
    (hP : P.IsHomogeneous (d + 1)) (j : ι)
    (x : ι → ℝ) (hPx : 0 < eval x P) :
    ∃ A : Matrix ι ι ℝ, A.transpose * A = 1 ∧ A * A.transpose = 1 ∧
      0 < (QuarticMinimal.changeVariables A P).coeff (Finsupp.single j (d + 1)) ∧
      ∀ k, j ≠ k → (QuarticMinimal.changeVariables A P).coeff
        (Finsupp.single j d + Finsupp.single k 1) = 0 := by
  obtain ⟨y, hy, hPy⟩ := exists_positive_sphere_value P d hP x hPx
  exact exists_normalized_positive_direction P d hP j y hy hPy

theorem exists_normalized_negative_direction_of_value (P : MvPolynomial ι ℝ) (d : ℕ)
    (hP : P.IsHomogeneous (d + 1)) (j : ι)
    (x : ι → ℝ) (hPx : eval x P < 0) :
    ∃ A : Matrix ι ι ℝ, A.transpose * A = 1 ∧ A * A.transpose = 1 ∧
      (QuarticMinimal.changeVariables A P).coeff (Finsupp.single j (d + 1)) < 0 ∧
      ∀ k, j ≠ k → (QuarticMinimal.changeVariables A P).coeff
        (Finsupp.single j d + Finsupp.single k 1) = 0 := by
  obtain ⟨A, hA, hA', hp, hz⟩ := exists_normalized_positive_direction_of_value
    (-P) d hP.neg j x (by simpa only [map_neg, neg_pos] using hPx)
  refine ⟨A, hA, hA', ?_, ?_⟩
  · simpa only [map_neg, coeff_neg, neg_pos] using hp
  · intro k hjk
    simpa only [map_neg, coeff_neg, neg_eq_zero] using hz k hjk

omit [Fintype ι] [DecidableEq ι] in
/-- Every nonzero homogeneous polynomial of odd degree assumes positive values. -/
theorem exists_positive_value_of_odd (P : MvPolynomial ι ℝ) (d : ℕ)
    (hP : P.IsHomogeneous d) (hd : Odd d) (hne : P ≠ 0) :
    ∃ x : ι → ℝ, 0 < eval x P := by
  by_contra hh
  push Not at hh
  apply hne
  apply QuarticCompatibility.polynomial_funext
  intro x
  have hx := hh x
  have hnx := hh (fun i => -x i)
  have he := eval_scale_of_isHomogeneous P d hP x (-1)
  rw [hd.neg_one_pow] at he
  simp only [neg_one_mul] at he
  rw [he] at hnx
  simp only [map_zero]
  linarith

end QuarticNormalization
end

end ComponentOrthogonalNormalization


/- Component: CoefficientNormalization -/
section ComponentCoefficientNormalization

/- Requires PolynomialBasics, LowDegree, ChangeVariables, OrthogonalNormalization. -/
noncomputable section
open scoped BigOperators Matrix
open MvPolynomial

namespace QuarticNormalization

variable {n : ℕ}

/-- The highest coefficient in the distinguished variable is constant for a
homogeneous polynomial of the same degree. -/
theorem finSuccEquiv_top_coeff (P : MvPolynomial (Fin (n + 1)) ℝ) (d : ℕ)
    (hP : P.IsHomogeneous d) :
    (finSuccEquiv ℝ n P).coeff d = C (P.coeff (Finsupp.single 0 d)) := by
  have hh := hP.finSuccEquiv_coeff_isHomogeneous d 0 (by omega)
  have hd := Nat.eq_zero_of_le_zero hh.totalDegree_le
  rw [totalDegree_eq_zero_iff_eq_C.mp hd, finSuccEquiv_coeff_coeff]
  simp only [Finsupp.cons_zero_eq_single_zero]

/-- Vanishing coefficients with one tangential variable eliminate the entire
next-to-leading coefficient in distinguished-variable normal form. -/
theorem finSuccEquiv_next_coeff_eq_zero (P : MvPolynomial (Fin (n + 1)) ℝ) (d : ℕ)
    (hP : P.IsHomogeneous (d + 1))
    (hz : ∀ i : Fin n, P.coeff (Finsupp.single 0 d + Finsupp.single i.succ 1) = 0) :
    (finSuccEquiv ℝ n P).coeff d = 0 := by
  have hh := hP.finSuccEquiv_coeff_isHomogeneous d 1 rfl
  rw [QuarticMinimal.homogeneous_linear_expansion _ hh]
  apply Finset.sum_eq_zero
  intro i _
  have hs : (Finsupp.single i 1).cons d =
      Finsupp.single 0 d + Finsupp.single i.succ 1 := by
    ext j
    cases j using Fin.cases <;> simp [Finsupp.single_apply]
  simp only [coeff_pderiv, zero_add, Finsupp.zero_apply, Nat.cast_zero,
    zero_add, mul_one, finSuccEquiv_coeff_coeff, hs, hz, map_zero, zero_mul]

/-- The positive normal form used by the cubic and quartic coefficient arguments. -/
theorem exists_positive_normal_form (P : MvPolynomial (Fin (n + 1)) ℝ) (d : ℕ)
    (hP : P.IsHomogeneous (d + 1)) (x : Fin (n + 1) → ℝ) (hx : 0 < eval x P) :
    ∃ (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (a : ℝ),
      A.transpose * A = 1 ∧ A * A.transpose = 1 ∧ 0 < a ∧
      (finSuccEquiv ℝ n (QuarticMinimal.changeVariables A P)).coeff (d + 1) = C a ∧
      (finSuccEquiv ℝ n (QuarticMinimal.changeVariables A P)).coeff d = 0 := by
  obtain ⟨A, hA, hA', ha, hz⟩ := exists_normalized_positive_direction_of_value P d hP 0 x hx
  refine ⟨A, (QuarticMinimal.changeVariables A P).coeff (Finsupp.single 0 (d + 1)),
    hA, hA', ha, ?_, ?_⟩
  · exact finSuccEquiv_top_coeff _ _ (isHomogeneous_changeVariables A P _ hP)
  · apply finSuccEquiv_next_coeff_eq_zero _ d (isHomogeneous_changeVariables A P _ hP)
    intro i
    exact hz i.succ (Ne.symm (Fin.succ_ne_zero i))

theorem exists_negative_normal_form (P : MvPolynomial (Fin (n + 1)) ℝ) (d : ℕ)
    (hP : P.IsHomogeneous (d + 1)) (x : Fin (n + 1) → ℝ) (hx : eval x P < 0) :
    ∃ (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (a : ℝ),
      A.transpose * A = 1 ∧ A * A.transpose = 1 ∧ a < 0 ∧
      (finSuccEquiv ℝ n (QuarticMinimal.changeVariables A P)).coeff (d + 1) = C a ∧
      (finSuccEquiv ℝ n (QuarticMinimal.changeVariables A P)).coeff d = 0 := by
  obtain ⟨A, hA, hA', ha, hz⟩ := exists_normalized_negative_direction_of_value P d hP 0 x hx
  refine ⟨A, (QuarticMinimal.changeVariables A P).coeff (Finsupp.single 0 (d + 1)),
    hA, hA', ha, ?_, ?_⟩
  · exact finSuccEquiv_top_coeff _ _ (isHomogeneous_changeVariables A P _ hP)
  · apply finSuccEquiv_next_coeff_eq_zero _ d (isHomogeneous_changeVariables A P _ hP)
    intro i
    exact hz i.succ (Ne.symm (Fin.succ_ne_zero i))

end QuarticNormalization
end

end ComponentCoefficientNormalization


/- Component: QuarticSpectral -/
section ComponentQuarticSpectral


open scoped BigOperators
open Matrix

namespace QuarticSpectral

/-- The scalar polynomial arising in the quartic tangential Laplacian identity. -/
noncomputable def scalarFa (a s : ℝ) : ℝ := 2*s+s^2/a+s^3/(2*a^2)

theorem scalarFa_factor (a s : ℝ) (ha : a ≠ 0) :
    scalarFa a s = s/2*((s/a+1)^2+3) := by
  unfold scalarFa
  field_simp
  ring

theorem scalarFa_strictMono (a : ℝ) (ha : a ≠ 0) : StrictMono (scalarFa a) := by
  intro x y hxy
  have hN : 0 < x^2+x*y+y^2+2*a*(x+y)+4*a^2 := by
    nlinarith [sq_nonneg (3*x+3*y+4*a), sq_nonneg (x-y), sq_pos_of_ne_zero ha]
  have hd : 0 < 2*a^2 := mul_pos (by norm_num) (sq_pos_of_ne_zero ha)
  have hid : scalarFa a y-scalarFa a x =
      (y-x)*(x^2+x*y+y^2+2*a*(x+y)+4*a^2)/(2*a^2) := by
    unfold scalarFa
    field_simp
    ring
  have hp : 0 < scalarFa a y-scalarFa a x := by
    rw [hid]
    exact div_pos (mul_pos (sub_pos.mpr hxy) hN) hd
  linarith

theorem scalarFa_zero (a : ℝ) : scalarFa a 0 = 0 := by simp [scalarFa]

theorem scalarFa_pos_iff (a s : ℝ) (ha : a ≠ 0) : 0 < scalarFa a s ↔ 0 < s := by
  simpa only [scalarFa_zero] using (scalarFa_strictMono a ha).lt_iff_lt (a := 0) (b := s)

theorem scalarFa_neg_iff (a s : ℝ) (ha : a ≠ 0) : scalarFa a s < 0 ↔ s < 0 := by
  simpa only [scalarFa_zero] using (scalarFa_strictMono a ha).lt_iff_lt (a := s) (b := 0)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Polynomial functional calculus at a real matrix. -/
noncomputable def matrixFa (a : ℝ) (S : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  (2:ℝ) • S+a⁻¹ • S^2+(2*a^2)⁻¹ • S^3

theorem matrixFa_mulVec (a : ℝ) (S : Matrix ι ι ℝ) (v : ι → ℝ) :
    matrixFa a S *ᵥ v = (2:ℝ) • (S *ᵥ v)+a⁻¹ • (S *ᵥ (S *ᵥ v))+
      (2*a^2)⁻¹ • (S *ᵥ (S *ᵥ (S *ᵥ v))) := by
  simp [matrixFa, add_mulVec, smul_mulVec, pow_succ, ← mulVec_mulVec]

omit [DecidableEq ι] in
theorem dot_move_symmetric (S : Matrix ι ι ℝ) (hS : S.IsSymm) (x y : ι → ℝ) :
    (S *ᵥ x) ⬝ᵥ y = x ⬝ᵥ (S *ᵥ y) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hS]

omit [DecidableEq ι] in
theorem dot_self_nonneg (v : ι → ℝ) : 0 ≤ v ⬝ᵥ v := by
  exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (v i))

omit [DecidableEq ι] in
theorem dot_self_pos (v : ι → ℝ) (hv : v ≠ 0) : 0 < v ⬝ᵥ v := by
  exact lt_of_le_of_ne (dot_self_nonneg v) (Ne.symm (dotProduct_self_eq_zero.not.mpr hv))

/-- A sum-of-squares identity replaces diagonalization in the sign argument. -/
theorem matrixFa_energy (a : ℝ) (ha : a ≠ 0) (S : Matrix ι ι ℝ)
    (hS : S.IsSymm) (v : ι → ℝ) :
    (S *ᵥ v) ⬝ᵥ (matrixFa a S *ᵥ v) =
      (3/2:ℝ)*((S *ᵥ v) ⬝ᵥ (S *ᵥ v))+
      (2*a^2)⁻¹*((S *ᵥ (S *ᵥ v)+a • (S *ᵥ v)) ⬝ᵥ
        (S *ᵥ (S *ᵥ v)+a • (S *ᵥ v))) := by
  have hh := dot_move_symmetric S hS (S *ᵥ v) (S *ᵥ (S *ᵥ v))
  have hcross := dotProduct_comm (S *ᵥ (S *ᵥ v)) (S *ᵥ v)
  rw [matrixFa_mulVec]
  simp only [dotProduct_add, add_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  rw [← hh, hcross]
  field_simp
  ring

/-- Every nonzero eigenvector of `Fa(S)` inherits the sign of its eigenvalue
in the quadratic form of `S`. -/
theorem eigenvalue_times_quadratic_pos (a c : ℝ) (ha : a ≠ 0) (hc : c ≠ 0)
    (S : Matrix ι ι ℝ) (hS : S.IsSymm) (v : ι → ℝ) (hv : v ≠ 0)
    (heig : matrixFa a S *ᵥ v = c • v) : 0 < c*(v ⬝ᵥ (S *ᵥ v)) := by
  have hsv : S *ᵥ v ≠ 0 := by
    intro hz
    have hz' : matrixFa a S *ᵥ v = 0 := by
      simp only [matrixFa_mulVec, hz, mulVec_zero, smul_zero, add_zero]
    rw [heig] at hz'
    exact hv ((smul_eq_zero.mp hz').resolve_left hc)
  have he := matrixFa_energy a ha S hS v
  rw [heig, dotProduct_smul, smul_eq_mul, dotProduct_comm (S *ᵥ v) v] at he
  rw [he]
  exact add_pos_of_pos_of_nonneg (mul_pos (by norm_num) (dot_self_pos _ hsv))
    (mul_nonneg (inv_nonneg.mpr (by positivity)) (dot_self_nonneg _))

theorem quadratic_neg_of_matrixFa_eigenvalue_neg (a c : ℝ) (ha : a ≠ 0) (hc : c < 0)
    (S : Matrix ι ι ℝ) (hS : S.IsSymm) (v : ι → ℝ) (hv : v ≠ 0)
    (heig : matrixFa a S *ᵥ v = c • v) : v ⬝ᵥ (S *ᵥ v) < 0 := by
  have hp := eigenvalue_times_quadratic_pos a c ha (ne_of_lt hc) S hS v hv heig
  by_contra hn
  have hnonpos := mul_nonpos_of_nonpos_of_nonneg (le_of_lt hc) (le_of_not_gt hn)
  linarith

theorem quadratic_pos_of_matrixFa_eigenvalue_pos (a c : ℝ) (ha : a ≠ 0) (hc : 0 < c)
    (S : Matrix ι ι ℝ) (hS : S.IsSymm) (v : ι → ℝ) (hv : v ≠ 0)
    (heig : matrixFa a S *ᵥ v = c • v) : 0 < v ⬝ᵥ (S *ᵥ v) := by
  have hp := eigenvalue_times_quadratic_pos a c ha (ne_of_gt hc) S hS v hv heig
  by_contra hn
  have hnonpos := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hc) (le_of_not_gt hn)
  linarith


omit [DecidableEq ι] in
/-- Distinct real eigenvalues of a symmetric matrix have orthogonal eigenvectors. -/
theorem eigenvectors_orthogonal (Q : Matrix ι ι ℝ) (hQ : Q.IsSymm)
    (e f : ι → ℝ) (c d : ℝ) (hcd : c ≠ d)
    (he : Q *ᵥ e = c • e) (hf : Q *ᵥ f = d • f) : e ⬝ᵥ f = 0 := by
  have heq := dot_move_symmetric Q hQ e f
  rw [he, hf, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul] at heq
  have hm : (c-d)*(e ⬝ᵥ f) = 0 := by linear_combination heq
  exact (mul_eq_zero.mp hm).resolve_left (sub_ne_zero.mpr hcd)

/-- The two opposite critical values cannot give the same mixed quartic coefficient.
This is the algebraic contradiction in Proposition 4, with no spectral theorem. -/
theorem two_critical_directions_impossible (a b : ℝ) (ha : 0 < a) (hb : b < 0)
    (S T : Matrix ι ι ℝ) (hS : S.IsSymm) (hT : T.IsSymm)
    (e f : ι → ℝ) (he : e ≠ 0) (hf : f ≠ 0)
    (hSf : matrixFa a S *ᵥ f = (12*b) • f)
    (hTe : matrixFa b T *ᵥ e = (12*a) • e)
    (hmixed : f ⬝ᵥ (S *ᵥ f) = e ⬝ᵥ (T *ᵥ e)) : False := by
  have hn := quadratic_neg_of_matrixFa_eigenvalue_neg a (12*b) (ne_of_gt ha)
    (mul_neg_of_pos_of_neg (by norm_num) hb) S hS f hf hSf
  have hp := quadratic_pos_of_matrixFa_eigenvalue_pos b (12*a) (ne_of_lt hb)
    (mul_pos (by norm_num) ha) T hT e he hTe
  rw [hmixed] at hn
  linarith

/-- A shared symmetric Laplacian matrix and its two tangential formulas yield
exactly the contradiction above. Orthogonality follows from the two critical values. -/
theorem two_critical_directions_from_laplacian (a b : ℝ) (ha : 0 < a) (hb : b < 0)
    (Q S T : Matrix ι ι ℝ) (hQ : Q.IsSymm) (hS : S.IsSymm) (hT : T.IsSymm)
    (e f : ι → ℝ) (he : e ≠ 0) (hf : f ≠ 0)
    (hQe : Q *ᵥ e = (12*a) • e) (hQf : Q *ᵥ f = (12*b) • f)
    (hSe : ∀ x : ι → ℝ, e ⬝ᵥ x = 0 → matrixFa a S *ᵥ x = Q *ᵥ x)
    (hTf : ∀ x : ι → ℝ, f ⬝ᵥ x = 0 → matrixFa b T *ᵥ x = Q *ᵥ x)
    (hmixed : f ⬝ᵥ (S *ᵥ f) = e ⬝ᵥ (T *ᵥ e)) : False := by
  have hef : e ⬝ᵥ f = 0 :=
    eigenvectors_orthogonal Q hQ e f (12*a) (12*b) (by nlinarith) hQe hQf
  have hfe : f ⬝ᵥ e = 0 := by simpa only [dotProduct_comm] using hef
  exact two_critical_directions_impossible a b ha hb S T hS hT e f he hf
    ((hSe f hef).trans hQf) ((hTf e hfe).trans hQe) hmixed

end QuarticSpectral

end ComponentQuarticSpectral


/- Component: QuarticSign -/
section ComponentQuarticSign

/- Requires CoefficientNormalization, AmbientQuartic, and QuarticSpectral. -/
noncomputable section
open scoped BigOperators Matrix
open MvPolynomial
open QuarticMinimal.QuarticNormalForm QuarticMinimal.AmbientQuartic

namespace QuarticMinimal

variable {n : ℕ}

/-- An actual homogeneous quartic solution of the leading minimal-graph operator
cannot have both a positive value and a negative value. -/
theorem homogeneous_quartic_no_opposite_signs
    (P : MvPolynomial (Fin (n + 1)) ℝ) (hP : P.IsHomogeneous 4)
    (hL : leadingOperator P = 0) (x y : Fin (n + 1) → ℝ)
    (hx : 0 < eval x P) (hy : eval y P < 0) : False := by
  obtain ⟨U, a, _hUt, hU, ha, h4U, h3U⟩ :=
    QuarticNormalization.exists_positive_normal_form P 3 hP x hx
  obtain ⟨V, b, _hVt, hV, hb, h4V, h3V⟩ :=
    QuarticNormalization.exists_negative_normal_form P 3 hP y hy
  let e := U *ᵥ axis n
  let f := V *ᵥ axis n
  let Q := quadraticMatrix (QuarticNormalForm.laplacian P)
  let S := canonicalS P a e
  let T := canonicalS P b f
  have hQa := ambient_Q_action P U hU a (ne_of_gt ha) hP h4U h3U hL
  have hQb := ambient_Q_action P V hV b (ne_of_lt hb) hP h4V h3V hL
  have he : e ≠ 0 := by
    intro he
    have hu : e ⬝ᵥ e = 1 := ambient_axis_unit U hU
    simp [he] at hu
  have hf : f ≠ 0 := by
    intro hf
    have hv : f ⬝ᵥ f = 1 := ambient_axis_unit V hV
    simp [hf] at hv
  have hQs : Q.IsSymm := quadraticMatrix_symmetric _
  have hSs : S.IsSymm := canonicalS_symmetric P a e
  have hTs : T.IsSymm := canonicalS_symmetric P b f
  have hef : e ⬝ᵥ f = 0 :=
    QuarticSpectral.eigenvectors_orthogonal Q hQs e f (12 * a) (12 * b)
      (by nlinarith) hQa.1 hQb.1
  have hmixed : f ⬝ᵥ (S *ᵥ f) = e ⬝ᵥ (T *ᵥ e) :=
    canonicalS_mixed_symmetry P hP a b e f hef
  exact QuarticSpectral.two_critical_directions_from_laplacian a b ha hb Q S T
    hQs hSs hTs e f he hf hQa.1 hQb.1 hQa.2 hQb.2 hmixed

/-- Every homogeneous quartic solution of the leading minimal-graph operator has
one weak sign, in every finite dimension. -/
theorem homogeneous_quartic_has_one_sign (P : MvPolynomial (Fin n) ℝ)
    (hP : P.IsHomogeneous 4) (hL : leadingOperator P = 0) :
    (∀ x, 0 ≤ eval x P) ∨ (∀ x, eval x P ≤ 0) := by
  cases n with
  | zero =>
    left
    intro x
    have hx : x = 0 := Subsingleton.elim _ _
    rw [hx, eval_zero_of_homogeneous P hP (by decide)]
  | succ n =>
    by_cases hp : ∃ x, 0 < eval x P
    · left
      obtain ⟨x, hx⟩ := hp
      intro y
      by_contra hy
      exact homogeneous_quartic_no_opposite_signs P hP hL x y hx (lt_of_not_ge hy)
    · right
      intro x
      exact le_of_not_gt (fun hx => hp ⟨x, hx⟩)

end QuarticMinimal
end

end ComponentQuarticSign


/- Component: QuadraticScalar -/
section ComponentQuadraticScalar

/-!
The diagonal quadratic minimal-graph obstruction.  The proof evaluates the
equation at points that cancel the gradient in each nonzero eigendirection.
The reduction of a quadratic polynomial to this diagonal equation is not
asserted here.
-/

namespace QuarticMinimal.QuadraticScalar

noncomputable def cancelPoint {ι : Type*} (eigenvalue c : ι → ℝ) (i : ι) : ℝ :=
  -c i / eigenvalue i

theorem velocity_cancel {ι : Type*} (eigenvalue c : ι → ℝ) (i : ι)
    (hi : eigenvalue i ≠ 0) :
    eigenvalue i * cancelPoint eigenvalue c i + c i = 0 := by
  unfold cancelPoint
  field_simp
  ring

theorem weighted_velocity_cancel {ι : Type*} (eigenvalue c : ι → ℝ) (i : ι) :
    eigenvalue i * (eigenvalue i * cancelPoint eigenvalue c i + c i) ^ 2 = 0 := by
  by_cases hi : eigenvalue i = 0
  · simp [hi]
  · simp [velocity_cancel eigenvalue c i hi]

theorem trace_zero_of_diagonal_equation {ι : Type*} [Fintype ι]
    (eigenvalue c : ι → ℝ) (s : ℝ)
    (hM : ∀ x : ι → ℝ,
      (1 + ∑ i, (eigenvalue i * x i + c i) ^ 2) * s -
        ∑ i, eigenvalue i * (eigenvalue i * x i + c i) ^ 2 = 0) : s = 0 := by
  have hbase := hM (cancelPoint eigenvalue c)
  have hweighted :
      (∑ i, eigenvalue i * (eigenvalue i * cancelPoint eigenvalue c i + c i) ^ 2) = 0 :=
    Finset.sum_eq_zero (fun i _ => weighted_velocity_cancel eigenvalue c i)
  rw [hweighted, sub_zero] at hbase
  have hpos : 0 < 1 + ∑ i, (eigenvalue i * cancelPoint eigenvalue c i + c i) ^ 2 := by
    have hs : 0 ≤ ∑ i, (eigenvalue i * cancelPoint eigenvalue c i + c i) ^ 2 :=
      Finset.sum_nonneg (fun i _ => sq_nonneg _)
    linarith
  exact (mul_eq_zero.mp hbase).resolve_left (ne_of_gt hpos)

theorem eigenvalues_zero_of_diagonal_equation {ι : Type*} [Fintype ι]
    (eigenvalue c : ι → ℝ) (s : ℝ)
    (hM : ∀ x : ι → ℝ,
      (1 + ∑ i, (eigenvalue i * x i + c i) ^ 2) * s -
        ∑ i, eigenvalue i * (eigenvalue i * x i + c i) ^ 2 = 0) :
    ∀ i, eigenvalue i = 0 := by
  classical
  have hs := trace_zero_of_diagonal_equation eigenvalue c s hM
  intro j
  by_contra hj
  let x : ι → ℝ := Function.update (cancelPoint eigenvalue c) j ((1 - c j) / eigenvalue j)
  have hxj : eigenvalue j * x j + c j = 1 := by
    simp only [x, Function.update_self]
    field_simp
    ring
  have hweighted : (∑ i, eigenvalue i * (eigenvalue i * x i + c i) ^ 2) = eigenvalue j := by
    rw [Finset.sum_eq_single j]
    · simp [hxj]
    · intro i _ hij
      have hxi : x i = cancelPoint eigenvalue c i := by simp [x, hij]
      rw [hxi]
      exact weighted_velocity_cancel eigenvalue c i
    · simp
  have htest := hM x
  rw [hs, mul_zero, hweighted, zero_sub] at htest
  exact hj (neg_eq_zero.mp htest)

theorem diagonal_quadratic_obstruction {ι : Type*} [Fintype ι]
    (eigenvalue c : ι → ℝ)
    (hM : ∀ x : ι → ℝ,
      (1 + ∑ i, (eigenvalue i * x i + c i) ^ 2) * (∑ i, eigenvalue i) -
        ∑ i, eigenvalue i * (eigenvalue i * x i + c i) ^ 2 = 0) :
    ∀ i, eigenvalue i = 0 :=
  eigenvalues_zero_of_diagonal_equation eigenvalue c _ hM

end QuarticMinimal.QuadraticScalar
end ComponentQuadraticScalar


/- Component: QuadraticMatrix -/
section ComponentQuadraticMatrix

/- Requires MatrixAlgebra and QuadraticScalar in the single-file build. -/
noncomputable section
open scoped BigOperators Matrix
open Matrix

namespace QuarticMinimal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem quadratic_matrix_obstruction (H : Matrix ι ι ℝ) (hH : H.IsSymm)
    (c : ι → ℝ)
    (hM : ∀ x : ι → ℝ,
      (1 + dotProduct (H *ᵥ x + c) (H *ᵥ x + c)) * trace H -
        dotProduct (H *ᵥ x + c) (H *ᵥ (H *ᵥ x + c)) = 0) : H = 0 := by
  have hHerm : H.IsHermitian := isHermitian_iff_isSymm.mpr hH
  let U : Matrix ι ι ℝ := hHerm.eigenvectorUnitary
  let d : ι → ℝ := hHerm.eigenvalues
  have hUU : U * U.transpose = 1 := by
    simpa only [U, Unitary.coe_star, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
      using Unitary.coe_mul_star_self hHerm.eigenvectorUnitary
  have hD : U.transpose * H * U = diagonal d := by
    simpa only [U, d, Unitary.conjStarAlgAut_star_apply, star_eq_conjTranspose,
      conjTranspose_eq_transpose_of_trivial, RCLike.ofReal_real_eq_id, Function.id_comp]
      using hHerm.conjStarAlgAut_star_eigenvectorUnitary
  let c' := U.transpose *ᵥ c
  have hv (x : ι → ℝ) :
      U.transpose *ᵥ (H *ᵥ (U *ᵥ x) + c) = diagonal d *ᵥ x + c' := by
    rw [mulVec_add, mulVec_mulVec, mulVec_mulVec, hD]
  have heq (x : ι → ℝ) :
      (1 + dotProduct (diagonal d *ᵥ x + c') (diagonal d *ᵥ x + c')) * trace (diagonal d) -
        dotProduct (diagonal d *ᵥ x + c') (diagonal d *ᵥ (diagonal d *ᵥ x + c')) = 0 := by
    have hi := MatrixAlgebra.minimal_expression_invariant U hUU H (H *ᵥ (U *ᵥ x) + c)
    rw [hv x, hD, hM (U *ᵥ x)] at hi
    exact hi
  have hd : ∀ i, d i = 0 := by
    apply QuadraticScalar.diagonal_quadratic_obstruction d c'
    intro x
    convert heq x using 1
    simp only [dotProduct, mulVec_diagonal, Pi.add_apply,
        trace_diagonal, pow_two]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    ring
  exact hHerm.eigenvalues_eq_zero_iff.mp (funext hd)

end QuarticMinimal
end

end ComponentQuadraticMatrix


/- Component: QuadraticObstruction -/
section ComponentQuadraticObstruction

/- Requires ChangeVariables, LowDegree, QuadraticMatrix. -/
noncomputable section
open scoped BigOperators Matrix
open MvPolynomial

namespace QuarticMinimal

variable {ι : Type*} [Fintype ι]

theorem affine_of_quadratic_minimal (P : MvPolynomial ι ℝ)
    (hdegree : P.totalDegree ≤ 2) (hminimal : minimalOperator P = 0) :
    P.totalDegree ≤ 1 := by
  classical
  let H := hessianCoeff P
  let c : ι → ℝ := fun i => (pderiv i P).coeff 0
  have hH : H = 0 := by
    apply quadratic_matrix_obstruction H (hessianCoeff_symmetric P) c
    intro x
    have hm := congrArg (eval x) hminimal
    have hg (i : ι) : eval x (pderiv i P) = (H *ᵥ x + c) i :=
      eval_quadratic_gradient P hdegree x i
    have hh (i j : ι) : eval x (pderiv i (pderiv j P)) = H i j := by
      rw [second_partial_eq_C_of_totalDegree_le_two P hdegree i j, eval_C]
    simp only [minimalOperator, map_sub, map_mul, map_add, map_one, map_sum,
      map_pow, map_zero, hg, hh] at hm
    have hc : dotProduct (H *ᵥ x + c) (H *ᵥ (H *ᵥ x + c)) =
        ∑ i, ∑ j, (H *ᵥ x + c) i * (H *ᵥ x + c) j * H i j := by
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [hc]
    simpa only [dotProduct, Matrix.trace, Matrix.diag, pow_two] using hm
  apply QuarticPolynomialBasics.totalDegree_le_one_of_second_partials_zero
  intro i j
  rw [second_partial_eq_C_of_totalDegree_le_two P hdegree i j]
  change C (H i j) = 0
  simp [hH]


end QuarticMinimal
end

end ComponentQuadraticObstruction


/- Component: HomogeneousCubicCoefficients -/
section ComponentHomogeneousCubicCoefficients

open scoped BigOperators
open Polynomial

namespace HomogeneousCubicCoefficients

variable {R : Type*} [CommRing R]

noncomputable def longitudinal (a A : R) : R[X] := C (3*a)*X^2+C A
noncomputable def longitudinalSecond (a : R) : R[X] := C (6*a)*X
noncomputable def transverse (α β : R) : R[X] := C α*X+C β
noncomputable def baseTerm (a A h k : R) : R[X] := longitudinal a A^2*transverse h k
noncomputable def singleTerm (a A h k α β : R) : R[X] :=
  transverse α β^2*(longitudinalSecond a+transverse h k)-
    2*longitudinal a A*C α*transverse α β
noncomputable def hessianTerm (α β α' β' H K : R) : R[X] :=
  transverse α β*transverse α' β'*transverse H K

theorem base_coeff5 (a A h k : R) :
    (baseTerm a A h k).coeff 5 = 9*a^2*h := by
  unfold baseTerm longitudinal transverse
  ring_nf
  simp [mul_assoc, ← map_mul, ← map_pow, Polynomial.coeff_X, Polynomial.coeff_C]
  ring

theorem base_coeff4 (a A h k : R) :
    (baseTerm a A h k).coeff 4 = 9*a^2*k := by
  unfold baseTerm longitudinal transverse
  ring_nf
  simp [mul_assoc, ← map_mul, ← map_pow, Polynomial.coeff_X, Polynomial.coeff_C]
  ring

theorem base_coeff3 (a A h k : R) :
    (baseTerm a A h k).coeff 3 = 6*a*A*h := by
  unfold baseTerm longitudinal transverse
  ring_nf
  simp [mul_assoc, ← map_mul, ← map_pow, Polynomial.coeff_X, Polynomial.coeff_C]
  ring

theorem single_coeff5 (a A h k α β : R) :
    (singleTerm a A h k α β).coeff 5 = 0 := by
  unfold singleTerm longitudinal longitudinalSecond transverse
  ring_nf
  simp [mul_assoc, ← map_mul, ← map_pow, Polynomial.coeff_X, Polynomial.coeff_C]

theorem single_coeff4 (a A h k α β : R) :
    (singleTerm a A h k α β).coeff 4 = 0 := by
  unfold singleTerm longitudinal longitudinalSecond transverse
  ring_nf
  simp [mul_assoc, ← map_mul, ← map_pow, Polynomial.coeff_X, Polynomial.coeff_C]

theorem single_coeff3 (a A h k α β : R) :
    (singleTerm a A h k α β).coeff 3 = h*α^2 := by
  unfold singleTerm longitudinal longitudinalSecond transverse
  ring_nf
  simp [mul_assoc, ← map_mul, ← map_pow, Polynomial.coeff_X, Polynomial.coeff_C]
  ring

theorem hessian_coeff5 (α β α' β' H K : R) :
    (hessianTerm α β α' β' H K).coeff 5 = 0 := by
  unfold hessianTerm transverse
  ring_nf
  simp [mul_assoc, ← map_mul, Polynomial.coeff_X, Polynomial.coeff_C]

theorem hessian_coeff4 (α β α' β' H K : R) :
    (hessianTerm α β α' β' H K).coeff 4 = 0 := by
  unfold hessianTerm transverse
  ring_nf
  simp [mul_assoc, ← map_mul, Polynomial.coeff_X, Polynomial.coeff_C]

theorem hessian_coeff3 (α β α' β' H K : R) :
    (hessianTerm α β α' β' H K).coeff 3 = α*α'*H := by
  unfold hessianTerm transverse
  ring_nf
  simp [mul_assoc, ← map_mul, Polynomial.coeff_X, Polynomial.coeff_C]

variable {ι : Type*} [Fintype ι]

noncomputable def operator (a A h k : R) (α β : ι → R) (H K : ι → ι → R) : R[X] :=
  (∑ i, transverse (α i) (β i)^2)*longitudinalSecond a+
    (longitudinal a A^2+∑ i, transverse (α i) (β i)^2)*transverse h k-
    2*longitudinal a A*(∑ i, C (α i)*transverse (α i) (β i))-
    ∑ i, ∑ j, hessianTerm (α i) (β i) (α j) (β j) (H i j) (K i j)

theorem operator_decomposition (a A h k : R) (α β : ι → R) (H K : ι → ι → R) :
    operator a A h k α β H K = baseTerm a A h k +
      (∑ i, singleTerm a A h k (α i) (β i))-
      ∑ i, ∑ j, hessianTerm (α i) (β i) (α j) (β j) (H i j) (K i j) := by
  unfold operator baseTerm singleTerm
  simp only [add_mul, mul_add, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.mul_sum, Finset.sum_mul, mul_assoc]
  abel

theorem operator_coeff5 (a A h k : R) (α β : ι → R) (H K : ι → ι → R) :
    (operator a A h k α β H K).coeff 5 = 9*a^2*h := by
  simp [operator_decomposition, base_coeff5, single_coeff5, hessian_coeff5]

theorem operator_coeff4 (a A h k : R) (α β : ι → R) (H K : ι → ι → R) :
    (operator a A h k α β H K).coeff 4 = 9*a^2*k := by
  simp [operator_decomposition, base_coeff4, single_coeff4, hessian_coeff4]

theorem operator_coeff3_of_trace_zero (a A : R) (α β : ι → R) (H K : ι → ι → R) :
    (operator a A 0 0 α β H K).coeff 3 = - ∑ i, ∑ j, α i*α j*H i j := by
  simp [operator_decomposition, base_coeff3, single_coeff3, hessian_coeff3]

theorem operator_pure_coeff1 (a : R) (β : ι → R) (K : ι → ι → R) :
    (operator a 0 0 0 (fun _ => 0) β (fun _ _ => 0) K).coeff 1 = 6*a*∑ i, β i^2 := by
  simp only [operator, transverse, longitudinal, longitudinalSecond, hessianTerm,
    map_zero, zero_mul, zero_add, add_zero, mul_zero, sub_zero, Finset.sum_const_zero]
  simp only [← map_pow, ← map_sum, ← map_mul, Polynomial.coeff_sub,
    Polynomial.coeff_C_mul, Polynomial.coeff_X, ite_true, mul_one,
    Polynomial.coeff_C, Nat.one_ne_zero, ite_false, sub_zero]
  ring

end HomogeneousCubicCoefficients
end ComponentHomogeneousCubicCoefficients


/- Component: CubicMatrix -/
section ComponentCubicMatrix

noncomputable section
open scoped BigOperators Matrix
open Matrix

namespace CubicMatrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem symmetric_eq_zero_of_quadratic_zero (A : Matrix ι ι ℝ)
    (hA : A.IsSymm) (h : ∀ x, x ⬝ᵥ (A *ᵥ x) = 0) : A = 0 := by
  ext i j
  have hi := h (Pi.single i 1)
  have hj := h (Pi.single j 1)
  have hij := h (Pi.single i 1 + Pi.single j 1)
  simp only [Matrix.mulVec_single_one, single_one_dotProduct] at hi hj
  simp only [Matrix.mulVec_add, dotProduct_add, add_dotProduct,
    Matrix.mulVec_single_one, single_one_dotProduct] at hij
  change A i i = 0 at hi
  change A j j = 0 at hj
  change A i i + A j i + (A i j + A j j) = 0 at hij
  rw [hA.apply i j] at hij
  change A i j = 0
  linarith

omit [DecidableEq ι] in
theorem dot_move (S : Matrix ι ι ℝ) (hS : S.IsSymm) (x y : ι → ℝ) :
    (S *ᵥ x) ⬝ᵥ y = x ⬝ᵥ (S *ᵥ y) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hS]

theorem symmetric_cube_zero (S : Matrix ι ι ℝ) (hS : S.IsSymm)
    (hcube : S ^ 3 = 0) : S = 0 := by
  have hv (x : ι → ℝ) : S *ᵥ x = 0 := by
    have hc : S *ᵥ (S *ᵥ (S *ᵥ x)) = 0 := by
      rw [mulVec_mulVec, mulVec_mulVec]
      rw [← pow_two, ← pow_succ, hcube, zero_mulVec]
    have hsq : S *ᵥ (S *ᵥ x) = 0 := by
      apply dotProduct_self_eq_zero.mp
      rw [dot_move S hS (S *ᵥ x) (S *ᵥ (S *ᵥ x)), hc, dotProduct_zero]
    apply dotProduct_self_eq_zero.mp
    rw [dot_move S hS x (S *ᵥ x), hsq, dotProduct_zero]
  ext i j
  have hij := congrArg (fun x : ι → ℝ => x i) (hv (Pi.single j 1))
  simpa only [mulVec_single_one, Matrix.col, Matrix.transpose_apply, Pi.zero_apply, Matrix.zero_apply] using hij

theorem symmetric_eq_zero_of_cube_quadratic_zero (S : Matrix ι ι ℝ)
    (hS : S.IsSymm) (h : ∀ x, x ⬝ᵥ (S ^ 3 *ᵥ x) = 0) : S = 0 :=
  symmetric_cube_zero S hS (symmetric_eq_zero_of_quadratic_zero _ (hS.pow 3) h)

end CubicMatrix
end

end ComponentCubicMatrix


/- Component: CubicNormalForm -/
section ComponentCubicNormalForm

/- Requires DistinguishedVariable, HomogeneousCubicCoefficients, QuarticNormalForm,
PolynomialBasics, LowDegree, and CubicMatrix. -/
noncomputable section
open scoped BigOperators Matrix
open MvPolynomial Matrix

namespace QuarticMinimal.CubicNormalForm

open DistinguishedVariable
open QuarticNormalForm (laplacian leadingExpression splitLeadingExpression)

variable {n : ℕ}

def normalForm (a : ℝ) (A B : MvPolynomial (Fin n) ℝ) :
    Polynomial (MvPolynomial (Fin n) ℝ) :=
  Polynomial.C (C a) * Polynomial.X ^ 3 + Polynomial.C A * Polynomial.X + Polynomial.C B

theorem finSuccEquiv_normalForm (P : MvPolynomial (Fin (n + 1)) ℝ) (a : ℝ)
    (hP : P.totalDegree ≤ 3) (h3 : (finSuccEquiv ℝ n P).coeff 3 = C a)
    (h2 : (finSuccEquiv ℝ n P).coeff 2 = 0) :
    finSuccEquiv ℝ n P = normalForm a ((finSuccEquiv ℝ n P).coeff 1)
      ((finSuccEquiv ℝ n P).coeff 0) := by
  conv_lhs => rw [finSuccEquiv_eq_sum P hP]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one,
    mul_one, zero_add, h3, h2, map_zero, zero_mul, add_zero, normalForm]
  ring

theorem derivative_normalForm (a : ℝ) (A B : MvPolynomial (Fin n) ℝ) :
    Polynomial.derivative (normalForm a A B) =
      HomogeneousCubicCoefficients.longitudinal (C a) A := by
  simp [normalForm, HomogeneousCubicCoefficients.longitudinal, Polynomial.C_ofNat]
  ring

theorem second_derivative_normalForm (a : ℝ) (A B : MvPolynomial (Fin n) ℝ) :
    Polynomial.derivative (Polynomial.derivative (normalForm a A B)) =
      HomogeneousCubicCoefficients.longitudinalSecond (C a) := by
  rw [derivative_normalForm]
  simp [HomogeneousCubicCoefficients.longitudinal,
    HomogeneousCubicCoefficients.longitudinalSecond, Polynomial.C_ofNat]
  ring

theorem coefficientPartial_normalForm (a : ℝ) (A B : MvPolynomial (Fin n) ℝ) (i : Fin n) :
    coefficientPartial i (normalForm a A B) =
      HomogeneousCubicCoefficients.transverse (pderiv i A) (pderiv i B) := by
  simp [normalForm, HomogeneousCubicCoefficients.transverse, coefficientPartial_add,
    coefficientPartial_mul, coefficientPartial_C, coefficientPartial_X, coefficientPartial_pow]

theorem derivative_transverse (α β : MvPolynomial (Fin n) ℝ) :
    Polynomial.derivative (HomogeneousCubicCoefficients.transverse α β) = Polynomial.C α := by
  simp [HomogeneousCubicCoefficients.transverse]

theorem coefficientPartial_transverse (α β : MvPolynomial (Fin n) ℝ) (i : Fin n) :
    coefficientPartial i (HomogeneousCubicCoefficients.transverse α β) =
      HomogeneousCubicCoefficients.transverse (pderiv i α) (pderiv i β) := by
  simp [HomogeneousCubicCoefficients.transverse, coefficientPartial_add,
    coefficientPartial_mul, coefficientPartial_C, coefficientPartial_X]

theorem sum_transverse (α β : Fin n → MvPolynomial (Fin n) ℝ) :
    (∑ i, HomogeneousCubicCoefficients.transverse (α i) (β i)) =
      HomogeneousCubicCoefficients.transverse (∑ i, α i) (∑ i, β i) := by
  simp only [HomogeneousCubicCoefficients.transverse,
    Finset.sum_add_distrib, ← Finset.sum_mul, ← map_sum]

theorem splitLeadingExpression_normalForm (a : ℝ) (A B : MvPolynomial (Fin n) ℝ) :
    splitLeadingExpression (normalForm a A B) =
      HomogeneousCubicCoefficients.operator (C a) A (laplacian A) (laplacian B)
        (fun i => pderiv i A) (fun i => pderiv i B)
        (fun i j => pderiv i (pderiv j A)) (fun i j => pderiv i (pderiv j B)) := by
  simp only [splitLeadingExpression, coefficientPartial_normalForm, derivative_normalForm,
    derivative_transverse, coefficientPartial_transverse, sum_transverse]
  rw [show Polynomial.derivative (HomogeneousCubicCoefficients.longitudinal (C a) A) =
    HomogeneousCubicCoefficients.longitudinalSecond (C a) from by
      simpa only [derivative_normalForm] using second_derivative_normalForm a A B]
  rfl

theorem leading_operator_zero_of_normalForm
    (P : MvPolynomial (Fin (n + 1)) ℝ) (a : ℝ) (A B : MvPolynomial (Fin n) ℝ)
    (hQ : finSuccEquiv ℝ n P = normalForm a A B) (hP : leadingExpression P = 0) :
    HomogeneousCubicCoefficients.operator (C a) A (laplacian A) (laplacian B)
      (fun i => pderiv i A) (fun i => pderiv i B)
      (fun i j => pderiv i (pderiv j A)) (fun i j => pderiv i (pderiv j B)) = 0 := by
  have h := QuarticNormalForm.finSuccEquiv_leadingExpression P
  rw [hP, map_zero, hQ, splitLeadingExpression_normalForm] at h
  exact h.symm

theorem actual_constraints_of_normalForm
    (P : MvPolynomial (Fin (n + 1)) ℝ) (a : ℝ) (A B : MvPolynomial (Fin n) ℝ)
    (ha : a ≠ 0) (hQ : finSuccEquiv ℝ n P = normalForm a A B)
    (hP : leadingExpression P = 0) :
    laplacian A = 0 ∧ laplacian B = 0 ∧
      (∑ i, ∑ j, pderiv i A * pderiv j A * pderiv i (pderiv j A)) = 0 := by
  have hop := leading_operator_zero_of_normalForm P a A B hQ hP
  have h5 := congrArg (fun Q => Polynomial.coeff Q 5) hop
  have h4 := congrArg (fun Q => Polynomial.coeff Q 4) hop
  rw [HomogeneousCubicCoefficients.operator_coeff5, Polynomial.coeff_zero] at h5
  rw [HomogeneousCubicCoefficients.operator_coeff4, Polynomial.coeff_zero] at h4
  have hfac : (9 : MvPolynomial (Fin n) ℝ) * C a ^ 2 ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero _ (C_ne_zero.mpr ha))
  have hA := (mul_eq_zero.mp h5).resolve_left hfac
  have hB := (mul_eq_zero.mp h4).resolve_left hfac
  refine ⟨hA, hB, ?_⟩
  rw [hA, hB] at hop
  have h3 := congrArg (fun Q => Polynomial.coeff Q 3) hop
  rw [HomogeneousCubicCoefficients.operator_coeff3_of_trace_zero, Polynomial.coeff_zero] at h3
  exact neg_eq_zero.mp h3

theorem quadratic_coefficient_zero
    (A : MvPolynomial (Fin n) ℝ) (hA : A.IsHomogeneous 2)
    (hc : (∑ i, ∑ j, pderiv i A * pderiv j A * pderiv i (pderiv j A)) = 0) : A = 0 := by
  have hm : ∀ y : Fin n → ℝ,
      y ⬝ᵥ (QuarticNormalForm.quadraticMatrix A ^ 3 *ᵥ y) = 0 := by
    intro y
    have he := congrArg (eval y) hc
    simp only [map_sum, map_mul, map_zero] at he
    simp_rw [QuarticNormalForm.eval_homogeneous_quadratic_gradient A hA y,
      QuarticNormalForm.eval_homogeneous_quadratic_hessian A hA y] at he
    rw [HomogeneousQuarticCoefficients.gradient_hessian_relation
      (QuarticNormalForm.quadraticMatrix A) (QuarticNormalForm.quadraticMatrix_symmetric A) y] at he
    linarith
  have hS := CubicMatrix.symmetric_eq_zero_of_cube_quadratic_zero
    (QuarticNormalForm.quadraticMatrix A) (QuarticNormalForm.quadraticMatrix_symmetric A) hm
  apply QuarticCompatibility.polynomial_funext
  intro y
  rw [QuarticNormalForm.eval_homogeneous_quadratic A hA, hS, zero_mulVec, dotProduct_zero, map_zero]

theorem homogeneous_coefficients_zero
    (P : MvPolynomial (Fin (n + 1)) ℝ) (a : ℝ) (A B : MvPolynomial (Fin n) ℝ)
    (ha : a ≠ 0) (hA : A.IsHomogeneous 2) (hB : B.IsHomogeneous 3)
    (hQ : finSuccEquiv ℝ n P = normalForm a A B) (hP : leadingExpression P = 0) :
    A = 0 ∧ B = 0 := by
  obtain ⟨_, hBlap, hAcubic⟩ := actual_constraints_of_normalForm P a A B ha hQ hP
  have hAz : A = 0 := quadratic_coefficient_zero A hA hAcubic
  refine ⟨hAz, ?_⟩
  have hop := leading_operator_zero_of_normalForm P a A B hQ hP
  rw [hAz, hBlap] at hop
  simp only [laplacian, map_zero, Finset.sum_const_zero] at hop
  have h1 := congrArg (fun Q => Polynomial.coeff Q 1) hop
  rw [HomogeneousCubicCoefficients.operator_pure_coeff1, Polynomial.coeff_zero] at h1
  have hfac : (6 : MvPolynomial (Fin n) ℝ) * C a ≠ 0 :=
    mul_ne_zero (by norm_num) (C_ne_zero.mpr ha)
  have hsq := (mul_eq_zero.mp h1).resolve_left hfac
  have hder : ∀ i, pderiv i B = 0 := fun i =>
    QuarticPolynomialBasics.eq_zero_of_sum_sq_eq_zero Finset.univ (fun i => pderiv i B)
      hsq i (Finset.mem_univ i)
  rw [QuarticMinimal.eq_C_of_pderiv_eq_zero B hder,
    hB.coeff_eq_zero (by simp), map_zero]

theorem homogeneous_cubic_pure
    (P : MvPolynomial (Fin (n + 1)) ℝ) (a : ℝ) (ha : a ≠ 0)
    (hP : P.IsHomogeneous 3) (h3 : (finSuccEquiv ℝ n P).coeff 3 = C a)
    (h2 : (finSuccEquiv ℝ n P).coeff 2 = 0) (hL : leadingExpression P = 0) :
    finSuccEquiv ℝ n P = Polynomial.C (C a) * Polynomial.X ^ 3 := by
  have hQ := finSuccEquiv_normalForm P a hP.totalDegree_le h3 h2
  have hA : ((finSuccEquiv ℝ n P).coeff 1).IsHomogeneous 2 :=
    hP.finSuccEquiv_coeff_isHomogeneous 1 2 rfl
  have hB : ((finSuccEquiv ℝ n P).coeff 0).IsHomogeneous 3 :=
    hP.finSuccEquiv_coeff_isHomogeneous 0 3 rfl
  obtain ⟨hAz, hBz⟩ := homogeneous_coefficients_zero P a _ _ ha hA hB hQ hL
  simpa only [normalForm, hAz, hBz, map_zero, zero_mul, add_zero] using hQ

end QuarticMinimal.CubicNormalForm
end

end ComponentCubicNormalForm


/- Component: FullCubicCoefficients -/
section ComponentFullCubicCoefficients

open scoped BigOperators
open Polynomial

namespace FullCubicCoefficients

variable {R : Type*} [CommRing R]

noncomputable def longitudinal (a b A : R) : R[X] := C (3*a)*X^2+C (2*b)*X+C A
noncomputable def longitudinalSecond (a b : R) : R[X] := C (6*a)*X+C (2*b)
noncomputable def transverse (α β : R) : R[X] := C α*X+C β
noncomputable def baseTerm (a b A d : R) : R[X] :=
  longitudinalSecond a b+(1+longitudinal a b A^2)*C d
noncomputable def singleTerm (a b A d α β : R) : R[X] :=
  transverse α β^2*(longitudinalSecond a b+C d)-
    2*longitudinal a b A*C α*transverse α β
noncomputable def hessianTerm (α β α' β' K : R) : R[X] :=
  transverse α β*transverse α' β'*C K

theorem base_coeff4 (a b A d : R) :
    (baseTerm a b A d).coeff 4 = 9*a^2*d := by
  unfold baseTerm longitudinal longitudinalSecond
  ring_nf
  simp [mul_assoc, ← map_mul, ← map_pow, Polynomial.coeff_X, Polynomial.coeff_C]
  ring

theorem base_coeff1 (a b A d : R) :
    (baseTerm a b A d).coeff 1 = 6*a+4*b*A*d := by
  unfold baseTerm longitudinal longitudinalSecond
  ring_nf
  simp [mul_assoc, ← map_mul, ← map_pow, Polynomial.coeff_X, Polynomial.coeff_C]
  ring

theorem single_coeff4 (a b A d α β : R) :
    (singleTerm a b A d α β).coeff 4 = 0 := by
  unfold singleTerm longitudinal longitudinalSecond transverse
  ring_nf
  simp [mul_assoc, ← map_mul, ← map_pow, Polynomial.coeff_X, Polynomial.coeff_C]

theorem single_coeff1 (a b A d α β : R) :
    (singleTerm a b A d α β).coeff 1 = 6*a*β^2-2*A*α^2+2*d*α*β := by
  unfold singleTerm longitudinal longitudinalSecond transverse
  ring_nf
  simp [mul_assoc, ← map_mul, ← map_pow, Polynomial.coeff_X, Polynomial.coeff_C]
  ring

theorem hessian_coeff4 (α β α' β' K : R) :
    (hessianTerm α β α' β' K).coeff 4 = 0 := by
  unfold hessianTerm transverse
  ring_nf
  simp [mul_assoc, ← map_mul, Polynomial.coeff_X, Polynomial.coeff_C]

theorem hessian_coeff1 (α β α' β' K : R) :
    (hessianTerm α β α' β' K).coeff 1 = (α*β'+β*α')*K := by
  unfold hessianTerm transverse
  ring_nf
  simp [mul_assoc, ← map_mul, Polynomial.coeff_X, Polynomial.coeff_C]

variable {ι : Type*} [Fintype ι]

noncomputable def operator (a b A d : R) (α β : ι → R) (K : ι → ι → R) : R[X] :=
  (1+∑ i, transverse (α i) (β i)^2)*longitudinalSecond a b+
    (1+longitudinal a b A^2+∑ i, transverse (α i) (β i)^2)*C d-
    2*longitudinal a b A*(∑ i, C (α i)*transverse (α i) (β i))-
    ∑ i, ∑ j, hessianTerm (α i) (β i) (α j) (β j) (K i j)

theorem operator_decomposition (a b A d : R) (α β : ι → R) (K : ι → ι → R) :
    operator a b A d α β K = baseTerm a b A d +
      (∑ i, singleTerm a b A d (α i) (β i))-
      ∑ i, ∑ j, hessianTerm (α i) (β i) (α j) (β j) (K i j) := by
  unfold operator baseTerm singleTerm
  simp only [add_mul, mul_add, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.mul_sum, Finset.sum_mul, mul_assoc, one_mul]
  abel

theorem operator_coeff4 (a b A d : R) (α β : ι → R) (K : ι → ι → R) :
    (operator a b A d α β K).coeff 4 = 9*a^2*d := by
  simp [operator_decomposition, base_coeff4, single_coeff4, hessian_coeff4]

theorem operator_coeff1_of_trace_zero (a b A : R) (α β : ι → R)
    (K : ι → ι → R) (hK : ∀ i j, K i j = K j i) :
    (operator a b A 0 α β K).coeff 1 =
      6*a*(1+∑ i, β i^2)-2*A*(∑ i, α i^2)-2*(∑ i, ∑ j, α i*β j*K i j) := by
  simp only [operator_decomposition, coeff_add, coeff_sub, finsetSum_coeff,
    base_coeff1, single_coeff1, hessian_coeff1, mul_zero, zero_mul, add_zero]
  simp only [add_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hh : (∑ i, ∑ j, β i*α j*K i j) = ∑ i, ∑ j, α i*β j*K i j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hK j i]
    ring
  rw [hh]
  ring

end FullCubicCoefficients
end ComponentFullCubicCoefficients


/- Component: CubicScalar -/
section ComponentCubicScalar

noncomputable section
open scoped BigOperators Matrix
open Matrix

namespace CubicScalar

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The linear coefficient in the distinguished variable is already incompatible
with a nonzero cubic leading coefficient. -/
theorem obstruction (a c : ℝ) (ha : a ≠ 0) (α δ : ι → ℝ) (K : Matrix ι ι ℝ)
    (h : ∀ y : ι → ℝ,
      6*a*(1+(K *ᵥ y+δ) ⬝ᵥ (K *ᵥ y+δ)) -
        2*(c+α ⬝ᵥ y)*(α ⬝ᵥ α)-2*(α ⬝ᵥ (K *ᵥ (K *ᵥ y+δ))) = 0) : False := by
  have hK : K = 0 := by
    have hv (y : ι → ℝ) : K *ᵥ y = 0 := by
      have hp := h y
      have hn := h (-y)
      have hz := h 0
      simp only [mulVec_neg, mulVec_zero, zero_add, dotProduct_zero, add_zero,
        mulVec_add, dotProduct_add, add_dotProduct, dotProduct_neg, neg_dotProduct] at hp hn hz
      have he : (12*a)*((K *ᵥ y) ⬝ᵥ (K *ᵥ y)) = 0 := by
        linear_combination hp + hn - 2*hz
      apply dotProduct_self_eq_zero.mp
      exact (mul_eq_zero.mp he).resolve_left (mul_ne_zero (by norm_num) ha)
    ext i j
    have hh := congrArg (fun y : ι → ℝ => y i) (hv (Pi.single j 1))
    simpa only [mulVec_single_one, Matrix.col, Matrix.transpose_apply, Pi.zero_apply, Matrix.zero_apply] using hh
  have hz := h 0
  have hα := h α
  simp only [hK, zero_mulVec, zero_add, dotProduct_zero, mul_zero, sub_zero,
    add_zero] at hz hα
  have hnorm : α ⬝ᵥ α = 0 := by nlinarith
  rw [hnorm, mul_zero, sub_zero] at hz
  have hn : 0 ≤ δ ⬝ᵥ δ := Finset.sum_nonneg (fun i _ => mul_self_nonneg (δ i))
  have hpos : 1+δ ⬝ᵥ δ ≠ 0 := by linarith
  exact (mul_ne_zero (mul_ne_zero (by norm_num) ha) hpos) hz

end CubicScalar
end

end ComponentCubicScalar


/- Component: FullCubicNormalForm -/
section ComponentFullCubicNormalForm

/- Requires PolynomialBasics, LowDegree, DistinguishedVariable, FullCubicCoefficients,
CubicScalar. -/
noncomputable section
open scoped BigOperators Matrix
open MvPolynomial Matrix

namespace QuarticMinimal.FullCubicNormalForm

open DistinguishedVariable

variable {n : ℕ}

def normalForm (a b : ℝ) (A B : MvPolynomial (Fin n) ℝ) :
    Polynomial (MvPolynomial (Fin n) ℝ) :=
  Polynomial.C (C a) * Polynomial.X ^ 3 + Polynomial.C (C b) * Polynomial.X ^ 2 +
    Polynomial.C A * Polynomial.X + Polynomial.C B

theorem derivative_normalForm (a b : ℝ) (A B : MvPolynomial (Fin n) ℝ) :
    Polynomial.derivative (normalForm a b A B) =
      FullCubicCoefficients.longitudinal (C a) (C b) A := by
  simp [normalForm, FullCubicCoefficients.longitudinal, Polynomial.C_ofNat]
  ring

theorem second_derivative_normalForm (a b : ℝ) (A B : MvPolynomial (Fin n) ℝ) :
    Polynomial.derivative (Polynomial.derivative (normalForm a b A B)) =
      FullCubicCoefficients.longitudinalSecond (C a) (C b) := by
  rw [derivative_normalForm]
  simp [FullCubicCoefficients.longitudinal, FullCubicCoefficients.longitudinalSecond,
    Polynomial.C_ofNat]
  ring

theorem coefficientPartial_normalForm (a b : ℝ) (A B : MvPolynomial (Fin n) ℝ) (i : Fin n) :
    coefficientPartial i (normalForm a b A B) =
      FullCubicCoefficients.transverse (pderiv i A) (pderiv i B) := by
  simp [normalForm, FullCubicCoefficients.transverse, coefficientPartial_add,
    coefficientPartial_mul, coefficientPartial_C, coefficientPartial_X, coefficientPartial_pow]

theorem derivative_transverse (α β : MvPolynomial (Fin n) ℝ) :
    Polynomial.derivative (FullCubicCoefficients.transverse α β) = Polynomial.C α := by
  simp [FullCubicCoefficients.transverse]

theorem second_coefficientPartial_normalForm (a b : ℝ) (A B : MvPolynomial (Fin n) ℝ)
    (hA : A.totalDegree ≤ 1) (hB : B.totalDegree ≤ 2) (i j : Fin n) :
    coefficientPartial i (coefficientPartial j (normalForm a b A B)) =
      Polynomial.C (C (hessianCoeff B i j)) := by
  rw [coefficientPartial_normalForm]
  simp [FullCubicCoefficients.transverse, coefficientPartial_add,
    coefficientPartial_mul, coefficientPartial_C, coefficientPartial_X,
    QuarticPolynomialBasics.second_partials_zero_of_totalDegree_le_one A hA i j,
    second_partial_eq_C_of_totalDegree_le_two B hB i j]

theorem splitMinimalExpression_normalForm (a b : ℝ) (A B : MvPolynomial (Fin n) ℝ)
    (hA : A.totalDegree ≤ 1) (hB : B.totalDegree ≤ 2) :
    splitMinimalExpression (normalForm a b A B) =
      FullCubicCoefficients.operator (C a) (C b) A (C (trace (hessianCoeff B)))
        (fun i => pderiv i A) (fun i => pderiv i B)
        (fun i j => C (hessianCoeff B i j)) := by
  unfold splitMinimalExpression
  rw [second_derivative_normalForm]
  simp only [coefficientPartial_normalForm, derivative_normalForm, derivative_transverse]
  have hh (i j : Fin n) :
      coefficientPartial i (FullCubicCoefficients.transverse (pderiv j A) (pderiv j B)) =
        Polynomial.C (C (hessianCoeff B i j)) := by
    simpa only [coefficientPartial_normalForm] using
      second_coefficientPartial_normalForm a b A B hA hB i j
  simp only [hh]
  have hsum : (∑ i, Polynomial.C (C (hessianCoeff B i i))) =
      Polynomial.C (C (trace (hessianCoeff B)) : MvPolynomial (Fin n) ℝ) := by
    simp only [trace, diag, map_sum]
  rw [hsum]
  rfl

theorem matrix_identity_of_minimal_normalForm
    (P : MvPolynomial (Fin (n + 1)) ℝ) (a b : ℝ) (A B : MvPolynomial (Fin n) ℝ)
    (ha : a ≠ 0) (hA : A.totalDegree ≤ 1) (hB : B.totalDegree ≤ 2)
    (hQ : finSuccEquiv ℝ n P = normalForm a b A B)
    (hP : (1 + ∑ i, pderiv i P ^ 2) * (∑ i, pderiv i (pderiv i P)) -
      ∑ i, ∑ j, pderiv i P * pderiv j P * pderiv i (pderiv j P) = 0) :
    ∀ y : Fin n → ℝ,
      6*a*(1+(hessianCoeff B *ᵥ y+(fun i => (pderiv i B).coeff 0)) ⬝ᵥ
        (hessianCoeff B *ᵥ y+(fun i => (pderiv i B).coeff 0))) -
      2*(A.coeff 0+(fun i => (pderiv i A).coeff 0) ⬝ᵥ y)*
        ((fun i => (pderiv i A).coeff 0) ⬝ᵥ (fun i => (pderiv i A).coeff 0)) -
      2*((fun i => (pderiv i A).coeff 0) ⬝ᵥ
        (hessianCoeff B *ᵥ (hessianCoeff B *ᵥ y+(fun i => (pderiv i B).coeff 0)))) = 0 := by
  have hop := finSuccEquiv_minimalExpression P
  rw [hP, map_zero, hQ, splitMinimalExpression_normalForm a b A B hA hB] at hop
  have h4 := congrArg (fun Q => Polynomial.coeff Q 4) hop.symm
  rw [FullCubicCoefficients.operator_coeff4, Polynomial.coeff_zero] at h4
  have hfac : (9 : MvPolynomial (Fin n) ℝ) * C a ^ 2 ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero _ (C_ne_zero.mpr ha))
  have htrace : C (trace (hessianCoeff B)) = (0 : MvPolynomial (Fin n) ℝ) :=
    (mul_eq_zero.mp h4).resolve_left hfac
  rw [htrace] at hop
  have h1 := congrArg (fun Q => Polynomial.coeff Q 1) hop.symm
  rw [FullCubicCoefficients.operator_coeff1_of_trace_zero _ _ _ _ _ _
      (fun i j => congrArg C ((hessianCoeff_symmetric B).apply i j).symm),
    Polynomial.coeff_zero] at h1
  intro y
  have he := congrArg (eval y) h1
  simp only [map_sub, map_mul, map_add, map_pow, map_sum, map_ofNat, eval_C, map_one, map_zero] at he
  have hEA (i : Fin n) : eval y (pderiv i A) = (pderiv i A).coeff 0 := by
    simpa only [eval_C] using congrArg (eval y) (pderiv_eq_C_of_totalDegree_le_one A hA i)
  simp_rw [hEA, eval_quadratic_gradient B hB] at he
  rw [eval_affine_expansion A hA] at he
  convert he using 1
  simp only [dotProduct, Matrix.mulVec, Pi.add_apply, ← pow_two,
      Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]

theorem normalForm_not_minimal
    (P : MvPolynomial (Fin (n + 1)) ℝ) (a b : ℝ) (A B : MvPolynomial (Fin n) ℝ)
    (ha : a ≠ 0) (hA : A.totalDegree ≤ 1) (hB : B.totalDegree ≤ 2)
    (hQ : finSuccEquiv ℝ n P = normalForm a b A B)
    (hP : (1 + ∑ i, pderiv i P ^ 2) * (∑ i, pderiv i (pderiv i P)) -
      ∑ i, ∑ j, pderiv i P * pderiv j P * pderiv i (pderiv j P) = 0) : False :=
  CubicScalar.obstruction a (A.coeff 0) ha
    (fun i => (pderiv i A).coeff 0) (fun i => (pderiv i B).coeff 0) (hessianCoeff B)
    (matrix_identity_of_minimal_normalForm P a b A B ha hA hB hQ hP)

end QuarticMinimal.FullCubicNormalForm
end

end ComponentFullCubicNormalForm


/- Component: CubicObstruction -/
section ComponentCubicObstruction

/- Requires the cubic normal form components, CoefficientNormalization,
OperatorInvariance, and LinearSubstitution. -/
noncomputable section
open scoped BigOperators Matrix
open MvPolynomial Matrix

namespace QuarticMinimal

open DistinguishedVariable

variable {n : ℕ}

theorem exists_full_cubic_normal_form
    (P p : MvPolynomial (Fin (n + 1)) ℝ) (a : ℝ)
    (hp : finSuccEquiv ℝ n p = Polynomial.C (C a) * Polynomial.X ^ 3)
    (hr : (P - p).totalDegree ≤ 2) :
    ∃ (b : ℝ) (A B : MvPolynomial (Fin n) ℝ), A.totalDegree ≤ 1 ∧ B.totalDegree ≤ 2 ∧
      finSuccEquiv ℝ n P = FullCubicNormalForm.normalForm a b A B := by
  let Q := finSuccEquiv ℝ n (P - p)
  have h2 : (Q.coeff 2).totalDegree = 0 := by
    apply Nat.eq_zero_of_le_zero
    simpa only [Nat.sub_self] using coeff_finSuccEquiv_totalDegree_le (P - p) hr 2
  have hc2 : Q.coeff 2 = C ((Q.coeff 2).coeff 0) := totalDegree_eq_zero_iff_eq_C.mp h2
  refine ⟨(Q.coeff 2).coeff 0, Q.coeff 1, Q.coeff 0, ?_, ?_, ?_⟩
  · exact coeff_finSuccEquiv_totalDegree_le (P - p) hr 1
  · exact coeff_finSuccEquiv_totalDegree_le (P - p) hr 0
  · have hsum := finSuccEquiv_eq_sum (P - p) hr
    change Q = _ at hsum
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one,
      mul_one, zero_add] at hsum
    have hsplit : finSuccEquiv ℝ n P = finSuccEquiv ℝ n p + Q := by
      change finSuccEquiv ℝ n P = finSuccEquiv ℝ n p + finSuccEquiv ℝ n (P - p)
      simp only [map_sub]
      ring
    rw [hsplit, hp]
    conv_lhs => rw [hsum, hc2]
    unfold FullCubicNormalForm.normalForm
    dsimp only [Q]
    ring

theorem exists_orthogonal_pure_cubic
    (p : MvPolynomial (Fin (n + 1)) ℝ) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (hL : leadingOperator p = 0) :
    ∃ (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (a : ℝ),
      U.transpose * U = 1 ∧ U * U.transpose = 1 ∧ 0 < a ∧
      finSuccEquiv ℝ n (changeVariables U p) = Polynomial.C (C a) * Polynomial.X ^ 3 := by
  obtain ⟨x, hx⟩ := QuarticNormalization.exists_positive_value_of_odd p 3 hp (by decide) hne
  obtain ⟨U, a, hU, hU', ha, h3, h2⟩ :=
    QuarticNormalization.exists_positive_normal_form p 2 hp x hx
  refine ⟨U, a, hU, hU', ha, ?_⟩
  apply CubicNormalForm.homogeneous_cubic_pure _ a (ne_of_gt ha)
    (isHomogeneous_changeVariables U p 3 hp) h3 h2
  exact leadingOperator_changeVariables_eq_zero U hU' p hL

theorem no_degree_three_minimal_polynomial
    (P : MvPolynomial (Fin (n + 1)) ℝ) (hdeg : P.totalDegree = 3)
    (hM : minimalOperator P = 0) : False := by
  let p := homogeneousComponent 3 P
  have hp : p.IsHomogeneous 3 := homogeneousComponent_isHomogeneous 3 P
  have hne : p ≠ 0 := by
    have ht := QuarticPolynomialBasics.top_homogeneousComponent_ne_zero P (by omega)
    simpa only [hdeg] using ht
  have hL : leadingOperator p = 0 := by
    exact QuarticPolynomialBasics.cubicOperator_top_eq_zero P 3 (by omega) (by omega) hM
  obtain ⟨U, a, hU, hU', ha, hpure⟩ := exists_orthogonal_pure_cubic p hp hne hL
  have hr : (changeVariables U P - changeVariables U p).totalDegree ≤ 2 := by
    rw [← map_sub]
    apply (totalDegree_changeVariables_le U (P - p)).trans
    exact QuarticPolynomialBasics.totalDegree_sub_homogeneousComponent_le P 3 (by omega)
  obtain ⟨b, A, B, hA, hB, hform⟩ :=
    exists_full_cubic_normal_form (changeVariables U P) (changeVariables U p) a hpure hr
  exact FullCubicNormalForm.normalForm_not_minimal _ a b A B (ne_of_gt ha) hA hB hform
    (minimalOperator_changeVariables_eq_zero U hU' P hM)

theorem no_degree_three_minimal_polynomial_any_dimension {m : ℕ}
    (P : MvPolynomial (Fin m) ℝ) (hdeg : P.totalDegree = 3)
    (hM : minimalOperator P = 0) : False := by
  cases m with
  | zero =>
    have hz := QuarticPolynomialBasics.totalDegree_zero_variables P
    omega
  | succ m => exact no_degree_three_minimal_polynomial P hdeg hM

end QuarticMinimal
end

end ComponentCubicObstruction


/- Component: FluxObstruction -/
section ComponentFluxObstruction


open MeasureTheory Filter
open scoped Topology BigOperators

noncomputable section

namespace FluxObstruction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

/-- Compact support of the test function supplies every integrability hypothesis in
multivariate integration by parts. The second function need not have compact support. -/
theorem integral_mul_fderiv_eq_neg_of_compactSupport
    {φ g : E → ℝ} (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ)
    (hg : ContDiff ℝ 1 g) (v : E) :
    ∫ x, φ x * fderiv ℝ g x v ∂μ =
      - ∫ x, fderiv ℝ φ x v * g x ∂μ := by
  have hdφ : Continuous (fun x ↦ fderiv ℝ φ x v) :=
    (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hdg : Continuous (fun x ↦ fderiv ℝ g x v) :=
    (hg.continuous_fderiv (by norm_num)).clm_apply continuous_const
  apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
  · exact (hdφ.mul hg.continuous).integrable_of_hasCompactSupport
      (hcφ.fderiv_apply ℝ v).mul_right
  · exact (hφ.continuous.mul hdg).integrable_of_hasCompactSupport hcφ.mul_right
  · exact (hφ.continuous.mul hg.continuous).integrable_of_hasCompactSupport hcφ.mul_right
  · exact fun x _ ↦ hφ.differentiable (by norm_num) x
  · exact fun x _ ↦ hg.differentiable (by norm_num) x

variable {ι : Type*} [Fintype ι]

/-- Divergence using an arbitrary finite family of fixed directions. With the coordinate
basis this is the usual Euclidean divergence of `F`. -/
def divergence (v : ι → E) (F : E → ι → ℝ) (x : E) : ℝ :=
  ∑ i, fderiv ℝ (fun y ↦ F y i) x (v i)

/-- The pairing of a test function's differential with a vector field in fixed coordinates. -/
def testFlux (v : ι → E) (φ : E → ℝ) (F : E → ι → ℝ) (x : E) : ℝ :=
  ∑ i, fderiv ℝ φ x (v i) * F x i

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
theorem testFlux_continuous
    (v : ι → E) {φ : E → ℝ} {F : E → ι → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hF : ∀ i, Continuous (fun x ↦ F x i)) :
    Continuous (testFlux v φ F) := by
  apply continuous_finsetSum
  intro i _
  exact ((hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const).mul (hF i)

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
theorem testFlux_hasCompactSupport
    (v : ι → E) {φ : E → ℝ} {F : E → ι → ℝ}
    (hcφ : HasCompactSupport φ) : HasCompactSupport (testFlux v φ F) := by
  convert (HasCompactSupport.finset_sum (s := Finset.univ)
      (fun i _ ↦ (hcφ.fderiv_apply ℝ (v i)).mul_right (f' := fun x ↦ F x i))) using 1
  ext x
  simp [testFlux]

omit [FiniteDimensional ℝ E] in
theorem testFlux_integrable
    (v : ι → E) {φ : E → ℝ} {F : E → ι → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ)
    (hF : ∀ i, Continuous (fun x ↦ F x i)) : Integrable (testFlux v φ F) μ :=
  (testFlux_continuous v hφ hF).integrable_of_hasCompactSupport
    (testFlux_hasCompactSupport v hcφ)

/-- Weak divergence identity on the full space, proved with no boundary integration. -/
theorem integral_mul_divergence_eq_neg_testFlux
    (v : ι → E) {φ : E → ℝ} {F : E → ι → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ)
    (hF : ∀ i, ContDiff ℝ 1 (fun x ↦ F x i)) :
    ∫ x, φ x * divergence v F x ∂μ = - ∫ x, testFlux v φ F x ∂μ := by
  have hi i : Integrable (fun x ↦ φ x * fderiv ℝ (fun y ↦ F y i) x (v i)) μ :=
    (hφ.continuous.mul
      (((hF i).continuous_fderiv (by norm_num)).clm_apply continuous_const)).integrable_of_hasCompactSupport hcφ.mul_right
  have hj i : Integrable (fun x ↦ fderiv ℝ φ x (v i) * F x i) μ :=
    (((hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const).mul
      (hF i).continuous).integrable_of_hasCompactSupport (hcφ.fderiv_apply ℝ (v i)).mul_right
  simp only [divergence, testFlux, Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ ↦ hi i), integral_finsetSum _ (fun i _ ↦ hj i)]
  simp_rw [integral_mul_fderiv_eq_neg_of_compactSupport hφ hcφ (hF _) (v _)]
  simp

/-- A divergence-free field has zero pairing with every compactly supported C¹ test gradient. -/
theorem integral_testFlux_eq_zero
    (v : ι → E) {φ : E → ℝ} {F : E → ι → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ)
    (hF : ∀ i, ContDiff ℝ 1 (fun x ↦ F x i))
    (hdiv : ∀ x, divergence v F x = 0) :
    ∫ x, testFlux v φ F x ∂μ = 0 := by
  have h := integral_mul_divergence_eq_neg_testFlux (μ := μ) v hφ hcφ hF
  simp only [hdiv, mul_zero, integral_zero] at h
  linarith

/-- An integrable bound for the flux of any field whose components have norm at most one. -/
def testBound (v : ι → E) (φ : E → ℝ) (x : E) : ℝ :=
  ∑ i, ‖fderiv ℝ φ x (v i)‖

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
theorem norm_testFlux_le_testBound (v : ι → E) (φ : E → ℝ) (F : E → ι → ℝ)
    (x : E) (hF : ∀ i, ‖F x i‖ ≤ 1) :
    ‖testFlux v φ F x‖ ≤ testBound v φ x := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (hF i)

omit [FiniteDimensional ℝ E] in
theorem testBound_integrable (v : ι → E) {φ : E → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ) :
    Integrable (testBound v φ) μ := by
  apply integrable_finsetSum
  intro i _
  exact ((hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const).norm.integrable_of_hasCompactSupport (hcφ.fderiv_apply ℝ (v i)).norm

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
theorem testFlux_tendsto (v : ι → E) (φ : E → ℝ)
    {F : ℕ → E → ι → ℝ} {G : E → ι → ℝ} {x : E}
    (hlim : ∀ i, Tendsto (fun n ↦ F n x i) atTop (𝓝 (G x i))) :
    Tendsto (fun n ↦ testFlux v φ (F n) x) atTop (𝓝 (testFlux v φ G x)) := by
  apply tendsto_finsetSum
  intro i _
  exact tendsto_const_nhds.mul (hlim i)

/-- An almost-everywhere limit of uniformly component-bounded, divergence-free C¹ fields
has zero flux against a compactly supported C¹ test gradient. -/
theorem integral_testFlux_limit_eq_zero
    (v : ι → E) {φ : E → ℝ} {F : ℕ → E → ι → ℝ} {G : E → ι → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ)
    (hF : ∀ n i, ContDiff ℝ 1 (fun x ↦ F n x i))
    (hdiv : ∀ n x, divergence v (F n) x = 0)
    (hbound : ∀ n x i, ‖F n x i‖ ≤ 1)
    (hlim : ∀ᵐ x ∂μ, ∀ i, Tendsto (fun n ↦ F n x i) atTop (𝓝 (G x i))) :
    ∫ x, testFlux v φ G x ∂μ = 0 := by
  have hc : Tendsto (fun n ↦ ∫ x, testFlux v φ (F n) x ∂μ) atTop
      (𝓝 (∫ x, testFlux v φ G x ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (testBound v φ)
    · exact fun n ↦ (testFlux_continuous v hφ (fun i ↦ (hF n i).continuous)).aestronglyMeasurable
    · exact testBound_integrable v hφ hcφ
    · exact fun n ↦ Filter.Eventually.of_forall fun x ↦
        norm_testFlux_le_testBound v φ (F n) x (hbound n x)
    · filter_upwards [hlim] with x hx
      exact testFlux_tendsto v φ hx
  have hz : (fun n ↦ ∫ x, testFlux v φ (F n) x ∂μ) = fun _ ↦ 0 := by
    funext n
    exact integral_testFlux_eq_zero v hφ hcφ (hF n) (hdiv n)
  rw [hz] at hc
  exact tendsto_nhds_unique hc tendsto_const_nhds

omit [FiniteDimensional ℝ E] in
/-- The limiting test flux is integrable even when the limiting vector field is not
continuous (for example, a normalized polynomial gradient at its critical points). -/
theorem testFlux_limit_integrable
    (v : ι → E) {φ : E → ℝ} {F : ℕ → E → ι → ℝ} {G : E → ι → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ)
    (hF : ∀ n i, Continuous (fun x ↦ F n x i))
    (hbound : ∀ n x i, ‖F n x i‖ ≤ 1)
    (hlim : ∀ᵐ x ∂μ, ∀ i, Tendsto (fun n ↦ F n x i) atTop (𝓝 (G x i))) :
    Integrable (testFlux v φ G) μ := by
  have hl : ∀ᵐ x ∂μ, Tendsto (fun n ↦ testFlux v φ (F n) x) atTop
      (𝓝 (testFlux v φ G x)) := by
    filter_upwards [hlim] with x hx
    exact testFlux_tendsto v φ hx
  have hm : AEStronglyMeasurable (testFlux v φ G) μ :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun n ↦ (testFlux_continuous v hφ (hF n)).aestronglyMeasurable) hl
  apply (testBound_integrable v hφ hcφ).mono' hm
  filter_upwards [hl] with x hx
  exact le_of_tendsto hx.norm (Filter.Eventually.of_forall fun n ↦
    norm_testFlux_le_testBound v φ (F n) x (hbound n x))

/-- A nonnegative limiting flux with positive-measure support obstructs a sequence of
uniformly bounded divergence-free fields. -/
theorem nonnegative_limit_obstruction
    (v : ι → E) {φ : E → ℝ} {F : ℕ → E → ι → ℝ} {G : E → ι → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ)
    (hF : ∀ n i, ContDiff ℝ 1 (fun x ↦ F n x i))
    (hdiv : ∀ n x, divergence v (F n) x = 0)
    (hbound : ∀ n x i, ‖F n x i‖ ≤ 1)
    (hlim : ∀ᵐ x ∂μ, ∀ i, Tendsto (fun n ↦ F n x i) atTop (𝓝 (G x i)))
    (hnonneg : ∀ᵐ x ∂μ, 0 ≤ testFlux v φ G x)
    (hpos : 0 < μ (Function.support (testFlux v φ G))) : False := by
  have hi := testFlux_limit_integrable v hφ hcφ (fun n i ↦ (hF n i).continuous)
    hbound hlim
  have hp := (integral_pos_iff_support_of_nonneg_ae hnonneg hi).2 hpos
  rw [integral_testFlux_limit_eq_zero v hφ hcφ hF hdiv hbound hlim] at hp
  exact lt_irrefl _ hp

section Radial

/-- Squared Euclidean radius, used on the coordinate space with its usual sup-norm topology. -/
def radiusSq (x : ι → ℝ) : ℝ := ∑ i, (x i) ^ 2

/-- An increasing radial compactly supported smooth test function. -/
def radialTest (x : ι → ℝ) : ℝ := -expNegInvGlue (1 - radiusSq x)

/-- The radial derivative is a nonnegative scalar multiple of the radius vector. -/
def radialWeight (x : ι → ℝ) : ℝ :=
  2 * ((1 - radiusSq x)⁻¹) ^ 2 * expNegInvGlue (1 - radiusSq x)

theorem radiusSq_contDiff : ContDiff ℝ 1 (radiusSq : (ι → ℝ) → ℝ) := by
  unfold radiusSq
  fun_prop

theorem radialTest_contDiff : ContDiff ℝ 1 (radialTest : (ι → ℝ) → ℝ) := by
  exact (expNegInvGlue.contDiff.comp (contDiff_const.sub radiusSq_contDiff)).neg

theorem radialWeight_nonneg (x : ι → ℝ) : 0 ≤ radialWeight x := by
  unfold radialWeight
  exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (expNegInvGlue.nonneg _)

theorem radialWeight_pos (x : ι → ℝ) (hx : radiusSq x < 1) : 0 < radialWeight x := by
  unfold radialWeight
  have hp : 0 < 1 - radiusSq x := sub_pos.mpr hx
  exact mul_pos (mul_pos (by norm_num) (sq_pos_of_pos (inv_pos.mpr hp)))
    (expNegInvGlue.pos_of_pos hp)

theorem radialTest_hasCompactSupport : HasCompactSupport (radialTest : (ι → ℝ) → ℝ) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : ι → ℝ) 1)
  intro x hx
  have hr : 1 ≤ radiusSq x := by
    by_contra h
    have hrs : radiusSq x < 1 := lt_of_not_ge h
    have hn : ‖x‖ ≤ 1 := by
      apply (pi_norm_le_iff_of_nonneg (by norm_num)).2
      intro i
      have hs : (x i) ^ 2 ≤ radiusSq x :=
        Finset.single_le_sum (fun j _ ↦ sq_nonneg (x j)) (Finset.mem_univ i)
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> nlinarith [sq_nonneg (x i + 1), sq_nonneg (x i - 1)]
    exact hx (by simpa only [Metric.mem_closedBall, dist_zero_right] using hn)
  simp only [radialTest, expNegInvGlue.zero_of_nonpos (sub_nonpos.mpr hr), neg_zero]

/-- Explicit derivative of the squared radius in any direction. -/
theorem radiusSq_hasFDerivAt (x : ι → ℝ) :
    HasFDerivAt radiusSq (∑ i, (2 * x i) • (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)) x := by
  unfold radiusSq
  apply HasFDerivAt.fun_sum
  intro i _
  convert (hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : ι ↦ ℝ) i x).pow 2 using 1; simp

theorem expNegInvGlue_hasDerivAt (s : ℝ) :
    HasDerivAt expNegInvGlue (s⁻¹ ^ 2 * expNegInvGlue s) s := by
  simpa using expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (1 : Polynomial ℝ) s

variable [DecidableEq ι]

theorem radialTest_fderiv_coordinate (x : ι → ℝ) (i : ι) :
    fderiv ℝ radialTest x (Pi.single i 1) = radialWeight x * x i := by
  have hi : HasFDerivAt (fun y : ι → ℝ ↦ 1 - radiusSq y)
      (0 - ∑ j, (2 * x j) • (ContinuousLinearMap.proj j : (ι → ℝ) →L[ℝ] ℝ)) x :=
    (hasFDerivAt_const (1 : ℝ) x).sub (radiusSq_hasFDerivAt x)
  have hd := (expNegInvGlue_hasDerivAt (1 - radiusSq x)).comp_hasFDerivAt x hi
  have he : fderiv ℝ radialTest x =
      - (((1 - radiusSq x)⁻¹ ^ 2 * expNegInvGlue (1 - radiusSq x)) •
        (0 - ∑ j, (2 * x j) • (ContinuousLinearMap.proj j : (ι → ℝ) →L[ℝ] ℝ))) := hd.neg.fderiv
  rw [he]
  simp [radialWeight, Pi.single_apply]
  ring

theorem radialTest_flux (F : (ι → ℝ) → ι → ℝ) (x : ι → ℝ) :
    testFlux (fun i ↦ Pi.single i 1) radialTest F x =
      radialWeight x * ∑ i, x i * F x i := by
  simp only [testFlux, radialTest_fderiv_coordinate, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

end Radial

section Normalization

/-- The everywhere-regular normalization used in the minimal graph equation. -/
def normalizedField (g : E → ι → ℝ) (x : E) (i : ι) : ℝ :=
  g x i / Real.sqrt (1 + radiusSq (g x))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] in
theorem normalization_pos (g : E → ι → ℝ) (x : E) : 0 < 1 + radiusSq (g x) := by
  have : 0 ≤ radiusSq (g x) := Finset.sum_nonneg fun i _ ↦ sq_nonneg (g x i)
  linarith

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
theorem normalizedField_contDiff {g : E → ι → ℝ}
    (hg : ∀ i, ContDiff ℝ 1 (fun x ↦ g x i)) (i : ι) :
    ContDiff ℝ 1 (fun x ↦ normalizedField g x i) := by
  have hs : ContDiff ℝ 1 (fun x ↦ 1 + radiusSq (g x)) := by
    apply contDiff_const.add
    apply ContDiff.sum
    intro j _
    exact (hg j).pow 2
  exact (hg i).div (hs.sqrt (fun x ↦ (normalization_pos g x).ne'))
    (fun x ↦ (Real.sqrt_pos.mpr (normalization_pos g x)).ne')

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] in
theorem normalizedField_norm_le_one (g : E → ι → ℝ) (x : E) (i : ι) :
    ‖normalizedField g x i‖ ≤ 1 := by
  have hs := Real.sqrt_pos.mpr (normalization_pos g x)
  have he := Real.sq_sqrt (normalization_pos g x).le
  have hi : (g x i) ^ 2 ≤ radiusSq (g x) :=
    Finset.single_le_sum (fun j _ ↦ sq_nonneg (g x j)) (Finset.mem_univ i)
  have hl : |g x i| ≤ Real.sqrt (1 + radiusSq (g x)) := by
    nlinarith [sq_abs (g x i)]
  simp only [normalizedField, norm_div, Real.norm_eq_abs, abs_of_pos hs]
  exact (div_le_one hs).2 hl

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
/-- Derivative of the squared denominator in an arbitrary direction. -/
theorem normalization_hasFDerivAt {g : E → ι → ℝ}
    (hg : ∀ i, ContDiff ℝ 1 (fun x ↦ g x i)) (x : E) :
    HasFDerivAt (fun y ↦ 1 + radiusSq (g y))
      (∑ i, (2 * g x i) • fderiv ℝ (fun y ↦ g y i) x) x := by
  have hd : HasFDerivAt (fun y ↦ radiusSq (g y))
      (∑ i, (2 * g x i) • fderiv ℝ (fun y ↦ g y i) x) x := by
    apply HasFDerivAt.fun_sum
    intro i _
    convert ((hg i).differentiable (by norm_num) x).hasFDerivAt.pow 2 using 1; simp
  convert (hasFDerivAt_const (1 : ℝ) x).add hd using 1; simp

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
/-- Differentiating the normalized field gives the exact denominator needed by the
minimal graph operator. -/
theorem normalizedField_fderiv {g : E → ι → ℝ}
    (hg : ∀ i, ContDiff ℝ 1 (fun x ↦ g x i)) (x v : E) (i : ι) :
    fderiv ℝ (fun y ↦ normalizedField g y i) x v =
      ((1 + radiusSq (g x)) * fderiv ℝ (fun y ↦ g y i) x v -
        g x i * ∑ j, g x j * fderiv ℝ (fun y ↦ g y j) x v) /
      (Real.sqrt (1 + radiusSq (g x))) ^ 3 := by
  let s := 1 + radiusSq (g x)
  have hs : 0 < s := normalization_pos g x
  have hroot : Real.sqrt s ≠ 0 := (Real.sqrt_pos.mpr hs).ne'
  have hsq : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs.le
  have houter : HasDerivAt (fun r : ℝ ↦ (Real.sqrt r)⁻¹)
      (-(Real.sqrt s ^ 2)⁻¹ * (1 / (2 * Real.sqrt s))) s := by
    exact (hasDerivAt_inv hroot).comp s (Real.hasDerivAt_sqrt hs.ne')
  have hd := houter.comp_hasFDerivAt x (normalization_hasFDerivAt hg x)
  have hp := (((hg i).differentiable (by norm_num) x).hasFDerivAt).mul hd
  have he : fderiv ℝ (fun y ↦ normalizedField g y i) x =
      g x i • ((-(Real.sqrt s ^ 2)⁻¹ * (1 / (2 * Real.sqrt s))) •
        (∑ j, (2 * g x j) • fderiv ℝ (fun y ↦ g y j) x)) +
      (Real.sqrt s)⁻¹ • fderiv ℝ (fun y ↦ g y i) x := by
    simpa only [normalizedField, div_eq_mul_inv, Pi.mul_def, Function.comp_def, s] using hp.fderiv
  rw [he]
  simp only [add_apply, smul_apply,
    sum_apply, smul_eq_mul]
  change _ = (s * _ - _) / (Real.sqrt s) ^ 3
  have hsum : (∑ j, 2 * g x j * fderiv ℝ (fun y ↦ g y j) x v) =
      2 * ∑ j, g x j * fderiv ℝ (fun y ↦ g y j) x v := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsum]
  field_simp
  rw [hsq]
  ring

/-- The numerator of the divergence of the normalized field. For `g = ∇u`, this is
the polynomial minimal graph operator. -/
def minimalFieldNumerator (v : ι → E) (g : E → ι → ℝ) (x : E) : ℝ :=
  (1 + radiusSq (g x)) * divergence v g x -
    ∑ i, ∑ j, g x i * g x j * fderiv ℝ (fun y ↦ g y j) x (v i)

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
theorem divergence_normalizedField (v : ι → E) {g : E → ι → ℝ}
    (hg : ∀ i, ContDiff ℝ 1 (fun x ↦ g x i)) (x : E) :
    divergence v (normalizedField g) x = minimalFieldNumerator v g x /
      (Real.sqrt (1 + radiusSq (g x))) ^ 3 := by
  simp only [divergence, normalizedField_fderiv hg, minimalFieldNumerator,
    ← Finset.sum_div, Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
theorem divergence_normalizedField_eq_zero (v : ι → E) {g : E → ι → ℝ}
    (hg : ∀ i, ContDiff ℝ 1 (fun x ↦ g x i))
    (hmin : ∀ x, minimalFieldNumerator v g x = 0) (x : E) :
    divergence v (normalizedField g) x = 0 := by
  rw [divergence_normalizedField v hg x, hmin, zero_div]

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
/-- Dilation preserves zero divergence. -/
theorem divergence_dilate (v : ι → E) {F : E → ι → ℝ}
    (hF : ∀ i, ContDiff ℝ 1 (fun x ↦ F x i)) (r : ℝ) (x : E) :
    divergence v (fun y ↦ F (r • y)) x = r * divergence v F (r • x) := by
  unfold divergence
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hd := (((hF i).differentiable (by norm_num) (r • x)).hasFDerivAt).comp x
    ((hasFDerivAt_id x).const_smul r)
  have he := congrArg (fun L : E →L[ℝ] ℝ ↦ L (v i)) hd.fderiv
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_eq_mul] using he

end Normalization

section LimitNormalization

theorem radiusSq_pos_of_ne_zero {z : ι → ℝ} (hz : z ≠ 0) : 0 < radiusSq z := by
  obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
    by_contra h
    apply hz
    ext i
    simpa using not_exists.mp h i
  exact (sq_pos_of_ne_zero hi).trans_le
    (Finset.single_le_sum (fun j _ ↦ sq_nonneg (z j)) (Finset.mem_univ i))

/-- A positive rescaling of numerator and denominator exposes the asymptotic limit. -/
theorem normalized_ratio_rescale (z : ι → ℝ) {r : ℝ} (hr : 0 < r) (i : ι) :
    z i / Real.sqrt (1 + radiusSq z) =
      (r * z i) / Real.sqrt (r ^ 2 + radiusSq (fun j ↦ r * z j)) := by
  have he : r ^ 2 + radiusSq (fun j ↦ r * z j) = r ^ 2 * (1 + radiusSq z) := by
    simp only [radiusSq, mul_pow, Finset.mul_sum, mul_add, mul_one]
  rw [he, Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hr.le]
  exact (mul_div_mul_left (z i) (Real.sqrt (1 + radiusSq z)) hr.ne').symm

/-- If a sequence of vectors has a nonzero limit after multiplication by positive scalars
tending to zero, its regularized unit vectors converge to the normalization of that limit. -/
theorem normalized_ratio_tendsto
    {g : ℕ → ι → ℝ} {r : ℕ → ℝ} {z : ι → ℝ}
    (hr : ∀ n, 0 < r n) (hr0 : Tendsto r atTop (𝓝 0))
    (hg : ∀ i, Tendsto (fun n ↦ r n * g n i) atTop (𝓝 (z i)))
    (hz : z ≠ 0) (i : ι) :
    Tendsto (fun n ↦ g n i / Real.sqrt (1 + radiusSq (g n))) atTop
      (𝓝 (z i / Real.sqrt (radiusSq z))) := by
  have hs : Tendsto (fun n ↦ r n ^ 2 + radiusSq (fun j ↦ r n * g n j)) atTop
      (𝓝 (radiusSq z)) := by
    have hsum := tendsto_finsetSum Finset.univ (fun j _ ↦ (hg j).pow 2)
    simpa only [zero_pow (by norm_num : 2 ≠ 0), zero_add, radiusSq] using (hr0.pow 2).add hsum
  have hden : Real.sqrt (radiusSq z) ≠ 0 :=
    (Real.sqrt_pos.mpr (radiusSq_pos_of_ne_zero hz)).ne'
  have ht := (hg i).div hs.sqrt hden
  convert ht using 1
  funext n
  exact normalized_ratio_rescale (g n) (hr n) i

end LimitNormalization

section PolynomialZeroSet

omit [Fintype ι] in
theorem continuous_polynomial_eval (p : MvPolynomial ι ℝ) :
    Continuous (fun x : ι → ℝ ↦ MvPolynomial.eval x p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using (continuous_const : Continuous (fun _ : ι → ℝ ↦ a))
  | add p q hp hq =>
      convert hp.add hq using 1
      ext x
      simp
  | mul_X p i hp =>
      convert hp.mul (continuous_apply i) using 1
      ext x
      simp

/-- A nonzero real polynomial in finitely many variables is nonzero almost everywhere.
The proof is induction in the number of variables, Fubini, and finiteness of univariate roots. -/
theorem mvPolynomial_eval_ne_zero_ae (n : ℕ) (p : MvPolynomial (Fin n) ℝ) (hp : p ≠ 0) :
    ∀ᵐ x : Fin n → ℝ, MvPolynomial.eval x p ≠ 0 := by
  induction n with
  | zero =>
      apply Filter.Eventually.of_forall
      intro x hx
      apply hp
      apply QuarticCompatibility.polynomial_funext
      intro y
      have hxy : y = x := Subsingleton.elim _ _
      simp only [hxy, hx, map_zero]
  | succ n ih =>
      let q := MvPolynomial.finSuccEquiv ℝ n p
      have hq : q ≠ 0 := by
        exact (map_ne_zero_iff (MvPolynomial.finSuccEquiv ℝ n)
          (MvPolynomial.finSuccEquiv ℝ n).injective).2 hp
      obtain ⟨k, hk⟩ : ∃ k, q.coeff k ≠ 0 := by
        by_contra h
        apply hq
        apply Polynomial.ext
        intro k
        simpa using not_exists.mp h k
      have hc := ih (q.coeff k) hk
      have heval : Continuous (fun z : ℝ × (Fin n → ℝ) ↦
          MvPolynomial.eval (Fin.cons z.1 z.2) p) := by
        apply (continuous_polynomial_eval p).comp
        apply continuous_pi
        intro i
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · exact continuous_fst
        · exact (continuous_apply j).comp continuous_snd
      have hmeas : MeasurableSet {z : ℝ × (Fin n → ℝ) |
          MvPolynomial.eval (Fin.cons z.1 z.2) p ≠ 0} :=
        (measurableSet_eq_fun heval.measurable measurable_const).compl
      have hprod : ∀ᵐ z : ℝ × (Fin n → ℝ),
          MvPolynomial.eval (Fin.cons z.1 z.2) p ≠ 0 := by
        apply (Measure.ae_prod_iff_ae_ae hmeas).2
        apply (Measure.ae_ae_comm hmeas).2
        filter_upwards [hc] with y hy
        let py := Polynomial.map (MvPolynomial.eval y) q
        have hpy : py ≠ 0 := by
          intro hz
          have hzero := congrArg (fun P : Polynomial ℝ ↦ P.coeff k) hz
          exact hy (by simpa [py, Polynomial.coeff_map] using hzero)
        have hroots := (Polynomial.finite_setOfPred_isRoot hpy).measure_zero volume
        have ha : ∀ᵐ t : ℝ, py.eval t ≠ 0 := by
          rw [ae_iff]
          simpa only [not_not, Polynomial.IsRoot] using hroots
        filter_upwards [ha] with t ht
        simpa only [MvPolynomial.eval_eq_eval_mv_eval', py, q] using ht
      have hpres := volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) 0
      have hfinal := hpres.quasiMeasurePreserving.ae hprod
      filter_upwards [hfinal] with x hx
      simpa [MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv,
        Fin.removeNth, Fin.succAbove_zero, Fin.cons_self_tail] using hx

end PolynomialZeroSet

section HomogeneousObstruction

variable {n : ℕ}

def evaluatedGradient (p : MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  MvPolynomial.eval x (MvPolynomial.pderiv i p)

def leadingNormalizedField (p : MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  evaluatedGradient p x i / Real.sqrt (radiusSq (evaluatedGradient p x))

theorem euler_evaluatedGradient (p : MvPolynomial (Fin n) ℝ) {d : ℕ}
    (hp : p.IsHomogeneous d) (x : Fin n → ℝ) :
    (∑ i, x i * evaluatedGradient p x i) = (d : ℝ) * MvPolynomial.eval x p := by
  have he := congrArg (MvPolynomial.eval x) (QuarticCompatibility.sum_X_mul_pderiv hp)
  simpa [evaluatedGradient] using he

theorem radial_flux_leadingNormalizedField (p : MvPolynomial (Fin n) ℝ) {d : ℕ}
    (hp : p.IsHomogeneous d) (x : Fin n → ℝ) :
    testFlux (fun i ↦ Pi.single i 1) radialTest (leadingNormalizedField p) x =
      radialWeight x * ((d : ℝ) * MvPolynomial.eval x p /
        Real.sqrt (radiusSq (evaluatedGradient p x))) := by
  rw [radialTest_flux]
  simp only [leadingNormalizedField, ← mul_div_assoc, ← Finset.sum_div]
  rw [euler_evaluatedGradient p hp x]

theorem evaluatedGradient_ne_zero_of_pos (p : MvPolynomial (Fin n) ℝ) {d : ℕ}
    (hp : p.IsHomogeneous d) (hd : 0 < d) {x : Fin n → ℝ}
    (hx : 0 < MvPolynomial.eval x p) : evaluatedGradient p x ≠ 0 := by
  intro hz
  have he := euler_evaluatedGradient p hp x
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  simp only [hz, Pi.zero_apply, mul_zero, Finset.sum_const_zero] at he
  exact (mul_pos hdR hx).ne' he.symm

/-- A nonzero nonnegative homogeneous polynomial of positive degree cannot supply the
normalized limit of uniformly bounded divergence-free fields. This is the radial flux
obstruction; its zero-set and positive-measure steps are included in the proof. -/
theorem homogeneous_nonnegative_limit_obstruction
    (p : MvPolynomial (Fin n) ℝ) {d : ℕ} (hp : p.IsHomogeneous d)
    (hd : 0 < d) (hne : p ≠ 0) (hnonneg : ∀ x, 0 ≤ MvPolynomial.eval x p)
    {F : ℕ → (Fin n → ℝ) → Fin n → ℝ}
    (hF : ∀ k i, ContDiff ℝ 1 (fun x ↦ F k x i))
    (hdiv : ∀ k x, divergence (fun i ↦ Pi.single i 1) (F k) x = 0)
    (hbound : ∀ k x i, ‖F k x i‖ ≤ 1)
    (hlim : ∀ᵐ x, ∀ i, Tendsto (fun k ↦ F k x i) atTop
      (𝓝 (leadingNormalizedField p x i))) : False := by
  have hflux_nonneg : ∀ᵐ x, 0 ≤
      testFlux (fun i ↦ Pi.single i 1) radialTest (leadingNormalizedField p) x := by
    apply Filter.Eventually.of_forall
    intro x
    rw [radial_flux_leadingNormalizedField p hp x]
    exact mul_nonneg (radialWeight_nonneg x)
      (div_nonneg (mul_nonneg (Nat.cast_nonneg d) (hnonneg x)) (Real.sqrt_nonneg _))
  have hpositive : ∀ᵐ x : Fin n → ℝ, 0 < MvPolynomial.eval x p := by
    filter_upwards [mvPolynomial_eval_ne_zero_ae n p hne] with x hx
    exact lt_of_le_of_ne (hnonneg x) hx.symm
  have hsupport : {x : Fin n → ℝ | radiusSq x < 1} ≤ᵐ[volume]
      Function.support (testFlux (fun i ↦ Pi.single i 1) radialTest
        (leadingNormalizedField p)) := by
    filter_upwards [hpositive] with x hx
    intro hr
    change testFlux (fun i ↦ Pi.single i 1) radialTest (leadingNormalizedField p) x ≠ 0
    rw [radial_flux_leadingNormalizedField p hp x]
    have hgradient := evaluatedGradient_ne_zero_of_pos p hp hd hx
    have hden : 0 < Real.sqrt (radiusSq (evaluatedGradient p x)) :=
      Real.sqrt_pos.mpr (radiusSq_pos_of_ne_zero hgradient)
    exact (mul_pos (radialWeight_pos x hr)
      (div_pos (mul_pos (by exact_mod_cast hd) hx) hden)).ne'
  have hopen : IsOpen {x : Fin n → ℝ | radiusSq x < 1} :=
    isOpen_lt radiusSq_contDiff.continuous continuous_const
  have hball : 0 < volume {x : Fin n → ℝ | radiusSq x < 1} := by
    exact hopen.measure_pos volume ⟨0, by simp [radiusSq]⟩
  exact nonnegative_limit_obstruction (fun i ↦ Pi.single i 1)
    radialTest_contDiff radialTest_hasCompactSupport hF hdiv hbound hlim hflux_nonneg
    (hball.trans_le (measure_mono_ae hsupport))

end HomogeneousObstruction

section PolynomialDilation

theorem pow_ratio_tendsto_zero {e d : ℕ} (hed : e < d) :
    Tendsto (fun r : ℝ ↦ r ^ e / r ^ d) atTop (𝓝 0) := by
  have hd : d - e ≠ 0 := by omega
  have ht := (tendsto_inv_atTop_zero : Tendsto (fun r : ℝ ↦ r⁻¹) atTop (𝓝 0)).pow (d - e)
  have he : (fun r : ℝ ↦ r ^ e / r ^ d) =ᶠ[atTop] (fun r ↦ (r⁻¹) ^ (d - e)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    rw [inv_pow, inv_eq_one_div]
    apply (div_eq_div_iff (pow_ne_zero _ hr.ne') (pow_ne_zero _ hr.ne')).2
    rw [one_mul, ← pow_add]
    congr 1
    omega
  have hz : Tendsto (fun r : ℝ ↦ (r⁻¹) ^ (d - e)) atTop (𝓝 0) := by
    simpa only [zero_pow hd] using ht
  exact hz.congr' he.symm

theorem eval_dilate_eq_sum (p : MvPolynomial ι ℝ) (x : ι → ℝ) (r : ℝ) :
    MvPolynomial.eval (r • x) p =
      ∑ m ∈ p.support, p.coeff m * (r ^ m.degree * ∏ i, (x i) ^ m i) := by
  change MvPolynomial.eval₂ (RingHom.id ℝ) (r • x) p = _
  rw [MvPolynomial.eval₂_eq']
  simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, mul_pow,
    Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finsupp.degree_eq_sum]

theorem eval_dilate_homogeneous (p : MvPolynomial ι ℝ) {d : ℕ}
    (hp : p.IsHomogeneous d) (x : ι → ℝ) (r : ℝ) :
    MvPolynomial.eval (r • x) p = r ^ d * MvPolynomial.eval x p := by
  rw [eval_dilate_eq_sum]
  change _ = r ^ d * MvPolynomial.eval₂ (RingHom.id ℝ) x p
  rw [MvPolynomial.eval₂_eq', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hd : m.degree = d := by simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hp (MvPolynomial.mem_support_iff.mp hm)
  simp only [RingHom.id_apply, hd]
  ring

theorem eval_dilate_div_pow_tendsto_zero (p : MvPolynomial ι ℝ) {d : ℕ}
    (hp : p.totalDegree < d) (x : ι → ℝ) :
    Tendsto (fun r : ℝ ↦ MvPolynomial.eval (r • x) p / r ^ d) atTop (𝓝 0) := by
  have ht : Tendsto (fun r : ℝ ↦ ∑ m ∈ p.support,
      (p.coeff m * ∏ i, (x i) ^ m i) * (r ^ m.degree / r ^ d)) atTop
      (𝓝 (∑ _m ∈ p.support, (0 : ℝ))) := by
    apply tendsto_finsetSum
    intro m hm
    have hd : m.degree < d := lt_of_le_of_lt (MvPolynomial.le_totalDegree hm) hp
    simpa using (pow_ratio_tendsto_zero hd).const_mul (p.coeff m * ∏ i, (x i) ^ m i)
  simp only [Finset.sum_const_zero] at ht
  convert ht using 1
  funext r
  rw [eval_dilate_eq_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro m hm
  ring

end PolynomialDilation


end FluxObstruction
end

end ComponentFluxObstruction


/- Component: FluxPolynomial -/
section ComponentFluxPolynomial

/- Requires PolynomialBasics and FluxObstruction. -/
noncomputable section

open MeasureTheory Filter MvPolynomial
open scoped Topology BigOperators

namespace FluxPolynomial

open QuarticPolynomialBasics FluxObstruction

variable {ι : Type*} [Fintype ι]

theorem contDiff_eval (p : MvPolynomial ι ℝ) :
    ContDiff ℝ 1 (fun x : ι → ℝ ↦ eval x p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using (contDiff_const : ContDiff ℝ 1 (fun _ : ι → ℝ ↦ a))
  | add p q hp hq => simpa using hp.add hq
  | mul_X p i hp => simpa using hp.mul (by fun_prop : ContDiff ℝ 1 (fun x : ι → ℝ ↦ x i))

theorem eval_dilate_div_pow_tendsto (p : MvPolynomial ι ℝ) {d : ℕ}
    (hd : 0 < d) (hp : p.totalDegree ≤ d) (x : ι → ℝ) :
    Tendsto (fun r : ℝ ↦ eval (r • x) p / r ^ d) atTop
      (𝓝 (eval x (homogeneousComponent d p))) := by
  let T := homogeneousComponent d p
  let R := p - T
  have hRdeg : R.totalDegree < d := by
    have h := totalDegree_sub_homogeneousComponent_le p d hp
    dsimp [R, T]
    omega
  have hR := eval_dilate_div_pow_tendsto_zero R hRdeg x
  have hT : Tendsto (fun r : ℝ ↦ eval (r • x) T / r ^ d) atTop (𝓝 (eval x T)) := by
    have he : (fun r : ℝ ↦ eval (r • x) T / r ^ d) =ᶠ[atTop] fun _ ↦ eval x T := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
      rw [eval_dilate_homogeneous T (homogeneousComponent_isHomogeneous d p) x r]
      field_simp
    exact tendsto_const_nhds.congr' he.symm
  have hsplit : p = T + R := by dsimp [T, R]; ring
  have he : (fun r : ℝ ↦ eval (r • x) p / r ^ d) =
      (fun r : ℝ ↦ eval (r • x) T / r ^ d + eval (r • x) R / r ^ d) := by
    funext r
    rw [hsplit, map_add, add_div]
  rw [he]
  simpa only [add_zero] using hT.add hR

variable {n : ℕ}

theorem minimalFieldNumerator_evaluatedGradient (p : MvPolynomial (Fin n) ℝ)
    (x : Fin n → ℝ) :
    minimalFieldNumerator (fun i ↦ Pi.single i 1) (evaluatedGradient p) x =
      eval x (minimalGraphOperator p) := by
  simp [minimalFieldNumerator, divergence, evaluatedGradient, radiusSq,
    minimalGraphOperator, fderiv_eval, evalFDeriv_apply, Pi.single_apply]

def dilationRadius (k : ℕ) : ℝ := (k + 1 : ℕ)

theorem dilationRadius_pos (k : ℕ) : 0 < dilationRadius k := by
  unfold dilationRadius
  positivity

theorem dilationRadius_tendsto : Tendsto dilationRadius atTop atTop :=
  tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)

/-- The flux obstruction for an actual polynomial solution of the minimal graph equation. -/
theorem top_not_nonnegative (p : MvPolynomial (Fin n) ℝ)
    (hmin : minimalGraphOperator p = 0) (hdeg : 2 ≤ p.totalDegree) :
    ¬ ∀ x, 0 ≤ eval x (homogeneousComponent p.totalDegree p) := by
  intro hnonneg
  let d := p.totalDegree - 1
  have hd : 0 < d := by dsimp [d]; omega
  have hdegree : d + 1 = p.totalDegree := by dsimp [d]; omega
  let top := homogeneousComponent (d + 1) p
  have htop : top.IsHomogeneous (d + 1) := homogeneousComponent_isHomogeneous _ _
  have hne : top ≠ 0 := by
    dsimp [top]
    rw [hdegree]
    exact top_homogeneousComponent_ne_zero p (by omega)
  have htop_nonneg : ∀ x, 0 ≤ eval x top := by simpa [top, hdegree] using hnonneg
  have hg : ∀ i, ContDiff ℝ 1 (fun x ↦ evaluatedGradient p x i) :=
    fun i ↦ contDiff_eval (pderiv i p)
  have hnorm : ∀ i, ContDiff ℝ 1 (fun x ↦ normalizedField (evaluatedGradient p) x i) :=
    normalizedField_contDiff hg
  let F : ℕ → (Fin n → ℝ) → Fin n → ℝ := fun k x ↦
    normalizedField (evaluatedGradient p) (dilationRadius k • x)
  have hF : ∀ k i, ContDiff ℝ 1 (fun x ↦ F k x i) := by
    intro k i
    exact (hnorm i).comp (by fun_prop)
  have hdiv : ∀ k x, divergence (fun i ↦ Pi.single i 1) (F k) x = 0 := by
    intro k x
    rw [show F k = fun y ↦ normalizedField (evaluatedGradient p)
      (dilationRadius k • y) from rfl]
    rw [divergence_dilate _ hnorm]
    have hz : ∀ y, minimalFieldNumerator (fun i ↦ Pi.single i 1) (evaluatedGradient p) y = 0 := by
      intro y
      rw [minimalFieldNumerator_evaluatedGradient, hmin, map_zero]
    rw [divergence_normalizedField_eq_zero _ hg hz, mul_zero]
  have hbound : ∀ k x i, ‖F k x i‖ ≤ 1 := by
    intro k x i
    exact normalizedField_norm_le_one _ _ _
  have hlim : ∀ᵐ x, ∀ i, Tendsto (fun k ↦ F k x i) atTop
      (𝓝 (leadingNormalizedField top x i)) := by
    filter_upwards [mvPolynomial_eval_ne_zero_ae n top hne] with x hx
    have hpx : 0 < eval x top := lt_of_le_of_ne (htop_nonneg x) hx.symm
    have hgrad : evaluatedGradient top x ≠ 0 :=
      evaluatedGradient_ne_zero_of_pos top htop (by omega) hpx
    intro i
    apply normalized_ratio_tendsto
      (r := fun k ↦ (dilationRadius k)⁻¹ ^ d)
    · intro k
      exact pow_pos (inv_pos.mpr (dilationRadius_pos k)) d
    · have hr := (tendsto_inv_atTop_zero.comp dilationRadius_tendsto).pow d
      simpa only [zero_pow hd.ne', Function.comp_def] using hr
    · intro j
      have hpd : (pderiv j p).totalDegree ≤ d :=
        totalDegree_pderiv_le_of_totalDegree_le p j d (by omega)
      have hh := (eval_dilate_div_pow_tendsto (pderiv j p) hd hpd x).comp
        dilationRadius_tendsto
      simpa only [evaluatedGradient, top, pderiv_homogeneousComponent,
        Function.comp_def, div_eq_mul_inv, inv_pow, mul_comm] using hh
    · exact hgrad
  exact homogeneous_nonnegative_limit_obstruction top htop (by omega) hne htop_nonneg
    hF hdiv hbound hlim

theorem minimalGraphOperator_neg (p : MvPolynomial (Fin n) ℝ) :
    minimalGraphOperator (-p) = -minimalGraphOperator p := by
  simp only [minimalGraphOperator, map_neg, neg_sq, mul_neg,
    Finset.sum_neg_distrib]
  ring_nf

/-- Every nonaffine polynomial minimal graph has a leading homogeneous term taking
both positive and negative values. -/
theorem top_changes_sign (p : MvPolynomial (Fin n) ℝ)
    (hmin : minimalGraphOperator p = 0) (hdeg : 2 ≤ p.totalDegree) :
    (∃ x, eval x (homogeneousComponent p.totalDegree p) < 0) ∧
      (∃ x, 0 < eval x (homogeneousComponent p.totalDegree p)) := by
  constructor
  · obtain ⟨x, hx⟩ := not_forall.mp (top_not_nonnegative p hmin hdeg)
    exact ⟨x, lt_of_not_ge hx⟩
  · have hminneg : minimalGraphOperator (-p) = 0 := by
      rw [minimalGraphOperator_neg, hmin, neg_zero]
    have hdegneg : 2 ≤ (-p).totalDegree := by simpa using hdeg
    obtain ⟨x, hx⟩ := not_forall.mp (top_not_nonnegative (-p) hminneg hdegneg)
    refine ⟨x, ?_⟩
    have hn : eval x (homogeneousComponent (-p).totalDegree (-p)) < 0 := lt_of_not_ge hx
    simpa only [totalDegree_neg, map_neg, neg_lt_zero] using hn


end FluxPolynomial
end

end ComponentFluxPolynomial


/- Component: FinalTheorem -/
section ComponentFinalTheorem

noncomputable section
open MvPolynomial

namespace QuarticMinimal

theorem no_degree_four_minimal_polynomial
    {n : ℕ} (P : MvPolynomial (Fin n) ℝ) (hdeg : P.totalDegree = 4)
    (hM : minimalOperator P = 0) : False := by
  have hL : leadingOperator (homogeneousComponent 4 P) = 0 :=
    QuarticPolynomialBasics.cubicOperator_top_eq_zero P 4 (by omega) (by omega) hM
  have hs := homogeneous_quartic_has_one_sign (homogeneousComponent 4 P)
    (homogeneousComponent_isHomogeneous 4 P) hL
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := FluxPolynomial.top_changes_sign P hM (by omega)
  rw [hdeg] at hx hy
  rcases hs with hnonneg | hnonpos
  · exact (not_lt_of_ge (hnonneg x)) hx
  · exact (not_lt_of_ge (hnonpos y)) hy

theorem affine_of_degree_le_four_minimal
    {n : ℕ} (P : MvPolynomial (Fin n) ℝ) (hdegree : P.totalDegree ≤ 4)
    (hminimal : minimalOperator P = 0) : P.totalDegree ≤ 1 := by
  by_cases htwo : P.totalDegree ≤ 2
  · exact affine_of_quadratic_minimal P htwo hminimal
  have hcases : P.totalDegree = 3 ∨ P.totalDegree = 4 := by omega
  rcases hcases with hthree | hfour
  · cases n with
    | zero =>
      have hz := QuarticPolynomialBasics.totalDegree_zero_variables P
      omega
    | succ n =>
      exact (no_degree_three_minimal_polynomial P hthree hminimal).elim
  · exact (no_degree_four_minimal_polynomial P hfour hminimal).elim

end QuarticMinimal

theorem target : fcTypeOfName% "Math30Catalog.source28" := by
  intro n P hdegree hminimal
  exact QuarticMinimal.affine_of_degree_le_four_minimal P hdegree hminimal
end

end ComponentFinalTheorem


/-
License for the attributed Mathlib adaptations above:
                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "{}"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright {yyyy} {name of copyright owner}

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

-/

