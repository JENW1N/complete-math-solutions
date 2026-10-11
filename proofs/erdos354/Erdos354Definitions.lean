/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Mathlib

/-!
# Shared Erdős 354 definitions, with only a Mathlib dependency

The indexed finite-sum and completeness definitions are copied from
FormalConjecturesForMathlib.NumberTheory.AdditivelyComplete. The floor and
interleaving definitions are copied from FormalConjectures.ErdosProblems.354.
No conjecture theorem or answer placeholder is imported.
-/

/-- Finite sums using each selected index once. -/
def subseqSums' {M : Type*} [AddCommMonoid M] (A : ℕ → M) : Set M :=
  {n | ∃ B : Finset ℕ, n = ∑ i ∈ B, A i}

/-- Every sufficiently large value is an indexed finite sum. -/
def IsAddCompleteNatSeq' {M : Type*} [AddCommMonoid M] [Preorder M]
    (A : ℕ → M) : Prop :=
  ∀ᶠ k in Filter.atTop, k ∈ subseqSums' A

namespace Erdos354

/-- The sequence of floors of a scaled geometric progression. -/
noncomputable def FloorMultiples (a γ : ℝ) (n : ℕ) : ℤ := ⌊γ ^ n * a⌋

/-- Interleave both sequences, retaining distinct occurrences of equal values. -/
noncomputable def FloorMultiples.interleave (a b γ : ℝ) (n : ℕ) : ℤ :=
  if n % 2 = 0 then FloorMultiples a γ (n / 2)
  else FloorMultiples b γ (n / 2)

end Erdos354
