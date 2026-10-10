import FormalConjectures.GreensOpenProblems.«40»
import TaskSupport

/-!
# Asymptotically optimal binary linear covering codes of radius two

Authors of the accompanying paper: Jensen Kohlmeyer and Liam Kruer.
Contact: jenwin@purdue.edu; kruerl@purdue.edu.

Complete single-file proof of the formalized Green 40 radius-two target.
All helper lemmas are included below. The only external imports are the
problem library and the challenge's trusted TaskSupport module.

Pinned formal-conjectures: 8432eac998110a563e03df65a28c117e97c8c142.
Pinned mathlib: 0df444a360eaa60ab8c11dca51a86af692955474.
Lean: 4.33.1.

The proof uses a finite linear interpolation operator, quadratic-map
doubling, graph repair, and a parity-check construction. Its code includes
a zero column and uses the sufficient bound 1 + 10 / 2^(c/2).

OpenAI's ChatGPT/Codex assisted with proof development, the operator
formulation, the Lean formalization, and preparation of the paper.

The included sphere-covering lower-bound lemmas are credited to the
public Conjectures.io contribution "Green 40 sphere-covering lower bounds":
https://github.com/conjectures-io/conjectures-contribution/tree/main/contributions/green-40-f-two-eq-one/61648655993994f3bfd0ae9b44322f5541653c3d63d5c284213e49162addebe5

This file includes the imports and the Bounty namespace. For the
Conjectures.io proof-body editor, use the separately supplied Submission.lean,
whose trusted imports and outer namespace are supplied by the challenge.
-/

namespace Bounty



/- Binary quadratic maps and a finite interpolation operator for Green 40. -/


noncomputable section


open Filter Finset
open scoped ENNReal Pointwise

namespace Green40Proof

abbrev B := ZMod 2

theorem binary_cases (a : B) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

section Binary
variable {M : Type*} [AddCommGroup M] [Module B M]

theorem twice (x : M) : x + x = 0 := by
  have h : (2 : B) = 0 := by decide
  simpa only [two_smul, zero_smul] using congrArg (fun a : B => a • x) h

theorem neg_binary (x : M) : -x = x := by
  apply neg_eq_of_add_eq_zero_left
  exact twice x

theorem sub_binary (x y : M) : x - y = x + y := by simp [neg_binary, sub_eq_add_neg]

end Binary

section Polar
variable {V H : Type*} [AddCommGroup V] [Module B V]
  [AddCommGroup H] [Module B H]

def bp (Q : V → H) (a x : V) : H := Q (a + x) + Q a + Q x

theorem bp_comm (Q : V → H) (a x : V) : bp Q a x = bp Q x a := by
  unfold bp
  rw [add_comm a x]
  abel

theorem bp_zero (Q : V → H) (h0 : Q 0 = 0) (a : V) : bp Q a 0 = 0 := by
  simp [twice, bp, h0]

theorem bp_self (Q : V → H) (h0 : Q 0 = 0) (a : V) : bp Q a a = 0 := by
  simp [twice, bp, h0]

def IsQuadratic (Q : V → H) : Prop :=
  Q 0 = 0 ∧ ∀ a x y, bp Q a (x + y) = bp Q a x + bp Q a y

def derivative (Q : V → H) (hq : IsQuadratic Q) (a : V) : V →ₗ[B] H :=
  AddMonoidHom.toZModLinearMap 2
    { toFun := bp Q a
      map_zero' := bp_zero Q hq.1 a
      map_add' := hq.2 a }

theorem derivative_apply (Q : V → H) (hq : IsQuadratic Q) (a x : V) :
    derivative Q hq a x = bp Q a x := rfl

variable {V' : Type*} [AddCommGroup V'] [Module B V']

theorem bp_comp (Q : V → H) (E : V' →ₗ[B] V) (a x : V') :
    bp (fun y => Q (E y)) a x = bp Q (E a) (E x) := by
  simp [bp]

theorem quadratic_comp (Q : V → H) (hq : IsQuadratic Q) (E : V' →ₗ[B] V) :
    IsQuadratic (fun y => Q (E y)) := by
  exact ⟨by simpa [twice, neg_binary, bp_zero, bp_self, derivative_apply] using hq.1, by intros; simp only [bp_comp, map_add, hq.2]⟩

end Polar

section Interpolation
variable (F : Type*) [Field F] [Algebra B F] [Fintype F] [DecidableEq F]
  (H : Type*) [AddCommGroup H] [Module B H] [Finite H]

abbrev Coord := Fin (Module.finrank B H)
abbrev Z := F → Coord H → F

noncomputable def coords : H ≃ₗ[B] (Coord H → B) :=
  (Module.finBasis B H).equivFun

noncomputable def inc : H →ₗ[B] Z F H :=
  { toFun := fun h _ j => algebraMap B F (coords H h j)
    map_add' := by intros; ext; simp
    map_smul' := by intros; ext; simp [Algebra.smul_def] }

noncomputable def delta : Z F H →ₗ[F] Z F H :=
  { toFun := fun t r j => r * t r j + ∑ s, t s j
    map_add' := by intros; ext; simp [mul_add, Finset.sum_add_distrib]; ring
    map_smul' := by
      intro m t
      ext r j
      change r * (m * t r j) + (∑ s, m * t s j) = m * (r * t r j + ∑ s, t s j)
      rw [mul_add, Finset.mul_sum]
      ring }

noncomputable def project (l : F →ₗ[B] B) : Z F H →ₗ[B] H :=
  (coords H).symm.toLinearMap.comp
    ({
      toFun := fun t j => l (∑ r ∈ Finset.univ.erase 0, t r j)
      map_add' := by intros; ext; simp [Finset.sum_add_distrib]
      map_smul' := by
        intro a t
        ext j
        change l (∑ r ∈ Finset.univ.erase 0, a • t r j) =
          a • l (∑ r ∈ Finset.univ.erase 0, t r j)
        rw [← Finset.smul_sum]
        exact l.map_smul a _ } : Z F H →ₗ[B] (Coord H → B))

theorem interp_support (r : F) (t : Z F H) (h : H)
    (heq : delta F H t + r • t = inc F H h) :
    t = fun s j => if s = r then algebraMap B F (coords H h j) else 0 := by
  classical
  have hsum (j : Coord H) : (∑ s, t s j) = algebraMap B F (coords H h j) := by
    have := congrFun (congrFun heq r) j
    dsimp [delta, inc] at this
    have hz : r * t r j + r * t r j = 0 := twice _
    linear_combination this - hz
  have hout (s : F) (hs : s ≠ r) (j : Coord H) : t s j = 0 := by
    have hh := congrFun (congrFun heq s) j
    dsimp [delta, inc] at hh
    rw [hsum] at hh
    have hz : (s + r) * t s j = 0 := by linear_combination hh
    exact (mul_eq_zero.mp hz).resolve_left (by simpa [twice, neg_binary, bp_zero, bp_self, derivative_apply, ← sub_binary] using sub_ne_zero.mpr hs)
  ext s j
  split_ifs with hs
  · subst s
    have hh := hsum j
    rw [Finset.sum_eq_single r] at hh
    · exact hh
    · intro b _ hb
      exact hout b hb j
    · simp
  · exact hout s hs j

theorem interp_project (l : F →ₗ[B] B) (hl : l 1 = 1)
    (r : F) (t : Z F H) (h : H)
    (heq : delta F H t + r • t = inc F H h) :
    project F H l t = if r = 0 then 0 else h := by
  classical
  have hlift (b : B) : l (algebraMap B F b) = b := by
    have := l.map_smul b (1 : F)
    simpa [twice, neg_binary, bp_zero, bp_self, derivative_apply, Algebra.smul_def, hl] using this
  rw [interp_support F H r t h heq]
  apply (coords H).injective
  ext j
  simp only [project, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]
  by_cases hr : r = 0
  · subst r
    simp [apply_ite, hlift]
  · simp [apply_ite, hr, Ne.symm hr, hlift]

theorem interp_injective (r : F) (t : Z F H)
    (heq : delta F H t + r • t = 0) : t = 0 := by
  have hh := interp_support F H r t 0 (by simpa [twice, neg_binary, bp_zero, bp_self, derivative_apply] using heq)
  rw [hh]
  ext s j
  simp

end Interpolation

end Green40Proof

end


/- The doubling construction for binary quadratic maps. -/


noncomputable section

namespace Green40Proof

section Lift
variable {F K H T : Type*} [Field F] [Algebra B F] [DecidableEq F]
  [AddCommGroup K] [Module B K]
  [AddCommGroup H] [Module B H]
  [AddCommGroup T] [Module F T] [Module B T] [IsScalarTower B F T]

variable (Q : F × K → H) (I : H →ₗ[B] T) (P : T →ₗ[B] H) (D : T →ₗ[F] T)

def liftQ (x : (F × F) × (K × T)) : F × (H × T) :=
  (x.1.1 * x.1.2,
   (Q (x.1.1, x.2.1) + Q (x.1.2, x.2.1) + P (x.1.2 • x.2.2),
    x.1.1 • x.2.2 + D (x.1.2 • x.2.2) + I (Q (x.1.2, x.2.1))))

theorem lift_polar (a b u v : F) (z w : K) (s t : T) :
    bp (liftQ Q I P D) ((a,b),(z,s)) ((u,v),(w,t)) =
      (a*v+b*u,
       (bp Q (a,z) (u,w) + bp Q (b,z) (v,w) + P (b • t + v • s),
        a • t + u • s + D (b • t + v • s) + I (bp Q (b,z) (v,w)))) := by
  unfold bp liftQ
  simp only [Prod.fst_add, Prod.snd_add, Prod.mk_add_mk,
    add_smul, smul_add, map_add]
  apply Prod.ext
  · dsimp
    have hchar : (2 : F) = 0 := by
      simpa only [one_add_one_eq_two] using twice (1 : F)
    linear_combination (a*b+u*v)*hchar
  · apply Prod.ext
    · dsimp
      abel_nf
      simp only [two_smul ℤ, twice, zero_add, add_zero]
    · dsimp
      abel_nf
      simp only [two_smul ℤ, twice, zero_add, add_zero]

theorem lift_zero (hzero : ∀ z, Q (0,z) = 0) (z : K) (t : T) :
    liftQ Q I P D ((0,0),(z,t)) = 0 := by
  simp [twice, liftQ, hzero]

theorem lift_quadratic (hq : IsQuadratic Q) : IsQuadratic (liftQ Q I P D) := by
  constructor
  · simp [twice, liftQ, show Q (0,0) = 0 from hq.1]
  · rintro ⟨⟨a,b⟩,z,s⟩ ⟨⟨u,v⟩,w,t⟩ ⟨⟨u',v'⟩,w',t'⟩
    have hq1 := hq.2 (a,z) (u,w) (u',w')
    have hq2 := hq.2 (b,z) (v,w) (v',w')
    simp only [Prod.mk_add_mk] at hq1 hq2
    simp only [Prod.mk_add_mk, lift_polar, hq1, hq2,
      add_smul, smul_add, map_add, mul_add, add_mul]
    apply Prod.ext
    · dsimp; ring
    · apply Prod.ext <;> dsimp <;> abel

variable (hzero : ∀ z, Q (0,z) = 0)
  (hgood : ∀ a z u w, a ≠ 0 → bp Q (a,z) (u,w) = 0 →
    (u,w) = 0 ∨ (u,w) = (a,z))
  (hinterp : ∀ (r : F) (t : T) (h : H), D t + r • t = I h →
    P t = if r = 0 then 0 else h)
  (hinj : ∀ (r : F) (t : T), D t + r • t = 0 → t = 0)

include hzero hgood hinterp hinj

theorem lift_kernel (a b u v : F) (z w : K) (s t : T)
    (hab : a ≠ 0 ∨ b ≠ 0)
    (h : bp (liftQ Q I P D) ((a,b),(z,s)) ((u,v),(w,t)) = 0) :
    ((u,v),(w,t)) = 0 ∨ ((u,v),(w,t)) = ((a,b),(z,s)) := by
  rw [lift_polar] at h
  have h1 : a*v+b*u = 0 := congrArg Prod.fst h
  have h2 : bp Q (a,z) (u,w) + bp Q (b,z) (v,w) + P (b • t + v • s) = 0 :=
    congrArg (fun x => x.2.1) h
  have h3 : a • t + u • s + D (b • t + v • s) + I (bp Q (b,z) (v,w)) = 0 :=
    congrArg (fun x => x.2.2) h
  have hq0 : Q 0 = 0 := hzero 0
  by_cases hb : b = 0
  · subst b
    have ha := hab.resolve_right (by simp)
    have hv : v = 0 := (mul_eq_zero.mp (by simpa [twice, neg_binary, bp_zero, bp_self, derivative_apply] using h1)).resolve_left ha
    subst v
    have hY : bp Q (0,z) (0,w) = 0 := by simp [twice, bp, hzero]
    have hX : bp Q (a,z) (u,w) = 0 := by simpa [twice, neg_binary, bp_zero, bp_self, derivative_apply, hY] using h2
    rcases hgood a z u w ha hX with hh | hh
    · have hu : u = 0 := congrArg Prod.fst hh
      have hw : w = 0 := congrArg Prod.snd hh
      subst u; subst w
      have ht : t = 0 := (smul_eq_zero.mp (by simpa [twice, neg_binary, bp_zero, bp_self, derivative_apply, hY] using h3)).resolve_left ha
      simp [ht]
    · have hu : u = a := congrArg Prod.fst hh
      have hw : w = z := congrArg Prod.snd hh
      subst u; subst w
      have ht : t = s := by
        have hs : a • (t + s) = 0 := by simpa [twice, neg_binary, bp_zero, bp_self, derivative_apply, smul_add, hY] using h3
        have := (smul_eq_zero.mp hs).resolve_left ha
        simpa [twice, neg_binary, bp_zero, bp_self, derivative_apply] using (eq_neg_of_add_eq_zero_left this)
      simp [ht]
  · have hu : u = (a / b) * v := by
      have hh : b*u = a*v := by simpa [twice, neg_binary, bp_zero, bp_self, derivative_apply] using eq_neg_of_add_eq_zero_right h1
      field_simp
      linear_combination hh
    have hR : D (b • t + v • s) + (a / b) • (b • t + v • s) =
        I (bp Q (b,z) (v,w)) := by
      have hh := eq_neg_of_add_eq_zero_left h3
      simp only [neg_binary] at hh
      rw [smul_add, ← mul_smul, div_mul_cancel₀ _ hb, ← mul_smul, ← hu]
      simpa only [add_comm, add_left_comm, add_assoc] using hh
    have hPR := hinterp (a / b) (b • t + v • s) (bp Q (b,z) (v,w)) hR
    have hcases : ((u,w) = 0 ∨ (u,w) = (a,z)) ∧ a ≠ 0 ∨
        ((v,w) = 0 ∨ (v,w) = (b,z)) ∧ a = 0 := by
      by_cases ha : a = 0
      · right
        have hu0 : u = 0 := by simp [ha] at hu; exact hu
        have hX : bp Q (a,z) (u,w) = 0 := by simp [twice, ha, hu0, bp, hzero]
        have hY : bp Q (b,z) (v,w) = 0 := by
          rw [hX, hPR] at h2
          simpa [twice, neg_binary, bp_zero, bp_self, derivative_apply, ha] using h2
        exact ⟨hgood b z v w hb hY, ha⟩
      · left
        have hX : bp Q (a,z) (u,w) = 0 := by
          simpa [twice, neg_binary, bp_zero, bp_self, derivative_apply, hPR, div_ne_zero ha hb, add_assoc] using h2
        exact ⟨hgood a z u w ha hX, ha⟩
    have huv : (u = 0 ∧ v = 0 ∧ w = 0) ∨ (u = a ∧ v = b ∧ w = z) := by
      rcases hcases with ⟨hh,ha⟩ | ⟨hh,ha⟩
      · rcases hh with hh | hh
        · have hu0 : u = 0 := congrArg Prod.fst hh
          have hw : w = 0 := congrArg Prod.snd hh
          have hv : v = 0 := (mul_eq_zero.mp (by simpa [twice, neg_binary, bp_zero, bp_self, derivative_apply, hu0] using h1)).resolve_left ha
          exact Or.inl ⟨hu0,hv,hw⟩
        · have hua : u = a := congrArg Prod.fst hh
          have hw : w = z := congrArg Prod.snd hh
          have hv : v = b := by
            have he : a * (v + b) = 0 := by simpa [twice, neg_binary, bp_zero, bp_self, derivative_apply, mul_add, hua, mul_comm b a] using h1
            simpa [twice, neg_binary, bp_zero, bp_self, derivative_apply] using eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp he).resolve_left ha)
          exact Or.inr ⟨hua,hv,hw⟩
      · rcases hh with hh | hh
        · have hv : v = 0 := congrArg Prod.fst hh
          have hw : w = 0 := congrArg Prod.snd hh
          exact Or.inl ⟨by simp [hv] at hu; exact hu, hv, hw⟩
        · have hv : v = b := congrArg Prod.fst hh
          have hw : w = z := congrArg Prod.snd hh
          exact Or.inr ⟨by simpa [twice, neg_binary, bp_zero, bp_self, derivative_apply, hv, hb] using hu, hv, hw⟩
    clear hu
    rcases huv with ⟨hu0,hv0,hw0⟩ | ⟨hua,hvb,hwz⟩
    · subst u; subst v; subst w
      have hRt : b • t = 0 := hinj (a/b) (b • t) (by simpa [twice, neg_binary, bp_zero, bp_self, derivative_apply, bp, hzero] using hR)
      have ht : t = 0 := (smul_eq_zero.mp hRt).resolve_left hb
      simp [ht]
    · subst u; subst v; subst w
      have hRt : b • t + b • s = 0 := hinj (a/b) (b • t + b • s)
        (by simpa [twice, neg_binary, bp_zero, bp_self, derivative_apply, bp_self Q hq0] using hR)
      have ht : t = s := by
        rw [← smul_add] at hRt
        simpa [twice, neg_binary, bp_zero, bp_self, derivative_apply] using eq_neg_of_add_eq_zero_left ((smul_eq_zero.mp hRt).resolve_left hb)
      simp [ht]

end Lift

end Green40Proof

end


/- Iterating the doubling construction. -/


noncomputable section

namespace Green40Proof

abbrev GF (c : ℕ) := GaloisField 2 c
abbrev BV (n : ℕ) := Fin n → B

structure Model (c : ℕ) where
  K : Type
  H : Type
  [addK : AddCommGroup K]
  [modK : Module B K]
  [finK : Finite K]
  [addH : AddCommGroup H]
  [modH : Module B H]
  [finH : Finite H]
  Q : GF c × K → H
  quadratic : IsQuadratic Q
  zero : ∀ z, Q (0,z) = 0
  good : ∀ a z u w, a ≠ 0 → bp Q (a,z) (u,w) = 0 →
    (u,w) = 0 ∨ (u,w) = (a,z)
  dim : Module.finrank B H + 1 = c + Module.finrank B K


def Model.step {c : ℕ} (hc : c ≠ 0) (M : Model c) : Model (c+c) := by
  letI := M.addK
  letI := M.modK
  letI := M.finK
  letI := M.addH
  letI := M.modH
  letI := M.finH
  letI : DecidableEq (GF c) := Classical.decEq _
  letI : Fintype (GF c) := Fintype.ofFinite _
  let E : GF (c+c) ≃ₗ[B] (GF c × GF c) :=
    LinearEquiv.ofFinrankEq _ _ (by
      rw [GaloisField.finrank 2 (by omega), Module.finrank_prod,
        GaloisField.finrank 2 hc])
  have hex := Module.Projective.exists_dual_eq_one B (one_ne_zero : (1 : GF c) ≠ 0)
  let l := Classical.choose hex
  have hl := Classical.choose_spec hex
  let I := inc (GF c) M.H
  let P := project (GF c) M.H l
  let D := delta (GF c) M.H
  let R := liftQ M.Q I P D
  let L : (GF (c+c) × (M.K × Z (GF c) M.H)) ≃ₗ[B]
      ((GF c × GF c) × (M.K × Z (GF c) M.H)) :=
    E.prodCongr (LinearEquiv.refl B _)
  refine {
    K := M.K × Z (GF c) M.H
    H := GF c × (M.H × Z (GF c) M.H)
    Q := fun x => R (L x)
    quadratic := quadratic_comp R (lift_quadratic M.Q I P D M.quadratic) L.toLinearMap
    zero := ?_
    good := ?_
    dim := ?_ }
  · rintro ⟨z,t⟩
    change liftQ M.Q I P D ((E 0),(z,t)) = 0
    rw [map_zero]
    exact lift_zero M.Q I P D M.zero z t
  · rintro a ⟨z,s⟩ u ⟨w,t⟩ ha hh
    have he : (E a).1 ≠ 0 ∨ (E a).2 ≠ 0 := by
      by_contra hn
      push Not at hn
      apply ha
      apply E.injective
      exact (Prod.ext hn.1 hn.2).trans (map_zero E).symm
    have hh' : bp R ((E a),(z,s)) ((E u),(w,t)) = 0 := by
      change bp (fun x => R (L.toLinearMap x)) (a,(z,s)) (u,(w,t)) = 0 at hh
      rw [bp_comp] at hh
      exact hh
    have hk := lift_kernel M.Q I P D M.zero M.good
      (interp_project (GF c) M.H l hl) (interp_injective (GF c) M.H)
      (E a).1 (E a).2 (E u).1 (E u).2 z w s t he hh'
    rcases hk with hk | hk
    · left
      apply L.injective
      simpa [twice, neg_binary, bp_zero, bp_self, derivative_apply, L] using hk
    · right
      apply L.injective
      simpa [twice, neg_binary, bp_zero, bp_self, derivative_apply, L] using hk
  · simp only [Module.finrank_prod, GaloisField.finrank 2 hc]
    have := M.dim
    omega

def baseModel : Model 1 := by
  let E : GF 1 ≃ₗ[B] B := LinearEquiv.ofFinrankEq _ _ (by
    simp [GaloisField.finrank])
  refine {
    K := BV 0
    H := BV 0
    Q := fun _ => 0
    quadratic := by constructor <;> simp [twice, bp]
    zero := by simp
    good := ?_
    dim := by simp [BV] }
  intro a z u w ha _
  have he : E a = 1 := (binary_cases (E a)).resolve_left (by simpa [twice, neg_binary, bp_zero, bp_self, derivative_apply] using ha)
  rcases binary_cases (E u) with hu | hu
  · left
    apply Prod.ext
    · exact E.injective (by simpa [twice, neg_binary, bp_zero, bp_self, derivative_apply] using hu)
    · exact Subsingleton.elim _ _
  · right
    apply Prod.ext
    · exact E.injective (hu.trans he.symm)
    · exact Subsingleton.elim _ _

def models : (r : ℕ) → Model (2 ^ r)
  | 0 => baseModel
  | r+1 => by
    simpa only [pow_succ, mul_two] using (models r).step (by positivity)

end Green40Proof

end


/- A sum basis gives a binary linear covering code, with an explicit density bound. -/


noncomputable section

open Finset
open scoped ENNReal Pointwise

namespace Green40Proof

theorem binary_support_injective (n : ℕ) :
    Function.Injective (fun x : 𝔽₂ n => Finset.univ.filter (fun i => x i ≠ 0)) := by
  intro x y h
  funext i
  have hi : x i = 0 ↔ y i = 0 := by
    have := Finset.ext_iff.mp h i
    simpa only [mem_filter, mem_univ, true_and, not_iff_not] using this
  have bx : x i = 0 ∨ x i = 1 := binary_cases (x i)
  have by' : y i = 0 ∨ y i = 1 := binary_cases (y i)
  rcases bx with hx | hx <;> rcases by' with hy | hy <;> simp_all

theorem hammingBall_card_bound (n : ℕ) :
    2 * Nat.card (Green40.hammingBall n 2) ≤ n*n+n+2 := by
  let A : Finset (Finset (Fin n)) :=
    (Finset.univ.powersetCard 0 ∪ Finset.univ.powersetCard 1) ∪ Finset.univ.powersetCard 2
  have hsupport (x : Green40.hammingBall n 2) :
      Finset.univ.filter (fun i => x.1 i ≠ 0) ∈ A := by
    have hx := x.2
    change (Finset.univ.filter (fun i => x.1 i ≠ 0)).card ≤ 2 at hx
    simp only [A, mem_union, mem_powersetCard, subset_univ, true_and]
    omega
  let f : Green40.hammingBall n 2 → A :=
    fun x => ⟨Finset.univ.filter (fun i => x.1 i ≠ 0), hsupport x⟩
  have hinj : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    exact binary_support_injective n (congrArg Subtype.val h)
  have h1 : Nat.card (Green40.hammingBall n 2) ≤ A.card := by
    simpa [twice, neg_binary, bp_zero, bp_self, derivative_apply] using Nat.card_le_card_of_injective f hinj
  have h2 : A.card ≤ 1+n+n.choose 2 := by
    have hh := (Finset.card_union_le (α := Finset (Fin n))
      (Finset.univ.powersetCard 0 ∪ Finset.univ.powersetCard 1)
      (Finset.univ.powersetCard 2)).trans
      (Nat.add_le_add_right (Finset.card_union_le
        (Finset.univ.powersetCard 0) (Finset.univ.powersetCard 1)) _)
    simpa [twice, neg_binary, bp_zero, bp_self, derivative_apply, A] using hh
  have h3 : 2 * n.choose 2 ≤ n * (n-1) := by
    rw [Nat.choose_two_right]
    omega
  have h4 : n * (n-1) + n = n*n := by
    cases n with
    | zero => simp
    | succ k => simp; ring
  omega

theorem hammingNorm_add_le {n : ℕ} (x y : 𝔽₂ n) :
    hammingNorm (x+y) ≤ hammingNorm x + hammingNorm y := by
  apply (Finset.card_le_card (s := Finset.univ.filter (fun i => (x+y) i ≠ 0))
    (t := (Finset.univ.filter (fun i => x i ≠ 0)) ∪
      (Finset.univ.filter (fun i => y i ≠ 0))) ?_).trans (Finset.card_union_le _ _)
  intro i hi
  simp only [mem_filter, mem_univ, true_and, mem_union, Pi.add_apply] at *
  by_contra hn
  push Not at hn
  simp [twice, hn] at hi

theorem hammingNorm_single_le {n : ℕ} (i : Fin n) :
    hammingNorm (Pi.single i (1 : B) : 𝔽₂ n) ≤ 1 := by
  unfold hammingNorm
  calc
    (Finset.univ.filter (fun j => (Pi.single i (1 : B) : 𝔽₂ n) j ≠ 0)).card
        ≤ ({i} : Finset (Fin n)).card := Finset.card_le_card (by
          intro j hj
          simp only [mem_filter, mem_univ, true_and] at hj
          by_contra hn
          have hji : j ≠ i := by simpa [twice, neg_binary, bp_zero, bp_self, derivative_apply] using hn
          simpa [twice, neg_binary, bp_zero, bp_self, derivative_apply, Pi.single_apply, hji, Ne.symm hji] using hj)
    _ = 1 := by simp

section Code
variable {G : Type*} [AddCommGroup G] [Module B G] [Finite G]
  (S : Finset G)
  (hS : ∀ g : G, ∃ a ∈ S, ∃ b ∈ S, a+b=g)

def columns : Fin S.card → G :=
  fun i => ((Fintype.equivFinOfCardEq (by simp : Fintype.card S = S.card)).symm i).1

theorem columns_surjective (a : S) : ∃ i, columns S i = a.1 := by
  use (Fintype.equivFinOfCardEq (by simp : Fintype.card S = S.card)) a
  simp [columns]

def parity : 𝔽₂ S.card →ₗ[B] G :=
  { toFun := fun x => ∑ i, x i • columns S i
    map_add' := by intros; simp [add_smul, Finset.sum_add_distrib]
    map_smul' := by intros; simp [Finset.smul_sum, smul_smul] }

theorem parity_single (i : Fin S.card) :
    parity S (Pi.single i (1 : B)) = columns S i := by
  simp [parity, Pi.single_apply, ite_smul]

include hS

theorem syndrome_small (g : G) : ∃ x : 𝔽₂ S.card,
    hammingNorm x ≤ 2 ∧ parity S x = g := by
  obtain ⟨a,ha,b,hb,hab⟩ := hS g
  obtain ⟨i,hi⟩ := columns_surjective S ⟨a,ha⟩
  obtain ⟨j,hj⟩ := columns_surjective S ⟨b,hb⟩
  refine ⟨Pi.single i 1 + Pi.single j 1, ?_, ?_⟩
  · exact (hammingNorm_add_le _ _).trans (by
      have := hammingNorm_single_le i
      have := hammingNorm_single_le j
      omega)
  · simp [parity_single, hi,hj,hab]

theorem parity_surjective : Function.Surjective (parity S) := by
  intro g
  obtain ⟨x,_,hx⟩ := syndrome_small S hS g
  exact ⟨x,hx⟩

theorem parity_cover : Green40.IsCoveringSubspace S.card 2 (parity S).ker := by
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨e,he,hxe⟩ := syndrome_small S hS (parity S x)
  refine ⟨x-e, ?_, e, he, sub_add_cancel _ _⟩
  change parity S (x-e) = 0
  simp [hxe]

theorem parity_card : Nat.card (parity S).ker * Nat.card G = 2 ^ S.card := by
  have hr := (parity S).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (parity_surjective S hS), finrank_top] at hr
  have hn : Module.finrank B (𝔽₂ S.card) = S.card := by simp
  rw [hn] at hr
  rw [Module.natCard_eq_pow_finrank (K := B) (V := (parity S).ker),
    Module.natCard_eq_pow_finrank (K := B) (V := G), Nat.card_zmod]
  rw [← pow_add, add_comm, hr]

theorem minDensity_le_sum_basis :
    Green40.minDensity S.card 2 ≤
      (Nat.card (Green40.hammingBall S.card 2) : ℝ≥0∞) / (Nat.card G : ℝ≥0∞) := by
  refine (iInf₂_le (parity S).ker (parity_cover S hS)).trans_eq ?_
  have hcard : (Nat.card (parity S).ker : ℝ≥0∞) * (Nat.card G : ℝ≥0∞) = 2 ^ S.card := by
    exact_mod_cast parity_card S hS
  rw [← hcard]
  exact ENNReal.mul_div_mul_left _ _
    (by exact_mod_cast (Nat.card_pos (α := (parity S).ker)).ne') (by simp)

end Code

end Green40Proof

end


/- Repairing the graph and obtaining small sum bases. -/


noncomputable section

open Finset
open scoped ENNReal Pointwise

namespace Green40Proof

theorem derivative_surj {V H : Type*} [AddCommGroup V] [Module B V] [Finite V]
    [AddCommGroup H] [Module B H] [Finite H]
    (Q : V → H) (hq : IsQuadratic Q)
    (hdim : Module.finrank B V = Module.finrank B H + 1)
    (a : V) (ha : a ≠ 0)
    (hk : ∀ x, bp Q a x = 0 → x = 0 ∨ x = a) :
    Function.Surjective (derivative Q hq a) := by
  let D := derivative Q hq a
  have hker : D.ker ≤ Submodule.span B {a} := by
    intro x hx
    rcases hk x hx with rfl | rfl
    · exact Submodule.zero_mem _
    · exact Submodule.subset_span (by simp)
  have hkdim : Module.finrank B D.ker ≤ 1 := by
    simpa only [finrank_span_singleton ha] using Submodule.finrank_mono hker
  have hr := D.finrank_range_add_finrank_ker
  have hrle := Submodule.finrank_le D.range
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  change Module.finrank B D.range = Module.finrank B H
  omega

theorem Model.graph_sums {c : ℕ} (hc : c ≠ 0) (M : Model c)
    (a : GF c) (z : M.K) (h : M.H) (ha : a ≠ 0) :
  letI := M.addK
  letI := M.modK
  letI := M.finK
  letI := M.addH
  letI := M.modH
  letI := M.finH
    ∃ x y : GF c × M.K, x+y=(a,z) ∧ M.Q x + M.Q y = h := by
  letI := M.addK
  letI := M.modK
  letI := M.finK
  letI := M.addH
  letI := M.modH
  letI := M.finH
  have hs := derivative_surj M.Q M.quadratic (by
      rw [Module.finrank_prod, GaloisField.finrank 2 hc]
      exact M.dim.symm)
    (a,z) (by intro hh; exact ha (congrArg Prod.fst hh))
    (fun x hx => M.good a z x.1 x.2 ha hx)
  obtain ⟨x,hx⟩ := hs (h + M.Q (a,z))
  refine ⟨x,(a,z)+x,?_,?_⟩
  · have hh := twice x
    calc x + ((a,z)+x) = (a,z)+(x+x) := by abel
         _ = (a,z) := by rw [hh,add_zero]
  · change M.Q ((a,z)+x) + M.Q (a,z) + M.Q x = h + M.Q (a,z) at hx
    apply add_right_cancel (b := M.Q (a,z))
    simpa only [add_comm,add_left_comm,add_assoc] using hx

def vertical {c : ℕ} (M : Model c) :
  letI := M.addK
  letI := M.modK
  letI := M.finK
  letI := M.addH
  letI := M.modH
  letI := M.finH
  (M.K × M.H) →ₗ[B] ((GF c × M.K) × M.H) := by
  letI := M.addK
  letI := M.modK
  letI := M.finK
  letI := M.addH
  letI := M.modH
  letI := M.finH
  exact
    { toFun := fun x => ((0,x.1),x.2)
      map_add' := by intros; rfl
      map_smul' := by intros; ext <;> simp }

theorem Model.exists_sum_basis {p : ℕ} (hp : 0 < p) (M : Model (2*p)) :
  letI := M.addK
  letI := M.modK
  letI := M.finK
  letI := M.addH
  letI := M.modH
  letI := M.finH
    let n := 2*p + Module.finrank B M.K
    ∃ (S : Finset ((GF (2*p) × M.K) × M.H)),
      (∀ g, ∃ a ∈ S, ∃ b ∈ S, a+b=g) ∧
      2^n ≤ S.card ∧ S.card ≤ 2^n + 2^(n-p+1) := by
  classical
  letI := M.addK
  letI := M.modK
  letI := M.finK
  letI := M.addH
  letI := M.modH
  letI := M.finH
  letI : Fintype M.K := Fintype.ofFinite _
  letI : Fintype M.H := Fintype.ofFinite _
  letI : Fintype (GF (2*p)) := Fintype.ofFinite _
  let n := 2*p + Module.finrank B M.K
  let d := p + Module.finrank B M.K
  have hd : 0 < d := by dsimp [d]; omega
  let E : (BV d × BV (d-1)) ≃ₗ[B] (M.K × M.H) :=
    LinearEquiv.ofFinrankEq _ _ (by
      simp only [Module.finrank_prod, Module.finrank_pi, Module.finrank_self,
        Fintype.card_fin, smul_eq_mul, mul_one]
      have hm := M.dim
      dsimp [d]
      omega)
  let C : Finset ((GF (2*p) × M.K) × M.H) :=
    Finset.univ.image (fun x => (x,M.Q x))
  let A : Finset ((GF (2*p) × M.K) × M.H) :=
    Finset.univ.image (fun x : BV d => vertical M (E (x,0)))
  let A' : Finset ((GF (2*p) × M.K) × M.H) :=
    Finset.univ.image (fun x : BV (d-1) => vertical M (E (0,x)))
  let S := C ∪ A ∪ A'
  have hCS : C ⊆ S := Finset.subset_union_left.trans Finset.subset_union_left
  have hAS : A ⊆ S := Finset.subset_union_right.trans Finset.subset_union_left
  have hBS : A' ⊆ S := Finset.subset_union_right
  have hcardV : Fintype.card (GF (2*p) × M.K) = 2^n := by
    rw [← Nat.card_eq_fintype_card, Module.natCard_eq_pow_finrank (K := B)]
    simp only [Nat.card_zmod, Module.finrank_prod,
      GaloisField.finrank 2 (n := 2*p) (by omega)]
    rfl
  have hcardC : C.card = 2^n := by
    dsimp only [C]
    rw [Finset.card_image_of_injective _ (by
      intro x y h
      exact congrArg Prod.fst h), Finset.card_univ, hcardV]
  have hcardA : A.card ≤ 2^d := by
    simpa [twice, neg_binary, bp_zero, bp_self, derivative_apply, BV, B] using (Finset.card_image_le (s := (Finset.univ : Finset (BV d)))
      (f := fun x => vertical M (E (x,0))))
  have hcardB : A'.card ≤ 2^(d-1) := by
    simpa [twice, neg_binary, bp_zero, bp_self, derivative_apply, BV, B] using (Finset.card_image_le (s := (Finset.univ : Finset (BV (d-1))))
      (f := fun x => vertical M (E (0,x))))
  refine ⟨S,?_,?_,?_⟩
  · rintro ⟨⟨a,z⟩,h⟩
    by_cases ha : a = 0
    · subst a
      let x := (E.symm (z,h)).1
      let y := (E.symm (z,h)).2
      refine ⟨vertical M (E (x,0)), hAS (by simp [A]),
        vertical M (E (0,y)), hBS (by simp [A']), ?_⟩
      rw [← map_add, ← map_add]
      simp only [Prod.mk_add_mk, add_zero, zero_add]
      change vertical M (E (E.symm (z,h))) = ((0,z),h)
      rw [LinearEquiv.apply_symm_apply]
      rfl
    · obtain ⟨x,y,hxy,hQ⟩ := M.graph_sums (by omega) a z h ha
      refine ⟨(x,M.Q x), hCS (by simp [C]), (y,M.Q y), hCS (by simp [C]), ?_⟩
      simp [Prod.mk_add_mk,hxy,hQ]
  · rw [← hcardC]
    exact Finset.card_le_card hCS
  · have hbound := (Finset.card_union_le (C∪A) A').trans
      (Nat.add_le_add_right (Finset.card_union_le C A) A'.card)
    have hpow : 2^(d-1) ≤ 2^d := Nat.pow_le_pow_right (by decide) (by omega)
    have hnd : n-p+1 = d+1 := by dsimp [n,d]; omega
    change S.card ≤ 2^n + 2^(n-p+1)
    rw [hnd,pow_succ]
    rw [hcardC] at hbound
    change S.card ≤ 2^n + A.card + A'.card at hbound
    omega

theorem Model.exists_code {p : ℕ} (hp : 0 < p) (M : Model (2*p)) :
    ∃ n N : ℕ, 2*p ≤ n ∧ 2^n ≤ N ∧ N ≤ 2^n+2^(n-p+1) ∧
      Green40.minDensity N 2 ≤
        (Nat.card (Green40.hammingBall N 2) : ℝ≥0∞) / 2^(2*n-1) := by
  letI := M.addK
  letI := M.modK
  letI := M.finK
  letI := M.addH
  letI := M.modH
  letI := M.finH
  obtain ⟨S,hcov,hlo,hhi⟩ := M.exists_sum_basis hp
  let n := 2*p + Module.finrank B M.K
  have hcard : Nat.card ((GF (2*p) × M.K) × M.H) = 2^(2*n-1) := by
    rw [Module.natCard_eq_pow_finrank (K := B)]
    simp only [Nat.card_zmod, Module.finrank_prod,
      GaloisField.finrank 2 (n := 2*p) (by omega)]
    congr 1
    have hm := M.dim
    dsimp [n]
    omega
  refine ⟨n,S.card,by dsimp [n]; omega,hlo,hhi,?_⟩
  simpa only [hcard, Nat.cast_pow, Nat.cast_ofNat] using minDensity_le_sum_basis S hcov

end Green40Proof

end


/- Uniform density estimates for the repaired graphs. -/


open Filter
open scoped ENNReal Pointwise

namespace Green40Proof

theorem numeric_estimate (v q N b d : ℝ)
    (hq : 2 ≤ q) (hv : q ≤ v) (hNlo : v ≤ N)
    (hNhi : N*q ≤ v*(q+2)) (hb : 2*b ≤ N*N+N+2)
    (hd : 2*d = v*v) : b / d ≤ 1 + 10 / q := by
  have hqpos : 0 < q := by linarith
  have hvpos : 0 < v := by linarith
  have hNpos : 0 < N := by linarith
  have hdpos : 0 < d := by nlinarith [sq_pos_of_pos hvpos]
  have hNtwo : N ≤ 2*v := by
    have hh := mul_nonneg (sub_nonneg.mpr hNlo) (sub_nonneg.mpr hq)
    nlinarith
  have hmain : q*(N*N-v*v) ≤ 6*v*v := by
    have hh := mul_nonneg (show 0 ≤ 2*v-q*(N-v) by nlinarith) (show 0 ≤ N+v by linarith)
    have hh' := mul_nonneg (show 0 ≤ 2*v-N by linarith) (show 0 ≤ 2*v by linarith)
    nlinarith
  have hsmall : q*(N+2) ≤ 4*v*v := by
    have hh := mul_nonneg (show 0 ≤ v-q by linarith) (show 0 ≤ N+2 by linarith)
    have hh' := mul_nonneg (show 0 ≤ v by linarith) (show 0 ≤ 4*v-(N+2) by linarith)
    nlinarith
  have htotal : 2*b*q ≤ (q+10)*v*v := by
    have hh := mul_le_mul_of_nonneg_right hb (le_of_lt hqpos)
    nlinarith
  rw [div_le_iff₀ hdpos]
  apply (mul_le_mul_iff_left₀ hqpos).mp
  have heq : (1+10/q)*d*q = (q+10)*d := by field_simp
  rw [heq]
  nlinarith [congrArg (fun x : ℝ => (q+10)*x) hd]

theorem density_estimate {p n N : ℕ} (hp : 0 < p) (hpn : 2*p ≤ n)
    (hlo : 2^n ≤ N) (hhi : N ≤ 2^n+2^(n-p+1)) :
    (Nat.card (Green40.hammingBall N 2) : ℝ≥0∞) / 2^(2*n-1) ≤
      ENNReal.ofReal (1+10/(2:ℝ)^p) := by
  have hreal : (Nat.card (Green40.hammingBall N 2) : ℝ) / (2:ℝ)^(2*n-1) ≤
      1+10/(2:ℝ)^p := by
    apply numeric_estimate ((2:ℝ)^n) ((2:ℝ)^p) N _ _
    · calc (2:ℝ) = 2^1 := by norm_num
           _ ≤ 2^p := pow_le_pow_right₀ (by norm_num) hp
    · exact pow_le_pow_right₀ (by norm_num) (by omega)
    · exact_mod_cast hlo
    · have hc : (N:ℝ) ≤ (2:ℝ)^n+2^(n-p+1) := by exact_mod_cast hhi
      have hh := mul_le_mul_of_nonneg_right hc (by positivity : (0:ℝ) ≤ 2^p)
      have hpow : (2:ℝ)^(n-p+1)*2^p = 2^n*2 := by
        rw [← pow_add, ← pow_succ]
        congr 1
        omega
      nlinarith
    · exact_mod_cast hammingBall_card_bound N
    · rw [mul_comm, ← pow_succ, ← pow_add]
      congr 1
      omega
  convert ENNReal.ofReal_le_ofReal hreal using 1
  rw [ENNReal.ofReal_div_of_pos (by positivity)]
  simp

end Green40Proof


/-
# Green 40 sphere-covering lower bounds

The elementary counting lower bound is the fixed half of the conjectured
equality `Green40.f 2 = 1`.  These lemmas isolate that half so a later solver
only has to construct a subsequence of covering subspaces with density at most
one.
-/

namespace Contribution.Green40FTwoEqOne

open Filter Set
open scoped ENNReal Pointwise

/-- A finite sumset that covers the ambient type has at most as many points as
the product of the two source sets.  This is the counting map used by the
sphere-covering bound. -/
theorem card_le_card_mul_of_add_eq_univ {α : Type*} [Add α] [Finite α]
    (A B : Set α) (hcover : A + B = Set.univ) :
    Nat.card α ≤ Nat.card A * Nat.card B := by
  let addMap : A × B → α := fun p => p.1.1 + p.2.1
  have hsurj : Function.Surjective addMap := by
    intro x
    have hx : x ∈ A + B := by rw [hcover]; exact Set.mem_univ x
    rcases hx with ⟨a, ha, b, hb, hab⟩
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), hab⟩
  simpa [Nat.card_prod] using Nat.card_le_card_of_surjective addMap hsurj

/-- Every covering subspace obeys the sphere-covering cardinality bound. -/
theorem coveringSubspace_card_bound (n r : ℕ)
    (V : Submodule (ZMod 2) (𝔽₂ n)) (hV : Green40.IsCoveringSubspace n r V) :
    2 ^ n ≤ Nat.card V * Nat.card (Green40.hammingBall n r) := by
  have h := card_le_card_mul_of_add_eq_univ
    (A := (V : Set (𝔽₂ n))) (B := Green40.hammingBall n r) hV
  simpa [Nat.card_eq_fintype_card] using h

/-- The density of each individual covering subspace is at least one. -/
theorem one_le_coveringSubspace_density (n r : ℕ)
    (V : Submodule (ZMod 2) (𝔽₂ n)) (hV : Green40.IsCoveringSubspace n r V) :
    (1 : ℝ≥0∞) ≤
      (Nat.card V : ℝ≥0∞) * (Nat.card (Green40.hammingBall n r) : ℝ≥0∞) /
        (2 ^ n : ℝ≥0∞) := by
  rw [ENNReal.le_div_iff_mul_le (Or.inl (by simp)) (Or.inl (by simp))]
  simp only [one_mul]
  exact_mod_cast coveringSubspace_card_bound n r V hV

/-- The minimum density at every finite length is at least one. -/
theorem one_le_minDensity (n r : ℕ) : (1 : ℝ≥0∞) ≤ Green40.minDensity n r := by
  rw [Green40.minDensity]
  refine le_iInf fun V => ?_
  refine le_iInf fun hV => ?_
  exact one_le_coveringSubspace_density n r V hV

/-- The sphere-covering lower bound survives the liminf defining `Green40.f`. -/
theorem one_le_f (r : ℕ) : (1 : ℝ≥0∞) ≤ Green40.f r := by
  rw [Green40.f]
  calc
    (1 : ℝ≥0∞) ≤ ⨅ n, Green40.minDensity n r := le_iInf fun n => one_le_minDensity n r
    _ ≤ liminf (fun n => Green40.minDensity n r) atTop := iInf_le_liminf

/-- Green 40 at radius two is therefore reduced to the matching upper bound. -/
theorem f_two_eq_one_iff_le_one : Green40.f 2 = 1 ↔ Green40.f 2 ≤ 1 := by
  constructor
  · intro h
    exact h.le
  · intro h
    exact le_antisymm h (one_le_f 2)

end Contribution.Green40FTwoEqOne


/- The asymptotic upper bound and the exact challenge target. -/


noncomputable section

open Filter Topology
open scoped ENNReal Pointwise

namespace Green40Proof

theorem f_two_le_one : Green40.f 2 ≤ 1 := by
  have hex (r : ℕ) : ∃ n N : ℕ, 2*(2^r) ≤ n ∧ 2^n ≤ N ∧
      N ≤ 2^n+2^(n-2^r+1) ∧
      Green40.minDensity N 2 ≤
        (Nat.card (Green40.hammingBall N 2) : ℝ≥0∞) / 2^(2*n-1) := by
    let M : Model (2*(2^r)) := by
      simpa only [pow_succ, mul_comm] using models (r+1)
    exact M.exists_code (by positivity)
  choose n N hpn hlo hhi hmd using hex
  have hNgrowth : Tendsto N atTop atTop := by
    apply tendsto_atTop_mono (fun r => ?_) tendsto_id
    change r ≤ N r
    have h1 : r < 2^r := Nat.lt_two_pow_self
    have h2 : n r < 2^(n r) := Nat.lt_two_pow_self
    have := hpn r
    have := hlo r
    omega
  have hupper (r : ℕ) : Green40.minDensity (N r) 2 ≤
      ENNReal.ofReal (1+10/(2:ℝ)^(2^r)) :=
    (hmd r).trans (density_estimate (by positivity) (hpn r) (hlo r) (hhi r))
  have hpgrowth : Tendsto (fun r : ℕ => 2^r) atTop atTop := by
    exact tendsto_atTop_mono (fun r => (show r < 2^r from Nat.lt_two_pow_self).le) tendsto_id
  have hden : Tendsto (fun r : ℕ => (2:ℝ)^(2^r)) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2)).comp hpgrowth
  have hreal : Tendsto (fun r : ℕ => 1+10/(2:ℝ)^(2^r)) atTop (𝓝 1) := by
    have hc1 : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have hc10 : Tendsto (fun _ : ℕ => (10:ℝ)) atTop (𝓝 10) := tendsto_const_nhds
    have hh := hc1.add (hc10.mul (tendsto_inv_atTop_zero.comp hden))
    simpa only [Function.comp_def, div_eq_mul_inv, mul_zero, add_zero] using hh
  have hlimit : Tendsto (fun r : ℕ => ENNReal.ofReal (1+10/(2:ℝ)^(2^r)))
      atTop (𝓝 (1:ℝ≥0∞)) := by
    simpa only [Function.comp_def, ENNReal.ofReal_one] using
      (ENNReal.continuous_ofReal.tendsto (1:ℝ)).comp hreal
  calc
    Green40.f 2 ≤ liminf (fun r => Green40.minDensity (N r) 2) atTop :=
      hNgrowth.liminf_le_liminf_comp
    _ ≤ liminf (fun r => ENNReal.ofReal (1+10/(2:ℝ)^(2^r))) atTop :=
      Filter.liminf_le_liminf (Filter.Eventually.of_forall hupper)
    _ = 1 := hlimit.liminf_eq

theorem density_two_eq_one : Green40.f 2 = 1 :=
  le_antisymm f_two_le_one (Contribution.Green40FTwoEqOne.one_le_f 2)

end Green40Proof


theorem target : fcTypeOfName% "Green40.green_40.f_two_eq_one" := by
  exact ⟨fun _ => Green40Proof.density_two_eq_one, fun _ => True.intro⟩

end

end Bounty


-- Check the resolved proposition as well as the exact challenge target.
example : True ↔ Green40.f 2 = 1 := Bounty.target
#print axioms Bounty.target
