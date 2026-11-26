import P5MainIteratorWalsh
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Orthogonal direct sum of the source swap spectra, with a copy/orbit
support certificate and the exact squared value on that orbit. -/
namespace P5MainIterator
open Matrix Module
open scoped BigOperators RealInnerProductSpace Classical

variable {O : Type*} (A : O → Type*) [Fintype O] [∀ o, Fintype (A o)]

abbrev OrbitSlots := Σ o : O, A o → Bool

noncomputable def orbitRow (r x : OrbitSlots A) : ℝ :=
  if h : r.1=x.1 then normalizedWalsh r.2 (h.symm ▸ x.2) else 0

omit [Fintype O] in
theorem orbitRow_same (o : O) (a x : A o → Bool) :
    orbitRow A ⟨o,a⟩ ⟨o,x⟩ = normalizedWalsh a x := by
  simp [orbitRow]

omit [Fintype O] in
theorem orbitRow_off (r x : OrbitSlots A) (h : r.1≠x.1) : orbitRow A r x=0 := by
  simp [orbitRow,h]

omit [Fintype O] in
theorem orbitRow_square (r x : OrbitSlots A) :
    (orbitRow A r x)^2 =
      if r.1=x.1 then ((2:ℝ)^Fintype.card (A x.1))⁻¹ else 0 := by
  rcases r with ⟨o,a⟩
  rcases x with ⟨p,x⟩
  by_cases h : o=p
  · subst p
    simp [orbitRow,normalizedWalsh_square]
  · simp [orbitRow,h]

set_option maxHeartbeats 5500000 in
theorem orbitRows_dot (r s : OrbitSlots A) :
    (∑ x, orbitRow A r x*orbitRow A s x) = if r=s then 1 else 0 := by
  rcases r with ⟨o,a⟩
  rcases s with ⟨p,b⟩
  rw [Fintype.sum_sigma]
  by_cases h : o=p
  · subst p
    rw [Finset.sum_eq_single o]
    · simp [orbitRow_same,normalizedWalsh_orthogonal]
    · intro q _ hq
      have hh : o≠q := hq.symm
      simp [orbitRow,hh]
    · simp
  · have hs : (Sigma.mk o a : OrbitSlots A) ≠ Sigma.mk p b :=
      fun he => h (congrArg Sigma.fst he)
    rw [if_neg hs]
    apply Finset.sum_eq_zero
    intro q _
    apply Finset.sum_eq_zero
    intro x _
    by_cases hq : o=q
    · subst q
      have hp : p≠o := fun hpo => h hpo.symm
      simp [orbitRow,hp]
    · simp [orbitRow,hq]

noncomputable def orbitVector (r : OrbitSlots A) : EuclideanSpace ℝ (OrbitSlots A) :=
  WithLp.toLp 2 (orbitRow A r)

theorem orbitFrame_orthonormal : Orthonormal ℝ (orbitVector A) := by
  apply (orthonormal_iff_ite).2
  intro r s
  rw [EuclideanSpace.inner_eq_star_dotProduct,dotProduct]
  simpa [orbitVector,mul_comm] using orbitRows_dot A r s

noncomputable def boolWeight {D : Type*} [Fintype D] (a : D → Bool) : ℕ :=
  (Finset.univ.filter (fun i => a i)).card

abbrev Exceptional (keep : ℕ → Prop) := {r : OrbitSlots A // keep (boolWeight r.2)}

theorem exceptional_orthonormal (keep : ℕ → Prop) :
    Orthonormal ℝ (fun r : Exceptional A keep => orbitVector A r.val) :=
  (orbitFrame_orthonormal A).comp Subtype.val Subtype.val_injective

noncomputable def qWalsh {D : Type*} [Fintype D] (a x : D → Bool) : ℚ :=
  ∏ i, if a i && x i then (-1:ℚ) else 1

theorem cast_qWalsh {D : Type*} [Fintype D] (a x : D → Bool) :
    (qWalsh a x : ℝ)=walsh a x := by
  unfold qWalsh walsh
  rw [Rat.cast_prod]
  apply Finset.prod_congr rfl
  intro i _
  by_cases h : (a i && x i)=true
  · simp [sign,h]
  · simp [sign,h]

/-- Integer signs encoded over Q, as used by the exact source measurements. -/
noncomputable def qOrbitRow (r x : OrbitSlots A) : ℚ :=
  if h : r.1=x.1 then qWalsh r.2 (h.symm ▸ x.2) else 0

omit [Fintype O] in
theorem orbitRow_normalizes (r x : OrbitSlots A) :
    orbitRow A r x = (Real.sqrt ((2:ℝ)^Fintype.card (A r.1)))⁻¹ * (qOrbitRow A r x : ℝ) := by
  unfold orbitRow qOrbitRow
  by_cases h : r.1=x.1
  · rw [dif_pos h,dif_pos h,cast_qWalsh]
    rfl
  · simp [h]

#print axioms orbitRow_square
#print axioms orbitRows_dot
#print axioms orbitFrame_orthonormal
#print axioms exceptional_orthonormal
#print axioms orbitRow_normalizes
end P5MainIterator
