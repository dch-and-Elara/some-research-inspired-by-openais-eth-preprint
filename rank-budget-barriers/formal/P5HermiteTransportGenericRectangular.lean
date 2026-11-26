import P5HermiteTransportGenericFinal
import P5HermiteTransportGenericMinors

/-! Original H.3 with a rank-r residue anchor and rectangular jet
matrices. The nonvanishing minor is obtained from the actual residue
matrix, and the same scalar transfers operate on that restriction. -/
namespace Paper5.HermiteGeneric
open Polynomial Matrix
open scoped BigOperators Polynomial Kronecker Classical

variable {K U V U' V' : Type*} [Field K]

theorem convolution_restrict {b : ℕ} (C : Fin b→Matrix U V K) (r : U'→U) (c : V'→V) :
    (convolution C).submatrix (fun x=> (x.1,r x.2)) (fun x=> (x.1,c x.2)) =
      convolution (fun j=>(C j).submatrix r c) := by
  apply Matrix.ext
  rintro ⟨i,u⟩ ⟨j,v⟩
  simp only [Matrix.submatrix_apply,convolution_apply]

variable {T : Type*} [Fintype T] [DecidableEq T]

theorem expanded_restrict (L : Layout K T) (b : ℕ)
    (C : (t : T)→Fin (L.order t)→Matrix U V K) (r : U'→U) (c : V'→V) :
    (expanded L b C).submatrix (fun x=> (x.1,r x.2)) (fun x=> (x.1,c x.2)) =
      expanded L b (fun t j=>(C t j).submatrix r c) := by
  apply Matrix.ext
  rintro ⟨i,u⟩ ⟨j,v⟩
  simp only [Matrix.submatrix_apply,expanded,Matrix.sum_apply,Matrix.kronecker_apply]

variable {R : Type*} [CommRing R] [IsLocalRing R] [Algebra R K]
  [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]

set_option maxHeartbeats 20000000 in
theorem rectangular_from_residue_H3 (L : Layout K T) {b : ℕ} (hb : 0<b) (d : ℕ)
    (A : Matrix U V K[X]) (hDeg : ∀u w,(A u w).natDegree≤d)
    (hWindow : d+b≤∑t,L.order t)
    (v : AddValuation K (WithTop ℤ)) (hv : v.toValuation.Integers R)
    (π : R) (hπ : v (algebraMap R K π)=1) (P : Slot L→ℕ) (p : ℕ) (hp : 0<p)
    (C : Fin b→Matrix U V R)
    (hC : ∀j,(C j).map (algebraMap R K)=observedCoefficients A L.anchor L.anchorScale b j)
    (hMargin : ∀s : Slot L,((p:ℤ):WithTop ℤ)≤((P s:ℤ):WithTop ℤ)+minimumTransfer L b v s)
    (B : (t : T)→Fin (L.order t)→Matrix U V K) (hB : Permissible L π P (nativeCoefficients L A) B) :
    let r := ((C ⟨0,hb⟩).map (IsLocalRing.residue R)).rank
    b*r≤(compressed L b B).rank ∧
      b*r≤∑t,(convolution (B t)).rank ∧
      b*r≤∑t,∑j,(transfer L b t j).rank*(B t j).rank := by
  let M := (C ⟨0,hb⟩).map (IsLocalRing.residue R)
  let r := M.rank
  change b*r≤_ ∧ b*r≤_ ∧ b*r≤_
  by_cases hr : r=0
  · simp [hr]
  letI : Nonempty (Fin r) := ⟨⟨0,Nat.pos_of_ne_zero hr⟩⟩
  obtain ⟨rows,cols,hdet⟩ := actual_full_rank_minor M
  let A' := A.submatrix rows cols
  let C' := (C ⟨0,hb⟩).submatrix rows cols
  let B' (t : T) (j : Fin (L.order t)) := (B t j).submatrix rows cols
  have hu₀ : IsUnit C'.det := by
    apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
    rw [RingHom.map_det]
    exact hdet
  obtain ⟨a,ha⟩ := hu₀
  have hu : (A'.map (Polynomial.evalRingHom L.anchor)).det=algebraMap R K (a:R) := by
    have hs : A'.map (Polynomial.evalRingHom L.anchor)=C'.map (algebraMap R K) := by
      rw [←anchor_constant L hb A']
      apply Matrix.ext
      intro u w
      exact (congrArg (fun X : Matrix U V K=>X (rows u) (cols w)) (hC ⟨0,hb⟩)).symm
    rw [hs]
    change ((algebraMap R K).mapMatrix C').det=algebraMap R K (a:R)
    rw [←RingHom.map_det,←ha]
  have hAI (j : Fin b) (u w : Fin r) :
      ∃ x : R,observedCoefficients A' L.anchor L.anchorScale b j u w=algebraMap R K x :=
    ⟨C j (rows u) (cols w),(congrArg (fun X : Matrix U V K=>X (rows u) (cols w)) (hC j)).symm⟩
  have hB' : Permissible L π P (nativeCoefficients L A') B' :=
    fun t j u w=>hB t j (rows u) (cols w)
  have hs := original_compression_H3 L hb d A' (fun u w=>hDeg (rows u) (cols w))
    hWindow v hv π hπ P p hp hAI ⟨a,hu⟩ hMargin B' hB'
  have hs₁ : (compressed L b B').rank=b*r := by simpa only [Fintype.card_fin] using hs.1
  have hs₂ : b*r≤∑t,(convolution (B' t)).rank := by simpa only [Fintype.card_fin] using hs.2.1
  have hs₃ : b*r≤∑t,∑j,(transfer L b t j).rank*(B' t j).rank := by
    simpa only [Fintype.card_fin] using hs.2.2
  refine ⟨?_,hs₂.trans (Finset.sum_le_sum ?_),hs₃.trans (Finset.sum_le_sum ?_)⟩
  · rw [compressed_eq_expanded] at hs₁ ⊢
    have h := submatrix_rank_mono (expanded L b B)
      (fun x : Fin b × Fin r=> (x.1,rows x.2))
      (fun x : Fin b × Fin r=> (x.1,cols x.2))
    rw [expanded_restrict] at h
    exact hs₁.symm.trans_le h
  · intro t _
    have h := submatrix_rank_mono (convolution (B t))
      (fun x : Fin (L.order t) × Fin r=> (x.1,rows x.2))
      (fun x : Fin (L.order t) × Fin r=> (x.1,cols x.2))
    rw [convolution_restrict] at h
    exact h
  · intro t _
    exact Finset.sum_le_sum fun j _=>Nat.mul_le_mul_left _
      (submatrix_rank_mono (B t j) rows cols)


set_option maxHeartbeats 14000000 in
theorem rectangular_integral_H3 (L : Layout K T) {b : ℕ} (hb : 0<b) (d : ℕ)
    (A : Matrix U V K[X]) (hDeg : ∀u w,(A u w).natDegree≤d)
    (hWindow : d+b≤∑t,L.order t)
    (v : AddValuation K (WithTop ℤ)) (hv : v.toValuation.Integers R)
    (π : R) (hπ : v (algebraMap R K π)=1) (P : Slot L→ℕ) (p : ℕ) (hp : 0<p)
    (hInt : ∀j u w,∃ x : R,observedCoefficients A L.anchor L.anchorScale b j u w=algebraMap R K x)
    (hMargin : ∀s : Slot L,((p:ℤ):WithTop ℤ)≤((P s:ℤ):WithTop ℤ)+minimumTransfer L b v s)
    (B : (t : T)→Fin (L.order t)→Matrix U V K) (hB : Permissible L π P (nativeCoefficients L A) B) :
    ∃ C : Fin b→Matrix U V R,
      (∀j,(C j).map (algebraMap R K)=observedCoefficients A L.anchor L.anchorScale b j) ∧
      (let r := ((C ⟨0,hb⟩).map (IsLocalRing.residue R)).rank
       b*r≤(compressed L b B).rank ∧
       b*r≤∑t,(convolution (B t)).rank ∧
       b*r≤∑t,∑j,(transfer L b t j).rank*(B t j).rank) := by
  choose x hx using hInt
  let C (j : Fin b) : Matrix U V R := Matrix.of fun u w=>x j u w
  have hC (j : Fin b) : (C j).map (algebraMap R K)=observedCoefficients A L.anchor L.anchorScale b j := by
    ext u w
    exact (hx j u w).symm
  exact ⟨C,hC,rectangular_from_residue_H3 L hb d A hDeg hWindow v hv π hπ P p hp C hC hMargin B hB⟩

#print axioms convolution_restrict
#print axioms expanded_restrict
#print axioms rectangular_from_residue_H3
#print axioms rectangular_integral_H3
end Paper5.HermiteGeneric
