import P5HermiteTransportGenericAnchor
import P5HermiteTransportGenericPrecision
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! The reconstructed, independently perturbed anchor is full rank:
construct its genuine integral lift and reduce that SAME matrix. -/
namespace Paper5.HermiteGeneric
open Polynomial Matrix
open scoped BigOperators Polynomial Classical

variable {R K U : Type*} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [Fintype U] [DecidableEq U]

set_option maxHeartbeats 12000000 in
theorem correction_full_rank {b : ℕ} (hb : 0<b)
    (hinj : Function.Injective (algebraMap R K)) (π : R)
    (hπ : π∈IsLocalRing.maximalIdeal R) (p : ℕ) (hp : 0<p)
    (C : Fin b→Matrix U U R) (hu : IsUnit (C ⟨0,hb⟩).det)
    (B : Matrix (Fin b × U) (Fin b × U) K)
    (hE : EntryPrecision π p ((convolution C).map (algebraMap R K)) B) :
    B.rank = b*Fintype.card U := by
  choose err he using hE
  let M : Matrix (Fin b × U) (Fin b × U) R :=
    Matrix.of fun i j=>convolution C i j+π^p*err i j
  have hMap : M.map (algebraMap R K)=B := by
    ext i j
    change algebraMap R K (convolution C i j+π^p*err i j)=B i j
    rw [map_add,add_comm]
    exact (sub_eq_iff_eq_add.mp (he i j)).symm
  let ρ := IsLocalRing.residue R
  have hπ₀ : ρ π=0 := (IsLocalRing.residue_eq_zero_iff π).mpr hπ
  have hRes : M.map ρ=(convolution C).map ρ := by
    ext i j
    change ρ (convolution C i j+π^p*err i j)=ρ (convolution C i j)
    rw [map_add,map_mul,map_pow,hπ₀,zero_pow hp.ne',zero_mul,add_zero]
  have hC : ((C ⟨0,hb⟩).map ρ).det≠0 := by
    change (ρ.mapMatrix (C ⟨0,hb⟩)).det≠0
    rw [←RingHom.map_det]
    exact (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr hu
  have hResDet : (M.map ρ).det≠0 := by
    rw [hRes,convolution_map,convolution_det hb]
    exact pow_ne_zero _ hC
  have hMdet : M.det≠0 := by
    intro h
    apply hResDet
    change (ρ.mapMatrix M).det=0
    rw [←RingHom.map_det,h,map_zero]
  have hBdet : B.det≠0 := by
    rw [←hMap]
    change ((algebraMap R K).mapMatrix M).det≠0
    rw [←RingHom.map_det]
    intro h
    apply hMdet
    apply hinj
    rwa [map_zero]
  have h := Matrix.rank_of_isUnit B ((Matrix.isUnit_iff_isUnit_det _).mpr
    (isUnit_iff_ne_zero.mpr hBdet))
  simpa only [Fintype.card_prod,Fintype.card_fin] using h

variable {T : Type*}

omit [IsLocalRing R] [Fintype U] [DecidableEq U] in
theorem anchor_constant (L : Layout K T) {b : ℕ} (hb : 0<b) (A : Matrix U U K[X]) :
    observedCoefficients A L.anchor L.anchorScale b ⟨0,hb⟩=A.map (Polynomial.evalRingHom L.anchor) := by
  ext i j
  change scalarObserve L.anchor L.anchorScale b (A i j) ⟨0,hb⟩=(A i j).eval L.anchor
  rw [scalarObserve_apply,Polynomial.coeff_zero_eq_eval_zero]
  change ((A i j).comp (C L.anchor+C L.anchorScale*X)).eval 0=_
  simp [Polynomial.eval_comp]

omit [IsLocalRing R] in
theorem anchor_rank_H1 (L : Layout K T) {b : ℕ} (hb : 0<b) (A : Matrix U U K[X])
    (h : (A.map (Polynomial.evalRingHom L.anchor)).det≠0) :
    (anchorMatrix L b A).rank=b*Fintype.card U := by
  apply convolution_rank hb
  rwa [anchor_constant L hb A]

set_option maxHeartbeats 12000000 in
theorem anchor_integral_correction_H3 (L : Layout K T) {b : ℕ} (hb : 0<b)
    (hinj : Function.Injective (algebraMap R K)) (π : R)
    (hπ : π∈IsLocalRing.maximalIdeal R) (p : ℕ) (hp : 0<p)
    (A : Matrix U U K[X])
    (hA : ∀ j u v,∃ r : R, observedCoefficients A L.anchor L.anchorScale b j u v=algebraMap R K r)
    (hu : ∃ a : Rˣ,(A.map (Polynomial.evalRingHom L.anchor)).det=algebraMap R K (a:R))
    (B : Matrix (Fin b × U) (Fin b × U) K)
    (hE : EntryPrecision π p (anchorMatrix L b A) B) :
    B.rank=b*Fintype.card U := by
  choose Entries hEntries using hA
  let C (j : Fin b) : Matrix U U R := Matrix.of fun u v=>Entries j u v
  have hC (j : Fin b) : (C j).map (algebraMap R K) = observedCoefficients A L.anchor L.anchorScale b j := by
    ext u v
    exact (hEntries j u v).symm
  have hMap : (convolution C).map (algebraMap R K) = anchorMatrix L b A := by
    rw [convolution_map]
    unfold anchorMatrix
    simp_rw [hC]
  obtain ⟨a,ha⟩ := hu
  have hU : (C ⟨0,hb⟩).det=(a:R) := by
    apply hinj
    rw [RingHom.map_det]
    change ((C ⟨0,hb⟩).map (algebraMap R K)).det=_
    rwa [hC,anchor_constant L hb A]
  rw [←hMap] at hE
  exact correction_full_rank hb hinj π hπ p hp C (hU ▸ a.isUnit) B hE

#print axioms correction_full_rank
#print axioms anchor_constant
#print axioms anchor_rank_H1
#print axioms anchor_integral_correction_H3
end Paper5.HermiteGeneric
