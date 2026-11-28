
import A2R45LiteralAdmission

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3250000
set_option maxRecDepth 1970
set_option linter.unusedSectionVars false

/-! The original unshifted source terminal is genuinely independent of
the input switch tape. This is a different claim from the hardness of
the single shifted completed register. -/
namespace A2R45Literal
open scoped Classical BigOperators Polynomial
open Polynomial J6R10Repack J6R11Integral J6R10Integral J6R9Recursive
open FixedHostAcquisition Acquisition
noncomputable section

variable {I Pad K : Type*} [Fintype I] [Fintype Pad] [CommRing K]

theorem filled_origin_eq (row col : (I→Bool)→K) :
    (∑ x : Bits I Pad,row (oddBits x)*sourceColumns col x) =
      ∑ x : I→Bool,∑ y : I→Bool,col x*(pinsZero y*row y) := by
  calc
    _ = ∑ p : Parts I Pad,row p.2.1*(col p.1*pinsZero p.2.1*pinsZero p.2.2) := by
      apply Fintype.sum_equiv (splitAssignment (I:=I) (Pad:=Pad))
      intro x
      rfl
    _ = _ := by
      simp only [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      have hz : (∑ z : Pad→Bool,row y*(col x*pinsZero y*pinsZero z)) =
          row y*(col x*pinsZero y)*(∑ z : Pad→Bool,pinsZero z) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun z _=>by ring)
      have hs : (∑ z : Pad→Bool, pinsZero z)=(1:K) := by
        simp only [pinsZero_eq,Fintype.sum_ite_eq']
      rw [hz,hs,mul_one]
      ring

private theorem same_frozen_origin {K' : Type*} [CommRing K'] {n' : ℕ}
    {P' : Type} [Fintype P'] (enabled : Pair n'→Bool) :
    (∑ x : Bits (Wire n') P',
      Acquisition.rowProduct (K:=K') (rowTable enabled) (oddBits x) *
        sourceColumns FixedHostAcquisition.columnTable x) =
      hostOrigin (K:=K') enabled := by
  let R : (Wire n'→Bool)→K' := Acquisition.rowProduct (K:=K') (rowTable enabled)
  let C : (Wire n'→Bool)→K' := FixedHostAcquisition.columnTable (K:=K')
  have H := @filled_origin_eq (Wire n') P' K' inferInstance inferInstance inferInstance R C
  refine Eq.trans ?_ (Eq.trans H ?_)
  · apply Finset.sum_congr (by ext z; simp only [Finset.mem_univ])
    intro z _
    rfl
  · unfold hostOrigin
    apply Finset.sum_congr (by ext z; simp only [Finset.mem_univ])
    intro z _
    apply Finset.sum_congr (by ext u; simp only [Finset.mem_univ])
    intro u _
    rfl
variable {n : ℕ} {P : Type} [Fintype P]

theorem true_source_origin (w : Input n) (f : ℤ[X]) (base : ℕ) (hb : 0<base)
    (hf : f.Monic) (hd : 0<f.natDegree) (hn : 0<n) :
    trueContraction (nativeNetwork n P) (file w f base) hf =
      ((2:IntRing f 1)^((n+1)^2)) := by
  let N := nativeNetwork n P
  calc
    _ = ∑ x : NativeWire n P→Bool,
        (Acquisition.rowProduct (K:=IntRing f 1) (rowTable w.enabled)) (oddBits x) *
        sourceColumns FixedHostAcquisition.columnTable x := by
      unfold trueContraction
      apply Finset.sum_congr (by ext u; simp only [Finset.mem_univ])
      intro x _
      rw [Fintype.prod_sum_type]
      have hr : (∏ r : NativeRow n P,(file w f base (.inl r)).frozen hf
          (assignment N x (.inl r))) =
          Acquisition.rowProduct (K:=IntRing f 1) (rowTable w.enabled) (oddBits x) := by
        calc
          _ = ∏ r : NativeRow n P,Acquisition.bit (K:=IntRing f 1) (rowFlag w x r) := 
            Finset.prod_congr rfl (fun r _=>file_frozen w f base hb hf hd (.inl r) _)
          _ = _ := rowFlags_identify w x
      have hc : (∏ c : NativeCol n P,(file w f base (.inr c)).frozen hf
          (assignment N x (.inr c))) = sourceColumns FixedHostAcquisition.columnTable x := by
        calc
          _ = ∏ c : NativeCol n P,Acquisition.bit (K:=IntRing f 1) (colFlag w x c) :=
            Finset.prod_congr rfl (fun c _=>file_frozen w f base hb hf hd (.inr c) _)
          _ = _ := colFlags_identify w x
      rw [hr,hc]
    _ = hostOrigin (K:=IntRing f 1) w.enabled :=
      same_frozen_origin (K':=IntRing f 1) (n':=n) (P':=P) w.enabled
    _ = _ := hostOrigin_eq (K:=IntRing f 1) hn w.enabled

theorem actual_root_origin_public {a : ℕ} (Q : PhysicalPacking (nativeNetwork n P) a (Fin 64))
    (w : Input n) (f : ℤ[X]) (base : ℕ) (hb : 0<base)
    (hf : f.Monic) (hd : 0<f.natDegree) (hn : 0<n) :
    (parentF Q (file w f base) hf).eval 0 = ((2:RatRing f 1)^((n+1)^2)) := by
  rw [parentF_origin,true_source_origin w f base hb hf hd hn,map_pow,map_ofNat]
#print axioms filled_origin_eq
#print axioms true_source_origin
#print axioms actual_root_origin_public
end
end A2R45Literal
