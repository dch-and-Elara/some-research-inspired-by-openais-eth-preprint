import P5OverlayPinnedSqZeroLib
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.AdjoinRoot

/-! A literal nonprincipal ideal in a double truncation, as opposed
to a formal two-generator argument about an abstract ideal. -/
namespace Paper5.ObservationExamples
open Polynomial
open scoped Polynomial

set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4000

noncomputable section

abbrev DoubleFour := AdjoinRoot ((X : (ZMod 4)[X])^2)
private abbrev PairFour := TrivSqZeroExt (ZMod 4) (ZMod 4)
local notation "p" => ((X : (ZMod 4)[X])^2)

def uniformizerFour : DoubleFour := AdjoinRoot.of p (2:ZMod 4)
def jetVariableFour : DoubleFour := AdjoinRoot.root p
def squareZeroObstruction : Ideal DoubleFour :=
  Ideal.span ({uniformizerFour,jetVariableFour} : Set DoubleFour)

private def pairDecode : DoubleFour→+*PairFour :=
  AdjoinRoot.lift (TrivSqZeroExt.inlHom (ZMod 4) (ZMod 4)) (TrivSqZeroExt.inr 1)
    (by rw [Polynomial.eval₂_pow,Polynomial.eval₂_X,pow_two,TrivSqZeroExt.inr_mul_inr])

private theorem uniformizerDecode :
    pairDecode uniformizerFour=TrivSqZeroExt.inl 2 := by
  simp [pairDecode,uniformizerFour]

private theorem jetVariableDecode :
    pairDecode jetVariableFour=TrivSqZeroExt.inr 1 := by
  simp [pairDecode,jetVariableFour]

private def firstPair : PairFour→+*ZMod 4 where
  toFun := TrivSqZeroExt.fst
  map_one' := rfl
  map_mul' := fun _ _=>rfl
  map_zero' := rfl
  map_add' := fun _ _=>rfl

private theorem pairObstruction :
    ∀ a b c e d : ZMod 4,
      a*2=0 → a*c=2 → a*e=0 → a*d+b*e=1 → False := by decide

theorem actual_double_truncation_ideal_is_not_principal :
    ¬∃ g : DoubleFour, squareZeroObstruction=Ideal.span ({g}:Set DoubleFour) := by
  rintro ⟨g,hg⟩
  have hπ : uniformizerFour∈squareZeroObstruction :=
    Ideal.subset_span (by simp : uniformizerFour∈({uniformizerFour,jetVariableFour}:Set DoubleFour))
  have hz : jetVariableFour∈squareZeroObstruction :=
    Ideal.subset_span (by simp : jetVariableFour∈({uniformizerFour,jetVariableFour}:Set DoubleFour))
  have hmem : g∈squareZeroObstruction := by
    rw [hg]
    exact Ideal.subset_span (by simp)
  let φ := firstPair.comp pairDecode
  let even : Ideal (ZMod 4) := Ideal.span ({2}:Set (ZMod 4))
  have hsubset : squareZeroObstruction≤Ideal.comap φ even := by
    refine Ideal.span_le.mpr ?_
    intro x hx
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx
    rcases hx with rfl|rfl
    · change (pairDecode uniformizerFour).fst∈even
      rw [uniformizerDecode,TrivSqZeroExt.fst_inl]
      exact Ideal.subset_span (by simp)
    · change (pairDecode jetVariableFour).fst∈even
      rw [jetVariableDecode,TrivSqZeroExt.fst_inr]
      exact even.zero_mem
  have oddSafe : (pairDecode g).fst∈even := hsubset hmem
  obtain ⟨k,hk⟩ := Ideal.mem_span_singleton.mp oddSafe
  have hzero : (pairDecode g).fst*2=0 := by
    rw [hk,mul_comm (2:ZMod 4) k,mul_assoc,show (2:ZMod 4)*2=0 by decide,mul_zero]
  rw [hg] at hπ hz
  obtain ⟨u,hu⟩ := Ideal.mem_span_singleton.mp hπ
  obtain ⟨v,hv⟩ := Ideal.mem_span_singleton.mp hz
  have u0 : (pairDecode g).fst*(pairDecode u).fst=2 := by
    simpa only [map_mul,TrivSqZeroExt.fst_mul,uniformizerDecode,TrivSqZeroExt.fst_inl]
      using congrArg (fun x : DoubleFour=>(pairDecode x).fst) hu.symm
  have v0 : (pairDecode g).fst*(pairDecode v).fst=0 := by
    simpa only [map_mul,TrivSqZeroExt.fst_mul,jetVariableDecode,TrivSqZeroExt.fst_inr]
      using congrArg (fun x : DoubleFour=>(pairDecode x).fst) hv.symm
  have v1 :
      (pairDecode g).fst*(pairDecode v).snd+
        (pairDecode g).snd*(pairDecode v).fst=1 := by
    have h := congrArg (fun x : DoubleFour=>(pairDecode x).snd) hv.symm
    change (pairDecode (g*v)).snd = (pairDecode jetVariableFour).snd at h
    rw [map_mul,jetVariableDecode,TrivSqZeroExt.snd_inr] at h
    exact h
  exact pairObstruction _ _ _ _ _ hzero u0 v0 v1

#print axioms actual_double_truncation_ideal_is_not_principal
end
end Paper5.ObservationExamples
