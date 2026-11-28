
import AAcquisitionCostSwitch
import Mathlib.Data.List.NodupEquivFin

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 16
set_option linter.unusedSectionVars false

/-! Actual public A2 input: one bit at each physical potential pair,
in the original fixed order, not a supplied truth-function oracle. -/
namespace A2R45Literal
open FixedHostAcquisition AAcquisitionCost
open scoped Classical

variable {n : ℕ}

private theorem pair_candidate_coordinates (i j : Vertex n) (p : Pair n)
    (h : p ∈ (if hh : i<j then some ⟨(i,j),hh⟩ else none)) :
    p.val=(i,j) := by
  split at h
  · exact congrArg Subtype.val ((Option.mem_some_iff).mp h).symm
  · cases h

theorem public_pair_order_nodup (n : ℕ) : (pairOrder n).Nodup := by
  unfold pairOrder
  apply List.nodup_flatMap.mpr
  constructor
  · intro i _
    apply List.Nodup.filterMap _ (List.nodup_finRange _)
    intro j j' p h h'
    have h0 := congrArg Prod.snd (pair_candidate_coordinates i j p h)
    have h1 := congrArg Prod.snd (pair_candidate_coordinates i j' p h')
    exact h0.symm.trans h1
  · apply (List.nodup_finRange (n+1)).imp
    intro i i' h p h₀ h₁
    obtain ⟨j,_,hj⟩ := List.mem_filterMap.mp h₀
    obtain ⟨j',_,hj'⟩ := List.mem_filterMap.mp h₁
    have h0 := congrArg Prod.fst (pair_candidate_coordinates i j p hj)
    have h1 := congrArg Prod.fst (pair_candidate_coordinates i' j' p hj')
    exact h (h0.symm.trans h1)

def pairAddress (p : Pair n) : Fin (pairOrder n).length :=
  letI : BEq (Pair n) := instBEqOfDecidableEq
  ⟨(pairOrder n).idxOf p,List.idxOf_lt_length_iff.mpr (pairOrder_complete n p)⟩

theorem pairAddress_reads_order (p : Pair n) :
    (pairOrder n)[(pairAddress p).val]? = some p := by
  unfold pairAddress
  exact List.getElem?_idxOf (pairOrder_complete n p)

theorem pairAddress_injective (n : ℕ) :
    Function.Injective (pairAddress (n:=n)) := by
  intro a b h
  have h₀ := pairAddress_reads_order a
  have h₁ := pairAddress_reads_order b
  rw [h] at h₀
  exact Option.some.inj (h₀.symm.trans h₁)

theorem pairAddress_surjective (n : ℕ) :
    Function.Surjective (pairAddress (n:=n)) := by
  intro i
  refine ⟨(pairOrder n)[i.val],Fin.ext ?_⟩
  simpa only [pairAddress] using List.idxOf_getElem (public_pair_order_nodup n) i.val i.isLt

structure Input (n : ℕ) where
  bits : List Bool
  fits : bits.length=(pairOrder n).length

def Input.enabled (w : Input n) (p : Pair n) : Bool :=
  w.bits[(pairAddress p).val]'(by rw [w.fits]; exact (pairAddress p).isLt)

theorem Input.bit_read (w : Input n) (p : Pair n) :
    w.bits[(pairAddress p).val]? = some (w.enabled p) := by
  exact List.getElem?_eq_getElem (by rw [w.fits]; exact (pairAddress p).isLt)

def Input.encode (f : Pair n→Bool) : Input n :=
  ⟨originalInput n f,by simp [originalInput]⟩

theorem Input.encode_enabled (f : Pair n→Bool) :
    (Input.encode f).enabled=f := by
  funext p
  have h := (Input.encode f).bit_read p
  simp only [Input.encode,originalInput,List.getElem?_map,pairAddress_reads_order,Option.map_some] at h
  exact (Option.some.inj h).symm

theorem pair_order_length (n : ℕ) :
    (pairOrder n).length=Fintype.card (Pair n) := by
  have h := Fintype.card_congr (Equiv.ofBijective (pairAddress (n:=n))
    ⟨pairAddress_injective n,pairAddress_surjective n⟩)
  simpa only [Fintype.card_fin] using h.symm

theorem raw_input_tape_fee (w : Input n) :
    consumed (a2Trace n w.bits)=w.bits ∧
    emitted (a2Trace n w.bits)=compileA2Rows n w.bits ∧
    (a2Trace n w.bits).length=6*Fintype.card (Pair n)+16*((n+1)*n) := by
  simpa only [w.fits,pair_order_length] using a2Trace_exact n w.bits

#print axioms public_pair_order_nodup
#print axioms pairAddress_reads_order
#print axioms pairAddress_injective
#print axioms pairAddress_surjective
#print axioms Input.encode_enabled
#print axioms pair_order_length
#print axioms raw_input_tape_fee
end A2R45Literal
