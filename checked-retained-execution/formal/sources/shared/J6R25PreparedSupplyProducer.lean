import J6R25PreparedSupplyModeDecode
import J6R25PreparedSupplyBatch
import J6R17ModeTapeSupply

/-! Actual R17 mode producer on a validated physical layout tape. The
weight words, order and support vectors are outputs of the programs,
not fields of a promised fee bound or a supplied menu list. -/
namespace J6R25PreparedSupply
open scoped Polynomial
open Polynomial AOracleMachineTime
open J6R15ModeCost J6R16ModeCost J6R17ModeTape
open J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable J6R11Blueprint J6R12Blueprint
open J1PPrinted

structure RawValid {q : ℕ} (T : RawTape q) : Prop where
  posWidth : 0<q
  posPrec : 0<T.precision.val
  posWeights : ∀ x∈T.weights,0<x.val
  sameLength : T.weights.length=T.modes.length

def producedBatch {q : ℕ} (a : ℕ) (build : Meter (RawTape q))
    (h : RawValid build.result) : Meter (Batch q) :=
  let E := emitBatch a build.result h.posWidth h.posPrec h.posWeights
  ⟨(E).result,build.steps+(E).steps⟩

variable {f : ℤ[X]} {ell s C : ℕ}
variable (cfg : RootBounds s C f) 
variable (sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s))
variable {r c : Call (PhysicalHost f ell)}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "qW" => (uniformWidth s C)
variable (hr : Stable s C r) (d₀ : r.depth=0) (p₀ : r.prec≤C*s)
variable (Ls : LayoutSupply (C:=C) sel r)
variable (hc : NativeReach (Plan sel) r c)
variable (d : J6R12Blueprint.Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c)
variable (t : Center (printedParams (f:=f) (ell:=ell) s) c)
local notation "Z" => (rawSite sel d t (Ls c hc d))
local notation "I" => (paidTapeSupply cfg sel hr d₀ p₀ Ls c hc d t)
local notation "E" => (paid_tape_supply_exact cfg sel hr d₀ p₀ Ls hc d t)

include cfg hr d₀ p₀ in
set_option maxHeartbeats 2300000 in
theorem actual_raw_valid : RawValid (Z).result := by
  have hp : (Z).result.precision.val=registerPrecision S c t :=
    (congrArg Word.val (E).2.2.1).trans (I).precisionMeaning
  have hW : (Z).result.weights.map Word.val=(I).modes.map modeWeight := by
    rw [(E).2.1]
    exact (I).weightMeaning
  refine ⟨by unfold uniformWidth; omega,hp ▸ register_positive d t,?_,?_⟩
  · intro x hx
    have h := List.mem_map_of_mem (f:=Word.val) hx
    rw [hW] at h
    obtain ⟨w,_,e⟩ := List.mem_map.mp h
    exact e ▸ (modeWeight_bounds w).1
  · have eq := congrArg List.length hW
    simpa only [(E).1,List.length_map] using eq

def build_native_batch : Meter (Batch qW) :=
  producedBatch ((S).levelBits c.depth) Z (actual_raw_valid cfg sel hr d₀ p₀ Ls hc d t)

structure GeneratedOrder {q : ℕ} (B : Batch q) (Mode : Type*) where
  modes : List Mode
  nodup : modes.Nodup
  complete : ∀ b,b∈modes
  view : List (List ℕ)
  read : B.vectors.map (List.map Word.val)=view
  sameCount : modes.length=view.length
  halted : B.halted=true

set_option maxHeartbeats 3800000 in
theorem native_produced_is_complete :
    let out := build_native_batch cfg sel hr d₀ p₀ Ls hc d t
    let A := (S).levelBits c.depth
    let xs := strictTuples ((I).modes.map modeWeight) (registerPrecision S c t)
    ∃ B : List (NativeMenu (N sel) c t),
      B.Nodup ∧ (∀ β,β∈B) ∧
      out.result.halted=true ∧ out.result.vectors.map (List.map Word.val)=B.map (vectorKey sel d t I) ∧
      out.result.support=out.result.vectors.map (fun v=>some (supportSpec (Z).result.modes v)) ∧
      out.steps≤buildUniform s C+emitBatchCap A qW (Z).result.weights.length (Z).result.modes.length xs.length := by
  let A := (S).levelBits c.depth
  let Z0 := Z
  let F := actual_raw_valid cfg sel hr d₀ p₀ Ls hc d t
  let V := emitBatch A Z0.result F.posWidth F.posPrec F.posWeights
  let xs := strictTuples ((I).modes.map modeWeight) (registerPrecision S c t)
  obtain ⟨hl,hrV,hsupp,hC⟩ := emit_batch_exact A Z0.result F.posWidth F.posPrec F.posWeights F.sameLength
  have hid : strictTuples (Z0.result.weights.map Word.val) Z0.result.precision.val=xs := by
    unfold Z0 xs
    rw [(E).2.1,(E).2.2.1,(I).weightMeaning,(I).precisionMeaning]
  obtain ⟨B,hN,hAll,hEmit⟩ := native_mode_order sel d t I
  rw [hid] at hrV hC
  exact ⟨B,hN,hAll,hl,hrV.trans hEmit.symm,hsupp,Nat.add_le_add (E).2.2.2 hC⟩

noncomputable def generatedOrder :
    GeneratedOrder (build_native_batch cfg sel hr d₀ p₀ Ls hc d t).result
      (NativeMenu (N sel) c t) := by
  let E0 := native_produced_is_complete cfg sel hr d₀ p₀ Ls hc d t
  let modes := Classical.choose E0
  let H := Classical.choose_spec E0
  exact ⟨modes,H.1,H.2.1,modes.map (vectorKey sel d t I),H.2.2.2.1,by simp,H.2.2.1⟩

#print axioms actual_raw_valid
#print axioms native_produced_is_complete
#print axioms generatedOrder
end J6R25PreparedSupply


