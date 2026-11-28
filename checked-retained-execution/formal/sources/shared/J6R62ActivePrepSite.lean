import J6R62ActivePrepWords
import J6R49DFSCentre

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 10000000
set_option maxRecDepth 2180
set_option Elab.async false

/-! Typed output of the actual finite-word producer. The raw tape is
not guessed from the fact that some complete list of modes exists:
its order is the R50 canonical physical roster. -/
namespace J6R62ActivePrep
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R16ModeCost J6R17ModeTape
open J6R14LayoutCost J6R24LegalLayout J6R27OriginalGate
open J6R31RootResidentTables J6R32ChildResidentTransfer J6R50SourceProducer
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R24MeteredRecursion J6R49DFS J6R22Active

noncomputable section
variable {f : ℤ[X]} {ell s q : ℕ}
variable {c : Call (PhysicalHost f ell)}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {d : Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c}
variable {t : Center (printedParams (f:=f) (ell:=ell) s) c} {bank : Bank f}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "Axis" => (J6ActiveRun.Shape.levelBits (printedParams (f:=f) (ell:=ell) s) (J6ActiveRun.Call.depth c))
local notation "atI" => (centerIndex d t)
local notation "copiesAt" => (J6R10Repack.PhysicalPacking.copies (packing sel d))
local notation "pHere" => (registerPrecision S c t)

structure CentreWords
    (sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s))
    (d : Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c)
    (t : Center (printedParams (f:=f) (ell:=ell) s) c) (q : ℕ) where
  copies : Word q
  precision : Word q
  copiesExact : copies.val=(packing sel d).copies
  precisionExact : precision.val=registerPrecision S c t

def fromWords (hq : 0<q) (axisFits : (atI).val+1<q) (U : CentreWords sel d t q) :
    Meter (J6R16ModeCost.SiteTape sel d t q) :=
  let raw := canonicalRaw hq Axis (atI).val U.copies U.precision
  let modes := physicalRoster (atI) (typedCells Axis) copiesAt (2^((atI).val+1)) pHere
  let cover := physicalRoster_complete (atI) (typedCells Axis) copiesAt (2^((atI).val+1)) pHere
    (typed_cells_exact Axis).1 (typed_cells_exact Axis).2.1
  let w := canonical_raw_weights hq (atI) axisFits U.copies U.precision U.copiesExact
    U.precisionExact (register_positive d t)
  ⟨⟨modes,cover.1,cover.2,raw.result.weights,raw.result.precision,w.1,
    (congrArg Word.val w.2).trans U.precisionExact⟩,raw.steps⟩

theorem supplied_words_build_the_literal_tape (hq : 0<q) (axisFits : (atI).val+1<q)
    (U : CentreWords sel d t q) :
    let raw := canonicalRaw hq Axis (atI).val U.copies U.precision
    let out := fromWords hq axisFits U
    out.result.words=raw.result.weights ∧ out.result.precision=raw.result.precision ∧
    out.result.modes.map (encodeMode (atI))=raw.result.modes ∧
    out.steps=raw.steps ∧
    out.steps≤canonicalCap Axis q (atI).val copiesAt pHere := by
  have order := canonical_raw_mode_order hq (atI) axisFits U.copies U.precision U.copiesExact
    U.precisionExact (register_positive d t)
  have fee := canonical_raw_bound hq (atI) axisFits U.copies U.precision U.copiesExact
    U.precisionExact (register_positive d t)
  exact ⟨rfl,rfl,order.symm,rfl,fee⟩

/-- The cost of the finite input words themselves can be included in
the same tape producer. Their provider is executed once for this
centre, not independently on each interpolation point. -/
def paidTape (hq : 0<q) (axisFits : (atI).val+1<q)
    (input : Meter (CentreWords sel d t q)) : Meter (J6R16ModeCost.SiteTape sel d t q) :=
  input.bind (fromWords hq axisFits)

theorem paid_tape_local_fee (hq : 0<q) (axisFits : (atI).val+1<q)
    (input : Meter (CentreWords sel d t q)) :
    let tape := paidTape hq axisFits input
    tape.steps = input.steps+
      (canonicalRaw hq Axis (atI).val input.result.copies input.result.precision).steps ∧
    tape.steps≤ input.steps+canonicalCap Axis q (atI).val copiesAt pHere := by
  exact ⟨rfl,Nat.add_le_add_left (supplied_words_build_the_literal_tape hq axisFits input.result).2.2.2.2 _⟩

theorem native_tape_reuses_replay_bytes {k : ℕ} (axisFits : (atI).val+1<k+1)
    (U : CentreWords sel d t (k+1)) (masks : List (MaskRow (k+1)))
    (seats : List (SeatField Axis ((k-Axis)+13*Axis))) :
    let replay := replaySelected Axis k (atI).val U.copies U.precision masks seats
    let tape := fromWords (Nat.succ_pos k) axisFits U
    tape.result.words=replay.result.raw.roster.weights ∧
    tape.result.precision=replay.result.raw.roster.precision ∧
    tape.result.modes.map (encodeMode (atI))=replay.result.raw.roster.modes :=
  let e := supplied_words_build_the_literal_tape (Nat.succ_pos k) axisFits U
  ⟨e.1,e.2.1,e.2.2.1⟩

def mountAtCentre (J : CentreMachine sel d t bank q) (hq : 0<q) (axisFits : (atI).val+1<q)
    (input : Meter (CentreWords sel d t q)) : CentreMachine sel d t bank q :=
  {J with tape:=paidTape hq axisFits input}

theorem actual_centre_receives_paid_tape (J : CentreMachine sel d t bank q)
    (hq : 0<q) (axisFits : (atI).val+1<q)
    (input : Meter (CentreWords sel d t q)) {pHigh : ℕ}
    (hv : 0<ell) (hf : f.Monic) (H : Frame f pHigh) (B : ℕ)
    (read : CentreChild (sel:=sel) (d:=d) (t:=t) bank) :
    let M := mountAtCentre J hq axisFits input
    let w := M.centreJet hq hv read
    let tails := sumM H.hp (M.centreTerm hv hf H B w.result) (List.range M.window)
    M.masks=J.masks ∧ M.roster=J.roster ∧
    (M.runCentre hq hv hf H B read).steps =
      (paidTape hq axisFits input).steps+w.steps+tails.steps+
        J6R22Active.tapeFee M.low.words.length ell pHere M.window+4 :=
  ⟨rfl,rfl,rfl⟩

#print axioms supplied_words_build_the_literal_tape
#print axioms paid_tape_local_fee
#print axioms native_tape_reuses_replay_bytes
#print axioms actual_centre_receives_paid_tape
end
end J6R62ActivePrep

