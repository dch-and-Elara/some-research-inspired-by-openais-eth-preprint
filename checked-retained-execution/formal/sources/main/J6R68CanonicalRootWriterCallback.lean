import J6R68CanonicalRootWriterAcquire

/-! Actual root leaf callback on the current page bank. Only the raw
preparation and measured owner-state inputs are supplied; no output
word or compiled instruction list is supplied to the callback. -/
namespace J6R68CanonicalRootWriter
open scoped Polynomial Classical
open Polynomial AOracleMachineTime AOracleMachineTimeTape J6R15ModeCost J6R21Ancestor
open J6R26DescriptorTree J6R35RootOrigins J6R36ChildFramedRoute
open J6R26StablePreparedRoot J6R28GeneratedRootFrame J6R31RootResidentTables
open J6R32RootGeneratedRegistryInputs J6R34RootAtlas J6R41StructuredAllPaths
open J6Mesh J6OrientedHost J6R24LegalLayout J6R10Repack J6R12Blueprint
open J6R12Repack J6ActiveRun J6ActiveSchedule J6R32StatefulArithmetic
open J6R32ChildResidentTransfer J6R27OriginalGate J6R33StatefulArithmeticPage
open J6R37StructuredRoot J6R30GeneratedRootLayout J6R25PreparedSupply
open J6R55BootBodies J6R48RawRoute J6R50SourceProducer J6R54ExteriorOwner
open J6R53OldOwner J6R62Leaf J6R50Leaf J6R52Terminal J6R53TerminalGate
open J6R67CanonicalStop J6R11Blueprint J6R49Leaf J6R51Leaf J6R34ChildPath J6R21Leaf
open J6R54TerminalBoot J6R24MeteredRecursion J6R48Leaf J6R53OldOwnerRoot

set_option quotPrecheck false
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 12500000
set_option maxRecDepth 4800
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q ro co d edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q ro co d edgew tc tj key prec tw bw)
variable (gate : Stamp key prec) (pad : ℕ)
local notation "Ext" => (exteriorChild G ell X.centre X.sample X.group)
local notation "U" => (Vertex (exteriorChild G ell X.centre X.sample X.group))
local notation "N" => (exteriorChild G ell X.centre X.sample X.group).edges
local notation "Pg" => (pageKeyWidth m+pad)
local notation "Bank" => (PageBank f ell key prec tw bw Pg)

structure RootStopInputs (ownerWidth sourceWidth : ℕ) where
  localName : U→Word ownerWidth
  incident : PaidIncidentNames X localName
  lanes : BootLaneTape X gate pad
  sourceName : SourceVertex P→Word sourceWidth
  source : RootRoster (P:=P) gate pad sourceName
  keys : KeyInputs X gate pad source localName
  codeWidth : ℕ

variable {ownerWidth sourceWidth : ℕ}
variable (A : RootStopInputs X gate pad ownerWidth sourceWidth)

def meteredRootStop (F : Frame f (Ext).prec) (B : Bank) : Meter (Block F ell) :=
  let setup := prepareRootBook X gate pad A.localName A.incident A.lanes
  let owners := readActualOuterOwnerBytes X gate pad A.localName A.source A.keys B
  requireWord F.hp (runRootWithOwnerOption A.codeWidth X.hf F X.positive B setup owners)

theorem metered_root_stop_uses_each_actual_producer_once
    (basePos : 0<base) (nameInj : Function.Injective A.localName)
    (srcInj : Function.Injective A.sourceName) (gateWidth : gate.created.val=base)
    (edgeCount : (Ext).host.edgeCount=N) (hb : 0<A.codeWidth) (fit : N≤2^A.codeWidth)
    (F : Frame f (Ext).prec) (B : Bank) (live : IsLive (X.seed pad) B) :
    let setup := prepareRootBook X gate pad A.localName A.incident A.lanes
    let owners := mountFirstOwners X gate pad A.source B live A.keys srcInj
    let fs := trueFrames X gate pad A.localName
    let bk := frameKeys fs
    let cmds := owners.result.order.map (expectedRootCommand X pad edgeCount A.codeWidth fit)
    let eval := runRows X.hf F X.positive B (visitFramesClock fs).result cmds
    ∃ ans, (meteredRootStop X gate pad A F B)=
      ⟨ans,setup.steps+owners.steps+
        (3+(owners.result.raw.map (fun u=>(writeRootOwner A.codeWidth bk.result fs u).steps+7)).sum)+
        (4*N+2)+eval.steps+13⟩ ∧
      F.decode ans=J6R9Recursive.reduce (Ext).prec f ell ((Ext).host.contract X.hf) := by
  let setup := prepareRootBook X gate pad A.localName A.incident A.lanes
  let owners := mountFirstOwners X gate pad A.source B live A.keys srcInj
  let W := runRootWriter A.codeWidth X.hf F X.positive B setup
    (paidOwnerRosterRaw X gate pad A.localName owners)
  obtain ⟨ans,ok,same,_,fee⟩ := raw_root_writer_returns_the_canonical_root_value X gate pad basePos A.localName
    nameInj gateWidth edgeCount A.codeWidth hb fit A.incident A.lanes owners F B live
  have code : W.result=some ans := ok
  have reader : (meteredRootStop X gate pad A F B)=⟨ans,W.steps+4⟩ := by
    unfold meteredRootStop
    dsimp only
    rw [live_owner_read_is_the_measured_mounted_roster X gate pad A.localName A.source A.keys B live srcInj]
    change requireWord F.hp (⟨W.result,W.steps+2⟩ : Meter (Option (Block F ell)))=_
    exact requireWord_hit F.hp (⟨W.result,W.steps+2⟩ : Meter (Option (Block F ell))) ans code
  refine ⟨ans,?_ ,same.trans (actual_root_tape_value X pad basePos F
    (exteriorOrdinal X edgeCount) edgeCount B live)⟩
  rw [reader]
  have fee' : W.steps=_ := fee
  rw [fee']

#print axioms meteredRootStop
#print axioms metered_root_stop_uses_each_actual_producer_once
end
end J6R68CanonicalRootWriter

