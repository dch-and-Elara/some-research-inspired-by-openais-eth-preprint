import J6R68ActiveInputsBaseRoster
import J6R64ActiveMachine
import J6R58ActivePrepCentre

/-! One actual R49 centre consumes the raw stock row that created its
centre key, the same R23 retained factors, and the original numbered
probe table. Remount no mask or header and charge the erase scan once. -/
namespace J6R68ActiveInputs
open scoped Polynomial BigOperators
open Polynomial AOracleMachineTime A1R10 J6R22Active J6ActiveSchedule
open J6ActiveRun J6R9Recursive J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R23ScheduleWeight J6R24MeteredRecursion J6R49DFS J6R58ActivePrep
open J6R62ActivePrep J6R63Active J6R64Active P1DyadicGrid HermiteLoss

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 18000000
set_option maxRecDepth 4100
set_option maxSynthPendingDepth 12
set_option Elab.async false

noncomputable section
variable {f : ℤ[X]} {ell s q pw ew n : ℕ} {c : Call (PhysicalHost f ell)}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {d : Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c}
variable {t : Center (printedParams (f:=f) (ell:=ell) s) c} {bank : Bank f}
variable {good : n ≤ 2^f.natDegree}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "A" => (Shape.levelBits (printedParams (f:=f) (ell:=ell) s) c.depth)
local notation "U" => (Shape.levelWidth (printedParams (f:=f) (ell:=ell) s) c.depth)

def stockProbeReader (hf : f.Monic) (B : MaskTable f.natDegree n good)
    (nested : physicalProbeCount f ell s c ≤ n) (z : Probe S c) :
    Meter {m : List Bool // m.length=(bank (registerPrecision S c t) (register_positive d t)).words.length} :=
  let emit := B.readRaw nested z
  have h : emit.result.length=(bank (registerPrecision S c t) (register_positive d t)).words.length := by
    change (B.readRaw nested z).result.length=_
    rw [B.read_raw_exact (small:=d.fit) nested z,List.length_ofFn,
      (bank (registerPrecision S c t) (register_positive d t)).natDegree hf]
  ⟨⟨emit.result,h⟩,emit.steps⟩

theorem stock_probe_is_original_index (hf : f.Monic) (B : MaskTable f.natDegree n good)
    (nested : physicalProbeCount f ell s c ≤ n) (z : Probe S c) :
    let M := stockProbeReader (d:=d) (t:=t) (bank:=bank) hf B nested z
    M.result.val=List.ofFn (NativeProbeRing.chosenRep f.natDegree _ d.fit z) ∧
      M.steps=(z.val+1)*(3*f.natDegree+5) := by
  exact ⟨by change (B.readRaw nested z).result=_; rw [B.read_raw_exact (small:=d.fit) nested z],
    by change (B.readRaw nested z).steps=_; rw [B.read_raw_exact (small:=d.fit) nested z]⟩

def centreFromStock {rows : List (RawCentre q)} (stock : StockTapeCorrect A c.edges U rows)
    (x : RawCentre q) (live : x∈rows) (word : offsetCentre A x.key=t.val)
    (hf : f.Monic) (table : MaskTable f.natDegree n good)
    (nested : physicalProbeCount f ell s c ≤ n)
    (hq : 0<q) (fit : InputFits sel d q) (taperPos : 0<U) (taperSmall : U ≤ c.edges)
    (W : CallWords c pw ew) (copies : J6R15ModeCost.Word q)
    (copyLaw : copies.val=(packing sel d).copies) : CentreMachine sel d t bank q :=
  let R := rosterForEmittedCentre stock x live
  let raw := paidTape hq (fit.axis t) (centreWords hq fit taperPos taperSmall W copies copyLaw t)
  ⟨word ▸ R.result,stockProbeReader (d:=d) (t:=t) (bank:=bank) hf table nested,
    fun z=>(stock_probe_is_original_index (d:=d) (t:=t) (bank:=bank) hf table nested z).1,
    ⟨raw.result,raw.steps+R.steps+3⟩⟩

private theorem transport_stock_rows {a M u : ℕ} {t w : ℤ} (eq : t=w) (R : Roster a M u t) :
    (eq ▸ R : Roster a M u w).rows=R.rows := by subst w; rfl

theorem actual_centre_consumes_stock_with_old_R23_value
    {rows : List (RawCentre q)} (stock : StockTapeCorrect A c.edges U rows)
    (x : RawCentre q) (live : x∈rows) (word : offsetCentre A x.key=t.val)
    (hf : f.Monic) (table : MaskTable f.natDegree n good)
    (nested : physicalProbeCount f ell s c ≤ n)
    (hq : 0<q) (fit : InputFits sel d q) (taperPos : 0<U) (taperSmall : U ≤ c.edges)
    (W : CallWords c pw ew) (copies : J6R15ModeCost.Word q)
    (copyLaw : copies.val=(packing sel d).copies) (b : Side) :
    let J := centreFromStock (bank:=bank) stock x live word hf table nested hq fit taperPos taperSmall W copies copyLaw
    let native := paidTape hq (fit.axis t) (centreWords hq fit taperPos taperSmall W copies copyLaw t)
    intParts t.val b J.roster.rows=
      ∏ z∈others A t.val, signedFactor t.val b z^taper U (sourceH c.edges U) (HermiteLoss.level z) ∧
    J.tape.result=native.result ∧
    J.tape.steps=native.steps+(10*(A+1)+5)*rows.length+3+3 ∧
    (∀ z, (J.masks z).result.val=List.ofFn (NativeProbeRing.chosenRep f.natDegree _ d.fit z) ∧
      (J.masks z).steps=(z.val+1)*(3*f.natDegree+5)) := by
  let R := rosterForEmittedCentre stock x live
  have weight := exactly_paid_R23_roster stock x live b
  refine ⟨?_,rfl,?_,fun z=>stock_probe_is_original_index (d:=d) (t:=t) (bank:=bank) hf table nested z⟩
  · change intParts t.val b (word ▸ R.result : Roster A c.edges U t.val).rows=_
    rw [transport_stock_rows]
    exact word ▸ weight.1
  · dsimp only [centreFromStock]
    rw [weight.2]
    omega


theorem stock_rows_drive_the_actual_R49_centre
    {rows : List (RawCentre q)} (stock : StockTapeCorrect A c.edges U rows)
    (x : RawCentre q) (live : x∈rows) (word : offsetCentre A x.key=t.val)
    (hf : f.Monic) (table : MaskTable f.natDegree n good)
    (nested : physicalProbeCount f ell s c ≤ n)
    (hq : 0<q) (fit : InputFits sel d q) (taperPos : 0<U) (taperSmall : U ≤ c.edges)
    (W : CallWords c pw ew) (copies : J6R15ModeCost.Word q)
    (copyLaw : copies.val=(packing sel d).copies)
    (hv : 0<ell) {highPrec : ℕ} (high : Frame f highPrec) (margin : ℕ)
    (child : CentreChild (sel:=sel) (d:=d) (t:=t) bank) :
    let J := centreFromStock (bank:=bank) stock x live word hf table nested hq fit taperPos taperSmall W copies copyLaw
    let native := paidTape hq (fit.axis t) (centreWords hq fit taperPos taperSmall W copies copyLaw t)
    let jet := J.centreJet hq hv child
    let out := sumM high.hp (J.centreTerm hv hf high margin jet.result) (List.range J.window)
    let exec := J.runCentre hq hv hf high margin child
    exec.result=out.result ∧ exec.steps=
      (native.steps+(10*(A+1)+5)*rows.length+3+3)+jet.steps+out.steps+
        tapeFee J.low.words.length ell (registerPrecision S c t) J.window+4 := by
  let J := centreFromStock (bank:=bank) stock x live word hf table nested hq fit taperPos taperSmall W copies copyLaw
  have observation := actual_centre_consumes_stock_with_old_R23_value (bank:=bank) stock x live word hf table
    nested hq fit taperPos taperSmall W copies copyLaw .num
  refine ⟨rfl,?_⟩
  simp only [CentreMachine.runCentre]
  rw [observation.2.2.1]

#print axioms stock_probe_is_original_index
#print axioms actual_centre_consumes_stock_with_old_R23_value
#print axioms stock_rows_drive_the_actual_R49_centre
end
end J6R68ActiveInputs
