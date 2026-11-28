import J6R58ActivePrepMaskTable
import J6R49DFSActive

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 8500000
set_option maxRecDepth 1700
set_option linter.unusedSectionVars false
set_option Elab.async false

/-! Mount the actual physical roster of interpolation probe bytes
in a prepared active machine.  Both the numeric tape and all symbolic
coordinates are unchanged; only the mask reader is replaced. -/
namespace J6R58ActivePrep
open scoped Polynomial
open Polynomial AOracleMachineTime A1R10 J6R22Active
open J1PPrinted J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R24MeteredRecursion J6R49DFS

abbrev physicalProbeCount (f : ℤ[X]) (ell s : ℕ) (c : Call (PhysicalHost f ell)) : ℕ :=
  J9PrintedSchedule.probeCount c.edges
    (2^((printedParams (f:=f) (ell:=ell) s).levelBits c.depth))

variable {f : ℤ[X]} {ell s q n : ℕ}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {c : Call (PhysicalHost f ell)}
variable {d : Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c}
variable {t : Center (printedParams (f:=f) (ell:=ell) s) c}
variable {bank : Bank f} {fit : n≤2^f.natDegree}
local notation "P" => (printedParams (f:=f) (ell:=ell) s)

def chartMask (hf : f.Monic) (B : MaskTable f.natDegree n fit)
    (nested : physicalProbeCount f ell s c≤n) (J : CentreMachine sel d t bank q) (z : Probe P c) :
    Meter {m : List Bool // m.length=J.low.words.length} :=
  let a := B.readRaw nested z
  have exactWord := B.read_raw_exact (small:=d.fit) nested z
  have size : a.result.length=J.low.words.length := by
    change (B.readRaw nested z).result.length=_
    rw [exactWord,List.length_ofFn,J.low.natDegree hf]
  ⟨⟨a.result,size⟩,a.steps⟩

theorem chart_mask_word (hf : f.Monic) (B : MaskTable f.natDegree n fit)
    (nested : physicalProbeCount f ell s c≤n) (J : CentreMachine sel d t bank q) (z : Probe P c) :
    (chartMask hf B nested J z).result=(J.masks z).result := by
  apply Subtype.ext
  change (B.readRaw nested z).result=(J.masks z).result.val
  rw [B.read_raw_exact (small:=d.fit) nested z]
  exact (J.literal z).symm

theorem chart_mask_fee (hf : f.Monic) (B : MaskTable f.natDegree n fit)
    (nested : physicalProbeCount f ell s c≤n) (J : CentreMachine sel d t bank q) (z : Probe P c) :
    (chartMask hf B nested J z).steps=(z.val+1)*(3*f.natDegree+5) := by
  change (B.readRaw nested z).steps=_
  rw [B.read_raw_exact (small:=d.fit) nested z]

def centreWithChart (hf : f.Monic) (B : MaskTable f.natDegree n fit)
    (nested : physicalProbeCount f ell s c≤n) (J : CentreMachine sel d t bank q) : CentreMachine sel d t bank q :=
  { J with
    masks := chartMask hf B nested J
    literal := fun z => (congrArg Subtype.val (chart_mask_word hf B nested J z)).trans (J.literal z) }

def activeWithChart (hf : f.Monic) (B : MaskTable f.natDegree n fit)
    (nested : physicalProbeCount f ell s c≤n) (A : ActiveMachine sel d bank q) : ActiveMachine sel d bank q :=
  { A with tape := fun t=>centreWithChart hf B nested (A.tape t) }

theorem active_mask_word (hf : f.Monic) (B : MaskTable f.natDegree n fit)
    (nested : physicalProbeCount f ell s c≤n) (A : ActiveMachine sel d bank q)
    (t : Center P c) (z : Probe P c) :
    (((activeWithChart hf B nested A).tape t).masks z).result=((A.tape t).masks z).result :=
  chart_mask_word hf B nested (A.tape t) z

theorem active_mask_fee (hf : f.Monic) (B : MaskTable f.natDegree n fit)
    (nested : physicalProbeCount f ell s c≤n) (A : ActiveMachine sel d bank q)
    (t : Center P c) (z : Probe P c) :
    (((activeWithChart hf B nested A).tape t).masks z).steps=(z.val+1)*(3*f.natDegree+5) :=
  chart_mask_fee hf B nested (A.tape t) z

/-- All non-mask producer meters and both high/low precisions are
byte-identical to the already selected source machine. -/
theorem other_setup_preserved (hf : f.Monic) (B : MaskTable f.natDegree n fit)
    (nested : physicalProbeCount f ell s c≤n) (A : ActiveMachine sel d bank q) :
    (activeWithChart hf B nested A).extraPrecision=A.extraPrecision ∧
    (activeWithChart hf B nested A).centres=A.centres ∧
    ∀ t,((activeWithChart hf B nested A).tape t).tape=(A.tape t).tape ∧
      ((activeWithChart hf B nested A).tape t).roster=(A.tape t).roster := ⟨rfl,rfl,fun _=>⟨rfl,rfl⟩⟩

#print axioms chart_mask_word
#print axioms chart_mask_fee
#print axioms active_mask_word
#print axioms active_mask_fee
#print axioms other_setup_preserved
end J6R58ActivePrep

