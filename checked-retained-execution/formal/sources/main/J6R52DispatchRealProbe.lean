import J6R52DispatchProbe

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 13000000
set_option maxRecDepth 2800

/-! Use the actual measured probe-mask operation from R49's current
centre. The mathematical chosenRep remains an equality witness only. -/
namespace J6R52Dispatch
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R27OriginalGate
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J6R49DFS
open J6R24MeteredRecursion J1PPrinted

variable {f : ℤ[X]} {ell s q : ℕ}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {c : Call (PhysicalHost f ell)}
variable {d : Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c}
variable {t : Center (printedParams (f:=f) (ell:=ell) s) c} {bank : Bank f}
local notation "SP" => (printedParams (f:=f) (ell:=ell) s)

def realMaskWords (J : CentreMachine sel d t bank q) (hf : f.Monic)
    (j : Probe SP c) : Meter {w : List Bool // w.length=f.natDegree} :=
  let result := J.masks j
  ⟨⟨result.result.val,result.result.property.trans (J.low.natDegree hf)⟩,result.steps⟩

def realProbeOrdinal {tz : ℕ} (J : CentreMachine sel d t bank q) (hf : f.Monic)
    (current : Word f.natDegree) : Meter (Option (Word tz)) :=
  readProbeOrdinal (realMaskWords J hf) current

theorem actual_R49_mask_yields_probe_ordinal {tz : ℕ} (J : CentreMachine sel d t bank q)
    (hf : f.Monic) (z : Probe SP c) (current : Word f.natDegree)
    (currentMask : current.bits=(J.masks z).result.val)
    (ht : 0<tz) (room : (J9PrintedSchedule.probeCount c.edges (2^((SP).levelBits c.depth)))<2^tz) :
    let out := realProbeOrdinal (tz:=tz) J hf current
    out.result=some (word z.val) ∧ (word (q:=tz) z.val).val=z.val ∧
      out.steps ≤ (3+((List.finRange ((J9PrintedSchedule.probeCount c.edges (2^((SP).levelBits c.depth))))).map
        (fun j=>(J.masks j).steps+3*f.natDegree+7)).sum)+
        (3*tz+7+(J9PrintedSchedule.probeCount c.edges (2^((SP).levelBits c.depth)))*(10*f.natDegree+9+13*tz+12))+4 := by
  have correct (j : Probe SP c) :
      (realMaskWords J hf j).result.val=(probeCode _ _ d.fit j).bits := J.literal j
  have eq := currentMask.trans (correct z)
  exact actual_binary_probe_ordinal (realMaskWords J hf) d.fit correct z current eq ht room

#print axioms realMaskWords
#print axioms actual_R49_mask_yields_probe_ordinal
end J6R52Dispatch

