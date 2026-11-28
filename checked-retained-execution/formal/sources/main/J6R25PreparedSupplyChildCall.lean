import J6R25PreparedSupplyNativeChild
import J6R25PreparedSupplyFundedRun

/-! A real byte-registry hit gates the measured child call at the same
native address. This is a one-child composition. It does not claim
that the wire header alone reconstructs all future Gate descriptors. -/
namespace J6R25PreparedSupply
open scoped Polynomial
open Polynomial AOracleMachineTime
open J6R15ModeCost J6R21Ancestor J6R17ModeTape J6R16ModeCost
open J6ActiveRun J6ActiveSchedule J6R10Reachable J6R10Repack J6R11Blueprint J6R12Blueprint
open J1PPrinted J6R24MeteredRecursion

def onRegistryHit {A : Type*} {w : ℕ}
    (D : Meter (List (DirRow w)×Option (List Bool))) (run : List Bool→Meter A) :
    Meter (List (DirRow w)×Option A) :=
  match D.result.2 with
  | none => ⟨(D.result.1,none),D.steps+2⟩
  | some bytes =>
    let ans := run bytes
    ⟨(D.result.1,some ans.result),D.steps+ans.steps+2⟩

theorem registry_hit_runs {A : Type*} {w : ℕ}
    (D : Meter (List (DirRow w)×Option (List Bool))) (run : List Bool→Meter A)
    (bank : List (DirRow w)) (bs : List Bool) (h : D.result=(bank,some bs)) :
    onRegistryHit D run=⟨(bank,some (run bs).result),D.steps+(run bs).steps+2⟩ := by
  simp only [onRegistryHit,h]

variable {f : ℤ[X]} {ell s C : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
variable (T : Input cfg sel r hf)
variable {c : Call (PhysicalHost f ell)}
variable (hc : NativeReach (Plan sel) r c)
variable (d : J6R12Blueprint.Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c)
variable (t : Center (printedParams (f:=f) (ell:=ell) s) c)

set_option maxHeartbeats 4100000 in
theorem stored_child_executes {w b dep aw : ℕ}
    (P : PhysicalPorts sel d t w) (z : Probe S c) (β : NativeMenu (N sel) c t) (g : Fin 64)
    (key : Meter (Word aw)) (bank : List (DirRow aw)) (oldDepth : Word dep)
    (precision : Word (uniformWidth s C))
    (resident : precision=(rawSite sel d t (T.layouts c hc d)).result.precision)
    (hd : oldDepth.val=c.depth) (hdep : 0<dep) (db : c.depth+1<2^dep)
    (hb : 0<b) (eb : ((Plan sel).child c (addressed d t z β g)).edges<2^b)
    (fresh : ∀ row∈bank,row.id≠key.result) :
    let addr := addressed d t z β g
    let next := (Plan sel).child c addr
    let entry := childStage (b:=b) key (word g.val) precision oldDepth P.raw
    let installed := publishThenAcquire entry bank
    let originalCall := T.run next (reach_snoc (Plan sel) hc addr)
    let out := onRegistryHit installed (fun _=>originalCall)
    out.result=(entry.result::bank,some originalCall.result) ∧
      out.steps=installed.steps+originalCall.steps+2 ∧
      installed.steps≤entry.steps+fetchFee bank+3*entry.result.bytes.length+2*aw+9+
        fetchFee (entry.result::bank)+4 := by
  let addr := addressed d t z β g
  let next := (Plan sel).child c addr
  let entry := childStage (b:=b) key (word g.val) precision oldDepth P.raw
  let installed := publishThenAcquire entry bank
  let originalCall := T.run next (reach_snoc (Plan sel) hc addr)
  obtain ⟨_,hBytes,hFee⟩ := acquired_native_child sel d t P z β g key bank precision oldDepth
    (by rw [resident]; exact physical_precision_word sel d t cfg (T.layouts c hc d)) hd hdep db hb eb fresh
  have h := registry_hit_runs installed (fun _=>originalCall) (entry.result::bank) _ hBytes
  exact ⟨congrArg Meter.result h,congrArg Meter.steps h,hFee⟩

#print axioms registry_hit_runs
#print axioms stored_child_executes
end J6R25PreparedSupply

