import J6R24MeteredRecursionFee
import J6R24MeteredRecursionFrame

/-! A descriptor carries one typed centre's *addresses* and raw masks,
never a numeric child answer, a normalizer value, a Hermite coefficient,
or a final value. The occurrence's centre result is produced once and
then reused through explicitly paid jet scans. -/
namespace J6R24MeteredRecursion
open scoped Polynomial
open Polynomial A1R10 A1R12 AOracleMachineTime
open J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R22Active J6R23ScheduleWeight J6R19Retained

variable {f : ℤ[X]} {ell s : ℕ}
variable (sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s))
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
variable {c : Call (PhysicalHost f ell)}
variable (d : Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c)
variable (t : Center (printedParams (f:=f) (ell:=ell) s) c)
local notation "a" => (Shape.levelBits S (Call.depth c))
local notation "u" => (Shape.levelWidth S (Call.depth c))
local notation "pₜ" => (registerPrecision S c t)
local notation "kₜ" => (order (Call.edges c) u (Subtype.val t))
local notation "z₀" => (Probe S c)

structure CentreDesc (bank : Bank f) where
  roster : Roster a c.edges u t.val
  masks : z₀→Meter {m : List Bool // m.length=(bank pₜ (register_positive d t)).words.length}
  literal : ∀ z,(masks z).result.val=List.ofFn (NativeProbeRing.chosenRep f.natDegree _ d.fit z)
  modes : List (NativeMenu (N sel) c t)
  modeUnique : modes.Nodup
  modeComplete : ∀ β,β∈modes

variable {sel d t} {bank : Bank f}
variable (D : CentreDesc sel d t bank)
variable (hv : 0<ell)

abbrev CentreChild (bank : Bank f) :=
  z₀→NativeMenu (N sel) c t→Fin 64→Meter (Block (bank pₜ (register_positive d t)) ell)

def CentreDesc.site (child : CentreChild (sel:=sel) (d:=d) (t:=t) bank) :
    SiteTape pₜ ell kₜ (J9PrintedSchedule.degreeBound c.edges (2^a)+1) (NativeMenu (N sel) c t) :=
  let F := bank pₜ (register_positive d t)
  { hp := F.hp
    hk := active_order_pos a c.edges u t.val t.property
    he := hv
    fw := F.words
    nonempty := F.sizePos
    masks := D.masks
    roster := D.roster.rows
    modes := D.modes
    child := child }

variable (hf : f.Monic)
variable {q : ℕ} (high : Frame f q) (B : ℕ)

def CentreDesc.term (jet : JetTape (bank pₜ (register_positive d t)).words ell kₜ) (j : ℕ) :
    Meter (Block high ell) :=
  let low := bank pₜ (register_positive d t)
  termM low.hp low.sizePos high.hp high.sizePos hv
    ((low.natDegree hf).trans (high.natDegree hf).symm)
    jet a B j t.val D.roster.rows

def CentreDesc.centre (child : CentreChild (sel:=sel) (d:=d) (t:=t) bank) :
    Meter (Block high ell) :=
  let site := D.site hv child
  let jet := site.run a t.val
  let w := sumM high.hp (D.term hv hf high B jet.result) (List.range kₜ)
  ⟨w.result,jet.steps+w.steps+tapeFee (bank pₜ (register_positive d t)).words.length ell pₜ kₜ+4⟩

theorem CentreDesc.once_delta (child : CentreChild (sel:=sel) (d:=d) (t:=t) bank) :
    Delta (D.centre hv hf high B child) (D.centre hv hf high B (fun z β g=>bare (child z β g)))
      ((D.site hv child).childBill) := by
  have h : Delta ((D.site hv child).run a t.val)
      ((D.site hv (fun z β g=>bare (child z β g))).run a t.val)
      ((D.site hv child).childBill) := site_delta (D.site hv child) a t.val
  refine ⟨?_,?_⟩
  · simp only [CentreDesc.centre,h.value]
  · simp only [CentreDesc.centre,h.value,h.fee]
    omega

#print axioms CentreDesc.once_delta
end J6R24MeteredRecursion



