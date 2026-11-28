import J6R25PreparedSupplyProducer
import J6R24MeteredRecursionWhole

/-! Build the R24 ordered mode descriptors from the actual R17 emitted
stream. The input no longer supplies a legal-mode list or an arbitrary
generation fee. Layout geometry, frame bits, and inherited entry
descriptors remain explicit inputs. -/
namespace J6R25PreparedSupply
open scoped Polynomial
open Polynomial A1R10 AOracleMachineTime
open J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R16ModeCost J6R17ModeTape J1PPrinted J6R21Ancestor J6R22Active J6R23ScheduleWeight
open J6R24MeteredRecursion

variable {f : ℤ[X]} {ell s C : ℕ}
variable (cfg : RootBounds s C f)
variable (sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s))
variable (r : Call (PhysicalHost f ell)) (hf : f.Monic)
local notation "S" => (printedParams (f:=f) (ell:=ell) s)

variable {c : Call (PhysicalHost f ell)}
variable (d : Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c)
variable (t : Center (printedParams (f:=f) (ell:=ell) s) c)
local notation "Alev" => (Shape.levelBits S (Call.depth c))
local notation "Ulev" => (Shape.levelWidth S (Call.depth c))
local notation "Plev" => (registerPrecision S c t)

structure CentreInput (bank : Bank f) where
  roster : Roster Alev c.edges Ulev t.val
  masks : Probe S c→Meter {m : List Bool // m.length=(bank Plev (register_positive d t)).words.length}
  literal : ∀ z,(masks z).result.val=List.ofFn (NativeProbeRing.chosenRep f.natDegree _ d.fit z)

structure ActiveInput (bank : Bank f) where
  centres : List (Center (printedParams (f:=f) (ell:=ell) s) c)
  nodup : centres.Nodup
  complete : ∀ t,t∈centres
  sites : ∀ t,CentreInput d t bank

structure Input where
  rootStable : Stable s C r
  dZero : r.depth=0
  rWidth : r.prec≤C*s
  rootPositive : 0<r.prec
  vPositive : 0<ell
  bank : Bank f
  leaf : NativeLeafTapes sel r hf
  layouts : LayoutSupply (C:=C) sel r
  geometry : ∀ c (hc : NativeReach (Plan sel) r c) (ha : (S).cutoff<c.edges),
    ActiveInput (ready_reachable cfg sel hc rootStable ha) bank

variable {cfg sel r hf d t}
variable (T : Input cfg sel r hf)

abbrev Input.draw {c : Call (PhysicalHost f ell)}
    (hc : NativeReach (Plan sel) r c)
    (d : Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c)
    (t : Center (printedParams (f:=f) (ell:=ell) s) c) :=
  build_native_batch cfg sel T.rootStable T.dZero T.rWidth T.layouts hc d t

noncomputable def Input.centreDesc (hc : NativeReach (Plan sel) r c)
    (z : CentreInput d t T.bank) : CentreDesc sel d t T.bank :=
  let G := generatedOrder cfg sel T.rootStable T.dZero T.rWidth T.layouts hc d t
  ⟨z.roster,z.masks,z.literal,G.modes,G.nodup,G.complete⟩

noncomputable def Input.activeDesc (hc : NativeReach (Plan sel) r c)
    (z : ActiveInput d T.bank) : ActiveDesc sel d T.bank :=
  ⟨commonLoss Alev c.edges Ulev,le_rfl,z.centres,z.nodup,z.complete,
    fun t=>T.centreDesc hc (z.sites t)⟩

noncomputable def Input.prepared : Prepared cfg sel r hf where
  rootStable := T.rootStable
  rootPositive := T.rootPositive
  vPositive := T.vPositive
  bank := T.bank
  leaf := T.leaf
  active := fun c h ha=>T.activeDesc h (T.geometry c h ha)

theorem Input.active_modes_are_generated (hc : NativeReach (Plan sel) r c)
    (D : ActiveInput d T.bank) (t : Center S c) :
    ((T.activeDesc hc D).tape t).modes=
      (generatedOrder cfg sel T.rootStable T.dZero T.rWidth T.layouts hc d t).modes := rfl

#print axioms Input.centreDesc
#print axioms Input.active_modes_are_generated
end J6R25PreparedSupply

