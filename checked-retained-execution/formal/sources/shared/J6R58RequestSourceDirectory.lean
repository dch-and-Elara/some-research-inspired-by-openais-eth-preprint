import J6R58RequestSourceRoute
import J6R58RequestSourceOwners
import J6R58RequestSourceSeats

/-! Assemble true fixed-chart directory inputs at a single reached
scope. Seat and endpoint tables come from the already selected
native replay and active parent cache. No per-site DirectorySeed or
globally supplied table of readiness/child recipes is used. -/
namespace J6R58RequestSource
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R16ModeCost J6R27OriginalGate
open P11FullPacking J6R9PacketScopes J6R10Repack J6R12CollisionEdges
open J6ActiveRun J6ActiveSchedule J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R26DescriptorTree J6R24MeteredRecursion J6R33GeneratedChildSite
open J6R34ChildPath J6R41StructuredAllPaths J6R48GeneratedAddons J6R48RawRoute
open J6R30ProducedGateRegistry J6R32ChildResidentTransfer J6R33StatefulArithmeticPage
open J6R49SourceLayout J6R50SourceProducer J6R51Online J6R52Dispatch
open J6R21Ancestor J6R36ChildFramedRoute J6R34RootAtlas J6R20Ancestor
open J6R51ParentFrames J6R52CacheSource J6R53OldOwner
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 24300000
set_option maxRecDepth 4900
set_option Elab.async false

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page gwidth : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {root : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel root hf}
variable {v : Ticket sel root}
variable (X : StoredSite T v key prec tw bw page)
local notation "ow" => (1+(X.site.ownerWidth+page))
local notation "Edge" => (v.child.host.Edge)
local notation "wireKey" => (childKey T v X.birth.native.physical)
local notation "Name" => (nameCurrentOwner X)

structure PaidPortIndex where
  read : Port Edge→Meter (Word X.birth.port × Bool)
  exact : ∀ h,(read h).result=(wireKey (edge h),side h)

variable (cache : CachedParentFrames X.site) (port : PaidPortIndex X)

def readLocalAddresses (h : Port Edge) : Meter (Option (Word ow × Word X.birth.port × Bool)) :=
  let p := port.read h
  let route := readScopedEndpoint p.result.1 p.result.2 cache.rows
  match route.result with
  | none => ⟨none,p.steps+route.steps+3⟩
  | some ends =>
    let o := writeTaggedName ends
    ⟨some (o.result,p.result.1,p.result.2),p.steps+route.steps+o.steps+4⟩

theorem actual_port_routes_get_its_owner_and_seat (h : Port Edge) :
    let p := port.read h
    let route := readScopedEndpoint p.result.1 p.result.2 cache.rows
    let addresses := readLocalAddresses X cache port h
    addresses.result=some (Name (owner v.child.host.network h),wireKey (edge h),side h) ∧
      addresses.steps=p.steps+route.steps+(writeTaggedName (currentEndpoint X (edge h) (side h))).steps+4 := by
  let p := port.read h
  have byRaw : (readScopedEndpoint p.result.1 p.result.2 cache.rows).result=
      some (currentEndpoint X (edge h) (side h)) := by
    have pShape : p.result=(wireKey (edge h),side h) := port.exact h
    rw [pShape]
    exact actual_frame_endpoint_is_paid X cache (edge h) (side h)
  have enc : (writeTaggedName (currentEndpoint X (edge h) (side h))).result=
      Name (owner v.child.host.network h) := by
    rw [actual_tagged_write_exact]
    cases h <;> rfl
  unfold readLocalAddresses
  dsimp only
  rw [byRaw]
  refine ⟨?_,rfl⟩
  change some ((writeTaggedName (currentEndpoint X (edge h) (side h))).result,p.result.1,p.result.2)=_
  rw [enc,port.exact h]

def queryActualPort (h : Port Edge) : Meter (Word ow × Word X.birth.port × Bool) :=
  unwrapSuccess (readLocalAddresses X cache port h)
    (by rw [(actual_port_routes_get_its_owner_and_seat X cache port h).1]; rfl)

theorem actual_query_is_from_live_chart (h : Port Edge) :
    (queryActualPort X cache port h).result=
      (Name (owner v.child.host.network h),wireKey (edge h),side h) ∧
      (queryActualPort X cache port h).steps=(readLocalAddresses X cache port h).steps := by
  have e := (actual_port_routes_get_its_owner_and_seat X cache port h).1
  have out := unwrap_success_exact (readLocalAddresses X cache port h)
      (by rw [e]; rfl) _ e
  exact ⟨congrArg Meter.result out,congrArg Meter.steps out⟩

variable {u : (Plan sel).Slot v.child} {q : ℕ}
variable {U : ExplicitSelectedWords X.site u q}
variable (R : Replayed X.site u q U)
local notation "nx" => (successorTicket v u)

section Bank
variable (gates : v.parent.host.Row⊕v.parent.host.Col→Option (CodeGate (Word gwidth)))
variable (source : CompleteRoster X.site.oldKey (parentData X gates))
variable (H : ParentOwnerHeaders X.site) (inj : Function.Injective X.site.oldKey)
variable (B : PayloadShell R)
local notation "Owners" => (buildOriginBank X gates source H inj)
local notation "Query" => (queryActualPort X cache port)
local notation "Seats" => (directorySeatRows R B)

theorem generated_native_routes_all_hit :
    NativeTables X.childOrigins (nameCurrentOwner X) (shellPageWord R B)
      (Owners).result Seats Query := by
  have ownerRows := (actual_origin_bank_all_owners_and_fee X gates source H inj).1
  have addr (h : Port Edge) := (actual_query_is_from_live_chart X cache port h).1
  have ownExists := (born_owner_order_full X H).2
  have namesInj := generated_name_stays_injective X inj
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro h
    rw [addr]
  · intro h
    rw [ownerRows,addr]
    exact List.mem_map.mpr ⟨owner v.child.host.network h,ownExists _,rfl⟩
  · intro h x here found
    rw [ownerRows] at here
    obtain ⟨o,_,rfl⟩ := List.mem_map.mp here
    rw [addr] at found
    have same : o=owner v.child.host.network h := namesInj found
    rw [same]
    rfl
  · intro h
    rw [addr]
    exact (held_seats_hit_and_unique R B (edge h)).1
  · intro h x here found
    rw [addr] at found
    exact (held_seats_hit_and_unique R B (edge h)).2 x here found

def nextDirectoryFromCurrent (fallback : Addon ow (dim nx) key prec page) : Meter (DirectorySeed R B) :=
  let O := buildOriginBank X gates source H inj
  ⟨⟨ow,X.birth.port,ow,nameCurrentOwner X,O.result,
    directorySeatRows R B,queryActualPort X cache port,fallback,
    generated_native_routes_all_hit X cache port R gates source H inj B⟩,O.steps+4⟩

theorem next_directory_has_only_actual_production
    (fallback : Addon ow (dim nx) key prec page) :
    let D := nextDirectoryFromCurrent X cache port R gates source H inj B fallback
    D.result.owners=(Owners).result ∧ D.result.seats=Seats ∧
      D.result.queries=Query ∧ D.steps=(Owners).steps+4 :=
  ⟨rfl,rfl,rfl,rfl⟩
end Bank

#print axioms actual_port_routes_get_its_owner_and_seat
#print axioms actual_query_is_from_live_chart
#print axioms generated_native_routes_all_hit
#print axioms nextDirectoryFromCurrent
#print axioms next_directory_has_only_actual_production
end
end J6R58RequestSource
