import J6R22ActiveSite
import J6R22ActiveNativeGroup
import J6R22ActiveCoeff

/-! Port the complete finite centre machine to the actual dependent
printed call. Its child readings are those of the same source
Program, not another child-generation schedule. Exact shape checks
for supplied raw descriptors remain explicit; cross-centre
recombination and installing child/registry tapes are not charged
by this site receipt. -/
namespace J6R22Active
open scoped Polynomial BigOperators Classical
open Polynomial A1R10 AOracleMachineTime
open J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable
open J6R11Blueprint J6R12Blueprint J1PPrinted

variable {f : ℤ[X]} {ell s : ℕ}
variable (sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s))
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
variable (r : Call (PhysicalHost f ell)) (hf : f.Monic)
variable [DecidableEq (Envelope (N sel) (Childs sel) r)]
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable {c : Call (PhysicalHost f ell)}
variable (t : Center (printedParams (f:=f) (ell:=ell) s) c)
local notation "Alev" => (Shape.levelBits S (Call.depth c))
local notation "Ulev" => (Shape.levelWidth S (Call.depth c))
local notation "Prec" => (childPrecision (Call.prec c) Alev (Call.edges c) Ulev (Subtype.val t))
local notation "Ord" => (order c.edges Ulev t.val)
local notation "Dg" => (J9PrintedSchedule.degreeBound c.edges (2^Alev))
local notation "Md" => (NativeMenu (N sel) c t)
local notation "Sh" => (paddedShape (N sel) (Childs sel) r)

set_option maxHeartbeats 5000000 in
theorem actual_finite_centre
    (hc : NativeReach (Plan sel) r c) (d : Ready S (sourceDelta s) c)
    (I : SiteTape Prec ell Ord (Dg+1) Md)
    (hD : I.fw.length=f.natDegree)
    (hF : Modulus Prec I.hp I.fw=NativeProbeRing.liftPoly Prec f)
    (raw : ∀ z,(I.masks z).result.val=List.ofFn (NativeProbeRing.chosenRep f.natDegree _ d.fit z))
    (hn : (I.roster.map Prod.fst).Nodup)
    (hr : (I.roster.map Prod.fst).toFinset=(active Alev c.edges Ulev).erase t.val)
    (ho : ∀ q∈I.roster,q.2=order c.edges Ulev q.1)
    (hm : I.modes.Nodup) (hmall : ∀ β,β∈I.modes)
    (hChild : ∀ z β g,boxTransport hF (uvRead I.hp I.fw ell (I.child z β g).result)=
      (sourceBlueprint sel r hf).program.run ((Plan sel).child c ⟨⟨t,z,β,g⟩,d.active⟩)) :
    let B := sourceBlueprint sel r hf
    let R : Responses Sh f ell c := fun w=>B.program.run (B.program.child c w)
    let E : (Box f ell Prec)[X] := (integralE f ell Alev c.edges Ulev t.val).map (reduce Prec f ell)
    let τ : Center Sh c := ⟨t.val,t.property⟩
    let T := I.run Alev t.val
    jetMap (boxTransport hF) Ord (jetRead I.hp I.nonempty T.result)=
      AdjoinRoot.mk (X^Ord) (quotientAt Sh f ell c d.fit R τ E) ∧
    T.steps≤I.nodeBill+I.childBill+I.localFee Alev := by
  let B := sourceBlueprint sel r hf
  let R : Responses Sh f ell c := fun w=>B.program.run (B.program.child c w)
  let τ : Center Sh c := ⟨t.val,t.property⟩
  obtain ⟨eq,cost⟩ := SiteTape.exact_local_receipt I hf hD hF d.fit raw Alev c.edges Ulev
    t.property hn hr ho
  refine ⟨?_,cost⟩
  have G (z : Probe S c) :
      boxTransport hF (nodeMeaning I.hp I.groupedM z)=groupedSample Sh f ell c R τ z := by
    obtain ⟨h,_,_⟩ := metered_native_probe sel r hf c hc d.active t z I.hp I.nonempty I.he
      hF I.modes hm hmall (I.child z) (fun β g=>by
        rw [←boxTransport_cast]
        exact hChild z β g)
    simpa only [SiteTape.groupedM,nodeMeaning,boxTransport_cast] using h
  change jetMap (boxTransport hF) Ord (jetRead I.hp I.nonempty (I.run Alev t.val).result)=_
  rw [eq,show boxTransport hF∘nodeMeaning I.hp I.groupedM=groupedSample Sh f ell c R τ from funext G]
  rfl

#print axioms actual_finite_centre
end J6R22Active




