import J6R54TerminalBootPath
import J6R25PreparedSupplyPhysicalPorts

/-! The first raw layout/name tape and its byte-level body/owner
agreement are logically distinct. Whole-list matching over the
actual complete orders certifies the latter. Conversely, true
layout and even identical key/group words alone cannot imply it. -/
namespace J6R54TerminalBoot
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R27OriginalGate J6OrientedHost
open J6Mesh J6R35RootOrigins J6R34RootAtlas J6R31RootResidentTables J6R32RootGeneratedRegistryInputs
open J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe
open J6R26DescriptorTree J6R34ChildPath J6R36ChildFramedRoute J6R50SourceProducer
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R22Active J6R24MeteredRecursion
open J6R9Recursive J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R49SourceLayout
open J6R51ParentFrames J6R51Online J6R41StructuredAllPaths J6R25PreparedSupply
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 28000000
set_option maxRecDepth 5000
set_option Elab.async false

theorem equal_maps_on_complete_orders {A B : Type*} (xs : List A) (all : ∀ x,x∈xs)
    (left right : A→B) (same : xs.map left=xs.map right) : left=right := by
  funext a
  obtain ⟨i,h⟩ := List.mem_iff_get.mp (all a)
  subst a
  have get := congrArg (fun l : List B=>l[i.val]?) same
  simpa [i.isLt] using get

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q ro co de edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q ro co de edgew tc tj key prec tw bw)
variable {pad s C rate : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
variable (M : OnlineMachine T key prec tw bw (pageKeyWidth m+pad) rate)
variable (gate : Stamp key prec)
local notation "r" => (exteriorChild G ell X.centre X.sample X.group)

theorem exact_boot_from_complete_owner_and_port_tapes
    (ownerOrder : (Plan sel).Slot r→List ((r).host.Row⊕(r).host.Col))
    (ownerAll : ∀ w u,u∈ownerOrder w)
    (ownerWords : ∀ w,(ownerOrder w).map (M.initial w).result.origins=
      (ownerOrder w).map (initialOrigin X gate pad))
    (bodyWords : ∀ w,
      let phys := (M.initial w).result.birth.native.physical
      phys.raw.map PortRow.body=phys.order.map (fun h=>(initialPayload X gate pad h).2)) :
    ExactPrintedBoot X M gate := by
  constructor
  · intro w
    exact equal_maps_on_complete_orders (ownerOrder w) (ownerAll w) _ _ (ownerWords w)
  · intro w h
    let phys := (M.initial w).result.birth.native.physical
    have raw := bodyWords w
    change phys.raw.map PortRow.body=_ at raw
    rw [phys.source,List.map_map] at raw
    exact congrFun (equal_maps_on_complete_orders phys.order phys.complete _ _ raw) h

end
section ShapeCounterexample
variable {f : ℤ[X]} {ell s C width : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {c : Call (PhysicalHost f ell)}
variable {d : J6R12Blueprint.Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c}
variable {t : Center (printedParams (f:=f) (ell:=ell) s) c}

def replaceOnlyPhysicalBodies (D : PhysicalPorts sel d t width)
    (body : Port c.host.Edge→List Bool) : PhysicalPorts sel d t width :=
  let row := fun h=>{ D.record h with body := body h }
  ⟨D.order.map row,D.order,D.nodup,D.complete,row,rfl,D.labelled,D.distinct⟩

theorem valid_names_and_groups_do_not_determine_boot_body (D : PhysicalPorts sel d t width)
    (h : Port c.host.Edge) :
    ∃ E : PhysicalPorts sel d t width,
      E.order=D.order ∧
      (∀ p,(E.record p).address=(D.record p).address ∧ (E.record p).group=(D.record p).group) ∧
      (E.record h).body≠(D.record h).body := by
  refine ⟨replaceOnlyPhysicalBodies D (fun p=>false::(D.record p).body),rfl,fun _=>⟨rfl,rfl⟩,?_⟩
  intro unexpected
  have hlen := congrArg List.length unexpected
  change (D.record h).body.length+1=(D.record h).body.length at hlen
  omega

end ShapeCounterexample
#print axioms equal_maps_on_complete_orders
#print axioms exact_boot_from_complete_owner_and_port_tapes
#print axioms valid_names_and_groups_do_not_determine_boot_body
end J6R54TerminalBoot
