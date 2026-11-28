import J6R49RootIngressBinding
import J6R37StructuredRootFields

/-! The paid ingress is consumed by the exact immutable parent file
selected by R37. This keeps the old compact file identity, physical
chart and original occurrence and never re-packs to a different order. -/
namespace J6R49RootIngress
open scoped Classical Polynomial
open Polynomial Std.Sat J6OrientedHost J6Mesh J6R24LegalLayout J6R26StablePreparedRoot
open J6R30GeneratedRootLayout J6R32RootGeneratedRegistryInputs J6R34RootAtlas
open J6R37StructuredRoot J6R25PreparedSupply AOracleMachineTime J7R10Ports J7R10Plant
open J6R35GatewayPreparation J6R36ChildFramedRoute J6R15ModeCost J6R26DescriptorTree J6R21Ancestor J6R10Repack
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 13000000
set_option maxRecDepth 3900
set_option quotPrecheck false

variable {V : Type} [DecidableEq V] [Fintype V]
variable (F : CNF V) (code : V→List Bool) (inj : Function.Injective code)
variable {f : ℤ[X]} {base native : ℕ}
variable {G : CNFShape F f base native}
variable {ell q r c d edgew tc tj key prec tw bw h : ℕ}
variable (X : StableExterior G ell q r c d edgew tc tj key prec tw bw)
variable (pos : List (Position r c d h))
variable (chart : pos=List.ofFn (positionForWire (guarded F) X.source.codec))
local notation "m" => J7R10Readout.mCNF F
local notation "keys" => ((Finset.univ : Finset V).toList.map code)
local notation "raw" => codeCNF code F


/-- The parsed parent produced above is actually passed to selection
and lane emission, together with the unchanged existing occurrence. -/
noncomputable def buildExteriorLanesFromCNF (gate : Stamp key prec) (pad : ℕ) :
    Meter (Option (ExteriorLanes m key prec pad)) :=
  let R := buildParentIngress m keys raw pos
  match R.result with
  | none => ⟨none,R.steps+4⟩
  | some parents =>
    let J := externalHeaderJob (b:=edgew) X.address.marked X.birth (word (q:=1) 0) parents
    let Y := emitLanes J X.issue gate pad
    ⟨some Y.result,R.steps+Y.steps+5⟩

include inj chart in
theorem actual_exterior_lanes_from_cnf (fit : (guarded F).length≤2^h)
    (gate : Stamp key prec) (pad : ℕ) :
    let run := buildExteriorLanesFromCNF F code X pos gate pad
    run.result=some (outerLanes X gate pad).result ∧
    run.steps=(buildParentIngress m keys raw pos).steps+(outerLanes X gate pad).steps+5 := by
  have parent := (actual_structured_root_from_ingress F code inj X pos chart fit).1
  have shared : (rootPreparationFor X).result.parents=(rootParent X).raw :=
    (actual_shared_parent_file G X.source ell X.field X.hq X.copies X.pre X.centre).1
  dsimp only [buildExteriorLanesFromCNF,outerLanes]
  rw [parent]
  simp [shared]

include inj chart in
theorem actual_origin_lane_is_produced (fit : (guarded F).length≤2^h)
    (gate : Stamp key prec) (pad : ℕ) (rail : Port (RootWire m))
    (groupEq : physicalGroup (G.selector ell) (G.ready ell) (G.centre ell X.centre) rail=X.group) :
    ∃ out, (buildExteriorLanesFromCNF F code X pos gate pad).result=some out ∧
      actualLane X gate pad rail∈out.lanes := by
  exact ⟨(outerLanes X gate pad).result,
    (actual_exterior_lanes_from_cnf F code inj X pos chart fit gate pad).1,
    selected_root_lane X gate pad rail groupEq⟩

#print axioms actual_exterior_lanes_from_cnf
#print axioms actual_origin_lane_is_produced
end J6R49RootIngress
