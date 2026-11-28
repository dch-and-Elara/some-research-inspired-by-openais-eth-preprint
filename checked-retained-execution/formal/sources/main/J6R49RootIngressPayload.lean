import J6R49RootIngressExterior
import J6R41StructuredAllPathsRoot

/-! The paid ingress is consumed by the exact immutable parent file
selected by R37. This keeps the old compact file identity, physical
chart and original occurrence and never re-packs to a different order. -/
namespace J6R49RootIngress
open scoped Classical Polynomial
open Polynomial Std.Sat J6OrientedHost J6Mesh J6R24LegalLayout J6R26StablePreparedRoot
open J6R30GeneratedRootLayout J6R32RootGeneratedRegistryInputs J6R34RootAtlas
open J6R37StructuredRoot J6R25PreparedSupply AOracleMachineTime J7R10Ports J7R10Plant
open J6R35GatewayPreparation J6R36ChildFramedRoute J6R15ModeCost J6R26DescriptorTree J6R21Ancestor J6R10Repack
open J6R41StructuredAllPaths
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



local notation "ext" => exteriorChild G ell X.centre X.sample X.group

include inj chart in
/-- The raw initial R41 payload for every real exterior half-port is
literally selected from this paid R37 output, not an equal-looking
payload reconstructed from a different chart. -/
theorem r41_payload_from_paid_original_root (fit : (guarded F).length≤2^h)
    (gate : Stamp key prec) (pad : ℕ)
    (x : Port ((exteriorChild G ell X.centre X.sample X.group).host.Edge)) :
    ∃ out lane,
      (buildExteriorLanesFromCNF F code X pos gate pad).result=some out ∧
      lane∈out.lanes ∧
      initialPayload X gate pad x=lanePayload (if side x then lane.packet else lane.gate) := by
  let rail : Port (RootWire m) := (edge x).val
  have groupEq : physicalGroup (G.selector ell) (G.ready ell) (G.centre ell X.centre) rail=X.group :=
    (edge x).property
  obtain ⟨out,paid,selected⟩ := actual_origin_lane_is_produced F code inj X pos chart fit gate pad rail groupEq
  exact ⟨out,actualLane X gate pad rail,paid,selected,rfl⟩

#print axioms r41_payload_from_paid_original_root
end J6R49RootIngress
