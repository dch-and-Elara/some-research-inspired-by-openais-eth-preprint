import J6R50RootIngressRankFee
import J6R49RootIngressPayload

/-! End the paid rank-book pass at the actual first R41 half-port
payload, not at a merely isomorphic root chart. The supplied old
wires and subdivision ranks are the sole new ABI inputs. -/
namespace J6R50RootIngress
open scoped Classical Polynomial
open Polynomial Std.Sat J6OrientedHost J6Mesh J6R24LegalLayout J6R26StablePreparedRoot
open J6R30GeneratedRootLayout J6R32RootGeneratedRegistryInputs J6R34RootAtlas
open J6R37StructuredRoot J6R25PreparedSupply AOracleMachineTime J7R10Ports J7R10Plant
open J6R35GatewayPreparation J6R36ChildFramedRoute J6R15ModeCost J6R26DescriptorTree
open J6R21Ancestor J6R10Repack J6R41StructuredAllPaths J6R49RootIngress
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
variable {ell q r c d edgew tc tj key prec tw bw h w : ℕ}
variable (X : StableExterior G ell q r c d edgew tc tj key prec tw bw)
variable (rows : List (RowBook w r h)) (cols : ColBook w)
local notation "m" => J7R10Readout.mCNF F

noncomputable def buildExteriorLanesFromBooks (gate : Stamp key prec) (pad : ℕ) :
    Meter (Option (ExteriorLanes m key prec pad)) :=
  let A := recoveredAtlas (c:=c) (d:=d) (nWires (guarded F)) rows cols
  match A.result with
  | none => ⟨none,A.steps+4⟩
  | some pos =>
    let Z := buildExteriorLanesFromCNF F code X pos gate pad
    ⟨Z.result,A.steps+Z.steps+6⟩

include inj in
theorem paid_rank_books_original_root
    (hw : 0<w) (hd : 0<d) (hc : 0<c)
    (rankFit : nWires (guarded F)≤2^w) (clauseFit : (guarded F).length≤2^h)
    (order : List (Old (guarded F))) (exhaustive : ∀ v,v∈order)
    (exactRow : rows=order.map (rowSpec (guarded F) X.source.codec))
    (exactCol : cols=colSpec (guarded F))
    (gate : Stamp key prec) (pad : ℕ) :
    let B := buildExteriorLanesFromBooks F code X rows cols gate pad
    let A := recoveredAtlas (c:=c) (d:=d) (nWires (guarded F)) rows cols
    let pos := List.ofFn (positionForWire (guarded F) X.source.codec :
      Fin (nWires (guarded F))→Position r c d h)
    B.result=some (outerLanes X gate pad).result ∧
      B.steps=A.steps+(buildExteriorLanesFromCNF F code X pos gate pad).steps+6 := by
  have a := recovered_actual_unsigned_atlas (guarded F) X.source.codec hw rankFit hd hc
    rows cols order exhaustive exactRow exactCol
  dsimp only [buildExteriorLanesFromBooks]
  rw [a]
  exact ⟨(actual_exterior_lanes_from_cnf F code inj X _ rfl clauseFit gate pad).1,rfl⟩

include inj in
theorem r41_payload_from_paid_rank_books
    (hw : 0<w) (hd : 0<d) (hc : 0<c)
    (rankFit : nWires (guarded F)≤2^w) (clauseFit : (guarded F).length≤2^h)
    (order : List (Old (guarded F))) (exhaustive : ∀ v,v∈order)
    (exactRow : rows=order.map (rowSpec (guarded F) X.source.codec))
    (exactCol : cols=colSpec (guarded F))
    (gate : Stamp key prec) (pad : ℕ)
    (x : Port ((exteriorChild G ell X.centre X.sample X.group).host.Edge)) :
    ∃ out lane,
      (buildExteriorLanesFromBooks F code X rows cols gate pad).result=some out ∧
      lane∈out.lanes ∧
      initialPayload X gate pad x=lanePayload (if side x then lane.packet else lane.gate) := by
  have a := recovered_actual_unsigned_atlas (guarded F) X.source.codec hw rankFit hd hc
    rows cols order exhaustive exactRow exactCol
  obtain ⟨out,lane,run,hl,ex⟩ :=
    r41_payload_from_paid_original_root F code inj X _ rfl clauseFit gate pad x
  refine ⟨out,lane,?_,hl,ex⟩
  dsimp only [buildExteriorLanesFromBooks]
  rw [a]
  exact run

#print axioms paid_rank_books_original_root
#print axioms r41_payload_from_paid_rank_books
end J6R50RootIngress
