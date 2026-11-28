import J6R50RootIngressRankSyntax
import J6R49RootIngressPayload

/-! Raw input and two recovered rank books, without the final atlas
or separate copied row/leg/column words, produce the same real R41
seed. This version derives clause selectors from the paid guard syntax
and does not repeat the guard for the sign pass. -/
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
set_option maxHeartbeats 14500000
set_option maxRecDepth 3900
set_option quotPrecheck false

variable {V : Type} [DecidableEq V] [Fintype V]
variable (F : CNF V) (code : V→List Bool) (inj : Function.Injective code)
variable {f : ℤ[X]} {base native : ℕ}
variable {G : CNFShape F f base native}
variable {ell q r c d edgew tc tj key prec tw bw w : ℕ}
variable (X : StableExterior G ell q r c d edgew tc tj key prec tw bw)
variable (lit eqs : List (BareRankRow w r)) (cols : ColBook w)
local notation "m" => J7R10Readout.mCNF F
local notation "keys" => ((Finset.univ : Finset V).toList.map code)
local notation "raw" => codeCNF code F

noncomputable def buildCategorizedExterior (hwClause : ℕ) (gate : Stamp key prec) (pad : ℕ) :
    Meter (Option (ExteriorLanes m key prec pad)) :=
  let A := compileParsedRoles (c:=c) (d:=d) (h:=hwClause) (nWires (guarded F)) keys raw lit eqs cols
  match A.result with
  | none => ⟨none,A.steps+4⟩
  | some compact =>
    let P := makeHalfTape m [] compact
    let J := externalHeaderJob (b:=edgew) X.address.marked X.birth (word (q:=1) 0) P.result
    let Y := emitLanes J X.issue gate pad
    ⟨some Y.result,A.steps+P.steps+Y.steps+7⟩

variable (hw : 0<w) (hd : 0<d) (hc : 0<c) {h : ℕ} (hh : 0<h)
variable (rankFit : nWires (guarded F)≤2^w) (clauseFit : (guarded F).length≤2^h)
variable (eqOrder : List (TreeIndex (guarded F))) (ex : ∀ j,j∈eqOrder)
variable (hl : lit=List.ofFn (fun i : J7R9Compiler.ClauseIndex (guarded F) =>
  bareRankSpec (guarded F) X.source.codec (.inl i)))
variable (he : eqs=eqOrder.map (fun i => bareRankSpec (guarded F) X.source.codec (.inr i)))
variable (exactCol : cols=colSpec (guarded F))

include inj hw hd hc hh rankFit clauseFit ex hl he exactCol in
theorem actual_categorized_exterior (gate : Stamp key prec) (pad : ℕ) :
    let B := buildCategorizedExterior F code X lit eqs cols h gate pad
    let A := compileParsedRoles (c:=c) (d:=d) (h:=h) (nWires (guarded F)) keys raw lit eqs cols
    B.result=some (outerLanes X gate pad).result ∧
      B.steps=A.steps+(makeHalfTape m [] X.source.raw).steps+(outerLanes X gate pad).steps+7 := by
  obtain ⟨out,paid,C⟩ := paid_original_compact_from_categorized_ranks F code inj X.source.codec
    hw hd hc hh rankFit clauseFit lit eqs cols eqOrder ex hl he exactCol
  have exactRaw : out.raw=X.source.raw := by rw [out.exactFile,X.source.exactFile,C]
  rw [exactRaw] at paid
  have shared : (rootPreparationFor X).result.parents=(rootParent X).raw :=
    (actual_shared_parent_file G X.source ell X.field X.hq X.copies X.pre X.centre).1
  have parent := (generated_typed_parent_receipt G X.source ell X.centre).1
  dsimp only [buildCategorizedExterior]
  rw [paid]
  dsimp only
  have e : (makeHalfTape m [] X.source.raw).result=(rootPreparationFor X).result.parents :=
    parent.symm.trans shared.symm
  change some (emitLanes (externalHeaderJob (b:=edgew) X.address.marked X.birth (word (q:=1) 0)
    (makeHalfTape m [] X.source.raw).result) X.issue gate pad).result =
      some (outerLanes X gate pad).result ∧ _
  constructor
  · rw [e]
    rfl
  · rw [e]
    rfl

include inj hw hd hc hh rankFit clauseFit ex hl he exactCol in
theorem actual_categorized_R41_initial_payload (gate : Stamp key prec) (pad : ℕ)
    (x : Port ((exteriorChild G ell X.centre X.sample X.group).host.Edge)) :
    ∃ out lane,
      (buildCategorizedExterior F code X lit eqs cols h gate pad).result=some out ∧
      lane∈out.lanes ∧
      initialPayload X gate pad x=lanePayload (if side x then lane.packet else lane.gate) := by
  let rail : Port (RootWire m) := (edge x).val
  have groupEq : physicalGroup (G.selector ell) (G.ready ell) (G.centre ell X.centre) rail=X.group :=
    (edge x).property
  refine ⟨(outerLanes X gate pad).result,actualLane X gate pad rail,?_,?_,rfl⟩
  · exact (actual_categorized_exterior F code inj X lit eqs cols hw hd hc hh
      rankFit clauseFit eqOrder ex hl he exactCol gate pad).1
  · exact selected_root_lane X gate pad rail groupEq

#print axioms actual_categorized_exterior
#print axioms actual_categorized_R41_initial_payload
end J6R50RootIngress
