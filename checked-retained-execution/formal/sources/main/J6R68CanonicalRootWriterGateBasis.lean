import J6R68CanonicalRootWriterOrder
import J6R53TerminalGateGeometry

/-! Read the true retained Gate lanes of the immutable printed
exterior. Columns are Pages; an old Gate's operand lookup is
confined to its own original, signed physical half-port scope. -/
namespace J6R68CanonicalRootWriter
open scoped Polynomial Classical
open Polynomial AOracleMachineTime AOracleMachineTimeTape J6R15ModeCost J6R21Ancestor
open J6R26DescriptorTree J6R35RootOrigins J6R36ChildFramedRoute
open J6R26StablePreparedRoot J6R28GeneratedRootFrame J6R31RootResidentTables
open J6R32RootGeneratedRegistryInputs J6R34RootAtlas J6R41StructuredAllPaths
open J6Mesh J6OrientedHost J6R24LegalLayout J6R10Repack J6R12Blueprint
open J6R12Repack J6ActiveRun J6ActiveSchedule J6R32StatefulArithmetic
open J6R32ChildResidentTransfer J6R27OriginalGate J6R33StatefulArithmeticPage
open J6R37StructuredRoot J6R30GeneratedRootLayout J6R25PreparedSupply
open J6R55BootBodies J6R48RawRoute J6R50SourceProducer J6R54ExteriorOwner
open J6R53OldOwner J6R62Leaf J6R50Leaf J6R52Terminal J6R53TerminalGate
open J6R67CanonicalStop J6R11Blueprint J6R49Leaf J6R51Leaf J6R34ChildPath J6R21Leaf

set_option quotPrecheck false
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2700000
set_option maxRecDepth 4500
set_option maxSynthPendingDepth 12
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q ro co d edgew tc tj key prec tw bw own : ℕ}
variable (X : StableExterior G ell q ro co d edgew tc tj key prec tw bw)
variable (gate : Stamp key prec) (pad : ℕ)
local notation "Ext" => (exteriorChild G ell X.centre X.sample X.group)
local notation "E" => (exteriorChild G ell X.centre X.sample X.group).host.Edge
local notation "U" => (Vertex (exteriorChild G ell X.centre X.sample X.group))
local notation "Row" => (exteriorChild G ell X.centre X.sample X.group).host.Row

def leftAt (r : Row) (e : E) (h : (Ext).host.network.row e=r) : PortAt (atVertex Ext (.inl r)) :=
  ⟨.inl e,congrArg Sum.inl h⟩

def orderedOldPorts (u : Row) : List (PortAt (atVertex Ext (.inl u))) :=
  (scanSubtype (fun e : E=>(Ext).host.network.row e=u)
    (orderedExteriorEdges X)).map (fun x=>leftAt X u x.val x.property)

theorem all_old_ports_in_physical_order (u : Row) (x : PortAt (atVertex Ext (.inl u))) :
    x∈orderedOldPorts X u := by
  obtain ⟨e,h⟩ := x
  cases e with
  | inr e => cases h
  | inl e =>
    let g : {u' : E // (Ext).host.network.row u'=u} :=
      ⟨e,Sum.inl.inj h⟩
    refine List.mem_map.mpr ⟨g,?_ ,rfl⟩
    exact (scan_subtype_mem _ _ g).mpr ((reviewed_exterior_order X).2 e)

private theorem old_back_across_point {f' : ℤ[X]} {ell' : ℕ} {origin a b : Point f' ell'}
    (h : a=b) (tr : Trace origin b) (x : PortAt a) :
    (Eq.mp (congrArg (Trace origin) h.symm) tr).back x=tr.back (castPort h x) := by
  cases h
  rfl

theorem old_root_back_keeps_the_half (u : Row) (x : PortAt (atVertex Ext (.inl u))) :
    ((oldRootTrace X u).back x).val=(edge x.val).val := by
  let M := firstRetained X u
  let E0 : atVertex Ext (.inl u)=M.next :=
    (retained_prescribed_point (G.selector ell) (G.ready ell) (G.centre ell X.centre)
      (J6R27PrescribedProbe.rootPreset G ell) X.sample X.group u).symm
  let tr : Trace (stableOriginal (f:=f) (ell:=ell) (base:=base) (rootOldSource X u)) M.next :=
    .keep .start M
  let y := castPort E0 x
  have e : edge y.val=edge x.val := (cast_port_edge E0 x).trans rfl
  have back := old_back_across_point E0 tr x
  have b : (oldRootTrace X u).back x=M.back y := back
  exact (congrArg Subtype.val b).trans ((M.back_val y).trans (congrArg Subtype.val e))

theorem retained_lane_is_true_original_suffix (name : U→Word own) (u : Row)
    (x : PortAt (atVertex Ext (.inl u))) :
    (exteriorFrameAt X gate pad name (edge x.val)).left.body=
      false::(rootSuffixAt (f:=f) (ell:=ell) (base:=base) P (rootOldSource X u)
        ((oldRootTrace X u).back x)).bits := by
  let p := (oldRootTrace X u).back x
  have b : p.val=(edge x.val).val := old_root_back_keeps_the_half X u x
  have body : (actualLane X gate pad (edge x.val).val).gate.body=
      false::(expectedHalfRow P (oddAxis m) (edge x.val).val).body := rfl
  exact body.trans ((congrArg (fun h=>false::(expectedHalfRow P (oddAxis m) h).body) b).symm)

theorem actual_root_old_scan (name : U→Word own) (injective : Function.Injective name) (u : Row) :
    (collectRetained (name (.inl u)) (trueFrames X gate pad name)).result=
      (orderedOldPorts X u).map (fun x=>requestView (exteriorFrameAt X gate pad name (edge x.val)).left) := by
  let keep := fun e : E=>(Ext).host.network.row e=u
  have eq (e : E) : name (.inl u)=(exteriorFrameAt X gate pad name e).oldOwner ↔ keep e := by
    change name (.inl u)=name (.inl ((Ext).host.network.row e)) ↔ _
    rw [injective.eq_iff]
    exact ⟨fun h=>(Sum.inl.inj h).symm,fun h=>congrArg Sum.inl h.symm⟩
  rw [trueFrames,structured_requests_for_subtype _ _ _ keep eq]
  unfold orderedOldPorts
  rw [List.map_map]
  rfl

#print axioms all_old_ports_in_physical_order
#print axioms old_root_back_keeps_the_half
#print axioms retained_lane_is_true_original_suffix
#print axioms actual_root_old_scan
end
end J6R68CanonicalRootWriter

