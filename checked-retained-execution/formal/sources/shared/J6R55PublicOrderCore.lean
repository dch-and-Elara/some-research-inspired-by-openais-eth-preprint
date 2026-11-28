import J6R34ChildPathOrdinal
import J6R32RootGeneratedRegistryInputsHeader

/-! Exterior analogue of the native ordinal receipt, using the same
root half-port scan as the real original header. A typed equivalence
is a specification of an observed order, not a source of free bytes. -/
namespace J6R55Public
open scoped Classical Polynomial
open Polynomial AOracleMachineTime AOracleMachineTimeTape J6R21Ancestor
open J6R15ModeCost J6R25PreparedSupply J6R27OriginalGate J6R31RootResidentTables
open J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R16ModeCost
open J6R26DescriptorTree J6R24MeteredRecursion J6ActiveRun J6R34ChildPath
open J6R32RootGeneratedRegistryInputs J6R26StablePreparedRoot J6R27PrescribedProbe J6R14ZeroMode
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 19800000
set_option maxRecDepth 3400
set_option Elab.async false

noncomputable section
variable {f : ℤ[X]} {ell s w : ℕ} {c : Call (PhysicalHost f ell)}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {d : Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c}
variable {t : Center (printedParams (f:=f) (ell:=ell) s) c}
variable (D : PhysicalPorts sel d t w)
variable (g : Fin 64)

abbrev ExteriorHalf := {p : Port c.host.Edge // physicalGroup sel d t p=g}

def externalHalfOrder : List (ExteriorHalf (sel:=sel) (d:=d) (t:=t) g) :=
  scanSubtype (fun p=>physicalGroup sel d t p=g) D.order

theorem external_half_projection :
    (externalHalfOrder D g).map Subtype.val=D.physicalSelected g := by
  unfold externalHalfOrder PhysicalPorts.physicalSelected
  let p := fun h : Port c.host.Edge=>physicalGroup sel d t h=g
  change (scanSubtype p D.order).map Subtype.val=(D.order.filter fun x=>decide (p x))
  generalize D.order = O
  induction O with
  | nil => rfl
  | cons head tail ih =>
    by_cases hp : p head
    · simp only [scanSubtype,List.filter_cons,List.filterMap_cons,dif_pos hp,decide_eq_true hp,
        if_true,List.map_cons] at *
      rw [ih]
    · simp only [scanSubtype,List.filter_cons,List.filterMap_cons,dif_neg hp,decide_eq_false hp,
        Bool.false_eq_true,if_false] at *
      exact ih

theorem external_half_complete :
    (externalHalfOrder D g).Nodup ∧ ∀ x,x∈externalHalfOrder D g :=
  ⟨scan_subtype_nodup _ _ D.nodup,fun x=>(scan_subtype_mem _ _ x).mpr (D.complete x.val)⟩

variable (P : Prescribed f (externalProbeDegree s c)) (j : Fin (externalProbeDegree s c+1))

theorem external_half_length :
    (externalHalfOrder D g).length=(externalZeroCall sel d t P j g).edges := by
  have H := physical_count_of_external sel d t D P j g
  rw [←external_half_projection D g,List.length_map] at H
  exact H

def externalEdgeOrder :
    Fin (externalZeroCall sel d t P j g).edges≃(externalZeroCall sel d t P j g).host.Edge :=
  (finCongr (external_half_length D g P j).symm).trans
    (rosterIndex (externalHalfOrder D g) (external_half_complete D g).1 (external_half_complete D g).2)

theorem ext_order_enumerates_actual_halves :
    List.ofFn (externalEdgeOrder D g P j)=(externalHalfOrder D g) := by
  apply List.ext_getElem
  · rw [List.length_ofFn,external_half_length D g P j]
  · intro a ha hb
    rw [List.getElem_ofFn]
    rfl

def externalEdgeKey (p : (externalZeroCall sel d t P j g).host.Edge) : Word w :=
  (D.record (show ExteriorHalf (sel:=sel) (d:=d) (t:=t) g from p).val).address

theorem external_edge_key_injective :
    Function.Injective (externalEdgeKey D g P j) :=
  D.distinct.comp Subtype.val_injective

theorem actual_external_edge_key_book (group : Word 6) (hg : group.val=g.val) :
    let run := selectedEdgeBook group D.raw
    run.result=List.ofFn (fun b : Fin (externalZeroCall sel d t P j g).edges=>externalEdgeKey D g P j (externalEdgeOrder D g P j b)) ∧
      run.result.Nodup ∧
      run.steps≤7+(D.raw.map rowScanFee).sum+(externalZeroCall sel d t P j g).edges*(4*w+5) := by
  let picked := selectPorts group D.raw
  have groupExact : group=word g.val :=
    (valued_word group).symm.trans (congrArg word hg)
  have rows : picked.result=(externalHalfOrder D g).map (fun u=>D.record u.val) := by
    unfold picked
    rw [groupExact,D.physical_port_select,←external_half_projection D g,List.map_map]
    rfl
  let out := copyEdgeIds picked.result
  obtain ⟨raw,fee⟩ := A1R12.mapMeter_exact (fun x : PortRow w=>copyFixed x.address) w (3*w+1)
    picked.result (fun u _=>by change (copyFixed u.address).steps≤_; rw [copy_fixed_exact])
  have keys : out.result=picked.result.map PortRow.address :=
    raw.trans (List.map_congr_left (fun u _=>congrArg Meter.result (copy_fixed_exact u.address)))
  have shape : out.result=List.ofFn (fun b : Fin (externalZeroCall sel d t P j g).edges=>externalEdgeKey D g P j (externalEdgeOrder D g P j b)) := by
    rw [keys,rows,List.map_map,←ext_order_enumerates_actual_halves D g P j,List.map_ofFn]
    rfl
  have count : picked.result.length=(externalZeroCall sel d t P j g).edges := by
    rw [rows,List.length_map,external_half_length D g P j]
  have act : picked.steps=3+(D.raw.map rowScanFee).sum := (select_ports_exact group D.raw).2
  have copied : out.steps≤(externalZeroCall sel d t P j g).edges*(4*w+5) := by
    change out.steps≤picked.result.length*((3*w+1)+w+4) at fee
    rw [count] at fee
    simpa only [show (3*w+1)+w+4=4*w+5 by omega] using fee
  refine ⟨shape,?_ ,?_⟩
  · change out.result.Nodup
    rw [shape]
    exact List.nodup_ofFn.mpr ((external_edge_key_injective D g P j).comp (externalEdgeOrder D g P j).injective)
  · change picked.steps+out.steps+4≤_
    rw [act]
    omega

#print axioms external_half_projection
#print axioms external_half_complete
#print axioms external_half_length
#print axioms externalEdgeOrder
#print axioms ext_order_enumerates_actual_halves
#print axioms actual_external_edge_key_book
end
end J6R55Public

