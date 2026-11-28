import J6R54ExteriorOwnerChart
import J6R54ExteriorOwnerSource

/-! Derive group headers from paid owner-type/cell words. At the
literal root the planted labels are zero; padding row and column
owners use different legs of their actual ordered cell. Empty parent
owners still have a role and a name in this complete descriptor tape. -/
namespace J6R54ExteriorOwner
open scoped Polynomial Classical
open Polynomial AOracleMachineTime AOracleMachineTimeTape J6R15ModeCost J6R21Ancestor
open J6R26DescriptorTree J6R35RootOrigins J6R36ChildFramedRoute
open J6R26StablePreparedRoot J6R28GeneratedRootFrame J6R31RootResidentTables
open J6R32RootGeneratedRegistryInputs J6R34RootAtlas J6R41StructuredAllPaths
open J6Mesh J6OrientedHost J6R24LegalLayout J6R10Repack J6R12Blueprint
open J6R12Repack J6ActiveRun J6ActiveSchedule J6R32StatefulArithmetic
open J6R32ChildResidentTransfer J6R27OriginalGate J6R33StatefulArithmeticPage
open J6R53OldOwner J6R53OldOwnerRoot J6R49SourceLayout J6R37StructuredRoot J6R14LayoutCost
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 18000000
set_option maxRecDepth 3300
set_option maxSynthPendingDepth 12
set_option Elab.async false
noncomputable section

inductive BootRole where
  | planted
  | padding (coords : List Bool)

def emitRoleGroup (axis : List Bool) : BootRole→Meter (Word 6)
  | .planted => ⟨word (q:=6) 0,9⟩
  | .padding coords =>
    let chosen := readSymbol axis coords
    let emitted := fitWord 6 chosen.result
    ⟨emitted.result,chosen.steps+emitted.steps+5⟩

def emitRootHeaders {own : ℕ} (axis : List Bool) :
    List (Word own × BootRole)→Meter (List (OwnerGroup own))
  | []=>⟨[],3⟩
  | (name,role)::rest=>
    let k := copyFixed name
    let g := emitRoleGroup axis role
    let tail := emitRootHeaders axis rest
    ⟨⟨k.result,g.result⟩::tail.result,k.steps+g.steps+tail.steps+6⟩

theorem emit_role_group_at_coord {a : ℕ} (i : Fin a) (axis : List Bool) (fit : axis.length=i.val)
    (c : Fin a→Fin 64) :
    (emitRoleGroup axis (.padding (coordinateLabel c))).result=word (q:=6) (c i).val := by
  have h := coordinate_word_at i axis fit c
  change (fitWord 6 (readSymbol axis (coordinateLabel c)).result).result=_
  rw [h]
  apply word_bits_inj
  rw [fit_word_value _ _ (symbol_length _)]
  rfl

theorem emit_role_group_cost_bound (axis : List Bool) (r : BootRole) :
    (emitRoleGroup axis r).steps≤16*axis.length+35+(fitWord 6 []).steps+5 := by
  cases r with
  | planted =>
    change 9≤16*axis.length+35+(fitWord 6 []).steps+5
    omega
  | padding b =>
    have H := read_symbol_fee axis b
    change (readSymbol axis b).steps+(fitWord 6 (readSymbol axis b).result).steps+5≤_
    rw [fit_word_fee,fit_word_fee]
    omega

theorem emitted_group_header_map {U : Type} {own : ℕ} (axis : List Bool) (name : U→Word own)
    (role : U→BootRole) (g : U→Fin 64) (order : List U)
    (sem : ∀ u,(emitRoleGroup axis (role u)).result=word (g u).val) :
    emitRootHeaders axis (order.map (fun u=>(name u,role u)))=
      ⟨order.map (ownerHeader name g),
        3+(order.map (fun u=>(copyFixed (name u)).steps+(emitRoleGroup axis (role u)).steps+6)).sum⟩ := by
  induction order with
  | nil=>rfl
  | cons u us ih=>
    rw [List.map_cons,emitRootHeaders,ih,sem u]
    simp only [List.map_cons,List.sum_cons,ownerHeader]
    have key : (copyFixed (name u)).result=name u := congrArg Meter.result (copy_fixed_exact _)
    rw [key]
    congr 1
    omega

variable {V : Type} [Fintype V]
variable {f : ℤ[X]} {m n base native : ℕ} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q ro co d edgew tc tj key prec tw bw own : ℕ}
variable (X : StableExterior G ell q ro co d edgew tc tj key prec tw bw)
local notation "Src" => (SourceVertex P)

def trueRootRole (u : Src) : BootRole :=
  match u with
  | .inl (.inl _)=>.planted
  | .inr (.inl _)=>.planted
  | .inl (.inr (p,_))=>.padding (coordinateLabel (fun i=>(p.1 i).1))
  | .inr (.inr p)=>.padding (coordinateLabel (fun i=>(p.1 i).2))

theorem true_role_resolves_original_group (axis : List Bool) (fit : axis.length=(oddAxis m).val)
    (u : Src) :
    (emitRoleGroup axis (trueRootRole u)).result=word (q:=6) (actualGroup X u).val := by
  rw [actual_group_of_every_root_owner X]
  rcases u with ((⟨u,k⟩|⟨p,b⟩)|(⟨u,k⟩|p))
  · rfl
  · exact emit_role_group_at_coord (oddAxis m) axis fit (fun i=>(p.1 i).1)
  · rfl
  · exact emit_role_group_at_coord (oddAxis m) axis fit (fun i=>(p.1 i).2)

def loadActualRootHeaders (axis : List Bool) (roles : Meter (List (Word own × BootRole))) :
    Meter (List (OwnerGroup own)) :=
  let out := emitRootHeaders axis roles.result
  ⟨out.result,roles.steps+out.steps+3⟩

theorem actual_root_group_headers_and_charge (axis : List Bool) (fit : axis.length=(oddAxis m).val)
    (name : Src→Word own) (order : List Src)
    (roles : Meter (List (Word own × BootRole)))
    (aligned : roles.result=order.map (fun u=>(name u,trueRootRole u))) :
    let out := loadActualRootHeaders axis roles
    out.result=order.map (ownerHeader name (actualGroup X)) ∧
    out.steps=roles.steps+3+(3+(order.map
      (fun u=>(copyFixed (name u)).steps+(emitRoleGroup axis (trueRootRole u)).steps+6)).sum) := by
  have made := emitted_group_header_map axis name trueRootRole (actualGroup X) order
    (true_role_resolves_original_group X axis fit)
  change (emitRootHeaders axis roles.result).result=_ ∧
    roles.steps+(emitRootHeaders axis roles.result).steps+3=_
  rw [aligned,made]
  exact ⟨rfl,by dsimp only; omega⟩

#print axioms emit_role_group_at_coord
#print axioms emit_role_group_cost_bound
#print axioms emitted_group_header_map
#print axioms true_role_resolves_original_group
#print axioms actual_root_group_headers_and_charge
end
end J6R54ExteriorOwner
