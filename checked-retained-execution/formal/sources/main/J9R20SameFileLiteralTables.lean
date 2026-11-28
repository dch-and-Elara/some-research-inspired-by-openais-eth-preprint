
import J9R20SameFileTables

/-! Explicit local old tables and exact arities of the original
four-clone graph. Original graph edges have their positive OR, cyclic
copy edges enforce equality, and each clone has its three-port equality.
The physical port type is the original incidence fibre. -/
namespace J9R20SameFile
open scoped Classical BigOperators
open J7SourceLabels J7SeatSource J7PrintedParamsGraph J7ToJ8Incidence J8Physical LiteralPortCompiler
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4200000

variable {Pair H : Type} [Fintype Pair] [Fintype H]
variable (ends : H×Bool≃Pin Pair×Fin 3)
local notation "T" => column ends cycle
local notation "D" => PrintedOld Pair H

theorem route_rightInverse (next : Equiv.Perm Index) :
    Function.RightInverse (routeBack ends next) (route ends next) := by
  rintro ⟨p|(c|v), k⟩
  · cases k <;> simp [routeBack,route]
  · cases c <;> rfl
  · rcases v with ⟨p,j⟩
    cases k with
    | none => simp [routeBack,route]
    | some b => cases b <;> simp [routeBack,route]

def actualOrdinaryRoute (next : Equiv.Perm Index) :
    OrdinaryWire Pair H ≃ Sigma (Port (Pair:=Pair) (G:=H)) :=
  ⟨route ends next,routeBack ends next,route_leftInverse ends next,route_rightInverse ends next⟩

private def portValue {V : Type} {P : V→Type} (v : V) : {p : Sigma P // p.1=v} ≃ P v where
  toFun p := p.prop ▸ p.val.2
  invFun x := ⟨⟨v,x⟩,rfl⟩
  left_inv := by rintro ⟨⟨p,x⟩,h⟩; change p=v at h; subst p; rfl
  right_inv _ := rfl

theorem ordinary_fibre_exact (v : D) : Nat.card {w : OrdinaryWire Pair H // T w=v} = Nat.card (Port v) := by
  let Q := (actualOrdinaryRoute ends cycle).subtypeEquiv
    (p:=fun w:OrdinaryWire Pair H=> T w=v) (q:=fun y:Sigma (Port (Pair:=Pair) (G:=H))=>y.1=v)
    (by intro w; rfl)
  exact Nat.card_congr (Q.trans (portValue v))

theorem printed_old_arity (v : D) : Nat.card (Ports T v) =
    match v with
    | .inl _ => 3
    | .inr (.inl _) => 2
    | .inr (.inr _) => 3 := by
  cases v with
  | inl s =>
    rw [Nat.card_congr (clonePorts T s),Nat.card_sum,Nat.card_unique,ordinary_fibre_exact ends]
    change 1 + Nat.card Bool = 3
    simp
  | inr o =>
    rw [Nat.card_congr (ordinaryPorts T o),ordinary_fibre_exact ends]
    cases o with
    | inl c => change Nat.card Bool = 2; simp
    | inr x => change Nat.card (Option Bool)=3; simp [Nat.card_eq_fintype_card]

theorem every_clone_is_trivalent (x : Pin Pair×Index) :
    Nat.card (Ports T (cloneOwner (H:=H) x))=3 := by
  rw [printed_old_arity ends]
  obtain ⟨s,i⟩ := x
  cases i <;> rfl

def graphEdgeOwner : D→Bool
  | .inr (.inl (.inl _)) => true
  | _ => false

def positiveOr {I : Type} [Fintype I] : CNF I :=
  [((Finset.univ : Finset I).toList.map fun p => (p,true))]

theorem positiveOr_true {I : Type} [Fintype I] (x : I→Bool) :
    satisfied positiveOr x=true ↔ ∃ i,x i=true := by
  simp [positiveOr,satisfied,lit,List.any_eq_true]

variable {Packet R : Type} {L : ℕ}
variable (d : Layout Packet R (Pin Pair) (PrintedOld Pair H) (Fin 64) (Ports (column ends cycle)) L)

def originalOldTables : OldTables d := by
  classical
  intro g v
  letI : Fintype (LocalPort d v) := Fintype.ofFinite _
  exact if graphEdgeOwner v.val then positiveOr else fullEqualityCNF

theorem original_tables_preserve_all_clones :
    LocalCloneLaw d (originalOldTables ends d) (allCloneOwners (Pair:=Pair) (H:=H)) := by
  intro v hv a
  obtain ⟨x,hx⟩ := (mem_allCloneOwners _).1 hv
  have eq : v = cloneOwner x := Sum.inr.inj (Option.some.inj hx)
  have h : graphEdgeOwner v=false := by
    rw [eq]
    obtain ⟨s,k⟩ := x
    cases k <;> rfl
  unfold originalOldTables
  rw [if_neg (fun h' => Bool.noConfusion (h.symm.trans h'))]
  exact @fullEqualityCNF_true (Ports T v) (Fintype.ofFinite _) a

theorem original_old_tables_satisfiable :
    ∀ g (v : LocalColumn d g), ∃ x : LocalPort d v→Bool, satisfied (originalOldTables ends d g v) x=true := by
  intro g v
  cases h : graphEdgeOwner v.val with
  | false =>
    refine ⟨fun _=>false,?_⟩
    unfold originalOldTables
    rw [if_neg (fun h' => Bool.noConfusion (h.symm.trans h'))]
    exact (@fullEqualityCNF_true (LocalPort d v) (Fintype.ofFinite _) (fun _=>false)).2 (fun _ _=>rfl)
  | true =>
    refine ⟨fun _=>true,?_⟩
    unfold originalOldTables
    rw [if_pos h]
    apply (@positiveOr_true (LocalPort d v) (Fintype.ofFinite _) (fun _=>true)).2
    have hp : 0<Nat.card (Ports T v.val) := by
      rw [printed_old_arity ends]
      rcases v.val with _|(c|_)
      · exact (by decide : 0<3)
      · exact (by decide : 0<2)
      · exact (by decide : 0<3)
    exact ⟨Classical.choice (Nat.card_pos_iff.mp hp).1,rfl⟩

#print axioms route_rightInverse
#print axioms actualOrdinaryRoute
#print axioms ordinary_fibre_exact
#print axioms printed_old_arity
#print axioms every_clone_is_trivalent
#print axioms positiveOr_true
#print axioms originalOldTables
#print axioms original_tables_preserve_all_clones
#print axioms original_old_tables_satisfiable
end
end J9R20SameFile
