import J6R53OldOwnerRootEmit
import J6R53OldOwnerBorn
import J6R51IngressPortRows

/-! The actual guarded raw brackets still has brackets, and the charged
fresh equality-tree builder retains its ordered equality rows. Emit
one literal head per such owner including a genuine degree-zero row. -/
namespace J6R53OldOwnerRoot
open scoped Classical
open Std.Sat AOracleMachineTime J6R49RootIngress J6R50RootIngress J6R51Ingress
open J7R9Compiler J7R9Subdivision
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 3100
set_option maxHeartbeats 16000000
set_option maxSynthPendingDepth 12
set_option Elab.async false

def scanClauseSigns : BitsClause→Meter (List Bool)
  | []=>⟨[],3⟩
  | x::xs=>
    let tail := scanClauseSigns xs
    ⟨x.2::tail.result,tail.steps+4⟩

theorem scan_clause_signs_exact (xs : BitsClause) :
    scanClauseSigns xs=⟨xs.map Prod.snd,4*xs.length+3⟩ := by
  induction xs with
  | nil=>rfl
  | cons x xs ih => simp only [scanClauseSigns,ih,List.map_cons,List.length_cons,Nat.mul_succ]

def headsOfClauses : BitsCNF→Meter (List GateHead)
  | []=>⟨[],3⟩
  | row::rows=>
    let first := scanClauseSigns row
    let rest := headsOfClauses rows
    ⟨GateHead.clause first.result::rest.result,first.steps+rest.steps+4⟩

theorem heads_of_clauses_exact (raw : BitsCNF) :
    headsOfClauses raw=⟨raw.map (fun row=>GateHead.clause (row.map Prod.snd)),
      3+(raw.map (fun row=>4*row.length+7)).sum⟩ := by
  induction raw with
  | nil=>rfl
  | cons r rs ih =>
    simp only [headsOfClauses,scan_clause_signs_exact,ih,List.map_cons,List.sum_cons]
    congr 1
    omega

def headsOfEqual {A : Type} : List A→Meter (List GateHead)
  | []=>⟨[],3⟩
  | _::xs=>
    let rest := headsOfEqual xs
    ⟨GateHead.equal::rest.result,rest.steps+4⟩

theorem heads_of_equal_exact {A : Type} (xs : List A) :
    headsOfEqual xs=⟨xs.map (fun _=>GateHead.equal),4*xs.length+3⟩ := by
  induction xs with
  | nil=>rfl
  | cons x xs ih => simp only [headsOfEqual,ih,List.map_cons,List.length_cons,Nat.mul_succ]

def rootHeadsFromData {A : Type} (guarded : BitsCNF) (trees : List A) :
    Meter (List GateHead) :=
  let c := headsOfClauses guarded
  let e := headsOfEqual trees
  let merge := J6R53OldOwner.stitchOwners e.result c.result
  ⟨merge.result,c.steps+e.steps+merge.steps+5⟩

def rawRootHeads {h d j : ℕ} (declares : List (List Bool)) (raw : BitsCNF) :
    Meter (List GateHead) :=
  let brackets := guardedMeter declares raw
  let trees := compileGraph (h:=h) (d:=d) (j:=j) declares raw
  let heads := rootHeadsFromData brackets.result trees.result.equality
  ⟨heads.result,brackets.steps+trees.steps+heads.steps+5⟩

theorem literal_heads_keep_empty (xs : BitsCNF) :
    (headsOfClauses ([]::xs)).result=GateHead.clause []::(headsOfClauses xs).result := rfl

section Meaning
variable {V : Type} [DecidableEq V]
variable (H : CNF V) (code : V→List Bool)

theorem typed_clause_head (i : ClauseIndex H) :
    GateHead.clause (((H.get i).map (codeLit code)).map Prod.snd)=
      gateHead (orderedGate H (.inl i)) := by
  change GateHead.clause (((H.get i).map (codeLit code)).map Prod.snd)=
    GateHead.clause (List.ofFn (fun j : Fin (H.get i).length => (literal H ⟨i,j⟩).2))
  congr 1
  simp only [List.map_map]
  conv_lhs => rw [←List.ofFn_get (H.get i)]
  rw [List.map_ofFn]
  rfl

theorem clause_heads_on_actual_typed_rows :
    (headsOfClauses (codeCNF code H)).result=
      (List.finRange H.length).map (fun i : ClauseIndex H=>gateHead (orderedGate H (.inl i))) := by
  rw [heads_of_clauses_exact]
  have eq : List.finRange H.length=List.ofFn (fun i : ClauseIndex H=>i) := by
    apply List.ext_getElem
    · simp
    · intro i hi₁ hi₂
      apply Fin.ext
      simp
  change (codeCNF code H).map (fun row=>GateHead.clause (row.map Prod.snd))=_
  unfold codeCNF
  rw [eq]
  conv_lhs => rw [←List.ofFn_get H]
  simp only [List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  exact typed_clause_head H code i

theorem fresh_tree_heads_ordered (vs : List V) :
    ((vs.flatMap (J6R51Ingress.orderedVar H)).map (fun _=>GateHead.equal))=
    (vs.flatMap (fun v=>List.ofFn (fun k : Fin (J6R51Ingress.orderedVar H v).length=>
      (Sum.inr ⟨v,k⟩ : OrderedOld H)))).map (fun v=>gateHead (orderedGate H v)) := by
  induction vs with
  | nil=>rfl
  | cons v vs ih =>
    simp only [List.flatMap_cons,List.map_append,ih]
    apply congrArg (fun left=>left++_)
    conv_lhs => rw [←List.ofFn_get (J6R51Ingress.orderedVar H v)]
    simp only [List.map_ofFn]
    rfl

theorem raw_fresh_root_heads_actual
    [Fintype V] {h d j : ℕ}
    (F : CNF V) (s : DeclaredOrder V) (code : V→List Bool) (inj : Function.Injective code)
    (hh : 0<h) (hd : 0<d) (hj : 0<j)
    (fitH : (guardedInOrder F s.roster).length≤2^h)
    (fitD : ∀ row∈guardedInOrder F s.roster,row.length≤2^d)
    (fitJ : ∀ v,(occurrences (guardedInOrder F s.roster) v).length-3≤2^j) :
    let H := guardedInOrder F s.roster
    let out := rawRootHeads (h:=h) (d:=d) (j:=j) (s.roster.map code) (codeCNF code F)
    out.result=(oldRoster H (guardRoster s)).map (fun v=>gateHead (orderedGate H v)) := by
  let H := guardedInOrder F s.roster
  let brackets := guardedMeter (s.roster.map code) (codeCNF code F)
  let graph := compileGraph (h:=h) (d:=d) (j:=j) (s.roster.map code) (codeCNF code F)
  have left : ((headsOfClauses brackets.result).result)=
      (List.finRange H.length).map (fun i : ClauseIndex H=>gateHead (orderedGate H (.inl i))) := by
    unfold brackets
    rw [paid_guard_in_order F s.roster code inj]
    exact clause_heads_on_actual_typed_rows H (guardCode code)
  have right := (raw_graph_exact (h:=h) (d:=d) (j:=j) F s code inj hh hd hj fitH fitD fitJ).2.2
  change (rootHeadsFromData brackets.result graph.result.equality).result=_
  unfold rootHeadsFromData
  dsimp only
  rw [J6R53OldOwner.stitch_owners_exact,left,heads_of_equal_exact]
  change _++graph.result.equality.map (fun _=>GateHead.equal)=_
  change graph.result.equality=_ at right
  rw [right,List.map_map]
  simp only [Function.comp_def,oldRoster,List.map_append,List.map_map]
  rw [fresh_tree_heads_ordered H (guardRoster s).roster]

end Meaning
#print axioms scan_clause_signs_exact
#print axioms heads_of_clauses_exact
#print axioms heads_of_equal_exact
#print axioms literal_heads_keep_empty
#print axioms clause_heads_on_actual_typed_rows
#print axioms raw_fresh_root_heads_actual
end J6R53OldOwnerRoot
