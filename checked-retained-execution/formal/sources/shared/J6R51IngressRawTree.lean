import J6R51IngressOccurrence
import J6R49RootIngressFees

/-! Actual equality-tree generation directly from the paid raw parser
and variable bucket. Fresh internal edges have local ranks 0 .. d-4,
and the two sides are emitted by the original directed caterpillar. -/
namespace J6R51Ingress
open scoped Classical
open Std.Sat A1R10 AOracleMachineTime J6R49RootIngress J6R50RootIngress
open J7R9Compiler J7R9Subdivision J7R9DirectedTree
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 11000000

inductive WireKey (h d j : ℕ)
  | original (clause : Word h) (localLeg : Word d)
  | tree (owner : List Bool) (index : Word j)

def keyOf {V : Type*} [DecidableEq V] {h d j : ℕ}
    (H : CNF V) (code : V→List Bool) : Wire H→WireKey h d j
  | .inl o => .original (wordAt h o.1.val) (wordAt d o.2.val)
  | .inr q => .tree (code q.1) (wordAt j q.2.val)

def halfKey {V : Type*} [DecidableEq V] {h d j : ℕ}
    (H : CNF V) (code : V→List Bool) (e : Half H) : WireKey h d j×Bool :=
  (keyOf H code e.1,e.2)

def keyOfToken {h d j : ℕ} (x : OccToken h d) : WireKey h d j :=
  .original x.clause x.leg

structure RawTree (h d j : ℕ) where
  privateWires : List (WireKey h d j)
  gates : List (List (WireKey h d j×Bool))

def compileTree {h d j : ℕ} (v : List Bool) (slots : List (OccToken h d)) :
    Meter (RawTree h d j) :=
  let front := bucket v slots
  let ranks := indexTape j (front.result.length-3)
  let priv := ranks.result.map (WireKey.tree v)
  let ext := front.result.map (fun z => ((keyOfToken z : WireKey h d j),true))
  let rows := halfGates ext priv
  ⟨⟨priv,rows⟩,front.steps+ranks.steps+18+
    front.result.length*(30+8*(h+d+v.length))+
    priv.length*(44+12*(j+v.length))⟩

theorem half_gates_map {A B : Type*} (m : A→B) (front : List (A×Bool)) (priv : List A) :
    (halfGates front priv).map (List.map (fun x=>(m x.1,x.2)))=
      halfGates (front.map (fun x=>(m x.1,x.2))) (priv.map m) := by
  induction priv generalizing front with
  | nil => cases front <;> rfl
  | cons z zs ih =>
    cases front with
    | nil => rfl
    | cons x xs =>
      cases xs with
      | nil => rfl
      | cons y ys =>
        simp only [halfGates,List.map_cons]
        rw [ih ((z,true)::ys)]
        rfl

theorem actual_tree_from_parsed_slots {V : Type*} [DecidableEq V] {h d j : ℕ}
    (H : CNF V) (code : V→List Bool) (inj : Function.Injective code) (v : V)
    (hj : 0<j) (fit : (occurrences H v).length-3≤2^j) :
    let R := compileTree (j:=j) (code v)
      ((occurrenceOrder H).map (guardToken H code) : List (OccToken h d))
    R.result.privateWires=(internal H v).map (keyOf H code) ∧
      R.result.gates=(orderedVar H v).map (List.map (halfKey H code)) := by
  let raw : List (OccToken h d) := (occurrenceOrder H).map (guardToken H code)
  have b : (bucket (code v) raw).result=(forVariable H v).map (guardToken H code) :=
    bucket_actual_occurrences H code inj v
  have e : (forVariable H v).length=(occurrences H v).length := (for_variable_perm H v).length_eq
  have R := (index_tape_exact j ((occurrences H v).length-3) hj fit).1
  have privateEq : (internal H v).map (keyOf H code)=
      (List.ofFn (fun i : Fin ((occurrences H v).length-3)=>wordAt j i.val)).map
        (WireKey.tree (h:=h) (d:=d) (code v)) := by
    simp only [internal,List.map_ofFn]
    rfl
  have externalEq : ((forVariable H v).map (guardToken H code)).map
      (fun z : OccToken h d=>((keyOfToken z : WireKey h d j),true))=
      ((orderedExternal H v).map (fun w=>(w,true))).map (halfKey H code) := by
    simp only [orderedExternal,List.map_map]
    rfl
  dsimp only [compileTree]
  change (indexTape j ((bucket (code v) raw).result.length-3)).result.map
      (WireKey.tree (code v)) = _ ∧ _
  rw [b,List.length_map,e,R,←privateEq]
  constructor
  · rfl
  · rw [externalEq]
    exact (half_gates_map (keyOf H code)
      ((orderedExternal H v).map (fun w=>(w,true))) (internal H v)).symm

theorem actual_tree_from_raw_cnf {V : Type} [DecidableEq V] [Fintype V] {h d j : ℕ}
    (F : CNF V) (code : V→List Bool) (inj : Function.Injective code)
    (hh : 0<h) (hd : 0<d) (hj : 0<j) (fitH : (guarded F).length≤2^h)
    (fitD : ∀ row∈(guarded F),row.length≤2^d) (v : Option V)
    (fitJ : (occurrences (guarded F) v).length-3≤2^j) :
    let P := parseInput (h:=h) (d:=d) ((Finset.univ : Finset V).toList.map code) (codeCNF code F)
    let R := compileTree (j:=j) (guardCode code v) P.result
    R.result.privateWires=(internal (guarded F) v).map (keyOf (guarded F) (guardCode code)) ∧
      R.result.gates=(orderedVar (guarded F) v).map (List.map (halfKey (guarded F) (guardCode code))) := by
  dsimp only
  rw [parse_actual_cnf F code inj hh hd fitH fitD]
  exact actual_tree_from_parsed_slots (guarded F) (guardCode code) (guard_code_injective code inj) v hj fitJ

#print axioms half_gates_map
#print axioms actual_tree_from_parsed_slots
#print axioms actual_tree_from_raw_cnf
end J6R51Ingress
