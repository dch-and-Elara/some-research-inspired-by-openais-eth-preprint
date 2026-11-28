import J6R51IngressRawTree
import J6R51IngressFreshInputOrder
import J6R51IngressFreshPlant

/-! The submitted declaration order and literal encounter order
produce the entire fresh raw wire roster and all equality rows. This
does not identify an archived selected physical seating or export its
old row labels. -/
namespace J6R51Ingress
open scoped Classical
open Std.Sat A1R10 AOracleMachineTime J6R49RootIngress J7R9Compiler J7R9Subdivision
open J7R10Plant J6OrientedHostEval
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 13400000


def guardRoster {V : Type*} (s : DeclaredOrder V) : DeclaredOrder (Option V) where
  roster := none::s.roster.map some
  distinct := by simpa using s.distinct.map (Option.some_injective V)
  complete v := by cases v <;> simp [s.complete]

def compileForest {h d j : ℕ} (slots : List (OccToken h d)) :
    List (List Bool)→Meter (RawTree h d j)
  | [] => ⟨⟨[],[]⟩,2⟩
  | k::ks =>
    let a := compileTree (j:=j) k slots
    let b := compileForest slots ks
    ⟨⟨a.result.privateWires++b.result.privateWires,a.result.gates++b.result.gates⟩,
      a.steps+b.steps+8+8*(a.result.privateWires.length+a.result.gates.length)⟩

theorem forest_from_charged_parser {V : Type*} [DecidableEq V] {h d j : ℕ}
    (H : CNF V) (code : V→List Bool) (inj : Function.Injective code) (roster : List V)
    (hj : 0<j) (fits : ∀ v∈roster,(occurrences H v).length-3≤2^j) :
    let l := ((occurrenceOrder H).map (guardToken H code) : List (OccToken h d))
    let R := compileForest (j:=j) l (roster.map code)
    R.result.privateWires=(roster.flatMap (internal H)).map (keyOf H code) ∧
      R.result.gates=(roster.flatMap (orderedVar H)).map (List.map (halfKey H code)) := by
  induction roster with
  | nil => exact ⟨rfl,rfl⟩
  | cons k ks ih =>
    obtain ⟨x,y⟩ := actual_tree_from_parsed_slots (h:=h) (d:=d) H code inj k hj (fits k List.mem_cons_self)
    obtain ⟨xs,ys⟩ := ih (fun v hv => fits v (List.mem_cons_of_mem _ hv))
    dsimp only [compileForest] at xs ys ⊢
    simp only [List.map_cons,compileForest,List.flatMap_cons,List.map_append,x,y,xs,ys]
    constructor <;> trivial

structure RawGraph (h d j : ℕ) where
  edges : List (WireKey h d j)
  clauses : List (OccToken h d)
  equality : List (List (WireKey h d j×Bool))

def compileGraph {h d j : ℕ} (declares : List (List Bool)) (raw : BitsCNF) :
    Meter (RawGraph h d j) :=
  let I := parseInput (h:=h) (d:=d) declares raw
  let K := compileForest (j:=j) I.result ([false]::declares.map (true::·))
  ⟨⟨I.result.map keyOfToken++K.result.privateWires,I.result,K.result.gates⟩,
    I.steps+K.steps+8+8*(declares.length+I.result.length)⟩

theorem raw_graph_exact {V : Type} [DecidableEq V] [Fintype V] {h d j : ℕ}
    (F : CNF V) (s : DeclaredOrder V) (code : V→List Bool) (inj : Function.Injective code)
    (hh : 0<h) (hd : 0<d) (hj : 0<j)
    (fitH : (guardedInOrder F s.roster).length≤2^h)
    (fitD : ∀ row∈guardedInOrder F s.roster,row.length≤2^d)
    (fitJ : ∀ v,(occurrences (guardedInOrder F s.roster) v).length-3≤2^j) :
    let H := guardedInOrder F s.roster
    let G := compileGraph (h:=h) (d:=d) (j:=j) (s.roster.map code) (codeCNF code F)
    G.result.edges=(wireOrder H (guardRoster s)).map (keyOf H (guardCode code)) ∧
      G.result.clauses=(occurrenceOrder H).map (guardToken H (guardCode code)) ∧
      G.result.equality=((guardRoster s).roster.flatMap (orderedVar H)).map
        (List.map (halfKey H (guardCode code))) := by
  let H := guardedInOrder F s.roster
  let C := guardCode code
  have e := parse_fresh_order_raw F s.roster code inj hh hd fitH fitD
  have f : [false]::(s.roster.map code).map (true::·)=(guardRoster s).roster.map C := by
    simp [guardRoster,C,guardCode,List.map_map,Function.comp_def]
  obtain ⟨w,g⟩ := forest_from_charged_parser (h:=h) (d:=d) H C
    (guard_code_injective code inj) (guardRoster s).roster hj (fun v _=>fitJ v)
  dsimp only [compileGraph]
  rw [e,f]
  refine ⟨?_,rfl,g⟩
  rw [wireOrder,List.map_append,w]
  simp only [List.map_map]
  rfl

#print axioms forest_from_charged_parser
#print axioms raw_graph_exact
end J6R51Ingress
