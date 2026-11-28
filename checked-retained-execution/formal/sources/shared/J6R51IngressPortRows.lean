import J6R51IngressRawGraph
import J6R51IngressRootLayout

/-! Recover the whole raw gate roster in the actual selected fresh
old-row order. Crucially the clause prefix is parsed *with brackets*,
so even zero-degree clause rows are real visitors. No position atlas,
endpoint words, sign table, or archived byte equality is an input. -/
namespace J6R51Ingress
open scoped Classical
open Std.Sat A1R10 AOracleMachineTime J6R49RootIngress J6R50RootIngress
open J7R9Compiler J7R9Subdivision J6R30GeneratedRootLayout
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 13500000
set_option maxRecDepth 2700

structure PortSeed (h d j : ℕ) where
  key : WireKey h d j
  side : Bool
  flag : OldFlag

def literalSeed {h d j : ℕ} (o : OccToken h d) : PortSeed h d j :=
  ⟨keyOfToken o,false,.literal o.sign⟩

def equalitySeed {h d j : ℕ} (o : WireKey h d j×Bool) : PortSeed h d j :=
  ⟨o.1,o.2,.equal⟩

def groupedClauseSeeds {h d j : ℕ} (rows : BitsCNF) :
    Meter (List (List (PortSeed h d j))) :=
  let H := indexTape h rows.length
  let P := parseRows (d:=d) rows H.result
  ⟨P.result.map (List.map literalSeed),
    H.steps+P.steps+7+P.result.length*5+P.result.flatten.length*(12+4*(h+d))⟩

structure PortRoster (h d j : ℕ) where
  wires : List (WireKey h d j)
  rows : List (List (PortSeed h d j))

def compilePortRoster {h d j : ℕ} (decl : List (List Bool)) (raw : BitsCNF) :
    Meter (PortRoster h d j) :=
  let guarded := guardedMeter decl raw
  let clauses := groupedClauseSeeds (h:=h) (d:=d) (j:=j) guarded.result
  let graph := compileGraph (h:=h) (d:=d) (j:=j) decl raw
  let equalities := graph.result.equality.map (List.map equalitySeed)
  ⟨⟨graph.result.edges,clauses.result++equalities⟩,
    guarded.steps+clauses.steps+graph.steps+11+5*equalities.length+
      (equalities.flatten.length)*(16+4*(h+d+j))⟩

section MathematicalSpecs
noncomputable section

variable {V : Type*} [DecidableEq V] (H : CNF V)
variable {h d j : ℕ} (code : V→List Bool)

def seatOf (p : OrderedPort H) : PortSeed h d j :=
  let edge := rowHalf H p
  ⟨keyOf H code edge.1,edge.2,flagAt (orderedGate H p.1) p.2⟩

def rowSeeds (v : OrderedOld H) : List (PortSeed h d j) :=
  List.ofFn (fun p : Fin (orderedDegree H v) => seatOf H code ⟨v,p⟩)

theorem grouped_clause_seeds_exact (hh : 0<h) (hd : 0<d)
    (fitH : H.length≤2^h) (fitD : ∀ row∈H,row.length≤2^d) :
    (groupedClauseSeeds (h:=h) (d:=d) (j:=j) (codeCNF code H)).result=
      (List.finRange H.length).map (fun i : ClauseIndex H => rowSeeds H code (.inl i)) := by
  have E := (index_tape_exact h H.length hh fitH).1
  have sources : codeCNF code H=List.ofFn (List.map (codeLit code) ∘ H.get) := by
    rw [←List.map_ofFn,List.ofFn_get]
    rfl
  have exactRows := parse_rows_map_ofFn (h:=h) (d:=d) H.length
    (List.map (codeLit code) ∘ H.get) (fun i=>wordAt h i.val)
    (fun i=>List.ofFn (fun k : Fin (H.get i).length=>guardToken H code ⟨i,k⟩))
    (fun i=>parse_clause_exact (H.get i) code _ hd (fitD _ (List.get_mem _ i)))
  dsimp only [groupedClauseSeeds]
  simp only [codeCNF,List.length_map,E]
  change (parseRows (d:=d) (codeCNF code H) _).result.map (List.map literalSeed)=_
  rw [sources,exactRows]
  have D : List.finRange H.length=List.ofFn (fun i : ClauseIndex H=>i) := by
    apply List.ext_getElem
    · simp
    · intro i hi₁ hi₂
      apply Fin.ext
      simp
  rw [D]
  simp only [List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  simp only [Function.comp_apply,rowSeeds,List.map_ofFn]
  rfl

theorem equal_row_seeds_exact (v : V) (k : Fin (orderedVar H v).length) :
    (((orderedVar H v).get k).map (halfKey H code)).map equalitySeed=
      (rowSeeds H code (.inr ⟨v,k⟩) : List (PortSeed h d j)) := by
  simp only [List.map_map,rowSeeds]
  change _=List.ofFn ((equalitySeed ∘ halfKey H code) ∘ ((orderedVar H v).get k).get)
  rw [←List.map_ofFn,List.ofFn_get]

theorem equal_forest_seeds_exact (vs : List V) :
    (((vs.flatMap (orderedVar H)).map (List.map (halfKey H code))).map
      (List.map equalitySeed) : List (List (PortSeed h d j)))=
      (vs.flatMap (fun v=>List.ofFn (fun k : Fin (orderedVar H v).length=>
        (Sum.inr ⟨v,k⟩ : OrderedOld H)))).map (rowSeeds H code) := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp only [List.flatMap_cons,List.map_append,ih]
    congr 1
    have orig :
        orderedVar H v=List.ofFn (fun k : Fin (orderedVar H v).length=>(orderedVar H v).get k) :=
      (List.ofFn_get _).symm
    conv_lhs => rw [orig]
    simp only [List.map_ofFn]
    apply congrArg List.ofFn
    funext k
    exact equal_row_seeds_exact H code v k

theorem actual_raw_port_roster {V : Type} [DecidableEq V] [Fintype V] {h d j : ℕ}
    (F : CNF V) (s : DeclaredOrder V) (code : V→List Bool) (inj : Function.Injective code)
    (hh : 0<h) (hd : 0<d) (hj : 0<j)
    (fitH : (guardedInOrder F s.roster).length≤2^h)
    (fitD : ∀ row∈guardedInOrder F s.roster,row.length≤2^d)
    (fitJ : ∀ v,(occurrences (guardedInOrder F s.roster) v).length-3≤2^j) :
    let H := guardedInOrder F s.roster
    let P := compilePortRoster (h:=h) (d:=d) (j:=j) (s.roster.map code) (codeCNF code F)
    P.result.wires=(wireOrder H (guardRoster s)).map (keyOf H (guardCode code)) ∧
      P.result.rows=(oldRoster H (guardRoster s)).map (rowSeeds H (guardCode code)) := by
  let H := guardedInOrder F s.roster
  let C := guardCode code
  obtain ⟨w,_,g⟩ := raw_graph_exact F s code inj hh hd hj fitH fitD fitJ
  have c := grouped_clause_seeds_exact (d:=d) (j:=j) H C hh hd fitH fitD
  have r := equal_forest_seeds_exact (h:=h) (d:=d) (j:=j) H C (guardRoster s).roster
  dsimp only [compilePortRoster]
  rw [paid_guard_in_order F s.roster code inj,w,g,c,r,oldRoster,List.map_append,List.map_map]
  exact ⟨rfl,rfl⟩

#print axioms grouped_clause_seeds_exact
#print axioms equal_row_seeds_exact
#print axioms equal_forest_seeds_exact
#print axioms actual_raw_port_roster
end
end MathematicalSpecs
end J6R51Ingress
