import J6R109ForestRate
import J6R109GuardGeometry
import J6R109PhysicalFrameRate

namespace J6R109RawRosterRate
open AOracleMachineTime A1R10 J6R49RootIngress J6R51Ingress J6R50RootIngress
open J6R109PhysicalFrame J6R109ForestRate J6R109RawParserRate
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxRecDepth 5200
set_option maxHeartbeats 21000000

def parseSeedsClock (h d w k rows : ℕ) : ℕ :=
  tapeFee h rows+2+rows*(clauseParserRoof h d w k+5)+7+5*rows+rows*k*(12+4*(h+d))

theorem actual_clause_seed_collect_uses_real_parser {h d j : ℕ}
    (rows : BitsCNF) (width size : ℕ)
    (rowFits : ∀ row∈rows,row.length≤size)
    (namesFit : ∀ row∈rows,∀ lit∈row,lit.1.length≤width) :
    let P := groupedClauseSeeds (h:=h) (d:=d) (j:=j) rows
    P.result.length≤rows.length ∧ P.result.flatten.length≤rows.length*size ∧
      P.steps≤parseSeedsClock h d width size rows.length := by
  let K := indexTape h rows.length
  let R := parseRows (d:=d) rows K.result
  have a := actual_row_parser_visits_no_more_than_its_input (d:=d) rows K.result width size rowFits namesFit
  have p : (R.result.map (List.map (literalSeed (j:=j)))).flatten.length=R.result.flatten.length := by
    rw [←List.map_flatten,List.length_map]
  have fee : K.steps≤tapeFee h rows.length := (actual_bit_index_tape_cost _ _).2
  have l1 : R.result.length≤rows.length := a.1
  have l2 : R.result.flatten.length≤rows.length*size := a.2.1
  have cost : R.steps≤2+rows.length*(clauseParserRoof h d width size+5) := a.2.2
  change (R.result.map (List.map (literalSeed (j:=j)))).length≤_ ∧
    (R.result.map (List.map (literalSeed (j:=j)))).flatten.length≤_ ∧
    K.steps+R.steps+7+R.result.length*5+R.result.flatten.length*(12+4*(h+d))≤_
  rw [List.length_map,p]
  refine ⟨l1,l2,?_⟩
  unfold parseSeedsClock
  have rowwork := Nat.mul_le_mul_right 5 l1
  have legwork := Nat.mul_le_mul_right (12+4*(h+d)) l2
  omega

theorem actual_forest_tree_key_width {h d j : ℕ} (slots : List (OccToken h d))
    (names : List (List Bool)) (w : ℕ)
    (fits : ∀ name∈names,name.length≤w) :
    ∀ u∈(compileForest (j:=j) slots names).result.privateWires,keyWidth u≤w+j := by
  induction names with
  | nil => simp [compileForest]
  | cons name more ih =>
    intro u use
    change u∈(compileTree (j:=j) name slots).result.privateWires++
      (compileForest (j:=j) slots more).result.privateWires at use
    rcases List.mem_append.mp use with U|U
    · change u∈((indexTape j ((bucket name slots).result.length-3)).result.map (WireKey.tree name)) at U
      obtain ⟨idx,_,rfl⟩ := List.mem_map.mp U
      exact Nat.add_le_add_right (fits name List.mem_cons_self) _
    · exact ih (fun v vMem=>fits v (List.mem_cons_of_mem _ vMem)) u U

def rootedForestClock (h d j slots width names : ℕ) : ℕ :=
  2+names*(treeRoof h d j slots width+8+8*(2*slots+1))

def rawRosterClock (h d j w k rows vars : ℕ) : ℕ :=
  let R := rows+vars
  let N := R*(k+2)
  let A := vars+1
  2*fullIngressFee w k rows vars+parseSeedsClock h d (w+1) (k+2) R+
    guardParserRoof h d (w+1) (k+2) R+4+rootedForestClock h d j N (w+1) A+
    8+8*(vars+N)+11+5*(A*(N+1))+(A*(3*N))*(16+4*(h+d+j))

theorem true_roster_cost_and_dimensions_from_original_cnf {h d j : ℕ}
    (declares : List (List Bool)) (cnf : BitsCNF) (w k : ℕ)
    (chart : ∀ z∈declares,z.length=w)
    (size : ∀ row∈cnf,row.length≤k)
    (wordFits : ∀ row∈cnf,∀ z∈row,z.1.length=w) :
    let R := cnf.length+declares.length
    let N := R*(k+2)
    let A := declares.length+1
    let G := compilePortRoster (h:=h) (d:=d) (j:=j) declares cnf
    G.steps≤rawRosterClock h d j w k cnf.length declares.length ∧
    G.result.wires.length≤N+A*N ∧
    G.result.rows.length≤R+A*(N+1) ∧
    G.result.rows.flatten.length≤N+A*(3*N) ∧
    (∀ z∈G.result.wires,keyWidth z≤h+d+w+1+j) := by
  let G := guardedMeter declares cnf
  let R := cnf.length+declares.length
  let N := R*(k+2)
  let A := declares.length+1
  let names := [false]::declares.map (true::·)
  let P := parseGuard (h:=h) (d:=d) G.result
  let L := groupedClauseSeeds (h:=h) (d:=d) (j:=j) G.result
  let F := compileForest (j:=j) P.result names
  have nom : names.length=A := by simp [names,A]
  have width : ∀ name∈names,name.length≤w+1 := by
    intro name hm
    simp only [names,List.mem_cons] at hm
    rcases hm with e|v
    · rw [e]; simp
    · obtain ⟨x,hx,rfl⟩ := List.mem_map.mp v
      simp [chart x hx]
  have guard := guarded_geometry_is_from_declared_input declares cnf w k chart size wordFits
  have r0 : G.result.length≤R := guard.1
  have gFee : G.steps≤fullIngressFee w k cnf.length declares.length :=
    paid_guard_source_cost declares cnf w k chart size wordFits
  have pars := actual_guarded_parser_bit_time (h:=h) (d:=d) G.result (w+1) (k+2) guard.2.1 guard.2.2
  have pLen : P.result.length≤N := pars.1.trans (Nat.mul_le_mul_right _ r0)
  have pFee : P.steps≤guardParserRoof h d (w+1) (k+2) R := by
    refine pars.2.trans ?_
    unfold guardParserRoof tapeFee
    gcongr
  have leads := actual_clause_seed_collect_uses_real_parser (h:=h) (d:=d) (j:=j) G.result (w+1) (k+2)
    guard.2.1 guard.2.2
  have clLen : L.result.length≤R := leads.1.trans r0
  have clLeg : L.result.flatten.length≤N := leads.2.1.trans (Nat.mul_le_mul_right _ r0)
  have clFee : L.steps≤parseSeedsClock h d (w+1) (k+2) R := by
    refine leads.2.2.trans ?_
    unfold parseSeedsClock tapeFee
    gcongr
  have forest := actual_forest_scans_each_declared_name (j:=j) P.result names (w+1) width
  have fw : F.result.privateWires.length≤A*N :=
    forest.1.trans (by rw [nom];gcongr)
  have fg : F.result.gates.length≤A*(N+1) :=
    forest.2.1.trans (by rw [nom]; gcongr)
  have fl : F.result.gates.flatten.length≤A*(3*N) :=
    forest.2.2.1.trans (by rw [nom]; gcongr)
  have fFee : F.steps≤rootedForestClock h d j N (w+1) A := by
    refine forest.2.2.2.trans ?_
    unfold rootedForestClock treeRoof tapeFee
    rw [nom]
    gcongr
  let leaves := F.result.gates.map (List.map equalitySeed)
  have gLen : leaves.length=F.result.gates.length := by simp [leaves]
  have legLen : leaves.flatten.length=F.result.gates.flatten.length := by
    unfold leaves
    rw [←List.map_flatten,List.length_map]
  change (G.steps+L.steps+(G.steps+P.steps+4+F.steps+8+8*(declares.length+P.result.length))+
     11+5*leaves.length+leaves.flatten.length*(16+4*(h+d+j)))≤_ ∧
     ((P.result.map keyOfToken)++F.result.privateWires).length≤_ ∧
     (L.result++leaves).length≤_ ∧ (L.result++leaves).flatten.length≤_ ∧
     (∀ z∈(P.result.map keyOfToken)++F.result.privateWires,keyWidth z≤_)
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [gLen,legLen]
    unfold rawRosterClock
    change _≤2*fullIngressFee w k cnf.length declares.length+
      parseSeedsClock h d (w+1) (k+2) R+guardParserRoof h d (w+1) (k+2) R+4+
      rootedForestClock h d j N (w+1) A+8+8*(declares.length+N)+11+
      5*(A*(N+1))+(A*(3*N))*(16+4*(h+d+j))
    have head := Nat.mul_le_mul_left 5 fg
    have tail := Nat.mul_le_mul_right (16+4*(h+d+j)) fl
    omega
  · rw [List.length_append,List.length_map]
    exact Nat.add_le_add pLen fw
  · rw [List.length_append,gLen]
    exact Nat.add_le_add clLen fg
  · rw [List.flatten_append,List.length_append,legLen]
    exact Nat.add_le_add clLeg fl
  · intro z hz
    rcases List.mem_append.mp hz with H|H
    · obtain ⟨u,_,rfl⟩ := List.mem_map.mp H
      change h+d≤_
      omega
    · have q := actual_forest_tree_key_width P.result names (w+1) width z H
      omega

#print axioms actual_clause_seed_collect_uses_real_parser
#print axioms true_roster_cost_and_dimensions_from_original_cnf
end J6R109RawRosterRate
