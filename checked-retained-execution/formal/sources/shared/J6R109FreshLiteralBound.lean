import J6R109RawRosterRate
import J6R109FreshInputTime

namespace J6R109FreshLiteralBound
open scoped Classical
open Std.Sat AOracleMachineTime A1R10
open J6R49RootIngress J6R51Ingress J6R54PublicFamily J6R50RootIngress J7R9Subdivision J7R10Plant
open J6R109RawRosterRate J6R109PhysicalFrame J6R109FreshInputTime
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxRecDepth 5200
set_option maxHeartbeats 20000000

def freshLiteralRoof (h d j r c w k rows vars physical : ℕ) : ℕ :=
  let R := rows+vars
  let N := R*(k+2)
  let A := vars+1
  rawRosterClock h d j w k rows vars+
    physicalFrameRoof r c d (N+A*N) (h+d+w+1+j) (R+A*(N+1)) (N+A*(3*N))+
    (16+4*r+4*c)*physical+12

noncomputable section
variable {V : Type} [DecidableEq V] [Fintype V] (F : CNF V) (order : DeclaredOrder V)
variable {h d j r c e : ℕ}

theorem actual_fresh_literal_has_a_closed_input_cost
    (g : SerialGuards F order h d j r c e)
    (code : V → List Bool) (inj : Function.Injective code)
    (declared : List (List Bool)) (body : BitsCNF)
    (declaredExact : declared=order.roster.map code) (bodyExact : body=codeCNF code F)
    (w k : ℕ) (width : ∀ x, (code x).length=w)
    (clause : ∀ row∈F,row.length≤k) :
    let fresh := actualFreshSerialization F order g code inj declared body declaredExact bodyExact
    (materializeLiteral fresh).steps≤freshLiteralRoof h d j r c w k F.length order.roster.length
      (nWires (guardedInOrder F order.roster)) := by
  let G := compilePortRoster (h:=h) (d:=d) (j:=j) declared body
  let R := body.length+declared.length
  let N := R*(k+2)
  let A := declared.length+1
  have dl : declared.length=order.roster.length := by rw [declaredExact,List.length_map]
  have bl : body.length=F.length := by rw [bodyExact,codeCNF,List.length_map]
  have names : ∀ x∈declared,x.length=w := by
    intro x hx
    rw [declaredExact] at hx
    obtain ⟨u,_,rfl⟩ := List.mem_map.mp hx
    exact width u
  have rows : ∀ row∈body,row.length≤k := by
    intro row hr
    rw [bodyExact,codeCNF] at hr
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hr
    rw [List.length_map]
    exact clause c hc
  have words : ∀ row∈body,∀ z∈row,z.1.length=w := by
    intro row hr z hz
    rw [bodyExact,codeCNF] at hr
    obtain ⟨c,_,rfl⟩ := List.mem_map.mp hr
    obtain ⟨lit,_,rfl⟩ := List.mem_map.mp hz
    exact width lit.1
  have roster := true_roster_cost_and_dimensions_from_original_cnf (h:=h) (d:=d) (j:=j)
    declared body w k names rows words
  have wire : G.result.wires.length≤N+A*N := roster.2.1
  have row : G.result.rows.length≤R+A*(N+1) := roster.2.2.1
  have leg : G.result.rows.flatten.length≤N+A*(3*N) := roster.2.2.2.1
  have format := actual_physical_frame_has_explicit_polynomial_cost (r:=r) (c:=c)
    G.result (h+d+w+1+j) roster.2.2.2.2
  have cost : (buildPhysicalFrame (r:=r) (c:=c) G.result).steps≤
      physicalFrameRoof r c d (N+A*N) (h+d+w+1+j) (R+A*(N+1)) (N+A*(3*N)) := by
    refine format.trans ?_
    unfold physicalFrameRoof rosterRankRoof rowRankRoof tapeFee halfSeekRoof
    gcongr
  have raw : G.steps≤rawRosterClock h d j w k body.length declared.length := roster.1
  refine (genuine_literal_preparation_has_the_actual_roster_and_frame_debits
    F order g code inj declared body declaredExact bodyExact).trans ?_
  change G.steps+(buildPhysicalFrame (r:=r) (c:=c) G.result).steps+
    (16+4*r+4*c)*nWires (guardedInOrder F order.roster)+12≤_
  rw [←dl,←bl]
  unfold freshLiteralRoof
  change _≤rawRosterClock h d j w k body.length declared.length+
    physicalFrameRoof r c d (N+A*N) (h+d+w+1+j) (R+A*(N+1)) (N+A*(3*N))+
    (16+4*r+4*c)*nWires (guardedInOrder F order.roster)+12
  omega

#print axioms actual_fresh_literal_has_a_closed_input_cost
end
end J6R109FreshLiteralBound
