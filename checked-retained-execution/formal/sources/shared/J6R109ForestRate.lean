import J6R109PhysicalFrame

namespace J6R109ForestRate
open AOracleMachineTime J6R51Ingress J6R50RootIngress J7R9DirectedTree
open J6R109PhysicalFrame
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxHeartbeats 12000000

theorem half_gates_count_le {A : Type*} (external : List (A×Bool)) (edges : List A) :
    (halfGates external edges).length≤edges.length+1 := by
  induction edges generalizing external with
  | nil => cases external <;> simp [halfGates]
  | cons x xs ih =>
    cases external with
    | nil => simp [halfGates]
    | cons a ys =>
      cases ys with
      | nil => simp [halfGates]
      | cons b ys =>
        have h := ih ((x,true)::ys)
        simp only [halfGates,List.length_cons]
        omega

theorem half_gates_legs_le {A : Type*} (external : List (A×Bool)) (edges : List A) :
    (halfGates external edges).flatten.length≤external.length+2*edges.length := by
  induction edges generalizing external with
  | nil => cases external <;> simp [halfGates]
  | cons x xs ih =>
    cases external with
    | nil => simp [halfGates]
    | cons a ys =>
      cases ys with
      | nil => simp [halfGates]
      | cons b ys =>
        have h := ih ((x,true)::ys)
        simp only [halfGates,List.flatten_cons,List.length_append,List.length_cons,List.length_nil]
        simp only [List.length_cons] at h
        omega

def treeRoof (h d j n word : ℕ) : ℕ :=
  2+n*(5*word+8)+tapeFee j n+18+n*(30+8*(h+d+word))+
    n*(44+12*(j+word))

theorem actual_compiled_tree_has_an_explicit_tariff {h d j : ℕ}
    (v : List Bool) (slots : List (OccToken h d)) :
    let T := compileTree (j:=j) v slots
    T.result.privateWires.length≤slots.length ∧
      T.result.gates.length≤slots.length+1 ∧
      T.result.gates.flatten.length≤3*slots.length ∧
      T.steps≤treeRoof h d j slots.length v.length := by
  let B := bucket v slots
  let C := indexTape j (B.result.length-3)
  let pr := C.result.map (WireKey.tree (h:=h) (d:=d) v)
  let ex := B.result.map (fun z=>((keyOfToken z : WireKey h d j),true))
  have bLen : B.result.length≤slots.length := by
    rw [show B.result=slots.filter _ from (bucket_exact v slots).1]
    exact List.length_filter_le _ _
  have c0 := actual_bit_index_tape_cost j (B.result.length-3)
  have pLen : pr.length≤slots.length := by
    dsimp only [pr]
    rw [List.length_map]
    rw [show C.result.length=B.result.length-3 from c0.1]
    omega
  have eLen : ex.length≤slots.length := by simpa only [ex,List.length_map] using bLen
  have gLen := half_gates_count_le ex pr
  have glen2 := half_gates_legs_le ex pr
  have bFee : B.steps≤2+slots.length*(5*v.length+8) := (bucket_exact v slots).2
  have cFee : C.steps≤tapeFee j slots.length := by
    refine c0.2.trans ?_
    unfold tapeFee
    gcongr
    omega
  change pr.length≤slots.length ∧ (halfGates ex pr).length≤slots.length+1 ∧
    (halfGates ex pr).flatten.length≤3*slots.length ∧
    B.steps+C.steps+18+B.result.length*(30+8*(h+d+v.length))+
      pr.length*(44+12*(j+v.length))≤_
  refine ⟨pLen,by omega,by omega,?_⟩
  unfold treeRoof
  gcongr

theorem actual_forest_scans_each_declared_name {h d j : ℕ}
    (slots : List (OccToken h d)) (names : List (List Bool)) (w : ℕ)
    (fit : ∀ v∈names,v.length≤w) :
    let F := compileForest (j:=j) slots names
    F.result.privateWires.length≤names.length*slots.length ∧
      F.result.gates.length≤names.length*(slots.length+1) ∧
      F.result.gates.flatten.length≤names.length*(3*slots.length) ∧
      F.steps≤2+names.length*(treeRoof h d j slots.length w+8+8*(2*slots.length+1)) := by
  induction names with
  | nil => simp [compileForest]
  | cons v vs ih =>
    let A := compileTree (j:=j) v slots
    let B := compileForest (j:=j) slots vs
    have a := actual_compiled_tree_has_an_explicit_tariff (j:=j) v slots
    have b := ih (fun name m=>fit name (List.mem_cons_of_mem _ m))
    have lens : v.length≤w := fit v List.mem_cons_self
    have aFee : A.steps≤treeRoof h d j slots.length w := by
      refine a.2.2.2.trans ?_
      unfold treeRoof
      gcongr
    change (A.result.privateWires++B.result.privateWires).length≤_ ∧
      (A.result.gates++B.result.gates).length≤_ ∧
      (A.result.gates++B.result.gates).flatten.length≤_ ∧
      A.steps+B.steps+8+8*(A.result.privateWires.length+A.result.gates.length)≤_
    change A.result.privateWires.length≤_ ∧ A.result.gates.length≤_ ∧
      A.result.gates.flatten.length≤_ ∧ A.steps≤_ at a
    change B.result.privateWires.length≤_ ∧ B.result.gates.length≤_ ∧
      B.result.gates.flatten.length≤_ ∧ B.steps≤_ at b
    simp only [List.length_cons,List.length_append,List.flatten_append,Nat.add_mul,Nat.one_mul]
    omega

#print axioms actual_compiled_tree_has_an_explicit_tariff
#print axioms actual_forest_scans_each_declared_name
end J6R109ForestRate
