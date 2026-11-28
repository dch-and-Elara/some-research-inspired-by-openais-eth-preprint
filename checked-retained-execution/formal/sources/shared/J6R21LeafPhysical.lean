
import J6R21LeafMachine
import J6R11BlueprintNetwork
import J6R18ChildWriteHost

/-! The finite tree sums the real physical entry file on the exact edge
ordering of a reached Call. Input readers remain explicit and individually
metered; this module never supplies a completed value as a callback. -/
namespace J6R21Leaf
open scoped BigOperators Polynomial Classical
open Polynomial AOracleMachineTime AOracleCoordinates A1R10 A1R11 A1R12
open J6ActiveRun J6R9Recursive J6R10Repack J6R11Blueprint
set_option linter.unusedSectionVars false
set_option maxHeartbeats 5500000

variable {p ell : ℕ} {fw : List (A1R10.Word p)}

/-- The coefficient-list modulus is verified before product/readout. -/
noncomputable def literalChart {F H : (ZMod (2^p))[X]} (h : F=H) :
    Truncated F ell →+* Truncated H ell := h ▸ RingHom.id _

theorem literalChart_is_cast {F H : (ZMod (2^p))[X]} (h : F=H)
    (x : Truncated F ell) :
    literalChart h x=J6R18ChildWrite.castBox h x := by cases h; rfl

def readProduct (hp : 0<p) (he : 0<fw.length) (hℓ : 0<ell) {V : Type}
    (nodes : List V) (query : V→List Bool→Meter (UVBlock fw ell))
    (bits : List Bool) : Meter (UVBlock fw ell) :=
  foldM hp he hℓ (fun v=>query v bits) nodes

def thisVertexBill {V : Type} (nodes : List V)
    (query : V→List Bool→Meter (UVBlock fw ell)) (bits : List Bool) : ℕ :=
  (nodes.map (fun v => (query v bits).steps)).sum

theorem readProduct_exact_and_billed (hp : 0<p) (he : 0<fw.length) (hℓ : 0<ell) {V : Type}
    (nodes : List V) (query : V→List Bool→Meter (UVBlock fw ell))
    (bits : List Bool) :
    let t := readProduct hp he hℓ nodes query bits
    let billed := thisVertexBill nodes query bits
    uvRead hp fw ell t.result=(nodes.map (fun v => uvRead hp fw ell (query v bits).result)).prod ∧
      billed≤t.steps ∧ t.steps≤billed+uvWidth fw.length ell p + nodes.length*(mulCap fw.length ell p+2) := by
  dsimp only
  induction nodes with
  | nil => simp [readProduct,foldM,thisVertexBill,oneM]
  | cons v vs ih =>
    let T := readProduct hp he hℓ vs query bits
    let q := query v bits
    let B := thisVertexBill vs query bits
    change
      uvRead hp fw ell (mulM hp q T).result=
        (uvRead hp fw ell q.result)*((vs.map (fun u=>uvRead hp fw ell (query u bits).result)).prod) ∧
      q.steps+B≤(mulM hp q T).steps ∧
        (mulM hp q T).steps≤(q.steps+B)+uvWidth fw.length ell p+
          (vs.length+1)*(mulCap fw.length ell p+2)
    obtain ⟨value,hlo,hhi⟩ := ih
    change B≤T.steps at hlo
    change T.steps≤B+uvWidth fw.length ell p+vs.length*(mulCap fw.length ell p+2) at hhi
    refine ⟨by rw [mulM_read,value],?_ ,?_⟩
    · exact (Nat.add_le_add_left hlo q.steps).trans (by simp [mulM]; omega)
    · have hb := mulM_cost hp q T
      rw [Nat.add_mul,one_mul]
      omega

def leafCompute (hp : 0<p) (he : 0<fw.length) (hℓ : 0<ell)
    (edges : ℕ) {V : Type} (nodes : List V)
    (query : V→List Bool→Meter (UVBlock fw ell)) : Meter (UVBlock fw ell) :=
  enumerate hp (readProduct hp he hℓ nodes query) edges []

noncomputable def leafEntryBill {V : Type} (edges : ℕ) (nodes : List V)
    (query : V→List Bool→Meter (UVBlock fw ell)) : ℕ :=
  ∑ bits : Fin edges→Bool, thisVertexBill nodes query (List.ofFn bits)

theorem leafCompute_bills_every_entry (hp : 0<p) (he : 0<fw.length) (hℓ : 0<ell)
    (edges : ℕ) {V : Type} (nodes : List V) (query : V→List Bool→Meter (UVBlock fw ell)) :
    let run := leafCompute hp he hℓ edges nodes query
    let billed := leafEntryBill edges nodes query
    billed≤run.steps ∧
      run.steps≤billed+2^edges*(uvWidth fw.length ell p+nodes.length*(mulCap fw.length ell p+2)
        +reverseFee edges)+(2^edges-1)*innerFee fw.length ell p hp := by
  dsimp only
  have H := enumerate_bills_callbacks hp (readProduct hp he hℓ nodes query) edges []
  dsimp only at H
  simp only [List.length_nil,Nat.zero_add] at H
  change callbackTotal (readProduct hp he hℓ nodes query) edges []≤
      (leafCompute hp he hℓ edges nodes query).steps ∧
      _≤callbackTotal (readProduct hp he hℓ nodes query) edges []+
        2^edges*reverseFee edges+(2^edges-1)*innerFee fw.length ell p hp at H
  rw [callback_at_complete_assignment] at H
  have lo : leafEntryBill edges nodes query≤
      ∑ x : Fin edges→Bool, (readProduct hp he hℓ nodes query (List.ofFn x)).steps :=
    Finset.sum_le_sum fun x _ => (readProduct_exact_and_billed hp he hℓ nodes query (List.ofFn x)).2.1
  have hi : (∑ x : Fin edges→Bool, (readProduct hp he hℓ nodes query (List.ofFn x)).steps) ≤
      leafEntryBill edges nodes query+2^edges*(uvWidth fw.length ell p+nodes.length*(mulCap fw.length ell p+2)) := by
    have h := Finset.sum_le_sum (s:=(Finset.univ : Finset (Fin edges→Bool))) (fun x _ =>
      (readProduct_exact_and_billed hp he hℓ nodes query (List.ofFn x)).2.2)
    have hN : Fintype.card (Fin edges→Bool) = 2^edges := by simp
    simpa only [leafEntryBill,add_assoc,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,
      hN,nsmul_eq_mul,Nat.mul_add,Nat.cast_id] using h
  refine ⟨lo.trans H.1,?_⟩
  unfold leafCompute
  rw [Nat.mul_add]
  omega

set_option maxHeartbeats 8000000 in
/-- The exact physical source leaf. Each retained or original table
reader is called once per complete assignment, never once per address
class with its repetitions silently dropped. -/
theorem actual_leaf_exact {f : ℤ[X]} (c : Call (PhysicalHost f ell)) (hp : 0<c.prec)
    {fw : List (A1R10.Word c.prec)} (he : 0<fw.length) (hℓ : 0<ell)
    (hPoly : Modulus c.prec hp fw=NativeProbeRing.liftPoly c.prec f) (hf : f.Monic)
    (edgeCount : c.host.edgeCount=c.edges)
    (nodes : List (c.host.Row⊕c.host.Col)) (hn : nodes.Nodup)
    (hall : ∀ v : c.host.Row⊕c.host.Col,v∈nodes)
    (query : (c.host.Row⊕c.host.Col)→List Bool→Meter (UVBlock fw ell))
    (hquery : ∀ (x : Fin c.edges→Bool) v,
      J6R18ChildWrite.castBox hPoly (uvRead hp fw ell (query v (List.ofFn x)).result)=
        (c.host.file v).read hf c.prec
          (assignment c.host.network (x∘c.host.edgeOrder c.edges edgeCount) v)) :
    J6R18ChildWrite.castBox hPoly (uvRead hp fw ell
      (leafCompute hp he hℓ c.edges nodes query).result) =
      reduce c.prec f ell (c.host.contract hf) := by
  classical
  letI := c.host.finiteRow
  letI := c.host.finiteCol
  let ι := literalChart (ell:=ell) hPoly
  have hSum := physicalEntries_sum hf c edgeCount
  rw [← literalChart_is_cast,← hSum,map_sum,leafCompute,enumerate_exact,J6ChildPlan.allBits_exact,map_sum]
  simp only [List.reverse_nil,List.nil_append]
  apply Finset.sum_congr rfl
  intro x _
  rw [(readProduct_exact_and_billed hp he hℓ nodes query (List.ofFn x)).1]
  rw [map_list_prod,List.map_map]
  have hx (v : c.host.Row⊕c.host.Col) :
      ι (uvRead hp fw ell (query v (List.ofFn x)).result) =
        (c.host.file v).read hf c.prec
          (assignment c.host.network (x∘c.host.edgeOrder c.edges edgeCount) v) := by
    rw [literalChart_is_cast]
    exact hquery x v
  simp only [Function.comp_def,physicalEntries,dif_pos edgeCount,map_list_prod,List.map_map]
  have eqset : nodes.toFinset=(Finset.univ : Finset (c.host.Row⊕c.host.Col)) :=
    Finset.ext (by intro v; simp [hall v])
  rw [← List.prod_toFinset _ hn,eqset,Finset.prod_map_toList]
  apply Finset.prod_congr rfl
  intro v _
  exact hx v

theorem leaf_callback_visit_count {V : Type} (edges : ℕ) (vertices : List V) :
    (∑ _ : Fin edges→Bool, vertices.length) = 2^edges*vertices.length := by
  simp [Finset.sum_const]

#print axioms literalChart
#print axioms literalChart_is_cast
#print axioms readProduct_exact_and_billed
#print axioms leafCompute_bills_every_entry
#print axioms actual_leaf_exact
#print axioms leaf_callback_visit_count
end J6R21Leaf
