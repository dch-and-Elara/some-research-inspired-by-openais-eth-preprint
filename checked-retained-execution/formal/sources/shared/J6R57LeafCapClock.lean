import J6R57LeafCapNumbers
import J6R21LeafEnvelope
import J6R21LeafClock

/-! The literal D.4.7 clocked DFS, including zero-edge leaves. The promised
input-entry cost is per actual ordered entry query, exactly as in D.1;
there is no assumed leaf bound, materialized assignment cube, or vertex
omission. Packet-entry costs must be obtained separately when used. -/
namespace J6R57LeafCap
open scoped Classical BigOperators
open A1R10 A1R11 A1R12 AOracleMachineTime J6R21Leaf J6R16ModeCost J1PPrinted
set_option autoImplicit false
set_option warningAsError true

def leafArithmeticScale (E L P H V U : ℕ) : ℕ :=
  V*(U+3432*dimEnvelope E L P+2)+429*dimEnvelope E L P+3*H+12

theorem actual_assignment_calls_pay_promised_entries {p ell : ℕ}
    {fw : List (A1R10.Word p)} {V : Type} (nodes : List V)
    (query : V→List Bool→Meter (UVBlock fw ell)) (m U : ℕ)
    (promised : ∀ v∈nodes, ∀ x : Fin m→Bool,(query v (List.ofFn x)).steps≤U) :
    leafEntryBill m nodes query≤2^m*(nodes.length*U) := by
  have one (x : Fin m→Bool) :
      thisVertexBill nodes query (List.ofFn x)≤nodes.length*U :=
    list_sum_cap nodes (fun v=>(query v (List.ofFn x)).steps) U (fun v hv=>promised v hv x)
  have sum := Finset.sum_le_sum (s:=(Finset.univ : Finset (Fin m→Bool))) (fun x _=>one x)
  have card : Fintype.card (Fin m→Bool)=2^m := by simp
  simpa only [leafEntryBill,Finset.sum_const,Finset.card_univ,card,nsmul_eq_mul] using sum

theorem actual_clocked_leaf_dimensional_tariff {p ell : ℕ} (hp : 0<p)
    {fw : List (A1R10.Word p)} (he : 0<fw.length) (hv : 0<ell)
    {V : Type} (nodes : List V) (query : V→List Bool→Meter (UVBlock fw ell))
    (clock : List Unit) {m E L P H Vmax U : ℕ} (exactClock : clock.length=m)
    (dE : fw.length≤E) (dL : ell≤L) (dP : p≤P) (dM : m≤H) (dV : nodes.length≤Vmax)
    (promised : ∀ v∈nodes, ∀ x : Fin m→Bool,(query v (List.ofFn x)).steps≤U) :
    (clockDFS hp (readProduct hp he hv nodes query) clock []).steps≤
      2^H*leafArithmeticScale E L P H Vmax U := by
  rw [clocked_leaf_is_native_enumerator hp he hv nodes query clock exactClock]
  have paid := actual_assignment_calls_pay_promised_entries nodes query m U promised
  have sum := (leafCompute_bills_every_entry hp he hv m nodes query).2
  have sub :=
    Nat.mul_le_mul_right (innerFee fw.length ell p hp) (Nat.sub_le ((2:ℕ)^m) 1)
  have locally : (leafCompute hp he hv m nodes query).steps≤
      callLeafFee fw.length ell p m nodes.length U hp := by
    unfold callLeafFee
    simp only [Nat.mul_add] at sum ⊢
    omega
  exact locally.trans (call_leaf_fee_uniform_dims hp dE dL dP dM dV (le_refl U))

theorem leaf_arithmetic_factor_with_entry_exponent (E L P H V B k : ℕ) :
    leafArithmeticScale E L P H V (B*2^k)≤leafArithmeticScale E L P H V B*2^k := by
  let d := dimEnvelope E L P
  let Pk := (2:ℕ)^k
  let a := 3432*d
  let b := 429*d+3*H+12
  have one : 0<Pk := by dsimp [Pk]; positivity
  change V*(B*Pk+a+2)+429*d+3*H+12≤(V*(B+a+2)+429*d+3*H+12)*Pk
  have hA := Nat.le_mul_of_pos_right a one
  have hB := Nat.le_mul_of_pos_right 2 one
  have hd := Nat.le_mul_of_pos_right (429*d) one
  have hh := Nat.le_mul_of_pos_right (3*H) one
  have hc := Nat.le_mul_of_pos_right 12 one
  calc
    _≤V*(B*Pk+a*Pk+2*Pk)+(429*d)*Pk+(3*H)*Pk+12*Pk :=
      Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
        (Nat.mul_le_mul_left V (Nat.add_le_add (Nat.add_le_add_left hA _) hB)) hd) hh) hc
    _=_ := by ring

theorem printed_leaf_evaluator_from_original_entry_contract {p ell : ℕ} (hp : 0<p)
    {fw : List (A1R10.Word p)} (he : 0<fw.length) (hv : 0<ell)
    {V : Type} (nodes : List V) (query : V→List Bool→Meter (UVBlock fw ell))
    (clock : List Unit) {m E L P Vmax : ℕ} (exactClock : clock.length=m)
    (s inputLen A b : ℕ) (large : 1024≤Nat.clog 2 s)
    (dE : fw.length≤E) (dL : ell≤L) (dP : p≤P)
    (dM : m≤J9PrintedSchedule.leafThreshold s (Nat.clog 2 s)) (dV : nodes.length≤Vmax)
    (entryContract : ∀ v∈nodes, ∀ x : Fin m→Bool,
      (query v (List.ofFn x)).steps≤(s+inputLen)^b*2^(A*sourceDelta s)) :
    let H := J9PrintedSchedule.leafThreshold s (Nat.clog 2 s)
    (clockDFS hp (readProduct hp he hv nodes query) clock []).steps≤
      leafArithmeticScale E L P H Vmax ((s+inputLen)^b)*2^((A+1)*H) := by
  let H := J9PrintedSchedule.leafThreshold s (Nat.clog 2 s)
  let base := (s+inputLen)^b
  have exp : A*sourceDelta s≤A*H := Nat.mul_le_mul_left _ (source_delta_le_actual_leaf_threshold s large)
  have fees (v : V) (hn : v∈nodes) (x : Fin m→Bool) :
      (query v (List.ofFn x)).steps≤base*2^(A*H) :=
    (entryContract v hn x).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) exp))
  have h := actual_clocked_leaf_dimensional_tariff hp he hv nodes query clock exactClock
    dE dL dP dM dV fees
  dsimp only
  refine h.trans ((Nat.mul_le_mul_left _ (leaf_arithmetic_factor_with_entry_exponent
    E L P H Vmax base (A*H))).trans ?_)
  rw [Nat.add_mul A 1 H,one_mul,pow_add]
  exact le_of_eq (by ring)

#print axioms leafArithmeticScale
#print axioms actual_assignment_calls_pay_promised_entries
#print axioms actual_clocked_leaf_dimensional_tariff
#print axioms leaf_arithmetic_factor_with_entry_exponent
#print axioms printed_leaf_evaluator_from_original_entry_contract
end J6R57LeafCap
