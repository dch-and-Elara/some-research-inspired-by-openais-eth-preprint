
import A2R45LiteralCodec
import J6R10RepackPrecision

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 10000000
set_option maxSynthPendingDepth 16
set_option linter.unusedSectionVars false

/-! The original fixed simulated A2 chart, with a real local table on each
true incidence fibre. No switch bit changes the network or its port list. -/
namespace A2R45Literal
open scoped Classical BigOperators Polynomial
open FixedHostAcquisition
open J6R10Repack

noncomputable section

def simulated (n : ℕ) : Network (Wire n) (Row n) (Column n) where
  row := Sigma.fst
  col := FixedHostAcquisition.owner

variable {n : ℕ}
local notation "N" => (simulated n)

def rowPortFibre (r : Row n) : WireAt r ≃ {e : Wire n // (N).row e=r} where
  toFun j := ⟨⟨r,j⟩,rfl⟩
  invFun e := e.property ▸ e.val.2
  left_inv _ := rfl
  right_inv := by
    intro e
    obtain ⟨⟨r',j⟩,h⟩ := e
    change r'=r at h
    subst r'
    rfl

def actualSimRowPort (r : Row n) : WireAt r ≃ ParentPorts N (.inl r) :=
  (rowPortFibre r).trans (rowPortsEquiv N r)

theorem actual_row_terminal (r : Row n) (j : WireAt r) :
    (actualSimRowPort r j).val=.inl ⟨r,j⟩ := rfl

theorem simulated_row_degrees (r : Row n) :
    Nat.card {e : Wire n // (N).row e=r}≤4 := by
  rw [←Nat.card_congr (rowPortFibre r),Nat.card_eq_fintype_card]
  exact fixed_row_degree r

theorem simulated_column_degrees (c : Column n) :
    Nat.card {e : Wire n // (N).col e=c}≤3 := by
  rw [Nat.card_eq_fintype_card]
  exact fixed_column_degree c

theorem simulated_size (n : ℕ) : Nat.card (Wire n×Bool)≤12*(n+1)^2 := by
  rw [Nat.card_eq_fintype_card]
  exact physical_wire_bound

def auxBitPort (c : Auxiliary n) : ParentPorts N (.inr (.inr c)) :=
  ⟨.inr (auxPort c),congrArg Sum.inr (owner_auxPort c)⟩

def simRowFlag (w : Input n) (r : Row n) (x : ParentPorts N (.inl r)→Bool) : Bool :=
  serializedRead w r (x ∘ actualSimRowPort r)

def simColFlag (c : Column n) (x : ParentPorts N (.inr c)→Bool) : Bool :=
  decide (∀ i j,x i=x j) && match c with
    | .inl _=>true
    | .inr k=>x (auxBitPort k)

theorem actual_sim_row_table {K : Type*} [CommRing K]
    (w : Input n) (r : Row n) (y : Wire n→Bool) :
    Acquisition.bit (K:=K) (simRowFlag w r (assignment N y (.inl r))) =
      rowTable w.enabled r (fun j=>y ⟨r,j⟩) := by
  exact serializedRead_truth w r (fun j=>y ⟨r,j⟩)

theorem occurrence_consistent_exact (c : Column n) (x : Wire n→Bool) :
    (∀ i j : ParentPorts N (.inr c), assignment N x (.inr c) i=assignment N x (.inr c) j) ↔
      ∀ i j : Wire n, FixedHostAcquisition.owner i=c →
        FixedHostAcquisition.owner j=c → x i=x j := by
  constructor
  · intro h i j hi hj
    exact h ⟨.inr i,congrArg Sum.inr hi⟩ ⟨.inr j,congrArg Sum.inr hj⟩
  · intro h i j
    obtain ⟨(i|i),hi⟩ := i
    · cases hi
    obtain ⟨(j|j),hj⟩ := j
    · cases hj
    exact h i j (Sum.inr.inj hi) (Sum.inr.inj hj)

private theorem bit_and {K : Type*} [CommRing K] (a b : Bool) :
    Acquisition.bit (K:=K) (a&&b)=Acquisition.bit a*Acquisition.bit b := by
  cases a <;> cases b <;> simp [Acquisition.bit]

theorem actual_sim_column_table {K : Type*} [CommRing K] (x : Wire n→Bool) :
    (∏ c : Column n,Acquisition.bit (K:=K) (simColFlag c (assignment N x (.inr c)))) =
      FixedHostAcquisition.columnTable x := by
  let v (c : Column n) : K := if ∀ i j : Wire n,
    FixedHostAcquisition.owner i=c → FixedHostAcquisition.owner j=c → x i=x j then 1 else 0
  let pin (c : Column n) : K := match c with
    | .inl _=>1
    | .inr k=>Acquisition.bit (x (auxPort k))
  have h (c : Column n) :
      Acquisition.bit (K:=K) (simColFlag c (assignment N x (.inr c)))=v c*pin c := by
    unfold simColFlag
    rw [bit_and]
    have ha :
        Acquisition.bit (K:=K) (decide (∀ i j : ParentPorts N (.inr c),
          assignment N x (.inr c) i=assignment N x (.inr c) j))=v c := by
      unfold Acquisition.bit v
      simp only [decide_eq_true_eq,occurrence_consistent_exact]
    rw [ha]
    cases c <;> rfl
  have pp : (∏ c : Column n,pin c)=auxPins (K:=K) (x ∘ auxPort) := by
    rw [Fintype.prod_sum_type]
    change (∏ _ : Occurrence n,(1:K)) * (∏ k : Auxiliary n,Acquisition.bit (x (auxPort k))) = _
    simp only [Finset.prod_const_one,one_mul,auxPins,Function.comp_apply]
  calc
    _ = (∏ c : Column n,v c) * (∏ c : Column n,pin c) := by
      simp_rw [h,Finset.prod_mul_distrib]
    _ = _ := by
      have hp : (∏ c : Column n,v c)=Acquisition.equalityTensor (K:=K) FixedHostAcquisition.owner x := by
        unfold Acquisition.equalityTensor
        apply Finset.prod_congr (by ext i; simp only [Finset.mem_univ])
        intro c _
        by_cases hc : ∀ (i j : Wire n),
          FixedHostAcquisition.owner i=c → FixedHostAcquisition.owner j=c → x i=x j
        · simp only [v,if_pos hc]
        · simp only [v,if_neg hc]
      rw [pp,hp,FixedHostAcquisition.columnTable]

#print axioms actual_row_terminal
#print axioms simulated_row_degrees
#print axioms simulated_column_degrees
#print axioms simulated_size
#print axioms actual_sim_row_table
#print axioms occurrence_consistent_exact
#print axioms actual_sim_column_table
end
end A2R45Literal
