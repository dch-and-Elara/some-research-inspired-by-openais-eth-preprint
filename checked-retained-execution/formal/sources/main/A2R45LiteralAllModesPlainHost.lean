
import J7R10Plant
import J6R12RepackBoolean
import J6R11BlueprintNetwork

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5500000
set_option maxRecDepth 2050
set_option linter.unusedSectionVars false

/-! The literal sparse-clause branch uses the original unguarded
subdivision chart, not the J6 planted copies or repaired padding.
A Plant already contains the exact old and subdivision incidence charts. -/
namespace A2R45Literal
open scoped Classical Polynomial BigOperators
open Polynomial J6OrientedHost J6OrientedHostEval J6RecursivePortCube
open J6R10Repack J6R11Blueprint J6R11Repack J6R9Recursive J6R12Repack

noncomputable section
variable {V : Type} {m q : ℕ} (T : Plant V m q)

def plainNetwork : Network (Fin m) V (Fin q) where
  row e := (T.rowPort.symm e).1
  col e := (T.colPort.symm e).1

def plainRowPort (v : V) (j : Fin (T.degree v)) :
    ParentPorts (plainNetwork T) (.inl v) :=
  ⟨.inl (T.rowPort ⟨v,j⟩),
    congrArg (fun p : Σ u : V,Fin (T.degree u) => Sum.inl p.1) (T.rowPort.symm_apply_apply ⟨v,j⟩)⟩

def plainColumnPort (v : Fin q) (j : Bool) :
    ParentPorts (plainNetwork T) (.inr v) :=
  ⟨.inr (T.colPort (v,j)),
    congrArg (fun p : Fin q×Bool=>Sum.inr p.1) (T.colPort.symm_apply_apply (v,j))⟩

def plainFlag : ∀ v : V⊕Fin q,(ParentPorts (plainNetwork T) v→Bool)→Bool
  | .inl v,x=>(T.old v).eval (x ∘ plainRowPort T v)
  | .inr v,x=>decide (x (plainColumnPort T v false)=x (plainColumnPort T v true))

def plainFile (f : ℤ[X]) (p : ℕ) : EntryFile f 1 (plainNetwork T) :=
  fun v=>⟨p,fun x=>if plainFlag T v x then 1 else 0⟩

theorem plain_actual_row (x : Fin m→Bool) (v : V) :
    plainFlag T (.inl v) (assignment (plainNetwork T) x (.inl v)) =
      (T.old v).eval (fun j=>x (T.rowPort ⟨v,j⟩)) := rfl

theorem plain_actual_column (x : Fin m→Bool) (v : Fin q) :
    plainFlag T (.inr v) (assignment (plainNetwork T) x (.inr v)) =
      decide (x (T.colPort (v,false))=x (T.colPort (v,true))) := rfl

theorem plain_actual_row_size (v : V) :
    Nat.card {e : Fin m//(plainNetwork T).row e=v}=T.degree v := by
  exact (Nat.card_congr (chartFiber T.rowPort v).symm).trans (Nat.card_fin _)

theorem plain_actual_column_size (v : Fin q) :
    Nat.card {e : Fin m//(plainNetwork T).col e=v}=2 := by
  let e := Equiv.sigmaEquivProd (Fin q) Bool
  let c := e.trans T.colPort
  exact (Nat.card_congr (chartFiber c v).symm).trans
    (by rw [Nat.card_eq_fintype_card,Fintype.card_bool])

private theorem bool_product {I K : Type*} [Fintype I] [CommRing K] (f : I→Bool) :
    (∏ i,if f i then (1:K) else 0)=if ∀ i,f i=true then 1 else 0 := by
  by_cases h : ∀ i,f i=true
  · rw [if_pos h]
    exact Finset.prod_eq_one (fun i _=>if_pos (h i))
  · rw [if_neg h]
    obtain ⟨i,hi⟩ := not_forall.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

variable [Fintype V]

def plainHost (f : ℤ[X]) (p : ℕ) : PhysicalHost f 1 :=
  physicalHost (plainNetwork T) (plainFile T f p)

theorem plain_contract_card (f : ℤ[X]) (p : ℕ) (hp : 0<p)
    (hf : f.Monic) (hF : 0<f.natDegree) :
    (plainHost T f p).contract hf =
      (Nat.card {x : Fin m→Bool // coreA T x=true ∧ coreB T x=true}:IntRing f 1) := by
  have localBinary (x : Fin m→Bool) (v : V⊕Fin q) :
      ((plainFile T f p) v).frozen hf (assignment (plainNetwork T) x v) =
        if plainFlag T v (assignment (plainNetwork T) x v) then (1:IntRing f 1) else 0 :=
    canonical_lift_bool p hp f hf hF 1 (by decide) _
  have factors (x : Fin m→Bool) :
      (∏ v : V⊕Fin q,((plainFile T f p) v).frozen hf (assignment (plainNetwork T) x v)) =
        if coreA T x=true ∧ coreB T x=true then (1:IntRing f 1) else 0 := by
    simp_rw [localBinary]
    rw [Fintype.prod_sum_type]
    simp only [plain_actual_row,plain_actual_column,bool_product]
    unfold coreA coreB good
    simp only [decide_eq_true_eq]
    split <;> split <;> simp_all
  unfold plainHost physicalHost PhysicalHost.contract
  classical
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype,Finset.card_filter,Nat.cast_sum]
  apply Finset.sum_congr (by ext x; simp only [Finset.mem_univ])
  intro x _
  rw [show (∏ v : V⊕Fin q,
      ((plainFile T f p) v).frozen hf (assignment (plainNetwork T) x v))=_ from factors x]
  split <;> simp_all

#print axioms plain_actual_row
#print axioms plain_actual_column
#print axioms plain_actual_row_size
#print axioms plain_actual_column_size
#print axioms plain_contract_card
end
end A2R45Literal
