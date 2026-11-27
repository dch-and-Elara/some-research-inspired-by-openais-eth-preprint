import P3BareissBitCells

open scoped BigOperators

namespace Paper3.BareissBit

open Reconstruction.BareissSolver Reconstruction.BareissPaper
open AffineCost.Bit (Run)

theorem valid_left {B : ℕ} {os ps : List ScalarOp} (h : ValidTrace B (os ++ ps)) :
    ValidTrace B os := fun op hop => h op (List.mem_append.mpr (Or.inl hop))

theorem valid_right {B : ℕ} {os ps : List ScalarOp} (h : ValidTrace B (os ++ ps)) :
    ValidTrace B ps := fun op hop => h op (List.mem_append.mpr (Or.inr hop))

def scanTrace {α : Type} (read : α → ℤ) (xs : List α) : List ScalarOp :=
  (scanNonzero read xs).tested.map fun a => .testZero (read a)

/-- Look up each tested candidate once; the bit test actually decides whether
to continue. The returned prefix is defined by this run, not supplied. -/
def paidScan {α : Type} (B nav : ℕ) (read : α → ℤ) : List α → Run (Scan α)
  | [] => ⟨⟨none, []⟩, nav⟩
  | a :: xs =>
    let h := paidZero B (read a)
    if h.value then
      let tail := paidScan B nav read xs
      ⟨⟨tail.value.found, a :: tail.value.tested⟩, nav + h.steps + tail.steps⟩
    else ⟨⟨some a, [a]⟩, nav + h.steps⟩

theorem paidScan_correct {α : Type} (B nav : ℕ) (read : α → ℤ) (xs : List α)
    (hcert : ValidTrace B (scanTrace read xs)) :
    (paidScan B nav read xs).value = scanNonzero read xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    have hfirst : Decodes B (.testZero (read a)) := hcert _ (by
      by_cases h : read a = 0 <;> simp [scanTrace,scanNonzero,h])
    have hpaid := paidZero_correct hfirst
    rw [paidScan,hpaid]
    by_cases h : read a = 0
    · have htail : ValidTrace B (scanTrace read xs) := by
        intro op hop
        apply hcert
        rw [scanTrace,scanNonzero,if_pos h,List.map_cons]
        exact List.mem_cons_of_mem _ hop
      simp [scanNonzero,h,ih htail]
    · simp [scanNonzero,h]

theorem paidScan_price {α : Type} (B nav : ℕ) (read : α → ℤ) (xs : List α) :
    (paidScan B nav read xs).steps ≤ (xs.length+1)*(cellPrice B+nav) := by
  induction xs with
  | nil => simp [paidScan]
  | cons a xs ih =>
    have hp := paidZero_price B (read a)
    simp only [paidScan,List.length_cons]
    rw [Nat.add_mul,Nat.one_mul]
    split <;> dsimp only <;> omega

def paidForwardCell {m n : ℕ} (B nav : ℕ)
    (M : IntegerAugment (m+1) (n+1)) (d : ℤ)
    (i : Fin (m+1)) (j : Fin (n+1)) (u : Fin m) (v : Option (Fin n)) : Run ℤ :=
  let p := M i (some j)
  let a := M (i.succAbove u) (v.map j.succAbove)
  let c := M (i.succAbove u) (some j)
  let r := M i (v.map j.succAbove)
  let x := paidInt B (.mul p a)
  let y := paidInt B (.mul c r)
  let z := paidInt B (.sub x.value y.value)
  let out := paidInt B (.exactDiv z.value d)
  ⟨out.value,nav+x.steps+y.steps+z.steps+out.steps⟩

theorem paidForwardCell_correct {m n : ℕ} (B nav : ℕ)
    (M : IntegerAugment (m+1) (n+1)) (d : ℤ)
    (i : Fin (m+1)) (j : Fin (n+1)) (u : Fin m) (v : Option (Fin n))
    (h : ValidTrace B (forwardCellTrace M d i j u v)) :
    (paidForwardCell B nav M d i j u v).value = forwardDividend M i j u v / d := by
  let p := M i (some j)
  let a := M (i.succAbove u) (v.map j.succAbove)
  let c := M (i.succAbove u) (some j)
  let r := M i (v.map j.succAbove)
  have he : forwardDividend M i j u v = p*a-c*r := rfl
  have h₁ : Decodes B (.mul p a) := h _ (by simp [forwardCellTrace,p,a])
  have h₂ : Decodes B (.mul c r) := h _ (by simp [forwardCellTrace,c,r])
  have h₃ : Decodes B (.sub (p*a) (c*r)) := h _ (by simp [forwardCellTrace,p,a,c,r])
  have h₄ : Decodes B (.exactDiv (forwardDividend M i j u v) d) :=
    h _ (by simp [forwardCellTrace])
  change (paidInt B (.exactDiv (paidInt B (.sub (paidInt B (.mul p a)).value
    (paidInt B (.mul c r)).value)).value d)).value = _
  rw [paidInt_correct h₁ rfl, paidInt_correct h₂ rfl, paidInt_correct h₃ rfl, ← he]
  exact paidInt_correct h₄ rfl

theorem paidForwardCell_price {m n : ℕ} (B nav : ℕ)
    (M : IntegerAugment (m+1) (n+1)) (d : ℤ)
    (i : Fin (m+1)) (j : Fin (n+1)) (u : Fin m) (v : Option (Fin n)) :
    (paidForwardCell B nav M d i j u v).steps ≤ nav+4*cellPrice B := by
  dsimp only [paidForwardCell]
  exact (Nat.add_le_add
    (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add_left (paidInt_price _ _) _)
      (paidInt_price _ _)) (paidInt_price _ _)) (paidInt_price _ _)).trans (by omega)

def onDenseTable {m n : ℕ} (F : Fin m → Option (Fin n) → Run ℤ) (init : ℕ) :
    Run (IntegerAugment m n) :=
  let A := Vector.ofFn fun i : Fin m => Vector.ofFn fun j : Fin (n+1) => F i (columnSlot j)
  ⟨Matrix.of (fun i j => (A[i.val][(j.elim (0 : Fin (n+1)) Fin.succ).val]).value),
    init + ∑ i : Fin m, ∑ j : Fin (n+1), A[i.val][j.val].steps⟩

@[simp] theorem onDenseTable_value {m n : ℕ} (F : Fin m → Option (Fin n) → Run ℤ) (init : ℕ)
    (i : Fin m) (j : Option (Fin n)) : (onDenseTable F init).value i j = (F i j).value := by
  cases j <;> simp [onDenseTable, columnSlot]

theorem onDenseTable_price {m n : ℕ} (F : Fin m → Option (Fin n) → Run ℤ) (init cap : ℕ)
    (h : ∀ i j, (F i j).steps ≤ cap) :
    (onDenseTable F init).steps ≤ init + m*(n+1)*cap := by
  simp only [onDenseTable, Vector.getElem_ofFn]
  apply Nat.add_le_add_left
  calc
    _ ≤ ∑ _i : Fin m, ∑ _j : Fin (n+1), cap :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h i (columnSlot j)
    _ = _ := by simp [Nat.mul_assoc]

def paidForward {m n : ℕ} (B nav : ℕ)
    (M : IntegerAugment (m+1) (n+1)) (d : ℤ) (i : Fin (m+1)) (j : Fin (n+1)) :
    Run (IntegerAugment m n) :=
  onDenseTable (paidForwardCell B nav M d i j) nav

theorem paidForward_correct {m n : ℕ} (B nav : ℕ)
    (M : IntegerAugment (m+1) (n+1)) (d : ℤ) (i : Fin (m+1)) (j : Fin (n+1))
    (h : ValidTrace B (forwardTrace M d i j)) :
    (paidForward B nav M d i j).value = forwardStep M d i j := by
  ext u v
  have hcv : v ∈ columns n := by cases v <;> simp [columns]
  have hf : ValidTrace B (forwardCellTrace M d i j u v) := fun op ho =>
    h op (List.mem_flatMap.mpr ⟨u, by simp, List.mem_flatMap.mpr ⟨v,hcv,ho⟩⟩)
  simp only [paidForward, onDenseTable_value, forwardStep, denseAugment_apply, Matrix.of_apply]
  exact paidForwardCell_correct B nav M d i j u v hf

theorem paidForward_price {m n : ℕ} (B nav : ℕ)
    (M : IntegerAugment (m+1) (n+1)) (d : ℤ) (i : Fin (m+1)) (j : Fin (n+1)) :
    (paidForward B nav M d i j).steps ≤ (4*m*(n+1)+1)*(cellPrice B+nav) := by
  have h := onDenseTable_price (paidForwardCell B nav M d i j) nav
    (nav+4*cellPrice B) (paidForwardCell_price B nav M d i j)
  apply h.trans
  let k := m*(n+1)
  have hk : 4*m*(n+1) = 4*k := by dsimp [k]; ring
  change nav+k*(nav+4*cellPrice B) ≤ _
  rw [hk]
  calc
    _ ≤ (cellPrice B+nav)+k*(4*(cellPrice B+nav)) := by
      apply Nat.add_le_add (by omega)
      apply Nat.mul_le_mul_left
      omega
    _ = _ := by ring

end Paper3.BareissBit

#print axioms Paper3.BareissBit.paidScan_correct
#print axioms Paper3.BareissBit.paidScan_price
#print axioms Paper3.BareissBit.paidForwardCell_correct
#print axioms Paper3.BareissBit.paidForwardCell_price
#print axioms Paper3.BareissBit.onDenseTable_price
#print axioms Paper3.BareissBit.paidForward_correct
#print axioms Paper3.BareissBit.paidForward_price

