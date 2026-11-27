import P3BareissBitForward

namespace Paper3.BareissBit

open Reconstruction.BareissSolver Reconstruction.BareissPaper
open AffineCost.Bit (Run)

def paidDot (B nav : ℕ) (acc : ℤ) : List (ℤ × ℤ) → Run ℤ
  | [] => ⟨acc,nav⟩
  | (a,b) :: ys =>
    let p := paidInt B (.mul a b)
    let v := paidInt B (.add acc p.value)
    let r := paidDot B nav v.value ys
    ⟨r.value,nav+p.steps+v.steps+r.steps⟩

theorem paidDot_correct (B nav : ℕ) (l : List (ℤ × ℤ)) (acc : ℤ)
    (h : ValidTrace B (dotTrace acc l)) :
    (paidDot B nav acc l).value = l.foldl (fun s p => s+p.1*p.2) acc := by
  induction l generalizing acc with
  | nil => rfl
  | cons z ls ih =>
    rcases z with ⟨a,b⟩
    have hm : Decodes B (.mul a b) := h _ (by simp [dotTrace])
    have ha : Decodes B (.add acc (a*b)) := h _ (by simp [dotTrace])
    have hh : ValidTrace B (dotTrace (acc+a*b) ls) := fun op ho =>
      h op (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ho))
    simp only [paidDot,List.foldl_cons,paidInt_correct hm rfl,paidInt_correct ha rfl]
    exact ih _ hh

theorem paidDot_price (B nav : ℕ) (l : List (ℤ × ℤ)) (acc : ℤ) :
    (paidDot B nav acc l).steps ≤ (2*l.length+1)*(cellPrice B+nav) := by
  induction l generalizing acc with
  | nil => simp [paidDot]
  | cons z ls ih =>
    rcases z with ⟨a,b⟩
    let p := paidInt B (.mul a b)
    let v := paidInt B (.add acc p.value)
    have hp : p.steps ≤ cellPrice B := paidInt_price _ _
    have hv : v.steps ≤ cellPrice B := paidInt_price _ _
    have hr := ih v.value
    have e : (2*(ls.length+1)+1)*(cellPrice B+nav) =
        (2*ls.length+1)*(cellPrice B+nav)+2*(cellPrice B+nav) := by ring
    simp only [paidDot,List.length_cons,e]
    change nav+p.steps+v.steps+(paidDot B nav v.value ls).steps ≤ _
    omega

def terms {m n : ℕ} (M : IntegerAugment (m+1) (n+1))
    (i : Fin (m+1)) (j : Fin (n+1)) (x : ScaledSolution n) : List (ℤ × ℤ) :=
  (List.finRange n).map fun v => (M i (some (j.succAbove v)), x.numerator v)

@[simp] theorem terms_length {m n : ℕ} (M : IntegerAugment (m+1) (n+1))
    (i : Fin (m+1)) (j : Fin (n+1)) (x : ScaledSolution n) :
    (terms M i j x).length = n := by simp [terms]

theorem terms_fold {m n : ℕ} (M : IntegerAugment (m+1) (n+1))
    (i : Fin (m+1)) (j : Fin (n+1)) (x : ScaledSolution n) :
    (terms M i j x).foldl (fun s p => s+p.1*p.2) 0 =
      (List.finRange n).foldl (fun s v => s+M i (some (j.succAbove v))*x.numerator v) 0 := by
  exact List.foldl_map

def paidBackward {m n : ℕ} (B nav : ℕ) (M : IntegerAugment (m+1) (n+1))
    (i : Fin (m+1)) (j : Fin (n+1)) (x : ScaledSolution n) : Run (ScaledSolution (n+1)) :=
  let lhs := paidInt B (.mul x.denominator (M i none))
  let rhs := paidDot B nav 0 (terms M i j x)
  let num := paidInt B (.sub lhs.value rhs.value)
  let out := paidInt B (.exactDiv num.value (M i (some j)))
  ⟨⟨x.denominator, denseIntColumn (Fin.insertNth j out.value x.numerator)⟩,
    (n+2)*nav+lhs.steps+rhs.steps+num.steps+out.steps⟩

theorem paidBackward_correct {m n : ℕ} (B nav : ℕ) (M : IntegerAugment (m+1) (n+1))
    (i : Fin (m+1)) (j : Fin (n+1)) (x : ScaledSolution n)
    (h : ValidTrace B (backwardTrace M i j x)) :
    (paidBackward B nav M i j x).value = backwardStep M i j x := by
  let a := x.denominator * M i none
  let b := (terms M i j x).foldl (fun s p => s+p.1*p.2) 0
  have hm : Decodes B (.mul x.denominator (M i none)) := h _ (by simp [backwardTrace])
  have hd : ValidTrace B (dotTrace 0 (terms M i j x)) := by
    intro op ho
    have he : op ∈ dotTrace 0 ((List.finRange n).map fun v =>
        (M i (some (j.succAbove v)), x.numerator v)) := ho
    exact h op (by simp [backwardTrace,he])
  have hs : Decodes B (.sub a b) := h _ (by simp [backwardTrace,a,b,terms_fold])
  have hq : Decodes B (.exactDiv (backwardDividend M i j x) (M i (some j))) :=
    h _ (by simp [backwardTrace])
  have he : a-b = backwardDividend M i j x := by simp only [a,b,terms_fold,backwardDividend]
  simp only [paidBackward,paidInt_correct hm rfl,paidDot_correct B nav _ _ hd]
  rw [show x.denominator * M i none = a from rfl,
    show (terms M i j x).foldl (fun s p => s+p.1*p.2) 0 = b from rfl,
    paidInt_correct hs rfl, he, paidInt_correct hq rfl]
  rfl

theorem paidBackward_price {m n : ℕ} (B nav : ℕ) (M : IntegerAugment (m+1) (n+1))
    (i : Fin (m+1)) (j : Fin (n+1)) (x : ScaledSolution n) :
    (paidBackward B nav M i j x).steps ≤ (3*n+6)*(cellPrice B+nav) := by
  let lhs := paidInt B (.mul x.denominator (M i none))
  let rhs := paidDot B nav 0 (terms M i j x)
  let num := paidInt B (.sub lhs.value rhs.value)
  let out := paidInt B (.exactDiv num.value (M i (some j)))
  have h₁ : lhs.steps ≤ cellPrice B := paidInt_price _ _
  have h₂ : rhs.steps ≤ (2*n+1)*(cellPrice B+nav) := by
    simpa only [terms_length] using paidDot_price B nav (terms M i j x) 0
  have h₃ : num.steps ≤ cellPrice B := paidInt_price _ _
  have h₄ : out.steps ≤ cellPrice B := paidInt_price _ _
  change (n+2)*nav+lhs.steps+rhs.steps+num.steps+out.steps ≤ _
  simp only [Nat.add_mul,Nat.mul_add,Nat.mul_assoc,Nat.one_mul] at h₂ ⊢
  omega

end Paper3.BareissBit

#print axioms Paper3.BareissBit.paidDot_correct
#print axioms Paper3.BareissBit.paidDot_price
#print axioms Paper3.BareissBit.paidBackward_correct
#print axioms Paper3.BareissBit.paidBackward_price
