import J9LayoutTransferCompiler
import J9EndProbe

/-!
# Literal J9 compiler with separate physical columns and binary row ports

The extra pinned port carries the source feature. For a column bit x,
its own base is x, so its unmarked affine factor is 1. Thus a column is
summed exactly once, and is not identified with either row Boolean leg.
The equality CNF on the original row pairs is retained literally.
-/

namespace J9R13Compiler

open scoped BigOperators Classical
open LiteralPortCompiler J9LayoutTransfer MvPolynomial

noncomputable section

def relabel {I J : Type*} (e : I→J) (F : CNF I) : CNF J :=
  F.map (fun c => c.map (fun q => (e q.1,q.2)))

theorem satisfied_relabel {I J : Type*} (e : I→J) (F : CNF I) (a : J→Bool) :
    satisfied (relabel e F) a=satisfied F (a ∘ e) := by
  unfold relabel satisfied
  rw [List.all_map]
  apply congrArg (List.all F)
  funext c
  rw [Function.comp_apply,List.any_map]
  rfl

theorem truth_relabel {I J K : Type*} [Zero K] [One K]
    (e : I→J) (F : CNF I) (a : J→Bool) :
    (truth (relabel e F) a : K)=truth F (a ∘ e) := by
  simp [truth,satisfied_relabel]

abbrev Site (I R : Type*) := I ⊕ (Port R ⊕ Unit)

def column {I R : Type*} (i : I) : Site I R := .inl i
def row {I R : Type*} (p : Port R) : Site I R := .inr (.inl p)
def feature {I R : Type*} : Site I R := .inr (.inr ())

def assignment {I R : Type*} (x : I→Bool) (y : Port R→Bool) (b : Bool) : Site I R→Bool :=
  Sum.elim x (Sum.elim y (fun _ => b))

def separate (I R : Type*) : (Site I R→Bool) ≃ ((I→Bool) × ((Port R→Bool) × Bool)) where
  toFun a := (a ∘ column, a ∘ row, a feature)
  invFun a := assignment a.1 a.2.1 a.2.2
  left_inv a := by
    funext i
    cases i with
    | inl i => rfl
    | inr t => cases t with
      | inl p => rfl
      | inr u => cases u; rfl
  right_inv a := by cases a; rfl

variable {I R K B : Type*} [Fintype I] [Fintype R] [Fintype B] [CommRing K]

def system (F : CNF I) : CNF (Site I R) :=
  relabel column F ++ relabel row (allRows (R:=R)) ++ pin feature true

def base (u : (I→Bool)→Port R→K) (w : (I→Bool)→K)
    (a : Site I R→Bool) : Site I R→K :=
  Sum.elim (fun i => indicator K (a (column i)))
    (Sum.elim (u (a ∘ column)) (fun _ => w (a ∘ column)))

def kernel (v : (I→Bool)→Port R→B→K)
    (a : Site I R→Bool) : Site I R→B→K :=
  Sum.elim (fun _ _ => 0) (Sum.elim (v (a ∘ column)) (fun _ _ => 0))

omit [Fintype I] [Fintype B] in
theorem system_truth (F : CNF I) (x : I→Bool) (y : Port R→Bool) (b : Bool) :
    (truth (system (R:=R) F) (assignment x y b) : K) =
      truth F x * truth (allRows (R:=R)) y * indicator K b := by
  rw [system,truth_append,truth_append,truth_relabel,truth_relabel,truth_pin]
  cases b <;> rfl

omit [Fintype I] [Fintype R] in
theorem column_neutral (u : (I→Bool)→Port R→K) (w : (I→Bool)→K)
    (v : (I→Bool)→Port R→B→K) (x : I→Bool) (y : Port R→Bool) (b : Bool) (i : I) :
    portPoly (assignment x y b) (base u w) (kernel v) (column i) = 1 := by
  cases h : x i <;>
    simp [portPoly,portTerm,base,kernel,column,assignment,indicator,affine,h]

omit [Fintype I] [Fintype R] in
theorem row_unchanged (u : (I→Bool)→Port R→K) (w : (I→Bool)→K)
    (v : (I→Bool)→Port R→B→K) (x : I→Bool) (y : Port R→Bool) (b : Bool) (p : Port R) :
    portPoly (assignment x y b) (base u w) (kernel v) (row p) =
      portPoly y (fun _ => u x) (fun _ => v x) p := by
  rfl

omit [Fintype I] [Fintype R] in
theorem pinned_feature (u : (I→Bool)→Port R→K) (w : (I→Bool)→K)
    (v : (I→Bool)→Port R→B→K) (x : I→Bool) (y : Port R→Bool) :
    portPoly (assignment x y true) (base u w) (kernel v) feature = C (w x) := by
  simp [portPoly,portTerm,base,kernel,feature,assignment,affine]
  rfl

theorem completed_separate (F : CNF I) (u : (I→Bool)→Port R→K)
    (v : (I→Bool)→Port R→B→K) (w : (I→Bool)→K) :
    completed (system (R:=R) F) (base u w) (kernel v) =
      ∑ x : I→Bool, C (truth F x * w x) *
        completed (allRows (R:=R)) (fun _ => u x) (fun _ => v x) := by
  unfold completed at ⊢
  let P (x : I→Bool) (y : Port R→Bool) (b : Bool) : MvPolynomial B K :=
    C (truth (system (R:=R) F) (assignment x y b)) *
      ∏ p : Site I R, portPoly (assignment x y b) (base u w) (kernel v) p
  have hsum : (∑ a : Site I R→Bool, C (truth (system (R:=R) F) a) *
      ∏ p : Site I R, portPoly a (base u w) (kernel v) p) =
      ∑ z : (I→Bool) × ((Port R→Bool) × Bool), P z.1 z.2.1 z.2.2 := by
    refine (Equiv.sum_comp (separate I R).symm
      (fun a => C (truth (system (R:=R) F) a) *
        ∏ p : Site I R, portPoly a (base u w) (kernel v) p)).symm
  have hterm (x : I→Bool) (y : Port R→Bool) :
      (∑ b : Bool, P x y b) =
        C (truth F x * w x) *
          (C (truth (allRows (R:=R)) y) * ∏ p : Port R,
              portPoly y (fun _ => u x) (fun _ => v x) p) := by
    rw [Finset.sum_eq_single true]
    · unfold P
      rw [system_truth, Fintype.prod_sum_type, Fintype.prod_sum_type]
      have h₁ (i : I) : portPoly (assignment x y true) (base u w) (kernel v) (.inl i) = 1 :=
        column_neutral u w v x y true i
      have h₂ (p : Port R) : portPoly (assignment x y true) (base u w) (kernel v) (.inr (.inl p)) =
          portPoly y (fun _ => u x) (fun _ => v x) p := row_unchanged u w v x y true p
      have h₃ (t : Unit) : portPoly (assignment x y true) (base u w) (kernel v) (.inr (.inr t)) = C (w x) := by
        cases t
        exact pinned_feature u w v x y
      simp [h₁,h₂,h₃,indicator,map_mul]
      ring
    · intro b _ hb
      cases b
      · unfold P
        rw [system_truth]
        simp [indicator]
      · exact (hb rfl).elim
    · simp
  rw [hsum,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  rw [Fintype.sum_prod_type,Finset.mul_sum]
  exact Finset.sum_congr rfl (fun y _ => hterm x y)

theorem singleton_separate (F : CNF I) (u v : (I→Bool)→Port R→K) (w : (I→Bool)→K) :
    coeff β (completed (system (R:=R) F) (base u w) (kernel (fun x p (_ : Unit) => v x p))) =
      ∑ x : I→Bool, (truth F x * w x) * coeff β (rowCompiler (u x) (v x)) := by
  rw [completed_separate,coeff_sum]
  exact Finset.sum_congr rfl (fun x _ => by rw [coeff_C_mul]; rfl)

#print axioms system_truth
#print axioms completed_separate
#print axioms singleton_separate

end
end J9R13Compiler
