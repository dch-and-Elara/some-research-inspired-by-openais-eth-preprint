import J6R32StatefulArithmeticCore

/-! Left-to-right visits of actual list occurrences. Arithmetic uses R12
word kernels with their exact charge and does not visit a callback again
to account for its fee. -/
namespace J6R32StatefulArithmetic
open AOracleMachineTime A1R10 A1R12 J6R22Active

def walk {S A B : Type*} (nil : Meter B) (op : B→B→Meter B) (read : A→SM S B) :
    List A→SM S B
  | [] => stationary nil
  | a::as => combine (read a) (walk nil op read as) op

def walkRef {A B : Type*} (nil : Meter B) (op : B→B→Meter B) (read : A→Meter B) :
    List A→Meter B
  | [] => nil
  | a::as => merge2 (read a) (walkRef nil op read as) op

theorem walk_sound {S A B : Type*} {I : S→Prop} (nil : Meter B) (op : B→B→Meter B)
    (read : A→SM S B) (ref : A→Meter B) (xs : List A)
    (h : ∀ a∈xs,Sound I (read a) (ref a)) :
    Sound I (walk nil op read xs) (walkRef nil op ref xs) := by
  induction xs with
  | nil => exact stationary_sound I nil
  | cons a as ih =>
    exact (h a List.mem_cons_self).combine
      (ih (fun i hi=>h i (List.mem_cons_of_mem _ hi))) op

variable {S : Type*} {p ell : ℕ} {fw : List (Word p)}
variable (hp : 0<p)

def addWord (x y : UVBlock fw ell) : Meter (UVBlock fw ell) := padCost (uvAdd hp x y) 2
def mulWord (x y : UVBlock fw ell) : Meter (UVBlock fw ell) := padCost (uvMul hp x y) 2

theorem merge_add (x y : Meter (UVBlock fw ell)) : merge2 x y (addWord hp)=addM hp x y := by
  simp only [merge2,addWord,padCost,addM,Nat.add_assoc]

theorem merge_mul (x y : Meter (UVBlock fw ell)) : merge2 x y (mulWord hp)=mulM hp x y := by
  simp only [merge2,mulWord,padCost,mulM,Nat.add_assoc]

def sumWords {A : Type*} (rd : A→SM S (UVBlock fw ell)) (as : List A) : SM S (UVBlock fw ell) :=
  walk (zeroM hp) (addWord hp) rd as

def prodWords {A : Type*} (he : 0<fw.length) (hv : 0<ell)
    (rd : A→SM S (UVBlock fw ell)) (as : List A) : SM S (UVBlock fw ell) :=
  walk (oneM hp he hv) (mulWord hp) rd as

theorem sumWords_sound {A : Type*} {I : S→Prop} (rd : A→SM S (UVBlock fw ell))
    (ref : A→Meter (UVBlock fw ell)) (as : List A)
    (h : ∀ i∈as,Sound I (rd i) (ref i)) : Sound I (sumWords hp rd as) (sumM hp ref as) := by
  have e : walkRef (zeroM hp) (addWord hp) ref as=sumM hp ref as := by
    clear h
    induction as with
    | nil => rfl
    | cons i is ih => rw [walkRef,sumM,ih,merge_add]
  rw [←e]
  exact walk_sound _ _ _ _ _ h

theorem prodWords_sound {A : Type*} {I : S→Prop} (he : 0<fw.length) (hv : 0<ell)
    (rd : A→SM S (UVBlock fw ell)) (ref : A→Meter (UVBlock fw ell)) (as : List A)
    (h : ∀ i∈as,Sound I (rd i) (ref i)) : Sound I (prodWords hp he hv rd as) (foldM hp he hv ref as) := by
  have e : walkRef (oneM hp he hv) (mulWord hp) ref as=foldM hp he hv ref as := by
    clear h
    induction as with
    | nil => rfl
    | cons i is ih => rw [walkRef,foldM,ih,merge_mul]
  rw [←e]
  exact walk_sound _ _ _ _ _ h

def grouped {Mode : Type*} {G : ℕ} (he : 0<fw.length) (hv : 0<ell) (ms : List Mode)
    (child : Mode→Fin G→SM S (UVBlock fw ell)) : SM S (UVBlock fw ell) :=
  sumWords hp (fun β=>prodWords hp he hv (child β) (groupOrder G)) ms

theorem grouped_sound {Mode : Type*} {G : ℕ} {I : S→Prop} (he : 0<fw.length) (hv : 0<ell)
    (ms : List Mode) (child : Mode→Fin G→SM S (UVBlock fw ell))
    (ref : Mode→Fin G→Meter (UVBlock fw ell))
    (exactChild : ∀ m∈ms,∀ g,Sound I (child m g) (ref m g)) :
    Sound I (grouped hp he hv ms child) (groupedProbe hp he hv ms ref) := by
  apply sumWords_sound
  intro β hβ
  exact prodWords_sound hp he hv (child β) (ref β) _ (fun g _=>exactChild β hβ g)

variable {k : ℕ} (he : 0<fw.length)
def addJet (x y : JetTape fw ell k) : Meter (JetTape fw ell k) := padCost (jetAdd hp he x y) 2
def sumJets {A : Type*} (rd : A→SM S (JetTape fw ell k)) (as : List A) : SM S (JetTape fw ell k) :=
  walk ⟨jetZero hp he k,tapeFee fw.length ell p k⟩ (addJet hp he) rd as

theorem sumJets_sound {A : Type*} {I : S→Prop} (rd : A→SM S (JetTape fw ell k))
    (ref : A→Meter (JetTape fw ell k)) (as : List A) (h : ∀ i∈as,Sound I (rd i) (ref i)) :
    Sound I (sumJets hp he rd as) (paidJetSum hp he ref as) := by
  have e : walkRef ⟨jetZero hp he k,tapeFee fw.length ell p k⟩ (addJet hp he) ref as=paidJetSum hp he ref as := by
    clear h
    induction as with
    | nil => rfl
    | cons i is ih => simp only [walkRef,paidJetSum,ih,merge2,addJet,padCost,Nat.add_assoc]
  rw [←e]
  exact walk_sound _ _ _ _ _ h

#print axioms walk_sound
#print axioms sumWords_sound
#print axioms prodWords_sound
#print axioms grouped_sound
#print axioms sumJets_sound
end J6R32StatefulArithmetic
