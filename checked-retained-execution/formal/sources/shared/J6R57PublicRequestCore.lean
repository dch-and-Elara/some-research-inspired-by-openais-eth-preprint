import J6R21AncestorDirectory

/-! Sequential producers and actual fixed-width request lookup. The
lookup borrows the selected resident row; no free data copy is asserted.
The separate producer meters row construction and writing every row. -/
namespace J6R57PublicRequest
open AOracleMachineTime J6R15ModeCost J6R21Ancestor
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

def emitRows {I A : Type*} (f : I → Meter A) : List I → Meter (List A)
  | [] => ⟨[],2⟩
  | x::xs =>
    let v := f x
    let tail := emitRows f xs
    ⟨v.result::tail.result,v.steps+tail.steps+4⟩

theorem emitted_rows_exact {I A : Type*} (f : I → Meter A) (is : List I) :
    (emitRows f is).result=is.map (fun x=>(f x).result) ∧
      (emitRows f is).steps=2+(is.map fun x=>(f x).steps+4).sum := by
  induction is with
  | nil => exact ⟨rfl,rfl⟩
  | cons x xs ih =>
    simp only [emitRows,List.map_cons,List.sum_cons,ih.1,ih.2]
    exact ⟨True.intro,by omega⟩

def prependRows {A : Type*} (tail : List A) : List A → Meter (List A)
  | [] => ⟨tail,2⟩
  | x::xs =>
    let rest := prependRows tail xs
    ⟨x::rest.result,rest.steps+3⟩

theorem prepend_rows_exact {A : Type*} (front tail : List A) :
    prependRows tail front=⟨front++tail,3*front.length+2⟩ := by
  induction front with
  | nil => rfl
  | cons x xs ih =>
    simp only [prependRows,ih,List.length_cons,List.cons_append]
    congr 1

def emitBooks {I A : Type*} (f : I → Meter (List A)) : List I → Meter (List A)
  | [] => ⟨[],2⟩
  | x::xs =>
    let head := f x
    let rest := emitBooks f xs
    let written := prependRows rest.result head.result
    ⟨written.result,head.steps+rest.steps+written.steps+3⟩

theorem emitted_books_exact {I A : Type*} (f : I → Meter (List A)) (is : List I) :
    (emitBooks f is).result=is.flatMap (fun x=>(f x).result) ∧
      (emitBooks f is).steps=2+(is.map fun x=>(f x).steps+3*(f x).result.length+5).sum := by
  induction is with
  | nil => exact ⟨rfl,rfl⟩
  | cons x xs ih =>
    simp only [emitBooks,prepend_rows_exact,List.flatMap_cons,List.map_cons,List.sum_cons,ih.1,ih.2]
    exact ⟨True.intro,by omega⟩

def lookup {A : Type*} {width : ℕ} (key : A→Word width) (raw : Word width) :
    List A → Meter (Option A)
  | [] => ⟨none,2⟩
  | x::xs =>
    let test := cmpAddr raw (key x)
    if test.result then ⟨some x,test.steps+3⟩ else
      let rest := lookup key raw xs
      ⟨rest.result,test.steps+rest.steps+4⟩

theorem lookup_exactly_first {A : Type*} {width : ℕ} (key : A→Word width)
    (raw : Word width) (x : A) (front tail : List A)
    (target : key x=raw) (before : ∀ y∈front,key y≠raw) :
    lookup key raw (front++x::tail)=
      ⟨some x,front.length*(10*width+9)+(10*width+8)⟩ := by
  induction front with
  | nil =>
    have test := cmpAddr_exact raw (key x)
    simp only [List.nil_append,lookup,if_pos (test.1.mpr target.symm),test.2, List.length_nil,
      Nat.zero_mul,Nat.zero_add]
  | cons y ys ih =>
    have test := cmpAddr_exact raw (key y)
    have no : ¬ (cmpAddr raw (key y)).result=true :=
      fun same=>before y List.mem_cons_self (test.1.mp same).symm
    have rest := ih (fun z hz=>before z (List.mem_cons_of_mem y hz))
    simp only [List.cons_append,lookup,if_neg no,test.2,rest,List.length_cons]
    congr 1
    simp only [Nat.add_mul,Nat.one_mul]
    omega

theorem lookup_roof {A : Type*} {width : ℕ} (key : A→Word width)
    (raw : Word width) (rows : List A) :
    (lookup key raw rows).steps≤rows.length*(10*width+9)+2 := by
  induction rows with
  | nil => simp [lookup]
  | cons x xs ih =>
    have fee := (cmpAddr_exact raw (key x)).2
    rw [lookup]
    split <;> simp only [fee,List.length_cons,Nat.add_mul,Nat.one_mul] <;> omega

theorem lookup_success_iff {A : Type*} {width : ℕ} (key : A→Word width)
    (raw : Word width) (rows : List A) :
    (lookup key raw rows).result.isSome ↔ ∃ row∈rows,key row=raw := by
  induction rows with
  | nil => simp [lookup]
  | cons x xs ih =>
    have h := cmpAddr_exact raw (key x)
    by_cases eq : key x=raw
    · rw [lookup,if_pos (h.1.mpr eq.symm)]
      exact ⟨fun _=>⟨x,List.mem_cons_self,eq⟩,fun _=>rfl⟩
    · have no : ¬ (cmpAddr raw (key x)).result=true := fun t=>eq (h.1.mp t).symm
      rw [lookup,if_neg no]
      change (lookup key raw xs).result.isSome ↔ _
      rw [ih]
      constructor
      · rintro ⟨r,hr,k⟩
        exact ⟨r,List.mem_cons_of_mem x hr,k⟩
      · rintro ⟨r,hr,k⟩
        rcases List.mem_cons.mp hr with h | h
        · exact (eq (h ▸ k)).elim
        · exact ⟨r,h,k⟩

theorem lookup_returns_only_written_row {A : Type*} {width : ℕ} (key : A→Word width)
    (raw : Word width) (rows : List A) (x : A) (hit : (lookup key raw rows).result=some x) :
    x∈rows ∧ key x=raw := by
  induction rows with
  | nil => simp [lookup] at hit
  | cons y ys ih =>
    have h := cmpAddr_exact raw (key y)
    by_cases eq : key y=raw
    · rw [lookup,if_pos (h.1.mpr eq.symm)] at hit
      have H : y=x := Option.some.inj hit
      subst x
      exact ⟨List.mem_cons_self,eq⟩
    · have no : ¬ (cmpAddr raw (key y)).result=true := fun t=>eq (h.1.mp t).symm
      rw [lookup,if_neg no] at hit
      obtain ⟨mem,k⟩ := ih hit
      exact ⟨List.mem_cons_of_mem y mem,k⟩

#print axioms emitted_rows_exact
#print axioms prepend_rows_exact
#print axioms emitted_books_exact
#print axioms lookup_exactly_first
#print axioms lookup_roof
#print axioms lookup_success_iff
#print axioms lookup_returns_only_written_row
end J6R57PublicRequest
