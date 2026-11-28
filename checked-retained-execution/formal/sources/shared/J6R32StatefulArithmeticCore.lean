import J6R24MeteredRecursionWhole

/-! Ordered metered effects: each arithmetic node uses its children's
real results and state. Proof projection reads the finished result; it
does not run the two versions of the machine. -/
namespace J6R32StatefulArithmetic
open AOracleMachineTime

abbrev SM (S A : Type*) := S→Meter (A×S)

def stationary {S A : Type*} (a : Meter A) : SM S A := fun s=>⟨(a.result,s),a.steps⟩

def finish {S A B : Type*} (a : SM S A) (f : A→Meter B) : SM S B := fun s=>
  let x := a s
  let b := f x.result.1
  ⟨(b.result,x.result.2),x.steps+b.steps⟩

def combine {S A B C : Type*} (a : SM S A) (b : SM S B) (f : A→B→Meter C) : SM S C := fun s=>
  let u := a s
  let v := b u.result.2
  let c := f u.result.1 v.result.1
  ⟨(c.result,v.result.2),u.steps+v.steps+c.steps⟩

def bind {S A B : Type*} (a : SM S A) (b : A→SM S B) : SM S B := fun s=>
  let x := a s
  let y := b x.result.1 x.result.2
  ⟨y.result,x.steps+y.steps⟩

def project {S A : Type*} (x : Meter (A×S)) : Meter A := ⟨x.result.1,x.steps⟩

def merge {A B : Type*} (a : Meter A) (f : A→Meter B) : Meter B :=
  let b := f a.result
  ⟨b.result,a.steps+b.steps⟩

def merge2 {A B C : Type*} (a : Meter A) (b : Meter B) (f : A→B→Meter C) : Meter C :=
  let c := f a.result b.result
  ⟨c.result,a.steps+b.steps+c.steps⟩

theorem project_finisher {S A B : Type*} (a : SM S A) (f : A→Meter B) (s : S) :
    project (finish a f s)=merge (project (a s)) f := rfl

theorem project_combine {S A B C : Type*} (a : SM S A) (b : SM S B) (f : A→B→Meter C)
    (s : S) : project (combine a b f s)=merge2 (project (a s)) (project (b (a s).result.2)) f := rfl

/-- The ghost reference contains no runtime callbacks. Its value, local
fee, and an exact additional fee are tracked; the actual program needs
none of the witness data. -/
structure AgreesAt {S A : Type*} (I : S→Prop) (out : Meter (A×S)) (ref : Meter A) (extra : ℕ) : Prop where
  value : out.result.1=ref.result
  fee : out.steps=ref.steps+extra
  invariant : I out.result.2

def Sound {S A : Type*} (I : S→Prop) (run : SM S A) (ref : Meter A) : Prop :=
  ∀ s,I s→∃ extra,AgreesAt I (run s) ref extra

theorem stationary_sound {S A : Type*} (I : S→Prop) (ref : Meter A) :
    Sound I (stationary ref) ref := by
  intro s hs
  exact ⟨0,⟨rfl,(Nat.add_zero _).symm,hs⟩⟩

theorem AgreesAt.finish {S A B : Type*} {I : S→Prop} {x : SM S A} {s : S}
    {a : Meter A} {d : ℕ} (h : AgreesAt I (x s) a d) (f : A→Meter B) :
    AgreesAt I (finish x f s) (merge a f) d := by
  refine ⟨?_,?_,h.invariant⟩
  · change (f (x s).result.1).result=(f a.result).result
    rw [h.value]
  · change (x s).steps+(f (x s).result.1).steps=a.steps+(f a.result).steps+d
    rw [h.value,h.fee]
    omega

theorem AgreesAt.combine {S A B C : Type*} {I : S→Prop} {x : SM S A} {y : SM S B} {s : S}
    {a : Meter A} {b : Meter B} {d e : ℕ} (h : AgreesAt I (x s) a d)
    (k : AgreesAt I (y (x s).result.2) b e) (f : A→B→Meter C) :
    AgreesAt I (combine x y f s) (merge2 a b f) (d+e) := by
  refine ⟨?_,?_,k.invariant⟩
  · change (f (x s).result.1 (y (x s).result.2).result.1).result=(f a.result b.result).result
    rw [h.value,k.value]
  · change (x s).steps+(y (x s).result.2).steps+
      (f (x s).result.1 (y (x s).result.2).result.1).steps=a.steps+b.steps+(f a.result b.result).steps+(d+e)
    rw [h.value,k.value,h.fee,k.fee]
    omega

theorem Sound.finish {S A B : Type*} {I : S→Prop} {x : SM S A} {a : Meter A}
    (h : Sound I x a) (f : A→Meter B) : Sound I (finish x f) (merge a f) := by
  intro s hs
  obtain ⟨d,v⟩ := h s hs
  exact ⟨d,v.finish f⟩

theorem Sound.combine {S A B C : Type*} {I : S→Prop} {x : SM S A} {y : SM S B}
    {a : Meter A} {b : Meter B} (h : Sound I x a) (k : Sound I y b)
    (f : A→B→Meter C) : Sound I (combine x y f) (merge2 a b f) := by
  intro s hs
  obtain ⟨d,v⟩ := h s hs
  obtain ⟨e,w⟩ := k _ v.invariant
  exact ⟨d+e,v.combine w f⟩

open J6R22Active in
/-- R24 success check is a real conditional; the state is not rolled back
on a failure. Legal source runs rule the failure branch out separately. -/
def stripCheck {S A : Type*} (fallback : Meter A) (x : SM S (Option A)) : SM S A :=
  finish x (fun a=>match a with
    | some v => ⟨v,2⟩
    | none => ⟨fallback.result,fallback.steps+2⟩)

theorem strip_sound {S A : Type*} {I : S→Prop} {fallback : Meter A}
    {x : SM S (Option A)} {a : Meter (Option A)} (h : Sound I x a) :
    Sound I (stripCheck fallback x) (J6R24MeteredRecursion.checkedWord fallback a) := by
  have q := h.finish (fun r=>match r with | some v=>⟨v,2⟩ | none=>⟨fallback.result,fallback.steps+2⟩)
  convert q using 1
  cases hA:a.result <;> simp [merge,J6R24MeteredRecursion.checkedWord,hA,Nat.add_assoc]

#print axioms project_combine
#print axioms AgreesAt.finish
#print axioms AgreesAt.combine
#print axioms Sound.combine
#print axioms strip_sound
end J6R32StatefulArithmetic
