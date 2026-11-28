
import J6R21AncestorRegistry

/-! A complete generated OriginFields capsule has one copied native U/V
probe word, two newly scanned physical slot arrays, and the newly emitted
typed mode records. Its constructor charges every component once.
Installing the new capsule in the durable child directory is separate. -/
namespace J6R27OriginalGate
open AOracleMachineTime A1R10 J6R21Ancestor J6R18ChildWrite

private theorem already_metered {A : Type*} {u : Meter A} {y : A} {n : ℕ}
    (a : u.result=y) (b : u.steps=n) : u=⟨y,n⟩ := by
  cases u
  simp_all

def cloneList {A : Type*} (read : A→Meter A) : List A→Meter (List A)
  | [] => ⟨[],2⟩
  | x::xs =>
    let y := read x
    let z := cloneList read xs
    ⟨y.result::z.result,y.steps+z.steps+4⟩

theorem clone_list_exact {A : Type*} (read : A→Meter A) (fee : ℕ)
    (h : ∀ x,read x=⟨x,fee⟩) (xs : List A) :
    cloneList read xs=⟨xs,2+xs.length*(fee+4)⟩ := by
  induction xs with
  | nil => simp [cloneList]
  | cons x xs ih =>
    rw [cloneList,h x,ih]
    simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
    congr 1
    omega

def cloneAWord {p : ℕ} (w : A1R10.Word p) : Meter (A1R10.Word p) :=
  let z := copyBytes w.val
  ⟨⟨z.result,by
    change (copyBytes w.val).result.length=p
    rw [copyBytes_exact]
    exact w.property⟩,z.steps⟩

theorem clone_word_exact {p : ℕ} (w : A1R10.Word p) :
    cloneAWord w=⟨w,3*p+1⟩ := by
  apply already_metered
  · apply Subtype.ext
    change (copyBytes w.val).result=w.val
    rw [copyBytes_exact]
  · change (copyBytes w.val).steps=_
    rw [copyBytes_exact,w.property]

def cloneU {p : ℕ} {fw : List (A1R10.Word p)} (u : UBlock fw) : Meter (UBlock fw) :=
  let z := cloneList cloneAWord u.val
  ⟨⟨z.result,by
    change (cloneList cloneAWord u.val).result.length=fw.length
    rw [clone_list_exact cloneAWord _ clone_word_exact]
    exact u.property⟩,z.steps+2⟩

theorem clone_u_exact {p : ℕ} {fw : List (A1R10.Word p)} (u : UBlock fw) :
    cloneU u=⟨u,4+fw.length*(3*p+5)⟩ := by
  have E := clone_list_exact cloneAWord _ clone_word_exact u.val
  apply already_metered
  · apply Subtype.ext
    change (cloneList cloneAWord u.val).result=u.val
    rw [E]
  · change (cloneList cloneAWord u.val).steps+2=_
    rw [E]
    dsimp only
    rw [u.property]
    rw [show 3*p+1+4=3*p+5 by omega]
    omega

def cloneUV {p ell : ℕ} {fw : List (A1R10.Word p)} (v : UVBlock fw ell) :
    Meter (UVBlock fw ell) :=
  let z := cloneList cloneU v.val
  ⟨⟨z.result,by
    change (cloneList cloneU v.val).result.length=ell
    rw [clone_list_exact cloneU _ clone_u_exact]
    exact v.property⟩,z.steps+2⟩

def probeCopyFee (p ell deg : ℕ) : ℕ := 4+ell*(8+deg*(3*p+5))

theorem clone_uv_exact {p ell : ℕ} {fw : List (A1R10.Word p)} (v : UVBlock fw ell) :
    cloneUV v=⟨v,probeCopyFee p ell fw.length⟩ := by
  have E := clone_list_exact cloneU _ clone_u_exact v.val
  apply already_metered
  · apply Subtype.ext
    change (cloneList cloneU v.val).result=v.val
    rw [E]
  · change (cloneList cloneU v.val).steps+2=_
    rw [E]
    dsimp only
    rw [v.property]
    change 2+ell*((4+fw.length*(3*p+5))+4)+2=4+ell*(8+fw.length*(3*p+5))
    rw [show 4+fw.length*(3*p+5)+4=8+fw.length*(3*p+5) by omega]
    omega

def assembleOriginFields {a p ell q : ℕ} {fw : List (A1R10.Word p)} {i : Fin a}
    (probe : UVBlock fw ell)
    (slots : Meter (List (J6R15ModeCost.Word a)×List (J6R15ModeCost.Word a)))
    (modes : Meter (Option (List (ModeInput a p i q)))) :
    Meter (Option (OriginFields a p ell q fw i)) :=
  let z := cloneUV probe
  match modes.result with
  | none => ⟨none,z.steps+slots.steps+modes.steps+4⟩
  | some ms =>
    ⟨some ⟨z.result,slots.result.1,slots.result.2,ms⟩,z.steps+slots.steps+modes.steps+6⟩

theorem origin_fields_written {a p ell q : ℕ} {fw : List (A1R10.Word p)} {i : Fin a}
    (probe : UVBlock fw ell)
    (slots : Meter (List (J6R15ModeCost.Word a)×List (J6R15ModeCost.Word a)))
    (modes : Meter (Option (List (ModeInput a p i q)))) (ms : List (ModeInput a p i q))
    (valid : modes.result=some ms) :
    assembleOriginFields probe slots modes=
      ⟨some ⟨probe,slots.result.1,slots.result.2,ms⟩,
        probeCopyFee p ell fw.length+slots.steps+modes.steps+6⟩ := by
  unfold assembleOriginFields
  dsimp only
  rw [clone_uv_exact,valid]

#print axioms clone_word_exact
#print axioms clone_uv_exact
#print axioms origin_fields_written
end J6R27OriginalGate




