import J6R22ActiveStrip
import A1R10Readout

/-! Checked high-word extraction across a full rectangular U/V
frame. A failed coordinate does not produce an output word. Each
word is actually visited once, and the two-level map charges the
explicit traversal, not just one ring-level shift. -/
namespace J6R23ScheduleWeight
open A1R10 A1R11 AOracleMachineTime AOracleMachineTimeTape J6R22Active

def checkedMap {A B : Type*} (get : A→Meter (Option B)) (stride : ℕ) :
    List A→Meter (Option (List B))
  | [] => ⟨some [],2⟩
  | x::xs =>
    let a := get x
    let b := checkedMap get stride xs
    ⟨a.result.bind (fun v=>b.result.map (v::·)),a.steps+b.steps+stride+4⟩

theorem checkedMap_result {A B : Type*} (get : A→Meter (Option B)) (stride : ℕ)
    (xs : List A) (ys : List B) :
    (checkedMap get stride xs).result=some ys ↔ List.Forall₂ (fun a b=>(get a).result=some b) xs ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys <;> simp [checkedMap]
  | cons a xs ih =>
    cases ha : (get a).result with
    | none =>
      constructor
      · simp [checkedMap,ha]
      · intro H
        cases H with
        | cons h _ => simp [ha] at h
    | some b =>
      cases ys with
      | nil =>
        constructor
        · intro H
          cases hh : (checkedMap get stride xs).result <;> simp [checkedMap,ha,hh] at H
        · intro H
          cases H
      | cons c ys =>
        constructor
        · intro H
          cases hh : (checkedMap get stride xs).result with
          | none => simp [checkedMap,ha,hh] at H
          | some bs =>
            simp only [checkedMap,ha,Option.bind_some,hh,Option.map_some,Option.some.injEq,List.cons.injEq] at H
            rcases H with ⟨rfl,rfl⟩
            exact .cons ha ((ih bs).mp hh)
        · intro H
          cases H with
          | cons h r =>
            have hb : b=c := Option.some.inj (ha.symm.trans h)
            subst c
            simp only [checkedMap,ha,Option.bind_some,(ih ys).mpr r,Option.map_some]

theorem checkedMap_valid {A B : Type*} (get : A→Meter (Option B)) (stride : ℕ)
    (xs : List A) (h : ∀ a∈xs,∃ b,(get a).result=some b) :
    ∃ ys,(checkedMap get stride xs).result=some ys := by
  induction xs with
  | nil => exact ⟨[],rfl⟩
  | cons a xs ih =>
    obtain ⟨b,hb⟩ := h a List.mem_cons_self
    obtain ⟨ys,hy⟩ := ih (fun z hz=>h z (List.mem_cons_of_mem _ hz))
    exact ⟨b::ys,(checkedMap_result get stride _ _).mpr
      (.cons hb ((checkedMap_result get stride _ _).mp hy))⟩

theorem checkedMap_steps {A B : Type*} (get : A→Meter (Option B)) (stride cap : ℕ)
    (xs : List A) (h : ∀ a∈xs,(get a).steps≤cap) :
    (checkedMap get stride xs).steps≤2+xs.length*(cap+stride+4) := by
  induction xs with
  | nil => simp [checkedMap]
  | cons a xs ih =>
    have ha := h a List.mem_cons_self
    have ht := ih (fun z hz=>h z (List.mem_cons_of_mem _ hz))
    change (get a).steps+(checkedMap get stride xs).steps+stride+4≤2+
      (xs.length+1)*(cap+stride+4)
    rw [Nat.succ_mul xs.length]
    omega

def stripULoop {p B : ℕ} {old : List (Word (p+B))} {new : List (Word p)}
    (eq : old.length=new.length) (v : UBlock old) : Meter (Option (UBlock new)) :=
  let raw := checkedMap (highWord p B) p v.val
  let z := match h : raw.result with
    | none => none
    | some ys =>
      let R := (checkedMap_result (highWord p B) p v.val ys).mp h
      some ⟨ys,R.length_eq.symm.trans (v.property.trans eq)⟩
  ⟨z,raw.steps+4⟩

theorem stripULoop_steps {p B : ℕ} {old : List (Word (p+B))} {new : List (Word p)}
    (eq : old.length=new.length) (v : UBlock old) :
    (stripULoop eq v).steps≤6+old.length*(8*(p+B+1)+p+8) := by
  have cap := checkedMap_steps (highWord p B) p (8*(p+B+1)+4) v.val
    (fun x _=>(highWord_exact p B x).1.le)
  rw [v.property] at cap
  change (checkedMap (highWord p B) p v.val).steps+4≤_
  have hs : (8*(p+B+1)+4)+p+4=8*(p+B+1)+p+8 := by omega
  rw [hs] at cap
  omega

theorem stripULoop_correct {p B : ℕ} {old : List (Word (p+B))} {new : List (Word p)}
    (eq : old.length=new.length) (v : UBlock old)
    (h : ∀ x∈v.val,2^B∣bitsValue x.val) :
    ∃ u,(stripULoop eq v).result=some u ∧
      List.Forall₂ (fun x y=>bitsValue y.val=bitsValue x.val/2^B) v.val u.val := by
  obtain ⟨ys,he⟩ := checkedMap_valid (highWord p B) p v.val
    (fun x hx=>(highWord_exact p B x).2.1.mpr (h x hx))
  let R := (checkedMap_result (highWord p B) p v.val ys).mp he
  refine ⟨⟨ys,R.length_eq.symm.trans (v.property.trans eq)⟩,?_,?_⟩
  · unfold stripULoop
    dsimp only
    split
    · rename_i h'
      rw [he] at h'
      cases h'
    · rename_i y h'
      rw [he] at h'
      have e := Option.some.inj h'
      subst y
      rfl
  · exact R.imp (fun x y hz=>(highWord_exact p B x).2.2 y hz)

def stripUVLoop {p B ell : ℕ} {old : List (Word (p+B))} {new : List (Word p)}
    (eq : old.length=new.length) (v : UVBlock old ell) : Meter (Option (UVBlock new ell)) :=
  let raw := checkedMap (stripULoop eq) (new.length*p) v.val
  let z := match h : raw.result with
    | none => none
    | some ys =>
      let R := (checkedMap_result (stripULoop eq) (new.length*p) v.val ys).mp h
      some ⟨ys,R.length_eq.symm.trans v.property⟩
  ⟨z,raw.steps+4⟩

theorem stripUVLoop_correct {p B ell : ℕ} {old : List (Word (p+B))} {new : List (Word p)}
    (eq : old.length=new.length) (v : UVBlock old ell)
    (h : ∀ row∈v.val,∀ x∈row.val,2^B∣bitsValue x.val) :
    ∃ u,(stripUVLoop eq v).result=some u ∧
      List.Forall₂ (fun a b=>List.Forall₂ (fun x y=>bitsValue y.val=bitsValue x.val/2^B) a.val b.val)
        v.val u.val ∧
      (stripUVLoop eq v).steps≤6+ell*(10+old.length*(8*(p+B+1)+p+8)+new.length*p) := by
  let F := stripULoop eq
  have ready (x : UBlock old) (hx : x∈v.val) := stripULoop_correct eq x (h x hx)
  obtain ⟨ys,he⟩ := checkedMap_valid F (new.length*p) v.val (fun x hx=>by
    obtain ⟨w,hw,_⟩ := ready x hx
    exact ⟨w,hw⟩)
  let R := (checkedMap_result F (new.length*p) v.val ys).mp he
  refine ⟨⟨ys,R.length_eq.symm.trans v.property⟩,?_,?_,?_⟩
  · unfold stripUVLoop
    dsimp only
    split
    · rename_i h'
      change (checkedMap F (new.length*p) v.val).result=none at h'
      rw [he] at h'
      cases h'
    · rename_i zs h'
      change (checkedMap F (new.length*p) v.val).result=some zs at h'
      rw [he] at h'
      have q := Option.some.inj h'
      subst zs
      rfl
  · have useful (xs : List (UBlock old)) (zs : List (UBlock new))
        (rel : List.Forall₂ (fun x y=>(F x).result=some y) xs zs)
        (inc : ∀ q∈xs,q∈v.val) :
        List.Forall₂ (fun a b=>List.Forall₂ (fun x y=>bitsValue y.val=bitsValue x.val/2^B) a.val b.val)
          xs zs := by
      induction rel with
      | nil => exact .nil
      | @cons x y xs ys he' ht ih =>
        obtain ⟨u,hu,hr⟩ := ready x (inc x List.mem_cons_self)
        have eq := Option.some.inj (hu.symm.trans he')
        subst y
        exact .cons hr (ih (fun z hz=>inc z (List.mem_cons_of_mem _ hz)))
    exact useful v.val ys R (fun _ h=>h)
  · have cap := checkedMap_steps F (new.length*p) (6+old.length*(8*(p+B+1)+p+8)) v.val
      (fun x _=>stripULoop_steps eq x)
    rw [v.property] at cap
    change (checkedMap F (new.length*p) v.val).steps+4≤_
    have all : 6+old.length*(8*(p+B+1)+p+8)+new.length*p+4 =
        10+old.length*(8*(p+B+1)+p+8)+new.length*p := by omega
    rw [all] at cap
    omega

#print axioms checkedMap_result
#print axioms checkedMap_steps
#print axioms stripULoop_correct
#print axioms stripUVLoop_correct
end J6R23ScheduleWeight


