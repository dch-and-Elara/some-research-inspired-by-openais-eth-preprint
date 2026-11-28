import J6R51IngressRawTree
import J6R51IngressFreshPlant

/-! A paid raw wire-key search selects the same actual ordinal as the
fresh typed chart. No input field stores the numeric answers. -/
namespace J6R51Ingress
open scoped Classical
open Std.Sat A1R10 AOracleMachineTime J6R49RootIngress J6R50RootIngress
open J7R9Compiler J7R10Plant J6R27OriginalGate
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 12200000

def eqWire {h d j : ℕ} : WireKey h d j→WireKey h d j→Meter Bool
  | .original u a,.original v b =>
    let p := eqRawBits u.val v.val
    let q := eqRawBits a.val b.val
    ⟨p.result && q.result,p.steps+q.steps+7⟩
  | .tree u a,.tree v b =>
    let p := eqRawBits u v
    let q := eqRawBits a.val b.val
    ⟨p.result && q.result,p.steps+q.steps+7⟩
  | _,_ => ⟨false,3⟩

theorem eq_wire_exact {h d j : ℕ} (u v : WireKey h d j) :
    (eqWire u v).result=true ↔ u=v := by
  cases u <;> cases v <;> simp [eqWire,(eq_raw_bits_exact _ _).1,Subtype.ext_iff]

def seekWire {h d j q : ℕ} (key : WireKey h d j) (one : Word q) :
    Word q→List (WireKey h d j)→Meter (Option (Word q))
  | _,[] => ⟨none,2⟩
  | k,u::us =>
    let e := eqWire u key
    if e.result then ⟨some k,e.steps+4⟩ else
      let n := addWord k one
      let R := seekWire key one n.result us
      ⟨R.result,e.steps+n.steps+R.steps+6⟩

theorem seek_wire_exact {A : Type*} [DecidableEq A] {h d j q : ℕ}
    (f : A→WireKey h d j) (inj : Function.Injective f) (x : A) (ls : List A)
    (mem : x∈ls) (i : ℕ) (hq : 0<q) (fit : i+ls.length≤2^q) :
    (seekWire (f x) (wordOne q) (wordAt q i) (ls.map f)).result =
      some (wordAt q (i+indexByEq x ls)) := by
  induction ls generalizing i with
  | nil => simp at mem
  | cons a as ih =>
    by_cases ex : a=x
    · subst a
      have E := (eq_wire_exact (f x) (f x)).mpr rfl
      simp [seekWire,E,indexByEq]
    · have exF : f a≠f x := fun w=>ex (inj w)
      have E := Bool.eq_false_iff.mpr (fun e=>exF ((eq_wire_exact (f a) (f x)).mp e))
      have mt : x∈as := (List.mem_cons.mp mem).resolve_left (Ne.symm ex)
      have hf : i+1<2^q := by
        have K : 0<as.length := List.length_pos_iff.mpr (by intro s; simp [s] at mt)
        simp only [List.length_cons] at fit
        omega
      have V := (J6R27PrescribedProbe.encoded_succ q i hq hf).1
      change (addWord (wordAt q i) (wordOne q)).result=wordAt q (i+1) at V
      have K := ih mt (i+1) (by simp only [List.length_cons] at fit; omega)
      have L : indexByEq x (a::as)=(indexByEq x as).succ := List.idxOf_cons_ne _ ex
      simp only [List.map_cons,seekWire,E,Bool.false_eq_true,if_false,V,K,L]
      congr 2
      omega

theorem key_of_injective {V : Type*} [DecidableEq V] {h d j : ℕ}
    (H : CNF V) (code : V→List Bool) (inj : Function.Injective code)
    (fitH : H.length≤2^h) (fitD : ∀ row∈H,row.length≤2^d)
    (fitJ : ∀ v,(occurrences H v).length-3≤2^j) :
    Function.Injective (keyOf (h:=h) (d:=d) (j:=j) H code) := by
  rintro (⟨a,l⟩|⟨a,l⟩) (⟨b,k⟩|⟨b,k⟩) eq
  · obtain ⟨u,v⟩ := WireKey.original.inj eq
    have es : a=b := Fin.ext (wordAt_rank_inj (a.isLt.trans_le fitH) (b.isLt.trans_le fitH) u)
    subst b
    have et : l=k := Fin.ext (wordAt_rank_inj
      (l.isLt.trans_le (fitD _ (List.get_mem _ a))) (k.isLt.trans_le (fitD _ (List.get_mem _ a))) v)
    subst k
    rfl
  · cases eq
  · cases eq
  · obtain ⟨u,v⟩ := WireKey.tree.inj eq
    have es : a=b := inj u
    subst b
    have et : l=k := Fin.ext (wordAt_rank_inj
      (l.isLt.trans_le (fitJ a)) (k.isLt.trans_le (fitJ a)) v)
    subst k
    rfl

theorem raw_wire_rank_from_chosen_list {V : Type*} [DecidableEq V] [Fintype V] {h d j q : ℕ}
    (H : CNF V) (s : DeclaredOrder V) (code : V→List Bool) (inj : Function.Injective code)
    (fitH : H.length≤2^h) (fitD : ∀ row∈H,row.length≤2^d)
    (fitJ : ∀ v,(occurrences H v).length-3≤2^j)
    (hq : 0<q) (fitQ : (wireOrder H s).length≤2^q)
    (v : Wire H) :
    (seekWire (keyOf (h:=h) (d:=d) (j:=j) H code v) (wordOne q) (wordAt q 0)
      ((wireOrder H s).map (keyOf H code))).result =
      some (wordAt q ((wireRank H s) v).val) := by
  have E := seek_wire_exact (keyOf (h:=h) (d:=d) (j:=j) H code)
    (key_of_injective H code inj fitH fitD fitJ) v (wireOrder H s) (wire_order_all H s v)
    0 hq (by simpa only [Nat.zero_add] using fitQ)
  rw [E,Nat.zero_add]
  rfl

#print axioms eq_wire_exact
#print axioms seek_wire_exact
#print axioms key_of_injective
#print axioms raw_wire_rank_from_chosen_list
end J6R51Ingress
