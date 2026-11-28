
import J6R23PaddingCensusMachine

/-! A concrete injective key for a physical Appendix D page: copy index,
the two six-bit symbols of each sorted coordinate, and one selector bit
per coordinate (zero in a cold coordinate). No arbitrary page-rank
oracle and no omitted orientation bits. -/
namespace J6R23PaddingCensus
open scoped BigOperators
open P11FullPacking A1R10 A1R12 AOracleMachineTime AOracleMachineTimeTape
set_option maxHeartbeats 14000000
set_option linter.unusedSectionVars false

private theorem little_bit_inj (x y : List Bool) (hlen : x.length=y.length)
    (h : bitsValue x=bitsValue y) : x=y := by
  induction x generalizing y with
  | nil => cases y <;> simp_all
  | cons b bs ih =>
    cases y with
    | nil => simp at hlen
    | cons c cs =>
      have len : bs.length=cs.length := Nat.succ.inj hlen
      cases b <;> cases c <;> simp only [bitsValue,Bool.toNat_false,Bool.toNat_true] at h
      · exact congrArg (List.cons false) (ih cs len (by omega))
      · omega
      · omega
      · exact congrArg (List.cons true) (ih cs len (by omega))

def fixedConcat {n : ℕ} : List (Word n)→List Bool
  | [] => []
  | a::as => a.val++fixedConcat as

theorem fixed_concat_length {n : ℕ} (xs : List (Word n)) :
    (fixedConcat xs).length=n*xs.length := by
  induction xs with
  | nil => simp [fixedConcat]
  | cons v vs ih =>
    simp only [fixedConcat,List.length_append,v.property,ih,List.length_cons,Nat.mul_add,mul_one]
    omega

theorem fixed_concat_injective {n : ℕ} (hn : 0<n) : Function.Injective (@fixedConcat n) := by
  intro x
  induction x with
  | nil =>
    intro y h
    cases y with
    | nil => rfl
    | cons b bs =>
      have E := congrArg List.length h
      simp only [fixed_concat_length,List.length_nil,List.length_cons,Nat.mul_add,mul_one] at E
      omega
  | cons a as ih =>
    intro y h
    cases y with
    | nil =>
      have E := congrArg List.length h
      simp only [fixed_concat_length,List.length_nil,List.length_cons,Nat.mul_add,mul_one] at E
      omega
    | cons b bs =>
      have e := List.append_inj h (a.property.trans b.property.symm)
      rw [Subtype.ext e.1,ih e.2]

def axisSelector {a b : ℕ} (p : Page a b (Fin 64)) (i : Fin a) : Bool :=
  if h : (p.1.val i).1≠(p.1.val i).2 then p.2.2 ⟨i,h⟩ else false

def axisRecord {a b : ℕ} (p : Page a b (Fin 64)) (i : Fin a) : Word 13 :=
  ⟨encodeBits 6 (p.1.val i).1.val++
    (encodeBits 6 (p.1.val i).2.val++[axisSelector p i]),by simp [encodeBits_length]⟩

theorem axis_record_values {a b : ℕ} (p q : Page a b (Fin 64)) (i : Fin a)
    (h : axisRecord p i=axisRecord q i) :
    p.1.val i=q.1.val i ∧ axisSelector p i=axisSelector q i := by
  have H := congrArg Subtype.val h
  change encodeBits 6 (p.1.val i).1.val++(encodeBits 6 (p.1.val i).2.val++[axisSelector p i]) =
    encodeBits 6 (q.1.val i).1.val++(encodeBits 6 (q.1.val i).2.val++[axisSelector q i]) at H
  have first := List.append_inj H (by simp only [encodeBits_length])
  have second := List.append_inj first.2 (by simp only [encodeBits_length])
  have A := congrArg bitsValue first.1
  have B := congrArg bitsValue second.1
  rw [encodeBits_exact _ _ (p.1.val i).1.isLt,encodeBits_exact _ _ (q.1.val i).1.isLt] at A
  rw [encodeBits_exact _ _ (p.1.val i).2.isLt,encodeBits_exact _ _ (q.1.val i).2.isLt] at B
  exact ⟨Prod.ext (Fin.ext A) (Fin.ext B),(List.cons.inj second.2).1⟩

def pageWord {a b : ℕ} (width : ℕ) (p : Page a b (Fin 64)) : Word (width+13*a) :=
  ⟨encodeBits width p.2.1.val ++ fixedConcat (List.ofFn (axisRecord p)),by
    simp only [List.length_append,encodeBits_length,fixed_concat_length,List.length_ofFn]⟩

def pageCode {a b : ℕ} (width : ℕ) (p : Page a b (Fin 64)) : ℕ :=
  bitsValue (pageWord width p).val

theorem page_code_injective {a b : ℕ} (width : ℕ) (fit : b≤2^width) :
    Function.Injective (pageCode (a:=a) (b:=b) width) := by
  intro p q he
  have eq := little_bit_inj (pageWord width p).val (pageWord width q).val
    ((pageWord width p).property.trans (pageWord width q).property.symm) he
  have H := List.append_inj eq (by simp only [encodeBits_length])
  have Q := congrArg bitsValue H.1
  rw [encodeBits_exact _ _ (p.2.1.isLt.trans_le fit),encodeBits_exact _ _ (q.2.1.isLt.trans_le fit)] at Q
  have G := List.ofFn_injective ((fixed_concat_injective (by decide : 0<13)) H.2)
  have C (i : Fin a) := axis_record_values p q i (congrFun G i)
  have Z : p.1=q.1 := Subtype.ext (funext fun i=>(C i).1)
  rcases p with ⟨kp,ip,op⟩
  rcases q with ⟨kq,iq,oq⟩
  change kp=kq at Z
  subst kq
  have zi : ip=iq := Fin.ext Q
  subst iq
  have zo : op=oq := by
    funext j
    have t := (C j.val).2
    simpa only [axisSelector,dif_pos j.property] using t
  subst oq
  rfl

def serializeSeat {a b : ℕ} (width : ℕ) (seat : Physical a b (Fin 64)) :
    SeatWord (width+13*a) (a+1) :=
  ⟨pageWord width seat.1,natWord (a+1) seat.2.val⟩

theorem serialize_seat_exact {a b : ℕ} (width : ℕ) (seat : Physical a b (Fin 64)) :
    (serializeSeat width seat).represents (pageCode width) seat := by
  refine ⟨rfl,?_⟩
  change bitsValue (encodeBits (a+1) seat.2.val)=_
  apply encodeBits_exact
  exact seat.2.isLt.trans_le (by rw [pow_succ]; omega)

def serializeColumn {a b : ℕ} (width : ℕ) (f : Bool→Physical a b (Fin 64)) :
    PadColumnWord (width+13*a) (a+1) :=
  ⟨serializeSeat width (f false),serializeSeat width (f true)⟩

theorem serialize_column_exact {a b : ℕ} (width : ℕ) (f : Bool→Physical a b (Fin 64)) :
    (serializeColumn width f).represents (pageCode width) f :=
  ⟨serialize_seat_exact width (f false),serialize_seat_exact width (f true)⟩

#print axioms fixed_concat_length
#print axioms fixed_concat_injective
#print axioms axis_record_values
#print axioms page_code_injective
#print axioms serialize_seat_exact
#print axioms serialize_column_exact
end J6R23PaddingCensus
