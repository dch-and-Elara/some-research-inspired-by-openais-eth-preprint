
import A2R45LiteralInput

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1900000
set_option linter.unusedSectionVars false

/-! A concrete packed read of the pair row or the four-port copy row.
The address is an actual row index times a fixed table width. -/
namespace A2R45Literal
open FixedHostAcquisition AAcquisitionCost
open scoped Classical

variable {n : ℕ}

def copyBitAddress (x : Bool×Bool→Bool) : Fin 16 :=
  ⟨(x (false,false)).toNat + 2*(x (false,true)).toNat +
    4*(x (true,false)).toNat + 8*(x (true,true)).toNat,by
      cases x (false,false) <;> cases x (false,true) <;>
        cases x (true,false) <;> cases x (true,true) <;> decide⟩

theorem fourPort_read_copy_address (x : Bool×Bool→Bool) :
    fourPort (copyBitAddress x)=x := by
  funext i
  rcases i with ⟨a,b⟩
  cases h₀ : x (false,false) <;> cases h₁ : x (false,true) <;>
    cases h₂ : x (true,false) <;> cases h₃ : x (true,true) <;> cases a <;> cases b <;>
      simp [fourPort,copyBitAddress,h₀,h₁,h₂,h₃] <;> decide

def copyRowAddress (l : Link n) : Fin ((n+1)*n) :=
  ⟨l.1.val*n+l.2.val,by
    calc
      _ < l.1.val*n+n := Nat.add_lt_add_left l.2.isLt _
      _ = (l.1.val+1)*n := by rw [Nat.add_mul,one_mul]
      _ ≤ _ := Nat.mul_le_mul_right n l.1.isLt⟩

theorem copyRowAddress_injective (n : ℕ) : Function.Injective (copyRowAddress (n:=n)) := by
  intro a b h
  have hv : a.1.val*n+a.2.val=b.1.val*n+b.2.val := congrArg Fin.val h
  have h₀ := congrArg (fun z : ℕ=>z%n) hv
  have hp₀ (x : Link n) : (x.1.val*n+x.2.val)%n=x.2.val := by
    rw [Nat.add_comm,Nat.add_mul_mod_self_right,Nat.mod_eq_of_lt x.2.isLt]
  have hj : a.2.val=b.2.val := by simpa only [hp₀] using h₀
  have hn : 0<n := lt_of_le_of_lt (Nat.zero_le _) a.2.isLt
  have h₁ : a.1.val*n=b.1.val*n := by omega
  exact Prod.ext (Fin.ext (Nat.eq_of_mul_eq_mul_right hn h₁)) (Fin.ext hj)

theorem fixed_copy_word_at (k i : ℕ) (hi : i<k) (j : Fin 16) :
    ((List.replicate k copyWord).flatten)[16*i+j.val]? = some (publicCopyAt j) := by
  induction k generalizing i with
  | zero => omega
  | succ k ih =>
    rw [List.replicate_succ,List.flatten_cons]
    cases i with
    | zero =>
      have hh : j.val<copyWord.length := by rw [copyWord_length]; exact j.isLt
      simpa only [Nat.mul_zero,Nat.zero_add,List.getElem?_append_left hh] using copyWord_get j
    | succ i =>
      have hh : copyWord.length ≤ 16*(i+1)+j.val := by rw [copyWord_length]; omega
      rw [List.getElem?_append_right hh]
      have hz : 16*(i+1)+j.val-copyWord.length=16*i+j.val := by rw [copyWord_length]; omega
      rw [hz]
      exact ih i (by omega)

def rowBitAddress (w : Input n) : (r : Row n) → (WireAt r→Bool) → ℕ
  | .inl p, x => 4*(pairAddress p).val+(pairBitAddress x).val
  | .inr l, x => 4*w.bits.length+16*(copyRowAddress l).val+(copyBitAddress x).val

def serializedRead (w : Input n) (r : Row n) (x : WireAt r→Bool) : Bool :=
  ((compileA2Rows n w.bits)[rowBitAddress w r x]?).getD false

theorem pair_cell_reads_tape (w : Input n) (p : Pair n) (x : Bool→Bool) :
    (compileA2Rows n w.bits)[rowBitAddress w (.inl p) x]? =
      some (switchAt (w.enabled p) (pairBitAddress x)) := by
  change (switchPayload w.bits ++ (List.replicate ((n+1)*n) copyWord).flatten)[4*(pairAddress p).val+(pairBitAddress x).val]? = _
  have hi : (pairAddress p).val<w.bits.length := by rw [w.fits]; exact (pairAddress p).isLt
  have hj := (pairBitAddress x).isLt
  have hlt : 4*(pairAddress p).val+(pairBitAddress x).val < (switchPayload w.bits).length := by
    rw [switchPayload_length]
    omega
  rw [List.getElem?_append_left hlt,switchPayload_get,w.bit_read]
  rfl

theorem copy_cell_reads_tape (w : Input n) (l : Link n) (x : Bool×Bool→Bool) :
    (compileA2Rows n w.bits)[rowBitAddress w (.inr l) x]? = some (publicCopyAt (copyBitAddress x)) := by
  change (switchPayload w.bits ++ (List.replicate ((n+1)*n) copyWord).flatten)[4*w.bits.length+16*(copyRowAddress l).val+(copyBitAddress x).val]? = _
  have hge : (switchPayload w.bits).length≤4*w.bits.length+
      16*(copyRowAddress l).val+(copyBitAddress x).val := by rw [switchPayload_length]; omega
  rw [List.getElem?_append_right hge]
  have hdiff : 4*w.bits.length+16*(copyRowAddress l).val+(copyBitAddress x).val-
      (switchPayload w.bits).length=16*(copyRowAddress l).val+(copyBitAddress x).val := by
    rw [switchPayload_length]
    omega
  rw [hdiff]
  exact fixed_copy_word_at _ _ (copyRowAddress l).isLt _

theorem serializedRead_truth {K : Type*} [CommRing K]
    (w : Input n) (r : Row n) (x : WireAt r→Bool) :
    Acquisition.bit (K:=K) (serializedRead w r x)=rowTable w.enabled r x := by
  unfold serializedRead
  cases r with
  | inl p =>
    rw [pair_cell_reads_tape]
    exact switchAt_truth (w.enabled p) x
  | inr l =>
    rw [copy_cell_reads_tape]
    change Acquisition.bit (K:=K) (publicCopyAt (copyBitAddress x))=copyTable x
    rw [publicCopyAt_truth,fourPort_read_copy_address]

theorem switched_row_changes_exact_cell (f : Pair n→Bool) (p q : Pair n) (x : Bool→Bool) :
    serializedRead (Input.encode (setSwitch f p false)) (.inl q) x ≠
      serializedRead (Input.encode (setSwitch f p true)) (.inl q) x ↔
      q=p ∧ (pairBitAddress x).val=3 := by
  unfold serializedRead
  rw [pair_cell_reads_tape,pair_cell_reads_tape,Input.encode_enabled,Input.encode_enabled]
  by_cases h : q=p
  · simp only [setSwitch,h,if_true,Option.getD_some,true_and]
    exact switchAt_change_address _
  · simp [setSwitch,h]

theorem copy_tape_unchanged (w w' : Input n) (l : Link n) (x : Bool×Bool→Bool) :
    serializedRead w (.inr l) x=serializedRead w' (.inr l) x := by
  unfold serializedRead
  rw [copy_cell_reads_tape,copy_cell_reads_tape]

#print axioms fourPort_read_copy_address
#print axioms copyRowAddress_injective
#print axioms fixed_copy_word_at
#print axioms pair_cell_reads_tape
#print axioms copy_cell_reads_tape
#print axioms serializedRead_truth
#print axioms switched_row_changes_exact_cell
#print axioms copy_tape_unchanged
end A2R45Literal
