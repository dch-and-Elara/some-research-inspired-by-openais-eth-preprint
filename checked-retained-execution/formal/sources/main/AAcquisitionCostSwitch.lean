import FixedHostAcquisition

/-! A2: literal serialized old-row tables. The graph-dependent input is
one bit per potential edge, in the public pair order. The compiler scans
that bit list and writes four bits per pair; the 16-entry equality-copy
rows are fixed. This does not charge the value of the queried register. -/

namespace AAcquisitionCost
open FixedHostAcquisition

def pairOrder (n : ℕ) : List (Pair n) :=
  (List.finRange (n+1)).flatMap fun i =>
    (List.finRange (n+1)).filterMap fun j =>
      if h : i < j then some ⟨(i,j),h⟩ else none

theorem pairOrder_complete (n : ℕ) (p : Pair n) : p ∈ pairOrder n := by
  refine List.mem_flatMap.mpr ⟨p.1.1, List.mem_finRange _, ?_⟩
  exact List.mem_filterMap.mpr ⟨p.1.2, List.mem_finRange _, dif_pos p.2⟩

def switchAt (enabled : Bool) (address : Fin 4) : Bool :=
  if address.val = 3 then !enabled else true

def pairBitAddress (y : Bool → Bool) : Fin 4 :=
  ⟨(if y false then 2 else 0)+(if y true then 1 else 0), by
    cases y false <;> cases y true <;> decide⟩

theorem switchAt_truth {K : Type*} [CommRing K] (enabled : Bool) (y : Bool → Bool) :
    Acquisition.bit (K := K) (switchAt enabled (pairBitAddress y)) =
      switchTable enabled y := by
  cases enabled <;> cases h0 : y false <;> cases h1 : y true <;>
    simp [switchAt, pairBitAddress, Acquisition.bit, switchTable,
      Acquisition.nandTable, h0, h1]

theorem switchAt_change_address (j : Fin 4) :
    switchAt false j ≠ switchAt true j ↔ j.val = 3 := by
  by_cases h : j.val = 3 <;> simp [switchAt,h]

def switchWord (enabled : Bool) : List Bool := [true,true,true,!enabled]

theorem switchWord_get (enabled : Bool) (j : Fin 4) :
    (switchWord enabled)[j.val]? = some (switchAt enabled j) := by
  fin_cases j <;> simp [switchWord,switchAt]

def switchPayload : List Bool → List Bool
  | [] => []
  | b::bs => switchWord b ++ switchPayload bs

theorem switchPayload_length (bits : List Bool) :
    (switchPayload bits).length = 4*bits.length := by
  induction bits with
  | nil => rfl
  | cons b bs ih => simp [switchPayload,switchWord,ih]; omega

theorem switchPayload_get (bits : List Bool) (i : ℕ) (j : Fin 4) :
    (switchPayload bits)[4*i+j.val]? = (bits[i]?).map (fun b => switchAt b j) := by
  induction bits generalizing i with
  | nil => simp [switchPayload]
  | cons b bs ih =>
    cases i with
    | zero =>
      have h : j.val < (switchWord b).length := by simp [switchWord]
      simpa only [switchPayload, Nat.mul_zero, Nat.zero_add,
        List.getElem?_append_left h,List.getElem?_cons_zero,Option.map_some]
        using switchWord_get b j
    | succ i =>
      have h : (switchWord b).length ≤ 4*(i+1)+j.val := by simp [switchWord]; omega
      rw [switchPayload,List.getElem?_append_right h,List.getElem?_cons_succ]
      have hi : 4*(i+1)+j.val - (switchWord b).length = 4*i+j.val := by
        simp [switchWord]; omega
      rw [hi,ih]

def originalInput (n : ℕ) (enabled : Pair n → Bool) : List Bool :=
  (pairOrder n).map enabled

theorem source_pair_table_exact {K : Type*} [CommRing K] {n i : ℕ} {p : Pair n}
    (enabled : Pair n → Bool) (h : (pairOrder n)[i]? = some p) (y : Bool → Bool) :
    ((switchPayload (originalInput n enabled))[4*i+(pairBitAddress y).val]?).map
        (Acquisition.bit (K := K)) = some (rowTable enabled (.inl p) y) := by
  rw [switchPayload_get]
  simp [originalInput,List.getElem?_map,h,switchAt_truth,rowTable]

/-- Index 0,1,2,3 in the tuple order FF, FT, TF, TT. -/
def fourPort (address : Fin 16) (p : Bool × Bool) : Bool :=
  address.val.testBit ((if p.1 then 2 else 0)+(if p.2 then 1 else 0))

def publicCopyAt (address : Fin 16) : Bool :=
  let y := fourPort address
  (y (false,false) && y (false,true)) == (y (true,false) && y (true,true))

theorem publicCopyAt_truth {K : Type*} [CommRing K] (address : Fin 16) :
    Acquisition.bit (K := K) (publicCopyAt address) = copyTable (fourPort address) := by
  simp [publicCopyAt,Acquisition.bit,copyTable]

def copyWord : List Bool := (List.finRange 16).map publicCopyAt

theorem copyWord_length : copyWord.length = 16 := by simp [copyWord]

theorem copyWord_get (address : Fin 16) :
    copyWord[address.val]? = some (publicCopyAt address) := by
  fin_cases address <;> decide

def compileA2Rows (n : ℕ) (bits : List Bool) : List Bool :=
  switchPayload bits ++ (List.replicate ((n+1)*n) copyWord).flatten

inductive BitOp where
  | read (value : Bool)
  | flip
  | write (value : Bool)
  deriving DecidableEq

def emitted (ops : List BitOp) : List Bool :=
  ops.filterMap fun op => match op with | .write b => some b | _ => none

def consumed (ops : List BitOp) : List Bool :=
  ops.filterMap fun op => match op with | .read b => some b | _ => none

def switchTrace : List Bool → List BitOp
  | [] => []
  | b::bs => [.read b,.flip,.write true,.write true,.write true,.write (!b)] ++ switchTrace bs

def a2Trace (n : ℕ) (bits : List Bool) : List BitOp :=
  switchTrace bits ++ (List.replicate ((n+1)*n) (copyWord.map BitOp.write)).flatten

theorem switchTrace_exact (bits : List Bool) :
    consumed (switchTrace bits) = bits ∧
    emitted (switchTrace bits) = switchPayload bits ∧
    (switchTrace bits).length = 6*bits.length := by
  induction bits with
  | nil => decide
  | cons b bs ih =>
    obtain ⟨hread,hwrite,hcost⟩ := ih
    refine ⟨?_,?_,?_⟩
    · change b :: consumed (switchTrace bs) = b :: bs
      rw [hread]
    · change true :: true :: true :: (!b) :: emitted (switchTrace bs) =
        true :: true :: true :: (!b) :: switchPayload bs
      rw [hwrite]
    · change (switchTrace bs).length + 6 = 6*(bs.length+1)
      rw [hcost]
      omega

theorem fixed_copy_trace (k : ℕ) :
    consumed ((List.replicate k (copyWord.map BitOp.write)).flatten) = [] ∧
    emitted ((List.replicate k (copyWord.map BitOp.write)).flatten) =
      (List.replicate k copyWord).flatten ∧
    ((List.replicate k (copyWord.map BitOp.write)).flatten).length = 16*k := by
  have hr : consumed (copyWord.map BitOp.write) = [] := by simp [consumed,List.filterMap_map]
  have hw : emitted (copyWord.map BitOp.write) = copyWord := by
    simp [emitted,List.filterMap_map,Function.comp_def]
  induction k with
  | zero => decide
  | succ k ih =>
    simp only [List.replicate_succ,List.flatten_cons]
    have cr (a b : List BitOp) : consumed (a++b) = consumed a ++ consumed b :=
      List.filterMap_append
    have wr (a b : List BitOp) : emitted (a++b) = emitted a ++ emitted b :=
      List.filterMap_append
    rw [cr,wr,hr,hw,ih.1,ih.2.1,List.nil_append,List.length_append,List.length_map,copyWord_length,ih.2.2]
    exact ⟨rfl,rfl,by omega⟩

theorem a2Trace_exact (n : ℕ) (bits : List Bool) :
    consumed (a2Trace n bits) = bits ∧ emitted (a2Trace n bits) = compileA2Rows n bits ∧
    (a2Trace n bits).length = 6*bits.length+16*((n+1)*n) := by
  have hc : consumed (a2Trace n bits) =
      consumed (switchTrace bits) ++ consumed ((List.replicate ((n+1)*n)
        (copyWord.map BitOp.write)).flatten) := List.filterMap_append
  have he : emitted (a2Trace n bits) =
      emitted (switchTrace bits) ++ emitted ((List.replicate ((n+1)*n)
        (copyWord.map BitOp.write)).flatten) := List.filterMap_append
  obtain ⟨r,w,c⟩ := switchTrace_exact bits
  obtain ⟨cr,cw,cc⟩ := fixed_copy_trace ((n+1)*n)
  refine ⟨by rw [hc,r,cr,List.append_nil],by rw [he,w,cw]; rfl,?_⟩
  rw [a2Trace,List.length_append,c,cc]

/-- Here the explicit input budget includes named vertices, even when
the supplied switch list is empty. No free random access is used. -/
theorem a2Trace_quadratic (n : ℕ) (bits : List Bool) :
    (a2Trace n bits).length ≤ 22*(bits.length+n+1)^2 := by
  let S := bits.length+n+1
  have hn : n+1 ≤ S := by dsimp [S]; omega
  have hlen : bits.length ≤ S := by dsimp [S]; omega
  have hprod : (n+1)*n ≤ S*S := Nat.mul_le_mul hn (by omega)
  have hS : S ≤ S*S := by simpa using Nat.mul_le_mul_left S (show 1 ≤ S by dsimp [S]; omega)
  rw [(a2Trace_exact n bits).2.2]
  change _ ≤ 22*S^2
  rw [pow_two]
  omega

#print axioms pairOrder_complete
#print axioms switchAt_truth
#print axioms switchAt_change_address
#print axioms source_pair_table_exact
#print axioms publicCopyAt_truth
#print axioms copyWord_get
#print axioms a2Trace_exact
#print axioms a2Trace_quadratic

end AAcquisitionCost
