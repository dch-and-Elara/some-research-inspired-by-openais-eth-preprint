import ACompactLayoutIncidence
import AAcquisitionCostNormalizer

/-! Executable serialization of fixed-width IDs and scan lookup of an
inverse incidence from a forward-only compact table. The proof knows
the table is bijective, but the executable scan does not use its inverse. -/
namespace ACompactLayout

def digits (width : ℕ) (value : ℕ) : List Bool :=
  List.ofFn fun i : Fin width => value.testBit i.val

theorem digits_injective_bounded (width : ℕ) {x y : ℕ}
    (hx : x<2^width) (hy : y<2^width) (h : digits width x=digits width y) : x=y := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i<width
  · have he := congrArg (fun l : List Bool => l[i]?) h
    simpa [digits,hi] using he
  · have hix := hx.trans_le (Nat.pow_le_pow_right (by decide) (by omega : width ≤ i))
    have hiy := hy.trans_le (Nat.pow_le_pow_right (by decide) (by omega : width ≤ i))
    rw [Nat.testBit_lt_two_pow hix,Nat.testBit_lt_two_pow hiy]

def wireDescriptor (width : ℕ) (tag : Fin 256) (row column address : ℕ) : List Bool :=
  digits 8 tag.val ++ digits width row ++ digits width column ++ digits width address

theorem wireDescriptor_length (width : ℕ) (tag : Fin 256) (row column address : ℕ) :
    (wireDescriptor width tag row column address).length=3*width+8 := by
  simp [wireDescriptor,digits]
  omega

def layoutStream (w : ℕ) (records : Fin (total w) → (Fin 256 × ℕ × ℕ × ℕ)) : List Bool :=
  false :: ((List.finRange (total w)).map fun i =>
    wireDescriptor (lambda w) (records i).1 (records i).2.1 (records i).2.2.1
      (records i).2.2.2).flatten

theorem layoutStream_budget (w : ℕ) (records : Fin (total w) → (Fin 256 × ℕ × ℕ × ℕ)) :
    (layoutStream w records).length ≤ 57*(w+2)^3 := by
  have hl (xs : List (Fin (total w))) :
      ((xs.map fun i =>
        wireDescriptor (lambda w) (records i).1 (records i).2.1 (records i).2.2.1
          (records i).2.2.2).flatten).length = xs.length*(3*lambda w+8) := by
    induction xs with
    | nil => simp
    | cons i is ih =>
      simp [wireDescriptor_length,ih,Nat.succ_mul,Nat.add_comm]
  unfold layoutStream
  rw [List.length_cons,hl,List.length_finRange,Nat.add_comm]
  exact layoutPayload_poly w

def readPort {n q m : ℕ} (width : ℕ) (read : Fin n × Fin q → Fin m) (key : Fin m) :
    Option (Fin n × Fin q) :=
  (List.ofFn fun i : Fin (n*q) => finProdFinEquiv.symm i).find? fun p =>
    (AAcquisitionCost.compareWord (digits width (read p).val) (digits width key.val)).1

theorem readPort_matches {n q m : ℕ} (width : ℕ) (fit : m≤2^width)
    (e : Fin n × Fin q ≃ Fin m) (key : Fin m) :
    readPort width e key=some (e.symm key) := by
  unfold readPort
  let xs := List.ofFn (fun i : Fin (n*q) => finProdFinEquiv.symm i)
  let p := fun (z : Fin n × Fin q) =>
    (AAcquisitionCost.compareWord (digits width (e z).val) (digits width key.val)).1
  have eTest (z : Fin n × Fin q) : p z=true ↔ e z=key := by
    unfold p
    rw [AAcquisitionCost.compareWord_exact,decide_eq_true_eq]
    constructor
    · intro h
      exact Fin.ext (digits_injective_bounded width ((e z).isLt.trans_le fit) (key.isLt.trans_le fit) h)
    · intro h
      rw [h]
  change xs.find? p=some (e.symm key)
  cases he : xs.find? p with
  | none =>
    have hm : e.symm key ∈ xs := by
      simp only [xs,List.mem_ofFn]
      exact ⟨finProdFinEquiv (e.symm key),finProdFinEquiv.symm_apply_apply _⟩
    have hh := (List.find?_eq_none.mp he) (e.symm key) hm
    exact (hh ((eTest _).2 (e.apply_symm_apply _))).elim
  | some z =>
    have hh := e.injective (((eTest z).1 (List.find?_some he)).trans (e.apply_symm_apply _).symm)
    rw [hh]

#print axioms digits_injective_bounded
#print axioms layoutStream_budget
#print axioms readPort_matches

end ACompactLayout
