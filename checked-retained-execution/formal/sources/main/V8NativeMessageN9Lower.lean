import V8NativeMessageN9Rows
import V8NativeMessageLower

/-! Simultaneous fixed-coordinate row and actual child tapes for C2/N9.
One may select any finite subset of the signed centers at the coordinate. -/
namespace V8NativeMessage.Five
open scoped Classical BigOperators Polynomial
open Polynomial J6R9Recursive
open V8PooledMenu V8PooledMenu.FiveCopy V8PooledRange V8PooledRange.NativeOrigin

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000

variable {V E : Type} [Fintype V] [Fintype E] {G : Graph V E} {p : ThreePorts G}
  {f : ℤ[X]} {m : ℕ} (K : Pairs G m)
variable (P : Packing G p) (hu : 0<rootU V) (huM : rootU V≤wireSize V)
  (i : Fin (rootU V)) (T : Finset (Fin 64))
  (chosen : Finset (FixedSites hu huM (rootA V) i))
  (probes : Probes V f) (hf : f.Monic) (hd : 0<f.natDegree) (cross : Crosses K P i T)

include hd cross in
theorem matched_children (x y : Fin m → Bool) :
    fixedChildren P hu huM i chosen probes hf (activeSigns K x y) =
      decodeRowChildren P hu huM i T chosen
        (rowChildren P hu huM i T chosen (matchRow K P i T x)) (matchCol K P i T y) := by
  rw [← matchSigns K P i T cross]
  exact N9_fixed_row_native P hu huM i T chosen probes hf hd _ _

include hd cross in
/-- The receiver gets both original types of value and its own input.
This does not postulate that a central algorithm must use this interface. -/
theorem N9_needs_bits_exact {b : ℕ} (aux : (Fin m→Bool) → Fin b→Bool)
    (dec : (Fin m→Bool) → (Fin b→Bool) →
      FixedMenu P hu huM i (parityPrecision V) f → FixedChildrenMenu P hu huM i chosen f → ZMod 2)
    (correct : ∀ x y, dec y (aux x)
        (fixedNative P hu huM i (parityPrecision V) probes hf (activeSigns K x y))
        (fixedChildren P hu huM i chosen probes hf (activeSigns K x y)) =
      (originCount G p (activeSigns K x y):ZMod 2)) :
    m ≤ (2^rootA V / 2^i.val) + fixedChildBits P hu huM i chosen + b := by
  let msg (x : Fin m→Bool) :
      RowTape hu huM i (parityPrecision V) × RowChildTapes P hu huM i chosen × (Fin b→Bool) :=
    (rowMessage P hu huM i T (parityPrecision V) (matchRow K P i T x),
      rowChildren P hu huM i T chosen (matchRow K P i T x),aux x)
  have inj : Function.Injective msg := by
    intro x x' h
    have hr := congrArg Prod.fst h
    have hc := congrArg (fun v => v.2.1) h
    have ha := congrArg (fun v => v.2.2) h
    have hmain :
        fixedNative P hu huM i (parityPrecision V) probes hf (activeSigns K x x) =
        fixedNative P hu huM i (parityPrecision V) probes hf (activeSigns K x' x) := by
      rw [matched_receiver K P hu huM i T (parityPrecision V) probes hf hd cross,
        matched_receiver K P hu huM i T (parityPrecision V) probes hf hd cross]
      exact congrArg (fun z => rowDecoder P hu huM i T (parityPrecision V) probes z (matchCol K P i T x)) hr
    have ht : fixedChildren P hu huM i chosen probes hf (activeSigns K x x) =
        fixedChildren P hu huM i chosen probes hf (activeSigns K x' x) := by
      rw [matched_children K P hu huM i T chosen probes hf hd cross,
        matched_children K P hu huM i T chosen probes hf hd cross]
      exact congrArg (fun z => decodeRowChildren P hu huM i T chosen z (matchCol K P i T x)) hc
    by_contra hn
    have hh : dec x (aux x)
          (fixedNative P hu huM i (parityPrecision V) probes hf (activeSigns K x x))
          (fixedChildren P hu huM i chosen probes hf (activeSigns K x x)) =
        dec x (aux x')
          (fixedNative P hu huM i (parityPrecision V) probes hf (activeSigns K x' x))
          (fixedChildren P hu huM i chosen probes hf (activeSigns K x' x)) := by
      change aux x=aux x' at ha
      rw [ha,hmain,ht]
    have ee := (correct x x).symm.trans (hh.trans (correct x' x))
    rw [C2_parity K p x x,C2_parity K p x' x,if_pos rfl,if_neg (Ne.symm hn)] at ee
    exact one_ne_zero ee
  have hc := Fintype.card_le_of_injective msg inj
  rw [Fintype.card_prod,Fintype.card_prod,N8_row_alphabet hu huM i (parityPrecision V),
    fixed_child_tapes_card P hu huM i chosen] at hc
  apply (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp
  simpa [Fintype.card_fun,Fintype.card_bool,pow_add,parityPrecision,fixedBits,triangle,Nat.mul_assoc] using hc

include hd cross in
theorem N9_needs_bits {b : ℕ} (aux : (Fin m→Bool) → Fin b→Bool)
    (dec : (Fin m→Bool) → (Fin b→Bool) →
      FixedMenu P hu huM i (parityPrecision V) f → FixedChildrenMenu P hu huM i chosen f → ZMod 2)
    (correct : ∀ x y, dec y (aux x)
        (fixedNative P hu huM i (parityPrecision V) probes hf (activeSigns K x y))
        (fixedChildren P hu huM i chosen probes hf (activeSigns K x y)) =
      (originCount G p (activeSigns K x y):ZMod 2)) :
    m ≤ (2^rootA V / 2^i.val) + chosen.card *
      (64+(12*wireSize V)/(2^rootA V / 2^i.val)) + b := by
  have e := N9_needs_bits_exact K P hu huM i T chosen probes hf hd cross aux dec correct
  have hb := fixed_child_budget P hu huM i chosen
  omega

include hd cross in
theorem N9_some_failure {b : ℕ} (aux : (Fin m→Bool) → Fin b→Bool)
    (dec : (Fin m→Bool) → (Fin b→Bool) →
      FixedMenu P hu huM i (parityPrecision V) f → FixedChildrenMenu P hu huM i chosen f → ZMod 2)
    (small : (2^rootA V / 2^i.val) + chosen.card *
      (64+(12*wireSize V)/(2^rootA V / 2^i.val)) + b < m) :
    ∃ x y, dec y (aux x)
        (fixedNative P hu huM i (parityPrecision V) probes hf (activeSigns K x y))
        (fixedChildren P hu huM i chosen probes hf (activeSigns K x y)) ≠
      (originCount G p (activeSigns K x y):ZMod 2) := by
  by_contra! h
  exact (not_le_of_gt small) (N9_needs_bits K P hu huM i T chosen probes hf hd cross aux dec h)

#print axioms matched_children
#print axioms N9_needs_bits_exact
#print axioms N9_needs_bits
#print axioms N9_some_failure
end
end V8NativeMessage.Five