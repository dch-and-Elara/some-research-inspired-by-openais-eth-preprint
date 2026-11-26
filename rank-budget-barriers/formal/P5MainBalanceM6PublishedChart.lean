import P5MainBalanceM6ExactBox
import P5MainIteratorPrinted

/-! Measurement box normalization, with no algorithm or asymptotic
parameters in the compiler's definitional-equality problem. -/
namespace P5MainBalance.M6
open P5MainBalance P5MainIterator
open scoped BigOperators Classical

variable {E W F Copy I B : Type*}
  [Fintype Copy] [Fintype I] [Fintype B] [LinearOrder B]

set_option maxHeartbeats 4000000 in
theorem exactBox_eq_copied_rows (keep : ℕ→Prop) (L : SourceLayout E W F Copy I B) :
    exactBox keep L =
      (2*Fintype.card (WordCell I B)+1)^(Fintype.card B*
        (Fintype.card Copy*Fintype.card (Exceptional (Unequal (I:=I) (B:=B)) keep))) := by
  unfold exactBox
  have hs : Fintype.card (NativeRows keep Copy I B) =
      Fintype.card (Exceptional (CoordFamily (Copy:=Copy) (I:=I) (B:=B)) keep) := by
    rfl
  rw [hs,literal_copied_rows (Copy:=Copy) (I:=I) (B:=B)]

#print axioms exactBox_eq_copied_rows
end P5MainBalance.M6
