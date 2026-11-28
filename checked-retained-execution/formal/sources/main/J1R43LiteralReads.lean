import J1R43LiteralCopies
import J1R14QueryBasis

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false

/-! Connect the stable actual occupancy to the original R14 copied
exceptional-basis measurements. This does not assume an abstract
prescribed word or that the rest of the jet has been evaluated. -/
namespace J1R43Literal
open scoped Polynomial BigOperators
open MainProbe J1R14Query J1MainSourceBridge J1MainSourcePlacement

section Index
variable {E : Type*} [DecidableEq E]

def literalPortOrder (es : List E) (all : ∀ e, e∈es) : E ↪ ℕ :=
  ⟨fun e=>es.idxOf e,fun {e f} h=>(List.idxOf_inj (all e) (all f)).mp h⟩

theorem literalPortOrder_value (es : List E) (all : ∀ e, e∈es) (e : E) :
    literalPortOrder es all e = es.idxOf e := rfl

end Index

section Printed
variable {I S X Copy Pin : Type*} [Fintype I] [DecidableEq I] [Fintype S] [LinearOrder S]
variable (D : DiagonalLayout I S X Copy Pin)
variable (width : ℕ) (hr : 2≤Fintype.card S) (hR : 32≤width) (hq : 6*width≤Fintype.card I)
local notation "J" => pubInterval (I:=I) (S:=S) width

include hr hR hq in
theorem printed_weight_zero_outside : 0∉J :=
  zero_not_mem_printedInterval hr hR hq

def sourceBasis : BasisFile (Basis:=Exceptional I S J) D :=
  printedBasis D J (printed_weight_zero_outside width hr hR hq)

variable [Fintype X] [DecidableEq X] [Fintype Copy]

theorem prescribed_printed_bit (t : I) (g : S) (E : Finset X)
    (y : RowValues S Copy (Exceptional I S J)) (x : X → Bool)
    (hx : x ∈ secondScan D (sourceBasis D width hr hR hq) t g E y)
    (p : Pin) (hg : (D.slot p).2 t=g) :
    x (D.pinVar p)=prescribed D (sourceBasis D width hr hR hq) t y p :=
  prescribed_of_fibre D (sourceBasis D width hr hR hq) t g E y x hx p hg

theorem actual_pin_factor_on_printed_fibre (t : I) (g : S) (E : Finset X) (f : ℚ[X])
    (y : RowValues S Copy (Exceptional I S J)) (x U : X → Bool)
    (hx : x ∈ secondScan D (sourceBasis D width hr hR hq) t g E y)
    (p : Pin) (hg : (D.slot p).2 t=g) (s : Bool) (node : I → ℚ) :
    pinFactor s (correctedArgument (sourceRow f node (D.slot p)) (node t)
      (embedded D (D.copy p) (fun j => boolRat (x j)))
      (embedded D (D.copy p) (fun j => boolRat (U j)))) =
    if s=prescribed D (sourceBasis D width hr hR hq) t y p then 1 else 0 := by
  rw [correctedArgument_pin,prescribed_printed_bit D width hr hR hq t g E y x hx p hg,
    pinFactor_on_bit]

variable [DecidableEq Pin]

theorem wrong_sign_original_group_zero (t : I) (g : S) (E : Finset X) (f : ℚ[X])
    (y : RowValues S Copy (Exceptional I S J))
    (tracked : Finset Pin) (U : X → Bool) (sigma : Pin → Bool)
    (other : (X → Bool) → ℚ[X]) (node : I → ℚ)
    (p : Pin) (hp : p ∈ ownedPins D t g tracked)
    (hwrong : sigma p ≠ prescribed D (sourceBasis D width hr hR hq) t y p) :
    sourceGroupProbe D J f node t g tracked
      (secondScan D (sourceBasis D width hr hR hq) t g E y) U
      (prescribed D (sourceBasis D width hr hR hq) t y) sigma other=0 :=
  sourceGroupProbe_off D J (printed_weight_zero_outside width hr hR hq) f node t g tracked
    (secondScan D (sourceBasis D width hr hR hq) t g E y) U
    (prescribed D (sourceBasis D width hr hR hq) t y) sigma other p hp hwrong

end Printed

#print axioms literalPortOrder_value
#print axioms printed_weight_zero_outside
#print axioms sourceBasis
#print axioms prescribed_printed_bit
#print axioms actual_pin_factor_on_printed_fibre
#print axioms wrong_sign_original_group_zero

end J1R43Literal