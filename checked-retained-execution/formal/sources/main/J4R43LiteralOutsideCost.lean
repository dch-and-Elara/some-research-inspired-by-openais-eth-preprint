import J4R43LiteralOutsideGeometry
import V8NativeMessageN7LiteralSupportOrientation
import J5R41LiteralChildCostRows

/-! Literal addresses for the outside evaluator. Each old column
enumerates its own Boolean arguments (not a full original cube).
Matching comparisons and the ring-input scalar have separate fees. -/
namespace J4R43LiteralOutside
open scoped Classical BigOperators Polynomial
open Polynomial P11FullPacking J6R10Repack J6R9PacketTiles J1MainSourceCollision
open Paper5.HybridClosure Paper5.D1Literal V8NativeMessage.N7LiteralSupport
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000

variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W×W)) (reg : ∀ v, GraphCutMoments.degree F v=3)

abbrev RealColumns := DOld F
abbrev RealArgs (u : DOld F) := ParentPorts (oldColumnNetwork F reg) (.inr u)
abbrev ColumnVisits := Σ u : RealColumns F,RealArgs F reg u→Bool
def writeVisits := ∑ u : DOld F,2^Nat.card (RealArgs F reg u)*(Nat.card (RealArgs F reg u)+1)

theorem physical_column_arity (u : DOld F) : Nat.card (RealArgs F reg u)≤3 := by
  rw [←Nat.card_congr (colPortsEquiv (oldColumnNetwork F reg) u),Nat.card_eq_fintype_card,
    Fintype.card_subtype]
  exact d_old_degree F reg u

theorem outside_column_count_exact : Nat.card (ColumnVisits F reg) =
    ∑ u : DOld F,2^Nat.card (RealArgs F reg u) := by
  rw [Nat.card_eq_fintype_card,Fintype.card_sigma]
  refine Finset.sum_congr rfl fun u _=>?_
  rw [Fintype.card_fun,Fintype.card_bool,Nat.card_eq_fintype_card]

theorem outside_local_term_count : Nat.card (ColumnVisits F reg)≤8*oldRowSize F := by
  rw [outside_column_count_exact]
  calc
    _ ≤ ∑ _ : DOld F,(8:ℕ) := Finset.sum_le_sum fun u _=>
      Nat.pow_le_pow_right (by decide) (physical_column_arity F reg u)
    _ = _ := by simp [oldRowSize,mul_comm]

theorem outside_local_product_count : writeVisits F reg≤32*oldRowSize F := by
  unfold writeVisits
  calc
    _ ≤ ∑ _ : DOld F,(32:ℕ) := by
      refine Finset.sum_le_sum fun u _=>?_
      have p := physical_column_arity F reg u
      exact Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) p) (Nat.succ_le_succ p)
    _ = _ := by simp [oldRowSize,mul_comm]

include reg in
/-- A simple direct prepared-chart scan compares each actual row address
with each actual column address; even this dense geometry pass is polynomial. -/
theorem actual_address_scan_count :
    Nat.card (DWire F×DWire F) = (24*Fintype.card W)^2 := by
  rw [Nat.card_prod,Nat.card_eq_fintype_card (α:=DWire F),d_physical_wire_count F reg,pow_two]

/-- Includes each inspected row/column comparison, each local table visit,
each local product update, and the final product. Separate explicit tariffs
cover one comparison, one local argument read, one ring operation, and
the source scalar construction. This is finite operation accounting,
not a byte-code or Turing tape implementation. -/
def outsideFee (comparison tableAccess ringOp sourceUnit : ℕ) : ℕ :=
  Nat.card (DWire F×DWire F)*comparison +
    Nat.card (ColumnVisits F reg)*tableAccess +
    (writeVisits F reg+Nat.card (ColumnVisits F reg)+oldRowSize F)*ringOp + sourceUnit

theorem actual_outside_fee (comparison tableAccess ringOp sourceUnit : ℕ) :
    outsideFee F reg comparison tableAccess ringOp sourceUnit≤
      (24*Fintype.card W)^2*comparison +
        (8*oldRowSize F)*tableAccess + (41*oldRowSize F)*ringOp + sourceUnit := by
  unfold outsideFee
  rw [actual_address_scan_count F reg]
  have h : writeVisits F reg+Nat.card (ColumnVisits F reg)+oldRowSize F≤41*oldRowSize F := by
    have one := outside_local_product_count F reg
    have two := outside_local_term_count F reg
    omega
  exact Nat.add_le_add_right (Nat.add_le_add
    (Nat.add_le_add_left (Nat.mul_le_mul_right _ (outside_local_term_count F reg)) _)
    (Nat.mul_le_mul_right _ h)) _

#print axioms physical_column_arity
#print axioms outside_column_count_exact
#print axioms outside_local_term_count
#print axioms outside_local_product_count
#print axioms actual_address_scan_count
#print axioms actual_outside_fee
end
end J4R43LiteralOutside

