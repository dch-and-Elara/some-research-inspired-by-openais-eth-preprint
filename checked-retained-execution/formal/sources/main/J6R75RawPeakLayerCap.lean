import J6R75RawPeakLayer
import J6R50PeakAbsoluteCaps
import J6R52PeakModePath

/-! Numeric reserve for the same selected layer: literal raw centre
table, already returned centre blocks, current native mode cursor
and group product, its weight words, and its physical roster. -/
namespace J6R75RawPeak
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R22Active
open J6R63Active J6R62ActivePrep J6R64Active J6R66Active
open J6R51Online J6R48DFS J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6ActiveRun J6ActiveSchedule J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R9Recursive J6R16ModeCost J6R24MeteredRecursion J6R49DFS J6R49LiveBits
open J6R68ActiveInputs.Sweep J6R68.HermiteWeightScratch J6R68.RecursivePeak
open J6R50NonModeScratch J6R50Peak J6R52Peak

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option quotPrecheck false
set_option maxRecDepth 4300
set_option maxHeartbeats 4700000

noncomputable section
variable {f : ℤ[X]} {ell s C q : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)

def selectedRawLayerRoof (s C q ell e low high : ℕ) : ℕ :=
  (q+(Nat.clog 2 s+1+q)*2^(Nat.clog 2 s+1))+
    (2^(Nat.clog 2 s+1))*(ell*(e*high))+
    (absoluteModeCap s C ell e low+weightCap s C low+suspendedRosterCap s C low)

theorem selected_raw_parent_fields_fit_the_absolute_layer_roof
    (p : Path sel r c) (a : (S).cutoff<c.edges)
    (D : Schedule sel (readyAtPath T p a) T.bank q)
    (hq : 0<q) (hp : 0<c.prec) (hv : 0<ell)
    (child : ActiveChild (sel:=sel) (d:=readyAtPath T p a) T.bank)
    (mode : NativeSuspension (C:=C) (sel:=sel) c) (pre : List D.EmitRow)
    (high : ℕ) (highAt : c.prec+D.extra≤high) (prefixFit : pre.length≤D.stock.rows.length) :
    selectedParentBits (readyAtPath T p a) D hq hp hv hf child mode pre≤
      selectedRawLayerRoof s C q ell f.natDegree (absolutePrecision s r.edges r.prec) high := by
  let grid := 2^(Nat.clog 2 s+1)
  have axis : (S).levelBits c.depth≤Nat.clog 2 s := bits_le_lam _ _
  have menu : D.stock.rows.length≤grid :=
    (stock_sweep_rows_bounded_by_actual_printed_grid D).trans
      (Nat.pow_le_pow_right (by decide) (Nat.add_le_add_right axis _))
  have stock : rawStockBits D.stock≤q+(Nat.clog 2 s+1+q)*grid := by
    rw [exact_sweep_stock_width D]
    exact Nat.add_le_add_left (Nat.mul_le_mul (Nat.add_le_add_right (Nat.add_le_add_right axis _) _) menu) _
  have prefixBound :
      (scalarTermsPayload (pre.map (emittedCentreMeter D hq hp hv hf child))).length≤
        grid*(ell*(f.natDegree*high)) := by
    rw [scalar_terms_payload_exact,List.length_map,(D.high hp).natDegree hf]
    exact Nat.mul_le_mul (prefixFit.trans menu)
      (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ highAt))
  have modeCap := mode_selected_payload_absolute T p mode
  have weight := actual_site_weight_bits T p mode
  have roster := actual_suspended_roster_has_absolute_selected_cap T p mode
  exact Nat.add_le_add (Nat.add_le_add stock prefixBound)
    (Nat.add_le_add (Nat.add_le_add modeCap weight) roster)

#print axioms selected_raw_parent_fields_fit_the_absolute_layer_roof
end
end J6R75RawPeak
