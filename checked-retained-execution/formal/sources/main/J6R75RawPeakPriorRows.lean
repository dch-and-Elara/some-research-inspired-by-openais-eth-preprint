import J6R75RawPeakProbe
import J6R50NonModeScratchRetained

/-! The raw fold keeps precisely the earlier centre outputs while the
chosen actually emitted centre is evaluating its actual native group
callback. This proof uses the raw row list, not a reconstructed roster
or equality of a different interpreter's final result. -/
namespace J6R75RawPeak
open scoped Polynomial Classical
open Polynomial AOracleMachineTime A1R10 A1R12 J6R22Active
open J1PPrinted J6ActiveRun J6ActiveSchedule J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R16ModeCost J6R17ModeTape J6R24MeteredRecursion J6R25PreparedSupply J6R9Recursive
open J6R49DFS J6R49LiveBits J6R50NonModeScratch J6R68ActiveInputs.Sweep J6R68.HermiteWeightScratch

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxHeartbeats 4500000
set_option maxRecDepth 3800
set_option maxSynthPendingDepth 12

noncomputable section
variable {f : ℤ[X]} {ell s C q : ℕ}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {c : Call (PhysicalHost f ell)} {bank : Bank f}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)

theorem actual_raw_fold_and_current_group_have_one_earlier_output_prefix
    (d : Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c)
    (D : Schedule sel d bank q)
    (fits : q≤uniformWidth s C) (hq : 0<q) (hp : 0<c.prec) (hv : 0<ell) (hf : f.Monic)
    (child : ActiveChild (sel:=sel) (d:=d) bank)
    (x : D.EmitRow) (z : Probe S c) (β : NativeMenu (N sel) c (D.tag x)) (g : Fin 64) :
    let run := emittedCentreMeter D hq hp hv hf child
    let unitWidth := ell*((D.high hp).words.length*(c.prec+D.extra))
    ∃ (mode : NativeSuspension (C:=C) (sel:=sel) c) (pre post : List D.EmitRow),
      SawEmittedProbe d D hq hv child x z β g mode ∧
      actualEmittedCentreRows D=pre++x::post ∧
      D.highRun hq hp hv hf child=resumeUV (D.high hp).hp (pre.map run)
        (addM (D.high hp).hp (run x) (sumM (D.high hp).hp run post)) ∧
      (scalarTermsPayload (pre.map run)).length=pre.length*unitWidth ∧
      (scalarTermsPayload (pre.map run)).length≤D.stock.rows.length*unitWidth := by
  let run := emittedCentreMeter D hq hp hv hf child
  obtain ⟨mode,modeCut⟩ := every_emitted_row_address_has_its_native_cursor_and_group_cut d D
    fits hq hv child x z β g
  obtain ⟨pre,post,rows,resumeFold⟩ := selected_stock_row_is_an_actual_sweep_operand D hq hp hv hf child x
  have encoded :
      (scalarTermsPayload (pre.map run)).length=pre.length*(ell*((D.high hp).words.length*(c.prec+D.extra))) := by
    rw [scalar_terms_payload_exact,List.length_map]
  have n : (actualEmittedCentreRows D).length=D.stock.rows.length := by
    simp only [actualEmittedCentreRows,List.length_pmap]
  have prior : pre.length≤D.stock.rows.length := by
    rw [rows,List.length_append] at n
    exact (Nat.le_add_right _ _).trans_eq n
  exact ⟨mode,pre,post,modeCut,rows,resumeFold,encoded,
    encoded.le.trans (Nat.mul_le_mul_right _ prior)⟩

#print axioms actual_raw_fold_and_current_group_have_one_earlier_output_prefix
end
end J6R75RawPeak
