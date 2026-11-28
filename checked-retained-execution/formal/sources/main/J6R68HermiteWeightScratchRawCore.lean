import J6R68ActiveInputsSweepCore
import J6R50NonModeScratchRetained

/-! Pure access to one actual emitted centre in the raw sweep.
No Classical.proofRow, new controller, or alternate jet producer is
inserted into the reference evaluation. -/
namespace J6R68.HermiteWeightScratch
open scoped Polynomial Classical
open Polynomial AOracleMachineTime A1R10 A1R11 A1R12 J6R22Active
open J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R23ScheduleWeight J6R24MeteredRecursion J6R49DFS
open J6R50NonModeScratch J6R68ActiveInputs J6R68ActiveInputs.Sweep

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxHeartbeats 11500000
set_option maxRecDepth 4000
set_option maxSynthPendingDepth 12

private theorem at_member {A : Type*} (x : A) (xs : List A) (h : x∈xs) :
    ∃ pre post,xs=pre++x::post := by
  induction xs with
  | nil => simp at h
  | cons y ys ih =>
    rcases List.mem_cons.mp h with eq|inTail
    · subst y
      exact ⟨[],ys,rfl⟩
    · obtain ⟨pre,post,eq⟩ := ih inTail
      exact ⟨y::pre,post,congrArg (y::·) eq⟩

noncomputable section
attribute [local irreducible] J6R12Blueprint.printedParams
variable {f : ℤ[X]} {ell s q : ℕ} {c : Call (PhysicalHost f ell)}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {d : Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c}
variable {bank : Bank f}
variable (D : Schedule sel d bank q)
local notation "S" => (printedParams (f:=f) (ell:=ell) s)

def actualEmittedCentreRows : List D.EmitRow :=
  D.stock.rows.pmap (fun x hx=>⟨x,hx⟩) (fun _ hx=>hx)

def emittedCentreMeter (hq : 0<q) (hp : 0<c.prec) (hv : 0<ell) (hf : f.Monic)
    (child : ActiveChild (sel:=sel) (d:=d) bank) (x : D.EmitRow) :
    Meter (Block (D.high hp) ell) :=
  (D.fetch x).runCentre hq hv hf (D.high hp) D.extra (child (D.tag x))

theorem raw_sweep_uses_its_real_emitted_rows_without_a_proof_lookup
    (hq : 0<q) (hp : 0<c.prec) (hv : 0<ell) (hf : f.Monic)
    (child : ActiveChild (sel:=sel) (d:=d) bank) :
    D.highRun hq hp hv hf child=
      sumM (D.high hp).hp (emittedCentreMeter D hq hp hv hf child) (actualEmittedCentreRows D) := by
  unfold Schedule.highRun actualEmittedCentreRows
  exact raw_fold_meter_is_in_the_emission_order _ _
    (fun x hx=>(⟨x,hx⟩ : D.EmitRow)) (emittedCentreMeter D hq hp hv hf child) _ _ (fun _ _=>rfl)

theorem selected_stock_row_is_an_actual_sweep_operand
    (hq : 0<q) (hp : 0<c.prec) (hv : 0<ell) (hf : f.Monic)
    (child : ActiveChild (sel:=sel) (d:=d) bank) (x : D.EmitRow) :
    let run := emittedCentreMeter D hq hp hv hf child
    ∃ pre post,actualEmittedCentreRows D=pre++x::post ∧
      D.highRun hq hp hv hf child=
        resumeUV (D.high hp).hp (pre.map run)
          (addM (D.high hp).hp (run x) (sumM (D.high hp).hp run post)) := by
  have hit : x∈actualEmittedCentreRows D := by
    rcases x with ⟨row,has⟩
    exact List.mem_pmap_of_mem has
  obtain ⟨pre,post,listEq⟩ := at_member x _ hit
  refine ⟨pre,post,listEq,?_⟩
  rw [raw_sweep_uses_its_real_emitted_rows_without_a_proof_lookup D hq hp hv hf child,listEq]
  exact scalar_sum_retains_actual_heads (D.high hp).hp (emittedCentreMeter D hq hp hv hf child) pre (x::post)

theorem emitted_row_consumes_its_literal_jet_roster_margin_and_frames
    (hq : 0<q) (hp : 0<c.prec) (hv : 0<ell) (hf : f.Monic)
    (child : ActiveChild (sel:=sel) (d:=d) bank) (x : D.EmitRow) :
    let J := D.fetch x
    let high := D.high hp
    let jet := J.centreJet hq hv (child (D.tag x))
    let step := fun j=>termM J.low.hp J.low.sizePos high.hp high.sizePos hv
      ((J.low.natDegree hf).trans (high.natDegree hf).symm)
      jet.result ((printedParams (f:=f) (ell:=ell) s).levelBits c.depth) D.extra j (D.tag x).val J.roster.rows
    let out := sumM high.hp step (List.range J.window)
    emittedCentreMeter D hq hp hv hf child x=
      ⟨out.result,J.tape.steps+jet.steps+out.steps+
        tapeFee J.low.words.length ell (registerPrecision S c (D.tag x)) J.window+4⟩ := rfl

#print axioms raw_sweep_uses_its_real_emitted_rows_without_a_proof_lookup
#print axioms selected_stock_row_is_an_actual_sweep_operand
#print axioms emitted_row_consumes_its_literal_jet_roster_margin_and_frames
end
end J6R68.HermiteWeightScratch
