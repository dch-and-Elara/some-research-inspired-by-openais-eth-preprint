import J6R25PreparedSupplyPrepared

/-! Per live native call, generation is charged just once per centre,
before the original probe × mode × group loops use that resident batch.
The replay with already produced batches is proof-side only. The
ordered structural equality is stronger than equality of menu sizes. -/
namespace J6R25PreparedSupply
open scoped Polynomial
open Polynomial A1R10 A1R12 AOracleMachineTime
open J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R16ModeCost J6R17ModeTape J1PPrinted J6R21Ancestor J6R22Active J6R23ScheduleWeight
open J6R19Retained J6R24MeteredRecursion

variable {f : ℤ[X]} {ell s C : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
variable (T : Input cfg sel r hf)
variable {c : Call (PhysicalHost f ell)}
variable (hc : NativeReach (Plan sel) r c)
variable {d : Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c}
variable (G : ActiveInput d T.bank)
variable (hp : 0<c.prec)

def Input.modeFee : ℕ :=
  (G.centres.map (fun t=>(T.draw hc d t).steps)).sum

noncomputable def Input.highFunded (child : ActiveChild (sel:=sel) (d:=d) T.bank) :
    Meter (Block ((T.activeDesc hc G).high hp) ell) :=
  let D := T.activeDesc hc G
  let H := D.high hp
  sumM H.hp (fun t=>
    let emitted := T.draw hc d t
    let centre := (D.tape t).centre T.vPositive hf H D.extraPrecision (child t)
    padCost centre emitted.steps) G.centres

noncomputable def Input.fundedOpt (child : ActiveChild (sel:=sel) (d:=d) T.bank) :
    Meter (Option (Block (T.bank c.prec hp) ell)) :=
  let D := T.activeDesc hc G
  let H := D.high hp
  let high := T.highFunded hc G hp child
  let z := stripUVLoop ((H.natDegree hf).trans ((T.bank c.prec hp).natDegree hf).symm) high.result
  ⟨z.result,high.steps+z.steps+4⟩

noncomputable def Input.fundedEval (child : ActiveChild (sel:=sel) (d:=d) T.bank) :
    Meter (Block (T.bank c.prec hp) ell) :=
  checkedWord (zeroM (T.bank c.prec hp).hp) (T.fundedOpt hc G hp child)

set_option maxHeartbeats 2800000 in
theorem Input.funded_extra_exact (child : ActiveChild (sel:=sel) (d:=d) T.bank) :
    Delta (T.fundedEval hc G hp child)
      ((T.activeDesc hc G).eval hp T.vPositive hf child) (T.modeFee hc G) := by
  let D := T.activeDesc hc G
  let H := D.high hp
  let K := fun t=>(D.tape t).centre T.vPositive hf H D.extraPrecision (child t)
  let F := fun t=>(T.draw hc d t).steps
  have high : Delta (T.highFunded hc G hp child) (D.highRun hp T.vPositive hf child)
      (T.modeFee hc G) := by
    exact sum_delta H.hp (fun t=>padCost (K t) (F t)) K F G.centres
      (fun t _=>⟨rfl,rfl⟩)
  apply checked_delta
  refine ⟨?_,?_⟩
  · simp only [Input.fundedOpt,ActiveDesc.finish,high.value,D]
  · simp only [Input.fundedOpt,ActiveDesc.finish,high.value,high.fee,D]
    omega

/-- For equal returned frames the active calculation ignores any
difference in already incurred child fees. This is the raw word view,
not a norm bound or an additional semantic premise. -/
theorem active_result_congr {bank : Bank f} (D : ActiveDesc sel d bank)
    (hv : 0<ell) (g h : ActiveChild (sel:=sel) (d:=d) bank)
    (equal : ∀ t z β q,(g t z β q).result=(h t z β q).result) :
    (D.eval hp hv hf g).result=(D.eval hp hv hf h).result := by
  have B : (fun t z β q=>bare (g t z β q))=(fun t z β q=>bare (h t z β q)) := by
    funext t z β q
    simp only [bare,equal t z β q]
  rw [(D.one_visit hp hv hf g).value,(D.one_visit hp hv hf h).value,B]

#print axioms Input.funded_extra_exact
#print axioms active_result_congr
end J6R25PreparedSupply

