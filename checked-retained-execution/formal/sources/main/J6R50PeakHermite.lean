
import J6R50PeakNested
import J6R50NonModeScratchRetained

/-! Selected retained fields between the current quotient and the
finalized high centre block: earlier complete centre blocks, earlier
weighted high terms at this centre, and its unchanged low quotient. -/
namespace J6R50Peak
open scoped Polynomial
open AOracleMachineTime A1R10 A1R12 J6R22Active J6R23ScheduleWeight
open J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R24MeteredRecursion J1PPrinted J6R49DFS J6R49NonModeStack J6R50NonModeScratch

set_option autoImplicit false
set_option maxRecDepth 3200
set_option maxHeartbeats 14000000

variable {f : ℤ[X]} {ell s q : ℕ}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {c : Call (PhysicalHost f ell)}
variable {d : Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c} {bank : Bank f}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)

noncomputable abbrev weightRead (D : ActiveMachine sel d bank q)
    (hq : 0<q) (hp : 0<c.prec) (hv : 0<ell) (hf : f.Monic)
    (child : ActiveChild (sel:=sel) (d:=d) bank) (t : Center S c) (j : ℕ) :
    Meter (Block (D.high hp) ell) :=
  let J := D.tape t
  J.centreTerm hv hf (D.high hp) D.extraPrecision (J.centreJet hq hv (child t)).result j

noncomputable def weightedPayload (D : ActiveMachine sel d bank q)
    (hq : 0<q) (hp : 0<c.prec) (hv : 0<ell) (hf : f.Monic)
    (child : ActiveChild (sel:=sel) (d:=d) bank)
    (before : List (Center S c)) (t : Center S c) (j : ℕ) : List Bool :=
  let J := D.tape t
  let step := weightRead D hq hp hv hf child t
  completedBlockPayload (before.map (centreRead D hq hp hv hf child)) ++
    (scalarTermsPayload (((List.range J.window).take j).map step) ++
      jetPayload (J.centreJet hq hv (child t)).result)

noncomputable def resumeWeighted (D : ActiveMachine sel d bank q)
    (hq : 0<q) (hp : 0<c.prec) (hv : 0<ell) (hf : f.Monic)
    (child : ActiveChild (sel:=sel) (d:=d) bank) (t : Center S c) (j : ℕ) :
    Meter (Block (D.high hp) ell) :=
  let J := D.tape t
  let H := D.high hp
  let jet := J.centreJet hq hv (child t)
  let step := weightRead D hq hp hv hf child t
  let out := resumeUV H.hp (((List.range J.window).take j).map step)
    (sumM H.hp step ((List.range J.window).drop j))
  ⟨out.result,J.tape.steps+jet.steps+out.steps+
    tapeFee J.low.words.length ell (registerPrecision S c t) J.window+4⟩

theorem actual_high_sum_resumes_weighted_centre (D : ActiveMachine sel d bank q)
    (hq : 0<q) (hp : 0<c.prec) (hv : 0<ell) (hf : f.Monic)
    (child : ActiveChild (sel:=sel) (d:=d) bank)
    (before after : List (Center S c)) (t : Center S c) (j : ℕ)
    (split : D.centres=before++t::after) (hj : j≤(D.tape t).window) :
    D.highRun hq hp hv hf child=
      resumeBlocks (D.high hp).hp (before.map (centreRead D hq hp hv hf child))
        (addM (D.high hp).hp
          (resumeWeighted D hq hp hv hf child t j)
          (sumM (D.high hp).hp (centreRead D hq hp hv hf child) after)) ∧
    (weightedPayload D hq hp hv hf child before t j).length=
      before.length*(ell*(f.natDegree*(c.prec+D.extraPrecision)))+
        (j*(ell*(f.natDegree*(c.prec+D.extraPrecision)))+
          (D.tape t).window*(ell*(f.natDegree*registerPrecision S c t))) := by
  let J := D.tape t
  let H := D.high hp
  let w := J.centreJet hq hv (child t)
  let read := weightRead D hq hp hv hf child t
  have hW := actual_hermite_retained_words J.low.hp J.low.sizePos H.hp H.sizePos hv
    ((J.low.natDegree hf).trans (H.natDegree hf).symm)
    w.result ((S).levelBits c.depth) D.extraPrecision j t.val J.roster.rows hj
  have eq : centreRead D hq hp hv hf child t=resumeWeighted D hq hp hv hf child t j :=
    congrArg (fun out : Meter (Block H ell) =>
      (⟨out.result,J.tape.steps+w.steps+out.steps+
        tapeFee J.low.words.length ell (registerPrecision S c t) J.window+4⟩ :
        Meter (Block H ell))) hW.1
  constructor
  · change sumM H.hp (centreRead D hq hp hv hf child) D.centres=_
    rw [split]
    exact paid_sum_resumes_at H.hp (centreRead D hq hp hv hf child) before t after _ eq
  · have size :
        (scalarTermsPayload (((List.range J.window).take j).map read) ++ jetPayload w.result).length=
          j*(ell*(H.words.length*(c.prec+D.extraPrecision)))+
          J.window*(ell*(J.low.words.length*registerPrecision S c t)) := hW.2
    rw [weightedPayload,List.length_append,completed_block_payload_exact,List.length_map,
      (D.high hp).natDegree hf]
    rw [size,H.natDegree hf,J.low.natDegree hf]

#print axioms actual_high_sum_resumes_weighted_centre
end J6R50Peak
