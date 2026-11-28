import J6R49CostActiveAddress

/-! Factor the original arithmetic tariff into costs outside the
native mode loop and the exact once-per-mode contribution. No new
interpreter or precomputed mode table is used. -/
namespace J6R57ActiveFee
open scoped Polynomial Classical BigOperators
open Polynomial AOracleMachineTime A1R10 A1R11 A1R12 J6R22Active
open J1PPrinted J6ActiveRun J6ActiveSchedule J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R24MeteredRecursion J6R23ScheduleWeight J6R19Retained HermiteLoss J6R48BitCost J6R49DFS J6R49Cost

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 9500000
set_option maxRecDepth 3000
set_option linter.unusedSectionVars false
set_option Elab.async false
attribute [local irreducible] J6R12Blueprint.printedParams

section Probe

variable {f : ℤ[X]} {ell : ℕ} {S : Params (f:=f) (ell:=ell)} {Δ q : ℕ}
variable {sel : Selector S Δ} {c : Call (PhysicalHost f ell)}
variable {d : Ready S Δ c} {t : Center S c}
local notation "pₜ" => registerPrecision S c t

def fixedProbe (F : Frame f pₜ) (I : J6R16ModeCost.SiteTape sel d t q) : ℕ :=
  J6R16ModeCost.setupCap q I.words.length+uvWidth F.words.length ell pₜ+
    J6R15ModeCost.delayCap q I.words.length

def unitMode (F : Frame f pₜ) (I : J6R16ModeCost.SiteTape sel d t q) : ℕ :=
  perModeArithmetic F.words.length ell pₜ F.hp+J6R15ModeCost.delayCap q I.words.length

theorem probe_split (F : Frame f pₜ) (I : J6R16ModeCost.SiteTape sel d t q) :
    streamedProbeTariff F I=
      fixedProbe F I+Nat.card (NativeMenu (shape S Δ sel) c t)*unitMode F I := by
  unfold streamedProbeTariff fixedProbe unitMode J6R16ModeCost.setupCap
  ring

end Probe

variable {f : ℤ[X]} {ell s : ℕ}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)} {c : Call (PhysicalHost f ell)}
variable {d : Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c} {bank : Bank f} {q : ℕ}

abbrev probeCount (c : Call (PhysicalHost f ell)) : ℕ :=
  J9PrintedSchedule.probeCount c.edges (2^(@centreA f ell s c))

noncomputable def fixedCentre {t : @J6ActiveRun.Center (PhysicalHost f ell) Unit S c}
    {highPrec : ℕ} (J : @CentreMachine f ell s sel c d t bank q)
    (hv : 0<ell) (high : Frame f highPrec) (B : ℕ) : ℕ :=
  let F := J.low
  let k := J.window
  let n := @probeCount f ell s c
  let node := fun z : Probe S c => padCost (encodeProbe F.hp hv (J.masks z).result) (J.masks z).steps
  J.tape.steps+
    (n*fixedProbe F J.tape.result+
      normalizerFee F.words.length ell (@centreP f ell s c t) (@centreA f ell s c) k F.hp J.roster.rows+
      ((probeOrder n).map (needsAt node)).sum+
      interpExtra F.words.length ell (@centreP f ell s c t) k n F.hp+
      quotientFee F.words.length ell (@centreP f ell s c t) k F.hp+4)+
    ((List.range k).map (fun j => termFee f.natDegree ell (@centreP f ell s c t) highPrec
      (@centreA f ell s c) B k j high.hp t.val J.roster.rows)).sum+
    uvWidth high.words.length ell highPrec+k*(addCap high.words.length ell highPrec high.hp+2)+
    tapeFee F.words.length ell (@centreP f ell s c t) k+4

theorem centre_split {t : @J6ActiveRun.Center (PhysicalHost f ell) Unit S c}
    {highPrec : ℕ} (J : @CentreMachine f ell s sel c d t bank q)
    (hv : 0<ell) (high : Frame f highPrec) (B : ℕ) :
    streamCentreTariff (sel:=sel) (d:=d) (t:=t) J hv high B=
      fixedCentre J hv high B+
        (@probeCount f ell s c*Nat.card (NativeMenu (N sel) c t))*unitMode J.low J.tape.result := by
  unfold streamCentreTariff fixedCentre
  dsimp only
  rw [probe_split]
  ring

noncomputable def fixedActive (D : @ActiveMachine f ell s sel c d bank q)
    (hp : 0<c.prec) (hv : 0<ell) : ℕ :=
  let H := D.high hp
  let L := bank c.prec hp
  let B := D.extraPrecision
  (D.centres.map (fun t => fixedCentre (D.tape t) hv H B)).sum+
    uvWidth H.words.length ell (c.prec+B)+D.centres.length*(addCap H.words.length ell (c.prec+B) H.hp+2)+
    stripFee H.words.length ell c.prec B+4+uvWidth L.words.length ell c.prec+2

theorem active_split (D : @ActiveMachine f ell s sel c d bank q)
    (hp : 0<c.prec) (hv : 0<ell) :
    streamActiveTariff D hp hv=
      fixedActive D hp hv+(D.centres.map (fun t=>
        (@probeCount f ell s c*Nat.card (NativeMenu (N sel) c t))*
          unitMode (D.tape t).low (D.tape t).tape.result)).sum := by
  let a := fun t => fixedCentre (D.tape t) hv (D.high hp) D.extraPrecision
  let b := fun t => (@probeCount f ell s c*Nat.card (NativeMenu (N sel) c t))*
      unitMode (D.tape t).low (D.tape t).tape.result
  have bill := list_charge D.centres
    (fun t=>streamCentreTariff (sel:=sel) (d:=d) (t:=t) (D.tape t) hv (D.high hp) D.extraPrecision)
    a b (fun t _=>centre_split (D.tape t) hv (D.high hp) D.extraPrecision)
  unfold streamActiveTariff fixedActive
  dsimp only
  rw [bill]
  dsimp only [a,b]
  ac_rfl

#print axioms probe_split
#print axioms centre_split
#print axioms active_split
end J6R57ActiveFee
