import J6R63OrdinalProbe
import J6R49DFSActive

/-! The ranked probe now runs inside the real centre and active
arithmetic: same masks, actual normalizer and Hermite rows, same
centre traversal and strip. No second auxiliary probe is evaluated. -/
namespace J6R63Ordinal
open scoped Polynomial
open Polynomial AOracleMachineTime A1R10 A1R12 J6R22Active
open J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable
open J6R11Blueprint J6R12Blueprint J1PPrinted J6R24MeteredRecursion
open J6R49DFS J6R16ModeCost J6R23ScheduleWeight J6R19Retained J6R25PreparedSupply
set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 3800
set_option maxHeartbeats 23000000
set_option maxSynthPendingDepth 12
set_option Elab.async false
noncomputable section

variable {f : ℤ[X]} {ell s q b highPrec : ℕ}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {c : Call (PhysicalHost f ell)}
local notation "SP" => (printedParams (f:=f) (ell:=ell) s)
variable {d : Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c} {bank : Bank f}
variable {t : Center (printedParams (f:=f) (ell:=ell) s) c}
variable (J : CentreMachine sel d t bank q) (ordinal : NativeMenu (N sel) c t → ℕ)

def rankedCentreJet (hq : 0<q) (hb : 0<b) (hv : 0<ell)
    (archive : HonestArchive J.tape.result ordinal b)
    (child : Probe SP c → RankedChild J.low J.tape.result ordinal b) :
    Meter (JetTape J.low.words ell J.window) := by
  exact fullCenterM J.low.hp J.low.sizePos hv
    (active_order_pos ((SP).levelBits c.depth) c.edges ((SP).levelWidth c.depth) t.val t.property)
    (fun z=>padCost (encodeProbe J.low.hp hv (J.masks z).result) (J.masks z).steps)
    (fun z=>runProbeRanked J.low J.tape.result ordinal hq hb hv archive (child z))
    (normalizerM J.low.hp J.low.sizePos hv
      (active_order_pos ((SP).levelBits c.depth) c.edges ((SP).levelWidth c.depth) t.val t.property)
      ((SP).levelBits c.depth) t.val J.roster.rows)

theorem ranked_centre_runs_its_original_jet
    (hq : 0<q) (hb : 0<b) (hv : 0<ell) (hf : f.Monic)
    (archive : HonestArchive J.tape.result ordinal b) (child : Probe SP c → RankedChild J.low J.tape.result ordinal b)
    (ref : CentreChild (sel:=sel) (d:=d) (t:=t) bank)
    (agree : ∀ (z : Probe SP c) (β : NativeMenu (N sel) c t)
      (raw : List (J6R15ModeCost.Word q)) (i : J6R15ModeCost.Word b)
      (bits : raw.map J6R15ModeCost.Word.val=vectorKey sel d t J.tape.result β)
      (rank : i.val=ordinal β) (g : Fin 64),(child z β raw i bits rank g).result=(ref z β g).result) :
    (rankedCentreJet J ordinal hq hb hv archive child).result=(J.centreJet hq hv ref).result := by
  unfold rankedCentreJet CentreMachine.centreJet directCentreJet
  apply interchangeable_samples
  intro z
  exact ranked_probe_keeps_the_actual_online_word J.low J.tape.result ordinal hf hq hb hv archive
    (child z) (ref z) (agree z)

def rankedCentre (hq : 0<q) (hb : 0<b) (hv : 0<ell) (hf : f.Monic)
    (high : Frame f highPrec) (B : ℕ)
    (archive : HonestArchive J.tape.result ordinal b) (child : Probe SP c → RankedChild J.low J.tape.result ordinal b) :
    Meter (Block high ell) := by
  let z := rankedCentreJet J ordinal hq hb hv archive child
  let work := sumM high.hp (J.centreTerm hv hf high B z.result) (List.range J.window)
  exact ⟨work.result,J.tape.steps+z.steps+work.steps+
    tapeFee J.low.words.length ell (registerPrecision SP c t) J.window+4⟩

theorem ranked_centre_keeps_original_high_word
    (hq : 0<q) (hb : 0<b) (hv : 0<ell) (hf : f.Monic) (high : Frame f highPrec) (B : ℕ)
    (archive : HonestArchive J.tape.result ordinal b) (child : Probe SP c → RankedChild J.low J.tape.result ordinal b)
    (ref : CentreChild (sel:=sel) (d:=d) (t:=t) bank)
    (agree : ∀ (z : Probe SP c) (β : NativeMenu (N sel) c t)
      (raw : List (J6R15ModeCost.Word q)) (i : J6R15ModeCost.Word b)
      (bits : raw.map J6R15ModeCost.Word.val=vectorKey sel d t J.tape.result β)
      (rank : i.val=ordinal β) (g : Fin 64),(child z β raw i bits rank g).result=(ref z β g).result) :
    (rankedCentre J ordinal hq hb hv hf high B archive child).result=
      (J.runCentre hq hv hf high B ref).result := by
  unfold rankedCentre CentreMachine.runCentre
  dsimp only
  rw [ranked_centre_runs_its_original_jet J ordinal hq hb hv hf archive child ref agree]

variable (D : ActiveMachine sel d bank q)
variable (ord : (v : Center (printedParams (f:=f) (ell:=ell) s) c) → NativeMenu (N sel) c v → ℕ)

abbrev ActiveReader (D : ActiveMachine sel d bank q)
    (rankOf : (v : Center (printedParams (f:=f) (ell:=ell) s) c) → NativeMenu (N sel) c v → ℕ)
    (b : ℕ) : Type :=
  (v : Center (printedParams (f:=f) (ell:=ell) s) c) → Probe (printedParams (f:=f) (ell:=ell) s) c →
    RankedChild (D.tape v).low (D.tape v).tape.result (rankOf v) b

def rankedHigh (hq : 0<q) (hb : 0<b) (hp : 0<c.prec) (hv : 0<ell) (hf : f.Monic)
    (archive : ∀ t,HonestArchive (D.tape t).tape.result (ord t) b) (read : ActiveReader D ord b) :
    Meter (Block (D.high hp) ell) := by
  exact sumM (D.high hp).hp (fun t=>rankedCentre (D.tape t) (ord t)
    hq hb hv hf (D.high hp) D.extraPrecision (archive t) (read t)) D.centres

def rankedFinish (hq : 0<q) (hb : 0<b) (hp : 0<c.prec) (hv : 0<ell) (hf : f.Monic)
    (archive : ∀ t,HonestArchive (D.tape t).tape.result (ord t) b) (read : ActiveReader D ord b) :
    Meter (Option (Block (bank c.prec hp) ell)) := by
  let value := rankedHigh D ord hq hb hp hv hf archive read
  let strip := stripUVLoop (((D.high hp).natDegree hf).trans ((bank c.prec hp).natDegree hf).symm)
    value.result
  exact ⟨strip.result,value.steps+strip.steps+4⟩

def rankedActive (hq : 0<q) (hb : 0<b) (hp : 0<c.prec) (hv : 0<ell) (hf : f.Monic)
    (archive : ∀ t,HonestArchive (D.tape t).tape.result (ord t) b) (read : ActiveReader D ord b) :
    Meter (Block (bank c.prec hp) ell) := by
  exact checkedWord (zeroM (bank c.prec hp).hp) (rankedFinish D ord hq hb hp hv hf archive read)

theorem ranked_active_keeps_actual_decoded_word
    (hq : 0<q) (hb : 0<b) (hp : 0<c.prec) (hv : 0<ell) (hf : f.Monic)
    (archive : ∀ t,HonestArchive (D.tape t).tape.result (ord t) b) (read : ActiveReader D ord b)
    (old : ActiveChild (sel:=sel) (d:=d) bank)
    (agree : ∀ (t : Center SP c) (z : Probe SP c) (β : NativeMenu (N sel) c t)
      (raw : List (J6R15ModeCost.Word q)) (i : J6R15ModeCost.Word b)
      (bits : raw.map J6R15ModeCost.Word.val=vectorKey sel d t (D.tape t).tape.result β)
      (rank : i.val=ord t β) (g : Fin 64),(read t z β raw i bits rank g).result=(old t z β g).result) :
    (rankedActive D ord hq hb hp hv hf archive read).result=(D.eval hq hp hv hf old).result := by
  have high : (rankedHigh D ord hq hb hp hv hf archive read).result=
      (D.highRun hq hp hv hf old).result := by
    unfold rankedHigh ActiveMachine.highRun
    apply sum_raw_congr
    intro t _
    exact ranked_centre_keeps_original_high_word (D.tape t) (ord t) hq hb hv hf
      (D.high hp) D.extraPrecision (archive t) (read t) (old t) (agree t)
  have final : (rankedFinish D ord hq hb hp hv hf archive read).result=
      (D.finish hq hp hv hf old).result := by
    unfold rankedFinish ActiveMachine.finish
    dsimp only
    rw [high]
  unfold rankedActive ActiveMachine.eval checkedWord
  rw [final]
  cases (D.finish hq hp hv hf old).result <;> rfl

#print axioms rankedCentreJet
#print axioms ranked_centre_runs_its_original_jet
#print axioms ranked_centre_keeps_original_high_word
#print axioms rankedActive
#print axioms ranked_active_keeps_actual_decoded_word
end
end J6R63Ordinal
