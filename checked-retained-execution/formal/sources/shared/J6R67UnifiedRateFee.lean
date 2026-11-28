import J6R66ActivePhase
import J6R64ActiveMachine

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 14500000
set_option maxRecDepth 3400
set_option maxSynthPendingDepth 12
set_option Elab.async false

/-! Numeric envelopes for the real R64 reads, fixed-word controller
and R62 tape in the R66 active machine. Bounds on opaque base or
layout acquisition meters are not inferred from value/width. -/
namespace J6R67UnifiedRate
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R17ModeTape
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R24MeteredRecursion J6R32StatefulArithmetic J6R49DFS
open J6R57ActiveFee J6R63Active J6R64Active J6R62ActivePrep
open J6R52FreshExterior J6R22RootReadout J6R30ProducedGateRegistry J6R50Peak J6R9Recursive

def sharedHeaderAndCopyRoof (K : ℕ) : ℕ := 26*K+22
def liveActiveTapeRoof (K : ℕ) : ℕ := ctrlFee K K K K K+3+tapePolynomial K

theorem true_header_and_retained_copy_roof
    {pw ew dw offset cw q K : ℕ}
    (hp : pw≤K) (he : ew≤K) (hd : dw≤K) (ho : offset≤K) (hc : cw≤K) (hq : q≤K) :
    (callReadFee pw ew dw offset+5)+(2*cw+4*q+5)+4≤sharedHeaderAndCopyRoof K := by
  unfold callReadFee headerReadFee sharedHeaderAndCopyRoof
  omega

theorem actual_fixed_word_control_roof {pw ew q a u K : ℕ}
    (hp : pw≤K) (he : ew≤K) (hq : q≤K) (ha : a≤K) (hu : u≤K) :
    ctrlFee pw ew q a u≤ctrlFee K K K K K := by
  unfold ctrlFee taperFee precisionFee wordArithmeticRoof signedDivisionFee
  gcongr

noncomputable section
variable {f : ℤ[X]} {ell s C q pw ew cw : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)

theorem real_shared_tape_from_numeric_dimensions
    (T : Prepared cfg sel r hf) (p : Path sel r c) (on : (S).cutoff<c.edges)
    (t : Center S c) (hq : 0<q)
    (F : InputFits sel (readyAtPath T p on) q)
    (W : Meter (CallWords c pw ew)) (L : Meter (AtLayout sel (readyAtPath T p on) cw))
    (D : Meter (ActiveMachine sel (readyAtPath T p on) T.bank q))
    (K : ℕ) (ws : ActiveWidthScale (ell:=ell) (s:=s) (C:=C) (q:=q) (r:=r) K)
    (cs : PrintedCentreScale s C K) (wp : pw≤K) (we : ew≤K) :
    let taper := actual_path_taper T p on
    ((sharedMachine hq F taper.1 taper.2 W L D).result.tape t).tape.steps≤liveActiveTapeRoof K := by
  let d := readyAtPath T p on
  let taper := actual_path_taper T p on
  obtain ⟨a,headers,_,copies,tiles⟩ := native_layout_sizes cfg sel p.reached T.rootStable d t
  have edges : C*s≤K := (Nat.le_mul_of_pos_left (C*s) (by decide : 0<(4:ℕ))).trans cs.edges
  have scale : s≤K := (Nat.le_mul_of_pos_left s cfg.constPos).trans edges
  have level := a.trans scale
  have taperFit := taper.2.trans ((physical_edges_at_most_root_scale (cfg:=cfg) p T.rootStable).trans edges)
  have pFit : registerPrecision S c t≤K :=
    (absolute_register_precision_cap cfg sel T.rootStable p on t).trans ws.register
  have copyFit : (packing sel d).copies≤K :=
    copies.trans ((Nat.mul_le_mul_right (C*s) (by decide : (3:ℕ)≤4)).trans cs.edges)
  have tick := canonical_cap_of_small_dimensions level ws.modeWord
    (headers.trans edges) copyFit (tiles.trans scale) pFit
  have control := actual_fixed_word_control_roof wp we ws.modeWord level taperFit
  exact (actual_centre_tape_uses_shared_words hq F taper.1 taper.2 W L D t).trans
    (Nat.add_le_add (Nat.add_le_add_right control 3) tick)

#print axioms true_header_and_retained_copy_roof
#print axioms actual_fixed_word_control_roof
#print axioms real_shared_tape_from_numeric_dimensions
end
end J6R67UnifiedRate

