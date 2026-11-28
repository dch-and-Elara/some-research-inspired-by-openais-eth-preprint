import J6R51OnlineCorrect
import J6R34OfficialGatewayCore

/-! Feed one actual R51 execution into the original public grouping
interface, on the exact exterior child of the one selected root shape. -/
namespace J6R52PublicSlot
open scoped Classical Polynomial BigOperators
open Polynomial AOracleMachineTime A1R10 A1R12 J6R22Active
open J6Mesh J6OrientedHost J6R24LegalLayout J6R24MeteredRecursion
open J6R26StablePreparedRoot J6R27PrescribedProbe J6R14ZeroMode J6R33OriginalJ6
open J6R32RootGeneratedRegistryInputs J6ActiveRun J6ActiveSchedule J6R12Blueprint
open J6R10Reachable J6R11Blueprint J1PPrinted J6R48DFS J6R51Online
open J6R30ProducedGateRegistry J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R34OfficialGateway

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2750
set_option maxHeartbeats 15000000
set_option linter.unusedSectionVars false
set_option Elab.async false
noncomputable section

variable {V : Type} [Fintype V]
variable {f : ℤ[X]} {m n base native ell key prec tw bw page speed : ℕ}
variable {T : Plant V m n}
variable (G : RootShape f m (printedHalf m) base native (printedRankWidth m) T
  (J6R28GeneratedRootFrame.constantRootWord m)) (hf : f.Monic)
variable (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) (g : Fin 64)
local notation "sig" => G.selector ell
local notation "ext" => exteriorChild G ell i j g
local notation "L" => PageBank f ell key prec tw bw page
local notation "J" => PageJob f ell key prec tw bw page

structure PublicGroup where
  tree : Prepared G.bounds sig ext hf
  machine : OnlineMachine tree key prec tw bw page speed
  initial : L
  retire : J→ℕ
  legal : ReadyOnStack (borns machine) initial
  leaves : letI : DecidableEq (Envelope (N sig) (Childs sig) ext) := sourceDecision sig ext
    LeafAgreement machine initial

variable (A : PublicGroup (ell:=ell) (key:=key) (prec:=prec) (tw:=tw) (bw:=bw) (page:=page)
  (speed:=speed) G hf i j g)

abbrev groupFrame : Frame f (ext).prec :=
  A.tree.frame (Path.root : Path sig ext ext).reached

def groupRun : Meter (Block (groupFrame G hf i j g A) ell × L) :=
  runRoot A.machine A.retire A.initial

theorem actual_exterior_group_value [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (hF : 0<f.natDegree) :
    let out := groupRun G hf i j g A
    (groupFrame G hf i j g A).decode out.result.1=
      J6R9Recursive.reduce (ext).prec f ell ((ext).host.contract hf) ∧ out.result.2=A.initial := by
  letI : DecidableEq (Envelope (N sig) (Childs sig) ext) := sourceDecision sig ext
  obtain ⟨value,state⟩ := full_online_selected_source A.machine A.initial A.retire A.legal A.leaves
  exact ⟨value.trans (J6R12Integral.printed_run_exact G.bounds sig ext A.tree.rootStable hf hF),state⟩

def actualGroupReceipt [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (hF : 0<f.natDegree) : GroupReceipt (ell:=ell) G hf i j g where
  frame := groupFrame G hf i j g A
  run := let out := groupRun G hf i j g A
         ⟨out.result.1,out.steps⟩
  truth := (actual_exterior_group_value G hf i j g A hF).1

theorem exterior_group_starts_at_one :
    (exteriorChild G ell i j g).depth=1 := rfl

theorem receipt_uses_actual_online_value_bill [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (hF : 0<f.natDegree) :
    (actualGroupReceipt G hf i j g A hF).run=
      ⟨(groupRun G hf i j g A).result.1,(groupRun G hf i j g A).steps⟩ := rfl

#print axioms actual_exterior_group_value
#print axioms actualGroupReceipt
#print axioms exterior_group_starts_at_one
#print axioms receipt_uses_actual_online_value_bill
end
end J6R52PublicSlot
