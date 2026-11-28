import J6R52FreshExteriorRunner
import J6R34OfficialGatewayCore

/-! The real installed external child, with the root seed installation
and the selected depth-one DFS in one original meter. -/
namespace J6R53PublicMount
open scoped Classical Polynomial BigOperators
open Polynomial AOracleMachineTime A1R10 A1R12
open J6Mesh J6OrientedHost J6R24LegalLayout J6R24MeteredRecursion
open J6R26StablePreparedRoot J6R27PrescribedProbe J6R33OriginalJ6 J6R28GeneratedRootFrame
open J6R34OfficialGateway J6R34RootAtlas J6R27OriginalGate J6R30ProducedGateRegistry
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R20Ancestor J6R21Ancestor
open J6R12Blueprint J6R10Reachable J6R11Blueprint J6ActiveRun J6R48DFS
open J6R50SourceProducer J6R51Online J6R51Leaf J6R50Leaf J6R52FreshExterior
open J6R15ModeCost J6R30GeneratedRootLayout J6R26DescriptorTree J6R17ModeTape
open J6R31RootResidentTables J6R32RootGeneratedRegistryInputs J6R51Ingress
open J6R49RootIngress J6R50RootIngress P11FullPacking J6R14ZeroMode
open J7R9Compiler J7R9Subdivision J7R10Plant

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 3400
set_option maxHeartbeats 11600000
set_option linter.unusedSectionVars false
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {f : ℤ[X]} {m n base native : ℕ} {T : Plant V m n}
variable (G : RootShape f m (printedHalf m) base native (printedRankWidth m) T (constantRootWord m))
variable {ell q rr cc dd edgew tc tj key prec tw bw rate pad : ℕ}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]

local notation "Sel" => (G.selector ell)
local notation "Pg" => (pageKeyWidth m+pad)
local notation "Site" => (StableExterior G ell q rr cc dd edgew tc tj key prec tw bw)
local notation "Ext" => (fun X : Site=>exteriorChild G ell X.centre X.sample X.group)
local notation "Bank" => (PageBank f ell key prec tw bw Pg)

structure MountedGroup (X : Site) where
  tree : Prepared G.bounds Sel (Ext X) X.hf
  finder : OnlineMachine tree key prec tw bw Pg rate
  basePositive : 0<base
  edgeOrder : Fin (Ext X).edges ≃ (Ext X).host.Edge
  terminal : ∀ {v : Ticket Sel (Ext X)} (s : StoredSite tree v key prec tw bw Pg), ResidentLeafData s
  retire : PageJob f ell key prec tw bw Pg→ℕ
  initial : Bank
  chart : letI := sourceDecision Sel (Ext X)
          LoopCharts X pad finder basePositive terminal
  live : IsLive (X.seed pad) ((X.seed pad).install initial).result.1
  ready : ReadyOnStack (borns finder) ((X.seed pad).install initial).result.1

variable (X : StableExterior G ell q rr cc dd edgew tc tj key prec tw bw)
variable (M : MountedGroup (rate:=rate) (pad:=pad) G X)

abbrev mountedFrame : Frame f (Ext X).prec :=
  M.tree.frame (Path.root : Path Sel (Ext X) (Ext X)).reached

def installedBank : Bank := ((X.seed pad).install M.initial).result.1

def installSteps : ℕ := ((X.seed pad).install M.initial).steps

def afterInstall : Meter (Block (mountedFrame G X M) ell × Bank) :=
  letI := sourceDecision Sel (Ext X)
  runRoot (replaceTerminalFields X pad M.finder M.basePositive M.edgeOrder M.terminal)
    M.retire (installedBank G X M)

def mountedMeter : Meter (Block (mountedFrame G X M) ell × Bank) :=
  letI := sourceDecision Sel (Ext X)
  mountedOnline X M.finder M.basePositive M.edgeOrder M.terminal M.retire M.initial

theorem mounted_job_exact (degree : 0<f.natDegree) :
    (mountedFrame G X M).decode (mountedMeter G X M).result.1 =
      J6R9Recursive.reduce (Ext X).prec f ell ((Ext X).host.contract X.hf) ∧
    (mountedMeter G X M).result.2=installedBank G X M ∧
    (mountedMeter G X M).steps=installSteps G X M+(afterInstall G X M).steps+4 := by
  letI := sourceDecision Sel (Ext X)
  have h := mounted_online_reuses_the_new_source X M.finder M.basePositive
    M.edgeOrder M.terminal M.retire M.initial M.chart M.live M.ready
  exact ⟨h.1.trans (J6R12Integral.printed_run_exact G.bounds Sel (Ext X) M.tree.rootStable X.hf degree),
    h.2.1,h.2.2⟩

def mountedReceipt (degree : 0<f.natDegree) :
    GroupReceipt (ell:=ell) G X.hf X.centre X.sample X.group where
  frame := mountedFrame G X M
  run := let run := mountedMeter G X M
         ⟨run.result.1,run.steps⟩
  truth := (mounted_job_exact G X M degree).1

theorem receipt_is_the_installed_meter (degree : 0<f.natDegree) :
    (mountedReceipt G X M degree).run =
      ⟨(mountedMeter G X M).result.1,(mountedMeter G X M).steps⟩ := rfl

theorem receipt_includes_install_and_dfs (degree : 0<f.natDegree) :
    (mountedReceipt G X M degree).run.steps =
      installSteps G X M+(afterInstall G X M).steps+4 :=
  (mounted_job_exact G X M degree).2.2

#print axioms mounted_job_exact
#print axioms mountedReceipt
#print axioms receipt_is_the_installed_meter
#print axioms receipt_includes_install_and_dfs
end
end J6R53PublicMount
