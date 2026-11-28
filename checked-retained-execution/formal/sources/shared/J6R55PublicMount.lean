import J6R55PublicReady
import J6R53PublicMountCore

/-! Construct the actual R53 mounted group on the exact R54 site.
The caller supplies the native machine and literal chart information,
not another live/ready certificate. There is no transport of a
previously published group to new source bytes. -/
namespace J6R55Public
open scoped Classical Polynomial
open Polynomial AOracleMachineTime A1R10 A1R12
open J6Mesh J6OrientedHost J6R24LegalLayout J6R24MeteredRecursion
open J6R26StablePreparedRoot J6R28GeneratedRootFrame J6R14ZeroMode
open J6R34RootAtlas J6R32RootGeneratedRegistryInputs
open J6R15ModeCost J6R30ProducedGateRegistry J6R32StatefulArithmetic
open J6R33StatefulArithmeticPage J6R31RootResidentTables J6R50SourceProducer
open J6R51 J6R51Online J6R51Leaf J6R50Leaf J6R48DFS J6R54PublicFamily J6R16ModeCost
open J6R12Blueprint J6R10Reachable J6R11Blueprint J6ActiveRun J1PPrinted J6R26DescriptorTree
open J6R53PublicMount
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 18000000
set_option maxRecDepth 3650
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {f : ℤ[X]} {m n base native : ℕ} {A : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) A (constantRootWord m)}
variable {ell q rr cc dd prec kp bw tc tj tw edgew rate : ℕ}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (W : Widths m native tc tj tw edgew) (C : Compiled G ell q rr cc dd prec kp bw)
variable (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) (g : Fin 64)
variable (pad : ℕ)
variable {T : Prepared G.bounds (G.selector ell) (exteriorChild G ell i j g) (literalSite W C i j g).hf}
variable (M : OnlineMachine T (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad) rate)
variable (B : reservedBank (f:=f) (ell:=ell) (kp:=kp) (tc:=tc) (tj:=tj)
  (prec:=prec) (tw:=tw) (bw:=bw) (m:=m) pad)
variable (bp : 0<base)
variable (order : Fin (exteriorChild G ell i j g).edges ≃ (exteriorChild G ell i j g).host.Edge)
variable (D : ∀ {v : Ticket (G.selector ell) (exteriorChild G ell i j g)}
  (x : StoredSite T v (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad)),ResidentLeafData x)
variable (retire : PageJob f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad)→ℕ)

def mountedRealPublic
    (sync : B.synced) (old : ∀ row∈B.headers,row.id.val≤C.mark.val)
    (capacity : nativeDepthCapacity W C i j g)
    (first : UsesFirstIssuer M (issuedAtFirstDepth W C i j g)) (later : UsesChildIncrement M)
    (chart : letI := sourceDecision (G.selector ell) (exteriorChild G ell i j g)
      LoopCharts (literalSite W C i j g) pad M bp D) :
    MountedGroup (rate:=rate) (pad:=pad) G (literalSite W C i j g) where
  tree := T
  finder := M
  basePositive := bp
  edgeOrder := order
  terminal := D
  retire := retire
  initial := B
  chart := chart
  live := (real_public_install_and_reserve W C i j g pad B sync old).2.1
  ready := (real_ready_after_literal_mount W C i j g pad M B sync old capacity first later).1

theorem same_real_public_mounted_fields
    (sync : B.synced) (old : ∀ row∈B.headers,row.id.val≤C.mark.val)
    (capacity : nativeDepthCapacity W C i j g)
    (first : UsesFirstIssuer M (issuedAtFirstDepth W C i j g)) (later : UsesChildIncrement M)
    (chart : letI := sourceDecision (G.selector ell) (exteriorChild G ell i j g)
      LoopCharts (literalSite W C i j g) pad M bp D) :
    let mounted := mountedRealPublic W C i j g pad M B bp order D retire sync old capacity first later chart
    mounted.finder=M ∧ mounted.initial=B ∧
      installedBank G (literalSite W C i j g) mounted=actualInstalledBank W C i j g pad B :=
  ⟨rfl,rfl,rfl⟩

theorem exact_public_group_from_issued_stack
    (sync : B.synced) (old : ∀ row∈B.headers,row.id.val≤C.mark.val)
    (capacity : nativeDepthCapacity W C i j g)
    (first : UsesFirstIssuer M (issuedAtFirstDepth W C i j g)) (later : UsesChildIncrement M)
    (chart : letI := sourceDecision (G.selector ell) (exteriorChild G ell i j g)
      LoopCharts (literalSite W C i j g) pad M bp D) :
    let X := literalSite W C i j g
    let A := mountedRealPublic W C i j g pad M B bp order D retire sync old capacity first later chart
    let result := mountedMeter G X A
    (mountedFrame G X A).decode result.result.1=
      J6R9Recursive.reduce (exteriorChild G ell i j g).prec f ell
        ((exteriorChild G ell i j g).host.contract X.hf) ∧
      result.result.2=actualInstalledBank W C i j g pad B ∧
      result.steps=installSteps G X A+(afterInstall G X A).steps+4 := by
  have degree : 0<f.natDegree := C.frame.natDegree C.hf ▸ C.frame.sizePos
  exact mounted_job_exact G (literalSite W C i j g)
    (mountedRealPublic W C i j g pad M B bp order D retire sync old capacity first later chart) degree

theorem leaf_agreement_without_a_new_leaf_value_or_stack
    (sync : B.synced) (old : ∀ row∈B.headers,row.id.val≤C.mark.val)
    (capacity : nativeDepthCapacity W C i j g)
    (first : UsesFirstIssuer M (issuedAtFirstDepth W C i j g)) (later : UsesChildIncrement M)
    (chart : letI := sourceDecision (G.selector ell) (exteriorChild G ell i j g)
      LoopCharts (literalSite W C i j g) pad M bp D) :
    letI := sourceDecision (G.selector ell) (exteriorChild G ell i j g)
    LeafAgreement (replaceTerminalFields (literalSite W C i j g) pad M bp order D)
      (actualInstalledBank W C i j g pad B) := by
  letI := sourceDecision (G.selector ell) (exteriorChild G ell i j g)
  exact proved_terminal_agreement (literalSite W C i j g) pad M bp order D
    (actualInstalledBank W C i j g pad B)
    (real_public_install_and_reserve W C i j g pad B sync old).2.1
    (real_ready_after_literal_mount W C i j g pad M B sync old capacity first later).1 chart

#print axioms mountedRealPublic
#print axioms same_real_public_mounted_fields
#print axioms exact_public_group_from_issued_stack
#print axioms leaf_agreement_without_a_new_leaf_value_or_stack
end
end J6R55Public

