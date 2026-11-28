import J6R53PublicMountCore

/-! Optional freshness corollary. The main mounted ABI deliberately
requires the post-attempt source to be live, not a fresh insertion.
A synchronized bank and an unused literal issue id ensure the actual
original install succeeds, and that exact bank survives the DFS. -/
namespace J6R53PublicMount
open scoped Classical Polynomial
open Polynomial AOracleMachineTime
open J6Mesh J6OrientedHost J6R24LegalLayout J6R24MeteredRecursion
open J6R26StablePreparedRoot J6R27PrescribedProbe J6R28GeneratedRootFrame
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R19Retained J6R21Ancestor J6R34RootAtlas J6R31RootResidentTables
open J6R30GeneratedRootLayout J6R30ProducedGateRegistry J6R32RootGeneratedRegistryInputs J6R33PageIndexedBirth
open J6R15ModeCost J6R27OriginalGate J6R17ModeTape J6R18ChildWrite J6R16ModeCost J6R20Ancestor
open J6R26DescriptorTree J6R25PreparedSupply J6R11Blueprint J6R12Blueprint J6R11Repack J6R12Repack J6R10Repack
open J6R14ZeroMode J6ActiveRun J6ActiveSchedule J1PPrinted P11FullPacking

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 3250
set_option maxHeartbeats 9500000
set_option linter.unusedSectionVars false
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {f : ℤ[X]} {m n base native : ℕ} {T : Plant V m n}
variable (G : RootShape f m (printedHalf m) base native (printedRankWidth m) T (constantRootWord m))
variable {ell q rr cc dd edgew tc tj key prec tw bw rate pad : ℕ}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (X : StableExterior G ell q rr cc dd edgew tc tj key prec tw bw)
variable (M : MountedGroup (rate:=rate) (pad:=pad) G X)

theorem genuinely_fresh_install_survives_the_dfs (degree : 0<f.natDegree)
    (synchronized : M.initial.synced)
    (fresh : ∀ row∈M.initial.headers,row.id≠X.issue.result)
    (k : Page (a m) (K m) (Fin 64)) :
    let install := (X.seed pad).install M.initial
    let out := mountedMeter G X M
    install.result.2=true ∧ out.result.2=install.result.1 ∧ IsLive (X.seed pad) out.result.2 := by
  have install := true_exterior_seed_lookup X pad M.initial synchronized fresh k
  have same := (mounted_job_exact G X M degree).2.1
  refine ⟨install.1,same,?_⟩
  rw [same]
  exact install.2.1

#print axioms genuinely_fresh_install_survives_the_dfs
end
end J6R53PublicMount
