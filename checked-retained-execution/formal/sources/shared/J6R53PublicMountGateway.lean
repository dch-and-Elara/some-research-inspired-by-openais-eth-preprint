import J6R53PublicMountAggregate
import J6R36SharedGatewayDelta

/-! The original legal byte gateway calls the mounted all-group
product, and its public returned meter necessarily includes every install. -/
namespace J6R53PublicMount
open scoped Classical Polynomial BigOperators
open Polynomial AOracleMachineTime AOracleMachineTimeTape A1R10 A1R12 J6R22Active
open J6Mesh J6OrientedHost J6R24LegalLayout J6R24MeteredRecursion
open J6R26StablePreparedRoot J6R27PrescribedProbe J6R33OriginalJ6 J6R28GeneratedRootFrame
open J6R34OfficialGateway J6R34RootAtlas J6R27OriginalGate J6R14ZeroMode J6R36SharedGateway
open J6R32RootGeneratedRegistryInputs J6R19Retained

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 3310
set_option maxHeartbeats 14000000
set_option linter.unusedSectionVars false
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {f : ℤ[X]} {m n base native : ℕ} {T : Plant V m n}
variable (G : RootShape f m (printedHalf m) base native (printedRankWidth m) T (constantRootWord m))
variable {ell q rr cc dd edgew tc tj key prec tw bw rate pad : ℕ}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (hf : f.Monic) (F : Frame f (J6SourcePrecision.printed m base)) (positive : 0<ell)

abbrev MountedFamily (ell q rr cc dd edgew tc tj key prec tw bw rate pad : ℕ) :=
  ∀ i j g, AddressGroup (ell:=ell) (q:=q) (rr:=rr) (cc:=cc) (dd:=dd) (edgew:=edgew)
    (tc:=tc) (tj:=tj) (key:=key) (prec:=prec) (tw:=tw) (bw:=bw) (rate:=rate) (pad:=pad) G i j g

variable (R : MountedFamily G ell q rr cc dd edgew tc tj key prec tw bw rate pad)
variable (A : SuppliedProbeBits (rootPreset G ell) f.natDegree)

def paidMountedQuery : SlotProgram (ell:=ell) (F:=F) G :=
  fun i j raw =>
    let expected := A.read j
    let test := eqRawBits raw expected.result.val
    if test.result then
      let run := mountedSlot G hf F i j positive (R i j)
      ⟨run.result,expected.steps+test.steps+run.steps+4⟩
    else
      let reject := zeroM (ell:=ell) (SiteFrame G ell F i).hp
      ⟨reject.result,expected.steps+test.steps+reject.steps+4⟩

variable (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1))
variable (raw : List Bool) (legal : raw=List.ofFn ((rootPreset G ell).word j))

include legal in
theorem legal_query_is_actual_mount_meter :
    let expected := A.read j
    let test := eqRawBits raw expected.result.val
    let run := mountedSlot G hf F i j positive (R i j)
    paidMountedQuery G hf F positive R A i j raw =
      ⟨run.result,expected.steps+test.steps+run.steps+4⟩ := by
  have same : raw=(A.read j).result.val := legal.trans (A.consistent j).symm
  have passed := (eq_raw_bits_exact raw (A.read j).result.val).1.mpr same
  unfold paidMountedQuery
  dsimp only
  rw [if_pos passed]

def mountedOracle : CompletedOracle G ell F hf :=
  completedOracle G hf F positive (fun a b h=>addressedReceipt G hf F a b (R a b h))

include legal in
theorem legal_mount_matches_original_oracle :
    (paidMountedQuery G hf F positive R A i j raw).result =
      (mountedOracle G hf F positive R).reply i j raw := by
  have h := (gateway_reply_exact G hf F positive
    (fun a b g=>addressedReceipt G hf F a b (R a b g)) i j raw legal).1
  exact (congrArg Meter.result (legal_query_is_actual_mount_meter G hf F positive R A i j raw legal)).trans h.symm

include legal in
theorem public_legal_reply_pays_every_mount :
    (∑ g : Fin 64, groupCharge G i j (R i j g)) ≤
      (paidMountedQuery G hf F positive R A i j raw).steps := by
  rw [legal_query_is_actual_mount_meter G hf F positive R A i j raw legal]
  have lower := all_sixty_four_installs_and_runs_are_paid G hf F i j positive (R i j)
  change _≤(A.read j).steps+(eqRawBits raw (A.read j).result.val).steps+
    (mountedSlot G hf F i j positive (R i j)).steps+4
  omega

#print axioms legal_query_is_actual_mount_meter
#print axioms legal_mount_matches_original_oracle
#print axioms public_legal_reply_pays_every_mount
end
end J6R53PublicMount
