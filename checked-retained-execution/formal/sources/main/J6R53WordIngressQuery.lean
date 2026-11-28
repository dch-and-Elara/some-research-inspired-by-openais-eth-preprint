import J6R53WordIngressCharge
import J6R53PublicMountGateway

/-! Actual legal entry point: charge each produced mounted group in the
same branch that accepts the prescribed raw probe. A rejected prefix
runs the original zero branch and does not charge/execute ingress. -/
namespace J6R53WordIngress
open scoped Classical Polynomial BigOperators
open Polynomial AOracleMachineTime AOracleMachineTimeTape A1R10 A1R12 J6R22Active
open J6Mesh J6OrientedHost J6R24LegalLayout J6R24MeteredRecursion
open J6R26StablePreparedRoot J6R27PrescribedProbe J6R33OriginalJ6 J6R28GeneratedRootFrame
open J6R34OfficialGateway J6R34RootAtlas J6R14ZeroMode J6R36SharedGateway
open J6R32RootGeneratedRegistryInputs J6R53PublicMount J6R27OriginalGate
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 3150
set_option maxHeartbeats 15500000
set_option linter.unusedSectionVars false
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {f : ℤ[X]} {m n base native : ℕ} {T : Plant V m n}
variable (G : RootShape f m (printedHalf m) base native (printedRankWidth m) T (constantRootWord m))
variable {ell q rr cc dd edgew tc tj key prec tw bw rate pad : ℕ}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (hf : f.Monic) (F : Frame f (J6SourcePrecision.printed m base)) (positive : 0<ell)

abbrev PaidMountedFamily (ell q rr cc dd edgew tc tj key prec tw bw rate pad : ℕ) :=
  ∀ i j g, Meter (AddressGroup (ell:=ell) (q:=q) (rr:=rr) (cc:=cc) (dd:=dd)
    (edgew:=edgew) (tc:=tc) (tj:=tj) (key:=key) (prec:=prec) (tw:=tw) (bw:=bw)
    (rate:=rate) (pad:=pad) G i j g)

variable (P : PaidMountedFamily G ell q rr cc dd edgew tc tj key prec tw bw rate pad)
variable (A : SuppliedProbeBits (rootPreset G ell) f.natDegree)

def runPaidIngressQuery : SlotProgram (ell:=ell) (F:=F) G :=
  fun i j raw =>
    let expected := A.read j
    let test := eqRawBits raw expected.result.val
    if test.result then
      let run := mountedSlotPaidIngress G hf F i j positive (P i j)
      ⟨run.result,expected.steps+test.steps+run.steps+4⟩
    else
      let reject := zeroM (ell:=ell) (SiteFrame G ell F i).hp
      ⟨reject.result,expected.steps+test.steps+reject.steps+4⟩

variable (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1))
variable (raw : List Bool) (legal : raw=List.ofFn ((rootPreset G ell).word j))

include legal in
theorem legal_ingress_exact_output_and_bill :
    runPaidIngressQuery G hf F positive P A i j raw =
      addIngressCharge
        (paidMountedQuery G hf F positive (fun i j g=>(P i j g).result) A i j raw)
        (∑ g : Fin 64,(P i j g).steps) := by
  have same : raw=(A.read j).result.val := legal.trans (A.consistent j).symm
  have passed := (eq_raw_bits_exact raw (A.read j).result.val).1.mpr same
  have H := original_slot_adds_each_ingress_once G hf F i j positive (P i j)
  rw [legal_query_is_actual_mount_meter G hf F positive (fun i j g=>(P i j g).result) A i j raw legal]
  unfold runPaidIngressQuery addIngressCharge
  dsimp only
  rw [if_pos passed,H.1,H.2]
  let run := mountedSlot G hf F i j positive (fun g=>(P i j g).result)
  let fee := ∑ g : Fin 64,(P i j g).steps
  let x := (A.read j).steps
  let y := (eqRawBits raw (A.read j).result.val).steps
  change (⟨run.result,x+y+(run.steps+fee)+4⟩ : Meter (Block (SiteFrame G ell F i) ell)) =
    ⟨run.result,fee+(x+y+run.steps+4)⟩
  have eq : x+y+(run.steps+fee)+4=fee+(x+y+run.steps+4) := by omega
  rw [eq]

theorem rejected_ingress_is_original
    (rejected : raw≠List.ofFn ((rootPreset G ell).word j)) :
    runPaidIngressQuery G hf F positive P A i j raw =
      paidMountedQuery G hf F positive (fun i j g=>(P i j g).result) A i j raw := by
  have neq : raw≠(A.read j).result.val := fun e=>rejected (e.trans (A.consistent j))
  have fail : ¬(eqRawBits raw (A.read j).result.val).result :=
    fun h=>neq ((eq_raw_bits_exact raw (A.read j).result.val).1.mp h)
  unfold runPaidIngressQuery paidMountedQuery
  dsimp only
  simp only [if_neg fail]

include legal in
theorem legal_ingress_exact_original_oracle :
    (runPaidIngressQuery G hf F positive P A i j raw).result =
      (mountedOracle G hf F positive (fun i j g=>(P i j g).result)).reply i j raw := by
  have H := legal_ingress_exact_output_and_bill G hf F positive P A i j raw legal
  rw [H]
  exact legal_mount_matches_original_oracle G hf F positive (fun i j g=>(P i j g).result) A i j raw legal

include legal in
theorem legal_ingress_pays_preparation_and_mount :
    (∑ g : Fin 64,(P i j g).steps)+
      (∑ g : Fin 64,groupCharge G i j (P i j g).result) ≤
        (runPaidIngressQuery G hf F positive P A i j raw).steps := by
  rw [legal_ingress_exact_output_and_bill G hf F positive P A i j raw legal]
  exact Nat.add_le_add_left
    (public_legal_reply_pays_every_mount G hf F positive
      (fun i j g=>(P i j g).result) A i j raw legal) _

#print axioms legal_ingress_exact_output_and_bill
#print axioms rejected_ingress_is_original
#print axioms legal_ingress_exact_original_oracle
#print axioms legal_ingress_pays_preparation_and_mount
end
end J6R53WordIngress

