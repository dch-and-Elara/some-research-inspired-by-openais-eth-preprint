import J6R53WordIngressCore
import J6R53WordIngressQuery

/-! Strict public specialization to the actual no-template retained
word producer. There is no assumed materialized setup/menu. The typed
mounted machine supplied on the exact produced chart remains explicit. -/
namespace J6R53WordIngress
open scoped Classical Polynomial BigOperators
open Polynomial AOracleMachineTime
open J6Mesh J6OrientedHost J6R24LegalLayout J6R24MeteredRecursion
open J6R26StablePreparedRoot J6R27PrescribedProbe J6R28GeneratedRootFrame
open J6R34OfficialGateway J6R14ZeroMode J6R36SharedGateway
open J6R32RootGeneratedRegistryInputs J6R53PublicMount J6R52FreshExterior
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 3300
set_option maxHeartbeats 15000000
set_option linter.unusedSectionVars false
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {f : ℤ[X]} {m n base native : ℕ} {T : Plant V m n}
variable (G : RootShape f m (printedHalf m) base native (printedRankWidth m) T (constantRootWord m))
variable {ell q rr cc dd edgew tc tj key prec tw bw rate pad : ℕ}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (hf : f.Monic) (F : Frame f (J6SourcePrecision.printed m base)) (positive : 0<ell)

abbrev RetainedFamily (ell q rr cc dd edgew tc tj key prec tw bw rate pad : ℕ) :=
  ∀ i j g, RetainedMounted G ell q rr cc dd edgew tc tj key prec tw bw rate pad i j g

variable (R : RetainedFamily G ell q rr cc dd edgew tc tj key prec tw bw rate pad)
variable (A : SuppliedProbeBits (rootPreset G ell) f.natDegree)

def retainedMountedQuery : SlotProgram (ell:=ell) (F:=F) G :=
  runPaidIngressQuery G hf F positive (fun i j g=>issueRetainedMounted (R i j g)) A

theorem retained_query_is_original_and_pays_words
    (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) (raw : List Bool)
    (legal : raw=List.ofFn ((rootPreset G ell).word j)) :
    let plain := fun i j g=>(issueRetainedMounted (R i j g)).result
    (retainedMountedQuery G hf F positive R A i j raw).result=
      (mountedOracle G hf F positive plain).reply i j raw ∧
    (retainedMountedQuery G hf F positive R A i j raw).steps=
      (paidMountedQuery G hf F positive plain A i j raw).steps+
      ∑ g : Fin 64,(exteriorRegistersFee (R i j g).oldWidth q prec+11) := by
  dsimp only
  have H := legal_ingress_exact_output_and_bill G hf F positive
    (fun i j g=>issueRetainedMounted (R i j g)) A i j raw legal
  refine ⟨legal_ingress_exact_original_oracle G hf F positive
    (fun i j g=>issueRetainedMounted (R i j g)) A i j raw legal,?_⟩
  unfold retainedMountedQuery
  rw [H]
  change (∑ g : Fin 64,(issueRetainedMounted (R i j g)).steps)+_=_+_
  simp only [issued_retained_fee,Nat.add_comm]

#print axioms retainedMountedQuery
#print axioms retained_query_is_original_and_pays_words
end
end J6R53WordIngress

