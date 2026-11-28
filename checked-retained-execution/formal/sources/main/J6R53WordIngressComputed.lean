import J6R53WordIngressQuery
import J6R52FreshExteriorWordsComputedShell
import J6R52FreshExteriorWordsFee

/-! Optional arithmetic ingress: the actual mounted group consumes
its exact attachment computed from the base tape; an already computed
printed-precision field is not an input to this producer. -/
namespace J6R53WordIngress
open scoped Classical Polynomial BigOperators
open Polynomial AOracleMachineTime J6Mesh J6OrientedHost
open J6R24LegalLayout J6R24MeteredRecursion J6R26StablePreparedRoot
open J6R28GeneratedRootFrame J6R34RootAtlas J6R30GeneratedRootLayout
open J6R52FreshExterior J6R53PublicMount J6R15ModeCost
open J6R14ZeroMode J6R33OriginalJ6 J6R32RootGeneratedRegistryInputs J6R36SharedGateway J6R27PrescribedProbe
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 3200
set_option maxHeartbeats 15000000
set_option linter.unusedSectionVars false
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {f : ℤ[X]} {m n base native : ℕ} {T : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) T (constantRootWord m)}
variable {ell q rr cc dd edgew tc tj key prec tw bw rate pad : ℕ}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]

structure BaseMounted (G : RootShape f m (printedHalf m) base native (printedRankWidth m)
    T (constantRootWord m)) (ell q rr cc dd edgew tc tj key prec tw bw rate pad : ℕ)
    (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) (g : Fin 64) where
  outside : SetupOutsideWords G ell edgew tc tj key tw bw
  raw : LiteralPortFile T rr cc dd
  baseWord : Word q
  baseTag : baseWord.val=base
  copyFit : K m<2^q
  preFit : J6SourcePrecision.printed m base<2^q
  birthFit : J6SourcePrecision.printed m base<2^prec
  sameCentre : outside.centre=i
  sameSample : outside.sample.val=j.val
  sameGroup : outside.group=g
  mounted : MountedGroup (rate:=rate) (pad:=pad) G
    (attachWithComputedPaidWords (prec:=prec) outside raw baseWord baseTag copyFit preFit birthFit).result

variable {i : J6Recovery.Addr m} {j : Fin (literalDegree m native+1)} {g : Fin 64}
variable (R : BaseMounted G ell q rr cc dd edgew tc tj key prec tw bw rate pad i j g)

def baseAttachment : Meter (StableExterior G ell q rr cc dd edgew tc tj key prec tw bw) :=
  attachWithComputedPaidWords R.outside R.raw R.baseWord R.baseTag R.copyFit R.preFit R.birthFit

def issueBaseMounted : Meter (AddressGroup (ell:=ell) (q:=q) (rr:=rr) (cc:=cc) (dd:=dd)
    (edgew:=edgew) (tc:=tc) (tj:=tj) (key:=key) (prec:=prec) (tw:=tw) (bw:=bw)
    (rate:=rate) (pad:=pad) G i j g) :=
  let S := baseAttachment R
  let h := computed_paid_words_attached_same_occurrence R.outside R.raw
    R.baseWord R.baseTag R.copyFit R.preFit R.birthFit
  ⟨⟨S.result,R.mounted,h.2.1.trans R.sameCentre,(congrArg Fin.val h.2.2.1).trans R.sameSample,
    h.2.2.2.1.trans R.sameGroup⟩,S.steps+3⟩

theorem issued_base_uses_same_site :
    (issueBaseMounted R).result.source=(baseAttachment R).result ∧
      (issueBaseMounted R).result.source.source.raw=R.raw.raw := ⟨rfl,rfl⟩

theorem issued_base_fee_le :
    (issueBaseMounted R).steps≤precisionFromBaseFee m q+exteriorRegistersFee q q prec+15 := by
  have H := computed_exterior_registers_fee_le m prec
    (Nat.zero_lt_one.trans (copy_width_above_one R.copyFit)) R.baseWord
  change (computeExteriorRegisters m prec R.baseWord).steps+8+3≤_
  omega

variable (hf : f.Monic) (F : Frame f (J6SourcePrecision.printed m base)) (positive : 0<ell)
variable (P : ∀ i j g,BaseMounted G ell q rr cc dd edgew tc tj key prec tw bw rate pad i j g)
variable (A : SuppliedProbeBits (rootPreset G ell) f.natDegree)

def baseMountedQuery : SlotProgram (ell:=ell) (F:=F) G :=
  runPaidIngressQuery G hf F positive (fun i j g=>issueBaseMounted (P i j g)) A

theorem base_query_is_original_and_pays_words
    (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) (raw : List Bool)
    (legal : raw=List.ofFn ((rootPreset G ell).word j)) :
    let plain := fun i j g=>(issueBaseMounted (P i j g)).result
    (baseMountedQuery hf F positive P A i j raw).result=
      (mountedOracle G hf F positive plain).reply i j raw ∧
    (baseMountedQuery hf F positive P A i j raw).steps=
      (paidMountedQuery G hf F positive plain A i j raw).steps+
      (∑ g : Fin 64,(issueBaseMounted (P i j g)).steps) := by
  dsimp only
  have H := legal_ingress_exact_output_and_bill G hf F positive
    (fun i j g=>issueBaseMounted (P i j g)) A i j raw legal
  refine ⟨legal_ingress_exact_original_oracle G hf F positive
    (fun i j g=>issueBaseMounted (P i j g)) A i j raw legal,?_⟩
  unfold baseMountedQuery
  rw [H]
  exact Nat.add_comm _ _

#print axioms issueBaseMounted
#print axioms issued_base_uses_same_site
#print axioms issued_base_fee_le
#print axioms base_query_is_original_and_pays_words
end
end J6R53WordIngress

