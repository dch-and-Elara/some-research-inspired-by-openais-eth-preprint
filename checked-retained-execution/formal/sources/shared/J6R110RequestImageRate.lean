import J6R57PublicRequestImage
import J6R57PublicRequestBounds

/-! Charge the shared compiler, the one real root cache, and the actual
request catalogue. Only source literal and field costs enter as
arguments to this generic bound, not an unconstrained cache cost. -/
namespace J6R110RequestImageRate
open scoped Classical Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R34RootAtlas J6R52FreshExterior
open J6Mesh J6OrientedHost J6R24LegalLayout J6R14ZeroMode J6R26StablePreparedRoot
open J6R28GeneratedRootFrame J6R27PrescribedProbe J6R54PublicFamily J6R27OriginalGate
open J6R35GatewayPreparation J6R57PublicRequest J6R31RootResidentTables J6R30GeneratedRootLayout
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxRecDepth 4300
set_option maxHeartbeats 18000000

def commonRootClock (m native e q p rr cc dd : ℕ) : ℕ :=
  positiveTapeFee e (literalDegree m native+1)+3+
    residentsFee m q 0 p rr cc dd+storedHalfRowsFee m+6

def catalogueClock (m native kp tc tj tw : ℕ) : ℕ :=
  2+((m+1)*(literalDegree m native+1))*(headRoof m native tc tj tw+203+
    groupRoof (KeyWidth kp tc tj))

noncomputable section
variable {V : Type} [Fintype V] {f : ℤ[X]} {m n base native : ℕ} {T : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) T (constantRootWord m)}
variable {ell q rr cc dd prec kp bw tc tj tw edgew : ℕ}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]

theorem actual_compiled_root_cache_cost (D : Compiled G ell q rr cc dd prec kp bw) :
    (buildCommonRoot D).steps≤commonRootClock m native f.natDegree q
      (J6SourcePrecision.printed m base) rr cc dd := by
  have more : 1<q := copy_width_above_one (by rw [←D.copiesOK]; exact val_lt D.regs.copies)
  have pos : 0<q := Nat.zero_lt_one.trans more
  simpa only [commonRootClock,Nat.zero_add] using (actual_shared_paid G D.literal ell ⟨D.frame,0⟩ pos more D.regs.copies D.regs.pre
    D.copiesOK D.preOK).2.1

theorem compiled_request_image_price_from_two_actual_input_producers
    (W : Widths m native tc tj tw edgew) (I : SharedInputs G ell q rr cc dd prec kp bw) :
    (buildRequestImage W I).steps≤I.literal.steps+I.field.steps+
      precisionFromBaseFee m q+exteriorRegistersFee q q prec+ordinalFee bw I.code+15+
      commonRootClock m native f.natDegree q (J6SourcePrecision.printed m base) rr cc dd+
      catalogueClock m native kp tc tj tw+8 := by
  let D := prepareShared I
  have Dfee : D.steps≤I.literal.steps+I.field.steps+
      precisionFromBaseFee m q+exteriorRegistersFee q q prec+ordinalFee bw I.code+15 := by
    have H := shared_paid_roof I (emitOrdinal bw I.code)
      (emitted_ordinal_exact bw I.code I.codeWordWidthPositive I.codeFit).1
    exact H.trans_eq (by rw [(emitted_ordinal_exact bw I.code I.codeWordWidthPositive I.codeFit).2])
  have H := actual_compiled_root_cache_cost D.result
  have menu : (emitCatalogue W D.result.mark).steps≤catalogueClock m native kp tc tj tw :=
    catalogue_construction_roof W D.result.mark
  have fee : (buildRequestImage W I).steps=
      D.steps+(buildCommonRoot D.result).steps+(emitCatalogue W D.result.mark).steps+8 :=
    (actual_request_image_retains_paid_compilation W I).2.2.2.2.trans
      (compiled_request_cache_exact_fee W I)
  rw [fee]
  omega

#print axioms actual_compiled_root_cache_cost
#print axioms compiled_request_image_price_from_two_actual_input_producers
end
end J6R110RequestImageRate
