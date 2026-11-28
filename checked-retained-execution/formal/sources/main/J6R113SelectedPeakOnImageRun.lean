import J6R113SelectedPeakOnImageCanonical
import J6R110CanonicalAllPeakRun

/-! Apply the named pause theorem at the literally selected local
program, after proving its exact invocation from this indexed head.
The retained data need the original named source and width receipts. -/
namespace J6R113SelectedPeakOnImage
open scoped Classical Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Leaf J6OrientedHost
open J6Mesh J6R34RootAtlas J6R34ChildPath J6R24MeteredRecursion
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R50SourceProducer
open J6R51Online J6R52FreshExterior J6R57PublicRequest J6R54PublicFamily
open J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe
open J6R28GeneratedRootFrame J6R14ZeroMode J6R34OfficialGateway
open J6R68ActiveInputs.Sweep J6R75OuterTime J6R19Retained J1PPrinted
open J6R31RootResidentTables J6R111SelectedGroup J6R108FinalDriver
open J6R112ExecutedSelectedStartup J6R110CanonicalCoverage J6R110CanonicalMount
open J6R109CanonicalProbeTable J6R32RootGeneratedRegistryInputs J6R12Blueprint J6ActiveRun J6R9Recursive J6R10Reachable
open J6R11Blueprint J6R57Public J6R68ActiveInputs J6R64Active J6R57ScopeFee
open J6R110CanonicalAllPeak J6R54TerminalBoot J6R51Peak J6R52Peak J6R16ModeCost
open J6R66Active J6R68.RecursivePeak J6R75RawPeak J6R48DFS J6R26DescriptorTree

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 5000
set_option maxHeartbeats 37000000
set_option maxSynthPendingDepth 12
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ} {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q rr cc dd prec kp bw tc tj tw edgew : ℕ}
variable {W : Widths m native tc tj tw edgew} {I : SharedInputs G ell q rr cc dd prec kp bw}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (image : RequestImage W I) (plan : SelectedCountOnImage image)
variable (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) (g : Fin 64)

local notation "D" => image.compiled
local notation "S" => image.tables
local notation "A" => (plan.plans i j g)
local notation "Q" => (plan.setups i j g)
local notation "r0" => (sourceRow (W:=W) image.compiled i j g)
local notation "Y" => (actualExterior (W:=W) image.compiled (sourceRow (W:=W) image.compiled i j g))
local notation "Ext" => (exteriorChild G ell (Y).centre (Y).sample (Y).group)
local notation "S0" => ((plan.plans i j g).sel)
local notation "Key" => (KeyWidth kp tc tj)
local notation "Bank" => (PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+plan.pad))

local instance sameSelectedOrder :
    DecidableEq (J6R10Reachable.Envelope (N S0) (Childs S0) Ext) :=
  J6R24MeteredRecursion.sourceDecision S0 Ext

/-- Only the phases of the canonical mounted raw operator are covered.
In particular this does not bound the outer emit/admission/chooser
scratch, the `shared` inputs, or the host allocator. -/
theorem actual_selected_head_has_this_same_canonical_named_peak
    (H : ExactHead m native tc tj tw i j) (same : H=(prepareHead W i j).result)
    {b : Bank} (ack : (submitResidentRow D S plan.pad plan.prior r0).result=some (b,true))
    (own : OwnsHeader (Y).header.result b) {rank width : ℕ}
    (names : CanonicalGroupNames D S plan.pad plan.prior r0 A Q b ack own rank width)
    (gate : Stamp Key prec) (boot : ExactPrintedBoot Y names.beforeStop gate)
    (valid : ReadyOnStack (borns names.beforeStop) b)
    (modeFits : plan.rate≤uniformWidth plan.size plan.constant)
    (supply : HasMeasuredOwnerInputs Y names.beforeStop names.provider)
    (gateWidth : gate.created.val=base)
    (shared pages fixed addr seed owner : ℕ)
    (pageFit : ExactPageFit (withPaidOwnerLeaves Y names.beforeStop names.basePos names.order names.provider) pages)
    (frameFit : EntryWidths (withPaidOwnerLeaves Y names.beforeStop names.basePos names.order names.provider) fixed addr)
    (bootFit : BootBodyWidth (withPaidOwnerLeaves Y names.beforeStop names.basePos names.order names.provider) seed)
    (ownerFit : OwnerWidth (withPaidOwnerLeaves Y names.beforeStop names.basePos names.order names.provider) owner) :
    let sent := emitEntry (D).mark (i,j) H g
    let src := entrySource (W:=W) D r0
    let reply := submitResidentRow D S plan.pad plan.prior r0
    let paid := (Q).paidChosen b ack own
    let native := canonicalPartOnAcceptedRow D S plan.pad plan.prior r0 A Q names
    paidSelectedAtHead D S plan.pad plan.prior plan.plans plan.sync plan.reserved plan.setups i j g H same =
      ⟨native.result.1,sent.steps+(src.steps+(reply.steps+(paid.steps+native.steps)+4)+3)+3⟩ ∧
    ActualPaidCanonicalExteriorNamedPeak Y names.beforeStop names.basePos names.order names.provider
      names.current names.fit names.bytes names.tails b own shared pages fixed addr seed owner := by
  have live : IsLive ((Y).seed plan.pad) b :=
    (actual_public_return_owns_its_literal_seed_and_header D S plan.pad plan.prior
      i j g plan.sync plan.reserved b ack).1
  have used := actual_paid_head_uses_that_successful_continuation image plan i j g H same b ack own
  have samePaid := same_ack_consumes_the_one_named_canonical_part D S plan.pad plan.prior r0 A Q names
  dsimp only [continuationOfTheSelectedHead] at used
  dsimp only at samePaid ⊢
  rw [samePaid] at used
  exact ⟨used,paper6_actual_paid_canonical_exterior_has_named_phase_maximum
    Y names.beforeStop names.basePos names.order names.provider gate boot names.current names.fit
    names.bytes names.tails b own live valid modeFits supply gateWidth shared pages fixed addr seed owner
    pageFit frameFit bootFit ownerFit⟩

#print axioms actual_selected_head_has_this_same_canonical_named_peak
end
end J6R113SelectedPeakOnImage

