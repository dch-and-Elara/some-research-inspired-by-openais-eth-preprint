import J6R94ExteriorDebitCap
import J6R94ExteriorDebitIssued
import J6R75OuterTimeHead
import J6R68ActiveInputsBind

/-! Attach only the raw-layout input to the actual public request's
successfully installed bank. No comparison of replies, reinstallation,
or extra entrySource evaluation substitutes for the exact byte Meter. -/
namespace J6R94ExteriorDebit
open scoped Classical Polynomial
open J6R64Active J6R32StatefulArithmetic
open AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R19Retained
open J6R25PreparedSupply J6R32RootGeneratedRegistryInputs J6R34RootAtlas J6R31RootResidentTables
open J6R27OriginalGate J6Mesh J6R49SourceLayout J6R54ExteriorOwner J6R55BootBodies
open J6R30GeneratedRootLayout J6R28GeneratedRootFrame J6R26StablePreparedRoot
open J6R10Repack J6OrientedHost J6R24LegalLayout J6R26DescriptorTree
open J6R32ChildResidentTransfer J6R12CollisionGreedyStep J6R68ActiveInputs
open V8NativeMessage.N2DLabels J6R33StatefulArithmeticPage J6R30ProducedGateRegistry
open J6R54PublicFamily J6R57PublicRequest J6R75OuterTime J6R35RootOrigins
open J6R52FreshExterior J6ActiveRun J6R11Blueprint J6R12Blueprint J6R24MeteredRecursion
open J1PPrinted J6R10Reachable J6R66.BootPeak

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option quotPrecheck false
set_option maxHeartbeats 18000000
set_option maxRecDepth 4900
set_option Elab.async false
noncomputable section

def runWithMeasuredLayoutStock {I Out : Type*}
    (once : Meter I) (build : I→Meter Out) : Meter Out :=
  let go := build once.result
  ⟨go.result,once.steps+go.steps+4⟩

/-- One separate stock emitter may be used around the entire literal
outer run; the same value is available to each actual group. The
statement prices its actual steps and does not promise they are small. -/
theorem independent_layout_stock_is_not_charged_per_group {Input Output : Type*}
    (stock : Meter Input) (entireOuter : Input→Meter Output) :
    runWithMeasuredLayoutStock stock entireOuter=
      ⟨(entireOuter stock.result).result,stock.steps+(entireOuter stock.result).steps+4⟩ := rfl

variable {V : Type} [Fintype V] {m n base native : ℕ} {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q rr cc dd prec kp bw tc tj tw edgew own : ℕ}
variable {W : Widths m native tc tj tw edgew}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (D : Compiled G ell q rr cc dd prec kp bw)
variable (Req : InstalledRequestInputs W D) (pad : ℕ)
local notation "Key" => (KeyWidth kp tc tj)
local notation "Pg" => (pageKeyWidth m+pad)
local notation "Bank" => (PageBank f ell Key prec tw bw Pg)
variable (prior : PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad)) (row : Entry D.mark m native tc tj tw)
local notation "Here" => (actualExterior (W:=W) D row)
local notation "Ext" => (rawCall (W:=W) D row)
local notation "B" => (publishedBank D Req pad prior row)
local instance groupEdge : Fintype (Ext).host.Edge := (Ext).host.finiteEdge
local notation "Header" => (published_head_is_the_actual_raw_header D Req pad prior row)
variable (sync : prior.synced) (reserved : ∀ x∈prior.headers,x.id.bits.take kp≠D.mark.bits)
variable (written : row∈Req.requests.rows)
variable {name : SourceVertex P→Word own} (stock : RootLayoutStock P name)

include sync reserved written in
theorem the_live_atlas_belongs_to_the_already_paid_request :
    IsLive ((Here).seed pad) B :=
  (accepted_entry_installs_that_actual_job D Req pad prior row sync reserved written).2.1

/-- These are the actual operands returned by the earlier execution.
Their two equations are proof data only; the runtime never evaluates
their source normal forms to obtain these values. -/
structure PublicExteriorOperands where
  source : StableExterior G ell q rr cc dd edgew tc tj Key prec tw bw
  bank : PageBank f ell Key prec tw bw (pageKeyWidth m+pad)
  sourceIsActual : source=actualExterior (W:=W) D row
  bankIsReturned : bank=publishedBank D Req pad prior row

variable (O : PublicExteriorOperands D Req pad prior row)
local notation "Real" => (O.source)
local notation "On" => (exteriorChild G ell (Real).centre (Real).sample (Real).group)
local instance receivedEdge : Fintype (On).host.Edge := (On).host.finiteEdge

theorem received_exterior_has_the_same_header :
    OwnsHeader (Real).header.result O.bank := by
  rw [O.sourceIsActual,O.bankIsReturned]
  exact Header

include sync reserved written in
theorem received_exterior_keeps_the_actual_live_atlas :
    IsLive ((Real).seed pad) O.bank := by
  rw [O.sourceIsActual,O.bankIsReturned]
  exact the_live_atlas_belongs_to_the_already_paid_request D Req pad prior row sync reserved written

theorem received_exterior_uses_the_original_issued_word :
    row.id=(Real).issue.result := by
  rw [O.sourceIsActual]
  exact (entry_source_is_actual (W:=W) D row).2.2.2.1.symm

def actualPublicIngress (rank bits : ℕ) (fit : Fintype.card (On).host.Edge<2^rank) :
    Ingress (printedExteriorFull64 Real pad stock rank bits fit) :=
  exteriorIngressFromIssued Real pad stock O.bank
    (received_exterior_keeps_the_actual_live_atlas D Req pad prior row sync reserved written O)
    (received_exterior_has_the_same_header D Req pad prior row O)
    row.id (received_exterior_uses_the_original_issued_word D Req pad prior row O) rank bits fit

theorem raw_debit_on_this_actual_public_group (rank bits K : ℕ)
    (fit : Fintype.card (On).host.Edge<2^rank)
    (widths : ExteriorInputWidths Real pad stock O.bank K) (paid : Meter IngressBytes)
    (uses : paid=(actualPublicIngress D Req pad prior row sync reserved written stock O rank bits fit).paid) :
    paid.steps≤ installedExteriorRawRoof K := by
  let l := received_exterior_keeps_the_actual_live_atlas D Req pad prior row sync reserved written O
  let h := received_exterior_has_the_same_header D Req pad prior row O
  let t := received_exterior_uses_the_original_issued_word D Req pad prior row O
  exact same_paid_root_operand_has_derived_rawDebit Real pad stock O.bank
    l h rank bits K fit widths paid
    (uses.trans (actual_issued_word_uses_the_same_checked_ingress Real pad stock O.bank l h row.id t rank bits fit))

#print axioms independent_layout_stock_is_not_charged_per_group
#print axioms the_live_atlas_belongs_to_the_already_paid_request
#print axioms received_exterior_has_the_same_header
#print axioms received_exterior_keeps_the_actual_live_atlas
#print axioms received_exterior_uses_the_original_issued_word
#print axioms actualPublicIngress
#print axioms raw_debit_on_this_actual_public_group
end
end J6R94ExteriorDebit

