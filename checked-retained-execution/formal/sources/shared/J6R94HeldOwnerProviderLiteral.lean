import J6R94HeldOwnerProviderRun
import J6R94HeldOwnerProviderProduced
import J6R94HeldOwnerProviderRetainLayout

/-! Use the actual carried layout and full roster to produce the true grouped table directly at the same stopped occurrence. No old whole-provider price is imported. -/
namespace J6R94HeldOwnerProvider
open scoped Polynomial Classical
open Polynomial AOracleMachineTime A1R12 J6R15ModeCost J6R21Ancestor J6R21Leaf J6OrientedHost
open J6Mesh J6R34RootAtlas J6R35RootOrigins J6R26DescriptorTree J6R34ChildPath
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R24MeteredRecursion
open J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R48DFS
open J6R50Leaf J6R50SourceProducer J6R51Leaf J6R51Online J6R49Leaf J6R48Leaf
open J6R57Public J6R58LeafScale J6R62Leaf J6R27OriginalGate J6R36ChildFramedRoute J6R54TerminalBoot
open J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R31RootResidentTables
open J6R32RootGeneratedRegistryInputs J6R37StructuredRoot J6R41StructuredAllPaths
open J6R52Terminal J6R53TerminalGate J6R53OldOwner J6R49SourceLayout J6R66LeafTariff J6R65LeafRate
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 41000000
set_option maxRecDepth 5500
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q ro co de edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q ro co de edgew tc tj key prec tw bw)
variable {pad s C rate : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
variable (M : OnlineMachine T key prec tw bw (pageKeyWidth m+pad) rate)
variable {c : Call (PhysicalHost f ell)}
variable (p : Path sel (exteriorChild G ell X.centre X.sample X.group) c)
variable (w : (Plan sel).Slot c)
local notation "ext" => (exteriorChild G ell X.centre X.sample X.group)
local notation "Bank" => (PageBank f ell key prec tw bw (pageKeyWidth m+pad))
local notation "Cmd" => (ReadCmd key (pageKeyWidth m+pad))
local notation "deg" => (4*Nat.clog 2 s)
local notation "ch" => (p.ticket w).child

open J6R52CacheWhole J6R51ParentFrames J6R82LayoutDebit J6R82LeafTime
open J6R9Recursive J6R58LeafScale J6R16ModeCost J6R14LayoutCost J6R68ActiveInputs
open V8NativeMessage.N2DLabels J6R10Repack
local instance cFintype : Fintype c.host.Edge := c.host.finiteEdge

def actualStoppedInputFromKeptTapes
    (resident : ResidentBank (sourceState M p w))
    (owners : CompleteRoster (sourceState M p w).site.oldKey
      (parentData (sourceState M p w) (gateHistory T (bootGates X) p)))
    (inj : Function.Injective (sourceState M p w).site.oldKey)
    (I : CallFormat (printedParams (f:=f) (ell:=ell) s) c)
    (W : Ingress I) (units : ℕ) {a cp wid edges : ℕ}
    (raw : KeptLayoutWords a cp wid edges) (axisBits : List Bool)
    (matching : ExistingRosterLabels (sourceState M p w) (gateHistory T (bootGates X) p)
      owners I W units raw.rawView axisBits) :
    Meter (OwnerTerminalInput X p w (sourceState M p w)) :=
  let Y := sourceState M p w
  let heads := groupHeadersFromOwnedRaw Y (gateHistory T (bootGates X) p) owners I W units raw.rawView axisBits matching
  let F := mountResident Y resident
  ⟨⟨F.result,heads.result,owners,inj⟩,F.steps+heads.steps+5⟩

variable (gate : Stamp key prec) (boot : ExactPrintedBoot X M gate)
variable (gateWidth : gate.created.val=base) (hBase : 0<base)

include boot gateWidth hBase in
theorem real_kept_tapes_generate_and_feed_the_same_R65_positive_bank
    (initial : Bank) (live : IsLive (X.seed pad) initial) (legal : ReadyOnStack (borns M) initial)
    (stop : ((Plan sel).child c w).edges≤(printedParams (f:=f) (ell:=ell) s).cutoff)
    (positive : 0<((Plan sel).child c w).edges)
    (resident : ResidentBank (sourceState M p w))
    (owners : CompleteRoster (sourceState M p w).site.oldKey
      (parentData (sourceState M p w) (gateHistory T (bootGates X) p)))
    (inj : Function.Injective (sourceState M p w).site.oldKey)
    (I : CallFormat (printedParams (f:=f) (ell:=ell) s) c)
    (W : Ingress I) (units : ℕ) {a cp wid edges : ℕ}
    (raw : KeptLayoutWords a cp wid edges) (axisBits : List Bool)
    (matching : ExistingRosterLabels (sourceState M p w) (gateHistory T (bootGates X) p)
      owners I W units raw.rawView axisBits)
    {K body arity significant : ℕ}
    (widths : LocalOwnerGeometry X p w (sourceState M p w) K)
    (bodyFit : observedFrameWidth (mountResident (sourceState M p w) resident).result.rows≤body)
    (gateFit : observedGateWidth owners.raw≤arity)
    (encoding : ActualEncodingFits (stackBank (borns M) initial (.step p w)) significant)
    (hn : native≤m) (hs : s=physicalSize m native) (baseFit : base≤C*s) :
    let Y := sourceState M p w
    let input := actualStoppedInputFromKeptTapes X M p w resident owners inj I W units raw axisBits matching
    let out := readProvidedOnR65Bank X M p w input initial
    let prep := stoppedPreparationCoefficient (pad:=pad) (s:=s) (C:=C) X K K body arity
    let reader := stoppedReaderCoefficient (pad:=pad) (s:=s) (C:=C) X body arity significant
      (initial.records.length+pathLimit s C)
    let headers := 3+(3*Y.site.ownerWidth+6)*owners.raw.length+
      (3+I.order.length*groupHeaderUnit Y.site.ownerWidth (axis T (p.ticket w)).val)+4
    (T.frame (Path.step p w).reached).decode out.result=reduce (ch).prec f ell ((ch).host.contract X.hf) ∧
      out.steps≤(256*(K+1)^3+headers+5)+(prep+reader+sourceArithmetic s C (ext))*2^(7*leafH s) := by
  let Y := sourceState M p w
  let input := actualStoppedInputFromKeptTapes X M p w resident owners inj I W units raw axisBits matching
  have hh := (same_raw_roster_and_actual_labels_supply_true_group_headers Y (gateHistory T (bootGates X) p)
    owners I W units raw.rawView axisBits matching).2.2
  let ownInstall := (installResidentBank Y).result
  have rows : resident.rows=ownInstall.rows := resident.exactRows.trans ownInstall.exactRows.symm
  have m : (mountResident Y resident).steps=(mountResident Y ownInstall).steps := by
    rw [mounted_resident_fee,mounted_resident_fee,rows]
  have mc := independently_priced_pre_layout_mount Y K widths.parentEdges widths.childEdges widths.port
    widths.owner widths.axis widths.keyWidth widths.precWidth widths.pageWidth widths.body
  have cap := Nat.add_le_add_right (Nat.add_le_add (m.trans_le mc) hh) 5
  obtain ⟨older,compiled,value,terminal⟩ :=
    provided_source_leaf_value_and_true_finite_cost X M p w gate boot gateWidth hBase initial live legal input stop positive
  have saved : observedFrameWidth input.result.saved.rows≤body := bodyFit
  have gates : observedGateWidth input.result.roster.raw≤arity := gateFit
  have prep := true_positive_preparation_from_chart_dimensions X p w Y input.result
    stop widths.port widths.owner saved gates
  have reader := actual_stacked_ordered_leaf_reader_price X M p w gate boot gateWidth input.result
    initial live legal hn hs baseFit encoding saved gates older compiled
  exact ⟨value,(terminal.trans (structural_leaf_fee_into_printed_rate (K:=6) prep reader)).trans
    (Nat.add_le_add_right cap _)⟩

#print axioms real_kept_tapes_generate_and_feed_the_same_R65_positive_bank
end
end J6R94HeldOwnerProvider