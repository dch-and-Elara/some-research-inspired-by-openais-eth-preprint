import J6R94HeldOwnerProviderFinalStop

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
set_option maxHeartbeats 8500000
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
local instance callbackEqEdge : Fintype c.host.Edge := c.host.finiteEdge

variable (gate : Stamp key prec) (boot : ExactPrintedBoot X M gate)
variable (gateWidth : gate.created.val=base) (hBase : 0<base)

open J6R10Reachable
variable [DecidableEq (Envelope (N sel) (Childs sel) (exteriorChild G ell X.centre X.sample X.group))]
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]

private theorem billed_no_more_than_after_exact_meter_reindex {A : Type} {u v : Meter A} {b : ℕ}
    (eq : u=v) (h : v.steps≤b) : u.steps≤b := (congrArg Meter.steps eq).trans_le h

include boot gateWidth in
theorem selected_positive_provider_uses_kept_actual_uniform_tariff
    (basePos : 0<base) (ord : Fin (ext).edges≃(ext).host.Edge)
    (provide : OwnerInputProvider (T:=T) (pad:=pad) X)
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
    (hn : native≤m) (hs : s=physicalSize m native) (baseFit : base≤C*s)
    (invoked : let input := actualStoppedInputFromKeptTapes X M p w resident owners inj I W units raw axisBits matching
      provide p w (sourceState M p w) stop=⟨some input.result,input.steps⟩) :
    let prep := stoppedPreparationCoefficient (pad:=pad) (s:=s) (C:=C) X K K body arity
    let reader := stoppedReaderCoefficient (pad:=pad) (s:=s) (C:=C) X body arity significant
      (initial.records.length+pathLimit s C)
    (provide p w (sourceState M p w) stop).result.isSome ∧
      (readLeaf (withPaidOwnerLeaves X M basePos ord provide) initial (.step p w) stop).steps≤
        keptOwnerBudget K (vertexCount (ext).host+4*(C*s)) +
        (prep+reader+sourceArithmetic s C (ext))*2^(7*leafH s) := by
  dsimp only at invoked ⊢
  have h := literal_R65_positive_uses_its_kept_tape_producer X M p w
    resident owners inj I W units raw axisBits matching basePos ord provide initial stop positive invoked
  have paid := direct_actual_R65_kept_stop_correct_at_uniform_tariff X M p w gate boot gateWidth basePos
    initial live legal stop positive resident owners inj I W units raw axisBits matching
    widths bodyFit gateFit encoding hn hs baseFit
  refine ⟨?_,billed_no_more_than_after_exact_meter_reindex h paid.2⟩
  rw [invoked]
  rfl

#print axioms selected_positive_provider_uses_kept_actual_uniform_tariff
end
end J6R94HeldOwnerProvider