import J6R94HeldOwnerProviderRun

/-! Compose the actual local held owner input, the real R65 stopped bank, and the R82 finite ordered reader bound, without HasMeasuredOwnerInputs or a per-command tariff. -/
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

open J6R52CacheWhole J6R82LeafTime J6R9Recursive J6R58LeafScale
open J6R16ModeCost

variable (gate : Stamp key prec) (boot : ExactPrintedBoot X M gate)
variable (gateWidth : gate.created.val=base) (hBase : 0<base)

include boot gateWidth hBase in
theorem actual_held_positive_stop_is_correct_and_geometrically_priced
    (initial : Bank) (live : IsLive (X.seed pad) initial) (legal : ReadyOnStack (borns M) initial)
    (stop : ((Plan sel).child c w).edges≤(printedParams (f:=f) (ell:=ell) s).cutoff)
    (positive : 0<((Plan sel).child c w).edges)
    (resident : ResidentBank (sourceState M p w))
    (headers : ParentOwnerHeaders (sourceState M p w).site)
    (owners : CompleteRoster (sourceState M p w).site.oldKey
      (parentData (sourceState M p w) (gateHistory T (bootGates X) p)))
    (inj : Function.Injective (sourceState M p w).site.oldKey)
    {K body arity significant : ℕ}
    (widths : LocalOwnerGeometry X p w (sourceState M p w) K)
    (bodyFit : observedFrameWidth (mountResident (sourceState M p w) resident).result.rows≤body)
    (gateFit : observedGateWidth owners.raw≤arity)
    (encoding : ActualEncodingFits (stackBank (borns M) initial (.step p w)) significant)
    (hn : native≤m) (hs : s=physicalSize m native) (baseFit : base≤C*s) :
    let Y := sourceState M p w
    let input := paidHeldOwnerInput X p w Y resident headers owners inj
    let L := readProvidedOnR65Bank X M p w input initial
    let prep := stoppedPreparationCoefficient (pad:=pad) (s:=s) (C:=C) X K K body arity
    let reader := stoppedReaderCoefficient (pad:=pad) (s:=s) (C:=C) X body arity significant
      (initial.records.length+pathLimit s C)
    (T.frame (Path.step p w).reached).decode L.result=reduce (ch).prec f ell ((ch).host.contract X.hf) ∧
      L.steps≤localOwnerBudget K (vertexCount (ext).host+4*(C*s))+
        (prep+reader+sourceArithmetic s C (ext))*2^(7*leafH s) := by
  let Y := sourceState M p w
  let input := paidHeldOwnerInput X p w Y resident headers owners inj
  obtain ⟨older,compiled,value,terminal⟩ :=
    provided_source_leaf_value_and_true_finite_cost X M p w gate boot gateWidth hBase initial live legal input stop positive
  have geometry := genuine_held_owner_input_keeps_paid_objects_and_exact_fee X p w Y resident headers owners inj
  have saved : observedFrameWidth input.result.saved.rows≤body := by
    rw [show input.result.saved=(mountResident Y resident).result from geometry.1]
    exact bodyFit
  have gates : observedGateWidth input.result.roster.raw≤arity := by
    rw [show input.result.roster=owners from geometry.2.2.1]
    exact gateFit
  have owner := real_held_owner_provider_has_geometric_fee X p w Y resident headers owners inj widths
  have prep := true_positive_preparation_from_chart_dimensions X p w Y input.result
    stop widths.port widths.owner saved gates
  have reader := actual_stacked_ordered_leaf_reader_price X M p w gate boot gateWidth input.result
    initial live legal hn hs baseFit encoding saved gates older compiled
  refine ⟨value,?_⟩
  exact (terminal.trans (structural_leaf_fee_into_printed_rate (K:=6) prep reader)).trans
    (Nat.add_le_add_right owner _)

#print axioms actual_held_positive_stop_is_correct_and_geometrically_priced
end
end J6R94HeldOwnerProvider