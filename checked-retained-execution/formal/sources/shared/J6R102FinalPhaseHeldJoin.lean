import J6R94HeldOwnerProviderEnd
import J6R65LeafRateCombine

/-! Only the concrete R94 positive-leaf producer can pay for this
stopping branch. The receipt binds the entire metered returned object
to the selected callback at the reached site; an equal decoded
answer or an Origin-only row list supplies no such receipt. -/
namespace J6R102FinalPhase.HeldWiring
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
open J6R52CacheWhole J6R82LeafTime J6R9Recursive J6R16ModeCost J6R94HeldOwnerProvider
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 29000000
set_option maxRecDepth 4900
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
variable (initial : PageBank f ell key prec tw bw (pageKeyWidth m+pad))
local notation "Ext" => (exteriorChild G ell X.centre X.sample X.group)
local notation "SP" => (printedParams (f:=f) (ell:=ell) s)
local instance sourceEq : DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel) (Ext)) :=
  J6R24MeteredRecursion.sourceDecision sel Ext
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
structure HeldAtStop
    (provide : OwnerInputProvider (T:=T) (pad:=pad) X)
    {c : Call (PhysicalHost f ell)}
    (p : Path sel (exteriorChild G ell X.centre X.sample X.group) c) (w : (Plan sel).Slot c)
    (stop : ((Plan sel).child c w).edges ≤ (printedParams (f:=f) (ell:=ell) s).cutoff)
    (K body arity significant : ℕ) where
  resident : ResidentBank (sourceState M p w)
  headers : ParentOwnerHeaders (sourceState M p w).site
  roster : CompleteRoster (sourceState M p w).site.oldKey
    (parentData (sourceState M p w) (gateHistory T (bootGates X) p))
  names : Function.Injective (sourceState M p w).site.oldKey
  widths : LocalOwnerGeometry X p w (sourceState M p w) K
  bodyFits : observedFrameWidth (mountResident (sourceState M p w) resident).result.rows ≤ body
  gateFits : observedGateWidth roster.raw ≤ arity
  encoding : ActualEncodingFits (stackBank (borns M) initial (.step p w)) significant
  used : let chosen := paidHeldOwnerInput X p w (sourceState M p w) resident headers roster names
    provide p w (sourceState M p w) stop=⟨some chosen.result,chosen.steps⟩

theorem selected_held_provider_returns_the_real_owner_data
    (provide : OwnerInputProvider (T:=T) (pad:=pad) X)
    {c : Call (PhysicalHost f ell)}
    (p : Path sel (exteriorChild G ell X.centre X.sample X.group) c) (w : (Plan sel).Slot c)
    (stop : ((Plan sel).child c w).edges ≤ (printedParams (f:=f) (ell:=ell) s).cutoff)
    {K body arity significant : ℕ} (S : HeldAtStop X M initial provide p w stop K body arity significant) :
    (provide p w (sourceState M p w) stop).result.isSome := by
  rw [S.used]
  rfl

theorem the_real_positive_stop_has_the_R94_tariff
    (provide : OwnerInputProvider (T:=T) (pad:=pad) X)
    {c : Call (PhysicalHost f ell)}
    (p : Path sel (exteriorChild G ell X.centre X.sample X.group) c) (w : (Plan sel).Slot c)
    (stop : ((Plan sel).child c w).edges ≤ (printedParams (f:=f) (ell:=ell) s).cutoff)
    (basePos : 0<base)
    (ord : Fin (exteriorChild G ell X.centre X.sample X.group).edges ≃
      (exteriorChild G ell X.centre X.sample X.group).host.Edge)
    (gate : Stamp key prec) (boot : ExactPrintedBoot X M gate) (gateWidth : gate.created.val=base)
    (live : IsLive (X.seed pad) initial) (legal : ReadyOnStack (borns M) initial)
    (positive : 0<((Plan sel).child c w).edges)
    {K body arity significant : ℕ} (S : HeldAtStop X M initial provide p w stop K body arity significant)
    (hn : native ≤ m) (hs : s=physicalSize m native) (baseFit : base ≤ C*s) :
    let prep := stoppedPreparationCoefficient (pad:=pad) (s:=s) (C:=C) X K K body arity
    let reader := stoppedReaderCoefficient (pad:=pad) (s:=s) (C:=C) X body arity significant
      (initial.records.length+pathLimit s C)
    (readLeaf (withPaidOwnerLeaves X M basePos ord provide) initial (.step p w) stop).steps ≤
      combinedLeafBound (s:=s) (C:=C) X (localOwnerBudget K (vertexCount (Ext).host+4*(C*s))) prep reader 6 := by
  let input := paidHeldOwnerInput X p w (sourceState M p w) S.resident S.headers S.roster S.names
  have e := r65_positive_is_the_selected_actual_provider X M p w basePos ord provide initial input stop positive S.used
  dsimp only
  rw [e]
  exact (actual_held_positive_stop_is_correct_and_geometrically_priced X M p w gate boot gateWidth basePos
    initial live legal stop positive S.resident S.headers S.roster S.names S.widths S.bodyFits S.gateFits
    S.encoding hn hs baseFit).2

#print axioms HeldAtStop
#print axioms selected_held_provider_returns_the_real_owner_data
#print axioms the_real_positive_stop_has_the_R94_tariff
end
end J6R102FinalPhase.HeldWiring

