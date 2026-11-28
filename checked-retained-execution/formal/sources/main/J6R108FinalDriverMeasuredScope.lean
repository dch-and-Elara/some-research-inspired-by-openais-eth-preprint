import J6R108FinalDriverPaidSetup
import J6R108FinalDriverScopeDemand
import J6R102FinalPhaseCode
import J6R102NativeCodeMeterBounds
import J6R85ScopeProducerBind

/-! First and next issuers are constructed, not extra promises on the
selected group. The actual R55 first emitter and measured selected
dispatch are both run by the R102 metered native-code machine. -/
namespace J6R108FinalDriver
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R21Leaf J6OrientedHost
open J6Mesh J6R34RootAtlas J6R35RootOrigins J6R26DescriptorTree J6R34ChildPath
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R24MeteredRecursion
open J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R48DFS
open J6R9Recursive J6R50SourceProducer J6R51Online J6R52FreshExterior
open J6R57PublicRequest J6R54PublicFamily J6R22Active
open J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R31RootResidentTables J6R28GeneratedRootFrame
open J6R32RootGeneratedRegistryInputs J6R37StructuredRoot J6R41StructuredAllPaths
open J6R55CachedLedger J6R56PrintedExponent J6R49Cost J6R16ModeCost J6R10Reachable
open J6R62ActivePrep J6R64Active J6R66Active J6R66.BootPeak J6R57Public
open J6R67UnifiedRate J6R68ActiveInputs J6R68ActiveInputs.Sweep J6R57ScopeFee
open J6R102FinalPhase J6R79Numeric J6R110ScopeWordRates J6R111SelectedGroup
open J6R88ScopeCode J6R66LeafTariff J6R85ScopeProducer
open J6R110CanonicalCoverage J6R110CanonicalMount J6R109CanonicalProbeTable
open J6R75OuterTime J6R14ZeroMode J6R55Public
open J6R102NativeCodeMeter J6R92NativeWidth J6R55TerminalBootJoined J6R55BootBodies
open J6R55TerminalOrigin J6R53OldOwnerRoot J6R54ExteriorOwner J6R54TerminalBoot

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 4900
set_option maxHeartbeats 8500000
set_option pp.maxSteps 1100
set_option maxSynthPendingDepth 12
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ} {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q rr cc dd prec kp bw tc tj tw edgew : ℕ}
variable {W : Widths m native tc tj tw edgew}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (D : Compiled G ell q rr cc dd prec kp bw) (S : InstalledRequestInputs W D)
variable (pad : ℕ)
variable (prior : PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad))
variable {rate : ℕ}
variable (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) (g : Fin 64)
variable {T : Prepared G.bounds (G.selector ell) (exteriorChild G ell i j g) (literalSite W D i j g).hf}

local instance measuredScopeR108Decision :
    DecidableEq (J6R10Reachable.Envelope (N (G.selector ell)) (Childs (G.selector ell)) ((exteriorChild G ell i j g))) :=
  J6R24MeteredRecursion.sourceDecision (G.selector ell) (exteriorChild G ell i j g)

variable {ownerWidth rank : ℕ} {rootName : SourceVertex P→Word ownerWidth}
variable (gate : Stamp (KeyWidth kp tc tj) prec)
variable (root : RootRoster (P:=P) gate pad rootName)


variable (rootInj : Function.Injective rootName)
variable (basePos : 0<base)
variable (edgeOrder : Fin (exteriorChild G ell i j g).edges ≃ (exteriorChild G ell i j g).host.Edge)
variable (handoff : PaidKeptHandoff (T:=T) (pad:=pad) (literalSite W D i j g))
variable (data : SelectedR55Operands D pad i j g gate root T rate)
variable (bank : PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad))
variable (live : IsLive ((literalSite W D i j g).seed pad) bank)

local notation "Lit" => (literalSite W D i j g)
local notation "Receiver" => (exteriorChild G ell i j g)
local notation "Wrapped" => (withSelectedDemands data.bodyMachine data.demandSource)
local notation "Bodies" => (publicIssuedBodyProgram W D i j g pad gate data.firstBodies)
local notation "Owners" => (ownerWordsWithPublicIssuer W D i j g pad gate root data.firstBodies data.firstOwners)
local notation "BeforeStop" =>
  (selectedPublicBeforeStopAtReturn D pad i j g gate root data.bodyMachine data.firstBodies data.firstOwners
    rootInj data.demandSource bank live)
local notation "Previous" =>
  (withMinimalNativeCode (Lit) gate pad root (Wrapped) (Bodies) (Owners) bank live rootInj)
local notation "Selected" => (withPaidOwnerLeaves (Lit) (BeforeStop) basePos edgeOrder (keptTapeOwnerProvider (Lit) handoff))
local notation "SourceCode" => (6*Nat.clog 2 (physicalSize m native))
local notation "Scan" => (nativeCodeScanRoof (atlasSourceRoof (physicalSize m native) 2 (Receiver).prec ell
  (pageKeyWidth m+pad) tw bw (SourceCode)))

/-- The scope profile is for the very machine chosen by the physical
R108/R111 setup. A former minimal-code debit is used only with the
proved additional actual scan. The two word bills instead come from
the real R55/R102 callback and its chosen keyed reader. -/
def measuredScopeOfTheSamePaidSelectedGroup
    (nativeFits : native≤m) (baseFits : base≤2*physicalSize m native)
    (Wcap : ScopeWordCaps) (fits : ScopeWordFits (Selected) bank Wcap)
    (K N first boot demand : ℕ)
    (oldBoot : ∀ w : (Plan (G.selector ell)).Slot (Receiver), ((Previous).initial w).steps≤boot)
    (oldDemand : ∀ {c : Call (PhysicalHost f ell)} (p : Path (G.selector ell) (Receiver) c)
      (u : (Plan (G.selector ell)).Slot c) (w : (Plan (G.selector ell)).Slot ((Plan (G.selector ell)).child c u)),
      ((Previous).demand (sourceState (Previous) p u) w).steps≤demand)
    (sizes : ∀ {c : Call (PhysicalHost f ell)} (p : Path (G.selector ell) (Receiver) c)
      (u : (Plan (G.selector ell)).Slot c) (w : (Plan (G.selector ell)).Slot ((Plan (G.selector ell)).child c u)),
      LiteralRequestSizes (data.demandSource (sourceState (Selected) p u) w) K)
    (issuedQuery : ∀ {c : Call (PhysicalHost f ell)} (p : Path (G.selector ell) (Receiver) c)
      (u : (Plan (G.selector ell)).Slot c) (w : (Plan (G.selector ell)).Slot ((Plan (G.selector ell)).child c u)),
      Nonempty (AlreadyInvokedKeyedQuery (data.demandSource (sourceState (Selected) p u) w) K N))
    (firstWords : ∀ u : (Plan (G.selector ell)).Slot (Receiver),
      measuredWordProducers (sourceState (Selected) (Path.root : Path (G.selector ell) (Receiver) (Receiver)) u).input≤first) :
    MeasuredScopeInputs (Selected) bank := by
  let current := (Selected)
  let op := (BeforeStop)
  let previous := (Previous)
  have exactWork : ActualR55R102Demand data.demandSource current := by
    intro v Y w
    exact configured_R108_exposes_the_actual_R110_demand_meter D pad i j g gate root
      data.bodyMachine data.firstBodies data.firstOwners rootInj data.demandSource basePos edgeOrder
      (keptTapeOwnerProvider (Lit) handoff) bank live Y w
  have both := same_selected_machine_supplies_query_and_source_word_fields
    data.demandSource current exactWork K N first
    (fun {_} p u w=>sizes p u w) (fun {_} p u w=>issuedQuery p u w) firstWords
  refine measuredScopeWithPrintedAtlas current bank Wcap fits (SourceCode)
    (boot+(Scan)) (demand+(Scan)) (actualSidecarRoof K N) (max first (descendantSourceWordsRoof K))
    ?_ ?_ ?_ (fun {_} p u w=>both.1 p u w) (fun {_} p u=>both.2 p u)
  · intro c p w
    change (sourceState (Selected) p w).input.code≤(SourceCode)
    rw [paid_owner_leaf_keeps_actual_source (Lit) op basePos edgeOrder
      (keptTapeOwnerProvider (Lit) handoff) p w]
    have code := all_selected_stored_sites_are_exactly_r92 (Lit) gate pad (Bodies)
      root (Wrapped) (Owners) bank live rootInj p w
    change sourceState op p w=sourceState previous p w at code
    rw [code]
    have receiver : (Receiver).prec≤161*2*(physicalSize m native)^2 :=
      literal_exterior_start_precision_quadratic (Lit) nativeFits (by decide) baseFits
    exact (same_new_runtime_fits_actual_native_label_bound (Lit) gate pad root (Wrapped) (Bodies)
      (Owners) bank live rootInj p w).trans
      (canonical_code_logarithmic_at_real_printed_receiver (physicalSize m native) 2 (Receiver).prec
        (root_lambda_large G.bounds) G.bounds.constSmall receiver)
  · intro w
    change (op.initial w).steps≤boot+(Scan)
    exact (actual_first_callback_has_only_polynomial_extra (Lit) gate pad (Bodies) root (Wrapped)
      (Owners) bank live rootInj rfl nativeFits baseFits w).trans
      (Nat.add_le_add_right (oldBoot w) _)
  · intro c p u w
    change ((Selected).demand (sourceState (Selected) p u) w).steps≤demand+(Scan)
    rw [paid_owner_leaf_keeps_actual_source (Lit) op basePos edgeOrder
      (keptTapeOwnerProvider (Lit) handoff) p u]
    change (op.demand (sourceState op p u) w).steps≤demand+(Scan)
    exact (actual_reached_demand_callback_has_only_polynomial_extra (Lit) gate pad (Bodies) root (Wrapped)
      (Owners) bank live rootInj rfl nativeFits baseFits p u w).trans
      (Nat.add_le_add_right (oldDemand p u w) _)

#print axioms measuredScopeOfTheSamePaidSelectedGroup
end
end J6R108FinalDriver

