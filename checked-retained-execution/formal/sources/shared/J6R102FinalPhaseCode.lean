import J6R92NativeWidthJoined
import J6R85ScopeProducerBind

/-! The measured scope is assembled for the runtime that actually
chooses the R92 least native mode widths and then uses the unchanged
R65 stopping branch. A code-width/atlas bound for a different input
cannot be transferred to this runtime. -/
namespace J6R102FinalPhase
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R26DescriptorTree
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R34RootAtlas
open J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun
open J6R24MeteredRecursion J6R51Online J6R50SourceProducer J6R49SourceLayout
open J6R30ProducedGateRegistry J6R54PublicFamily J6R57ScopeFee J6R88ScopeCode
open J6R55BootBodies J6R55TerminalOrigin J6R48GeneratedAddons
open J6Mesh J6OrientedHost J6R24LegalLayout J6R31RootResidentTables
open J6R26StablePreparedRoot J6R28GeneratedRootFrame J6R32RootGeneratedRegistryInputs
open J6R35RootOrigins J6R55TerminalBootJoined J6R53OldOwnerRoot J6R54TerminalBoot J6R54ExteriorOwner
open J6R85ScopeProducer J6R66LeafTariff J6R92NativeWidth J6R57Public J6R67UnifiedRate J6R16ModeCost

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxRecDepth 4900
set_option maxHeartbeats 19000000
set_option maxSynthPendingDepth 12

noncomputable section
variable {V : Type} [Fintype V]
variable {f : ℤ[X]} {m n base native : ℕ} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q ro co de edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q ro co de edgew tc tj key prec tw bw)
variable (gate : Stamp key prec) (pad : ℕ)
variable {s C : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
local notation "Ext" => (exteriorChild G ell X.centre X.sample X.group)
local notation "Pg" => (pageKeyWidth m+pad)
local instance sourceEq : DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel) (Ext)) :=
  J6R24MeteredRecursion.sourceDecision sel Ext
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable {own rate : ℕ} {rootName : SourceVertex P→Word own}
variable (root : RootRoster (P:=P) gate pad rootName)
variable (M : OnlineMachine T key prec tw bw (pageKeyWidth m+pad) rate)
variable (A : FirstBodyProgram X gate pad T)
variable (D : OwnerWordsAtBodies X gate pad root A)
variable (B : PageBank f ell key prec tw bw (pageKeyWidth m+pad))
variable (live : IsLive (X.seed pad) B) (rootInj : Function.Injective rootName)
variable (basePos : 0<base)
variable (ord : Fin (exteriorChild G ell X.centre X.sample X.group).edges ≃
  (exteriorChild G ell X.centre X.sample X.group).host.Edge)
variable (provide : OwnerInputProvider (T:=T) (pad:=pad) X)
local notation "Wired" => (withMinimalNativeCode X gate pad root M A D B live rootInj)
local notation "Chosen" => (withPaidOwnerLeaves X (withMinimalNativeCode X gate pad root M A D B live rootInj) basePos ord provide)

theorem terminating_source_keeps_the_exact_selected_printed_boot :
    ExactPrintedBoot X (Wired) gate :=
  selected_first_factory_is_still_the_original_body_and_owner_mount X gate pad root M A D B live rootInj

theorem stopped_runtime_uses_the_selected_native_width
    (physicalSizeEq : s=physicalSize m native) (nativeFits : native ≤ m) (baseFit : base ≤ C*s)
    {c : Call (PhysicalHost f ell)} (p : Path sel Ext c) (w : (Plan sel).Slot c) :
    (sourceState (Chosen) p w).input.code ≤ 6*Nat.clog 2 s := by
  rw [paid_owner_leaf_keeps_actual_source X (Wired) basePos ord provide]
  have receiver : (Ext).prec ≤ 161*C*s^2 := by
    rw [physicalSizeEq] at baseFit ⊢
    exact literal_exterior_start_precision_quadratic X nativeFits cfg.constPos baseFit
  exact (same_new_runtime_fits_actual_native_label_bound X gate pad root M A D B live rootInj p w).trans
    (canonical_code_logarithmic_at_real_printed_receiver s C (Ext).prec
      (root_lambda_large cfg) cfg.constSmall receiver)

/-- Nothing measures old callbacks by their values: all four fee bounds
refer to the concrete machine that will be used by R68. The atlas
and numerical mode width are computed from its own source geometry. -/
def measuredScopeForActualSelectedNativeCode
    (W : ScopeWordCaps) (fit : ScopeWordFits (Chosen) B W)
    (physicalSizeEq : s=physicalSize m native) (nativeFits : native ≤ m) (baseFit : base ≤ C*s)
    (first next queries words : ℕ)
    (hFirst : ∀ w : (Plan sel).Slot Ext, ((Chosen).initial w).steps ≤ first)
    (hNext : ∀ {c : Call (PhysicalHost f ell)} (p : Path sel Ext c) (u : (Plan sel).Slot c)
      (w : (Plan sel).Slot ((Plan sel).child c u)), ((Chosen).demand (sourceState (Chosen) p u) w).steps ≤ next)
    (hQuery : ∀ {c : Call (PhysicalHost f ell)} (p : Path sel Ext c) (u : (Plan sel).Slot c)
      (w : (Plan sel).Slot ((Plan sel).child c u)), sidecarQueryBill ((Chosen).demand (sourceState (Chosen) p u) w).result ≤ queries)
    (hWords : ∀ {c : Call (PhysicalHost f ell)} (p : Path sel Ext c) (w : (Plan sel).Slot c),
      measuredWordProducers (sourceState (Chosen) p w).input ≤ words) :
    MeasuredScopeInputs (Chosen) B :=
  measuredScopeWithPrintedAtlas (Chosen) B W fit (6*Nat.clog 2 s) first next queries words
    (fun p w=>stopped_runtime_uses_the_selected_native_width X gate pad root M A D B live rootInj
      basePos ord provide physicalSizeEq nativeFits baseFit p w)
    hFirst hNext hQuery hWords

#print axioms terminating_source_keeps_the_exact_selected_printed_boot
#print axioms stopped_runtime_uses_the_selected_native_width
#print axioms measuredScopeForActualSelectedNativeCode
end
end J6R102FinalPhase

