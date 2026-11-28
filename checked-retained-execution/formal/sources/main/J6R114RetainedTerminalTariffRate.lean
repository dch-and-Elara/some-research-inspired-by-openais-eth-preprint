import J6R114RetainedTerminalTariffBase
import J6R82LeafTimeStop
import J6R94HeldOwnerProviderUniform

/-! The measured arithmetic and actual Page reader use the exact words
of the captured leaf. The bounds describe their encoding, not another
oracle or a replacement fee schedule. -/
namespace J6R114RetainedTerminalTariff
open scoped Classical Polynomial
open Polynomial AOracleMachineTime A1R12 J6R15ModeCost J6R21Ancestor J6R21Leaf J6OrientedHost
open J6Mesh J6R34RootAtlas J6R35RootOrigins J6R26DescriptorTree J6R34ChildPath
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R24MeteredRecursion
open J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R48DFS
open J6R50Leaf J6R50SourceProducer J6R51Leaf J6R51Online J6R49Leaf J6R48Leaf
open J6R57Public J6R58LeafScale J6R62Leaf J6R27OriginalGate J6R36ChildFramedRoute J6R54TerminalBoot
open J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R31RootResidentTables
open J6R32RootGeneratedRegistryInputs J6R37StructuredRoot J6R41StructuredAllPaths
open J6R52Terminal J6R53TerminalGate J6R53OldOwner J6R49SourceLayout J6R66LeafTariff J6R65LeafRate
open J6R52CacheWhole J6R51ParentFrames J6R82LayoutDebit J6R82LeafTime
open J6R9Recursive J6R58LeafScale J6R16ModeCost J6R14LayoutCost J6R68ActiveInputs
open V8NativeMessage.N2DLabels J6R10Repack J6R94HeldOwnerProvider J6R110ScopeWordRates
open J6R30ProducedGateRegistry J6R66Active J6R64Active J6R68.RecursivePeak J6R54PeakInput J6R59Public
open J6R51ParentFrames J6R65LeafRate J6R82LeafTime J6R24MeteredRecursion
open J6R111KeptOwnerFlow
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 28000000
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
variable {c : Call (PhysicalHost f ell)}
variable (p : Path sel (exteriorChild G ell X.centre X.sample X.group) c)
variable (w : (Plan sel).Slot c)
variable (M : OnlineMachine T key prec tw bw (pageKeyWidth m+pad) rate)
variable (A : CapturedEntry X p w (sourceState M p w))

variable (gate : Stamp key prec) (boot : ExactPrintedBoot X M gate)

include boot in
theorem actual_retained_positive_leaf_has_the_printed_reader_tariff
    (initial : (PageBank f ell key prec tw bw (pageKeyWidth m+pad))) (bank : A.bank=stackBank (borns M) initial (.step p w))
    (live : IsLive (X.seed pad) initial) (legal : ReadyOnStack (borns M) initial)
    (gateWidth : gate.created.val=base) (basePos : 0<base)
    (hn : native≤m) (hs : s=physicalSize m native) (baseFit : base≤C*s)
    (stop : (p.ticket w).child.edges≤(printedParams (f:=f) (ell:=ell) s).cutoff) (positive : 0<(p.ticket w).child.edges)
    {K body arity significant : ℕ} (geo : LocalOwnerGeometry X p w (sourceState M p w) K)
    (enc : ActualEncodingFits (stackBank (borns M) initial (.step p w)) significant)
    (frameFit : observedFrameWidth (measuredInputFromCapture X p w M A).result.saved.rows≤body)
    (gateFit : observedGateWidth (measuredInputFromCapture X p w M A).result.roster.raw≤arity) :
    let input := measuredInputFromCapture X p w M A
    let out := resumePositive X p w (sourceState M p w) A
    let B := stackBank (borns M) initial (.step p w)
    let prep := stoppedPreparationCoefficient (pad:=pad) (s:=s) (C:=C) X K K body arity
    let read := stoppedReaderCoefficient (pad:=pad) (s:=s) (C:=C) X body arity significant
      (initial.records.length+J6R16ModeCost.pathLimit s C)
    let V₀ := vertexCount (exteriorChild G ell X.centre X.sample X.group).host+4*(C*s)
    ∃ older : List (ReadCmd key (pageKeyWidth m+pad)),
      (oldCompiler X p w (sourceState M p w) input.result).result=some older ∧
      positiveReadBill X p w (sourceState M p w) older B≤read*2^(6*leafH s) ∧
      input.steps≤keptOwnerBudget K V₀ ∧
      out.steps≤keptOwnerBudget K V₀+
        (prep+read+sourceArithmetic s C (exteriorChild G ell X.centre X.sample X.group))*2^(7*leafH s) := by
  let input := measuredInputFromCapture X p w M A
  let desc := bindKept X p w (sourceState M p w) A.labelled A.resident
  let B := stackBank (borns M) initial (.step p w)
  let pref := stoppedPreparationCoefficient (pad:=pad) (s:=s) (C:=C) X K K body arity
  let rr := stoppedReaderCoefficient (pad:=pad) (s:=s) (C:=C) X body arity significant
    (initial.records.length+J6R16ModeCost.pathLimit s C)
  let V₀ := vertexCount (exteriorChild G ell X.centre X.sample X.group).host+4*(C*s)
  obtain ⟨older,compiled,_,fee⟩ := provided_source_leaf_value_and_true_finite_cost
    X M p w gate boot gateWidth basePos initial live legal input stop positive
  have setup : positiveSetup X p w (sourceState M p w) input.result≤pref :=
    true_positive_preparation_from_chart_dimensions X p w (sourceState M p w) input.result stop geo.port geo.owner frameFit gateFit
  have reads : positiveReadBill X p w (sourceState M p w) older B≤rr*2^(6*leafH s) :=
    actual_stacked_ordered_leaf_reader_price X M p w gate boot gateWidth input.result initial live legal
      hn hs baseFit enc frameFit gateFit older compiled
  have measured : input.steps≤keptOwnerBudget K V₀ :=
    actual_kept_owner_input_has_a_uniform_physical_coefficient X M p w desc.resident desc.owners
      desc.names desc.input desc.ingress desc.units desc.raw desc.axisBytes desc.sameChart geo
  refine ⟨older,compiled,reads,measured,?_⟩
  rw [retained_positive_steps_use_the_same_terminal_on_the_live_stack X p w M A initial bank]
  exact (fee.trans (structural_leaf_fee_into_printed_rate (K:=6) setup reads)).trans
    (Nat.add_le_add_right measured _)

#print axioms actual_retained_positive_leaf_has_the_printed_reader_tariff
end
end J6R114RetainedTerminalTariff
