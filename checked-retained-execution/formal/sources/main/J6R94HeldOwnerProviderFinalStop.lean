import J6R94HeldOwnerProviderUniform

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
local instance finalStopEdge : Fintype c.host.Edge := c.host.finiteEdge

variable (gate : Stamp key prec) (boot : ExactPrintedBoot X M gate)
variable (gateWidth : gate.created.val=base) (hBase : 0<base)

include boot gateWidth hBase in
theorem direct_actual_R65_kept_stop_correct_at_uniform_tariff
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
    let input := actualStoppedInputFromKeptTapes X M p w resident owners inj I W units raw axisBits matching
    let out := readProvidedOnR65Bank X M p w input initial
    let prep := stoppedPreparationCoefficient (pad:=pad) (s:=s) (C:=C) X K K body arity
    let reader := stoppedReaderCoefficient (pad:=pad) (s:=s) (C:=C) X body arity significant
      (initial.records.length+pathLimit s C)
    (T.frame (Path.step p w).reached).decode out.result=reduce (ch).prec f ell ((ch).host.contract X.hf) ∧
      out.steps≤keptOwnerBudget K (vertexCount (ext).host+4*(C*s)) +
        (prep+reader+sourceArithmetic s C (ext))*2^(7*leafH s) := by
  let Y := sourceState M p w
  let V₀ := vertexCount (ext).host+4*(C*s)
  let H := groupHeadersFromOwnedRaw Y (gateHistory T (bootGates X) p) owners I W units raw.rawView axisBits matching
  have count := all_actual_grouped_headers_count_the_parent_vertices X p w Y H.result
  have len : I.order.length=vertexCount c.host := by
    rw [show I.order.length=H.result.raw.length by rw [H.result.same,List.length_map]; rfl]
    exact count
  have len2 : owners.raw.length=vertexCount c.host := by
    rw [owners.exactRows,List.length_map,matching.order,len]
  have V : vertexCount c.host≤V₀ := (actual_leaf_field_width_and_vertices (T:=T) p).2.2
  have ix : (axis T (p.ticket w)).val≤K :=
    (show (axis T (p.ticket w)).val<(dim (p.ticket w)) from (axis T (p.ticket w)).isLt).le.trans widths.axis
  have ow : Y.site.ownerWidth≤K := widths.owner
  have ow3 := Nat.mul_le_mul_left 3 ow
  have keys := Nat.mul_le_mul (show 3*Y.site.ownerWidth+6≤3*K+6 by omega) (len2.trans_le V)
  have gs := Nat.mul_le_mul (len.trans_le V) (physical_group_header_unit_is_monotone ow ix)
  have cap : 256*(K+1)^3+(3+(3*Y.site.ownerWidth+6)*owners.raw.length+
      (3+I.order.length*groupHeaderUnit Y.site.ownerWidth (axis T (p.ticket w)).val)+4)+5≤keptOwnerBudget K V₀ := by
    calc
      _ ≤ 256*(K+1)^3+(3+(3*K+6)*V₀+(3+V₀*groupHeaderUnit K K)+4)+5 :=
        Nat.add_le_add_right (Nat.add_le_add_left (Nat.add_le_add_right
          (Nat.add_le_add (Nat.add_le_add_left keys 3) (Nat.add_le_add_left gs 3)) 4) _) 5
      _ = keptOwnerBudget K V₀ := by unfold keptOwnerBudget; ring
  have old := real_kept_tapes_generate_and_feed_the_same_R65_positive_bank X M p w gate boot gateWidth hBase
    initial live legal stop positive resident owners inj I W units raw axisBits matching
    widths bodyFit gateFit encoding hn hs baseFit
  exact ⟨old.1,old.2.trans (Nat.add_le_add_right cap _)⟩

#print axioms direct_actual_R65_kept_stop_correct_at_uniform_tariff
end
end J6R94HeldOwnerProvider