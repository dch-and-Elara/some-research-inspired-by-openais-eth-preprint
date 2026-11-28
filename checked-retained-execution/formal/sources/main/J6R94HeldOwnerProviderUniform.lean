import J6R94HeldOwnerProviderLiteral

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
local instance uniformEdge : Fintype c.host.Edge := c.host.finiteEdge

/-- Paid same-source stop coefficient; the second term pays for the real
name copy and grouped header extraction once, not another layout run. -/
def keptOwnerBudget (K V₀ : ℕ) : ℕ :=
  256*(K+1)^3+15+(3*K+6+groupHeaderUnit K K)*V₀

theorem physical_group_header_unit_is_monotone {own ix K : ℕ}
    (hOwn : own≤K) (hIx : ix≤K) : groupHeaderUnit own ix≤groupHeaderUnit K K := by
  have u := Nat.mul_le_mul_left 3 hOwn
  have v := Nat.mul_le_mul_left 16 hIx
  unfold groupHeaderUnit
  omega

section ExactProducer
variable (resident : ResidentBank (sourceState M p w))
variable (owners : CompleteRoster (sourceState M p w).site.oldKey
  (parentData (sourceState M p w) (gateHistory T (bootGates X) p)))
variable (inj : Function.Injective (sourceState M p w).site.oldKey)
variable (I : CallFormat (printedParams (f:=f) (ell:=ell) s) c)
variable (W : Ingress I) (units : ℕ) {a cp wid edges : ℕ}
variable (raw : KeptLayoutWords a cp wid edges) (axisBits : List Bool)
variable (matching : ExistingRosterLabels (sourceState M p w) (gateHistory T (bootGates X) p)
  owners I W units raw.rawView axisBits)

include matching in
private theorem grouped_source_headers_count_same_live_owners :
    I.order.length=vertexCount c.host ∧ owners.raw.length=vertexCount c.host := by
  let H := groupHeadersFromOwnedRaw (sourceState M p w) (gateHistory T (bootGates X) p)
    owners I W units raw.rawView axisBits matching
  have actual := all_actual_grouped_headers_count_the_parent_vertices X p w (sourceState M p w) H.result
  have ih : H.result.raw.length=I.order.length := by
    rw [(same_raw_roster_and_actual_labels_supply_true_group_headers (sourceState M p w)
      (gateHistory T (bootGates X) p) owners I W units raw.rawView axisBits matching).2.1,List.length_map]
  exact ⟨ih.symm.trans actual,by rw [owners.exactRows,List.length_map,matching.order]; exact ih.symm.trans actual⟩

/-- Actual bytes from both true tapes are paid on the selected stop.
The roster and headers really count all vertices of this parent. -/
theorem actual_kept_owner_input_has_a_uniform_physical_coefficient {K : ℕ}
    (widths : LocalOwnerGeometry X p w (sourceState M p w) K) :
    (actualStoppedInputFromKeptTapes X M p w resident owners inj I W units raw axisBits matching).steps≤
      keptOwnerBudget K (vertexCount (ext).host+4*(C*s)) := by
  let Y := sourceState M p w
  let V₀ := vertexCount (ext).host+4*(C*s)
  let ownInstall := (installResidentBank Y).result
  have rows : resident.rows=ownInstall.rows := resident.exactRows.trans ownInstall.exactRows.symm
  have mounted : (mountResident Y resident).steps=(mountResident Y ownInstall).steps := by
    rw [mounted_resident_fee,mounted_resident_fee,rows]
  have mountCap := independently_priced_pre_layout_mount Y K widths.parentEdges widths.childEdges widths.port
    widths.owner widths.axis widths.keyWidth widths.precWidth widths.pageWidth widths.body
  have count := grouped_source_headers_count_same_live_owners X M p w owners I W units raw axisBits matching
  have vertices : vertexCount c.host≤V₀ := (actual_leaf_field_width_and_vertices (T:=T) p).2.2
  have rankCap : (axis T (p.ticket w)).val≤K :=
    (show (axis T (p.ticket w)).val<(dim (p.ticket w)) from (axis T (p.ticket w)).isLt).le.trans widths.axis
  have ow : Y.site.ownerWidth≤K := widths.owner
  have ownCap := Nat.mul_le_mul_left 3 ow
  have n := Nat.mul_le_mul (show 3*Y.site.ownerWidth+6≤3*K+6 by omega) (count.2.trans_le vertices)
  have g := Nat.mul_le_mul (count.1.trans_le vertices)
    (physical_group_header_unit_is_monotone ow rankCap)
  have h := (same_raw_roster_and_actual_labels_supply_true_group_headers Y (gateHistory T (bootGates X) p)
    owners I W units raw.rawView axisBits matching).2.2
  have charge := h.trans
    (Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add_left n 3) (Nat.add_le_add_left g 3)) 4)
  have m := mounted.trans_le mountCap
  change (mountResident Y resident).steps+
    (groupHeadersFromOwnedRaw Y (gateHistory T (bootGates X) p) owners I W units raw.rawView axisBits matching).steps+5≤_
  calc
    _ ≤ 256*(K+1)^3 + (3+(3*K+6)*V₀+(3+V₀*groupHeaderUnit K K)+4) + 5 :=
      Nat.add_le_add_right (Nat.add_le_add m charge) 5
    _ = keptOwnerBudget K V₀ := by unfold keptOwnerBudget; ring

open J6R10Reachable
variable [DecidableEq (Envelope (N sel) (Childs sel) (exteriorChild G ell X.centre X.sample X.group))]
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]

/-- The legacy path is priced only when its selected acquisition actually
calls the generated producer, comparing the entire metered reply. -/
theorem literal_R65_positive_uses_its_kept_tape_producer
    (basePos : 0<base)
    (ord : Fin (ext).edges≃(ext).host.Edge)
    (provide : OwnerInputProvider (T:=T) (pad:=pad) X)
    (initial : Bank) (stop : (ch).edges≤(printedParams (f:=f) (ell:=ell) s).cutoff)
    (positive : 0<(ch).edges)
    (invoked : let input := actualStoppedInputFromKeptTapes X M p w resident owners inj I W units raw axisBits matching
      provide p w (sourceState M p w) stop=⟨some input.result,input.steps⟩) :
    readLeaf (withPaidOwnerLeaves X M basePos ord provide) initial (.step p w) stop=
      readProvidedOnR65Bank X M p w
        (actualStoppedInputFromKeptTapes X M p w resident owners inj I W units raw axisBits matching) initial :=
  r65_positive_is_the_selected_actual_provider X M p w basePos ord provide initial
    (actualStoppedInputFromKeptTapes X M p w resident owners inj I W units raw axisBits matching) stop positive invoked

end ExactProducer
#print axioms physical_group_header_unit_is_monotone
#print axioms actual_kept_owner_input_has_a_uniform_physical_coefficient
#print axioms literal_R65_positive_uses_its_kept_tape_producer
end
end J6R94HeldOwnerProvider