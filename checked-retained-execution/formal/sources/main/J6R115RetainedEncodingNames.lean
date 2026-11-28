import J6R111KeptOwnerFlowRun

/-! The exact tagged key encoding length for the actually retained
successor, inherited from its real creation-directory name law. -/
namespace J6R115RetainedEncoding
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
open J6R58RequestSource J6R48DFS J6R16ModeCost J6R50Peak
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


section One
variable (Y : StoredSite T (p.ticket w) key prec tw bw (pageKeyWidth m+pad))
variable (u : (Plan sel).Slot (p.ticket w).child)
variable (K : LocalLoad Y u)

theorem actual_successor_owner_keys_add_one_tag_and_one_page_word
    (fit : NativeCreationOwnerContext Y K) :
    K.advance.next.site.ownerWidth=Y.site.ownerWidth+(pageKeyWidth m+pad+1) := by
  change namesAsRawContext (nameCurrentOwner Y)=namesAsRawContext K.advance.next.site.oldKey at fit
  have widths := congrArg (fun v : OwnerNames _=>v.1) fit
  change 1+(Y.site.ownerWidth+(pageKeyWidth m+pad))=K.advance.next.site.ownerWidth at widths
  omega
end One

variable (M : OnlineMachine T key prec tw bw (pageKeyWidth m+pad) rate)
variable {rank rootWidth : ℕ} (D : KeptDrivers X M rank)
variable (first : ∀ slot : (Plan sel).Slot (exteriorChild G ell X.centre X.sample X.group),
  (M.initial slot).result.site.ownerWidth≤rootWidth)

include D first in
theorem actual_retained_owner_names_follow_path_width :
    (sourceState M p w).site.ownerWidth≤rootWidth+moves p*(pageKeyWidth m+pad+1) := by
  induction p with
  | root => simpa only [moves,Nat.zero_mul,Nat.add_zero] using first w
  | @step q path slot ih =>
    let Y := sourceState M path slot
    let K := (M.demand Y w).result
    have h : (sourceState M (.step path slot) w).site.ownerWidth=
        Y.site.ownerWidth+(pageKeyWidth m+pad+1) :=
      actual_successor_owner_keys_add_one_tag_and_one_page_word X path slot Y w K (D.names path slot w)
    rw [h,moves,Nat.add_mul,Nat.one_mul]
    simpa only [Nat.add_assoc] using Nat.add_le_add_right (ih slot) (pageKeyWidth m+pad+1)

include D first in
theorem actual_captured_owner_name_width_from_first_width_and_source_depth (x : KeptInvocation X M) :
    x.site.site.ownerWidth≤rootWidth+pathLimit s C*(pageKeyWidth m+pad+1) := by
  have grow := actual_retained_owner_names_follow_path_width X x.path x.slot M D first
  have depth := actual_ancestry_moves_any_start cfg sel T.rootStable x.path
  rw [x.actualSite]
  exact grow.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ depth) _)

#print axioms actual_successor_owner_keys_add_one_tag_and_one_page_word
#print axioms actual_retained_owner_names_follow_path_width
#print axioms actual_captured_owner_name_width_from_first_width_and_source_depth
end
end J6R115RetainedEncoding
