import J6R49SourceLayoutInstall
import J6R49SourceLayoutPageKeys

/-! Online construction on the actual dependent source path. The
output family is built by replaying the requested path from its root;
no precomputed Births, SiteFiles or Linked witness is an input. A
request still needs a real local producer for its registered words. -/
namespace J6R50SourceProducer
open scoped Classical Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor
open J6R25PreparedSupply J6R26DescriptorTree J6R34ChildPath J6R41StructuredAllPaths
open J6R33StatefulArithmeticPage J6R36ChildFramedRoute J6R27OriginalGate
open J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R24MeteredRecursion
open J6ActiveRun P11FullPacking J6R9PacketScopes J6R11Repack
open J6R32ChildResidentTransfer J6R48RawRoute J6R33GeneratedChildSite J6R49SourceLayout
open J6R34RootAtlas J6R32StatefulArithmetic
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 3200
set_option maxHeartbeats 11800000
set_option maxSynthPendingDepth 12
set_option linter.unusedSectionVars false
set_option Elab.async false
noncomputable section

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable (T : Prepared cfg sel r hf)

structure StoredSite (T : Prepared cfg sel r hf) (v : Ticket sel r) (key prec tw bw page : ℕ) where
  input : OccurrenceInput T v key prec tw bw page
  origins : v.parent.host.Row⊕v.parent.host.Col→Origin key prec page
  site : SiteInputs (compileOccurrence input) origins
  canonical : site.pageKey=occurrencePageWord input

variable {T} {v : Ticket sel r}

def StoredSite.birth (X : StoredSite T v key prec tw bw page) : Birth T v key prec tw bw page :=
  compileOccurrence X.input

def StoredSite.childOrigins (X : StoredSite T v key prec tw bw page)
    (u : v.child.host.Row⊕v.child.host.Col) : Origin key prec page :=
  match childVertices T v u with
  | .inl old => X.origins old.val
  | .inr pageId => ⟨X.birth.job.immutable.payload.stamp,some (occurrencePageWord X.input pageId)⟩

structure Advance (X : StoredSite T v key prec tw bw page) (u : (Plan sel).Slot v.child) where
  next : StoredSite T (successorTicket v u) key prec tw bw page
  liveOrigins : next.origins=X.childOrigins
  exactBody : ∀ h,(next.birth.native.physical.record h).body=
    (X.site.issuedLane (childHalves T v (edge h)) (side h)).body

structure LiveProducer (T : Prepared cfg sel r hf)
    (rootTags : r.host.Row⊕r.host.Col→Origin key prec page)
    (rootPorts : Port r.host.Edge→Payload key prec page) where
  start : (u : (Plan sel).Slot r) →
    StoredSite T ((Path.root : Path sel r r).ticket u) key prec tw bw page
  startOrigins : ∀ u,(start u).origins=rootTags
  startBody : ∀ u h,((start u).birth.native.physical.record h).body=(rootPorts h).2
  advance : ∀ {v : Ticket sel r} (X : StoredSite T v key prec tw bw page)
    (u : (Plan sel).Slot v.child),Advance X u

variable {rootTags : r.host.Row⊕r.host.Col→Origin key prec page}
variable {rootPorts : Port r.host.Edge→Payload key prec page}
variable (P : LiveProducer T (tw:=tw) (bw:=bw) rootTags rootPorts)

def buildAlong :
    {c : Call (PhysicalHost f ell)} → (p : Path sel r c) → (w : (Plan sel).Slot c) →
      StoredSite T (p.ticket w) key prec tw bw page
  | _,.root,w => P.start w
  | _,.step p x,w => (P.advance (buildAlong p x) w).next

def births : Births T key prec tw bw page :=
  fun p w=>(buildAlong P p w).birth

def pageKeys : PageKeys (births P) :=
  fun p w=>occurrencePageWord (buildAlong P p w).input

theorem built_origin_table_is_the_actual_path :
    ∀ {c : Call (PhysicalHost f ell)} (p : Path sel r c) (u : (Plan sel).Slot c),
      (buildAlong P p u).origins=expectedOrigin (births P) (pageKeys P) rootTags p := by
  intro c p
  induction p with
  | root =>
    intro w
    exact P.startOrigins w
  | step p z ih =>
    intro w
    let prior := buildAlong P p z
    refine (P.advance prior w).liveOrigins.trans ?_
    funext vtx
    unfold StoredSite.childOrigins
    rw [expectedOrigin]
    cases ea : childVertices T (p.ticket z) vtx with
    | inl old =>
      exact congrFun (ih z) old.val
    | inr fresh => rfl

def files : SiteFiles (births P) (pageKeys P) rootTags :=
  fun p w=>built_origin_table_is_the_actual_path P p w ▸ (buildAlong P p w).site

private theorem transport_site_key {Q : Birth T v key prec tw bw page}
    {a b : v.parent.host.Row⊕v.parent.host.Col→Origin key prec page}
    (same : a=b) (S : SiteInputs Q a) :
    (same ▸ S : SiteInputs Q b).pageKey=S.pageKey := by
  cases same
  rfl

private theorem transport_site_lane {Q : Birth T v key prec tw bw page}
    {a b : v.parent.host.Row⊕v.parent.host.Col→Origin key prec page}
    (same : a=b) (S : SiteInputs Q a) (x : HalfAt T v) (s : Bool) :
    (same ▸ S : SiteInputs Q b).issuedLane x s=S.issuedLane x s := by
  cases same
  rfl

theorem online_paths_have_no_supplied_link_table :
    Linked (files P) rootPorts := by
  constructor
  · intro c p w
    unfold files
    rw [transport_site_key]
    exact (buildAlong P p w).canonical
  · intro c p w h
    cases p with
    | root => exact P.startBody w h
    | step p j =>
      let X := buildAlong P p j
      have A := (P.advance X w).exactBody h
      change ((P.advance X w).next.birth.native.physical.record h).body=
        (lanePayload ((files P p j).issuedLane (childHalves T (p.ticket j) (edge h)) (side h))).2
      unfold files
      rw [transport_site_lane]
      exact A

/-- No cost of a second construction is hidden in the step.
This is a local R49 adapter; the recursive prefix interpreter does not
require an outgoing receipt table indexed by the entire source tree. -/
def fromR49 {q : ℕ} (X : StoredSite T v key prec tw bw page) (u : (Plan sel).Slot v.child)
    {out : Meter (Option (PreparedSeats ((printedParams (f:=f) (ell:=ell) s).levelBits v.child.depth) q))}
    (G : GeneratedChild (q:=q) X.site (ticketReady T (successorTicket v u))
      (successorTicket v u).centerAt out)
    (choose : G.chart=packing sel (ticketReady T (successorTicket v u)))
    (W : PreparedOccurrenceWords (q:=q) (u:=u) G choose)
    (nextSite : SiteInputs
      (compileOccurrence ((bindPreparedWords (q:=q) (u:=u) W).bind
        (adjacentOfGenerated (q:=q) (u:=u) G choose).generated)) X.childOrigins)
    (nextKey : nextSite.pageKey=occurrencePageWord
      ((bindPreparedWords (q:=q) (u:=u) W).bind (adjacentOfGenerated (q:=q) (u:=u) G choose).generated)) :
    Advance X u :=
  ⟨⟨_,X.childOrigins,nextSite,nextKey⟩,rfl,
    fun h=>(actual_successor_from_generated_resident_and_ports (q:=q) (u:=u) G choose W h).2.2.1⟩

#print axioms built_origin_table_is_the_actual_path
#print axioms online_paths_have_no_supplied_link_table
#print axioms fromR49
end
end J6R50SourceProducer