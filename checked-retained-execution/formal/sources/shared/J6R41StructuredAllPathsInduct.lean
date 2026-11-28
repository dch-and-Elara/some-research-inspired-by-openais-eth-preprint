import J6R41StructuredAllPathsStep

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 17000000
set_option maxRecDepth 3200

/-! Actual occurrence induction. The written child payload itself,
not a test-provided trace body, is the conclusion. An aligned path
remembers the same native creator, physical page, and creation word
until that vertex is dropped. -/
namespace J6R41StructuredAllPaths
open scoped Polynomial Classical
open Polynomial J6R21Ancestor J6R20Ancestor J6R34ChildPath J6R26DescriptorTree J6R15ModeCost
open J6R36ChildFramedRoute J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted
open J6ActiveRun J6R24MeteredRecursion J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R25PreparedSupply J6R30ProducedGateRegistry

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
variable {born : Births T key prec tw bw page}
variable {keys : PageKeys born} {rootTags : r.host.Row⊕r.host.Col→Origin key prec page}
variable (files : SiteFiles born keys rootTags) (rootPorts : Port r.host.Edge→Payload key prec page)

def BodyFollows {c : Call (PhysicalHost f ell)} (p : Path sel r c) (u : c.host.Row⊕c.host.Col)
    (src : Point f ell) (seed : PortAt src→List Bool) (tag : Origin key prec page)
    (tr : Trace src (point c.host u)) : Prop :=
  expectedOrigin born keys rootTags p u=tag ∧
    ∀ x : PortAt (point c.host u),publishedPayload files rootPorts p x.val=(tag,tr.literal seed x)

def RootContinues {c : Call (PhysicalHost f ell)} (p : Path sel r c)
    (u : c.host.Row⊕c.host.Col) : Prop :=
  ∃ a : r.host.Row⊕r.host.Col, ∃ tr : Trace (point r.host a) (point c.host u),
    BodyFollows files rootPorts p u (point r.host a)
      (fun x=>(rootPorts x.val).2) (rootTags a) tr

def NativeContinues {c : Call (PhysicalHost f ell)} (p : Path sel r c)
    (u : c.host.Row⊕c.host.Col) : Prop :=
  ∃ (ca : Call (PhysicalHost f ell)) (anc : Path sel r ca) (w : (Plan sel).Slot ca)
    (k : PageAt T (anc.ticket w)), OnPath born (born anc w).job p ∧
    ∃ tr : Trace (bornPoint T (anc.ticket w) k) (point c.host u),
      BodyFollows files rootPorts p u (bornPoint T (anc.ticket w) k)
        (originSeed (layout T (anc.ticket w)) (axis T (anc.ticket w)) (anc.ticket w).groupAt k)
        (nativeOrigin (files anc w) k) tr

theorem linked_paths_use_original_payload
    (L : Linked files rootPorts)
    (boot : ∀ (u : r.host.Row⊕r.host.Col) (h : PortAt (point r.host u)),(rootPorts h.val).1=rootTags u)
    {c : Call (PhysicalHost f ell)} (p : Path sel r c) :
    ∀ u : c.host.Row⊕c.host.Col,RootContinues files rootPorts p u ∨ NativeContinues files rootPorts p u := by
  induction p with
  | root =>
    intro u
    exact Or.inl ⟨u,Trace.start,rfl,fun h=>Prod.ext (boot u h) rfl⟩
  | @step c p w ih =>
    intro u
    let v := p.ticket w
    cases h : childVertices T v u with
    | inl old =>
      rcases ih old.val with root|inner
      · obtain ⟨initial,tr,tag,bodies⟩ := root
        let E := selected_retained_chart T v u old h
        let made := carried_retention_publishes_correct_body L p w u old h
          (fun x=>(rootPorts x.val).2) tr (rootTags initial) tag bodies
        exact Or.inl ⟨initial,E.symm ▸ tr.keep (retainedMove T v old),made⟩
      · obtain ⟨ca,anc,kSlot,k,on,tr,tag,bodies⟩ := inner
        let E := selected_retained_chart T v u old h
        let seed := originSeed (layout T (anc.ticket kSlot)) (axis T (anc.ticket kSlot)) (anc.ticket kSlot).groupAt k
        let made := carried_retention_publishes_correct_body L p w u old h
          seed tr (nativeOrigin (files anc kSlot) k) tag bodies
        exact Or.inr ⟨ca,anc,kSlot,k,.inherited p w on,E.symm ▸ tr.keep (retainedMove T v old),made⟩
    | inr k =>
      let E := selected_packet_chart T v u k h
      exact Or.inr ⟨c,p,w,k,.youngest p w rfl,E.symm ▸ Trace.start,
        actual_new_page_publishes_correct_body L p w u k h⟩

#print axioms linked_paths_use_original_payload
end J6R41StructuredAllPaths