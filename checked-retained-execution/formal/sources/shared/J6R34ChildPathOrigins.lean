import J6R34ChildPathChart
import J6R33StatefulArithmeticPagePath

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 2700
set_option maxHeartbeats 17500000

/-! Every vertex of a real invocation obtains its origin by following
the *same occurrence path*. Each old endpoint follows the explicit
typed retained move; a right endpoint belongs to exactly the page
created at that particular preceding slot. -/
namespace J6R34ChildPath
open scoped Polynomial Classical
open Polynomial
open J6ActiveRun J6R10Reachable J6R10Repack J6R11Blueprint J6R12Blueprint
open J1PPrinted J6R16ModeCost J6R26DescriptorTree J6R24MeteredRecursion
open J6R21Ancestor J6R32StatefulArithmetic J6R33StatefulArithmeticPage

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
variable (born : J6R33StatefulArithmeticPage.Births T key prec tw bw page)

/-- A proposition about the live tree already used by the interpreter.
The left case is one actual original root vertex; the right case
keeps the precise prior invocation and physical page. -/
def sourceOriginAt {c : Call (PhysicalHost f ell)} (p : Path sel r c) (cur : Point f ell) : Prop :=
  (∃ u : r.host.Row⊕r.host.Col, Nonempty (Trace (point r.host u) cur)) ∨
  (∃ (start : Call (PhysicalHost f ell)) (older : Path sel r start)
      (w : (Plan sel).Slot start) (k : PageAt T (older.ticket w)),
    OnPath born (born older w).job p ∧
      Nonempty (Trace (bornPoint T (older.ticket w) k) cur))

theorem actual_path_has_typed_origin {c : Call (PhysicalHost f ell)} (p : Path sel r c)
    (u : c.host.Row⊕c.host.Col) : sourceOriginAt born p (point c.host u) := by
  induction p with
  | root =>
    exact Or.inl ⟨u,⟨Trace.start⟩⟩
  | @step c p w ih =>
    let s := p.ticket w
    have H := actual_child_vertex_chart T s u
    cases h : childVertices T s u with
    | inl old =>
      have E : point s.child.host u=(retainedMove T s old).next := by
        rw [h] at H
        exact H.trans (actual_retained_point T s old).symm
      cases ih old.val with
      | inl initiation =>
        obtain ⟨o,⟨tr⟩⟩ := initiation
        exact Or.inl ⟨o,⟨E.symm ▸ Trace.keep tr (retainedMove T s old)⟩⟩
      | inr retained =>
        obtain ⟨olderCall,older,w0,k,hPath,⟨tr⟩⟩ := retained
        exact Or.inr ⟨olderCall,older,w0,k,.inherited p w hPath,
          ⟨E.symm ▸ Trace.keep tr (retainedMove T s old)⟩⟩
    | inr k =>
      have E : point s.child.host u=bornPoint T s k := by rw [h] at H; exact H
      exact Or.inr ⟨c,p,w,k,.youngest p w rfl,⟨E.symm ▸ Trace.start⟩⟩

theorem actual_path_live_origin {c : Call (PhysicalHost f ell)} (p : Path sel r c)
    (u : c.host.Row⊕c.host.Col) (rootLive : PageBank f ell key prec tw bw page→Prop)
    (B : PageBank f ell key prec tw bw page) (isNow : opened born rootLive p B) :
    (∃ orig : r.host.Row⊕r.host.Col, Nonempty (Trace (point r.host orig) (point c.host u))) ∨
    (∃ (start : Call (PhysicalHost f ell)) (older : Path sel r start)
      (w : (Plan sel).Slot start) (k : PageAt T (older.ticket w)),
      IsLive (born older w).job B ∧
        Nonempty (Trace (bornPoint T (older.ticket w) k) (point c.host u))) := by
  rcases actual_path_has_typed_origin born p u with h|h
  · exact Or.inl h
  · obtain ⟨start,older,w,k,there,tr⟩ := h
    exact Or.inr ⟨start,older,w,k,ancestor_paged_live born _ p there B isNow,tr⟩

#print axioms actual_path_has_typed_origin
#print axioms actual_path_live_origin
end J6R34ChildPath
