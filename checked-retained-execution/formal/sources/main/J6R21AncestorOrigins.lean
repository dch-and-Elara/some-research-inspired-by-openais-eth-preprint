import J6R21AncestorHistory
import J6R16ModeCostBranchFold

/-! Every tensor on the actual printed recursion has an origin:
an original input or a real generated packet vertex. Retention extends
the same trace; it does not create another numeric recipe. This is the
logical provenance invariant, not a compiler for the whole directory. -/
namespace J6R21Ancestor
open scoped Polynomial Classical
open J1PPrinted J6ActiveRun J6ActiveSchedule J6R10Reachable J6R12Blueprint
open J6R11Blueprint J6R10Repack J6R16ModeCost P11FullPacking J6R9Recursive

variable {f : ℤ[X]} {ell : ℕ} {S : Params (f:=f) (ell:=ell)} {Δ : ℕ}
variable (sel : Selector S Δ) {c : Call (PhysicalHost f ell)}

abbrev sitePage (d : Ready S Δ c) := Page (S.levelBits c.depth) (packing sel d).copies (Fin 64)

noncomputable def packetPoint (d : Ready S Δ c) (t : Center S c) (z : Probe S c)
    (β : SiteMode sel d t→₀ℕ) (g : Fin 64) (k : sitePage sel d) : Point f ell :=
  ⟨packetOfSite sel d t z β g,.inr k⟩

noncomputable def actualMove (d : Ready S Δ c) (t : Center S c) (z : Probe S c)
    (β : SiteMode sel d t→₀ℕ) (g : Fin 64)
    (v : c.host.Row⊕c.host.Col) (keep : atGroup (packing sel d) (centerIndex d t) v=g) :
    Move (⟨c.host,v⟩ : Point f ell) := by
  letI := c.host.finiteEdge
  let P := packing sel d
  let i := centerIndex d t
  let p := registerPrecision S c t
  let F := actualPacket P i (centerNonzero t) rfl p (J6R10Integral.box_two_nil p f ell)
    (sampleNode S f ell c d.fit t z) β g
  exact {
    Group := Fin 64
    Packet := sitePage sel d
    decGroup := inferInstance
    finitePacket := inferInstance
    group := atGroup P i
    packet := atPacket P
    selected := g
    keeps := keep
    p := p
    siblings := compiledPacket P i g p F }

set_option maxHeartbeats 5000000 in
theorem actual_move_next (d : Ready S Δ c) (t : Center S c) (z : Probe S c)
    (β : SiteMode sel d t→₀ℕ) (g : Fin 64)
    (v : c.host.Row⊕c.host.Col) (keep : atGroup (packing sel d) (centerIndex d t) v=g) :
    (actualMove sel d t z β g v keep).next=
      (⟨packetOfSite sel d t z β g,.inl ⟨v,keep⟩⟩ : Point f ell) := rfl

variable {s C : ℕ} (cfg : RootBounds s C f)
variable (native : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s))

def genuineOrigin (r : Call (PhysicalHost f ell)) (p : Point f ell) : Prop :=
  (∃ v : r.host.Row⊕r.host.Col,Nonempty (Trace ⟨r.host,v⟩ p)) ∨
  (∃ (c : Call (PhysicalHost f ell)) (_walk : NativeReach (Plan native) r c)
      (d : Ready (printedParams s) (sourceDelta s) c) (t : Center (printedParams s) c)
      (z : Probe (printedParams s) c) (β : SiteMode native d t→₀ℕ)
      (g : Fin 64) (k : sitePage native d),
      Nonempty (Trace (packetPoint native d t z β g k) p))

set_option maxHeartbeats 2200000 in
include cfg in
theorem every_reachable_vertex_has_origin {r c : Call (PhysicalHost f ell)}
    (walk : NativeReach (Plan native) r c) (hr : Stable s C r) (v : c.host.Row⊕c.host.Col) :
    genuineOrigin native r ⟨c.host,v⟩ := by
  let inv (x : Call (PhysicalHost f ell)) := Stable s C x ∧ NativeReach (Plan native) r x ∧
    ∀ p : x.host.Row⊕x.host.Col,genuineOrigin native r ⟨x.host,p⟩
  have step (x : Call (PhysicalHost f ell)) (hx : inv x) (w : (Plan native).Slot x) :
      inv ((Plan native).child x w) := by
    refine ⟨stable_step cfg native hx.1 w,reach_snoc (Plan native) hx.2.1 w,?_⟩
    let d := getReady cfg hx.1 w.property
    let t := w.val.1
    let z := w.val.2.1
    let b := siteTuple native d w.val
    let g := w.val.2.2.2
    let child := packetOfSite native d t z b g
    have hchild : (Plan native).child x w=⟨child,x.depth+1,child.edgeCount,registerPrecision _ x t⟩ :=
      child_exact native d w.val
    rw [hchild]
    intro p
    change genuineOrigin native r (⟨child,p⟩ : Point f ell)
    change _ ⊕ _ at p
    cases p with
    | inr k =>
      exact Or.inr ⟨x,hx.2.1,d,t,z,b,g,k,⟨Trace.start⟩⟩
    | inl old =>
      let mv := actualMove native d t z b g old.val old.property
      have eqPt : mv.next=(⟨child,.inl old⟩ : Point f ell) := actual_move_next native d t z b g old.val old.property
      rw [←eqPt]
      rcases hx.2.2 old.val with ⟨r0,⟨trace⟩⟩|⟨z0,h0,d0,t0,x0,b0,g0,k0,⟨trace⟩⟩
      · exact Or.inl ⟨r0,⟨trace.keep mv⟩⟩
      · exact Or.inr ⟨z0,h0,d0,t0,x0,b0,g0,k0,⟨trace.keep mv⟩⟩
  have rInv : inv r := ⟨hr,.reflexive _,fun y=>Or.inl ⟨y,⟨Trace.start⟩⟩⟩
  exact (nativeReach_run_invariant (Plan native) inv step walk rInv).2.2 v

#print axioms actual_move_next
#print axioms every_reachable_vertex_has_origin
end J6R21Ancestor



