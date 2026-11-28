import J6R48DFSPayload

/-! Sum the explicit live frame encodings over the genuine occurrence
path, rather than multiplying the largest frame by the depth. The
caller still has to account for actual running temporaries in its
chosen machine representation. -/
namespace J6R49LiveBits
open scoped Polynomial
open J1PPrinted J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R16ModeCost J6R24MeteredRecursion J6R30ProducedGateRegistry J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R48DFS

set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)}

noncomputable def frameLengths
    (encode : {x : Call (PhysicalHost f ell)} → Path sel r x → List Bool) :
    {x : Call (PhysicalHost f ell)} → Path sel r x → List ℕ
  | _, .root => [(encode .root).length]
  | _, .step p w => frameLengths encode p ++ [(encode (.step p w)).length]

theorem affine_frame_bits
    (encode : {x : Call (PhysicalHost f ell)} → Path sel r x → List Bool)
    (base slope : ℕ)
    (fits : ∀ {x} (p : Path sel r x), (encode p).length ≤ base + x.edges * slope)
    (p : Path sel r c) :
    (frameLengths encode p).sum ≤ (edgeStack p).length * base + (edgeStack p).sum * slope := by
  induction p with
  | root =>
    simpa only [frameLengths, edgeStack, List.sum_cons, List.sum_nil, Nat.add_zero,
      List.length_cons, List.length_nil, Nat.zero_add, Nat.one_mul] using fits (.root : Path sel r r)
  | @step par p w ih =>
    simp only [frameLengths, edgeStack, List.sum_append, List.sum_cons, List.sum_nil,
      List.length_append, List.length_cons, List.length_nil, Nat.zero_add, Nat.add_zero, Nat.add_mul]
    exact (Nat.add_le_add ih (fits (.step p w))).trans_eq (by ac_rfl)

theorem affine_frames_at_printed_root (cfg : RootBounds s C f) (hr : Stable s C r)
    (hzero : r.depth = 0)
    (encode : {x : Call (PhysicalHost f ell)} → Path sel r x → List Bool)
    (base slope : ℕ)
    (fits : ∀ {x} (p : Path sel r x), (encode p).length ≤ base + x.edges * slope)
    (p : Path sel r c) :
    (frameLengths encode p).sum ≤ (pathLimit s C + 1) * base + (32*r.edges/29) * slope := by
  have hs : (edgeStack p).sum ≤ 32*r.edges/29 := by
    have h := edgeStack_geometric p
    omega
  exact (affine_frame_bits encode base slope fits p).trans
    (Nat.add_le_add (Nat.mul_le_mul_right _ (printed_stack_level_bound cfg hr hzero p))
      (Nat.mul_le_mul_right _ hs))

variable {cfg : RootBounds s C f} {hf : f.Monic} {T : Prepared cfg sel r hf}

theorem explicit_pages_and_frames_at_printed_root
    (born : Births T key prec tw bw page) (initial : PageBank f ell key prec tw bw page)
    (U base slope : ℕ)
    (hRows : AllExactPages born)
    (pageFit : ∀ {x : Call (PhysicalHost f ell)} (p : Path sel r x) (w : (Plan sel).Slot x),
      let e := (born p w).job.immutable.payload.payload
      ∀ y ∈ e.pages, (originPayload y.payload).length ≤ U)
    (hzero : r.depth = 0)
    (encode : {x : Call (PhysicalHost f ell)} → Path sel r x → List Bool)
    (frameFit : ∀ {x} (p : Path sel r x), (encode p).length ≤ base + x.edges * slope)
    (p : Path sel r c) :
    residentAtlasBits (stackBank born initial p) + (frameLengths encode p).sum ≤
      residentAtlasBits initial + (96*r.edges/29) * (page+U) +
        ((pathLimit s C + 1) * base + (32*r.edges/29) * slope) :=
  Nat.add_le_add (scoped_generated_literal_page_bits born initial U hRows pageFit p)
    (affine_frames_at_printed_root cfg T.rootStable hzero encode base slope frameFit p)

#print axioms affine_frame_bits
#print axioms affine_frames_at_printed_root
#print axioms explicit_pages_and_frames_at_printed_root
end J6R49LiveBits



