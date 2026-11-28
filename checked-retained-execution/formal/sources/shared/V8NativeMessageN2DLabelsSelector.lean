import V8NativeMessageN2DLabelsTape

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6000000

/-! Connect the source's source_64 -> actual_labels_feed_packing
pipeline to Ready at a real call. A complete format family is still
an input; the labels and their balance bound are not. -/
namespace V8NativeMessage.N2DLabels
open scoped Classical Polynomial
open J6R9Recursive J6ActiveRun J6R10Repack J6R11Repack J6R11Blueprint J6R12Blueprint

variable {f : ℤ[X]} {ell Δ : ℕ} {S : Params (f:=f) (ell:=ell)}

abbrev CallFormat (S : Params (f:=f) (ell:=ell)) (c : Call (PhysicalHost f ell)) :=
  @Full64Input c.host.Edge c.host.Row c.host.Col c.host.finiteEdge c.host.network (S.levelBits c.depth)

abbrev CallObservation {c : Call (PhysicalHost f ell)} (I : CallFormat S c) (Δ : ℕ) :=
  @ObservedPacking c.host.Edge c.host.Row c.host.Col c.host.finiteEdge c.host.network
    (S.levelBits c.depth) c.host.finiteRow c.host.finiteCol I Δ

theorem ready_actual_full64 {c : Call (PhysicalHost f ell)} (d : Ready S Δ c)
    (I : CallFormat S c) : Nonempty (CallObservation I Δ) := by
  letI := c.host.finiteEdge
  letI := c.host.finiteRow
  letI := c.host.finiteCol
  have M : Nat.card c.host.Edge=c.edges := (host_card c.host).trans d.edgeCount
  exact actual_full64_packing I Δ d.degree.1 d.degree.2
    (M.symm ▸ d.collision) (M.symm ▸ d.paddedSlots)

abbrev Full64PlanInputs (S : Params (f:=f) (ell:=ell)) (Δ : ℕ) :=
  ∀ c : Call (PhysicalHost f ell), Ready S Δ c → CallFormat S c

noncomputable def observedAt (inputs : Full64PlanInputs S Δ) {c : Call (PhysicalHost f ell)}
    (d : Ready S Δ c) : CallObservation (inputs c d) Δ :=
  Classical.choice (ready_actual_full64 d (inputs c d))

noncomputable def full64Selector (inputs : Full64PlanInputs S Δ) : CertifiedSelector S Δ :=
  fun c d => by
    letI := c.host.finiteEdge
    letI := c.host.finiteRow
    letI := c.host.finiteCol
    exact (observedAt inputs d).pack

/-- Same packing as used by the literal packet factory after projection.
In particular its ordered row and column words are the output of
this very source labeler, not those of an independent witness. -/
theorem full64_selected_receipt (inputs : Full64PlanInputs S Δ) {c : Call (PhysicalHost f ell)}
    (d : Ready S Δ c) :
    letI := c.host.finiteEdge
    letI := c.host.finiteRow
    letI := c.host.finiteCol
    let I := inputs c d
    let P := packing (forget (full64Selector inputs)) d
    CollisionCertified Δ P ∧ RoundsExactly P ∧
      I.run.result.2=I.order.map (fun v=>I.format.label (wordsOf P v)) ∧
      I.run.result.1=I.format.graph (fun v=>some (wordsOf P v)) ∧
      I.run.steps≤I.fee := by
  letI := c.host.finiteEdge
  letI := c.host.finiteRow
  letI := c.host.finiteCol
  let O := observedAt inputs d
  exact ⟨O.pack.property,O.rounded,O.labelFile,O.incidenceFile,O.cost⟩

/-- A separately certified tied root can stay fixed without pretending
that it is a descendant's greedy label tape. -/
theorem full64_else_fixed_root
    (inputs : Full64PlanInputs S Δ) (root : Call (PhysicalHost f ell))
    (P : CertifiedPacking root.host.network (S.levelBits root.depth) Δ) (d : Ready S Δ root) :
    packing (forget (pinCertified (full64Selector inputs) root P)) d=P.val :=
  pin_certified_root (full64Selector inputs) root P d

#print axioms ready_actual_full64
#print axioms full64_selected_receipt
#print axioms full64_else_fixed_root
end V8NativeMessage.N2DLabels
