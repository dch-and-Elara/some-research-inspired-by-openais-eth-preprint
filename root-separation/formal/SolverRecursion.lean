import SolverChildren
import SolverCoordinates
import RootExecutionDriver

noncomputable section
namespace RootSeparation.Solver
open S11 RootSeparation.Execution Polynomial
open Classical

/-- A recursive call contracts the immutable integer coordinates of the
entries. A packet table is lifted once, at construction of its network. -/
structure Call (f : ℤ[X]) where
  depth : ℕ
  precision : ℕ
  precision_pos : 0 < precision
  network : Network (IntegerRing f)

def Call.edges {f : ℤ[X]} (c : Call f) : ℕ := Fintype.card c.network.Wire

def leafValue {f : ℤ[X]} (c : Call f) : WordRing f c.precision :=
  (c.network.map (fromInteger f c.precision)).contract

theorem leafValue_contract {f : ℤ[X]} (c : Call f) :
    leafValue c = fromInteger f c.precision c.network.contract :=
  Network.map_contract _ _

abbrev callA (s : ℕ) {f : ℤ[X]} (c : Call f) := labelLength s c.depth
abbrev callL (s : ℕ) {f : ℤ[X]} (c : Call f) := packetLength s c.depth
abbrev callU (s : ℕ) {f : ℤ[X]} (c : Call f) := retained s c.depth
abbrev callCenters (s : ℕ) {f : ℤ[X]} (c : Call f) := centers (callU s c) (callL s c)
abbrev callProbes (s : ℕ) {f : ℤ[X]} (c : Call f) := Fin (probeCount c.edges (callL s c))
abbrev callPrecision (s : ℕ) {f : ℤ[X]} (c : Call f) (t : ℤ) :=
  precision c.precision c.edges (callA s c) (callU s c) (callL s c) t

theorem callPrecision_pos (s : ℕ) {f : ℤ[X]} (c : Call f) (t : ℤ) :
    0 < callPrecision s c t := by
  have hp := c.precision_pos
  unfold callPrecision precision
  omega

/-- Layout certificate is for the physical wire type of this call.
    The labels are on vertices and determine the labels of retained ports. -/
structure CallLayout {f : ℤ[X]} (s : ℕ) (c : Call f) where
  Packet : Type
  finite : Fintype Packet
  left : c.network.Row → Fin (callA s c) → Fin 64
  right : c.network.Col → Fin (callA s c) → Fin 64
  packing : @Packing c.network.Wire Packet finite (callA s c) (callL s c)
  cells : packing.cell = S8.DChild.rootCell c.network.row c.network.col left right
  legal : SourceDensity.CollisionCertificate packing.cell (degreeEnvelope s : ℚ)
  positive : leafThreshold s < c.edges
  u_le_a : callU s c ≤ callA s c

attribute [instance] CallLayout.finite

variable {f : ℤ[X]} {s e : ℕ} {c : Call f}

def CallLayout.coord (layout : CallLayout s c) (t : callCenters s c) : Fin (callA s c) :=
  ⟨level t.val, ((Finset.mem_filter.1 t.property).2.2).trans_le layout.u_le_a⟩

def CallLayout.weights (layout : CallLayout s c) (t : ℤ) : List ℕ :=
  modeWeights (layout.packing.mixedAt t) (level t) (callPrecision s c t)

/-- The sole coefficient computation supplied by a packet constructor.
    Its input is one assignment to the actual ports, at the child's
    printed creation precision. -/
abbrev PacketTables (layout : CallLayout s c) :=
  (t : callCenters s c) → callProbes s c → List ℕ → (g : Fin 64) →
    (k : layout.Packet) →
      ({w // packetEndpoint c.network layout.left layout.right (layout.coord t) g
        layout.packing.position w = k} → Bool) → WordRing f (callPrecision s c t.val)

def childCall (hf : f.Monic) (he : f.natDegree = e) (layout : CallLayout s c)
    (tables : PacketTables layout)
    (t : callCenters s c) (j : callProbes s c) (β : List ℕ) (g : Fin 64) : Call f where
  depth := c.depth + 1
  precision := callPrecision s c t.val
  precision_pos := callPrecision_pos s c t.val
  network := childNetwork c.network layout.left layout.right (layout.coord t) g
    (RingHom.id _) layout.packing.position (fun k bits =>
      liftCanonical hf he (callPrecision_pos s c t.val) (tables t j β g k bits))

theorem childCall_packet_at_creation (hf : f.Monic) (he : f.natDegree = e)
    (layout : CallLayout s c) (tables : PacketTables layout)
    (t : callCenters s c) (j : callProbes s c) (β : List ℕ) (g : Fin 64)
    (k : layout.Packet)
    (bits : {w // packetEndpoint c.network layout.left layout.right (layout.coord t) g
        layout.packing.position w = k} → Bool) :
    fromInteger f (callPrecision s c t.val)
      ((childCall hf he layout tables t j β g).network.colEntry k bits) = tables t j β g k bits :=
  liftCanonical_section hf he (callPrecision_pos s c t.val) _

theorem childCall_shrink (hf : f.Monic) (he : f.natDegree = e) (layout : CallLayout s c)
    (tables : PacketTables layout)
    (t : callCenters s c) (j : callProbes s c) (β : List ℕ) (g : Fin 64) :
    (childCall hf he layout tables t j β g).edges < c.edges := by
  have h := childNetwork_shrink c.network layout.left layout.right (layout.coord t) g
    (RingHom.id _) layout.packing layout.cells (degreeEnvelope s : ℚ) layout.legal
    (fun k bits => liftCanonical hf he (callPrecision_pos s c t.val) (tables t j β g k bits))
  change 8 * (childCall hf he layout tables t j β g).edges ≤ c.edges at h
  have hpos := layout.positive
  omega

abbrev ProbeStates (e s : ℕ) {f : ℤ[X]} (c : Call f) :=
  (t : callCenters s c) → callProbes s c → BatchState (Fin e) (callPrecision s c t.val)

/-- Configuration for this recursion engine. The packet formula and the
    reduction after Hermite readout are the two operators to be linked
    by the correctness proof. Both receive input data, never a child
    return with a proof of correctness. -/
structure RecursionOps (f : ℤ[X]) (e s cutoff : ℕ) where
  monic : f.Monic
  degree : f.natDegree = e
  track : Fin e
  admissible : Call f → Prop
  prepare : (c : Call f) → admissible c → cutoff < s → leafThreshold s < c.edges →
    (layout : CallLayout s c) × (tables : PacketTables layout) ×'
      (∀ t j β g, admissible (childCall monic degree layout tables t j β g))
  readout : (c : Call f) →
    ((t : callCenters s c) → callProbes s c → WordRing f (callPrecision s c t.val)) →
    WordRing f c.precision

structure CallResult (f : ℤ[X]) (p : ℕ) where
  value : WordRing f p
  localTrace : List Step

set_option maxHeartbeats 1600000 in
/-- Well-founded semantics with the frozen leaf cutoff and the actual
    Wegener accumulator at each probe. Only the current call's trace
    is retained. Its operands come from recursive calls with smaller
    physical wire sets. -/
def runCall {cutoff : ℕ} (ops : RecursionOps f e s cutoff) (c : Call f) (hc : ops.admissible c) :
    CallResult f c.precision :=
  if hs : cutoff < s then
    if hm : leafThreshold s < c.edges then
      let data := ops.prepare c hc hs hm
      let sample : ProbeStates e s c := fun t j =>
        let p := callPrecision s c t.val
        let codec := wordCoords ops.monic ops.degree p (callPrecision_pos s c t.val)
        executeBatch p codec ops.track (fun slot g =>
          (runCall ops (childCall ops.monic ops.degree data.1 data.2.1 t j slot.exponents g)
            (data.2.2 t j slot.exponents g)).value)
          (data.1.weights t.val) t.val j.val
      let decode (t : callCenters s c) (j : callProbes s c) : WordRing f (callPrecision s c t.val) :=
        let codec := wordCoords ops.monic ops.degree (callPrecision s c t.val) (callPrecision_pos s c t.val)
        codec.symm (sample t j).accumulator
      let trace := (callCenters s c).attach.toList.flatMap fun t =>
        (List.finRange (probeCount c.edges (callL s c))).flatMap fun j => (sample t j).trace
      ⟨ops.readout c decode,trace⟩
    else ⟨leafValue c,[]⟩
  else ⟨leafValue c,[]⟩
termination_by c.edges
decreasing_by apply childCall_shrink

theorem runCall_leaf {cutoff : ℕ} (ops : RecursionOps f e s cutoff) (c : Call f)
    (hc : ops.admissible c) (h : c.edges ≤ leafThreshold s) :
    (runCall ops c hc).value = fromInteger f c.precision c.network.contract := by
  rw [runCall]
  split
  · rw [dif_neg (not_lt_of_ge h)]
    exact leafValue_contract c
  · exact leafValue_contract c

theorem runCall_finite_exception {cutoff : ℕ} (ops : RecursionOps f e s cutoff) (c : Call f)
    (hc : ops.admissible c) (h : s ≤ cutoff) :
    (runCall ops c hc).value = fromInteger f c.precision c.network.contract := by
  rw [runCall, dif_neg (not_lt_of_ge h)]
  exact leafValue_contract c

#print axioms leafValue_contract
#print axioms childCall_packet_at_creation
#print axioms childCall_shrink
#print axioms runCall
#print axioms runCall_leaf
#print axioms runCall_finite_exception

end RootSeparation.Solver
