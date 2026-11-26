import SolverRecursion

noncomputable section
namespace RootSeparation.Solver
open S11 SourceDensity Polynomial Classical

variable {f : ℤ[X]} (s : ℕ) (c : Call f)

def degreeBound : Prop :=
  (∀ x, fiberCount c.network.row x ≤ degreeEnvelope s) ∧
  (∀ y, fiberCount c.network.col y ≤ degreeEnvelope s)

theorem callU_le_callA : callU s c ≤ callA s c := by
  have h : retained s c.depth ≤ ∑ j ∈ Finset.range (c.depth+1), retained s j :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 (Nat.lt_succ_self _))
  change retained s c.depth ≤ 2 * ∑ j ∈ Finset.range (c.depth+1), retained s j
  omega

def selectedCell : c.network.Wire → RootCell (callA s c) :=
  cellAt c.network.row c.network.col (selectedLabels c.network.row c.network.col (fun _ => 0))

/-- Use the frozen conditional-expectation labels and exact padded
    placement on the current incidence functions. The two numerical
    hypotheses are the printed active-call packing conditions. -/
def selectCallLayout (active : leafThreshold s < c.edges) (hdegree : degreeBound s c)
    (hCollision : 2 * (Fintype.card (RootCell (callA s c)))^2 * degreeEnvelope s ≤ c.edges)
    (hSlots : callL s c * Fintype.card (RootCell (callA s c)) ≤ c.edges) : CallLayout s c := by
  letI : Fintype c.network.Wire := c.network.finiteWire
  letI : Fintype c.network.Row := c.network.finiteRow
  letI : Fintype c.network.Col := c.network.finiteCol
  let a := callA s c
  let Δ := degreeEnvelope s
  have cert : CollisionCertificate (selectedCell s c) (Δ : ℚ) := by
    constructor
    · exact selected_collision c.network.row c.network.col (fun _ => 0) Δ hdegree.1 hdegree.2
    · exact_mod_cast hCollision
  let pack := exact_packets (selectedCell s c) (Δ : ℚ) cert hSlots
  exact {
    Packet := S8.Packet (Fin a) (Fin 64) (exactPad (selectedCell s c))
    finite := inferInstance
    left := fun v => selectedLabels c.network.row c.network.col (fun _ => 0) (.inl v)
    right := fun v => selectedLabels c.network.row c.network.col (fun _ => 0) (.inr v)
    packing := Classical.choose pack
    cells := (Classical.choose_spec pack).1
    legal := by rw [(Classical.choose_spec pack).1]; exact cert
    positive := active
    u_le_a := callU_le_callA s c }

theorem childCall_degrees {e : ℕ} (hf : f.Monic) (he : f.natDegree = e)
    (G : CallLayout s c) (tables : PacketTables G)
    (hdegree : degreeBound s c) (hpack : 2*callL s c ≤ degreeEnvelope s)
    (t : callCenters s c) (j : callProbes s c) (β : List ℕ) (g : Fin 64) :
    degreeBound s (childCall hf he G tables t j β g) := by
  classical
  constructor
  · rintro ⟨x | y,h⟩
    · have hh := S8.DChild.old_degree_left c.network.row c.network.col G.left G.right
        (G.coord t) g x h
      refine le_of_eq_of_le ?_ (hdegree.1 x)
      refine Eq.trans ?_ hh
      simp only [fiberCount, ← Fintype.card_subtype]
      exact Fintype.card_congr (Equiv.refl _)
    · have hh := S8.DChild.old_degree_right c.network.row c.network.col G.left G.right
        (G.coord t) g y h
      refine le_of_eq_of_le ?_ (hdegree.2 y)
      refine Eq.trans ?_ hh
      simp only [fiberCount, ← Fintype.card_subtype]
      exact Fintype.card_congr (Equiv.refl _)
  · intro p
    change fiberCount (S8.DChild.childPacket G.packing.position :
      ChildEdge c.network G.left G.right (G.coord t) g → G.Packet) p ≤ _
    exact (S8.DChild.packet_degree _ _ _ _ _ _ _ _).trans (by simpa using hpack)

#print axioms callU_le_callA
#print axioms selectCallLayout
#print axioms childCall_degrees

end RootSeparation.Solver
