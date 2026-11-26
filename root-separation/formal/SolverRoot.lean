import SolverPacket
import SolverDeformation
import SolverProbes

noncomputable section
namespace RootSeparation.Solver

open Entry S11 GraphCutMoments Execution Polynomial Classical
open scoped BigOperators

variable {V : Type} [Fintype V] [DecidableEq V]
variable (E : Finset (V × V)) (reg : ∀ v, degree E v = 3) (σ : V → Bool)
variable (F : SourcePolynomial (4*lambda (size E)))

def rootCall : Call F.f where
  depth := 0
  precision := initialPrecision (V := V)
  precision_pos := Nat.succ_pos _
  network := entryNetwork E reg σ (IntegerRing F.f)

theorem rootCall_wire_count : (rootCall E reg σ F).edges = 10*n (V := V) := wire_count E reg

def rootLayout (hn : bigRoot (n (V := V))) : CallLayout (size E) (rootCall E reg σ F) where
  Packet := RootPackets E reg
  finite := inferInstance
  left := fun v => selectedLabels (row E reg) (column E) (fun _ => 0) (.inl v)
  right := fun v => selectedLabels (row E reg) (column E) (fun _ => 0) (.inr v)
  packing := chosenPacking E reg hn
  cells := (chosenPacking_spec E reg hn).1
  legal := (chosenPacking_spec E reg hn).2.1
  positive := root_active E reg (by have h := bigRoot_n hn; omega)
  u_le_a := by
    change rootU E ≤ rootA E
    have ha : rootA E = 2 * rootU E := (root_parameters (size E)).1
    rw [ha]
    omega

abbrev RootCenter := Active (rootA E) (rootU E)
abbrev RootProbe := Fin (probeCount (rootM E) (rootL E))

theorem rootLeaf_word :
    leafValue (rootCall E reg σ F) =
      (PinnedCNF.modelCount (PinnedCNF.formula E σ) : WordRing F.f (initialPrecision (V := V))) := by
  change ((entryNetwork E reg σ (IntegerRing F.f)).map (fromInteger F.f _)).contract = _
  rw [Network.map_contract, entryNetwork_contract, map_natCast]

def rootBinary (hn : bigRoot (n (V := V))) (j : RootProbe E) : IntegerRing F.f :=
  binaryPoint F (probe E reg hn j)

def rootCodec : Codec E (R := fun t => WordRing F.f (nativePrecision E t))
    (I := Fin (4*lambda (size E))) :=
  fun t => wordCoords F.monic F.degree (nativePrecision E t) (nativePrecision_positive E t)

section Arithmetic

variable {K : Type*} [Field K] [CharZero K]
variable (embed : IntegerRing F.f →+* K) (hn : bigRoot (n (V := V)))

/-- Concrete Hermite readout after canonical lifting of the word returned
    by every probe's shared accumulator. The result is in the fraction field
    before the final reduction to the caller's precision. -/
def rootReadout (samples : (t : RootCenter E) → RootProbe E → WordRing F.f (nativePrecision E t.val)) : K :=
  readout (fun t : RootCenter E => S7.scaledCenter (rootA E) t.val)
    (fun t => multiplicity (rootM E) (rootU E) t.val) (fun _ j => embed (rootBinary E reg F hn j))
    (fun t j => embed (liftCanonical F.monic F.degree (nativePrecision_positive E t.val) (samples t j)))

set_option maxHeartbeats 2400000 in
theorem rootReadout_error (v : AddValuation K (WithTop ℤ)) (h₂ : v (2:K) = 1)
    (hζ : ∀ j, 0 ≤ v (embed (rootBinary E reg F hn j)))
    (hunit : ∀ i j, i ≠ j → v (embed (rootBinary E reg F hn i) -
      embed (rootBinary E reg F hn j)) = 0)
    (huM : rootU E ≤ rootM E)
    (samples : (t : RootCenter E) → RootProbe E → WordRing F.f (nativePrecision E t.val))
    (herr : ∀ (t : RootCenter E) (j : RootProbe E), (↑(nativePrecision E t.val:ℤ) : WithTop ℤ) ≤
      v (embed (liftCanonical F.monic F.degree (nativePrecision_positive E t.val) (samples t j)) -
        (rootDeformation E reg σ hn : K[X]).eval
          (S7.scaledCenter (rootA E) t.val + embed (rootBinary E reg F hn j)))) :
    ∃ error : K, 0 ≤ v error ∧ rootReadout E reg F embed hn samples =
      (PinnedCNF.modelCount (PinnedCNF.formula E σ) : K) + (2:K)^(initialPrecision (V := V))*error := by
  have hM : 0 < rootM E := (Nat.zero_le _).trans_lt
    (root_active E reg (by have hh := bigRoot_n hn; omega))
  obtain ⟨error,he,hr⟩ := recover_modular (J := RootProbe E) v h₂ (rootM E) (rootA E) (rootU E)
    (initialPrecision (V := V)) hM (root_certified E reg hn).1 huM
    (fun _ j => embed (rootBinary E reg F hn j)) (fun _ => hζ) (fun _ => hunit)
    (rootDeformation E reg σ hn) (rootDeformation_window E reg σ hn)
    (fun t => by rw [Fintype.card_fin]; exact rootDeformation_local (K := K) E reg σ hn t.val)
    _ herr
  rw [rootDeformation_origin] at hr
  exact ⟨error,he,hr⟩

end Arithmetic

section Execution

variable {cutoff : ℕ}
variable (ops : RecursionOps F.f (4*lambda (size E)) (size E) cutoff)
variable (hn : bigRoot (n (V := V)))
variable (tables : PacketTables (rootLayout E reg σ F hn))
variable (valid : ∀ t j β g,
    ops.admissible (childCall F.monic F.degree (rootLayout E reg σ F hn) tables t j β g))

/-- Wegener's root child interface, filled with child values returned by
    the well-founded recursion. The inactive branches are outside both
    source loops and serve only to totalize the interface. -/
def rootChild : Child (R := fun t => WordRing F.f (nativePrecision E t)) :=
  fun t j β g =>
    if ht : t ∈ centers (rootU E) (rootL E) then
      if hj : j < probeCount (rootM E) (rootL E) then
        (runCall ops (childCall F.monic F.degree (rootLayout E reg σ F hn) tables ⟨t,ht⟩ ⟨j,hj⟩ β g)
          (valid ⟨t,ht⟩ ⟨j,hj⟩ β g)).value
      else 0
    else 0

def rootSample (t : RootCenter E) (j : RootProbe E) : WordRing F.f (nativePrecision E t.val) :=
  (rootCodec E F t.val).symm
    (executeProbe E reg hn (rootCodec E F) ops.track (rootChild E reg σ F ops hn tables valid) t.val j.val).accumulator

def rootExecutionTrace : List Step :=
  executeRoot E reg σ cutoff (rootCodec E F) ops.track (rootChild E reg σ F ops hn tables valid)

theorem rootExecutionTrace_project :
    rootProjection (rootExecutionTrace E reg σ F ops hn tables valid) =
      runEvents E reg σ cutoff (fun _ _ _ _ => (0 : ModTwoPow ℤ _)) :=
  executeRoot_project E reg σ cutoff _ _ _ _

theorem rootExecutionTrace_lower (simple : Simple E) (large : max (2^131071) cutoff < n (V := V)) :
    (2:ℝ)^((n (V := V):ℝ) / (2*Real.sqrt (Real.logb 2 (n (V := V))))) ≤
      ((executedDigits (rootExecutionTrace E reg σ F ops hn tables valid)).length : ℝ) :=
  executed_root_lower E simple reg σ cutoff _ _ _ large

end Execution

#print axioms rootCall_wire_count
#print axioms rootLeaf_word
#print axioms rootReadout_error
#print axioms rootChild
#print axioms rootExecutionTrace_project
#print axioms rootExecutionTrace_lower

end RootSeparation.Solver
