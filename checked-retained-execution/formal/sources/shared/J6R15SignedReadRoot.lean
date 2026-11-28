import J6R15SignedReadBase
import J6R14ZeroModePlanted

/-! The signed readout followed by rational mesh interpolation. Its
only remaining input identity is at the literal receiving-ring level,
not an assumption about an already lifted integer or a raw CNF count. -/
namespace J6R15SignedRead
set_option maxHeartbeats 3800000
open scoped Classical Polynomial BigOperators
open Polynomial P11FullPacking J6Mesh J6OrientedHost J6OrientedHostEval
open J6RepairedCentered J6NativeHeightDyadic J6NativeHeightMesh J6NativeHeightResidue
open J6R9Recursive J6ActiveRun J6ActiveSchedule J6R11Blueprint J6R12Blueprint
open J6R12Repack J6R14ZeroMode

def castBox (f : ℤ[X]) (ell : ℕ) {p q : ℕ} (h : p=q) (x : Box f ell p) :
    Box f ell q := h ▸ x

section Decode
variable {W S : Type*} [LinearOrder S] [Fintype S] [Fintype W]

noncomputable def localLiteralSlot
    (m q l : ℕ) (T : Plant W m q)
    (mask : MaskFamily (a m) (K m) S) (w : Fin (a m) → S)
    (hm : m≤K m) (hL : 2*l=L m) (i : J6Recovery.Addr m) :
    DenominatorBudget.TwoLocal := by
  letI : DecidableEq (Pad w m (K m) l) := Classical.decEq _
  exact residueSlot (oldOK T w) (newOK T w)
    (fun k x => ((shiftAt m l mask w hm hL i k).map x).getD false) (scalar m i)

theorem finite_literalSlot (f : ℤ[X]) (ell m q b l : ℕ) (T : Plant W m q)
    (mask : MaskFamily (a m) (K m) S) (w : Fin (a m) → S)
    (hm : m≤K m) (hL : 2*l=L m) (i : J6Recovery.Addr m) :
    J6ZeroTransport.reduceAt _ (J6R10Integral.box_two_nil (J6SourcePrecision.printed m b) f ell)
         (localLiteralSlot m q l T mask w hm hL i) =
      boxBase _ f ell (literalRead m q b l T mask w hm hL i) := by
  rw [← boxBase_reduce,localLiteralSlot,literalRead]
  letI : DecidableEq (Pad w m (K m) l) := Classical.decEq _
  exact congrArg (boxBase _ f ell) (map_slot (P:=Ports m l w)
    (J6ZeroTransport.reduceBase (J6SourcePrecision.printed m b)) (oldOK T w) (newOK T w)
    (fun k x => ((shiftAt m l mask w hm hL i k).map x).getD false) (scalar m i))

theorem printed_precision_pos (m b : ℕ) : 0<J6SourcePrecision.printed m b := by
  unfold J6SourcePrecision.printed
  have h := J6Mesh.b_pos m
  have hm : 0<M m := by unfold M; positivity
  have hL : 0<L m := by unfold L; positivity
  positivity

noncomputable def readLayer
    (f : ℤ[X]) (ell m q b l : ℕ)
    (mask : MaskFamily (a m) (K m) S) (w : Fin (a m) → S)
    (hm : m≤K m) (hL : 2*l=L m) (hf : f.Monic) (hℓ : 0<ell)
    (recv : J6Recovery.Addr m → Box f ell (J6SourcePrecision.printed m b)) :
    ℚ[X] :=
  Lagrange.interpolate Finset.univ (point m) (fun i =>
    ((receiverNumeral f ell m q b l mask w hm hL i hf hℓ (recv i)).1:ℚ)/(sampleDen m i:ℚ)^m)

theorem readLayer_exact
    (f : ℤ[X]) (ell m q b l : ℕ) (T : Plant W m q)
    (mask : MaskFamily (a m) (K m) S) (w : Fin (a m) → S)
    (hm : m≤K m) (hL : 2*l=L m) (hf : f.Monic) (hF : 0<f.natDegree)
    (hℓ : 0<ell) (hS : Fintype.card S=64) (hz : coreA T (fun _ => false)=true)
    (recv : J6Recovery.Addr m → Box f ell (J6SourcePrecision.printed m b))
    (hrecv : ∀ i, recv i =
      J6ZeroTransport.reduceAt _ (J6R10Integral.box_two_nil (J6SourcePrecision.printed m b) f ell)
        (localLiteralSlot m q l T mask w hm hL i)) :
    readLayer f ell m q b l mask w hm hL hf hℓ recv = J7R10Readout.layer m q T := by
  unfold readLayer
  have he : (fun i : J6Recovery.Addr m =>
      ((receiverNumeral f ell m q b l mask w hm hL i hf hℓ (recv i)).1:ℚ)/(sampleDen m i:ℚ)^m) =
      J7R10Readout.sample m q b l T mask w hm hL := by
    funext i
    refine (receiverSample_exact f ell m q b l T mask w hm hL i hf (printed_precision_pos m b)
      hF hℓ (recv i) hS hz ((hrecv i).trans (finite_literalSlot f ell m q b l T mask w hm hL i))).trans ?_
    exact (J7R10Readout.sample_exact m q b l T mask w hm hL hS hz i).symm
  rw [he]
  exact J7R10Readout.reconstructed_exact m q b l T mask w hm hL hS hz

variable {V : Type*} [DecidableEq V] [Fintype V] [Nonempty V]
open Std.Sat
open J7R10Plant

theorem readRaw_count
    (f : ℤ[X]) (ell b l : ℕ) (F : CNF V)
    (mask : MaskFamily (a (J7R10Readout.mCNF F)) (K (J7R10Readout.mCNF F)) S)
    (w : Fin (a (J7R10Readout.mCNF F)) → S)
    (hm : J7R10Readout.mCNF F≤K (J7R10Readout.mCNF F)) (hL : 2*l=L (J7R10Readout.mCNF F))
    (hf : f.Monic) (hF : 0<f.natDegree) (hℓ : 0<ell) (hS : Fintype.card S=64)
    (recv : J6Recovery.Addr (J7R10Readout.mCNF F) →
      Box f ell (J6SourcePrecision.printed (J7R10Readout.mCNF F) b))
    (hrecv : ∀ i, recv i = J6ZeroTransport.reduceAt _
      (J6R10Integral.box_two_nil (J6SourcePrecision.printed (J7R10Readout.mCNF F) b) f ell)
      (localLiteralSlot (J7R10Readout.mCNF F) (J7R10Readout.qCNF F) l
        (physicalPlant (J7R10Readout.H F)) mask w hm hL i)) :
    (readLayer f ell (J7R10Readout.mCNF F) (J7R10Readout.qCNF F) b l
      mask w hm hL hf hℓ recv).eval 1 - 1 = (PinnedCNF.modelCount F:ℚ) := by
  rw [readLayer_exact f ell _ _ b l (physicalPlant (J7R10Readout.H F)) mask w hm hL
    hf hF hℓ hS (planted_guard_zero F) recv hrecv]
  change (LayerRecovery.layerPolynomial _ _).eval 1 - 1 = _
  rw [guarded_origin_exact F]
  push_cast
  ring
end Decode

#print axioms castBox
#print axioms finite_literalSlot
#print axioms printed_precision_pos
#print axioms readLayer_exact
#print axioms readRaw_count
end J6R15SignedRead