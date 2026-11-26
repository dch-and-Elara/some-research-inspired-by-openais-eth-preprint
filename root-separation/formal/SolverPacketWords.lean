import SolverConcreteRoot
import SolverPacketIntegral

noncomputable section
namespace RootSeparation.Solver
open S11

variable {e : ℕ} (F : SourcePolynomial e) {s : ℕ} {c : Call F.f}
variable (G : CallLayout s c)
variable (cap : probeCount c.edges (callL s c) ≤ 2^e)

def callBinary (j : callProbes s c) : IntegerRing F.f :=
  binaryPoint F (binaryProbe e _ cap j)

def callPoint (j : callProbes s c) : RationalCoefficients F :=
  integerRational F.f (callBinary F cap j)

def nativeEntryValue (t : callCenters s c) (j : callProbes s c)
    (β : List ℕ) (g : Fin 64) (k : G.Packet) (bits : PacketPort G t g k → Bool) :
    RationalRing F.f :=
  nativePacket (K := RationalCoefficients F) G t (callPoint F cap j) β g k bits

theorem nativeEntry_integral (t : callCenters s c) (j : callProbes s c)
    (β : List ℕ) (g : Fin 64) (k : G.Packet) (bits : PacketPort G t g k → Bool) :
    nativeEntryValue F G cap t j β g k bits ∈ (integralRational F.f).range :=
  (coordinateOrder_nonnegative F.monic F.degree _).1
    (nativePacket_integral G t (K := RationalCoefficients F)
      (rationalValuation F) (rationalValuation_two F) (callPoint F cap j)
      (rationalValuation_integer F _) β g k bits)

/-- Packet table in the actual coefficient ring. The proof obligation
    is local integrality of the printed arithmetic expression. -/
def nativeTables : PacketTables G := fun t j β g k bits => by
  exact integralWord F.f (callPrecision s c t.val)
    (Classical.choose (nativeEntry_integral F G cap t j β g k bits))

theorem nativeTables_residue (t : callCenters s c) (j : callProbes s c)
    (β : List ℕ) (g : Fin 64) (k : G.Packet) (bits : PacketPort G t g k → Bool) :
    tryWord F.monic (callPrecision s c t.val) (nativeEntryValue F G cap t j β g k bits) =
      some (nativeTables F G cap t j β g k bits) := by
  classical
  unfold nativeTables tryWord
  rw [dif_pos (nativeEntry_integral F G cap t j β g k bits)]

end RootSeparation.Solver

#print axioms RootSeparation.Solver.nativeTables_residue
