
import J6R28GeneratedRootFrameBits
import J6R24MeteredRecursionFrame
import J6SourcePrecision

/-! Generate the literal R26/R27 Frame, at precisely the odd root's
printed precision, with one monic-modulus tape (no separate alleged
modulus value or prepared coefficient-word tape as input). -/
namespace J6R28GeneratedRootFrame
open scoped Polynomial
open Polynomial A1R10 AOracleMachineTime J6R24MeteredRecursion J6Mesh
set_option maxHeartbeats 3300000

def frameBuildFee (e p : ℕ) : ℕ := 4+e*(4*p+6)+3

def makeFrame {f : ℤ[X]} (data : LiteralPresentation f) (positive : 0<f.natDegree)
    (p : ℕ) (hp : 0<p) : Meter (Frame f p) :=
  let A := widenLower p data.lower
  let len : A.result.length=f.natDegree := by
    rw [(widen_lower_exact p data.lower).1,List.length_map,data.size]
  ⟨⟨hp,A.result,len.symm ▸ positive,widened_modulus_exact p hp data⟩,A.steps+3⟩

theorem frame_build_receipt {f : ℤ[X]} (data : LiteralPresentation f) (eP : 0<f.natDegree)
    (p : ℕ) (hp : 0<p) :
    let F := makeFrame data eP p hp
    F.result.words=data.lower.map (zeroExtend p) ∧
      F.result.words.length=f.natDegree ∧
      F.steps=frameBuildFee f.natDegree p := by
  obtain ⟨h,c⟩ := widen_lower_exact p data.lower
  refine ⟨h,?_,?_⟩
  · change (widenLower p data.lower).result.length=f.natDegree
    rw [h,List.length_map,data.size]
  · change (widenLower p data.lower).steps+3=frameBuildFee f.natDegree p
    rw [c,frameBuildFee,data.size]

theorem printed_precision_positive (m base : ℕ) : 0<J6SourcePrecision.printed m base := by
  have hM : 0<M m := by unfold M; positivity
  have hpad : 0<8*M m*(a m+1) := by positivity
  unfold J6SourcePrecision.printed
  omega

def printedFrame {f : ℤ[X]} (data : LiteralPresentation f) (eP : 0<f.natDegree) (m base : ℕ) :
    Meter (Frame f (J6SourcePrecision.printed m base)) :=
  makeFrame data eP _ (printed_precision_positive m base)

theorem printed_frame_exact {f : ℤ[X]} (data : LiteralPresentation f) (eP : 0<f.natDegree)
    (m base : ℕ) :
    let P := J6SourcePrecision.printed m base
    let F := printedFrame data eP m base
    F.result.words=data.lower.map (zeroExtend P) ∧
    F.result.words.length=f.natDegree ∧
    F.steps=frameBuildFee f.natDegree P :=
  frame_build_receipt data eP _ (printed_precision_positive m base)

#print axioms frame_build_receipt
#print axioms printed_precision_positive
#print axioms printed_frame_exact
end J6R28GeneratedRootFrame
