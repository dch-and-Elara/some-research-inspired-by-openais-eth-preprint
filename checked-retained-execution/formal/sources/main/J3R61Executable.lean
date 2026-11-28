import J3R61Product

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3700000

/-! Executable explicit-tape presentation of the proved literal source
algorithm. No Polynomial evaluation or quotient representative is used
by this code; the adapter relates its input to the literal coefficients. -/
namespace J3R61
open Polynomial V8NativeMessage
open V8NativeMessage.C3.NativeAssembly.MainScan V8NativeMessage.N6.MainFiber

def readTape (D : ℕ) (t : ℤ) (cs : List ℚ) : Paid (Pair ℤ) :=
  let int := cs.map (scaledCoefficient D)
  let a := horner t int
  ⟨a.value,2*int.length+a.ops⟩

def explicitRow {I : Type*} (ord : List I) (tapes : I → List ℚ) (D : ℕ) (t : ℤ) (i : I) :
    Paid (Pair ℤ) :=
  let read := fun j => readTape D t (tapes j)
  let r := sumRow read ord
  let q := read i
  ⟨⟨r.value,q.value.d⟩,r.ops+q.ops⟩

def explicitProduct {W I : Type*} {F : Finset (W×W)}
    (ord : List I) (tape : N1.Occ F → I → List ℚ) (R Q : ℕ) (node : ℕ)
    (direction : I) (s : W → Bool) (terms : List (Clause F)) : Paid (Pair ℚ) :=
  let d := printedScale R Q
  let t := (node:ℤ)+1
  let r := fun o : N1.Occ F => explicitRow ord (tape o) d.value t direction
  let exponent := factorDegrees terms
  let p := paidProduct (terms.map (factorAt (d.value:ℤ) r s))
  let den := powerLoop d.value exponent.value
  ⟨rationalPair p.value den.value,d.ops+1+exponent.ops+p.ops+den.ops+2⟩

noncomputable section
open scoped Polynomial Classical

def readSourceCoeffs (R : ℕ) (p : ℚ[X]) : List ℚ :=
  List.ofFn (fun k : Fin (R+1) => p.coeff k.val)

theorem readTape_eq_evalCoord (p : ℚ[X]) (D R : ℕ) (t : ℤ) :
    readTape D t (readSourceCoeffs R p) = evalCoord p D R t := by
  have h : (readSourceCoeffs R p).map (scaledCoefficient D) = coeffTape p D R := by
    simp only [readSourceCoeffs,List.map_ofFn,Function.comp_def,coeffTape]
  unfold readTape evalCoord
  rw [h]

theorem explicitRow_eq_evalRow {I : Type*} (ord : List I) (p : I → ℚ[X])
    (D R : ℕ) (t : ℤ) (i : I) :
    explicitRow ord (fun v => readSourceCoeffs R (p v)) D t i = evalRow ord p D R t i := by
  simp only [explicitRow,evalRow,readTape_eq_evalCoord]

variable {W : Type*} [Fintype W] [DecidableEq W]
variable {F : Finset (W×W)} {r Q J : ℕ}

theorem explicitProduct_eq_signedRun (L : CloneTuple F r Q J)
    (hreg : ∀ v, GraphCutMoments.degree F v=3)
    (R : ℕ) (direction : Clone W) (s : W → Bool) (terms : Finset (Clause F)) :
    explicitProduct (coords W) (fun o v => readSourceCoeffs R (N1.row L hreg o v))
      R Q L.node.val direction s terms.toList = signedRun L hreg R direction s terms := by
  simp only [explicitProduct,signedRun,explicitRow_eq_evalRow,N1.tInt]

#print axioms readTape_eq_evalCoord
#print axioms explicitRow_eq_evalRow
#print axioms explicitProduct_eq_signedRun

end
end J3R61
