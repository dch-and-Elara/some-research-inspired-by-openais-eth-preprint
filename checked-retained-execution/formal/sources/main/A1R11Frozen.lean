import A1R11Machine

/-! Machine entry point on already serialized input and already guessed
bit fields. Unlike the mathematical Packed convenience wrapper, this
function never calls a Fin-indexed recipe function to generate a list. -/

namespace A1R11
open A1R10 A1R9 AOracleWitness AOracleSuccinct AOracleCoordinates AOracleThreshold
open AOracleMachineTime AOracleMachineTimeTape AOracleMachineTimeZero AOracleMachineTimeLocal

structure Frozen {p : ℕ} (c bc : ℕ) (f : List (A1R10.Word p)) (ell : ℕ) where
  limit : List Bool
  legalRows : List (List Bool)
  counters : List (List Bool × List Bool)
  rowTensors : List TensorTape
  colTensors : List TensorTape
  rowRecords : List (List (Pick c bc f ell))
  momentRecords : List (WireTape c bc f ell)

structure RawGuess (p : ℕ) where
  y : List Bool
  x : List Bool
  alloc : List (List Bool)
  d : A1R10.Word p

def rawGuess {p r c b : ℕ} (z : Code r c b × AOracleThreshold.Word p) : RawGuess p :=
  ⟨List.ofFn z.1.1,List.ofFn z.1.2.1,rawChoices z.1,thresholdBits z.2⟩

def freezeInput {p r c m delta bc ell : ℕ} {f : List (A1R10.Word p)}
    (P : Packed r c m delta bc f ell) (br b q : ℕ) (beta : Fin m →₀ ℕ) :
    Frozen c bc f ell :=
  ⟨encodeBits (b+1) (m+1),List.ofFn (legalTape P.target),counterTape b q beta (List.finRange m),
    P.rows.map (packTensor br),P.cols.map (packTensor bc),List.ofFn P.rowTape,P.momentTape⟩

def frozenGate {p c bc ell : ℕ} {f : List (A1R10.Word p)} (q : ℕ) (T : Frozen c bc f ell)
    (z : RawGuess p) : Meter Bool :=
  let g := checkFrames T.limit z.alloc
  if g.result then
    let s := runLegal z.alloc T.legalRows
    let n := checkModes q z.alloc T.counters
    ⟨s.result && n.result,g.steps+s.steps+n.steps+5⟩
  else ⟨false,g.steps+5⟩

def frozenFactors {p c bc ell : ℕ} (hp : 0<p) {f : List (A1R10.Word p)}
    (he : 0<f.length) (hv : 0<ell) (T : Frozen c bc f ell) (z : RawGuess p) :
    Meter (List (UVBlock f ell)) :=
  let a := runTensors z.y T.rowTensors
  let b := runTensors z.x T.colTensors
  let t := runRows hp he hv z.x T.momentRecords z.y z.alloc T.rowRecords
  ⟨bitBlock hp he hv a.result :: bitBlock hp he hv b.result :: t.result,
    a.steps+b.steps+t.steps+2*uvWidth f.length ell p+6⟩

/-- Really executes on a serialized input, not on Packed functions.
No factor or count oracle is used inside the branch. -/
def frozenUV {p c bc ell : ℕ} (q : ℕ) (hp : 0<p) {f : List (A1R10.Word p)}
    (he : 0<f.length) (hv : 0<ell) (T : Frozen c bc f ell) (i j : ℕ) (z : RawGuess p) : Meter Bool :=
  let a := frozenGate q T z
  if a.result then
    let b := frozenFactors hp he hv T z
    let c := uvProductAccept hp he hv b.result i j z.d
    ⟨c.result,a.steps+b.steps+c.steps+2⟩
  else ⟨false,a.steps+2⟩

theorem frozenUV_model {p r c m delta b bc ell : ℕ} (q : ℕ) (hp : 0<p)
    {f : List (A1R10.Word p)} (he : 0<f.length) (hv : 0<ell)
    (P : Packed r c m delta bc f ell) (br : ℕ) (beta : Fin m →₀ ℕ)
    (i j : ℕ) (z : Code r c b × AOracleThreshold.Word p) :
    frozenUV q hp he hv (freezeInput P br b q beta) i j (rawGuess z) =
      runPackedUV q hp he hv P br beta i j z := rfl

theorem frozenUV_count_and_cost {p r c m delta b bc ell : ℕ} (q : ℕ) (hp : 0<p)
    {f : List (A1R10.Word p)} (he : 0<f.length) (hv : 0<ell)
    (hf : (Modulus p hp f).Monic) (hd : (Modulus p hp f).natDegree=f.length)
    (P : Packed r c m delta bc f ell) (br : ℕ) (beta : Fin m →₀ ℕ)
    (hq : 0<q) (fr : r≤2^br) (fc : c≤2^bc) (fit : m+1≤2^b) (hr : r<2^q)
    (hb : ∀ k,beta k<2^q) (s : ℕ) (hl : ∀ j,(P.localRecipe j).length≤s)
    (hm : ∀ k,(P.moment k).length≤s) (i : Fin f.length) (j : Fin ell) :
    let run := fun z : Code r c b × AOracleThreshold.Word p =>
      frozenUV q hp he hv (freezeInput P br b q beta) i.val j.val (rawGuess z)
    let coord := doubleCoord (Modulus p hp f) hf ell
      (⟨f.length-1-i.val,by have := i.isLt; omega⟩,⟨ell-1-j.val,by have := j.isLt; omega⟩)
    (countVerify (fun z => (run z).result) : ZMod (2^p)) =
      coord (MvPolynomial.coeff beta (rootPolynomial (rootTerms (P.denote hp)))) ∧
    ∀ z, (run z).steps≤
      gateBudget r m b q+factorBudget r c m b br bc delta s P.rows.length P.cols.length f.length ell p hp+
      productAcceptBudget (r+2) f.length ell p+2 := by
  refine ⟨?_,?_⟩
  · simpa only [frozenUV_model] using
      runPackedUV_count q hp he hv hf hd P br beta hq fr fc fit hr hb s hl hm i j
  · intro z
    simpa only [frozenUV_model] using
      runPackedUV_cost q hp he hv hf hd P br beta hq fr fc fit hr hb s hl hm i j z

#print axioms frozenUV_model
#print axioms frozenUV_count_and_cost
end A1R11
