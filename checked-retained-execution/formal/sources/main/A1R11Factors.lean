import A1R11Rows
import A1R11Gate

/-! Actual witness-local factor tape, including original Boolean row
and column tables via their metered bounded-arity tensor readers. -/

open scoped BigOperators
namespace A1R11
open A1R10 A1R9 AOracleMachineTime AOracleMachineTimeTape AOracleMachineTimeZero
open AOracleWitness AOracleSuccinct AOracleMachineTimeLocal

theorem tensorGate_eq {R : Type*} [CommRing R] {n delta : ℕ}
    (a : Fin n → Bool) (b : ℕ) (fit : n≤2^b) (ts : List (BoolTensor n delta)) :
    (if (runTensors (List.ofFn a) (ts.map (packTensor b))).result then (1:R) else 0) =
      tensorEval a ts := by
  induction ts with
  | nil => rfl
  | cons T ts ih =>
    obtain ⟨ha,_⟩ := readTensor_exact T a b fit
    let tail := (runTensors (List.ofFn a) (ts.map (packTensor b))).result
    change (if tail then 1 else 0)=_ at ih
    change (if ((readTensor (packTensor b T).1 (packTensor b T).2 (List.ofFn a)).result &&
      tail) then 1 else 0) = (if T.read a then 1 else 0)*tensorEval a ts
    change (readTensor (packTensor b T).1 (packTensor b T).2 (List.ofFn a)).result=_ at ha
    rw [ha,← ih]
    cases T.read a <;> cases tail <;> simp

def bitBlock {p ell : ℕ} (hp : 0<p) {f : List (A1R10.Word p)}
    (he : 0<f.length) (hv : 0<ell) (b : Bool) : UVBlock f ell :=
  if b then uvOne hp he hv else uvZero hp f ell

theorem bitBlock_read {p ell : ℕ} (hp : 0<p) {f : List (A1R10.Word p)}
    (he : 0<f.length) (hv : 0<ell) (b : Bool) :
    uvRead hp f ell (bitBlock hp he hv b)=(if b then 1 else 0) := by
  cases b <;> simp [bitBlock]

def runFactors {p r c m delta b bc ell : ℕ} (hp : 0<p)
    {f : List (A1R10.Word p)} (he : 0<f.length) (hv : 0<ell)
    (P : Packed r c m delta bc f ell) (br : ℕ) (z : Code r c b) : Meter (List (UVBlock f ell)) :=
  let a := runTensors (List.ofFn z.1) (P.rows.map (packTensor br))
  let bq := runTensors (List.ofFn z.2.1) (P.cols.map (packTensor bc))
  let q := runRows hp he hv (List.ofFn z.2.1) P.momentTape
    (List.ofFn z.1) (rawChoices z) (List.ofFn P.rowTape)
  ⟨bitBlock hp he hv a.result :: bitBlock hp he hv bq.result :: q.result,
    a.steps+bq.steps+q.steps+2*uvWidth f.length ell p+6⟩

def factorBudget (r c m b br bc delta s R C e ell p : ℕ) (hp : 0<p) : ℕ :=
  R*tensorBudget r delta br+C*tensorBudget c delta bc+r*rowBudget m b c bc s e ell p hp+
  2*uvWidth e ell p+6

theorem runFactors_exact {p r c m delta b bc ell : ℕ} (hp : 0<p)
    {f : List (A1R10.Word p)} (he : 0<f.length) (hv : 0<ell)
    (P : Packed r c m delta bc f ell) (br : ℕ) (fr : r≤2^br) (fc : c≤2^bc)
    (fit : m+1≤2^b) (w : Witness r c m)
    (s : ℕ) (hl : ∀ j,(P.localRecipe j).length≤s) (hm : ∀ k,(P.moment k).length≤s) :
    let u := runFactors hp he hv P br (encode fit w)
    u.result.length=r+2 ∧
    (u.result.map (uvRead hp f ell)).prod=weight (rootTerms (P.denote hp)) w ∧
    u.steps≤factorBudget r c m b br bc delta s P.rows.length P.cols.length f.length ell p hp := by
  let a := runTensors (List.ofFn w.1) (P.rows.map (packTensor br))
  let g := runTensors (List.ofFn w.2.1) (P.cols.map (packTensor bc))
  let q := runRows hp he hv (List.ofFn w.2.1) P.momentTape
    (List.ofFn w.1) (allocationWords b w.2.2) (List.ofFn P.rowTape)
  have hrw := runRows_exact hp he hv P w fit s hl hm (List.finRange r)
  have hrows {α : Type} (F : Fin r → α) : (List.finRange r).map F=List.ofFn F := by
    simp [List.finRange,Function.comp_def]
  dsimp only at hrw
  rw [hrows w.1,hrows (fun j => encodeBits b (w.2.2 j).val),hrows P.rowTape,List.length_finRange] at hrw
  obtain ⟨hql,hqv,hqc⟩ := hrw
  change q.result.length=r at hql
  change q.result.map (uvRead hp f ell)=_ at hqv
  change q.steps≤_ at hqc
  have ha := (runTensors_exact w.1 br 1 fr P.rows).2
  have hg := (runTensors_exact w.2.1 bc 1 fc P.cols).2
  have hav := tensorGate_eq (R:=AOracleCoordinates.Truncated (Modulus p hp f) ell) w.1 br fr P.rows
  have hgv := tensorGate_eq (R:=AOracleCoordinates.Truncated (Modulus p hp f) ell) w.2.1 bc fc P.cols
  change a.steps≤_ at ha
  change g.steps≤_ at hg
  change (if a.result then 1 else 0)=_ at hav
  change (if g.result then 1 else 0)=_ at hgv
  change (bitBlock hp he hv a.result :: bitBlock hp he hv g.result :: q.result).length=r+2 ∧
    ((bitBlock hp he hv a.result :: bitBlock hp he hv g.result :: q.result).map (uvRead hp f ell)).prod=_ ∧
    a.steps+g.steps+q.steps+2*uvWidth f.length ell p+6≤_
  refine ⟨?_,?_,?_⟩
  · simp only [List.length_cons,hql]
  · simp only [List.map_cons,List.prod_cons,bitBlock_read,hav,hgv,hqv]
    rw [hrows (evaluateRow (P.denote hp) w),List.prod_ofFn]
    rw [← AOracleSuccinct.evaluate_eq,AOracleSuccinct.evaluate,AOracleMachine.foldProduct_eq,mul_assoc]
    rfl
  · unfold factorBudget
    omega

#print axioms tensorGate_eq
#print axioms bitBlock_read
#print axioms runFactors_exact
end A1R11




