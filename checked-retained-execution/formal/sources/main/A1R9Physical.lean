import A1R9Register
import AOracleSuccinctPhysical

/-! Scalar specialization of the frozen native physical recipes. The
proof composes the actual signed local/cross generators with the metered
receiver; the bound is for the prepared bit tapes (not the cost of
generating a legal packing or all coefficients from compact input). -/

namespace A1R9
open AOracleMachineTime AOracleMachineTimeTape AOracleSuccinct
open AOracleWitness AOracleThreshold
open AOracleSuccinctPacket AOracleSuccinctPhysical AOracleSuccinctKernel

section ScalarPhysical
variable {r c m packets G a i delta p : ℕ}

def scalarPhysical (rows : List (BoolTensor r delta)) (columns : List (BoolTensor c delta))
    (row : Ports r packets G (2^a)) (col : Ports c packets G (2^a))
    (modes : Fin m → Mode packets G i p) (t : ℤ) (z : ZMod (2^p)) :
    Recipes (ZMod (2^p)) r c m delta :=
  compile rows columns row col modes
    (fun j k => modular p a t (((col.slot k).val:ℤ)-((row.slot j).val:ℤ)) z)
    (fun j mode => crossCell p a i mode.exponent.val t
      (row.slot j).val mode.tile.val z)

theorem physicalRecipe_lengths (rows : List (BoolTensor r delta)) (columns : List (BoolTensor c delta))
    (row : Ports r packets G (2^a)) (col : Ports c packets G (2^a))
    (modes : Fin m → Mode packets G i p) (t : ℤ) (z : ZMod (2^p)) :
    let L := scalarPhysical rows columns row col modes t z
    (∀ j, (L.localRecipe j).length≤c) ∧ ∀ k, (L.moment k).length≤c := by
  dsimp only
  constructor
  · intro j
    apply scanRecipe_length
  · intro k
    apply scanRecipe_length

theorem physicalScalar_meter (rows : List (BoolTensor r delta)) (columns : List (BoolTensor c delta))
    (row : Ports r packets G (2^a)) (col : Ports c packets G (2^a))
    (modes : Fin m → Mode packets G i p) (t : ℤ) (z : ZMod (2^p))
    (beta : Fin m →₀ ℕ) (br bc bm bq : ℕ) (w : Witness r c m) (d : Word p)
    (hp : 0<p) (hq : 0<bq) (hr : r≤2^br) (hc : c≤2^bc)
    (hm : m+1≤2^bm) (hrq : r<2^bq) (hb : ∀ k, beta k<2^bq) :
    let L := scalarPhysical rows columns row col modes t z
    let q := scalarVerify br bc bm bq L beta w d
    (q.result=true ↔ valid (rootTerms L) beta w=true ∧ d.val<(weight (rootTerms L) w).val) ∧
    q.steps≤witnessBudget br bc bm bq c L := by
  let L := scalarPhysical rows columns row col modes t z
  obtain ⟨hL,hM⟩ := physicalRecipe_lengths rows columns row col modes t z
  exact scalarVerify_exact br bc bm bq c hp hq hr hc hm hrq L beta hb hL hM w d

theorem physicalScalar_by_count (rows : List (BoolTensor r delta)) (columns : List (BoolTensor c delta))
    (row : Ports r packets G (2^a)) (col : Ports c packets G (2^a))
    (modes : Fin m → Mode packets G i p) (t : ℤ) (z : ZMod (2^p))
    (beta : Fin m →₀ ℕ) (br bc bm bq : ℕ)
    (hp : 0<p) (hq : 0<bq) (hr : r≤2^br) (hc : c≤2^bc)
    (hm : m+1≤2^bm) (hrq : r<2^bq) (hb : ∀ k, beta k<2^bq) :
    let L := scalarPhysical rows columns row col modes t z
    (countVerify (scalarVerifyCode br bc bm bq L beta) : ZMod (2^p)) =
      MvPolynomial.coeff beta (rootPolynomial (rootTerms L)) := by
  let L := scalarPhysical rows columns row col modes t z
  obtain ⟨hL,hM⟩ := physicalRecipe_lengths rows columns row col modes t z
  exact scalarRegister_by_count br bc bm bq c hp hq hr hc hm hrq L beta hb hL hM

end ScalarPhysical

#print axioms physicalRecipe_lengths
#print axioms physicalScalar_meter
#print axioms physicalScalar_by_count
end A1R9
