import A1R12Serialized
import A1R11PhysicalRun

/-! The non-oracular physical numeric source and the raw per-guess A1
verifier compose at the same native ring and coordinate. No supplied
Cauchy, crossing, quotient or witness-factor value appears as a
premise. The cost of symbolic/layout/template provision and the
integer accepting count itself is not a claim of this theorem. -/

namespace A1R12
open A1R10 A1R11 AOracleCoordinates AOracleMachineTime AOracleMachineTimeZero
open P1DyadicGrid AOracleSuccinct AOracleSuccinctPacket AOracleSuccinctPhysical AOracleWitness
open AOracleThreshold

theorem generatedPhysical_count_and_cost {p r c m packets G a i delta br bc ell b : ℕ}
    (q : ℕ) (hp : 0<p) {f : List (A1R10.Word p)} (he : 0<f.length) (hv : 0<ell)
    (hf : (Modulus p hp f).Monic) (hd : (Modulus p hp f).natDegree=f.length)
    (fr : r≤2^br) (fc : c≤2^bc) (fit : m+1≤2^b) (hq : 0<q) (hr : r<2^q)
    (beta : Fin m →₀ ℕ) (hb : ∀ k,beta k<2^q)
    (rt : List (BoolTensor r delta)) (ct : List (BoolTensor c delta))
    (row : Ports r packets G (2^a)) (col : Ports c packets G (2^a))
    (modes : Fin m → Mode packets G i p) (z : UVBlock f ell) (t : ℤ) (ht : t∈grid a)
    (I : Fin f.length) (J : Fin ell) :
    let T := numericOnSlots hp he hv z t (List.ofFn row.slot) (List.ofFn col.slot) (List.ofFn modes)
    let P := packedPhysical hp he hv fc rt ct row col modes (T.result.localAt hp)
      (T.result.crossAt hp) T.result.quotientAt
    let run := fun w : Code r c b × AOracleThreshold.Word p =>
      frozenUV q hp he hv (freezeInput P br b q beta) I.val J.val (rawGuess w)
    let coord := doubleCoord (Modulus p hp f) hf ell
      (⟨f.length-1-I.val,by have := I.isLt; omega⟩,⟨ell-1-J.val,by have := J.isLt; omega⟩)
    T.steps≤numericCap r c m f.length ell p a i hp ∧
    (countVerify (fun w => (run w).result) : ZMod (2^p)) =
      coord (MvPolynomial.coeff beta (rootPolynomial (rootTerms
        (physical (Modulus p hp f) rt ct row col modes t (uvRead hp f ell z))))) ∧
    ∀ w, (run w).steps≤gateBudget r m b q+
      factorBudget r c m b br bc delta c rt.length ct.length f.length ell p hp+
        productAcceptBudget (r+2) f.length ell p+2 := by
  let T := numericOnSlots hp he hv z t (List.ofFn row.slot) (List.ofFn col.slot) (List.ofFn modes)
  have H := numericGen_exact hp he hv z t ht row col modes
  dsimp only at H
  rw [← numericOnSlots_model hp he hv z t row col modes] at H
  obtain ⟨hL,hC,hQ,hcost⟩ := H
  refine ⟨hcost,?_⟩
  exact physicalFrozen_count_and_cost q hp he hv hf hd fr fc fit hq hr beta hb rt ct row col modes
    (T.result.localAt hp) (T.result.crossAt hp) T.result.quotientAt z t hQ hL hC I J

#print axioms generatedPhysical_count_and_cost
end A1R12
