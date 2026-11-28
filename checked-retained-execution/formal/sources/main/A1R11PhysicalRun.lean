import A1R11Physical
import A1R11Frozen

/-! End-to-end conditional physical instance. The ready compiled tape
contains a kernel cell and crossing cell wherever specified by the
physical interface. Nothing in these statements computes the accepting
count from its finite verifier in polynomial time. -/

namespace A1R11
open A1R10 AOracleCoordinates AOracleMachineTime AOracleSuccinct AOracleWitness AOracleThreshold
open AOracleSuccinctPacket AOracleSuccinctKernel AOracleSuccinctPhysical AOracleMachineTimeZero

theorem physicalFrozen_count_and_cost {p r c m packets G a i delta br bc ell b : ℕ} (q : ℕ) (hp : 0<p)
    {f : List (A1R10.Word p)} (he : 0<f.length) (hv : 0<ell)
    (hf : (Modulus p hp f).Monic) (hd : (Modulus p hp f).natDegree=f.length)
    (fr : r≤2^br) (fc : c≤2^bc) (fit : m+1≤2^b) (hq : 0<q) (hr : r<2^q)
    (beta : Fin m →₀ ℕ) (hb : ∀ k,beta k<2^q)
    (rt : List (BoolTensor r delta)) (ct : List (BoolTensor c delta))
    (row : Ports r packets G (2^a)) (col : Ports c packets G (2^a))
    (modes : Fin m → Mode packets G i p)
    (lk : Fin r → Fin c → UVBlock f ell) (cr : Fin r → Fin m → UVBlock f ell)
    (slotQuot : Fin c → A1R10.Word p) (z : UVBlock f ell) (t : ℤ)
    (hslot : ∀ j,wordRead (slotQuot j)=(quotient i (col.slot j).val:ZMod (2^p)))
    (hlk : ∀ j k,uvRead hp f ell (lk j k)=modular p a t
          (((col.slot k).val:ℤ)-((row.slot j).val:ℤ)) (uvRead hp f ell z))
    (hcr : ∀ j k,uvRead hp f ell (cr j k)=crossCell p a i (modes k).exponent.val t
          (row.slot j).val (modes k).tile.val (uvRead hp f ell z))
    (I : Fin f.length) (J : Fin ell) :
    let P := packedPhysical hp he hv fc rt ct row col modes lk cr slotQuot
    let run := fun w : Code r c b × AOracleThreshold.Word p =>
      frozenUV q hp he hv (freezeInput P br b q beta) I.val J.val (rawGuess w)
    let coord := doubleCoord (Modulus p hp f) hf ell
      (⟨f.length-1-I.val,by have := I.isLt; omega⟩,⟨ell-1-J.val,by have := J.isLt; omega⟩)
    (countVerify (fun w => (run w).result) : ZMod (2^p)) =
      coord (MvPolynomial.coeff beta (rootPolynomial (rootTerms
        (physical (Modulus p hp f) rt ct row col modes t (uvRead hp f ell z))))) ∧
    ∀ w, (run w).steps≤gateBudget r m b q+
      factorBudget r c m b br bc delta c rt.length ct.length f.length ell p hp+
        productAcceptBudget (r+2) f.length ell p+2 := by
  let P := packedPhysical hp he hv fc rt ct row col modes lk cr slotQuot
  have hP := packedPhysical_eq hp he hv fc rt ct row col modes lk cr slotQuot z t hslot hlk hcr
  obtain ⟨hL,hM⟩ := packedPhysical_width hp he hv fc rt ct row col modes lk cr slotQuot
  have H := frozenUV_count_and_cost q hp he hv hf hd P br beta hq fr fc fit hr hb c hL hM I J
  change P.denote hp=_ at hP
  rw [← hP]
  exact H

#print axioms physicalFrozen_count_and_cost
end A1R11
