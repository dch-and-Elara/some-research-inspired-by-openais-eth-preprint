
import J6R14ZeroModeProbe
import J6R22ActiveCoeff
import J6R22ActiveBinary

/-! The prescribed nonzero outer probe menu need not be the native
prefix used inside recursive calls. Use its actual metered word reads,
the same U/V representation, and the R22 addition, multiplication and
unit inverse machines, specializing the finite jet to order one. -/
namespace J6R26StablePreparedRoot
open scoped Polynomial BigOperators
open Polynomial J6R22Active NativeProbeRing A1R10 A1R11 A1R12
open AOracleMachineTime AOracleCoordinates J6R9Recursive J6R14ZeroMode
set_option maxHeartbeats 6500000
set_option maxRecDepth 1500

section Interpolation
variable {f : ℤ[X]} {ell p d : ℕ} {fw : List (Word p)}

def readPrescribed (hp : 0<p) (hv : 0<ell)
    (words : Fin (d+1)→Meter {x : List Bool // x.length=fw.length}) (j : Fin (d+1)) :
    Meter (UVBlock fw ell) :=
  let w := words j
  let e := encodeProbe hp hv w.result
  ⟨e.result,w.steps+e.steps+2⟩

theorem read_prescribed_exact (hp : 0<p) (hv : 0<ell) (W : Prescribed f d)
    (hMod : Modulus p hp fw = liftPoly p f)
    (words : Fin (d+1)→Meter {x : List Bool // x.length=fw.length})
    (raw : ∀ j,(words j).result.val=List.ofFn (W.word j))
    (j : Fin (d+1)) :
    boxTransport hMod (nodeMeaning hp (readPrescribed hp hv words) j)=prescribedNode W p ell j ∧
      (readPrescribed hp hv words j).steps=(words j).steps+
        (fw.length*(p+6)+uvWidth fw.length ell p+2)+2 := by
  refine ⟨encodeProbe_is_literal hp hv hMod (words j).result (W.word j) (raw j),?_⟩
  change (words j).steps+(encodeProbe hp hv (words j).result).steps+2=_
  rw [encodeProbe_cost]

theorem prescribed_inverse_at (hp : 0<p) (he : 0<fw.length) (hv : 0<ell)
    (hf : f.Monic) (hF : 0<f.natDegree) (hD : fw.length=f.natDegree)
    [Fact (Irreducible (residuePoly f))] (hMod : Modulus p hp fw=liftPoly p f)
    (W : Prescribed f d) (node : Fin (d+1)→Meter (UVBlock fw ell))
    (literal : ∀ j,boxTransport hMod (nodeMeaning hp node j)=prescribedNode W p ell j)
    (i j : Fin (d+1)) (ne : i≠j) :
    (nodeMeaning hp node i-nodeMeaning hp node j)*inverseMeaning hp he hv node i j=1 := by
  let x := stored (node i).result
  let y := stored (node j).result
  let c := probe p f (W.word i)-probe p f (W.word j)
  have nonzero : residueMap p hp f c≠0 := by
    change residueMap p hp f (probe p f (W.word i) - probe p f (W.word j)) ≠ 0
    rw [map_sub,sub_ne_zero]
    intro E
    exact ne (W.distinct (binary_residues_injective p hp f hf hF E))
  have read : boxTransport hMod (uvRead hp fw ell (subM hp he x y).result)=
      J6ActiveInterpolation.scalarIn p f ell c := by
    rw [subM_value,map_sub]
    change boxTransport hMod (nodeMeaning hp node i)-boxTransport hMod (nodeMeaning hp node j)=_
    rw [literal i,literal j]
    exact (map_sub _ _ _).symm
  obtain ⟨result,_⟩ := inverse_actual_scalar hp he hv hf hMod hD (subM hp he x y) c nonzero read
  apply boxTransport_injective hMod
  change boxTransport hMod ((uvRead hp fw ell x.result-uvRead hp fw ell y.result)*
    uvRead hp fw ell (unitInverse hp he hv (subM hp he x y)).result)=boxTransport hMod 1
  rw [map_mul,map_one,←subM_value hp he x y,read]
  exact result

def interpolateAt0 (hp : 0<p) (he : 0<fw.length) (hv : 0<ell)
    (node sample : Fin (d+1)→Meter (UVBlock fw ell)) : Meter (UVBlock fw ell) :=
  let J := interpPrefix hp he hv (k:=1) (by decide) node sample
  let c := jetCoeffM hp he J.result 0
  ⟨c.result,J.steps+c.steps+3⟩

theorem prescribed_interpolate_at_zero (hp : 0<p) (he : 0<fw.length) (hv : 0<ell)
    (hf : f.Monic) (hF : 0<f.natDegree) (hD : fw.length=f.natDegree)
    [Fact (Irreducible (residuePoly f))] (hMod : Modulus p hp fw=liftPoly p f)
    (W : Prescribed f d) (node sample : Fin (d+1)→Meter (UVBlock fw ell))
    (P : (Box f ell p)[X]) (bound : P.natDegree≤d)
    (literal : ∀ j,boxTransport hMod (nodeMeaning hp node j)=prescribedNode W p ell j)
    (values : ∀ j,boxTransport hMod (nodeMeaning hp sample j)=P.eval (prescribedNode W p ell j)) :
    let out := interpolateAt0 hp he hv node sample
    boxTransport hMod (uvRead hp fw ell out.result)=P.eval 0 ∧
      out.steps≤ interpBill node sample+interpExtra fw.length ell p 1 (d+1) hp+
        jetCoeffFee fw.length ell p 1+3 := by
  let φ := boxTransport (ell:=ell) hMod
  let J := interpPrefix hp he hv (k:=1) (by decide) node sample
  let c := jetCoeffM hp he J.result 0
  have inv (i j : Fin (d+1)) (ne : i≠j) :=
    prescribed_inverse_at hp he hv hf hF hD hMod W node literal i j ne
  have E : (J6ActiveInterpolation.decoded (φ∘nodeMeaning hp node) (φ∘nodeMeaning hp sample))=P := by
    rw [show φ∘nodeMeaning hp node=prescribedNode W p ell from funext literal,
      show φ∘nodeMeaning hp sample=(fun j=>P.eval (prescribedNode W p ell j)) from funext values]
    exact J6ActiveInterpolation.decoded_exact _ _ bound (prescribed_units W p ell hp hf hF)
  have eq : jetMap φ 1 (jetRead hp he J.result)=AdjoinRoot.mk (X^1) P := by
    rw [show jetRead hp he J.result=_ from interpPrefix_value hp he hv (by decide) node sample inv,
      jetMap_mk,decoded_map_with_inverses φ _ _ (inverseMeaning hp he hv node) inv,E]
  obtain ⟨value,cost⟩ := jetCoeffM_exact hp he φ J.result 0 (by decide) P eq
  have jcost := interpPrefix_steps hp he hv (k:=1) (by decide) node sample
  refine ⟨value.trans (Polynomial.coeff_zero_eq_eval_zero P),?_⟩
  change J.steps+c.steps+3≤_
  exact Nat.add_le_add_right (Nat.add_le_add jcost cost) _

end Interpolation
#print axioms read_prescribed_exact
#print axioms prescribed_inverse_at
#print axioms prescribed_interpolate_at_zero
end J6R26StablePreparedRoot
