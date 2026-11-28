import J6R22ActiveInterpolate
import J6R22ActiveQuotient
import J6R9RecursiveNormalizer

/-! The complete modular *one-centre* arithmetic pass: from the
literal binary probes and measured grouped responses to the finite
quotient coefficients that R9's actual recomposition consumes.
The supplied normalizer tape has its stated coefficient meaning,
and its acquisition fee is kept. The outer rational Hermite sum,
the recursive child construction, and whole input bootstrap are
not consequences of this local receipt. -/
namespace J6R22Active
open scoped Polynomial BigOperators
open Polynomial A1R10 AOracleMachineTime AOracleCoordinates
open J6ActiveRun J6ActiveSchedule J6R9Recursive

section Map
variable {R K : Type*} [CommRing R] [CommRing K] {d : ℕ}

theorem lagDecode_map (φ : R→+*K) (x y : Fin (d+1)→R)
    (I : Fin (d+1)→Fin (d+1)→R) :
    (lagDecode x y I).map φ=lagDecode (φ∘x) (φ∘y) (fun i j=>φ (I i j)) := by
  simp only [lagDecode,Polynomial.map_sum,Polynomial.map_mul,Polynomial.map_C,
    lagBasis,Polynomial.map_prod,lagFactor,Polynomial.map_sub,Polynomial.map_X,Function.comp_apply]

theorem decoded_map_with_inverses (φ : R→+*K) (x y : Fin (d+1)→R)
    (I : Fin (d+1)→Fin (d+1)→R)
    (h : ∀ i j,i≠j→(x i-x j)*I i j=1) :
    (J6ActiveInterpolation.decoded x y).map φ=J6ActiveInterpolation.decoded (φ∘x) (φ∘y) := by
  have ht (i j : Fin (d+1)) (n : i≠j) : (φ (x i)-φ (x j))*φ (I i j)=1 := by
    rw [←map_sub,←map_mul,h i j n,map_one]
  rw [←lagDecode_is_native x y I h,lagDecode_map]
  exact lagDecode_is_native _ _ _ ht

noncomputable def jetMap (φ : R→+*K) (k : ℕ) :
    AdjoinRoot ((X : R[X])^k) →+* AdjoinRoot ((X : K[X])^k) :=
  adjoinMap φ _ _ (by rw [Polynomial.map_pow,Polynomial.map_X])

theorem jetMap_mk (φ : R→+*K) (k : ℕ) (P : R[X]) :
    jetMap φ k (AdjoinRoot.mk (X^k) P)=AdjoinRoot.mk (X^k) (P.map φ) :=
  adjoinMap_mk .. 

noncomputable def pullRing {p ell : ℕ} {F G : (ZMod (2^p))[X]} (h : F=G) :
    Truncated G ell →+* Truncated F ell := boxTransport h.symm

theorem transport_pull {p ell : ℕ} {F G : (ZMod (2^p))[X]} (h : F=G)
    (x : Truncated G ell) :
    boxTransport h (pullRing h x)=x := by
  subst G
  rfl

theorem jetMap_inj {p ell : ℕ} {F G : (ZMod (2^p))[X]} (h : F=G) (k : ℕ) :
    Function.Injective (jetMap (boxTransport (ell:=ell) h) k) := by
  subst G
  intro x y hh
  induction x using AdjoinRoot.induction_on
  rename_i x
  induction y using AdjoinRoot.induction_on
  rename_i y
  simpa only [jetMap_mk,boxTransport,Polynomial.map_id] using hh
end Map

section Kernel
variable {p ell : ℕ} {fw : List (Word p)}

def fullCenterM (hp : 0<p) (he : 0<fw.length) (hv : 0<ell) {k : ℕ} (hk : 0<k)
    {n : ℕ} (node samples : Fin n→Meter (UVBlock fw ell))
    (normal : Meter (JetTape fw ell k)) : Meter (JetTape fw ell k) :=
  let val := interpPrefix hp he hv hk node samples
  let q := divideJet hp he hv hk normal.result val.result
  ⟨q.result,normal.steps+val.steps+q.steps+4⟩

theorem full_center_exact (hp : 0<p) (he : 0<fw.length) (hv : 0<ell)
    {k : ℕ} (hk : 0<k) {f : ℤ[X]} (hf : f.Monic) (hD : fw.length=f.natDegree)
    [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (hF : Modulus p hp fw=NativeProbeRing.liftPoly p f)
    {d : ℕ} (fit : d+1≤2^f.natDegree)
    (node samples : Fin (d+1)→Meter (UVBlock fw ell))
    (normal : Meter (JetTape fw ell k))
    (E : (Box f ell p)[X])
    (hE : jetMap (boxTransport hF) k (jetRead hp he normal.result)=AdjoinRoot.mk (X^k) E)
    (liveNode : ∀ i,boxTransport hF (nodeMeaning hp node i)=J6ActiveInterpolation.node p f ell _ fit i) :
    let V := fullCenterM hp he hv hk node samples normal
    jetMap (boxTransport hF) k (jetRead hp he V.result)=
      AdjoinRoot.mk (X^k) (J6ActiveNormalizer.quotientJet k E (J6ActiveInterpolation.decoded
        (J6ActiveInterpolation.node p f ell _ fit) (boxTransport hF ∘ nodeMeaning hp samples))) ∧
    V.steps≤normal.steps+interpBill node samples+interpExtra fw.length ell p k (d+1) hp+
      quotientFee fw.length ell p k hp+4 := by
  let R := Coeff hp fw ell
  let φ := boxTransport (ell:=ell) hF
  let E0 : R[X] := E.map (pullRing hF)
  let L := interpPrefix hp he hv hk node samples
  let T := J6ActiveInterpolation.decoded (nodeMeaning hp node) (nodeMeaning hp samples)
  have hE0 : E0.map φ=E := by
    ext j
    simp only [E0,Polynomial.coeff_map,φ,transport_pull]
  have he0 : jetRead hp he normal.result=AdjoinRoot.mk (X^k) E0 := by
    apply jetMap_inj hF k
    rw [hE,jetMap_mk,hE0]
  have hU (i j : Fin (d+1)) (ne : i≠j) :
      (nodeMeaning hp node i-nodeMeaning hp node j)*inverseMeaning hp he hv node i j=1 :=
    (actual_pair_inverse hp he hv hf hD hF fit i j ne
      (stored (node i).result) (stored (node j).result) (liveNode i) (liveNode j)).1
  have hL : jetRead hp he L.result=AdjoinRoot.mk (X^k) T :=
    interpPrefix_value hp he hv hk node samples hU
  have hMap : T.map φ=J6ActiveInterpolation.decoded (J6ActiveInterpolation.node p f ell _ fit)
      (φ∘nodeMeaning hp samples) := by
    rw [decoded_map_with_inverses φ _ _ (inverseMeaning hp he hv node) hU,
      show φ∘nodeMeaning hp node=J6ActiveInterpolation.node p f ell _ fit from funext liveNode]
  obtain ⟨eqQ,cQ⟩ := divideJet_exact hp he hv hk normal.result L.result E0 T he0 hL
  refine ⟨?_,?_⟩
  · change jetMap φ k (jetRead hp he (divideJet hp he hv hk normal.result L.result).result)=_
    rw [eqQ,jetMap_mk,J6ActiveNormalizer.quotientJet_map,hE0,hMap]
  · have cL : L.steps≤ interpBill node samples+interpExtra fw.length ell p k (d+1) hp :=
      interpPrefix_steps hp he hv hk node samples
    change normal.steps+L.steps+(divideJet hp he hv hk normal.result L.result).steps+4≤_
    omega
end Kernel

#print axioms decoded_map_with_inverses
#print axioms jetMap_mk
#print axioms jetMap_inj
#print axioms full_center_exact
end J6R22Active


