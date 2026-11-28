import J6R22ActiveJetFold
import J6R22ActiveLagrange

/-! Paid low-coefficient Lagrange decode on the original binary probes.
The decoder receives an executable metered loader for the already
encoded probe words and the actual grouped replies. It never
requests an inverse, a basis coefficient, or a polynomial as input.
The caller remains responsible for producing its descriptor and
providing the certified metered loader (not a free random read). -/
namespace J6R22Active
open scoped Polynomial BigOperators
open Polynomial A1R10 A1R11 A1R12 AOracleMachineTime AOracleCoordinates
open NativeProbeRing

section Machinery
variable {p ell : ℕ} {fw : List (Word p)}

def factorM (hp : 0<p) (he : 0<fw.length) (hv : 0<ell) {k : ℕ} (hk : 0<k)
    (x : UVBlock fw ell) (y : Meter (UVBlock fw ell)) : Meter (JetTape fw ell k) :=
  let recip := unitInverse hp he hv (subM hp he (stored x) (stored y.result))
  let lin := jetSub hp he hv (jetX hp he hv k) (jetConst hp he hk y.result)
  let out := jetMult hp he (jetConst hp he hk recip.result) lin.result
  ⟨out.result,y.steps+recip.steps+lin.steps+out.steps+3*tapeFee fw.length ell p k+4⟩

def factorExtra (e ell p k : ℕ) (hp : 0<p) : ℕ :=
  2*uvWidth e ell p+subCap e ell p hp+2+inverseFee e ell p hp+
    jetSubFee e ell p k hp+jetMulFee e ell p k hp+3*tapeFee e ell p k+4

theorem factorM_steps (hp : 0<p) (he : 0<fw.length) (hv : 0<ell) {k : ℕ} (hk : 0<k)
    (x : UVBlock fw ell) (y : Meter (UVBlock fw ell)) :
    (factorM hp he hv hk x y).steps≤y.steps+factorExtra fw.length ell p k hp := by
  let q := subM hp he (stored x) (stored y.result)
  let recip := unitInverse hp he hv q
  let lin := jetSub hp he hv (jetX hp he hv k) (jetConst hp he hk y.result)
  let out := jetMult hp he (jetConst hp he hk recip.result) lin.result
  have hq := subM_steps hp he (stored x) (stored y.result)
  change q.steps≤uvWidth fw.length ell p+uvWidth fw.length ell p+
    subCap fw.length ell p hp+2 at hq
  have hR : recip.steps≤q.steps+inverseFee fw.length ell p hp := unit_inverse_cost hp he hv q
  have hL : lin.steps≤_ := (jetSub_exact hp he hv (jetX hp he hv k) (jetConst hp he hk y.result)).2
  have hO : out.steps≤_ := (jetMult_exact hp he (jetConst hp he hk recip.result) lin.result).2
  change y.steps+recip.steps+lin.steps+out.steps+3*tapeFee fw.length ell p k+4≤_
  unfold factorExtra
  omega

theorem factorM_value (hp : 0<p) (he : 0<fw.length) (hv : 0<ell) {k : ℕ} (hk : 0<k)
    (x : UVBlock fw ell) (y : Meter (UVBlock fw ell)) :
    let recip := unitInverse hp he hv (subM hp he (stored x) (stored y.result))
    jetRead hp he (factorM hp he hv hk x y).result=
      AdjoinRoot.mk (X^k) (lagFactor (uvRead hp fw ell y.result)
        (uvRead hp fw ell recip.result)) := by
  let q := subM hp he (stored x) (stored y.result)
  let r := (unitInverse hp he hv q).result
  let lin := jetSub hp he hv (jetX hp he hv k) (jetConst hp he hk y.result)
  change jetRead hp he (jetMult hp he (jetConst hp he hk r) lin.result).result=_
  rw [(jetMult_exact hp he (jetConst hp he hk r) lin.result).1,jetConst_exact]
  rw [show jetRead hp he lin.result=_ from
    (jetSub_exact hp he hv (jetX hp he hv k) (jetConst hp he hk y.result)).1,
    jetX_exact hp he hv k hk,jetConst_exact,←map_sub,←map_mul]
  rfl

def probeOrder (n : ℕ) : List (Fin n) := List.ofFn (fun x=>x)

theorem probeOrder_nodup (n : ℕ) : (probeOrder n).Nodup := by
  exact List.nodup_ofFn.mpr (fun _ _ e=>e)

theorem probeOrder_mem {n : ℕ} (i : Fin n) : i∈probeOrder n := by
  exact List.mem_ofFn.mpr ⟨i,rfl⟩

def offDiagonal {n : ℕ} (i : Fin n) : List (Fin n) := (probeOrder n).erase i

theorem offDiagonal_length {n : ℕ} (i : Fin n) : (offDiagonal i).length=n-1 := by
  unfold offDiagonal
  rw [List.length_erase_of_mem (probeOrder_mem i)]
  simp only [probeOrder,List.length_ofFn]

theorem offDiagonal_toFinset {n : ℕ} (i : Fin n) :
    (offDiagonal i).toFinset=Finset.univ.erase i := by
  ext j
  rw [List.mem_toFinset,Finset.mem_erase]
  unfold offDiagonal
  rw [(probeOrder_nodup n).mem_erase_iff]
  simp [probeOrder_mem]

def basisM (hp : 0<p) (he : 0<fw.length) (hv : 0<ell) {k : ℕ} (hk : 0<k)
    {n : ℕ} (node : Fin n→Meter (UVBlock fw ell)) (i : Fin n) : Meter (JetTape fw ell k) :=
  let xi := node i
  let b := paidJetProd hp he hv hk (fun j=>factorM hp he hv hk xi.result (node j)) (offDiagonal i)
  ⟨b.result,xi.steps+b.steps+4*(n+1)^2+6⟩

def needsAt {n : ℕ} (node : Fin n→Meter (UVBlock fw ell)) (i : Fin n) : ℕ :=
  (node i).steps+bill node (offDiagonal i)

def basisExtra (e ell p k n : ℕ) (hp : 0<p) : ℕ :=
  tapeFee e ell p k+(n-1)*(factorExtra e ell p k hp+jetMulFee e ell p k hp+2)+4*(n+1)^2+6

theorem basisM_steps (hp : 0<p) (he : 0<fw.length) (hv : 0<ell) {k : ℕ} (hk : 0<k)
    {n : ℕ} (node : Fin n→Meter (UVBlock fw ell)) (i : Fin n) :
    (basisM hp he hv hk node i).steps≤needsAt node i+basisExtra fw.length ell p k n hp := by
  let fac := fun j=>factorM hp he hv hk (node i).result (node j)
  have h := bill_mono fac node (offDiagonal i) (factorExtra fw.length ell p k hp)
    (fun j _=>factorM_steps hp he hv hk (node i).result (node j))
  have h' := (paidJetProd_exact hp he hv hk fac (offDiagonal i)).2
  change (node i).steps+(paidJetProd hp he hv hk fac (offDiagonal i)).steps+
    4*(n+1)^2+6≤_
  unfold needsAt basisExtra
  rw [offDiagonal_length] at h h'
  rw [Nat.add_assoc (factorExtra fw.length ell p k hp),Nat.mul_add]
  omega

noncomputable def nodeMeaning (hp : 0<p) {n : ℕ}
    (node : Fin n→Meter (UVBlock fw ell)) (i : Fin n) : Coeff hp fw ell :=
  uvRead hp fw ell (node i).result

noncomputable def inverseMeaning (hp : 0<p) (he : 0<fw.length) (hv : 0<ell)
    {n : ℕ} (node : Fin n→Meter (UVBlock fw ell)) (i j : Fin n) : Coeff hp fw ell :=
  uvRead hp fw ell (unitInverse hp he hv (subM hp he (stored (node i).result) (stored (node j).result))).result

theorem basisM_value (hp : 0<p) (he : 0<fw.length) (hv : 0<ell) {k : ℕ} (hk : 0<k)
    {d : ℕ} (node : Fin (d+1)→Meter (UVBlock fw ell)) (i : Fin (d+1)) :
    jetRead hp he (basisM hp he hv hk node i).result=
      AdjoinRoot.mk (X^k) (lagBasis (nodeMeaning hp node) (inverseMeaning hp he hv node) i) := by
  let F (j : Fin (d+1)) := factorM hp he hv hk (node i).result (node j)
  change jetRead hp he (paidJetProd hp he hv hk F (offDiagonal i)).result=_
  rw [(paidJetProd_exact hp he hv hk F (offDiagonal i)).1]
  rw [←List.prod_toFinset (l:=offDiagonal i) _ ((probeOrder_nodup (d+1)).erase i),offDiagonal_toFinset,lagBasis,map_prod]
  apply Finset.prod_congr rfl
  intro j _
  exact factorM_value hp he hv hk (node i).result (node j)

def interpTerm (hp : 0<p) (he : 0<fw.length) (hv : 0<ell) {k : ℕ} (hk : 0<k)
    {n : ℕ} (node sample : Fin n→Meter (UVBlock fw ell)) (i : Fin n) : Meter (JetTape fw ell k) :=
  let b := basisM hp he hv hk node i
  let y := sample i
  let out := jetMult hp he (jetConst hp he hk y.result) b.result
  ⟨out.result,b.steps+y.steps+out.steps+tapeFee fw.length ell p k+4⟩

def interpPrefix (hp : 0<p) (he : 0<fw.length) (hv : 0<ell) {k : ℕ} (hk : 0<k)
    {n : ℕ} (node sample : Fin n→Meter (UVBlock fw ell)) : Meter (JetTape fw ell k) :=
  let v := paidJetSum hp he (interpTerm hp he hv hk node sample) (probeOrder n)
  ⟨v.result,v.steps+4*(n+1)^2+4⟩

def interpBill {n : ℕ} (node sample : Fin n→Meter (UVBlock fw ell)) : ℕ :=
  ((probeOrder n).map (fun i=>needsAt node i+(sample i).steps)).sum

def interpExtra (e ell p k n : ℕ) (hp : 0<p) : ℕ :=
  n*(basisExtra e ell p k n hp+jetMulFee e ell p k hp+tapeFee e ell p k+4+
      (jetAddFee e ell p k hp+2))+tapeFee e ell p k+4*(n+1)^2+4

theorem interpPrefix_steps (hp : 0<p) (he : 0<fw.length) (hv : 0<ell) {k : ℕ} (hk : 0<k)
    {n : ℕ} (node sample : Fin n→Meter (UVBlock fw ell)) :
    (interpPrefix hp he hv hk node sample).steps≤ interpBill node sample+
      interpExtra fw.length ell p k n hp := by
  let T := interpTerm hp he hv hk node sample
  let A := probeOrder n
  let C (i : Fin n) : Meter Unit := ⟨(),needsAt node i+(sample i).steps⟩
  let E := basisExtra fw.length ell p k n hp+jetMulFee fw.length ell p k hp+
    tapeFee fw.length ell p k+4
  have h := bill_mono T C A E (fun i _=>by
    have hB := basisM_steps hp he hv hk node i
    have hM := (jetMult_exact hp he (jetConst hp he hk (sample i).result)
      (basisM hp he hv hk node i).result).2
    change (basisM hp he hv hk node i).steps+(sample i).steps+
      (jetMult hp he (jetConst hp he hk (sample i).result)
        (basisM hp he hv hk node i).result).steps+tapeFee fw.length ell p k+4≤_
    change _≤needsAt node i+(sample i).steps+E
    unfold E
    omega)
  have h' := (paidJetSum_exact hp he T A).2
  have hN : A.length=n := List.length_ofFn
  change (paidJetSum hp he T A).steps+4*(n+1)^2+4≤bill C A+_
  rw [hN] at h h'
  change _≤bill C A+(n*(E+(jetAddFee fw.length ell p k hp+2))+
    tapeFee fw.length ell p k+4*(n+1)^2+4)
  rw [Nat.mul_add]
  omega

theorem interpPrefix_value (hp : 0<p) (he : 0<fw.length) (hv : 0<ell) {k : ℕ} (hk : 0<k)
    {d : ℕ} (node sample : Fin (d+1)→Meter (UVBlock fw ell))
    (h : ∀ i j,i≠j→(nodeMeaning hp node i-nodeMeaning hp node j)*inverseMeaning hp he hv node i j=1) :
    jetRead hp he (interpPrefix hp he hv hk node sample).result=
      AdjoinRoot.mk (X^k) (J6ActiveInterpolation.decoded (nodeMeaning hp node)
        (nodeMeaning hp sample)) := by
  rw [←lagDecode_is_native _ _ (inverseMeaning hp he hv node) h]
  change jetRead hp he (paidJetSum hp he (interpTerm hp he hv hk node sample)
      (probeOrder (d+1))).result=_
  rw [(paidJetSum_exact hp he _ _).1,probeOrder,List.map_ofFn,List.sum_ofFn,lagDecode,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  change jetRead hp he (jetMult hp he (jetConst hp he hk (sample i).result)
    (basisM hp he hv hk node i).result).result=_
  rw [(jetMult_exact hp he _ _).1,jetConst_exact,basisM_value,←map_mul]
  rfl
end Machinery

theorem actual_interpolation_prefix {p ell k : ℕ} (hp : 0<p) {fw : List (Word p)}
    (he : 0<fw.length) (hv : 0<ell) (hk : 0<k) {f : ℤ[X]} (hf : f.Monic) (hD : fw.length=f.natDegree)
    [Fact (Irreducible (residuePoly f))] (hF : Modulus p hp fw=liftPoly p f)
    {d : ℕ} (fit : d+1≤2^f.natDegree)
    (node sample : Fin (d+1)→Meter (UVBlock fw ell))
    (literal : ∀ i,boxTransport hF (nodeMeaning hp node i)=J6ActiveInterpolation.node p f ell (d+1) fit i) :
    let V := interpPrefix hp he hv hk node sample
    jetRead hp he V.result=AdjoinRoot.mk (X^k)
      (J6ActiveInterpolation.decoded (nodeMeaning hp node) (nodeMeaning hp sample)) ∧
    V.steps≤ interpBill node sample+interpExtra fw.length ell p k (d+1) hp := by
  refine ⟨interpPrefix_value hp he hv hk node sample ?_,interpPrefix_steps hp he hv hk node sample⟩
  intro i j ne
  exact (actual_pair_inverse hp he hv hf hD hF fit i j ne
    (stored (node i).result) (stored (node j).result) (literal i) (literal j)).1

#print axioms factorM_steps
#print axioms factorM_value
#print axioms basisM_steps
#print axioms basisM_value
#print axioms interpPrefix_steps
#print axioms interpPrefix_value
#print axioms actual_interpolation_prefix
end J6R22Active


