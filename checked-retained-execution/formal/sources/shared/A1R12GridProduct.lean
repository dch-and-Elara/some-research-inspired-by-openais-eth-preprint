import A1R12Factors

/-! All source grid products are obtained by bounded, ordered scans of
the exact dyadic grid. The cost includes enumerating and filtering
the signed address words, not just multiplying precomputed factors. -/

open scoped BigOperators
namespace A1R12
open A1R10 A1R11 AOracleMachineTime AOracleCoordinates
open P1DyadicGrid AOracleSuccinctPhysical AOracleSuccinctNative AOracleSuccinctKernel

def omitGrid (a : ℕ) (x y : ℤ) : List ℤ :=
  (gridList a).filter (fun q => q != x && q != y)

theorem omitGrid_finset (a : ℕ) (x y : ℤ) :
    (omitGrid a x y).toFinset=((grid a).erase x).erase y := by
  rw [omitGrid,List.toFinset_filter,gridList_toFinset]
  ext k
  simp [and_assoc,and_comm,and_left_comm]

theorem omitGrid_bound (a : ℕ) (x y : ℤ) :
    (omitGrid a x y).length≤2^(a+1) := by
  unfold omitGrid
  exact (List.length_filter_le _ _).trans_eq (gridList_length a)

theorem omitGrid_mem {a : ℕ} {t k q : ℤ} (h : q∈omitGrid a t k) : q∈grid a := by
  unfold omitGrid at h
  exact (gridList_mem a q).mp (List.mem_filter.mp h).1

def gridCap (a : ℕ) : ℕ := (2^(a+1)+1)*(16*(a+3)^2+8)

def gridFold {p ell : ℕ} (hp : 0<p) {f : List (A1R10.Word p)}
    (he : 0<f.length) (hv : 0<ell) (a : ℕ) (t k : ℤ) (g : ℤ → Meter (UVBlock f ell)) :
    Meter (UVBlock f ell) :=
  padCost (foldM hp he hv g (omitGrid a t k)) (gridCap a)

def gridFoldCap (e ell p a c : ℕ) : ℕ :=
  uvWidth e ell p+2^(a+1)*(c+mulCap e ell p+2)+gridCap a

theorem gridFold_exact {p ell : ℕ} (hp : 0<p) {f : List (A1R10.Word p)}
    (he : 0<f.length) (hv : 0<ell) (a : ℕ) (t k : ℤ) (g : ℤ → Meter (UVBlock f ell))
    (F : ℤ → Truncated (Modulus p hp f) ell) (cap : ℕ)
    (H : ∀ q∈grid a,uvRead hp f ell (g q).result=F q ∧ (g q).steps≤cap) :
    uvRead hp f ell (gridFold hp he hv a t k g).result=∏ q∈((grid a).erase t).erase k,F q ∧
    (gridFold hp he hv a t k g).steps≤gridFoldCap f.length ell p a cap := by
  let s := omitGrid a t k
  obtain ⟨heq,hc⟩ := foldM_exact hp he hv s g F cap (fun q hq => H q (omitGrid_mem hq))
  have hnd : s.Nodup := (gridList_nodup a).filter _
  have Hs := List.prod_toFinset F hnd
  change (omitGrid a t k).toFinset.prod F = _ at Hs
  rw [omitGrid_finset] at Hs
  refine ⟨heq.trans Hs.symm,?_⟩
  change (foldM hp he hv g s).steps+gridCap a≤_
  have hs := Nat.mul_le_mul_right (cap+mulCap f.length ell p+2) (omitGrid_bound a t k)
  change s.length*(cap+mulCap f.length ell p+2)≤_ at hs
  unfold gridFoldCap
  omega

theorem erase_twice (a : ℕ) (t : ℤ) : ((grid a).erase t).erase t=(grid a).erase t := by
  ext k
  simp

def oddProdM {p ell : ℕ} (hp : 0<p) {f : List (A1R10.Word p)}
    (he : 0<f.length) (hv : 0<ell) (a : ℕ) (t : ℤ) : Meter (UVBlock f ell) :=
  gridFold hp he hv a t t (fun q => oddM hp he hv (a+1) (t-q))

def oddProdCap (e ell p a : ℕ) : ℕ :=
  gridFoldCap e ell p a (uvWidth e ell p+dyadicCap p (a+1))

theorem oddProdM_exact {p ell : ℕ} (hp : 0<p) {f : List (A1R10.Word p)}
    (he : 0<f.length) (hv : 0<ell) (a : ℕ) (t : ℤ) (ht : t∈grid a) :
    uvRead hp f ell (oddProdM hp he hv a t).result=(oddPartsAt a t:Truncated (Modulus p hp f) ell) ∧
    (oddProdM hp he hv a t).steps≤oddProdCap f.length ell p a := by
  unfold oddProdM oddProdCap
  obtain ⟨h,hc⟩ := gridFold_exact hp he hv a t t _
    (fun q => (oddWord (t-q):Truncated (Modulus p hp f) ell)) _ (fun q hq =>
      oddM_exact hp he hv (a+1) _ (diff_width ht hq))
  rw [erase_twice] at h
  simpa only [oddPartsAt,Int.cast_prod] using ⟨h,hc⟩

theorem oddDerivative_eq_parts (a : ℕ) : oddDerivative a=oddPartsAt a 0 := rfl

def normProdM {p ell : ℕ} (hp : 0<p) {f : List (A1R10.Word p)}
    (he : 0<f.length) (hv : 0<ell) (z : UVBlock f ell) (a : ℕ) (t k : ℤ) :
    Meter (UVBlock f ell) :=
  gridFold hp he hv a t k (fun q => shiftM hp he hv z a (a+1) (t-q))

def normProdCap (e ell p a : ℕ) (hp : 0<p) : ℕ :=
  gridFoldCap e ell p a (shiftCap e ell p a (a+1) hp)

theorem normProdM_exact {p ell : ℕ} (hp : 0<p) {f : List (A1R10.Word p)}
    (he : 0<f.length) (hv : 0<ell) (z : UVBlock f ell) (a : ℕ) (t k : ℤ) (ht : t∈grid a) :
    uvRead hp f ell (normProdM hp he hv z a t k).result=
      ∏ q∈((grid a).erase t).erase k,normFactor a t q (uvRead hp f ell z) ∧
    (normProdM hp he hv z a t k).steps≤normProdCap f.length ell p a hp := by
  exact gridFold_exact hp he hv a t k _ _ _ (fun q hq =>
    shiftM_exact hp he hv z a (a+1) _ (diff_width ht hq))

def ratioProdM {p ell : ℕ} (hp : 0<p) {f : List (A1R10.Word p)}
    (he : 0<f.length) (hv : 0<ell) (z : UVBlock f ell) (a : ℕ) (t : ℤ) :
    Meter (UVBlock f ell) :=
  gridFold hp he hv a t t (fun q => ratioM hp he hv z a (a+1) (t-q))

def ratioProdCap (e ell p a : ℕ) (hp : 0<p) : ℕ :=
  gridFoldCap e ell p a (ratioCap e ell p a (a+1) hp)

theorem ratioProdM_exact {p ell : ℕ} (hp : 0<p) {f : List (A1R10.Word p)}
    (he : 0<f.length) (hv : 0<ell) (z : UVBlock f ell) (a : ℕ) (t : ℤ) (ht : t∈grid a) :
    uvRead hp f ell (ratioProdM hp he hv z a t).result=
      ∏ q∈(grid a).erase t, (1+(2:Truncated (Modulus p hp f) ell)^(a+1-padicValInt 2 (t-q))*
        uvRead hp f ell z * oddInverse p (oddWord (t-q):Truncated (Modulus p hp f) ell)) ∧
    (ratioProdM hp he hv z a t).steps≤ratioProdCap f.length ell p a hp := by
  unfold ratioProdM ratioProdCap
  rw [← erase_twice a t]
  exact gridFold_exact hp he hv a t t _ _ _ (fun q hq =>
    ratioM_exact hp he hv z a (a+1) _ (diff_width ht hq))

#print axioms omitGrid_finset
#print axioms gridFold_exact
#print axioms oddProdM_exact
#print axioms normProdM_exact
#print axioms ratioProdM_exact
end A1R12

