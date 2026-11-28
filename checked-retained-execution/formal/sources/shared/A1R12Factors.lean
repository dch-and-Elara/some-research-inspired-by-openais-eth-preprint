import A1R12Combine

/-! The three source leaves: signed odd part, normalized shifted
factor, and normalized crossing ratio factor. Every numeric output
comes from the exact geometry arguments and the supplied probe value. -/

namespace A1R12
open A1R10 A1R11 AOracleMachineTime AOracleCoordinates
open P1DyadicGrid AOracleSuccinctNative AOracleSuccinctKernel

def scaleM {p ell : ℕ} (hp : 0<p) {f : List (A1R10.Word p)}
    (he : 0<f.length) (hv : 0<ell) (z : UVBlock f ell) (k : ℕ) : Meter (UVBlock f ell) :=
  mulM hp (twoM hp he hv k) (Meter.pure z)

def scaleCap (e ell p k : ℕ) : ℕ := uvWidth e ell p+4*(p+k+1)+mulCap e ell p+2

@[simp] theorem scaleM_read {p ell : ℕ} (hp : 0<p) {f : List (A1R10.Word p)}
    (he : 0<f.length) (hv : 0<ell) (z : UVBlock f ell) (k : ℕ) :
    uvRead hp f ell (scaleM hp he hv z k).result=(2:Truncated (Modulus p hp f) ell)^k*uvRead hp f ell z := by
  simp [scaleM,Meter.pure]

theorem scaleM_cost {p ell : ℕ} (hp : 0<p) {f : List (A1R10.Word p)}
    (he : 0<f.length) (hv : 0<ell) (z : UVBlock f ell) {k K : ℕ} (hk : k≤K) :
    (scaleM hp he hv z k).steps≤scaleCap f.length ell p K := by
  have he' := mulM_cost hp (twoM hp he hv k) (Meter.pure z)
  change (scaleM hp he hv z k).steps≤scaleCap f.length ell p k at he'
  exact he'.trans (by unfold scaleCap; omega)

def oddM {p ell : ℕ} (hp : 0<p) {f : List (A1R10.Word p)}
    (he : 0<f.length) (hv : 0<ell) (w : ℕ) (u : ℤ) : Meter (UVBlock f ell) :=
  let d := dyadicInt hp w u
  padCost (scalarM hp he hv d.result.2) d.steps

theorem oddM_exact {p ell : ℕ} (hp : 0<p) {f : List (A1R10.Word p)}
    (he : 0<f.length) (hv : 0<ell) (w : ℕ) (u : ℤ) (h : u.natAbs<2^w) :
    uvRead hp f ell (oddM hp he hv w u).result=(oddWord u:Truncated (Modulus p hp f) ell) ∧
    (oddM hp he hv w u).steps≤uvWidth f.length ell p+dyadicCap p w := by
  obtain ⟨_,hv',hc⟩ := dyadicInt_exact hp w u h
  refine ⟨?_,?_⟩
  · change uvRead hp f ell (scalarM hp he hv (dyadicInt hp w u).result.2).result=_
    rw [scalarM_read,hv',map_intCast]
  · exact Nat.add_le_add_left hc _

def shiftM {p ell : ℕ} (hp : 0<p) {f : List (A1R10.Word p)}
    (he : 0<f.length) (hv : 0<ell) (z : UVBlock f ell) (a w : ℕ) (u : ℤ) : Meter (UVBlock f ell) :=
  let d := dyadicInt hp w u
  let x := scalarM hp he hv d.result.2
  let y := scaleM hp he hv z (a+1-d.result.1)
  padCost (addM hp x y) (d.steps+4*(a+w+4))

def shiftCap (e ell p a w : ℕ) (hp : 0<p) : ℕ :=
  uvWidth e ell p+scaleCap e ell p (a+1)+addCap e ell p hp+2+
    dyadicCap p w+4*(a+w+4)

theorem shiftM_exact {p ell : ℕ} (hp : 0<p) {f : List (A1R10.Word p)}
    (he : 0<f.length) (hv : 0<ell) (z : UVBlock f ell) (a w : ℕ) (u : ℤ) (h : u.natAbs<2^w) :
    uvRead hp f ell (shiftM hp he hv z a w u).result=
      shiftWord (oddWord u) (a+1-padicValInt 2 u) (uvRead hp f ell z) ∧
    (shiftM hp he hv z a w u).steps≤shiftCap f.length ell p a w hp := by
  let d := dyadicInt hp w u
  obtain ⟨he',hv',hc⟩ := dyadicInt_exact hp w u h
  let x := scalarM hp he hv d.result.2
  let y := scaleM hp he hv z (a+1-d.result.1)
  have hy := scaleM_cost hp he hv z (Nat.sub_le (a+1) d.result.1)
  have ha := addM_cost hp x y
  refine ⟨?_,?_⟩
  · change uvRead hp f ell (addM hp
      (scalarM hp he hv (dyadicInt hp w u).result.2)
      (scaleM hp he hv z (a+1-(dyadicInt hp w u).result.1))).result=_
    rw [addM_read,scalarM_read,scaleM_read,hv',he',map_intCast]
    rfl
  · change (addM hp x y).steps+(d.steps+4*(a+w+4))≤_
    change y.steps≤_ at hy
    change (addM hp x y).steps≤uvWidth f.length ell p+y.steps+addCap f.length ell p hp+2 at ha
    change d.steps≤_ at hc
    unfold shiftCap
    omega

def ratioM {p ell : ℕ} (hp : 0<p) {f : List (A1R10.Word p)}
    (he : 0<f.length) (hv : 0<ell) (z : UVBlock f ell) (a w : ℕ) (u : ℤ) : Meter (UVBlock f ell) :=
  let d := dyadicInt hp w u
  let v := invM hp he hv (scalarM hp he hv d.result.2)
  let y := scaleM hp he hv z (a+1-d.result.1)
  padCost (addM hp (oneM hp he hv) (mulM hp y v)) (d.steps+4*(a+w+4))

def ratioCap (e ell p a w : ℕ) (hp : 0<p) : ℕ :=
  2*uvWidth e ell p+scaleCap e ell p (a+1)+oddCap e ell p hp+
   mulCap e ell p+addCap e ell p hp+6+dyadicCap p w+4*(a+w+4)

theorem ratioM_exact {p ell : ℕ} (hp : 0<p) {f : List (A1R10.Word p)}
    (he : 0<f.length) (hv : 0<ell) (z : UVBlock f ell) (a w : ℕ) (u : ℤ) (h : u.natAbs<2^w) :
    uvRead hp f ell (ratioM hp he hv z a w u).result=
      1+(2:Truncated (Modulus p hp f) ell)^(a+1-padicValInt 2 u)*
       uvRead hp f ell z * oddInverse p (oddWord u:Truncated (Modulus p hp f) ell) ∧
    (ratioM hp he hv z a w u).steps≤ratioCap f.length ell p a w hp := by
  let d := dyadicInt hp w u
  obtain ⟨he',hv',hc⟩ := dyadicInt_exact hp w u h
  let x := scalarM hp he hv d.result.2
  let v := invM hp he hv x
  let y := scaleM hp he hv z (a+1-d.result.1)
  let m := mulM hp y v
  let n := oneM hp he hv
  have hy := scaleM_cost hp he hv z (Nat.sub_le (a+1) d.result.1)
  have hv'c := invM_cost hp he hv x
  have hm := mulM_cost hp y v
  have hn := addM_cost hp n m
  refine ⟨?_,?_⟩
  · change uvRead hp f ell (addM hp (oneM hp he hv)
      (mulM hp (scaleM hp he hv z (a+1-(dyadicInt hp w u).result.1))
        (invM hp he hv (scalarM hp he hv (dyadicInt hp w u).result.2)))).result=_
    rw [addM_read,oneM_read,mulM_read,scaleM_read,invM_read,scalarM_read,hv',he',map_intCast]
  · change (addM hp n m).steps+(d.steps+4*(a+w+4))≤_
    change y.steps≤_ at hy
    change v.steps≤uvWidth f.length ell p+oddCap f.length ell p hp+2 at hv'c
    change m.steps≤_ at hm
    change (addM hp n m).steps≤uvWidth f.length ell p+m.steps+addCap f.length ell p hp+2 at hn
    change d.steps≤_ at hc
    unfold ratioCap
    omega

#print axioms scaleM_read
#print axioms oddM_exact
#print axioms shiftM_exact
#print axioms ratioM_exact
end A1R12


