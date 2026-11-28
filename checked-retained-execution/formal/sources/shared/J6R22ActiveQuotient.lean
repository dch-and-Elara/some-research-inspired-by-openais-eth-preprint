import J6R22ActiveJet
import J6ActiveHermite

/-! Metered Horner evaluation of the actual Appendix D quotient jet.
Performed at receiving precision and in the prescribed Taylor order:
the algorithm never builds the high-degree geometric inverse. Input
tapes must contain the indicated normalizer and interpolated prefix;
this does not meter their production or the rational recomposition. -/
namespace J6R22Active
open scoped Polynomial BigOperators
open Polynomial A1R10 AOracleMachineTime

variable {p ell : ℕ} {fw : List (Word p)}

def jetGeom (hp : 0<p) (he : 0<fw.length) (hv : 0<ell)
    {k : ℕ} (hk : 0<k) (x : JetTape fw ell k) : ℕ→Meter (JetTape fw ell k)
  | 0 => ⟨jetZero hp he k,k*(jetEntryWidth fw.length ell p+1)+2⟩
  | n+1 =>
    let y := jetGeom hp he hv hk x n
    let z := jetMult hp he x y.result
    let s := jetAdd hp he (jetOne hp he hv k hk) z.result
    ⟨s.result,y.steps+z.steps+s.steps+3*k*(jetEntryWidth fw.length ell p+1)+4⟩

def jetGeomBase (e ell p k : ℕ) : ℕ := k*(jetEntryWidth e ell p+1)+2
def jetGeomStride (e ell p k : ℕ) (hp : 0<p) : ℕ :=
  jetMulFee e ell p k hp+jetAddFee e ell p k hp+3*k*(jetEntryWidth e ell p+1)+4
def jetGeomFee (e ell p k n : ℕ) (hp : 0<p) : ℕ :=
  jetGeomBase e ell p k+n*jetGeomStride e ell p k hp

theorem geom_succ {R : Type*} [CommSemiring R] (x : R) (n : ℕ) :
    (∑ j∈Finset.range (n+1),x^j)=1+x*(∑ j∈Finset.range n,x^j) := by
  rw [Finset.sum_range_succ',pow_zero,add_comm,Finset.mul_sum]
  apply congrArg (fun y : R=>1+y)
  apply Finset.sum_congr rfl
  intro j _
  rw [pow_succ']

theorem jetGeom_exact (hp : 0<p) (he : 0<fw.length) (hv : 0<ell)
    {k : ℕ} (hk : 0<k) (x : JetTape fw ell k) (n : ℕ) :
    let y := jetGeom hp he hv hk x n
    jetRead hp he y.result=∑ j∈Finset.range n,(jetRead hp he x)^j ∧
      y.steps≤jetGeomFee fw.length ell p k n hp := by
  dsimp only
  induction n with
  | zero => simp [jetGeom,jetZero_exact,jetGeomFee,jetGeomBase]
  | succ n ih =>
    let y := jetGeom hp he hv hk x n
    let z := jetMult hp he x y.result
    let s := jetAdd hp he (jetOne hp he hv k hk) z.result
    have h1 : jetRead hp he y.result=∑ j∈Finset.range n,(jetRead hp he x)^j := ih.1
    have h2 : y.steps≤jetGeomFee fw.length ell p k n hp := ih.2
    have hz := jetMult_exact hp he x y.result
    have hs := jetAdd_exact hp he (jetOne hp he hv k hk) z.result
    change jetRead hp he s.result=_ ∧ y.steps+z.steps+s.steps+
      3*k*(jetEntryWidth fw.length ell p+1)+4≤_
    constructor
    · rw [hs.1,jetOne_exact,hz.1,h1,geom_succ]
    · unfold jetGeomFee at h2 ⊢
      rw [Nat.succ_mul n]
      unfold jetGeomStride at h2 ⊢
      have h3 : z.steps≤_ := hz.2
      have h4 : s.steps≤_ := hs.2
      omega

def divideJet (hp : 0<p) (he : 0<fw.length) (hv : 0<ell)
    {k : ℕ} (hk : 0<k) (normal values : JetTape fw ell k) : Meter (JetTape fw ell k) :=
  let x := jetSub hp he hv (jetOne hp he hv k hk) normal
  let geom := jetGeom hp he hv hk x.result k
  let out := jetMult hp he values geom.result
  ⟨out.result,x.steps+geom.steps+out.steps+3*k*(jetEntryWidth fw.length ell p+1)+4⟩

def quotientFee (e ell p k : ℕ) (hp : 0<p) : ℕ :=
  jetSubFee e ell p k hp+jetGeomFee e ell p k k hp+jetMulFee e ell p k hp+
     3*k*(jetEntryWidth e ell p+1)+4

theorem divideJet_exact (hp : 0<p) (he : 0<fw.length) (hv : 0<ell)
    {k : ℕ} (hk : 0<k) (normal values : JetTape fw ell k)
    (E F : (Coeff hp fw ell)[X])
    (hE : jetRead hp he normal=AdjoinRoot.mk (X^k) E)
    (hF : jetRead hp he values=AdjoinRoot.mk (X^k) F) :
    let Q := divideJet hp he hv hk normal values
    jetRead hp he Q.result=AdjoinRoot.mk (X^k) (J6ActiveNormalizer.quotientJet k E F) ∧
    Q.steps≤quotientFee fw.length ell p k hp := by
  let x := jetSub hp he hv (jetOne hp he hv k hk) normal
  let geom := jetGeom hp he hv hk x.result k
  let out := jetMult hp he values geom.result
  have hx := jetSub_exact hp he hv (jetOne hp he hv k hk) normal
  have hg := jetGeom_exact hp he hv hk x.result k
  have hq := jetMult_exact hp he values geom.result
  change jetRead hp he out.result=_ ∧ x.steps+geom.steps+out.steps+
      3*k*(jetEntryWidth fw.length ell p+1)+4≤_
  constructor
  · let R := Coeff hp fw ell
    let π := AdjoinRoot.mk ((X : R[X])^k)
    have hx' : jetRead hp he x.result=π (1-E) := by
      rw [hx.1,jetOne_exact,hE,map_sub,map_one]
    have hg' : jetRead hp he geom.result=π (∑ j∈Finset.range k,(1-E)^j) := by
      rw [hg.1,hx',map_sum]
      simp only [map_pow]
    rw [hq.1,hF,hg',←map_mul,J6ActiveNormalizer.quotientJet,
      ←AdjoinRoot.modByMonicHom_mk (monic_X.pow k)]
    exact (AdjoinRoot.mk_leftInverse (monic_X.pow k) _).symm
  · exact Nat.add_le_add_right (Nat.add_le_add_right
      (Nat.add_le_add (Nat.add_le_add hx.2 hg.2) hq.2) _) 4

#print axioms geom_succ
#print axioms jetGeom_exact
#print axioms divideJet_exact
end J6R22Active



