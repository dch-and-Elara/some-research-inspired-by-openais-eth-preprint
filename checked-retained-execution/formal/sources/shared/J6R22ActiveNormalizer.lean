import J6R22ActiveJetFold
import J6R18ChildWriteKernel
import J6R9RecursiveNormalizer

/-! Construct the local Hermite normalizer prefix, not just consume
supplied coefficients. Its data are signed grid addresses and taper
orders in the source centre roster. Every slope uses the literal
dyadic factorization and the metered odd correction; all powers
and products use the dense finite-tape machine. Roster production
and address reading from a global store are separate. -/
namespace J6R22Active
open scoped Polynomial BigOperators
open Polynomial A1R10 A1R11 A1R12 AOracleCoordinates AOracleMachineTime
open AOracleSuccinctNative AOracleSuccinctPhysical P1DyadicGrid DenominatorBudget

section Normal
variable {p ell : ℕ} {fw : List (Word p)}

def slopeM (hp : 0<p) (he : 0<fw.length) (hv : 0<ell) (a : ℕ) (t q : ℤ) :
    Meter (UVBlock fw ell) :=
  let d := dyadicInt hp (a+1) (t-q)
  let w := invM hp he hv (scalarM hp he hv d.result.2)
  let s := twoM hp he hv (a+1-d.result.1)
  padCost (mulM hp s w) (d.steps+8*(a+3)^2+4)

def slopeFee (e ell p a : ℕ) (hp : 0<p) : ℕ :=
  2*uvWidth e ell p+oddCap e ell p hp+mulCap e ell p+
    4*(p+a+2)+dyadicCap p (a+1)+8*(a+3)^2+8

noncomputable def localReduce (hp : 0<p) (fw : List (Word p)) (ell : ℕ) :
    TwoLocal →+* Coeff hp fw ell :=
  J6ZeroTransport.reduceAt p (double_quotient_two_nilpotent (Modulus p hp fw) ell)

theorem slopeM_exact (hp : 0<p) (he : 0<fw.length) (hv : 0<ell)
    {a : ℕ} {t q : ℤ} (ht : t∈grid a) (hq : q∈grid a) (hn : t≠q) :
    uvRead hp fw ell (slopeM hp he hv a t q).result=
      localReduce hp fw ell (J6ActiveLocalFactor.slope a t q) ∧
    (slopeM hp he hv a t q).steps≤slopeFee fw.length ell p a hp := by
  let d := dyadicInt hp (a+1) (t-q)
  let w := invM hp he hv (scalarM hp he hv d.result.2)
  let s := twoM hp he hv (a+1-d.result.1)
  obtain ⟨h1,h2,h3⟩ := dyadicInt_exact hp (a+1) (t-q) (diff_width ht hq)
  have hD : d.steps≤_ := h3
  have hW : w.steps≤uvWidth fw.length ell p+oddCap fw.length ell p hp+2 :=
    invM_cost hp he hv _
  have hS : s.steps≤uvWidth fw.length ell p+4*(p+a+2) := by
    change uvWidth fw.length ell p+4*(p+(a+1-d.result.1)+1)≤_
    omega
  have hM := mulM_cost hp s w
  refine ⟨?_,?_⟩
  · change uvRead hp fw ell (mulM hp s w).result=_
    simp only [s,w,mulM_read,twoM_read,invM_read,scalarM_read]
    have dx : d.result.1=padicValInt 2 (t-q) := h1
    have dy : wordRead d.result.2=(oddWord (t-q):ZMod (2^p)) := h2
    rw [dx,dy,map_intCast]
    exact (J6R18ChildWrite.reduction_slope p (double_quotient_two_nilpotent _ _) ht hq hn).symm
  · change (mulM hp s w).steps+(d.steps+8*(a+3)^2+4)≤_
    unfold slopeFee
    omega

def jetPowM (hp : 0<p) (he : 0<fw.length) (hv : 0<ell) {k : ℕ} (hk : 0<k)
    (x : JetTape fw ell k) : ℕ→Meter (JetTape fw ell k)
  | 0=>⟨jetOne hp he hv k hk,tapeFee fw.length ell p k⟩
  | n+1=>
    let y := jetPowM hp he hv hk x n
    let z := jetMult hp he y.result x
    ⟨z.result,y.steps+z.steps+tapeFee fw.length ell p k+2⟩

def powerTapeFee (e ell p k n : ℕ) (hp : 0<p) : ℕ :=
  tapeFee e ell p k+n*(jetMulFee e ell p k hp+tapeFee e ell p k+2)

theorem jetPowM_exact (hp : 0<p) (he : 0<fw.length) (hv : 0<ell) {k : ℕ} (hk : 0<k)
    (x : JetTape fw ell k) (n : ℕ) :
    let y := jetPowM hp he hv hk x n
    jetRead hp he y.result=jetRead hp he x^n ∧
    y.steps≤powerTapeFee fw.length ell p k n hp := by
  dsimp only
  induction n with
  | zero => simp [jetPowM,jetOne_exact,powerTapeFee]
  | succ n ih =>
    let y := jetPowM hp he hv hk x n
    let z := jetMult hp he y.result x
    have r : jetRead hp he y.result=jetRead hp he x^n := ih.1
    have c : y.steps≤_ := ih.2
    have zc : z.steps≤_ := (jetMult_exact hp he y.result x).2
    change jetRead hp he z.result=_ ∧ y.steps+z.steps+tapeFee fw.length ell p k+2≤_
    constructor
    · rw [(jetMult_exact hp he y.result x).1,r,pow_succ]
    · unfold powerTapeFee at c ⊢
      rw [Nat.succ_mul n]
      omega

def normalFactorM (hp : 0<p) (he : 0<fw.length) (hv : 0<ell) {k : ℕ} (hk : 0<k)
    (a : ℕ) (t : ℤ) (q : ℤ×ℕ) : Meter (JetTape fw ell k) :=
  let w := slopeM hp he hv a t q.1
  let x := jetMult hp he (jetConst hp he hk w.result) (jetX hp he hv k)
  let f := jetAdd hp he (jetOne hp he hv k hk) x.result
  let z := jetPowM hp he hv hk f.result q.2
  ⟨z.result,w.steps+x.steps+f.steps+z.steps+3*tapeFee fw.length ell p k+6⟩

def normalFactorFee (e ell p a k n : ℕ) (hp : 0<p) : ℕ :=
  slopeFee e ell p a hp+jetMulFee e ell p k hp+jetAddFee e ell p k hp+
    powerTapeFee e ell p k n hp+3*tapeFee e ell p k+6

theorem normalFactorM_exact (hp : 0<p) (he : 0<fw.length) (hv : 0<ell) {k : ℕ} (hk : 0<k)
    {a : ℕ} {t : ℤ} (q : ℤ×ℕ) (ht : t∈grid a) (hq : q.1∈grid a) (hn : t≠q.1) :
    let z := normalFactorM hp he hv hk a t q
    jetRead hp he z.result=AdjoinRoot.mk (X^k)
      ((1+C (localReduce hp fw ell (J6ActiveLocalFactor.slope a t q.1))*X)^q.2) ∧
    z.steps≤normalFactorFee fw.length ell p a k q.2 hp := by
  let w := slopeM hp he hv a t q.1
  let x := jetMult hp he (jetConst hp he hk w.result) (jetX hp he hv k)
  let f := jetAdd hp he (jetOne hp he hv k hk) x.result
  let z := jetPowM hp he hv hk f.result q.2
  have hw := slopeM_exact hp he hv ht hq hn
  have hx := jetMult_exact hp he (jetConst hp he hk w.result) (jetX hp he hv k)
  have hf := jetAdd_exact hp he (jetOne hp he hv k hk) x.result
  have hz := jetPowM_exact hp he hv hk f.result q.2
  change jetRead hp he z.result=_ ∧ w.steps+x.steps+f.steps+z.steps+3*tapeFee fw.length ell p k+6≤_
  constructor
  · rw [hz.1,hf.1,jetOne_exact,hx.1,jetConst_exact,jetX_exact hp he hv k hk,
      show uvRead hp fw ell w.result=_ from hw.1,←map_mul,←map_one (AdjoinRoot.mk (X^k)),
      ←map_add,←map_pow]
  · have w1 : w.steps≤_ := hw.2
    have x1 : x.steps≤_ := hx.2
    have f1 : f.steps≤_ := hf.2
    have z1 : z.steps≤_ := hz.2
    unfold normalFactorFee
    omega
end Normal

#print axioms slopeM_exact
#print axioms jetPowM_exact
#print axioms normalFactorM_exact
end J6R22Active

