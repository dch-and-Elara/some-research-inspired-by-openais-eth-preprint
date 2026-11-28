import J6R23ScheduleWeightRoster
import J6R23ScheduleWeightFormula
import J6R22ActiveNormalizer
import J6R22ActiveUnit

/-! Actual common-precision Hermite weight generation. Input is a
source sign/order roster and centre number, not precomputed numeric
weights. Run the two signed dyadic folds, invert the single odd
denominator in the native UV machine, and write the clipped shift.
The surrounding descriptor preparation and cross-centre accumulation
are not assigned zero cost by this per-weight receipt. -/
namespace J6R23ScheduleWeight
open scoped Polynomial
open A1R10 A1R11 A1R12 AOracleCoordinates AOracleMachineTime
open P1DyadicGrid HermiteLoss J6ActiveSchedule J6R22Active
open AOracleSuccinctNative AOracleSuccinctPhysical

variable {p ell : ℕ} {fw : List (Word p)}

def rawWeight (hp : 0<p) (he : 0<fw.length) (hv : 0<ell)
    (a B j : ℕ) (t : ℤ) (xs : List (ℤ×ℕ)) : Meter (UVBlock fw ell) :=
  let N := foldParts hp he hv a t .num (xs++[(t,j)])
  let D := foldParts hp he hv a t .den xs
  let denInv := invM hp he hv (stored D.result.odd)
  let prod := mulM hp (stored N.result.odd) denInv
  let shifted := mulM hp (twoM hp he hv (B+N.result.two-(D.result.two+(a+1)*j))) prod
  padCost shifted (N.steps+D.steps+8*(a+B+j+N.result.two+D.result.two+6)^2+10)

def rawWeightFee (e ell p a B j : ℕ) (hp : 0<p) (t : ℤ) (xs : List (ℤ×ℕ)) : ℕ :=
  let vn := countParts t .num (xs++[(t,j)])
  let vd := countParts t .den xs
  foldFee e ell p a t .num (xs++[(t,j)])+foldFee e ell p a t .den xs+
  3*uvWidth e ell p+oddCap e ell p hp+2*(mulCap e ell p+2)+2+
  4*(p+B+vn+1)+8*(a+B+j+vn+vd+6)^2+10

theorem rawWeight_exact (hp : 0<p) (he : 0<fw.length) (hv : 0<ell)
    {a M u B j : ℕ} {t : ℤ} (ht : t∈active a M u)
    (hB : totalLoss a (sourceH M u) j t≤B) (L : Roster a M u t) :
    let z := rawWeight hp he hv a B j t L.rows
    uvRead hp fw ell z.result=localReduce hp fw ell (scaledWeight a u (sourceH M u) B j t) ∧
    z.steps≤rawWeightFee fw.length ell p a B j hp t L.rows := by
  have ⟨hGr,hNe⟩ := J6R9Recursive.active_grid a M u ht
  let xs := L.rows++[(t,j)]
  let N := foldParts hp he hv a t .num xs
  let D := foldParts hp he hv a t .den L.rows
  let x := invM hp he hv (stored D.result.odd)
  let y := mulM hp (stored N.result.odd) x
  let k := B+N.result.two-(D.result.two+(a+1)*j)
  let s := twoM hp he hv k
  let z := mulM hp s y
  have hn (q : ℤ×ℕ) (hq : q∈xs) : q.1∈grid a := by
    rcases List.mem_append.mp hq with h | h
    · exact L.is_grid q h
    · rw [List.mem_singleton] at h
      subst q
      exact hGr
  obtain ⟨hN1,hN2,hN3⟩ := foldParts_exact hp he hv hGr .num xs hn
  obtain ⟨hD1,hD2,hD3⟩ := foldParts_exact hp he hv hGr .den L.rows L.is_grid
  let vn := countParts t .num xs
  let vd := countParts t .den L.rows
  have hn1 : N.result.two=vn := hN1
  have hd1 : D.result.two=vd := hD1
  have hnC : N.steps≤foldFee fw.length ell p a t .num xs := hN3
  have hdC : D.steps≤foldFee fw.length ell p a t .den L.rows := hD3
  have hx : x.steps≤uvWidth fw.length ell p+oddCap fw.length ell p hp+2 :=
    invM_cost hp he hv (stored D.result.odd)
  have hy : y.steps≤uvWidth fw.length ell p+x.steps+mulCap fw.length ell p+2 :=
    mulM_cost hp (stored N.result.odd) x
  have hs : s.steps≤uvWidth fw.length ell p+4*(p+B+vn+1) := by
    change uvWidth fw.length ell p+4*(p+k+1)≤_
    have H : k≤B+vn := by unfold k; rw [hn1]; exact Nat.sub_le _ _
    omega
  have hz : z.steps≤s.steps+y.steps+mulCap fw.length ell p+2 := mulM_cost hp s y
  constructor
  · change uvRead hp fw ell z.result=_
    have A := L.numerator_parts ht j
    have D' := L.denominator_parts j
    have h1 : uvRead hp fw ell N.result.odd=
        (oddWord (weightNum a u (sourceH M u) j t):Truncated (Modulus p hp fw) ell) :=
      hN2.trans (congrArg (fun v : ℤ=>(v:Truncated (Modulus p hp fw) ell)) A.2)
    have h2 : uvRead hp fw ell D.result.odd=
        (oddWord (weightDen a u (sourceH M u) j t):Truncated (Modulus p hp fw) ell) :=
      hD2.trans (congrArg (fun v : ℤ=>(v:Truncated (Modulus p hp fw) ell)) D'.2)
    have hK : k=B+level (weightNum a u (sourceH M u) j t)-
        level (weightDen a u (sourceH M u) j t) := by
      unfold k
      rw [hn1,hd1,show vn=level (weightNum a u (sourceH M u) j t) from A.1,
        show vd+(a+1)*j=level (weightDen a u (sourceH M u) j t) from D'.1]
    simp only [z,s,y,x,mulM_read,invM_read,twoM_read,stored_result,h1,h2,hK]
    rw [localReduce,scaled_word_formula p (double_quotient_two_nilpotent _ _) a u (sourceH M u) B j hGr hNe hB]
    ring
  · change z.steps+(N.steps+D.steps+8*(a+B+j+N.result.two+D.result.two+6)^2+10)≤_
    rw [hn1,hd1]
    unfold rawWeightFee
    change _≤foldFee fw.length ell p a t .num xs+foldFee fw.length ell p a t .den L.rows+
      3*uvWidth fw.length ell p+oddCap fw.length ell p hp+2*(mulCap fw.length ell p+2)+2+
      4*(p+B+vn+1)+8*(a+B+j+vn+vd+6)^2+10
    omega

#print axioms rawWeight_exact
end J6R23ScheduleWeight



