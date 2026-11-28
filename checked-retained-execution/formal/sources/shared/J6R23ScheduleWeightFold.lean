import J6R23ScheduleWeightParts

/-! Stream the real signed numerator or denominator factors. The
denotational integer powers below are never allocated by the machine.
Every factor is read at the receiving modulus; its valuation is
carried separately and all UV multiplication and copies are metered. -/
namespace J6R23ScheduleWeight
open scoped Polynomial
open A1R10 A1R11 A1R12 AOracleCoordinates AOracleMachineTime
open P1DyadicGrid HermiteLoss AOracleSuccinctNative

inductive Side where | num | den

def signedFactor (t : ℤ) (b : Side) (q : ℤ) : ℤ :=
  match b with
  | .num => -q
  | .den => t-q

def factorCount (t : ℤ) (b : Side) (q : ℤ×ℕ) : ℕ :=
  q.2*padicValInt 2 (signedFactor t b q.1)

def factorOdd (t : ℤ) (b : Side) (q : ℤ×ℕ) : ℤ :=
  (oddWord (signedFactor t b q.1))^q.2

def countParts (t : ℤ) (b : Side) (xs : List (ℤ×ℕ)) : ℕ :=
  (xs.map (factorCount t b)).sum

def oddParts (t : ℤ) (b : Side) (xs : List (ℤ×ℕ)) : ℤ :=
  (xs.map (factorOdd t b)).prod

def intParts (t : ℤ) (b : Side) (xs : List (ℤ×ℕ)) : ℤ :=
  (xs.map (fun q=>(signedFactor t b q.1)^q.2)).prod

theorem signedFactor_width {a : ℕ} {t q : ℤ} (ht : t∈grid a) (hq : q∈grid a) (b : Side) :
    (signedFactor t b q).natAbs<2^(a+1) := by
  cases b
  · exact grid_neg_width hq
  · exact diff_width ht hq

theorem intParts_split (t : ℤ) (b : Side) (xs : List (ℤ×ℕ))
    (hn : ∀ q∈xs,signedFactor t b q.1≠0) :
    intParts t b xs=pow₂ (countParts t b xs)*oddParts t b xs ∧ Odd (oddParts t b xs) := by
  induction xs with
  | nil => simp [intParts,countParts,oddParts,pow₂]
  | cons q qs ih =>
    obtain ⟨hQ,ho⟩ := factor_power_as_odd _ (hn q List.mem_cons_self) q.2
    obtain ⟨hR,hr⟩ := ih (fun z hz=>hn z (List.mem_cons_of_mem _ hz))
    refine ⟨?_,?_⟩
    · simp only [intParts,List.map_cons,List.prod_cons]
      have eqR : (List.map (fun q=>signedFactor t b q.1 ^ q.2) qs).prod=
          pow₂ (countParts t b qs)*oddParts t b qs := hR
      rw [hQ,eqR]
      change pow₂ (factorCount t b q)*factorOdd t b q*(pow₂ (countParts t b qs)*oddParts t b qs)
        =pow₂ (factorCount t b q+countParts t b qs)*(factorOdd t b q*oddParts t b qs)
      simp only [pow₂,pow_add]
      ring
    · exact ho.mul hr

variable {p ell : ℕ} {fw : List (Word p)}

def foldParts (hp : 0<p) (he : 0<fw.length) (hv : 0<ell)
    (a : ℕ) (t : ℤ) (b : Side) : List (ℤ×ℕ)→Meter (Part fw ell)
  | [] => ⟨⟨0,uvOne hp he hv⟩,uvWidth fw.length ell p+4⟩
  | q::qs =>
    let w := powerPart hp he hv (a+1) q.2 (signedFactor t b q.1)
    let r := foldParts hp he hv a t b qs
    let out := uvMul hp w.result.odd r.result.odd
    let T := w.result.two+r.result.two
    ⟨⟨T,out.result⟩,w.steps+r.steps+out.steps+8*(a+T+3)^2+10⟩

def foldFee (e ell p a : ℕ) (t : ℤ) (b : Side) : List (ℤ×ℕ)→ℕ
  | []=>uvWidth e ell p+4
  | q::qs=>partCap e ell p (a+1) q.2+foldFee e ell p a t b qs+
    mulCap e ell p+8*(a+factorCount t b q+countParts t b qs+3)^2+10

theorem foldParts_exact (hp : 0<p) (he : 0<fw.length) (hv : 0<ell)
    {a : ℕ} {t : ℤ} (ht : t∈grid a) (b : Side) (xs : List (ℤ×ℕ))
    (hx : ∀ q∈xs,q.1∈grid a) :
    let v := foldParts hp he hv a t b xs
    v.result.two=countParts t b xs ∧
    uvRead hp fw ell v.result.odd=(oddParts t b xs:Truncated (Modulus p hp fw) ell) ∧
    v.steps≤foldFee fw.length ell p a t b xs := by
  dsimp only
  induction xs with
  | nil => simp [foldParts,countParts,oddParts,uvOne_read hp he hv,foldFee]
  | cons q qs ih =>
    let w := powerPart hp he hv (a+1) q.2 (signedFactor t b q.1)
    let r := foldParts hp he hv a t b qs
    let out := uvMul hp w.result.odd r.result.odd
    have hF := powerPart_exact hp he hv (a+1) q.2 (signedFactor t b q.1)
      (signedFactor_width ht (hx q List.mem_cons_self) b)
    have hR := ih (fun q hq=>hx q (List.mem_cons_of_mem _ hq))
    have h1 : w.result.two=factorCount t b q := hF.1
    have h2 : r.result.two=countParts t b qs := hR.1
    have h3 : uvRead hp fw ell w.result.odd=(factorOdd t b q:Truncated (Modulus p hp fw) ell) := hF.2.1
    have h4 : uvRead hp fw ell r.result.odd=(oddParts t b qs:Truncated (Modulus p hp fw) ell) := hR.2.1
    have hM := uvMul_native_bit_cost hp w.result.odd r.result.odd
    refine ⟨by change w.result.two+r.result.two=_; rw [h1,h2]; rfl,?_,?_⟩
    · change uvRead hp fw ell out.result=
        ((factorOdd t b q*oddParts t b qs:ℤ):Truncated (Modulus p hp fw) ell)
      rw [hM.1,h3,h4,Int.cast_mul]
    · have hW : w.steps≤_ := hF.2.2
      have hT : r.steps≤_ := hR.2.2
      have hO : out.steps≤mulCap fw.length ell p := hM.2
      change w.steps+r.steps+out.steps+8*(a+(w.result.two+r.result.two)+3)^2+10≤_
      rw [h1,h2,foldFee]
      have eq : a+(factorCount t b q+countParts t b qs)+3=
          a+factorCount t b q+countParts t b qs+3 := by omega
      rw [eq]
      omega

#print axioms signedFactor_width
#print axioms intParts_split
#print axioms foldParts_exact
end J6R23ScheduleWeight


