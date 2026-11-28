
import J9R19CompiledBitsPrefixes

/-! Integer coefficient recurrence for an explicitly multiplied Lagrange
numerator. Every intermediate product and subtraction has a size proof.
The counter has one multiplication and one subtraction per visited old
coefficient. No general polynomial convolution is used. -/
namespace J9R19CompiledBits
open scoped BigOperators Polynomial
open Polynomial
set_option linter.unusedSectionVars false

structure LinearRun where
  coeffs : List ℤ
  words : List ℤ
  work : ℕ

/-- Horner list representation, with the constant coefficient first. -/
noncomputable def ofCoefficients : List ℤ → ℤ[X]
  | [] => 0
  | a::as => C a + X * ofCoefficients as

def linearRun (x previous : ℤ) : List ℤ → LinearRun
  | [] => ⟨[previous],[previous],0⟩
  | a::as =>
    let p := x*a
    let w := previous-p
    let q := linearRun x a as
    ⟨w::q.coeffs,p::w::q.words,q.work+2⟩

theorem linearRun_exact (x previous : ℤ) (coeffs : List ℤ) :
    ofCoefficients (linearRun x previous coeffs).coeffs =
      C previous + (X-C x)*ofCoefficients coeffs := by
  induction coeffs generalizing previous with
  | nil => simp [linearRun,ofCoefficients]
  | cons a as ih =>
    change C (previous-x*a) + X*ofCoefficients (linearRun x a as).coeffs = _
    rw [ih]
    simp only [ofCoefficients,map_sub,map_mul]
    ring

theorem linearRun_count (x previous : ℤ) (coeffs : List ℤ) :
    (linearRun x previous coeffs).coeffs.length=coeffs.length+1 ∧
      (linearRun x previous coeffs).work=2*coeffs.length := by
  induction coeffs generalizing previous with
  | nil => simp [linearRun]
  | cons a as ih => simp [linearRun,(ih a).1,(ih a).2,Nat.mul_succ]

theorem linearRun_fits {b w : ℕ} (x previous : ℤ) (coeffs : List ℤ)
    (hx : Fits b x) (hp : Fits w previous) (h : ∀ a∈coeffs, Fits w a) :
    (∀ z∈(linearRun x previous coeffs).coeffs, Fits (w+b+1) z) ∧
    (∀ z∈(linearRun x previous coeffs).words, Fits (w+b+1) z) := by
  induction coeffs generalizing previous with
  | nil =>
    have hh := hp.mono (show w≤w+b+1 by omega)
    simpa [linearRun] using hh
  | cons a as ih =>
    have ha : Fits w a := h a (by simp)
    have hmul : Fits (w+b) (x*a) := by
      simpa only [Nat.add_comm] using hx.mul ha
    have hsub := (hp.mono (show w≤w+b by omega)).sub hmul
    have tail := ih a ha (fun v hv => h v (by simp [hv]))
    constructor
    · intro z hz
      simp only [linearRun,List.mem_cons] at hz
      rcases hz with rfl|hz
      · exact hsub
      · exact tail.1 z hz
    · intro z hz
      simp only [linearRun,List.mem_cons] at hz
      rcases hz with rfl|rfl|hz
      · exact hmul.mono (by omega)
      · exact hsub
      · exact tail.2 z hz

/-- Construct coefficients only by adjoining linear factors on the
right-to-left coordinate list. -/
def factorRun : List ℤ → LinearRun
  | [] => ⟨[1],[1],0⟩
  | x::xs =>
    let q := factorRun xs
    let r := linearRun x 0 q.coeffs
    ⟨r.coeffs,q.words++r.words,q.work+r.work⟩

theorem factorRun_exact (xs : List ℤ) :
    ofCoefficients (factorRun xs).coeffs = (xs.map fun x => (X:ℤ[X])-C x).prod := by
  induction xs with
  | nil => simp [factorRun,ofCoefficients]
  | cons x xs ih =>
    change ofCoefficients (linearRun x 0 (factorRun xs).coeffs).coeffs =
      (X-C x)*(xs.map fun a => X-C a).prod
    rw [linearRun_exact,ih,map_zero,zero_add]

theorem factorRun_count (xs : List ℤ) :
    (factorRun xs).coeffs.length=xs.length+1 ∧
      (factorRun xs).work=xs.length*(xs.length+1) := by
  induction xs with
  | nil => simp [factorRun]
  | cons x xs ih =>
    have q := linearRun_count x 0 (factorRun xs).coeffs
    constructor
    · simpa only [factorRun,List.length_cons,ih.1] using q.1
    · simp only [factorRun,List.length_cons,ih.2,q.2,ih.1]
      ring

theorem factorRun_fits {b : ℕ} (xs : List ℤ) (h : ∀ a∈xs, Fits b a) :
    (∀ z∈(factorRun xs).coeffs, Fits ((b+1)*xs.length) z) ∧
    (∀ z∈(factorRun xs).words, Fits ((b+1)*xs.length) z) := by
  induction xs with
  | nil => simpa [factorRun] using Fits.one 0
  | cons x xs ih =>
    have hx := h x (by simp)
    have tail := ih (fun a ha => h a (by simp [ha]))
    have step := linearRun_fits x 0 (factorRun xs).coeffs hx (Fits.zero _) tail.1
    have ex : (b+1)*(x::xs).length=(b+1)*xs.length+b+1 := by
      simp only [List.length_cons,Nat.mul_succ]
      omega
    rw [ex]
    refine ⟨step.1,?_⟩
    intro z hz
    simp only [factorRun,List.mem_append] at hz
    rcases hz with hz|hz
    · exact (tail.2 z hz).mono (by omega)
    · exact step.2 z hz

theorem differenceProducts_fits {b : ℕ} (x : ℤ) (xs : List ℤ)
    (hx : Fits b x) (h : ∀ a∈xs, Fits b a) :
    Fits ((b+1)*xs.length) (xs.map fun a => x-a).prod := by
  have hl : ∀ t∈(xs.map fun a => x-a), Fits (b+1) t := by
    intro t ht
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp ht
    exact hx.sub (h a ha)
  simpa only [List.length_map] using product_fits _ hl

#print axioms linearRun_exact
#print axioms linearRun_count
#print axioms linearRun_fits
#print axioms factorRun_exact
#print axioms factorRun_count
#print axioms factorRun_fits
#print axioms differenceProducts_fits
end J9R19CompiledBits
