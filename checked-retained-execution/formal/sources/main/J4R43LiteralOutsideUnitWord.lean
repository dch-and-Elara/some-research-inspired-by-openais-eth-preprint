import J4R43LiteralOutsideUnitStrip
import A1R12Words

/-! The signed Cauchy unit uses real fixed-width p-bit add/subtract and
schoolbook multiplication kernels after its bounded raw grid
preprocessing. No word-sized field arithmetic is assumed free. -/
namespace J4R43LiteralOutside
open scoped Classical BigOperators Polynomial
open Polynomial P1DyadicGrid DenominatorBudget J6R9PacketCoeff
open A1R10 A1R12 AOracleMachineTime AOracleCoordinates
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 5700000

def wordOpCap (p : ℕ) : ℕ := 32*(p+1)^2

def unitWordHorner {p : ℕ} (x : Word p) : ℕ→Meter (Word p)
  | 0 => ⟨wordZero p,3*p+4⟩
  | q+1 =>
    let last := unitWordHorner x q
    let m := mulWord x last.result
    let k := addWord (wordOne p) m.result
    ⟨k.result,last.steps+m.steps+k.steps+4*p+5⟩

theorem word_horner_exact {p : ℕ} (hp : 0<p) (x : Word p) (n : ℕ) :
    wordRead (unitWordHorner x n).result=(geoRun (wordRead x) n).1 ∧
    (unitWordHorner x n).steps≤3*p+4+n*(2*wordOpCap p+4*p+5) := by
  induction n with
  | zero =>
    constructor
    · exact (wordOps p hp).zero_read
    · simp [unitWordHorner]
  | succ n ih =>
    let last := unitWordHorner x n
    let m := mulWord x last.result
    let k := addWord (wordOne p) m.result
    constructor
    · simp only [unitWordHorner,addWord_read,wordOne_read p hp,mulWord_read,ih.1,geoRun]
    · have c₁ : m.steps≤wordOpCap p := (wordOps p hp).mul_cost _ _
      have c₂ : k.steps≤wordOpCap p := (wordOps p hp).add_cost _ _
      have c₀ : last.steps≤3*p+4+n*(2*wordOpCap p+4*p+5) := ih.2
      change last.steps+m.steps+k.steps+4*p+5≤3*p+4+(n+1)*(2*wordOpCap p+4*p+5)
      rw [Nat.succ_mul n]
      omega

def ratioWord {p : ℕ} (hp : 0<p) (n d : Word p) : Meter (Word p) :=
  let x := subWord hp (wordOne p) d
  let v := unitWordHorner x.result p
  let z := mulWord n v.result
  ⟨z.result,x.steps+v.steps+z.steps+9*p+9⟩

def ratioWordCap (p : ℕ) : ℕ :=
  2*wordOpCap p+12*p+13+p*(2*wordOpCap p+4*p+5)

theorem word_ratio_exact {p : ℕ} (hp : 0<p) (n d : Word p) :
    wordRead (ratioWord hp n d).result=
      wordRead n * (geoRun (1-wordRead d) p).1 ∧
    (ratioWord hp n d).steps≤ratioWordCap p := by
  let x := subWord hp (wordOne p) d
  let v := unitWordHorner x.result p
  let z := mulWord n v.result
  have xv : wordRead x.result=1-wordRead d := by
    dsimp only [x]
    rw [subWord_read,wordOne_read p hp]
  rw [show ratioWord hp n d=⟨z.result,x.steps+v.steps+z.steps+9*p+9⟩ from rfl]
  constructor
  · change wordRead (mulWord n v.result).result=_
    rw [mulWord_read,(word_horner_exact hp x.result p).1,xv]
  · change x.steps+v.steps+z.steps+9*p+9≤_
    have vc : v.steps≤3*p+4+p*(2*wordOpCap p+4*p+5) := (word_horner_exact hp x.result p).2
    have zc : z.steps≤wordOpCap p := (wordOps p hp).mul_cost _ _
    have xc : x.steps≤wordOpCap p := (wordOps p hp).sub_cost _ _
    unfold ratioWordCap
    omega

theorem actual_word_unit {p a : ℕ} (hp : 0<p) {t : ℤ} (mem : t∈grid a)
    (n d : Word p)
    (readsN : wordRead n=((paidNormalizeUnit a t).numerator:NativeProbeRing.Base p))
    (readsD : wordRead d=((paidNormalizeUnit a t).denominator:NativeProbeRing.Base p)) :
    wordRead (ratioWord hp n d).result=
      J6ZeroTransport.reduceAt p (NativeProbeRing.base_nilpotent p) (rho a t) ∧
      (ratioWord hp n d).steps≤ratioWordCap p := by
  obtain ⟨x,r⟩ := word_ratio_exact hp n d
  obtain ⟨nc,dc,_,_⟩ := normalized_unit_is_original a mem
  obtain ⟨_,odd,_⟩ := scaled_derivative_odd_fraction a mem
  have hc : scaledDerivative a 0=2*(scaledDerivative a 0/2)+1 := by
    obtain ⟨k,h⟩ := odd
    omega
  have A : (1:NativeProbeRing.Base p)-((scaledDerivative a 0:ℤ):NativeProbeRing.Base p)=
      -((2:NativeProbeRing.Base p)*((scaledDerivative a 0/2:ℤ):NativeProbeRing.Base p)) := by
    conv_lhs => rw [hc]
    push_cast
    ring
  rw [readsN,readsD,nc,dc,A] at x
  exact ⟨x.trans (actual_unit_run a mem p (NativeProbeRing.base_nilpotent p)).1,r⟩

#print axioms word_horner_exact
#print axioms word_ratio_exact
#print axioms actual_word_unit
end
end J4R43LiteralOutside

