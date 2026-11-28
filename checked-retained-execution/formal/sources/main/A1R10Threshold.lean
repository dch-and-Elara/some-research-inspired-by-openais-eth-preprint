import A1R10Readout
import A1R10Ops

/-! One threshold witness after multiplying supplied signed row factors.
The supplied factor tape, validity/parse checks and the counting oracle
are not charged by this arithmetic subroutine. -/

namespace A1R10
open AOracleMachineTime AOracleMachineTimeMul AOracleMachineTimeLocal AOracleCoordinates

def uvAccept {p : ℕ} (hp : 0<p) {f : List (Word p)} {ell : ℕ}
    (v : UVBlock f ell) (i j : ℕ) (d : Word p) : Meter Bool :=
  let a := uvScan hp v i j
  let b := compareBits d.val a.result.val
  ⟨b.result,a.steps+b.steps+2⟩

theorem uvAccept_exact {p : ℕ} (hp : 0<p) {f : List (Word p)} {ell : ℕ}
    (v : UVBlock f ell) (i : Fin f.length) (j : Fin ell) (d : Word p)
    (hf : (Modulus p hp f).Monic) (hd : (Modulus p hp f).natDegree=f.length) :
    let coord := doubleCoord (Modulus p hp f) hf ell
      (⟨f.length-1-i.val,by have := i.isLt; omega⟩,⟨ell-1-j.val,by have := j.isLt; omega⟩)
    ((uvAccept hp v i.val j.val d).result=true ↔ bitsValue d.val<(coord (uvRead hp f ell v)).val) ∧
      (uvAccept hp v i.val j.val d).steps≤ell*(f.length*p+2)+f.length*(p+2)+10*p+6 := by
  let a := uvScan hp v i.val j.val
  have hv := uvScan_native hp v i j hf hd
  obtain ⟨hb,hc⟩ := compareBits_exact d.val a.result.val (d.property.trans a.result.property.symm)
  have hval : (wordRead a.result).val=bitsValue a.result.val := by
    apply ZMod.val_natCast_of_lt
    have h := bitsValue_lt a.result.val
    rwa [a.result.property] at h
  constructor
  · change (compareBits d.val a.result.val).result=true ↔ _
    rw [hb,← hval]
    exact Iff.intro (fun h => by rw [← hv]; exact h) (fun h => by rwa [hv])
  · change a.steps+(compareBits d.val a.result.val).steps+2≤_
    have ht := uvScan_cost hp v i.val j.val
    change a.steps≤_ at ht
    rw [hc,d.property]
    omega

def uvProductAccept {p : ℕ} (hp : 0<p) {f : List (Word p)} {ell : ℕ}
    (he : 0<f.length) (hv : 0<ell) (t : List (UVBlock f ell))
    (i j : ℕ) (d : Word p) : Meter Bool :=
  let a := uvProduct hp he hv t
  let b := uvAccept hp a.result i j d
  ⟨b.result,a.steps+b.steps⟩

theorem uvProductAccept_exact {p : ℕ} (hp : 0<p) {f : List (Word p)} {ell : ℕ}
    (he : 0<f.length) (hv : 0<ell) (t : List (UVBlock f ell))
    (i : Fin f.length) (j : Fin ell) (d : Word p)
    (hf : (Modulus p hp f).Monic) (hd : (Modulus p hp f).natDegree=f.length) :
    let coord := doubleCoord (Modulus p hp f) hf ell
      (⟨f.length-1-i.val,by have := i.isLt; omega⟩,⟨ell-1-j.val,by have := j.isLt; omega⟩)
    ((uvProductAccept hp he hv t i.val j.val d).result=true ↔
      bitsValue d.val<(coord ((t.map (uvRead hp f ell)).prod)).val) ∧
    (uvProductAccept hp he hv t i.val j.val d).steps≤
       ell*(f.length*p+1)+4+t.length*(3432*((ell+1)^2*(f.length+1)^2*(p+1)^2)+4)+
       ell*(f.length*p+2)+f.length*(p+2)+10*p+6 := by
  let a := uvProduct hp he hv t
  obtain ⟨he',ht⟩ := uvProduct_exact hp he hv t
  obtain ⟨ha,hv'⟩ := uvAccept_exact hp a.result i j d hf hd
  change uvRead hp f ell a.result=_ at he'
  constructor
  · change (uvAccept hp a.result i.val j.val d).result=true ↔ _
    simpa only [he'] using ha
  · change a.steps+(uvAccept hp a.result i.val j.val d).steps≤_
    change a.steps≤_ at ht
    omega

#print axioms uvAccept_exact
#print axioms uvProductAccept_exact
end A1R10
