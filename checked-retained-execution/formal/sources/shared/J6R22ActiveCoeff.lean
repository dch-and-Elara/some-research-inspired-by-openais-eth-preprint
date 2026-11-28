import J6R22ActiveCenter
import A1R10Readout

/-! The quotient jet is physically a descending list of coefficient
blocks, so passing a prescribed coefficient to a later stage does
not require an oracle or an abstract quotient inverse. This only
prices the current-frame scan, not later cross-centre weighting. -/
namespace J6R22Active
open scoped Polynomial
open Polynomial A1R10 AOracleMachineTime AOracleCoordinates

variable {p ell k : ℕ} {fw : List (Word p)}

def jetCoeffM (hp : 0<p) (he : 0<fw.length) (v : JetTape fw ell k) (j : ℕ) :
    Meter (UVBlock fw ell) :=
  let x := scanWord (jetGates hp he ell) (k-1-j) v.val
  ⟨x.result,x.steps+6*(k+1)+4⟩

def jetCoeffFee (e ell p k : ℕ) : ℕ :=
  k*(jetEntryWidth e ell p+2)+6*(k+1)+4

theorem jetCoeffM_exact {R : Type*} [CommRing R]
    (hp : 0<p) (he : 0<fw.length) (φ : Coeff hp fw ell→+*R)
    (v : JetTape fw ell k) (j : ℕ) (hj : j<k) (F : R[X])
    (h : jetMap φ k (jetRead hp he v)=AdjoinRoot.mk (X^k) F) :
    φ (uvRead hp fw ell (jetCoeffM hp he v j).result)=F.coeff j ∧
      (jetCoeffM hp he v j).steps≤jetCoeffFee fw.length ell p k := by
  let o := jetOps hp he ell
  let i := k-1-j
  let scan := scanWord o.toGates i v.val
  have hI : i<v.val.length := by rw [v.property]; unfold i; omega
  have hJ : v.val.length-1-i=j := by rw [v.property]; unfold i; omega
  have hs := scanWord_exact o.toGates v.val i
  have hx := decode_coeff_scan o v.val i hI
  have hEq : AdjoinRoot.mk (X^k) ((decode o v.val).map φ)=AdjoinRoot.mk (X^k) F := by
    change jetMap φ k (AdjoinRoot.mk (X^k) (decode o v.val))=_ at h
    rwa [jetMap_mk] at h
  have hd := (X_pow_dvd_iff.mp (AdjoinRoot.mk_eq_mk.mp hEq)) j hj
  rw [coeff_sub,coeff_map,sub_eq_zero] at hd
  constructor
  · change φ (uvRead hp fw ell scan.result)=_
    rw [←hd,hJ] at * 
    exact congrArg φ (congrArg o.read hs.1 |>.trans hx.symm)
  · have hC : scan.steps≤k*(jetEntryWidth fw.length ell p+2) := by
      simpa only [v.property] using hs.2
    exact Nat.add_le_add_right (Nat.add_le_add_right hC _) _

#print axioms jetCoeffM_exact
end J6R22Active

