
import J6R22RootReadoutWord
import J6R19RetainedNormal
import J6R19RetainedScalar
import J6R15SignedReadBase

/-! At the returned native U/V word, the constant input coefficient
is obtained by two actual bounded sequential scans of descending
coefficient tapes. The bit code never invokes polynomial normalization. -/
namespace J6R22RootReadout
open scoped Polynomial BigOperators
open Polynomial AOracleMachineTime AOracleCoordinates A1R10 A1R12
open J6R9Recursive J6R19Retained J6R15SignedRead J6R18ChildWrite
set_option linter.unusedSectionVars false
set_option maxHeartbeats 9500000

def scanLast {A : Type*} (width : ℕ) (prev : A) : List A→Meter A
  | [] => ⟨prev,1⟩
  | v::vs => padCost (scanLast width v vs) (width+2)

theorem scan_last_cost {A : Type*} (width : ℕ) (prev : A) (data : List A) :
    (scanLast width prev data).steps=1+data.length*(width+2) := by
  induction data generalizing prev with
  | nil => simp [scanLast]
  | cons v vs ih =>
    simp only [scanLast,padCost,ih,List.length_cons,Nat.add_mul,one_mul]
    omega

theorem constant_coefficient_scanned {A R : Type*} [CommRing R]
    (o : Ops A R) (width : ℕ) (data : List A) (prev : A)
    (h : data=[] → o.read prev=0) :
    (decode o data).coeff 0=o.read (scanLast width prev data).result := by
  induction data generalizing prev with
  | nil => simp [decode,scanLast,h rfl]
  | cons u us ih =>
    cases us with
    | nil => simp [decode,scanLast,padCost]
    | cons z zs =>
      have nz : 0≠(z::zs).length := by simp
      rw [decode,coeff_add,coeff_monomial_of_ne _ nz,zero_add]
      exact ih u (by simp)

def extractBaseWord {p ell : ℕ} (hp : 0<p) {fw : List (A1R10.Word p)} (uv : UVBlock fw ell) :
    Meter (A1R10.Word p) :=
  let row := scanLast (fw.length*p) (uGates hp fw).zero uv.val
  let w := scanLast p (wordZero p) row.result.val
  ⟨w.result,row.steps+w.steps+2⟩

theorem base_word_extract_exact {p ell : ℕ} (hp : 0<p) (hℓ : 0<ell)
    {fw : List (A1R10.Word p)} {f : ℤ[X]}
    (hf : f.Monic) (hPoly : Modulus p hp fw=NativeProbeRing.liftPoly p f)
    (uv : UVBlock fw ell) :
    wordRead (extractBaseWord hp uv).result=boxProject p f ell hf hℓ (castBox hPoly (uvRead hp fw ell uv)) ∧
      (extractBaseWord hp uv).steps=4+ell*(fw.length*p+2)+fw.length*(p+2) := by
  let row := scanLast (fw.length*p) (uGates hp fw).zero uv.val
  let B := scanLast p (wordZero p) row.result.val
  have hR := constant_coefficient_scanned (uOps hp fw) (fw.length*p) uv.val (uGates hp fw).zero
    (fun _=>(uOps hp fw).zero_read)
  have hW := constant_coefficient_scanned (wordOps p hp) p row.result.val (wordZero p)
    (fun _=>(wordOps p hp).zero_read)
  letI : Fact (1<(2:ℕ)^p) := ⟨one_lt_pow₀ (by decide) hp.ne'⟩
  have hSize := size_of_monic_words hp hf hPoly
  have hLen : row.result.val.length≤(NativeProbeRing.liftPoly p f).natDegree := by
    rw [row.result.property,hSize]
    unfold NativeProbeRing.liftPoly
    rw [hf.natDegree_map]
  have NF := normal_mapped (wordOps p hp) (RingHom.id (ZMod (2^p)))
    (hf.map (Int.castRingHom (ZMod (2^p)))) row.result.val hLen
  simp only [Polynomial.map_id] at NF
  constructor
  · change wordRead B.result=_
    unfold boxProject boxAtZero uvRead
    rw [castBox_mk,AdjoinRoot.lift_mk,Polynomial.eval₂_at_zero,RingHom.id_apply,Polynomial.coeff_map,hR]
    change wordRead B.result=NativeProbeRing.projectBase p f hf (transportU hPoly (uRead hp fw row.result))
    rw [uRead,transportU_mk,NativeProbeRing.projectBase]
    unfold NativeProbeRing.liftPoly
    rw [NF]
    exact hW.symm
  · change row.steps+B.steps+2=_
    rw [scan_last_cost,scan_last_cost,uv.property,row.result.property]
    ring

#print axioms scan_last_cost
#print axioms constant_coefficient_scanned
#print axioms base_word_extract_exact
end J6R22RootReadout
