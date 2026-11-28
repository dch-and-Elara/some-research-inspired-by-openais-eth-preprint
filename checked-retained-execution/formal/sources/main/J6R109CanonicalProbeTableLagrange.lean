import J6R109CanonicalProbeTableBits
import J6ActiveInterpolation

/-! Read the already produced table, form its binary-coordinate
lifts in the actual U/V quotient, and reconstruct at the printed
count. Samples must be at these new legal probes, not relabelled
from the frozen other run. Construction and indexed copy are
different billed operations. -/
namespace J6R109CanonicalProbeTable
open scoped Polynomial
open Polynomial AOracleMachineTime AOracleMachineTimeTape
open A1R10 J6R58ActivePrep J6R27PrescribedProbe J6R33OriginalJ6
open NativeProbeRing J6ActiveInterpolation

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxHeartbeats 11000000

def readCanonical (rows : List (List Bool)) (i : ℕ) : Meter (List Bool) :=
  let scan := scanMask i rows
  ⟨scan.result.getD [],scan.steps⟩

theorem actual_canonical_lookup_is_paid_and_indexed (e d : ℕ) (he : 0<e)
    (fit : d+1≤2^e) (i : Fin (d+1)) :
    readCanonical (canonicalTable e (d+1)).result i.val=
      ⟨List.ofFn (zeroPrefix e d i),(i.val+1)*(3*e+5)⟩ := by
  let T := canonicalTable e (d+1)
  obtain ⟨num,width,_⟩ := actual_canonical_table_payload_exact e d he fit
  have hit : i.val<T.result.length := by rw [show T.result.length=d+1 from num]; exact i.isLt
  have correct := scan_mask_exact T.result e width i.val hit
  have same : T.result[i.val]=List.ofFn (zeroPrefix e d i) := by
    have H : T.result[i.val]?=(List.ofFn (fun j : Fin (d+1)=>List.ofFn (zeroPrefix e d j)))[i.val]? :=
      congrArg (fun x : List (List Bool)=>x[i.val]?) (actual_canonical_table_is_paid_binary_prefix e d he fit).1
    rw [getElem?_pos T.result i.val hit,List.getElem?_ofFn,dif_pos i.isLt,Option.some.injEq] at H
    exact H
  unfold readCanonical
  change (⟨(scanMask i.val T.result).result.getD [],(scanMask i.val T.result).steps⟩ :
    Meter (List Bool))=_
  rw [correct,same]
  rfl

theorem canonical_lookup_is_literal_prefix_of_a_larger_paid_table (e d D : ℕ)
    (he : 0<e) (fits : D+1≤2^e) (h : d≤D) (i : Fin (d+1)) :
    readCanonical (canonicalTable e (D+1)).result i.val=
      readCanonical (canonicalTable e (d+1)).result i.val := by
  have big := actual_canonical_lookup_is_paid_and_indexed e D he fits (Fin.castLE (Nat.add_le_add_right h 1) i)
  change readCanonical (canonicalTable e (D+1)).result i.val=
    ⟨List.ofFn (bitAt e i.val),(i.val+1)*(3*e+5)⟩ at big
  exact big.trans (actual_canonical_lookup_is_paid_and_indexed e d he ((Nat.add_le_add_right h 1).trans fits) i).symm

def writtenCoefficients (e d : ℕ) (rows : List (List Bool)) (i : Fin (d+1)) : Fin e→Bool :=
  fun k=>(readCanonical rows i.val).result[k.val]?.getD false

theorem read_canonical_coefficients_equal_zero_prefix (e d : ℕ) (he : 0<e)
    (fit : d+1≤2^e) (i : Fin (d+1)) :
    writtenCoefficients e d (canonicalTable e (d+1)).result i=zeroPrefix e d i := by
  funext k
  unfold writtenCoefficients
  rw [actual_canonical_lookup_is_paid_and_indexed e d he fit i,List.getElem?_ofFn,dif_pos k.isLt]
  rfl

theorem paid_canonical_rows_distinct (e d : ℕ) (he : 0<e)
    (fit : d+1≤2^e) :
    Function.Injective (fun i : Fin (d+1) => (readCanonical (canonicalTable e (d+1)).result i.val).result) := by
  intro i j H
  have eq : writtenCoefficients e d (canonicalTable e (d+1)).result i=
      writtenCoefficients e d (canonicalTable e (d+1)).result j :=
    funext (fun k=>congrArg (fun xs : List Bool=>xs[k.val]?.getD false) H)
  rw [read_canonical_coefficients_equal_zero_prefix e d he fit i,
    read_canonical_coefficients_equal_zero_prefix e d he fit j] at eq
  exact zero_prefix_distinct e d fit eq

noncomputable def writtenNode (p : ℕ) (f : ℤ[X]) (ell d : ℕ) (rows : List (List Bool))
    (i : Fin (d+1)) : J6ActiveInterpolation.Ring p f ell :=
  scalarIn p f ell (probe p f (writtenCoefficients f.natDegree d rows i))

theorem paid_canonical_probe_differences_are_units
    (p : ℕ) (f : ℤ[X]) (ell d : ℕ) (hp : 0<p) (hf : f.Monic)
    (hd : 0<f.natDegree) [Fact (Irreducible (residuePoly f))]
    (fit : d+1≤2^f.natDegree) :
    let rows := (canonicalTable f.natDegree (d+1)).result
    ∀ i j,i≠j→IsUnit (writtenNode p f ell d rows j-writtenNode p f ell d rows i) := by
  intro rows i j ne
  unfold writtenNode
  rw [read_canonical_coefficients_equal_zero_prefix f.natDegree d hd fit j,
    read_canonical_coefficients_equal_zero_prefix f.natDegree d hd fit i]
  exact (available_legal_zero_probe p ell d hp hf hd fit).2 i j ne

/-- Same degree, field size, and sample count as the source at any
allowed positive receiving precision. This is interpolation from
samples at the actually generated chosen binary coordinates. -/
theorem paid_printed_binary_probe_table_recovers_its_polynomial
    (p : ℕ) (f : ℤ[X]) (ell s M L : ℕ) (hp : 0<p) (hf : f.Monic)
    (hd : 0<f.natDegree) [Fact (Irreducible (residuePoly f))]
    (degree : f.natDegree=4*Nat.clog 2 s)
    (size : J9PrintedSchedule.probeCount M L≤s^4)
    (F : (J6ActiveInterpolation.Ring p f ell)[X]) (deg : F.natDegree≤J9PrintedSchedule.degreeBound M L) :
    let n := J9PrintedSchedule.probeCount M L
    let d := J9PrintedSchedule.degreeBound M L
    let actual := canonicalTable f.natDegree n
    let nodes := writtenNode p f ell d actual.result
    actual.result.length=n ∧ rawPayload actual.result=f.natDegree*n ∧
    actual.steps=canonicalTableFee f.natDegree n ∧
    Function.Injective (fun i : Fin (d+1) => (readCanonical actual.result i.val).result) ∧
    (∀ i j,i≠j→IsUnit (nodes j-nodes i)) ∧
    decoded nodes (fun i=>F.eval (nodes i))=F := by
  let d := J9PrintedSchedule.degreeBound M L
  have fit : d+1≤2^f.natDegree := by
    rw [degree]
    exact printed_fit s (Nat.clog 2 s) (d+1) (Nat.le_pow_clog (by decide : (1:ℕ)<2) s) size
  obtain ⟨count,_,raw⟩ := actual_canonical_table_payload_exact f.natDegree d hd fit
  have bill := (actual_canonical_table_is_paid_binary_prefix f.natDegree d hd fit).2
  have unique := paid_canonical_rows_distinct f.natDegree d hd fit
  have units := paid_canonical_probe_differences_are_units p f ell d hp hf hd fit
  exact ⟨count,raw,bill,unique,units,decoded_exact _ F deg units⟩

#print axioms actual_canonical_lookup_is_paid_and_indexed
#print axioms canonical_lookup_is_literal_prefix_of_a_larger_paid_table
#print axioms read_canonical_coefficients_equal_zero_prefix
#print axioms paid_canonical_rows_distinct
#print axioms paid_canonical_probe_differences_are_units
#print axioms paid_printed_binary_probe_table_recovers_its_polynomial
end J6R109CanonicalProbeTable
