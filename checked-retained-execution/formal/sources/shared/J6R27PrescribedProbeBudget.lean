
import J6R27PrescribedProbeRead
import J6R26StablePreparedRootInterpolate
import J6R22ActiveBinary

/-! Bound the actual repeated reads inside the existing quadratic
Lagrange pass. A raw-tape lookup is not separately assumed free. -/
namespace J6R27PrescribedProbe
open scoped Polynomial
open Polynomial A1R10 A1R11 AOracleMachineTime
open J6R22Active J6R26StablePreparedRoot
set_option maxHeartbeats 4200000

theorem uniform_word_bill {A B : Type*} (read : A→Meter B)
    (cost : ℕ) (h : ∀ i,(read i).steps≤cost) (L : List A) :
    bill read L≤L.length*cost := by
  induction L with
  | nil => simp [bill]
  | cons i L ih =>
    change (read i).steps+bill read L≤(L.length+1)*cost
    rw [Nat.add_mul,one_mul]
    exact (Nat.add_le_add (h i) ih).trans (le_of_eq (Nat.add_comm _ _))

section Batch
variable {p ell n : ℕ} {fw : List (Word p)}

theorem needs_at_uniform (node : Fin n→Meter (UVBlock fw ell))
    (cap : ℕ) (h : ∀ i,(node i).steps≤cap) (i : Fin n) :
    needsAt node i≤n*cap := by
  have H := uniform_word_bill node cap h (offDiagonal i)
  rw [offDiagonal_length] at H
  have A : cap+(n-1)*cap=(1+(n-1))*cap := by ring
  rw [show 1+(n-1)=n from by have := i.isLt; omega] at A
  change (node i).steps+bill node (offDiagonal i)≤_
  exact (Nat.add_le_add (h i) H).trans (le_of_eq A)

theorem interp_charged_repeated_reads (node sample : Fin n→Meter (UVBlock fw ell))
    (cap : ℕ) (h : ∀ i,(node i).steps≤cap) :
    interpBill node sample≤bill sample (probeOrder n)+n^2*cap := by
  let read (i : Fin n) : Meter Unit := ⟨(),needsAt node i+(sample i).steps⟩
  have H := bill_mono read sample (probeOrder n) (n*cap) (fun i _=>by
    have e := needs_at_uniform node cap h i
    change needsAt node i+(sample i).steps≤(sample i).steps+n*cap
    omega)
  simpa only [read,interpBill,bill,probeOrder,List.length_ofFn,pow_two,Nat.mul_assoc] using H
end Batch

theorem generated_probe_interp_bill {p ell D : ℕ} {fw : List (Word p)}
    (f : ℤ[X]) (hp : 0<p) (hv : 0<ell) (hN : f.natDegree=fw.length)
    (fit : D+1<2^f.natDegree) (sample : Fin (D+1)→Meter (UVBlock fw ell)) :
    let A := generatedProbeBits f D fw.length hN fit
    let node := readPrescribed hp hv A.result.read
    interpBill node sample≤bill sample (probeOrder (D+1))+(D+1)^2*
      ((D+1)*(f.natDegree+2)+f.natDegree*(p+6)+uvWidth f.natDegree ell p+4) := by
  let A := generatedProbeBits f D fw.length hN fit
  let node := readPrescribed hp hv A.result.read
  apply interp_charged_repeated_reads
  intro i
  have read := ((generated_probe_bits_receipt f D fw.length hN fit).2 i).2
  have enc := encodeProbe_cost hp hv (A.result.read i).result
  change (A.result.read i).steps+(encodeProbe hp hv (A.result.read i).result).steps+2≤_
  have same : fw.length*(p+6)+uvWidth fw.length ell p+2 =
      f.natDegree*(p+6)+uvWidth f.natDegree ell p+2 :=
    congrArg (fun k=>k*(p+6)+uvWidth k ell p+2) hN.symm
  rw [enc,same]
  have H : (A.result.read i).steps≤(D+1)*(f.natDegree+2) := read
  omega

#print axioms uniform_word_bill
#print axioms needs_at_uniform
#print axioms interp_charged_repeated_reads
#print axioms generated_probe_interp_bill
end J6R27PrescribedProbe
