
import J6R30ProducedGateRegistryJobs

/-! Structural overhead of that actual publisher, excluding the
measured child-entry producer and the measured page-body compiler.
A failed comparison still scans the stored bytes. The overall
publication charge includes the two supplied producer meters once. -/
namespace J6R51Peak
open AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R26DescriptorTree J6R30ProducedGateRegistry

set_option autoImplicit false
set_option maxHeartbeats 3600000

def scanByWidth (key width rows : ℕ) : ℕ :=
  2+rows*(12*key+3*width+12)

theorem physical_header_scan_width_bill {key : ℕ} (bank : List (DirRow key)) (width : ℕ)
    (fit : ∀ row∈bank,row.bytes.length≤width) :
    fetchFee bank≤scanByWidth key width bank.length := by
  induction bank with
  | nil => simp [fetchFee,scanByWidth]
  | cons row tail ih =>
    have old := ih (fun x hx=>fit x (List.mem_cons_of_mem _ hx))
    have k := Nat.mul_le_mul_left 3 (fit row List.mem_cons_self)
    simp only [fetchFee,rowFee,scanByWidth,List.length_cons,Nat.add_mul,Nat.one_mul] at old ⊢
    omega

def publicationOverhead (key prec tw bw offset width hs rs : ℕ) : ℕ :=
  scanByWidth key width hs+3*width+2*key+9+(12*key+3*width+12)+4+
    headerReadFee prec offset+locateFee key rs+(3*key+3*prec+12)+contextCopyFee tw bw+key+14

theorem actual_publication_fee_with_explicit_word_caps
    {key prec tw bw : ℕ} {D : Type*} (bank : Ledger key prec tw bw D)
    (j : Job (key:=key) (prec:=prec) (tw:=tw) (bw:=bw) D) (width : ℕ)
    (fit : ∀ row∈bank.headers,row.bytes.length≤width) (newFit : j.entry.result.bytes.length≤width) :
    publishFee bank j.entry j.offset j.built ≤ j.entry.steps+j.built.steps+
      publicationOverhead key prec tw bw j.offset width bank.headers.length bank.records.length := by
  have h := physical_header_scan_width_bill bank.headers width fit
  have b := Nat.mul_le_mul_left 3 newFit
  unfold publishFee installFee rowFee publicationOverhead
  omega

#print axioms physical_header_scan_width_bill
#print axioms actual_publication_fee_with_explicit_word_caps
end J6R51Peak
