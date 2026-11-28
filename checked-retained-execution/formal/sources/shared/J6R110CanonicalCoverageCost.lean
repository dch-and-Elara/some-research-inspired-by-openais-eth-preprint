import J6R109CanonicalProbeTableSpace
import J6R29BinaryFieldSearchCost

/-! Polynomial caps for actually building and keeping the selected
standard probe table when the field degree is the printed one.
These bounds are not supplied for unrelated field degrees. -/
namespace J6R110CanonicalCoverage
open AOracleMachineTime J6R109CanonicalProbeTable J6R29BinaryFieldSearch

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxHeartbeats 13000000

theorem printed_full_field_cardinality (s e : ℕ) (hs : 1<s)
    (degree : e=4*Nat.clog 2 s) : 2^e≤16*s^4 := by
  rw [degree,Nat.mul_comm 4 (Nat.clog 2 s),pow_mul]
  exact (Nat.pow_le_pow_left (pow_clog_two_bound s hs) 4).trans_eq (by ring)

theorem printed_full_field_width (s e : ℕ) (hs : 1<s)
    (degree : e=4*Nat.clog 2 s) : e≤8*s := by
  have log := (Nat.le_of_lt (Nat.lt_pow_self (n:=Nat.clog 2 s) (a:=2) (by decide))).trans
    (pow_clog_two_bound s hs)
  omega

/-- Exact source overhead for the R110 chart entry:
R109 generation, one R58 install (including its base), a table
handoff of four steps, then a chart handoff of three steps. -/
def wholeMountedDebit (e n : ℕ) : ℕ :=
  canonicalTableFee e n+(2+n*(3*e+5))+4+3

theorem printed_full_chart_numeric_caps (s e : ℕ) (hs : 1<s)
    (degree : e=4*Nat.clog 2 s) :
    let n := 2^e
    e*n≤128*s^5 ∧
    n*(3*e+5)≤464*s^5 ∧
    wholeMountedDebit e n≤3660*s^5 ∧
    selectedBuilderRoof e n≤264*s^5 ∧
    2*(e*n)≤256*s^5 := by
  let n := 2^e
  have hN : n≤16*s^4 := printed_full_field_cardinality s e hs degree
  have hE := printed_full_field_width s e hs degree
  have prod : e*n≤128*s^5 := (Nat.mul_le_mul hE hN).trans_eq (by ring)
  have h4 : s^4≤s^5 := Nat.pow_le_pow_right (show 0<s by omega) (by decide : 4≤5)
  have h1 : s≤s^5 := by
    simpa only [pow_one] using (Nat.pow_le_pow_right (show 0<s by omega) (by decide : 1≤5))
  have h0 : 1≤s^5 := (show 1≤s by omega).trans h1
  have variableCopy : n*(3*e+5)≤384*s^5+80*s^4 :=
    (Nat.mul_le_mul hN (show 3*e+5≤24*s+5 by omega)).trans_eq (by ring)
  have variableIncrement : (n-1)*(20*e+6)≤2560*s^5+96*s^4 :=
    (Nat.mul_le_mul ((Nat.sub_le n 1).trans hN) (show 20*e+6≤160*s+6 by omega)).trans_eq (by ring)
  have fee : wholeMountedDebit e n≤3660*s^5 := by
    unfold wholeMountedDebit canonicalTableFee
    omega
  have space : selectedBuilderRoof e n≤264*s^5 := by
    unfold selectedBuilderRoof
    exact Nat.max_le.mpr ⟨by omega,by omega⟩
  have read : n*(3*e+5)≤464*s^5 := by omega
  have two : 2*(e*n)≤256*s^5 := by omega
  exact ⟨prod,read,fee,space,two⟩

/-- Refers to the actual billed generator at the full printed count.
The one-table resident bound and selected-local-peak envelope are
independent of any prior numerical proof about a different table. -/
theorem actual_full_chart_builder_has_printed_polynomial_debit_and_peak
    (s e : ℕ) (hs : 1<s) (he : 0<e) (degree : e=4*Nat.clog 2 s) :
    let n := 2^e
    let out := canonicalTable e n
    out.result.length=n ∧ rawPayload out.result=e*n ∧
    out.steps=canonicalTableFee e n ∧
    out.steps≤3660*s^5 ∧ rawPayload out.result≤128*s^5 ∧
    selectedBuilderRoof e n≤264*s^5 := by
  let n := 2^e
  have np : 1≤n := Nat.succ_le_of_lt (by unfold n; positivity)
  have eq : n-1+1=n := Nat.sub_add_cancel np
  have dFit : n-1+1≤2^e := eq.le
  obtain ⟨count,_,bits⟩ := actual_canonical_table_payload_exact e (n-1) he dFit
  have F := (actual_canonical_table_is_paid_binary_prefix e (n-1) he dFit).2
  change (canonicalTable e (n-1+1)).result.length=n-1+1 at count
  change rawPayload (canonicalTable e (n-1+1)).result=e*(n-1+1) at bits
  change (canonicalTable e (n-1+1)).steps=canonicalTableFee e (n-1+1) at F
  rw [eq] at count bits F
  obtain ⟨B,_,fee,space,_⟩ := printed_full_chart_numeric_caps s e hs degree
  refine ⟨count,bits,F,?_,bits.le.trans B,space⟩
  rw [F]
  exact (show canonicalTableFee e n≤wholeMountedDebit e n by unfold wholeMountedDebit; omega).trans fee

#print axioms printed_full_field_cardinality
#print axioms printed_full_field_width
#print axioms printed_full_chart_numeric_caps
#print axioms actual_full_chart_builder_has_printed_polynomial_debit_and_peak
end J6R110CanonicalCoverage
