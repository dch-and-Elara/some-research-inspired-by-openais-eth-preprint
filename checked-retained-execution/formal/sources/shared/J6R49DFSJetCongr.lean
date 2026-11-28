import J6R24MeteredRecursionActiveValue

/-! Reuse the same finite interpolation and quotient arithmetic with
a different observed-sample stream. Equality is of actual output
words, not an unsupported equality of the work meters. -/
namespace J6R49DFS
open AOracleMachineTime A1R10 J6R22Active
set_option autoImplicit false
set_option maxHeartbeats 4300000

variable {p ell k n : ℕ} {fw : List (A1R10.Word p)}
variable (hp : 0<p) (he : 0<fw.length) (hv : 0<ell) (hk : 0<k)

theorem paid_jets_same_values {A : Type*}
    (g h : A→Meter (JetTape fw ell k)) (xs : List A)
    (eq : ∀ z∈xs,(g z).result=(h z).result) :
    (paidJetSum hp he g xs).result=(paidJetSum hp he h xs).result := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    have hd := eq x List.mem_cons_self
    have ht := ih (fun y hy=>eq y (List.mem_cons_of_mem _ hy))
    simp only [paidJetSum,hd,ht]

theorem interchangeable_samples
    (nodes g h : Fin n→Meter (UVBlock fw ell)) (normal : Meter (JetTape fw ell k))
    (eq : ∀ z,(g z).result=(h z).result) :
    (fullCenterM hp he hv hk nodes g normal).result=
      (fullCenterM hp he hv hk nodes h normal).result := by
  have ht (z : Fin n) :
      (interpTerm hp he hv hk nodes g z).result=(interpTerm hp he hv hk nodes h z).result := by
    simp only [interpTerm,eq z]
  have V := paid_jets_same_values hp he (interpTerm hp he hv hk nodes g)
    (interpTerm hp he hv hk nodes h) (probeOrder n) (fun z _=>ht z)
  simp only [fullCenterM,interpPrefix,V]

#print axioms paid_jets_same_values
#print axioms interchangeable_samples
end J6R49DFS
