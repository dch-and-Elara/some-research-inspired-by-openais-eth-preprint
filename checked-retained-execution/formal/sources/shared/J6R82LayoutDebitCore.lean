import J6R68ActiveInputsProducer
import J6R49SourceLayoutLiveHeaders

/-! Real selected-layout inputs copy already produced physical endpoint
words. Bounds are on these operations, not on an arbitrary Meter with
the same output bytes. -/
namespace J6R82LayoutDebit
open scoped Classical Polynomial
open AOracleMachineTime J6R10Repack J6R36ChildFramedRoute
open J6R49SourceLayout J6R68ActiveInputs V8NativeMessage.N2DLabels

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4500000
set_option maxRecDepth 3400
set_option Elab.async false

section AbstractGap
variable {E R C : Type*} [Fintype E] {a : ℕ}
variable {N : Network E R C} {I : Full64Input N a}

def addIngressDelay (W : Ingress I) (extra : ℕ) : Ingress I :=
  ⟨⟨W.paid.result,W.paid.steps+extra⟩,W.commands,W.incidences⟩

/-- Keep the input, format, exact labels, rounded packing, and exported
payload intact. No bound follows on the full Meter from those fields. -/
theorem same_selected_bytes_do_not_bound_ingress (W : Ingress I) (cap : ℕ) :
    ∃ B : Ingress I, B.paid.result=W.paid.result ∧ cap<B.paid.steps ∧
      ∀ q,(runWithIngress I q B).result=(runWithIngress I q W).result ∧
        (runWithIngress I q B).steps=(runWithIngress I q W).steps+(cap+1) := by
  refine ⟨addIngressDelay W (cap+1),rfl,?_,fun _=>⟨rfl,?_⟩⟩
  · change cap<W.paid.steps+(cap+1)
    omega
  · simp only [runWithIngress,addIngressDelay]
    omega
end AbstractGap

/-- Both printed origin fields can carry a Page. This bounds the actual
reader above in either case, charging both body traversals separately. -/
theorem incidence_row_width_cap {w owner key prec page K : ℕ}
    (x : FramedEdge w owner key prec page)
    (e : w≤K) (o : owner≤K) (k : key≤K) (p : prec≤K) (g : page≤K)
    (left : x.left.body.length≤K) (right : x.right.body.length≤K) :
    framedIncidenceFee x+6≤33*K+67 := by
  have originUpper (present : Bool) : originFee key prec page present≤9*K+22 := by
    cases present <;> simp only [originFee,Bool.false_eq_true,if_false,if_true] <;> omega
  have l := originUpper x.left.origin.pageKey.isSome
  have r := originUpper x.right.origin.pageKey.isSome
  unfold framedIncidenceFee
  omega

theorem sum_mapped_bounded {α : Type*} (xs : List α) (g : α→ℕ)
    (K : ℕ) (fit : ∀ x∈xs,g x≤K) :
    (xs.map g).sum≤K*xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have h := fit x (List.mem_cons_self)
    have t := ih (fun y hy=>fit y (List.mem_cons_of_mem x hy))
    simpa only [List.map_cons,List.sum_cons,List.length_cons,Nat.mul_succ,Nat.add_comm K]
      using Nat.add_le_add h t

-- The three summands keep prior roster/header reads, target serialization,
-- and physical incidence scans distinct, with the named glue charged once.
def ingressRoof (K : ℕ) : ℕ :=
  ((3*K+77)*K+(3*K+1)*K+(3*K+7)*K+18)+
    ((6*K+22)*K+(3*K+13)*K+4)+(7+(33*K+67)*K)+5

theorem ingressRoof_quadratic (K : ℕ) :
    ingressRoof K=51*K^2+187*K+34 := by
  unfold ingressRoof
  ring

#print axioms same_selected_bytes_do_not_bound_ingress
#print axioms incidence_row_width_cap
#print axioms sum_mapped_bounded
#print axioms ingressRoof_quadratic
end J6R82LayoutDebit
