
import A1R11Linear

/-! Exact fixed-width squared-truncation payload. An outer V row is a
real list of U residues, each represented by a physical p-bit word. -/
namespace J6R21Leaf
open AOracleMachineTime A1R10
set_option linter.unusedSectionVars false

variable {p ell : ℕ} {fw : List (A1R10.Word p)}

def scalarPayload (u : UBlock fw) : List Bool :=
  u.val.flatMap (fun w => w.val)

def leafPayload (u : UVBlock fw ell) : List Bool :=
  u.val.flatMap scalarPayload

private theorem length_flat_constant {A B : Type} (s : List A) (f : A→List B) (b : ℕ)
    (h : ∀ x∈s,(f x).length=b) :
    (s.flatMap f).length = s.length*b := by
  induction s with
  | nil => simp
  | cons y s ih =>
    simp only [List.flatMap_cons,List.length_append,List.length_cons,Nat.succ_mul]
    rw [h y List.mem_cons_self,ih (fun x hx=>h x (List.mem_cons_of_mem _ hx)),Nat.add_comm]

theorem scalar_payload_width (u : UBlock fw) :
    (scalarPayload u).length=fw.length*p := by
  unfold scalarPayload
  rw [length_flat_constant _ _ p (fun x _=>x.property),u.property]

theorem leaf_payload_width (u : UVBlock fw ell) :
    (leafPayload u).length=ell*(fw.length*p) := by
  unfold leafPayload
  rw [length_flat_constant _ _ (fw.length*p) (fun x _=>scalar_payload_width x),u.property]

theorem leaf_register_width (u : UVBlock fw ell) :
    (leafPayload u).length≤A1R11.uvWidth fw.length ell p := by
  rw [leaf_payload_width,A1R11.uvWidth]
  exact le_trans (Nat.mul_le_mul_left _ (Nat.le_succ _)) (Nat.le_add_right _ _)

#print axioms scalar_payload_width
#print axioms leaf_payload_width
#print axioms leaf_register_width
end J6R21Leaf
