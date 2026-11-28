import J6R33GeneratedChildSiteSparse

set_option autoImplicit false
set_option warningAsError true

/-! The legal selected adapter's installed rank width suffices for both
physical copy numbers and tile numbers of the R51 replay key. -/
namespace J6R51Dispatch
open J6R10Repack P11FullPacking J6R32ChildResidentTransfer J6R33GeneratedChildSite

theorem resident_dispatch_fields_fit {E A B : Type} {N : Network E A B} {a q p : ℕ}
    {P : PhysicalPacking N a (Fin 64)} (i : Fin a) {R : ChildResidents a q}
    (H : ResidentReceipt P i p R) (width : a ≤ q) :
    P.copies < 2^(q+1) ∧ (2:ℕ)^(i.val+1) < 2^(q+1) := by
  have hcopy : (2:ℕ)^(q-a) ≤ 2^q := Nat.pow_le_pow_right (by decide) (Nat.sub_le ..)
  have hmore : (2:ℕ)^q < 2^(q+1) := Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _)
  exact ⟨(H.copiesFit.trans hcopy).trans_lt hmore,
    Nat.pow_lt_pow_right (by decide) (by have := i.isLt; omega)⟩

#print axioms resident_dispatch_fields_fit
end J6R51Dispatch

