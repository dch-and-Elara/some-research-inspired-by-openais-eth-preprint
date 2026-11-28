import A1R43LiteralEstimate

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6000000

/-! Literal truth tables of the hard physical graph require at most
eight bits per original tensor (not a truth table of the global
input function). This is storage payload, not preprocessing time. -/
namespace A1R43Literal
open scoped Classical BigOperators
open J6R10Repack
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]
variable (F : Finset (V×V)) (Pad : Type) [Fintype Pad]
local notation "N" => network F Pad

def booleanTableBits : ℕ :=
  ∑ v : Row F Pad⊕Col F Pad, Nat.card (ParentPorts N v→Bool)

theorem source_vertex_count (cubic : ∀ v,GraphCutMoments.degree F v=3) :
    Nat.card (Row F Pad⊕Col F Pad)≤2*Nat.card (Wire F Pad) := by
  have hF : Nat.card (↥F)=F.card := by rw [Nat.card_eq_fintype_card,Fintype.card_coe]
  have hv : 2*F.card=3*Nat.card V := by
    rw [Nat.card_eq_fintype_card]
    exact GraphCutMoments.regular_edge_count F 3 cubic
  have hN : Nat.card (Wire F Pad)=2*(2*F.card)+Nat.card Pad := physical_wire_count F Pad
  rw [hN]
  change Nat.card ((↥F⊕(Occ F⊕Pad))⊕(V⊕(Occ F⊕Pad)))≤_
  simp only [Nat.card_sum,hF,simulated_incidence_count]
  omega

theorem each_local_table_has_at_most_eight (cubic : ∀ v,GraphCutMoments.degree F v=3)
    (v : Row F Pad⊕Col F Pad) : Nat.card (ParentPorts N v→Bool)≤8 := by
  have hc : Nat.card (ParentPorts N v)≤3 := by
    rcases v with r|c
    · rw [←Nat.card_congr (rowPortsEquiv N r)]
      rcases r with r|z
      · rw [real_row_degree]; decide
      · let emb : {e : Wire F Pad//(N).row e=.inr z} ↪ Unit :=
          ⟨fun _=>(),fun x y _=>Subtype.ext
            (((dummy_row_unique F Pad z x.val).1 x.property).trans
              ((dummy_row_unique F Pad z y.val).1 y.property).symm)⟩
        exact (Nat.card_le_card_of_injective emb emb.injective).trans (by simp)
    · rw [←Nat.card_congr (colPortsEquiv N c)]
      rcases c with v|z
      · rw [real_column_degree,cubic]
      · let emb : {e : Wire F Pad//(N).col e=.inr z} ↪ Unit :=
          ⟨fun _=>(),fun x y _=>Subtype.ext
            (((dummy_col_unique F Pad z x.val).1 x.property).trans
              ((dummy_col_unique F Pad z y.val).1 y.property).symm)⟩
        exact (Nat.card_le_card_of_injective emb emb.injective).trans (by simp)
  have hb : Nat.card Bool=2 := by rw [Nat.card_eq_fintype_card,Fintype.card_bool]
  rw [Nat.card_fun,hb]
  exact (Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) hc).trans (by decide)

theorem raw_binary_entry_payload (cubic : ∀ v,GraphCutMoments.degree F v=3) :
    booleanTableBits F Pad≤16*Nat.card (Wire F Pad) := by
  unfold booleanTableBits
  calc
    _ ≤ ∑ _v : Row F Pad⊕Col F Pad,8 :=
      Finset.sum_le_sum (fun v _=>each_local_table_has_at_most_eight F Pad cubic v)
    _ = 8*Nat.card (Row F Pad⊕Col F Pad) := by
      rw [Nat.card_eq_fintype_card]
      simp [Nat.mul_comm]
    _ ≤ 16*Nat.card (Wire F Pad) := by
      have h := Nat.mul_le_mul_left 8 (source_vertex_count F Pad cubic)
      omega

#print axioms source_vertex_count
#print axioms each_local_table_has_at_most_eight
#print axioms raw_binary_entry_payload
end
end A1R43Literal
