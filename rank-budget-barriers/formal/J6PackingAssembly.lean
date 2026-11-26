import J6Mesh
import J6PhysicalPacking

/-! Tie the no-hole packet chart to the literal padding network's
counts. A padding gadget has one row for the negative unary clause,
one row for its variable, and two physical wires. -/
namespace J6PackingAssembly
open J6Mesh J6PhysicalPacking
variable {C : Type*} [Fintype C] [DecidableEq C]

theorem literal_assembly (m sH : ℕ) (hs : sH ≤ m) (rho : C) (hC : Fintype.card C = D m) :
    ∃ l : ℕ, ∃ h : m ≤ K m, 2*l = L m ∧
      (∀ c : C, (Finset.univ.filter
        (fun w : Wire rho m (K m) l => (place rho m (K m) l h w).1=c)).card = K m*L m) ∧
      Fintype.card (Wire rho m (K m) l) = M m ∧
      sH*L m + 2*Fintype.card (Pad rho m (K m) l) = physicalSize m sH ∧
      Nat.clog 2 (sH*L m + 2*Fintype.card (Pad rho m (K m) l))=lambda m := by
  obtain ⟨l,hL⟩ := (mesh_seats m).2.2
  have hl : 2*l=L m := by omega
  have ha := (mesh_seats m).2.1
  have hm : m ≤ K m := by omega
  have hcard :
      Fintype.card (Wire rho m (K m) l) = M m := by
    rw [Fintype.card_congr (placement rho m (K m) l hm)]
    simp only [Fintype.card_prod,Fintype.card_fin,hC,hl,mesh_product]
  have htotal : m*L m + Fintype.card (Pad rho m (K m) l)*2 = M m := by
    simpa only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,hl] using hcard
  have heq : sH*L m + 2*Fintype.card (Pad rho m (K m) l) = physicalSize m sH := by
    unfold physicalSize
    rw [Nat.mul_comm sH, Nat.mul_comm (L m) m, Nat.mul_comm 2]
    omega
  refine ⟨l,hm,hl,?_,hcard,heq,?_⟩
  · intro c
    rw [uniform_cell,hl]
  · rw [heq]
    exact (physicalSize_ceiling m sH hs).2.2

#print axioms literal_assembly
end J6PackingAssembly
