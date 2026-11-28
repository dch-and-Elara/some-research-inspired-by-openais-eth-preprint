import J6RepairedCentered
import J6PackingAssembly

/-! Physical size arithmetic follows from the actual 64-letter alphabet.
The capacity chart is used only to count wires, not for packet shifts. -/
namespace J6RepairedCapacity
open J6Mesh P11FullPacking J6RepairedCentered J6RecursiveOrientation
variable {S : Type*} [LinearOrder S] [Fintype S]

omit [LinearOrder S] in
theorem ordered_cells_exact (m : ℕ) (hs : Fintype.card S = 64) :
    Fintype.card (Cell (Fin (a m)) S) = D m := by
  unfold Cell
  rw [Fintype.card_fun,Fintype.card_fin,Fintype.card_prod,hs]
  unfold a D
  have he : (64*64 : ℕ)=2^12 := by decide
  rw [he,← pow_mul]
  congr 1
  omega

theorem actual_wire_count (m l : ℕ) (w : Fin (a m) → S)
    (h : m ≤ K m) (hL : 2*l=L m) (hs : Fintype.card S = 64) :
    Fintype.card (Ports m l w) = M m := by
  classical
  rw [Fintype.card_congr (J6PhysicalPacking.placement (diagonal w) m (K m) l h)]
  simp only [Fintype.card_prod,Fintype.card_fin,ordered_cells_exact m hs,hL,mesh_product]

theorem exists_actual_repaired_size (m sH : ℕ) (hSize : sH ≤ m)
    (w : Fin (a m) → S) (hs : Fintype.card S = 64) :
    ∃ l, ∃ _h : m≤K m, 2*l=L m ∧ Fintype.card (Ports m l w)=M m ∧
        Nat.clog 2 (sH*L m + 2*Fintype.card (J6PhysicalPacking.Pad (diagonal w) m (K m) l))
          = lambda m := by
  obtain ⟨l,h,hh,_,hW,_,hc⟩ :=
    J6PackingAssembly.literal_assembly m sH hSize (diagonal w) (ordered_cells_exact m hs)
  exact ⟨l,h,hh,hW,hc⟩

#print axioms ordered_cells_exact
#print axioms actual_wire_count
#print axioms exists_actual_repaired_size
end J6RepairedCapacity