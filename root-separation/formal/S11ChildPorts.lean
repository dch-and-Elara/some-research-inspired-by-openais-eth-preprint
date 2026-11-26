
import S11Modes
import MainIncidence

noncomputable section
namespace S11
open Classical

variable {W P : Type*} [Fintype W] [Fintype P] {a L : ℕ}

/-- Every retained old port produces exactly one edge of the child, even
    when both endpoints of the original physical wire are in the group. -/
def ChildWire (G : Packing W P a L) (i : Fin a) (g : Fin 64) :=
  {w : W // (G.cell w).1 i = g} ⊕ {w : W // (G.cell w).2 i = g}

noncomputable instance (G : Packing W P a L) (i : Fin a) (g : Fin 64) :
    Fintype (ChildWire G i g) := by
  unfold ChildWire
  infer_instance

theorem child_wire_shrink (G : Packing W P a L) (i : Fin a) (g : Fin 64) (Δ : ℚ)
    (cert : SourceDensity.CollisionCertificate G.cell Δ) :
    16 * Fintype.card (ChildWire G i g) ≤ Fintype.card W := by
  have hl := SourceDensity.projected_port_bound G.cell Δ cert (fun c => c.1 i) _
    (BalancedUnion.single_coordinate_fiber i) g
  have hr := SourceDensity.projected_port_bound G.cell Δ cert (fun c => c.2 i) _
    (MainIncidence.factor_symbol_fiber i) g
  have hc : (Fintype.card (ChildWire G i g) : ℚ) =
      (SourceDensity.fiberCount (fun w => (G.cell w).1 i) g : ℚ) +
      (SourceDensity.fiberCount (fun w => (G.cell w).2 i) g : ℚ) := by
    simp only [ChildWire,Fintype.card_sum,Fintype.card_subtype,SourceDensity.fiberCount,Nat.cast_add]
  norm_num at hl hr
  exact_mod_cast (show (16:ℚ) * Fintype.card (ChildWire G i g) ≤ Fintype.card W by
    rw [hc]
    linarith)

theorem child_wire_source_eighth (G : Packing W P a L) (i : Fin a) (g : Fin 64) (Δ : ℚ)
    (cert : SourceDensity.CollisionCertificate G.cell Δ) :
    8 * Fintype.card (ChildWire G i g) ≤ Fintype.card W := by
  have h := child_wire_shrink G i g Δ cert
  omega

#print axioms child_wire_shrink
#print axioms child_wire_source_eighth

end S11

