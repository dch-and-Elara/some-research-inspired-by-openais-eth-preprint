import J6R10RepackPhysical
import J6R15ModeCostEnum

/-! Direct Appendix D descriptor geometry, independent of the timing
proof. One crossing packet and one residue tile give one variable
at each positive weight strictly below the node precision. Eligible
packets are actual P11 pages, not edges, tuples, or emitted children. -/
namespace J6R15ModeCost
open P11FullPacking J6R10Repack

abbrev Mode (P : Type*) (tiles p : ℕ) := P × Fin tiles × Fin (p-1)

def modeWeight {P : Type*} {tiles p : ℕ} (m : Mode P tiles p) : ℕ :=
  m.2.2.val+1

theorem modeWeight_bounds {P : Type*} {tiles p : ℕ} (m : Mode P tiles p) :
    0<modeWeight m ∧ modeWeight m<p := by
  have := m.2.2.isLt
  change 0<m.2.2.val+1 ∧ m.2.2.val+1<p
  omega

theorem modeWeight_fibre {P : Type*} (tiles p w : ℕ) :
    Nat.card {m : Mode P tiles p // modeWeight m=w} =
      if 0<w ∧ w<p then Nat.card P*tiles else 0 := by
  by_cases h : 0<w ∧ w<p
  · rw [if_pos h]
    let b : Fin (p-1) := ⟨w-1,by omega⟩
    let e : {m : Mode P tiles p // modeWeight m=w} ≃ P×Fin tiles :=
      { toFun := fun m => (m.val.1,m.val.2.1)
        invFun := fun m => ⟨(m.1,m.2,b),by
          change (w-1)+1=w
          omega⟩
        left_inv := by
          rintro ⟨⟨u,v,t⟩,ht⟩
          have hh : b=t := by
            apply Fin.ext
            change w-1=t.val
            change t.val+1=w at ht
            omega
          apply Subtype.ext
          change (u,v,b)=(u,v,t)
          rw [hh]
        right_inv := fun _ => rfl }
    calc
      _ = Nat.card (P×Fin tiles) := Nat.card_congr e
      _ = _ := by rw [Nat.card_prod,Nat.card_fin]
  · rw [if_neg h]
    letI : IsEmpty {m : Mode P tiles p // modeWeight m=w} :=
      ⟨fun m => h (m.property ▸ modeWeight_bounds m.val)⟩
    exact Nat.card_of_isEmpty

abbrev Crossing {G : Type*} [LinearOrder G] {a pages : ℕ} (i : Fin a) :=
  {u : Page a pages G // (u.1.val i).1≠(u.1.val i).2}

theorem crossing_le_all {G : Type*} [LinearOrder G] [Fintype G] {a pages : ℕ}
    (i : Fin a) : Nat.card (Crossing (G:=G) (pages:=pages) i)≤Nat.card (Page a pages G) := by
  classical
  exact Nat.card_le_card_of_injective
    (fun u : Crossing (G:=G) (pages:=pages) i => u.val) Subtype.val_injective

theorem native_weight_multiplicity {E R C G : Type*} [Fintype E] [LinearOrder G] [Fintype G]
    {a : ℕ} {N : Network E R C} (P : PhysicalPacking N a G) (i : Fin a) (p w : ℕ) :
    Nat.card {m : Mode (Crossing (G:=G) (pages:=P.copies) i) (2^(i.val+1)) p //
        modeWeight m=w} * 2^(a-i.val) ≤ 6*Nat.card E := by
  rw [modeWeight_fibre]
  by_cases h : 0<w ∧ w<p
  · rw [if_pos h,mul_assoc,← pow_add]
    have hi : i.val+1+(a-i.val)=a+1 := by have := i.isLt; omega
    rw [hi,pow_succ,← mul_assoc]
    have hP := physical_packet_count P
    have hC := Nat.mul_le_mul_right (2^a) (crossing_le_all (G:=G) (pages:=P.copies) i)
    exact (Nat.mul_le_mul_right 2 (hC.trans hP)).trans_eq (by ring)
  · simp [h]

#print axioms modeWeight_bounds
#print axioms modeWeight_fibre
#print axioms native_weight_multiplicity
end J6R15ModeCost


