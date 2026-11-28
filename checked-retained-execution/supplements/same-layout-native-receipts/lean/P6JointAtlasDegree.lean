import P6JointAtlas

namespace Paper6JointSeating
open scoped Classical
open J7SourceLabels J7SeatSource J7PrintedParamsGraph J9R20SameFile

noncomputable section

variable {Pair H : Type} [Fintype Pair] [Fintype H]
variable (ends : H×Bool ≃ Pin Pair×Fin 3)

def cloneWires : Finset (Wires Pair H) := Finset.univ.filter fun w => clonePort w=true
def publicNonpins : Finset (Wires Pair H) := Finset.univ.filter fun w => nonpin (column ends cycle) w

theorem cloneWires_nonpin : cloneWires (Pair:=Pair) (H:=H) ⊆ publicNonpins ends := by
  intro w hw
  have h := clone_port_owner_exact ends w (Finset.mem_filter.mp hw).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨_,h⟩⟩

private theorem raw_clone_bound (x : Clones Pair) :
    Nat.card {w : Wires Pair H // colNode (column ends cycle) w = .inr (cloneOwner x)} ≤ 3 := by
  let col := column ends cycle
  obtain ⟨p,i⟩ := x
  cases i with
  | none =>
    let f : {w : Wires Pair H // colNode col w = .inr (.inl p)} →
        Option {w : OrdinaryWire Pair H // col w = .inl p}
      | ⟨.inl _,_⟩ => none
      | ⟨.inr w,h⟩ => some ⟨w,Sum.inr.inj h⟩
    have fi : Function.Injective f := by
      rintro ⟨⟨q,b⟩|u,hu⟩ ⟨⟨v,c⟩|w,hw⟩ hf
      · cases b <;> cases c <;> simp [colNode] at hu hw
        subst q; subst v; rfl
      · simp [f] at hf
      · simp [f] at hf
      · apply Subtype.ext
        exact congrArg Sum.inr (congrArg Subtype.val (Option.some.inj hf))
    have hc := Nat.card_le_card_of_injective f fi
    have hd := clone_degree ends cycle p
    rw [← Fintype.card_subtype] at hd
    simp only [Nat.card_eq_fintype_card, Fintype.card_option] at hc
    rw [Nat.card_eq_fintype_card]
    change _ ≤ (Fintype.card {w : OrdinaryWire Pair H // column ends cycle w = .inl p})+1 at hc
    exact hc.trans (by omega)
  | some j =>
    let v : OldNonPrivate Pair H := .inr (p,j)
    let f : {w : Wires Pair H // colNode col w = .inr (.inr v)} →
        {w : OrdinaryWire Pair H // col w = .inr v}
      | ⟨.inl (p,b),h⟩ => False.elim (by cases b <;> simp [colNode] at h)
      | ⟨.inr w,h⟩ => ⟨w,Sum.inr.inj h⟩
    have fi : Function.Injective f := by
      rintro ⟨⟨q,b⟩|u,hu⟩ ⟨⟨z,c⟩|w,hw⟩ hf
      · cases b <;> simp [colNode] at hu
      · cases b <;> simp [colNode] at hu
      · cases c <;> simp [colNode] at hw
      · exact Subtype.ext (congrArg (fun y => Sum.inr y.val) hf)
    have hc := Nat.card_le_card_of_injective f fi
    have hd := ordinary_degree ends cycle v
    rw [← Fintype.card_subtype,← Nat.card_eq_fintype_card] at hd
    exact hc.trans hd

theorem clone_port_cap (x : Clones Pair) :
    ((cloneWires (Pair:=Pair) (H:=H)).filter (fun w => associatedClone ends w=x)).card ≤ 3 := by
  let f : {w // w ∈ (cloneWires (Pair:=Pair) (H:=H)).filter
      (fun w => associatedClone ends w=x)} →
      {w : Wires Pair H // colNode (column ends cycle) w = .inr (cloneOwner x)} :=
    fun w => ⟨w.val,by
      have g := Finset.mem_filter.mp w.prop
      exact (clone_port_owner_exact ends w.val (Finset.mem_filter.mp g.1).2).trans
        (congrArg (fun y => Sum.inr (cloneOwner y)) g.2)⟩
  have h := Nat.card_le_card_of_injective f (fun _ _ h => Subtype.ext (congrArg (fun y : {w : Wires Pair H // colNode (column ends cycle) w =
    .inr (cloneOwner x)} => y.val) h))
  rw [Nat.card_eq_fintype_card,Fintype.card_coe] at h
  exact h.trans (raw_clone_bound ends x)

theorem match_clone_cap (M : Finset (Wires Pair H))
    (hM : Set.InjOn (rowNode Prod.fst) {w | w ∈ M}) (x : Clones Pair) :
    (M.filter (fun w => associatedClone ends w=x)).card ≤ 3 := by
  apply le_trans _ (clone_port_cap ends x)
  apply Finset.card_le_card_of_injOn cloneWireOf
  · intro w hw
    have hw' := (Finset.mem_filter.mp hw).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,clone_wire_is_clone w⟩,?_⟩
    exact (associatedClone_eq_of_row ends _ _ (clone_wire_same_row w)).trans hw'
  · intro w hw v hv he
    exact hM (Finset.mem_filter.mp hw).1 (Finset.mem_filter.mp hv).1
      ((clone_wire_same_row w).symm.trans ((congrArg (rowNode Prod.fst) he).trans (clone_wire_same_row v)))

#print axioms cloneWires_nonpin
#print axioms clone_port_cap
#print axioms match_clone_cap
end
end Paper6JointSeating

