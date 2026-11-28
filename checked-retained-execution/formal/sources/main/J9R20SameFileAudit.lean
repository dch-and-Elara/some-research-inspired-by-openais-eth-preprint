
import J9R15FrozenErasureReadout
import J7PrintedParamsGraph

/-! Audit of the numerical R15 alias versus the actual J7 four-clone
incidence atlas. The reusable R15 projection theorem is unaffected. -/
namespace J9R20SameFile
open scoped Classical
open J7SourceLabels J7PrintedParamsGraph J7ToJ8Incidence J7SeatSource
noncomputable section
set_option linter.unusedSectionVars false

variable {Pair H : Type} [Fintype Pair] [Fintype H]

abbrev PrintedOld (Pair H : Type*) :=
  OrdinaryColumn Pair (OldNonPrivate Pair H)

abbrev PrintedOwners (Pair H : Type*) := Pin Pair ⊕ PrintedOld Pair H

theorem printed_pin_count_eq : Fintype.card (Pin Pair) = 2*Fintype.card Pair := by
  simp [Pin,Fintype.card_prod,Nat.mul_comm]

/-- Exact literal wire count from the actual incidence atlas. The Pair
type contributes two pins per element, never half a pin. -/
theorem fourClone_wire_count_eq (ends : H×Bool ≃ Pin Pair×Fin 3) :
    Fintype.card (Wire Pair (OrdinaryWire Pair H)) = 48*Fintype.card Pair := by
  rw [(actual_incidence ends).1,printed_pin_count_eq]
  ring

/-- The hypotheses of the numeric convenience theorem
J9R15FrozenErasure.four_clone_same_file_low_bits (and its frozen-binary
specialization), when applied to the later literal four-clone atlas,
force zero input size. This does not contradict the paper or the generic
low-precision lemma. -/
theorem r15_numeric_hypotheses_force_zero (ends : H×Bool ≃ Pin Pair×Fin 3)
    (N : ℕ) (hPair : Fintype.card Pair=2*N)
    (hEdges : Fintype.card (Wire Pair (OrdinaryWire Pair H))=24*N) :
    N=0 ∧ Fintype.card (Wire Pair (OrdinaryWire Pair H))=0 := by
  have hw := fourClone_wire_count_eq ends
  omega

theorem r15_numeric_not_a_nonempty_printed_root
    (ends : H×Bool ≃ Pin Pair×Fin 3)
    (hM : 0<Fintype.card (Wire Pair (OrdinaryWire Pair H))) :
    ¬ ∃ N : ℕ, Fintype.card Pair=2*N ∧
      Fintype.card (Wire Pair (OrdinaryWire Pair H))=24*N := by
  rintro ⟨N,hPair,hEdges⟩
  exact hM.ne' (r15_numeric_hypotheses_force_zero ends N hPair hEdges).2

/-- The declared old R15 set names only the pin-adjacent clone. -/
theorem r15_named_hosts_are_only_one_per_pin :
    (J9R15FrozenErasure.cloneHosts (Pair:=Pair) (Col:=OldNonPrivate Pair H)).card=
      Fintype.card (Pin Pair) := by
  rw [J9R15FrozenErasure.cloneHosts_card,printed_pin_count_eq]

/-- The tagged original four clone types, with no pin vertex or old
binary clause vertex included. -/
def cloneOwner (x : Pin Pair × Index) : PrintedOld Pair H :=
  match x.2 with
  | none => .inl x.1
  | some j => .inr (.inr (x.1,j))

theorem cloneOwner_injective : Function.Injective (cloneOwner (Pair:=Pair) (H:=H)) := by
  rintro ⟨p,i⟩ ⟨q,j⟩ h
  cases i <;> cases j <;> simp [cloneOwner] at h ⊢ <;> aesop

def allCloneOwners : Finset (Option (PrintedOwners Pair H)) :=
  Finset.univ.image (fun x : Pin Pair×Index => some (.inr (cloneOwner x)))

theorem allCloneOwners_card :
    (allCloneOwners (Pair:=Pair) (H:=H)).card=4*Fintype.card (Pin Pair) := by
  unfold allCloneOwners
  rw [Finset.card_image_of_injective _ (fun _ _ h => cloneOwner_injective (Sum.inr.inj (Option.some.inj h))),
    Finset.card_univ]
  simp [Index,Fintype.card_prod,Nat.mul_comm]

theorem mem_allCloneOwners (w : Option (PrintedOwners Pair H)) :
    w∈allCloneOwners (Pair:=Pair) (H:=H) ↔ ∃ u : Pin Pair×Index, w=some (.inr (cloneOwner u)) := by
  constructor
  · intro h
    obtain ⟨x,_,hx⟩ := Finset.mem_image.mp h
    exact ⟨x,hx.symm⟩
  · rintro ⟨x,rfl⟩
    exact Finset.mem_image.mpr ⟨x,Finset.mem_univ _,rfl⟩

theorem r15_named_hosts_subset :
    J9R15FrozenErasure.cloneHosts (Pair:=Pair) (Col:=OldNonPrivate Pair H) ⊆
      allCloneOwners (Pair:=Pair) (H:=H) := by
  intro x hx
  obtain ⟨p,rfl⟩ := (J9R15FrozenErasure.mem_cloneHosts_iff x).1 hx
  exact (mem_allCloneOwners _).2 ⟨(p,none),rfl⟩

/-- Actual real port of each selected clone, including the three
nonpin-adjacent clones which R15's old host set omitted. -/
theorem allClones_have_literal_port (ends : H×Bool ≃ Pin Pair×Fin 3)
    (x : Pin Pair×Index) :
    ∃ e : Wire Pair (OrdinaryWire Pair H),
      colNode (column ends cycle) e=.inr (cloneOwner x) := by
  obtain ⟨p,j⟩ := x
  cases j with
  | none => exact ⟨.inl (p,true),rfl⟩
  | some j =>
    let y := ends.symm (p,j)
    refine ⟨.inr ((.inl y.1,y.2),true),?_⟩
    unfold colNode column route cloneOwner
    change Sum.inr (Sum.inr (Sum.inr (ends y))) = Sum.inr (Sum.inr (Sum.inr (p,j)))
    rw [Equiv.apply_symm_apply]

#print axioms printed_pin_count_eq
#print axioms fourClone_wire_count_eq
#print axioms r15_numeric_hypotheses_force_zero
#print axioms r15_numeric_not_a_nonempty_printed_root
#print axioms r15_named_hosts_are_only_one_per_pin
#print axioms allCloneOwners_card
#print axioms r15_named_hosts_subset
#print axioms allClones_have_literal_port

end
end J9R20SameFile
