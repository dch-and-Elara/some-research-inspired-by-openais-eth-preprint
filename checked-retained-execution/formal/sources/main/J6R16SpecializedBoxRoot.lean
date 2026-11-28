import J6R16SpecializedBoxSelected

/-! Install original subdivision equalities and old/pin CNF truth tables
as the real weighted-recursion parent, preserving the separate row
and column owners. The native guard uses these physical fibres. -/
namespace J6R14SpecializedBox
open scoped Polynomial Classical BigOperators
open Polynomial J6ActiveRun J6R9Recursive J6R12Blueprint J6R11Blueprint
open J6R10Repack J6R11Repack J8Physical J1PPrinted
noncomputable section
set_option linter.unusedSectionVars false

variable {Packet R S V G : Type} {P : V→Type} {L : ℕ}
variable (d : Layout Packet R S V G P L)
variable [Fintype R] [Fintype S] [Fintype V] [Fintype G] [Fintype Packet]
variable [(v : V)→Fintype (P v)]
variable (f : ℤ[X]) (ell created : ℕ) (F : OldTables d) (sign : S→Bool)

def orientedRootCall : Call (PhysicalHost f ell) :=
  ⟨physicalHost (orientedNetwork d) (orientedEntryFile d f ell created F sign),
    0,Fintype.card (Wire R),created⟩

theorem row_fibre_exact (r : R) :
    Nat.card {w : Wire R // (orientedNetwork d).row w=r} = 2 := by
  let e : {w : Wire R // (orientedNetwork d).row w=r} ≃ Bool :=
    { toFun := fun w => w.val.2
      invFun := fun x => ⟨(r,x),rfl⟩
      left_inv := by rintro ⟨⟨r',x⟩,h⟩; cases h; rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e,Nat.card_eq_fintype_card,Fintype.card_bool]

theorem pins_fibre_exact (s : S) :
    Nat.card {w : Wire R // (orientedNetwork d).col w=Sum.inl s} = 1 := by
  let e : {w : Wire R // (orientedNetwork d).col w=Sum.inl s} ≃ Unit :=
    { toFun := fun _ => ()
      invFun := fun _ => ⟨pinWire d s,by
        change colOwner d (pinWire d s)=Sum.inl s
        simp [colOwner,pinWire_column]⟩
      left_inv := by
        intro w
        have h := w.prop
        change colOwner d w.val = Sum.inl s at h
        unfold colOwner at h
        apply Subtype.ext
        apply d.column.injective
        rw [pinWire_column]
        cases hx : d.column w.val with
        | inl x =>
          rw [hx] at h
          have hh : x=s := Sum.inl.inj h
          rw [hh]
        | inr x => simp only [hx] at h; cases h
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e,Nat.card_eq_fintype_card,Fintype.card_unit]

theorem old_fibre_exact (v : V) :
    Nat.card {w : Wire R // (orientedNetwork d).col w=Sum.inr v} = Nat.card (P v) := by
  let owner : ColPort S P→S⊕V := Sum.map id Sigma.fst
  have howner (w : Wire R) : (orientedNetwork d).col w = owner (d.column w) := rfl
  let a : {w : Wire R // (orientedNetwork d).col w=Sum.inr v} ≃
      {q : ColPort S P // owner q=Sum.inr v} :=
    d.column.subtypeEquiv (fun w => by rw [howner])
  let e : {q : ColPort S P // owner q=Sum.inr v} ≃ P v :=
    { toFun := fun x => by
        rcases x with ⟨q,h⟩
        cases q with
        | inl w => cases h
        | inr y =>
          have he : y.1=v := Sum.inr.inj h
          exact he ▸ y.2
      invFun := fun x => ⟨.inr ⟨v,x⟩,rfl⟩
      left_inv := by
        rintro ⟨q,h⟩
        cases q with
        | inl c => cases h
        | inr y =>
          rcases y with ⟨v',x⟩
          change Sum.inr v' = Sum.inr v at h
          have eq := Sum.inr.inj h
          subst v'
          rfl
      right_inv := fun _ => rfl }
  exact Nat.card_congr (a.trans e)

theorem literal_oriented_root_stable {s C : ℕ}
    (hcap : Fintype.card (Wire R) ≤ C*s) (hΔ : 2≤sourceDelta s)
    (hCol : ∀ v, Nat.card (P v) ≤ sourceDelta s) :
    Stable s C (orientedRootCall d f ell created F sign) := by
  apply stable_root s C _ rfl rfl ?_ ?_ hcap
  · refine ⟨?_,?_⟩
    · intro r
      change Nat.card {w : Wire R // (orientedNetwork d).row w=r} ≤ _
      rw [row_fibre_exact]
      exact hΔ
    · intro v
      cases v with
      | inl p =>
        change Nat.card {w : Wire R // (orientedNetwork d).col w=Sum.inl p} ≤ _
        rw [pins_fibre_exact]
        omega
      | inr q =>
        change Nat.card {w : Wire R // (orientedNetwork d).col w=Sum.inr q} ≤ _
        rw [old_fibre_exact]
        exact hCol q
  · intro v
    exact le_rfl

#print axioms row_fibre_exact
#print axioms pins_fibre_exact
#print axioms old_fibre_exact
#print axioms literal_oriented_root_stable
end
end J6R14SpecializedBox