
import A2R45LiteralGate

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 8000000
set_option maxRecDepth 1800
set_option linter.unusedSectionVars false

/-! Degree bounds for the real split A2 network, including all
fillers. Splitting does not add ports to any old row or column. -/
namespace A2R45Literal
open scoped Classical BigOperators Polynomial
open FixedHostAcquisition A1R43Literal.General J6R10Repack 
noncomputable section

variable {n : ℕ} {Pad : Type}
local notation "T" => simulated n
local notation "N" => nativeNetwork n Pad
local notation "E" => NativeWire n Pad

private def rowFibreMap (r : Row n) (e : {u : Wire n//(T).row u=r}) :
    {u : E//(N).row u=.inl r} := ⟨oddWire (Wire n) Pad e.val,congrArg Sum.inl e.property⟩

private def colFibreMap (c : Column n) (e : {u : Wire n//(T).col u=c}) :
    {u : E//(N).col u=.inl c} := ⟨evenWire (Wire n) Pad e.val,congrArg Sum.inl e.property⟩

private theorem rowFibre_bijective (r : Row n) : Function.Bijective (rowFibreMap (Pad:=Pad) r) := by
  constructor
  · intro a b h
    apply Subtype.ext
    exact congrArg Prod.fst (Sum.inl.inj (congrArg Subtype.val h))
  · rintro ⟨⟨u,b⟩|z,h⟩
    · cases b
      · cases h
      · exact ⟨⟨u,Sum.inl.inj h⟩,rfl⟩
    · cases h

private theorem colFibre_bijective (c : Column n) : Function.Bijective (colFibreMap (Pad:=Pad) c) := by
  constructor
  · intro a b h
    apply Subtype.ext
    exact congrArg Prod.fst (Sum.inl.inj (congrArg Subtype.val h))
  · rintro ⟨⟨u,b⟩|z,h⟩
    · cases b
      · exact ⟨⟨u,Sum.inl.inj h⟩,rfl⟩
      · cases h
    · cases h

def dummyRowIndex : Wire n⊕Pad→E
  | .inl e=>evenWire (Wire n) Pad e
  | .inr p=>.inr p

theorem dummy_row_exact (e : E) (z : Wire n⊕Pad) (h : (N).row e=.inr z) :
    e=dummyRowIndex z := by
  rcases e with ⟨u,b⟩|p
  · cases b
    · have hz : Sum.inl u=z := Sum.inr.inj h
      cases hz
      rfl
    · cases h
  · have hz : Sum.inr p=z := Sum.inr.inj h
    cases hz
    rfl

theorem dummy_col_exact (e : E) (z : Wire n⊕Pad) (h : (N).col e=.inr z) :
    e=dummyColIndex z := by
  rcases e with ⟨u,b⟩|p
  · cases b
    · cases h
    · have hz : Sum.inl u=z := Sum.inr.inj h
      cases hz
      rfl
  · have hz : Sum.inr p=z := Sum.inr.inj h
    cases hz
    rfl

theorem real_physical_row_degrees (r : NativeRow n Pad) :
    Nat.card {e : E//(N).row e=r} ≤ 4 := by
  rcases r with r|z
  · rw [←Nat.card_congr (Equiv.ofBijective (rowFibreMap r) (rowFibre_bijective r))]
    exact simulated_row_degrees r
  · let h : {e : E//(N).row e=.inr z} ↪ Unit :=
      ⟨fun _=>(),fun x y _=>Subtype.ext
        ((dummy_row_exact x.val z x.property).trans (dummy_row_exact y.val z y.property).symm)⟩
    exact (Nat.card_le_card_of_injective h h.injective).trans (by simp)

theorem real_physical_col_degrees (c : NativeCol n Pad) :
    Nat.card {e : E//(N).col e=c} ≤ 3 := by
  rcases c with c|z
  · rw [←Nat.card_congr (Equiv.ofBijective (colFibreMap c) (colFibre_bijective c))]
    exact simulated_column_degrees c
  · let h : {e : E//(N).col e=.inr z} ↪ Unit :=
      ⟨fun _=>(),fun x y _=>Subtype.ext
        ((dummy_col_exact x.val z x.property).trans (dummy_col_exact y.val z y.property).symm)⟩
    exact (Nat.card_le_card_of_injective h h.injective).trans (by simp)

#print axioms dummy_row_exact
#print axioms dummy_col_exact
#print axioms real_physical_row_degrees
#print axioms real_physical_col_degrees
end
end A2R45Literal
