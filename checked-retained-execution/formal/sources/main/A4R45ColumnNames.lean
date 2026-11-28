import A4R45PlantedLabels
import A4R45HardPairs

/-! Names of the actual subdivision columns. Designated columns are the
two-port occurrences of the extra negative unary rows for each intended
edge/auxiliary bit. All other real columns are represented separately. -/
namespace A4R45ColumnNames
open Acquisition A4R45LiteralNetwork A4R45FullCell A4R45ActualPairs
open A4R45PlantedLabels A4R45HardPairs
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

noncomputable section
variable {E V₂ V₃ G : Type*} [LinearOrder G] {a : ℕ}
variable [Fintype E] [Fintype V₂] [Fintype V₃]
local notation "Ubase" => E⊕V₃
variable (word : Fin a→G) (half : ℕ)
local notation "Uplus" => More (V₂:=V₂) (V₃:=V₃) (U:=Ubase) word half
local notation "Vplus" => Var V₂ V₃ Uplus

def designatedColumn (e : Ubase) : Vplus :=
  (embedOriginal word half (designated e,false)).1

theorem designatedColumn_injective : Function.Injective
    (designatedColumn (E:=E) (V₂:=V₂) (V₃:=V₃) word half) := by
  intro x y h
  apply designated_injective (V₂:=V₂)
  have hw : embedOriginal word half ((designated x:DVar V₂ V₃ E),false) =
      embedOriginal word half (designated y,false) := Prod.ext h rfl
  exact congrArg Prod.fst ((embedOriginal word half).injective hw)

abbrev OtherColumn := {v : Vplus //
  v ∉ Set.range (designatedColumn (E:=E) (V₂:=V₂) (V₃:=V₃) word half)}

def columnNames : Vplus ≃ CoverCol E V₃ (OtherColumn (E:=E) (V₂:=V₂) (V₃:=V₃) word half) := by
  classical
  let tag := designatedColumn (E:=E) (V₂:=V₂) (V₃:=V₃) word half
  let picked := Equiv.ofInjective tag (designatedColumn_injective word half)
  exact (Equiv.Set.sumCompl (Set.range tag)).symm.trans
    ((Equiv.sumCongr picked.symm (Equiv.refl _)).trans (Equiv.sumAssoc _ _ _))

theorem columnName_designated (e : Ubase) :
    columnNames word half (designatedColumn (V₂:=V₂) word half e) =
      Sum.elim Sum.inl (Sum.inr ∘ Sum.inl) e := by
  classical
  let f := designatedColumn (E:=E) (V₂:=V₂) (V₃:=V₃) word half
  let picked := Equiv.ofInjective f (designatedColumn_injective word half)
  have hm : f e∈Set.range f := ⟨e,rfl⟩
  change (Equiv.sumAssoc _ _ _) ((Equiv.sumCongr picked.symm (Equiv.refl _))
    ((Equiv.Set.sumCompl (Set.range f)).symm (f e)))=_
  rw [Equiv.Set.sumCompl_symm_apply_of_mem hm]
  change (Equiv.sumAssoc _ _ _) (Sum.inl (picked.symm (picked e)))=_
  rw [Equiv.symm_apply_apply]
  cases e <;> rfl

theorem columnName_other (z : OtherColumn (E:=E) (V₂:=V₂) (V₃:=V₃) word half) :
    columnNames word half z.val = .inr (.inr z) := by
  classical
  let f := designatedColumn (E:=E) (V₂:=V₂) (V₃:=V₃) word half
  let picked := Equiv.ofInjective f (designatedColumn_injective word half)
  change (Equiv.sumAssoc _ _ _) ((Equiv.sumCongr picked.symm (Equiv.refl _))
    ((Equiv.Set.sumCompl (Set.range f)).symm z.val))=_
  rw [Equiv.Set.sumCompl_symm_apply_of_notMem z.property]
  rfl

theorem actual_card_hard_column_le (c : E) :
    columnNames word half (designatedColumn (V₂:=V₂) (V₃:=V₃) word half (.inl c))=.inl c :=
  columnName_designated word half (.inl c)

#print axioms designatedColumn_injective
#print axioms columnName_designated
#print axioms columnName_other
end
end A4R45ColumnNames
