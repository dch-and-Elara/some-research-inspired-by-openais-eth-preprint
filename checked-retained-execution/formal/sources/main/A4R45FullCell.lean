import A4R45LiteralNetwork
import A4R45PrintedLoad

/-! A4 full-cell padding. Each added coordinate selects one genuine negative
unary formula variable, and its subdivision makes two wires in precisely
the requested ordered label cell. -/
namespace A4R45FullCell
open A4R45LiteralNetwork Acquisition J6R10Repack
set_option autoImplicit false
set_option warningAsError true

variable {Cell : Type*} [DecidableEq Cell]

def capacity (diag c : Cell) (half core : ℕ) : ℕ :=
  half - if c=diag then core else 0

abbrev Filler (diag : Cell) (half core : ℕ) :=
  Σ c : Cell, Fin (capacity diag c half core)

def cellOf {Core : Type*} (diag : Cell) (half core : ℕ) :
    Core ⊕ Filler diag half core → Cell
  | .inl _ => diag
  | .inr x => x.1

def padFibre (diag c : Cell) (half core : ℕ) :
    {p : Filler diag half core // p.1=c} ≃ Fin (capacity diag c half core) where
  toFun p := Fin.cast (congrArg (fun d=>capacity diag d half core) p.2) p.val.2
  invFun q := ⟨⟨c,q⟩,rfl⟩
  left_inv p := by rcases p with ⟨⟨v,q⟩,rfl⟩; rfl
  right_inv _ := rfl

def occurrenceFibre {Core : Type*} (diag c : Cell) (half core : ℕ) :
    {p : Core ⊕ Filler diag half core // cellOf diag half core p=c} ≃
      ({_p : Core // diag=c} ⊕ {p : Filler diag half core // p.1=c}) where
  toFun
    | ⟨.inl x,h⟩ => .inl ⟨x,h⟩
    | ⟨.inr x,h⟩ => .inr ⟨x,h⟩
  invFun
    | .inl ⟨x,h⟩ => ⟨.inl x,h⟩
    | .inr ⟨x,h⟩ => ⟨.inr x,h⟩
  left_inv
    | ⟨.inl _,_⟩ => rfl
    | ⟨.inr _,_⟩ => rfl
  right_inv
    | .inl ⟨_,_⟩ => rfl
    | .inr ⟨_,_⟩ => rfl

theorem exact_half_load {Core : Type*} [Fintype Core] [Fintype Cell]
    (diag c : Cell) (half : ℕ) (room : Fintype.card Core≤half) :
    Nat.card {p : Core ⊕ Filler diag half (Fintype.card Core) //
      cellOf diag half (Fintype.card Core) p=c}=half := by
  classical
  let n := Fintype.card Core
  letI : Fintype {p : Core // diag=c} := Fintype.ofFinite _
  letI : Fintype {p : Filler diag half n // p.1=c} := Fintype.ofFinite _
  letI : Fintype {p : Core ⊕ Filler diag half n // cellOf diag half n p=c} :=
    Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Fintype.card_congr (occurrenceFibre diag c half n),
    Fintype.card_sum, Fintype.card_congr (padFibre diag c half n), Fintype.card_fin]
  by_cases h : diag=c
  · let equiv : {p : Core // diag=c} ≃ Core :=
      Equiv.subtypeUnivEquiv fun _ => h
    rw [Fintype.card_congr equiv]
    simp only [capacity,h,if_true]
    exact Nat.add_sub_of_le room
  · letI : IsEmpty {p : Core // diag=c} := ⟨fun q => h q.property⟩
    have h' : c≠diag := Ne.symm h
    simp [capacity,h']

/-- Planted and filler occurrence names give two subdivision wires per
fresh variable; the original three types of hard clauses remain intact. -/
def paddedVars {V₂ V₃ U : Type*} (diag : Cell) (half core : ℕ) :
    Var V₂ V₃ (U ⊕ Filler diag half core) ≃
      Var V₂ V₃ U ⊕ Filler diag half core where
  toFun
    | ⟨.inl v,j⟩ => .inl ⟨.inl v,j⟩
    | ⟨.inr (.inl v),j⟩ => .inl ⟨.inr (.inl v),j⟩
    | ⟨.inr (.inr (.inl v)),j⟩ => .inl ⟨.inr (.inr (.inl v)),j⟩
    | ⟨.inr (.inr (.inr (.inl v))),j⟩ => .inl ⟨.inr (.inr (.inr v)),j⟩
    | ⟨.inr (.inr (.inr (.inr pad))),_⟩ => .inr pad
  invFun
    | .inl ⟨.inl v,j⟩ => ⟨.inl v,j⟩
    | .inl ⟨.inr (.inl v),j⟩ => ⟨.inr (.inl v),j⟩
    | .inl ⟨.inr (.inr (.inl v)),j⟩ => ⟨.inr (.inr (.inl v)),j⟩
    | .inl ⟨.inr (.inr (.inr v)),j⟩ => ⟨.inr (.inr (.inr (.inl v))),j⟩
    | .inr pad => ⟨.inr (.inr (.inr (.inr pad))),()⟩
  left_inv
    | ⟨.inl _,_⟩ => rfl
    | ⟨.inr (.inl _),_⟩ => rfl
    | ⟨.inr (.inr (.inl _)),_⟩ => rfl
    | ⟨.inr (.inr (.inr (.inl _))),_⟩ => rfl
    | ⟨.inr (.inr (.inr (.inr _))),p⟩ =>
      have hp : p=() := Subsingleton.elim (α:=Unit) _ _
      by cases hp; rfl
  right_inv
    | .inl ⟨.inl _,_⟩ => rfl
    | .inl ⟨.inr (.inl _),_⟩ => rfl
    | .inl ⟨.inr (.inr (.inl _)),_⟩ => rfl
    | .inl ⟨.inr (.inr (.inr _)),_⟩ => rfl
    | .inr _ => rfl

theorem exact_padded_wire_load {V₂ V₃ U : Type*}
    [Fintype Cell] [Fintype V₂] [Fintype V₃] [Fintype U]
    (diag c : Cell) (half : ℕ) (room : Fintype.card (Var V₂ V₃ U)≤half) :
    let n := Fintype.card (Var V₂ V₃ U)
    Nat.card {w : Wire V₂ V₃ (U ⊕ Filler diag half n) //
      cellOf diag half n (paddedVars diag half n w.1)=c}=2*half := by
  dsimp only
  let n:=Fintype.card (Var V₂ V₃ U)
  let t:=paddedVars (V₂:=V₂) (V₃:=V₃) (U:=U) diag half n
  let e : {w : Wire V₂ V₃ (U ⊕ Filler diag half n) // cellOf diag half n (t w.1)=c} ≃
      {p : Var V₂ V₃ U ⊕ Filler diag half n // cellOf diag half n p=c} × Bool := {
    toFun := fun w => (⟨t w.1.1,w.2⟩,w.1.2)
    invFun := fun w => ⟨(t.symm w.1.val,w.2),by simpa only [Equiv.apply_symm_apply] using w.1.2⟩
    left_inv := fun w => Subtype.ext (Prod.ext (t.symm_apply_apply w.1.1) rfl)
    right_inv := fun w => Prod.ext (Subtype.ext (t.apply_symm_apply w.1.val)) rfl }
  change Nat.card _ = _
  rw [Nat.card_congr e, Nat.card_prod, exact_half_load diag c half room,
    Nat.card_eq_fintype_card, Fintype.card_bool, Nat.mul_comm]

#print axioms exact_half_load
#print axioms paddedVars
#print axioms exact_padded_wire_load
end A4R45FullCell
