import A4R45FullCell
import A4R45ActualPairs

/-! The generated sparse formula has exactly the prescribed real wire
load in each original ordered word cell, including the filled diagonal
plant. No fake zero wires are used for either side of a literal edge. -/
namespace A4R45PlantedLabels
open Acquisition J6R10Repack P11FullPacking AAcquisitionCost
open A4R45LiteralNetwork A4R45FullCell A4R45ActualPairs
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2800000

variable {V₂ V₃ U G : Type*} {a copies : ℕ} [LinearOrder G]
variable [Fintype V₂] [Fintype V₃] [Fintype U]

local notation "Core" => Var V₂ V₃ U
local notation "n" => Fintype.card Core
local notation "CellWord" => Cell (Fin a) G

abbrev More (word : Fin a→G) (half : ℕ) :=
  U ⊕ Filler (diagCell word) half n

def labelClause (word : Fin a→G) (half : ℕ) :
    CoverRow V₂ V₃ (More (V₂:=V₂) (V₃:=V₃) (U:=U) word half) → CellWord
  | .inr (.inr (.inr (.inr d))) => d.1
  | _ => diagCell word

def labelVar (word : Fin a→G) (half : ℕ)
    (v : Var V₂ V₃ (More (V₂:=V₂) (V₃:=V₃) (U:=U) word half)) : CellWord :=
  labelClause word half v.1

theorem labelVar_cellOf (word : Fin a→G) (half : ℕ)
    (v : Var V₂ V₃ (More (V₂:=V₂) (V₃:=V₃) (U:=U) word half)) :
    labelVar word half v=cellOf (diagCell word) half n (paddedVars (diagCell word) half n v) := by
  rcases v with ⟨r,j⟩
  rcases r with r|r
  · rfl
  rcases r with r|r
  · rfl
  rcases r with r|r
  · rfl
  rcases r with r|r <;> rfl

def rowWords (word : Fin a→G) (half : ℕ) :
    Row V₂ V₃ (More (V₂:=V₂) (V₃:=V₃) (U:=U) word half) → Fin a→G :=
  Sum.elim (fun r i => (labelClause word half r i).1) (fun v i => (labelVar word half v i).1)

def colWords (word : Fin a→G) (half : ℕ)
    (v : Var V₂ V₃ (More (V₂:=V₂) (V₃:=V₃) (U:=U) word half)) (i : Fin a) : G :=
  (labelVar word half v i).2

theorem declared_is_actual (word : Fin a→G) (half : ℕ)
    (w : Wire V₂ V₃ (More (V₂:=V₂) (V₃:=V₃) (U:=U) word half)) :
    declaredCell network (rowWords word half) (colWords word half) w =
      cellOf (diagCell word) half n (paddedVars (diagCell word) half n w.1) := by
  rw [←labelVar_cellOf word half w.1]
  rcases w with ⟨v,b⟩
  cases b <;> rfl

def embedOriginal (word : Fin a→G) (half : ℕ) :
    Wire V₂ V₃ U ↪ Wire V₂ V₃ (More (V₂:=V₂) (V₃:=V₃) (U:=U) word half) where
  toFun w := ((paddedVars (diagCell word) half n).symm (.inl w.1),w.2)
  inj' := by
    intro x y h
    apply Prod.ext
    · exact Sum.inl.inj ((paddedVars (diagCell word) half n).symm.injective (congrArg Prod.fst h))
    · exact congrArg (fun z : Wire V₂ V₃ (More (V₂:=V₂) (V₃:=V₃) (U:=U) word half) => z.2) h

theorem all_original_wires_diagonal (word : Fin a→G) (half : ℕ) (w : Wire V₂ V₃ U) :
    declaredCell network (rowWords word half) (colWords word half) (embedOriginal word half w)
      = diagCell word := by
  rw [declared_is_actual]
  simp [embedOriginal,cellOf]

theorem every_actual_cell_full [Fintype G] (word : Fin a→G) (half : ℕ)
    (room : n≤half) (c : CellWord) :
    Nat.card {w : Wire V₂ V₃ (More (V₂:=V₂) (V₃:=V₃) (U:=U) word half) //
      declaredCell network (rowWords word half) (colWords word half) w=c} = 2*half := by
  let Typ := Wire V₂ V₃ (More (V₂:=V₂) (V₃:=V₃) (U:=U) word half)
  let e : {w : Typ // declaredCell network (rowWords word half) (colWords word half) w=c} ≃
      {w : Typ // cellOf (diagCell word) half n (paddedVars (diagCell word) half n w.1)=c} :=
    Equiv.subtypeEquivRight (fun w => by rw [declared_is_actual word half w])
  exact (Nat.card_congr e).trans (exact_padded_wire_load (V₂:=V₂) (V₃:=V₃) (U:=U)
    (diagCell word) c half room)

theorem legal_padded_actual_pair_order {Hard : Type*} [Fintype Hard] [Fintype G]
    (word : Fin a→G) (half : ℕ) (ha : 0<a)
    (mask : MaskFamily a copies G) (original : Hard×Bool ↪ Wire V₂ V₃ U)
    (room : n≤half) (full : 2*half=copies*2^a)
    (pairs : Fintype.card Hard≤copies*2^(a-1)) :
    ∃ seat : Wire V₂ V₃ (More (V₂:=V₂) (V₃:=V₃) (U:=U) word half) ≃ Physical a copies G,
      (∀ w, physicalCell mask (seat w)=declaredCell network (rowWords word half) (colWords word half) w) ∧
      (∀ j, wirePred seat (embedOriginal word half (original (j,true))) =
        some (embedOriginal word half (original (j,false)))) := by
  let hard := original.trans (embedOriginal word half)
  have hc (c : CellWord) := (every_actual_cell_full (V₂:=V₂) (V₃:=V₃) (U:=U)
      word half room c).trans full
  exact original_diagonal_actual_pairs network (rowWords word half) (colWords word half)
    mask word ha hard pairs (fun _ => all_original_wires_diagonal _ _ _) hc

#print axioms declared_is_actual
#print axioms all_original_wires_diagonal
#print axioms every_actual_cell_full
#print axioms legal_padded_actual_pair_order
end A4R45PlantedLabels
