import A4R45SourceTaps

/-! The sourced A4 chart, with a real full-cell packet packing, including
the signed chosen predecessor of each hard port and the decoded physical
stray factor. There are no assumptions about the value of the slot. -/
namespace A4R45PlantedPacking
open scoped Polynomial BigOperators Classical
open Polynomial Acquisition J6R10Repack P11FullPacking AAcquisitionCost
open A4R45LiteralNetwork A4R45FullCell A4R45PlantedLabels A4R45ColumnNames
open A4R45HardPairs A4R45SourceTaps A4R45PrintedLoad A4R45PhysicalFullChart
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4700000

noncomputable section
variable {E V₂ V₃ : Type} [Fintype E] [Fintype V₂] [Fintype V₃]
variable {a copies : ℕ}
variable (word : Fin a→Fin 64) (half : ℕ)
local notation "Vbase" => Var V₂ V₃ (E⊕V₃)
local notation "Uplus" => More (V₂:=V₂) (V₃:=V₃) (U:=E⊕V₃) word half
local notation "Wplus" => Wire V₂ V₃ Uplus
local notation "Nplus" => network (V₂:=V₂) (V₃:=V₃) (U:=Uplus)
local notation "Cols" => columnNames (E:=E) (V₂:=V₂) (V₃:=V₃) word half

def printed_mask (a copies : ℕ) : MaskFamily a copies (Fin 64) := fun _ _ _=>false

theorem actual_full_padded_cover_packing
    (actual : (V₂×Fin 2)⊕(V₃×Fin 3) ≃ E×Bool)
    (ha : 0<a) (room : Fintype.card Vbase≤half) (full : 2*half=copies*2^a)
    (pairs : Fintype.card (HPort V₂ V₃)≤copies*2^(a-1)) :
    ∃ (P : PhysicalPacking Nplus a (Fin 64)) (seat : Wplus ≃ Physical a P.copies (Fin 64)),
      (∀ w,P.seat w=seat w) ∧ P.copies=copies ∧
      Nat.card Wplus = wordCells a*(copies*2^a) ∧
      (∀ (r : CoverRow V₂ V₃ Uplus) (j : CoverPort r),
        (wirePred seat (⟨r,j⟩,true)).map (Cols ∘ Prod.fst) =
          coverSources (side₂ actual) (side₃ actual) (compiledStray seat Cols) r j) := by
  let mask := printed_mask a copies
  obtain ⟨seat,chart,paired⟩ := legal_padded_actual_pair_order word half ha mask
    (reservePair actual) room full pairs
  have hcard := Nat.card_congr (seat.trans (fullSlotChart mask))
  have exactCount : Nat.card Wplus=wordCells a*(copies*2^a) := by
    simpa only [Nat.card_prod,Nat.card_fin,total_cells,Fintype.card_fin,wordCells] using hcard
  have padded : Nat.card (Cell (Fin a) (Fin 64))*(copies*2^a)≤3*Nat.card Wplus := by
    rw [total_cells,Fintype.card_fin]
    change wordCells a*(copies*2^a) ≤ 3*Nat.card Wplus
    rw [←exactCount]
    omega
  let P := install_full_chart Nplus (rowWords word half) (colWords word half) mask seat chart padded
  refine ⟨P,seat,fun _=>rfl,rfl,exactCount,?_⟩
  exact actual_cover_taps word half actual seat paired

theorem variable_host_room_at_printed_parameters
    (actual : (V₂×Fin 2)⊕(V₃×Fin 3) ≃ E×Bool)
    (hBig : 131072 ≤ scale (6*(Fintype.card E+Fintype.card V₃))) :
    let ell:=scale (6*(Fintype.card E+Fintype.card V₃))
    let a:=A4R45PrintedLoad.bits ell 131072
    let copies:=packetCopies ell a
    let half:=copies*2^(a-1)
    0<a ∧ Fintype.card Vbase≤half ∧ 2*half=copies*2^a ∧
      Fintype.card (HPort V₂ V₃)≤copies*2^(a-1) ∧
      wordCells a*(copies*2^a)=wireCount ell := by
  dsimp only
  let k:=Fintype.card E+Fintype.card V₃
  let ell:=scale (6*k)
  let a:=A4R45PrintedLoad.bits ell 131072
  let copies:=packetCopies ell a
  let half:=copies*2^(a-1)
  have guards := printed_diagonal_room (6*k) 131072 (by decide) hBig
  have hA : 0<a := guards.1
  have hfull : 2*half=copies*2^a := by
    unfold half
    rw [←Nat.mul_assoc,Nat.mul_comm 2 copies,Nat.mul_assoc,←pow_succ',Nat.sub_add_cancel hA]
  have hroom : Fintype.card Vbase ≤ half := by
    have hw := (exact_unpadded_size (U:=E⊕V₃) actual
      (by simp)).1
    rw [Fintype.card_prod,Fintype.card_bool] at hw
    have load : 6*k≤2*half := by rw [hfull,guards.2.2.2.2]; exact guards.2.2.1
    omega
  have need : Fintype.card (HPort V₂ V₃)≤copies*2^(a-1) := by
    rw [hard_pair_quota actual]
    exact hard_pairs_fit k ell a hA guards.2.1.le guards.2.2.1
  refine ⟨hA,hroom,hfull,need,?_⟩
  rw [guards.2.2.2.2]
  exact guards.2.2.2.1

#print axioms actual_full_padded_cover_packing
#print axioms variable_host_room_at_printed_parameters
end
end A4R45PlantedPacking
