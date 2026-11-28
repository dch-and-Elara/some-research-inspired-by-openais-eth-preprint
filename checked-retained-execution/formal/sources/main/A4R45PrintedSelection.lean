import A4R45PlantedPacking
import A4R45SourceSchedule
import J6ActiveSchedule

/-! A4: on the printed saturated original sparse input, legal consecutive
pairs, exact padding, and the single fixed native slot use the same packing. -/
namespace A4R45PrintedSelection
open scoped BigOperators Classical Polynomial
open Polynomial Acquisition DenominatorBudget J6R9Recursive J6R10Repack
open P11FullPacking AAcquisitionCost
open A4R45LiteralNetwork A4R45FullCell A4R45PrintedLoad A4R45PlantedLabels A4R45SourceTaps
open A4R45PlantedPacking A4R45SourceSchedule A4R45ColumnNames
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000
noncomputable section

variable {E V₂ V₃ : Type} [Fintype E] [Fintype V₂] [Fintype V₃]

theorem selected_printed_layout
    (actual : (V₂×Fin 2) ⊕ (V₃×Fin 3) ≃ E×Bool)
    (hBig : 131072 ≤ scale (6*(Fintype.card E+Fintype.card V₃)))
    (locked : ∀ a : ℕ, Fin a→Fin 64) :
    let m := 6*(Fintype.card E+Fintype.card V₃)
    let ell := scale m
    let a := A4R45PrintedLoad.bits ell 131072
    let copies := packetCopies ell a
    let half := copies*2^(a-1)
    let word := locked a
    let Uplus := More (V₂:=V₂) (V₃:=V₃) (U:=E⊕V₃) word half
    let W := Wire V₂ V₃ Uplus
    let s := sourceSize V₂ V₃ Uplus
    let N := network (V₂:=V₂) (V₃:=V₃) (U:=Uplus)
    ∃ (P : PhysicalPacking N a (Fin 64)) (seat : W ≃ Physical a P.copies (Fin 64))
      (i : Fin a),
      i.val=0 ∧ P.copies=copies ∧ (∀ w,P.seat w=seat w) ∧ Nat.card W=wireCount ell ∧
      Nat.clog 2 s=ell ∧ J9PrintedSchedule.leafThreshold s ell<Nat.card W ∧
      (∀ (r : CoverRow V₂ V₃ Uplus) (j : CoverPort r),
        (wirePred seat (⟨r,j⟩,true)).map
          (columnNames (E:=E) (V₂:=V₂) (V₃:=V₃) word half ∘ Prod.fst) =
          coverSources (side₂ actual) (side₃ actual)
            (compiledStray seat (columnNames (E:=E) (V₂:=V₂) (V₃:=V₃) word half)) r j) ∧
      Even (Fintype.card V₃) ∧
      2*Fintype.card E≤Nat.card W ∧
      2*Fintype.card (OtherColumn (E:=E) (V₂:=V₂) (V₃:=V₃) word half) ≤ Nat.card W ∧
      2*Nat.card W<J6ActiveSchedule.childPrecision
        (Fintype.card (Var V₂ V₃ Uplus)+1) a (Nat.card W) (J9PrintedSchedule.rootU ell) (-1) := by
  classical
  dsimp only
  let m := 6*(Fintype.card E+Fintype.card V₃)
  let ell := scale m
  let a := A4R45PrintedLoad.bits ell 131072
  let copies := packetCopies ell a
  let half := copies*2^(a-1)
  let word := locked a
  let Uplus := More (V₂:=V₂) (V₃:=V₃) (U:=E⊕V₃) word half
  let W := Wire V₂ V₃ Uplus
  obtain ⟨ha,hroom,hfull,hpair,hcell⟩ := variable_host_room_at_printed_parameters actual hBig
  obtain ⟨P,seat,hs,hcopies,hcount,htaps⟩ :=
    actual_full_padded_cover_packing word half actual ha hroom hfull hpair
  have hMnat : Nat.card W=wireCount ell := hcount.trans hcell
  have hM : Fintype.card W=wireCount ell := by simpa only [Nat.card_eq_fintype_card] using hMnat
  obtain ⟨hBare,hSmall⟩ := exact_unpadded_size (U:=E⊕V₃) actual (by simp)
  change sourceSize V₂ V₃ (E⊕V₃) ≤ Fintype.card (Wire V₂ V₃ (E⊕V₃)) at hSmall
  have hlog : Nat.clog 2 (sourceSize V₂ V₃ Uplus)=ell := by
    exact (literal_formula_sets_printed_scale _ _ _ hBare (hSmall.trans_eq hBare) hM).2
  have hsz : sourceSize V₂ V₃ Uplus ≤ Nat.card W := by
    rw [Nat.card_eq_fintype_card]
    unfold sourceSize
    rw [Fintype.card_prod,Fintype.card_bool,formula_clause_count,occurrence_count]
    simp only [CoverRow,Fintype.card_sum]
    omega
  have hEz : 2*Fintype.card E≤Fintype.card W := by
    have h := Fintype.card_le_of_injective
      (fun e : E => (designatedColumn (V₂:=V₂) (V₃:=V₃) word half (.inl e))) (by
        intro x y eq
        exact Sum.inl.inj (designatedColumn_injective word half eq))
    change _ ≤ Fintype.card (Var V₂ V₃ Uplus) at h
    change _ ≤ Fintype.card (Var V₂ V₃ Uplus × Bool)
    rw [Fintype.card_prod,Fintype.card_bool,Nat.mul_comm (Fintype.card (Var V₂ V₃ Uplus)) 2]
    exact Nat.mul_le_mul_left 2 h
  have hOther : 2*Fintype.card (OtherColumn (E:=E) (V₂:=V₂) (V₃:=V₃) word half)≤Fintype.card W := by
    have h := Fintype.card_le_of_injective
      (Subtype.val : OtherColumn (E:=E) (V₂:=V₂) (V₃:=V₃) word half → _) Subtype.val_injective
    change _ ≤ Fintype.card (Var V₂ V₃ Uplus) at h
    change _ ≤ Fintype.card (Var V₂ V₃ Uplus × Bool)
    rw [Fintype.card_prod,Fintype.card_bool,Nat.mul_comm (Fintype.card (Var V₂ V₃ Uplus)) 2]
    exact Nat.mul_le_mul_left 2 h
  have bigEll : 131072≤ell := hBig
  have hm : 2≤Nat.card W := by
    rw [hMnat]
    exact Nat.one_lt_two_pow (by omega : ell≠0)
  let i : Fin a := ⟨0,ha⟩
  refine ⟨P,seat,i,rfl,hcopies,hs,hMnat,hlog,genuine_root_is_active _ _ _ hsz hm (by omega),
    htaps,(handshake_even actual).2,?_,?_,?_⟩
  · rw [Nat.card_eq_fintype_card]
    exact hEz
  · rw [Nat.card_eq_fintype_card]
    exact hOther
  · unfold J6ActiveSchedule.childPrecision
    have hpos : 0<Nat.card W := lt_of_lt_of_le (by decide : 0<2) hm
    exact actual_p_cap _ _ _ (Nat.card W) _ hpos

#print axioms selected_printed_layout
end
end A4R45PrintedSelection
