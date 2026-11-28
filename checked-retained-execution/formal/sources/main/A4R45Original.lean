import A4R45PrintedSelection
import A4R45NativeA6
import J6ActiveSchedule

/-! A4: on the printed saturated original sparse input, legal consecutive
pairs, exact padding, and the single fixed native slot use the same packing. -/
namespace A4R45Original
open scoped BigOperators Classical Polynomial
open Polynomial Acquisition DenominatorBudget J6R9Recursive J6R10Repack
open J6R10Integral J6R12Repack P11FullPacking AAcquisitionCost
open A4R45LiteralNetwork A4R45FullCell A4R45PrintedLoad A4R45PlantedLabels A4R45SourceTaps
open A4R45PrintedSelection A4R45SourceSchedule A4R45NativeA6 A4R45ColumnNames
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000
noncomputable section

variable {E V₂ V₃ : Type} [Fintype E] [Fintype V₂] [Fintype V₃]

theorem original_printed_single_slot
    (actual : (V₂×Fin 2) ⊕ (V₃×Fin 3) ≃ E×Bool)
    (hBig : 131072 ≤ scale (6*(Fintype.card E+Fintype.card V₃)))
    (locked : ∀ a : ℕ, Fin a→Fin 64)
    (f : ℤ[X]) (hf : f.Monic) (hd : 0<f.natDegree) :
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
      (i : Fin a) (hi : i.val=0),
      P.copies=copies ∧ (∀ w,P.seat w=seat w) ∧ Nat.card W=wireCount ell ∧
      Nat.clog 2 s=ell ∧ J9PrintedSchedule.leafThreshold s ell<Nat.card W ∧
      let p₀ := Fintype.card (Var V₂ V₃ Uplus)+1
      let p := J6ActiveSchedule.childPrecision p₀ a (Nat.card W) (J9PrintedSchedule.rootU ell) (-1)
      boxNatural f 1 p hf (originalSlot P i hi f p₀ p hf) /
        publicFactor (compiledStray seat (columnNames (E:=E) (V₂:=V₂) (V₃:=V₃) word half)) =
          coverCount (side₂ actual) (side₃ actual) := by
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
  obtain ⟨P,seat,i,hi,hcopies,hs,hM,hlog,hactive,htaps,even,hE,hC,hp⟩ :=
    selected_printed_layout actual hBig locked
  refine ⟨P,seat,i,hi,hcopies,hs,hM,hlog,hactive,?_⟩
  let p₀ := Fintype.card (Var V₂ V₃ Uplus)+1
  let p := J6ActiveSchedule.childPrecision p₀ a (Nat.card W) (J9PrintedSchedule.rootU ell) (-1)
  have hE' : 2*Fintype.card E≤Fintype.card W := by
    simpa only [Nat.card_eq_fintype_card] using hE
  have hC' : 2*Fintype.card (OtherColumn (E:=E) (V₂:=V₂) (V₃:=V₃) word half)≤Fintype.card W := by
    simpa only [Nat.card_eq_fintype_card] using hC
  have hp' : 2*Fintype.card W<p := by
    rw [←Nat.card_eq_fintype_card]
    exact hp
  exact actual_A6_integer_then_divide P i hi seat hs f p₀ p hf hd (by dsimp [p₀]; omega)
    (side₂ actual) (side₃ actual) _ htaps even hE' hC' hp'

#print axioms original_printed_single_slot
end
end A4R45Original
