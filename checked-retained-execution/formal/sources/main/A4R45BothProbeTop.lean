import A4R45Original
import A4R45OriginalFallback

/-! A4 direct and omitted-zero branches use one selected real packing,
one source file, one printed word precision and the same public divisor. -/
namespace A4R45BothProbeTop
open scoped Polynomial Classical
open Polynomial Acquisition J6R9Recursive J6R10Repack J6R12Repack P11FullPacking
open AAcquisitionCost A4R45LiteralNetwork A4R45PrintedLoad A4R45PlantedLabels
open A4R45SourceTaps A4R45ColumnNames A4R45NativeA6 A4R45Original A4R45OriginalFallback
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000
noncomputable section

variable {E V₂ V₃ : Type} [Fintype E] [Fintype V₂] [Fintype V₃]

theorem original_A4_either_native_probe_roster
    (actual : (V₂×Fin 2) ⊕ (V₃×Fin 3) ≃ E×Bool)
    (hBig : 131072 ≤ scale (6*(Fintype.card E+Fintype.card V₃)))
    (locked : ∀ a : ℕ, Fin a→Fin 64)
    (f : ℤ[X]) (hf : f.Monic) (hd : 0<f.natDegree)
    [Fact (Irreducible (NativeProbeRing.residuePoly f))] :
    let ell := scale (6*(Fintype.card E+Fintype.card V₃))
    let a := A4R45PrintedLoad.bits ell 131072
    let copies := packetCopies ell a
    let half := copies*2^(a-1)
    let word := locked a
    let Uplus := More (V₂:=V₂) (V₃:=V₃) (U:=E⊕V₃) word half
    let W := Wire V₂ V₃ Uplus
    let N := network (V₂:=V₂) (V₃:=V₃) (U:=Uplus)
    let p₀ := Fintype.card (Var V₂ V₃ Uplus)+1
    let p := J6ActiveSchedule.childPrecision p₀ a (Nat.card W) (J9PrintedSchedule.rootU ell) (-1)
    ∃ (P : PhysicalPacking N a (Fin 64)) (seat : W ≃ Physical a P.copies (Fin 64))
      (i : Fin a) (hi : i.val=0),
      P.copies=copies ∧ (∀ w,P.seat w=seat w) ∧ Nat.card W=wireCount ell ∧
      Nat.clog 2 (A4R45SourceSchedule.sourceSize V₂ V₃ Uplus)=ell ∧
      J9PrintedSchedule.leafThreshold (A4R45SourceSchedule.sourceSize V₂ V₃ Uplus) ell<Nat.card W ∧
      let factor := publicFactor (compiledStray seat (columnNames (E:=E) (V₂:=V₂) (V₃:=V₃) word half))
      let target := coverCount (side₂ actual) (side₃ actual)
      boxNatural f 1 p hf (originalSlot P i hi f p₀ p hf) / factor = target ∧
      ∀ b : J6R14ZeroMode.Prescribed f (J9PrintedSchedule.degreeBound (Fintype.card W) (2^a)),
        boxNatural f 1 p hf (noZeroSlot P i hi f p₀ p hf b) / factor = target := by
  classical
  dsimp only
  obtain ⟨P,seat,i,hi,pc,ps,hM,hlog,active,read⟩ :=
    original_printed_single_slot actual hBig locked f hf hd
  refine ⟨P,seat,i,hi,pc,ps,hM,hlog,active,read,?_⟩
  intro b
  rw [no_zero_recovers_same_original_slot P i hi f _ _ hf ?_ hd b]
  · exact read
  · unfold J6ActiveSchedule.childPrecision J9PrintedSchedule.precision
    omega

#print axioms original_A4_either_native_probe_roster
end
end A4R45BothProbeTop
