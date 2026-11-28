import V8NativeMessageN6MainFiberFrame
import V8NativeMessageN6MainFiberValueCore

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 14500000

/-! Bind the just-proved zero scan value and extreme words to the
literal printed measurements on this existing N2 CloneTuple. -/
namespace V8NativeMessage.N6.MainFiber
open V8NativeMessage.C3.NativeAssembly.MainScan
open scoped BigOperators Classical Polynomial
open Polynomial

noncomputable section
variable {W Copy : Type*} [Fintype W] [DecidableEq W] [Fintype Copy]
variable {F : Finset (W×W)} {r Q J : ℕ}
variable (hreg : ∀ v,GraphCutMoments.degree F v=3)
variable (L : CloneTuple F r Q J)

theorem actual_zero_fibers (keep : ℕ→Prop) (hk : keep 0) (P : Seating F Copy r Q hreg)
    (hFrame : L.frame=sourceFrame keep P L.node L.frame.E (fun _ _=>0)) :
    feasible L.frame ∧ ∀ g,
      (∀ x,unrestricted L.frame g x ↔ x=zeroWord L.frame g) ∧
      (Finset.univ : Finset (Word L.frame g)).filter (eligible L.frame g) =
        (if touches L.frame g then ∅ else {zeroWord L.frame g}) := by
  have hC : positiveCover L.frame := hFrame.symm ▸ source_frame_positive keep hk P L.node L.frame.E _
  have h0 : zeroTarget L.frame := hFrame.symm ▸ zero_source_target keep P L.node L.frame.E
  refine ⟨zero_feasible _ h0,fun g=>⟨zero_unrestricted_iff _ hC h0 g,?_⟩⟩
  by_cases h : touches L.frame g
  · rw [if_pos h]
    ext x
    simp [zero_eligible_iff L.frame hC h0 g x,h]
  · rw [if_neg h]
    ext x
    simp [zero_eligible_iff L.frame hC h0 g x,h]

theorem actual_one_fibers (keep : ℕ→Prop) (hk : keep 0) (P : Seating F Copy r Q hreg)
    (hFrame : L.frame=sourceFrame keep P L.node L.frame.E (allOneAddress keep P L.node)) :
    feasible L.frame ∧ ∀ g,
      (∀ x,unrestricted L.frame g x ↔ x=oneWord L.frame g) ∧
      (Finset.univ : Finset (Word L.frame g)).filter (eligible L.frame g)={oneWord L.frame g} := by
  have hC : positiveCover L.frame := hFrame.symm ▸ source_frame_positive keep hk P L.node L.frame.E _
  have h1 : oneTarget L.frame := hFrame.symm ▸ one_source_target keep P L.node L.frame.E
  refine ⟨one_feasible _ h1,fun g=>⟨one_unrestricted_iff _ hC h1 g,?_⟩⟩
  ext x
  simp [one_eligible_iff L.frame hC h1 g x]

theorem actual_zero_register (keep : ℕ→Prop) (hk : keep 0) (P : Seating F Copy r Q hreg)
    (hFrame : L.frame=sourceFrame keep P L.node L.frame.E (fun _ _=>0))
    (hF : F.Nonempty) (σ : W→Bool) :
    feasible L.frame ∧ (nativeScan F hreg L σ).2.2=0 := by
  have hC : positiveCover L.frame := hFrame.symm ▸ source_frame_positive keep hk P L.node L.frame.E _
  have h0 : zeroTarget L.frame := hFrame.symm ▸ zero_source_target keep P L.node L.frame.E
  refine ⟨zero_feasible _ h0,?_⟩
  by_cases hE : L.frame.E.Nonempty
  · exact nativeScan_zero_restricted hreg L hC h0 hE σ
  · exact nativeScan_zero_edge_OR hreg L hC h0 (Finset.not_nonempty_iff_eq_empty.mp hE) hF σ

#print axioms actual_zero_fibers
#print axioms actual_one_fibers
#print axioms actual_zero_register
end
end V8NativeMessage.N6.MainFiber
