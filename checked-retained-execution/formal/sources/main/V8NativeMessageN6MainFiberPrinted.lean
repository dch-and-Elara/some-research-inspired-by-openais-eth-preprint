import V8NativeMessageN6MainFiberSchedule
import V8NativeMessageN6MainFiberValue

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 14500000

/-! The original printed interval, the actual two fibers and the same
four-clone native evaluator. The exceptional rows are not supplied as
positivity or injectivity receipts. -/
namespace V8NativeMessage.N6.MainFiber
open V8NativeMessage.C3.NativeAssembly.MainScan
open P5MainBalance P5MainBalance.M6 Filter
open scoped BigOperators Classical

noncomputable section

def printedRows (r Q R : ℕ) : ℕ→Prop := outsideInterval (intervalStart r Q R) R

theorem four_clone_schedule_eventually (β : ℕ) :
    ∀ᶠ N : ℕ in atTop,
      2≤mainAlphabet (4*N) ∧ 32≤mainWidth β (4*N) ∧
      6*mainWidth β (4*N)≤mainNodes (4*N) ∧
      printedRows (mainAlphabet (4*N)) (mainNodes (4*N)) (mainWidth β (4*N)) 0 := by
  obtain ⟨n₀,hn⟩ := eventually_atTop.mp (fixed_beta_published_range β)
  apply eventually_atTop.mpr
  refine ⟨n₀,fun N hN=>?_⟩
  have H := hn (4*N) (by omega)
  exact ⟨H.1,H.2.1,H.2.2,zero_is_printed_exceptional _ _ _ H.1 (by omega) H.2.2⟩

variable {W Copy : Type*} [Fintype W] [DecidableEq W] [Fintype Copy]
variable {F : Finset (W×W)} {r Q J R : ℕ}
variable (hreg : ∀ v,GraphCutMoments.degree F v=3)
variable (P : Seating F Copy r Q hreg)
variable (L : CloneTuple F r Q J)

theorem printed_MAIN_zero (hr : 2≤r) (hR : 1≤R) (hfit : 6*R≤Q)
    (hFrame : L.frame=sourceFrame (printedRows r Q R) P L.node L.frame.E (fun _ _=>0))
    (hF : F.Nonempty) (σ : W→Bool) :
    (nativeScan F hreg L σ).2.2=0 ∧ feasible L.frame ∧ ∀ g,
      (∀ x,unrestricted L.frame g x ↔ x=zeroWord L.frame g) ∧
      (Finset.univ : Finset (Word L.frame g)).filter (eligible L.frame g) =
        (if touches L.frame g then ∅ else {zeroWord L.frame g}) := by
  have hk : printedRows r Q R 0 := zero_is_printed_exceptional r Q R hr hR hfit
  exact ⟨(actual_zero_register hreg L _ hk P hFrame hF σ).2,
    actual_zero_fibers hreg L _ hk P hFrame⟩

theorem printed_MAIN_one (hr : 2≤r) (hR : 1≤R) (hfit : 6*R≤Q)
    (hFrame : L.frame=sourceFrame (printedRows r Q R) P L.node L.frame.E
      (allOneAddress (printedRows r Q R) P L.node)) :
    (∀ g j,|L.frame.y g j|≤((r^(2*Q):ℕ):ℤ)) ∧ feasible L.frame ∧ ∀ g,
      (∀ x,unrestricted L.frame g x ↔ x=oneWord L.frame g) ∧
      (Finset.univ : Finset (Word L.frame g)).filter (eligible L.frame g)={oneWord L.frame g} := by
  have hk : printedRows r Q R 0 := zero_is_printed_exceptional r Q R hr hR hfit
  refine ⟨?_,actual_one_fibers hreg L _ hk P hFrame⟩
  rw [hFrame]
  intro g j
  exact one_address_in_printed_box _ P L.node g (rowAt _ j)

#print axioms four_clone_schedule_eventually
#print axioms printed_MAIN_zero
#print axioms printed_MAIN_one
end
end V8NativeMessage.N6.MainFiber
