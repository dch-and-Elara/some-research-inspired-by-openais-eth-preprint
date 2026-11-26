import P5HybridMainOnlyTerminal
import P5HybridMainOnlyPrintedGuards

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

namespace Paper5.HybridMainOnly
open scoped Classical
open Paper5.HybridClosure Paper5.HybridClosure.Printed
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
variable (E : Finset (V×V)) (cubic : ∀ v,GraphCutMoments.degree E v=3)
variable (loopless : ∀v,(v,v)∉E)
local notation "N" => (Fintype.card (TriVertex V))

theorem actual_printed_main_only (ready : PrintedMainOnlyReady N)
    (t u : Fin (mainQ N)) (tu : t≠u) :
    letI : Nonempty (Fin (mainR N)) := ⟨⟨0,by have := ready.alphabet; omega⟩⟩
    ∃ z : SourcePrimitive E cubic (Fin (mainQ N))→Fin (mainR N),
      ActualCertificate E cubic loopless t u tu z ∧
      ∀ σ, (sourceScan E cubic t u tu z σ).2≤8*N+1 := by
  letI : Nonempty (Fin (mainR N)) := ⟨⟨0,by have := ready.alphabet; omega⟩⟩
  obtain ⟨z,h⟩ := actual_main_only_two_designated_coordinates E cubic loopless
    (mainQ N) (mainR N) t u tu (by have := ready.alphabet; omega) ready.newLayout ready.groups
  refine ⟨z,h,?_⟩
  intro σ
  have h' : ActualCertificate E cubic loopless t u tu z := h
  have hfee : (sourceScan E cubic t u tu z σ).2=6*N+2*Fintype.card (Fin (mainR N))+1 :=
    (h'.countAndFee σ).2
  calc
    _ = _ := hfee
    _ ≤ _ := by simpa only [Fintype.card_fin] using main_only_linear_scan_cost N Fintype.card_pos ready

#print axioms actual_printed_main_only
end
end Paper5.HybridMainOnly
