
import P5HybridMainOnlyPlacement
import P5HybridSameRouteTerminal
import P5HybridClosureLiteral

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4200000
set_option linter.unusedSectionVars false

/-! Same real MAIN layout and same fixed input: two different projections
are used by the two source-scoped terminal group families. No Hermite
coefficient or arbitrary native register is identified with either family. -/
namespace Paper5.HybridMainOnly
open scoped Classical BigOperators
open Paper5.HybridClosure J1MainSourceCollision EmpiricalCutMoments ProductVariance
open DiagonalAbundance (Draw)
noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
variable (E : Finset (V×V)) (cubic : ∀v,GraphCutMoments.degree E v=3)
variable (loopless : ∀v,(v,v)∉E)
local notation "F" => (replacedEdges E cubic)
local notation "reg" => (replaced_cubic E cubic loopless)
local notation "N" => (Fintype.card (TriVertex V))

variable {I S : Type*} [Fintype I] [DecidableEq I] [Fintype S] [Nonempty S]

def sourceScan (t u : I) (tu : t≠u) (z : SourcePrimitive E cubic I→S) (σ : TriVertex V→Bool) :
    Bool×ℕ := by
  letI : Nonempty I := ⟨t⟩
  exact sameRouteScan E cubic (actualPinWord E cubic t u z) t u
    (fun v=>z (.inr (.inr (.inl v)))) (fun e=>z (.inr (.inr (.inr e))))
    (source_pin_first E cubic t u z) (source_pin_second E cubic t u tu z) σ

theorem actual_main_only_scan (t u : I) (tu : t≠u) (z : SourcePrimitive E cubic I→S)
    (σ : TriVertex V→Bool) :
    boolAsNat (sourceScan E cubic t u tu z σ).1 =
      PinnedCNF.modelCount (MainClonedCNF.formula F (MainClonedCNF.leftSlot F reg)
        (MainClonedCNF.rightSlot F reg) σ) ∧
    (sourceScan E cubic t u tu z σ).2=6*N+2*Fintype.card S+1 := by
  letI : Nonempty I := ⟨t⟩
  exact sameRouteScan_exact E cubic loopless _ t u _ _
    (source_pin_first E cubic t u z) (source_pin_second E cubic t u tu z)
    (MainClonedCNF.leftSlot F reg) (MainClonedCNF.rightSlot F reg) σ

theorem actual_main_only_product (t u : I) (tu : t≠u) (z : SourcePrimitive E cubic I→S) :
    ∃ (mono₁ : ∀ e∈innerEdges V,actualPinWord E cubic t u z e.1 t=actualPinWord E cubic t u z e.2 t)
      (mono₂ : ∀ e∈outerEdges E cubic,actualPinWord E cubic t u z e.1 u=actualPinWord E cubic t u z e.2 u),
      ∀ σ : TriVertex V→Bool,
      PinnedCNF.modelCount (MainClonedCNF.formula F (MainClonedCNF.leftSlot F reg)
        (MainClonedCNF.rightSlot F reg) σ) =
      (∏ g : S,groupOperand (innerEdges V) (fun p=>actualPinWord E cubic t u z p t) mono₁ g (σ ∘ Subtype.val)) *
      (∏ h : S,groupOperand (outerEdges E cubic) (fun p=>actualPinWord E cubic t u z p u) mono₂ h (σ ∘ Subtype.val)) := by
  letI : Nonempty I := ⟨t⟩
  exact literal_source_group_factorization E cubic loopless _ _ _ _
    (source_pin_first E cubic t u z) (source_pin_second E cubic t u tu z)

structure ActualCertificate (t u : I) (tu : t≠u) (z : SourcePrimitive E cubic I→S) : Prop where
  phiCap : sourcePhi E cubic loopless t u z≤2*(12*(N:ℚ))*5
  xiCap : sourceXi E cubic z≤2*(4*(N:ℚ))*(Fintype.card I:ℚ)
  normalized : sourcePhi E cubic loopless t u z/(5*(12*(N:ℚ)))+
    sourceXi E cubic z/((Fintype.card I:ℚ)*(4*(N:ℚ)))≤2
  cells : ∀ c, load (SourceCell E cubic loopless t u z) c≤
    2*(12*(N:ℚ))/(Fintype.card (Draw I S):ℚ)
  groups : ∀ j g,load (SourceVarGroup E cubic z j) g≤2*(4*(N:ℚ))/(Fintype.card S:ℚ)
  seats : ActualSeats E cubic loopless t u z (2*(12*(N:ℚ))/(Fintype.card (Draw I S):ℚ))
  pins : ∀ w,empiricalLaw (actualPinWord E cubic t u z) w≤24*uniformWeight (I→S)
  first : ∀ p,actualPinWord E cubic t u z p t=mainPinColor (fun v=>z (.inr (.inr (.inl v)))) p
  second : ∀ p,actualPinWord E cubic t u z p u=dPinColor E cubic (fun e=>z (.inr (.inr (.inr e)))) p
  countAndFee : ∀ σ, boolAsNat (sourceScan E cubic t u tu z σ).1 =
    PinnedCNF.modelCount (MainClonedCNF.formula F (MainClonedCNF.leftSlot F reg)
      (MainClonedCNF.rightSlot F reg) σ) ∧
    (sourceScan E cubic t u tu z σ).2=6*N+2*Fintype.card S+1

/-- For every pair of distinct prescribed nodes, the placement is chosen before
any signs and simultaneously supports the two literal Boolean operands. -/
theorem actual_main_only_two_designated_coordinates (Q r : ℕ) (t u : Fin Q) (tu : t≠u) (hr : 0<r)
    (hCells : 2*5*(r^(2*Q))^2≤12*N) (hGroups : 2*Q*r^2≤4*N) :
    letI : Nonempty (Fin r) := ⟨⟨0,hr⟩⟩
    ∃ z : SourcePrimitive E cubic (Fin Q)→Fin r,ActualCertificate E cubic loopless t u tu z := by
  letI : Nonempty (Fin Q) := ⟨t⟩
  letI : Nonempty (Fin r) := ⟨⟨0,hr⟩⟩
  have hC : 2*5*(Fintype.card (Draw (Fin Q) (Fin r)):ℚ)^2≤12*(N:ℚ) := by
    rw [J6R11Collision.source_word_cells r Q]
    exact_mod_cast hCells
  have hG : 2*(Fintype.card (Fin Q):ℚ)*(Fintype.card (Fin r):ℚ)^2≤4*(N:ℚ) := by
    simp only [Fintype.card_fin]
    exact_mod_cast hGroups
  obtain ⟨z,hφ,hξ,hJ,hcell,hgroups⟩ := simultaneous_source_loads E cubic loopless t u hC hG
  refine ⟨z,⟨hφ,hξ,hJ,hcell,hgroups,actual_copied_seats E cubic loopless t u z _ hcell,?_,?_,?_,?_⟩⟩
  · exact actual_pin_density E cubic loopless t u z hcell
  · exact source_pin_first E cubic t u z
  · exact source_pin_second E cubic t u tu z
  · exact actual_main_only_scan E cubic loopless t u tu z

#print axioms actual_main_only_scan
#print axioms actual_main_only_product
#print axioms actual_main_only_two_designated_coordinates
end
end Paper5.HybridMainOnly
