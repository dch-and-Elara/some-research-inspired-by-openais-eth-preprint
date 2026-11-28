import J1PhysicalCertificate
import J1PhysicalWitness
import Mathlib.Tactic

/-! Turn a word indexed by the compiled native menu into the actual
sign pattern of the physical formula. No independent interpretation
of the output bit is required. -/
namespace J1PhysicalNative
open scoped Polynomial
open J1MainSourceBridge J1MainSourcePlacement
open J1PhysicalHost J1PhysicalIncidence J1PhysicalIndependent J1PhysicalCertificate
open MainClonedCNF PinnedWitness FiniteWeightedQueryTree
variable {B I S : Type*} [Fintype B] [DecidableEq B]
  [Fintype I] [DecidableEq I] [Fintype S] [DecidableEq S]

noncomputable def tracked (M : Match B) (data : IncidenceData I S (Port (edges M))
    (Variable (Vertex B)) (Factor (edges M))) (H : Finset (Vertex B)) :
    Fin (kOf data (pinSubset M H)) ↪ Vertex B where
  toFun i := ((Fintype.equivFin (Diagonal data (pinSubset M H))).symm i).val.val
  inj' := by
    intro i j h
    apply (Fintype.equivFin (Diagonal data (pinSubset M H))).symm.injective
    exact Subtype.ext (Subtype.ext h)

noncomputable def selectors (M : Match B) (data : IncidenceData I S (Port (edges M))
    (Variable (Vertex B)) (Factor (edges M))) (H : Finset (Vertex B)) :
    Finset (Vertex B) :=
  Finset.univ.map (tracked M data H)

omit [Fintype I] [DecidableEq I] [Fintype S] [DecidableEq S] in
theorem selectors_sub (M : Match B) (data : IncidenceData I S (Port (edges M))
    (Variable (Vertex B)) (Factor (edges M))) (H : Finset (Vertex B)) :
    selectors M data H ⊆ H := by
  intro v hv
  obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hv
  exact ((Fintype.equivFin (Diagonal data (pinSubset M H))).symm i).val.property

noncomputable def signal {V : Type*} {k : ℕ} (e : Fin k ↪ V) (s : Fin k → Bool)
    (v : V) : Bool := by
  classical
  exact if hv : ∃ i, e i = v then s (Classical.choose hv) else true

theorem signal_tracked {V : Type*} {k : ℕ} (e : Fin k ↪ V) (s : Fin k → Bool)
    (i : Fin k) : signal e s (e i) = s i := by
  classical
  have hi : ∃ j, e j = e i := ⟨i,rfl⟩
  unfold signal
  rw [dif_pos hi,e.injective (Classical.choose_spec hi)]

noncomputable def actualSigns (M : Match B) (b₀ : B)
    (data : IncidenceData I S (Port (edges M))
      (Variable (Vertex B)) (Factor (edges M))) (H : Finset (Vertex B))
    (s : Fin (kOf data (pinSubset M H)) → Bool) (b : Bool) : Vertex B → Bool :=
  let P := selectors M data H
  let w := signal (tracked M data H) s
  if b then enabled P w else
    disabled P w (J1PhysicalWitness.p b₀) (J1PhysicalWitness.q b₀)

omit [Fintype I] [DecidableEq I] [Fintype S] [DecidableEq S] in
theorem actualSigns_match_word (M : Match B) (b₀ : B)
    (data : IncidenceData I S (Port (edges M))
      (Variable (Vertex B)) (Factor (edges M))) (H : Finset (Vertex B))
    (s : Fin (kOf data (pinSubset M H)) → Bool) (b : Bool)
    (hH : H ⊆ available M b₀) (i : Fin (kOf data (pinSubset M H))) :
    actualSigns M b₀ data H s b (tracked M data H i) = s i := by
  classical
  have hp : tracked M data H i ∈ selectors M data H := Finset.mem_map.mpr ⟨i,by simp,rfl⟩
  have hh : tracked M data H i ∈ H := selectors_sub M data H hp
  have hl : tracked M data H i ≠ J1PhysicalWitness.p b₀ := by
    intro h
    rw [h] at hh
    exact (unavailable_at_reserved M b₀ H hH _ rfl).1 hh
  have hr : tracked M data H i ≠ J1PhysicalWitness.q b₀ := by
    intro h
    rw [h] at hh
    exact (unavailable_at_reserved M b₀ H hH _ rfl).1 hh
  cases b <;> simp [actualSigns,enabled,disabled,hp,signal_tracked,hl,hr]

noncomputable def actualCount (M : Match B) (b₀ : B)
    (data : IncidenceData I S (Port (edges M))
      (Variable (Vertex B)) (Factor (edges M))) (H : Finset (Vertex B))
    (s : Fin (kOf data (pinSubset M H)) → Bool) (b : Bool) : ℕ :=
  PinnedCNF.modelCount (compiledCNF (edges M) (degree_eq_three M)
    (actualSigns M b₀ data H s b))

omit [Fintype I] [DecidableEq I] [Fintype S] [DecidableEq S] in
theorem actualCount_eq (M : Match B) (b₀ : B)
    (data : IncidenceData I S (Port (edges M))
      (Variable (Vertex B)) (Factor (edges M))) (H : Finset (Vertex B))
    (hH : H ⊆ available M b₀) (hI : Independent M H)
    (s : Fin (kOf data (pinSubset M H)) → Bool) (b : Bool) :
    actualCount M b₀ data H s b = b.toNat := by
  let P := selectors M data H
  have hs : P ⊆ H := selectors_sub M data H
  have ht : P ⊆ available M b₀ := hs.trans hH
  have hInd : Independent M P := fun v hv w hw hne => hI v (hs hv) w (hs hw) hne
  obtain ⟨hOn,hOff⟩ := J1PhysicalWitness.opposite_actual_formulas M b₀ P ht hInd
    (signal (tracked M data H) s)
  cases b
  · exact hOff
  · exact hOn

/-- The actual physical count is the target of the original MAIN native
query lower bound, with the original mixed erasure condition still explicit. -/
theorem native_path_on_physical_count {R O D : Type*} [CommSemiring R] [CommSemiring O]
    (M : Match B) (b₀ : B) (special : I) (cfg : ConfigKey M I → S) (H : Finset (Vertex B))
    (hH : H ⊆ available M b₀) (hI : Independent M H)
    (width floor : ℕ) (node : I → ℚ)
    (hr : 2 ≤ Fintype.card S) (hR : 32 ≤ width) (hq : 6*width ≤ Fintype.card I)
    (hHits : ∀ t g, floor ≤ (hits (physicalData M special cfg) (pinSubset M H) t g).card)
    (ψ : R →+* O) (precision : ℕ) (hprecision : (2:O)^precision = 0)
    (p : (Fin (kOf (physicalData M special cfg) (pinSubset M H)) → Bool) → Bool → D → R[X])
    (z : D → O) (targets ord : D → ℕ)
    (hord : ∀ d, targets d ≤ ord d)
    (hcoeff : ∀ s b d j, (2 : R) ^ (precision-targets d-j) ∣ (p s b d).coeff j)
    (tree : DecisionTree (Menu D (physicalData M special cfg) (pinSubset M H)) (ℚ[X]×O))
    (correct : ∀ s b, evaluate
      (sourceOracle (physicalData M special cfg) (pinSubset M H) width node ψ p z targets ord s b) tree =
        decide (0 < actualCount M b₀ (physicalData M special cfg) H s b)) :
    ∃ s b, 2 ^ kOf (physicalData M special cfg) (pinSubset M H) ≤
      paid (menuPrice D (physicalData M special cfg) (pinSubset M H) floor)
        (sourceOracle (physicalData M special cfg) (pinSubset M H) width node ψ p z targets ord s b) tree := by
  apply native_path_from_original_main (physicalData M special cfg) (pinSubset M H)
    width floor node hr hR hq hHits ψ precision hprecision p z targets ord hord hcoeff tree
  intro s b
  rw [correct s b,actualCount_eq M b₀ _ H hH hI]
  cases b <;> rfl

#print axioms selectors_sub
#print axioms actualSigns_match_word
#print axioms actualCount_eq
#print axioms native_path_on_physical_count

end J1PhysicalNative
