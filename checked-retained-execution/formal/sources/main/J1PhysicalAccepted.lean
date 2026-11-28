import J1PhysicalParameters
import J1PhysicalBounds
import Mathlib.Tactic

/-! Simultaneously certify the actual source copy capacities, group
capacities and diagonal-pin abundance on one physical labeling. -/
namespace J1PhysicalAccepted
open J1MainSourceLabels J1MainSourceBridge J1MainSourceCollision MainProbe MainClonedCNF
open J1PhysicalHost J1PhysicalIndependent J1PhysicalIncidence J1PhysicalCertificate
variable {B I S : Type*} [Fintype B] [DecidableEq B] [Fintype I] [DecidableEq I]
  [Nonempty I] [Fintype S] [DecidableEq S] [Nonempty S]

omit [Nonempty I] [DecidableEq S] [Nonempty S] in
theorem cell_count : Fintype.card (DiagonalAbundance.Draw I S) =
    Fintype.card S ^ (2*Fintype.card I) := by
  simp only [Fintype.card_prod,Fintype.card_fun]
  rw [Nat.mul_comm 2,pow_mul,pow_two]

/-- The same successful labeling obeys all native caps and group lower
bounds; no separate feasibility or diagonal-abundance witness is needed. -/
theorem accepted_physical_layout (M : Match B) (b₀ : B) (special : I)
    (hL : 256 ≤ Nat.clog 2 (4*Fintype.card (Vertex B)))
    (hQ : Fintype.card I ≤ Nat.clog 2 (4*Fintype.card (Vertex B)))
    (hr : Fintype.card S ^ 2 ≤ Nat.clog 2 (4*Fintype.card (Vertex B)))
    (hP : (Fintype.card S ^ Fintype.card I)^256 ≤ 2^(Nat.clog 2 (4*Fintype.card (Vertex B)))) :
    ∃ H : Finset (Vertex B), H ⊆ available M b₀ ∧ Independent M H ∧
      Fintype.card (Vertex B) ≤ 4*H.card+6 ∧
      ∃ cfg : ConfigKey M I → S,
        (∀ c, load ((physicalData M special cfg).cell) c <
          2*((Fintype.card (Port (edges M)):ℚ)/(Fintype.card (DiagonalAbundance.Draw I S):ℚ))) ∧
        (∀ t g, load (fun v : Variable (Vertex B) => J1MainSourceLabels.variableWord cfg v t) g <
          2*((Fintype.card (Variable (Vertex B)):ℚ)/(Fintype.card S:ℚ))) ∧
        (∀ t g, ((H.card:ℚ)*DiagonalAbundance.successProb (I := I) (S := S))/2 <
          ((ownedPins (compiledLayout (physicalData M special cfg) (pinSubset M H))
            t g Finset.univ).card : ℚ)) := by
  let n := Fintype.card (Vertex B)
  let q := Fintype.card I
  let r := Fintype.card S
  have hb : Nonempty B := ⟨b₀⟩
  letI : Nonempty B := hb
  have hn : 0 < n := Fintype.card_pos
  have h := J1PhysicalParameters.ceiling_guards n q r hn hL hQ hr Fintype.card_pos hP
  obtain ⟨hsize,hcell,hgroup⟩ := h
  obtain ⟨H,hH,hI,hHcard,cfg,hscore,hab⟩ := compiled_physical_certificate M b₀ special hsize
  have hm :
      (10 : ℚ)*(Fintype.card (DiagonalAbundance.Draw I S):ℚ)^2 ≤
          (Fintype.card (Port (edges M)):ℚ) := by
    rw [cell_count,port_card (edges M) (degree_eq_three M)]
    exact_mod_cast hcell
  have hv :
      (2 : ℚ)*(Fintype.card I:ℚ)*(Fintype.card S:ℚ)^2 ≤
          (Fintype.card (Variable (Vertex B)):ℚ) := by
    rw [variables_card]
    exact_mod_cast hgroup
  obtain ⟨hc,hg⟩ := J1PhysicalBounds.original_caps M special cfg hn hm hv hscore
  exact ⟨H,hH,hI,hHcard,cfg,hc,hg,hab⟩

#print axioms cell_count
#print axioms accepted_physical_layout
end J1PhysicalAccepted
