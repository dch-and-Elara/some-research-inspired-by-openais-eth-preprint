import J1PhysicalIncidence
import J1PhysicalIndependent
import J1MainSourceCertificate
import Mathlib.Tactic

/-! Actual four-clone triangle-host input enters the source J1 certificate.
The bound is finite and numeric; no asymptotic assertion is hidden as a
choice of graph-dependent labels. -/
namespace J1PhysicalCertificate
open J1MainSourceLabels J1MainSourceBridge J1MainSourceCollision
open J1PhysicalHost J1PhysicalIncidence J1PhysicalIndependent
open MainProbe MainClonedCNF
variable {B I S : Type*} [Fintype B] [DecidableEq B] [Fintype I] [DecidableEq I]
  [Nonempty I] [Fintype S] [DecidableEq S] [Nonempty S]

abbrev ConfigKey (M : Match B) (I : Type*) :=
  Primitive (Variable (Vertex B)) (Factor (edges M)) B I

noncomputable def pinSubset (M : Match B) (H : Finset (Vertex B)) : H → Port (edges M) :=
  fun h => pinPort (edges M) h.val

noncomputable def physicalData (M : Match B) (special : I)
    (cfg : ConfigKey M I → S) :
    J1MainSourcePlacement.IncidenceData I S (Port (edges M)) (Variable (Vertex B))
      (Factor (edges M)) :=
  originalData special (tie (edges M) Prod.fst) (portVar (edges M) (degree_eq_three M))
    (portFactor (edges M)) cfg

noncomputable def physicalPhi (M : Match B) (special : I) (cfg : ConfigKey M I → S) : ℚ :=
  incidenceCost special (tie (edges M) Prod.fst) (portVar (edges M) (degree_eq_three M))
    (portFactor (edges M)) cfg

noncomputable def physicalXi (M : Match B) (cfg : ConfigKey M I → S) : ℚ :=
  variableCost cfg

/-- Triangle host, actual ports, literal counts, triangle sharing and the
real reserved independent set discharge the finite J1 hypotheses. -/
theorem compiled_physical_certificate (M : Match B) (b₀ : B) (special : I)
    (hSize : 192 * Fintype.card I * Fintype.card S ^ 2 *
        Fintype.card S ^ Fintype.card I + 6 < Fintype.card (Vertex B)) :
    ∃ H : Finset (Vertex B), H ⊆ available M b₀ ∧ Independent M H ∧
      Fintype.card (Vertex B) ≤ 4*H.card+6 ∧
      ∃ cfg : ConfigKey M I → S,
        physicalPhi M special cfg / (5*(12*(Fintype.card (Vertex B):ℚ))) +
          physicalXi M cfg / ((Fintype.card I:ℚ)*(4*(Fintype.card (Vertex B):ℚ))) < 2 ∧
        ∀ t g, ((H.card:ℚ)*DiagonalAbundance.successProb (I := I) (S := S))/2 <
          ((ownedPins (compiledLayout (physicalData M special cfg) (pinSubset M H))
            t g Finset.univ).card : ℚ) := by
  classical
  obtain ⟨H,hH,hI,hcap⟩ := reserve_has_large_independent M b₀
  have hmul : 192 * Fintype.card I * Fintype.card S ^ 2 * Fintype.card S ^ Fintype.card I =
      4*(48 * Fintype.card I * Fintype.card S ^ 2 * Fintype.card S ^ Fintype.card I) := by ring
  have hs : 48 * Fintype.card I * Fintype.card S ^ 2 * Fintype.card S ^ Fintype.card I <
      H.card := by
    rw [hmul] at hSize
    omega
  have he : 0 < H.card := by omega
  have hne : Nonempty H := by
    obtain ⟨v,hv⟩ := Finset.card_pos.mp he
    exact ⟨⟨v,hv⟩⟩
  letI : Nonempty H := hne
  let pv : H ↪ Variable (Vertex B) :=
    ⟨fun v => (v.val,0),fun _ _ h => Subtype.ext (congrArg Prod.fst h)⟩
  let pf : H ↪ Factor (edges M) :=
    ⟨fun v => Sum.inl v.val,fun _ _ h => Subtype.ext (Sum.inl_injective h)⟩
  let block : Variable (Vertex B) → B := fun v => v.1.1
  have hPinVar (a : H) : portVar (edges M) (degree_eq_three M) (pinSubset M H a) = pv a := rfl
  have hPinFac (a : H) : portFactor (edges M) (pinSubset M H a) = pf a := rfl
  have hPinTie (a : H) : tie (edges M) Prod.fst (pf a) = some (block (pv a)) := rfl
  have hdt : ∀ a a' : H, ¬ triangleEdge block (pv a) (pv a') := by
    intro a a' h
    exact triangle_restriction M H hI a a' ⟨fun h' => h.1 (Prod.ext h' rfl),h.2⟩
  refine ⟨H,hH,hI,hcap,?_⟩
  have hN : 0 < Fintype.card (Vertex B) := by omega
  have hsize' : 48 * Fintype.card I * Fintype.card S ^ 2 * Fintype.card S ^ Fintype.card I <
      Fintype.card H := by rwa [Fintype.card_coe]
  have hcert := J1MainSourceCertificate.source_weighted_score_exists special
    (tie (edges M) Prod.fst) (portVar (edges M) (degree_eq_three M)) (portFactor (edges M))
    (pinSubset M H) pv pf pv block hPinVar hPinFac hPinTie hdt
    (Fintype.card (Vertex B)) hN (port_card (edges M) (degree_eq_three M)) variables_card
    (var_degree_bound (edges M) (degree_eq_three M))
    (by
      intro q
      convert factor_scope_bound (edges M) q using 1
      apply congrArg Finset.card
      ext e
      simp [facFibre])
    (tag_degree_bound (edges M) Prod.fst (fun b => le_of_eq (block_card b)))
    (le_of_eq (number_tied_slots (edges M) Prod.fst)) hsize'
  simpa only [Fintype.card_coe,physicalData,physicalPhi,physicalXi] using hcert

#print axioms compiled_physical_certificate

end J1PhysicalCertificate
