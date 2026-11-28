import J1MainSourceBridge
import J1MainSourceCollision
import Mathlib.Tactic

/-! Composition of the actual MAIN word law, original finite cost estimates,
and actual source copy placement. No graph-dependent expectation estimate is
an input: only explicit graph cardinalities and support/degree bounds are. -/
namespace J1MainSourceCertificate
open scoped BigOperators
open MainProbe J1MainSourceLabels J1MainSourceBridge
open J1MainSourceCollision J1MainSourcePlacement
universe i s e v f b a
variable {I : Type i} {S : Type s} {E : Type e} {V : Type v}
  {F : Type f} {B : Type b} {A : Type a}
variable [Fintype I] [DecidableEq I] [Nonempty I] [Fintype S] [DecidableEq S] [Nonempty S]
variable [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F] [Fintype B] [DecidableEq B]
variable [Fintype E] [DecidableEq E] [Fintype A] [DecidableEq A] [Nonempty A]

theorem source_weighted_score_exists (special : I) (tie : F → Option B) (var : E → V)
    (fac : E → F) (pin : A → E) (pvar : A ↪ V) (pfac : A ↪ F) (pvertex : A ↪ V)
    (block : V → B)
    (hv : ∀ a, var (pin a) = pvar a) (hf : ∀ a, fac (pin a) = pfac a)
    (ht : ∀ a, tie (pfac a) = some (block (pvertex a)))
    (hind : ∀ a a', ¬triangleEdge block (pvertex a) (pvertex a'))
    (N : ℕ) (hN : 0 < N) (hM : Fintype.card E = 12*N) (hn : Fintype.card V = 4*N)
    (hvar : ∀ v, (varFibre var v).card ≤ 3) (hfac : ∀ f, (facFibre fac f).card ≤ 2)
    (htags : ∀ b, (tagFibre (tie ∘ fac) b).card ≤ 3)
    (hTied : (tiedSlots (tie ∘ fac)).card ≤ N)
    (hSize : 48 * Fintype.card I * Fintype.card S ^ 2 *
        Fintype.card S ^ Fintype.card I < Fintype.card A) :
    ∃ cfg : Primitive V F B I → S,
      incidenceCost special tie var fac cfg / (5*(12*(N:ℚ))) +
        variableCost cfg / ((Fintype.card I : ℚ)*(4*(N:ℚ))) < 2 ∧
      ∀ t g, ((Fintype.card A : ℚ)*DiagonalAbundance.successProb (I := I) (S := S))/2 <
        ((ownedPins (compiledLayout (originalData special tie var fac cfg) pin)
          t g Finset.univ).card : ℚ) := by
  apply exists_actual_main_layout special tie var fac pin pvar pfac pvertex block hv hf ht hind N hN
    (incidenceCost special tie var fac) variableCost
  · exact fun x => deviation_nonneg (literalCell special tie var fac x)
  · exact fun x => Finset.sum_nonneg (fun t _ => deviation_nonneg
      (fun v : V => J1MainSourceLabels.variableWord x v t))
  · simpa [hM] using expected_main_phi (S := S) special tie var fac N hvar hfac htags hTied
  · simpa [hn] using expected_variableCost (V := V) (F := F) (B := B) (I := I) (S := S)
  · exact hSize

#print axioms source_weighted_score_exists

end J1MainSourceCertificate
