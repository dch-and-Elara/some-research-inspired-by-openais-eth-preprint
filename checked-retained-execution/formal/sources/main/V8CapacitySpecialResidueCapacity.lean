import V8CapacitySpecialResidue
import V8CapacitySpecialRankCompare
import V8CapacityGridOrder

/-! Literal v8 L=0, p=1. The residue-field normal form is applied to the
actual active Taylor features of A2, so its rank counts the original
universal capacity rather than that of a substituted receiver model. -/
namespace V8CapacitySpecialResidueCapacity
open scoped Classical BigOperators
open V8CapacitySpecialResidue V8CapacitySpecialRankCompare
open V8CapacitySymbolic V8CapacityNativeMatrix V8CapacityIntegrated
open V8CapacityMonicBasis V8CapacityNewtonGrid V8CapacitySmith V8CapacityGridOrder
open V8CapacityWidthUpper

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1100000

variable {O H : Type*} [CommRing O] [IsDomain O] [IsLocalRing O]
variable [IsPrincipalIdealRing O] [Fintype H] [Fintype (IsLocalRing.ResidueField O)]
variable {π : O} {q : ℕ} (D : V8CapacityDigits.Digits π q) (hq : 0<q)
variable (hq₂ : 2≤q) (h0 : D.d ⟨0,hq⟩=0) (hπ : π≠0)
variable (hMax : IsLocalRing.maximalIdeal O=Ideal.span ({π}:Set O))
variable (k : ℕ)

local notation "κ" => IsLocalRing.ResidueField O
local notation "ρ" => IsLocalRing.residue O
local notation "E" => Digits H k
local notation "I" => Grid H 1 k
local notation "J" => Columns H π 1 k
local notation "rdeg" => (@rowDegree E _ (DegreeCap 1 k))
local notation "CM" => monicC π 1 k D hq
local notation "W" => weighted π q rdeg (CM : Matrix I J O)
local notation "Rows" => (E → Fin (Fintype.card κ))

def residueFeatures (j : J) : MvPolynomial E κ :=
  MvPolynomial.map ρ (symCol π 1 k j.val)

theorem evaluate_reduced {V : Type*} (f : MvPolynomial V O) (x : V → O) :
    MvPolynomial.eval (fun r => ρ (x r)) (MvPolynomial.map ρ f)=
      ρ (MvPolynomial.eval x f) := by
  rw [MvPolynomial.eval_map]
  change MvPolynomial.eval₂Hom ρ (fun r => ρ (x r)) f =
    ρ (MvPolynomial.eval₂Hom (RingHom.id O) x f)
  rw [MvPolynomial.map_eval₂Hom,RingHom.comp_id]

theorem raw_eval_column (x : E → O) (j : J) :
    ρ (MvPolynomial.eval x (symCol π 1 k j.val)) =
      ∑ i : I, ρ (tensorNorm D hq hq₂ h0 hπ (rdeg i) x) * ((W).map ρ) i j := by
  rw [column_evaluates π 1 k D hq j,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [tensor_factor D hq hq₂ h0 hπ,weighted,Matrix.map_apply,Matrix.of_apply,map_mul]
  ring

/-- Determinants do not depend on which proof-producing decision
procedure for index equality is used. Losing this dependent instance
causes an unnecessary comparison of enumerated permutations. -/
theorem det_independent_decEq {V : Type*} [Fintype V] (A : Matrix V V O)
    (a b : DecidableEq V) : (letI := a; A.det)=(letI := b; A.det) := by
  have h : a=b := by funext i j; exact Subsingleton.elim _ _
  subst b
  rfl


section GenericEvaluation

variable {V' A' B' : Type*}
variable [Fintype V'] [Fintype A'] [Fintype B'] [LinearOrder A']

include hMax hq₂ h0 hπ in
theorem rank_on_field_grid
    (degree : A' → V' → ℕ)
    (order : ∀ i j, (∀ e, degree i e≤degree j e) → i≤j)
    (M : Matrix A' B' O) (f : B' → MvPolynomial V' O)
    (formula : ∀ (x : V' → O) (j : B'), ρ (MvPolynomial.eval x (f j)) =
      ∑ i : A', ρ (tensorNorm D hq hq₂ h0 hπ (degree i) x)*(M.map ρ) i j)
    (e : Fin (Fintype.card κ) ≃ κ) (d : κ → O) (hd : Function.RightInverse d ρ) :
    (residueEvaluationMatrix e (fun j => MvPolynomial.map ρ (f j))).rank=(M.map ρ).rank := by
  let V : Matrix A' A' O := normGrid D hq hq₂ h0 hπ degree
  have hu : IsUnit V.det := norm_grid_unit D hq hq₂ h0 hπ hMax degree order
  let lifts (x : V' → Fin (Fintype.card κ)) (u : V') := d (e (x u))
  let G : Matrix (V' → Fin (Fintype.card κ)) A' κ :=
    Matrix.of fun x i => ρ (tensorNorm D hq hq₂ h0 hπ (degree i) (lifts x))
  let fromGrid (i : A') (u : V') : Fin (Fintype.card κ) := e.symm (ρ (nodeAt D hq degree i u))
  let B : Matrix (V' → Fin (Fintype.card κ)) B' κ :=
    residueEvaluationMatrix e (fun j => MvPolynomial.map ρ (f j))
  change B.rank=(M.map ρ).rank
  have hu' : (letI := Classical.decEq A'; IsUnit V.det) := by
    have e := det_independent_decEq V (inferInstance : DecidableEq A') (Classical.decEq A')
    exact e ▸ hu
  refine same_rank_of_raw_evaluation M V hu' G B fromGrid ?_ ?_
  · ext x j
    change MvPolynomial.eval (fun u => e (x u)) (MvPolynomial.map ρ (f j)) =
      ∑ i : A', ρ (tensorNorm D hq hq₂ h0 hπ (degree i) (lifts x))*(M.map ρ) i j
    have he : (fun u => e (x u))=fun u => ρ (lifts x u) := funext (fun u => (hd (e (x u))).symm)
    rw [he,evaluate_reduced]
    exact formula (lifts x) j
  · ext i j
    change MvPolynomial.eval (fun u => e (fromGrid i u)) (MvPolynomial.map ρ (f j)) =
      ∑ u : A', (V.map ρ) i u*(M.map ρ) u j
    have he : (fun u => e (fromGrid i u))=fun u => ρ (nodeAt D hq degree i u) :=
      funext (fun _ => e.apply_symm_apply _)
    rw [he,evaluate_reduced]
    exact formula (nodeAt D hq degree i) j

end GenericEvaluation

include hMax hq₂ h0 hπ in
theorem field_eval_actual_rank (enumerate : Fin (Fintype.card κ) ≃ κ)
    (d : κ → O) (hd : Function.RightInverse d ρ) :
    (residueEvaluationMatrix enumerate (residueFeatures (H:=H) (π:=π) k)).rank=((W).map ρ).rank := by
  letI : LinearOrder I := gridOrder
  exact rank_on_field_grid D hq hq₂ h0 hπ hMax rdeg
    (fun i j => coordinate_le (x:=i) (y:=j)) W
    (fun j : J => symCol π 1 k j.val) (raw_eval_column D hq hq₂ h0 hπ k) enumerate d hd


include hMax hq₂ h0 hπ in
/-- The exact A3 index for one residue digit is q^h times the coefficient
rank after arbitrary collisions in the correct field. -/
theorem residue_capacity_formula (enumerate : Fin (Fintype.card κ) ≃ κ)
    (d : κ → O) (hd : Function.RightInverse d ρ) :
    Fintype.card ((H → κ) × Active (matrixPowered π hMax W).2 1) =
      (Fintype.card κ)^(Fintype.card H) *
        (reducedCoefficientMatrix (residueFeatures (H:=H) (π:=π) k)).rank := by
  rw [Fintype.card_prod,Fintype.card_fun,← units_count_from_rank π hπ hMax W,
    ← field_eval_actual_rank D hq hq₂ h0 hπ hMax k enumerate d hd,
    exact_reduced_coefficient_rank enumerate]

#print axioms evaluate_reduced
#print axioms raw_eval_column
#print axioms field_eval_actual_rank
#print axioms residue_capacity_formula
end
end V8CapacitySpecialResidueCapacity

