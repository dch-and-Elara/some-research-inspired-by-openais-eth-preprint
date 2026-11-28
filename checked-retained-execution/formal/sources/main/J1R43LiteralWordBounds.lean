import J1R43LiteralIntegerHeight
import J1R43LiteralPhysical
import J1R43LiteralBudget
import J1R43LiteralPrinted

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6900000
set_option maxRecDepth 2000
set_option maxSynthPendingDepth 18
set_option linter.unusedSectionVars false

/-! Word magnitudes at the actual printed parameters of original J1.
With binary arithmetic these bounds give logarithmic length in N, without
assuming that arbitrary full-space rational sums are cheap. -/
namespace J1R43Literal
open scoped BigOperators
open J1PhysicalHost J1PhysicalIncidence J1PhysicalCertificate J1PhysicalPrinted J1PPrinted
open J1MainSourceLabels MainClonedCNF
noncomputable section

theorem polynomial_integer_height (N q rr h A W : ℕ) (hN : 0<N) (hq : q≤4*N)
    (hr : rr≤4*N) (hh : h≤N) (hA : A≤2*N) (hW : W≤8*N^2) :
    intHeightBound (12*N) (4*N) h q rr A W≤19931136*N^12 := by
  have h1 : 1≤N^2 := Nat.pow_pos hN
  have W1 : W+1≤9*N^2 := by
    calc
      _ ≤ 8*N^2+N^2 := Nat.add_le_add hW h1
      _ = _ := by ring
  have first : (q*(4*N))*h^2*((12*N)^2*(2*A))≤9216*N^7 := by
    calc
      _ ≤ ((4*N)*(4*N))*N^2*((12*N)^2*(2*(2*N))) := by
        exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_right _ hq) (Nat.pow_le_pow_left hh _))
          (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hA))
      _ = _ := by ring
  have second : (5*(12*N))*h^2*(q*(4*N)^2*(2*A))≤15360*N^7 := by
    calc
      _ ≤ (5*(12*N))*N^2*((4*N)*(4*N)^2*(2*(2*N))) := by
        exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hh _))
          (Nat.mul_le_mul (Nat.mul_le_mul_right _ hq) (Nat.mul_le_mul_left _ hA))
      _ = _ := by ring
  have third : (5*(12*N))*(q*(4*N))*8*(q*rr*(h^2*A*(W+1)^2))≤19906560*N^12 := by
    calc
      _ ≤ (5*(12*N))*((4*N)*(4*N))*8*((4*N)*(4*N)*(N^2*(2*N)*(9*N^2)^2)) := by
        exact Nat.mul_le_mul
          (Nat.mul_le_mul_right 8 (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hq)))
          (Nat.mul_le_mul (Nat.mul_le_mul hq hr) (Nat.mul_le_mul
            (Nat.mul_le_mul (Nat.pow_le_pow_left hh _) hA) (Nat.pow_le_pow_left W1 _)))
      _ = _ := by ring
  have hpow : N^7≤N^12 := Nat.pow_le_pow_right hN (by decide)
  unfold intHeightBound
  exact (Nat.add_le_add
    (Nat.add_le_add (first.trans (Nat.mul_le_mul_left _ hpow)) (second.trans (Nat.mul_le_mul_left _ hpow)))
    third).trans_eq (by ring)

theorem polynomial_shared_den (N q h A : ℕ) (hq : q≤4*N) (hh : h≤N) (hA : A≤2*N) :
    5*(12*N)*(q*(4*N))*h^2*A≤1920*N^6 := by
  calc
    _ ≤ 5*(12*N)*((4*N)*(4*N))*N^2*(2*N) :=
      Nat.mul_le_mul (Nat.mul_le_mul
        (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hq)) (Nat.pow_le_pow_left hh _)) hA
    _ = _ := by ring

section Physical
variable {B : Type*} [Fintype B] [DecidableEq B]
local notation "N" => Fintype.card (Vertex B)
local notation "Q" => sourceQ (printedLambda B)
local notation "r" => sourceR (printedLambda B)

theorem original_candidate_word_bounds (M : Match B) (b : B) (beta : ℕ)
    (hScale : 32≤mainScaleIndex (printedLambda B)) (hBeta : beta+3≤mainScaleIndex (printedLambda B)+1)
    (special : Site B) (default : Symbol B) (H : Finset (Vertex B))
    (state : ConfigKey M (Site B) → Option (Symbol B)) :
    sharedDen (Port (edges M)) (Variable (Vertex B)) H (Site B) (Symbol B)≤1920*N^6 ∧
    (integerScore special (tie (edges M) Prod.fst) (portVar (edges M) (degree_eq_three M))
      (portFactor (edges M)) (pinSubset M H) state).natAbs≤19931136*N^12 := by
  letI : Nonempty B := ⟨b⟩
  letI : Nonempty (Symbol B) := ⟨default⟩
  have hN : 0<N := Fintype.card_pos
  obtain ⟨hr,_,_,_,hc,_⟩ := actual_j1_guards N beta hN hScale hBeta
  change 2≤r at hr
  have hr0 : 0<r := (by decide : 0<(2:ℕ)).trans_le hr
  have hA : r^(4*Q)≤2*N := by
    rw [show r^(4*Q)=(r^Q)^4 by rw [← pow_mul]; congr 1; ring]
    exact printed_completions_poly N Q r hc
  have hK : r^Q≤2*N := (Nat.le_self_pow (by decide) _).trans
    (printed_completions_poly N Q r hc)
  obtain ⟨hq,hrr⟩ := printed_Q_r_poly N
  have hW : r^(Q+1)≤8*N^2 := by
    rw [pow_succ]
    exact (Nat.mul_le_mul hK hrr).trans_eq (by ring)
  have hH : H.card≤N := Finset.card_le_univ _
  constructor
  · unfold sharedDen
    rw [Fintype.card_fin,Fintype.card_fin,Fintype.card_coe,
      port_card (edges M) (degree_eq_three M),variables_card]
    exact polynomial_shared_den N Q H.card (r^(4*Q)) hq hH hA
  · apply (integerScore_height special (tie (edges M) Prod.fst) (portVar (edges M) (degree_eq_three M))
      (portFactor (edges M)) (pinSubset M H) state).trans
    rw [Fintype.card_fin,Fintype.card_fin,Fintype.card_coe,
      port_card (edges M) (degree_eq_three M),variables_card]
    exact polynomial_integer_height N Q r H.card (r^(4*Q)) (r^(Q+1)) hN hq hrr hH hA hW

end Physical

#print axioms polynomial_integer_height
#print axioms polynomial_shared_den
#print axioms original_candidate_word_bounds

end
end J1R43Literal