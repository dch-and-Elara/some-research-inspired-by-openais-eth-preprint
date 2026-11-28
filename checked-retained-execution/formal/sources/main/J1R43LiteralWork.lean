import J1R43LiteralPrinted
import J1R43LiteralBudget

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6900000
set_option maxRecDepth 1900
set_option maxSynthPendingDepth 18
set_option linter.unusedSectionVars false

/-! A loose polynomial bound, with the actual original source sizes and
the exact driver call counter, for literal local completions. This is
the graph-only score stage, not a bound on acquiring MAIN native jets. -/
namespace J1R43Literal
open scoped BigOperators
open J1PhysicalHost J1PhysicalCertificate J1PhysicalIncidence J1PhysicalPrinted J1PPrinted
open MainClonedCNF J1MainSourceLabels
noncomputable section

section Numerical
theorem countEnvelope (N Q r : ℕ) (hN : 0<N) (hQ : Q≤4*N) (hr : r≤4*N) :
    (2*(16*N*Q+N)*r) *
      ((144*N^2+16*Q*N^2+Q*r*(N^2+N))*(2*N)) ≤ 249600*N^8 := by
  have hn2 : N≤N^2 := Nat.le_self_pow (by decide) N
  have hn24 : N^2≤N^4 := Nat.pow_le_pow_right hN (by decide)
  have hn34 : N^3≤N^4 := Nat.pow_le_pow_right hN (by decide)
  have keys : 16*N*Q+N≤65*N^2 := by
    calc
      _ ≤ 16*N*(4*N)+N^2 := Nat.add_le_add (Nat.mul_le_mul_left _ hQ) hn2
      _ = _ := by ring
  have visits : 144*N^2+16*Q*N^2+Q*r*(N^2+N)≤240*N^4 := by
    have h1 := Nat.mul_le_mul_left 144 hn24
    have h2 : 16*Q*N^2≤64*N^4 := by
      calc
        _ ≤ 16*(4*N)*N^2 := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hQ)
        _ = 64*N^3 := by ring
        _ ≤ _ := Nat.mul_le_mul_left _ hn34
    have h3 : Q*r*(N^2+N)≤32*N^4 := by
      calc
        _ ≤ (4*N)*(4*N)*(N^2+N^2) := Nat.mul_le_mul (Nat.mul_le_mul hQ hr) (Nat.add_le_add_left hn2 _)
        _ = _ := by ring
    exact (Nat.add_le_add (Nat.add_le_add h1 h2) h3).trans_eq (by ring)
  calc
    _ ≤ (2*(65*N^2)*(4*N))*((240*N^4)*(2*N)) := Nat.mul_le_mul
      (Nat.mul_le_mul (Nat.mul_le_mul_left _ keys) hr) (Nat.mul_le_mul_right _ visits)
    _ = _ := by ring
end Numerical

section Physical
variable {B : Type*} [Fintype B] [DecidableEq B]
local notation "N" => Fintype.card (Vertex B)
local notation "Q" => sourceQ (printedLambda B)
local notation "r" => sourceR (printedLambda B)

def candidateCompletionCount (M : Match B) (special : Site B) (H : Finset (Vertex B)) : ℕ :=
  completionVisits (S:=Symbol B) special (tie (edges M) Prod.fst)
    (portVar (edges M) (degree_eq_three M)) (portFactor (edges M)) (pinSubset M H)

theorem original_conditioned_local_work (M : Match B) (b : B) (beta : ℕ)
    (hScale : 32≤mainScaleIndex (printedLambda B)) (hBeta : beta+3≤mainScaleIndex (printedLambda B)+1)
    (special : Site B) (default : Symbol B) (H : Finset (Vertex B))
    (keys : List (ConfigKey M (Site B))) (keyNodup : keys.Nodup) (allKeys : ∀ k,k∈keys) :
    (selected M special H keys (List.finRange r) default).2 * candidateCompletionCount M special H ≤
      249600*N^8 := by
  letI : Nonempty B := ⟨b⟩
  letI : Nonempty (Symbol B) := ⟨default⟩
  have hN : 0<N := Fintype.card_pos
  obtain ⟨_,_,_,_,hc,_⟩ := actual_j1_guards N beta hN hScale hBeta
  have com := printed_completions_poly N Q r hc
  have count : keys.toFinset = Finset.univ := by
    ext k
    simp [allKeys k]
  have keyE : keys.length=Fintype.card (ConfigKey M (Site B)) := by
    rw [← List.toFinset_card_of_nodup keyNodup,count,Finset.card_univ]
  have keyCap : keys.length≤16*N*Q+N := by
    rw [keyE]
    simpa only [Fintype.card_fin] using primitiveCount_bound (I:=Site B) M
  have hRoster : Fintype.card (ScoreVisit (Port (edges M)) (Variable (Vertex B)) H
      (Site B) (Symbol B))≤144*N^2+16*Q*N^2+Q*r*(N^2+N) := by
    simpa only [Fintype.card_fin] using actual_event_roster (I:=Site B) (S:=Symbol B) M H
  have hCases : candidateCompletionCount M special H≤
      Fintype.card (ScoreVisit (Port (edges M)) (Variable (Vertex B)) H (Site B) (Symbol B)) *
        (r^Q)^4 := by
    unfold candidateCompletionCount
    simpa only [Fintype.card_fin] using completionVisits_bound (S:=Symbol B) special
      (tie (edges M) Prod.fst) (portVar (edges M) (degree_eq_three M)) (portFactor (edges M))
      (pinSubset M H)
  have hCalls : (selected M special H keys (List.finRange r) default).2 = 2*keys.length*r := by
    unfold selected
    rw [chooseLayout_calls,List.length_finRange]
  rw [hCalls]
  have qr := printed_Q_r_poly N
  exact (Nat.mul_le_mul (Nat.mul_le_mul_right r (Nat.mul_le_mul_left 2 keyCap))
    (hCases.trans (Nat.mul_le_mul hRoster com))).trans (countEnvelope N Q r hN qr.1 qr.2)

end Physical

#print axioms countEnvelope
#print axioms original_conditioned_local_work

end
end J1R43Literal