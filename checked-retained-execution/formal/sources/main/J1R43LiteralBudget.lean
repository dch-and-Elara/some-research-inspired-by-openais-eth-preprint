import J1R43LiteralScore
import J1PhysicalCertificate
import J1PhysicalIncidence
import J1PhysicalHost
import J1PhysicalPrinted
import J1R43LiteralDriver

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false

/-! A finite event roster does not expand the complete primitive
assignment space. Its actual cardinal and completion work are the
polynomial accounting relevant to original J1 lines 1587–1594. -/
namespace J1R43Literal
open scoped BigOperators
open DiagonalAbundance J1MainSourceLabels J1MainSourceCollision
noncomputable section

abbrev ScoreVisit (E V A I S : Type*) :=
  (E×E) ⊕ ((I×(V×V)) ⊕ ((I×S)×((A×A)⊕A)))

section Local
variable {V F B I S E A : Type*}
  [Fintype V] [Fintype I] [Fintype S] [Fintype E] [Fintype A]
  [DecidableEq V] [DecidableEq F] [DecidableEq B] [DecidableEq I] [DecidableEq S] [Nonempty S]

local notation "P" => Primitive V F B I

def scoreVisit (t : I) (tag : F → Option B) (var : E → V) (fac : E → F)
    (pin : A → E) : ScoreVisit E V A I S → LocalTest P S
  | .inl z => incidenceEvent t tag var fac z.1 z.2
  | .inr (.inl z) => variableEvent z.2.1 z.2.2 z.1
  | .inr (.inr (j,.inl z)) => hitPairEvent t tag var fac j.1 j.2 (pin z.1) (pin z.2)
  | .inr (.inr (j,.inr a)) => hitPairEvent t tag var fac j.1 j.2 (pin a) (pin a)

def coefficient (mu : ℚ) : ScoreVisit E V A I S → ℚ
  | .inl _ => (5*(Fintype.card E:ℚ))⁻¹
  | .inr (.inl _) => ((Fintype.card I:ℚ)*(Fintype.card V:ℚ))⁻¹
  | .inr (.inr (_,.inl _)) => 8 / mu^2
  | .inr (.inr (_,.inr _)) => -(16*mu) / mu^2

def constantTerm (mu : ℚ) : ℚ :=
  -(∑ _ : E×E, 1/(Fintype.card (Draw I S):ℚ))/(5*(Fintype.card E:ℚ)) -
  (∑ _ : I, ∑ _ : V×V, 1/(Fintype.card S:ℚ))/((Fintype.card I:ℚ)*(Fintype.card V:ℚ)) +
    8*(∑ _ : I×S, mu^2)/mu^2

theorem exact_visit_count :
    Fintype.card (ScoreVisit E V A I S) =
      Fintype.card E^2+Fintype.card I*Fintype.card V^2+
        Fintype.card I*Fintype.card S*(Fintype.card A^2+Fintype.card A) := by
  simp only [ScoreVisit,Fintype.card_sum,Fintype.card_prod,pow_two]
  ring

theorem visit_completions_le (t : I) (tag : F → Option B) (var : E → V) (fac : E → F)
    (pin : A → E) (j : ScoreVisit E V A I S) :
    Fintype.card ((scoreVisit t tag var fac pin j).support → S) ≤
      (Fintype.card S ^ Fintype.card I)^4 := by
  rcases j with z|z
  · exact incidenceEvent_completions t tag var fac z.1 z.2
  rcases z with z|z
  · exact variableEvent_completions z.2.1 z.2.2 z.1
  rcases z with ⟨j,z⟩
  rcases z with b|a
  · exact hitPairEvent_completions t tag var fac j.1 j.2 (pin b.1) (pin b.2)
  · exact hitPairEvent_completions t tag var fac j.1 j.2 (pin a) (pin a)

def completionVisits (t : I) (tag : F → Option B) (var : E → V) (fac : E → F)
    (pin : A → E) : ℕ :=
  ∑ j : ScoreVisit E V A I S,Fintype.card ((scoreVisit t tag var fac pin j).support → S)

theorem completionVisits_bound (t : I) (tag : F → Option B) (var : E → V) (fac : E → F)
    (pin : A → E) :
    completionVisits (S:=S) t tag var fac pin ≤
      Fintype.card (ScoreVisit E V A I S)*(Fintype.card S ^ Fintype.card I)^4 := by
  unfold completionVisits
  exact (Finset.sum_le_sum (fun j _=>visit_completions_le t tag var fac pin j)).trans_eq
    (by simp)

end Local

section Quantitative
open J1PhysicalHost J1PhysicalCertificate J1PhysicalIncidence MainClonedCNF

variable {B I S : Type*} [Fintype B] [DecidableEq B] [Fintype I] [DecidableEq I]
  [Fintype S] [DecidableEq S] [Nonempty S]

local notation "N" => Fintype.card (Vertex B)
local notation "Q" => Fintype.card I
local notation "r" => Fintype.card S

theorem factor_injects_into_ports (M : Match B) :
    Fintype.card (Factor (edges M)) ≤ Fintype.card (Port (edges M)) := by
  have retraction (f : Factor (edges M)) :
      portFactor (edges M) (portAtFactor (edges M) (f,false))=f := by
    rcases f with f|f
    · rfl
    rcases f with f|f <;> rfl
  exact Fintype.card_le_of_injective (fun f => portAtFactor (edges M) (f,false))
    (fun a b h => (retraction a).symm.trans ((congrArg (portFactor (edges M)) h).trans (retraction b)))

theorem primitiveCount_bound (M : Match B) :
    Fintype.card (ConfigKey M I) ≤ 16*N*Q+N := by
  have hF := (factor_injects_into_ports M).trans_eq (port_card (edges M) (degree_eq_three M))
  have hB : Fintype.card B ≤ N :=
    Fintype.card_le_of_injective (fun b : B => ((b,0) : Vertex B))
      (fun _ _ h=>congrArg Prod.fst h)
  change Fintype.card ((Variable (Vertex B)×I)⊕((Factor (edges M)×I)⊕B)) ≤ _
  rw [Fintype.card_sum,Fintype.card_sum,Fintype.card_prod (Variable (Vertex B)) I,
    Fintype.card_prod (Factor (edges M)) I,variables_card]
  have hFM := Nat.mul_le_mul_right Q hF
  calc
    _ ≤ 4*N*Q+(12*N*Q+N) := Nat.add_le_add_left (Nat.add_le_add hFM hB) _
    _ = _ := by ring

theorem printed_completions_poly (nn qq rr : ℕ) (hcell : 10*(rr^(2*qq))^2≤12*nn) :
    (rr^qq)^4≤2*nn := by
  have he : (rr^(2*qq))^2=(rr^qq)^4 := by rw [← pow_mul,← pow_mul]; congr 1; ring
  rw [he] at hcell
  omega

theorem printed_Q_r_poly (nn : ℕ) :
    J1PhysicalPrinted.sourceQ (Nat.clog 2 (4*nn))≤4*nn ∧
    J1PhysicalPrinted.sourceR (Nat.clog 2 (4*nn))≤4*nn := by
  have h : Nat.clog 2 (4*nn)≤4*nn :=
    (Nat.clog_le_iff_le_pow (by decide)).2 (show 4*nn<2^(4*nn) from Nat.lt_two_pow_self).le
  refine ⟨(J1PhysicalPrinted.sourceQ_le _).trans h,?_⟩
  have hr := (J1PhysicalPrinted.sourceR_sq (Nat.clog 2 (4*nn))).trans h
  exact (Nat.le_self_pow (by decide) _).trans hr

theorem actual_event_roster (M : Match B) (H : Finset (Vertex B)) :
    Fintype.card (ScoreVisit (Port (edges M)) (Variable (Vertex B)) H I S) ≤
      144*N^2+16*Q*N^2+Q*r*(N^2+N) := by
  rw [exact_visit_count, port_card (edges M) (degree_eq_three M),variables_card,Fintype.card_coe]
  have hn : H.card ≤ N := Finset.card_le_univ H
  have he : (12*N)^2+Q*(4*N)^2=144*N^2+16*Q*N^2 := by ring
  rw [he]
  apply Nat.add_le_add_left
  exact Nat.mul_le_mul_left _ (Nat.add_le_add (Nat.pow_le_pow_left hn _) hn)

end Quantitative

#print axioms exact_visit_count
#print axioms visit_completions_le
#print axioms completionVisits_bound
#print axioms factor_injects_into_ports
#print axioms primitiveCount_bound
#print axioms printed_completions_poly
#print axioms printed_Q_r_poly
#print axioms actual_event_roster

end
end J1R43Literal