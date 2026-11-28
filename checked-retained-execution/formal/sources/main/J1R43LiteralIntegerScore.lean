import J1R43LiteralScaledEvents
import J1R43LiteralMoments
import J1PhysicalAccepted

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 7100000
set_option linter.unusedSectionVars false

/-! All three printed candidate score components use one fixed
integer denominator on the given graph. No multiplication of unrelated
rational denominators occurs in the exact candidate arithmetic. -/
namespace J1R43Literal
open scoped BigOperators
open DiagonalAbundance J1MainSourceLabels J1MainSourceCollision
noncomputable section

variable {V F B I S E A : Type*}
  [Fintype V] [Fintype F] [Fintype B] [Fintype I] [Fintype S] [Fintype E] [Fintype A]
  [DecidableEq V] [DecidableEq F] [DecidableEq B] [DecidableEq I] [DecidableEq S] [Nonempty S]
local notation "P" => Primitive V F B I

variable (t : I) (tag : F → Option B) (var : E → V) (fac : E → F) (pin : A → E)
    (known : Primitive V F B I → Option S)

def eventInt (t : I) (tag : F → Option B) (var : E → V) (fac : E → F) (pin : A → E)
    (known : Primitive V F B I → Option S) (j : ScoreVisit E V A I S) : ℤ :=
  Int.ofNat (scaledEventNumerator (Fintype.card I) (scoreVisit t tag var fac pin j) known)

include known in
theorem eventInt_exact (j : ScoreVisit E V A I S) :
    (eventInt t tag var fac pin known j:ℚ) =
      ((Fintype.card S^(4*Fintype.card I)):ℕ)*(scoreVisit t tag var fac pin j).conditional (partialWeight known) := by
  unfold eventInt
  push_cast
  exact (actual_visit_scaled t tag var fac pin j known).1

def phiInt : ℤ :=
  ∑ j : E×E, (eventInt (S:=S) (A:=A) t tag var fac pin known (.inl j) - ((Fintype.card S)^(2*(Fintype.card I)):ℕ))

def xiInt : ℤ :=
  ∑ i : I, ∑ j : V×V,
    (eventInt (S:=S) (A:=A) t tag var fac pin known (.inr (.inl (i,j))) - ((Fintype.card S)^(4*(Fintype.card I)-1):ℕ))

def pairInt (j : I×S) : ℤ :=
  ∑ e : A×A, eventInt (S:=S) (A:=A) t tag var fac pin known (.inr (.inr (j,.inl e)))

def singleInt (j : I×S) : ℤ :=
  ∑ a : A, eventInt (S:=S) (A:=A) t tag var fac pin known (.inr (.inr (j,.inr a)))

def varInt (j : I×S) : ℤ :=
  ((Fintype.card S^(Fintype.card I+1)):ℕ)^2 * pairInt t tag var fac pin known j -
    (2:ℤ)*((Fintype.card S^(Fintype.card I+1)):ℕ)*((Fintype.card A):ℕ)*singleInt t tag var fac pin known j + ((Fintype.card A):ℕ)^2*((Fintype.card S^(4*Fintype.card I)):ℕ)

def sharedDen (E V A I S : Type*) [Fintype E] [Fintype V] [Fintype A] [Fintype I] [Fintype S] : ℕ :=
  5*Fintype.card E * (Fintype.card I*Fintype.card V) *
    Fintype.card A^2 * Fintype.card S^(4*Fintype.card I)

def integerScore : ℤ :=
  (((Fintype.card I)*(Fintype.card V):ℕ):ℤ)*((Fintype.card A):ℕ)^2*phiInt t tag var fac pin known +
    ((5*(Fintype.card E):ℕ):ℤ)*((Fintype.card A):ℕ)^2*xiInt t tag var fac pin known +
    ((5*(Fintype.card E):ℕ):ℤ)*((Fintype.card I)*(Fintype.card V):ℕ)*8*∑ j : I×S, varInt t tag var fac pin known j

theorem cell_baseline_scale : ((Fintype.card S^(4*Fintype.card I)):ℕ)/(Fintype.card (Draw I S):ℚ) = (((Fintype.card S)^(2*(Fintype.card I)):ℕ):ℚ) := by
  have hc := J1PhysicalAccepted.cell_count (I:=I) (S:=S)
  rw [hc]
  push_cast
  have hr : (0:ℚ)<(Fintype.card S) := by exact_mod_cast (Fintype.card_pos : 0<(Fintype.card S))
  rw [show 4*(Fintype.card I)=(2*(Fintype.card I))+(2*(Fintype.card I)) by omega,pow_add]
  field_simp

theorem group_baseline_scale (hq : 0<(Fintype.card I)) : ((Fintype.card S^(4*Fintype.card I)):ℕ)/((Fintype.card S):ℚ)=(((Fintype.card S)^(4*(Fintype.card I)-1):ℕ):ℚ) := by
  have hr : (0:ℚ)<(Fintype.card S) := by exact_mod_cast (Fintype.card_pos : 0<(Fintype.card S))
  push_cast
  conv_lhs => rw [show 4*(Fintype.card I)=(4*(Fintype.card I)-1)+1 by omega,pow_add,pow_one]
  exact mul_div_cancel_right₀ _ hr.ne'

theorem phiInt_exact :
    (phiInt t tag var fac pin known:ℚ) =
      ((Fintype.card S^(4*Fintype.card I)):ℕ)*phiLocal t tag var fac (partialWeight known) := by
  unfold phiInt phiLocal
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [eventInt_exact]
  change ((Fintype.card S^(4*Fintype.card I)):ℕ)*(incidenceEvent t tag var fac j.1 j.2).conditional (partialWeight known) -
    (((Fintype.card S):ℚ)^(2*(Fintype.card I))) = _
  have hc : ((Fintype.card S):ℚ)^(4*(Fintype.card I))*(1/(Fintype.card (Draw I S):ℚ)) = ((Fintype.card S):ℚ)^(2*(Fintype.card I)) := by
    have ht := cell_baseline_scale (I:=I) (S:=S)
    push_cast at ht
    simpa only [div_eq_mul_inv,one_mul] using ht
  push_cast
  rw [mul_sub,hc]

theorem xiInt_exact (hq : 0<(Fintype.card I)) :
    (xiInt t tag var fac pin known:ℚ) =
      ((Fintype.card S^(4*Fintype.card I)):ℕ)*xiLocal (partialWeight known) := by
  unfold xiInt xiLocal
  push_cast
  simp_rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [eventInt_exact]
  change ((Fintype.card S^(4*Fintype.card I)):ℕ)*(variableEvent (F:=F) (B:=B) (S:=S) j.1 j.2 i).conditional (partialWeight known) -
    (((Fintype.card S):ℚ)^(4*(Fintype.card I)-1)) = _
  have hc : ((Fintype.card S):ℚ)^(4*(Fintype.card I))*(1/((Fintype.card S):ℚ)) = ((Fintype.card S):ℚ)^(4*(Fintype.card I)-1) := by
    have ht := group_baseline_scale (I:=I) (S:=S) hq
    push_cast at ht
    simpa only [div_eq_mul_inv,one_mul] using ht
  push_cast
  rw [mul_sub,hc]

theorem pairInt_exact (j : I×S) :
    (pairInt t tag var fac pin known j:ℚ) =
      ((Fintype.card S^(4*Fintype.card I)):ℕ) * ∑ e : A×A,(hitPairEvent t tag var fac j.1 j.2 (pin e.1) (pin e.2)).conditional
        (partialWeight known) := by
  unfold pairInt
  rw [Int.cast_sum,Finset.mul_sum]
  exact Finset.sum_congr rfl fun e _ => eventInt_exact t tag var fac pin known (.inr (.inr (j,.inl e)))

theorem singleInt_exact (j : I×S) :
    (singleInt t tag var fac pin known j:ℚ) =
      ((Fintype.card S^(4*Fintype.card I)):ℕ) * ∑ a : A,(hitPairEvent t tag var fac j.1 j.2 (pin a) (pin a)).conditional
        (partialWeight known) := by
  unfold singleInt
  rw [Int.cast_sum,Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => eventInt_exact t tag var fac pin known (.inr (.inr (j,.inr a)))

theorem mu_ratio : sourceMu A I S=((Fintype.card A):ℚ)/((Fintype.card S^(Fintype.card I+1)):ℕ) := by
  unfold sourceMu successProb
  push_cast
  rw [pow_succ,div_eq_mul_inv,mul_comm ((Fintype.card S):ℚ) _]

theorem varInt_exact (j : I×S) :
    (varInt t tag var fac pin known j:ℚ) =
      (((Fintype.card S^(Fintype.card I+1)):ℕ):ℚ)^2*((Fintype.card S^(4*Fintype.card I)):ℕ)*varianceLocal t tag var fac pin j (sourceMu A I S) (partialWeight known) := by
  unfold varInt
  simp only [Int.cast_add,Int.cast_sub,Int.cast_mul,Int.cast_pow,Int.cast_natCast,Int.cast_ofNat]
  rw [pairInt_exact,singleInt_exact,mu_ratio]
  unfold varianceLocal
  have hp : ((((Fintype.card S^(Fintype.card I+1)):ℕ):ℚ)) ≠ 0 := by
    have hr : (0:ℚ)<(Fintype.card S) := by exact_mod_cast (Fintype.card_pos : 0<(Fintype.card S))
    push_cast
    exact pow_ne_zero _ hr.ne'
  field_simp [hp]

theorem exact_integer_source_score (hE : 0<(Fintype.card E)) (hV : 0<(Fintype.card V)) (hI : 0<(Fintype.card I)) (hA : 0<(Fintype.card A)) :
    (integerScore t tag var fac pin known:ℚ) =
      (sharedDen E V A I S:ℚ)*localScore t tag var fac pin (sourceMu A I S) (partialWeight known) := by
  unfold integerScore
  simp only [Int.cast_sum, Int.cast_add,Int.cast_mul,Int.cast_pow,Int.cast_natCast,Int.cast_ofNat]
  rw [phiInt_exact _ _ _ _ _ _,xiInt_exact _ _ _ _ _ _ hI]
  simp_rw [varInt_exact t tag var fac pin known]
  rw [← Finset.mul_sum]
  unfold sharedDen localScore
  rw [mu_ratio]
  have he : (0:ℚ)<(Fintype.card E) := by exact_mod_cast hE
  have hv : (0:ℚ)<(Fintype.card V) := by exact_mod_cast hV
  have hi : (0:ℚ)<(Fintype.card I) := by exact_mod_cast hI
  have ha : (0:ℚ)<(Fintype.card A) := by exact_mod_cast hA
  have hr : (0:ℚ)<(Fintype.card S) := by exact_mod_cast (Fintype.card_pos : 0<(Fintype.card S))
  push_cast
  field_simp [he.ne',hv.ne',hi.ne',ha.ne',hr.ne']

theorem exact_integer_comparison (hE : 0<(Fintype.card E)) (hV : 0<(Fintype.card V)) (hI : 0<(Fintype.card I)) (hA : 0<(Fintype.card A))
    (other : P → Option S) :
    integerScore t tag var fac pin known < integerScore t tag var fac pin other ↔
      localScore t tag var fac pin (sourceMu A I S) (partialWeight known) <
      localScore t tag var fac pin (sourceMu A I S) (partialWeight other) := by
  have hS : 0<(Fintype.card S) := Fintype.card_pos
  have hd : (0:ℚ)<sharedDen E V A I S := by
    exact_mod_cast (show 0<sharedDen E V A I S by unfold sharedDen; positivity)
  have hh : ((integerScore t tag var fac pin known:ℚ)<(integerScore t tag var fac pin other:ℚ)) ↔
      integerScore t tag var fac pin known < integerScore t tag var fac pin other := Int.cast_lt
  rw [← hh,exact_integer_source_score _ _ _ _ _ _ hE hV hI hA,
    exact_integer_source_score _ _ _ _ _ _ hE hV hI hA]
  exact mul_lt_mul_iff_right₀ hd

#print axioms eventInt_exact
#print axioms cell_baseline_scale
#print axioms group_baseline_scale
#print axioms phiInt_exact
#print axioms xiInt_exact
#print axioms pairInt_exact
#print axioms singleInt_exact
#print axioms mu_ratio
#print axioms varInt_exact
#print axioms exact_integer_source_score
#print axioms exact_integer_comparison

end
end J1R43Literal