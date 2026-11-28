import J1R43LiteralScore
import J1MainSourceBridge

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5100000
set_option linter.unusedSectionVars false

/-! The very same score whose compact conditional evaluator is used
by the driver has uniform mean < 2 on the physical primitive charts.
These are pointwise extraction statements, not an unrelated existence
certificate. -/
namespace J1R43Literal
open scoped BigOperators
open DiagonalAbundance J1MainSourceLabels J1MainSourceCollision J1MainSourceBridge

section Bound
variable {Z J : Type*} [Fintype J]

theorem joint_mean_lt [Fintype Z] [Nonempty Z]
    (base : Z → ℚ) (X : J → Z → ℚ) (mu cap : ℚ) (hm : 0<mu)
    (hb : mean base≤cap) (hv : ∀ j, mean (fun z => (X j z-mu)^2)≤mu)
    (hcap : cap+8*(Fintype.card J:ℚ)/mu<2) :
    mean (jointScore base X mu)<2 := by
  have hsum : (∑ j, mean (fun z => (X j z-mu)^2)) ≤ (Fintype.card J:ℚ)*mu := by
    simpa [nsmul_eq_mul] using (Finset.sum_le_sum (s:=(Finset.univ : Finset J)) fun j _ => hv j)
  have H : (8:ℚ)*(∑ j, mean (fun z => (X j z-mu)^2))/mu^2 ≤ 8*(Fintype.card J:ℚ)/mu :=
    calc
      _ ≤ 8*((Fintype.card J:ℚ)*mu)/mu^2 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsum (by norm_num)) (sq_nonneg mu)
      _ = _ := by field_simp
  unfold jointScore
  rw [mean_lin_add,mean_const_div,mean_scale,mean_sum]
  linarith

theorem pointwise_certificate (base : Z → ℚ) (X : J → Z → ℚ) (mu : ℚ)
    (hm : 0<mu) {z : Z} (hb : 0≤base z) (hs : jointScore base X mu z<2) :
    base z<2 ∧ ∀ j, mu/2<X j z := by
  have hp : 0≤(8:ℚ)*(∑ j,(X j z-mu)^2)/mu^2 := by positivity
  unfold jointScore at hs
  refine ⟨by linarith,?_⟩
  intro j
  have hsq : (X j z-mu)^2≤∑ i,(X i z-mu)^2 :=
    Finset.single_le_sum (f:=fun i=>(X i z-mu)^2) (fun _ _=>sq_nonneg _) (Finset.mem_univ j)
  have hscaled := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hsq (show (0:ℚ)≤8 by norm_num)) (sq_nonneg mu)
  have hraw : 8*(X j z-mu)^2<2*mu^2 := by
    apply (div_lt_iff₀ (sq_pos_of_pos hm)).mp
    linarith
  by_contra! hlow
  have hnon : 0≤(mu/2-X j z)*(3*mu/2-X j z) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith

end Bound

section Source
variable {V F B I S E A : Type*}
  [Fintype V] [Fintype F] [Fintype B] [Fintype I] [Fintype S] [Fintype E] [Fintype A]
  [DecidableEq V] [DecidableEq F] [DecidableEq B] [DecidableEq I] [DecidableEq S]
  [Nonempty I] [Nonempty S] [Nonempty A]

local notation "P" => Primitive V F B I

noncomputable def sourceMu (A I S : Type*) [Fintype A] [Fintype I] [Fintype S] : ℚ :=
  (Fintype.card A:ℚ)*successProb (I:=I) (S:=S)

theorem sourceMu_pos : 0<sourceMu A I S := by
  have hA : (0:ℚ)<Fintype.card A := by exact_mod_cast (Fintype.card_pos : 0<Fintype.card A)
  have hS : (0:ℚ)<Fintype.card S := by exact_mod_cast (Fintype.card_pos : 0<Fintype.card S)
  unfold sourceMu successProb
  positivity

theorem chart_actual_count (special : I) (tie : F → Option B) (var : E → V) (fac : E → F)
    (pin : A → E) (pvar : A ↪ V) (pfac : A ↪ F) (pvertex : A ↪ V) (block : V → B)
    (hv : ∀ a, var (pin a)=pvar a) (hf : ∀ a, fac (pin a)=pfac a)
    (ht : ∀ a, tie (pfac a)=some (block (pvertex a)))
    (hind : ∀ a a', ¬triangleEdge block (pvertex a) (pvertex a'))
    (z : P → S) (j : I×S) :
    let key : A × Bool × I ↪ P := ⟨drawKey special tie pvar pfac,
      tied_drawKey_injective special tie pvar pfac pvertex block ht hind⟩
    actualCount special tie var fac pin j z = hitCount j.1 j.2 ((chart (S:=S) key) z).1 := by
  dsimp only
  unfold actualCount
  congr 1
  rw [chart_tied_words special tie pvar pfac pvertex block ht hind]
  funext a
  change literalCell special tie var fac z (pin a)=_
  simp [literalCell,hv,hf]

theorem chart_actual_variance (special : I) (tie : F → Option B) (var : E → V)
    (fac : E → F) (pin : A → E) (pvar : A ↪ V) (pfac : A ↪ F) (pvertex : A ↪ V)
    (block : V → B)
    (hv : ∀ a, var (pin a)=pvar a) (hf : ∀ a, fac (pin a)=pfac a)
    (ht : ∀ a, tie (pfac a)=some (block (pvertex a)))
    (hind : ∀ a a', ¬triangleEdge block (pvertex a) (pvertex a')) (j : I×S) :
    mean (fun z => (actualCount special tie var fac pin j z-sourceMu A I S)^2) ≤ sourceMu A I S := by
  classical
  let key : A × Bool × I ↪ P := ⟨drawKey special tie pvar pfac,
    tied_drawKey_injective special tie pvar pfac pvertex block ht hind⟩
  let Tail := {p : P // p ∉ Set.range key} → S
  letI : Fintype Tail := Fintype.ofFinite Tail
  letI : Nonempty Tail := ⟨fun _ => Classical.choice inferInstance⟩
  let C := chart (S:=S) key
  let Q : State A I S Tail → ℚ := fun x => (hitCount j.1 j.2 x.1-sourceMu A I S)^2
  have step (z : P → S) :
      (actualCount special tie var fac pin j z-sourceMu A I S)^2 = Q (C z) := by
    unfold C Q
    rw [chart_actual_count special tie var fac pin pvar pfac pvertex block hv hf ht hind]
  simp_rw [step,mean_equiv C Q]
  unfold Q
  rw [mean_extra (fun x : A → Draw I S => (hitCount j.1 j.2 x-sourceMu A I S)^2)]
  change mean (fun x : A → Draw I S => (hitCount j.1 j.2 x -
    (Fintype.card A:ℚ)*successProb (I:=I) (S:=S))^2)≤_
  rw [variance_hitCount]
  exact mul_le_of_le_one_right (sourceMu_pos (A:=A) (I:=I) (S:=S)).le (by
    have hn : 0≤successProb (I:=I) (S:=S) := by unfold successProb; positivity
    linarith)

theorem actual_joint_uniform_mean (special : I) (tie : F → Option B) (var : E → V)
    (fac : E → F) (pin : A → E) (pvar : A ↪ V) (pfac : A ↪ F) (pvertex : A ↪ V)
    (block : V → B)
    (hv : ∀ a, var (pin a)=pvar a) (hf : ∀ a, fac (pin a)=pfac a)
    (ht : ∀ a, tie (pfac a)=some (block (pvertex a)))
    (hind : ∀ a a', ¬triangleEdge block (pvertex a) (pvertex a'))
    (N : ℕ) (hN : 0<N) (hM : Fintype.card E=12*N) (hn : Fintype.card V=4*N)
    (hphi : mean (incidenceCost (S:=S) special tie var fac)≤4*(12*(N:ℚ))+2*N)
    (hxi : mean (variableCost (V:=V) (F:=F) (B:=B) (I:=I) (S:=S))≤(Fintype.card I:ℚ)*(4*(N:ℚ)))
    (hsize : 48*Fintype.card I*Fintype.card S^2*Fintype.card S^Fintype.card I<Fintype.card A) :
    mean (printedScore (S:=S) special tie var fac pin (sourceMu A I S))<2 := by
  have hd : (0:ℚ)<Fintype.card I := by exact_mod_cast (Fintype.card_pos : 0<Fintype.card I)
  have hNr : (0:ℚ)<N := by exact_mod_cast hN
  unfold printedScore
  apply joint_mean_lt _ _ _ (11/6) (sourceMu_pos (A:=A) (I:=I) (S:=S))
  · simpa only [hM,hn,Nat.cast_mul,Nat.cast_ofNat] using source_base_cost N _ hNr hd _ _ hphi hxi
  · exact chart_actual_variance special tie var fac pin pvar pfac pvertex block hv hf ht hind
  · exact explicit_size_guard hsize

end Source

#print axioms joint_mean_lt
#print axioms pointwise_certificate
#print axioms sourceMu_pos
#print axioms chart_actual_count
#print axioms chart_actual_variance
#print axioms actual_joint_uniform_mean

end J1R43Literal