import P11R12ProbabilityMarginal
import P11R12ProbabilityIndexed
import Mathlib.Tactic

/-! Actual independent-type draw has the P11 expected number of fully
seated binary subdivision columns. Same-type legs deliberately share
one permutation; different-type legs use separate product coordinates. -/
namespace P11R12Probability
open scoped Classical BigOperators
open P11FullPacking P11R12Choice P11SourceGeometry RandomEndpoint
variable {K W : Type*} [LinearOrder K] [Fintype W] {a b n : ℕ}

theorem real_pair_lower (f : W → Cell (Fin a) K)
    (cap : ∀ c, Nat.card (RealFiber f c) ≤ b*2^a)
    (w w' : W) (distinct : w≠w')
    (hk : key (f w)=key (f w')) (hcol : ∀ i, (f w i).2=(f w' i).2)
    (right : Bool) (hb : 0<b) (hH : 1<b*2^a) :
    (1-1/(b:ℚ))/((2^a:ℕ):ℚ)^2 ≤
      probability (uniform (TypeDraw b (key (f w))))
        (fun z => realEvent f cap w right z ∧
          realEvent f cap w' right (cast (congrArg (TypeDraw b) hk) z)) := by
  classical
  have hc : f w=f w' := same_key_same_column _ _ hk hcol
  let k := key (f w)
  let c := orientation (f w)
  have h' (z : TypeDraw b k) :
    realEvent f cap w' right (cast (congrArg (TypeDraw b) hk) z) =
      endpointEvent k c (realIndex f cap w') right z := by
    have he := realEvent_at_cell f cap w' right (f w) hc.symm z
    have hp : congrArg (fun d : Cell (Fin a) K => TypeDraw b (key d)) hc.symm.symm =
        congrArg (TypeDraw b) hk := Subsingleton.elim _ _
    rw [hp] at he
    exact he
  have he (z : TypeDraw b k) :
      (realEvent f cap w right z ∧ realEvent f cap w' right (cast (congrArg (TypeDraw b) hk) z)) ↔
        (endpointEvent k c (realIndex f cap w) right z ∧ endpointEvent k c (realIndex f cap w') right z) := by
    rw [h']
    rfl
  rw [event_congr _ _ _ he]
  exact uniform_same_cell_pair k c _ _ (sameCell_index_ne f cap w w' hc distinct) right hb hH

theorem coordinate_single (e : Fin n ≃ Key (Fin a) K) (f : W → Cell (Fin a) K)
    (cap : ∀ c, Nat.card (RealFiber f c) ≤ b*2^a) (right : Bool) (w : W) (hb : 0<b) :
    probability (sampleWeight b e (legType e f w)) (fun x => hit e f cap right w x=true) =
      1/((2^a:ℕ):ℚ) := by
  calc
    _ = probability (uniform (TypeDraw b (key (f w)))) (realEvent f cap w right) :=
      uniform_transport (fromCoordinate e f w) _ _ (by intro x; simp [hit])
    _ = _ := uniform_single_endpoint _ _ _ right hb

theorem coordinate_same (e : Fin n ≃ Key (Fin a) K) (f : W → Cell (Fin a) K)
    (cap : ∀ c, Nat.card (RealFiber f c) ≤ b*2^a)
    (w w' : W) (different : w≠w') (h : legType e f w=legType e f w')
    (hcol : ∀ i, (f w i).2=(f w' i).2)
    (right : Bool) (hb : 0<b) (hH : 1<b*2^a) :
    (1-1/(b:ℚ))/((2^a:ℕ):ℚ)^2 ≤
      probability (sampleWeight b e (legType e f w))
        (fun x => hit e f cap right w x=true ∧
          hit e f cap right w' (cast (congrArg (Indexed b e) h) x)=true) := by
  have hk : key (f w)=key (f w') := e.symm.injective h
  rw [show probability (sampleWeight b e (legType e f w))
        (fun x => hit e f cap right w x=true ∧
          hit e f cap right w' (cast (congrArg (Indexed b e) h) x)=true) =
      probability (uniform (TypeDraw b (key (f w))))
        (fun z => realEvent f cap w right z ∧
          realEvent f cap w' right (cast (congrArg (TypeDraw b) hk) z)) from
    uniform_transport (fromCoordinate e f w) _ _ (by
      intro x
      simp only [hit,decide_eq_true_eq]
      rw [fromCoordinate_transport e f w w' h x])]
  exact real_pair_lower f cap w w' different hk hcol right hb hH

omit [Fintype W] in
theorem expected_actual_endpoints {E : Type*} [Fintype E]
    (e : Fin n ≃ Key (Fin a) K) (f : E×Bool → Cell (Fin a) K)
    (cap : ∀ c, Nat.card (RealFiber f c) ≤ b*2^a)
    (column : ∀ v i, (f (v,false) i).2=(f (v,true) i).2)
    (right : Bool) (hb : 0<b) (hH : 1<b*2^a) :
    (Fintype.card E:ℚ)*((1-1/(b:ℚ))/((2^a:ℕ):ℚ)^2) ≤
      PacketVariance.avg (PacketVariance.product (sampleWeight b e))
        (fun x => ((seated Finset.univ (fun v s => seat (toDraw e x) f cap (v,s)) right).card:ℚ)) := by
  classical
  refine mean_from_type_laws (sampleWeight b e) (sampleWeight_prob b e)
    (fun x v s => seat (toDraw e x) f cap (v,s)) right
    (fun v s => legType e f (v,s)) (fun v s => hit e f cap right (v,s))
    (fun x v s => chart e f cap right x (v,s)) _ ?_ ?_
  · intro v h
    have hne : (v,false) ≠ (v,true) := fun hx => Bool.false_ne_true (congrArg Prod.snd hx)
    exact coordinate_same e f cap (v,false) (v,true) hne h (column v) right hb hH
  · intro v _
    rw [coordinate_single e f cap right (v,false) hb,
      coordinate_single e f cap right (v,true) hb]
    have hcalc : (1/((2^a:ℕ):ℚ))*(1/((2^a:ℕ):ℚ))=1/(((2^a:ℕ):ℚ)^2) := by ring
    rw [hcalc]
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith [show 0≤(1/(b:ℚ)) by positivity]

#print axioms real_pair_lower
#print axioms coordinate_single
#print axioms coordinate_same
#print axioms expected_actual_endpoints
end P11R12Probability
