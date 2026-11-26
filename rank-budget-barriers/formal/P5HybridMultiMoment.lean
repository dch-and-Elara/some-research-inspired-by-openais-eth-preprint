import P5HybridClosureMoment

/-! X1: arbitrary finite (dependent) collection of layouts. Only the
coordinates within a single layout have a product-uniform comparison.
The vertex laws of different layouts may be arbitrarily correlated. -/
namespace Paper5.HybridMulti
open scoped BigOperators Classical
open Paper5.HybridClosure GraphCutMoments EmpiricalCutMoments

theorem mean_square_finite_sum {V S : Type*} [Fintype V] [Nonempty V]
    (F : S→V→ℚ) (H : S→ℚ) (s : Finset S)
    (hH : ∀ j∈s,0≤H j)
    (hF : ∀ j∈s,(∑ v,(F j v)^2)/(Fintype.card V:ℚ)≤(H j)^2) :
    (∑ v,(∑ j∈s,F j v)^2)/(Fintype.card V:ℚ)≤(∑ j∈s,H j)^2 := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
    simp_rw [Finset.sum_insert hj]
    have hJ := Finset.mem_insert_self j s
    have hSum : 0≤∑ a∈s,H a := Finset.sum_nonneg (fun a ha=>hH a (Finset.mem_insert_of_mem ha))
    exact mean_square_add_bound (F j) (fun v=>∑ a∈s,F a v) (H j) (∑ a∈s,H a)
      (hH j hJ) hSum (hF j hJ)
      (ih (fun a ha=>hH a (Finset.mem_insert_of_mem ha))
        (fun a ha=>hF a (Finset.mem_insert_of_mem ha)))

section Family
variable {V S : Type*} {I A : S→Type*} [Fintype S]
  [Fintype V] [DecidableEq V] [Nonempty V]
  [∀ s,Fintype (I s)] [∀ s,DecidableEq (I s)]
  [∀ s,Fintype (A s)] [∀ s,DecidableEq (A s)] [∀ s,Nonempty (A s)]

def combinedCuts (L : ∀ s,V→I s→A s) (symbols : ∀ s,I s→Finset (A s)) :
    (Σ s,I s)→Finset V := fun j=>labelCut (L j.1) id (symbols j.1) j.2

theorem weighted_multi_layout_moment
    (L : ∀ s,V→I s→A s) (symbols : ∀ s,I s→Finset (A s))
    (C w H : S→ℚ) (hC : ∀ s,0≤C s) (hH : ∀ s,0≤H s)
    (hDom : ∀ s x,empiricalLaw (L s) x≤C s*ProductVariance.uniformWeight (I s→A s))
    (hNorm : ∀ s,(w s)^2*C s*(Fintype.card (I s):ℚ)≤(H s)^2)
    (eps : (Σ s,I s)→Bool) :
    let cut := combinedCuts L symbols
    (∑ v,(BangCore.signedTotal (fun j v=>w j.1*(cutBit ℚ (cut j) v-
      cutDensity (cut j))) eps v)^2)/(Fintype.card V:ℚ)≤(∑ s,H s)^2 := by
  let cut := combinedCuts L symbols
  let f (s : S) := BangCore.signedTotal
    (fun i v=>w s*(cutBit ℚ (labelCut (L s) id (symbols s) i) v-
      cutDensity (labelCut (L s) id (symbols s) i))) (fun i=>eps ⟨s,i⟩)
  have hf (v : V) :
      BangCore.signedTotal (fun j v=>w j.1*(cutBit ℚ (cut j) v-cutDensity (cut j))) eps v =
        ∑ s,f s v := by
    rw [BangCore.signedTotal,Fintype.sum_sigma]
    rfl
  change (∑ v,(BangCore.signedTotal (fun j v=>w j.1*(cutBit ℚ (cut j) v-
    cutDensity (cut j))) eps v)^2)/(Fintype.card V:ℚ)≤_
  simp_rw [hf]
  exact mean_square_finite_sum f H Finset.univ (fun s _=>hH s) (fun s _=>
    weighted_one_route_moment (L s) (symbols s) (C s) (w s) (H s)
      (hC s) (hDom s) (hNorm s) _)

end Family

#print axioms mean_square_finite_sum
#print axioms weighted_multi_layout_moment
end Paper5.HybridMulti
