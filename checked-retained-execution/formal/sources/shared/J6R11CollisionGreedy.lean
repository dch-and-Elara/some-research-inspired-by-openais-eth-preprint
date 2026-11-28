import J6R11Collision
import GuardExpectation

/-!
# Exact conditional-expectation score for source labels

A candidate choice fixes one vertex marginal to a Dirac mass.
The conditional score is evaluated from ordered edge pairs: on each
side use 1 for an identical endpoint, otherwise the dot product
of its two marginals. Thus no enumeration of complete labelings
is part of evaluating a conditional score. This is a finite
greedy-correctness certificate, not a formal Turing-runtime theorem.
-/

open scoped BigOperators Classical

namespace J6R11CollisionGreedy
open J6R11Collision DiagonalAbundance
noncomputable section
universe u v w a

abbrev ind := J1MainSourceCollision.indicator

section Weighted
variable {I : Type*} {A : Type a} [Fintype I] [Fintype A]

def equalityMass (w : I → A → ℚ) (i j : I) : ℚ :=
  if i=j then 1 else ∑ v : A,w i v*w j v

theorem average_eq_indicator (w : I → A → ℚ) (hn : ∀ i, ∑ a, w i a=1) (i j : I) :
    GuardExpectation.average w (fun z => ind (z i=z j))=equalityMass w i j := by
  classical
  by_cases hij : i=j
  · subst j
    simpa [ind,J1MainSourceCollision.indicator,equalityMass] using
      GuardExpectation.average_const w hn (1:ℚ)
  · have expn (z : I→A) : ind (z i=z j)=
        ∑ a : A, ind (z i=a)*ind (z j=a) := by
      rw [Finset.sum_eq_single_of_mem (z i) (Finset.mem_univ _)]
      · simp [ind,J1MainSourceCollision.indicator,eq_comm]
      · intro a _ ha
        simp [ind,J1MainSourceCollision.indicator,Ne.symm ha]
    simp_rw [expn]
    rw [GuardExpectation.average_sum]
    unfold equalityMass
    rw [if_neg hij]
    apply Finset.sum_congr rfl
    intro h _
    rw [GuardExpectation.average_pair w hn hij (fun a => ind (a=h)) (fun a => ind (a=h))]
    simp [ind,J1MainSourceCollision.indicator]

end Weighted

variable {E : Type u} {R : Type v} {C : Type w} {A : Type a}
  [Fintype E] [Fintype R] [Fintype C] [Fintype A] [Nonempty A]

def splitSample : (R⊕C→A) ≃ Sample R C A where
  toFun z := (fun r => z (.inl r),fun c => z (.inr c))
  invFun z := Sum.elim z.1 z.2
  left_inv z := funext (fun i => by cases i <;> rfl)
  right_inv z := by cases z; rfl

omit [Fintype E] [Nonempty A] in
theorem average_split (w : R⊕C → A → ℚ) (fr : (R→A)→ℚ) (fc : (C→A)→ℚ) :
    GuardExpectation.average w (fun z => fr (splitSample z).1*fc (splitSample z).2) =
      GuardExpectation.average (fun i => w (.inl i)) fr *
        GuardExpectation.average (fun i => w (.inr i)) fc := by
  let F := fun z : Sample R C A =>
    (GuardExpectation.productMass (fun i => w (.inl i)) z.1*fr z.1) *
      (GuardExpectation.productMass (fun i => w (.inr i)) z.2*fc z.2)
  calc
    _ = ∑ z : R⊕C→A, F (splitSample z) := by
      unfold GuardExpectation.average F
      apply Finset.sum_congr rfl
      intro z _
      unfold GuardExpectation.productMass
      rw [Fintype.prod_sum_type]
      simp only [splitSample,Equiv.coe_fn_mk]
      ring
    _ = ∑ z : Sample R C A, F z := Equiv.sum_comp splitSample F
    _ = _ := by
      unfold F GuardExpectation.average
      rw [Fintype.sum_prod_type,Finset.sum_mul]
      simp only [Finset.mul_sum]

omit [Fintype E] [Nonempty A] in
theorem conditional_collision (row : E → R) (col : E → C) (e f : E)
    (w : R⊕C → A → ℚ) (hn : ∀ i, ∑ b, w i b=1) :
    GuardExpectation.average w (fun z =>
      ind (edgeCell row col (splitSample z) e=edgeCell row col (splitSample z) f)) =
      equalityMass w (.inl (row e)) (.inl (row f)) *
        equalityMass w (.inr (col e)) (.inr (col f)) := by
  let r := fun z : R→A => ind (z (row e)=z (row f))
  let c := fun z : C→A => ind (z (col e)=z (col f))
  have hcell (z : R⊕C→A) :
      ind (edgeCell row col (splitSample z) e=edgeCell row col (splitSample z) f) =
        r (splitSample z).1*c (splitSample z).2 := by
    by_cases hR : z (.inl (row e))=z (.inl (row f)) <;>
      by_cases hC : z (.inr (col e))=z (.inr (col f)) <;>
        simp [ind,J1MainSourceCollision.indicator,edgeCell,splitSample,r,c,hR,hC]
  simp_rw [hcell]
  rw [average_split w r c]
  unfold r c
  rw [average_eq_indicator (fun i => w (.inl i)) (fun i => hn (.inl i)) (row e) (row f),
    average_eq_indicator (fun i => w (.inr i)) (fun i => hn (.inr i)) (col e) (col f)]
  simp [equalityMass]

omit [Fintype E] [Fintype R] [Fintype C] [Nonempty A] in
private theorem average_sub {I : Type*} [Fintype I] [DecidableEq I] (w : I → A → ℚ)
    (f g : (I→A) → ℚ) :
    GuardExpectation.average w (fun z => f z-g z)=
      GuardExpectation.average w f - GuardExpectation.average w g := by
  simp only [GuardExpectation.average,mul_sub,Finset.sum_sub_distrib]

/-- Formula evaluated by the source's candidate-label test. It is
a finite sum over exactly M² ordered pairs of two marginal overlaps. -/
def compressed (row : E → R) (col : E → C) (w : R⊕C→A→ℚ) : ℚ :=
  (∑ ef : E×E, equalityMass w (.inl (row ef.1)) (.inl (row ef.2)) *
                 equalityMass w (.inr (col ef.1)) (.inr (col ef.2))) -
    (Fintype.card E:ℚ)^2/(Fintype.card (A×A):ℚ)

theorem compressed_correct (row : E → R) (col : E → C) (w : R⊕C→A→ℚ)
    (hn : ∀ i, ∑ b, w i b=1) :
    GuardExpectation.average w (fun z =>
      J1MainSourceCollision.deviation (edgeCell row col (splitSample z))) =
      compressed row col w := by
  let g := fun (ef : E×E) (z : R⊕C→A) => ind (edgeCell row col (splitSample z) ef.1 =
    edgeCell row col (splitSample z) ef.2)
  let k := (Fintype.card E:ℚ)^2/(Fintype.card (A×A):ℚ)
  simp_rw [squared_load_identity]
  change GuardExpectation.average w (fun z => (∑ q, g q z)-k) = _
  rw [average_sub w (fun z => ∑ q, g q z) (fun _ => k),
    GuardExpectation.average_sum w g,GuardExpectation.average_const w hn k]
  unfold compressed
  congr 1
  apply Finset.sum_congr rfl
  intro ef _
  exact conditional_collision row col ef.1 ef.2 w hn

theorem greedy_step (row : E → R) (col : E → C) (w : R⊕C→A→ℚ)
    (h0 : ∀ i b, 0≤w i b) (hn : ∀ i, ∑ b,w i b=1) (i : R⊕C) :
    ∃ b : A, compressed row col (GuardExpectation.fixAt w i b)≤compressed row col w := by
  obtain ⟨b,hb⟩ := GuardExpectation.exists_decreasing_fixAt w h0 hn
    (fun z => J1MainSourceCollision.deviation (edgeCell row col (splitSample z))) i
  rw [compressed_correct row col w hn,
    compressed_correct row col _ (GuardExpectation.fixAt_normalized w hn i b)] at hb
  exact ⟨b,hb⟩

omit [Fintype E] [Fintype R] [Fintype C] [Nonempty A] in
theorem uniform_product_mean {I : Type*} [Fintype I] [DecidableEq I] (f : (I→A) → ℚ) :
    GuardExpectation.average (fun _ _ => (Fintype.card A:ℚ)⁻¹) f=mean f := by
  simp only [GuardExpectation.average,GuardExpectation.productMass,Finset.prod_const,
    Finset.card_univ,mean,Fintype.card_fun,Nat.cast_pow,inv_pow,div_eq_mul_inv]
  rw [← Finset.mul_sum]
  ring

/-- Applying the finite greedy conditioning construction gives an
actual label assignment with the original graph variance bound. -/
theorem labels_by_conditioning (row : E → R) (col : E → C) (Δ : ℕ)
    (hr : ∀ v, (fibre row v).card≤Δ) (hc : ∀ v, (fibre col v).card≤Δ) :
    ∃ z : Sample R C A, J1MainSourceCollision.deviation (edgeCell row col z)≤
      2*(Fintype.card E:ℚ)*Δ := by
  let w : R⊕C→A→ℚ := fun _ _ => (Fintype.card A:ℚ)⁻¹
  have hn (i : R⊕C) : ∑ b, w i b=1 := by
    simp [w,nsmul_eq_mul]
  have h0 (i : R⊕C) (b : A) : 0≤w i b := by
    dsimp [w]
    positivity
  let F := fun z : R⊕C→A => J1MainSourceCollision.deviation (edgeCell row col (splitSample z))
  let G := fun z : Sample R C A => J1MainSourceCollision.deviation (edgeCell row col z)
  obtain ⟨z,hz⟩ := GuardExpectation.exists_sample_by_conditioning w h0 hn F
  use splitSample z
  change F z ≤ GuardExpectation.average (fun _ _ => (Fintype.card A:ℚ)⁻¹) F at hz
  rw [uniform_product_mean (I:=R⊕C) (A:=A) F] at hz
  have he : mean F=mean G := mean_equiv splitSample G
  rw [he] at hz
  exact hz.trans (expected_squared_loads row col Δ hr hc)

#print axioms average_eq_indicator
#print axioms conditional_collision
#print axioms compressed_correct
#print axioms greedy_step
#print axioms uniform_product_mean
#print axioms labels_by_conditioning

end
end J6R11CollisionGreedy

