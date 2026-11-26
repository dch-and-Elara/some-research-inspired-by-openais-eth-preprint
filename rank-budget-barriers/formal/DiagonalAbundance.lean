import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic

/-! Finite uniform model of the diagonal labels used for J1.
The other randomized layout costs are kept separate from the diagonal-hit
calculation. In particular the slot-collision bound is not an axiom. -/
namespace DiagonalAbundance
open scoped BigOperators
universe u v w c

/-- Exact uniform mean; rational finite sums only. -/
def mean {A : Type u} [Fintype A] (f : A → ℚ) : ℚ :=
  (∑ a, f a) / (Fintype.card A : ℚ)

private theorem card_ne_zero_rat (A : Type u) [Fintype A] [Nonempty A] :
    (Fintype.card A : ℚ) ≠ 0 := by
  exact_mod_cast (Fintype.card_ne_zero : Fintype.card A ≠ 0)

theorem mean_const {A : Type u} [Fintype A] [Nonempty A] (x : ℚ) :
    mean (fun _ : A => x) = x := by
  simp [mean,nsmul_eq_mul]

theorem mean_lin_add {A : Type u} [Fintype A] (f g : A → ℚ) :
    mean (fun a => f a + g a) = mean f + mean g := by
  rw [mean,Finset.sum_add_distrib,add_div]
  rfl

theorem mean_lin_sub {A : Type u} [Fintype A] (f g : A → ℚ) :
    mean (fun a => f a - g a) = mean f - mean g := by
  rw [mean,Finset.sum_sub_distrib,sub_div]
  rfl

theorem mean_scale {A : Type u} [Fintype A] (q : ℚ) (f : A → ℚ) :
    mean (fun a => q * f a) = q * mean f := by
  rw [mean,← Finset.mul_sum,mul_div_assoc]
  rfl

theorem mean_sum {A : Type u} {J : Type v} [Fintype A] [Fintype J] (f : J → A → ℚ) :
    mean (fun a => ∑ i, f i a) = ∑ i, mean (f i) := by
  unfold mean
  rw [Finset.sum_comm,← Finset.sum_div]

theorem mean_mono {A : Type u} [Fintype A] (f g : A → ℚ) (h : ∀ a, f a ≤ g a) :
    mean f ≤ mean g := by
  unfold mean
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun i _ => h i)) (by positivity)

theorem mean_equiv {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    (e : A ≃ B) (f : B → ℚ) :
    mean (fun a => f (e a)) = mean f := by
  unfold mean
  rw [Fintype.card_congr e,Equiv.sum_comp e f]

theorem mean_product {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    (f : A → ℚ) (g : B → ℚ) :
    mean (fun p : A × B => f p.1 * g p.2) = mean f * mean g := by
  have hsum : (∑ p : A×B, f p.1 * g p.2) = (∑ a, f a) * ∑ b, g b := by
    rw [Fintype.sum_prod_type]
    simp_rw [←Finset.mul_sum]
    rw [Finset.sum_mul]
  simp [mean,hsum,div_mul_div_comm]

/-- One coordinate of a uniform random function is itself uniform. -/
theorem mean_coordinate {A : Type u} {D : Type v}
    [Fintype A] [DecidableEq A] [Fintype D] [Nonempty D] (a : A) (f : D → ℚ) :
    mean (fun x : A → D => f (x a)) = mean f := by
  let e := Equiv.funSplitAt a D
  have hm : mean (fun p : D × ({j // j ≠ a} → D) => f p.1 * 1) = mean f := by
    rw [mean_product f (fun _ : {j // j ≠ a} → D => 1),mean_const,mul_one]
  have he := mean_equiv e (fun p : D × ({j // j ≠ a} → D) => f p.1 * 1)
  simpa [e] using he.trans hm

/-- Different coordinates in the full configuration space are independent. -/
theorem mean_coordinates_mul {A : Type u} {D : Type v}
    [Fintype A] [DecidableEq A] [Fintype D] [Nonempty D] (a b : A) (hab : b ≠ a)
    (f g : D → ℚ) :
    mean (fun x : A → D => f (x a) * g (x b)) = mean f * mean g := by
  let e := Equiv.funSplitAt a D
  let h : ({j // j ≠ a} → D) → ℚ := fun x => g (x ⟨b,hab⟩)
  have he := mean_equiv e (fun p : D × ({j // j ≠ a} → D) => f p.1 * h p.2)
  change mean (fun x : A → D => f (x a) * g (x b)) =
    mean (fun p : D × ({j // j ≠ a} → D) => f p.1 * h p.2) at he
  rw [he,mean_product]
  congr 1
  exact mean_coordinate (A := {j : A // j ≠ a}) (D := D) ⟨b,hab⟩ g

/-- The diagonal success indicator for two independent words, at one specified symbol. -/
noncomputable def hit {I : Type u} {S : Type v} (i : I) (s : S)
    (p : (I → S) × (I → S)) : ℚ := by
  classical
  exact if p.1 = p.2 ∧ p.1 i = s then 1 else 0

theorem hit_sq {I : Type u} {S : Type v} (t : I) (g : S) (p : (I → S) × (I → S)) :
    hit t g p ^ 2 = hit t g p := by
  classical
  unfold hit
  split <;> norm_num

/-- Exact Bernoulli probability 1/(r K), K=r^Q. -/
theorem mean_hit {I : Type u} {S : Type v} [Fintype I] [DecidableEq I]
    [Fintype S] [Nonempty S] (t : I) (g : S) :
    mean (hit t g) = ((Fintype.card S : ℚ) * (Fintype.card (I → S) : ℚ))⁻¹ := by
  classical
  let f : (I → S) → ℚ := fun x => if x t = g then 1 else 0
  have hrow (x : I → S) : (∑ y : I → S, hit t g (x,y)) = f x := by
    rw [Finset.sum_eq_single x]
    · simp [hit,f]
    · intro y _ hy
      simp [hit,Ne.symm hy]
    · simp
  have hcol : (∑ s : S, if s = g then (1 : ℚ) else 0) = 1 := by simp
  have hsymbol : mean f = 1 / (Fintype.card S : ℚ) := by
    rw [show mean f = mean (fun s : S => if s = g then (1 : ℚ) else 0) from
      mean_coordinate (A := I) (D := S) t (fun s => if s = g then (1 : ℚ) else 0)]
    rw [mean,hcol]
  calc
    mean (hit t g) = (∑ x : I→S, f x) / ((Fintype.card (I→S) : ℚ) *
        (Fintype.card (I→S) : ℚ)) := by
      simp [mean,Fintype.sum_prod_type,hrow]
    _ = mean f / (Fintype.card (I→S) : ℚ) := by rw [mean,div_div]
    _ = _ := by rw [hsymbol,div_div,one_div]

#print axioms mean_coordinates_mul
#print axioms mean_hit


/-- First moment of a distribution can only be low if an actual finite
configuration is low.  No hypotheses about independent event counts. -/
theorem exists_below_mean_bound {A : Type u} [Fintype A] [Nonempty A]
    (f : A → ℚ) (bound : ℚ) (h : mean f < bound) :
    ∃ a, f a < bound := by
  by_contra! hh
  have := mean_mono (fun _ : A => bound) f hh
  rw [mean_const] at this
  exact (not_lt_of_ge this) h

theorem mean_const_div {A : Type u} [Fintype A] (f : A → ℚ) (d : ℚ) :
    mean (fun a => f a / d) = mean f / d := by
  unfold mean
  rw [← Finset.sum_div]
  ring

/-- Joint score used to control all symbol groups at once. -/
def jointScore {A : Type u} {J : Type v} [Fintype J]
    (layoutCost : A → ℚ) (X : J → A → ℚ) (mu : ℚ) (a : A) : ℚ :=
  layoutCost a + 8 * (∑ j, (X j a - mu)^2) / mu^2

/-- The second-moment bound for each group suffices. The groups need not be
independent of each other or of the separate layout cost. -/
theorem joint_score_certificate {A : Type u} {J : Type v}
    [Fintype A] [Nonempty A] [Fintype J] (layoutCost : A → ℚ)
    (X : J → A → ℚ) (mu base : ℚ)
    (hmu : 0 < mu) (h0 : ∀ a, 0 ≤ layoutCost a)
    (hbase : mean layoutCost ≤ base)
    (hvar : ∀ j, mean (fun a => (X j a - mu)^2) ≤ mu)
    (hthreshold : base + 8*(Fintype.card J : ℚ)/mu < 2) :
    ∃ a, jointScore layoutCost X mu a < 2 ∧ layoutCost a < 2 ∧
      ∀ j, mu/2 < X j a := by
  classical
  have hs : (∑ j, mean (fun a => (X j a - mu)^2)) ≤ (Fintype.card J : ℚ)*mu := by
    simpa [nsmul_eq_mul] using
      (Finset.sum_le_sum (s := (Finset.univ : Finset J)) fun j _ => hvar j)
  have hb : (8:ℚ)*(∑ j, mean (fun a => (X j a-mu)^2))/mu^2 ≤
      8 * (Fintype.card J : ℚ) / mu := by
    calc
      _ ≤ 8*((Fintype.card J : ℚ)*mu)/mu^2 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hs (by norm_num)) (sq_nonneg mu)
      _ = _ := by field_simp
  have hexp : mean (jointScore layoutCost X mu) < 2 := by
    change mean (fun a => layoutCost a + 8 * (∑ j, (X j a - mu)^2) / mu^2) < 2
    rw [mean_lin_add, mean_const_div, mean_scale, mean_sum]
    linarith
  obtain ⟨a, ha⟩ := exists_below_mean_bound _ _ hexp
  have hcost : layoutCost a < 2 := by
    have hp : 0 ≤ (8:ℚ) * (∑ j, (X j a - mu)^2) / mu^2 := by positivity
    unfold jointScore at ha
    linarith
  refine ⟨a,ha,hcost,?_⟩
  intro j
  have hsq : (X j a - mu)^2 ≤ ∑ i, (X i a - mu)^2 :=
    Finset.single_le_sum (f := fun i => (X i a - mu)^2)
      (fun i _ => sq_nonneg _) (Finset.mem_univ j)
  have hs' := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hsq (show (0 : ℚ) ≤ 8 by norm_num)) (sq_nonneg mu)
  have raw : 8*(X j a-mu)^2 < 2*mu^2 := by
    apply (div_lt_iff₀ (sq_pos_of_pos hmu)).mp
    unfold jointScore at ha
    linarith [h0 a]
  by_contra! hlo
  have hbad : 0 ≤ (mu/2-X j a)*(3*mu/2-X j a) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith

section Concrete
variable {A : Type u} {I : Type v} {S : Type w}

abbrev Draw (I : Type v) (S : Type w) := (I → S) × (I → S)

noncomputable def successProb [Fintype I] [Fintype S] : ℚ :=
  ((Fintype.card S : ℚ)*(Fintype.card S : ℚ) ^ Fintype.card I)⁻¹

noncomputable def hitCount [Fintype A] (t : I) (g : S) (x : A → Draw I S) : ℚ :=
  ∑ a, hit t g (x a)

open Classical in
theorem hitCount_eq_card [Fintype A] (t : I) (g : S) (x : A → Draw I S) :
    hitCount t g x = ((Finset.univ.filter fun a => (x a).1 = (x a).2 ∧
      (x a).1 t = g).card : ℚ) := by
  classical
  rw [Finset.card_filter]
  push_cast
  rfl

variable [Fintype I] [DecidableEq I] [Fintype S] [Nonempty S]
variable [Fintype A] [DecidableEq A]

theorem mean_hitCount (t : I) (g : S) :
    mean (hitCount (A := A) t g) = (Fintype.card A : ℚ)*successProb (I := I) (S := S) := by
  classical
  change mean (fun x : A → Draw I S => ∑ a, hit t g (x a)) = _
  rw [mean_sum]
  simp_rw [mean_coordinate (D := Draw I S) _ (hit t g), mean_hit]
  simp [successProb,nsmul_eq_mul]

/-- Exact centered second moment of the actual diagonal count:
m·p(1-p). Independence between different t,g is not asserted. -/
theorem variance_hitCount (t : I) (g : S) :
    let p := successProb (I := I) (S := S)
    let mu := (Fintype.card A : ℚ)*p
    mean (fun x : A → Draw I S => (hitCount t g x - mu)^2) = mu*(1-p) := by
  classical
  intro p mu
  let Y : Draw I S → ℚ := fun d => hit t g d - p
  have hmean : mean (hit t g) = p := by
    simpa [p, successProb] using mean_hit t g
  have hY : mean Y = 0 := by
    change mean (fun d : Draw I S => hit t g d - p) = 0
    rw [mean_lin_sub,hmean,mean_const,sub_self]
  have hY2 : mean (fun d => Y d * Y d) = p*(1-p) := by
    have hy (d : Draw I S) :
        Y d * Y d = hit t g d - (2*p)*hit t g d + p^2 := by
      have hs := hit_sq t g d
      dsimp [Y]
      nlinarith
    simp_rw [hy]
    rw [mean_lin_add,mean_lin_sub,mean_scale,mean_const,hmean]
    ring
  have hsum (x : A → Draw I S) :
      hitCount t g x - mu = ∑ a, Y (x a) := by
    simp [hitCount,mu,Y,Finset.sum_sub_distrib,nsmul_eq_mul]
  have hsquare (x : A → Draw I S) :
      (hitCount t g x - mu)^2 = ∑ a, ∑ b, Y (x a) * Y (x b) := by
    rw [hsum,pow_two,Finset.sum_mul]
    simp_rw [Finset.mul_sum]
  simp_rw [hsquare,mean_sum]
  have hdiag (a : A) :
      (∑ b, mean (fun x : A → Draw I S => Y (x a)*Y (x b))) = p*(1-p) := by
    rw [Finset.sum_eq_single a]
    · rw [mean_coordinate (D := Draw I S) a (fun d => Y d * Y d),hY2]
    · intro b _ hb
      rw [mean_coordinates_mul a b hb,hY,zero_mul]
    · simp
  simp_rw [hdiag]
  simp [mu,nsmul_eq_mul,mul_assoc]

omit [Nonempty S] in
/-- The same exact moments hold when the rest of the primitive labels and
layout choices are independent extra coordinates. Derived labels may be any
functions of both coordinate blocks. -/
theorem mean_extra {B : Type c} [Fintype B] [Nonempty B]
    (f : (A → Draw I S) → ℚ) :
    mean (fun x : (A → Draw I S) × B => f x.1) = mean f := by
  have h := mean_product f (fun _ : B => (1:ℚ))
  simpa only [mean_const,mul_one] using h

end Concrete

#print axioms hitCount_eq_card
#print axioms mean_hitCount
#print axioms variance_hitCount
#print axioms joint_score_certificate


/-- Condition on a finite coordinate. Taking conditional means gives back the
whole mean, so a next primitive symbol can be fixed without losing feasibility. -/
theorem mean_fibre_average {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    (f : A × B → ℚ) :
    mean f = mean (fun a => mean (fun b => f (a,b))) := by
  unfold mean
  rw [Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul, ← Finset.sum_div]
  ring

theorem low_cost_fibre {A : Type u} {B : Type v} [Fintype A] [Nonempty A] [Fintype B]
    (f : A × B → ℚ) (bound : ℚ) (h : mean f < bound) :
    ∃ a, mean (fun b => f (a,b)) < bound := by
  rw [mean_fibre_average] at h
  exact exists_below_mean_bound _ _ h

/-- The constant 11/6 follows from the source expectation budget: there
are 12N incidences and 4N private variables in the designated family. -/
theorem source_base_cost {Ω : Type u} [Fintype Ω]
    (N Q : ℚ) (hN : 0 < N) (hQ : 0 < Q)
    (phi xi : Ω → ℚ)
    (hPhi : mean phi ≤ 4*(12*N)+2*N) (hXi : mean xi ≤ Q*(4*N)) :
    mean (fun x => phi x / (5*(12*N)) + xi x / (Q*(4*N))) ≤ 11/6 := by
  rw [mean_lin_add,mean_const_div,mean_const_div]
  have hdenPhi : 0 < 5 * (12 * N) := by positivity
  have hdenXi : 0 < Q * (4 * N) := by positivity
  have hhPhi := div_le_div_of_nonneg_right hPhi hdenPhi.le
  have hhXi := div_le_div_of_nonneg_right hXi hdenXi.le
  have hvPhi : (4*(12*N)+2*N)/(5*(12*N)) = 5/6 := by field_simp; ring
  rw [hvPhi] at hhPhi
  rw [div_self hdenXi.ne'] at hhXi
  linarith

section SourceCertificate
variable {A : Type u} {I : Type v} {S : Type w} {B : Type c}
variable [Fintype A] [DecidableEq A] [Nonempty A] [Fintype I] [DecidableEq I] [Nonempty I]
variable [Fintype S] [Nonempty S] [Fintype B] [Nonempty B]

abbrev State (A : Type u) (I : Type v) (S : Type w) (B : Type c) :=
  (A → Draw I S) × B

/-- Finite form of J1's joint abundance. The layout collision means hPhi
and hXi, and the explicit threshold hSize, are inputs. Only the primitive
labels of the independent reserved pins are required to be distinct uniform
coordinates. No independence of the different (node,symbol) counts, nor
conditional independence of this joint cost from them, is needed or used. -/
theorem source_joint_abundance (N : ℕ) (hN : 0 < N)
    (phi xi : State A I S B → ℚ)
    (hPhi0 : ∀ x, 0 ≤ phi x) (hXi0 : ∀ x, 0 ≤ xi x)
    (hPhi : mean phi ≤ 4*(12*(N:ℚ))+2*(N:ℚ))
    (hXi : mean xi ≤ (Fintype.card I : ℚ)*(4*(N:ℚ)))
    (hSize : (11/6 : ℚ) + 8*(Fintype.card (I×S) : ℚ)/
      ((Fintype.card A : ℚ)*successProb (I := I) (S := S)) < 2) :
    ∃ x : State A I S B,
      phi x / (5*(12*(N:ℚ))) + xi x / ((Fintype.card I : ℚ)*(4*(N:ℚ))) < 2 ∧
      ∀ t g, ((Fintype.card A : ℚ)*successProb (I := I) (S := S))/2 <
        hitCount t g x.1 := by
  classical
  let p := successProb (I := I) (S := S)
  let mu := (Fintype.card A : ℚ)*p
  let layoutCost : State A I S B → ℚ := fun x =>
    phi x / (5*(12*(N:ℚ))) + xi x / ((Fintype.card I : ℚ)*(4*(N:ℚ)))
  let X : (I×S) → State A I S B → ℚ := fun a x => hitCount a.1 a.2 x.1
  have hp : 0 < p := by
    have h : (0 : ℚ) < Fintype.card S := by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card S)
    simp only [p,successProb]
    positivity
  have hmu : 0 < mu := by
    have h : (0 : ℚ) < Fintype.card A := by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card A)
    dsimp [mu]
    positivity
  have hN' : (0 : ℚ) < N := by exact_mod_cast hN
  have hQ : (0 : ℚ) < Fintype.card I := by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card I)
  have hcost : ∀ x, 0 ≤ layoutCost x := fun x =>
    add_nonneg (div_nonneg (hPhi0 x) (by positivity)) (div_nonneg (hXi0 x) (by positivity))
  have hvar : ∀ j, mean (fun x => (X j x-mu)^2) ≤ mu := by
    intro j
    dsimp [X]
    rw [mean_extra (A := A) (I := I) (S := S) (fun x => (hitCount j.1 j.2 x-mu)^2)]
    have hv := variance_hitCount (A := A) j.1 j.2
    change mean (fun x : A → Draw I S => (hitCount j.1 j.2 x - mu)^2) = mu * (1 - p) at hv
    rw [hv]
    exact mul_le_of_le_one_right hmu.le (by linarith)
  obtain ⟨x,_,hx,hgroups⟩ :=
    joint_score_certificate layoutCost X mu (11/6) hmu hcost
      (source_base_cost N _ hN' hQ phi xi hPhi hXi) hvar hSize
  exact ⟨x,hx,fun t g => hgroups (t,g)⟩
end SourceCertificate

#print axioms source_base_cost
#print axioms source_joint_abundance
#print axioms mean_fibre_average
#print axioms low_cost_fibre

end DiagonalAbundance
