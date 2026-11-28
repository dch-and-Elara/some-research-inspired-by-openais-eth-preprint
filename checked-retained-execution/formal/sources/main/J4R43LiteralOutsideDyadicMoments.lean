import J4R43LiteralOutsideDeterministicSupply

/-! Exact small dyadic probabilities for the actual greedy decisions:
a local request is inconsistent, or each still-unfixed request
costs one independent fair bit. For the physical degree-three
source, one or two stars never need more than ten such bits. -/
namespace J4R43LiteralOutside
open scoped Classical BigOperators
open P11FullPacking J6R10Repack IndependentThinning
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 5200000

variable {U : Type*} [Fintype U] [DecidableEq U]

def matchesPartial (a : Option Bool) (want : Bool) : Prop :=
  match a with
  | none => True
  | some b => want=b

def freeRequests (a : U→Option Bool) (S : Finset U) : ℕ :=
  (S.filter (fun x=>a x=none)).card

def dyadicNumber (a : U→Option Bool) (S : Finset U) (w : U→Bool) (D : ℕ) : ℕ :=
  if ∀ x∈S,matchesPartial (a x) (w x) then 2^(D-freeRequests a S) else 0

theorem raw_partial_is_inverse_power (a : U→Option Bool) (S : Finset U) (w : U→Bool) :
    localMass a S w=
      if ∀ x∈S,matchesPartial (a x) (w x) then (1/2:ℚ)^freeRequests a S else 0 := by
  unfold localMass
  by_cases h : ∀ x∈S,matchesPartial (a x) (w x)
  · rw [if_pos h]
    calc
      _ = ∏ x∈S,if a x=none then (1/2:ℚ) else 1 := by
        refine Finset.prod_congr rfl fun x hx=>?_
        have g := h x hx
        cases b : a x with
        | none => simp [b,coinAt]
        | some z =>
          have r : w x=z := by simpa [b,matchesPartial] using g
          simp [b,coinAt,r]
      _ = _ := by rw [←Finset.prod_filter,Finset.prod_const]; rfl
  · rw [if_neg h]
    push_neg at h
    obtain ⟨x,hx,xh⟩ := h
    apply Finset.prod_eq_zero hx
    cases b : a x with
    | none => exact False.elim (xh (by simp [b,matchesPartial]))
    | some z =>
      have r : w x≠z := fun j=>xh (by simpa [b,matchesPartial] using j)
      simp [b,coinAt,r]

theorem dyadic_numerator_receipt (a : U→Option Bool) (S : Finset U) (w : U→Bool) (D : ℕ)
    (bound : S.card≤D) :
    (dyadicNumber a S w D:ℚ)=(2:ℚ)^D*localMass a S w ∧
      dyadicNumber a S w D≤2^D := by
  let k := freeRequests a S
  have small : k≤D :=
    (Finset.card_filter_le S (fun x=>a x=none)).trans bound
  rw [raw_partial_is_inverse_power]
  unfold dyadicNumber
  by_cases legal : ∀ x∈S,matchesPartial (a x) (w x)
  · rw [if_pos legal,if_pos legal]
    constructor
    · change ((2^(D-k):ℕ):ℚ)=(2:ℚ)^D*(1/2:ℚ)^k
      rw [Nat.cast_pow,Nat.cast_ofNat,div_pow,one_pow,mul_one_div,
        ←Nat.sub_add_cancel small,pow_add]
      field_simp
      congr 1
      omega
    · exact Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
  · simp [legal]

theorem true_pair_moments_at_most_ten {E A B : Type} [Fintype E] (N : Network E A B)
    (pin : E) (dr : ∀ u : A,Nat.card {e : E//N.row e=u}≤3)
    (dc : ∀ u : B,Nat.card {e : E//N.col e=u}≤3)
    (a : Eligible N pin→Option Bool) (e f : Eligible N pin) :
    ∃ q : ℕ,q≤2^10 ∧ (q:ℚ)=2^10*twoMoment a (block N pin) e f := by
  by_cases same : sameRequest (block N pin) e f
  · let S := block N pin e∪block N pin f
    let w := bothRequest (block N pin) e f
    have h : S.card≤10 :=
      (two_star_scan_bound (block N pin) 5 (literal_block_count N 3 dr dc pin) e f).1
    have C := dyadic_numerator_receipt a S w 10 h
    refine ⟨dyadicNumber a S w 10,C.2,?_⟩
    rw [twoMoment,if_pos same]
    exact C.1
  · refine ⟨0,by decide,?_⟩
    simp [twoMoment,same]

#print axioms raw_partial_is_inverse_power
#print axioms dyadic_numerator_receipt
#print axioms true_pair_moments_at_most_ten
end
end J4R43LiteralOutside

