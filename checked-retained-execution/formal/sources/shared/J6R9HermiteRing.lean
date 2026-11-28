import J6R9HermiteArithmetic

/-! Whole-ring version of the finite Hermite readout. The integral ring
may have nilpotents; no cancellation in it, and no field model for a
prime-power receiving ring, is used. -/
namespace J6R9Hermite
open HermiteLoss DenominatorBudget
open J6ActiveSchedule
open scoped BigOperators

section IntegralRing
variable {A K : Type*} [CommRing A] [CommRing K]

def imageCongruence (ι : A→+*K) (p : ℕ) (x y : K) : Prop :=
  ∃ r : A, x-y=ι ((2:A)^p*r)

theorem image_zero (ι : A→+*K) (p : ℕ) : imageCongruence ι p 0 0 :=
  ⟨0,by simp⟩

theorem image_add (ι : A→+*K) (p : ℕ) {x y z w : K}
    (h : imageCongruence ι p x y) (k : imageCongruence ι p z w) :
    imageCongruence ι p (x+z) (y+w) := by
  obtain ⟨r,hr⟩ := h
  obtain ⟨s,hs⟩ := k
  refine ⟨r+s,?_⟩
  rw [mul_add,map_add,←hr,←hs]
  ring

theorem image_sum {I : Type*} (ι : A→+*K) (p : ℕ) (s : Finset I) (x y : I→K)
    (h : ∀ i∈s, imageCongruence ι p (x i) (y i)) :
    imageCongruence ι p (∑ i∈s, x i) (∑ i∈s, y i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using image_zero ι p
  | insert i s hi ih =>
    rw [Finset.sum_insert hi,Finset.sum_insert hi]
    exact image_add ι p (h i (Finset.mem_insert_self i s))
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

theorem image_divisibility (ι : A→+*K) (prec : ℕ) (x y : A)
    (h : (2:A)^prec ∣ x-y) : imageCongruence ι prec (ι x) (ι y) := by
  obtain ⟨r,hr⟩ := h
  exact ⟨r, by rw [←map_sub,hr]⟩

variable [Algebra ℚ K]

theorem image_weight
    (ι : A→+*K) (base : TwoLocal→+*A)
    (compat : ∀ z : TwoLocal, ι (base z) = algebraMap ℚ K (twoLocalRat z))
    {p prec k : ℕ} {w : ℚ} {x y : K}
    (scale : (2:ℚ)^k*w ∈ twoLocalSubalgebra) (fit : p+k≤prec)
    (h : imageCongruence ι prec x y) :
    imageCongruence ι p (w • x) (w • y) := by
  obtain ⟨r,hr⟩ := h
  let s : TwoLocal := ⟨(2:ℚ)^k*w,scale⟩
  let e := prec-(p+k)
  have hpow : prec=p+e+k := by dsimp [e]; omega
  have hs : ι (base s) = (2:K)^k*algebraMap ℚ K w := by
    rw [compat]
    change algebraMap ℚ K ((2:ℚ)^k*w) = _
    rw [map_mul,map_pow,map_ofNat]
  refine ⟨(2:A)^e*base s*r,?_⟩
  rw [Algebra.smul_def,Algebra.smul_def,←mul_sub,hr]
  simp only [map_mul,map_pow,map_ofNat,hs]
  rw [hpow,pow_add,pow_add]
  ring

theorem weighted_ring_errors
    (ι : A→+*K) (base : TwoLocal→+*A)
    (compat : ∀ z : TwoLocal, ι (base z) = algebraMap ℚ K (twoLocalRat z))
    (a M u p : ℕ) (hM : u≤M) (approx exactJet : ℤ→ℕ→A)
    (data : ∀ t∈active a M u, ∀ j<order M u t,
      (2:A)^childPrecision p a M u t ∣ approx t j-exactJet t j) :
    imageCongruence ι p
      (linearRecompose a M u (fun t j => ι (approx t j)))
      (linearRecompose a M u (fun t j => ι (exactJet t j))) := by
  unfold linearRecompose
  apply image_sum
  intro t ht
  apply image_sum
  intro j hj
  have hret : t∈retained a u (sourceH M u) := (active_retained a M u) ▸ ht
  obtain ⟨hg,hn,_⟩ := retained_mem.mp hret
  have hF : p+totalLoss a (sourceH M u) j t ≤ childPrecision p a M u t := by
    rw [child_precision_loss p a M u hg hn]
    simpa only [totalLoss,Nat.add_assoc] using
      source_loss_fits p M a (level t) u j (2^(a-level t)) hM (Finset.mem_range.mp hj)
  exact image_weight ι base compat (weight_scaled_integral a u (sourceH M u) j hg hn)
    hF (image_divisibility ι _ _ _ (data t ht j (Finset.mem_range.mp hj)))

/-- A verified two-local integral result in the original coefficient ring,
not merely a formal rational value. An injective embedding is unnecessary
for existence and for the displayed result of reducing this witness. -/
theorem finite_ring_receive
    (ι : A→+*K) (base : TwoLocal→+*A)
    (compat : ∀ z : TwoLocal, ι (base z) = algebraMap ℚ K (twoLocalRat z))
    (a M u p : ℕ) (hM : u≤M) (approx exactJet : ℤ→ℕ→A) (out : A)
    (correct : linearRecompose a M u (fun t j => ι (exactJet t j))=ι out)
    (data : ∀ t∈active a M u, ∀ j<order M u t,
      (2:A)^childPrecision p a M u t ∣ approx t j-exactJet t j) :
    ∃ z : A, ι z=linearRecompose a M u (fun t j=>ι (approx t j)) ∧
      (2:A)^p ∣ z-out := by
  have h := weighted_ring_errors ι base compat a M u p hM approx exactJet data
  rw [correct] at h
  obtain ⟨r,hr⟩ := h
  refine ⟨out+(2:A)^p*r,?_,⟨r,by abel⟩⟩
  rw [map_add,←hr]
  abel

theorem finite_ring_receive_reduced
    {B : Type*} [CommRing B]
    (ι : A→+*K) (base : TwoLocal→+*A)
    (compat : ∀ z : TwoLocal, ι (base z) = algebraMap ℚ K (twoLocalRat z))
    (a M u p : ℕ) (hM : u≤M) (approx exactJet : ℤ→ℕ→A) (out : A)
    (correct : linearRecompose a M u (fun t j => ι (exactJet t j))=ι out)
    (data : ∀ t∈active a M u, ∀ j<order M u t,
      (2:A)^childPrecision p a M u t ∣ approx t j-exactJet t j)
    (receiver : A→+*B) (nilpotent : (2:B)^p=0) :
    ∃ z : A, ι z=linearRecompose a M u (fun t j=>ι (approx t j)) ∧
      receiver z=receiver out := by
  obtain ⟨z,hz,r,hr⟩ := finite_ring_receive ι base compat a M u p hM approx exactJet out correct data
  refine ⟨z,hz,sub_eq_zero.mp ?_⟩
  rw [← map_sub,hr,map_mul,map_pow,map_ofNat,nilpotent,zero_mul]

/-- The kernel identity in a native receiving tower discharges the
input congruence premise. No domain assumption is needed for this. -/
theorem kernel_power_divisibility {B : Type*} [CommRing B]
    (receiver : A→+*B) (p : ℕ)
    (kernel : RingHom.ker receiver=Ideal.span ({(2:A)^p}:Set A))
    {x y : A} (h : receiver x=receiver y) :
    (2:A)^p ∣ x-y := by
  have hz : x-y∈RingHom.ker receiver := by rw [RingHom.mem_ker,map_sub,h,sub_self]
  rw [kernel,Ideal.mem_span_singleton] at hz
  exact hz

end IntegralRing

#print axioms image_weight
#print axioms finite_ring_receive
#print axioms finite_ring_receive_reduced
#print axioms kernel_power_divisibility
end J6R9Hermite

