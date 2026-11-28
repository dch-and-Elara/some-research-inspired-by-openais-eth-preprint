import J6R9HermiteRing
import NativeProbeRing

/-! Certified common dyadic clearing for the actual tapered weights.
A global working precision p+B does *not* require the child replies
all to arrive with p+B bits. Below each local width is compensated
by its own proved divisibility 2^(B-totalLoss_tj).
This is an algebraic/receiving lemma, not the metered generation of
every rational-weight numerator or denominator. -/
namespace J6R22Active
open scoped BigOperators
open J6R9Hermite HermiteLoss DenominatorBudget J6ActiveSchedule P1DyadicGrid

def commonLoss (a M u : ℕ) : ℕ :=
  6*sourceH M u*2^a+(4*M)*(a+1)

theorem actual_weight_loss_le {a M u j : ℕ} {t : ℤ}
    (hu : 0<u) (huM : u≤M) (hj : j<order M u t) :
    totalLoss a (sourceH M u) j t≤commonLoss a M u := by
  unfold totalLoss commonLoss
  apply Nat.add_le_add
  · exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _))
  · exact Nat.mul_le_mul (hj.le.trans (order_bound M u t hu huM)) (Nat.sub_le _ _)

noncomputable def scaledWeight (a u h B j : ℕ) (t : ℤ) : TwoLocal := by
  classical
  exact if k : (2:ℚ)^B*weight a u h j t∈twoLocalSubalgebra then ⟨_,k⟩ else 0

theorem scaled_weight_factor {a u h B j : ℕ} {t : ℤ} (ht : t∈grid a) (hn : t≠0)
    (fit : totalLoss a h j t≤B) :
    scaledWeight a u h B j t=
      (2:TwoLocal)^(B-totalLoss a h j t)*scaledWeight a u h (totalLoss a h j t) j t := by
  let L := totalLoss a h j t
  have h0 := weight_scaled_integral a u h j ht hn
  have he : B-L+L=B := Nat.sub_add_cancel fit
  have hB : (2:ℚ)^B*weight a u h j t∈twoLocalSubalgebra := by
    rw [←he,pow_add,mul_assoc]
    exact twoLocalSubalgebra.mul_mem (integral_pow_two _) h0
  unfold scaledWeight
  rw [dif_pos h0,dif_pos hB]
  apply Subtype.ext
  change (2:ℚ)^B*weight a u h j t=(2:ℚ)^(B-L)*((2:ℚ)^L*weight a u h j t)
  rw [←mul_assoc,←pow_add,he]

theorem actual_precision_pays_term_loss {p a M u j : ℕ} {t : ℤ}
    (ht : t∈active a M u) (huM : u≤M) (hj : j<order M u t) :
    p+totalLoss a (sourceH M u) j t≤childPrecision p a M u t := by
  have hret : t∈retained a u (sourceH M u) := (active_retained a M u) ▸ ht
  obtain ⟨hg,hn,_⟩ := retained_mem.mp hret
  rw [child_precision_loss p a M u hg hn]
  simpa only [totalLoss,Nat.add_assoc] using
    source_loss_fits p M a (level t) u j (2^(a-level t)) huM hj

theorem common_precision_each_scaled_error {A : Type*} [CommRing A]
    (base : TwoLocal→+*A) {p a M u B j : ℕ} {t : ℤ} (ht : t∈active a M u)
    (huM : u≤M) (hj : j<order M u t) (fit : totalLoss a (sourceH M u) j t≤B)
    {x y : A} (hxy : (2:A)^childPrecision p a M u t ∣ x-y) :
    (2:A)^(p+B) ∣ base (scaledWeight a u (sourceH M u) B j t)*(x-y) := by
  have hret : t∈retained a u (sourceH M u) := (active_retained a M u) ▸ ht
  obtain ⟨hg,hn,_⟩ := retained_mem.mp hret
  let T := childPrecision p a M u t
  let L := totalLoss a (sourceH M u) j t
  have hfit : p+L≤T := actual_precision_pays_term_loss (p:=p) ht huM hj
  have hN : p+B≤B-L+T := by omega
  have hpow : B-L+T=p+B+(B-L+T-(p+B)) := by omega
  obtain ⟨z,hz⟩ := hxy
  refine ⟨(2:A)^(B-L+T-(p+B))*
    (base (scaledWeight a u (sourceH M u) L j t)*z),?_⟩
  rw [scaled_weight_factor hg hn fit,map_mul,map_pow,map_ofNat,hz]
  change ((2:A)^(B-L)*_)*((2:A)^T*z)=_
  calc
    _=(2:A)^(B-L+T)*(base (scaledWeight a u (sourceH M u) L j t)*z) := by rw [pow_add]; ring
    _=_ := by
      conv_lhs => rw [hpow,pow_add]
      ring

theorem high_word_requires_exact_divisibility (p B n : ℕ) :
    let x : NativeProbeRing.Base (p+B) := (2:NativeProbeRing.Base (p+B))^B*n
    2^B ∣ x.val ∧ x.val/2^B=n%2^p := by
  haveI : NeZero (2^(p+B) : ℕ) := ⟨by positivity⟩
  have hn : (2:NativeProbeRing.Base (p+B))^B*n=((2^B*n:ℕ):NativeProbeRing.Base (p+B)) := by
    push_cast
    rfl
  dsimp only
  rw [hn,ZMod.val_natCast,pow_add,mul_comm ((2:ℕ)^p) ((2:ℕ)^B),Nat.mul_mod_mul_left]
  exact ⟨dvd_mul_right _ _,Nat.mul_div_cancel_left _ (by positivity)⟩

#print axioms actual_weight_loss_le
#print axioms scaled_weight_factor
#print axioms actual_precision_pays_term_loss
#print axioms common_precision_each_scaled_error
#print axioms high_word_requires_exact_divisibility
end J6R22Active


