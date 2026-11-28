import J6R9PacketReceive

/-! The printed R12 finite row coefficient at the actual valuation-zero
mode uses its own C-hat and the inverse of its certified odd
denominator. This keeps all nonzero probe dependence; no Taylor tail is
chosen by a callback. It is not a proof of the separate J9 slot chart. -/
namespace J6R14SpecializedBox
open scoped Polynomial BigOperators
open Polynomial J6R9PacketCoeff J6R9PacketReceive

variable {R : Type*} [CommRing R] {t : ℤ} {x tile : ℕ}

theorem valuation_zero_mode_exact (a p : ℕ) (hnil : (2:R)^p=0)
    (d : Crossing t x tile 0) (z : R) (b : ℕ) :
    mode a p hnil (Nat.zero_le a) d z b =
      (2:R)^(a+1+b)*z * (cHat a t).eval₂ (J6ZeroTransport.reduceAt p hnil) z *
        (inverseB a p hnil (Nat.zero_le a) d z)^(b+1) := by
  have hd : d.level = 0 := Nat.eq_zero_of_le_zero d.level_le
  unfold mode leading ratio
  rw [hd,Nat.sub_zero,Nat.sub_zero,pow_one,mul_pow,pow_add,pow_succ]
  ring

theorem valuation_zero_inverse_geometric (a p : ℕ) (hnil : (2:R)^p=0)
    (d : Crossing t x tile 0) (z : R) :
    let u := J6ZeroTransport.oddReciprocal R p d.oddPart
    inverseB a p hnil (Nat.zero_le a) d z =
      u * ∑ j ∈ Finset.range p, (-((2:R)^(a+1)*z*u))^j := by
  dsimp only
  let u := J6ZeroTransport.oddReciprocal R p d.oddPart
  let v := (2:R)^(a+1)*z*u
  let inv := inverseB a p hnil (Nat.zero_le a) d z
  let D := B a d.level d.oddPart z
  have hDinv : D*inv=1 :=
    denominator_inverse_product a p hnil (Nat.zero_le a) d z
  have hu : (d.oddPart:R)*u=1 := by
    apply J6ZeroTransport.oddReciprocal_valid p hnil
    exact fun h => (Int.not_even_iff_odd.mpr d.odd) (even_iff_two_dvd.mpr h)
  have hd : d.level = 0 := Nat.eq_zero_of_le_zero d.level_le
  have he : D*u=1-(-v) := by
    unfold D B
    rw [hd,Nat.sub_zero,add_mul,hu,sub_neg_eq_add]
  have hv : v=(2:R)*((2:R)^a*z*u) := by
    unfold v
    rw [pow_succ']
    ring
  have hn : (-v)^p=0 := by rw [neg_pow,hv,mul_pow,hnil,zero_mul,mul_zero]
  let F := ∑ j ∈ Finset.range p, (-v)^j
  have hh : D*(u*F)=1 := by
    rw [← mul_assoc,he]
    unfold F
    rw [mul_comm,geom_sum_mul_neg,hn,sub_zero]
  change inv=u*F
  calc
    inv = inv*(D*(u*F)) := by rw [hh,mul_one]
    _ = (D*inv)*(u*F) := by ring
    _ = u*F := by rw [hDinv,one_mul]

#print axioms valuation_zero_mode_exact
#print axioms valuation_zero_inverse_geometric
end J6R14SpecializedBox
