import J6R22ActiveScaled
import J6R9RecursiveNormalizer

/-! The common high register really contains one whole multiple of
2^B, even though the approximants are only known at their individual
printed p_t. The result supplies a certificate for reading the upper
word later; neither arbitrary rational register values nor arbitrary
width substitutions justify that read. -/
namespace J6R22Active
open scoped BigOperators Polynomial
open J6R9Hermite HermiteLoss DenominatorBudget J6ActiveSchedule P1DyadicGrid

theorem scaled_weight_read {a u h B j : ℕ} {t : ℤ} (ht : t∈grid a) (hn : t≠0)
    (fit : totalLoss a h j t≤B) :
    twoLocalRat (scaledWeight a u h B j t)=(2:ℚ)^B*weight a u h j t := by
  let L := totalLoss a h j t
  have h0 := weight_scaled_integral a u h j ht hn
  have he : B-L+L=B := Nat.sub_add_cancel fit
  have hB : (2:ℚ)^B*weight a u h j t∈twoLocalSubalgebra := by
    rw [←he,pow_add,mul_assoc]
    exact twoLocalSubalgebra.mul_mem (integral_pow_two _) h0
  rw [scaledWeight,dif_pos hB]
  rfl

section Compose
variable {A K : Type*} [CommRing A] [CommRing K] [Algebra ℚ K]

noncomputable def scaledRecompose (base : TwoLocal→+*A) (a M u B : ℕ)
    (jet : ℤ→ℕ→A) : A :=
  ∑ t ∈ active a M u, ∑ j ∈ Finset.range (order M u t),
     base (scaledWeight a u (sourceH M u) B j t)*jet t j

theorem scaled_recompose_embed (ι : A→+*K) (base : TwoLocal→+*A)
    (compat : ∀ z,ι (base z)=algebraMap ℚ K (twoLocalRat z))
    (a M u B : ℕ) (hu : 0<u) (huM : u≤M) (hB : commonLoss a M u≤B) (jet : ℤ→ℕ→A) :
    ι (scaledRecompose base a M u B jet)=
      (2:K)^B*linearRecompose a M u (fun t j=>ι (jet t j)) := by
  simp only [scaledRecompose,linearRecompose,map_sum,Finset.mul_sum,map_mul,compat,Algebra.smul_def]
  refine Finset.sum_congr rfl (fun t ht=> Finset.sum_congr rfl (fun j hj=>?_))
  have hret : t∈retained a u (sourceH M u) := (active_retained a M u) ▸ ht
  obtain ⟨hg,hn,_⟩ := retained_mem.mp hret
  rw [scaled_weight_read hg hn ((actual_weight_loss_le hu huM (Finset.mem_range.mp hj)).trans hB),
    map_mul,map_pow,map_ofNat,mul_assoc]

theorem scaled_recompose_error (base : TwoLocal→+*A) (a M u p B : ℕ)
    (hu : 0<u) (huM : u≤M) (hB : commonLoss a M u≤B)
    (x y : ℤ→ℕ→A)
    (h : ∀ t∈active a M u,∀ j<order M u t,(2:A)^childPrecision p a M u t ∣ x t j-y t j) :
    (2:A)^(p+B) ∣ scaledRecompose base a M u B x-scaledRecompose base a M u B y := by
  simp only [scaledRecompose,←Finset.sum_sub_distrib,←mul_sub]
  apply Finset.dvd_sum
  intro t ht
  apply Finset.dvd_sum
  intro j hj
  exact common_precision_each_scaled_error base ht huM (Finset.mem_range.mp hj)
    ((actual_weight_loss_le hu huM (Finset.mem_range.mp hj)).trans hB)
    (h t ht j (Finset.mem_range.mp hj))

theorem scaled_recompose_actual_register {R : Type*} [CommRing R]
    (ι : A→+*K) (hinj : Function.Injective ι) (base : TwoLocal→+*A)
    (compat : ∀ z,ι (base z)=algebraMap ℚ K (twoLocalRat z))
    (a M u p B : ℕ) (hu : 0<u) (huM : u≤M) (hB : commonLoss a M u≤B)
    (x y : ℤ→ℕ→A) (out : A) (recv : A→+*R) (nil : (2:R)^(p+B)=0)
    (origin : linearRecompose a M u (fun t j=>ι (y t j))=ι out)
    (input : ∀ t∈active a M u,∀ j<order M u t,(2:A)^childPrecision p a M u t ∣ x t j-y t j) :
    recv (scaledRecompose base a M u B x)=(2:R)^B*recv out := by
  have hExact : scaledRecompose base a M u B y=(2:A)^B*out := by
    apply hinj
    rw [scaled_recompose_embed ι base compat a M u B hu huM hB y,origin,map_mul,map_pow,map_ofNat]
  obtain ⟨z,hZ⟩ := scaled_recompose_error base a M u p B hu huM hB x y input
  have hE : recv (scaledRecompose base a M u B x)=recv (scaledRecompose base a M u B y) := by
    apply sub_eq_zero.mp
    rw [←map_sub,hZ,map_mul,map_pow,map_ofNat,nil,zero_mul]
  rw [hE,hExact,map_mul,map_pow,map_ofNat]
end Compose

#print axioms scaled_weight_read
#print axioms scaled_recompose_embed
#print axioms scaled_recompose_error
#print axioms scaled_recompose_actual_register
end J6R22Active

