import V8NativeMessageMatchCount
import V8CapacityUnifiedHybrid

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2600000

/-! Finite C3 rank calculation. Its hypothesis is the specific completed
bilinear readout of each fixed private choice, with separate row and
column lifts of the D operand. No general nonlinear circuit is assumed
to admit the completion or its paid listing. -/
namespace V8NativeMessage.C3
open scoped Classical BigOperators
open Module
noncomputable section

variable {K X Y : Type*} [Field K] [Fintype X] [Fintype Y]

def mixedTerm {J : Type*} [CommRing J] [Algebra K J] (ρ : J →ₗ[K] K)
    (u : X → J) (v : Y → J) (dr : X → K) (dc : Y → K) : Matrix X Y K :=
  Matrix.of fun x y => ρ (u x * v y) * (dr x * dc y)

omit [Fintype X] in
theorem mixedTerm_rank {I J : Type*} [Fintype I] [CommRing J] [Algebra K J]
    (basis : Basis I K J) (ρ : J →ₗ[K] K)
    (u : X → J) (v : Y → J) (dr : X → K) (dc : Y → K) :
    (mixedTerm ρ u v dr dc).rank ≤ Fintype.card I := by
  let A : Matrix X I K := Matrix.of (fun x i => basis.repr (u x) i * dr x)
  let B : Matrix I Y K := Matrix.of (fun i y => ρ (basis i * v y) * dc y)
  have fact : mixedTerm ρ u v dr dc=A*B := by
    ext x y
    simp only [mixedTerm,Matrix.of_apply,Matrix.mul_apply,A,B]
    have expand : ρ (u x * v y) = ∑ i, basis.repr (u x) i * ρ (basis i * v y) := by
      conv_lhs => rw [← basis.sum_repr (u x)]
      rw [Finset.sum_mul,map_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [smul_mul_assoc,LinearMap.map_smul,smul_eq_mul]
    rw [expand,Finset.sum_mul]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  rw [fact]
  exact (Matrix.rank_mul_le_left A B).trans (Matrix.rank_le_card_width A)

variable {H G : Type*} [Fintype H] [Fintype G]
variable (κ : H → ℕ) (b : H → G → ℕ)

abbrev Choices (h : H) := (g : G) → Fin (b h g)

theorem fixed_block_rank {J : H → Type*} [∀ h, CommRing (J h)] [∀ h, Algebra K (J h)]
    (basis : ∀ h, Basis (Fin (κ h)) K (J h))
    (read : ∀ h, J h →ₗ[K] K)
    (left : ∀ h, Choices b h → X → J h) (right : ∀ h, Choices b h → Y → J h)
    (dr : H → X → K) (dc : H → Y → K) :
    (∑ h, ∑ q : Choices b h, mixedTerm (read h) (left h q) (right h q) (dr h) (dc h)).rank
      ≤ ∑ h, κ h * ∏ g, b h g := by
  apply (V8CapacityUnified.U7.rank_sum_le Finset.univ _).trans
  apply Finset.sum_le_sum
  intro h _
  apply (V8CapacityUnified.U7.rank_sum_le Finset.univ _).trans
  calc
    _ ≤ ∑ _q : Choices b h, κ h := by
      apply Finset.sum_le_sum
      intro q _
      simpa only [Fintype.card_fin] using mixedTerm_rank (basis h) (read h) (left h q) (right h q) (dr h) (dc h)
    _ = _ := by simp [Choices,Fintype.card_pi,Nat.mul_comm]

section ActualTarget
open V8PooledRange V8PooledRange.NativeOrigin
variable {V E O : Type*} [Fintype V] [Fintype E] {G₀ : Graph V E} (p : ThreePorts G₀)
    {m : ℕ} (P : Pairs G₀ m)
    [CommRing O] [Algebra O K]
variable (χ : O →+* ZMod 2) (hinj : Function.Injective (algebraMap O K))

include hinj in
/-- It is the assembled matrix that must be integral with the parity of
the true five-copy count. Its summands need not have integral entries. -/
theorem origin_parity_rank (M : Matrix (Fin m → Bool) (Fin m → Bool) K)
    (integral : ∀ x y, ∃ o : O, algebraMap O K o=M x y ∧
      χ o=(originCount G₀ p (activeSigns P x y):ZMod 2)) : M.rank=2^m := by
  choose a ha using integral
  let A : Matrix (Fin m → Bool) (Fin m → Bool) O := Matrix.of a
  have eK : A.map (algebraMap O K)=M := by
    ext x y
    exact (ha x y).1
  have e₂ : A.map χ=1 := by
    ext x y
    change χ (a x y)=(1 : Matrix (Fin m → Bool) (Fin m → Bool) (ZMod 2)) x y
    rw [(ha x y).2,C2_parity P p x y,Matrix.one_apply]
  have emap : χ A.det=(A.map χ).det := RingHom.map_det χ A
  have he : χ A.det=1 := by rw [emap,e₂,Matrix.det_one]
  have hA : A.det≠0 := by
    intro h
    rw [h,map_zero] at he
    exact zero_ne_one he
  have hM : M.det≠0 := by
    have emapK : algebraMap O K A.det=(A.map (algebraMap O K)).det :=
      RingHom.map_det (algebraMap O K) A
    rw [← eK,← emapK]
    exact (map_ne_zero_iff _ hinj).mpr hA
  rw [Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).mpr
    (isUnit_iff_ne_zero.mpr hM))]
  simp

include hinj in
theorem C3_rank_budget {J : H → Type*} [∀ h, CommRing (J h)] [∀ h, Algebra K (J h)]
    (basis : ∀ h, Basis (Fin (κ h)) K (J h))
    (read : ∀ h, J h →ₗ[K] K)
    (left : ∀ h, Choices b h → (Fin m→Bool) → J h)
    (right : ∀ h, Choices b h → (Fin m→Bool) → J h)
    (dr dc : H → (Fin m → Bool) → K)
    (integral : ∀ x y, ∃ o : O, algebraMap O K o =
      (∑ h, ∑ q : Choices b h, mixedTerm (read h) (left h q) (right h q) (dr h) (dc h)) x y ∧
        χ o=(originCount G₀ p (activeSigns P x y):ZMod 2)) :
    2^m≤∑ h, κ h * ∏ g, b h g := by
  have hr := origin_parity_rank p P χ hinj _ integral
  rw [← hr]
  exact fixed_block_rank κ b basis read left right dr dc

end ActualTarget

/-- A concrete paid-trace cardinal receipt is needed to pass to cost.
This is the exact pre-logarithm version, with no real-log hypotheses. -/
theorem C3_paid_budget {m W steps κmax : ℕ}
    (rank : 2^m≤∑ h, κ h * ∏ g, b h g)
    (blocks : Fintype.card H ≤ W*steps)
    (list : ∀ h g, b h g ≤ W*steps)
    (depth : ∀ h, κ h ≤ κmax) :
    2^m≤κmax*(W*steps)^(Fintype.card G+1) := by
  apply rank.trans
  calc
    _ ≤ ∑ _h : H, κmax*(W*steps)^(Fintype.card G) := by
      apply Finset.sum_le_sum
      intro h _
      apply Nat.mul_le_mul (depth h)
      calc
        _ ≤ ∏ _g : G, W*steps := Finset.prod_le_prod' (fun g _ => list h g)
        _ = _ := by simp
    _ = Fintype.card H * (κmax*(W*steps)^(Fintype.card G)) := by simp
    _ ≤ _ := by
      rw [pow_succ]
      calc
        _ ≤ (W*steps) * (κmax*(W*steps)^(Fintype.card G)) :=
          Nat.mul_le_mul_right _ blocks
        _ = _ := by ring

#print axioms mixedTerm_rank
#print axioms fixed_block_rank
#print axioms origin_parity_rank
#print axioms C3_rank_budget
#print axioms C3_paid_budget

end
end V8NativeMessage.C3