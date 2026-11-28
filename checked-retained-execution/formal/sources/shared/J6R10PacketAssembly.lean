import J6NoOversizedChild

namespace J6R10PacketAssembly
open scoped Classical BigOperators
open MvPolynomial J6ActiveAllocation J6BlockFactor J6FixedProfile
open J6PacketCoefficientBridge J6LiteralCoeff

variable {R I M G K : Type*} [CommRing R] [Fintype I] [Fintype M]
  [DecidableEq G] [DecidableEq K]

def actualRows (block : I → G × K) (g : G) (k : K) : Finset I :=
  Finset.univ.filter (fun i => block i = (g,k))

omit [DecidableEq G] [DecidableEq K] [Fintype I] in
theorem literal_row_congr (w : M → ℕ) (f : I → Option M → R)
    (i : I) (bit : Bool) (base : R) (cross : M → R)
    (h0 : scaled w f i none = LiteralPortCompiler.affine bit base)
    (hm : ∀ m, scaled w f i (some m) = LiteralPortCompiler.slope bit * cross m) :
    (∑ v : Option M, monomial (exponent v) (scaled w f i v)) =
    J6RecursiveModes.row bit base cross := by
  rw [← source_signed_row bit base cross]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  cases v with
  | none => rw [h0]; rfl
  | some m => rw [hm m]; rfl

/-- The weighted finite extraction (from the exact factorized contraction)
is the actual new tensor's target coefficient times its own source moments. -/
theorem actual_packet_entry
    (w : M → ℕ) (f : I → Option M → R)
    (block : I → G × K) (target source : M → G × K)
    (b : M → Fin (Fintype.card I+1)) (g : G) (k : K)
    (bit : I → Bool) (base : I → R) (cross : I → M → R) (L : M → R)
    (hzero : ∀ i m, block i ≠ target m → f i (some m) = 0)
    (h0 : ∀ i, block i = (g,k) → scaled w f i none = LiteralPortCompiler.affine (bit i) (base i))
    (hm : ∀ i, block i = (g,k) → ∀ m,
      scaled w f i (some m) = LiteralPortCompiler.slope (bit i) * cross i m) :
    targetCoeff w f block target b (g,k) *
      (∏ m ∈ Finset.univ.filter (fun m => source m = (g,k)), L m ^ (b m).val) =
      J6RecursiveModes.packet target source g k (actualRows block g k)
        bit base cross L (profileFinsupp b) := by
  classical
  let S := actualRows block g k
  have he (m : M) : profileFinsupp b m = (b m).val := by simp [profileFinsupp]
  rw [target_coefficient_is_polynomial w f block target b (g,k) hzero]
  unfold J6RecursiveModes.packet
  simp only [he]
  congr 1
  have hpoly :
      (∏ i : rows block (g,k), ∑ v : Option M, monomial (exponent v) (scaled w f i.val v)) =
        ∏ i ∈ actualRows block g k, J6RecursiveModes.row (bit i) (base i) (cross i) := by
    calc
      _ = ∏ i : rows block (g,k), J6RecursiveModes.row (bit i.val) (base i.val) (cross i.val) := by
        refine Finset.prod_congr rfl (fun i _ => ?_)
        exact literal_row_congr w f i.val (bit i.val) (base i.val) (cross i.val)
          (h0 i.val i.property) (hm i.val i.property)
      _ = ∏ i ∈ S, J6RecursiveModes.row (bit i) (base i) (cross i) := by
        let f' (i : I) := J6RecursiveModes.row (bit i) (base i) (cross i)
        change (∏ i : rows block (g,k), f' i.val) = ∏ i ∈ S, f' i
        let e : rows block (g,k) ≃ {i // i ∈ S} :=
          Equiv.subtypeEquivRight (fun i => by simp [S,actualRows])
        exact (Fintype.prod_equiv e (fun i => f' i.val) (fun i => f' i.val) (fun _ => rfl)).trans
          (Finset.prod_coe_sort S f')
  rw [hpoly]
  congr 1
  ext m
  by_cases h : target m = (g,k) <;> simp [h]

#print axioms literal_row_congr
#print axioms actual_packet_entry
end J6R10PacketAssembly
