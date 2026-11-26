import SolverPacket

noncomputable section
namespace RootSeparation.Solver
open S11 Polynomial
open scoped BigOperators

variable {f : ℤ[X]} {s : ℕ} {c : Call f}
variable (G : CallLayout s c) (t : callCenters s c)

theorem target_tile_bit {g : Fin 64} {k : G.Packet}
    (x : {w : PacketPort G t g k // isColumn G t w = false})
    (z : ActualMode G t) (hk : z.1.val = k) (hg : tileTarget G t z = g) :
    (slotOf G t x.val).val.testBit (level t.val) = z.2.1.val.testBit (level t.val) := by
  let w := wireOf G t x.val
  have hslot : (G.packing.position w).1 = k := x.val.property
  have hrow : (G.packing.cell w).1 (G.coord t) = g := by
    have hx := x.val.val.property
    change S8.DChild.symbol G.left G.right (G.coord t)
      (if isColumn G t x.val then Sum.inr (c.network.col w) else Sum.inl (c.network.row w)) = g at hx
    rw [if_neg (by simp [x.property])] at hx
    rw [G.cells]
    exact hx
  obtain ⟨i,hi,hm⟩ := z.1.property
  have he : i = G.coord t := Fin.ext hi
  rw [he,hk] at hm
  have hx := G.packing.orientation w (G.coord t)
  rw [hslot] at hx
  have hpair := congrArg Prod.fst hx
  change (G.packing.cell w).1 (G.coord t) =
    (if (slotOf G t x.val).val.testBit (level t.val) then (G.packing.pair k (G.coord t)).swap
      else G.packing.pair k (G.coord t)).1 at hpair
  rw [hrow] at hpair
  unfold tileTarget at hg
  rw [hk] at hg
  cases hx : (slotOf G t x.val).val.testBit (level t.val) <;>
    cases hz : z.2.1.val.testBit (level t.val) <;> simp only [hx, hz, Bool.false_eq_true,
      if_false, if_true, Prod.fst_swap] at hpair hg ⊢
  · exact (hm (hpair.symm.trans hg.symm)).elim
  · exact (hm (hg.trans hpair)).elim

section Bounds

variable {K : Type*} [Field K] [CharZero K]
variable (v : AddValuation K (WithTop ℤ)) (h₂ : v (2:K) = 1) (ζ : K) (hζ : 0 ≤ v ζ)

include h₂ hζ in
theorem localForm_integral {g : Fin 64} {k : G.Packet}
    (bits : PacketPort G t g k → Bool)
    (x : {w : PacketPort G t g k // isColumn G t w = false}) :
    0 ≤ v (localForm G t ζ bits x) := by
  classical
  unfold localForm
  apply S7.valuation_sum_bound v
  intro y _
  rw [v.map_mul]
  apply add_nonneg
  · have hb := eval_bound v (kernel_integral_shift v h₂ (slotOf G t x.val)
      (slotOf G t y.val) (active_mem_grid t)) hζ
    simpa only [eval_comp,eval_add,eval_C,eval_mul,eval_X,nodeProbe] using hb
  · exact S7.valuation_nat_nonnegative v _

include h₂ hζ in
theorem crossingCoeff_factor {g : Fin 64} {k : G.Packet}
    (x : {w : PacketPort G t g k // isColumn G t w = false})
    (z : ActualMode G t) (hk : z.1.val = k) (hg : tileTarget G t z = g) :
    ∃ q : K, 0 ≤ v q ∧ crossingCoeff G t ζ x z = (2:K)^(z.2.2.val+1) * q := by
  let i := level t.val
  let y : Fin (callL s c) := ⟨z.2.1.val, z.2.1.isLt.trans_le
    (Nat.pow_le_pow_right (by decide) (G.coord t).isLt)⟩
  obtain ⟨h,_⟩ := crossing_modes_native v h₂ (i := level t.val) (Nat.le_of_lt (G.coord t).isLt)
    (active_mem_grid t) (active_ne_zero t) rfl (slotOf G t x.val) y
    (target_tile_bit G t x z hk hg) ζ hζ _ (callPrecision_pos s c t.val)
  obtain ⟨q,hq,hqeq⟩ := h z.2.2.val
  have hmod : y.val % 2^(i+1) = z.2.1.val := Nat.mod_eq_of_lt z.2.1.isLt
  rw [hmod] at hqeq
  have hd : (↑(t.val-(z.2.1.val:ℤ)+(slotOf G t x.val).val:ℤ):K)
      + shiftScale K (callA s c) * ζ =
      nodeProbe t ζ - (z.2.1.val:K) + (slotOf G t x.val).val := by
    unfold nodeProbe
    push_cast
    ring
  rw [hd] at hqeq
  exact ⟨q,hq,hqeq⟩

include h₂ hζ in
theorem crossingCoeff_integral {g : Fin 64} {k : G.Packet}
    (x : {w : PacketPort G t g k // isColumn G t w = false})
    (z : ActualMode G t) (hk : z.1.val = k) (hg : tileTarget G t z = g) :
    0 ≤ v (crossingCoeff G t ζ x z) := by
  obtain ⟨q,hq,he⟩ := crossingCoeff_factor G t v h₂ ζ hζ x z hk hg
  rw [he, v.map_mul,v.map_pow,h₂]
  exact add_nonneg (nsmul_nonneg (by norm_num) _) hq

omit [CharZero K] in
private theorem nonnegative_product {I : Type*} (S : Finset I) (f : I → K)
    (h : ∀ i ∈ S, 0 ≤ v (f i)) : 0 ≤ v (∏ i ∈ S,f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert i S hi ih =>
    rw [Finset.prod_insert hi,v.map_mul]
    exact add_nonneg (h i (Finset.mem_insert_self _ _))
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

omit [CharZero K] in
theorem sourceTile_integral {g : Fin 64} {k : G.Packet} (bits : PacketPort G t g k → Bool)
    (z : ActualMode G t) :
    0 ≤ v (sourceTile G t bits z) := by
  classical
  unfold sourceTile
  apply S7.valuation_sum_bound v
  intro y _
  split
  · rw [v.map_mul,v.map_pow]
    exact add_nonneg (nsmul_nonneg (S7.valuation_nat_nonnegative v _) _)
      (S7.valuation_nat_nonnegative v _)
  · simp

include h₂ hζ in
theorem nativePacket_integral (β : List ℕ) (g : Fin 64) (k : G.Packet)
    (bits : PacketPort G t g k → Bool) :
    0 ≤ v (nativePacket G t ζ β g k bits) := by
  classical
  unfold nativePacket packetValue
  rw [v.map_mul]
  apply add_nonneg
  · unfold packetCoeff
    apply S7.valuation_sum_bound v
    intro choices _
    split
    · apply nonnegative_product v
      intro x _
      cases choices x with
      | none =>
        change 0 ≤ v (if bits x.val then localForm G t ζ bits x else 1-localForm G t ζ bits x)
        split
        · exact localForm_integral G t v h₂ ζ hζ bits x
        · rw [sub_eq_add_neg]
          apply (le_min (by simp) ?_).trans (v.map_add _ _)
          rw [v.map_neg]
          exact localForm_integral G t v h₂ ζ hζ bits x
      | some z =>
        change 0 ≤ v (if bits x.val then crossingCoeff G t ζ x z.val else -crossingCoeff G t ζ x z.val)
        have h := crossingCoeff_integral G t v h₂ ζ hζ x z.val z.property.1 z.property.2
        split
        · exact h
        · rwa [v.map_neg]
    · simp
  · apply nonnegative_product v
    intro z _
    rw [v.map_pow]
    exact nsmul_nonneg (sourceTile_integral G t v bits z.val) _

end Bounds

#print axioms target_tile_bit
#print axioms localForm_integral
#print axioms crossingCoeff_factor
#print axioms crossingCoeff_integral
#print axioms nativePacket_integral

end RootSeparation.Solver
