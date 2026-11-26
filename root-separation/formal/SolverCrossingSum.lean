import SolverCrossingColumns
import SolverRowApproximation

noncomputable section
namespace RootSeparation.Solver
open S11 Polynomial Classical
open scoped BigOperators

variable {s : ℕ} (F : SourcePolynomial (4*lambda s))
variable {c : Call F.f} (G : CallLayout s c)
variable (cap : probeCount c.edges (callL s c) ≤ 2^(4*lambda s))
variable (t : callCenters s c) (j : callProbes s c)

theorem colGroup_eq (y : c.network.Wire) :
    colGroup F G t y = G.right (c.network.col y) (G.coord t) := by
  unfold colGroup
  rw [G.cells]
  rfl

theorem rowGroup_eq (x : c.network.Wire) :
    rowGroup F G t x = G.left (c.network.row x) (G.coord t) := by
  unfold rowGroup
  rw [G.cells]
  rfl

def rowPort (x : c.network.Wire) : LocalRows F G t (rowGroup F G t x) (wirePacket F G x) :=
  ⟨⟨⟨(x,false),(rowGroup_eq F G t x).symm⟩,rfl⟩,rfl⟩

theorem crossingSeries_in_modes (x : c.network.Wire) (y : CrossingColumns F G t x) :
    realCrossingSeries F G t cap j x y.val =
      ∑ b : Fin (callPrecision s c t.val-1),
        crossingCoeff G t (callPoint F cap j) (rowPort F G t x)
          (modeOfCross G t x y.val y.property.1 y.property.2 b) *
        (((G.packing.position y.val).2.val / 2^(level t.val+1) : ℕ):RationalCoefficients F)^b.val := by
  let K := RationalCoefficients F
  let p := callPrecision s c t.val
  let ζ : K := callPoint F cap j
  let u := (G.packing.position x).2.val
  let v := (G.packing.position y.val).2.val
  let i := level t.val
  let y₀ := v % 2^(i+1)
  let d : K := (((t.val-(y₀:ℕ)+u:ℤ):K) + shiftScale K (callA s c)*ζ)
  let d' : K := nodeProbe t ζ - (y₀:K) + (u:K)
  have hd : d=d' := by
    dsimp [d,d',nodeProbe]
    push_cast
    ring
  let coef (d : K) (b : ℕ) :=
    ((shiftedNumerator K (callA s c) t.val).eval ζ / d) *
      ((2:K)^(i+1) / d)^b * ((v / 2^(i+1) : ℕ):K)^b
  change (∑ b ∈ Finset.range (p-1), coef d b) = ∑ b : Fin (p-1), coef d' b.val
  rw [hd,Fin.sum_univ_eq_sum_range]

def tileReadTerm (X : c.network.Wire → Bool) (z : ActualMode G t) (y : c.network.Wire) :
    RationalCoefficients F :=
  (((G.packing.position y).2.val / 2^(level t.val+1) : ℕ):RationalCoefficients F)^z.2.2.val *
    (X y).toNat

theorem sourceTile_in_columns (Y X : c.network.Wire → Bool) (z : ActualMode G t) :
    sourceTile G t (K := RationalCoefficients F)
      (splitPacketBits G t (g := tileSource G t z) (k := z.1.val) Y X) z =
        ∑ y : ModeColumns F G t z, tileReadTerm F G t X z y.val := by
  rw [sourceTile_physical]
  let U := RealColumns G t (tileSource G t z) z.1.val
  let q (y : U) := (G.packing.position y.val).2.val % 2^(level t.val+1) = z.2.1.val
  let v (y : U) := tileReadTerm F G t X z y.val
  change (∑ y : U, if q y then v y else 0) = _
  rw [← Finset.sum_filter,
    Finset.sum_subtype (p := q) (Finset.univ.filter q) (fun _ => by simp) v]
  apply Fintype.sum_equiv
    { toFun := fun y : {y : U // q y} => (⟨y.val.val,y.val.property.2,
        (colGroup_eq F G t y.val.val).trans y.val.property.1, Fin.ext y.property⟩ :
          ModeColumns F G t z)
      invFun := fun y => ⟨⟨y.val,(colGroup_eq F G t y.val).symm.trans y.property.2.1,
        y.property.1⟩,congrArg Fin.val y.property.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  intro _
  rfl

set_option maxHeartbeats 1200000 in
set_option maxRecDepth 1024 in
/-- Printed cross-column sum, reindexed by the actual targeted tile
    modes and their actual source-side column bits. -/
theorem crossingSum_in_modes (Y X : c.network.Wire → Bool) (x : c.network.Wire) :
    (∑ y : CrossingColumns F G t x, realCrossingSeries F G t cap j x y.val * (X y.val).toNat) =
      ∑ z : TargetAt F G t (rowGroup F G t x) (wirePacket F G x),
        crossingCoeff G t (callPoint F cap j) (rowPort F G t x) z.val *
          sourceTile G t (K := RationalCoefficients F)
            (splitPacketBits G t (g := tileSource G t z.val) (k := z.val.1.val) Y X) z.val := by
  let p := callPrecision s c t.val
  let A := CrossingColumns F G t x
  let B := TargetAt F G t (rowGroup F G t x) (wirePacket F G x)
  let e := crossingColumnsEquiv F G t x
  let coeff (z : ActualMode G t) :=
    crossingCoeff G t (callPoint F cap j) (rowPort F G t x) z
  let a (m : A × Fin (p-1)) :=
    coeff (modeOfCross G t x m.1.val m.1.property.1 m.1.property.2 m.2) *
      tileReadTerm F G t X (modeOfCross G t x m.1.val m.1.property.1 m.1.property.2 m.2) m.1.val
  let b (m : Σ z : B, ModeColumns F G t z.val) := coeff m.1.val * tileReadTerm F G t X m.1.val m.2.val
  calc
    _ = ∑ m, a m := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro y _
      rw [crossingSeries_in_modes, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro b _
      exact mul_assoc _ _ _
    _ = ∑ m, b m := Fintype.sum_equiv e a b (fun _ => rfl)
    _ = _ := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro z _
      rw [sourceTile_in_columns,Finset.mul_sum]

theorem expandedRow_field (Y X : c.network.Wire → Bool) (x : c.network.Wire) :
    (expandedRow F G cap t j X x).val =
      localForm G t (callPoint F cap j) (splitPacketBits G t Y X)
        (rowPort F G t x) +
      ∑ z : TargetAt F G t (rowGroup F G t x) (wirePacket F G x),
        crossingCoeff G t (callPoint F cap j) (rowPort F G t x) z.val *
          sourceTile G t (K := RationalCoefficients F)
            (splitPacketBits G t (g := tileSource G t z.val) (k := z.val.1.val) Y X) z.val := by
  let K := RationalCoefficients F
  let same (y : c.network.Wire) : Prop :=
    G.right (c.network.col y) (G.coord t) = rowGroup F G t x ∧ wirePacket F G y = wirePacket F G x
  let cross (y : c.network.Wire) : Prop :=
    wirePacket F G x = wirePacket F G y ∧ rowGroup F G t x ≠ colGroup F G t y
  let loc (y : c.network.Wire) : K :=
    realKernelAt F G t cap j x y * (X y).toNat
  let cr (y : c.network.Wire) : K := realCrossingSeries F G t cap j x y * (X y).toNat
  change (integralElements F).subtype (expandedRow F G cap t j X x) = _
  unfold expandedRow
  simp only [map_sum,map_mul,map_natCast]
  calc
    _ = ∑ y : c.network.Wire, ((if same y then loc y else 0) + (if cross y then cr y else 0)) := by
      apply Finset.sum_congr rfl
      intro y _
      by_cases hp : wirePacket F G x = wirePacket F G y
      · by_cases hg : rowGroup F G t x = colGroup F G t y
        · have hs : same y := ⟨((colGroup_eq F G t y).symm.trans hg.symm),hp.symm⟩
          have hc : ¬ cross y := fun h => h.2 hg
          rw [if_pos hs,if_neg hc,add_zero]
          have h : ¬ ((G.packing.position x).1 = (G.packing.position y).1 ∧
              (G.packing.cell x).1 (G.coord t) ≠ (G.packing.cell y).2 (G.coord t)) :=
            fun h => h.2 hg
          change expandedKernelEntry F G cap t j x y * _ = _
          rw [expandedKernelEntry,if_neg h]
          unfold exactKernelEntry kernel loc realKernelAt
          unfold wirePacket at hp
          rw [if_pos hp]
        · have hs : ¬ same y := fun h => hg (h.1.symm.trans (colGroup_eq F G t y).symm)
          have hc : cross y := ⟨hp,hg⟩
          rw [if_neg hs,if_pos hc,zero_add]
          change expandedKernelEntry F G cap t j x y * _ = _
          unfold cross wirePacket rowGroup colGroup at hc
          rw [expandedKernelEntry,if_pos hc]
      · have hs : ¬ same y := fun h => hp h.2.symm
        have hc : ¬ cross y := fun h => hp h.1
        rw [if_neg hs,if_neg hc,add_zero]
        change expandedKernelEntry F G cap t j x y * _ = _
        unfold cross wirePacket rowGroup colGroup at hc
        rw [expandedKernelEntry,if_neg hc]
        unfold exactKernelEntry kernel
        unfold wirePacket at hp
        rw [if_neg hp,eval_zero,zero_mul]
    _ = (∑ y : RealColumns G t (rowGroup F G t x) (wirePacket F G x), loc y.val) +
        ∑ y : CrossingColumns F G t x, cr y.val := by
      rw [Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter]
      rw [Finset.sum_subtype (p := same) (Finset.univ.filter same) (fun _ => by simp),
          Finset.sum_subtype (p := cross) (Finset.univ.filter cross) (fun _ => by simp)]
      rfl
    _ = _ := by
      have hl := localForm_physical (K := K) G t (callPoint F cap j) Y X _ _ (rowPort F G t x)
      change _ = ∑ y : RealColumns G t (rowGroup F G t x) (wirePacket F G x), loc y.val at hl
      rw [← hl]
      exact congrArg (_ + ·) (crossingSum_in_modes F G cap t j Y X x)

end RootSeparation.Solver

#print axioms RootSeparation.Solver.crossingSeries_in_modes
#print axioms RootSeparation.Solver.crossingSum_in_modes
#print axioms RootSeparation.Solver.expandedRow_field
