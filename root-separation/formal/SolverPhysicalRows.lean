import SolverCrossingSum
import SolverChildCompatibility

noncomputable section
namespace RootSeparation.Solver
open S11 Classical
open scoped BigOperators

variable {s : ℕ} (F : SourcePolynomial (4*lambda s))
variable {c : Call F.f} (G : CallLayout s c)
variable (cap : probeCount c.edges (callL s c) ≤ 2^(4*lambda s))
variable (t : callCenters s c) (j : callProbes s c)

def allRowPorts : c.network.Wire ≃ (Σ g : Fin 64, Σ k : G.Packet, LocalRows F G t g k) where
  toFun x := ⟨rowGroup F G t x,wirePacket F G x,rowPort F G t x⟩
  invFun x := wireOf G t x.2.2.val
  left_inv x := rfl
  right_inv x := by
    rcases x with ⟨g,k,⟨⟨⟨⟨w,b⟩,hw⟩,hp⟩,hb⟩⟩
    have h : b = false := hb
    subst b
    have hg : rowGroup F G t w = g := (rowGroup_eq F G t w).trans hw
    have hk : wirePacket F G w = k := hp
    cases hg
    cases hk
    rfl

def integralRowLiteral (Y X : c.network.Wire → Bool) (x : c.network.Wire) : integralElements F :=
  let r : integralElements F :=
    ⟨rowLinearAt F G cap t j X x,rowLinearAt_integral F G cap t j X x⟩
  if Y x then r else 1-r

def expandedRowLiteral (Y X : c.network.Wire → Bool) (x : c.network.Wire) : integralElements F :=
  let r := expandedRow F G cap t j X x
  if Y x then r else 1-r

theorem integralRowLiteral_reduce (Y X : c.network.Wire → Bool) (x : c.network.Wire) :
    reduceElements F (callPrecision s c t.val) (integralRowLiteral F G cap t j Y X x) =
      reduceElements F (callPrecision s c t.val) (expandedRowLiteral F G cap t j Y X x) := by
  let p := callPrecision s c t.val
  let r : integralElements F := ⟨rowLinearAt F G cap t j X x,rowLinearAt_integral F G cap t j X x⟩
  have hr := reduceElements_spec F p r
  change tryWord F.monic p (rowLinearAt F G cap t j X x) = _ at hr
  have he := (Option.some.inj ((rowLinearAt_residue F G cap t j X x).symm.trans hr)).symm
  by_cases hY : Y x = true
  · simp only [integralRowLiteral,expandedRowLiteral,if_pos hY]
    exact he
  · simp only [integralRowLiteral,expandedRowLiteral,if_neg hY,map_sub,map_one]
    exact congrArg (fun x : WordRing F.f p => 1-x) he

def modeRowLiteral (Y X : c.network.Wire → Bool) (x : c.network.Wire) : integralElements F :=
  let bits := splitPorts c.network G.left G.right (G.coord t) Y X
  let g := rowGroup F G t x
  let k := wirePacket F G x
  let r := rowPort F G t x
  integralRow F G cap t j g k (bits g) r none +
    ∑ z : TargetAt F G t g k,
      integralRow F G cap t j g k (bits g) r (some z) *
        integralRead F G t (tileSource G t z.val) k (bits (tileSource G t z.val))
          ⟨z.val,z.property.1,rfl⟩

set_option maxHeartbeats 1000000 in
theorem expandedRowLiteral_modes (Y X : c.network.Wire → Bool) (x : c.network.Wire) :
    expandedRowLiteral F G cap t j Y X x = modeRowLiteral F G cap t j Y X x := by
  classical
  apply Subtype.ext
  let K := RationalCoefficients F
  let g := rowGroup F G t x
  let k := wirePacket F G x
  let r := rowPort F G t x
  let zeta := callPoint F cap j
  let bits := splitPorts c.network G.left G.right (G.coord t) Y X
  let loc := localForm G t zeta (splitPacketBits G t Y X) r
  let coeff (z : TargetAt F G t g k) := crossingCoeff G t zeta r z.val
  let tile (z : TargetAt F G t g k) :=
    sourceTile G t (K := K) (splitPacketBits G t (g := tileSource G t z.val) (k := z.val.1.val) Y X) z.val
  have hbit : packetBits F G t (bits g) r.val = Y x := rfl
  have hv := expandedRow_field F G cap t j Y X x
  change (expandedRow F G cap t j X x).val = loc + ∑ z, coeff z * tile z at hv
  have signrow (z : TargetAt F G t g k) :
      (integralRow F G cap t j g k (bits g) r (some z)).val =
        (if Y x then coeff z else -coeff z) := by
    let w := z.val.2.2.val+1
    have hw : (2:K)^w ≠ 0 := pow_ne_zero _ (NeZero.ne 2)
    change (2:K)^w * (if packetBits F G t (bits g) r.val then coeff z / (2:K)^w
        else -(coeff z / (2:K)^w)) = _
    rw [hbit]
    by_cases b : Y x = true
    · rw [if_pos b,if_pos b,mul_div_cancel₀ _ hw]
    · rw [if_neg b,if_neg b,mul_neg,mul_div_cancel₀ _ hw]
  have read (z : TargetAt F G t g k) :
      (integralRead F G t (tileSource G t z.val) k (bits (tileSource G t z.val))
          ⟨z.val,z.property.1,rfl⟩).val = tile z := by
    have h (a b : G.Packet) (he : a = b) :
        sourceTile G t (K := K) (splitPacketBits G t (g := tileSource G t z.val) (k := a) Y X) z.val =
        sourceTile G t (K := K) (splitPacketBits G t (g := tileSource G t z.val) (k := b) Y X) z.val := by
      cases he
      rfl
    exact h k z.val.1.val z.property.1.symm
  have locval : (integralRow F G cap t j g k (bits g) r none).val =
      (if Y x then loc else 1-loc) := by
    change (2:K)^(0:ℕ) * (if packetBits F G t (bits g) r.val then loc else 1-loc) = _
    rw [pow_zero,one_mul,hbit]
  have htotal : (modeRowLiteral F G cap t j Y X x).val =
      (if Y x then loc else 1-loc) + ∑ z, (if Y x then coeff z else -coeff z)*tile z := by
    change (integralElements F).subtype (modeRowLiteral F G cap t j Y X x) = _
    unfold modeRowLiteral
    dsimp only
    rw [map_add,map_sum]
    refine congrArg₂ (·+·) locval ?_
    apply Finset.sum_congr (Finset.ext fun _ => by simp)
    intro z _
    rw [map_mul]
    exact congrArg₂ (·*·) (signrow z) (read z)
  rw [htotal]
  by_cases b : Y x = true
  · simp only [expandedRowLiteral, if_pos b,hv]
  · simp only [expandedRowLiteral,if_neg b]
    change (1:K) - (show K from (expandedRow F G cap t j X x).val) = _
    simp only [hv,neg_mul,Finset.sum_neg_distrib]
    ring

end RootSeparation.Solver

#print axioms RootSeparation.Solver.allRowPorts
#print axioms RootSeparation.Solver.integralRowLiteral_reduce
#print axioms RootSeparation.Solver.expandedRowLiteral_modes
