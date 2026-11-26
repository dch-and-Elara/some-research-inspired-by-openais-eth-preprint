import SolverPacket

noncomputable section
namespace RootSeparation.Solver
open S11

variable {f : Polynomial ℤ} {s : ℕ} {c : Call f}
variable (G : CallLayout s c) (t : callCenters s c)

theorem crossing_mixed (x y : c.network.Wire)
    (h : (G.packing.position x).1 = (G.packing.position y).1)
    (cross : (G.packing.cell x).1 (G.coord t) ≠ (G.packing.cell y).2 (G.coord t)) :
    (G.packing.position y).1 ∈ {k | ∃ i : Fin (callA s c), i.val = level t.val ∧
      (G.packing.pair k i).1 ≠ (G.packing.pair k i).2} := by
  refine ⟨G.coord t,rfl,?_⟩
  intro he
  have hx := G.packing.orientation x (G.coord t)
  have hy := G.packing.orientation y (G.coord t)
  rw [h] at hx
  have hswap : (G.packing.pair (G.packing.position y).1 (G.coord t)).swap =
      G.packing.pair (G.packing.position y).1 (G.coord t) :=
    Prod.ext he.symm he
  simp only [hswap,ite_self] at hx hy
  exact cross ((congrArg Prod.fst hx).trans (he.trans (congrArg Prod.snd hy).symm))

def modeOfCross (x y : c.network.Wire)
    (h : (G.packing.position x).1 = (G.packing.position y).1)
    (cross : (G.packing.cell x).1 (G.coord t) ≠ (G.packing.cell y).2 (G.coord t))
    (b : Fin (callPrecision s c t.val-1)) : ActualMode G t :=
  ⟨⟨(G.packing.position y).1,crossing_mixed G t x y h cross⟩,
    ⟨(G.packing.position y).2.val % 2^(level t.val+1),Nat.mod_lt _ (by positivity)⟩, b⟩

theorem modeOfCross_source (x y : c.network.Wire)
    (h : (G.packing.position x).1 = (G.packing.position y).1)
    (cross : (G.packing.cell x).1 (G.coord t) ≠ (G.packing.cell y).2 (G.coord t))
    (b : Fin (callPrecision s c t.val-1)) :
    tileSource G t (modeOfCross G t x y h cross b) = (G.packing.cell y).2 (G.coord t) := by
  have hy := congrArg Prod.snd (G.packing.orientation y (G.coord t))
  unfold tileSource modeOfCross
  dsimp only
  rw [tile_constant_group_bit]
  change (G.packing.cell y).2 (G.coord t) = (if (G.packing.position y).2.val.testBit (level t.val) then
      (G.packing.pair (G.packing.position y).1 (G.coord t)).swap
      else G.packing.pair (G.packing.position y).1 (G.coord t)).2 at hy
  rw [hy]
  split <;> rfl

theorem modeOfCross_target (x y : c.network.Wire)
    (h : (G.packing.position x).1 = (G.packing.position y).1)
    (cross : (G.packing.cell x).1 (G.coord t) ≠ (G.packing.cell y).2 (G.coord t))
    (b : Fin (callPrecision s c t.val-1)) :
    tileTarget G t (modeOfCross G t x y h cross b) = (G.packing.cell x).1 (G.coord t) := by
  have hx := congrArg Prod.fst (G.packing.orientation x (G.coord t))
  have hbit := tile_crossing_bit G t x y h cross
  unfold tileTarget modeOfCross
  dsimp only
  rw [tile_constant_group_bit, ← hbit]
  change (G.packing.cell x).1 (G.coord t) = (if (G.packing.position x).2.val.testBit (level t.val) then
      (G.packing.pair (G.packing.position x).1 (G.coord t)).swap
      else G.packing.pair (G.packing.position x).1 (G.coord t)).1 at hx
  rw [hx,h]
  split <;> rfl

end RootSeparation.Solver

#print axioms RootSeparation.Solver.modeOfCross_source
#print axioms RootSeparation.Solver.modeOfCross_target
