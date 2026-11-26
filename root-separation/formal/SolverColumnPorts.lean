import SolverNativeAffine
import SolverPortPartition

noncomputable section
namespace RootSeparation.Solver
open S11 Polynomial Classical
open scoped BigOperators

variable {f : ℤ[X]} {s : ℕ} {c : Call f}
variable (G : CallLayout s c) (t : callCenters s c)

abbrev RealColumns (g : Fin 64) (k : G.Packet) :=
  {y : c.network.Wire // G.right (c.network.col y) (G.coord t) = g ∧
    (G.packing.position y).1 = k}

def columnPortEquiv (g : Fin 64) (k : G.Packet) :
    {w : PacketPort G t g k // isColumn G t w = true} ≃ RealColumns G t g k where
  toFun y := by
    refine ⟨wireOf G t y.val, ?_, y.val.property⟩
    have h := y.val.val.property
    change S8.DChild.symbol G.left G.right (G.coord t)
      (if isColumn G t y.val then Sum.inr (c.network.col (wireOf G t y.val))
        else Sum.inl (c.network.row (wireOf G t y.val))) = g at h
    simpa only [y.property,if_true] using h
  invFun y := ⟨⟨⟨(y.val,true),y.property.1⟩,y.property.2⟩,rfl⟩
  left_inv y := by
    rcases y with ⟨⟨⟨⟨w,side⟩,hw⟩,hp⟩,hb⟩
    have h : side = true := hb
    subst side
    rfl
  right_inv y := rfl

variable {K : Type*} [Field K] [CharZero K]
variable (ζ : K)

def splitPacketBits {g : Fin 64} {k : G.Packet} (Y X : c.network.Wire → Bool)
    (p : PacketPort G t g k) : Bool :=
  splitPorts c.network G.left G.right (G.coord t) Y X g p.val

omit [CharZero K] in
theorem localForm_physical (Y X : c.network.Wire → Bool) (g : Fin 64) (k : G.Packet)
    (x : {w : PacketPort G t g k // isColumn G t w = false}) :
    localForm G t ζ (splitPacketBits G t Y X) x =
      ∑ y : RealColumns G t g k,
        (packetKernel K (callL s c) (slotOf G t x.val) (G.packing.position y.val).2).eval
          (nodeProbe t ζ) * (X y.val).toNat := by
  unfold localForm
  apply Fintype.sum_equiv (columnPortEquiv G t g k)
  rintro ⟨⟨⟨⟨w,b⟩,hw⟩,hp⟩,hb⟩
  have h : b = true := hb
  subst b
  rfl

omit [CharZero K] in
theorem sourceTile_physical (Y X : c.network.Wire → Bool) (g : Fin 64) (k : G.Packet)
    (z : ActualMode G t) :
    sourceTile G t (K := K) (splitPacketBits G t (g := g) (k := k) Y X) z =
      ∑ y : RealColumns G t g k,
        if (G.packing.position y.val).2.val % 2^(level t.val+1) = z.2.1.val then
          (((G.packing.position y.val).2.val / 2^(level t.val+1) : ℕ):K)^z.2.2.val * (X y.val).toNat
        else 0 := by
  unfold sourceTile
  apply Fintype.sum_equiv (columnPortEquiv G t g k)
  rintro ⟨⟨⟨⟨w,b⟩,hw⟩,hp⟩,hb⟩
  have h : b = true := hb
  subst b
  rfl

end RootSeparation.Solver

#print axioms RootSeparation.Solver.columnPortEquiv
#print axioms RootSeparation.Solver.localForm_physical
#print axioms RootSeparation.Solver.sourceTile_physical
