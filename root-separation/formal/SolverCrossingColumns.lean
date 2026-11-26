import SolverPhysicalModes
import SolverColumnPorts
import SolverPacketCompatibility

noncomputable section
namespace RootSeparation.Solver
open S11 Polynomial Classical

variable {e : ℕ} (F : SourcePolynomial e) {s : ℕ} {c : Call F.f}
variable (G : CallLayout s c) (t : callCenters s c)

def rowGroup (x : c.network.Wire) : Fin 64 := (G.packing.cell x).1 (G.coord t)
def colGroup (y : c.network.Wire) : Fin 64 := (G.packing.cell y).2 (G.coord t)
def wirePacket (x : c.network.Wire) : G.Packet := (G.packing.position x).1
def wireTile (y : c.network.Wire) : Fin (2^(level t.val+1)) :=
  ⟨(G.packing.position y).2.val % 2^(level t.val+1),Nat.mod_lt _ (by positivity)⟩

abbrev CrossingColumns (x : c.network.Wire) :=
  {y : c.network.Wire // wirePacket F G x = wirePacket F G y ∧ rowGroup F G t x ≠ colGroup F G t y}
abbrev ModeColumns (z : ActualMode G t) :=
  {y : c.network.Wire // wirePacket F G y = z.1.val ∧
    colGroup F G t y = tileSource G t z ∧ wireTile F G t y = z.2.1}

theorem source_ne_target (z : ActualMode G t) :
    tileSource G t z ≠ tileTarget G t z := by
  obtain ⟨i,hi,hm⟩ := z.1.property
  have h : i = G.coord t := Fin.ext hi
  subst i
  unfold tileSource tileTarget
  split
  · exact hm
  · exact Ne.symm hm

/-- Each genuine crossing uses the unique tile of its physical column.
This reindexing counts neither padding slots nor fictitious child edges. -/
def crossingColumnsEquiv (x : c.network.Wire) :
    (CrossingColumns F G t x × Fin (callPrecision s c t.val-1)) ≃
      (Σ z : TargetAt F G t (rowGroup F G t x) (wirePacket F G x), ModeColumns F G t z.val) where
  toFun a := by
    let y := a.1
    let z := modeOfCross G t x y.val y.property.1 y.property.2 a.2
    refine ⟨⟨z,y.property.1.symm,modeOfCross_target G t x y.val y.property.1 y.property.2 a.2⟩,
      ⟨y.val,rfl,(modeOfCross_source G t x y.val y.property.1 y.property.2 a.2).symm,rfl⟩⟩
  invFun a := by
    let z := a.1
    let y := a.2
    refine (⟨y.val,z.property.1.symm.trans y.property.1.symm,?_⟩,z.val.2.2)
    intro h
    exact source_ne_target F G t z.val ((y.property.2.1.symm.trans h.symm).trans z.property.2.symm)
  left_inv a := rfl
  right_inv := by
    rintro ⟨⟨⟨m,y₀,b⟩,hk,hg⟩,y,hy,hs,ht⟩
    have hpack : wirePacket F G x = wirePacket F G y := hk.symm.trans hy.symm
    have hcross : rowGroup F G t x ≠ colGroup F G t y := by
      intro h
      exact source_ne_target F G t ⟨m,y₀,b⟩ ((hs.symm.trans h.symm).trans hg.symm)
    have hz : modeOfCross G t x y hpack hcross b = ⟨m,y₀,b⟩ := by
      exact Prod.ext (Subtype.ext hy) (Prod.ext ht rfl)
    apply Sigma.ext (Subtype.ext hz)
    exact (Subtype.heq_iff_coe_eq (fun _ => by
      change _ ↔ _
      simp only [ModeColumns,hz])).2 rfl

end RootSeparation.Solver

#print axioms RootSeparation.Solver.crossingColumnsEquiv
