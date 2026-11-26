import SolverPhysicalRows

noncomputable section
namespace RootSeparation.Solver
open S11 Classical
open scoped BigOperators

variable {s : ℕ} (F : SourcePolynomial (4*lambda s))
variable {c : Call F.f} (G : CallLayout s c)
variable (cap : probeCount c.edges (callL s c) ≤ 2^(4*lambda s))
variable (t : callCenters s c) (j : callProbes s c)

abbrev localData := nativeAffineData F G cap t j
abbrev nativeBits := ∀ g, (localData F G cap t j).Bits g

def affineLiteral (bits : nativeBits F G cap t j) (g : Fin 64)
    (r : (localData F G cap t j).affine.Rows g) : WordRing F.f (callPrecision s c t.val) :=
  let A := (localData F G cap t j).affine
  ∑ o : Option (A.TargetMode g), A.row g (bits g) r o *
    o.elim' 1 (fun z => A.readTile ⟨g,z⟩ (bits (A.source ⟨g,z⟩)))

private theorem reduce_integralRow (g : Fin 64) (k : G.Packet) (bits : GroupBits F G t g)
    (x : LocalRows F G t g k) (o : Option (TargetAt F G t g k)) :
    reduceElements F (callPrecision s c t.val) (integralRow F G cap t j g k bits x o) =
      (localData F G cap t j).localRow g bits k x o := by
  unfold integralRow PacketData.localRow
  rw [map_mul,map_pow,map_ofNat,reduced_is_reduceElements]

private theorem reduce_integralRead (g : Fin 64) (k : G.Packet) (bits : GroupBits F G t g)
    (z : SourceAt F G t g k) :
    reduceElements F (callPrecision s c t.val) (integralRead F G t g k bits z) =
      reduced F t (sourceTile G t (K := RationalCoefficients F) (packetBits F G t (k := k) bits) z.val)
        (sourceTile_integral G t (K := RationalCoefficients F) (rationalValuation F)
          (packetBits F G t (k := k) bits) z.val) := by
  unfold integralRead
  rw [reduced_is_reduceElements]

set_option maxHeartbeats 2400000 in
theorem affineLiteral_physical (Y X : c.network.Wire → Bool) (x : c.network.Wire) :
    let bits := splitPorts c.network G.left G.right (G.coord t) Y X
    affineLiteral F G cap t j bits (rowGroup F G t x) ⟨wirePacket F G x,rowPort F G t x⟩ =
      reduceElements F (callPrecision s c t.val) (integralRowLiteral F G cap t j Y X x) := by
  dsimp only
  rw [integralRowLiteral_reduce,expandedRowLiteral_modes]
  unfold modeRowLiteral
  dsimp only
  simp only [map_add,map_sum,map_mul,reduce_integralRow,reduce_integralRead]
  let g := rowGroup F G t x
  let k := wirePacket F G x
  let r := rowPort F G t x
  let bits := splitPorts c.network G.left G.right (G.coord t) Y X
  let D := localData F G cap t j
  let A := D.affine
  let C (z : A.TargetMode g) := A.row g (bits g) ⟨k,r⟩ (some z) *
      A.readTile ⟨g,z⟩ (bits (A.source ⟨g,z⟩))
  unfold affineLiteral
  rw [Fintype.sum_option]
  change A.row g (bits g) ⟨k,r⟩ none * 1 + ∑ z, C z = _
  rw [mul_one,PacketData.affine_row,globalRow]
  congr 1
  have hsum (u : G.Packet) (hu : u ≠ k) : (∑ z : D.Modes g u, C ⟨u,z⟩) = 0 := by
    apply Finset.sum_eq_zero
    intro z _
    unfold C
    rw [PacketData.affine_row,globalRow,dif_neg hu,zero_mul]
  rw [Fintype.sum_sigma C,Finset.sum_eq_single_of_mem k (Finset.mem_univ _) (fun u _ hu => hsum u hu)]
  apply Finset.sum_congr rfl
  intro z _
  unfold C
  rw [PacketData.affine_row,globalRow,dif_pos rfl]

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 1024 in
theorem nativeAffine_sample (Y X : c.network.Wire → Bool) :
    let bits := splitPorts c.network G.left G.right (G.coord t) Y X
    let D := localData F G cap t j
    let A := D.affine
    (∏ g, A.old g (bits g) * ∏ r, affineLiteral F G cap t j bits g r) =
      reduceElements F (callPrecision s c t.val)
        (integralPhysicalTerm F G cap t j ((splitPortsEquiv c.network G.left G.right (G.coord t)) (Y,X))) := by
  dsimp only
  let bits := splitPorts c.network G.left G.right (G.coord t) Y X
  let p := callPrecision s c t.val
  let D := localData F G cap t j
  let phi := fromInteger F.f p
  have hold : (∏ g, D.old g (bits g)) = phi (c.network.rowProduct Y * c.network.colProduct X) := by
    have h := childOldProducts (P := G.Packet) c.network G.left G.right (G.coord t)
      Y X phi G.packing.position (fun _ _ _ => (0:WordRing F.f p))
    exact h
  have hbits : (splitPortsEquiv c.network G.left G.right (G.coord t)).symm
      ((splitPortsEquiv c.network G.left G.right (G.coord t)) (Y,X)) = (Y,X) :=
    Equiv.symm_apply_apply _ _
  let term (pair : (c.network.Wire → Bool) × (c.network.Wire → Bool)) : integralElements F :=
    let old := c.network.rowProduct pair.1 * c.network.colProduct pair.2
    ⟨integerRational F.f old,rationalValuation_integer F old⟩ *
      ∏ x, integralRowLiteral F G cap t j pair.1 pair.2 x
  change (∏ g, D.old g (bits g) * ∏ r, affineLiteral F G cap t j bits g r) =
    reduceElements F p (term ((splitPortsEquiv c.network G.left G.right (G.coord t)).symm
      ((splitPortsEquiv c.network G.left G.right (G.coord t)) (Y,X))))
  rw [hbits]
  unfold term
  dsimp only
  rw [map_mul,map_prod,Finset.prod_mul_distrib,hold,reduceElements_int]
  apply congrArg (phi (c.network.rowProduct Y * c.network.colProduct X) * ·)
  let f (r : Σ g : Fin 64, Σ k : G.Packet, LocalRows F G t g k) :=
    affineLiteral F G cap t j bits r.1 r.2
  rw [← Fintype.prod_sigma f]
  apply Fintype.prod_equiv (allRowPorts F G t).symm
  intro r
  have hr := affineLiteral_physical F G cap t j Y X ((allRowPorts F G t).symm r)
  change f ((allRowPorts F G t) ((allRowPorts F G t).symm r)) = _ at hr
  rwa [Equiv.apply_symm_apply] at hr

set_option maxHeartbeats 1200000 in
set_option maxRecDepth 1024 in
theorem exactCallProbe_affine_sample :
    tryWord F.monic (callPrecision s c t.val) (exactCallProbe F G cap t j) =
      some (localData F G cap t j).affine.sample := by
  rw [exactCallProbe_reduce]
  apply congrArg some
  unfold AffinePacket.sample
  apply Finset.sum_congr (Finset.ext fun _ => by simp)
  intro bits _
  let e := splitPortsEquiv c.network G.left G.right (G.coord t)
  let pair := e.symm bits
  have hb : splitPorts c.network G.left G.right (G.coord t) pair.1 pair.2 = bits :=
    e.apply_symm_apply bits
  have h := nativeAffine_sample F G cap t j pair.1 pair.2
  change (∏ g, (localData F G cap t j).old g
    (splitPorts c.network G.left G.right (G.coord t) pair.1 pair.2 g) *
    ∏ r, affineLiteral F G cap t j
      (splitPorts c.network G.left G.right (G.coord t) pair.1 pair.2) g r) =
    reduceElements F (callPrecision s c t.val)
      (integralPhysicalTerm F G cap t j (splitPorts c.network G.left G.right (G.coord t) pair.1 pair.2)) at h
  rw [hb] at h
  exact h.symm

end RootSeparation.Solver

#print axioms RootSeparation.Solver.affineLiteral_physical
#print axioms RootSeparation.Solver.exactCallProbe_affine_sample
