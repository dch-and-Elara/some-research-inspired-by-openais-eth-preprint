import P5OuterCenterRows
import J6R12BlueprintPacket

set_option warningAsError true

namespace Paper5.OuterCenters
open scoped BigOperators Polynomial Classical
open P11FullPacking J6R9PacketChild J6R9PacketScopes J6R10Repack
  J6R10RowAffine J6R10PacketAssembly J6R11Blueprint J6R10RowIdentity J6R9Recursive

variable {E A B G R : Type} [Fintype E] [LinearOrder G] [Fintype G] [CommRing R]
variable {a : ℕ} {N : Network E A B}

/-- Pointwise vanishing of the real packet tensor on the sentry bit. -/
theorem actualPacket_zero_of_sentry (P : PhysicalPacking N a G) (i : Fin a)
    {t : ℤ} (ht : t ≠ 0) (hv : padicValInt 2 t = i.val) (p : ℕ)
    (hnil : (2 : R)^p = 0) (β : Mode i p P.mask →₀ ℕ) (g : G)
    (v : PhysicalState P i g) (e : E) (hg : rowGroup P.mask i (P.seat e) = g)
    (hbit : v.1 ⟨e, hg⟩ = true)
    (hunmatch : ∀ q : E, (P.seat q).1 = (P.seat e).1 →
        ((P.seat q).2.val : ℤ) - ((P.seat e).2.val : ℤ) ≠ t) :
    actualPacket P i ht hv p hnil 0 β g (P.seat e).1 v = 0 := by
  classical
  have hb : e ∈ actualRows (childBlock P i) g (P.seat e).1 := by
    simp [actualRows, childBlock, rowBlock, hg]
  have hc : ∀ m : Mode i p P.mask, scaledRow P.mask i ht hv p hnil 0 (P.seat e) m = 0 := by
    intro m
    simp [scaledRow, crossNorm_zero]
  have hr : J6RecursiveModes.row
      (groupBit (fun e => P.seat e) (fun e => P.seat e) P.mask i g v e)
      (groupBase (fun e => P.seat e) (fun e => P.seat e) P.mask i t p hnil 0 g v e)
      (fun m => scaledRow P.mask i ht hv p hnil 0 (P.seat e) m) = 0 := by
    subst g
    simp [groupBit, groupBase, hbit, localValue_zero_of_unmatched _ _ _ _ _ _ _ _ hunmatch,
      J6RecursiveModes.row, LiteralPortCompiler.affine, hc]
  unfold actualPacket J6RecursiveModes.packet
  rw [Finset.prod_eq_zero hb hr, MvPolynomial.coeff_zero, zero_mul]

variable [Fintype A] [Fintype B] {f : ℤ[X]} {ell : ℕ}

/-- Vanishing of the actual source child contraction at the actual precision;
the old retained tensor product must enforce the indicated sentry bit. -/
theorem actualChild_zero_of_sentry (P : PhysicalPacking N a G) (i : Fin a)
    {t : ℤ} (ht : t ≠ 0) (hv : padicValInt 2 t = i.val) (p : ℕ)
    (hnil : (2 : Residue f ell p)^p = 0) (oldFile : EntryFile f ell N) (hf : f.Monic)
    (β : Mode i p P.mask →₀ ℕ) (g : G) (e : E)
    (hg : rowGroup P.mask i (P.seat e) = g)
    (hold : ∀ v : PhysicalState P i g,
      v.1 ⟨e,hg⟩ = false → oldState P i g p oldFile hf v = 0)
    (hunmatch : ∀ q : E, (P.seat q).1 = (P.seat e).1 →
        ((P.seat q).2.val : ℤ) - ((P.seat e).2.val : ℤ) ≠ t) :
    let F := actualPacket P i ht hv p hnil 0 β g
    reduce p f ell (trueContraction (child N (atGroup P i) (atPacket P) g)
      (compileChild N (atGroup P i) (atPacket P) g oldFile p (compiledPacket P i g p F)) hf) = 0 := by
  dsimp only
  rw [actual_physical_child]
  apply Finset.sum_eq_zero
  intro v _
  cases h : v.1 ⟨e,hg⟩
  · rw [hold v h, zero_mul]
  · rw [Finset.prod_eq_zero (Finset.mem_univ (P.seat e).1)
      (actualPacket_zero_of_sentry P i ht hv p hnil β g v e hg h hunmatch), mul_zero]

#print axioms actualPacket_zero_of_sentry
#print axioms actualChild_zero_of_sentry

end Paper5.OuterCenters

