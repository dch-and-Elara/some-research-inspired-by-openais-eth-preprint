
import S11ModeIdentity
import S11TupleCodec
import S11Literal
import S11Lift

noncomputable section
namespace S11
open Classical
open scoped BigOperators

variable {R : Type*} [CommSemiring R]
variable (A : AffinePacket (Fin 64) R)
variable [∀ g, Fintype (A.Bits g)] [∀ g, Fintype (A.Rows g)]
variable [∀ g, Fintype (A.TargetMode g)]

def nativeModeOrder {B : Type*} [Fintype B] (i p : ℕ) (e : A.Z ≃ Mode B i p) : List A.Z :=
  (modes B i p).map e.symm

/-- The child results in the contraction identity are evaluated by the
    same ordered weighted DFS as the root trace, with actual packet, tile,
    and exponent labels supplied by the mode equivalence. -/
theorem native_batch_value {B : Type*} [Fintype B] (t : ℤ) (j p : ℕ)
    (e : A.Z ≃ Mode B (level t) p)
    (hw : ∀ z : A.Z, A.weight z = (e z).2.2.val+1) (hp : (2 : R)^p = 0) :
    (runBatch (List.finRange 64)
      (fun s g => A.child (readExponent (nativeModeOrder A (level t) p e) s.exponents) g)
      (batch B t j p)).1 = A.sample := by
  let zs := nativeModeOrder A (level t) p e
  have hl : zs.map A.weight = modeWeights B (level t) p := by
    unfold zs nativeModeOrder modeWeights
    rw [List.map_map]
    apply List.map_inj_left.mpr
    intro m _
    simpa using hw (e.symm m)
  have hn : zs.Nodup := by
    unfold zs nativeModeOrder modes
    exact (Finset.nodup_toList _).map e.symm.injective
  have hall (z : A.Z) : z ∈ zs := List.mem_map.2 ⟨e z, by simp [modes], e.symm_apply_apply z⟩
  have hpw (z : A.Z) : 0 < A.weight z := by rw [hw]; omega
  rw [runBatch_value, batch, List.map_map, ← hl]
  change ((tuples (zs.map A.weight) p).map
    (fun β => ((List.finRange 64).map (A.child (readExponent zs β))).prod)).sum = _
  simp_rw [← Fin.prod_univ_def]
  rw [tuple_sum_eq zs hn hall A.weight hpw p (fun β => ∏ g, A.child β g)]
  have he : orderedFiber A.weight p = A.feasible p := by
    ext β
    simp [orderedFiber, AffinePacket.feasible, AffinePacket.budget]
  rw [he]
  exact (A.recursion_identity p hp hpw).symm

theorem native_mod_two_pow {O : Type*} [CommRing O] (p : ℕ) :
    (2 : ModTwoPow O p)^p = 0 := by
  have h : (2 : O)^p ∈ Ideal.span ({(2 : O)^p} : Set O) := Ideal.subset_span (by simp)
  rw [show (2 : ModTwoPow O p) = reduce O p 2 from (map_ofNat (reduce O p) 2).symm, ← map_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.2 h

/-- Composition with the actual streaming evaluator at a fixed probe.
    One may use a ring that varies with t and choose the affine packet
    data at the t being evaluated. -/
theorem sourceBatch_recursion {Rs : ℤ → Type*} [∀ t, CommSemiring (Rs t)]
    (B : ℤ → Type) [∀ t, Fintype (B t)] (M L a u p : ℕ)
    (child : (t : ℤ) → ℕ → List ℕ → Fin 64 → Rs t) (t : ℤ) (j : ℕ)
    (A : AffinePacket (Fin 64) (Rs t))
    [∀ g, Fintype (A.Bits g)] [∀ g, Fintype (A.Rows g)] [∀ g, Fintype (A.TargetMode g)]
    (e : A.Z ≃ Mode (B t) (level t) (precision p M a u L t))
    (hw : ∀ z : A.Z, A.weight z = (e z).2.2.val+1)
    (hp : (2 : Rs t)^(precision p M a u L t) = 0)
    (hchild : ∀ β g, child t j β g =
      A.child (readExponent (nativeModeOrder A (level t) (precision p M a u L t) e) β) g) :
    (sourceBatch B M L a u p child t j).1 = A.sample := by
  rw [sourceBatch_eq]
  have hfun : (fun (b : Slot) => child t j b.exponents) = fun b g =>
      A.child (readExponent (nativeModeOrder A (level t) (precision p M a u L t) e) b.exponents) g := by
    funext b g
    exact hchild b.exponents g
  rw [hfun]
  exact native_batch_value A t j _ e hw hp

#print axioms native_batch_value
#print axioms native_mod_two_pow
#print axioms sourceBatch_recursion

end S11

