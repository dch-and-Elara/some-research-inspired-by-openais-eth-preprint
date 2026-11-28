import V8PooledMenuSlots
import V8PooledMenuBinary
import V8PooledMenuDigits

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3400000

namespace V8PooledMenu
open scoped BigOperators Polynomial Classical
open Polynomial DenominatorBudget P11FullPacking J6R10Repack J6R9Recursive
open J6R9PacketScopes J6R9PacketChild J6R9PacketTiles J6R10PacketAssembly J6R10RowAffine
noncomputable section

variable {E A B G : Type} [Fintype E] [Fintype A] [Fintype B]
  [LinearOrder G] [Fintype G] {a : ℕ} {N : Network E A B} {f : ℤ[X]}

/-- Finite sums use only actual columns in the same group and packet. -/
def localScaled (P : PhysicalPacking N a G) (i : Fin a) (t : ℤ)
    (w : Physical a P.copies G)
    (X : ColBits (fun e => P.seat e) P.mask i (rowGroup P.mask i w)) : TwoLocal[X] :=
  ∑ q : {q : E // colGroup P.mask i (P.seat q)=rowGroup P.mask i w},
    if (P.seat q.val).1=w.1 then
      normalizedW a t (((P.seat q.val).2.val:ℤ)-(w.2.val:ℤ))*C (bit TwoLocal (X q))
    else 0

omit [Fintype A] [Fintype B] in
theorem localScaled_eval {S : Type*} [CommRing S]
    (P : PhysicalPacking N a G) (i : Fin a) (t : ℤ)
    (w : Physical a P.copies G)
    (X : ColBits (fun e => P.seat e) P.mask i (rowGroup P.mask i w))
    (p : ℕ) (h₂ : (2:Residue f 1 p)^p=0) (z : Residue f 1 p)
    (ψ : Residue f 1 p →+* S) :
    (localScaled P i t w X).eval₂ (ψ.comp (J6ZeroTransport.reduceAt p h₂)) (2*ψ z) =
      ψ (localValue (fun e => P.seat e) P.mask i t p h₂ z w X) := by
  let e := eval₂RingHom (ψ.comp (J6ZeroTransport.reduceAt p h₂)) (2*ψ z)
  change e (localScaled P i t w X) = _
  rw [localScaled,map_sum,localValue,map_sum]
  refine Finset.sum_congr (Finset.ext (fun _ => by simp only [Finset.mem_univ])) (fun q _ => ?_)
  by_cases h : (P.seat q.val).1=w.1
  · simp only [if_pos h, map_mul, e, coe_eval₂RingHom, eval₂_C, normalized_eval]
    rw [Polynomial.hom_eval₂]
    cases X q <;> simp [bit]
  · simp only [if_neg h,map_zero]

def baseScaled (P : PhysicalPacking N a G) (i : Fin a) (t : ℤ) (g : G)
    (v : PhysicalState P i g) (r : E) : TwoLocal[X] :=
  if h : rowGroup P.mask i (P.seat r)=g then
    localScaled P i t (P.seat r) (fun q => v.2 ⟨q.val,q.property.trans h⟩)
  else 0

omit [Fintype A] [Fintype B] in
theorem baseScaled_eval {S : Type*} [CommRing S]
    (P : PhysicalPacking N a G) (i : Fin a) (t : ℤ) (g : G) (v : PhysicalState P i g) (r : E)
    (p : ℕ) (h₂ : (2:Residue f 1 p)^p=0) (z : Residue f 1 p)
    (ψ : Residue f 1 p →+* S) :
    (baseScaled P i t g v r).eval₂ (ψ.comp (J6ZeroTransport.reduceAt p h₂)) (2*ψ z) =
      ψ (groupBase (fun e => P.seat e) (fun e => P.seat e) P.mask i t p h₂ z g v r) := by
  unfold baseScaled groupBase
  split
  · apply localScaled_eval
  · simp

def affineScaled (P : PhysicalPacking N a G) (i : Fin a) (t : ℤ) (g : G)
    (v : PhysicalState P i g) (r : E) : TwoLocal[X] :=
  LiteralPortCompiler.affine
    (groupBit (fun e => P.seat e) (fun e => P.seat e) P.mask i g v r)
    (baseScaled P i t g v r)

omit [Fintype A] [Fintype B] in
theorem affineScaled_eval {S : Type*} [CommRing S]
    (P : PhysicalPacking N a G) (i : Fin a) (t : ℤ) (g : G) (v : PhysicalState P i g) (r : E)
    (p : ℕ) (h₂ : (2:Residue f 1 p)^p=0) (z : Residue f 1 p)
    (ψ : Residue f 1 p →+* S) :
    (affineScaled P i t g v r).eval₂ (ψ.comp (J6ZeroTransport.reduceAt p h₂)) (2*ψ z) =
      LiteralPortCompiler.affine
        (groupBit (fun e => P.seat e) (fun e => P.seat e) P.mask i g v r)
        (ψ (groupBase (fun e => P.seat e) (fun e => P.seat e) P.mask i t p h₂ z g v r)) := by
  exact (affine_map (eval₂RingHom (ψ.comp (J6ZeroTransport.reduceAt p h₂)) (2*ψ z)) _ _).trans
    (congrArg (LiteralPortCompiler.affine _) (baseScaled_eval P i t g v r p h₂ z ψ))

/-- Whole-root polynomial in the indeterminate standing for 2z.
The original retained flags are binary table reads on actual incidences;
no scalar polynomial is accepted from the caller. -/
def wholeScaled (P : PhysicalPacking N a G) (i : Fin a) (t : ℤ)
    (flags : ∀ v : A ⊕ B, (ParentPorts N v → Bool) → Bool) : TwoLocal[X] :=
  ∏ g : G, ∑ v : PhysicalState P i g, C (oldScalar P i g flags v) *
    ∏ k, ∏ r ∈ actualRows (childBlock P i) g k, affineScaled P i t g v r

theorem wholeScaled_eval {S : Type*} [CommRing S]
    (P : PhysicalPacking N a G) (i : Fin a) (t : ℤ)
    (flags : ∀ v : A ⊕ B, (ParentPorts N v → Bool) → Bool)
    (p₀ : ℕ) (hp₀ : 0<p₀) (hf : f.Monic) (hd : 0<f.natDegree)
    (p : ℕ) (h₂ : (2:Residue f 1 p)^p=0) (z : Residue f 1 p)
    (ψ : Residue f 1 p →+* S) :
    (wholeScaled P i t flags).eval₂ (ψ.comp (J6ZeroTransport.reduceAt p h₂)) (2*ψ z) =
      zeroValue P i t p h₂ z (binaryFile f p₀ flags) hf ψ := by
  let e := eval₂RingHom (ψ.comp (J6ZeroTransport.reduceAt p h₂)) (2*ψ z)
  change e (wholeScaled P i t flags) = _
  simp only [wholeScaled,map_prod,map_sum,map_mul,zeroValue]
  refine Finset.prod_congr rfl fun g _ => ?_
  refine Finset.sum_congr rfl fun v _ => ?_
  have he : e (C (oldScalar P i g flags v)) =
      ψ (oldState P i g p (binaryFile f p₀ flags) hf v) := by
    simp only [e, coe_eval₂RingHom, eval₂_C, RingHom.comp_apply]
    exact congrArg ψ (oldScalar_map P i g p₀ p hp₀ hf hd flags v (J6ZeroTransport.reduceAt p h₂))
  rw [he]
  apply congrArg (ψ (oldState P i g p (binaryFile f p₀ flags) hf v)*·)
  refine Finset.prod_congr rfl fun k _ => ?_
  exact Finset.prod_congr rfl (fun r _ => affineScaled_eval P i t g v r p h₂ z ψ)

theorem receive_actual_slot {S : Type*} [CommRing S]
    (P : PhysicalPacking N a G) (i : Fin a) {t : ℤ}
    (ht : t≠0) (hv : padicValInt 2 t=i.val)
    (flags : ∀ v : A ⊕ B, (ParentPorts N v → Bool) → Bool)
    (p₀ : ℕ) (hp₀ : 0<p₀) (hf : f.Monic) (hd : 0<f.natDegree)
    (p : ℕ) (h₂ : (2:Residue f 1 p)^p=0) (z : Residue f 1 p)
    (β : Mode i p P.mask →₀ ℕ) (ψ : Residue f 1 p →+* S)
    {q : ℕ} (hq : q ≤ a+1-i.val) (hzero : (2:S)^q=0) :
    ψ (slot P i ht hv p h₂ z (binaryFile f p₀ flags) hf β) =
      if β=0 then TruncatedProbeMenu.reconstruct (digits q (wholeScaled P i t flags)) (ψ z) else 0 := by
  by_cases hb : β=0
  · subst β
    rw [if_pos rfl,projected_zero_slot,receive_digits hzero (ψ.comp (J6ZeroTransport.reduceAt p h₂))]
    exact (wholeScaled_eval P i t flags p₀ hp₀ hf hd p h₂ z ψ).symm
  · rw [if_neg hb]
    exact projected_nonzero_slot P i ht hv p h₂ z _ hf β hb ψ hq hzero

#print axioms localScaled_eval
#print axioms baseScaled_eval
#print axioms affineScaled_eval
#print axioms wholeScaled_eval
#print axioms receive_actual_slot

end
end V8PooledMenu
