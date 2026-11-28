import V8NativeMessageN7PublicShift

/-! Exact signed whole contraction at the zero probe. In contrast to
the parity formula, the surviving base is multiplied by the original
signed grid derivative ratio, and unmatched columns are still summed. -/
namespace V8NativeMessage.N7LiteralSupport
open scoped Classical BigOperators Polynomial
open Polynomial DenominatorBudget P11FullPacking J6R10Repack J6R9Recursive
open J6R9PacketChild J6R9PacketScopes J6R9PacketCoeff J6R10RowAffine J6R9PacketTiles J6R10PacketAssembly
open V8NativeMessage.N7
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 7000000
set_option maxRecDepth 1900
noncomputable section

variable {E A B G : Type} [Fintype E] [Fintype A] [Fintype B]
  [LinearOrder G] [Fintype G] {a : ℕ} {N : Network E A B}
variable (P : PhysicalPacking N a G) (i : Fin a)

omit [Fintype A] [Fintype B] in
theorem actual_local_at_zero (t : ℤ) (w : Physical a P.copies G)
    (X : ColBits (fun e=>P.seat e) P.mask i (rowGroup P.mask i w)) :
    (V8PooledMenu.localScaled P i t w X).eval 0 = rho a t * shiftBit P i t w X := by
  let ev : TwoLocal[X]→+*TwoLocal := Polynomial.evalRingHom 0
  change ev (V8PooledMenu.localScaled P i t w X)=_
  rw [V8PooledMenu.localScaled,map_sum,shiftBit,Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _=>?_
  by_cases pg : (P.seat q.val).1=w.1
  · have nh (k : ℤ) : ev (V8PooledMenu.normalizedW a t k) =
          if k=t then rho a t else 0 := by
      have h := normalized_at_zero (RingHom.id TwoLocal) a t k
      simpa only [Polynomial.eval₂_id,RingHom.id_apply] using h
    simp only [if_pos pg,map_mul,nh,ev,coe_evalRingHom,eval_C]
    by_cases shift : ((P.seat q.val).2.val:ℤ)-(w.2.val:ℤ)=t <;> simp [shift,pg]
  · simp [pg,ev]

omit [Fintype A] [Fintype B] in
theorem actual_base_at_zero (t : ℤ) (g : G) (v : PhysicalState P i g) (r : E) :
    (V8PooledMenu.baseScaled P i t g v r).eval 0 = rho a t * shiftBase P i t g v r := by
  unfold V8PooledMenu.baseScaled shiftBase
  split
  · exact actual_local_at_zero P i t _ _
  · simp

def oldFlagsValue (R : Type*) [CommRing R] (g : G)
    (flags : ∀ v : A⊕B,(ParentPorts N v→Bool)→Bool) (x : PhysicalState P i g) : R :=
  ∏ u : Old (atGroup P i) g,
    bit R (flags u.val (restrictOriginal N (atGroup P i) g u ((stateEquiv P i g).symm x)))

def signedRoot {R : Type} [CommRing R] (t : ℤ) (kappa : R)
    (flags : ∀ v : A⊕B,(ParentPorts N v→Bool)→Bool) : R :=
  ∏ g : G,∑ v : PhysicalState P i g,oldFlagsValue P i R g flags v *
    ∏ k,∏ r∈actualRows (childBlock P i) g k,
      LiteralPortCompiler.affine
        (groupBit (fun e=>P.seat e) (fun e=>P.seat e) P.mask i g v r)
        (kappa * shiftBase P i t g v r)

theorem full_signed_root_is_zero_polynomial (t : ℤ)
    (flags : ∀ v : A⊕B,(ParentPorts N v→Bool)→Bool) :
    (V8PooledMenu.wholeScaled P i t flags).eval 0 = signedRoot P i t (rho a t) flags := by
  let ev : TwoLocal[X]→+*TwoLocal := Polynomial.evalRingHom 0
  change ev (V8PooledMenu.wholeScaled P i t flags)=_
  rw [V8PooledMenu.wholeScaled,signedRoot,map_prod]
  refine Finset.prod_congr rfl fun g _=>?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun v _=>?_
  rw [map_mul,map_prod]
  have eq : ev (C (V8PooledMenu.oldScalar P i g flags v))=
      oldFlagsValue P i TwoLocal g flags v := by
    simp only [ev,coe_evalRingHom,eval_C,V8PooledMenu.oldScalar,oldFlagsValue,bit]
  rw [eq]
  congr 1
  refine Finset.prod_congr rfl fun k _=>?_
  rw [map_prod]
  refine Finset.prod_congr rfl fun r _=>?_
  rw [V8PooledMenu.affineScaled,V8PooledMenu.affine_map]
  exact congrArg (LiteralPortCompiler.affine _) (actual_base_at_zero P i t g v r)

variable {R S : Type} [CommRing R] [CommRing S]

omit [Fintype A] [Fintype B] in
theorem map_shift_base (h : R→+*S) (t : ℤ) (g : G) (v : PhysicalState P i g) (r : E) :
    h (shiftBase P i t g v r)=shiftBase P i t g v r := by
  unfold shiftBase
  split
  · unfold shiftBit
    rw [map_sum]
    refine Finset.sum_congr rfl fun q _=>?_
    split
    · cases v.2 ⟨q.val,q.property.trans ‹_›⟩ <;> simp [J6R9PacketTiles.bit]
    · exact map_zero h
  · exact map_zero h

theorem map_signed_root (h : R→+*S) (kappa : R) (t : ℤ)
    (flags : ∀ v : A⊕B,(ParentPorts N v→Bool)→Bool) :
    h (signedRoot P i t kappa flags)=signedRoot P i t (h kappa) flags := by
  unfold signedRoot
  simp only [map_prod,map_sum,map_mul]
  refine Finset.prod_congr rfl fun g _=>Finset.sum_congr rfl fun v _=>?_
  refine congrArg₂ (·*·) ?_ ?_
  · simp only [oldFlagsValue,map_prod]
    refine Finset.prod_congr rfl fun u _=>?_
    cases flags u.val (restrictOriginal N (atGroup P i) g u ((stateEquiv P i g).symm v)) <;>
      simp [J6R9PacketTiles.bit]
  · refine Finset.prod_congr rfl fun k _=>Finset.prod_congr rfl fun r _=>?_
    rw [V8PooledMenu.affine_map,map_mul,map_shift_base]

end
end V8NativeMessage.N7LiteralSupport
#print axioms V8NativeMessage.N7LiteralSupport.actual_local_at_zero
#print axioms V8NativeMessage.N7LiteralSupport.actual_base_at_zero
#print axioms V8NativeMessage.N7LiteralSupport.full_signed_root_is_zero_polynomial
#print axioms V8NativeMessage.N7LiteralSupport.map_shift_base
#print axioms V8NativeMessage.N7LiteralSupport.map_signed_root
