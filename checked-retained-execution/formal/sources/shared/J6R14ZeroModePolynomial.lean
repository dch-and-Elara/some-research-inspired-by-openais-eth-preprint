import J6R14ZeroModeAlgebra
import J6R11IntegralStep
import J6R10IntegralFinite
import J6BlockFactor

/-! The common polynomial is built from the real same-packet, same-group
entries, frozen old tensors, and one affine factor per original row wire. -/
namespace J6R14ZeroMode
open scoped Classical Polynomial BigOperators
open Polynomial P11FullPacking P1DyadicGrid J6R9Recursive J6R9PacketScopes
open J6R10Repack J6R10Integral J6R11Integral J6R9PacketChild J6R9PacketLocal
open J6R10PacketAssembly J6R10RowAffine
noncomputable section

variable {E A B G : Type*} [Fintype E] [Fintype A] [Fintype B] [LinearOrder G] [Fintype G]
variable {a : ℕ} {N : Network E A B} {f : ℤ[X]} {ell : ℕ}

def localPoly (P : PhysicalPacking N a G) (i : Fin a) (t : ℤ) (p : ℕ)
    (w : Physical a P.copies G) (X : ColBits (fun e => P.seat e) P.mask i (rowGroup P.mask i w)) :
    (Box f ell p)[X] :=
  ∑ q : {q : E // colGroup P.mask i (P.seat q) = rowGroup P.mask i w},
    if (P.seat q.val).1 = w.1 then
      ((W a t (((P.seat q.val).2.val:ℤ)-(w.2.val:ℤ))).map
        (J6ZeroTransport.reduceAt p (box_two_nil p f ell))) * C (J6R9PacketTiles.bit (Box f ell p) (X q))
    else 0

omit [Fintype A] [Fintype B] in
theorem localPoly_eval (P : PhysicalPacking N a G) (i : Fin a) (t : ℤ) (p : ℕ)
    (w : Physical a P.copies G) (X : ColBits (fun e => P.seat e) P.mask i (rowGroup P.mask i w))
    (z : Box f ell p) :
    (localPoly P i t p w X).eval z = localValue (fun e => P.seat e) P.mask i t p
      (box_two_nil p f ell) z w X := by
  change (evalRingHom z) (localPoly P i t p w X) = _
  rw [localPoly,map_sum,localValue]
  refine Finset.sum_congr (Finset.ext (fun _ => by simp only [Finset.mem_univ])) (fun q _ => ?_)
  by_cases h : (P.seat q.val).1=w.1
  · simp only [if_pos h,map_mul,coe_evalRingHom,Polynomial.eval_map,eval_C]
  · simp only [if_neg h,map_zero]

omit [Fintype A] [Fintype B] in
theorem localPoly_degree (P : PhysicalPacking N a G) (i : Fin a) (t : ℤ) (p : ℕ)
    (ht : t ∈ grid a) (w : Physical a P.copies G)
    (X : ColBits (fun e => P.seat e) P.mask i (rowGroup P.mask i w)) :
    (localPoly (f:=f) (ell:=ell) P i t p w X).natDegree ≤ 2*2^a-1 := by
  unfold localPoly
  apply natDegree_sum_le_of_forall_le
  intro q _
  by_cases h : (P.seat q.val).1=w.1
  · rw [if_pos h]
    exact natDegree_mul_le.trans (by
      rw [natDegree_C,add_zero]
      exact natDegree_map_le.trans
        (W_degree a t _ ht (J6R9PacketRealTile.difference_mem_grid w.2 (P.seat q.val).2)))
  · simp [h]

def basePoly (P : PhysicalPacking N a G) (i : Fin a) (t : ℤ) (p : ℕ) (g : G)
    (v : PhysicalState P i g) (r : E) : (Box f ell p)[X] :=
  if e : rowGroup P.mask i (P.seat r)=g then
    localPoly P i t p (P.seat r) (fun q => v.2 ⟨q.val,q.property.trans e⟩)
  else 0

omit [Fintype A] [Fintype B] in
theorem basePoly_eval (P : PhysicalPacking N a G) (i : Fin a) (t : ℤ) (p : ℕ)
    (g : G) (v : PhysicalState P i g) (r : E) (z : Box f ell p) :
    (basePoly P i t p g v r).eval z =
      groupBase (fun e => P.seat e) (fun e => P.seat e) P.mask i t p
        (box_two_nil p f ell) z g v r := by
  unfold basePoly groupBase
  split
  · exact localPoly_eval _ _ _ _ _ _ _
  · simp

omit [Fintype A] [Fintype B] in
theorem basePoly_degree (P : PhysicalPacking N a G) (i : Fin a) (t : ℤ) (p : ℕ)
    (ht : t ∈ grid a) (g : G) (v : PhysicalState P i g) (r : E) :
    (basePoly (f:=f) (ell:=ell) P i t p g v r).natDegree ≤ 2*2^a-1 := by
  unfold basePoly
  split
  · exact localPoly_degree _ _ _ _ ht _ _
  · simp

def affinePoly (P : PhysicalPacking N a G) (i : Fin a) (t : ℤ) (p : ℕ)
    (g : G) (v : PhysicalState P i g) (r : E) : (Box f ell p)[X] :=
  LiteralPortCompiler.affine (groupBit (fun e => P.seat e) (fun e => P.seat e) P.mask i g v r)
    (basePoly P i t p g v r)

omit [Fintype A] [Fintype B] in
theorem affinePoly_eval (P : PhysicalPacking N a G) (i : Fin a) (t : ℤ) (p : ℕ)
    (g : G) (v : PhysicalState P i g) (r : E) (z : Box f ell p) :
    (affinePoly P i t p g v r).eval z =
      LiteralPortCompiler.affine
        (groupBit (fun e => P.seat e) (fun e => P.seat e) P.mask i g v r)
        (groupBase (fun e => P.seat e) (fun e => P.seat e) P.mask i t p
          (box_two_nil p f ell) z g v r) := by
  cases h : groupBit (fun e => P.seat e) (fun e => P.seat e) P.mask i g v r <;>
    simp [affinePoly,LiteralPortCompiler.affine,h,basePoly_eval]

omit [Fintype A] [Fintype B] in
theorem affinePoly_degree (P : PhysicalPacking N a G) (i : Fin a) (t : ℤ) (p : ℕ)
    (ht : t ∈ grid a) (g : G) (v : PhysicalState P i g) (r : E) :
    (affinePoly (f:=f) (ell:=ell) P i t p g v r).natDegree ≤ 2*2^a-1 := by
  have h := basePoly_degree (f:=f) (ell:=ell) P i t p ht g v r
  unfold affinePoly LiteralPortCompiler.affine
  split
  · exact h
  · exact (natDegree_sub_le _ _).trans (max_le (by simp) h)

def packetPoly (P : PhysicalPacking N a G) (i : Fin a) (t : ℤ) (p : ℕ)
    (g : G) (k : Page a P.copies G) (v : PhysicalState P i g) : (Box f ell p)[X] :=
  ∏ r ∈ actualRows (childBlock P i) g k, affinePoly P i t p g v r

def childPoly (P : PhysicalPacking N a G) (i : Fin a) (t : ℤ) (p : ℕ)
    (file : EntryFile f ell N) (hf : f.Monic) (g : G) : (Box f ell p)[X] :=
  ∑ v : PhysicalState P i g, C (oldState P i g p file hf v) * ∏ k, packetPoly P i t p g k v

def polynomial (P : PhysicalPacking N a G) (i : Fin a) (t : ℤ) (p : ℕ)
    (file : EntryFile f ell N) (hf : f.Monic) : (Box f ell p)[X] :=
  ∏ g : G, childPoly P i t p file hf g

omit [Fintype A] [Fintype B] in
theorem packetPoly_eval (P : PhysicalPacking N a G) (i : Fin a) {t : ℤ}
    (ht : t ≠ 0) (hv : padicValInt 2 t=i.val) (p : ℕ)
    (g : G) (k : Page a P.copies G) (v : PhysicalState P i g) (z : Box f ell p) :
    (packetPoly P i t p g k v).eval z =
      actualPacket P i ht hv p (box_two_nil p f ell) z 0 g k v := by
  rw [actualPacket,packet_constant]
  change (evalRingHom z) (packetPoly P i t p g k v) = _
  rw [packetPoly,map_prod]
  exact Finset.prod_congr rfl (fun r _ => affinePoly_eval P i t p g v r z)

theorem childPoly_eval (P : PhysicalPacking N a G) (i : Fin a) {t : ℤ}
    (ht : t ≠ 0) (hv : padicValInt 2 t=i.val) (p : ℕ)
    (file : EntryFile f ell N) (hf : f.Monic) (g : G) (z : Box f ell p) :
    (childPoly P i t p file hf g).eval z =
      reduce p f ell (actualChildTruth P i ht hv p z file hf 0 g) := by
  change (evalRingHom z) (childPoly P i t p file hf g) = _
  rw [actualChildTruth,actual_physical_child,childPoly,map_sum]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [map_mul,map_prod]
  have hC : (evalRingHom z) (C (oldState P i g p file hf v)) =
      oldState P i g p file hf v := eval_C
  rw [hC]
  rw [show (∏ k, (evalRingHom z) (packetPoly P i t p g k v)) =
    ∏ k, actualPacket P i ht hv p (box_two_nil p f ell) z 0 g k v from
      Finset.prod_congr rfl (fun k _ => packetPoly_eval P i ht hv p g k v z)]

theorem polynomial_eval (P : PhysicalPacking N a G) (i : Fin a) {t : ℤ}
    (ht : t ≠ 0) (hv : padicValInt 2 t=i.val) (p : ℕ)
    (file : EntryFile f ell N) (hf : f.Monic) (z : Box f ell p) :
    (polynomial P i t p file hf).eval z =
      ∏ g : G, reduce p f ell (actualChildTruth P i ht hv p z file hf 0 g) := by
  change (evalRingHom z) (polynomial P i t p file hf) = _
  rw [polynomial,map_prod]
  exact Finset.prod_congr rfl (fun g _ => childPoly_eval P i ht hv p file hf g z)

#print axioms localPoly_eval
#print axioms localPoly_degree
#print axioms affinePoly_eval
#print axioms affinePoly_degree
#print axioms packetPoly_eval
#print axioms childPoly_eval
#print axioms polynomial_eval
end
end J6R14ZeroMode
