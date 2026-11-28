import V8NativeMessageN7LiteralSupportGeometry
import J6BlockFactor

/-! The original grouped states are exactly the full independent pair
of row and column Boolean cubes, regrouped along the actual layout.
This result does not set unmatched column bits to zero. -/
namespace V8NativeMessage.N7LiteralSupport
open scoped BigOperators Classical Polynomial
open Polynomial P11FullPacking J6R10Repack J6R9Recursive
open J6R9PacketChild J6R9PacketScopes J6R10RowAffine J6R9PacketTiles
open V8NativeMessage.N7
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5500000
set_option maxRecDepth 1600
noncomputable section

variable {E A B G : Type} [Fintype E] [LinearOrder G] [Fintype G]
variable {a : ℕ} {N : Network E A B} (P : PhysicalPacking N a G) (i : Fin a)

def groupCube : (Port E→Bool) ≃ (∀ g : G,PhysicalState P i g) where
  toFun w g := stateEquiv P i g (fun q=>w q.val)
  invFun s q := (stateEquiv P i (retainedGroup N (atGroup P i) q)).symm
    (s (retainedGroup N (atGroup P i) q)) ⟨q,rfl⟩
  left_inv w := by
    funext q
    change (stateEquiv P i (retainedGroup N (atGroup P i) q)).symm
      (stateEquiv P i (retainedGroup N (atGroup P i) q) (fun z=>w z.val)) ⟨q,rfl⟩=w q
    rw [Equiv.symm_apply_apply]
  right_inv s := by
    funext g
    apply (stateEquiv P i g).symm.injective
    rw [show (stateEquiv P i g).symm
      (stateEquiv P i g (fun (q : ChildEdge N (atGroup P i) g)=>
        (stateEquiv P i (retainedGroup N (atGroup P i) q.val)).symm
          (s (retainedGroup N (atGroup P i) q.val)) ⟨q.val,rfl⟩))=_
      from Equiv.symm_apply_apply _ _]
    funext q
    rcases q with ⟨q,hq⟩
    subst g
    rfl

omit [Fintype E] in
theorem restricted_actual_bits (w : Port E→Bool) (g : G) (v : Old (atGroup P i) g) :
    restrictOriginal N (atGroup P i) g v ((stateEquiv P i g).symm (groupCube P i w g)) =
      fun q=>w q.val := by
  change restrictOriginal N (atGroup P i) g v
    ((stateEquiv P i g).symm (stateEquiv P i g (fun q=>w q.val)))=_
  rw [Equiv.symm_apply_apply]
  rfl

omit [Fintype E] in
theorem literal_group_bit (w : Port E→Bool) (g : G) (r : E)
    (h : rowGroup P.mask i (P.seat r)=g) :
    groupBit (fun e=>P.seat e) (fun e=>P.seat e) P.mask i g (groupCube P i w g) r=w (.inl r) := by
  rw [groupBit,dif_pos h]
  exact state_reads_row P i g (fun u=>w u.val) r h

def wholeShiftBit (R : Type) [CommRing R] (t : ℤ) (w : Port E→Bool) (r : E) : R :=
  ∑ q : E, if Matches P t r q then bit R (w (.inr q)) else 0

theorem literal_group_shift {R : Type} [CommRing R]
    {t : ℤ} (ht : t≠0) (hv : padicValInt 2 t=i.val)
    (w : Port E→Bool) (g : G) (r : E)
    (h : rowGroup P.mask i (P.seat r)=g) :
    shiftBase P i t g (groupCube P i w g) r =
      wholeShiftBit P R t w r := by
  rw [shiftBase,dif_pos h]
  unfold shiftBit wholeShiftBit
  let filt : Finset E := Finset.univ.filter (fun q=>colGroup P.mask i (P.seat q)=rowGroup P.mask i (P.seat r))
  let body (q : E) := if Matches P t r q then bit R (w (.inr q)) else 0
  have localEqual : (∑ q : {q : E//colGroup P.mask i (P.seat q)=rowGroup P.mask i (P.seat r)},body q.val)=
      ∑ q∈filt,body q := (Finset.sum_subtype filt (by simp [filt]) body).symm
  calc
    _ = _ := by
      refine Finset.sum_congr rfl fun q _=>?_
      have read := state_reads_col P i g (fun u=>w u.val) q.val (q.property.trans h)
      by_cases hM : Matches P t r q.val
      · have H : (P.seat q.val).1=(P.seat r).1 ∧
            ((P.seat q.val).2.val:ℤ)-(P.seat r).2.val=t := hM
        rw [if_pos H]
        unfold body
        rw [if_pos hM]
        exact congrArg (bit R) read
      · have H : ¬ ((P.seat q.val).1=(P.seat r).1 ∧
            ((P.seat q.val).2.val:ℤ)-(P.seat r).2.val=t) := hM
        rw [if_neg H]
        unfold body
        rw [if_neg hM]
    _ = _ := localEqual
    _ = _ := by
      refine Finset.sum_subset (Finset.filter_subset _ _) ?_
      intro q _ outside
      have hm : ¬ Matches P t r q := by
        intro yes
        exact outside (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (actual_match_is_group_local P i ht hv yes).symm⟩)
      simp [body,hm]

theorem literal_port_bit_unique {R : Type} [CommRing R]
    (t : ℤ) (w : Port E→Bool) (r q : E) (h : Matches P t r q) :
    wholeShiftBit P R t w r = bit R (w (.inr q)) := by
  rw [wholeShiftBit,Finset.sum_eq_single q]
  · simp [h]
  · intro j _ away
    have hne : ¬ Matches P t r j := fun e=>away (match_unique_col P e h)
    simp [hne]
  · simp

theorem literal_unmatched_port_zero {R : Type} [CommRing R]
    (t : ℤ) (w : Port E→Bool) (r : E) (h : ∀ q,¬ Matches P t r q) :
    wholeShiftBit P R t w r = 0 :=
  Finset.sum_eq_zero (fun q _=>if_neg (h q))

end
end V8NativeMessage.N7LiteralSupport
#print axioms V8NativeMessage.N7LiteralSupport.groupCube
#print axioms V8NativeMessage.N7LiteralSupport.restricted_actual_bits
#print axioms V8NativeMessage.N7LiteralSupport.literal_group_bit
#print axioms V8NativeMessage.N7LiteralSupport.literal_group_shift
#print axioms V8NativeMessage.N7LiteralSupport.literal_port_bit_unique
#print axioms V8NativeMessage.N7LiteralSupport.literal_unmatched_port_zero
