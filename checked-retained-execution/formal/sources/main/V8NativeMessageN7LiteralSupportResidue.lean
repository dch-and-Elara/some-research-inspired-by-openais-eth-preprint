import V8NativeMessageN7LiteralSupportFlat
import J6NativeHeightResidue

/-! Use the actual raw root flags and the same uniquely matched source
bit in the already verified two-cube clearing model. Both orientations
instantiate this exact identity, without substituting a different host. -/
namespace V8NativeMessage.N7LiteralSupport
open scoped Classical Polynomial BigOperators
open Polynomial P11FullPacking J6R10Repack J6R9PacketTiles
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 8000000
set_option maxRecDepth 2100
noncomputable section

variable {E A B G R : Type} [Fintype E] [Fintype A] [Fintype B]
  [LinearOrder G] [Fintype G] [CommRing R]
variable {a : ℕ} {N : Network E A B} (P : PhysicalPacking N a G)

def readTrueShift (t : ℤ) (r : E) (y : E→Bool) : Bool :=
  if h : ∃ q,Matches P t r q then y (Classical.choose h) else false

omit [Fintype A] [Fintype B] in
theorem shifted_bits_are_exact_boolean (t : ℤ) (x y : E→Bool) (r : E) :
    wholeShiftBit P R t (Sum.elim x y) r=bit R (readTrueShift P t r y) := by
  unfold readTrueShift
  split
  · rename_i h
    exact literal_port_bit_unique P t (Sum.elim x y) r (Classical.choose h) (Classical.choose_spec h)
  · rename_i h
    rw [literal_unmatched_port_zero P t (Sum.elim x y) r (fun q m=>h ⟨q,m⟩)]
    rfl

def rowKeep (N : Network E A B)
    (flags : ∀ v : A⊕B,(ParentPorts N v→Bool)→Bool) (x : E→Bool) : Bool :=
  decide (∀ v : A,flags (.inl v) (fun u=>x (edge u.val))=true)

def colKeep (N : Network E A B)
    (flags : ∀ v : A⊕B,(ParentPorts N v→Bool)→Bool) (y : E→Bool) : Bool :=
  decide (∀ v : B,flags (.inr v) (fun u=>y (edge u.val))=true)

private theorem finite_binary_product {I : Type} [Fintype I] (f : I→Bool) :
    (∏ u,bit R (f u))=bit R (decide (∀ u,f u=true)) := by
  by_cases yes : ∀ u,f u=true
  · rw [decide_eq_true yes]
    exact Finset.prod_eq_one (fun u _=>by rw [yes u]; rfl)
  · rw [decide_eq_false yes]
    obtain ⟨w,hw⟩ := not_forall.mp yes
    apply Finset.prod_eq_zero (Finset.mem_univ w)
    cases e : f w
    · rfl
    · exact (hw e).elim

omit [Fintype E] [Fintype A] [Fintype B] in
private theorem on_row_bits (v : A) (x y : E→Bool) :
    (fun p : ParentPorts N (.inl v)=>Sum.elim x y p.val)=(fun p=>x (edge p.val)) := by
  funext p
  rcases p with ⟨p,h⟩
  cases p with
  | inl e => rfl
  | inr e => cases h

omit [Fintype E] [Fintype A] [Fintype B] in
private theorem on_col_bits (v : B) (x y : E→Bool) :
    (fun p : ParentPorts N (.inr v)=>Sum.elim x y p.val)=(fun p=>y (edge p.val)) := by
  funext p
  rcases p with ⟨p,h⟩
  cases p with
  | inl e => cases h
  | inr e => rfl

omit [Fintype E] in
theorem actual_flags_on_full_side_words
    (flags : ∀ v : A⊕B,(ParentPorts N v→Bool)→Bool) (x y : E→Bool) :
    (∏ v,bit R (flags v (fun p=>Sum.elim x y p.val)))=
      bit R (rowKeep N flags x && colKeep N flags y) := by
  rw [Fintype.prod_sum_type]
  simp only [on_row_bits,on_col_bits,finite_binary_product]
  change bit R (rowKeep N flags x)*bit R (colKeep N flags y)=_
  cases h : rowKeep N flags x <;> cases j : colKeep N flags y <;> simp [bit]

theorem literal_signed_cube_is_residue_slot (i : Fin a) {t : ℤ}
    (ht : t≠0) (hv : padicValInt 2 t=i.val) (κ : R)
    (flags : ∀ v : A⊕B,(ParentPorts N v→Bool)→Bool) :
    signedRoot P i t κ flags =
      J6NativeHeightResidue.residueSlot (rowKeep N flags) (colKeep N flags) (readTrueShift P t) κ := by
  rw [full_root_at_zero_has_literal_two_cubes P i ht hv,literal_cubes_sum_columns_first]
  conv_rhs => rw [J6NativeHeightResidue.residueSlot,Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _=>Finset.sum_congr rfl fun x _=>?_
  rw [flatTerm,actual_flags_on_full_side_words]
  cases gate : rowKeep N flags x && colKeep N flags y
  · simp [bit]
  · simp only [if_true,bit,one_mul]
    refine Finset.prod_congr rfl fun r _=>?_
    rw [shifted_bits_are_exact_boolean]
    cases h : x r <;> cases j : readTrueShift P t r y <;>
      simp [bit,h,J6NativeHeightResidue.ringEntry,LiteralPortCompiler.affine]

end
end V8NativeMessage.N7LiteralSupport
#print axioms V8NativeMessage.N7LiteralSupport.shifted_bits_are_exact_boolean
#print axioms V8NativeMessage.N7LiteralSupport.actual_flags_on_full_side_words
#print axioms V8NativeMessage.N7LiteralSupport.literal_signed_cube_is_residue_slot
