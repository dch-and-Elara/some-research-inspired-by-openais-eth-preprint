import V8NativeMessageN7LiteralSupportCube
import V8NativeMessageN7LiteralSupportFactor

/-! Recombine the actual zero-probe group contractions into the original
global row and column cubes, retaining both old-side orientations.
This is a value identity, not a charge for materialising either cube. -/
namespace V8NativeMessage.N7LiteralSupport
open scoped BigOperators Classical Polynomial
open Polynomial P11FullPacking J6R10Repack J6R9Recursive
open J6R9PacketChild J6R9PacketScopes J6R10RowAffine J6R9PacketTiles J6R10PacketAssembly
open V8NativeMessage.N7
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6300000
set_option maxRecDepth 1900
noncomputable section

variable {E A B G R : Type} [Fintype E] [Fintype A] [Fintype B] [LinearOrder G] [Fintype G]
variable {a : ℕ} {N : Network E A B} [CommRing R] (P : PhysicalPacking N a G) (i : Fin a)

def flatTerm (t : ℤ) (kappa : R)
    (flags : ∀ v : A⊕B,(ParentPorts N v→Bool)→Bool) (w : Port E→Bool) : R :=
  (∏ v,bit R (flags v (fun p=>w p.val))) *
    (∏ r : E,LiteralPortCompiler.affine (w (.inl r)) (kappa*wholeShiftBit P R t w r))

def flatSigned (t : ℤ) (kappa : R)
    (flags : ∀ v : A⊕B,(ParentPorts N v→Bool)→Bool) : R :=
  ∑ w : Port E→Bool,flatTerm P t kappa flags w

omit [Fintype A] [Fintype B] in
theorem actual_row_partition (f : E→R) :
    (∏ g : G,∏ k : Page a P.copies G,∏ r∈actualRows (childBlock P i) g k,f r)=
    ∏ r,f r := by
  let Gf (p : G×Page a P.copies G) := ∏ r∈actualRows (childBlock P i) p.1 p.2,f r
  calc
    _ = ∏ p : G×Page a P.copies G,Gf p := (Fintype.prod_prod_type Gf).symm
    _ = _ := Finset.prod_fiberwise (Finset.univ : Finset E) (childBlock P i) f

theorem full_root_at_zero_has_literal_two_cubes
    {t : ℤ} (ht : t≠0) (hv : padicValInt 2 t=i.val) (kappa : R)
    (flags : ∀ v : A⊕B,(ParentPorts N v→Bool)→Bool) :
    signedRoot P i t kappa flags=flatSigned P t kappa flags := by
  unfold signedRoot flatSigned
  rw [Fintype.prod_sum]
  symm
  refine Fintype.sum_equiv (groupCube P i) _ _ fun w=>?_
  rw [Finset.prod_mul_distrib]
  unfold flatTerm
  refine congrArg₂ (·*·) ?_ ?_
  · rw [J6BlockFactor.prod_rows (atGroup P i)]
    refine Finset.prod_congr rfl fun g _=>?_
    unfold oldFlagsValue
    refine Finset.prod_congr (Finset.ext fun _=>by simp only [Finset.mem_univ]) fun u _=>?_
    rw [restricted_actual_bits P i w g u]
  · rw [←actual_row_partition P i]
    refine Finset.prod_congr rfl fun g _=>Finset.prod_congr rfl fun k _=>?_
    refine Finset.prod_congr rfl fun r inRows=>?_
    have grp : rowGroup P.mask i (P.seat r)=g :=
      congrArg Prod.fst (Finset.mem_filter.mp inRows).2
    rw [literal_group_bit P i w g r grp,literal_group_shift P i ht hv w g r grp]

theorem literal_cubes_sum_columns_first (t : ℤ) (kappa : R)
    (flags : ∀ v : A⊕B,(ParentPorts N v→Bool)→Bool) :
    flatSigned P t kappa flags =
      ∑ y : E→Bool,∑ x : E→Bool, flatTerm P t kappa flags (Sum.elim x y) := by
  unfold flatSigned
  let e := Equiv.sumArrowEquivProdArrow E E Bool
  have H := Fintype.sum_equiv e (flatTerm P t kappa flags)
    (fun a : (E→Bool)×(E→Bool)=>flatTerm P t kappa flags (Sum.elim a.1 a.2))
    (fun w=>congrArg (flatTerm P t kappa flags) (by
      funext q
      cases q <;> rfl))
  rw [H,Fintype.sum_prod_type,Finset.sum_comm]

end
end V8NativeMessage.N7LiteralSupport
#print axioms V8NativeMessage.N7LiteralSupport.actual_row_partition
#print axioms V8NativeMessage.N7LiteralSupport.full_root_at_zero_has_literal_two_cubes
#print axioms V8NativeMessage.N7LiteralSupport.literal_cubes_sum_columns_first
