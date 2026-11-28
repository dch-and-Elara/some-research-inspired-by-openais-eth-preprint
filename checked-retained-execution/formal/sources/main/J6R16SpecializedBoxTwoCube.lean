import J6R15SpecializedBoxNativeLegs
import J6R15SpecializedBoxAllocation

/-! Equality after projecting the actual fixed weighted slot. The
proof is on the original two separate physical Boolean cubes and uses
only entrywise identities, never a supplied aggregate equality. -/
namespace J6R14SpecializedBox
open scoped Polynomial BigOperators Classical
open Polynomial P11FullPacking J6R9Recursive J6R10Repack J6R11Integral
open J6R9PacketScopes J6R9PacketChild J6R9PacketCoeff J6R10RowIdentity
open J6R10RowLocal J6R10RowAffine J9R15FrozenErasurePhysical
open LiteralPortCompiler
noncomputable section
set_option linter.unusedSectionVars false
section Cube
variable {E K : Type*} [Fintype E] [CommRing K]

def twoCubeMark (TR TC : (E→Bool)→K) (u k : (E→Bool)→E→K) (feat : (E→Bool)→K) : K :=
  ∑ Y : E→Bool, ∑ X : E→Bool, (TR Y * TC X) *
    ∑ e : E, ((LiteralPortCompiler.slope (Y e)*k X e)*feat X) *
      ∏ j ∈ (Finset.univ : Finset E).erase e, affine (Y j) (u X j)
end Cube

variable {E A B G : Type*} [Fintype E] [Fintype A] [Fintype B] [LinearOrder G] [Fintype G]
variable {a : ℕ} {N : Network E A B} {f : ℤ[X]} {ell : ℕ}
variable (P : PhysicalPacking N a G) (i : Fin a) {t : ℤ} (ht : t≠0) (hv : padicValInt 2 t=i.val)
variable (p : ℕ) (z : Box f ell p) (file : EntryFile f ell N) (hf : f.Monic)
local notation "σ" => (fun e : E => P.seat e)
local notation "D" => Box f ell p
local notation "h2" => (J6R10Integral.box_two_nil p f ell)



set_option maxHeartbeats 1900000 in
theorem actual_singleton_two_cube
    (m : Mode i p P.mask)
    (TR TC : (E→Bool)→D) (u k : (E→Bool)→E→D) (feat : (E→Bool)→D)
    (hrow : ∀ Y, reduce p f ell (rowProduct N file hf Y) = TR Y)
    (hcol : ∀ X, reduce p f ell (colProduct N file hf X) = TC X)
    (hU : ∀ X, ∀ e, localValue σ P.mask i t p h2 z (σ e) (fun q => X q.val) = u X e)
    (hK : ∀ X, ∀ e, scaledRow P.mask i ht hv p h2 z (σ e) m = k X e)
    (hF : ∀ X, moment σ P.mask i m (fun q => X q.val) = feat X) :
    actualProjection P i ht hv p z file hf (Finsupp.single m 1) = twoCubeMark TR TC u k feat := by
  rw [← exact_literal_projection,literalSlot,twoCubeMark]
  refine Finset.sum_congr (Finset.ext (fun _ => by simp only [Finset.mem_univ])) ?_
  intro Y _
  refine Finset.sum_congr (Finset.ext (fun _ => by simp only [Finset.mem_univ])) ?_
  intro X _
  rw [hrow Y,hcol X,allocation_exact_one]
  apply congrArg (fun v : D => (TR Y*TC X)*v)
  refine Finset.sum_congr rfl ?_
  intro e _
  rw [physicalLeg_some,hK X,hF X]
  apply congrArg (fun v : D => ((LiteralPortCompiler.slope (Y e)*k X e)*feat X)*v)
  refine Finset.prod_congr rfl ?_
  intro q _
  rw [physicalLeg_none,hU X]

#print axioms actual_singleton_two_cube
end
end J6R14SpecializedBox