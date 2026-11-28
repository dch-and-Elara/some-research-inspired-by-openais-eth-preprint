import J6R16SpecializedBoxTwoCube
import J6R15SpecializedBoxCompilerSum

/-! Compare the exact, compiled J6 child tensor product with J9's original
literal one-mark compiler, using only pointwise entry identities.
No assumption identifies their aggregate contraction or coefficient. -/
namespace J6R14SpecializedBox
open scoped Polynomial BigOperators Classical
open Polynomial P11FullPacking J6R9Recursive J6R10Repack J6R11Integral
open J6R9PacketScopes J6R9PacketChild J6R9PacketCoeff J6R10RowIdentity
open J6R10RowLocal J6R10RowAffine J8Physical J9R15FrozenErasurePhysical
open LiteralPortCompiler
noncomputable section
set_option linter.unusedSectionVars false
local instance (priority := 10000) specializedFinDecEq (n : ℕ) : DecidableEq (Fin n) :=
  fun j k => Classical.propDecidable (j=k)

variable {R A B G K : Type*} [Fintype R] [Fintype A] [Fintype B] [LinearOrder G] [Fintype G]
variable [CommRing K] {a : ℕ} {N : Network (Wire R) A B} {f : ℤ[X]} {ell : ℕ}
variable (P : PhysicalPacking N a G) (i : Fin a) {t : ℤ} (ht : t≠0) (hv : padicValInt 2 t=i.val)
variable (p : ℕ) (z : Box f ell p) (file : EntryFile f ell N) (hf : f.Monic)
local notation "σ" => (fun e : Wire R => P.seat e)
local notation "D" => Box f ell p
local notation "h2" => (J6R10Integral.box_two_nil p f ell)

set_option maxHeartbeats 700000 in
theorem compiled_two_cube_on_chart {M : ℕ} (idx : Wire R ≃ Fin M)
    (φ : K→+*D) (s : D) (F : CNF (Fin M))
    (u k : (Fin M→Bool)→Wire R→K) (feat : (Fin M→Bool)→K) :
    twoCubeMark (fun Y => (truth (J9LayoutTransfer.allRows (R:=R)) Y : D))
      (fun X => truth F (X ∘ idx.symm)) (fun X e => φ (u (X ∘ idx.symm) e))
      (fun X e => s*φ (k (X ∘ idx.symm) e)) (fun X => φ (feat (X ∘ idx.symm))) =
      s * φ (MvPolynomial.coeff J9LayoutTransfer.β
        (completed (J9R13Compiler.system F) (J9R13Compiler.base u feat)
          (J9R13Compiler.kernel (fun x e (_ : Unit) => k x e)))) := by
  refine Eq.trans ?_ (evaluated_compiler_sum φ s F u k feat).symm
  unfold twoCubeMark
  rw [Finset.sum_comm]
  let e := idx.arrowCongr (Equiv.refl Bool)
  refine Finset.sum_equiv e (fun _ => by simp only [Finset.mem_univ]) ?_
  intro X _
  refine Finset.sum_congr (Finset.ext (fun _ => by simp only [Finset.mem_univ])) ?_
  intro Y _
  refine congrArg (fun v : D => ((truth (J9LayoutTransfer.allRows (R:=R)) Y : D) *
    truth F (X ∘ idx.symm)) * v) ?_
  refine Finset.sum_congr rfl ?_
  intro r _
  have eX : e X = X ∘ idx.symm := rfl
  rw [eX]
  refine congrArg (fun v : D => (LiteralPortCompiler.slope (Y r) *
    (s*φ (k (X ∘ idx.symm) r)) * φ (feat (X ∘ idx.symm))) * v) ?_
  refine Finset.prod_congr (Finset.ext (fun _ => by
    simp only [Finset.mem_erase,Finset.mem_univ,and_true])) ?_
  intro q _
  rfl

set_option maxHeartbeats 3000000 in
theorem fixed_product_of_pointwise_entries {M : ℕ} (idx : Wire R ≃ Fin M)
    (m : Mode i p P.mask) (φ : K→+*D) (s : D)
    (F : CNF (Fin M)) (u k : (Fin M→Bool)→Wire R→K) (feat : (Fin M→Bool)→K)
    (hrow : ∀ Y : Wire R→Bool, reduce p f ell (rowProduct N file hf Y) =
      (truth (J9LayoutTransfer.allRows (R:=R)) Y : D))
    (hcol : ∀ X : Wire R→Bool, reduce p f ell (colProduct N file hf X) =
      (truth F (X ∘ idx.symm) : D))
    (hU : ∀ X : Wire R→Bool, ∀ e, localValue σ P.mask i t p h2 z (σ e) (fun q => X q.val)
      = φ (u (X ∘ idx.symm) e))
    (hK : ∀ X : Wire R→Bool, ∀ e, scaledRow P.mask i ht hv p h2 z (σ e) m
      = s * φ (k (X ∘ idx.symm) e))
    (hF : ∀ X : Wire R→Bool, moment σ P.mask i m (fun q => X q.val)
      = φ (feat (X ∘ idx.symm))) :
    actualProjection P i ht hv p z file hf (Finsupp.single m 1) =
      s * φ (MvPolynomial.coeff J9LayoutTransfer.β
        (completed (J9R13Compiler.system F) (J9R13Compiler.base u feat)
          (J9R13Compiler.kernel (fun x e (_ : Unit) => k x e)))) := by
  calc
    _ = twoCubeMark (fun Y => (truth (J9LayoutTransfer.allRows (R:=R)) Y : D))
      (fun X => truth F (X ∘ idx.symm)) (fun X e => φ (u (X ∘ idx.symm) e))
      (fun X e => s*φ (k (X ∘ idx.symm) e)) (fun X => φ (feat (X ∘ idx.symm))) :=
        actual_singleton_two_cube P i ht hv p z file hf m _ _ _ _ _ hrow hcol hU hK hF
    _ = _ := compiled_two_cube_on_chart p idx φ s F u k feat

#print axioms compiled_two_cube_on_chart
#print axioms fixed_product_of_pointwise_entries
end
end J6R14SpecializedBox