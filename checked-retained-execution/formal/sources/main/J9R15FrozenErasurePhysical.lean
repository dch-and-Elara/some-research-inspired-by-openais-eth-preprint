import J9R15FrozenErasureProjection
import J9R14LowPrecisionNative

/-! Exact projection to the product of the literal frozen rounded-recursion
children. All child files and their creation tags are inherited unchanged. -/
namespace J9R15FrozenErasurePhysical
open scoped Polynomial Classical BigOperators
open Polynomial P11FullPacking J6R9Recursive J6R10Repack J6R11Integral
open J6R9PacketChild J6R9PacketScopes
open J6ActiveAllocation J6R10RowAffine J6R10RowIdentity J6R10RowPrinted J6R11RowFormula
open J9R14LowPrecisionNative J9R15FrozenErasureProjection J6R10Integral

noncomputable section
set_option maxHeartbeats 2200000
set_option linter.unusedSectionVars false

variable {E A B G : Type*} [Fintype E] [Fintype A] [Fintype B] [LinearOrder G] [Fintype G]
variable {a : ℕ} {N : Network E A B} {f : ℤ[X]} {ell : ℕ}
variable (P : PhysicalPacking N a G) (i : Fin a) {t : ℤ}
variable (ht : t≠0) (hv : padicValInt 2 t=i.val) (p : ℕ) (z : Box f ell p)
variable (file : EntryFile f ell N) (hf : f.Monic)
local notation "ρ" => (fun e : E => P.seat e)
local notation "W" => Mode i p P.mask
local notation "K" => Box f ell p
local notation "hnil" => box_two_nil p f ell

def literalSlot (β : W →₀ ℕ) : K :=
  ∑ Y : E → Bool, ∑ X : E → Bool,
    (reduce p f ell (rowProduct N file hf Y) * reduce p f ell (colProduct N file hf X)) *
      ∑ α : E → Option W, if allocationExponent α=β then
        ∏ e : E, actualLeg ρ ρ P.mask i ht hv p hnil z Y X e (α e) else 0

def actualProjection (β : W →₀ ℕ) : K :=
  ∏ g : G, reduce p f ell (actualChildTruth P i ht hv p z file hf β g)

theorem reindex_global (β : W →₀ ℕ) :
    literalSlot P i ht hv p z file hf β =
      groupedProjection (weight i p P.mask) (block ρ P.mask i) (sourceGP P.mask i)
        (fun r v => row ρ ρ P.mask i ht hv p hnil z r v)
        (fun g v => oldState P i g p file hf v) (fun m v => moment ρ P.mask i m v.2) β := by
  classical
  unfold literalSlot groupedProjection
  let F (x : (E → Bool) × (E → Bool)) : K :=
    (reduce p f ell (rowProduct N file hf x.1) * reduce p f ell (colProduct N file hf x.2)) *
      ∑ α : E → Option W, if allocationExponent α=β then
        ∏ e : E, actualLeg ρ ρ P.mask i ht hv p hnil z x.1 x.2 e (α e) else 0
  change (∑ Y : E → Bool, ∑ X : E → Bool, F (Y,X)) = _
  rw [← Fintype.sum_prod_type F]
  let S (x : ∀ g, State ρ ρ P.mask i g) : K :=
    (∏ g, oldState P i g p file hf (x g)) *
      ∑ α : E → Option W, if allocationExponent α=β then
        ∏ r : E, scaled (weight i p P.mask)
          (J6SourceMoment.insert (fun r => row ρ ρ P.mask i ht hv p hnil z r (x (rowGroup P.mask i (ρ r))))
            (fun m => moment ρ P.mask i m (x (source P.mask i m)).2)) r (α r) else 0
  let fty := fun g => (inferInstance : Fintype (State ρ ρ P.mask i g))
  have hft : @Pi.instFintype G (State ρ ρ P.mask i)
      (fun x y => Classical.propDecidable (x=y)) _ fty =
      @Pi.instFintype G (State ρ ρ P.mask i)
        (fun x y => LinearOrder.toDecidableEq x y) _ fty :=
    Subsingleton.elim _ _
  rw [hft]
  change (∑ x, F x) = ∑ x, S x
  refine Fintype.sum_equiv (pairedGroups (Equiv.refl E) (rowGroupAt P i) (colGroupAt P i)) F S ?_
  intro x
  dsimp only [F,S]
  rw [← oldState_factors P i p file hf x.1 x.2]
  exact congrArg (fun u : K => (reduce p f ell (rowProduct N file hf x.1) *
    reduce p f ell (colProduct N file hf x.2))*u) rfl

theorem exact_literal_projection (β : W →₀ ℕ) :
    literalSlot P i ht hv p z file hf β = actualProjection P i ht hv p z file hf β := by
  classical
  let v := weight i p P.mask
  let bl := block ρ P.mask i
  let T := targetGP (p:=p) P.mask i
  let U := sourceGP (p:=p) P.mask i
  let Q (r : E) (x : State ρ ρ P.mask i (bl r).1) (m : Option W) :=
    row ρ ρ P.mask i ht hv p hnil z r x m
  let L (m : W) (x : State ρ ρ P.mask i (U m).1) : K := moment ρ P.mask i m x.2
  have hz (r : E) (m : W) (x : State ρ ρ P.mask i (bl r).1)
      (h : bl r≠T m) : Q r x (some m)=0 := by
    exact row_off_target ρ ρ P.mask i ht hv p hnil z r m x (fun e => h (congrArg Prod.swap e))
  have h0 (g : G) (y : State ρ ρ P.mask i g) (r : E) (e : (bl r).1=g) :
      scaled v (fun _ m => Q r (e.symm ▸ y) m) r none =
        LiteralPortCompiler.affine (groupBit ρ ρ P.mask i g y r)
          (groupBase ρ ρ P.mask i t p hnil z g y r) := by
    change rowGroup P.mask i (ρ r)=g at e
    subst g
    change scaled v (fun _ m => Q r y m) r none = _
    simp [Q,scaled,cost,row,groupBit,groupBase]
  have hm (g : G) (y : State ρ ρ P.mask i g) (r : E) (e : (bl r).1=g) (m : W) :
      scaled v (fun _ o => Q r (e.symm ▸ y) o) r (some m) =
        LiteralPortCompiler.slope (groupBit ρ ρ P.mask i g y r) * scaledRow P.mask i ht hv p hnil z (ρ r) m := by
    change rowGroup P.mask i (ρ r)=g at e
    subst g
    change scaled v (fun _ o => Q r y o) r (some m) = _
    change (2:K)^(m.order.val+1)*(LiteralPortCompiler.slope (y.1 ⟨r,rfl⟩) *
      crossNorm P.mask i ht hv p hnil z (ρ r) m) = _
    rw [groupBit,dif_pos rfl,scaledRow]
    exact mul_left_comm _ _ _
  let old := fun g (x : State ρ ρ P.mask i g) => oldState P i g p file hf x
  have proj := exact_projection v bl T U Q old L (groupBit ρ ρ P.mask i)
    (groupBase ρ ρ P.mask i t p hnil z)
    (fun _ _ r m => scaledRow P.mask i ht hv p hnil z (ρ r) m) hz h0 hm β
  calc
    _ = _ := reindex_global P i ht hv p z file hf β
    _ = _ := proj
    _ = _ := by
      unfold actualProjection
      refine Finset.prod_congr rfl (fun g _ => ?_)
      rw [← reconstructedChild_formula,actualChildTruth]
      exact (printed_child_realized P i ht hv p hnil z file hf β g).symm

#print axioms reindex_global
#print axioms exact_literal_projection

end
end J9R15FrozenErasurePhysical
