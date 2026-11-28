import J9R15FrozenErasurePhysical

/-! The weighted R12 leg is exactly the product of the literal marked
slope, the scaled physical crossing, and its source tile moment. Unmarked
legs are the old affine form evaluated on the same column half-port. -/
namespace J6R14SpecializedBox
open scoped Polynomial Classical BigOperators
open P11FullPacking J6R9PacketScopes J6R9PacketChild J6R9PacketCoeff J6R10RowLocal
open J6R10RowIdentity J6R10RowAffine J6ActiveAllocation J9R14LowPrecisionNative
noncomputable section
set_option linter.unusedSectionVars false
variable {E G K : Type*} [LinearOrder G] [Fintype E] [CommRing K] {a b : ℕ}
variable (σ : E→Physical a b G) (mask : MaskFamily a b G) (i : Fin a)
variable {t : ℤ} (ht : t≠0) (hv : padicValInt 2 t=i.val)
variable (p : ℕ) (hnil : (2:K)^p=0) (z : K) (Y X : E→Bool) (e : E)

theorem physicalLeg_none :
    actualLeg σ σ mask i ht hv p hnil z Y X e none =
      LiteralPortCompiler.affine (Y e)
        (localValue σ mask i t p hnil z (σ e) (fun q => X q.val)) := by
  simp [actualLeg,J6SourceMoment.insert,scaled,cost,row]

theorem physicalLeg_some (m : Mode i p mask) :
    actualLeg σ σ mask i ht hv p hnil z Y X e (some m) =
      (LiteralPortCompiler.slope (Y e)*scaledRow mask i ht hv p hnil z (σ e) m) *
        moment σ mask i m (fun q => X q.val) := by
  simp only [actualLeg,J6SourceMoment.insert,scaled,cost,row,J6R10RowAffine.weight,
    Option.elim'_some,scaledRow]
  ring

#print axioms physicalLeg_none
#print axioms physicalLeg_some
end
end J6R14SpecializedBox