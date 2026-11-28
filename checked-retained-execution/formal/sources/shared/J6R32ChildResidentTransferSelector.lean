import J6R12BlueprintSite

/-! Install one selected legal layout without identifying it with an old
choice. This proof-side selector is not itself a metered table lookup
or a runner which has paid for all other call layouts. -/
namespace J6R32ChildResidentTransfer
open scoped Classical Polynomial
open J6R10Repack J6R11Blueprint J6R12Blueprint J6ActiveRun
variable {f : ℤ[X]} {ell Δ : ℕ} {S : J6R12Blueprint.Params (f:=f) (ell:=ell)}

noncomputable def oneSiteSelector (base : Selector S Δ) (home : Call (PhysicalHost f ell))
    (chosen : PhysicalPacking home.host.network (S.levelBits home.depth) (Fin 64)) :
    Selector S Δ := fun c ready=>if h : c=home then h.symm ▸ chosen else base c ready

theorem one_site_exact (base : Selector S Δ) (home : Call (PhysicalHost f ell))
    (chosen : PhysicalPacking home.host.network (S.levelBits home.depth) (Fin 64)) (d : Ready S Δ home) :
    packing (oneSiteSelector base home chosen) d = chosen := by
  unfold packing oneSiteSelector
  rw [dif_pos rfl]

theorem other_site_unchanged (base : Selector S Δ) (home : Call (PhysicalHost f ell))
    (chosen : PhysicalPacking home.host.network (S.levelBits home.depth) (Fin 64))
    {c : Call (PhysicalHost f ell)} (d : Ready S Δ c) (ne : c≠home) :
    packing (oneSiteSelector base home chosen) d = packing base d := by
  unfold packing oneSiteSelector
  rw [dif_neg ne]

#print axioms one_site_exact
#print axioms other_site_unchanged
end J6R32ChildResidentTransfer