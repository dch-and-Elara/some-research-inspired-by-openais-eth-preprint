import J6R35RootOriginsChart
import J6R35RootOriginsTransport
import J6R34RootAtlasGeometry
import J6R21AncestorOriginReads

/-! Identify both real exterior branches with the actual stable-CNF
records. The right branch's equivalence is pure dependent transport
across the proved physical chart equality, including its copy index.
The executable atlas was generated and charged in round 34. -/
namespace J6R35RootOrigins
open scoped Polynomial Classical
open Polynomial J6Mesh J6OrientedHost P11FullPacking J6R24LegalLayout
open J6R10Repack J6R11Blueprint J6R12Blueprint J6R21Ancestor J6R21Leaf J6R11Repack J6R12Repack J6R27PrescribedProbe
open J6ActiveRun J6ActiveSchedule J1PPrinted J6R26StablePreparedRoot
open J6R14ZeroMode J6R32RootGeneratedRegistryInputs J6R34RootAtlas J6R31RootResidentTables
set_option autoImplicit false
set_option maxHeartbeats 25000000
set_option maxRecDepth 2700

variable {V : Type} [Fintype V]
variable {f : ℤ[X]} {m n base native : ℕ} {T : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) T
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q r c d edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q r c d edgew tc tj key prec tw bw)

abbrev CanonicalPage (m : ℕ) := Page (a m) (K m) (Fin 64)
abbrev SourceVertex (T : Plant V m n) :=
  PlantNode (b:=K m) (l:=printedHalf m) T (J6R28GeneratedRootFrame.constantRootWord m)

noncomputable def canonicalPageEquiv (G : RootShape f m (printedHalf m) base native
    (printedRankWidth m) T (J6R28GeneratedRootFrame.constantRootWord m))
    (ell : ℕ) (i : J6Recovery.Addr m) :
    CanonicalPage m ≃ exteriorPages (G.selector ell) (G.ready ell) :=
  packPageCongr (mesh_root_bits m native G.nativeFits).symm (rootChart T) _
    (odd_site_matches_geometry G ell i).1

noncomputable def stableOriginal (v : SourceVertex T) : Point f ell :=
  actualOriginalPoint (created:=base) T (J6R28GeneratedRootFrame.constantRootWord m) v

noncomputable def stableBorn (k : CanonicalPage m) : Point f ell := by
  let P := physicalRootCall f ell base m (printedHalf m) n T (J6R28GeneratedRootFrame.constantRootWord m)
  letI := P.host.finiteEdge
  letI := P.host.finiteRow
  letI := P.host.finiteCol
  exact generatedPoint (rootChart T) (oddAxis m)
    (J6RecursiveCrossing.odd_center_valuation m X.centre).1
    (J6RecursiveCrossing.odd_center_valuation m X.centre).2.1
    (prescribedNode (rootPreset G ell) (J6SourcePrecision.printed m base) ell X.sample)
    P.host.file 0 X.group k

theorem stable_exterior_exact_born (k : CanonicalPage m) :
    exteriorPagePoint (G.selector ell) (G.ready ell) (G.centre ell X.centre)
      (rootPreset G ell) X.sample X.group (canonicalPageEquiv G ell X.centre k) =
    stableBorn X k := by
  rw [exterior_page_is_real]
  let P := physicalRootCall f ell base m (printedHalf m) n T (J6R28GeneratedRootFrame.constantRootWord m)
  letI := P.host.finiteEdge
  letI := P.host.finiteRow
  letI := P.host.finiteCol
  have H := odd_site_matches_geometry G ell X.centre
  have node (p q : ℕ) (ep : p=q) :
      cast (congrArg (Residue f ell) ep)
        (prescribedNode (rootPreset G ell) p ell X.sample) =
      prescribedNode (rootPreset G ell) q ell X.sample := by
    subst q
    rfl
  exact transport_zero_page (mesh_root_bits m native G.nativeFits).symm H.2.2.2
    (rootChart T) _ H.1 _ (oddAxis m) H.2.1 H.2.2.1
    (centerNonzero (G.centre ell X.centre)) (J6RecursiveCrossing.odd_center_valuation m X.centre).1
    rfl (J6RecursiveCrossing.odd_center_valuation m X.centre).2.1
    _ _ (node _ _ H.2.2.2) P.host.file X.group k

theorem true_seed_payload_page (pad : ℕ) (k : CanonicalPage m) :
    (locate (widened pad (residentPageKey m k)).result
      (X.seed pad).immutable.payload.payload.pages).result=some (X.chosenFields k) := by
  have original := (Classical.choose_spec (stable_exterior_atlas X)).2.1 k
  have transfer := widened_lookup_same pad (rootTable X.chosenFields) (residentPageKey m k)
  rw [widened_rows_exact] at transfer
  exact transfer.trans original

theorem stable_exterior_vertex_origin
    (v : (exteriorChild G ell X.centre X.sample X.group).host.Row⊕
         (exteriorChild G ell X.centre X.sample X.group).host.Col) :
    (∃ u : SourceVertex T,Nonempty (Trace (stableOriginal (f:=f) (ell:=ell) (base:=base) u)
      (point (exteriorChild G ell X.centre X.sample X.group).host v))) ∨
    (∃ k : CanonicalPage m,Nonempty (Trace (stableBorn X k)
      (point (exteriorChild G ell X.centre X.sample X.group).host v))) := by
  rcases real_exterior_vertex_origin (G.selector ell) (G.ready ell) (G.centre ell X.centre)
      (rootPreset G ell) X.sample X.group v with h|h
  · exact Or.inl h
  · obtain ⟨k,tr⟩ := h
    let E := canonicalPageEquiv G ell X.centre
    let k0 := E.symm k
    have ec : E k0=k := E.apply_symm_apply k
    have H := stable_exterior_exact_born X k0
    change exteriorPagePoint (G.selector ell) (G.ready ell) (G.centre ell X.centre)
      (rootPreset G ell) X.sample X.group (E k0)=stableBorn X k0 at H
    rw [ec] at H
    exact Or.inr ⟨k0,H ▸ tr⟩

end J6R35RootOrigins
#print axioms J6R35RootOrigins.canonicalPageEquiv
#print axioms J6R35RootOrigins.stable_exterior_exact_born
#print axioms J6R35RootOrigins.true_seed_payload_page
#print axioms J6R35RootOrigins.stable_exterior_vertex_origin
