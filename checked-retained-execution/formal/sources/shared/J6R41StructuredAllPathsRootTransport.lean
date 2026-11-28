import J6R41StructuredAllPathsChart
import J6R37StructuredRootPath

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 14000000
set_option maxRecDepth 3000

/-! The printed root's change of axis is an equality of the same
physical chart, not an equivalence picked by cardinality. In
particular it leaves the original half-wire identifier unchanged. -/
namespace J6R41StructuredAllPaths
open scoped Polynomial Classical
open Polynomial P11FullPacking J6R9PacketScopes J6R21Ancestor J6R10Repack J6R11Blueprint
open J6Mesh J6OrientedHost J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe
open J6R31RootResidentTables J6R32RootGeneratedRegistryInputs J6R34RootAtlas J6R35RootOrigins
open J6R11Repack J6R12Repack J6R12Blueprint J6R25PreparedSupply J6ActiveSchedule J6ActiveRun J6R14ZeroMode

theorem move_cast_literal {f : ℤ[X]} {ell : ℕ} {source a b : Point f ell}
    (e : a=b) (tr : Trace source b) (seed : PortAt source→List Bool) (x : PortAt a) :
    (e.symm ▸ tr : Trace source a).literal seed x=tr.literal seed (castPort e x) := by
  subst b
  rfl

section Transport
variable {E A B G : Type} [Fintype E] [Fintype A] [Fintype B] [LinearOrder G] [Fintype G]
variable {N : Network E A B} {a₀ a₁ : ℕ}

theorem packed_zero_cast_keeps_half {f : ℤ[X]} {ell p q : ℕ}
    (size : a₀=a₁) (prec : p=q) (P : PhysicalPacking N a₀ G)
    (P' : PhysicalPacking N a₁ G) (shape : P'=packAxis P size)
    (i : Fin a₁) (j : Fin a₀) (axis : i.val=j.val)
    {t u : ℤ} (time : t=u) (ht : t≠0) (hu : u≠0)
    (vi : padicValInt 2 t=i.val) (vj : padicValInt 2 u=j.val)
    (z : Residue f ell p) (z' : Residue f ell q) (value : cast (congrArg (Residue f ell) prec) z=z')
    (file : EntryFile f ell N) (group : G) (page : Page a₀ P.copies G)
    (eq : generatedPoint P' i ht vi z file 0 group (packPageCongr size P P' shape page)=
      generatedPoint P j hu vj z' file 0 group page)
    (x : PortAt (generatedPoint P' i ht vi z file 0 group (packPageCongr size P P' shape page))) :
    (edge (castPort eq x).val).val=(edge x.val).val := by
  subst a₁
  subst P'
  subst q
  subst u
  have axes : i=j := Fin.ext axis
  subst j
  have same : z=z' := value
  subst z'
  rfl

end Transport

variable {V : Type} [Fintype V]
variable {f : ℤ[X]} {m n base native : ℕ} {T : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) T
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q ro co d edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q ro co d edgew tc tj key prec tw bw)

theorem canonical_exterior_cast_keeps_wire (k : CanonicalPage m)
    (x : PortAt (exteriorPagePoint (G.selector ell) (G.ready ell) (G.centre ell X.centre)
      (rootPreset G ell) X.sample X.group (canonicalPageEquiv G ell X.centre k))) :
    (edge (castPort (stable_exterior_exact_born X k) x).val).val=(edge x.val).val := by
  let P := physicalRootCall f ell base m (printedHalf m) n T (J6R28GeneratedRootFrame.constantRootWord m)
  letI := P.host.finiteEdge
  letI := P.host.finiteRow
  letI := P.host.finiteCol
  have H := odd_site_matches_geometry G ell X.centre
  have node (p q : ℕ) (ep : p=q) :
      cast (congrArg (Residue f ell) ep) (prescribedNode (rootPreset G ell) p ell X.sample)=
        prescribedNode (rootPreset G ell) q ell X.sample := by
    subst q
    rfl
  exact packed_zero_cast_keeps_half (mesh_root_bits m native G.nativeFits).symm H.2.2.2
    (rootChart T) _ H.1 _ (oddAxis m) H.2.1 H.2.2.1
    (centerNonzero (G.centre ell X.centre)) (J6RecursiveCrossing.odd_center_valuation m X.centre).1
    rfl (J6RecursiveCrossing.odd_center_valuation m X.centre).2.1
    _ _ (node _ _ H.2.2.2) P.host.file X.group k (stable_exterior_exact_born X k) x

#print axioms move_cast_literal
#print axioms packed_zero_cast_keeps_half
#print axioms canonical_exterior_cast_keeps_wire
end J6R41StructuredAllPaths