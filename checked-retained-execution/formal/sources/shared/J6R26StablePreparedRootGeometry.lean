
import J6R26StablePreparedRootSelector
import J6R14ZeroModePlanted

/-! Exact identification of the dependent native odd-centre polynomial
with the R24 stable root polynomial. The only transport is across
proved finite shape and receiving-precision equalities. -/
namespace J6R26StablePreparedRoot
open scoped Classical Polynomial
open Polynomial J6Mesh P11FullPacking J6OrientedHost J6R9Recursive
open J6R10Integral J6R10Repack J6R11Repack J6R11Blueprint J6R12Blueprint
open J6R12Repack J6R14ZeroMode J6R24LegalLayout J6ActiveRun J6ActiveSchedule J1PPrinted
set_option linter.unusedSectionVars false
set_option maxHeartbeats 9000000
set_option maxRecDepth 1800

theorem zero_polynomial_transport
    {E A B G : Type} [Fintype E] [Fintype A] [Fintype B] [Fintype G] [LinearOrder G]
    {f : ℤ[X]} {ell a₀ a₁ p q : ℕ} {N : Network E A B}
    (ea : a₀=a₁) (ep : p=q) (P : PhysicalPacking N a₀ G)
    (i : Fin a₁) (j : Fin a₀) (same : i.val=j.val) (t : ℤ)
    (file : EntryFile f ell N) (hf : f.Monic) :
    cast (congrArg (Box f ell) ep)
      ((polynomial (cast (congrArg (fun a=>PhysicalPacking N a G) ea) P) i t p file hf).eval 0)=
    (polynomial P j t q file hf).eval 0 := by
  subst a₁
  subst q
  have eq : i=j := Fin.ext same
  subst i
  rfl

variable {f : ℤ[X]} {ell : ℕ} {V : Type} [Fintype V]

theorem physical_zero_is_stable
    (b m l q native width : ℕ) (T : Plant V m q) (w : Fin (a m)→Fin 64)
    (hm : m≤K m) (hL : 2*l=L m) (hn : native≤m) (ha : a m≤width) (cap : K m*L m≤2^width)
    (d : Ready (rootParams f ell m native) (sourceDelta (physicalSize m native))
      (physicalRootCall f ell b m l q T w)) (hf : f.Monic)
    (j : J6Recovery.Addr m) :
    let sel := stableSelector (f:=f) (ell:=ell) b m l q native width T w hm hL hn ha cap
    let t := oddRootCenter f ell b m l q native T w hn j
    let pr := oddRootCenter_precision f ell b m l q native T w hn j
    cast (congrArg (Box f ell) pr) ((physicalZeroP sel d t hf).eval 0) =
      (polynomial (stableRootPacking m l q width T w hm hL ha cap) (oddAxis m)
        (index m j:ℤ) (J6SourcePrecision.printed m b) (rootEntryFile f ell b T w) hf).eval 0 := by
  dsimp only
  let r := physicalRootCall f ell b m l q T w
  letI := r.host.finiteEdge
  letI := r.host.finiteRow
  letI := r.host.finiteCol
  unfold physicalZeroP
  rw [exact_stable_selector_at_root]
  refine zero_polynomial_transport (mesh_root_bits m native hn).symm
    (oddRootCenter_precision f ell b m l q native T w hn j) _ _ _ ?_ _ _ _
  exact (J6RecursiveCrossing.odd_center_valuation m j).2.1

#print axioms zero_polynomial_transport
#print axioms physical_zero_is_stable
end J6R26StablePreparedRoot
