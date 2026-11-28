import J6R41StructuredAllPathsContinue
import J6R37StructuredRootPath

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 12500000
set_option maxRecDepth 3100

/-! All real occurrence paths, all vertices, all their ports. The
native branch now has a real structured seed in the same R26 issue,
not merely a typed existence/OnPath claim. This result is conditional
on actual per-site aligned addon input. It certifies the reconstructed
body, not that arbitrary next-site raw tapes have already copied it. -/
namespace J6R41StructuredAllPaths
open scoped Polynomial Classical
open Polynomial J6R21Ancestor J6R34ChildPath J6R35RootOrigins J6R26DescriptorTree
open J6R36ChildFramedRoute J6R37StructuredRoot J6R34RootAtlas J6R32RootGeneratedRegistryInputs
open J6R31RootResidentTables J6Mesh J6OrientedHost J6R24LegalLayout J6R10Repack
open J6R26StablePreparedRoot J6R11Repack J6R25PreparedSupply
open J6R24MeteredRecursion J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6ActiveRun J6R12Blueprint J6R11Blueprint J1PPrinted J6R16ModeCost

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {P : Prepared cfg sel r hf}
variable (born : Births P key prec tw bw page)

abbrev PriorOrigins (sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s))
    (r : Call (PhysicalHost f ell)) (key prec page : ℕ) :=
  ∀ {c : Call (PhysicalHost f ell)},Path sel r c→c.host.Row⊕c.host.Col→Origin key prec page

abbrev AlignedFamily (past : PriorOrigins sel r key prec page) :=
  ∀ {c : Call (PhysicalHost f ell)} (p : Path sel r c) (w : (Plan sel).Slot c),SiteInputs (born p w) (past p)

variable {born} {past : PriorOrigins sel r key prec page}
variable (sites : AlignedFamily born past)

def NativeLine {c : Call (PhysicalHost f ell)} (p : Path sel r c) (cur : Point f ell) : Prop :=
  ∃ (start : Call (PhysicalHost f ell)) (older : Path sel r start)
    (w : (Plan sel).Slot start) (k : PageAt P (older.ticket w)),
    OnPath born (born older w).job p ∧
    ∃ tr : Trace (bornPoint P (older.ticket w) k) cur,
      ∀ x : PortAt cur, NativeRoute (sites older w) k tr x

theorem actual_native_route_on_live_path {c : Call (PhysicalHost f ell)}
    (p : Path sel r c) (cur : Point f ell) (line : NativeLine sites p cur)
    (rootLive : PageBank f ell key prec tw bw page→Prop)
    (B : PageBank f ell key prec tw bw page) (ready : opened born rootLive p B) :
    ∃ (start : Call (PhysicalHost f ell)) (older : Path sel r start)
      (w : (Plan sel).Slot start) (k : PageAt P (older.ticket w)),
      IsLive (born older w).job B ∧
      ∃ tr : Trace (bornPoint P (older.ticket w) k) cur,
        ∀ x : PortAt cur, NativeRoute (sites older w) k tr x := by
  obtain ⟨start,older,w,k,on,tr,law⟩ := line
  exact ⟨start,older,w,k,ancestor_paged_live born _ p on B ready,tr,law⟩

section Exterior
variable {V : Type} [Fintype V] {m n base native : ℕ} {T : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) T
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {q ro co d edgew tc tj : ℕ}
variable (X : StableExterior G ell q ro co d edgew tc tj key prec tw bw)
variable (gate : Stamp key prec) (pad : ℕ)
variable {PX : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
variable (births : Births PX key prec tw bw (pageKeyWidth m+pad))
variable {prior : PriorOrigins sel (exteriorChild G ell X.centre X.sample X.group) key prec (pageKeyWidth m+pad)}
variable (actual : AlignedFamily births prior)

theorem actual_paths_all_three_seeds (gateWidth : gate.created.val=base)
    {c : Call (PhysicalHost f ell)}
    (p : Path sel (exteriorChild G ell X.centre X.sample X.group) c) (u : c.host.Row⊕c.host.Col) :
    GateLine X gate pad (J6R34ChildPath.point c.host u) ∨
    PageLine X gate pad (J6R34ChildPath.point c.host u) ∨
    NativeLine actual p (J6R34ChildPath.point c.host u) := by
  rcases actual_path_from_structured_exterior X gate pad births gateWidth p u with old|outer|inner
  · exact Or.inl old
  · exact Or.inr (Or.inl outer)
  · obtain ⟨start,previous,slot,page,onPath,⟨tr⟩⟩ := inner
    exact Or.inr (Or.inr ⟨start,previous,slot,page,onPath,tr,native_seed_retention_trace (actual previous slot) page tr⟩)

end Exterior

#print axioms actual_native_route_on_live_path
#print axioms actual_paths_all_three_seeds
end J6R41StructuredAllPaths