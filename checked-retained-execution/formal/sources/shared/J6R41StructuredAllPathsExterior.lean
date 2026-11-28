import J6R41StructuredAllPathsInduct

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 13500000
set_option maxRecDepth 3200

/-! Discharge the induction's initial record condition with the real
R37 source file, not any supplied seed table. The remaining
per-occurrence guard is only the ordered addon data and the physical
adjacent-copy/next-chart agreement. -/
namespace J6R41StructuredAllPaths
open scoped Polynomial Classical
open Polynomial J6R21Ancestor J6R34ChildPath J6R35RootOrigins J6R26DescriptorTree
open J6R36ChildFramedRoute J6R37StructuredRoot J6R34RootAtlas J6R32RootGeneratedRegistryInputs
open J6R31RootResidentTables J6Mesh J6OrientedHost J6R24LegalLayout J6R10Repack
open J6R26StablePreparedRoot J6R11Repack J6R25PreparedSupply
open J6R24MeteredRecursion J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6ActiveRun J6R12Blueprint J6R11Blueprint J1PPrinted J6R16ModeCost J6R15ModeCost

variable {V : Type} [Fintype V]
variable {f : ℤ[X]} {m n base native : ℕ} {plant : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) plant
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q ro co d edgew tc tj key prec tw bw C s : ℕ}
variable (X : StableExterior G ell q ro co d edgew tc tj key prec tw bw)
variable (gate : Stamp key prec) (pad : ℕ)

local notation "rootCall" => (exteriorChild G ell X.centre X.sample X.group)

theorem exact_real_root_tag_at_port (gateWidth : gate.created.val=base)
    (u : (rootCall).host.Row⊕(rootCall).host.Col)
    (x : PortAt (J6R34ChildPath.point (rootCall).host u)) :
    (initialPayload X gate pad x.val).1=initialOrigin X gate pad u := by
  rcases u with old|packet
  · obtain ⟨tr,h⟩ := initial_gate_is_written X gate pad gateWidth old
    exact congrArg Prod.fst (h x)
  · let E := canonicalPageEquiv G ell X.centre
    have e : E (E.symm packet)=packet := E.apply_symm_apply packet
    obtain ⟨tr,_,h⟩ := initial_packet_is_written X gate pad (E.symm packet)
    obtain ⟨h'⟩ : Nonempty (∀ y : PortAt (J6R34ChildPath.point (rootCall).host (.inr packet)),
        (initialPayload X gate pad y.val).1=initialOrigin X gate pad (.inr packet)) := by
      rw [←e]
      exact ⟨fun y=>congrArg Prod.fst (h y)⟩
    exact h' x

variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
variable {born : Births T key prec tw bw (pageKeyWidth m+pad)}
variable {keys : PageKeys born}
variable (files : SiteFiles born keys (initialOrigin X gate pad))

theorem conditional_real_exterior_all_paths
    (L : Linked files (initialPayload X gate pad)) (gateWidth : gate.created.val=base)
    {c : Call (PhysicalHost f ell)} (p : Path sel rootCall c)
    (u : c.host.Row⊕c.host.Col) :
    RootContinues files (initialPayload X gate pad) p u ∨
    NativeContinues files (initialPayload X gate pad) p u :=
  linked_paths_use_original_payload files (initialPayload X gate pad) L
    (exact_real_root_tag_at_port X gate pad gateWidth) p u

#print axioms exact_real_root_tag_at_port
#print axioms conditional_real_exterior_all_paths
end J6R41StructuredAllPaths