import J6R11RepackRootEntry
import J6R11BlueprintNetwork

/-! The native root call is the actual repaired J6 host plus its stored
initial ring entries. This pins the root size/precision fields to the
literal value of the chart, rather than supplying a fictional Call. -/
namespace J6R11Repack
open scoped Classical BigOperators Polynomial
open P11FullPacking J6OrientedHost J6R10Repack J6R11Blueprint J6ActiveRun J6R9Recursive
variable {S V : Type} [LinearOrder S] [Fintype S] [Fintype V]

noncomputable def physicalRootHost (f : ℤ[X]) (ell p m l q : ℕ)
    (T : Plant V m q) (w : Fin (J6Mesh.a m) → S) : PhysicalHost f ell :=
  physicalHost (rootNetwork (b:=J6Mesh.K m) (l:=l) T w)
    (rootEntryFile f ell p T w)

noncomputable def physicalRootCall (f : ℤ[X]) (ell p m l q : ℕ)
    (T : Plant V m q) (w : Fin (J6Mesh.a m) → S) : Call (PhysicalHost f ell) :=
  ⟨physicalRootHost f ell p m l q T w,0,J6Mesh.M m,p⟩

theorem actual_root_edges (f : ℤ[X]) (ell p m l q : ℕ)
    (T : Plant V m q) (w : Fin (J6Mesh.a m) → S)
    (h : m≤J6Mesh.K m) (hL : 2*l=J6Mesh.L m) (hS : Fintype.card S=64) :
    (physicalRootCall f ell p m l q T w).host.edgeCount =
      (physicalRootCall f ell p m l q T w).edges := by
  change Fintype.card (J6RepairedCentered.Ports m l w)=J6Mesh.M m
  exact J6RepairedCapacity.actual_wire_count m l w h hL hS

theorem actual_root_tags (f : ℤ[X]) (ell p m l q : ℕ)
    (T : Plant V m q) (w : Fin (J6Mesh.a m) → S)
    (v : (physicalRootCall f ell p m l q T w).host.Row ⊕
      (physicalRootCall f ell p m l q T w).host.Col) :
    ((physicalRootCall f ell p m l q T w).host.file v).created =
      (physicalRootCall f ell p m l q T w).prec :=
  root_created f ell p T w v

/-- The stored recursive root at its own precision computes the original
planted/padding contraction on literal Boolean edges and vertex tensors. -/
theorem actual_root_receives (f : ℤ[X]) (ell p m l q : ℕ)
    (T : Plant V m q) (w : Fin (J6Mesh.a m) → S) (hf : f.Monic) :
    reduce p f ell ((physicalRootCall f ell p m l q T w).host.contract hf) =
      ∑ x : Wire w m (J6Mesh.K m) l → Bool,
        ∏ v : Left V w m (J6Mesh.K m) l ⊕ Right w m (J6Mesh.K m) l q,
          if rootFlag T w x v then 1 else 0 :=
  root_truth_at_creation f ell p T w hf

#print axioms actual_root_edges
#print axioms actual_root_tags
#print axioms actual_root_receives
end J6R11Repack
