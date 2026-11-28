import J6R12BlueprintReach

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

/-! N2: all 64 actual children of one fixed source centre, probe and
legal mode own exactly the parent half-ports. This keeps the same
address and the original stored file throughout. -/
namespace V8NativeMessage.C3.NativeAssembly
open scoped Classical Polynomial BigOperators
open Polynomial J6R10Reachable J6ActiveRun J6R12Blueprint J6R11Blueprint J6R10Repack
noncomputable section

theorem exact_halfport_partition {E A B K : Type} [Fintype E] [Fintype K]
    (N : Network E A B) (gr : A ⊕ B→K) :
    (∑ g : K, Fintype.card (ChildEdge N gr g))=2*Fintype.card E := by
  have h := Fintype.card_congr (Equiv.sigmaFiberEquiv (retainedGroup N gr))
  simpa only [Fintype.card_sigma,Fintype.card_sum,Port,two_mul] using h

variable {f : ℤ[X]} {ell : ℕ}
variable {S : Params (f:=f) (ell:=ell)} {Δ : ℕ} (sel : Selector S Δ)
variable {c : Call (PhysicalHost f ell)}
variable (d : Ready S Δ c) (t : Center S c) (z : Probe S c)
variable (β : SiteMode sel d t→₀ℕ)

theorem actual_sibling_edge_conservation :
    (∑ g : Fin 64, (packetOfSite sel d t z β g).edgeCount)=2*c.edges := by
  letI := c.host.finiteEdge
  letI := c.host.finiteRow
  letI := c.host.finiteCol
  let gr : c.host.Row ⊕ c.host.Col→Fin 64 :=
    J6R10Repack.atGroup (packing sel d) (centerIndex d t)
  have hpoint (g : Fin 64) : (packetOfSite sel d t z β g).edgeCount =
      Nat.card (ChildEdge c.host.network gr g) := by
    rw [Nat.card_eq_fintype_card]
    rfl
  calc
    _ = ∑ g : Fin 64, Nat.card (ChildEdge c.host.network gr g) :=
      Finset.sum_congr rfl (fun g _ => hpoint g)
    _ = 2*Nat.card c.host.Edge := all_children_conserve_ports c.host.network gr
    _ = 2*c.edges := by rw [Nat.card_eq_fintype_card]; exact congrArg (Nat.mul 2) d.edgeCount
theorem actual_sibling_has_maximum :
    ∃ g : Fin 64, (∀ j : Fin 64,
      (packetOfSite sel d t z β j).edgeCount≤(packetOfSite sel d t z β g).edgeCount) ∧
      c.edges≤32*(packetOfSite sel d t z β g).edgeCount ∧
      32*(packetOfSite sel d t z β g).edgeCount≤3*c.edges := by
  let weight (g : Fin 64) := (packetOfSite sel d t z β g).edgeCount
  obtain ⟨g,_,hg⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin 64)) weight Finset.univ_nonempty
  have hmax : ∀ j : Fin 64, weight j≤weight g := fun j => hg j (Finset.mem_univ j)
  have hsum : (∑ j, weight j)=2*c.edges := actual_sibling_edge_conservation sel d t z β
  have h64 : 2*c.edges≤64*weight g := by
    rw [←hsum]
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using
      (Finset.sum_le_sum (fun j _ => hmax j) :
        (∑ j : Fin 64, weight j) ≤ ∑ _j : Fin 64, weight g)
  exact ⟨g,hmax,by change c.edges≤32*weight g; omega,packetOfSite_shrinks sel d t z β g⟩

#print axioms exact_halfport_partition
#print axioms actual_sibling_edge_conservation
#print axioms actual_sibling_has_maximum
end
end V8NativeMessage.C3.NativeAssembly
