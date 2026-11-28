import J6R10RepackPrecision
import J6R9RecursiveRun

/-! A concrete Blueprint host carries an actual finite bipartite network
and its immutable creation-tagged entry file. The generic finite edge
index is only a reindexing: Blueprint.truth is exactly trueContraction
on this physical host, with all tables frozen individually. -/
namespace J6R11Blueprint
open scoped Polynomial BigOperators Classical
open J6R10Repack J6ActiveRun J6R9Recursive

structure PhysicalHost (f : ℤ[X]) (ell : ℕ) where
  Edge : Type
  Row : Type
  Col : Type
  finiteEdge : Fintype Edge
  finiteRow : Fintype Row
  finiteCol : Fintype Col
  network : Network Edge Row Col
  file : EntryFile f ell network

variable {f : ℤ[X]} {ell : ℕ}

def PhysicalHost.edgeCount (H : PhysicalHost f ell) : ℕ :=
  @Fintype.card H.Edge H.finiteEdge

def physicalHost {E A B : Type} [Fintype E] [Fintype A] [Fintype B]
    (N : Network E A B) (file : EntryFile f ell N) : PhysicalHost f ell :=
  ⟨E,A,B,inferInstance,inferInstance,inferInstance,N,file⟩

noncomputable def PhysicalHost.contract (H : PhysicalHost f ell) (hf : f.Monic) : IntRing f ell := by
  letI := H.finiteEdge
  letI := H.finiteRow
  letI := H.finiteCol
  exact trueContraction H.network H.file hf

noncomputable def PhysicalHost.edgeOrder (H : PhysicalHost f ell) (M : ℕ)
    (h : H.edgeCount = M) : H.Edge ≃ Fin M := by
  letI := H.finiteEdge
  exact (Fintype.equivFin H.Edge).trans (finCongr h)

noncomputable def physicalEntries (hf : f.Monic) (c : Call (PhysicalHost f ell))
    (x : Fin c.edges → Bool) : List (IntRing f ell) := by
  letI := c.host.finiteRow
  letI := c.host.finiteCol
  exact if h : c.host.edgeCount = c.edges then
    (Finset.univ : Finset (c.host.Row ⊕ c.host.Col)).toList.map
      (fun v => (c.host.file v).frozen hf
        (assignment c.host.network (x ∘ c.host.edgeOrder c.edges h) v))
  else []

theorem physicalEntries_sum (hf : f.Monic) (c : Call (PhysicalHost f ell))
    (h : c.host.edgeCount = c.edges) :
    (∑ x : Fin c.edges → Bool, (physicalEntries hf c x).prod) = c.host.contract hf := by
  letI := c.host.finiteEdge
  letI := c.host.finiteRow
  letI := c.host.finiteCol
  unfold PhysicalHost.contract trueContraction
  apply Fintype.sum_equiv ((c.host.edgeOrder c.edges h).symm.arrowCongr (Equiv.refl Bool))
  intro x
  unfold physicalEntries
  rw [dif_pos h,Finset.prod_map_toList]
  rfl

theorem physicalBlueprint_truth {Mode : Type*} [Fintype Mode] [DecidableEq Mode]
    {S : Shape (PhysicalHost f ell) Mode}
    (hf : f.Monic) (B : Blueprint S f ell)
    (entries : B.entries = physicalEntries hf) (c : Call (PhysicalHost f ell))
    (h : c.host.edgeCount = c.edges) :
    B.truth c = c.host.contract hf := by
  rw [Blueprint.truth,entries]
  exact physicalEntries_sum hf c h

section Child
variable {E A B K G : Type} [Fintype E] [Fintype A] [Fintype B] [Fintype K]
    [DecidableEq G]

noncomputable def physicalChildHost (N : Network E A B) (group : A ⊕ B → G)
    (packet : E → K) (g : G) (oldFile : EntryFile f ell N) (p : ℕ)
    (packetValue : ∀ k : K, (PacketPorts N group packet g k → Bool) → Residue f ell p) :
    PhysicalHost f ell :=
  physicalHost (J6R10Repack.child N group packet g)
    (compileChild N group packet g oldFile p packetValue)

end Child

#print axioms physicalEntries_sum
#print axioms physicalBlueprint_truth
end J6R11Blueprint