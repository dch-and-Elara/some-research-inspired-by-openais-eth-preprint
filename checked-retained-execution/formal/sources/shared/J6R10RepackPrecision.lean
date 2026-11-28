import J6R10Repack
import J6R9RecursiveCanonical

/-! Source lines 57--71 and 489--553. Each entry routine is owned by
the precision at creation. Retaining a vertex restricts/reindexes its
incidence domain, never changes that precision, and never re-lifts a
computed product. A packet tensor gets exactly its parent's p_t tag. -/
namespace J6R10Repack
open scoped Polynomial BigOperators Classical
open J6R9Recursive Polynomial

abbrev Residue (f : ℤ[X]) (ell p : ℕ) := J6ActiveInterpolation.Ring p f ell

structure CreatedEntry (f : ℤ[X]) (ell : ℕ) (Args : Type*) where
  created : ℕ
  table : Args → Residue f ell created

variable {f : ℤ[X]} {ell : ℕ}

def CreatedEntry.reindex {X Y : Type*} (d : CreatedEntry f ell Y) (ρ : X → Y) :
    CreatedEntry f ell X := ⟨d.created,fun x => d.table (ρ x)⟩

theorem CreatedEntry.reindex_comp {X Y Z : Type*} (d : CreatedEntry f ell Z)
    (ρ : Y → Z) (σ : X → Y) :
    (d.reindex ρ).reindex σ = d.reindex (ρ ∘ σ) := rfl

noncomputable def CreatedEntry.frozen {X : Type*} (d : CreatedEntry f ell X)
    (hf : f.Monic) (x : X) : IntRing f ell :=
  canonicalLift d.created f hf ell (d.table x)

noncomputable def CreatedEntry.read {X : Type*} (d : CreatedEntry f ell X)
    (hf : f.Monic) (p : ℕ) (x : X) : Residue f ell p :=
  reduce p f ell (d.frozen hf x)

theorem CreatedEntry.read_created {X : Type*} (d : CreatedEntry f ell X)
    (hf : f.Monic) (x : X) : d.read hf d.created x = d.table x :=
  canonicalLift_spec _ f hf ell _

theorem CreatedEntry.reindex_frozen {X Y : Type*} (d : CreatedEntry f ell Y)
    (ρ : X → Y) (hf : f.Monic) (x : X) : (d.reindex ρ).frozen hf x = d.frozen hf (ρ x) := rfl

theorem CreatedEntry.reindex_read {X Y : Type*} (d : CreatedEntry f ell Y)
    (ρ : X → Y) (hf : f.Monic) (p : ℕ) (x : X) : (d.reindex ρ).read hf p x = d.read hf p (ρ x) := rfl

variable {E A B K G : Type*}

abbrev EntryFile (f : ℤ[X]) (ell : ℕ) (N : Network E A B) :=
  ∀ v : A ⊕ B, CreatedEntry f ell (ParentPorts N v → Bool)

def oldReindex (N : Network E A B) (group : A ⊕ B → G) (packet : E → K) (g : G)
    (v : Old group g) :
    ParentPorts (child N group packet g) (.inl v) ≃ ParentPorts N v.val :=
  ((rowPortsEquiv (child N group packet g) v).symm).trans (oldPortsEquiv N group packet g v)

def packetReindex (N : Network E A B) (group : A ⊕ B → G) (packet : E → K) (g : G)
    (k : K) :
    ParentPorts (child N group packet g) (.inr k) ≃ PacketPorts N group packet g k :=
  (colPortsEquiv (child N group packet g) k).symm

/-- Only the new packet entry is formed at p; retained old entries reference
their existing description with the exact parent-incidence reindexing. -/
def compileChild (N : Network E A B) (group : A ⊕ B → G) (packet : E → K) (g : G)
    (oldFile : EntryFile f ell N) (p : ℕ)
    (packetValue : ∀ k : K, (PacketPorts N group packet g k → Bool) → Residue f ell p) :
    EntryFile f ell (child N group packet g)
  | .inl v => (oldFile v.val).reindex (fun y => y ∘ (oldReindex N group packet g v).symm)
  | .inr k => (⟨p,packetValue k⟩ : CreatedEntry f ell _).reindex
      (fun y => y ∘ (packetReindex N group packet g k).symm)

theorem old_tag (N : Network E A B) (group : A ⊕ B → G) (packet : E → K) (g : G)
    (oldFile : EntryFile f ell N) (p : ℕ)
    (packetValue : ∀ k : K, (PacketPorts N group packet g k → Bool) → Residue f ell p)
    (v : Old group g) :
    (compileChild N group packet g oldFile p packetValue (.inl v)).created =
      (oldFile v.val).created := rfl

theorem new_tag (N : Network E A B) (group : A ⊕ B → G) (packet : E → K) (g : G)
    (oldFile : EntryFile f ell N) (p : ℕ)
    (packetValue : ∀ k : K, (PacketPorts N group packet g k → Bool) → Residue f ell p) (k : K) :
    (compileChild N group packet g oldFile p packetValue (.inr k)).created = p := rfl

def restrictOriginal (N : Network E A B) (group : A ⊕ B → G) (g : G)
    (v : Old group g) (x : ChildEdge N group g → Bool) : ParentPorts N v.val → Bool :=
  fun p => x ⟨p.val,(congrArg group p.property).trans v.property⟩

def assignment (N : Network E A B) (x : E → Bool) (v : A ⊕ B) :
    ParentPorts N v → Bool := fun p => x (edge p.val)

theorem retained_int_exact (N : Network E A B) (group : A ⊕ B → G) (packet : E → K) (g : G)
    (oldFile : EntryFile f ell N) (p : ℕ)
    (packetValue : ∀ k : K, (PacketPorts N group packet g k → Bool) → Residue f ell p)
    (v : Old group g) (x : ChildEdge N group g → Bool) (hf : f.Monic) :
    (compileChild N group packet g oldFile p packetValue (.inl v)).frozen hf
      (assignment (child N group packet g) x (.inl v)) =
      (oldFile v.val).frozen hf (restrictOriginal N group g v x) := rfl

theorem packet_at_creation (N : Network E A B) (group : A ⊕ B → G) (packet : E → K) (g : G)
    (oldFile : EntryFile f ell N) (p : ℕ)
    (packetValue : ∀ k : K, (PacketPorts N group packet g k → Bool) → Residue f ell p)
    (k : K) (x : ChildEdge N group g → Bool) (hf : f.Monic) :
    (compileChild N group packet g oldFile p packetValue (.inr k)).read hf p
      (assignment (child N group packet g) x (.inr k)) = packetValue k (fun h => x h.val) := by
  exact (compileChild N group packet g oldFile p packetValue (.inr k)).read_created hf _

/-- Leaf truth formed by multiplying individually canonical-lifted tensor
entries. The finite product is not itself lifted to obtain this truth. -/
noncomputable def trueContraction [Fintype E] [Fintype A] [Fintype B]
    (N : Network E A B) (file : EntryFile f ell N) (hf : f.Monic) : IntRing f ell :=
  ∑ x : E → Bool, ∏ v : A ⊕ B, (file v).frozen hf (assignment N x v)

/-- The physically re-wired child's truth reduces to the intended retained
plus packet contraction at its creation precision, with one shared bit
assignment on the whole incidence fibre. No child-answer oracle appears. -/
theorem child_at_creation [Fintype E] [Fintype A] [Fintype B] [Fintype K]
    (N : Network E A B) (group : A ⊕ B → G) (packet : E → K) (g : G)
    (oldFile : EntryFile f ell N) (p : ℕ)
    (packetValue : ∀ k : K, (PacketPorts N group packet g k → Bool) → Residue f ell p)
    (hf : f.Monic) :
    reduce p f ell (trueContraction (child N group packet g)
      (compileChild N group packet g oldFile p packetValue) hf) =
      ∑ x : ChildEdge N group g → Bool,
        (∏ v : Old group g, (oldFile v.val).read hf p (restrictOriginal N group g v x)) *
        (∏ k : K, packetValue k (fun h => x h.val)) := by
  classical
  rw [trueContraction,map_sum]
  refine Finset.sum_congr (Finset.ext (fun x => by simp only [Finset.mem_univ])) (fun x _ => ?_)
  rw [map_prod,Fintype.prod_sum_type]
  congr 1
  refine Finset.prod_congr (Finset.ext (fun _ => by simp only [Finset.mem_univ])) (fun k _ => ?_)
  exact packet_at_creation N group packet g oldFile p packetValue k x hf

#print axioms CreatedEntry.reindex_comp
#print axioms CreatedEntry.read_created
#print axioms CreatedEntry.reindex_frozen
#print axioms old_tag
#print axioms new_tag
#print axioms retained_int_exact
#print axioms packet_at_creation
#print axioms child_at_creation
end J6R10Repack
