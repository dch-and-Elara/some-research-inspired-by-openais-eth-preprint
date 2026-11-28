import J6R10RepackPhysical
import J6R10RepackPrecision
import J6R9PacketChild

/-! The recursively created child half-port cube is the very same cube
used by the physical mode algebra.  This includes both row and column
bits at a single parent's actual slot, without identifying them. -/
namespace J6R10Repack
open scoped Polynomial BigOperators Classical
open P11FullPacking J6R9PacketScopes J6R9PacketChild J6R9Recursive
variable {E A B G : Type*} [LinearOrder G] [Fintype G] {a : ℕ}
variable {N : Network E A B} {f : ℤ[X]} {ell : ℕ}

abbrev atGroup (P : PhysicalPacking N a G) (i : Fin a) : A ⊕ B → G :=
  declaredGroup P.rowLabel P.colLabel i

abbrev atPacket (P : PhysicalPacking N a G) : E → Page a P.copies G := fun e => (P.seat e).1

theorem row_symbol (P : PhysicalPacking N a G) (i : Fin a) (e : E) :
    rowGroup P.mask i (P.seat e) = atGroup P i (.inl (N.row e)) := by
  exact congrArg (fun c => (c i).1) (P.exactCell e)

theorem col_symbol (P : PhysicalPacking N a G) (i : Fin a) (e : E) :
    colGroup P.mask i (P.seat e) = atGroup P i (.inr (N.col e)) := by
  exact congrArg (fun c => (c i).2) (P.exactCell e)

def rowPhysical (P : PhysicalPacking N a G) (i : Fin a) (g : G) :
    rowsIn N (atGroup P i) g ≃ {e : E // rowGroup P.mask i (P.seat e) = g} :=
  Equiv.subtypeEquivRight (fun e => by rw [row_symbol P i e])

def colPhysical (P : PhysicalPacking N a G) (i : Fin a) (g : G) :
    colsIn N (atGroup P i) g ≃ {e : E // colGroup P.mask i (P.seat e) = g} :=
  Equiv.subtypeEquivRight (fun e => by rw [col_symbol P i e])

abbrev PhysicalState (P : PhysicalPacking N a G) (i : Fin a) (g : G) :=
  State (fun e => P.seat e) (fun e => P.seat e) P.mask i g

def stateEquiv (P : PhysicalPacking N a G) (i : Fin a) (g : G) :
    (ChildEdge N (atGroup P i) g → Bool) ≃ PhysicalState P i g :=
  (((splitSides N (atGroup P i) g).trans
    (Equiv.sumCongr (rowPhysical P i g) (colPhysical P i g))).arrowCongr (Equiv.refl Bool)).trans
    (Equiv.sumArrowEquivProdArrow _ _ Bool)

theorem state_reads_row (P : PhysicalPacking N a G) (i : Fin a) (g : G)
    (x : ChildEdge N (atGroup P i) g → Bool) (e : E)
    (he : rowGroup P.mask i (P.seat e)=g) :
    (stateEquiv P i g x).1 ⟨e,he⟩ =
      x ⟨.inl e,(row_symbol P i e).symm.trans he⟩ := rfl

theorem state_reads_col (P : PhysicalPacking N a G) (i : Fin a) (g : G)
    (x : ChildEdge N (atGroup P i) g → Bool) (e : E)
    (he : colGroup P.mask i (P.seat e)=g) :
    (stateEquiv P i g x).2 ⟨e,he⟩ =
      x ⟨.inr e,(col_symbol P i e).symm.trans he⟩ := rfl

def readPacket (P : PhysicalPacking N a G) (i : Fin a) (g : G)
    (k : Page a P.copies G) (x : ChildEdge N (atGroup P i) g → Bool) :
    PacketPorts N (atGroup P i) (atPacket P) g k → Bool := fun e => x e.val

noncomputable def fillPacket (P : PhysicalPacking N a G) (i : Fin a) (g : G)
    (k : Page a P.copies G)
    (bits : PacketPorts N (atGroup P i) (atPacket P) g k → Bool) :
    ChildEdge N (atGroup P i) g → Bool :=
  fun e => if h : atPacket P (edge e.val)=k then bits ⟨e,h⟩ else false

theorem read_fill_packet (P : PhysicalPacking N a G) (i : Fin a) (g : G)
    (k : Page a P.copies G)
    (bits : PacketPorts N (atGroup P i) (atPacket P) g k → Bool) :
    readPacket P i g k (fillPacket P i g k bits) = bits := by
  funext e
  exact dif_pos e.property

/-- Packet entry obtained from a scoped expression by extension away from
its physical incidence. Such extension is harmless only with the supplied
scope equality; no arbitrary whole-state function is made a packet tensor. -/
noncomputable def compiledPacket (P : PhysicalPacking N a G) (i : Fin a)
    (g : G) (p : ℕ) (F : Page a P.copies G → PhysicalState P i g → Residue f ell p)
    (k : Page a P.copies G) (bits : PacketPorts N (atGroup P i) (atPacket P) g k → Bool) :
    Residue f ell p :=
  F k (stateEquiv P i g (fillPacket P i g k bits))

noncomputable def oldState [Fintype A] [Fintype B]
    (P : PhysicalPacking N a G) (i : Fin a) (g : G) (p : ℕ)
    (oldFile : EntryFile f ell N) (hf : f.Monic) (v : PhysicalState P i g) :
    Residue f ell p :=
  ∏ u : Old (atGroup P i) g,
    (oldFile u.val).read hf p (restrictOriginal N (atGroup P i) g u ((stateEquiv P i g).symm v))

set_option maxHeartbeats 1100000 in
/-- Identification in the printed sum's local state type. Assumes only
packet scope (the next lemma for the signed physical factors), not equality
of the contractions. The left side really constructs the new child graph
and evaluates it from its distinct old/new creation-time descriptors. -/
theorem child_of_scoped_packets [Fintype E] [Fintype A] [Fintype B]
    (P : PhysicalPacking N a G) (i : Fin a) (g : G) (p : ℕ)
    [Fintype (Page a P.copies G)]
    (oldFile : EntryFile f ell N) (hf : f.Monic)
    (F : Page a P.copies G → PhysicalState P i g → Residue f ell p)
    (scopedF : ∀ k (x y : ChildEdge N (atGroup P i) g → Bool),
      readPacket P i g k x = readPacket P i g k y →
      F k (stateEquiv P i g x) = F k (stateEquiv P i g y)) :
    reduce p f ell (trueContraction (child N (atGroup P i) (atPacket P) g)
      (compileChild N (atGroup P i) (atPacket P) g oldFile p (compiledPacket P i g p F)) hf) =
      ∑ v : PhysicalState P i g, oldState P i g p oldFile hf v * ∏ k, F k v := by
  unfold trueContraction
  rw [map_sum]
  refine Finset.sum_bij (fun x _ => stateEquiv P i g x) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_univ]
  · intro x hx y hy hxy
    exact (stateEquiv P i g).injective hxy
  · intro v hv
    refine ⟨(stateEquiv P i g).symm v, ?_, (stateEquiv P i g).apply_symm_apply v⟩
    simp only [Finset.mem_univ]
  intro x hx
  unfold oldState
  rw [Equiv.symm_apply_apply,map_prod,Fintype.prod_sum_type]
  congr 1
  refine Finset.prod_congr (Finset.ext (fun _ => by simp only [Finset.mem_univ])) (fun k _ => ?_)
  calc
    _ = compiledPacket P i g p F k (readPacket P i g k x) :=
      packet_at_creation N (atGroup P i) (atPacket P) g oldFile p (compiledPacket P i g p F) k x hf
    _ = _ := scopedF k (fillPacket P i g k (readPacket P i g k x)) x (read_fill_packet P i g k _)

#print axioms row_symbol
#print axioms col_symbol
#print axioms state_reads_row
#print axioms state_reads_col
#print axioms read_fill_packet
#print axioms child_of_scoped_packets
end J6R10Repack
