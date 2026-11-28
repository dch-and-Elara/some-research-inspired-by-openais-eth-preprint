import J6R10RepackState
import J6R10RowAffine
import J6R10PacketAssembly

/-! The signed nonzero source-packet expression depends only on its
physical child ports. This identifies the printed one-step RHS with the
newly rewired child's contraction on its actual creation precision. -/
namespace J6R10Repack
open scoped Polynomial BigOperators Classical
open P11FullPacking J6R9PacketScopes J6R9PacketChild J6R9PacketTiles
open J6R10RowAffine J6R10RowIdentity J6R10PacketAssembly J6R9Recursive
variable {E A B G : Type*} [LinearOrder G] [Fintype G] {a : ℕ}
variable {N : Network E A B} {f : ℤ[X]} {ell : ℕ}

theorem same_page_row (P : PhysicalPacking N a G) (i : Fin a) (g : G)
    (k : Page a P.copies G) (x y : ChildEdge N (atGroup P i) g → Bool)
    (hxy : readPacket P i g k x = readPacket P i g k y)
    (e : E) (hg : rowGroup P.mask i (P.seat e)=g) (hk : (P.seat e).1=k) :
    (stateEquiv P i g x).1 ⟨e,hg⟩ = (stateEquiv P i g y).1 ⟨e,hg⟩ := by
  simp only [state_reads_row]
  exact congrFun hxy ⟨⟨.inl e,(row_symbol P i e).symm.trans hg⟩,hk⟩

theorem same_page_col (P : PhysicalPacking N a G) (i : Fin a) (g : G)
    (k : Page a P.copies G) (x y : ChildEdge N (atGroup P i) g → Bool)
    (hxy : readPacket P i g k x = readPacket P i g k y)
    (e : E) (hg : colGroup P.mask i (P.seat e)=g) (hk : (P.seat e).1=k) :
    (stateEquiv P i g x).2 ⟨e,hg⟩ = (stateEquiv P i g y).2 ⟨e,hg⟩ := by
  simp only [state_reads_col]
  exact congrFun hxy ⟨⟨.inr e,(col_symbol P i e).symm.trans hg⟩,hk⟩

section Ring
variable [Fintype E] {R : Type*} [CommRing R]

def childBlock (P : PhysicalPacking N a G) (i : Fin a) (r : E) : G × Page a P.copies G :=
  (rowBlock P.mask i (P.seat r)).swap

def childTarget (P : PhysicalPacking N a G) (i : Fin a) {p : ℕ} (m : Mode i p P.mask) :
    G × Page a P.copies G := (target P.mask i m).swap

def childSource (P : PhysicalPacking N a G) (i : Fin a) {p : ℕ} (m : Mode i p P.mask) :
    G × Page a P.copies G := (source P.mask i m,m.page)

noncomputable def stateMoment (P : PhysicalPacking N a G) (i : Fin a) (g : G)
    (p : ℕ) (v : PhysicalState P i g) (m : Mode i p P.mask) : R :=
  if h : source P.mask i m=g then
    moment (fun e => P.seat e) P.mask i m ((h.symm ▸ v : PhysicalState P i (source P.mask i m))).2
  else 0

theorem groupBase_same_packet (P : PhysicalPacking N a G) (i : Fin a) (g : G)
    (t : ℤ) (p : ℕ) (hnil : (2:R)^p=0) (z : R) (k : Page a P.copies G)
    (x y : ChildEdge N (atGroup P i) g → Bool) (hxy : readPacket P i g k x = readPacket P i g k y)
    (r : E) (hg : rowGroup P.mask i (P.seat r)=g) (hk : (P.seat r).1=k) :
    groupBase (fun e => P.seat e) (fun e => P.seat e) P.mask i t p hnil z g (stateEquiv P i g x) r =
      groupBase (fun e => P.seat e) (fun e => P.seat e) P.mask i t p hnil z g (stateEquiv P i g y) r := by
  classical
  simp only [groupBase,dif_pos hg]
  unfold localValue
  refine Finset.sum_congr (Finset.ext (fun _ => by simp only [Finset.mem_univ])) (fun q _ => ?_)
  by_cases hq : (P.seat q.val).1=(P.seat r).1
  · simp only [if_pos hq]
    rw [same_page_col P i g k x y hxy q.val (q.property.trans hg) (hq.trans hk)]
  · simp only [if_neg hq]

theorem moment_same_packet (P : PhysicalPacking N a G) (i : Fin a) (g : G)
    (p : ℕ) (k : Page a P.copies G)
    (x y : ChildEdge N (atGroup P i) g → Bool) (hxy : readPacket P i g k x = readPacket P i g k y)
    (m : Mode i p P.mask) (hm : childSource P i m=(g,k)) :
    stateMoment (R:=R) P i g p (stateEquiv P i g x) m =
      stateMoment (R:=R) P i g p (stateEquiv P i g y) m := by
  classical
  have hg : source P.mask i m=g := congrArg Prod.fst hm
  have hk : m.page=k := congrArg Prod.snd hm
  subst g
  simp only [stateMoment]
  unfold moment
  refine Finset.sum_congr rfl (fun q _ => ?_)
  have hpage : (P.seat q.val).1=m.page := (Finset.mem_filter.mp q.property).2.1
  have hgroup := column_source_group (fun e => P.seat e) P.mask i m q.val q.property
  rw [same_page_col P i (source P.mask i m) k x y hxy q.val hgroup (hpage.trans hk)]

noncomputable def actualPacket (P : PhysicalPacking N a G) (i : Fin a) {t : ℤ}
    (ht : t≠0) (hv : padicValInt 2 t=i.val) (p : ℕ) (hnil : (2:R)^p=0) (z : R)
    (β : Mode i p P.mask →₀ ℕ) (g : G) (k : Page a P.copies G) (v : PhysicalState P i g) : R :=
  J6RecursiveModes.packet (childTarget P i) (childSource P i) g k
    (actualRows (childBlock P i) g k)
    (groupBit (fun e => P.seat e) (fun e => P.seat e) P.mask i g v)
    (groupBase (fun e => P.seat e) (fun e => P.seat e) P.mask i t p hnil z g v)
    (fun r m => scaledRow P.mask i ht hv p hnil z (P.seat r) m) (stateMoment P i g p v) β

theorem actual_packet_scope (P : PhysicalPacking N a G) (i : Fin a) {t : ℤ}
    (ht : t≠0) (hv : padicValInt 2 t=i.val) (p : ℕ) (hnil : (2:R)^p=0) (z : R)
    (β : Mode i p P.mask →₀ ℕ) (g : G) (k : Page a P.copies G)
    (x y : ChildEdge N (atGroup P i) g → Bool) (hxy : readPacket P i g k x = readPacket P i g k y) :
    actualPacket P i ht hv p hnil z β g k (stateEquiv P i g x) =
      actualPacket P i ht hv p hnil z β g k (stateEquiv P i g y) := by
  classical
  unfold actualPacket J6RecursiveModes.packet
  refine congrArg₂ (· * ·) ?_ ?_
  · apply congrArg (MvPolynomial.coeff _)
    refine Finset.prod_congr rfl (fun r hr => ?_)
    have h : childBlock P i r=(g,k) := (Finset.mem_filter.mp hr).2
    have hg : rowGroup P.mask i (P.seat r)=g := congrArg Prod.fst h
    have hk : (P.seat r).1=k := congrArg Prod.snd h
    rw [groupBase_same_packet P i g t p hnil z k x y hxy r hg hk]
    simp only [groupBit,dif_pos hg]
    rw [same_page_row P i g k x y hxy r hg hk]
  · refine Finset.prod_congr rfl (fun m hm => ?_)
    rw [moment_same_packet P i g p k x y hxy m (Finset.mem_filter.mp hm).2]
end Ring

set_option maxHeartbeats 1000000 in
/-- The explicit finite child entries realize exactly the printed packet
factors at this probe, with the old tensor factors still sharing all their
incident bits. This statement does not depend on the parent expansion. -/
theorem actual_physical_child [Fintype E] [Fintype A] [Fintype B]
    (P : PhysicalPacking N a G) (i : Fin a) {t : ℤ} (ht : t≠0)
    (hv : padicValInt 2 t=i.val) (p : ℕ)
    (hnil : (2:Residue f ell p)^p=0) (z : Residue f ell p)
    (oldFile : EntryFile f ell N) (hf : f.Monic)
    (β : Mode i p P.mask →₀ ℕ) (g : G) :
    let F := actualPacket P i ht hv p hnil z β g
    reduce p f ell (trueContraction (child N (atGroup P i) (atPacket P) g)
      (compileChild N (atGroup P i) (atPacket P) g oldFile p (compiledPacket P i g p F)) hf) =
    ∑ v : PhysicalState P i g, oldState P i g p oldFile hf v * ∏ k, F k v := by
  exact child_of_scoped_packets P i g p oldFile hf _ (actual_packet_scope P i ht hv p hnil z β g)

#print axioms actual_physical_child
#print axioms same_page_row
#print axioms same_page_col
#print axioms groupBase_same_packet
#print axioms moment_same_packet
#print axioms actual_packet_scope
end J6R10Repack
