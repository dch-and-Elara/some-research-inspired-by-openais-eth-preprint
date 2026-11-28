import J6R20AncestorTape
import J6R18ChildWritePhysical

/-! The key of a real port at an actual newly created packet is its
previous same-page slot and previous row/column side. Multiedges are
not merged, and the two sides at the same slot remain distinct. -/
namespace J6R20Ancestor
open scoped Classical
open J6R18ChildWrite J6R10Repack P11FullPacking J6R9PacketScopes J6R9PacketChild
open J6R15ModeCost

variable {E A B G : Type} [LinearOrder G] [Fintype G]
variable {a : ℕ} {N : Network E A B}

abbrev OriginNet (P : PhysicalPacking N a G) (i : Fin a) (g : G) :=
  child N (atGroup P i) (atPacket P) g

abbrev OriginPorts (P : PhysicalPacking N a G) (i : Fin a)
    (g : G) (k : Page a P.copies G) :=
  ParentPorts (OriginNet P i g) (.inr k)

def slotWord (P : PhysicalPacking N a G) (e : E) : Word a :=
  word (P.seat e).2.val

def originKey (P : PhysicalPacking N a G) (i : Fin a) (g : G)
    (k : Page a P.copies G) (p : OriginPorts P i g k) : Key a :=
  let u := packetReindex N (atGroup P i) (atPacket P) g k p
  ⟨side u.val.val,slotWord P (edge u.val.val)⟩

theorem originKey_inj (P : PhysicalPacking N a G) (i : Fin a) (g : G)
    (k : Page a P.copies G) : Function.Injective (originKey P i g k) := by
  intro x y h
  apply (packetReindex N (atGroup P i) (atPacket P) g k).injective
  apply (packetPortsEmbedding N (atGroup P i) P.seat g k).injective
  let e (u : OriginPorts P i g k) := edge ((packetReindex N (atGroup P i) (atPacket P) g k u).val.val)
  refine Prod.ext (Fin.ext ?_) (congrArg Key.side h)
  have H := congrArg (fun z : Key a=>z.slot.val) h
  change (slotWord P (e x)).val=(slotWord P (e y)).val at H
  rw [slotWord,slotWord,word_val (P.seat (e x)).2.isLt,word_val (P.seat (e y)).2.isLt] at H
  exact H

def rowOriginPort (P : PhysicalPacking N a G) (i : Fin a) {g : G}
    {k : Page a P.copies G} (r : RowsOf P i g k) : OriginPorts P i g k :=
  (packetReindex N (atGroup P i) (atPacket P) g k).symm
    ⟨⟨.inl r.val,(row_symbol P i r.val).symm.trans (row_scope P i r).1⟩,(row_scope P i r).2⟩

def colOriginPort (P : PhysicalPacking N a G) (i : Fin a) {g : G}
    {k : Page a P.copies G} (r : ColsOf P i g k) : OriginPorts P i g k :=
  (packetReindex N (atGroup P i) (atPacket P) g k).symm
    ⟨⟨.inr r.val,(col_symbol P i r.val).symm.trans r.property.1⟩,r.property.2⟩

theorem rowKey (P : PhysicalPacking N a G) (i : Fin a) {g : G}
    {k : Page a P.copies G} (r : RowsOf P i g k) :
    originKey P i g k (rowOriginPort P i r)=⟨false,slotWord P r.val⟩ := by
  simp only [originKey,rowOriginPort,Equiv.apply_symm_apply]
  rfl

theorem colKey (P : PhysicalPacking N a G) (i : Fin a) {g : G}
    {k : Page a P.copies G} (r : ColsOf P i g k) :
    originKey P i g k (colOriginPort P i r)=⟨true,slotWord P r.val⟩ := by
  simp only [originKey,colOriginPort,Equiv.apply_symm_apply]
  rfl

noncomputable def originState (P : PhysicalPacking N a G) (i : Fin a) (g : G)
    (k : Page a P.copies G) (bits : OriginPorts P i g k→Bool) : PhysicalState P i g :=
  stateEquiv P i g (fillPacket P i g k
    (bits ∘ (packetReindex N (atGroup P i) (atPacket P) g k).symm))

theorem origin_row_reads (P : PhysicalPacking N a G) (i : Fin a) (g : G)
    (k : Page a P.copies G) (bits : OriginPorts P i g k→Bool) (r : RowsOf P i g k) :
    realRow P i (originState P i g k bits) r=⟨slotWord P r.val,bits (rowOriginPort P i r)⟩ := by
  have H := state_reads_row P i g (fillPacket P i g k
    (bits ∘ (packetReindex N (atGroup P i) (atPacket P) g k).symm)) r.val (row_scope P i r).1
  unfold realRow originState
  rw [H]
  have hk : atPacket P (edge (.inl r.val))=k := (row_scope P i r).2
  simp only [fillPacket,dif_pos hk]
  rfl

theorem origin_col_reads (P : PhysicalPacking N a G) (i : Fin a) (g : G)
    (k : Page a P.copies G) (bits : OriginPorts P i g k→Bool) (r : ColsOf P i g k) :
    realCol P i (originState P i g k bits) r=⟨slotWord P r.val,bits (colOriginPort P i r)⟩ := by
  have H := state_reads_col P i g (fillPacket P i g k
    (bits ∘ (packetReindex N (atGroup P i) (atPacket P) g k).symm)) r.val r.property.1
  unfold realCol originState
  rw [H]
  have hk : atPacket P (edge (.inr r.val))=k := r.property.2
  simp only [fillPacket,dif_pos hk]
  rfl

#print axioms originKey_inj
#print axioms rowKey
#print axioms colKey
#print axioms origin_row_reads
#print axioms origin_col_reads
end J6R20Ancestor

