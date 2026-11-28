import J6R20AncestorActual

/-! A typed path follows ONE retained tensor through successive actual
child graphs. Each step uses the source repacking of that child; none
of the new siblings' numeric entry routines is invoked on this path. -/
namespace J6R21Ancestor
open scoped Polynomial
open J6R10Repack J6R11Blueprint

structure Point (f : ℤ[X]) (ell : ℕ) where
  host : PhysicalHost f ell
  vertex : host.Row ⊕ host.Col

variable {f : ℤ[X]} {ell : ℕ}

abbrev PortAt (x : Point f ell) := ParentPorts x.host.network x.vertex
abbrev entry (x : Point f ell) := x.host.file x.vertex

structure Move (x : Point f ell) where
  Group : Type
  Packet : Type
  decGroup : DecidableEq Group
  finitePacket : Fintype Packet
  group : x.host.Row ⊕ x.host.Col → Group
  packet : x.host.Edge → Packet
  selected : Group
  keeps : group x.vertex=selected
  p : ℕ
  siblings : ∀ k : Packet,(PacketPorts x.host.network group packet selected k→Bool)→Residue f ell p

def Move.kept {x : Point f ell} (t : Move x) : Old t.group t.selected :=
  ⟨x.vertex,t.keeps⟩

noncomputable def Move.next {x : Point f ell} (t : Move x) : Point f ell := by
  letI := x.host.finiteEdge
  letI := x.host.finiteRow
  letI := x.host.finiteCol
  letI := t.finitePacket
  letI := t.decGroup
  exact ⟨physicalChildHost x.host.network t.group t.packet t.selected x.host.file t.p t.siblings,
    .inl t.kept⟩

noncomputable def Move.back {x : Point f ell} (t : Move x) : PortAt t.next ≃ PortAt x :=
  oldReindex x.host.network t.group t.packet t.selected t.kept

theorem Move.side_left {x : Point f ell} (t : Move x) (y : PortAt t.next) :
    side y.val=false := by
  rcases y with ⟨y,h⟩
  cases y with
  | inl e => rfl
  | inr e => cases h

theorem Move.back_val {x : Point f ell} (t : Move x) (y : PortAt t.next) :
    (t.back y).val=(edge y.val).val := by
  rcases y with ⟨y,h⟩
  cases y with
  | inl e => rfl
  | inr e => cases h

theorem Move.file_reindexed {x : Point f ell} (t : Move x) :
    entry t.next=(entry x).reindex (fun bits=>bits ∘ t.back.symm) := rfl

inductive Trace (ancestor : Point f ell) : Point f ell → Type 1
  | start : Trace ancestor ancestor
  | keep {cur : Point f ell} (old : Trace ancestor cur) (m : Move cur) :
    Trace ancestor m.next

variable {ancestor : Point f ell}

def Trace.depth {cur : Point f ell} : Trace ancestor cur→ℕ
  | .start => 0
  | .keep old _ => old.depth+1

noncomputable def Trace.back : {cur : Point f ell} → Trace ancestor cur → PortAt cur ≃ PortAt ancestor
  | _,.start => Equiv.refl _
  | _,.keep prev m => m.back.trans prev.back

noncomputable def Trace.literal (base : PortAt ancestor→List Bool) :
    {cur : Point f ell} → Trace ancestor cur → PortAt cur→List Bool
  | _,.start,b => base b
  | _,.keep prev m,b => side b.val::prev.literal base (m.back b)

theorem Trace.literal_exact {cur : Point f ell} (tr : Trace ancestor cur) (base : PortAt ancestor→List Bool)
    (b : PortAt cur) :
    tr.literal base b=List.replicate tr.depth false++base (tr.back b) := by
  induction tr with
  | start => rfl
  | keep old m ih =>
    rw [Trace.literal,m.side_left,ih,Trace.depth,Trace.back,List.replicate_succ,List.cons_append]
    rfl

theorem Trace.file_reindexed {cur : Point f ell} (tr : Trace ancestor cur) :
    entry cur=(entry ancestor).reindex (fun bits=>bits ∘ tr.back.symm) := by
  induction tr with
  | start => rfl
  | keep old m ih =>
    rw [m.file_reindexed,ih,CreatedEntry.reindex_comp]
    rfl

theorem Trace.tag {cur : Point f ell} (tr : Trace ancestor cur) :
    (entry cur).created=(entry ancestor).created :=
  congrArg CreatedEntry.created tr.file_reindexed

theorem Trace.read {cur : Point f ell} (tr : Trace ancestor cur)
    (hf : f.Monic) (p : ℕ) (bits : PortAt cur→Bool) :
    (entry cur).read hf p bits=(entry ancestor).read hf p (bits ∘ tr.back.symm) := by
  rw [tr.file_reindexed,CreatedEntry.reindex_read]

#print axioms Move.back_val
#print axioms Move.file_reindexed
#print axioms Trace.literal_exact
#print axioms Trace.file_reindexed
#print axioms Trace.tag
#print axioms Trace.read
end J6R21Ancestor


