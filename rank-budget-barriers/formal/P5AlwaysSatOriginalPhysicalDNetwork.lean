import P5AlwaysSatOriginalPhysicalFibre
import J6R10Repack

/-! The identical cloned CNF enters the clause route of Appendix D.
Its actual old vertices are the copy attachments and clause tables;
its new vertices are precisely one per literal occurrence. -/
namespace Paper5.AlwaysSatOriginal.Physical
open scoped BigOperators Classical
variable {V : Type*} [Fintype V]
variable (E : Finset (V×V)) (T : Finset V)

abbrev DWire := ClausePort E T×Bool
abbrev DVertex := Port E T ⊕ CloneFactor E T

noncomputable def dNetwork : J6R10Repack.Network (DWire E T) (DVertex E T) (ClausePort E T) where
  row p := if p.2 then .inr (portFactor E T p.1) else .inl (portOwner E T p.1)
  col p := p.1

def dMarked : V↪DWire E T :=
  ⟨fun v=>(marked E T v,true),fun _ _ h=>(marked E T).injective (congrArg Prod.fst h)⟩

@[simp] theorem d_marked_row (v : V) :
    (dNetwork E T).row (dMarked E T v)=.inr (.inl (.inl v)) := rfl

@[simp] theorem d_marked_col (v : V) :
    (dNetwork E T).col (dMarked E T v)=marked E T v := rfl

noncomputable def varEnd (v : Port E T) :
    {p : DWire E T // (dNetwork E T).row p=.inl v} ≃
      {p : ClausePort E T // portOwner E T p=v} where
  toFun := fun ⟨⟨p,b⟩,hp⟩=>⟨p,by
    cases b
    · exact Sum.inl.inj hp
    · simp [dNetwork] at hp⟩
  invFun p := ⟨(p.val,false),by simpa [dNetwork] using p.property⟩
  left_inv := by
    rintro ⟨⟨p,b⟩,hp⟩
    cases b
    · rfl
    · simp [dNetwork] at hp
  right_inv _ := rfl

def clauseEnd (f : CloneFactor E T) :
    {p : DWire E T // (dNetwork E T).row p=.inr f} ≃ FactorFibre E T f where
  toFun := fun ⟨⟨p,b⟩,hp⟩=>⟨p,by
    cases b
    · simp [dNetwork] at hp
    · exact Sum.inr.inj hp⟩
  invFun p := ⟨(p.val,true),by simpa [dNetwork] using p.property⟩
  left_inv := by
    rintro ⟨⟨p,b⟩,hp⟩
    cases b
    · simp [dNetwork] at hp
    · rfl
  right_inv _ := rfl

def subdivEnd (p : ClausePort E T) :
    {w : DWire E T // (dNetwork E T).col w=p} ≃ Bool where
  toFun w := w.val.2
  invFun b := ⟨(p,b),rfl⟩
  left_inv w := Subtype.ext (Prod.ext w.property.symm rfl)
  right_inv _ := rfl

theorem d_attachment_degree (v : Port E T) :
    Nat.card {p : DWire E T // (dNetwork E T).row p=.inl v} =
      if v=bonusZeroPort E T then 1 else 3 := by
  rw [Nat.card_congr (varEnd E T v),physical_copy_degree]

theorem d_clause_degree (s : V→Bool) (f : CloneFactor E T) :
    Nat.card {p : DWire E T // (dNetwork E T).row p=.inr f} =
      (clonedClause E T s f).length := by
  rw [Nat.card_congr (clauseEnd E T f),factor_fibre_card E T s]

theorem d_subdivision_degree (p : ClausePort E T) :
    Nat.card {w : DWire E T // (dNetwork E T).col w=p}=2 := by
  rw [Nat.card_congr (subdivEnd E T p)]
  simp [Nat.card_eq_fintype_card]

theorem d_row_degree_le (v : DVertex E T) :
    Nat.card {p : DWire E T // (dNetwork E T).row p=v}≤3 := by
  rcases v with v|v
  · rw [Nat.card_congr (varEnd E T v)]
    exact physical_copy_degree_le E T v
  · rw [Nat.card_congr (clauseEnd E T v)]
    exact (factor_fibre_degree E T v).2

noncomputable def dSize : ℕ := Fintype.card (Port E T)+Fintype.card (CloneFactor E T)
noncomputable def dWires : ℕ := Fintype.card (DWire E T)

theorem d_size_literal (s : V→Bool) :
    dSize E T=Fintype.card (Port E T)+(cloneCNF E T s).length := by
  unfold dSize cloneCNF
  rw [List.length_map,Finset.length_toList,Finset.card_univ]

theorem d_wire_exact [DecidableEq V] (s : V→Bool)
    (hC : ∀ v,GraphCutMoments.degree E v=3) :
    dWires E T=33*Fintype.card V+24*T.card+8 := by
  unfold dWires DWire
  rw [Fintype.card_prod,Fintype.card_bool,Nat.mul_comm]
  exact (original_physical_sizes E T s hC).2.1

theorem d_wire_quarter_upper [DecidableEq V]
    (hC : ∀ v,GraphCutMoments.degree E v=3) (hT : T.card≤Fintype.card V/4) :
    dWires E T≤39*Fintype.card V+8 := by
  rw [d_wire_exact E T (fun _=>false) hC]
  omega

theorem d_size_exact [DecidableEq V] (hC : ∀ v,GraphCutMoments.degree E v=3) :
    2*dSize E T=27*Fintype.card V+20*T.card+8 := by
  rw [d_size_literal E T (fun _=>false),(original_physical_sizes E T (fun _=>false) hC).1,
    original_port_card]
  have he := GraphCutMoments.regular_edge_count E 3 hC
  omega

theorem d_size_and_wire_range [DecidableEq V]
    (hC : ∀ v,GraphCutMoments.degree E v=3) :
    Fintype.card V≤dSize E T ∧ dSize E T≤dWires E T ∧ dWires E T≤3*dSize E T := by
  have hs := d_size_exact E T hC
  have hw := d_wire_exact E T (fun _=>false) hC
  omega

#print axioms dNetwork
#print axioms d_marked_row
#print axioms d_marked_col
#print axioms d_attachment_degree
#print axioms d_clause_degree
#print axioms d_subdivision_degree
#print axioms d_row_degree_le
#print axioms d_size_literal
#print axioms d_wire_exact
#print axioms d_wire_quarter_upper
#print axioms d_size_exact
#print axioms d_size_and_wire_range
end Paper5.AlwaysSatOriginal.Physical