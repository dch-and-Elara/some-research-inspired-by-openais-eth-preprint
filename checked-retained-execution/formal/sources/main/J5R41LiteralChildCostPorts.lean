import J5R41LiteralChildCostFactors

/-! Reindex the genuine child state by original vertices and their
actual local Boolean ports. The weights are still the original file
entries at their own creation tags, read at p_t. -/
namespace J5R41LiteralChildCost
open scoped Classical BigOperators Polynomial
open Polynomial P11FullPacking J6R10Repack J6R9Recursive J6R9PacketScopes
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2200000

variable {E A B G : Type} [Fintype E] [Fintype A] [Fintype B] [LinearOrder G] [Fintype G]
variable {a : ℕ} {N : Network E A B}
variable (P : PhysicalPacking N a G) (i : Fin a) (g : G)

def rowOwner (q : RowHalf P i g) : RowVertex P i g :=
  ⟨N.row q.val,(row_symbol P i q.val).symm.trans q.prop⟩

def colOwner (q : ColHalf P i g) : ColVertex P i g :=
  ⟨N.col q.val,(col_symbol P i q.val).symm.trans q.prop⟩

def rowChart : (Σ v : RowVertex P i g, RowPort P i g v) ≃ RowHalf P i g where
  toFun q := ⟨q.2.val, (row_symbol P i q.2.val).trans <|
    (congrArg (fun z=>P.rowLabel z i) q.2.prop).trans q.1.prop⟩
  invFun q := ⟨rowOwner P i g q,⟨q.val,rfl⟩⟩
  left_inv := by
    rintro ⟨⟨b,hb⟩,⟨e,he⟩⟩
    cases he
    rfl
  right_inv _ := rfl

def colChart : (Σ v : ColVertex P i g, ColPort P i g v) ≃ ColHalf P i g where
  toFun q := ⟨q.2.val, (col_symbol P i q.2.val).trans <|
    (congrArg (fun z=>P.colLabel z i) q.2.prop).trans q.1.prop⟩
  invFun q := ⟨colOwner P i g q,⟨q.val,rfl⟩⟩
  left_inv := by
    rintro ⟨⟨b,hb⟩,⟨e,he⟩⟩
    cases he
    rfl
  right_inv _ := rfl

abbrev RowAssignments := (v : RowVertex P i g)→RowPort P i g v→Bool
abbrev ColAssignments := (v : ColVertex P i g)→ColPort P i g v→Bool

def rowAssignmentsEquiv : RowAssignments P i g ≃ (RowHalf P i g→Bool) where
  toFun Y e := let w := (rowChart P i g).symm e; Y w.1 w.2
  invFun Y v e := Y (rowChart P i g ⟨v,e⟩)
  left_inv Y := by
    funext v e
    change ((fun w : Σ v : RowVertex P i g,RowPort P i g v=>Y w.1 w.2)
      ((rowChart P i g).symm (rowChart P i g ⟨v,e⟩)))=_
    rw [Equiv.symm_apply_apply]
  right_inv Y := by
    funext e
    exact congrArg Y ((rowChart P i g).apply_symm_apply e)

def colAssignmentsEquiv : ColAssignments P i g ≃ (ColHalf P i g→Bool) where
  toFun X e := let w := (colChart P i g).symm e; X w.1 w.2
  invFun X v e := X (colChart P i g ⟨v,e⟩)
  left_inv X := by
    funext v e
    change ((fun w : Σ v : ColVertex P i g,ColPort P i g v=>X w.1 w.2)
      ((colChart P i g).symm (colChart P i g ⟨v,e⟩)))=_
    rw [Equiv.symm_apply_apply]
  right_inv X := by
    funext e
    exact congrArg X ((colChart P i g).apply_symm_apply e)

def oldChart : RowVertex P i g ⊕ ColVertex P i g ≃ Old (atGroup P i) g where
  toFun a := match a with
    | .inl b => ⟨.inl b.val,b.prop⟩
    | .inr b => ⟨.inr b.val,b.prop⟩
  invFun a := match a with
    | ⟨.inl b,h⟩ => .inl ⟨b,h⟩
    | ⟨.inr b,h⟩ => .inr ⟨b,h⟩
  left_inv := fun s=>by cases s <;> rfl
  right_inv := by rintro ⟨s,h⟩; cases s <;> rfl

def pairedState : ((RowAssignments P i g) × (ColAssignments P i g)) ≃ PhysicalState P i g :=
  Equiv.prodCongr (rowAssignmentsEquiv P i g) (colAssignmentsEquiv P i g)

theorem new_state_row_reads (Y : RowAssignments P i g) (X : ColAssignments P i g)
    (b : RowVertex P i g) (e : RowPort P i g b) :
    (pairedState P i g (Y,X)).1 (rowChart P i g ⟨b,e⟩)=Y b e := by
  exact congrArg (fun u : RowAssignments P i g=>u b e) ((rowAssignmentsEquiv P i g).symm_apply_apply Y)

theorem new_state_col_reads (Y : RowAssignments P i g) (X : ColAssignments P i g)
    (b : ColVertex P i g) (e : ColPort P i g b) :
    (pairedState P i g (Y,X)).2 (colChart P i g ⟨b,e⟩)=X b e := by
  exact congrArg (fun u : ColAssignments P i g=>u b e) ((colAssignmentsEquiv P i g).symm_apply_apply X)

variable {f : ℤ[X]} {ell : ℕ} (p : ℕ) (old : EntryFile f ell N) (hf : f.Monic)

def rowTable (b : RowVertex P i g) (Y : RowPort P i g b→Bool) : Residue f ell p :=
  (old (.inl b.val)).read hf p (fun q=>Y ((rowPortsEquiv N b.val).symm q))

def colTable (b : ColVertex P i g) (X : ColPort P i g b→Bool) : Residue f ell p :=
  (old (.inr b.val)).read hf p (fun q=>X ((colPortsEquiv N b.val).symm q))

theorem old_original_row_input (Y : RowAssignments P i g) (X : ColAssignments P i g)
    (b : RowVertex P i g) :
    restrictOriginal N (atGroup P i) g (oldChart P i g (.inl b))
      ((stateEquiv P i g).symm (pairedState P i g (Y,X))) =
      fun q=>Y b ((rowPortsEquiv N b.val).symm q) := by
  funext q
  rcases q with ⟨q,hq⟩
  cases q with
  | inr e => exact nomatch hq
  | inl e =>
    have he : N.row e=b.val := Sum.inl.inj hq
    let p₀ : RowPort P i g b := ⟨e,he⟩
    let j := rowChart P i g ⟨b,p₀⟩
    let v := pairedState P i g (Y,X)
    let x := (stateEquiv P i g).symm v
    have r := state_reads_row P i g x e j.prop
    dsimp only [x] at r
    rw [(stateEquiv P i g).apply_symm_apply] at r
    exact r.symm.trans (new_state_row_reads P i g Y X b p₀)

theorem old_original_col_input (Y : RowAssignments P i g) (X : ColAssignments P i g)
    (b : ColVertex P i g) :
    restrictOriginal N (atGroup P i) g (oldChart P i g (.inr b))
      ((stateEquiv P i g).symm (pairedState P i g (Y,X))) =
      fun q=>X b ((colPortsEquiv N b.val).symm q) := by
  funext q
  rcases q with ⟨q,hq⟩
  cases q with
  | inl e => exact nomatch hq
  | inr e =>
    have he : N.col e=b.val := Sum.inr.inj hq
    let p₀ : ColPort P i g b := ⟨e,he⟩
    let j := colChart P i g ⟨b,p₀⟩
    let v := pairedState P i g (Y,X)
    let x := (stateEquiv P i g).symm v
    have r := state_reads_col P i g x e j.prop
    dsimp only [x] at r
    rw [(stateEquiv P i g).apply_symm_apply] at r
    exact r.symm.trans (new_state_col_reads P i g Y X b p₀)

theorem old_vertex_tables_realized (Y : RowAssignments P i g) (X : ColAssignments P i g) :
    oldState P i g p old hf (pairedState P i g (Y,X)) =
      (∏ b, rowTable P i g p old hf b (Y b)) *
      ∏ b,colTable P i g p old hf b (X b) := by
  unfold oldState
  let v := pairedState P i g (Y,X)
  let val (d : Old (atGroup P i) g) :=
    (old d.val).read hf p (restrictOriginal N (atGroup P i) g d ((stateEquiv P i g).symm v))
  change (∏ d,val d)=_
  rw [←Fintype.prod_equiv (oldChart P i g) (fun s=>val (oldChart P i g s)) val (by intro; rfl),
    Fintype.prod_sum_type]
  congr 1
  · refine Finset.prod_congr rfl fun b _=>?_
    change (old (.inl b.val)).read hf p
      (restrictOriginal N (atGroup P i) g (oldChart P i g (.inl b)) ((stateEquiv P i g).symm v))=_
    rw [old_original_row_input P i g Y X b]
    rfl
  · refine Finset.prod_congr rfl fun b _=>?_
    change (old (.inr b.val)).read hf p
      (restrictOriginal N (atGroup P i) g (oldChart P i g (.inr b)) ((stateEquiv P i g).symm v))=_
    rw [old_original_col_input P i g Y X b]
    rfl

#print axioms rowChart
#print axioms colChart
#print axioms new_state_row_reads
#print axioms new_state_col_reads
#print axioms old_original_row_input
#print axioms old_original_col_input
#print axioms old_vertex_tables_realized
end
end J5R41LiteralChildCost
