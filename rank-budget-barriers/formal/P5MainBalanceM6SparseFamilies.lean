import P5MainBalanceM6SparseAnchor
import P5MainBalanceM6DirectChart

/-! The actual two sparse-clause reductions. Tests have real unary,
positive-edge, implication or neutral shape. Their parity count is
identified with the original pinned graph independently of any assumed
terminal equality. The last adapter leaves local compiled lift equality
explicit. -/
namespace P5MainBalance.M6.Sparse
open P5MainBalance P5MainBalance.M6 P5MainIterator Polynomial
open scoped BigOperators Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev UFactor (graph : Finset (V×V)) := (V⊕graph)⊕V
abbrev UPort (graph : Finset (V×V)) := (V⊕(graph×Bool))⊕V
abbrev CFactor (graph : Finset (V×V)) := Direct.Factor graph⊕(V×Fin 4)
abbrev CPort (graph : Finset (V×V)) := MainClonedCNF.Port graph⊕(V×Fin 4)

omit [Fintype V] [DecidableEq V] in
def unclonedTests (graph : Finset (V×V)) (σ : V→Bool) :
    UFactor graph→(V→Bool)→Option ℤ
  | .inl (.inl v), x => some (integerBit (x v)+integerBit (σ v))
  | .inl (.inr e), x => some ((1+integerBit (x e.val.1))*(1+integerBit (x e.val.2)))
  | .inr _, _ => none

omit [Fintype V] [DecidableEq V] in
def clonedTests (graph : Finset (V×V)) (left right : graph→Fin 4) (σ : V→Bool) :
    CFactor graph→(V×Fin 4→Bool)→Option ℤ
  | .inl (.inl v), x => some (integerBit (x (v,0))+integerBit (σ v))
  | .inl (.inr (.inl e)), x =>
      some ((1+integerBit (x (e.val.1,left e)))*(1+integerBit (x (e.val.2,right e))))
  | .inl (.inr (.inr (v,i))), x => some (integerBit (x (v,i))*(1+integerBit (x (v,i+1))))
  | .inr _, _ => none

omit [DecidableEq V] in
theorem uncloned_tests_sat (graph : Finset (V×V)) (σ x : V→Bool) :
    (∀ f,validTest (unclonedTests graph σ f x)) ↔ Std.Sat.CNF.Sat x (PinnedCNF.formula graph σ) := by
  rw [PinnedCNF.sat_iff]
  constructor
  · intro h
    have hx : x=σ := funext (fun v=>source_pin_even (x v) (σ v) |>.mp (h (.inl (.inl v))))
    refine ⟨hx,fun e he=>?_⟩
    simpa only [hx] using (source_edge_even (x e.1) (x e.2)).mp (h (.inl (.inr ⟨e,he⟩)))
  · rintro ⟨rfl,he⟩ f
    rcases f with (v|e)|v
    · exact (source_pin_even _ _).mpr rfl
    · exact (source_edge_even _ _).mpr (he e.val e.property)
    · trivial

set_option maxHeartbeats 9000000 in
omit [DecidableEq V] in
theorem cloned_tests_sat (graph : Finset (V×V)) (left right : graph→Fin 4)
    (σ : V→Bool) (x : V×Fin 4→Bool) :
    (∀ f,validTest (clonedTests graph left right σ f x)) ↔
      Std.Sat.CNF.Sat x (MainClonedCNF.formula graph left right σ) := by
  rw [MainClonedCNF.sat_iff]
  constructor
  · intro h
    have hc (v : V) : Std.Sat.CNF.Sat x (MainClonedCNF.cycle v) := by
      have ht (i : Fin 4) : x (v,i)=false ∨ x (v,i+1)=true :=
        (source_implication_even _ _).mp (h (.inl (.inr (.inr (v,i)))))
      simpa [MainClonedCNF.cycle,Std.Sat.CNF.sat_def] using And.intro (ht 0) (And.intro (ht 1) (And.intro (ht 2) (ht 3)))
    have hp (v : V) : x (v,0)=σ v := (source_pin_even _ _).mp (h (.inl (.inl v)))
    have hEq : x=fun v=>σ v.1 := by
      funext v
      exact ((MainClonedCNF.cycle_sat v.1 x).mp (hc v.1) v.2).trans (hp v.1)
    refine ⟨hEq,fun e he=>?_⟩
    let a : graph := ⟨e,he⟩
    have hF := (source_edge_even _ _).mp (h (.inl (.inr (.inl a))))
    simpa only [hEq] using hF
  · rintro ⟨rfl,he⟩ f
    rcases f with (v|e|⟨v,i⟩)|y
    · exact (source_pin_even _ _).mpr rfl
    · exact (source_edge_even _ _).mpr (he e.val e.property)
    · apply (source_implication_even _ _).mpr
      cases σ v <;> simp
    · trivial

private theorem acceptedCount_formula {W F : Type*} [Fintype W] [Fintype F]
    (ix : Fintype (W→Bool)) (test : F→(W→Bool)→Option ℤ) (formula : Std.Sat.CNF W)
    (hh : ∀ x,(∀ f,validTest (test f x)) ↔ Std.Sat.CNF.Sat x formula) :
    @acceptedCard (W→Bool) F ix _ test=PinnedCNF.modelCount formula := by
  letI : Fintype (W→Bool) := ix
  unfold acceptedCard PinnedCNF.modelCount
  rw [Fintype.card_subtype]
  congr 1
  ext x
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  exact (hh x).trans (Std.Sat.CNF.sat_def _ _)

set_option maxHeartbeats 2500000 in
omit [DecidableEq V] in
theorem uncloned_sparse_count (graph : Finset (V×V)) (σ : V→Bool) (ix : Fintype (V→Bool)) :
    @acceptedCard (V→Bool) (UFactor graph) ix _ (unclonedTests graph σ)=
      PinnedCNF.modelCount (PinnedCNF.formula graph σ) :=
  acceptedCount_formula ix _ _ (uncloned_tests_sat graph σ)

set_option maxHeartbeats 2500000 in
omit [DecidableEq V] in
theorem cloned_sparse_count (graph : Finset (V×V)) (left right : graph→Fin 4) (σ : V→Bool)
    (ix : Fintype (V×Fin 4→Bool)) :
    @acceptedCard (V×Fin 4→Bool) (CFactor graph) ix _ (clonedTests graph left right σ)=
      PinnedCNF.modelCount (PinnedCNF.formula graph σ) :=
  (acceptedCount_formula ix _ _ (cloned_tests_sat graph left right σ)).trans
    (MainClonedCNF.modelCount_cloned graph left right σ)

variable {Copy I B : Type*} [Fintype Copy] [Fintype I] [Fintype B] [LinearOrder B]

noncomputable def uncloned_local (graph : Finset (V×V))
    (L : SourceLayout (UPort graph) V (UFactor graph) Copy I B)
    (mark : V↪UPort graph) (pin : ∀ v,signedOwner L mark v=(.inl (.inl v):UFactor graph)) :
    LocalTest L mark
  | .inl (.inl v), s, x => some (integerBit (x v)+integerBit (s ⟨v,pin v⟩))
  | .inl (.inr e), _, x => some ((1+integerBit (x e.val.1))*(1+integerBit (x e.val.2)))
  | .inr _, _, _ => none

noncomputable def cloned_local (graph : Finset (V×V)) (left right : graph→Fin 4)
    (L : SourceLayout (CPort graph) (V×Fin 4) (CFactor graph) Copy I B)
    (mark : V↪CPort graph) (pin : ∀ v,signedOwner L mark v=(.inl (.inl v):CFactor graph)) :
    LocalTest L mark
  | .inl (.inl v), s, x => some (integerBit (x (v,0))+integerBit (s ⟨v,pin v⟩))
  | .inl (.inr (.inl e)), _, x =>
      some ((1+integerBit (x (e.val.1,left e)))*(1+integerBit (x (e.val.2,right e))))
  | .inl (.inr (.inr (v,i))), _, x => some (integerBit (x (v,i))*(1+integerBit (x (v,i+1))))
  | .inr _, _, _ => none

omit [Fintype V] [DecidableEq V] [Fintype Copy] [Fintype I] [Fintype B] in
theorem uncloned_local_exact (graph : Finset (V×V))
    (L : SourceLayout (UPort graph) V (UFactor graph) Copy I B)
    (mark : V↪UPort graph) (pin : ∀ v,signedOwner L mark v=(.inl (.inl v):UFactor graph))
    (σ : V→Bool) :
    (fun f x=>uncloned_local graph L mark pin f (fun v=>σ v.val) x)=unclonedTests graph σ := by
  funext f x
  rcases f with (v|e)|v <;> rfl

omit [Fintype V] [DecidableEq V] [Fintype Copy] [Fintype I] [Fintype B] in
theorem cloned_local_exact (graph : Finset (V×V)) (left right : graph→Fin 4)
    (L : SourceLayout (CPort graph) (V×Fin 4) (CFactor graph) Copy I B)
    (mark : V↪CPort graph) (pin : ∀ v,signedOwner L mark v=(.inl (.inl v):CFactor graph))
    (σ : V→Bool) :
    (fun f x=>cloned_local graph left right L mark pin f (fun v=>σ v.val) x)=clonedTests graph left right σ := by
  funext f x
  rcases f with (v|e|⟨v,i⟩)|v <;> rfl

set_option maxHeartbeats 10000000 in
theorem uncloned_terminal_from_lift (graph : Finset (V×V))
    (L : SourceLayout (UPort graph) V (UFactor graph) Copy I B)
    (mark : V↪UPort graph) (pin : ∀ v,signedOwner L mark v=(.inl (.inl v):UFactor graph))
    (t : I→ℚ) (M : Mix Copy I B) (P : SourceRecipe L mark)
    (ell : ℕ) (he : 0<ell)
    (hLocal : ∀ f s x,atAnchorFactor L mark P f s x =
      (sparseEntry ell (uncloned_local graph L mark pin f s x)).map (Int.castRingHom ℚ)) :
    ∃ out : (V→Bool)→ℤ,
      (∀ σ,(out σ:ℚ)=retainedOrigin ell (actualH L mark t M P σ)) ∧
      (∀ σ,(out σ:ZMod 2)=(PinnedCNF.modelCount (PinnedCNF.formula graph σ):ZMod 2)) :=
  sparse_terminal_witness L mark t M P graph ell he (uncloned_local graph L mark pin)
    hLocal (fun σ=>by rw [uncloned_local_exact graph L mark pin σ]; exact uncloned_sparse_count graph σ _)

set_option maxHeartbeats 10000000 in
theorem cloned_terminal_from_lift (graph : Finset (V×V)) (left right : graph→Fin 4)
    (L : SourceLayout (CPort graph) (V×Fin 4) (CFactor graph) Copy I B)
    (mark : V↪CPort graph) (pin : ∀ v,signedOwner L mark v=(.inl (.inl v):CFactor graph))
    (t : I→ℚ) (M : Mix Copy I B) (P : SourceRecipe L mark)
    (ell : ℕ) (he : 0<ell)
    (hLocal : ∀ f s x,atAnchorFactor L mark P f s x =
      (sparseEntry ell (cloned_local graph left right L mark pin f s x)).map (Int.castRingHom ℚ)) :
    ∃ out : (V→Bool)→ℤ,
      (∀ σ,(out σ:ℚ)=retainedOrigin ell (actualH L mark t M P σ)) ∧
      (∀ σ,(out σ:ZMod 2)=(PinnedCNF.modelCount (PinnedCNF.formula graph σ):ZMod 2)) :=
  sparse_terminal_witness L mark t M P graph ell he (cloned_local graph left right L mark pin)
    hLocal (fun σ=>by rw [cloned_local_exact graph left right L mark pin σ]; exact cloned_sparse_count graph left right σ _)

#print axioms uncloned_tests_sat
#print axioms cloned_tests_sat
#print axioms uncloned_sparse_count
#print axioms cloned_sparse_count
#print axioms uncloned_local_exact
#print axioms cloned_local_exact
#print axioms uncloned_terminal_from_lift
#print axioms cloned_terminal_from_lift
end P5MainBalance.M6.Sparse
