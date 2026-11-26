import P5MainBalanceM6SparseParity

/-! Exact source sparse origin arithmetic for arbitrary integer test
arguments and neutral factors. The resulting Lean terminal witness
is integer-valued and correct modulo two, which is enough for M.6.
The hLocal guard in the final adapter is the *local expanded lift*
identity, not an assumed count or terminal residue equality. -/
namespace P5MainBalance.M6.Sparse
open P5MainBalance P5MainBalance.M6 P5MainIterator Polynomial
open scoped BigOperators Classical

noncomputable def sparseEntry (ell : ℕ) : Option ℤ→ℤ[X]
  | none => 1
  | some y => integerSparseFactor ell y

def validTest : Option ℤ→Prop
  | none => True
  | some y => (y:ZMod 2)=0

theorem sparseEntry_mod_two (ell : ℕ) (he : 0<ell) (y : Option ℤ) :
    (sparseEntry ell y).map (Int.castRingHom (ZMod 2)) =
      (if validTest y then (1:(ZMod 2)[X]) else 0) := by
  cases y with
  | none => simp [sparseEntry,validTest]
  | some y =>
    unfold sparseEntry validTest
    rw [sparse_factor_mod_two ell he]
    split_ifs <;> simp

private theorem zmod_two_zero : (2:ZMod 2)=0 := ZMod.natCast_self 2

def integerBit (b : Bool) : ℤ := if b then 1 else 0

theorem source_pin_even (x s : Bool) :
    validTest (some (integerBit x+integerBit s)) ↔ x=s := by
  cases x <;> cases s <;> norm_num [validTest,integerBit]
  all_goals exact zmod_two_zero

theorem source_edge_even (x y : Bool) :
    validTest (some ((1+integerBit x)*(1+integerBit y))) ↔ x=true ∨ y=true := by
  cases x <;> cases y <;> norm_num [validTest,integerBit]
  all_goals exact zmod_two_zero

theorem source_implication_even (x y : Bool) :
    validTest (some (integerBit x*(1+integerBit y))) ↔ x=false ∨ y=true := by
  cases x <;> cases y <;> norm_num [validTest,integerBit]
  all_goals exact zmod_two_zero

section Fold

variable {X F : Type*} [Fintype X] [Fintype F]

noncomputable def acceptedCard (tests : F→X→Option ℤ) : ℕ :=
  Fintype.card {x : X // ∀ f,validTest (tests f x)}

noncomputable def integerAnchor (ell : ℕ) (tests : F→X→Option ℤ) : ℤ[X] :=
  ∑ x,∏ f,sparseEntry ell (tests f x)

set_option maxHeartbeats 7200000 in
theorem integerAnchor_mod_two (ell : ℕ) (he : 0<ell) (tests : F→X→Option ℤ) :
    (integerAnchor ell tests).map (Int.castRingHom (ZMod 2))=C (acceptedCard tests:ZMod 2) := by
  have h (x : X) : (∏ f,(if validTest (tests f x) then (1:(ZMod 2)[X]) else 0))=
      if ∀ f,validTest (tests f x) then 1 else 0 := by
    split_ifs with hh
    · exact Finset.prod_eq_one (fun f _=>if_pos (hh f))
    · obtain ⟨f,hf⟩ := not_forall.mp hh
      exact Finset.prod_eq_zero (Finset.mem_univ f) (if_neg hf)
  unfold integerAnchor acceptedCard
  rw [Polynomial.map_sum]
  simp_rw [Polynomial.map_prod,sparseEntry_mod_two ell he,h]
  rw [←Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,mul_one,←map_natCast C,
    Fintype.card_subtype]

noncomputable def integerRead (ell : ℕ) (tests : F→X→Option ℤ) : ℤ :=
  ∑ s : Fin ell,(integerAnchor ell tests).coeff s

theorem integerRead_mod_two (ell : ℕ) (he : 0<ell) (tests : F→X→Option ℤ) :
    (integerRead ell tests:ZMod 2)=(acceptedCard tests:ZMod 2) := by
  let m := Int.castRingHom (ZMod 2)
  unfold integerRead
  calc
    (m _) = ∑ s : Fin ell,((integerAnchor ell tests).map m).coeff s := by
      rw [map_sum]; simp_rw [coeff_map]
    _ = _ := by
      unfold m
      rw [integerAnchor_mod_two ell he]
      rw [Finset.sum_eq_single (⟨0,he⟩:Fin ell)]
      · exact coeff_C_zero
      · intro k _ hk
        exact coeff_C_ne_zero (fun h=>hk (Fin.ext h))
      · simp

end Fold

variable {E W F Copy I B V : Type*} [Fintype E] [Fintype W] [Fintype F]
  [Fintype Copy] [Fintype I] [Fintype B] [LinearOrder B]

abbrev LocalTest (L : SourceLayout E W F Copy I B) (mark : V↪E) :=
  ∀ f : F,({v : V // signedOwner L mark v=f}→Bool)→(W→Bool)→Option ℤ

set_option maxHeartbeats 9500000 in
theorem sparse_anchor_is_integer (L : SourceLayout E W F Copy I B) (mark : V↪E)
    (t : I→ℚ) (M : Mix Copy I B) (P : SourceRecipe L mark)
    (ell : ℕ) (test : LocalTest L mark)
    (hLocal : ∀ f s x,atAnchorFactor L mark P f s x =
      (sparseEntry ell (test f s x)).map (Int.castRingHom ℚ)) (σ : V→Bool) :
    retainedOrigin ell (actualH L mark t M P σ) =
      (integerRead ell (fun f x=>test f (fun v=>σ v.val) x):ℚ) := by
  have h0 : (actualH L mark t M P σ).coeff 0 =
      (integerAnchor ell (fun f x=>test f (fun v=>σ v.val) x)).map (Int.castRingHom ℚ) := by
    rw [actual_anchor_is_source_sum]
    unfold integerAnchor
    rw [Polynomial.map_sum]
    simp_rw [Polynomial.map_prod]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.prod_congr rfl
    intro f _
    exact hLocal f _ _
  unfold retainedOrigin integerRead
  rw [h0,Int.cast_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [coeff_map]
  rfl

theorem sparse_terminal_witness [Fintype V] [DecidableEq V] (L : SourceLayout E W F Copy I B) (mark : V↪E)
    (t : I→ℚ) (M : Mix Copy I B) (P : SourceRecipe L mark) (graph : Finset (V×V))
    (ell : ℕ) (he : 0<ell) (test : LocalTest L mark)
    (hLocal : ∀ f s x,atAnchorFactor L mark P f s x =
      (sparseEntry ell (test f s x)).map (Int.castRingHom ℚ))
    (hCount : ∀ σ,acceptedCard (fun f x=>test f (fun v=>σ v.val) x) =
      PinnedCNF.modelCount (PinnedCNF.formula graph σ)) :
    ∃ out : (V→Bool)→ℤ,
      (∀ σ,(out σ:ℚ)=retainedOrigin ell (actualH L mark t M P σ)) ∧
      (∀ σ,(out σ:ZMod 2)=(PinnedCNF.modelCount (PinnedCNF.formula graph σ):ZMod 2)) := by
  refine ⟨fun σ=>integerRead ell (fun f x=>test f (fun v=>σ v.val) x),?_,?_⟩
  · exact fun σ=>(sparse_anchor_is_integer L mark t M P ell test hLocal σ).symm
  · intro σ
    rw [integerRead_mod_two ell he,hCount]

#print axioms sparseEntry_mod_two
#print axioms source_pin_even
#print axioms source_edge_even
#print axioms source_implication_even
#print axioms integerAnchor_mod_two
#print axioms integerRead_mod_two
#print axioms sparse_anchor_is_integer
#print axioms sparse_terminal_witness
end P5MainBalance.M6.Sparse
