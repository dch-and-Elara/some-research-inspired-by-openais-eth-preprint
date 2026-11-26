import P5AlwaysSatOriginalTaylorCanonical
import P5AlwaysSatOriginalTaylorLift
import P5MainBalanceM6SparseAnchor

/-! Literal source adapter for the cloned guarded CNF: the sparse
canonical 0/1 lift, its width-three typed expansion, true integer
origin and old cover parity. The neutral factors never acquire tests. -/
namespace Paper5.AlwaysSatOriginal.Physical.Taylor
open P5MainBalance P5MainIterator P5MainBalance.M6 P5MainBalance.M6.Sparse Polynomial
open scoped BigOperators Classical Polynomial

variable {V Copy I B : Type*} [Fintype V] [LinearOrder B]
variable {E : Finset (V×V)} {T : Finset V}
variable (L : SourceLayout (SparsePort E T) (Port E T) (SparseFactor E T) Copy I B)
variable (ho : L.placement.owner=sparseOwner E T) (hf : L.factor=sparseFactor E T)

local notation "D" => sparseChart L ho hf

noncomputable def sparseCount : SparseFactor E T→ℕ
  | .inl f => Fintype.card (Choices ((D).literals f))
  | .inr _ => 0

noncomputable def sparseWords :
    (f : SparseFactor E T)→Fin (sparseCount L ho hf f)→List {e : SparsePort E T // L.factor e=f}
  | .inl f, i => (subword ((D).literals f) (choiceCode ((D).literals f) i)).map ((D).scoped f)
  | .inr _, i => Fin.elim0 i

noncomputable def sparseWeights :
    (f : SparseFactor E T)→({v : V // signedOwner L (D).mark v=f}→Bool)→Fin (sparseCount L ho hf f)→ℚ
  | .inl f, s, i => wordWeight ((D).literals f) ((D).localSign f s) supportLetter
      (choiceCode ((D).literals f) i)
  | .inr _, _, i => Fin.elim0 i

noncomputable def sparseInput : PrintedLift L (D).mark 3 where
  neutral := fun f => match f with
    | .inl _ => false
    | .inr _ => true
  number := sparseCount L ho hf
  terms := sparseWords L ho hf
  weight := sparseWeights L ho hf
  small := by
    rintro (f|w) i
    · change ((subword ((D).literals f) (choiceCode ((D).literals f) i)).map ((D).scoped f)).length≤3
      rw [List.length_map]
      exact (subword_length _ _).trans ((D).literal_count_le f)
    · exact Fin.elim0 i

theorem sparse_nominal_base : (∑ f,(sparseInput L ho hf).base f)=3*Fintype.card (CloneFactor E T) := by
  rw [Fintype.sum_sum_type]
  simp only [PrintedLift.base,sparseInput]
  simp [Nat.mul_comm]

noncomputable def sourceIntegerLift (f : CloneFactor E T) (s : (D).Signs f) :
    MvPolynomial (Port E T) ℤ :=
  integralWordLift ((D).literals f) (fun p=>portOwner E T p.val) ((D).localSign f s)

theorem source_integer_map (f : CloneFactor E T) (σ : V→Bool) :
    MvPolynomial.map (Int.castRingHom (ZMod 2)) (sourceIntegerLift L ho hf f (fun v=>σ v.val))=
      sparseTest E T σ f := by
  rw [sourceIntegerLift,lift_map_field,(D).literal_word_global]
  rfl

theorem source_integer_canonical [DecidableEq V] [Nonempty V]
    (hC : ∀ v,GraphCutMoments.degree E v=3) (f : CloneFactor E T) (σ : V→Bool)
    (u : Port E T→₀ℕ) :
    (sourceIntegerLift L ho hf f (fun v=>σ v.val)).coeff u=((sparseTest E T σ f).coeff u).val := by
  have hNoDup : ((D).literals f).Nodup := by
    apply List.Nodup.of_map (f:=Subtype.val)
    change ((scopePorts E T f).map Subtype.val).Nodup
    rw [scope_projects]
    exact port_list_nodup E T f
  have hu : Function.Injective (fun i : Fin ((D).literals f).length =>
      portOwner E T (((D).literals f).get i).val) := by
    intro i j h
    apply (List.nodup_iff_injective_get.mp hNoDup)
    apply Subtype.ext
    refine port_owner_injective_at_clause E T hC _ _ ?_ h
    exact (((D).literals f).get i).property.trans (((D).literals f).get j).property.symm
  unfold sourceIntegerLift
  rw [literal_canonical_lift _ _ _ hu,(D).literal_word_global]
  rfl

theorem sparse_literal_test {R : Type*} [CommRing R] (φ : ℚ[X]→+*R)
    (f : CloneFactor E T) (s : (D).Signs f) (A : SparsePort E T→R) :
    (sparseInput L ho hf).test φ (.inl f) s (fun e=>A e.val)=
      letters ((D).literals f) (fun p=>if (D).localSign f s p then 1+A (.inl p.val) else A (.inl p.val)) := by
  unfold PrintedLift.test sumMonomials
  change (∑ i : Fin (Fintype.card (Choices ((D).literals f))),
      (φ.comp Polynomial.C) (wordWeight ((D).literals f) ((D).localSign f s)
          supportLetter (choiceCode ((D).literals f) i))*
        letters ((subword ((D).literals f) (choiceCode ((D).literals f) i)).map ((D).scoped f))
          (fun p=>A p.val))=_
  have h (l : List (FactorFibre E T f)) :
      letters (l.map ((D).scoped f)) (fun p=>A p.val)=letters l (fun p=>A (.inl p.val)) := by
    unfold letters
    rw [List.map_map]
    rfl
  simp_rw [h,support_word_map]
  rw [(choiceCode ((D).literals f)).sum_comp (fun p=>
    wordWeight ((D).literals f) ((D).localSign f s) supportLetter p *
      letters (subword ((D).literals f) p) (fun q=>A (.inl q.val)))]
  exact support_word_expansion _ _ _

noncomputable def sparseAnchorValue (f : CloneFactor E T) (s : (D).Signs f) (x : Port E T→Bool) : ℤ :=
  MvPolynomial.eval (integerBit ∘ x) (sourceIntegerLift L ho hf f s)

theorem sparse_literal_test_origin (f : CloneFactor E T) (s : (D).Signs f) (x : Port E T→Bool) :
    (sparseInput L ho hf).test (RingHom.id ℚ[X]) (.inl f) s
      (fun e=>Polynomial.C (qbits x (L.placement.owner e.val))) =
      Polynomial.C (sparseAnchorValue L ho hf f s x:ℚ) := by
  rw [sparse_literal_test L ho hf (RingHom.id ℚ[X]) f s
    (fun e : SparsePort E T => Polynomial.C (qbits x (L.placement.owner e)))]
  unfold sparseAnchorValue sourceIntegerLift
  rw [evaluate_our_lift,support_word_expansion]
  let ψ : ℤ→+*ℚ[X] := Polynomial.C.comp (Int.castRingHom ℚ)
  change _=ψ (letters ((D).literals f) _)
  rw [←letters_mapped]
  unfold letters
  congr 1
  apply List.map_congr_left
  intro p _
  have he := congrFun ho (.inl p.val)
  change L.placement.owner (.inl p.val)=portOwner E T p.val at he
  rw [he]
  cases hp : (D).localSign f s p <;> cases hb : x (portOwner E T p.val) <;>
    simp [hp,hb,ψ,integerBit,qbits,BooleanMeasurement.bit]
  simpa only [map_one,one_add_one_eq_two] using
    (map_add (Polynomial.C : ℚ →+* ℚ[X]) 1 1).symm

noncomputable def generatedTest : LocalTest L (D).mark
  | .inl f,s,x => some (sparseAnchorValue L ho hf f s x)
  | .inr _,_,_ => none

theorem generated_test_anchor (ell : ℕ) (f : SparseFactor E T)
    (s : {v : V // signedOwner L (D).mark v=f}→Bool) (x : Port E T→Bool) :
    atAnchorFactor L (D).mark ((sparseInput L ho hf).compile ell) f s x =
      (sparseEntry ell (generatedTest L ho hf f s x)).map (Int.castRingHom ℚ) := by
  rw [(sparseInput L ho hf).anchor_literal]
  rcases f with f|w
  · change liftedTest (RingHom.id ℚ[X]) ell _=(integerSparseFactor ell
      (sparseAnchorValue L ho hf f s x)).map _
    rw [sparse_literal_test_origin,liftedTest_at_constant]
  · change (1:ℚ[X])=(1:ℤ[X]).map _
    rw [Polynomial.map_one]

theorem sparse_anchor_test_mod2 (f : CloneFactor E T) (σ : V→Bool) (x : Port E T→Bool) :
    (sparseAnchorValue L ho hf f (fun v=>σ v.val) x:ZMod 2)=
      MvPolynomial.eval (bitValue ∘ x) (sparseTest E T σ f) := by
  let ψ := Int.castRingHom (ZMod 2)
  unfold sparseAnchorValue
  change ψ (MvPolynomial.eval (integerBit ∘ x) _) = _
  rw [MvPolynomial.eval₂_comp,←MvPolynomial.eval_map,source_integer_map]
  have he : (⇑ψ ∘ integerBit ∘ x) = (bitValue ∘ x) := by
    funext w
    cases hw : x w <;> simp [ψ,hw,integerBit,bitValue]
  rw [he]

theorem generated_tests_count (σ : V→Bool) :
    acceptedCard (fun f x=>generatedTest L ho hf f (fun v=>σ v.val) x)=
      PinnedCNF.modelCount (cloneCNF E T σ) := by
  unfold acceptedCard PinnedCNF.modelCount
  rw [Fintype.card_subtype]
  congr 1
  ext x
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,←Std.Sat.CNF.sat_def]
  rw [←sparse_tests_exact E T σ x]
  constructor
  · intro hx f
    have he := hx (.inl f)
    change (sparseAnchorValue L ho hf f (fun v=>σ v.val) x:ZMod 2)=0 at he
    rwa [sparse_anchor_test_mod2] at he
  · intro hx f
    cases f with
    | inl f =>
      change (sparseAnchorValue L ho hf f (fun v=>σ v.val) x:ZMod 2)=0
      rw [sparse_anchor_test_mod2]
      exact hx f
    | inr _ => trivial

variable [Fintype Copy] [Fintype I] [Fintype B]

theorem sparse_terminal_witness (ell : ℕ) (he : 0<ell) (t : I→ℚ) (M : Mix Copy I B) :
    ∃ out : (V→Bool)→ℤ,
      (∀ σ,(out σ:ℚ)=retainedOrigin ell
        (actualH L (D).mark t M ((sparseInput L ho hf).compile ell) σ)) ∧
      (∀ σ,(out σ:ZMod 2)=(PinnedCNF.modelCount (PinnedCNF.formula E σ):ZMod 2)) := by
  refine ⟨fun σ=>integerRead ell (fun f x=>generatedTest L ho hf f (fun v=>σ v.val) x),?_,?_⟩
  · intro σ
    exact (sparse_anchor_is_integer L (D).mark t M ((sparseInput L ho hf).compile ell)
      ell (generatedTest L ho hf) (generated_test_anchor L ho hf ell) σ).symm
  · intro σ
    rw [integerRead_mod_two ell he,generated_tests_count,←ZMod.natCast_mod
      (PinnedCNF.modelCount (cloneCNF E T σ)) 2,cloned_count_parity]

#print axioms sparse_nominal_base
#print axioms source_integer_map
#print axioms source_integer_canonical
#print axioms sparse_literal_test
#print axioms sparse_literal_test_origin
#print axioms generated_test_anchor
#print axioms sparse_anchor_test_mod2
#print axioms generated_tests_count
#print axioms sparse_terminal_witness
end Paper5.AlwaysSatOriginal.Physical.Taylor