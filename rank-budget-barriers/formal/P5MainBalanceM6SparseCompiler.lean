import P5MainBalanceM6SparseAffine
import P5MainBalanceM6SparseMonomial
import P5MainBalanceM6SparseAnchor

/-! Typed compilation of the actual e_j(L)h(L)^jV^j local polynomial.
A neutral singleton contributes exactly 1; a real row only reads its
own physically typed test occurrences. -/
namespace P5MainBalance.M6.Sparse
open P5MainBalance P5MainBalance.M6 P5MainIterator Polynomial
open scoped BigOperators Classical Polynomial

variable {E W F Copy I B V : Type*} [LinearOrder B]
variable {L : SourceLayout E W F Copy I B} {mark : V↪E}

structure LiftSource (L : SourceLayout E W F Copy I B) (mark : V↪E) where
  neutral : F→Bool
  number : F→ℕ
  terms : ∀ f,Fin (number f)→List {e : E // L.factor e=f}
  weight : ∀ f,({v : V // signedOwner L mark v=f}→Bool)→Fin (number f)→ℚ
  small : ∀ f k,(terms f k).length≤2

def LiftSource.base (P : LiftSource L mark) (f : F) : ℕ := if P.neutral f then 0 else 2

abbrev Modes (ell c : ℕ) := Σ a : Fin ell,Choice c a.val

noncomputable def LiftSource.modeCode (P : LiftSource L mark) (ell : ℕ) (f : F) :
    Fin (Fintype.card (Modes ell (P.number f))) ≃ Modes ell (P.number f) :=
  (Fintype.equivFin _).symm

noncomputable def LiftSource.modeList (P : LiftSource L mark)
    (ell : ℕ) (f : F) (q : Modes ell (P.number f)) : List {e : E // L.factor e=f} :=
  if P.neutral f then [] else modeTerms (P.terms f) q.2

noncomputable def LiftSource.modeCoeff (P : LiftSource L mark)
    (ell : ℕ) (f : F) (s : {v : V // signedOwner L mark v=f}→Bool)
    (q : Modes ell (P.number f)) : ℚ[X] :=
  if P.neutral f then 0 else monomial q.1.val
    (modeWeight (P.weight f s) ((printedE ell q.1).coeff 0:ℚ) ((printedE ell q.1).coeff 1:ℚ) q.2)

noncomputable def LiftSource.termList (P : LiftSource L mark) (ell : ℕ) (f : F) :
    Fin (Fintype.card (Modes ell (P.number f))+1)→List {e : E // L.factor e=f} :=
  Fin.cases [] (fun k=>P.modeList ell f (P.modeCode ell f k))

noncomputable def LiftSource.compile (P : LiftSource L mark) (ell : ℕ) :
    SourceRecipe L mark where
  count f := Fintype.card (Modes ell (P.number f))+1
  degree f i := (P.termList ell f i).length
  read f i j := (P.termList ell f i).get j
  coeff f i s := Fin.cases (if P.neutral f then 1 else 0)
    (fun k=>P.modeCoeff ell f s (P.modeCode ell f k)) i

set_option maxHeartbeats 9000000 in
theorem LiftSource.compile_graded (P : LiftSource L mark) (ell : ℕ) :
    (P.compile ell).graded P.base 4 := by
  intro f k
  refine Fin.cases ?_ (fun i=>?_) k
  · intro s j hj
    change (P.termList ell f 0).length≤P.base f+4*j
    simp [LiftSource.termList]
  · intro s j hj
    let q := P.modeCode ell f i
    change (P.modeList ell f q).length≤P.base f+4*j
    by_cases h : P.neutral f
    · simp [LiftSource.modeList,h]
    · have hs : q.1.val=j := by
        contrapose! hj
        change (P.modeCoeff ell f s q).coeff j=0
        simp [LiftSource.modeCoeff,h,coeff_monomial,hj]
      simpa only [LiftSource.modeList,LiftSource.base,if_neg h,hs] using
        modeTerms_length (P.terms f) q.2 (P.small f)

variable [Fintype E] [Fintype W] [Fintype F] [Fintype Copy] [Fintype I] [Fintype B]

noncomputable def LiftSource.anchorTest (P : LiftSource L mark) (f : F)
    (s : {v : V // signedOwner L mark v=f}→Bool) (x : W→Bool) : ℚ :=
  sumMonomials (P.terms f) (P.weight f s) (RingHom.id ℚ)
    (fun e=>qbits x (L.placement.owner e.val))

theorem product_get_eq_letters {A K : Type*} [CommRing K] (p : List A) (Y : A→K) :
    (∏ j : Fin p.length,Y (p.get j))=letters p Y := by
  rw [←List.prod_ofFn]
  change (List.ofFn (Y∘p.get)).prod=letters p Y
  rw [←List.map_ofFn,List.ofFn_get]
  rfl

set_option maxHeartbeats 11000000 in
omit [Fintype E] [Fintype W] [Fintype F] [Fintype Copy] [Fintype I] [Fintype B] in
theorem LiftSource.compile_anchor_sum (P : LiftSource L mark) (ell : ℕ) (f : F)
    (s : {v : V // signedOwner L mark v=f}→Bool) (x : W→Bool) :
    atAnchorFactor L mark (P.compile ell) f s x =
      (if P.neutral f then 1 else (∑ q : Modes ell (P.number f),
        P.modeCoeff ell f s q * letters (modeTerms (P.terms f) q.2)
          (fun e=>C (qbits x (L.placement.owner e.val))))) := by
  unfold atAnchorFactor
  let Y : {e : E // L.factor e=f}→ℚ[X] := fun e=>C (qbits x (L.placement.owner e.val))
  change (∑ i : Fin (Fintype.card (Modes ell (P.number f))+1),
    Fin.cases (if P.neutral f then 1 else 0) (fun k=>P.modeCoeff ell f s (P.modeCode ell f k)) i *
      ∏ j : Fin (P.termList ell f i).length,Y ((P.termList ell f i).get j))=_
  rw [Fin.sum_univ_succ]
  simp only [Fin.cases_zero,Fin.cases_succ,product_get_eq_letters,LiftSource.termList,letters,
    List.map_nil,List.prod_nil,mul_one]
  by_cases h : P.neutral f
  · simp [h,LiftSource.modeCoeff]
  · simp only [h,Bool.false_eq_true,if_false,zero_add,LiftSource.modeList]
    exact (P.modeCode ell f).sum_comp (fun q : Modes ell (P.number f) =>
      P.modeCoeff ell f s q * letters (modeTerms (P.terms f) q.2) Y)

#print axioms LiftSource.compile_graded
#print axioms LiftSource.compile_anchor_sum
end P5MainBalance.M6.Sparse
