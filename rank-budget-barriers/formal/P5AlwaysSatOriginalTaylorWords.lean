import P5MainBalanceM6SparseMonomial

/-! A selected subword is a typed monomial, not a supplied evaluation
oracle. The expansion is valid in every commutative ring. -/
namespace Paper5.AlwaysSatOriginal.Physical.Taylor
open P5MainBalance.M6.Sparse
open scoped BigOperators Classical

variable {A K : Type*} [CommRing K]

abbrev Choices (l : List A) := Fin l.length→Bool

noncomputable def choiceCode (l : List A) :
    Fin (Fintype.card (Choices l)) ≃ Choices l := (Fintype.equivFin _).symm

def subword (l : List A) (pick : Choices l) : List A :=
  (List.ofFn fun i=>if pick i then [l.get i] else []).flatten

omit [CommRing K] in
theorem subword_length (l : List A) (pick : Choices l) :
    (subword l pick).length≤l.length := by
  rw [subword,length_ofFn_flatten]
  calc
    _ ≤ ∑ _i : Fin l.length, (1:ℕ) := Finset.sum_le_sum (fun i _=>by cases pick i <;> simp)
    _ = l.length := by simp

def signedLetter (positive pick : Bool) : K :=
  if pick then (if positive then -1 else 1) else (if positive then 1 else 0)

def supportLetter (positive pick : Bool) : K :=
  if positive || pick then 1 else 0

def wordWeight (l : List A) (sign : A→Bool) (g : Bool→Bool→K) (pick : Choices l) : K :=
  ∏ i : Fin l.length,g (sign (l.get i)) (pick i)

theorem word_expansion (l : List A) (sign : A→Bool) (g : Bool→Bool→K) (Y : A→K) :
    (∑ pick : Choices l,wordWeight l sign g pick*letters (subword l pick) Y) =
      ∏ i : Fin l.length,(g (sign (l.get i)) false+g (sign (l.get i)) true*Y (l.get i)) := by
  let w (i : Fin l.length) (b : Bool) :=
    g (sign (l.get i)) b * letters (if b then [l.get i] else []) Y
  have h (i : Fin l.length) :
      (∑ b : Bool,w i b)=g (sign (l.get i)) false+g (sign (l.get i)) true*Y (l.get i) := by
    simp [w,letters]
    ring
  calc
    _ = ∑ p : Choices l,∏ i,w i (p i) := by
      apply Finset.sum_congr rfl
      intro p _
      rw [wordWeight,subword,letters_ofFn,←Finset.prod_mul_distrib]
    _ = ∏ i,∑ b : Bool,w i b := (Fintype.prod_sum w).symm
    _ = _ := by simp only [h]

theorem signed_word_expansion (l : List A) (sign : A→Bool) (Y : A→K) :
    (∑ pick : Choices l,wordWeight l sign signedLetter pick * letters (subword l pick) Y) =
      letters l (fun p=>if sign p then 1-Y p else Y p) := by
  rw [word_expansion]
  have he (f : A→K) : (∏ i : Fin l.length,f (l.get i))=letters l f := by
    rw [←List.prod_ofFn]
    change (List.ofFn (f ∘ l.get)).prod=_
    rw [←List.map_ofFn,List.ofFn_get]
    rfl
  rw [←he]
  apply Finset.prod_congr rfl
  intro i _
  cases sign (l.get i) <;> simp [signedLetter]
  ring

theorem support_word_expansion (l : List A) (sign : A→Bool) (Y : A→K) :
    (∑ pick : Choices l,wordWeight l sign supportLetter pick * letters (subword l pick) Y) =
      letters l (fun p=>if sign p then 1+Y p else Y p) := by
  rw [word_expansion]
  have he (f : A→K) : (∏ i : Fin l.length,f (l.get i))=letters l f := by
    rw [←List.prod_ofFn]
    change (List.ofFn (f ∘ l.get)).prod=_
    rw [←List.map_ofFn,List.ofFn_get]
    rfl
  rw [←he]
  apply Finset.prod_congr rfl
  intro i _
  cases sign (l.get i) <;> simp [supportLetter]

def bitValueAux (b : Bool) : K := if b then 1 else 0

theorem letters_false_truth (l : List A) (sg bit : A→Bool) :
    letters l (fun p=>if sg p then (1:K)-bitValueAux (bit p) else bitValueAux (bit p)) =
      if l.any (fun p=>bit p == sg p) then 0 else 1 := by
  induction l with
  | nil => simp [letters]
  | cons p l ih =>
    change (if sg p then (1:K)-bitValueAux (bit p) else bitValueAux (bit p))*
      letters l (fun p=>if sg p then (1:K)-bitValueAux (bit p) else bitValueAux (bit p)) =
      if ((bit p == sg p) || l.any (fun p=>bit p == sg p)) then 0 else 1
    rw [ih]
    cases h₁ : sg p <;> cases h₂ : bit p <;> cases h₃ : l.any (fun p=>bit p == sg p) <;>
      norm_num [h₁,h₂,h₃,bitValueAux]

theorem signed_word_map {R : Type*} [CommRing R] (φ : K→+*R) (l : List A)
    (sg : A→Bool) (p : Choices l) :
    φ (wordWeight l sg signedLetter p)=wordWeight l sg signedLetter p := by
  rw [wordWeight,map_prod,wordWeight]
  apply Finset.prod_congr rfl
  intro i _
  cases sg (l.get i) <;> cases p i <;> simp [signedLetter]

theorem support_word_map {R : Type*} [CommRing R] (φ : K→+*R) (l : List A)
    (sg : A→Bool) (p : Choices l) :
    φ (wordWeight l sg supportLetter p)=wordWeight l sg supportLetter p := by
  rw [wordWeight,map_prod,wordWeight]
  apply Finset.prod_congr rfl
  intro i _
  cases sg (l.get i) <;> cases p i <;> simp [supportLetter]

#print axioms signed_word_map
#print axioms support_word_map
#print axioms subword_length
#print axioms word_expansion
#print axioms signed_word_expansion
#print axioms support_word_expansion
#print axioms letters_false_truth
end Paper5.AlwaysSatOriginal.Physical.Taylor