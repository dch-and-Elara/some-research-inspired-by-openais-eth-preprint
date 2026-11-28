import J9R13Compiler
import J8J9GroupedBudget

/-!
# Exact grouped singleton fusion, at every order of the coefficient ring

Different source and target groups are required: it would not be sound
to multiply two independently summed copies of one local cube. Kernel
entries live only at the real target ports. The coefficient ring may
itself be the odd-localized polynomial ring, so this identity retains
all native row and crossing tails.
-/

namespace J9R13GroupFusion
open scoped Classical BigOperators
open LiteralPortCompiler J9LayoutTransfer MvPolynomial
open J8SourceMoment

noncomputable section
variable {I R T G K : Type*} [Fintype I] [Fintype R] [Fintype G] [CommRing K]

abbrev Fiber (owner : R→G) (g : G) := {r : R // owner r=g}

def globalMarker (p : Port R) (r : R) : Option Bool := if r=p.1 then some p.2 else none

def derivativeProduct (u : Port R→K) (p : Port R) : K :=
  ∏ r : R, rowFactor (globalMarker p r) (u (r,false)) (u (r,true))

omit [Fintype G] [Fintype I] in
theorem derivativeProduct_eq (u : Port R→K) (p : Port R) :
    derivativeProduct u p =
      (-1+2*u (p.1,!p.2)) *
        ∏ r ∈ (Finset.univ : Finset R).erase p.1,
          TargetDerivative.equality (u (r,false)) (u (r,true)) := by
  unfold derivativeProduct
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ p.1)]
  congr 1
  · cases p with
    | mk r b =>
      cases b <;> simp [globalMarker,rowFactor,selectedEquality_eq]
  · apply Finset.prod_congr rfl
    intro r hr
    simp [globalMarker,rowFactor,if_neg (Finset.mem_erase.mp hr).1,oldEquality_eq]

def targetKernel (s : Finset T) (wire : T→Port R) (v : T→K) (p : Port R) : K :=
  ∑ j ∈ s, if wire j=p then v j else 0

omit [Fintype I] [Fintype G] in
theorem singleton_targets (s : Finset T) (wire : T→Port R) (v : T→K) (u : Port R→K) :
    coeff β (rowCompiler u (targetKernel s wire v)) =
      ∑ j ∈ s, v j * derivativeProduct u (wire j) := by
  rw [singleton_native_rows]
  simp_rw [mul_assoc,← derivativeProduct_eq]
  unfold targetKernel
  simp_rw [Finset.sum_mul,Finset.sum_comm (s := (Finset.univ : Finset (Port R))) (t := s)]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_eq_single_of_mem (wire j) (Finset.mem_univ _)]
  · simp
  · intro p _ hn
    simp [Ne.symm hn]

variable {Ω : G→Type*} [∀ g, Fintype (Ω g)]

abbrev Cube (Ω : G→Type*) := (g : G)→Ω g

def baseAt (owner : R→G) (u : ∀ g, Ω g→Fiber owner g→Bool→K)
    (x : Cube Ω) (p : Port R) : K :=
  u (owner p.1) (x (owner p.1)) ⟨p.1,rfl⟩ p.2

omit [CommRing K] [Fintype I] [Fintype R] [Fintype G] [(g : G) → Fintype (Ω g)] in
theorem baseAt_fibre (owner : R→G) (u : ∀ g, Ω g→Fiber owner g→Bool→K)
    (x : Cube Ω) (g : G) (r : Fiber owner g) (b : Bool) :
    baseAt owner u x (r.1,b) = u g (x g) r b := by
  obtain ⟨r,hr⟩ := r
  subst g
  rfl

def childAt (owner : R→G) (u : ∀ g, Ω g→Fiber owner g→Bool→K)
    (w : ∀ g, Ω g→K) (g : G) (mark : Option (Fiber owner g×Bool)) (feat : Ω g→K)
    (x : Ω g) : K :=
  w g x * feat x *
    ∏ r : Fiber owner g, rowFactor (marker mark r) (u g x r false) (u g x r true)

def childSum (owner : R→G) (u : ∀ g, Ω g→Fiber owner g→Bool→K)
    (w : ∀ g, Ω g→K) (g : G) (mark : Option (Fiber owner g×Bool)) (feat : Ω g→K) : K :=
  ∑ x : Ω g, childAt owner u w g mark feat x

def baselinePub (owner : R→G) (u : ∀ g, Ω g→Fiber owner g→Bool→K)
    (w : ∀ g, Ω g→K) (gs gt : G) : K :=
  ∏ g ∈ ((Finset.univ : Finset G).erase gs).erase gt, childSum owner u w g none (fun _ => 1)

omit [Fintype I] [(g : G) → Fintype (Ω g)] in
theorem pointwise_children (owner : R→G) (u : ∀ g, Ω g→Fiber owner g→Bool→K)
    (w : ∀ g, Ω g→K) (gs gt : G) (hne : gs≠gt) (feat : Ω gs→K)
    (p : Fiber owner gt×Bool) (x : Cube Ω) :
    (∏ g : G, J8J9Grouped.insertSpecial (fun g => childAt owner u w g none (fun _ => 1))
        gs gt (childAt owner u w gs none feat) (childAt owner u w gt (some p) (fun _ => 1)) g (x g)) =
      ((∏ g : G, w g (x g)) * feat (x gs)) *
        derivativeProduct (baseAt owner u x) (p.1.1,p.2) := by
  let z (r : R) := rowFactor (globalMarker (p.1.1,p.2) r)
    (baseAt owner u x (r,false)) (baseAt owner u x (r,true))
  let add (g : G) : K := if g=gs then feat (x gs) else 1
  have hn (g : G) (hg : g≠gt) (r : Fiber owner g) : r.1≠p.1.1 := by
    intro h
    apply hg
    exact r.2.symm.trans ((congrArg owner h).trans p.1.2)
  have H (g : G) :
      J8J9Grouped.insertSpecial (fun g => childAt owner u w g none (fun _ => 1))
        gs gt (childAt owner u w gs none feat) (childAt owner u w gt (some p) (fun _ => 1)) g (x g) =
      w g (x g) * add g * ∏ r : Fiber owner g, z r.1 := by
    by_cases hs : g=gs
    · subst g
      simp only [J8J9Grouped.insertSpecial,dif_pos True.intro,childAt,add,if_pos rfl]
      congr 1
      apply Finset.prod_congr rfl
      intro r _
      simp only [z,globalMarker,if_neg (hn gs hne r),marker,Option.bind_none,baseAt_fibre]
    · by_cases ht : g=gt
      · subst g
        simp only [J8J9Grouped.insertSpecial,dif_neg hs,dif_pos True.intro,childAt,add,if_neg hs]
        congr 1
        apply Finset.prod_congr rfl
        intro r _
        simp only [z,globalMarker,baseAt_fibre]
        congr 1
        by_cases h : r=p.1
        · subst r
          simp [marker]
        · have hh : r.1≠p.1.1 := fun eq => h (Subtype.ext eq)
          simp [marker,Ne.symm h,hh]
      · simp only [J8J9Grouped.insertSpecial,dif_neg hs,dif_neg ht,childAt,add,if_neg hs]
        congr 1
        apply Finset.prod_congr rfl
        intro r _
        simp only [z,globalMarker,if_neg (hn g ht r),marker,Option.bind_none,baseAt_fibre]
  have addProd : (∏ g : G, add g)=feat (x gs) := by
    rw [Finset.prod_eq_single gs]
    · simp [add]
    · intro g _ hg
      simp [add,hg]
    · simp
  have fibreProd : (∏ g : G, ∏ r : Fiber owner g, z r.1)=∏ r : R, z r := by
    calc
      _ = ∏ q : (Σ g, Fiber owner g), z q.2.1 := (Fintype.prod_sigma
        (fun q : (Σ g, Fiber owner g) => z q.2.1)).symm
      _ = _ := Fintype.prod_equiv (Equiv.sigmaFiberEquiv owner) _ _ (fun _ => rfl)
  rw [Finset.prod_congr rfl (fun g _ => H g),Finset.prod_mul_distrib,
    Finset.prod_mul_distrib,addProd,fibreProd]
  rfl

omit [Fintype I] in
theorem summed_children (owner : R→G) (u : ∀ g, Ω g→Fiber owner g→Bool→K)
    (w : ∀ g, Ω g→K) (gs gt : G) (hne : gs≠gt) (feat : Ω gs→K) (p : Fiber owner gt×Bool) :
    (∑ x : Cube Ω, ((∏ g : G, w g (x g)) * feat (x gs)) *
      derivativeProduct (baseAt owner u x) (p.1.1,p.2)) =
      baselinePub owner u w gs gt * childSum owner u w gs none feat *
        childSum owner u w gt (some p) (fun _ => 1) := by
  simp_rw [← pointwise_children owner u w gs gt hne feat p]
  rw [J8J9Grouped.splitSpecial _ gs gt hne]
  unfold baselinePub childSum
  ring

/-- This equality holds in the whole coefficient ring. In particular for
K=Source[X] it identifies all binary probe values, not only their first
coefficient after recovery. -/
theorem grouped_completed (F : CNF I) (e : Cube Ω ≃ (I→Bool))
    (owner : R→G) (u : ∀ g, Ω g→Fiber owner g→Bool→K) (w : ∀ g, Ω g→K)
    (hF : ∀ x : Cube Ω, (truth F (e x) : K)=∏ g : G, w g (x g))
    (gs gt : G) (hne : gs≠gt) (feat : Ω gs→K)
    (s : Finset T) (port : T→Fiber owner gt×Bool) (cross : T→K) :
    coeff β (completed (J9R13Compiler.system (R:=R) F)
      (J9R13Compiler.base (fun x => baseAt owner u (e.symm x)) (fun x => feat (e.symm x gs)))
      (J9R13Compiler.kernel (fun _ p (_ : Unit) =>
        targetKernel s (fun j => ((port j).1.1,(port j).2)) cross p))) =
      (baselinePub owner u w gs gt * childSum owner u w gs none feat) *
        ∑ j ∈ s, cross j * childSum owner u w gt (some (port j)) (fun _ => 1) := by
  rw [J9R13Compiler.singleton_separate]
  simp_rw [singleton_targets]
  let f (x : I→Bool) : K := (truth F x * feat (e.symm x gs)) *
    ∑ j ∈ s, cross j * derivativeProduct (baseAt owner u (e.symm x)) ((port j).1.1,(port j).2)
  change (∑ x, f x)=_
  rw [← Equiv.sum_comp e f]
  simp only [f,Equiv.symm_apply_apply,hF,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  let g (x : Cube Ω) :=
    ((∏ g : G, w g (x g)) * feat (x gs)) * derivativeProduct (baseAt owner u x) ((port j).1.1,(port j).2)
  have h1 (x : Cube Ω) : ((∏ g : G, w g (x g)) * feat (x gs)) *
      (cross j * derivativeProduct (baseAt owner u x) ((port j).1.1,(port j).2)) = cross j * g x := by
    unfold g
    ring
  simp_rw [h1,← Finset.mul_sum]
  rw [show (∑ x, g x)=_ from summed_children owner u w gs gt hne feat (port j)]
  ring

#print axioms derivativeProduct_eq
#print axioms singleton_targets
#print axioms pointwise_children
#print axioms summed_children
#print axioms grouped_completed

end
end J9R13GroupFusion
