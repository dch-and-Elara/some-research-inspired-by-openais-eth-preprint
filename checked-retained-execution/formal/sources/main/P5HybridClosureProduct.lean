import P5HybridClosureTriangle

/-! Exact §8 cross-method evaluation for the same cloned CNF. The
two operands use only their displayed local pin groups. They are
arbitrary local edge-OR products, not native Taylor/child values. -/
namespace Paper5.HybridClosure
open scoped BigOperators Classical

variable {V A B : Type*} [Fintype V] [DecidableEq V]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

def boolOrNat (x y : Bool) : ℕ := if x=true ∨ y=true then 1 else 0

def edgeOr {W : Type*} (σ : W→Bool) (e : W×W) : ℕ :=
  boolOrNat (σ e.1) (σ e.2)

theorem edge_product_is_indicator {W : Type*}
    (F : Finset (W×W)) (σ : W→Bool) :
    (∏ e∈F,edgeOr σ e) = if PinnedCNF.AllEdges F σ then 1 else 0 := by
  classical
  by_cases h : PinnedCNF.AllEdges F σ
  · rw [if_pos h]
    apply Finset.prod_eq_one
    intro e he
    exact if_pos (h e he)
  · rw [if_neg h]
    have hh : ∃ e∈F,¬ (σ e.1=true ∨ σ e.2=true) := by
      by_contra hn
      apply h
      intro e he
      by_contra he'
      exact hn ⟨e,he,he'⟩
    obtain ⟨e,he,hz⟩ := hh
    exact Finset.prod_eq_zero he (if_neg hz)

def mainPinColor (c : V→A) (p : TriVertex V) : A := c p.1

noncomputable def dPinColor (E : Finset (V×V))
    (cubic : ∀ v,GraphCutMoments.degree E v=3) (c : E→B) (p : TriVertex V) : B :=
  c ((exteriorPort E cubic).symm p).1

omit [Fintype A] [DecidableEq A] in
theorem main_inner_monochromatic (c : V→A) :
    ∀ e∈innerEdges V,mainPinColor c e.1=mainPinColor c e.2 :=
  fun _ he => congrArg c (innerEdges_stay_in_triangle he)

omit [Fintype V] [Fintype B] [DecidableEq B] in
theorem d_outer_monochromatic (E : Finset (V×V))
    (cubic : ∀ v,GraphCutMoments.degree E v=3) (c : E→B) :
    ∀ e∈outerEdges E cubic,dPinColor E cubic c e.1=dPinColor E cubic c e.2 := by
  intro e he
  obtain ⟨f,_,rfl⟩ := Finset.mem_image.mp he
  simp [dPinColor,outerEdge]

section GroupOnly
variable {W C : Type*} [Fintype C] [DecidableEq C]

abbrev SignGroup (c : W→C) (g : C) := {x : W // c x=g}→Bool

def bucketEdges (F : Finset (W×W)) (c : W→C) (g : C) : Finset (W×W) :=
  F.filter fun e => c e.1=g

/-- The input type contains no sign outside the designated group.
Both endpoints are constructed as members of that very group. -/
def groupOperand (F : Finset (W×W)) (c : W→C) (mono : ∀ e∈F,c e.1=c e.2)
    (g : C) (x : SignGroup c g) : ℕ :=
  ∏ e∈(bucketEdges F c g).attach,
    boolOrNat (x ⟨e.val.1,(Finset.mem_filter.mp e.property).2⟩)
      (x ⟨e.val.2,(mono e.val (Finset.mem_filter.mp e.property).1).symm.trans
        (Finset.mem_filter.mp e.property).2⟩)

omit [Fintype C] in
theorem groupOperand_restrict (F : Finset (W×W)) (c : W→C) (mono : ∀e∈F,c e.1=c e.2)
    (g : C) (σ : W→Bool) :
    groupOperand F c mono g (σ ∘ Subtype.val) = ∏ e∈bucketEdges F c g,edgeOr σ e := by
  unfold groupOperand
  exact Finset.prod_attach _ (edgeOr σ)

theorem completed_operand (F : Finset (W×W)) (c : W→C) (mono : ∀e∈F,c e.1=c e.2)
    (σ : W→Bool) :
    (∏ g : C, groupOperand F c mono g (σ ∘ Subtype.val)) = ∏ e∈F,edgeOr σ e := by
  simp only [groupOperand_restrict]
  exact Finset.prod_fiberwise F (fun e => c e.1) (edgeOr σ)

theorem preassigned_bucket_sizes (F : Finset (W×W)) (c : W→C) :
    (∑ g : C,(bucketEdges F c g).card)=F.card := by
  simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using
    (Finset.sum_fiberwise F (fun e => c e.1) (fun _ => (1:ℕ)))
end GroupOnly

def mainOperand (c : V→A) (g : A) (x : SignGroup (mainPinColor c) g) : ℕ :=
  groupOperand (innerEdges V) (mainPinColor c) (main_inner_monochromatic c) g x

noncomputable def dOperand (E : Finset (V×V))
    (cubic : ∀ v,GraphCutMoments.degree E v=3) (c : E→B)
    (g : B) (x : SignGroup (dPinColor E cubic c) g) : ℕ :=
  groupOperand (outerEdges E cubic) (dPinColor E cubic c) (d_outer_monochromatic E cubic c) g x

/-- The actual four-clone clause list, with any endpoint slot choices,
has exactly the product of the two completed group operands for every
sign word.  Legality of the three-occurrence slot assignment is
verified separately via cubicity of the replacement. -/
theorem cross_method_count (E : Finset (V×V)) (cubic : ∀ v,GraphCutMoments.degree E v=3)
    (loopless : ∀v,(v,v)∉E)
    (cM : V→A) (cD : E→B) (left right : (replacedEdges E cubic)→Fin 4)
    (σ : TriVertex V→Bool) :
    PinnedCNF.modelCount (MainClonedCNF.formula (replacedEdges E cubic) left right σ) =
      (∏ g : A,mainOperand cM g (σ ∘ Subtype.val)) *
      (∏ h : B,dOperand E cubic cD h (σ ∘ Subtype.val)) := by
  rw [MainClonedCNF.modelCount_cloned, PinnedCNF.count_eq_indicator,←edge_product_is_indicator]
  unfold mainOperand dOperand replacedEdges
  rw [completed_operand,completed_operand,Finset.prod_union (triangle_split_disjoint E cubic loopless)]

theorem two_family_indexed_scan_counts (E : Finset (V×V)) (cubic : ∀ v,GraphCutMoments.degree E v=3)
    (loopless : ∀ v,(v,v)∉E) (cM : V→A) (cD : E→B) :
    2*((∑ g : A,(bucketEdges (innerEdges V) (mainPinColor cM) g).card)+
       (∑ h : B,(bucketEdges (outerEdges E cubic) (dPinColor E cubic cD) h).card))=
      3*Fintype.card (TriVertex V) := by
  rw [preassigned_bucket_sizes,preassigned_bucket_sizes]
  have h := triangle_edge_count E cubic loopless
  rwa [replacedEdges,Finset.card_union_of_disjoint (triangle_split_disjoint E cubic loopless)] at h

#print axioms edge_product_is_indicator
#print axioms d_outer_monochromatic
#print axioms groupOperand_restrict
#print axioms completed_operand
#print axioms preassigned_bucket_sizes
#print axioms cross_method_count
#print axioms two_family_indexed_scan_counts
end Paper5.HybridClosure
