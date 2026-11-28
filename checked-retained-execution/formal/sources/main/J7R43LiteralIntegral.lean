import J7R43LiteralWeights
import J6R15SpecializedBoxRowCollapse

/-! One true selected group at zeta=0 equals its wholly integral local
column evaluator: the two row rails are summed through their literal
equality truth tables, not by accessing or multiplying other children. -/
namespace J7R43Literal
open scoped BigOperators Classical Polynomial
open Polynomial P11FullPacking J6R9Recursive J6R10Repack J6R10Integral J6R11Integral
open J6R9PacketScopes J6R9PacketChild J6R10PacketAssembly J6R10RowAffine
open J8Physical J8J9Grouped J6R14SpecializedBox NativeProbeRing DyadicProbeCompiler
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-- Finite sums agree across definitionally different enumerations of the
same physical type. Avoid reducing either enumeration inside a cast. -/
theorem sum_univ_congr_instance {I K : Type*} [AddCommMonoid K]
    (ft₁ ft₂ : Fintype I) (φ ψ : I→K) (h : ∀ i, φ i=ψ i) :
    (@Finset.univ I ft₁).sum φ = (@Finset.univ I ft₂).sum ψ := by
  have hh : ft₁=ft₂ := Subsingleton.elim _ _
  subst ft₂
  exact Finset.sum_congr rfl (fun i _ => h i)

variable {G R S V : Type} [LinearOrder G] {U : V→Type} {a b : ℕ}
variable (d : Layout (Page a b G) R S V G U (2^a))
variable [Fintype R] [Fintype S] [Fintype V] [Fintype G]
variable [∀ v, Fintype (U v)]
variable (mask : MaskFamily a b G)
variable (wordsR : R→Fin a→G) (wordsC : S⊕V→Fin a→G)
variable (hC : ∀ w : Wire R, physicalCell mask (d.seat w) =
  declaredCell (orientedNetwork d) wordsR wordsC w)
variable (hB : Nat.card (Cell (Fin a) G) * (b*2^a) ≤ 3*Nat.card (Wire R))
local notation "Q" => (seatedParentPacking d mask wordsR wordsC hC hB)
variable (i : Fin a)
variable (hr : ∀ w, rowGroup mask i (d.seat w)=d.rowLabel w.1)
variable (hc : ∀ w, colGroup mask i (d.seat w)=actualColLabel d w)
variable (hrow : ∀ r, wordsR r i=d.rowLabel r)
variable (hpin : ∀ s, wordsC (.inl s) i=d.pinLabel s)
variable (hold : ∀ v, wordsC (.inr v) i=d.colLabel v)

variable {f : ℤ[X]} {ell : ℕ}
variable (p created : ℕ) (F : OldTables d) (sign : S→Bool)
variable (hf : f.Monic) (hc0 : 0<created) (hf0 : 0<f.natDegree) (hell : 0<ell)
variable (e : EndpointSeating d) (even : Even (2^a))
local notation "D" => Box f ell p
local notation "file" => orientedEntryFile d f ell created F sign
local notation "L" => (2^a : ℕ)
local notation "T" => LiteralPortCompiler.truth
local notation "aff" => LiteralPortCompiler.affine
local notation "E" => groupedPhysicalStateEquiv d mask i hr hc

set_option maxHeartbeats 6000000 in
include hrow hpin hold hc0 hf0 hell in
theorem baselineFeature_exact (g : G) (feat : Assignment d g→ℤ) :
    (∑ v : PhysicalState Q i g,
      actualBaselineWeight Q i (t:=(L:ℤ)-1) p (0:D) file hf g v * (feat (E g v).2 : D)) =
      (J8J9Grouped.child d e even F sign g none feat : D) := by
  let A (x : Assignment d g) (r : LocalRow d g) (leg : Bool) : D :=
    (argument d e even g x r leg : D)
  let W (x : Assignment d g) (r : LocalRow d g) (y : Bool→Bool) : D :=
    (T (LiteralPortCompiler.equality false true) y : D) *
       (aff (y false) (A x r false) * aff (y true) (A x r true))
  let B (x : Assignment d g) : D := (tablesAt d F sign g x : D) * (feat x : D)
  have hcols (v : PhysicalState Q i g) :
      (E g v).2 = localLabels d g (extendCol d mask i g v.2) := rfl
  have hrows (v : PhysicalState Q i g) (r : LocalRow d g) (leg : Bool) :
      (E g v).1 r leg = extendRow d mask i g v.1 (r.val,leg) :=
    grouped_row_reads d mask i hr g v.1 r leg
  have hentry (v : PhysicalState Q i g) :
      actualBaselineWeight Q i (t:=(L:ℤ)-1) p (0:D) file hf g v * (feat (E g v).2 : D)
        = B (E g v).2 * ∏ r, W (E g v).2 r ((E g v).1 r) := by
    unfold actualBaselineWeight
    rw [old_state_exact_by_group d mask wordsR wordsC hC hB i hrow hpin hold p created
        F sign hf hc0 hf0 hell g v]
    dsimp only
    have hfib := actual_row_packet_product d mask i hr g (fun w : Wire R =>
      aff (groupBit d.seat d.seat mask i g v w)
        (groupBase d.seat d.seat mask i ((L:ℤ)-1) p (box_two_nil p f ell) (0:D) g v w))
    change _ * (∏ k : Page a b G, ∏ w ∈ actualRows
      (fun w : Wire R => (rowBlock mask i (d.seat w)).swap) g k,
        aff (groupBit d.seat d.seat mask i g v w)
          (groupBase d.seat d.seat mask i ((L:ℤ)-1) p (box_two_nil p f ell) (0:D) g v w)) * _ = _
    rw [hfib]
    unfold B W
    rw [Finset.prod_mul_distrib]
    have eRow (r : LocalRow d g) : (E g v).1 r = fun leg => extendRow d mask i g v.1 (r.val,leg) :=
      funext (hrows v r)
    simp only [eRow,hcols]
    have hleg : (∏ r : LocalRow d g, ∏ b : Bool,
        aff (groupBit d.seat d.seat mask i g v (r.val,b))
          (groupBase d.seat d.seat mask i ((L:ℤ)-1) p (box_two_nil p f ell) (0:D) g v (r.val,b))) =
        ∏ r : LocalRow d g,
          aff (extendRow d mask i g v.1 (r.val,false))
            (A (localLabels d g (extendCol d mask i g v.2)) r false) *
          aff (extendRow d mask i g v.1 (r.val,true))
            (A (localLabels d g (extendCol d mask i g v.2)) r true) := by
      refine Finset.prod_congr rfl (fun r _ => ?_)
      have step (leg : Bool) :
          aff (groupBit d.seat d.seat mask i g v (r.val,leg))
            (groupBase d.seat d.seat mask i ((L:ℤ)-1) p (box_two_nil p f ell) (0:D) g v (r.val,leg)) =
          aff (extendRow d mask i g v.1 (r.val,leg))
            (A (localLabels d g (extendCol d mask i g v.2)) r leg) := by
        rw [zero_group_leg d mask wordsR wordsC hC hB i hr hc p F e even g v r leg]
        rfl
      simp only [step]
      rw [Fintype.prod_bool]
      exact mul_comm _ _
    rw [hleg]
    ac_rfl
  calc
    _ = ∑ v : (LocalRow d g → Bool → Bool) × Assignment d g,
        B v.2 * ∏ r, W v.2 r (v.1 r) :=
      Fintype.sum_equiv (E g) _ _ hentry
    _ = ∑ x : Assignment d g, B x * ∏ r : LocalRow d g,
        J8SourceMoment.rowFactor none (A x r false) (A x r true) := by
      rw [Fintype.sum_prod_type,Finset.sum_comm]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      dsimp only
      rw [← Finset.mul_sum, ← Fintype.prod_sum (W x)]
      congr 1
      apply Finset.prod_congr rfl
      intro r _
      exact J6R14SpecializedBox.pair_sum_rowFactor none _ _
    _ = _ := by
      rw [child_as_sum,Int.cast_sum]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      simp only [summand,J8SourceMoment.marker,Option.bind_none,Int.cast_mul,Int.cast_prod,B,A]
      congr 2
      funext r
      simp only [J8SourceMoment.rowFactor, Option.elim_none, J8SourceMoment.oldEquality_eq,
        TargetDerivative.equality,Int.cast_add,Int.cast_sub,Int.cast_one,Int.cast_mul]

#print axioms sum_univ_congr_instance
#print axioms baselineFeature_exact
end
end J7R43Literal
