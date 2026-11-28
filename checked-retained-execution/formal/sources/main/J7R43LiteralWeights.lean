import J7R43LiteralGeometry
import J7R43LiteralSlots
import J6R16SpecializedBoxBinding
import J8J9GroupedTerm

/-! Resolve the retained old tensors and baseline packet factors in one
group. The inputs are the exact owner labels of the selected layout,
never a hypothesized equality of completed contractions. -/
namespace J7R43Literal
open scoped BigOperators Classical Polynomial
open Polynomial P11FullPacking J6R9Recursive J6R10Repack J6R10Integral J6R11Integral
open J6R9PacketScopes J6R9PacketChild J6R10PacketAssembly J6R10RowAffine
open J8Physical J8J9Grouped J6R14SpecializedBox NativeProbeRing DyadicProbeCompiler
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false

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

def groupedOwners (g : G) :
    Old (atGroup Q i) g ≃ LocalRow d g ⊕ (LocalPin d g ⊕ LocalColumn d g) :=
  Equiv.subtypeSum.trans <| Equiv.sumCongr
    (Equiv.subtypeEquivRight (fun r => by
      change wordsR r i=g ↔ d.rowLabel r=g
      rw [hrow]))
    (Equiv.subtypeSum.trans <| Equiv.sumCongr
      (Equiv.subtypeEquivRight (fun s => by
        change wordsC (.inl s) i=g ↔ d.pinLabel s=g
        rw [hpin]))
      (Equiv.subtypeEquivRight (fun v => by
        change wordsC (.inr v) i=g ↔ d.colLabel v=g
        rw [hold])))

theorem groupedOwners_inverse (g : G) (u : LocalRow d g ⊕ (LocalPin d g ⊕ LocalColumn d g)) :
    ((groupedOwners d mask wordsR wordsC hC hB i hrow hpin hold g).symm u).val =
      Sum.map Subtype.val (Sum.map Subtype.val Subtype.val) u := by
  rcases u with r | s | v <;> rfl

variable {f : ℤ[X]} {ell : ℕ}
variable (p created : ℕ) (F : OldTables d) (sign : S→Bool)
variable (hf : f.Monic) (hc0 : 0<created) (hf0 : 0<f.natDegree) (hell : 0<ell)
local notation "D" => Box f ell p
local notation "file" => orientedEntryFile d f ell created F sign
local notation "T" => LiteralPortCompiler.truth
local notation "L" => (2^a : ℕ)

set_option maxHeartbeats 2400000 in
include hrow hpin hold hc0 hf0 hell in
theorem old_state_exact_by_group (g : G) (v : PhysicalState Q i g) :
    oldState Q i g p file hf v =
      let Y := extendRow d mask i g v.1
      let X := extendCol d mask i g v.2
      (∏ r : LocalRow d g, (T (LiteralPortCompiler.equality false true) (fun b => Y (r.val,b)) : D)) *
        ((tablesAt d F sign g (localLabels d g X) : ℤ) : D) := by
  let Y := extendRow d mask i g v.1
  let X := extendCol d mask i g v.2
  have hv : pairedGroups (Equiv.refl (Wire R)) (rowGroupAt Q i) (colGroupAt Q i) (Y,X) g = v := by
    apply Prod.ext
    · funext w
      exact dif_pos w.prop
    · funext w
      exact dif_pos w.prop
  let U₀ := LocalRow d g ⊕ (LocalPin d g ⊕ LocalColumn d g)
  let e := groupedOwners d mask wordsR wordsC hC hB i hrow hpin hold g
  let B (u : R ⊕ (S⊕V)) : D :=
    reduce p f ell ((file u).frozen hf (mixedAssignment (orientedNetwork d) Y X u))
  have hfirst : oldState Q i g p file hf v = ∏ u : U₀, B (Sum.map Subtype.val
      (Sum.map Subtype.val Subtype.val) u) := by
    unfold oldState
    apply Fintype.prod_equiv e
    intro u
    have hu := groupedOwners_inverse d mask wordsR wordsC hC hB i hrow hpin hold g (e u)
    change (e.symm (e u)).val = _ at hu
    rw [e.symm_apply_apply] at hu
    rw [← hu]
    change reduce p f ell ((file u.val).frozen hf _) = _
    unfold B
    rw [← hv,retained_reads_mixed]
  have hR (r : LocalRow d g) :
      B (.inl r.val) = (T (LiteralPortCompiler.equality false true) (fun b => Y (r.val,b)) : D) := by
    unfold B
    rw [mixed_eq_row, oriented_row_truth d f ell created F sign hf hc0 hf0 hell]
    exact LiteralPortCompiler.map_truth (reduce p f ell) _ _
  have hP (s : LocalPin d g) :
      B (.inr (.inl s.val)) = (T (LiteralPortCompiler.pin s (sign s.val)) (localLabels d g X).1 : D) := by
    unfold B
    rw [mixed_eq_col, oriented_pin_truth d f ell created F sign hf hc0 hf0 hell X g s]
    exact LiteralPortCompiler.map_truth (reduce p f ell) _ _
  have hV (v : LocalColumn d g) :
      B (.inr (.inr v.val)) = (T (F g v) ((localLabels d g X).2 v) : D) := by
    unfold B
    rw [mixed_eq_col, oriented_old_truth d f ell created F sign hf hc0 hf0 hell X g v]
    exact LiteralPortCompiler.map_truth (reduce p f ell) _ _
  rw [hfirst]
  dsimp only [U₀]
  rw [Fintype.prod_sum_type,Fintype.prod_sum_type]
  simp only [Sum.map_inl,Sum.map_inr,hR,hP,hV,tablesAt,table,Int.cast_mul,Int.cast_prod]
  congr 2 <;>
    (apply Finset.prod_congr rfl; intro u _; exact
      (LiteralPortCompiler.map_truth (Int.castRingHom D) _ _).symm)

theorem evalBox_int_const (A : Source[X]) (n : ℤ) (h : A.coeff 0=(n:Source)) :
    evalBox p f ell 0 A = (n:D) := by
  change J6ActiveInterpolation.scalarIn p f ell
    (A.eval₂ (toScalar p f) (2*0)) = _
  rw [mul_zero,eval₂_at_zero,h,map_intCast,map_intCast]

include hr hc F in
theorem zero_group_leg (e : EndpointSeating d) (even : Even L)
    (g : G) (v : PhysicalState Q i g) (r : LocalRow d g) (leg : Bool) :
    groupBase d.seat d.seat mask i ((L:ℤ)-1) p (box_two_nil p f ell) (0:D)
      g v (r.val,leg) =
      (argument d e even g (localLabels d g (extendCol d mask i g v.2)) r leg : D) := by
  have h : rowGroup mask i (d.seat (r.val,leg))=g := (hr _).trans r.prop
  let X := extendCol d mask i g v.2
  rw [groupBase,dif_pos h]
  have hX : (fun q : {q : Wire R // colGroup mask i (d.seat q)=rowGroup mask i (d.seat (r.val,leg))} =>
      v.2 ⟨q.val,q.prop.trans h⟩) = fun q => X q.val := by
    funext q
    exact (extendCol_at d mask i g v.2 q.val (q.prop.trans h)).symm
  rw [hX]
  have hh := (genuine_samepage_box d mask i hr hc e even F p ell f
    (box_two_nil p f ell) (0 : Scalar p f) X (r.val,leg)).symm
  simp only [map_zero] at hh
  rcases r with ⟨r,rr⟩
  subst g
  rw [hh]
  apply evalBox_int_const
  exact (argument_cast d e even _ _ _ _ _).symm

#print axioms groupedOwners_inverse
#print axioms old_state_exact_by_group
#print axioms evalBox_int_const
#print axioms zero_group_leg
end
end J7R43Literal