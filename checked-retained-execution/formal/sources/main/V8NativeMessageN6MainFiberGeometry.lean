import V8NativeMessageN1MainRow
import P5MainBalanceM6ExactBox

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 8400000

/-! Literal four-clone placements, original integer exceptional rows and
a weight-zero copy/orbit indicator. Every private column is covered by
one of those nonnegative rows because its genuine cycle occurrence is
seated, not because all measurement fibers are assumed to be injective. -/
namespace V8NativeMessage.N6.MainFiber
open V8NativeMessage.C3.NativeAssembly.MainScan V8NativeMessage.N1
open P5MainIterator P5MainBalance
open scoped BigOperators Classical

noncomputable section

variable {W Copy : Type*} [Fintype W] [DecidableEq W] [Fintype Copy]
variable {F : Finset (W×W)} {r Q : ℕ}

omit [Fintype W] in
theorem occurrence_covers (hreg : ∀ v,GraphCutMoments.degree F v=3) :
    Function.Surjective (occVar hreg) := by
  rintro ⟨v,j⟩
  exact ⟨.inr (.inr ((v,j),true)),rfl⟩

structure Seating (F : Finset (W×W)) (Copy : Type*) (r Q : ℕ)
    (hreg : ∀ v,GraphCutMoments.degree F v=3) where
  slot : Occ F ↪ (Copy × WordCell (Fin Q) (Fin r))
  variableLabel : Clone W→Fin Q→Fin r
  factorLabel : Clause F→Fin Q→Fin r
  left : ∀ e i,((slot e).2 i).1=variableLabel (occVar hreg e) i
  right : ∀ e i,((slot e).2 i).2=factorLabel (occClause e) i

def Seating.layout {hreg : ∀ v,GraphCutMoments.degree F v=3}
    (P : Seating F Copy r Q hreg) :
    SourceLayout (Occ F) (Clone W) (Clause F) Copy (Fin Q) (Fin r) where
  placement := ⟨occVar hreg,P.slot,occurrence_covers hreg⟩
  factor := occClause
  a := P.variableLabel
  d := P.factorLabel
  first := P.left
  second := P.right

abbrev Orbit (Copy : Type*) (r Q : ℕ) := CopyOrbit Copy (Fin Q) (Fin r)

abbrev Slot (Copy : Type*) (r Q : ℕ) := CopiedSlot Copy (Fin Q) (Fin r)

abbrev Row (keep : ℕ→Prop) (Copy : Type*) (r Q : ℕ) :=
  NativeRows keep Copy (Fin Q) (Fin r)

def zeroRow (keep : ℕ→Prop) (h0 : keep 0) (o : Orbit Copy r Q) :
    Row keep Copy r Q := ⟨⟨o,fun _=>false⟩,by simpa [boolWeight] using h0⟩

omit [Fintype Copy] in
theorem weight_zero_indicator (o : Orbit Copy r Q) (x : Slot Copy r Q) :
    zOrbitRow CoordFamily (⟨o,fun _=>false⟩ : Slot Copy r Q) x =
      if o=x.1 then 1 else 0 := by
  by_cases h : o=x.1 <;> simp [zOrbitRow,zWalsh,h]

def rowCoefficient (keep : ℕ→Prop) {hreg : ∀ v,GraphCutMoments.degree F v=3}
    (P : Seating F Copy r Q hreg) (j : Row keep Copy r Q) (v : Clone W) : ℤ :=
  ∑ s∈filled P.layout.orbitPlacement v,zOrbitRow CoordFamily j.val s

theorem rowCoefficient_cast (keep : ℕ→Prop) {hreg : ∀ v,GraphCutMoments.degree F v=3}
    (P : Seating F Copy r Q hreg) (j : Row keep Copy r Q) (v : Clone W) :
    (rowCoefficient keep P j v:ℚ) =
      rawMeasurement CoordFamily keep P.layout.orbitPlacement j v := by
  rw [rowCoefficient,rawMeasurement_apply,Int.cast_sum]
  simp_rw [zOrbitRow_cast]

omit [Fintype Copy] in
theorem zeroRow_counts (keep : ℕ→Prop) (h0 : keep 0)
    {hreg : ∀ v,GraphCutMoments.degree F v=3}
    (P : Seating F Copy r Q hreg) (o : Orbit Copy r Q) (v : Clone W) :
    rowCoefficient keep P (zeroRow keep h0 o) v =
      ((filled P.layout.orbitPlacement v).filter (fun s=>o=s.1)).card := by
  unfold rowCoefficient zeroRow
  simp only [weight_zero_indicator,←Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,mul_one]

omit [Fintype Copy] in
theorem zeroRow_has_positive_cover (keep : ℕ→Prop) (h0 : keep 0)
    {hreg : ∀ v,GraphCutMoments.degree F v=3}
    (P : Seating F Copy r Q hreg) (v : Clone W) :
    ∃ o : Orbit Copy r Q,
      (∀ w,0≤rowCoefficient keep P (zeroRow keep h0 o) w) ∧
      0 < rowCoefficient keep P (zeroRow keep h0 o) v := by
  obtain ⟨s,hs⟩ := Finset.card_pos.mp (filled_pos P.layout.orbitPlacement v)
  refine ⟨s.1,fun w=>?_,?_⟩
  · rw [zeroRow_counts]
    positivity
  · rw [zeroRow_counts]
    have hp : 0 < ((filled P.layout.orbitPlacement v).filter (fun t=>s.1=t.1)).card :=
      Finset.card_pos.mpr ⟨s,Finset.mem_filter.mpr ⟨hs,rfl⟩⟩
    exact_mod_cast hp

#print axioms occurrence_covers
#print axioms Seating.layout
#print axioms weight_zero_indicator
#print axioms rowCoefficient_cast
#print axioms zeroRow_counts
#print axioms zeroRow_has_positive_cover

end
end V8NativeMessage.N6.MainFiber
