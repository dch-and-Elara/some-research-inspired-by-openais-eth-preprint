import P5MainBalanceGroupedFibers

/-! The MAIN assignment fiber is literally the exceptional-matrix tuple
together with the Boolean Taylor restriction, not an assumed product
domain. Infeasible tuples simply give an empty factor. -/
namespace P5MainBalance
open scoped BigOperators Classical
open P5MainIterator

variable {E X F Copy I B V R : Type*} [Fintype E] [Fintype X] [Fintype Copy]
  [Fintype I] [Fintype B] [LinearOrder B] [CommSemiring R]

abbrev NativeRows (keep : ℕ→Prop) (Copy I B : Type*) [Fintype I] [LinearOrder B] :=
  Exceptional (CoordFamily (Copy:=Copy) (I:=I) (B:=B)) keep

def padGroup (a : X→B) (g : B) (x : GroupBits a g) : X→Bool :=
  fun u=>if h:a u=g then x ⟨u,h⟩ else false

theorem literal_measurement_depends_on_group (keep : ℕ→Prop) (L : SourceLayout E X F Copy I B)
    (t : I) (g : B) (x : X→Bool) :
    sourceTuple keep L t (padGroup (fun v=>L.a v t) g (restrictGroup _ x g)) g =
      sourceTuple keep L t x g := by
  unfold sourceTuple
  apply congrArg (Matrix.mulVec (exceptionalMatrix keep L))
  funext v
  by_cases h : L.a v t = g <;> simp [padGroup,restrictGroup,h]

noncomputable def actualGate (keep : ℕ→Prop) (L : SourceLayout E X F Copy I B)
    (t : I) (p : Finset X) (y : B→NativeRows keep Copy I B→ℚ)
    (g : B) (x : GroupBits (fun v=>L.a v t) g) : Prop :=
  sourceTuple keep L t (padGroup _ g x) g = y g ∧
    ∀ v : {v : X//L.a v t=g}, v.val∈p → x v=true

theorem exact_native_fibre_predicate (keep : ℕ→Prop) (L : SourceLayout E X F Copy I B)
    (t : I) (p : Finset X) (y : B→NativeRows keep Copy I B→ℚ) (x : X→Bool) :
    (∀ g,actualGate keep L t p y g (restrictGroup (fun v=>L.a v t) x g)) ↔
      sourceTuple keep L t x=y ∧ ∀ v∈p,x v=true := by
  unfold actualGate
  simp_rw [literal_measurement_depends_on_group]
  constructor
  · intro h
    exact ⟨funext (fun g=>(h g).1),fun v hv=>(h (L.a v t)).2 ⟨v,rfl⟩ hv⟩
  · rintro ⟨hm,hp⟩ g
    exact ⟨congrFun hm g,fun v hv=>hp v.val hv⟩

set_option maxHeartbeats 7400000 in
theorem source_fibre_update_is_group_term (keep : ℕ→Prop) (L : SourceLayout E X F Copy I B)
    (t : I) (p : Finset X) (y : B→NativeRows keep Copy I B→ℚ)
    (d : V→I→B) (σ : V→Bool)
    (localFactor : ∀ g : B, ({v : V//d v t=g}→Bool)→GroupBits (fun v=>L.a v t) g→R) :
    (actualFibreMacro d t (fun v=>L.a v t) (actualGate keep L t p y) localFactor).value σ =
      ∑ x : {x : X→Bool // sourceTuple keep L t x=y ∧ ∀ v∈p,x v=true},
        ∏ g,localFactor g (fun v=>σ v.val) (restrictGroup (fun v=>L.a v t) x.val g) := by
  let e := Equiv.subtypeEquivRight (exact_native_fibre_predicate keep L t p y)
  rw [exact_grouped_fibre_update]
  exact (e.symm.sum_comp (fun x : CombinedFiber (fun v=>L.a v t) (actualGate keep L t p y) =>
    ∏ g,localFactor g (fun v=>σ v.val) (restrictGroup (fun v=>L.a v t) x.val g))).symm

#print axioms literal_measurement_depends_on_group
#print axioms exact_native_fibre_predicate
#print axioms source_fibre_update_is_group_term
end P5MainBalance
