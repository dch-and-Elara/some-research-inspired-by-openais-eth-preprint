import J1MainSourceCollision

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false

/-! A source factor coordinate can use its own tied generator. Distinct
coordinates have disjoint generator tags. Variable words are unchanged. -/
namespace Paper5.HybridMainOnly
open scoped Classical BigOperators
open J1MainSourceLabels J1MainSourceCollision DiagonalAbundance

noncomputable section
variable {I S E V F B : Type*}
variable [Fintype I] [DecidableEq I] [Fintype S] [Nonempty S]
variable [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F] [Fintype B] [DecidableEq B]

def factorKeyAt (ties : I→F→Option B) (f : F) (j : I) : Primitive V F B I :=
  match ties j f with
  | none => .inr (.inl (f,j))
  | some b => .inr (.inr b)

def factorAt (ties : I→F→Option B) (cfg : Primitive V F B I→S) (f : F) (j : I) : S :=
  cfg (factorKeyAt ties f j)

def twoCell (ties : I→F→Option B) (var : E→V) (fac : E→F)
    (cfg : Primitive V F B I→S) (e : E) : Draw I S :=
  (variableWord cfg (var e),factorAt ties cfg (fac e))

def DisjointCoordinates (ties : I→F→Option B) : Prop :=
  ∀ j j' f f' b, ties j f=some b → ties j' f'=some b → j=j'

theorem factor_key_inj_of_no_shared (ties : I→F→Option B)
    (sep : DisjointCoordinates ties) (pf : Bool↪F)
    (disj : ∀ j b, ¬(ties j (pf false)=some b ∧ ties j (pf true)=some b)) :
    Function.Injective (fun x : Bool×I => (factorKeyAt ties (pf x.1) x.2 : Primitive V F B I)) := by
  rintro ⟨u,j⟩ ⟨v,k⟩ h
  change factorKeyAt ties (pf u) j = factorKeyAt ties (pf v) k at h
  cases hj : ties j (pf u) <;> cases hk : ties k (pf v)
  · have ht : (pf u,j)=(pf v,k) := by simpa [factorKeyAt,hj,hk] using h
    exact Prod.ext (pf.injective (congrArg Prod.fst ht)) (congrArg (fun x : F×I => x.2) ht)
  · simp [factorKeyAt,hj,hk] at h
  · simp [factorKeyAt,hj,hk] at h
  · rename_i b b'
    have hb : b=b' := by simpa [factorKeyAt,hj,hk] using h
    subst b'
    have hjk := sep j k (pf u) (pf v) b hj hk
    subst k
    have huv : u=v := by
      cases u <;> cases v
      · rfl
      · exact False.elim (disj j b ⟨hj,hk⟩)
      · exact False.elim (disj j b ⟨hk,hj⟩)
      · rfl
    exact Prod.ext huv rfl

def pairKey (ties : I→F→Option B) (pv : Bool↪V) (pf : Bool↪F)
    (x : Bool×Bool×I) : Primitive V F B I :=
  if x.2.1 then factorKeyAt ties (pf x.1) x.2.2 else .inl (pv x.1,x.2.2)

theorem pair_key_inj (ties : I→F→Option B) (sep : DisjointCoordinates ties)
    (pv : Bool↪V) (pf : Bool↪F)
    (disj : ∀ j b, ¬(ties j (pf false)=some b ∧ ties j (pf true)=some b)) :
    Function.Injective (pairKey ties pv pf) := by
  rintro ⟨u,left,j⟩ ⟨v,right,k⟩ h
  cases left <;> cases right
  · have hv : (pv u,j)=(pv v,k) := by simpa [pairKey] using h
    exact Prod.ext (pv.injective (congrArg Prod.fst hv)) (Prod.ext rfl (congrArg (fun x : V×I => x.2) hv))
  · unfold pairKey at h
    cases ht : ties k (pf v) <;> simp [factorKeyAt,ht] at h
  · unfold pairKey at h
    cases ht : ties j (pf u) <;> simp [factorKeyAt,ht] at h
  · have hh : factorKeyAt (V:=V) ties (pf u) j=factorKeyAt ties (pf v) k := by simpa [pairKey] using h
    have hx : (u,j)=(v,k) := factor_key_inj_of_no_shared (V:=V) ties sep pf disj hh
    have huv : u=v := congrArg (fun x : Bool×I=>x.1) hx
    have hjk : j=k := congrArg (fun x : Bool×I=>x.2) hx
    subst v
    subst k
    rfl

/-- Outside the common graph-defined bad pair set, the two full cells
are independent, not just the two tied factor digits. -/
theorem two_cells_coincide (ties : I→F→Option B) (sep : DisjointCoordinates ties)
    (var : E→V) (fac : E→F) (e e' : E)
    (hv : var e≠var e') (hf : fac e≠fac e')
    (disj : ∀ j b, ¬(ties j (fac e)=some b ∧ ties j (fac e')=some b)) :
    mean (fun cfg : Primitive V F B I→S => indicator
      (twoCell ties var fac cfg e=twoCell ties var fac cfg e'))=
      1/(Fintype.card (Draw I S):ℚ) := by
  let pv := twoDistinct (var e) (var e') hv
  let pf := twoDistinct (fac e) (fac e') hf
  have hn (j : I) (b : B) : ¬(ties j (pf false)=some b ∧ ties j (pf true)=some b) :=
    disj j b
  let key : Bool×Bool×I↪Primitive V F B I := ⟨pairKey ties pv pf,pair_key_inj ties sep pv pf hn⟩
  let Tail := {p // p∉Set.range key}→S
  letI : Fintype Tail := Fintype.ofFinite Tail
  letI : Nonempty Tail := ⟨fun _ => Classical.choice inferInstance⟩
  let split := chart (S:=S) key
  let h : (Bool→Draw I S)→ℚ := fun w => indicator (w false=w true)
  let H : (Bool→Draw I S)×Tail→ℚ := fun w => h w.1
  have point (cfg : Primitive V F B I→S) (u : Bool) :
      (split cfg).1 u=twoCell ties var fac cfg (if u then e' else e) := by
    apply Prod.ext
    · funext j
      rw [(chart_first_of_key key cfg u j).1]
      cases u <;> rfl
    · funext j
      rw [(chart_first_of_key key cfg u j).2]
      cases u <;> rfl
  have he : (fun cfg : Primitive V F B I→S => indicator
      (twoCell ties var fac cfg e=twoCell ties var fac cfg e')) = fun cfg => H (split cfg) := by
    funext cfg
    unfold H h
    rw [point cfg false,point cfg true]
    rfl
  rw [he,mean_equiv split H,show mean H=mean h from mean_extra h]
  exact independent_coincidence (D:=Draw I S) false true (by decide)

#print axioms factor_key_inj_of_no_shared
#print axioms pair_key_inj
#print axioms two_cells_coincide
end
end Paper5.HybridMainOnly