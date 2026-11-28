import GuardedPacking
import OuterNodePacking
import RandomEndpoint
import PacketVariance
import GuardedEndpointVariance
import Mathlib.Tactic

/-!
# P11: from endpoint seats to unsupported physical equality vertices

The production layout records an original owner for every real column.
For each eligible degree-two equality, its entire original port fiber consists
of its two recorded seats. No shift wraps a packet or crosses into another
packet. Thus counting whole endpoint equalities lower-bounds the independent
equality bits left untouched by every shift of the corresponding sign.
-/
namespace P11SourceGeometry

open scoped BigOperators
open OuterNodePacking

section Geometry

variable {P E : Type*} [DecidableEq P] [DecidableEq E] {L : ℕ}

/-- Eligible degree-two vertices whose two actual seats both lie at the
specified endpoint. Counting both ports, not just one, is essential. -/
def seated (old : Finset E) (seat : E → Bool → Slot P L) (right : Bool) : Finset E :=
  old.filter fun e => (seat e false).2.val = GuardedPacking.endpoint L right ∧
    (seat e true).2.val = GuardedPacking.endpoint L right

omit [DecidableEq P] [DecidableEq E] in
theorem mem_seated (old : Finset E) (seat : E → Bool → Slot P L) (right : Bool) (e : E) :
    e ∈ seated old seat right ↔
      e ∈ old ∧ ∀ b, (seat e b).2.val = GuardedPacking.endpoint L right := by
  simp only [seated, Finset.mem_filter]
  constructor
  · rintro ⟨he,h₀,h₁⟩
    refine ⟨he,fun b => ?_⟩
    cases b
    · exact h₀
    · exact h₁
  · rintro ⟨he,h⟩
    exact ⟨he,h false,h true⟩

/-- Coverage of all original real ports of a degree-two column vertex.
Unused padding and columns owned by a different vertex are irrelevant. -/
def fullPortFiber (old : Finset E) (seat : E → Bool → Slot P L)
    (colReal : Slot P L → Bool) (owner : Slot P L → E) : Prop :=
  ∀ e ∈ old, ∀ y, colReal y = true → owner y = e → ∃ b, seat e b = y

/-- The literal predecessor condition in the older matched-columns module
makes an occupied endpoint impossible to match, without any small-shift
assumption or assumption on which rows are real. -/
theorem endpoint_not_matched (packets : Finset P) (rowReal colReal : Slot P L → Bool)
    (right : Bool) (t : ℤ) (ht : if right then t<0 else 0<t)
    (y : Slot P L) (hy : y.2.val = GuardedPacking.endpoint L right) :
    y ∉ matchedColumns packets rowReal colReal t := by
  intro hm
  obtain ⟨_,_,x,_,he⟩ := (mem_matchedColumns packets rowReal colReal t y).mp hm
  rw [hy] at he
  exact GuardedPacking.endpoint_no_predecessor
    (Nat.zero_lt_of_lt y.2.isLt) right ht _ x.isLt he

theorem seated_subset_untouched (old : Finset E) (packets : Finset P)
    (seat : E → Bool → Slot P L) (rowReal colReal : Slot P L → Bool)
    (owner : Slot P L → E) (hf : fullPortFiber old seat colReal owner)
    (right : Bool) (t : ℤ) (ht : if right then t<0 else 0<t) :
    seated old seat right ⊆ untouched old owner (matchedColumns packets rowReal colReal t) := by
  intro e he
  obtain ⟨he,hs⟩ := (mem_seated old seat right e).mp he
  refine Finset.mem_sdiff.mpr ⟨he,?_⟩
  intro hu
  obtain ⟨y,hy,howner⟩ := Finset.mem_image.mp hu
  have hreal := ((mem_matchedColumns packets rowReal colReal t y).mp hy).2.1
  obtain ⟨b,hb⟩ := hf e he y hreal howner
  exact (endpoint_not_matched packets rowReal colReal right t ht y
    (hb ▸ hs b)) hy

/-- Lower bound across every nonzero integer shift, and in particular the
actual retained grid. The exceptions are classified by sign, not by probe,
order, target mode, source word, or packing tie-breaking. -/
theorem both_endpoint_counts_le_every_shift (old : Finset E) (packets : Finset P)
    (seat : E → Bool → Slot P L) (rowReal colReal : Slot P L → Bool)
    (owner : Slot P L → E) (hf : fullPortFiber old seat colReal owner)
    (t : ℤ) (ht : t≠0) :
    min (seated old seat false).card (seated old seat true).card ≤
      (untouched old owner (matchedColumns packets rowReal colReal t)).card := by
  rcases lt_or_gt_of_ne ht with hnegative | hpositive
  · exact (min_le_right _ _).trans (Finset.card_le_card
      (seated_subset_untouched old packets seat rowReal colReal owner hf true t hnegative))
  · exact (min_le_left _ _).trans (Finset.card_le_card
      (seated_subset_untouched old packets seat rowReal colReal owner hf false t hpositive))

section Laws

variable {Ω : Type*} [Fintype Ω]

/-- Transfer *joint* success on the two endpoint counts to success at every
nonzero retained shift, for any law on the actual collection of layouts. -/
theorem endpoint_event_lower (old : Finset E) (packets : Finset P)
    (seat : Ω → E → Bool → Slot P L) (rowReal colReal : Ω → Slot P L → Bool)
    (owner : Ω → Slot P L → E) (hf : ∀ ω, fullPortFiber old (seat ω) (colReal ω) (owner ω))
    (s : Finset ℤ) (w : Ω → ℚ) (hw : ∀ ω, 0≤w ω) (T : ℚ) :
    RandomEndpoint.probability w
      (fun ω => T≤((seated old (seat ω) false).card:ℚ) ∧ T≤((seated old (seat ω) true).card:ℚ)) ≤
    RandomEndpoint.probability w
      (fun ω => ∀ t∈s, t≠0 →
        T≤((untouched old (owner ω) (matchedColumns packets (rowReal ω) (colReal ω) t)).card:ℚ)) := by
  apply RandomEndpoint.probability_mono _ _ _ hw
  intro ω h t _ ht
  have hgood : T ≤ (min (seated old (seat ω) false).card (seated old (seat ω) true).card : ℕ) := by
    rw [Nat.cast_min]
    exact le_min h.1 h.2
  exact hgood.trans (by exact_mod_cast (both_endpoint_counts_le_every_shift old packets (seat ω)
    (rowReal ω) (colReal ω) (owner ω) (hf ω) t ht))

/-- Combining checked finite concentration with literal predecessor geometry.
The hypotheses are moment bounds for counts of the two actual occupied ends,
not of arbitrary unrelated observables. -/
theorem p11_from_concrete_moments
    (old : Finset E) (packets : Finset P)
    (seat : Ω → E → Bool → Slot P L) (rowReal colReal : Ω → Slot P L → Bool)
    (owner : Ω → Slot P L → E) (hf : ∀ ω, fullPortFiber old (seat ω) (colReal ω) (owner ω))
    (s : Finset ℤ) (w : Ω → ℚ) (hw : PacketVariance.prob w)
    (A D b : ℚ) (hA : 0<A) (hL : 0<L) (hD : 0<D)
    (hmean : ∀ right, (1-1/b)*A ≤
      PacketVariance.avg w (fun ω => ((seated old (seat ω) right).card:ℚ)))
    (hvar : ∀ right, PacketVariance.variance w (fun ω => ((seated old (seat ω) right).card:ℚ)) ≤
      64*(L:ℚ)^3/D*A^2) :
    1-128*(L:ℚ)^7/D ≤
    RandomEndpoint.probability w (fun ω => ∀ t∈s, t≠0 →
       (1-1/b-1/(L:ℚ)^2)*A ≤
         ((untouched old (owner ω) (matchedColumns packets (rowReal ω) (colReal ω) t)).card:ℚ)) := by
  have hL' : (0:ℚ)<L := by exact_mod_cast hL
  have hc := RandomEndpoint.native_tail_from_moments w
     (fun ω => ((seated old (seat ω) false).card:ℚ))
     (fun ω => ((seated old (seat ω) true).card:ℚ)) _ _ A L D b
     hA hL' hD hw.1 hw.2 (hmean false) (hmean true) (hvar false) (hvar true)
  exact hc.trans (endpoint_event_lower old packets seat rowReal colReal owner hf s w hw.1 _)

end Laws
end Geometry

section Permutations

open RandomEndpoint

variable {A B : Type*}

/-- Pullback of a finite predicate is the union of all its fibers. -/
def fiberOverEquiv (f : A → B) (S : B → Prop) :
    {a // S (f a)} ≃ (Σ b : {b // S b}, {a // f a = b.val}) where
  toFun a := ⟨⟨_,a.prop⟩, ⟨a.val,rfl⟩⟩
  invFun x := ⟨x.2.val, x.2.prop.symm ▸ x.1.prop⟩
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨y,hy⟩,⟨a,ha⟩⟩
    change f a = y at ha
    subst y
    rfl

/-- A surjective map with equal nonzero finite fibers pushes the uniform
law to the uniform law. This uses the actual event cardinality. -/
theorem uniform_fiber_fraction [Fintype A] [Fintype B] [Nonempty A]
    (f : A → B) (surj : Function.Surjective f) (S : B → Prop)
    (uniform : ∀ b c, Nat.card {a // f a = b} = Nat.card {a // f a = c}) :
    (Nat.card {a // S (f a)} : ℚ) / (Nat.card A : ℚ) =
      (Nat.card {b // S b} : ℚ) / (Nat.card B : ℚ) := by
  classical
  let b₀ : B := f (Classical.arbitrary A)
  let k := Nat.card {a // f a = b₀}
  have hk : 0<k := by
    obtain ⟨a,ha⟩ := surj b₀
    letI : Nonempty {a // f a = b₀} := ⟨⟨a,ha⟩⟩
    exact Nat.card_pos
  have hCard (S : B → Prop) :
      Nat.card {a // S (f a)} = Nat.card {b // S b} * k := by
    rw [Nat.card_congr (fiberOverEquiv f S), Nat.card_eq_fintype_card,
      Nat.card_eq_fintype_card (α := {b // S b}), Fintype.card_sigma]
    have hh (b : {b // S b}) : Fintype.card {a // f a = b.val} = k := by
      rw [← Nat.card_eq_fintype_card]
      exact uniform b.val b₀
    simp [hh]
  have hAll : Nat.card A = Nat.card B * k := by
    simpa using hCard (fun _ => True)
  have hk' : (k:ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  rw [hCard S,hAll]
  push_cast
  letI : Nonempty B := ⟨b₀⟩
  have hb : (0:ℚ) < Fintype.card B := by exact_mod_cast (@Fintype.card_pos B _ _)
  field_simp

/-- Apply the full physical ordering to two distinguished distinct ports. -/
def pairImage {A : Type*} (p : DistinctPair A) (g : Equiv.Perm A) : DistinctPair A :=
  ⟨(g p.val.1,g p.val.2),fun h => p.prop (g.injective h)⟩

/-- Two swaps extend any prescribed injection of the two distinct indices
to an actual permutation of the whole cell. -/
theorem pairImage_exists [DecidableEq A] (p q : DistinctPair A) :
    ∃ g : Equiv.Perm A, pairImage p g=q := by
  let s := Equiv.swap p.val.1 q.val.1
  have hs : s p.val.1 = q.val.1 := Equiv.swap_apply_left _ _
  have hq : q.val.1 ≠ s p.val.2 := by
    intro h
    exact p.prop (s.injective (hs.trans h))
  let u := Equiv.swap (s p.val.2) q.val.2
  refine ⟨s.trans u, Subtype.ext (Prod.ext ?_ ?_)⟩
  · change u (s p.val.1) = q.val.1
    rw [hs]
    exact Equiv.swap_apply_of_ne_of_ne hq q.prop
  · exact Equiv.swap_apply_left _ _

theorem pairImage_trans (p : DistinctPair A) (g h : Equiv.Perm A) :
    pairImage p (g.trans h) = pairImage (pairImage p g) h := rfl

/-- Transport the fiber of one ordered image pair to the fiber of any other
by a permutation of the entire cell. The same construction keeps the mask. -/
def translatePairFiber (p q r : DistinctPair A) (g : Equiv.Perm A)
    (hg : pairImage q g=r) :
    {f : Equiv.Perm A // pairImage p f = q} ≃
      {f : Equiv.Perm A // pairImage p f = r} where
  toFun f := ⟨f.val.trans g, by rw [pairImage_trans,f.prop,hg]⟩
  invFun f := ⟨f.val.trans g.symm, by
    rw [pairImage_trans, f.prop, ← hg, ← pairImage_trans]
    simp [pairImage]⟩
  left_inv f := by
    apply Subtype.ext
    apply Equiv.ext
    intro a
    exact g.symm_apply_apply (f.val a)
  right_inv f := by
    apply Subtype.ext
    apply Equiv.ext
    intro a
    exact g.apply_symm_apply (f.val a)

def maskFiberEquiv (f : A → B) {M : Type*} (m : M × B) :
    {x : M × A // (x.1, f x.2) = m} ≃ {a : A // f a = m.2} where
  toFun x := ⟨x.val.2,congrArg Prod.snd x.prop⟩
  invFun a := ⟨(m.1,a.val),Prod.ext rfl a.prop⟩
  left_inv x := Subtype.ext (Prod.ext (congrArg Prod.fst x.prop).symm rfl)
  right_inv _ := rfl

/-- Starting from a uniform orientation mask and a uniform *full cell
permutation* gives exactly the two-point law RandomEndpoint computes.
No replacement or independence-of-ports approximation is inserted. -/
theorem physical_permutation_pair {s H : ℕ} (eligible : Fin s)
    (p : DistinctPair (Fin H)) (E : Finset (Fin H)) :
    (Nat.card {a : Fin s × Equiv.Perm (Fin H) //
       a.1=eligible ∧ a.2 p.val.1 ∈ E ∧ a.2 p.val.2 ∈ E} : ℚ) /
      (Nat.card (Fin s × Equiv.Perm (Fin H)) : ℚ) =
        RandomEndpoint.probPair eligible E := by
  classical
  let f : Fin s × Equiv.Perm (Fin H) → Fin s × DistinctPair (Fin H) :=
    fun x => (x.1,pairImage p x.2)
  let S : Fin s × DistinctPair (Fin H) → Prop :=
    fun x => x.1=eligible ∧ x.2.val.1∈E ∧ x.2.val.2∈E
  letI : Nonempty (Fin s × Equiv.Perm (Fin H)) := ⟨(eligible,Equiv.refl _)⟩
  have hs : Function.Surjective f := by
    rintro ⟨i,q⟩
    obtain ⟨g,hg⟩ := pairImage_exists p q
    exact ⟨(i,g),Prod.ext rfl hg⟩
  apply uniform_fiber_fraction f hs S
  intro x y
  obtain ⟨g,hg⟩ := pairImage_exists x.2 y.2
  exact Nat.card_congr ((maskFiberEquiv (pairImage p) x).trans
    ((translatePairFiber p x.2 y.2 g hg).trans (maskFiberEquiv (pairImage p) y).symm))

/-- Consequently the real without-replacement event in a physical cell
obeys the P11 lower bound as soon as the endpoint slot and mask cardinalities
are known. -/
theorem physical_sameType_lower {b s L : ℕ} (eligible : Fin s)
    (p : DistinctPair (Fin (b*L))) (E : Finset (Fin (b*L))) (hb : 0<b) (hL : 0<L)
    (hH : 1<b*L) (hE : E.card=b*s) :
    (1-1/(b:ℚ))/(L:ℚ)^2 ≤
     (Nat.card {a : Fin s × Equiv.Perm (Fin (b*L)) //
         a.1=eligible ∧ a.2 p.val.1∈E ∧ a.2 p.val.2∈E} : ℚ) /
        (Nat.card (Fin s × Equiv.Perm (Fin (b*L))) : ℚ) := by
  rw [physical_permutation_pair eligible p E]
  exact RandomEndpoint.sameType_lower eligible E hb hL hH hE

/-- Uniform full permutations also induce a uniform image of one port. -/
theorem physical_permutation_single {s H : ℕ} (eligible : Fin s)
    (p : Fin H) (E : Finset (Fin H)) :
    (Nat.card {a : Fin s × Equiv.Perm (Fin H) //
         a.1=eligible ∧ a.2 p∈E} : ℚ) /
      (Nat.card (Fin s × Equiv.Perm (Fin H)) : ℚ) =
    (Nat.card (SuccessSingle eligible E) : ℚ) / (Nat.card (Fin s × Fin H) : ℚ) := by
  classical
  let f : Fin s × Equiv.Perm (Fin H) → Fin s × Fin H := fun x => (x.1,x.2 p)
  let S : Fin s × Fin H → Prop := fun x => x.1=eligible ∧ x.2∈E
  letI : Nonempty (Fin s × Equiv.Perm (Fin H)) := ⟨(eligible,Equiv.refl _)⟩
  have hs : Function.Surjective f := by
    rintro ⟨i,q⟩
    exact ⟨(i,Equiv.swap p q),Prod.ext rfl (Equiv.swap_apply_left _ _)⟩
  apply uniform_fiber_fraction f hs S
  intro x y
  let g := Equiv.swap x.2 y.2
  have hx : g x.2 = y.2 := Equiv.swap_apply_left _ _
  have hy : g.symm y.2 = x.2 := g.symm_apply_eq.mpr hx.symm
  let u : {σ : Equiv.Perm (Fin H) // σ p=x.2} ≃ {σ : Equiv.Perm (Fin H) // σ p=y.2} :=
    { toFun := fun σ => ⟨σ.val.trans g, by change g (σ.val p)=y.2; rw [σ.prop,hx]⟩
      invFun := fun σ => ⟨σ.val.trans g.symm, by change g.symm (σ.val p)=x.2; rw [σ.prop,hy]⟩
      left_inv := fun σ => Subtype.ext (Equiv.ext fun a => g.symm_apply_apply (σ.val a))
      right_inv := fun σ => Subtype.ext (Equiv.ext fun a => g.apply_symm_apply (σ.val a)) }
  exact Nat.card_congr ((maskFiberEquiv (fun σ : Equiv.Perm (Fin H) => σ p) x).trans
      (u.trans (maskFiberEquiv (fun σ : Equiv.Perm (Fin H) => σ p) y).symm))

theorem physical_single_exact {b s L : ℕ} (eligible : Fin s) (p : Fin (b*L))
    (E : Finset (Fin (b*L))) (hb : 0<b) (hL : 0<L) (hE : E.card=b*s) :
    (Nat.card {a : Fin s × Equiv.Perm (Fin (b*L)) //
         a.1=eligible ∧ a.2 p∈E} : ℚ) /
      (Nat.card (Fin s × Equiv.Perm (Fin (b*L))) : ℚ) = 1/(L:ℚ) := by
  rw [physical_permutation_single eligible p E]
  exact RandomEndpoint.single_native eligible E hb hL hE

/-- A uniform weighted event is exactly the cardinality fraction. -/
theorem uniform_event_card {U : Type*} [Fintype U] (S : U → Prop) [DecidablePred S] :
    RandomEndpoint.probability (fun _ : U => 1/(Fintype.card U:ℚ)) S =
      (Nat.card {a // S a}:ℚ) / (Nat.card U:ℚ) := by
  rw [RandomEndpoint.probability, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
    Nat.card_eq_fintype_card, Nat.card_eq_fintype_card (α := U), Fintype.card_subtype]
  ring

end Permutations

section ProductLaws

variable {n : ℕ} {T : Fin n → Type*} [∀ i, Fintype (T i)]
open RandomEndpoint PacketVariance

/-- Probability of simultaneous events at independent finite type states.
This takes the *full* independent product, not just selected pair states. -/
theorem product_event (w : ∀ i, T i → ℚ) (S : ∀ i, T i → Prop)
    [∀ i, DecidablePred (S i)] :
    probability (product w) (fun a => ∀ i, S i (a i)) = ∏ i, probability (w i) (S i) := by
  classical
  unfold probability
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : ∀ i, S i (a i)
  · rw [if_pos h]
    exact Finset.prod_congr rfl fun i _ => (if_pos (h i)).symm
  · rw [if_neg h]
    push_neg at h
    obtain ⟨i,hi⟩ := h
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)).symm

/-- Congruence with unrelated decidability choices for the same event. -/
theorem event_congr {U : Type*} [Fintype U] (w : U → ℚ) (A B : U → Prop)
    [DecidablePred A] [DecidablePred B] (h : ∀ x, A x ↔ B x) :
    probability w A = probability w B := by
  unfold probability
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : A x
  · rw [if_pos hx, if_pos ((h x).mp hx)]
  · rw [if_neg hx, if_neg (fun hb => hx ((h x).mpr hb))]

/-- Only the j-th factor has a nontrivial event. The transport uses the
literal dependent coordinate, rather than equating different sample types. -/
def projectionEvent (j : Fin n) (S : T j → Prop) (i : Fin n) (x : T i) : Prop :=
  ∀ h : i=j, S (cast (congrArg T h) x)

omit [∀ i, Fintype (T i)] in
private theorem allProjection (j : Fin n) (S : T j → Prop) (a : ∀ i, T i) :
    (∀ i, projectionEvent (T:=T) j S i (a i)) ↔ S (a j) := by
  constructor
  · intro h
    exact h j rfl
  · intro h i hi
    subst i
    exact h

private theorem projectionProduct (w : ∀ i,T i → ℚ) (hw : ∀ i, prob (w i))
    (j : Fin n) (S : T j → Prop) [DecidablePred S]
    [∀ i, DecidablePred (projectionEvent (T:=T) j S i)] :
    (∏ i, probability (w i) (projectionEvent (T:=T) j S i)) = probability (w j) S := by
  rw [Finset.prod_eq_single j]
  · exact event_congr _ _ _ (by intro x; simp [projectionEvent])
  · intro i _ hi
    simp [probability, projectionEvent, hi, (hw i).2]
  · simp

/-- Reach one independently sampled type by a coordinate projection. This
also applies to a mask/one-cell marginal after using a product equivalence. -/
theorem product_event_one (w : ∀ i, T i → ℚ) (hw : ∀ i, prob (w i))
    (j : Fin n) (S : T j → Prop) [DecidablePred S] :
    probability (product w) (fun a => S (a j)) = probability (w j) S := by
  classical
  have he := event_congr (product w) (fun a => S (a j))
    (fun a => ∀ i, projectionEvent (T:=T) j S i (a i)) (fun a => (allProjection j S a).symm)
  exact he.trans ((product_event w _).trans (projectionProduct w hw j S))

/-- Distinct packet types are independent in the full finite random layout;
reusing the same type is intentionally excluded from this factorization. -/
theorem product_event_two (w : ∀ i,T i → ℚ) (hw : ∀ i, prob (w i))
    (j k : Fin n) (hne : j≠k) (S : T j → Prop) (R : T k → Prop)
    [DecidablePred S] [DecidablePred R] :
    probability (product w) (fun a => S (a j) ∧ R (a k)) =
      probability (w j) S * probability (w k) R := by
  classical
  let A := projectionEvent (T:=T) j S
  let B := projectionEvent (T:=T) k R
  have h : ∀ a : (∀ i, T i), (S (a j) ∧ R (a k)) ↔ (∀ i, A i (a i) ∧ B i (a i)) := by
    intro a
    constructor
    · intro hp i
      exact ⟨(allProjection j S a).mpr hp.1 i,(allProjection k R a).mpr hp.2 i⟩
    · intro hp
      exact ⟨(allProjection j S a).mp (fun i => (hp i).1),
        (allProjection k R a).mp (fun i => (hp i).2)⟩
  have hmul (i : Fin n) :
      probability (w i) (fun x => A i x ∧ B i x) =
       probability (w i) (A i) * probability (w i) (B i) := by
    by_cases hi : i=j
    · have hik : i≠k := fun g => hne (hi.symm.trans g)
      simp [probability, B, projectionEvent, hik, (hw i).2]
    · simp [probability, A, projectionEvent, hi, (hw i).2]
  calc
    _ = probability (product w) (fun a => ∀ i, A i (a i) ∧ B i (a i)) :=
      event_congr _ _ _ h
    _ = ∏ i, probability (w i) (fun x => A i x ∧ B i x) := product_event w (fun i x => A i x ∧ B i x)
    _ = (∏ i, probability (w i) (A i)) * (∏ i, probability (w i) (B i)) := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl (fun i _ => hmul i)
    _ = _ := by rw [projectionProduct w hw j S, projectionProduct w hw k R]

/-- A two-port equality uses the within-type joint law if its two ports
are in one type, and the product of their marginal laws otherwise. -/
theorem two_leg_marginal (w : ∀ i,T i → ℚ) (hw : ∀ i, prob (w i))
    (i j : Fin n) (A : T i → Prop) (B : T j → Prop)
    [DecidablePred A] [DecidablePred B] (c : ℚ)
    (same : ∀ h : i=j, c ≤ probability (w i) (fun x => A x ∧ B (cast (congrArg T h) x)))
    (split : i≠j → c ≤ probability (w i) A * probability (w j) B) :
    c ≤ probability (product w) (fun a => A (a i) ∧ B (a j)) := by
  by_cases h : i=j
  · subst j
    rw [product_event_one w hw i (fun x => A x ∧ B x)]
    exact same rfl
  · rw [product_event_two w hw i j h A B]
    exact split h

end ProductLaws

section FullBridge

open PacketVariance GuardedEndpointVariance
variable {E P : Type*} [Fintype E] [DecidableEq E] [DecidableEq P] {L n : ℕ}
  {T : Fin n → Type*} [∀ i, Fintype (T i)] [∀ i, Nonempty (T i)]

/-- The precise two-port owner chart. Each equality uses two distinct
incidences even if both belong to the same ordered cell. -/
def legs (e : E) : Finset (E × Bool) := {(e,false),(e,true)}

omit [DecidableEq P] [∀ i, Fintype (T i)] [∀ i, Nonempty (T i)] in
theorem picked_count_eq (Q : ∀ i, T i → Finset (E × Bool))
    (seat : (∀ i, T i) → E → Bool → Slot P L) (right : Bool) (a : ∀ i, T i)
    (hseat : ∀ e b, (e,b) ∈ picked Q a ↔
      (seat a e b).2.val = GuardedPacking.endpoint L right) :
    count Q legs a = ((seated Finset.univ (seat a) right).card:ℚ) := by
  unfold count
  suffices hh : guarded legs (picked Q a) = seated Finset.univ (seat a) right by rw [hh]
  ext e
  rw [guarded, Finset.mem_filter, mem_seated]
  simp only [Finset.mem_univ, true_and]
  constructor
  · intro h b
    apply (hseat e b).mp
    apply h
    cases b <;> simp [legs]
  · intro h p hp
    rcases p with ⟨e',b⟩
    have he : e'=e := by
      simp only [legs, Finset.mem_insert, Finset.mem_singleton] at hp
      exact hp.elim (congrArg Prod.fst) (congrArg Prod.fst)
    subst e'
    exact (hseat e b).mpr (h b)

omit [∀ i, Nonempty (T i)] in
theorem product_prob (w : ∀ i, T i → ℚ) (hw : ∀ i, PacketVariance.prob (w i)) :
    PacketVariance.prob (PacketVariance.product w) := by
  classical
  refine ⟨fun t => Finset.prod_nonneg (fun i _ => (hw i).1 (t i)), ?_⟩
  unfold PacketVariance.product
  rw [← Fintype.prod_sum]
  exact Finset.prod_eq_one fun i _ => (hw i).2

/-- Compose the machine-checked type-wise bounded-differences theorem with
the concrete physical owner and shift model. A lower bound on each actual
endpoint marginal still determines the mean; a standard scaling hypothesis
relates the integer packet counts to the padded grid. -/
theorem p11_from_product_counts
    (packets : Finset P) (seat : (∀ i, T i) → E → Bool → Slot P L)
    (rowReal colReal : (∀ i,T i) → Slot P L → Bool) (owner : (∀ i,T i) → Slot P L → E)
    (hcover : ∀ a, fullPortFiber Finset.univ (seat a) (colReal a) (owner a))
    (Q : Bool → ∀ i,T i → Finset (E × Bool))
    (hseat : ∀ right a e b, (e,b) ∈ picked (Q right) a ↔
        (seat a e b).2.val = GuardedPacking.endpoint L right)
    (w : ∀ i,T i → ℚ) (hw : ∀ i, PacketVariance.prob (w i))
    (cp : Fin n → ℕ) (H : ℕ) (hc : ∀ i, cp i ≤ H)
    (hQ : ∀ right i a, ((Q right) i a).card ≤ cp i)
    (s : Finset ℤ) (A D b : ℚ) (hA : 0<A) (hL : 0<L) (hD : 0<D)
    (hmean : ∀ right, (1-1/b)*A ≤
      PacketVariance.avg (PacketVariance.product w)
        (fun ω => ((seated Finset.univ (seat ω) right).card:ℚ)))
    (hscale : (H:ℚ) * (∑ i, (cp i:ℚ)) ≤ 64*(L:ℚ)^3/D*A^2) :
    1-128*(L:ℚ)^7/D ≤ RandomEndpoint.probability (PacketVariance.product w) (fun a => ∀ t∈s, t≠0 →
        (1-1/b-1/(L:ℚ)^2)*A ≤
          ((untouched Finset.univ (owner a) (matchedColumns packets (rowReal a) (colReal a) t)).card:ℚ)) := by
  apply p11_from_concrete_moments Finset.univ packets seat rowReal colReal owner hcover s
    (PacketVariance.product w) (product_prob w hw) A D b hA hL hD hmean
  intro right
  have heq : (fun ω => ((seated Finset.univ (seat ω) right).card:ℚ)) = count (Q right) legs := by
    funext a
    exact (picked_count_eq (Q right) seat right a (hseat right a)).symm
  rw [heq]
  refine (physical_variance (Q right) legs Prod.fst ?_ w cp H hw hc (hQ right)).trans hscale
  intro e p hp
  simp only [legs, Finset.mem_insert, Finset.mem_singleton] at hp
  exact hp.elim (congrArg Prod.fst) (congrArg Prod.fst)

end FullBridge

section MarginalMeans

variable {E P Ω : Type*} [Fintype E] [Fintype Ω] [DecidableEq E] [DecidableEq P] {L : ℕ}

omit [DecidableEq E] [DecidableEq P] in
/-- The exact expectation of the physical number of endpoint equalities
is at least the number of original equalities times a proved marginal bound.
There is no independence hypothesis between different equalities. -/
theorem mean_from_each_marginal (w : Ω → ℚ) (seat : Ω → E → Bool → Slot P L)
    (right : Bool) (c : ℚ)
    (h : ∀ e, c ≤ RandomEndpoint.probability w (fun a =>
       (seat a e false).2.val = GuardedPacking.endpoint L right ∧
       (seat a e true).2.val = GuardedPacking.endpoint L right)) :
    (Fintype.card E:ℚ)*c ≤ PacketVariance.avg w
      (fun a => ((seated Finset.univ (seat a) right).card:ℚ)) := by
  have hm := RandomEndpoint.expectation_count w _ _ h
  unfold PacketVariance.avg
  simpa only [seated, Finset.sum_boole] using hm

omit [DecidableEq E] [DecidableEq P] in
/-- Expectation from the actual seats and the same/distinct-type local
laws. A chart says which type owns each port and exactly what a hit is.
The same-type and distinct-type bounds are the respective finite laws from
the physical permutation checks above; no independence between different
equalities, or two ports within a type, is required. -/
theorem mean_from_type_laws {n : ℕ} {T : Fin n → Type*} [∀ i, Fintype (T i)]
    (w : ∀ i,T i → ℚ) (hw : ∀ i, PacketVariance.prob (w i))
    (seat : (∀ i,T i) → E → Bool → Slot P L)
    (right : Bool) (ty : E → Bool → Fin n)
    (hit : ∀ e b, T (ty e b) → Bool)
    (chart : ∀ a e b, (seat a e b).2.val = GuardedPacking.endpoint L right ↔
      hit e b (a (ty e b)) = true) (c : ℚ)
    (same : ∀ e (h : ty e false=ty e true),
      c ≤ RandomEndpoint.probability (w (ty e false)) (fun x =>
        hit e false x=true ∧ hit e true (cast (congrArg T h) x)=true))
    (split : ∀ e, ty e false≠ty e true →
      c ≤ RandomEndpoint.probability (w (ty e false)) (fun x => hit e false x=true) *
        RandomEndpoint.probability (w (ty e true)) (fun x => hit e true x=true)) :
    (Fintype.card E:ℚ)*c ≤ PacketVariance.avg (PacketVariance.product w)
      (fun a => ((seated Finset.univ (seat a) right).card:ℚ)) := by
  refine mean_from_each_marginal _ seat right c (fun e => ?_)
  have he := event_congr (PacketVariance.product w) _ _ (fun a =>
    and_congr (chart a e false) (chart a e true))
  rw [he]
  exact two_leg_marginal (T:=T) w hw (ty e false) (ty e true)
    (fun x => hit e false x=true) (fun x => hit e true x=true) c (same e) (split e)

end MarginalMeans

/-- When common column labels occur in one unordered type, the ordered row
labels are identical: an unordered pair plus its column component determines
its row component. This is why the within-type law is a same-cell law. -/
theorem one_type_same_column_one_cell {I K : Type*} [DecidableEq K]
    (r r' c : I → K) (h : ∀ i, ({r i,c i} : Finset K) = {r' i,c i}) :
    r=r' := by
  funext i
  have hr : r i ∈ ({r' i,c i} : Finset K) := h i ▸ (by simp)
  have hr' : r' i ∈ ({r i,c i} : Finset K) := (h i).symm ▸ (by simp)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hr hr'
  rcases hr with heq | heq
  · exact heq
  · rcases hr' with h' | h'
    · exact h'.symm
    · exact heq.trans h'.symm

theorem unique_endpoint_mask {I : Type*} (right : Bool) (cell : I → Bool) :
    ∃! m, GuardedPacking.endMask right m=cell := by
  refine ⟨GuardedPacking.endMask right cell, GuardedPacking.endMask_involutive right cell,?_⟩
  intro m hm
  exact (GuardedPacking.endMask_involutive right m).symm.trans (congrArg _ hm)

/-- Unused cell permutations or any other factors of the full randomness
sum out: a normalized law on the other factor contributes exactly 1. -/
theorem ignore_unread_product {U V : Type*} [Fintype U] [Fintype V]
    (w : U → ℚ) (v : V → ℚ) (hv : PacketVariance.prob v)
    (E : U → Prop) [DecidablePred E] :
    RandomEndpoint.probability (PacketVariance.prodWeight w v) (fun x : U×V => E x.1) =
    RandomEndpoint.probability w E := by
  unfold RandomEndpoint.probability PacketVariance.prodWeight
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun u _ => ?_
  by_cases hu : E u
  · simp [hu, ← Finset.mul_sum, hv.2]
  · simp [hu]

#print axioms mem_seated
#print axioms endpoint_not_matched
#print axioms seated_subset_untouched
#print axioms both_endpoint_counts_le_every_shift
#print axioms endpoint_event_lower
#print axioms p11_from_concrete_moments
#print axioms uniform_fiber_fraction
#print axioms pairImage_exists
#print axioms pairImage_trans
#print axioms physical_permutation_pair
#print axioms physical_sameType_lower
#print axioms picked_count_eq
#print axioms product_prob
#print axioms p11_from_product_counts
#print axioms mean_from_each_marginal
#print axioms physical_permutation_single
#print axioms physical_single_exact
#print axioms uniform_event_card
#print axioms product_event
#print axioms event_congr
#print axioms product_event_one
#print axioms product_event_two
#print axioms two_leg_marginal
#print axioms mean_from_type_laws
#print axioms one_type_same_column_one_cell
#print axioms unique_endpoint_mask
#print axioms ignore_unread_product

end P11SourceGeometry