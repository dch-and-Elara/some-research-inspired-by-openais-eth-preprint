
import S11Schedule
import Mathlib.Data.List.Nodup

noncomputable section
namespace S11
open scoped BigOperators

theorem tuples_nodup (ws : List ℕ) (p : ℕ) : (tuples ws p).Nodup := by
  induction ws generalizing p with
  | nil => by_cases hp : p = 0 <;> simp [tuples, hp]
  | cons w ws ih =>
    by_cases hp : p = 0
    · simp [tuples, hp]
    rw [tuples, if_neg hp, List.nodup_flatMap]
    refine ⟨?_, ?_⟩
    · intro b _
      exact (ih _).map (fun _ _ h => List.cons.inj h |>.2)
    · apply List.nodup_range.imp
      intro b c hne
      simp only [List.disjoint_left, List.mem_map]
      rintro x ⟨xs,_,rfl⟩ ⟨ys,_,he⟩
      exact hne (List.cons.inj he).1.symm

variable {Z : Type*} [DecidableEq Z]

/-- The exponent vector is stored in the same order as the packet mode list. -/
def readExponent : List Z → List ℕ → Z → ℕ
  | z :: zs, b :: bs, t => if t = z then b else readExponent zs bs t
  | _, _, _ => 0

theorem readExponent_map (zs : List Z) (β : Z → ℕ) (z : Z) (hz : z ∈ zs) :
    readExponent zs (zs.map β) z = β z := by
  induction zs with
  | nil => simp at hz
  | cons t ts ih =>
    by_cases h : z = t
    · subst t
      simp [readExponent]
    · simp [readExponent, h, ih ((List.mem_cons.1 hz).resolve_left h)]

theorem encode_readExponent (zs : List Z) (bs : List ℕ)
    (hz : zs.Nodup) (hl : bs.length = zs.length) :
    zs.map (readExponent zs bs) = bs := by
  induction zs generalizing bs with
  | nil => simp_all
  | cons z zs ih =>
    cases bs with
    | nil => simp at hl
    | cons b bs =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      simp only [List.nodup_cons] at hz
      simp only [List.map_cons, readExponent, List.cons.injEq, eq_self, if_true, true_and]
      calc
        _ = zs.map (readExponent zs bs) := by
          apply List.map_inj_left.mpr
          intro t ht
          exact if_neg (show t ≠ z from fun h => hz.1 (h ▸ ht))
        _ = _ := ih bs hz.2 hl

omit [DecidableEq Z] in
theorem weightSum_encoding (zs : List Z) (weight β : Z → ℕ) :
    weightSum (zs.map weight) (zs.map β) = (zs.map fun z => weight z * β z).sum := by
  induction zs with
  | nil => rfl
  | cons z zs ih => simp [weightSum, ih]

variable [Fintype Z]
open Classical

def orderedFiber (weight : Z → ℕ) (p : ℕ) : Finset (Z → Fin p) :=
  Finset.univ.filter fun β => (∑ z, weight z * (β z).val) < p

private theorem sum_weights (zs : List Z) (nodup : zs.Nodup) (covers : ∀ z, z ∈ zs)
    (f : Z → ℕ) : (zs.map f).sum = ∑ z, f z := by
  have hz : zs.toFinset = Finset.univ := by ext z; simp [covers]
  rw [← Multiset.sum_coe, ← Multiset.map_coe]
  change (Multiset.map f (zs : Multiset Z)).sum = _
  rw [← List.dedup_eq_self.mpr nodup]
  change (∑ z ∈ zs.toFinset, f z) = _
  rw [hz]

/-- The exact ordered tuple sum is the semantic weighted-mode sum.
    Distinct DFS leaves implement distinct exponent functions. -/
theorem tuple_sum_eq {R : Type*} [AddCommMonoid R] (zs : List Z) (nodup : zs.Nodup)
    (covers : ∀ z, z ∈ zs) (weight : Z → ℕ) (hw : ∀ z, 0 < weight z) (p : ℕ)
    (term : (Z → ℕ) → R) :
    ((tuples (zs.map weight) p).map (fun bs => term (readExponent zs bs))).sum =
      ∑ β ∈ orderedFiber weight p, term (fun z => (β z).val) := by
  classical
  let L := tuples (zs.map weight) p
  have hw' : ∀ w ∈ zs.map weight, 0 < w := by
    intro w h
    obtain ⟨z,_,rfl⟩ := List.mem_map.1 h
    exact hw z
  have hfin (bs) (hbs : bs ∈ L) : ∑ z, weight z * readExponent zs bs z < p := by
    obtain ⟨hl,hb⟩ := (mem_tuples hw').1 hbs
    rw [List.length_map] at hl
    rw [← sum_weights zs nodup covers, ← weightSum_encoding, encode_readExponent zs bs nodup hl]
    exact hb
  let f (bs : List ℕ) (h : bs ∈ L.toFinset) : Z → Fin p := fun z =>
    ⟨readExponent zs bs z, by
      apply lt_of_le_of_lt _ (hfin bs (List.mem_toFinset.1 h))
      refine (Nat.le_mul_of_pos_left _ (hw z)).trans ?_
      exact Finset.single_le_sum (f := fun z => weight z * readExponent zs bs z)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ z)⟩
  have hL (bs) (hbs : bs ∈ L.toFinset) : bs.length = zs.length := by
    have hh := ((mem_tuples hw').1 (List.mem_toFinset.1 hbs)).1
    simpa using hh
  have hsum : ((L.map fun bs => term (readExponent zs bs)).sum) =
      ∑ bs ∈ L.toFinset, term (readExponent zs bs) := by
    rw [← Multiset.sum_coe, ← Multiset.map_coe]
    change (Multiset.map (fun bs => term (readExponent zs bs)) (L : Multiset (List ℕ))).sum = _
    have hn : L.Nodup := tuples_nodup _ _
    conv_lhs => rw [← List.dedup_eq_self.mpr hn]
    rfl
  rw [hsum]
  refine Finset.sum_bij f ?_ ?_ ?_ ?_
  · intro bs hbs
    simp [orderedFiber, f, hfin bs (List.mem_toFinset.1 hbs)]
  · intro bs hs cs hc he
    rw [← encode_readExponent zs bs nodup (hL bs hs), ← encode_readExponent zs cs nodup (hL cs hc)]
    apply congrArg (List.map · zs)
    funext z
    exact congrArg Fin.val (congrFun he z)
  · intro β hβ
    let bs := zs.map (fun z => (β z).val)
    have hbs : bs ∈ L.toFinset := by
      apply List.mem_toFinset.2
      apply (mem_tuples hw').2
      refine ⟨by simp [bs], ?_⟩
      change weightSum (zs.map weight) (zs.map fun z => (β z).val) < p
      rw [weightSum_encoding, sum_weights zs nodup covers]
      simpa [orderedFiber] using hβ
    refine ⟨bs,hbs,?_⟩
    funext z
    exact Fin.ext (readExponent_map zs _ z (covers z))
  · intro bs hbs
    rfl

#print axioms tuples_nodup
#print axioms tuple_sum_eq

end S11

