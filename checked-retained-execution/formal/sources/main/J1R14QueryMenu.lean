import J1R14QueryTape
import Mathlib.Data.List.Sublists

/-! The actual source enumeration of (E,U) after applying the order cap:
the algorithm never constructs a table of all length-n three-state words
and filters afterwards. Each outer operation calls the explicit
exact-cardinality sublist generator on [n], then sublists of that E. -/
namespace J1R14Query
open scoped BigOperators

abbrev Pair (n : ℕ) := Finset (Fin n) × Finset (Fin n)

def pairLayer (n s : ℕ) : List (Pair n) :=
  ((List.finRange n).sublistsLen s).flatMap (fun E =>
    E.sublists.map (fun U => (E.toFinset,U.toFinset)))

def pairs (n q : ℕ) : List (Pair n) :=
  (List.range (min q n+1)).flatMap (pairLayer n)

theorem pairLayer_length (n s : ℕ) :
    (pairLayer n s).length = 2^s * n.choose s := by
  unfold pairLayer
  generalize hl : (List.finRange n).sublistsLen s = es
  have hE (E : List (Fin n)) (h : E ∈ es) : E.length = s := by
    rw [← hl] at h
    exact (List.mem_sublistsLen.mp h).2
  have hlen :
      (es.flatMap fun E => E.sublists.map fun U => (E.toFinset,U.toFinset)).length =
      es.length * 2^s := by
    clear hl
    induction es with
    | nil => simp
    | cons E es ih =>
      have he := hE E (by simp)
      rw [List.flatMap_cons,List.length_append,List.length_map,List.length_sublists,he,
        ih (fun E h => hE E (List.mem_cons_of_mem _ h))]
      simp [Nat.succ_mul,add_comm]
  rw [hlen,← hl,List.length_sublistsLen,List.length_finRange,Nat.mul_comm]

theorem pairs_length (n q : ℕ) :
    (pairs n q).length = ∑ s ∈ Finset.range (min q n+1), 2^s * n.choose s := by
  have hlen (k : ℕ) :
      ((List.range k).flatMap (pairLayer n)).length =
      ∑ s ∈ Finset.range k, 2^s * n.choose s := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [List.range_succ,List.flatMap_append,List.length_append,ih,
        Finset.sum_range_succ]
      simp [pairLayer_length]
  exact hlen _

theorem ordered_toFinset {n : ℕ} (E : Finset (Fin n)) :
    ((List.finRange n).filter fun j => decide (j∈E)).toFinset = E := by
  ext j
  simp

/-- Every enumerated pair is exactly one legal finite-difference address;
every legal pair occurs. Multiplicity is separately exposed by length. -/
theorem mem_pairs {n q : ℕ} (E U : Finset (Fin n)) :
    (E,U) ∈ pairs n q ↔ U ⊆ E ∧ E.card ≤ q := by
  constructor
  · intro h
    obtain ⟨s,hs,h⟩ := List.mem_flatMap.mp h
    obtain ⟨es,hes,h⟩ := List.mem_flatMap.mp h
    obtain ⟨us,hus,he⟩ := List.mem_map.mp h
    have hs' := List.mem_range.mp hs
    have hes' := List.mem_sublistsLen.mp hes
    have hus' := List.mem_sublists.mp hus
    have hnod := hes'.1.nodup (List.nodup_finRange _)
    obtain ⟨hE,hU⟩ := Prod.mk.inj he
    refine ⟨?_,?_⟩
    · intro j hj
      rw [← hU,List.mem_toFinset] at hj
      rw [← hE,List.mem_toFinset]
      exact hus'.subset hj
    · rw [← hE,List.toFinset_card_of_nodup hnod,hes'.2]
      omega
  · rintro ⟨hun,heq⟩
    let es := (List.finRange n).filter fun j => decide (j∈E)
    let us := es.filter fun j => decide (j∈U)
    have hEt : es.toFinset = E := ordered_toFinset E
    have husub : List.Sublist us es := List.filter_sublist
    have hUt : us.toFinset = U := by
      ext j
      simp only [us,List.mem_toFinset,List.mem_filter,decide_eq_true_eq]
      rw [show j ∈ es ↔ j ∈ E by rw [← hEt,List.mem_toFinset]]
      exact ⟨fun h => h.2,fun h => ⟨hun h,h⟩⟩
    have hsub : List.Sublist es (List.finRange n) := List.filter_sublist
    have hlen : es.length = E.card := by
      rw [← hEt,List.toFinset_card_of_nodup (hsub.nodup (List.nodup_finRange _))]
    have hb : E.card ≤ n := by
      simpa only [Finset.card_univ,Fintype.card_fin] using E.card_le_univ
    apply List.mem_flatMap.mpr
    refine ⟨E.card,List.mem_range.mpr (by omega),?_⟩
    apply List.mem_flatMap.mpr
    refine ⟨es,List.mem_sublistsLen.mpr ⟨hsub,hlen⟩,?_⟩
    exact List.mem_map.mpr ⟨us,List.mem_sublists.mpr husub,by rw [hEt,hUt]⟩

theorem pairs_length_all (n q : ℕ) (hq : n ≤ q) :
    (pairs n q).length = 3^n := by
  rw [pairs_length,min_eq_right hq]
  simpa using (add_pow (2:ℕ) 1 n).symm

#print axioms pairLayer_length
#print axioms pairs_length
#print axioms mem_pairs
#print axioms pairs_length_all
end J1R14Query
