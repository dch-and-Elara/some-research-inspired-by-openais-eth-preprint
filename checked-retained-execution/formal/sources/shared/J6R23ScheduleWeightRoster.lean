import J6R23ScheduleWeightFold
import J6R22ActiveScaled
import J6R9RecursiveWeights

/-! An actual tapered address roster, not a supplied integer-weight
table. Omitted nonretained grid nodes have exponent zero in the
printed numerator and denominator and so contribute exactly one. -/
namespace J6R23ScheduleWeight
open scoped BigOperators
open P1DyadicGrid HermiteLoss J6ActiveSchedule J6R22Active J6R9Hermite
open AOracleSuccinctNative

structure Roster (a M u : ℕ) (t : ℤ) where
  rows : List (ℤ×ℕ)
  distinct : (rows.map Prod.fst).Nodup
  complete : (rows.map Prod.fst).toFinset=(active a M u).erase t
  exponents : ∀ q∈rows,q.2=order M u q.1

variable {a M u : ℕ} {t : ℤ}

theorem Roster.in_active (L : Roster a M u t) (q : ℤ×ℕ) (hx : q∈L.rows) :
    q.1∈active a M u ∧ q.1≠t := by
  have h : q.1∈(active a M u).erase t := by
    rw [←L.complete,List.mem_toFinset]
    exact List.mem_map_of_mem hx
  exact ⟨(Finset.mem_erase.mp h).2,(Finset.mem_erase.mp h).1⟩

theorem Roster.is_grid (L : Roster a M u t) (q : ℤ×ℕ) (hx : q∈L.rows) : q.1∈grid a :=
  (J6R9Recursive.active_grid a M u (L.in_active q hx).1).1

theorem Roster.nonzero (L : Roster a M u t) (b : Side) (q : ℤ×ℕ) (hx : q∈L.rows) :
    signedFactor t b q.1≠0 := by
  cases b
  · exact neg_ne_zero.mpr (J6R9Recursive.active_grid a M u (L.in_active q hx).1).2
  · exact sub_ne_zero.mpr (L.in_active q hx).2.symm

theorem Roster.baseProduct (L : Roster a M u t) (b : Side) :
    intParts t b L.rows=
      ∏ q∈others a t, signedFactor t b q^taper u (sourceH M u) (level q) := by
  classical
  let G := fun q : ℤ=> (signedFactor t b q)^taper u (sourceH M u) (level q)
  have he : (L.rows.map (fun q=>signedFactor t b q.1^q.2))=(L.rows.map Prod.fst).map G := by
    rw [List.map_map]
    apply List.map_congr_left
    intro q hq
    exact congrArg (fun n=>signedFactor t b q.1^n) (L.exponents q hq)
  unfold intParts
  rw [he,←List.prod_toFinset G L.distinct,L.complete]
  apply Finset.prod_subset
  · intro q hq
    obtain ⟨hn,hq⟩ := Finset.mem_erase.mp hq
    have hg := J6R9Recursive.active_grid a M u hq
    exact mem_others.mpr ⟨hg.1,hg.2,hn⟩
  · intro q hq hn
    obtain ⟨hg,hz,hqt⟩ := mem_others.mp hq
    have h0 : order M u q=0 := by
      by_contra! h
      exact hn (Finset.mem_erase.mpr ⟨hqt,Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hz,hg⟩,by omega⟩⟩)
    change (signedFactor t b q)^order M u q=1
    rw [h0,pow_zero]

theorem Roster.numerator_parts (L : Roster a M u t) (ht : t∈active a M u) (j : ℕ) :
    let xs := L.rows++[(t,j)]
    countParts t .num xs=level (weightNum a u (sourceH M u) j t) ∧
      oddParts t .num xs=oddWord (weightNum a u (sourceH M u) j t) := by
  have hz := (J6R9Recursive.active_grid a M u ht).2
  let xs := L.rows++[(t,j)]
  have hn (q : ℤ×ℕ) (hq : q∈xs) : signedFactor t .num q.1≠0 := by
    rcases List.mem_append.mp hq with a | b
    · exact L.nonzero .num q a
    · rw [List.mem_singleton] at b
      subst q
      exact neg_ne_zero.mpr hz
  have e : intParts t .num xs=weightNum a u (sourceH M u) j t := by
    unfold xs intParts
    simp only [List.map_append,List.prod_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]
    rw [show (List.map (fun q=>signedFactor t .num q.1^q.2) L.rows).prod=
      numerator a u (sourceH M u) t from L.baseProduct .num]
    rfl
  obtain ⟨he,ho⟩ := intParts_split t .num xs hn
  rw [e] at he
  obtain ⟨hV,hO⟩ := odd_factor_recovers_word he ho
  exact ⟨hV.symm,hO.symm⟩

theorem Roster.denominator_parts (L : Roster a M u t) (j : ℕ) :
    countParts t .den L.rows+(a+1)*j=level (weightDen a u (sourceH M u) j t) ∧
      oddParts t .den L.rows=oddWord (weightDen a u (sourceH M u) j t) := by
  obtain ⟨hD,hO⟩ := intParts_split t .den L.rows (L.nonzero .den)
  have he : intParts t .den L.rows=denominator a u (sourceH M u) t := L.baseProduct .den
  have hF : weightDen a u (sourceH M u) j t=
      pow₂ (countParts t .den L.rows+(a+1)*j)*oddParts t .den L.rows := by
    rw [weightDen,←he,hD]
    simp only [pow₂,pow_mul,pow_add]
    ring
  exact ⟨(odd_factor_recovers_word hF hO).1.symm,(odd_factor_recovers_word hF hO).2.symm⟩

#print axioms Roster.baseProduct
#print axioms Roster.numerator_parts
#print axioms Roster.denominator_parts
end J6R23ScheduleWeight


