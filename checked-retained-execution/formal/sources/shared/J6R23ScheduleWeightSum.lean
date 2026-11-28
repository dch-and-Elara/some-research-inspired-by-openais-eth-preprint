import J6R23ScheduleWeightTerm

/-! The actual two-level weighted pass; not a ring oracle for all
sites. Each term callback is visited and its full incurred meter
is carried, including physical jet scans, resizing, and weight
generation when the R23 term interpreter is plugged in. -/
namespace J6R23ScheduleWeight
open scoped BigOperators Polynomial Classical
open Polynomial A1R10 A1R11 A1R12 AOracleMachineTime AOracleCoordinates
open J6R22Active J6R9Recursive J6ActiveSchedule P1DyadicGrid HermiteLoss

variable {q ell : ℕ} {fw : List (Word q)}

def centreTerms (hp : 0<q) (term : ℤ→ℕ→Meter (UVBlock fw ell)) (z : ℤ×ℕ) :
    Meter (UVBlock fw ell) :=
  sumM hp (term z.1) (List.range z.2)

def allTerms (hp : 0<q) (term : ℤ→ℕ→Meter (UVBlock fw ell)) (centres : List (ℤ×ℕ)) :
    Meter (UVBlock fw ell) :=
  sumM hp (centreTerms hp term) centres

def termBill (term : ℤ→ℕ→Meter (UVBlock fw ell)) (centres : List (ℤ×ℕ)) : ℕ :=
  (centres.map (fun z=>bill (term z.1) (List.range z.2))).sum

def termsLoopFee (e ell q : ℕ) (hp : 0<q) (centres : List (ℤ×ℕ)) : ℕ :=
  (centres.length+1)*uvWidth e ell q+
    ((centres.map Prod.snd).sum+centres.length)*(addCap e ell q hp+2)

theorem allTerms_steps (hp : 0<q) (term : ℤ→ℕ→Meter (UVBlock fw ell))
    (centres : List (ℤ×ℕ)) :
    (allTerms hp term centres).steps≤termBill term centres+termsLoopFee fw.length ell q hp centres := by
  let C := centreTerms hp term
  let c := uvWidth fw.length ell q
  let a := addCap fw.length ell q hp+2
  have h (z : ℤ×ℕ) : (C z).steps≤bill (term z.1) (List.range z.2)+c+z.2*a := by
    simpa only [C,centreTerms,List.length_range,c,a] using (sumM_steps hp (term z.1) (List.range z.2)).2
  have this' (l : List (ℤ×ℕ)) :
      bill C l≤termBill term l+l.length*c+(l.map Prod.snd).sum*a := by
    induction l with
    | nil => simp [bill,termBill]
    | cons z zs ih =>
      have hz := h z
      change (C z).steps+bill C zs≤
        bill (term z.1) (List.range z.2)+termBill term zs+
          (zs.length+1)*c+(z.2+(zs.map Prod.snd).sum)*a
      rw [Nat.succ_mul zs.length,Nat.add_mul z.2]
      omega
  have lead := (sumM_steps hp C centres).2
  have b := this' centres
  unfold termsLoopFee
  rw [Nat.succ_mul centres.length,Nat.add_mul]
  change (sumM hp C centres).steps≤termBill term centres+(centres.length*c+c+
    ((centres.map Prod.snd).sum*a+centres.length*a))
  change (sumM hp C centres).steps≤bill C centres+c+centres.length*a at lead
  omega

theorem allTerms_scaled_register {f : ℤ[X]} (hp : 0<q)
    (hF : Modulus q hp fw=NativeProbeRing.liftPoly q f)
    (a M u B : ℕ) (centres : List (ℤ×ℕ)) (term : ℤ→ℕ→Meter (UVBlock fw ell))
    (nd : (centres.map Prod.fst).Nodup)
    (cv : (centres.map Prod.fst).toFinset=active a M u)
    (co : ∀ z∈centres,z.2=order M u z.1)
    (lift : ℤ→ℕ→IntRing f ell)
    (read : ∀ z∈centres,∀ j<z.2,
      boxTransport hF (uvRead hp fw ell (term z.1 j).result)=
        reduce q f ell (localScalar f ell (scaledWeight a u (sourceH M u) B j z.1)*lift z.1 j)) :
    boxTransport hF (uvRead hp fw ell (allTerms hp term centres).result)=
      reduce q f ell (scaledRecompose (localScalar f ell) a M u B lift) := by
  let C := centreTerms hp term
  let termInt (t : ℤ) (j : ℕ) :=
    localScalar f ell (scaledWeight a u (sourceH M u) B j t)*lift t j
  let J (t : ℤ) := ∑ j∈Finset.range (order M u t),reduce q f ell (termInt t j)
  have atCentre (z : ℤ×ℕ) (hz : z∈centres) : boxTransport hF (uvRead hp fw ell (C z).result)=J z.1 := by
    rw [show C z=sumM hp (term z.1) (List.range z.2) from rfl,sumM_value,map_list_sum,List.map_map]
    unfold J
    rw [←co z hz,←List.toFinset_range, List.sum_toFinset _ List.nodup_range]
    apply congrArg List.sum
    apply List.map_congr_left
    intro j hj
    exact read z hz j (List.mem_range.mp hj)
  rw [allTerms,sumM_value,map_list_sum,List.map_map]
  have eq :
      centres.map (boxTransport hF ∘ fun z=>uvRead hp fw ell (C z).result)=
      (centres.map Prod.fst).map J := by
    rw [List.map_map]
    exact List.map_congr_left (fun z hz=>atCentre z hz)
  change (centres.map (boxTransport hF ∘ fun z=>uvRead hp fw ell (C z).result)).sum=_
  rw [eq,←List.sum_toFinset J nd,cv,scaledRecompose,map_sum]
  refine Finset.sum_congr rfl (fun t _=>?_ )
  unfold J
  rw [map_sum]

#print axioms allTerms_steps
#print axioms allTerms_scaled_register
end J6R23ScheduleWeight


