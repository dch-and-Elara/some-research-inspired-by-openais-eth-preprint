import P5MainBalanceM6Swaps

/-! A complete finite label for the printed exceptional row set:
the ordered pairs below index the + and − swap eigencharacters
exactly once, including fixed diagonal axes. -/
namespace P5MainBalance.M6
open P5MainIterator
open scoped BigOperators Classical

variable {I B : Type*} [Fintype I] [Fintype B] [LinearOrder B]

omit [Fintype I] [Fintype B] in
theorem key_decode (s : OrbitCell I B) : orbitKey (decodeOrbit s)=s.1 := by
  funext i
  unfold orbitKey decodeOrbit
  let q := s.1 i
  have hle : q.val.1≤q.val.2 := q.property
  by_cases h : q.val.1≠q.val.2
  · change sortedKey (if h' : q.val.1≠q.val.2 then
      if s.2 ⟨i,h'⟩ then q.val.swap else q.val else q.val)=q
    rw [dif_pos h]
    cases hv : s.2 ⟨i,h⟩
    · simp [sortedKey,hle,q]
    · have hh : ¬q.val.2≤q.val.1 := fun hp=> h (le_antisymm hle hp)
      simp [sortedKey,hh,q]
  · change sortedKey (if h' : q.val.1≠q.val.2 then
      if s.2 ⟨i,h'⟩ then q.val.swap else q.val else q.val)=q
    simp [h,sortedKey,hle,q]

omit [Fintype I] [Fintype B] in
theorem decode_orientation_recovers (o : I→SortedPair B) (w : Unequal o→Bool)
    (i : Unequal o) :
    decide (((decodeOrbit ⟨o,w⟩ i.val).2)<((decodeOrbit ⟨o,w⟩ i.val).1))=w i := by
  have h : (o i.val).val.1<(o i.val).val.2 := lt_of_le_of_ne (o i.val).property i.property
  cases hW : w i <;> simp [decodeOrbit,i.property,hW,h,not_lt_of_ge h.le]

omit [Fintype I] [Fintype B] in
theorem decodeOrbit_injective : Function.Injective (decodeOrbit (I:=I) (B:=B)) := by
  rintro ⟨o,w⟩ ⟨u,v⟩ h
  have ho := congrArg orbitKey h
  rw [key_decode,key_decode] at ho
  change o=u at ho
  subst u
  congr 1
  funext i
  have hi := congrFun h i.val
  have hx := congrArg (fun p : B×B=>decide (p.2<p.1)) hi
  simpa only [decode_orientation_recovers] using hx

noncomputable def singleBasisOrder : OrbitCell I B ≃ WordCell I B where
  toFun := decodeOrbit
  invFun := encodeOrbit
  left_inv := fun u=>decodeOrbit_injective (decode_encodeOrbit (decodeOrbit u))
  right_inv := decode_encodeOrbit

noncomputable def descendingWeight (u : WordCell I B) : ℕ :=
  (Finset.univ.filter (fun i=>(u i).2<(u i).1)).card

omit [Fintype I] [Fintype B] in
theorem oddAt_ordered_pair (u : WordCell I B) (i : I) :
    oddAt (copyEncode (((),u) : Unit×WordCell I B)) i = decide ((u i).2<(u i).1) := by
  unfold copyEncode oddAt
  by_cases h : (orbitKey u i).val.1≠(orbitKey u i).val.2
  · simp [h,encodeOrbit]
  · rw [dif_neg h]
    have hn : (u i).1=(u i).2 := by
      by_contra hne
      exact h ((unequal_at_key_iff u i).mpr hne)
    simp [hn]

omit [Fintype B] in
theorem weight_encode_descends (u : WordCell I B) :
    boolWeight (encodeOrbit u).2=descendingWeight u := by
  change boolWeight (copyEncode (((),u) : Unit×WordCell I B)).2=descendingWeight u
  rw [←card_oddAt (copyEncode (((),u) : Unit×WordCell I B))]
  unfold descendingWeight
  apply congrArg Finset.card
  ext i
  simp [oddAt_ordered_pair]

/-- A precise address-count equality, before any Chernoff bound or
asymptotic estimate. -/
theorem exceptional_count_is_weight_tail (keep : ℕ→Prop) :
    Fintype.card (Exceptional (Unequal (I:=I) (B:=B)) keep) =
      (Finset.univ.filter (fun u : WordCell I B=>keep (descendingWeight u))).card := by
  have hB (r : OrbitCell I B) : boolWeight r.2=descendingWeight (decodeOrbit r) := by
    have h := weight_encode_descends (singleBasisOrder r)
    change boolWeight (singleBasisOrder.symm (singleBasisOrder r)).2=_ at h
    rw [Equiv.symm_apply_apply] at h
    exact h
  let e : {r : OrbitCell I B // keep (boolWeight r.2)} ≃
      {u : WordCell I B // keep (descendingWeight u)} :=
    ⟨fun r=>⟨decodeOrbit r.val,(hB r.val) ▸ r.property⟩,
     fun u=>⟨encodeOrbit u.val,(weight_encode_descends u.val).symm ▸ u.property⟩,
     fun r=>Subtype.ext (singleBasisOrder.symm_apply_apply r.val),
     fun u=>Subtype.ext (decode_encodeOrbit u.val)⟩
  rw [Fintype.card_congr e,Fintype.card_subtype]

#print axioms key_decode
#print axioms decodeOrbit_injective
#print axioms oddAt_ordered_pair
#print axioms weight_encode_descends
#print axioms exceptional_count_is_weight_tail
end P5MainBalance.M6
