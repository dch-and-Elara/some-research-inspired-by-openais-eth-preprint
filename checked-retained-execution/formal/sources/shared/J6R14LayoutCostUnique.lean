import J6R14LayoutCostPhysical

/-! For a common serialization width, literal addresses are injective
in their ordered cell and rank. Missing (cold) selector positions are
provably zero, so discarding them at the P11 boundary loses no bit. -/
namespace J6R14LayoutCost
open AOracleMachineTime P11FullPacking J6R12CollisionBits J6R12CollisionMenu

theorem fixedWordExt (l r : List Bool) (h : l.length=r.length)
    (hk : ∀ i<l.length, l.getD i false=r.getD i false) : l=r := by
  apply List.ext_getElem h
  intro i hi hR
  simpa [List.getD_eq_getElem?_getD,hi,hR] using hk i hi

theorem selectorAt_equal {a : ℕ} (c : Cell (Fin a) (Fin 64)) (r : List Bool)
    (i : Fin a) (he : (c i).1=(c i).2) :
    (seatWords (marksOf c) r).result.selector.getD i.val false=false := by
  change (weave true (fun _ => false) (marksOf c)
    (weave false Prod.snd (marksOf c) r).result.2).result.1.getD i.val false=_
  have ht : i.val<(marksOf c).length := by simpa only [marksOf_len] using i.isLt
  exact weave_fixed_getD true _ _ _ _ ht (by rw [marksOf_at]; simp [he])

theorem hot_iff {a : ℕ} (c : Cell (Fin a) (Fin 64)) (i : Fin a) :
    ((key c).val i).1≠((key c).val i).2 ↔ (c i).1≠(c i).2 := by
  by_cases h : (c i).1≤(c i).2
  · simp [key,sortPair,h]
  · simp [key,sortPair,h,ne_comm]

def pageNo {a b : ℕ} (p : Physical a b (Fin 64)) : ℕ := p.1.2.1.val

theorem realPhysical_cell_injective {a b : ℕ} (c : Cell (Fin a) (Fin 64))
    (r s : List Bool) (hwidth : a≤r.length) (hsize : r.length=s.length)
    (hr : bitsValue r<b*2^a) (hs : bitsValue s<b*2^a)
    (h :
      decodePhysical c (seatWords (marksOf c) r).result
        (page_in_range (marksOf c) r (by rwa [marksOf_len]) b (by rwa [marksOf_len])) =
      decodePhysical c (seatWords (marksOf c) s).result
        (page_in_range (marksOf c) s (by rwa [marksOf_len,← hsize]) b (by rwa [marksOf_len]))) :
    r=s := by
  have hwidth₂ : a≤s.length := hsize ▸ hwidth
  obtain ⟨Lr,Pr,_,Rr,Dr,_⟩ := seatWords_exact (marksOf c) r (by rwa [marksOf_len])
  obtain ⟨Ls,Ps,_,Rs,Ds,_⟩ := seatWords_exact (marksOf c) s (by rwa [marksOf_len])
  let x := (seatWords (marksOf c) r).result
  let y := (seatWords (marksOf c) s).result
  have xlen : x.slot.length=a ∧ x.selector.length=a := by
    simpa only [x,marksOf_len] using And.intro Lr Pr
  have ylen : y.slot.length=a ∧ y.selector.length=a := by
    simpa only [y,marksOf_len] using And.intro Ls Ps
  have Hpg : x.page=y.page := by
    apply equal_width_inj
    · change x.page=r.drop (marksOf c).length at Dr
      change y.page=s.drop (marksOf c).length at Ds
      rw [Dr,Ds,List.length_drop,List.length_drop,hsize]
    · exact congrArg pageNo h
  have Hsl : x.slot=y.slot := by
    apply fixedWordExt _ _ (xlen.1.trans ylen.1.symm)
    intro j hJ
    have hj : j<a := xlen.1 ▸ hJ
    have He := congrArg Prod.snd h
    change (bitsChart a).symm (fun k : Fin a => x.slot.getD k.val false) =
      (bitsChart a).symm (fun k : Fin a => y.slot.getD k.val false) at He
    exact congrFun ((bitsChart a).symm.injective He) ⟨j,hj⟩
  have Hse : x.selector=y.selector := by
    apply fixedWordExt _ _ (xlen.2.trans ylen.2.symm)
    intro j hJ
    have hj : j<a := xlen.2 ▸ hJ
    let i : Fin a := ⟨j,hj⟩
    by_cases hq : (c i).1=(c i).2
    · exact (selectorAt_equal c r i hq).trans (selectorAt_equal c s i hq).symm
    · let u : Hot (key c) := ⟨i,(hot_iff c i).2 hq⟩
      have e := Sigma.mk.inj_iff.mp (congrArg Prod.fst h)
      have E := congrArg Prod.snd (eq_of_heq e.2)
      exact congrFun E u
  change selectMask false (marksOf c) x.slot++selectMask true (marksOf c) x.selector++x.page=r at Rr
  change selectMask false (marksOf c) y.slot++selectMask true (marksOf c) y.selector++y.page=s at Rs
  rw [Hpg,Hsl,Hse,Rs] at Rr
  exact Rr.symm

#print axioms fixedWordExt
#print axioms selectorAt_equal
#print axioms realPhysical_cell_injective
end J6R14LayoutCost


