import J6R15ModeCostNative
import J6R15ModeCostPaid

/-! The admitted typed mode roster can be in any fixed enumeration
order. This is an input-format theorem: the tape already contains
the q-bit weights of that roster. It does not charge constructing
the child tensor descriptions or the roster itself. -/
namespace J6R15ModeCost

theorem roster_weight_count {P : Type*} [Fintype P] {tiles p : ℕ}
    (ms : List (Mode P tiles p)) (hm : ms.Nodup) (hall : ∀ m,m∈ms) (w : ℕ) :
    (ms.map modeWeight).count w=Nat.card {m : Mode P tiles p // modeWeight m=w} := by
  classical
  rw [List.count_eq_countP,List.countP_map,List.countP_eq_length_filter]
  let s := ms.filter (fun m=>modeWeight m == w)
  have hs : s.Nodup := hm.filter _
  have hset : s.toFinset=(Finset.univ.filter (fun (m : Mode P tiles p)=>modeWeight m=w)) := by
    ext m
    simp [s,hall m]
  change s.length=_
  rw [← List.toFinset_card_of_nodup hs,hset,Nat.card_eq_fintype_card,Fintype.card_subtype]

theorem roster_paid {P : Type*} {tiles p q : ℕ} (hq : 0<q) (hP : 0<p)
    (ms : List (Mode P tiles p)) (ws : List (Word q)) (pre : Word q)
    (hT : ws.map Word.val=ms.map modeWeight) (hE : pre.val=p) :
    let xs := strictTuples (ms.map modeWeight) p
    ∃ s : State q,
      (start ws pre).result=.again s ∧ s.wellFormed ws.length ∧
      let run := collect ws.length (xs.length+1) s
      run.result.2=true ∧ run.result.1.map (List.map Word.val)=xs ∧
      (start ws pre).steps+run.steps≤
        16*q+14+4*(ws.length+1)*(q+1)+(xs.length+1)*delayCap q ws.length := by
  have H : ∀ w∈ws,0<w.val := by
    intro w hw
    have he : w.val∈ws.map Word.val := List.mem_map.mpr ⟨w,hw,rfl⟩
    rw [hT] at he
    obtain ⟨m,_,h⟩ := List.mem_map.mp he
    rw [← h]
    exact (modeWeight_bounds m).1
  have R := all_tuple_cost hq ws pre H (by rwa [hE])
  simpa only [hT,hE] using R

#print axioms roster_weight_count
#print axioms roster_paid
end J6R15ModeCost


