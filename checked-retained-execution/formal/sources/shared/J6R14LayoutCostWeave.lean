import J6R14LayoutCostRound

/-! Exact bit permutation for a packet address with all-zero packet
convention. Low rank bits occupy the cold (equal-symbol) slot positions,
the subsequent bits occupy the hot packet selector, and the rest is
the page number. This is a reversible sequential traversal. -/

namespace J6R14LayoutCost
open AOracleMachineTime

abbrev AxisMarks := List (Bool × Bool)

def maskCount (pick : Bool) (m : AxisMarks) : ℕ :=
  (m.filter (fun x => x.1 == pick)).length

theorem maskCount_cons (p : Bool) (x : Bool × Bool) (xs : AxisMarks) :
    maskCount p (x::xs)=maskCount p xs+(if x.1=p then 1 else 0) := by
  by_cases h : x.1=p <;> simp [maskCount,h]

theorem maskCount_total (m : AxisMarks) :
    maskCount false m+maskCount true m=m.length := by
  induction m with
  | nil => rfl
  | cons x xs ih =>
    rw [maskCount_cons,maskCount_cons]
    cases h : x.1 <;> simp [List.length_cons] <;> omega

def selectMask (p : Bool) : AxisMarks → List Bool → List Bool
  | x::xs,b::bs => if x.1=p then b::selectMask p xs bs else selectMask p xs bs
  | _,_ => []

def weave (pick : Bool) (default : Bool×Bool→Bool) :
    AxisMarks → List Bool → Meter (List Bool × List Bool)
  | [],data => ⟨([],data),0⟩
  | x::xs,data =>
    if x.1=pick then
      let q := weave pick default xs data.tail
      ⟨(data.headD false::q.result.1,q.result.2),q.steps+8⟩
    else
      let q := weave pick default xs data
      ⟨(default x::q.result.1,q.result.2),q.steps+8⟩

theorem weave_exact (pick : Bool) (default : Bool×Bool→Bool) (marks : AxisMarks)
    (data : List Bool) (h : maskCount pick marks≤data.length) :
    let q := weave pick default marks data
    q.result.1.length=marks.length ∧
    selectMask pick marks q.result.1=data.take (maskCount pick marks) ∧
    selectMask (!pick) marks q.result.1=(marks.filter (fun x=>x.1 == !pick)).map default ∧
    q.result.2=data.drop (maskCount pick marks) ∧ q.steps=8*marks.length := by
  induction marks generalizing data with
  | nil => simp [weave,maskCount,selectMask]
  | cons x xs ih =>
    rw [maskCount_cons] at h
    by_cases he : x.1=pick
    · rw [if_pos he] at h
      cases data with
      | nil => simp at h
      | cons z zs =>
        have H : maskCount pick xs≤zs.length := by simpa using h
        obtain ⟨hL,hP,hQ,hD,hC⟩ := ih zs H
        cases pick <;> simp at hQ <;> simp [weave,he,hL,selectMask,hP,hQ,hD,hC,maskCount_cons,Nat.mul_succ]
    · have hk : x.1 = !pick := by cases pick <;> cases hx : x.1 <;> simp_all
      rw [if_neg he,Nat.add_zero] at h
      obtain ⟨hL,hP,hQ,hD,hC⟩ := ih data h
      cases pick <;> simp at hQ <;> simp [weave,hk,hL,selectMask,hP,hQ,hD,hC,maskCount_cons,Nat.mul_succ]

structure SeatWords where
  slot : List Bool
  selector : List Bool
  page : List Bool

def seatWords (marks : AxisMarks) (rank : List Bool) : Meter SeatWords :=
  let s := weave false Prod.snd marks rank
  let p := weave true (fun _ => false) marks s.result.2
  ⟨⟨s.result.1,p.result.1,p.result.2⟩,s.steps+p.steps+6⟩

theorem seatWords_exact (marks : AxisMarks) (rank : List Bool) (h : marks.length≤rank.length) :
    let q := seatWords marks rank
    q.result.slot.length=marks.length ∧ q.result.selector.length=marks.length ∧
    selectMask true marks q.result.slot=(marks.filter (fun x=>x.1)).map Prod.snd ∧
    selectMask false marks q.result.slot++selectMask true marks q.result.selector++q.result.page=rank ∧
    q.result.page=rank.drop marks.length ∧ q.steps=16*marks.length+6 := by
  let s := weave false Prod.snd marks rank
  have hs : maskCount false marks≤rank.length := by
    have := maskCount_total marks
    omega
  obtain ⟨sl,sL,sH,sR,st⟩ := weave_exact false Prod.snd marks rank hs
  change s.result.2=_ at sR
  have ht : maskCount true marks≤s.result.2.length := by
    rw [sR,List.length_drop]
    have := maskCount_total marks
    omega
  let p := weave true (fun _ => false) marks s.result.2
  obtain ⟨pl,pL,_,pR,pt⟩ := weave_exact true (fun _ => false) marks s.result.2 ht
  refine ⟨sl,pl,?_,?_,?_,?_⟩
  · simpa using sH
  · change selectMask false marks s.result.1++selectMask true marks p.result.1++p.result.2=_
    rw [List.append_assoc,show selectMask false marks s.result.1=_ from sL,
      show selectMask true marks p.result.1=_ from pL,show p.result.2=_ from pR,
      List.take_append_drop,sR,List.take_append_drop]
  · change p.result.2=_
    rw [show p.result.2=_ from pR,sR,List.drop_drop,maskCount_total]
  · change s.steps+p.steps+6=_
    rw [show s.steps=_ from st,show p.steps=_ from pt]
    omega

theorem page_in_range (marks : AxisMarks) (rank : List Bool) (h : marks.length≤rank.length)
    (b : ℕ) (H : bitsValue rank<b*2^marks.length) :
    bitsValue (seatWords marks rank).result.page<b := by
  have hr := (seatWords_exact marks rank h).2.2.2.2.1
  rw [hr,drop_value]
  exact (Nat.div_lt_iff_lt_mul (by positivity)).mpr H

#print axioms maskCount_total
#print axioms weave_exact
#print axioms seatWords_exact
#print axioms page_in_range
end J6R14LayoutCost


