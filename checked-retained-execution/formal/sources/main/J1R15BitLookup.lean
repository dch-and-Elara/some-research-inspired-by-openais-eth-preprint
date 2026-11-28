import J1R14QueryTape
import A1R10Word

/-! Deliberately sequential bit-indexed tables for MAIN. An array indexing
oracle is not an operation here: every lookup reads and compares a stored
key. We also meter joining a public index file to a candidate bit vector. -/
namespace J1R15
open AOracleMachineTime

def equalBits : List Bool → List Bool → Meter Bool
  | [], [] => ⟨true,1⟩
  | [], _::_ => ⟨false,1⟩
  | _::_, [] => ⟨false,1⟩
  | x::xs, y::ys =>
    let sub := equalBits xs ys
    ⟨(x == y) && sub.result, 4+sub.steps⟩

theorem equalBits_result (x y : List Bool) : (equalBits x y).result = decide (x=y) := by
  induction x generalizing y with
  | nil => cases y <;> rfl
  | cons a x ih =>
    cases y with
    | nil => rfl
    | cons b y =>
      cases a <;> cases b <;> simp [equalBits,ih]

theorem equalBits_cost (x y : List Bool) :
    (equalBits x y).steps = 4*min x.length y.length+1 := by
  induction x generalizing y with
  | nil => cases y <;> simp [equalBits]
  | cons a x ih =>
    cases y with
    | nil => simp [equalBits]
    | cons b y =>
      simp only [equalBits,ih,List.length_cons]
      omega

abbrev File := List (List Bool × List Bool)

def lookup (q : List Bool) : File → Meter (Option (List Bool))
  | [] => ⟨none,1⟩
  | (k,v)::more =>
    let matchKey := equalBits q k
    let scan := matchKey.steps+k.length+v.length+2
    if matchKey.result then ⟨some v,scan⟩
    else
      let later := lookup q more
      ⟨later.result,scan+later.steps⟩

theorem lookup_absent (q : List Bool) (l : File)
    (hm : ∀ v, (q,v) ∉ l) : (lookup q l).result = none := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    obtain ⟨k,v⟩ := e
    have hn : q ≠ k := by
      intro h
      subst k
      exact hm v (List.mem_cons_self)
    have hr := ih (fun y hy => hm y (List.mem_cons_of_mem _ hy))
    simp [lookup,equalBits_result,hn,hr]

theorem lookup_unique (q payload : List Bool) (l : File)
    (hm : (q,payload) ∈ l) (hf : ∀ v, (q,v) ∈ l → v=payload) :
    (lookup q l).result = some payload := by
  induction l with
  | nil => simp at hm
  | cons e l ih =>
    obtain ⟨k,v⟩ := e
    by_cases h : q=k
    · subst k
      have hv := hf v List.mem_cons_self
      simp [lookup,equalBits_result,hv]
    · have hp : (q,payload) ∈ l := by
        rcases List.mem_cons.mp hm with hh | hh
        · exact (h (congrArg Prod.fst hh)).elim
        · exact hh
      have hh := ih hp (fun v hv => hf v (List.mem_cons_of_mem _ hv))
      simp [lookup,equalBits_result,h,hh]

/-- Each record consumed on a sequential tape charges the key and payload
bits in addition to the explicit comparison. Early success only saves work. -/
theorem lookup_cost (q : List Bool) (l : File) (w z : ℕ)
    (hw : q.length ≤ w)
    (hb : ∀ e ∈ l, e.1.length ≤ w ∧ e.2.length ≤ z) :
    (lookup q l).steps ≤ l.length*(5*w+z+3)+1 := by
  induction l with
  | nil => simp [lookup]
  | cons e l ih =>
    obtain ⟨k,v⟩ := e
    have he := hb (k,v) List.mem_cons_self
    have hn := ih (fun a ha => hb a (List.mem_cons_of_mem _ ha))
    have hc := equalBits_cost q k
    have hmin : min q.length k.length ≤ w := (Nat.min_le_left _ _).trans hw
    change k.length≤w ∧ v.length≤z at he
    rcases he with ⟨hk,hv⟩
    let K := 5*w+z+3
    have hstep : (equalBits q k).steps+k.length+v.length+2 ≤ K := by
      dsimp [K]
      omega
    have hlen : K+(l.length*K+1) = ((k,v)::l).length*K+1 := by
      simp only [List.length_cons,Nat.succ_mul]
      ac_rfl
    change (lookup q ((k,v)::l)).steps ≤ ((k,v)::l).length*K+1
    change (lookup q l).steps ≤ l.length*K+1 at hn
    by_cases hkq : q=k
    · have ht : (equalBits q k).result = true := by simp [equalBits_result,hkq]
      simpa only [lookup,ht,ite_true] using
        hstep.trans ((Nat.le_add_right K (l.length*K+1)).trans_eq hlen)
    · have ht : (equalBits q k).result = false := by simp [equalBits_result,hkq]
      simpa only [lookup,ht,Bool.false_eq_true,ite_false] using
        (Nat.add_le_add hstep hn).trans_eq hlen

/-- The candidate itself arrives as an ordinary bit tape. Joining it with
the public sequential index file consumes and writes the two fields. -/
def attachCandidates : List (List Bool) → List Bool → Meter File
  | [], _ => ⟨[],1⟩
  | _::_, [] => ⟨[],1⟩
  | k::ks, b::bs =>
    let more := attachCandidates ks bs
    ⟨(k,[b])::more.result,2*k.length+3+more.steps⟩

theorem attachCandidates_result (ks : List (List Bool)) (bs : List Bool) :
    (attachCandidates ks bs).result = List.zipWith (fun k b => (k,[b])) ks bs := by
  induction ks generalizing bs with
  | nil => rfl
  | cons k ks ih =>
    cases bs with
    | nil => rfl
    | cons b bs => simp [attachCandidates,ih]

theorem attachCandidates_cost (ks : List (List Bool)) (bs : List Bool) (w : ℕ)
    (hw : ∀ k ∈ ks, k.length ≤ w) :
    (attachCandidates ks bs).steps ≤ ks.length*(2*w+3)+1 := by
  induction ks generalizing bs with
  | nil => simp [attachCandidates]
  | cons k ks ih =>
    cases bs with
    | nil => simp [attachCandidates]
    | cons b bs =>
      have hk := hw k List.mem_cons_self
      have hr := ih bs (fun t ht => hw t (List.mem_cons_of_mem _ ht))
      let K := 2*w+3
      have hstep : 2*k.length+3 ≤ K := by dsimp [K]; omega
      have hlen : K+(ks.length*K+1) = (k::ks).length*K+1 := by
        simp only [List.length_cons,Nat.succ_mul]
        ac_rfl
      change (attachCandidates ks bs).steps ≤ ks.length*K+1 at hr
      change 2*k.length+3+(attachCandidates ks bs).steps ≤ (k::ks).length*K+1
      exact (Nat.add_le_add hstep hr).trans_eq hlen

#print axioms equalBits_result
#print axioms equalBits_cost
#print axioms lookup_absent
#print axioms lookup_unique
#print axioms lookup_cost
#print axioms attachCandidates_result
#print axioms attachCandidates_cost
end J1R15
