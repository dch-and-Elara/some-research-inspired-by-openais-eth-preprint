import J6R21AncestorPrefix

/-! A sequential immutable descriptor directory. Lookups compare real
fixed-width address words and charge copying/scanning any payload they
pass. Appending a fresh entry never overwrites an old descriptor. -/
namespace J6R21Ancestor
open AOracleMachineTime J6R15ModeCost J6R20Ancestor

structure DirRow (w : ℕ) where
  id : Word w
  bytes : List Bool

def copyBytes : List Bool→Meter (List Bool)
  | [] => ⟨[],1⟩
  | x::xs =>
    let h := copyBytes xs
    ⟨x::h.result,h.steps+3⟩

theorem copyBytes_exact (bs : List Bool) : copyBytes bs=⟨bs,3*bs.length+1⟩ := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    rw [copyBytes,ih]
    congr 1

def cmpAddr {w : ℕ} (a b : Word w) : Meter Bool :=
  compare ⟨false,a⟩ ⟨false,b⟩

theorem cmpAddr_exact {w : ℕ} (a b : Word w) :
    ((cmpAddr a b).result=true↔a=b) ∧ (cmpAddr a b).steps=10*w+5 := by
  obtain ⟨h,hc⟩ := compare_exact (⟨false,a⟩ : Key w) ⟨false,b⟩
  refine ⟨h.trans ?_,hc⟩
  constructor
  · exact congrArg Key.slot
  · intro h; rw [h]

def fetch {w : ℕ} (addr : Word w) : List (DirRow w)→Meter (Option (List Bool))
  | [] => ⟨none,2⟩
  | x::xs =>
    let c := cmpAddr addr x.id
    let payload := copyBytes x.bytes
    let fee := c.steps+payload.steps+2*w+6
    if c.result then ⟨some payload.result,fee⟩
    else
      let tail := fetch addr xs
      ⟨tail.result,fee+tail.steps⟩

def rowFee {w : ℕ} (r : DirRow w) := 12*w+3*r.bytes.length+12

def fetchFee {w : ℕ} : List (DirRow w)→ℕ
  | [] => 2
  | y::ys => rowFee y+fetchFee ys

theorem fetch_bound {w : ℕ} (addr : Word w) (xs : List (DirRow w)) :
    (fetch addr xs).steps≤fetchFee xs := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    have hc := (cmpAddr_exact addr y.id).2
    have hB := copyBytes_exact y.bytes
    have hFee : (cmpAddr addr y.id).steps+(copyBytes y.bytes).steps+2*w+6=rowFee y := by
      rw [hc,hB,rowFee]
      change 10*w+5+(3*y.bytes.length+1)+2*w+6 = _
      omega
    rw [fetch]
    split
    · change (cmpAddr addr y.id).steps+(copyBytes y.bytes).steps+2*w+6≤_
      rw [hFee,fetchFee]
      omega
    · change (cmpAddr addr y.id).steps+(copyBytes y.bytes).steps+2*w+6+(fetch addr ys).steps≤_
      rw [hFee,fetchFee]
      exact Nat.add_le_add_left ih _

theorem fetch_hit {w : ℕ} (addr : Word w) (bytes : List Bool) (xs : List (DirRow w))
    (here : (⟨addr,bytes⟩ : DirRow w)∈xs)
    (unique : ∀ row∈xs,row.id=addr → row.bytes=bytes) :
    (fetch addr xs).result=some bytes := by
  induction xs with
  | nil => simp at here
  | cons x xs ih =>
    by_cases h : addr=x.id
    · have H := unique x List.mem_cons_self h.symm
      rw [fetch,if_pos ((cmpAddr_exact _ _).1.mpr h),copyBytes_exact,H]
    · have hp : (⟨addr,bytes⟩ : DirRow w)∈xs := by
        rcases List.mem_cons.mp here with hx | hx
        · exact (h (congrArg DirRow.id hx)).elim
        · exact hx
      rw [fetch,if_neg (fun hx=>h ((cmpAddr_exact _ _).1.mp hx))]
      exact ih hp (fun y hy=>unique y (List.mem_cons_of_mem _ hy))

theorem fetch_miss {w : ℕ} (addr : Word w) (xs : List (DirRow w))
    (h : ∀r∈xs,r.id≠addr) : (fetch addr xs).result=none := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [fetch,if_neg (fun e=>h x List.mem_cons_self ((cmpAddr_exact _ _).1.mp e).symm)]
    exact ih (fun r hr=>h r (List.mem_cons_of_mem _ hr))

def addImmutable {w : ℕ} (x : DirRow w) (xs : List (DirRow w)) : Meter (List (DirRow w)) :=
  let probe := fetch x.id xs
  match probe.result with
  | some _ => ⟨xs,probe.steps+5⟩
  | none =>
    let written := copyBytes x.bytes
    ⟨⟨x.id,written.result⟩::xs,probe.steps+written.steps+2*w+8⟩

theorem addImmutable_fresh {w : ℕ} (x : DirRow w) (xs : List (DirRow w))
    (h : ∀r∈xs,r.id≠x.id) :
    let op := addImmutable x xs
    op.result=x::xs ∧ op.steps≤fetchFee xs+3*x.bytes.length+2*w+9 := by
  have hn := fetch_miss x.id xs h
  have hFee := fetch_bound x.id xs
  unfold addImmutable
  dsimp only
  rw [hn,copyBytes_exact]
  constructor
  · cases x
    rfl
  · dsimp only
    omega

theorem preserved_read {w : ℕ} (x : DirRow w) (addr : Word w) (xs : List (DirRow w))
    (h : x.id≠addr) :
    (fetch addr (x::xs)).result=(fetch addr xs).result := by
  rw [fetch,if_neg (fun hp=>h ((cmpAddr_exact _ _).1.mp hp).symm)]

#print axioms copyBytes_exact
#print axioms cmpAddr_exact
#print axioms fetch_bound
#print axioms fetch_hit
#print axioms fetch_miss
#print axioms addImmutable_fresh
#print axioms preserved_read
end J6R21Ancestor



