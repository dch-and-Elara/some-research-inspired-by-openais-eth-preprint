import J6R20AncestorTape

/-! The stored port ID has one left bit per subsequent retention.
Strip exactly that many tags with a paid scan, then give the unchanged
origin slot and side to the one-hop route matcher. -/
namespace J6R21Ancestor
open AOracleMachineTime A1R12 J6R20Ancestor

def strip : ℕ→List Bool→Meter (Option (List Bool))
  | 0,xs => ⟨some xs,2⟩
  | n+1,false::xs =>
    let r := strip n xs
    ⟨r.result,r.steps+4⟩
  | _+1,_ => ⟨none,4⟩

theorem strip_exact (d : ℕ) (xs : List Bool) :
    strip d (List.replicate d false++xs)=⟨some xs,4*d+2⟩ := by
  induction d with
  | zero => simp [strip]
  | succ d ih =>
    rw [List.replicate_succ,List.cons_append,strip,ih]
    congr 1

theorem strip_bound (d : ℕ) (xs : List Bool) : (strip d xs).steps≤4*d+2 := by
  induction d generalizing xs with
  | zero => simp [strip]
  | succ d ih => cases xs with
    | nil => simp [strip]; omega
    | cons b xs => cases b <;> simp only [strip] <;> have := ih xs <;> omega

def normalize (d : ℕ) (p : Raw) : Meter Raw :=
  let r := strip d p.1
  ⟨(r.result.elim [] (fun tail=>false::tail),p.2),r.steps+4⟩

def normalizeFee (a d n : ℕ) := n*(4*d+a+14)

def normalizeTape (a d : ℕ) (raw : List Raw) : Meter (List Raw) :=
  mapMeter (normalize d) (a+4) raw

theorem normalize_exact {a : ℕ} (d : ℕ) (k : Key a) (b : Bool) :
    normalize d (List.replicate d false++true::k.side::k.slot.bits,b)=
      ⟨nested (k,b),4*d+6⟩ := by
  unfold normalize
  rw [strip_exact]
  rfl

theorem normalizeTape_exact (a d : ℕ) (raw : List Raw) :
    (normalizeTape a d raw).result=raw.map (fun p=>(normalize d p).result) ∧
      (normalizeTape a d raw).steps≤normalizeFee a d raw.length := by
  have h : ∀ p : Raw,(normalize d p).steps≤4*d+6 := by
    intro p
    change (strip d p.1).steps+4≤_
    exact (Nat.add_le_add_right (strip_bound d p.1) 4)
  obtain ⟨hr,hc⟩ := mapMeter_exact (normalize d) (a+4) (4*d+6) raw (fun p _=>h p)
  refine ⟨hr,hc.trans ?_⟩
  unfold normalizeFee
  exact Nat.mul_le_mul_left _ (by omega)

#print axioms strip_exact
#print axioms strip_bound
#print axioms normalize_exact
#print axioms normalizeTape_exact
end J6R21Ancestor


