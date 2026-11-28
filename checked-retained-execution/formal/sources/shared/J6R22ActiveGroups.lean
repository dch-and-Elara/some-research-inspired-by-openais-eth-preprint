import A1R12Combine

/-! Sequential arithmetic of one full Appendix D probe. Each child
exposes its own measured execution, not a unit-cost ring-valued
oracle. The per-probe traversal consumes the already enumerated legal
tuple batches in their printed order. Constructing native child
descriptors and dispatching a live recursive machine are separate. -/
namespace J6R22Active
open scoped BigOperators
open A1R10 A1R11 A1R12 AOracleCoordinates AOracleMachineTime

section Folds
variable {p ell : ℕ} {f : List (Word p)}

def zeroM (hp : 0<p) : Meter (UVBlock f ell) :=
  ⟨uvZero hp f ell,uvWidth f.length ell p⟩

@[simp] theorem zeroM_read (hp : 0<p) :
    uvRead hp f ell (zeroM hp).result=0 := uvZero_read hp f ell

def sumM {A : Type*} (hp : 0<p) (read : A→Meter (UVBlock f ell)) :
    List A → Meter (UVBlock f ell)
  | [] => zeroM hp
  | a::as => addM hp (read a) (sumM hp read as)

def bill {A B : Type*} (read : A→Meter B) (as : List A) : ℕ :=
  (as.map (fun a=>(read a).steps)).sum

theorem sumM_value {A : Type*} (hp : 0<p) (read : A→Meter (UVBlock f ell))
    (as : List A) :
    uvRead hp f ell (sumM hp read as).result =
      (as.map (fun a=>uvRead hp f ell (read a).result)).sum := by
  induction as with
  | nil => simp [sumM]
  | cons a as ih => simp [sumM,ih]

theorem sumM_steps {A : Type*} (hp : 0<p) (read : A→Meter (UVBlock f ell))
    (as : List A) :
    let n := (sumM hp read as).steps
    bill read as ≤ n ∧
      n ≤ bill read as+uvWidth f.length ell p+as.length*(addCap f.length ell p hp+2) := by
  dsimp only
  induction as with
  | nil => simp [sumM,zeroM,bill]
  | cons a as ih =>
    have hm := addM_cost hp (read a) (sumM hp read as)
    have hl : (read a).steps+(sumM hp read as).steps≤
        (addM hp (read a) (sumM hp read as)).steps := by
      simp only [addM]
      omega
    rw [sumM,List.length_cons,Nat.succ_mul as.length]
    change (read a).steps+bill read as≤_ ∧
      _≤(read a).steps+bill read as+uvWidth f.length ell p+
        (as.length*(addCap f.length ell p hp+2)+(addCap f.length ell p hp+2))
    omega

theorem prodM_value {A : Type*} (hp : 0<p) (he : 0<f.length) (hv : 0<ell)
    (read : A→Meter (UVBlock f ell)) (as : List A) :
    uvRead hp f ell (foldM hp he hv read as).result =
      (as.map (fun a=>uvRead hp f ell (read a).result)).prod := by
  induction as with
  | nil => simp [foldM]
  | cons a as ih => simp [foldM,ih]

theorem prodM_steps {A : Type*} (hp : 0<p) (he : 0<f.length) (hv : 0<ell)
    (read : A→Meter (UVBlock f ell)) (as : List A) :
    let n := (foldM hp he hv read as).steps
    bill read as ≤ n ∧
      n ≤ bill read as+uvWidth f.length ell p+as.length*(mulCap f.length ell p+2) := by
  dsimp only
  induction as with
  | nil => simp [foldM,oneM,bill]
  | cons a as ih =>
    have hm := mulM_cost hp (read a) (foldM hp he hv read as)
    have hl : (read a).steps+(foldM hp he hv read as).steps≤
        (mulM hp (read a) (foldM hp he hv read as)).steps := by
      simp only [mulM]
      omega
    rw [foldM,List.length_cons,Nat.succ_mul as.length]
    change (read a).steps+bill read as≤_ ∧
      _≤(read a).steps+bill read as+uvWidth f.length ell p+
        (as.length*(mulCap f.length ell p+2)+(mulCap f.length ell p+2))
    omega

theorem bill_mono {A B D : Type*} (g : A→Meter B) (h : A→Meter D)
    (as : List A) (c : ℕ) (le : ∀ a∈as,(g a).steps≤(h a).steps+c) :
    bill g as ≤ bill h as+as.length*c := by
  induction as with
  | nil => simp [bill]
  | cons a as ih =>
    have ha := le a List.mem_cons_self
    have ht := ih (fun i hi=>le i (List.mem_cons_of_mem _ hi))
    simp only [bill,List.map_cons,List.sum_cons,List.length_cons,Nat.succ_mul] at *
    omega

theorem bill_rel {A B D : Type*} (g : A→Meter B) (h : A→Meter D)
    (as : List A) (le : ∀ a∈as,(g a).steps≤(h a).steps) :
    bill g as ≤ bill h as := by
  simpa using bill_mono g h as 0 (by simpa using le)

end Folds

section Groups
variable {p ell : ℕ} {f : List (Word p)}
variable {B : Type*} {G : ℕ}

def groupOrder (G : ℕ) : List (Fin G) := List.ofFn (fun i : Fin G=>i)

def tupleProduct (hp : 0<p) (he : 0<f.length) (hv : 0<ell)
    (child : B→Fin G→Meter (UVBlock f ell)) (β : B) : Meter (UVBlock f ell) :=
  foldM hp he hv (child β) (groupOrder G)

def groupedProbe (hp : 0<p) (he : 0<f.length) (hv : 0<ell)
    (modes : List B) (child : B→Fin G→Meter (UVBlock f ell)) : Meter (UVBlock f ell) :=
  sumM hp (tupleProduct hp he hv child) modes

def probeEntryBill (modes : List B) (child : B→Fin G→Meter (UVBlock f ell)) : ℕ :=
  (modes.map (fun β=>bill (child β) (groupOrder G))).sum

def tupleExtra (e ell p G : ℕ) : ℕ := uvWidth e ell p+G*(mulCap e ell p+2)
def probeExtra (e ell p G K : ℕ) (hp : 0<p) : ℕ :=
  uvWidth e ell p+K*(tupleExtra e ell p G+addCap e ell p hp+2)

set_option maxHeartbeats 1200000 in
set_option maxRecDepth 1400 in
theorem grouped_probe_value (hp : 0<p) (he : 0<f.length) (hv : 0<ell)
    (modes : List B) (child : B→Fin G→Meter (UVBlock f ell)) :
    uvRead hp f ell (groupedProbe hp he hv modes child).result =
      (modes.map (fun β=>∏ g : Fin G,uvRead hp f ell (child β g).result)).sum := by
  rw [groupedProbe,sumM_value]
  congr 1
  apply List.map_congr_left
  intro β _
  rw [tupleProduct,prodM_value,groupOrder,List.map_ofFn]
  exact List.prod_ofFn

set_option maxHeartbeats 1200000 in
set_option maxRecDepth 1400 in
theorem grouped_probe_exact_bill (hp : 0<p) (he : 0<f.length) (hv : 0<ell)
    (modes : List B) (child : B→Fin G→Meter (UVBlock f ell)) :
    let q := (groupedProbe hp he hv modes child).steps
    let b := probeEntryBill modes child
    b≤q ∧ q≤b+probeExtra f.length ell p G modes.length hp := by
  let calcTerm := tupleProduct hp he hv child
  let sumTerm (β : B) : Meter Unit := ⟨(),bill (child β) (groupOrder G)⟩
  have hB : probeEntryBill modes child = bill sumTerm modes := rfl
  have hm (β : B) := prodM_steps hp he hv (child β) (groupOrder G)
  have hG : (groupOrder G).length=G := List.length_ofFn
  have hl := bill_rel sumTerm calcTerm modes (fun β _=>(hm β).1)
  have hu := bill_mono calcTerm sumTerm modes (tupleExtra f.length ell p G) (fun β _=> by
    simpa only [calcTerm,sumTerm,tupleProduct,tupleExtra,hG,Nat.add_assoc] using (hm β).2)
  have hs := sumM_steps hp calcTerm modes
  change probeEntryBill modes child≤_ ∧ _≤_
  rw [hB]
  refine ⟨hl.trans hs.1,?_⟩
  change (sumM hp calcTerm modes).steps≤_
  unfold probeExtra
  rw [Nat.add_assoc (tupleExtra f.length ell p G),Nat.mul_add modes.length]
  omega

end Groups

#print axioms sumM_value
#print axioms sumM_steps
#print axioms prodM_value
#print axioms prodM_steps
#print axioms bill_mono
#print axioms bill_rel
#print axioms grouped_probe_value
#print axioms grouped_probe_exact_bill
end J6R22Active






