import J6R21AncestorRun
import J6R21AncestorDirectory

/-! Source descriptions are immutable by reference. This bank stores
address + reference headers of one installed native register shape;
the referenced contents are not a ring-value oracle. The actual
packet evaluator below must read the selected finite fields. -/
namespace J6R21Ancestor
open AOracleMachineTime A1R10 J6R18ChildWrite J6R20Ancestor

structure RefRow (width : ℕ) (D : Type*) where
  address : J6R15ModeCost.Word width
  payload : D

def locate {w : ℕ} {D : Type*} (address : J6R15ModeCost.Word w) :
    List (RefRow w D)→Meter (Option D)
  | [] => ⟨none,2⟩
  | row::tail =>
    let c := cmpAddr address row.address
    let readHeader := c.steps+3*w+8
    if c.result then ⟨some row.payload,readHeader⟩
    else
      let later := locate address tail
      ⟨later.result,readHeader+later.steps⟩

def locateFee (w n : ℕ) := n*(13*w+13)+2

theorem locate_bound {w : ℕ} {D : Type*} (addr : J6R15ModeCost.Word w)
    (bank : List (RefRow w D)) :
    (locate addr bank).steps≤locateFee w bank.length := by
  induction bank with
  | nil => simp [locate,locateFee]
  | cons row rows ih =>
    have h : (cmpAddr addr row.address).steps+3*w+8=13*w+13 := by
      rw [(cmpAddr_exact addr row.address).2]
      omega
    change (locate addr rows).steps≤rows.length*(13*w+13)+2 at ih
    rw [locate]
    split
    · change (cmpAddr addr row.address).steps+3*w+8≤(rows.length+1)*(13*w+13)+2
      rw [h,Nat.succ_mul rows.length]
      omega
    · change (cmpAddr addr row.address).steps+3*w+8+(locate addr rows).steps≤
        (rows.length+1)*(13*w+13)+2
      rw [h,Nat.succ_mul rows.length]
      omega

theorem locate_hit {w : ℕ} {D : Type*} (addr : J6R15ModeCost.Word w)
    (obj : D) (bank : List (RefRow w D))
    (existsHit : (⟨addr,obj⟩ : RefRow w D)∈bank)
    (unique : ∀ row∈bank,row.address=addr → row.payload=obj) :
    (locate addr bank).result=some obj := by
  induction bank with
  | nil => simp at existsHit
  | cons r rs ih =>
    by_cases h : addr=r.address
    · rw [locate,if_pos ((cmpAddr_exact _ _).1.mpr h)]
      exact congrArg some (unique r List.mem_cons_self h.symm)
    · have hp : (⟨addr,obj⟩ : RefRow w D)∈rs := by
        rcases List.mem_cons.mp existsHit with e|e
        · exact (h (congrArg RefRow.address e)).elim
        · exact e
      rw [locate,if_neg (fun e=>h ((cmpAddr_exact _ _).1.mp e))]
      exact ih hp (fun e he=>unique e (List.mem_cons_of_mem _ he))

structure OriginFields (a p ell w : ℕ) (old : List (A1R10.Word p)) (i : Fin a) where
  probe : UVBlock old ell
  rows : List (J6R15ModeCost.Word a)
  cols : List (J6R15ModeCost.Word a)
  modes : List (ModeInput a p i w)

def invokeLocated {p q ell a w aw : ℕ} (hp : 0<p)
    {old : List (A1R10.Word p)} {new : List (A1R10.Word q)}
    (he : 0<old.length) (hEll : 0<ell) (hD : old.length=new.length)
    (t : ℤ) (i : Fin a) (b depth : ℕ) (addr : J6R15ModeCost.Word aw)
    (bank : List (RefRow aw (OriginFields a p ell w old i))) (raw : List Raw) :
    Meter (Option (UVBlock new ell)) :=
  let found := locate addr bank
  match found.result with
  | none => ⟨none,found.steps+4⟩
  | some r =>
    let x := invokeTrace hp he hEll hD r.probe t i b depth r.rows r.cols r.modes raw
    ⟨some x.result,found.steps+x.steps+4⟩

theorem invoke_located_exact {p q ell a w aw : ℕ} (hp : 0<p)
    {old : List (A1R10.Word p)} {new : List (A1R10.Word q)}
    (he : 0<old.length) (hEll : 0<ell) (hD : old.length=new.length)
    (t : ℤ) (i : Fin a) (b depth : ℕ) (addr : J6R15ModeCost.Word aw)
    (bank : List (RefRow aw (OriginFields a p ell w old i))) (raw : List Raw)
    (fields : OriginFields a p ell w old i)
    (h : (⟨addr,fields⟩ : RefRow aw (OriginFields a p ell w old i))∈bank)
    (hU : ∀ x∈bank,x.address=addr → x.payload=fields) :
    let z := invokeLocated hp he hEll hD t i b depth addr bank raw
    let eval := invokeTrace hp he hEll hD fields.probe t i b depth fields.rows fields.cols fields.modes raw
    z.result=some eval.result ∧ z.steps ≤ locateFee aw bank.length+eval.steps+4 := by
  have hit := locate_hit addr fields bank h hU
  have paid := locate_bound addr bank
  dsimp only [invokeLocated]
  rw [hit]
  exact ⟨rfl,Nat.add_le_add_right (Nat.add_le_add_right paid _) _⟩

#print axioms locate_bound
#print axioms locate_hit
#print axioms invoke_located_exact
end J6R21Ancestor


