import J6R49RootIngressPorts
import J6R27PrescribedProbeBits

/-! Concrete counters and an exact charged join of independent old rank
books. A row contains its raw row label and old half ranks, not its
columns or the new-leg side. A column holds two old half ranks only,
in the chosen subdivision order. No input record is an R49 Position. -/
namespace J6R50RootIngress
open A1R10 AOracleMachineTime J6R49RootIngress J6R30GeneratedRootLayout
open J6R27OriginalGate
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 6000000
set_option maxRecDepth 2400

def indexTape (w : ℕ) : ℕ → Meter (List (Word w))
  | 0 => ⟨[],1⟩
  | n+1 =>
      let q := J6R27PrescribedProbe.positiveTape w n
      ⟨wordAt w 0::q.result,q.steps+3*w+4⟩

def tapeFee (w n : ℕ) : ℕ := 18+6*w+n*(20*w+6)

theorem index_tape_exact (w n : ℕ) (hw : 0<w) (fit : n≤2^w) :
    (indexTape w n).result=List.ofFn (fun i : Fin n => wordAt w i.val) ∧
      (indexTape w n).steps≤tapeFee w n := by
  cases n with
  | zero => simp [indexTape,tapeFee]; omega
  | succ n =>
    have hn : n<2^w := by omega
    obtain ⟨e,c⟩ := J6R27PrescribedProbe.positive_tape_exact w n hw hn
    simp only [indexTape,e,c]
    constructor
    · rw [List.ofFn_succ]
      rfl
    · simp only [J6R27PrescribedProbe.positiveTapeFee,tapeFee,Nat.succ_mul]
      omega

structure RowBook (w r h : ℕ) where
  label : Word r
  clause : Option (Word h)
  ranks : List (Word w)

abbrev ColBook (w : ℕ) := List (Word w × Word w)
abbrev RowHit (r d h : ℕ) := Word r × Word d × Option (Word h)
abbrev ColHit (c : ℕ) := Word c × Bool

def emitRows {w r d h : ℕ} :
    List (RowBook w r h) → Meter (List (Word w × RowHit r d h))
  | [] => ⟨[],1⟩
  | b::bs =>
    let tape := indexTape d b.ranks.length
    let row := b.ranks.zipWith (fun k leg => (k,b.label,leg,b.clause)) tape.result
    let tail := emitRows bs
    ⟨row++tail.result,tape.steps+tail.steps+8+row.length*(16+4*(w+r+d+h))⟩

def colData {w c : ℕ} (k : Word w × Word w) (j : Word c) :
    List (Word w × ColHit c) := [(k.1,j,false),(k.2,j,true)]

def emitColumns {w c : ℕ} (book : ColBook w) : Meter (List (Word w × ColHit c)) :=
  let tape := indexTape c book.length
  ⟨(book.zipWith colData tape.result).flatten,tape.steps+7+book.length*(28+8*(w+c))⟩

def findRank {w : ℕ} {A : Type*} (k : Word w) : List (Word w × A) → Meter (Option A)
  | [] => ⟨none,2⟩
  | a::as =>
    let test := eqRawBits k.val a.1.val
    if test.result then ⟨some a.2,test.steps+4⟩
    else
      let tail := findRank k as
      ⟨tail.result,test.steps+tail.steps+4⟩

theorem find_rank_exact {w : ℕ} {A : Type*} (k : Word w) (rows : List (Word w × A)) (p : A)
    (hit : (k,p)∈rows) (only : ∀ a,(k,a)∈rows → a=p) :
    (findRank k rows).result=some p := by
  induction rows with
  | nil => simp at hit
  | cons x xs ih =>
    have e := (eq_raw_bits_exact k.val x.1.val).1
    by_cases h : k=x.1
    · have key := e.mpr (congrArg Subtype.val h)
      have q : x.2=p := only x.2 (List.mem_cons.mpr (Or.inl (by rw [h])))
      simp [findRank,key,q]
    · have notTrue : (eqRawBits k.val x.1.val).result=false := by
        apply Bool.eq_false_iff.mpr
        intro E
        exact h (Subtype.ext (e.mp E))
      have H : (k,p)∈xs := by
        rcases List.mem_cons.mp hit with K|K
        · exact (h (congrArg Prod.fst K)).elim
        · exact K
      simp only [findRank,notTrue,Bool.false_eq_true,if_false]
      exact ih H (fun a ha => only a (List.mem_cons_of_mem _ ha))

theorem find_rank_fee {w : ℕ} {A : Type*} (k : Word w) (rows : List (Word w × A)) :
    (findRank k rows).steps≤2+rows.length*(5*w+6) := by
  induction rows with
  | nil => simp [findRank]
  | cons x xs ih =>
    have b := (eq_raw_bits_exact k.val x.1.val).2
    rw [k.property] at b
    by_cases h : (eqRawBits k.val x.1.val).result=true
    · simp only [findRank,h,if_true,List.length_cons,Nat.succ_mul]
      omega
    · have h0 : (eqRawBits k.val x.1.val).result=false := Bool.eq_false_iff.mpr h
      simp only [findRank,h0,Bool.false_eq_true,if_false,List.length_cons]
      rw [Nat.add_mul,Nat.one_mul]
      omega

def emitPosition {w r c d h : ℕ} (rows : List (Word w × RowHit r d h))
    (cols : List (Word w × ColHit c)) (k : Word w) : Meter (Option (Position r c d h)) :=
  let x := findRank k rows
  let y := findRank k cols
  match x.result,y.result with
  | some (row,leg,clause),some (col,side) =>
      let u := copyPortWord row
      let v := copyPortWord leg
      let z := copyPortWord col
      let q := clause.map copyPortWord
      ⟨some ⟨u.result,z.result,v.result,side,q.map Meter.result⟩,
        x.steps+y.steps+u.steps+v.steps+z.steps+(q.map Meter.steps).getD 0+10⟩
  | _,_ => ⟨none,x.steps+y.steps+6⟩

theorem emit_position_exact {w r c d h : ℕ} (rows : List (Word w × RowHit r d h))
    (cols : List (Word w × ColHit c)) (k : Word w) (p : Position r c d h)
    (hr : (findRank k rows).result=some (p.row,p.leg,p.clause))
    (hc : (findRank k cols).result=some (p.column,p.side)) :
    (emitPosition rows cols k).result=some p := by
  rcases p with ⟨row,col,leg,side,clause⟩
  cases clause <;> simp [emitPosition,hr,hc,port_word_copy]

def positionFee (w r c d h R C : ℕ) : ℕ := 22+(R+C)*(5*w+6)+4*(r+c+d+h)

theorem emit_position_fee {w r c d h : ℕ} (rows : List (Word w × RowHit r d h))
    (cols : List (Word w × ColHit c)) (k : Word w) :
    (emitPosition rows cols k).steps≤positionFee w r c d h rows.length cols.length := by
  have hr := find_rank_fee k rows
  have hc := find_rank_fee k cols
  unfold emitPosition
  cases e₁ : (findRank k rows).result with
  | none => simp [positionFee,e₁,Nat.add_mul]; omega
  | some p =>
    rcases p with ⟨rw,lg,opt⟩
    cases e₂ : (findRank k cols).result with
    | none => simp [positionFee,e₁,e₂,Nat.add_mul]; omega
    | some c0 =>
      rcases c0 with ⟨col,side⟩
      cases opt <;> simp [positionFee,e₁,e₂,port_word_copy,Nat.add_mul] <;> omega

def joinKeys {w r c d h : ℕ} (rows : List (Word w × RowHit r d h))
    (cols : List (Word w × ColHit c)) :
    List (Word w) → Meter (Option (List (Position r c d h)))
  | [] => ⟨some [],1⟩
  | x::xs =>
    let a := emitPosition rows cols x
    let b := joinKeys rows cols xs
    ⟨a.result.bind (fun p => b.result.map (p::·)),a.steps+b.steps+4⟩

theorem joined_keys_exact {I : Type*} {w r c d h : ℕ}
    (rows : List (Word w × RowHit r d h)) (cols : List (Word w × ColHit c))
    (ks : List I) (key : I → Word w) (pos : I → Position r c d h)
    (row : ∀ i,(findRank (key i) rows).result=some ((pos i).row,(pos i).leg,(pos i).clause))
    (col : ∀ i,(findRank (key i) cols).result=some ((pos i).column,(pos i).side)) :
    (joinKeys rows cols (ks.map key)).result=some (ks.map pos) := by
  induction ks with
  | nil => rfl
  | cons i ks ih => simp [joinKeys,emit_position_exact rows cols _ _ (row i) (col i),ih]

theorem joined_keys_fee {w r c d h : ℕ} (rows : List (Word w × RowHit r d h))
    (cols : List (Word w × ColHit c)) (ks : List (Word w)) :
    (joinKeys rows cols ks).steps≤1+ks.length*(positionFee w r c d h rows.length cols.length+4) := by
  induction ks with
  | nil => simp [joinKeys]
  | cons x xs ih =>
    have h := emit_position_fee rows cols x
    simp only [joinKeys,List.length_cons,Nat.succ_mul]
    omega

def recoveredAtlas {w r c d h : ℕ} (n : ℕ) (row : List (RowBook w r h)) (col : ColBook w) :
    Meter (Option (List (Position r c d h))) :=
  let R := emitRows (d:=d) row
  let C := emitColumns (c:=c) col
  let K := indexTape w n
  let A := joinKeys R.result C.result K.result
  ⟨A.result,R.steps+C.steps+K.steps+A.steps+8⟩

#print axioms index_tape_exact
#print axioms find_rank_exact
#print axioms find_rank_fee
#print axioms emit_position_exact
#print axioms emit_position_fee
#print axioms joined_keys_exact
#print axioms joined_keys_fee
end J6R50RootIngress
