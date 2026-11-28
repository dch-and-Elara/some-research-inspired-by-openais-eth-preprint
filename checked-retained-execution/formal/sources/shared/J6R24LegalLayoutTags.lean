
import J6R24LegalLayoutTable

/-! The compact planted metadata suffices to tag the complete stable
physical tape. Tags are derived by the actual ordered-label bit
comparison and the planted rank cutoff, not by an inverse oracle. -/
namespace J6R24LegalLayout
open scoped BigOperators Classical
open P11FullPacking J6OrientedHost J6RecursiveOrientation
open J6R14LayoutCost J6R12CollisionMenu J6R12CollisionEdges
open AOracleMachineTime AOracleMachineTimeTape
set_option maxHeartbeats 14000000
set_option linter.unusedSectionVars false

def isPlanted {a b m l : ℕ} {w : Fin a→Fin 64} : Wire w m b l→Bool
  | .inl _=>true
  | .inr _=>false

theorem placed_planted_iff {a b m l : ℕ} (w : Fin a→Fin 64) (hm : m≤b) (hL : 2*l=2^a)
    (e : Wire w m b l) :
    isPlanted e=true ↔ (placedRank w hm hL e).1=diagonal w ∧
      (placedRank w hm hL e).2.val<m*2^a := by
  cases e with
  | inl p =>
    constructor
    · intro _
      refine ⟨rfl,?_⟩
      change p.2.val+2^a*p.1.val<m*2^a
      have hx : p.2.val<2^a := hL ▸ p.2.isLt
      have hmain : (p.1.val+1)*2^a≤m*2^a := Nat.mul_le_mul_right _ p.1.isLt
      rw [Nat.add_mul,one_mul] at hmain
      rw [Nat.mul_comm (2^a) p.1.val]
      omega
    · intro _
      rfl
  | inr p =>
    constructor
    · simp [isPlanted]
    · rintro ⟨hcell,hrank⟩
      change p.1.1=diagonal w at hcell
      let v := J6PhysicalPacking.place (diagonal w) m b l hm (.inr p)
      have rank : (placedRank w hm hL (.inr p)).2.val=v.2.2.val+2^a*v.2.1.val := rfl
      have H := J6PhysicalPacking.place_pad_gap (diagonal w) m b l hm p.1 p.2
      simp only [J6PhysicalPacking.offset,hcell] at H
      have H' : m*2^a≤2^a*v.2.1.val := by
        rw [Nat.mul_comm m (2^a)]
        exact Nat.mul_le_mul_left _ H
      rw [rank] at hrank
      omega

def sameToken (x y : CellWord) : Meter Bool :=
  let a := A1R9.eqWord x.1 y.1
  let b := A1R9.eqWord x.2 y.2
  ⟨a.result&&b.result,a.steps+b.steps+6⟩

theorem same_token_exact (a : ℕ) (c d : CellType a) :
    ((sameToken (wordCell c) (wordCell d)).result=true ↔ c=d) ∧
      (sameToken (wordCell c) (wordCell d)).steps=120*a+6 := by
  let u := wordCell c
  let v := wordCell d
  have l₁ : u.1.length=6*a := coordinateLabel_len _
  have l₂ : u.2.length=6*a := coordinateLabel_len _
  have r₁ : v.1.length=6*a := coordinateLabel_len _
  have r₂ : v.2.length=6*a := coordinateLabel_len _
  have L := A1R9.eqWord_exact u.1 v.1 (l₁.trans r₁.symm)
  have R := A1R9.eqWord_exact u.2 v.2 (l₂.trans r₂.symm)
  constructor
  · change ((A1R9.eqWord u.1 v.1).result&&(A1R9.eqWord u.2 v.2).result)=true↔_
    rw [Bool.and_eq_true,L.1,R.1]
    constructor
    · intro h
      exact word_cell_injective a (Prod.ext (equal_width_inj (l₁.trans r₁.symm) h.1)
        (equal_width_inj (l₂.trans r₂.symm) h.2))
    · intro h
      subst d
      exact ⟨rfl,rfl⟩
  · change (A1R9.eqWord u.1 v.1).steps+(A1R9.eqWord u.2 v.2).steps+6=_
    rw [L.2,R.2,l₁,l₂]
    omega

structure MarkedAnchor where
  anchor : AnchorWord
  old : Bool

def markOld (diag : CellWord) (cut : List Bool) (rec : AnchorWord) : Meter MarkedAnchor :=
  let l := sameToken diag rec.cell
  let h := compareBits rec.rank cut
  ⟨⟨rec,l.result&&h.result⟩,l.steps+h.steps+12⟩

def markFee (a q : ℕ) := 120*a+10*q+18

theorem mark_old_exact {a b m l q : ℕ} (w : Fin a→Fin 64) (hm : m≤b) (hL : 2*l=2^a)
    (cap : b*2^a<2^q) (e : Wire w m b l) :
    let row := anchorAt q (placedRank w hm hL e)
    let run := markOld (wordCell (diagonal w)) (encodeBits q (m*2^a)) row
    run.result.old=isPlanted e ∧ run.steps=markFee a q := by
  let x := placedRank w hm hL e
  let row := anchorAt q x
  let A := sameToken (wordCell (diagonal w)) (wordCell x.1)
  let B := compareBits (encodeBits q x.2.val) (encodeBits q (m*2^a))
  have W : m*2^a<2^q := (Nat.mul_le_mul_right _ hm).trans_lt cap
  have c1 := same_token_exact a (diagonal w) x.1
  have c2 := threshold_machine q x.2.val (m*2^a) (x.2.isLt.trans cap) W
  change (A.result&&B.result)=isPlanted e ∧ A.steps+B.steps+12=_
  refine ⟨?_,?_⟩
  · apply Bool.eq_iff_iff.mpr
    have p1 : A.result=true↔diagonal w=x.1 := c1.1
    have p2 : B.result=true↔x.2.val<m*2^a := c2.1
    rw [Bool.and_eq_true,p1,p2,placed_planted_iff w hm hL e]
    exact and_congr_left (fun _=>eq_comm)
  · rw [show A.steps=_ from c1.2,show B.steps=_ from c2.2]
    unfold markFee
    omega

def markTable (diag : CellWord) (cut : List Bool) : List AnchorWord→Meter (List MarkedAnchor)
  | [] => ⟨[],4⟩
  | x::xs =>
    let r := markOld diag cut x
    let tail := markTable diag cut xs
    ⟨r.result::tail.result,r.steps+tail.steps+4⟩

def compactSeatTape (a b q : ℕ) (diag : CellWord) (cut : List Bool) : Meter (List MarkedAnchor) :=
  let A := allSeatWords a b q
  let T := markTable diag cut A.result
  ⟨T.result,A.steps+T.steps+4⟩

private theorem mark_table_receipt {E : Type*} (f : E→AnchorWord) (g : E→Bool)
    (diag : CellWord) (cut : List Bool) (cs : List E) (cap : ℕ)
    (h : ∀ e∈cs, (markOld diag cut (f e)).result.old=g e ∧
        (markOld diag cut (f e)).steps=cap) :
    (markTable diag cut (cs.map f)).result=cs.map (fun e=>MarkedAnchor.mk (f e) (g e)) ∧
    (markTable diag cut (cs.map f)).steps=4+cs.length*(cap+4) := by
  induction cs with
  | nil => simp [markTable]
  | cons e es ih =>
    obtain ⟨ER,EC⟩ := h e List.mem_cons_self
    obtain ⟨r,s⟩ := ih (fun v hv=>h v (List.mem_cons_of_mem _ hv))
    constructor
    · simp only [List.map_cons,markTable,r]
      have R : (markOld diag cut (f e)).result=⟨f e,g e⟩ := by
        change MarkedAnchor.mk (f e) _=MarkedAnchor.mk (f e) _
        exact congrArg (MarkedAnchor.mk (f e)) ER
      rw [R]
    · simp only [List.map_cons,markTable,EC,s,List.length_cons,Nat.add_mul,one_mul]
      omega

theorem compact_seat_tape_exact {a b m l q : ℕ} (hq : 0<q) (ha : a≤q) (cap : b*2^a<2^q)
    (w : Fin a→Fin 64) (hm : m≤b) (hL : 2*l=2^a) :
    let run := compactSeatTape a b q (wordCell (diagonal w)) (encodeBits q (m*2^a))
    let seq := orderedWires w hm hL
    run.result=seq.map (fun e=>MarkedAnchor.mk (anchorAt q (placedRank w hm hL e)) (isPlanted e)) ∧
    run.steps≤completeSeatFee a b q+seq.length*(markFee a q+4)+8 := by
  obtain ⟨_,_,ex,_,C⟩ := actual_legal_chart_tape hq ha cap w hm hL
  have Q := mark_table_receipt (fun e=>anchorAt q (placedRank w hm hL e)) isPlanted
    (wordCell (diagonal w)) (encodeBits q (m*2^a)) (orderedWires w hm hL) (markFee a q)
    (fun e _=>mark_old_exact w hm hL cap e)
  constructor
  · unfold compactSeatTape
    dsimp only
    rw [ex]
    exact Q.1
  · unfold compactSeatTape
    dsimp only
    rw [ex,Q.2]
    omega

#print axioms placed_planted_iff
#print axioms same_token_exact
#print axioms mark_old_exact
#print axioms compact_seat_tape_exact
end J6R24LegalLayout
