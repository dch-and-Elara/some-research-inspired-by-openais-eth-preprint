import J4R43LiteralOutsideGeometry
import J7SeatPacking

/-! At every fixed position (not just the two endpoints), the genuinely
balanced mask gives exactly one seat of a given ordered cell per copy.
The interval guard is its two disjoint sets of real positions. -/
namespace J4R43LiteralOutside
open scoped Classical BigOperators
open P11FullPacking J7SeatPacking J6R10Repack
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000

variable {G : Type} [LinearOrder G] {a b : ℕ}

theorem twice_orient (k : Key (Fin a) G) (m : Orient k) (x : Fin (2^a)) :
    slotOrient k (slotOrient k m x) x=m := by
  funext j
  simp only [slotOrient,shiftMask]
  by_cases q : bits a x j.val=true <;> simp [q]

def inCellAt (c : Cell (Fin a) G) (j : Fin (2^a)) (k : Fin b) : SlotFiber (b:=b) c :=
  ⟨(⟨key c,(k,slotOrient (key c) (orientation c) j)⟩,j),by
    change cell (key c) (slotOrient (key c) (slotOrient (key c) (orientation c) j) j)=c
    rw [twice_orient,cell_decode]⟩

def positionChart (c : Cell (Fin a) G) :
    (Fin b×Fin (2^a)) ≃ SlotFiber (b:=b) c where
  toFun q := inCellAt c q.2 q.1
  invFun z := (z.val.1.2.1,z.val.2)
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨⟨k,bn,m⟩,j⟩,hj⟩
    change cell k (slotOrient k m j)=c at hj
    have hk : k=key c := by
      have H := congrArg key hj
      rwa [key_cell] at H
    subst k
    have o : slotOrient (key c) m j=orientation c :=
      cell_injective (key c) (hj.trans (cell_decode c).symm)
    have e : m=slotOrient (key c) (orientation c) j := by
      rw [←o,twice_orient]
    subst m
    rfl

abbrev BandIndex (a h : ℕ) := {j : Fin (2^a) // InBand (2^a) h j.val}
abbrev CellBand (c : Cell (Fin a) G) (h : ℕ) :=
  {q : SlotFiber (b:=b) c // InBand (2^a) h q.val.2.val}

def bandPositionChart (c : Cell (Fin a) G) (h : ℕ) :
    Fin b×BandIndex a h ≃ CellBand (b:=b) c h where
  toFun z := ⟨positionChart c (z.1,z.2.val),z.2.prop⟩
  invFun p := (((positionChart c).symm p.val).1,⟨p.val.val.2,p.prop⟩)
  left_inv _ := rfl
  right_inv q := by
    apply Subtype.ext
    exact (positionChart c).apply_symm_apply q.val

def bandHalves (h : ℕ) (fit : 2*h≤2^a) : Fin h⊕Fin h ≃ BandIndex a h := by
  let left (j : Fin h) : BandIndex a h :=
    ⟨⟨j.val,by have h := j.isLt; omega⟩,Or.inl j.isLt⟩
  let right (j : Fin h) : BandIndex a h :=
    ⟨⟨2^a-h+j.val,by have h := j.isLt; omega⟩,Or.inr (by change 2^a-h≤2^a-h+j.val; omega)⟩
  refine Equiv.ofBijective (Sum.elim left right) ⟨?_,?_⟩
  · rintro (j|j) (k|k) eq
    all_goals
      have E := congrArg (fun z : BandIndex a h=>z.val.val) eq
      have hj := j.isLt
      have hk := k.isLt
    · exact congrArg Sum.inl (Fin.ext E)
    · change j.val=2^a-h+k.val at E; omega
    · change 2^a-h+j.val=k.val at E; omega
    · change 2^a-h+j.val=2^a-h+k.val at E
      exact congrArg Sum.inr (Fin.ext (by omega))
  · rintro ⟨j,lo|hi⟩
    · exact ⟨.inl ⟨j.val,lo⟩,Subtype.ext (Fin.ext rfl)⟩
    · let k : Fin h := ⟨j.val-(2^a-h),by have h := j.isLt; omega⟩
      exact ⟨.inr k,Subtype.ext (Fin.ext (by change 2^a-h+(j.val-(2^a-h))=j.val; omega))⟩

theorem actual_cell_band_measure (c : Cell (Fin a) G) (h : ℕ) (fit : 2*h≤2^a) :
    Nat.card (CellBand (b:=b) c h)=2*h*b := by
  have H := Nat.card_congr (bandPositionChart (b:=b) c h)
  have K : Nat.card (BandIndex a h)=h+h := by
    calc
      _ = Nat.card (Fin h⊕Fin h) := Nat.card_congr (bandHalves (a:=a) h fit).symm
      _ = _ := by simp only [Nat.card_sum,Nat.card_fin]
  calc
    _ = b*(h+h) := by simpa only [Nat.card_prod,Nat.card_fin,K] using H.symm
    _ = _ := by ring

#print axioms twice_orient
#print axioms inCellAt
#print axioms positionChart
#print axioms bandPositionChart
#print axioms bandHalves
#print axioms actual_cell_band_measure
end
end J4R43LiteralOutside

