
import J6R24LegalLayoutStable

/-! Optional nonzero conventions: a local bit flip retargets a stable
raw slot within the same packet. Computing a compact mask's actual
per-packet bit record remains a separate input interface. -/
namespace J6R24LegalLayout
open scoped Classical BigOperators
open P11FullPacking J6OrientedHost J6RecursiveOrientation J6R23PaddingCensus
open AOracleMachineTime
set_option linter.unusedSectionVars false
set_option maxHeartbeats 15000000

def maskWordAt {a b : ℕ} (mask : MaskFamily a b (Fin 64)) (p : Page a b (Fin 64))
    (i : Fin a) : Bool :=
  if h : (p.1.val i).1≠(p.1.val i).2 then mask p.1 p.2 ⟨i,h⟩ else false

def slotFlip (x m : Bool) : Bool := if m then !x else x

noncomputable def twistSeat {a b : ℕ} (mask : MaskFamily a b (Fin 64)) (z : Physical a b (Fin 64)) :
    Physical a b (Fin 64) :=
  (z.1,(bitsChart a).symm (fun i=>slotFlip (bits a z.2 i) (maskWordAt mask z.1 i)))

theorem twist_seat_bit {a b : ℕ} (mask : MaskFamily a b (Fin 64)) (z : Physical a b (Fin 64))
    (i : Fin a) :
    bits a (twistSeat mask z).2 i = slotFlip (bits a z.2 i) (maskWordAt mask z.1 i) :=
  congrFun ((bitsChart a).apply_symm_apply _) i

theorem twist_seat_involutive {a b : ℕ} (mask : MaskFamily a b (Fin 64)) :
    Function.Involutive (twistSeat mask) := by
  intro z
  refine Prod.ext rfl ((bits_injective a) ?_)
  funext i
  rw [twist_seat_bit,twist_seat_bit]
  change slotFlip (slotFlip (bits a z.2 i) (maskWordAt mask z.1 i)) (maskWordAt mask z.1 i)=_
  cases bits a z.2 i <;> cases maskWordAt mask z.1 i <;> simp [slotFlip]

noncomputable def twistChart {a b : ℕ} (mask : MaskFamily a b (Fin 64)) :
    Equiv.Perm (Physical a b (Fin 64)) :=
  ⟨twistSeat mask,twistSeat mask,twist_seat_involutive mask,twist_seat_involutive mask⟩

theorem twist_preserves_ordered_cell {a b : ℕ} (mask : MaskFamily a b (Fin 64)) (z : Physical a b (Fin 64)) :
    physicalCell mask (twistSeat mask z)=physicalCell (fun _ _ _=>false) z := by
  unfold physicalCell
  change cell z.1.1 (slotOrient z.1.1 (mask z.1.1 z.1.2) (twistSeat mask z).2)=_
  congr 1
  funext i
  change shiftMask (mask z.1.1 z.1.2) (fun h=>bits a (twistSeat mask z).2 h.val) i =
    shiftMask (fun _=>false) (fun h=>bits a z.2 h.val) i
  simp only [shiftMask,twist_seat_bit,maskWordAt,dif_pos i.property]
  cases mask z.1.1 z.1.2 i <;> cases bits a z.2 i.val <;> simp [slotFlip]

theorem twist_diagonal_no_change {a b : ℕ} (mask : MaskFamily a b (Fin 64))
    (w : Fin a→Fin 64) (p : Fin b) (j : Fin (2^a)) :
    twistSeat mask (diagonalSlot w p j)=diagonalSlot w p j := by
  refine Prod.ext rfl ((bits_injective a) ?_)
  funext i
  rw [twist_seat_bit]
  have H : ¬ (((diagonalSlot w p j).1.1.val i).1 ≠ ((diagonalSlot w p j).1.1.val i).2) := by
    intro e
    exact (diagonal_no_hot w).false ⟨i,e⟩
  simp [maskWordAt,H,slotFlip]

noncomputable def maskedDeterministic {a b m l q : ℕ} (ha : a≤q) (cap : b*2^a≤2^q)
    (mask : MaskFamily a b (Fin 64)) (w : Fin a→Fin 64) (hm : m≤b) (hL : 2*l=2^a) :
    LegalRootChart w hm hL where
  seats := (deterministicLegal ha cap w hm hL).seats.trans (twistChart mask)
  plant u j := by
    change twistSeat mask ((deterministicLegal ha cap w hm hL).seats (.inl (u,j)))=_
    rw [(deterministicLegal ha cap w hm hL).plant,twist_diagonal_no_change]

theorem masked_deterministic_cell {a b m l q : ℕ} (ha : a≤q) (cap : b*2^a≤2^q)
    (mask : MaskFamily a b (Fin 64)) (w : Fin a→Fin 64) (hm : m≤b) (hL : 2*l=2^a)
    (e : Wire w m b l) :
    physicalCell mask ((maskedDeterministic ha cap mask w hm hL).seats e)=
      (J6PhysicalPacking.place (diagonal w) m b l hm e).1 := by
  exact (twist_preserves_ordered_cell mask _).trans (deterministic_legal_cell ha cap w hm hL e)

def flipTape : List Bool→List Bool→Meter (List Bool)
  | x::xs,m::ms =>
    let r := flipTape xs ms
    ⟨slotFlip x m::r.result,r.steps+8⟩
  | _,_ => ⟨[],4⟩

theorem flip_tape_exact (x m : List Bool) (h : x.length=m.length) :
    (flipTape x m).result=x.zipWith slotFlip m ∧ (flipTape x m).steps=4+8*x.length := by
  induction x generalizing m with
  | nil => simp [flipTape]
  | cons b bs ih =>
    cases m with
    | nil => simp at h
    | cons d ds =>
      obtain ⟨r,s⟩ := ih ds (Nat.succ.inj h)
      rw [List.length_cons]
      constructor
      · simp only [flipTape,r,List.zipWith_cons_cons]
      · simp only [flipTape,s]
        omega

private theorem zip_fn {n : ℕ} (x m : Fin n→Bool) :
    (List.ofFn x).zipWith slotFlip (List.ofFn m)=List.ofFn (fun i=>slotFlip (x i) (m i)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.ofFn_succ,List.zipWith_cons_cons]
    rw [ih]

theorem actual_slot_flip_word {a b : ℕ} (mask : MaskFamily a b (Fin 64)) (z : Physical a b (Fin 64)) :
    let inWord := List.ofFn (bits a z.2)
    let flags := List.ofFn (maskWordAt mask z.1)
    let out := flipTape inWord flags
    out.result=List.ofFn (bits a (twistSeat mask z).2) ∧ out.steps=4+8*a := by
  have P := flip_tape_exact (List.ofFn (bits a z.2)) (List.ofFn (maskWordAt mask z.1)) (by simp)
  rw [List.length_ofFn] at P
  refine ⟨P.1.trans ?_,P.2⟩
  rw [zip_fn]
  apply congrArg List.ofFn
  funext i
  exact (twist_seat_bit mask z i).symm

#print axioms twist_seat_bit
#print axioms twist_seat_involutive
#print axioms twist_preserves_ordered_cell
#print axioms twist_diagonal_no_change
#print axioms masked_deterministic_cell
#print axioms flip_tape_exact
#print axioms actual_slot_flip_word
end J6R24LegalLayout
