import J6R48RawRouteTagged
import J6R32ChildResidentTransferFull

/-! Raw finite adapters for the actual descendant greedy export. Attach
the saved pre-sort occurrence serial to each already-written seat. Read
back in source order by a charged sequential comparison scan. Neither
endpoints with the same labels nor padded unused slots are used as keys. -/
namespace J6R49SourceLayout
open AOracleMachineTime AOracleMachineTimeTape J6R15ModeCost J6R21Ancestor
open J6R14LayoutCost J6R27OriginalGate J6R31RootResidentTables
open J6R32ChildResidentTransfer J6R48RawRoute J6R12CollisionMenu J6R17ModeTape
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3200000
set_option Elab.async false

def rowSerials (q : ℕ) : List Seated → Meter (List (Word q))
  | [] => ⟨[],3⟩
  | x::xs =>
    let w := fitWord q x.tag.serial
    let t := rowSerials q xs
    ⟨w.result::t.result,w.steps+t.steps+5⟩

theorem row_serials_exact (q : ℕ) (rows : List Seated) :
    rowSerials q rows =
      ⟨rows.map (fun x=>(fitWord q x.tag.serial).result),3+(6*q+7)*rows.length⟩ := by
  induction rows with
  | nil => simp [rowSerials]
  | cons x xs ih =>
    simp only [rowSerials,ih,fit_word_fee,List.map_cons,List.length_cons,Nat.mul_succ]
    congr 1
    omega

def packedKeys (q : ℕ) : List ExportBox → Meter (List (Word q))
  | [] => ⟨[],4⟩
  | x::xs =>
    let r := rowSerials q x.rows
    let t := packedKeys q xs
    ⟨r.result++t.result,r.steps+t.steps+2*x.rows.length+6⟩

theorem packed_keys_exact (q : ℕ) (boxes : List ExportBox) :
    packedKeys q boxes = ⟨(seatedItems boxes).map
      (fun x=>(fitWord q x.2.tag.serial).result),4+(6*q+9)*exportRows boxes+9*boxes.length⟩ := by
  induction boxes with
  | nil => simp [packedKeys,seatedItems,exportRows]
  | cons x xs ih =>
    simp only [packedKeys,row_serials_exact,ih,seatedItems,List.flatMap_cons,
      List.map_append,List.map_map,List.length_cons]
    rw [show exportRows (x::xs)=x.rows.length+exportRows xs by simp [exportRows]]
    congr 1
    simp only [Nat.mul_add,Nat.mul_succ,show 6*q+9=6*q+7+2 by omega,Nat.add_mul]
    omega

/-- Include the sequential read of fields passed over in a packed
record, not only the q-bit key copied out of it. -/
def skipBits (xs : List Bool) : ℕ := (copyBytes xs).steps

def skipLabel : Option (List Bool) → ℕ
  | none => 2
  | some x => skipBits x+3

def skipSeated (x : Seated) : ℕ :=
  skipBits x.tag.edge.row.addr+skipLabel x.tag.edge.row.label+
  skipBits x.tag.edge.col.addr+skipLabel x.tag.edge.col.label+
  skipBits x.address.page+skipBits x.address.selector+skipBits x.address.slot+8

def skipBox (x : ExportBox) : ℕ :=
  skipBits x.key.1+skipBits x.key.2+
    (x.axes.map (fun t=>skipBits t.low+skipBits t.high+4)).sum+
    4*x.flags.length+(x.rows.map skipSeated).sum+8

def packingTraffic (boxes : List ExportBox) : ℕ :=
  (boxes.map skipBox).sum

def packedSerials (q : ℕ) (boxes : List ExportBox) : Meter (List (Word q)) :=
  let keys := packedKeys q boxes
  ⟨keys.result,keys.steps+packingTraffic boxes⟩

theorem packed_serials_exact (q : ℕ) (boxes : List ExportBox) :
    packedSerials q boxes = ⟨(seatedItems boxes).map
      (fun x=>(fitWord q x.2.tag.serial).result),
      4+(6*q+9)*exportRows boxes+9*boxes.length+packingTraffic boxes⟩ := by
  rw [packedSerials,packed_keys_exact]

def pairKeyedSeats {q a k : ℕ} : List (Word q) → List (SeatField a k) →
    Meter (Option (List (RefRow q (SeatField a k))))
  | [],[] => ⟨some [],4⟩
  | key::ks,row::rs =>
    let K := copyFixed key
    let R := copySeat row
    let T := pairKeyedSeats ks rs
    ⟨T.result.map ((⟨K.result,R.result⟩ : RefRow q (SeatField a k))::·),
      K.steps+R.steps+T.steps+8⟩
  | _,_ => ⟨none,4⟩

theorem paired_seats_exact {E : Type*} {q a k : ℕ} (es : List E)
    (key : E→Word q) (seat : E→SeatField a k) :
    pairKeyedSeats (es.map key) (es.map seat) =
      ⟨some (es.map (fun e=>⟨key e,seat e⟩)),4+(3*q+3*(a+k)+55)*es.length⟩ := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [List.map_cons,pairKeyedSeats,copy_fixed_exact,copied_seat_exact,ih,
      Option.map_some,List.length_cons,Nat.mul_succ]
    congr 1
    omega

/-- Read independent, stored serials and stored seat words in lockstep.
The optional answer guards against length mismatch; no sorting law
or dependent list is an input to the raw program. -/
def alignResidentSeats {q a k : ℕ} (boxes : List ExportBox) (rows : List (SeatField a k))
    (wanted : List (Word q)) : Meter (Option (List (SeatField a k))) :=
  let serials := packedSerials q boxes
  let bank := pairKeyedSeats serials.result rows
  match bank.result with
  | none => ⟨none,serials.steps+bank.steps+3⟩
  | some b =>
    let aligned := restoreSeats b wanted
    ⟨aligned.result,serials.steps+bank.steps+aligned.steps+6⟩

def alignFee (q a k n m b traffic : ℕ) : ℕ :=
  (4+(6*q+9)*m+9*b)+(4+(3*q+3*(a+k)+55)*m)+
    (4+n*(locateFee q m+3*(a+k)+54))+6+traffic

theorem align_resident_exact {E : Type*} {q a k : ℕ} (boxes : List ExportBox)
    (rows : List (SeatField a k)) (placed wanted : List E)
    (key : E→Word q) (seat : E→SeatField a k)
    (read : (packedSerials q boxes).result=placed.map key)
    (seatEq : rows=placed.map seat)
    (formed : placed.length=exportRows boxes)
    (inj : Function.Injective key) (all : ∀ e∈wanted,e∈placed) :
    let out := alignResidentSeats boxes rows (wanted.map key)
    out.result=some (wanted.map seat) ∧
    out.steps≤alignFee q a k wanted.length placed.length boxes.length (packingTraffic boxes) := by
  obtain ⟨res,fee⟩ := restore_order_exact wanted placed key seat inj all
  have rawFee : (packedSerials q boxes).steps=
      4+(6*q+9)*exportRows boxes+9*boxes.length+packingTraffic boxes :=
    congrArg Meter.steps (packed_serials_exact q boxes)
  unfold alignResidentSeats
  dsimp only
  rw [read,seatEq,paired_seats_exact]
  change (restoreSeats (placed.map (fun e=>⟨key e,seat e⟩)) (wanted.map key)).result=some (wanted.map seat) ∧
    (packedSerials q boxes).steps+(4+(3*q+3*(a+k)+55)*placed.length)
      +(restoreSeats (placed.map (fun e=>⟨key e,seat e⟩)) (wanted.map key)).steps+6≤_
  rw [rawFee,←formed]
  refine ⟨res,?_⟩
  unfold alignFee
  omega

/-- The stream drives one bounded-width ripple increment per actual
pre-sort record. The stride is charged for scanning the input record,
including those fields not interpreted by this loop. -/
def ordinalWordsFrom {A : Type*} (q stride : ℕ) :
    List Bool → List A → Meter (List (Word q))
  | _,[]=>⟨[],4⟩
  | current,_::xs =>
    let w := fitWord q current
    let inc := addBits current (encodeBits q 1)
    let tail := ordinalWordsFrom q stride inc.result xs
    ⟨w.result::tail.result,w.steps+inc.steps+tail.steps+stride+6⟩

theorem ordinal_words_from_exact {A : Type*} (q stride j : ℕ) (xs : List A)
    (pos : 0<q) (fit : j+xs.length<2^q) :
    ordinalWordsFrom q stride (encodeBits q j) xs =
      ⟨List.ofFn (fun l : Fin xs.length=>word (q:=q) (j+l.val)),
        4+(18*q+stride+8)*xs.length⟩ := by
  induction xs generalizing j with
  | nil => rfl
  | cons x xs ih =>
    have h' : j+1+xs.length<2^q := by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using fit
    have jFit : j+1<2^q := by omega
    have n := succWord q j pos jFit
    have w : (fitWord q (encodeBits q j)).result=word (q:=q) j := by
      apply word_bits_inj
      exact fit_word_value q _ (encodeBits_length _ _)
    rw [ordinalWordsFrom]
    simp only [w,fit_word_fee,n.1,n.2,ih (j+1) h',List.length_cons,List.ofFn_succ,
      Fin.val_zero,Nat.add_zero,Fin.val_succ,Nat.mul_succ]
    apply congrArg₂ (fun (v : List (Word q)) (n : ℕ)=>(⟨v,n⟩ : Meter (List (Word q))))
    · congr 1
      apply congrArg List.ofFn
      funext k
      congr 1
      omega
    · omega

def ordinalWords {A : Type*} (q stride : ℕ) (xs : List A) : Meter (List (Word q)) :=
  let s := ordinalWordsFrom q stride (encodeBits q 0) xs
  ⟨s.result,s.steps+q+2⟩

theorem ordinal_words_exact {A : Type*} (q stride : ℕ) (xs : List A)
    (pos : 0<q) (fit : xs.length<2^q) :
    ordinalWords q stride xs =
      ⟨List.ofFn (fun l : Fin xs.length=>word (q:=q) l.val),
        6+q+(18*q+stride+8)*xs.length⟩ := by
  simp only [ordinalWords,ordinal_words_from_exact q stride 0 xs pos (by simpa using fit),Nat.zero_add]
  congr 1
  omega

#print axioms row_serials_exact
#print axioms packed_serials_exact
#print axioms paired_seats_exact
#print axioms align_resident_exact
#print axioms ordinal_words_from_exact
#print axioms ordinal_words_exact
end J6R49SourceLayout