
import J6R31RootResidentTablesMask
import J6R31RootResidentTablesRoster
import J6R31RootResidentTablesSeat

/-! One concrete initial source site supplies the three resident files
without an externally chosen mask table, seat table, or mode atlas.
The numeric copy/precision registers are already legal finite source
words; no acquisition of another site's register is asserted here. -/
namespace J6R31RootResidentTables
open scoped Classical
open AOracleMachineTime AOracleMachineTimeTape
open J6R30GeneratedRootLayout J6R24LegalLayout J6R14LayoutCost
open J6Mesh J6OrientedHost P11FullPacking J6R15ModeCost J6R17ModeTape J6R27OriginalGate
set_option maxHeartbeats 13500000
set_option maxRecDepth 2150

structure Resident (m q : ℕ) where
  axis : List Bool
  seats : List (SeatField (a m) (pageKeyWidth m))
  mask : List (MaskRow q)
  roster : RawTape q

def writeResidents {q : ℕ} (m : ℕ) (hq : 0<q) (i : Fin (a m)) (copies prec : Word q)
    {r c d : ℕ} (raw : List (SignedHalfPort r c d)) : Meter (Resident m q) :=
  let axis := List.replicate i.val false
  let s := rootSeats m axis raw
  let b := rootMaskBank hq m copies
  let R := rootRoster hq m i.val copies prec
  ⟨⟨axis,s.result,b.result,R.result⟩,s.steps+b.steps+R.steps+4*i.val+8⟩

def residentsFee (m q i p r c d : ℕ) :=
  seatsFee m r c d+maskBankFee m q+rosterFee m q i p+4*i+8

noncomputable def rosterIndex {A : Type*} (xs : List A) (unique : xs.Nodup) (all : ∀ y,y∈xs) :
    Fin xs.length≃A := Equiv.ofBijective xs.get
  ⟨fun _ _ eq=>unique.get_inj_iff.mp eq,fun y=>List.mem_iff_get.mp (all y)⟩

theorem actual_root_resident_tables {V : Type} [Fintype V] {m n r c d q p : ℕ}
    {T : Plant V m n} (P : LiteralPortFile T r c d)
    (hq : 0<q) (i : Fin (a m)) (hi : i.val+1<q) (copies prec : Word q)
    (hCopy : copies.val=K m) (hPrec : prec.val=p) (hp : 0<p) :
    let W := writeResidents m hq i copies prec P.raw
    W.result.axis.length=i.val ∧
      W.result.seats=(actualWires m).map (physicalSeatField (rootChart T) i (residentPageKey m)) ∧
      W.result.mask=(orderedRootPages m).map (encodeMaskRow (rootChart T).mask) ∧
      W.result.roster.precision.val=p ∧ W.result.roster.modes.Nodup ∧
      (∃ N : ℕ,∃ ξ : Fin N≃PacketMode i (K m) (2^(i.val+1)) p,
        W.result.roster.modes=List.ofFn (fun j=>encodeMode i (ξ j)) ∧
        W.result.roster.weights.map Word.val=List.ofFn (fun j=>modeWeight (ξ j))) ∧
      W.steps≤residentsFee m q i.val p r c d := by
  let axis := List.replicate i.val false
  let S := rootSeats m axis P.raw
  let B := rootMaskBank hq m copies
  let R := rootRoster hq m i.val copies prec
  have ax : axis.length=i.val := List.length_replicate
  obtain ⟨hS,sFee⟩ := root_seat_table_exact P i axis ax
  obtain ⟨hB,_,bFee⟩ := root_mask_bank_exact hq m copies hCopy
  obtain ⟨M,Mn,Ma,MM,Rn,Rw,Rp,rFee⟩ := root_ordered_roster_exact hq i hi copies prec hCopy hPrec hp
  refine ⟨ax,hS,hB,Rp,Rn,?_,?_⟩
  · let I := rosterIndex M Mn Ma
    have J : List.ofFn I=M := List.ofFn_get M
    refine ⟨M.length,I,?_,?_⟩
    · change R.result.modes=_
      refine MM.trans ((congrArg (List.map (encodeMode i)) J.symm).trans ?_)
      rw [List.map_ofFn]
      rfl
    · change R.result.weights.map Word.val=_
      refine Rw.trans ((congrArg (List.map modeWeight) J.symm).trans ?_)
      rw [List.map_ofFn]
      rfl
  · change S.steps+B.steps+R.steps+4*i.val+8≤_
    change S.steps≤_ at sFee
    change B.steps≤_ at bFee
    change R.steps≤_ at rFee
    unfold residentsFee
    omega

theorem printed_odd_residents {V : Type} [Fintype V] {m n r c d q base : ℕ}
    {T : Plant V m n} (P : LiteralPortFile T r c d)
    (hq : 0<q) (hQ : 1<q) (copies prec : Word q)
    (hCopy : copies.val=K m) (hPrec : prec.val=J6SourcePrecision.printed m base) :
    let i := oddAxis m
    let p := J6SourcePrecision.printed m base
    let W := writeResidents m hq i copies prec P.raw
    W.result.axis=[] ∧
      W.result.seats=(actualWires m).map (physicalSeatField (rootChart T) i (residentPageKey m)) ∧
      W.result.mask=(orderedRootPages m).map (encodeMaskRow (rootChart T).mask) ∧
      W.result.roster.precision.val=p ∧ W.result.roster.modes.Nodup ∧
      (∃ N : ℕ,∃ ξ : Fin N≃PacketMode i (K m) (2^(i.val+1)) p,
        W.result.roster.modes=List.ofFn (fun j=>encodeMode i (ξ j)) ∧
        W.result.roster.weights.map Word.val=List.ofFn (fun j=>modeWeight (ξ j))) ∧
      W.steps≤residentsFee m q 0 p r c d := by
  have G := actual_root_resident_tables P hq (oddAxis m) hQ copies prec hCopy hPrec
    (J6R28GeneratedRootFrame.printed_precision_positive m base)
  exact ⟨rfl,G.2⟩

#print axioms actual_root_resident_tables
#print axioms printed_odd_residents
end J6R31RootResidentTables
