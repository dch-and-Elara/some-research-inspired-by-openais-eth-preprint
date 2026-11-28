
import J6R25StableCensusRawCodec
import J6R25StableCensusPadOrder
import J6R24LegalLayoutTags
import J6R25StableCensusGeometry

/-! Generate the same stable ordered-cell padding pairs directly from
compact metadata. Skip exactly the whole planted prefix of its cell.
No full-chart inverse or precomputed list of typed positions is read. -/
namespace J6R25StableCensus
open scoped Classical BigOperators
open P11FullPacking J6OrientedHost J6RecursiveOrientation J6PhysicalPacking
open J6R24LegalLayout J6R23PaddingCensus J6R14LayoutCost J6R12CollisionEdges
open AOracleMachineTime AOracleMachineTimeTape
set_option maxHeartbeats 17000000
set_option maxRecDepth 1800
set_option linter.unusedSectionVars false

abbrev RawCol (a q : ℕ) := PadColumnWord (q-a+13*a) (a+1)

def expectedPair (a q : ℕ) (k : CellWord) (j : ℕ) : RawCol a q :=
  ⟨(encodeRawSeat a q (expectedAnchor a q k j).physical).result,
   (encodeRawSeat a q (expectedAnchor a q k (j+1)).physical).result⟩

def padStepFee (a q : ℕ) :=
  2*exportOneCap a+24*q+2*seatCodecFee a q+24*(a+q+3)

def pairRun (a q : ℕ) (k : CellWord) :
    List Bool→List Unit→Meter (List (RawCol a q))
  | _,[] => ⟨[],4⟩
  | r,_::cs =>
    let u := exportOne a k r
    let next := addBits r (encodeBits q 1)
    let v := exportOne a k next.result
    let after := addBits next.result (encodeBits q 1)
    let x := encodeRawSeat a q u.result
    let y := encodeRawSeat a q v.result
    let tail := pairRun a q k after.result cs
    ⟨⟨x.result,y.result⟩::tail.result,
      u.steps+next.steps+v.steps+after.steps+x.steps+y.steps+tail.steps+24*(a+q+3)⟩

private theorem fuse_fee (x : List AxisWord) (b : List Bool) :
    (fuseAxes x b).steps≤4+64*x.length := by
  induction x generalizing b with
  | nil => simp [fuseAxes]
  | cons u us ih =>
    cases b with
    | nil => simp [fuseAxes]
    | cons b bs =>
      have p := ih bs
      simp only [fuseAxes,List.length_cons]
      omega

private theorem codec_fee (a q : ℕ) (r : RawAddress) (h : r.axes.length=a) :
    (encodeRawSeat a q r).steps≤seatCodecFee a q := by
  have R := fuse_fee r.axes r.seat.selector
  rw [h] at R
  change (fuseAxes r.axes r.seat.selector).steps+12*(q+15*a+3)≤_
  unfold seatCodecFee
  omega

theorem pair_run_exact (a b q : ℕ) (hq : 0<q) (ha : a≤q) (cap : b*2^a<2^q)
    (c : CellType a) (j : ℕ) (clock : List Unit) (fit : j+2*clock.length≤b*2^a) :
    let out := pairRun a q (wordCell c) (encodeBits q j) clock
    out.result=List.ofFn (fun k : Fin clock.length=>expectedPair a q (wordCell c) (j+2*k.val)) ∧
    out.steps≤4+clock.length*padStepFee a q := by
  induction clock generalizing j with
  | nil => simp [pairRun]
  | cons u us ih =>
    have F : j+2+2*us.length≤b*2^a := by simp only [List.length_cons] at fit; omega
    have q1 : j+1<2^q := by omega
    have q2 : j+1+1<2^q := by omega
    let r := encodeBits q j
    let n1 := addBits r (encodeBits q 1)
    obtain ⟨b1,c1⟩ := succWord q j hq q1
    obtain ⟨b2,c2⟩ := succWord q (j+1) hq q2
    obtain ⟨R,C⟩ := ih (j+2) F
    have Ep : ∀ v : ℕ, v<b*2^a→
        (exportOne a (wordCell c) (encodeBits q v)).result.axes=axesOf c ∧
        (exportOne a (wordCell c) (encodeBits q v)).steps≤exportOneCap a := by
      intro v hv
      have eq := encodeBits_exact q v (hv.trans cap)
      obtain ⟨_,ax,_,_,_,f⟩ := exportOne_exact c (encodeBits q v)
        (by simpa only [encodeBits_length] using ha) (by rwa [eq])
      exact ⟨ax,f⟩
    have P := Ep j (by omega)
    have T := Ep (j+1) (by omega)
    have p1 := codec_fee a q (exportOne a (wordCell c) (encodeBits q j)).result
      (by rw [P.1,axesOf,List.length_ofFn])
    have p2 := codec_fee a q (exportOne a (wordCell c) (encodeBits q (j+1))).result
      (by rw [T.1,axesOf,List.length_ofFn])
    constructor
    · unfold pairRun
      dsimp only
      rw [b1,b2,R,List.ofFn_succ]
      simp only [expectedPair,expectedAnchor,Fin.val_zero,mul_zero,Nat.add_zero]
      congr 1
      apply congrArg List.ofFn
      funext i
      have E : j+2+2*i.val=j+2*i.succ.val := by simp only [Fin.val_succ]; omega
      rw [E]
    · unfold pairRun
      dsimp only
      rw [b1,b2,c1,c2,show j+1+1=j+2 by omega]
      simp only [List.length_cons,Nat.add_mul,one_mul]
      have h0 := P.2
      have h1 := T.2
      unfold padStepFee at C ⊢
      omega

def localCellPairs (a b l q m : ℕ) (diag k : CellWord) : Meter (List (RawCol a q)) :=
  let E := sameToken diag k
  let off := if E.result then m else 0
  let pairs := (b-off)*l
  let v := pairRun a q k (encodeBits q (off*2^a)) (List.replicate pairs ())
  ⟨v.result,E.steps+v.steps+12*q+16⟩

def padCellExtra (a q : ℕ) := 120*a+12*q+26

theorem local_cell_pairs (a b l q m : ℕ) (hq : 0<q) (ha : a≤q) (cap : b*2^a<2^q)
    (w : Fin a→Fin 64) (hm : m≤b) (hL : 2*l=2^a) (c : CellType a) :
    let out := localCellPairs a b l q m (wordCell (diagonal w)) (wordCell c)
    out.result=List.ofFn (fun j : Fin (padSpan m b l w c) =>
      expectedPair a q (wordCell c) (padStart m w c+2*j.val)) ∧
    out.steps≤padSpan m b l w c*padStepFee a q+padCellExtra a q := by
  have eq := same_token_exact a (diagonal w) c
  have off : (if (sameToken (wordCell (diagonal w)) (wordCell c)).result then m else 0)=
      offset (diagonal w) m c := by
    unfold offset
    by_cases h : c=diagonal w
    · rw [if_pos h,if_pos (eq.1.mpr h.symm)]
    · rw [if_neg h,if_neg (fun p=>h (eq.1.mp p).symm)]
  have H := pad_range_exact_tail w hm hL c
  have B := pair_run_exact a b q hq ha cap c (padStart m w c) (List.replicate (padSpan m b l w c) ())
    (by simpa only [List.length_replicate] using H.le)
  unfold localCellPairs
  dsimp only
  rw [off,eq.2]
  change (pairRun a q (wordCell c) (encodeBits q (padStart m w c)) (List.replicate (padSpan m b l w c) ())).result=_ ∧ _
  constructor
  · rw [B.1]
    simp only [List.length_replicate,Fin.coe_cast]
  · have P := B.2
    simp only [List.length_replicate] at P
    change 120*a+6+(pairRun a q (wordCell c) (encodeBits q (padStart m w c))
      (List.replicate (padSpan m b l w c) ())).steps+12*q+16≤_
    unfold padCellExtra
    omega

private theorem f2_map {A B D : Type*} (f : D→A) (g : D→B)
    (r : A→B→Prop) (z : List D) (h : ∀ d,r (f d) (g d)) :
    List.Forall₂ r (z.map f) (z.map g) := by
  induction z with
  | nil => exact .nil
  | cons a z ih => exact .cons (h a) ih

theorem local_realizes_pairs (a b l q m : ℕ) (hq : 0<q) (ha : a≤q) (cap : b*2^a<2^q)
    (w : Fin a→Fin 64) (hm : m≤b) (hL : 2*l=2^a) (c : CellType a) :
    let C := deterministicLegal ha cap.le w hm hL
    let out := localCellPairs a b l q m (wordCell (diagonal w)) (wordCell c)
    List.Forall₂ (fun (row : RawCol a q) (d : J6OrientedHost.Pad w m b l) =>
      row.represents (pageCode (q-a)) (fun side=>C.seats (.inr (d,side))))
      out.result (padsInCell m b l w c) := by
  let C := deterministicLegal ha cap.le w hm hL
  have H := (local_cell_pairs a b l q m hq ha cap w hm hL c).1
  dsimp only
  rw [H,List.ofFn_eq_map]
  unfold padsInCell
  apply f2_map
  intro j
  let d := localPad m b l w c j
  have addressEq (side : Bool) :
      anchorAt q (placedRank w hm hL (.inr (d,side)))=
        expectedAnchor a q (wordCell c) (padStart m w c+2*j.val+siteBit side) := by
    unfold anchorAt
    rw [(placed_rank_pad_address w hm hL c j side).1,(placed_rank_pad_address w hm hL c j side).2]
  have codec (side : Bool) :=
    (anchor_census_format ha cap.le (placedRank w hm hL (.inr (d,side)))).1
  constructor
  · have eq := codec false
    rw [addressEq false] at eq
    simpa only [siteBit,if_false,Bool.false_eq_true,add_zero] using eq
  · have eq := codec true
    rw [addressEq true] at eq
    simpa only [siteBit,if_true] using eq

#print axioms pair_run_exact
#print axioms local_cell_pairs
#print axioms local_realizes_pairs
end J6R25StableCensus
