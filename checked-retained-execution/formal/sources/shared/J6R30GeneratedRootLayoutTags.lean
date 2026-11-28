
import J6R30GeneratedRootLayoutHeader
import J6R25StableCensusPadOrder

/-! Emit the complete stable root source identities. Input is the actual
generated ordered-cell rank tape. A planted ranked row reads the literal
wire ordinal and layer; a padding row reads its compressed pair ID and
actual free/negative-unary side. None of these are decoded from the
possibly reversed physical slot bits. -/
namespace J6R30GeneratedRootLayout
open scoped Classical
open P11FullPacking J6Mesh J6OrientedHost J6RecursiveOrientation J6R14LayoutCost
open J6R24LegalLayout J6R28GeneratedRootFrame
open AOracleMachineTime AOracleMachineTimeTape
set_option maxHeartbeats 11000000
set_option maxRecDepth 1900

abbrev RootWire (m : ℕ) := Wire (constantRootWord m) m (K m) (printedHalf m)

noncomputable abbrev rankAt (m : ℕ) (e : RootWire m) : FullRank (a m) (K m) :=
  placedRank (constantRootWord m) (printed_room m) (printed_half_correct m) e

noncomputable def sourceAnchor (m : ℕ) (e : RootWire m) : MarkedAnchor :=
  ⟨anchorAt (printedRankWidth m) (rankAt m e),isPlanted e⟩

theorem rank_fits (m : ℕ) (e : RootWire m) :
    (rankAt m e).2.val<2^printedRankWidth m :=
  (rankAt m e).2.isLt.trans (printed_rank_width m).2.2

theorem planted_rank_actual (m : ℕ) (u : Fin m) (j : Fin (2*printedHalf m)) :
    (rankAt m (.inl (u,j))).1=diagonal (constantRootWord m) ∧
      (rankAt m (.inl (u,j))).2.val=2^a m*u.val+j.val := by
  exact ⟨rfl,Nat.add_comm _ _⟩

def paddingPair (m : ℕ) (p : J6OrientedHost.Pad (constantRootWord m) m (K m) (printedHalf m)) : ℕ :=
  printedHalf m*(J6PhysicalPacking.offset (diagonal (constantRootWord m)) m p.1+p.2.1.val)+p.2.2.val

theorem padding_rank_actual (m : ℕ)
    (p : J6OrientedHost.Pad (constantRootWord m) m (K m) (printedHalf m)) (s : Bool) :
    (rankAt m (.inr (p,s))).1=p.1 ∧
      (rankAt m (.inr (p,s))).2.val=2*paddingPair m p+J6PhysicalPacking.siteBit s := by
  refine ⟨rfl,?_⟩
  change 2*p.2.2.val+J6PhysicalPacking.siteBit s+
    2^a m*(J6PhysicalPacking.offset (diagonal (constantRootWord m)) m p.1+p.2.1.val)=_
  rw [←show 2*printedHalf m=2^a m from printed_half_correct m]
  unfold paddingPair
  ring

theorem head_bit_modulo (x : List Bool) : (x.headD false).toNat=bitsValue x%2 := by
  cases x with
  | nil => rfl
  | cons b bs => cases b <;> simp only [List.headD_cons,bitsValue,Bool.toNat_false,Bool.toNat_true] <;> omega

def appendBits : List Bool→List Bool→Meter (List Bool)
  | [],ys=>⟨ys,2⟩
  | x::xs,ys=>
    let A := appendBits xs ys
    ⟨x::A.result,A.steps+4⟩

theorem append_bits_exact (xs ys : List Bool) :
    appendBits xs ys=⟨xs++ys,2+4*xs.length⟩ := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [appendBits,ih,List.cons_append,List.length_cons,Nat.mul_add,Nat.mul_one]
    congr 1

def splitBits : ℕ→List Bool→Meter (List Bool×List Bool)
  | 0,x=>⟨([],x),3⟩
  | _+1,[]=>⟨([],[]),3⟩
  | n+1,b::bs=>
    let A := splitBits n bs
    ⟨(b::A.result.1,A.result.2),A.steps+8⟩

theorem split_bits_exact (n : ℕ) (xs : List Bool) :
    (splitBits n xs).result=(xs.take n,xs.drop n) ∧
      (splitBits n xs).steps≤3+8*n := by
  induction n generalizing xs with
  | zero => simp [splitBits]
  | succ n ih =>
    cases xs with
    | nil => simp [splitBits]
    | cons x xs =>
      obtain ⟨r,c⟩ := ih xs
      constructor
      · simp [splitBits,r]
      · change (splitBits n xs).steps+8≤_
        omega

inductive OriginTag
  | literal (sourceWire layer : List Bool)
  | padding (cell : CellWord) (pair : List Bool) (free : Bool)

structure RootPortBase where
  anchor : MarkedAnchor
  key : List Bool
  origin : OriginTag

def packedKey (x : AnchorWord) : List Bool :=
  x.cell.1++(x.cell.2++x.rank)

def paidOrigin (a : ℕ) (x : MarkedAnchor) : Meter OriginTag :=
  if x.old then
    let s := splitBits a x.anchor.rank
    ⟨.literal s.result.2 s.result.1,s.steps+6⟩
  else
    let s := splitBits 1 x.anchor.rank
    ⟨.padding x.anchor.cell s.result.2 (s.result.1.headD false),s.steps+8⟩

theorem paid_origin_fee (a : ℕ) (x : MarkedAnchor) :
    (paidOrigin a x).steps≤8*a+19 := by
  unfold paidOrigin
  split
  · have H := (split_bits_exact a x.anchor.rank).2
    change (splitBits a x.anchor.rank).steps+6≤_
    omega
  · have H := (split_bits_exact 1 x.anchor.rank).2
    change (splitBits 1 x.anchor.rank).steps+8≤_
    omega

def writeBase (a : ℕ) (x : MarkedAnchor) : Meter RootPortBase :=
  let v := appendBits x.anchor.cell.2 x.anchor.rank
  let u := appendBits x.anchor.cell.1 v.result
  let g := paidOrigin a x
  ⟨⟨x,u.result,g.result⟩,u.steps+v.steps+g.steps+18⟩

def baseStride (a : ℕ) := 56*a+41

theorem write_base_form (a : ℕ) (x : MarkedAnchor)
    (widths : x.anchor.cell.1.length=6*a ∧ x.anchor.cell.2.length=6*a) :
    (writeBase a x).result=⟨x,packedKey x.anchor,(paidOrigin a x).result⟩ ∧
      (writeBase a x).steps≤baseStride a := by
  obtain ⟨h,k⟩ := widths
  have C := paid_origin_fee a x
  unfold writeBase packedKey baseStride
  simp only [append_bits_exact,h,k]
  exact ⟨True.intro,by omega⟩

noncomputable def writtenOrigin (m : ℕ) : RootWire m→OriginTag
  | .inl (u,j)=>.literal (encodeBits (RootKey m) u.val) (encodeBits (a m) j.val)
  | .inr (p,s)=>.padding (wordCell p.1) (encodeBits (printedRankWidth m-1) (paddingPair m p)) s

theorem source_origin_literal (m : ℕ) (u : Fin m) (j : Fin (2*printedHalf m)) :
    (paidOrigin (a m) (sourceAnchor m (.inl (u,j)))).result =
      writtenOrigin m (.inl (u,j)) := by
  let e : RootWire m := .inl (u,j)
  let q := printedRankWidth m
  let raw := encodeBits q (rankAt m e).2.val
  have rawLen : raw.length=q := encodeBits_length _ _
  have qa : a m≤q := (printed_rank_width m).2.1
  have jl : j.val<2^a m := j.isLt.trans_le (le_of_eq (printed_half_correct m))
  have uFit : u.val<2^RootKey m := u.isLt.trans (root_count_high_fit m)
  have rv : bitsValue raw=2^a m*u.val+j.val :=
    (encodeBits_exact _ _ (rank_fits m e)).trans (planted_rank_actual m u j).2
  have up : raw.drop (a m)=encodeBits (RootKey m) u.val := by
    apply J6R29BinaryFieldSearch.equal_width_inj
    · rw [List.length_drop,rawLen,encodeBits_length,RootKey]
    · rw [drop_value,rv,encodeBits_exact _ _ uFit,Nat.mul_add_div (by positivity),
        Nat.div_eq_of_lt jl,Nat.add_zero]
  have lo : raw.take (a m)=encodeBits (a m) j.val := by
    apply J6R29BinaryFieldSearch.equal_width_inj
    · rw [List.length_take,rawLen,encodeBits_length,Nat.min_eq_left qa]
    · rw [take_value,rv,encodeBits_exact _ _ jl,Nat.mul_add_mod,Nat.mod_eq_of_lt jl]
  change (if true then
    (⟨OriginTag.literal (splitBits (a m) raw).result.2 (splitBits (a m) raw).result.1,
      (splitBits (a m) raw).steps+6⟩ : Meter OriginTag) else _).result=_
  rw [if_pos rfl]
  dsimp only
  rw [(split_bits_exact (a m) raw).1]
  exact congrArg₂ OriginTag.literal up lo

theorem source_origin_padding (m : ℕ)
    (p : J6OrientedHost.Pad (constantRootWord m) m (K m) (printedHalf m)) (s : Bool) :
    (paidOrigin (a m) (sourceAnchor m (.inr (p,s)))).result =
      writtenOrigin m (.inr (p,s)) := by
  let e : RootWire m := .inr (p,s)
  let q := printedRankWidth m
  let raw := encodeBits q (rankAt m e).2.val
  have rawLen : raw.length=q := encodeBits_length _ _
  have rv : bitsValue raw=2*paddingPair m p+J6PhysicalPacking.siteBit s :=
    (encodeBits_exact _ _ (rank_fits m e)).trans (padding_rank_actual m p s).2
  have qpos : 0<q := (printed_rank_width m).1
  have pr : bitsValue (raw.drop 1)=paddingPair m p := by
    rw [drop_value,rv]
    cases s <;> simp only [J6PhysicalPacking.siteBit,Bool.false_eq_true,if_false,if_true] <;> omega
  have fit : paddingPair m p<2^(q-1) := by
    have B := bitsValue_lt (raw.drop 1)
    rw [pr,List.length_drop,rawLen] at B
    exact B
  have up : raw.drop 1=encodeBits (q-1) (paddingPair m p) := by
    apply J6R29BinaryFieldSearch.equal_width_inj
    · rw [List.length_drop,rawLen,encodeBits_length]
    · rw [pr,encodeBits_exact _ _ fit]
  have hBit : (raw.take 1).headD false=s := by
    have b : (raw.take 1).headD false=raw.headD false := by
      cases raw using List.casesOn <;> rfl
    rw [b]
    have pr := head_bit_modulo raw
    rw [rv] at pr
    cases s <;> cases h : raw.headD false <;>
      simp only [h,J6PhysicalPacking.siteBit,Bool.false_eq_true,if_false,if_true,
        Bool.toNat_false,Bool.toNat_true] at pr ⊢ <;> omega
  have key : (sourceAnchor m e).anchor.cell=wordCell p.1 :=
    congrArg wordCell (padding_rank_actual m p s).1
  change (if false then _ else
    (⟨OriginTag.padding (sourceAnchor m e).anchor.cell (splitBits 1 raw).result.2
      ((splitBits 1 raw).result.1.headD false),(splitBits 1 raw).steps+8⟩ : Meter OriginTag)).result=_
  rw [if_neg (by decide : false≠true)]
  dsimp only
  rw [(split_bits_exact 1 raw).1]
  rw [key,up,hBit]
  rfl

theorem source_origin_exact (m : ℕ) (e : RootWire m) :
    (paidOrigin (a m) (sourceAnchor m e)).result=writtenOrigin m e := by
  rcases e with (⟨u,j⟩|⟨p,s⟩)
  · exact source_origin_literal m u j
  · exact source_origin_padding m p s

noncomputable def expectedBase (m : ℕ) (e : RootWire m) : RootPortBase :=
  ⟨sourceAnchor m e,packedKey (sourceAnchor m e).anchor,writtenOrigin m e⟩

theorem base_at_wire (m : ℕ) (e : RootWire m) :
    (writeBase (a m) (sourceAnchor m e)).result=expectedBase m e ∧
    (writeBase (a m) (sourceAnchor m e)).steps≤baseStride (a m) := by
  have f := write_base_form (a m) (sourceAnchor m e)
    ⟨coordinateLabel_len _,coordinateLabel_len _⟩
  exact ⟨f.1.trans (congrArg _ (source_origin_exact m e)),f.2⟩

theorem base_key_injective (m : ℕ) :
    Function.Injective (fun e : RootWire m=>(expectedBase m e).key) := by
  intro u v eq
  let U := rankAt m u
  let V := rankAt m v
  change (wordCell U.1).1++((wordCell U.1).2++encodeBits (printedRankWidth m) U.2.val)=
    (wordCell V.1).1++((wordCell V.1).2++encodeBits (printedRankWidth m) V.2.val) at eq
  have L := List.append_inj eq ((coordinateLabel_len _).trans (coordinateLabel_len _).symm)
  have R := List.append_inj L.2 ((coordinateLabel_len _).trans (coordinateLabel_len _).symm)
  have c : U.1=V.1 := word_cell_injective _ (Prod.ext L.1 R.1)
  have h := congrArg bitsValue R.2
  rw [encodeBits_exact _ _ (rank_fits m u),encodeBits_exact _ _ (rank_fits m v)] at h
  exact (placedRank _ (printed_room m) (printed_half_correct m)).injective (Prod.ext c (Fin.ext h))

theorem base_key_width (m : ℕ) (e : RootWire m) :
    (expectedBase m e).key.length=12*a m+printedRankWidth m := by
  change ((wordCell (rankAt m e).1).1++((wordCell (rankAt m e).1).2++
      encodeBits (printedRankWidth m) (rankAt m e).2.val)).length=_
  simp only [List.length_append,wordCell,coordinateLabel_len,encodeBits_length]
  omega

def baseTable (a : ℕ) : List MarkedAnchor→Meter (List RootPortBase)
  | []=>⟨[],4⟩
  | x::xs=>
    let B := writeBase a x
    let T := baseTable a xs
    ⟨B.result::T.result,B.steps+T.steps+4⟩

theorem base_table_exact (m : ℕ) (xs : List (RootWire m)) :
    (baseTable (a m) (xs.map (sourceAnchor m))).result=xs.map (expectedBase m) ∧
    (baseTable (a m) (xs.map (sourceAnchor m))).steps≤4+xs.length*(baseStride (a m)+4) := by
  induction xs with
  | nil => simp [baseTable]
  | cons x xs ih =>
    obtain ⟨B,C⟩ := base_at_wire m x
    obtain ⟨e,f⟩ := ih
    simp only [List.map_cons,baseTable,B,e,true_and,List.length_cons,Nat.succ_mul]
    omega

def generatedBases (m : ℕ) {D : Type*} (literal : List D) : Meter (List RootPortBase) :=
  let file := generatedAnchors m literal
  let out := baseTable (a m) file.result
  ⟨out.result,file.steps+out.steps+5⟩

def basesFee (m : ℕ) := anchorsFee m+4+M m*(baseStride (a m)+4)+5

theorem generated_bases_exact (m : ℕ) {D : Type*} (literal : List D) (hl : literal.length=m) :
    let O := generatedBases m literal
    O.result=(actualWires m).map (expectedBase m) ∧
    O.result.length=M m ∧
    (O.result.map RootPortBase.key).Nodup ∧ O.steps≤basesFee m := by
  obtain ⟨E,_,paid⟩ := generated_anchors_exact m literal hl
  change (generatedAnchors m literal).result=(actualWires m).map (sourceAnchor m) at E
  have R := base_table_exact m (actualWires m)
  have C := ordered_wires_exact (constantRootWord m) (printed_room m) (printed_half_correct m)
  have hmap : ((actualWires m).map (expectedBase m)).map RootPortBase.key =
      (actualWires m).map (fun e=>(expectedBase m e).key) := by
    rw [List.map_map]
    rfl
  have hResult : (generatedBases m literal).result=(actualWires m).map (expectedBase m) := by
    change (baseTable (a m) (generatedAnchors m literal).result).result=_
    rw [E,R.1]
  refine ⟨hResult,by rw [hResult,List.length_map,actual_wires_count],?_,?_⟩
  · rw [hResult,hmap]
    exact C.1.map (base_key_injective m)
  · change (generatedAnchors m literal).steps+(baseTable (a m) (generatedAnchors m literal).result).steps+5≤_
    rw [E]
    have W := R.2
    rw [actual_wires_count] at W
    unfold basesFee
    omega

#print axioms planted_rank_actual
#print axioms padding_rank_actual
#print axioms source_origin_exact
#print axioms base_key_injective
#print axioms base_key_width
#print axioms generated_bases_exact
end J6R30GeneratedRootLayout
