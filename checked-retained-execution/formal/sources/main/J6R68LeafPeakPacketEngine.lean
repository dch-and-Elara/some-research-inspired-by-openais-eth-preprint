import J6R68LeafPeakPacketTables
import J6R48LeafRawTape
import J6R19RetainedWords

/-! One actual generated entry gathers the current Boolean ports once,
then normalizes creation ancestry and returns full routed row/column
assignments. These are actual tapes, not another immutable atlas. -/
namespace J6R68.LeafPeak.Packet
open AOracleMachineTime A1R12 J6R18ChildWrite J6R20Ancestor J6R21Ancestor J6R48Leaf
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 5500000
set_option Elab.async false

def rawBits (raw : List Raw) : List Bool := raw.flatMap (fun u=>u.1++[u.2])
def gatheredWidth (wires : List WireRead) : ℕ := (wires.map (fun u=>u.header.length+1)).sum
def slotBitWords {a : ℕ} (v : SlotBit a) : List Bool := v.slot.bits++[v.assigned]
def parsedWords {a : ℕ} (v : Key a×Bool) : List Bool := v.1.slot.bits++[v.1.side,v.2]

theorem actual_gather_result_width (w : ℕ) (wires : List WireRead) (bits : List Bool) :
    let out := (gather w wires bits).result
    out.length=wires.length ∧ (rawBits out).length=gatheredWidth wires := by
  refine ⟨(raw_wire_gather_steps w wires bits).1,?_⟩
  unfold rawBits gather
  rw [map_result,List.flatMap_map]
  induction wires with
  | nil => rfl
  | cons u us ih =>
    simp only [List.flatMap_cons,List.length_append,gatheredWidth,List.map_cons,
      List.sum_cons,(attachBit_exact bits u).1,List.length_cons,List.length_nil]
    exact congrArg (fun n=>u.header.length+1+n) ih

theorem strip_return_length {d : ℕ} {xs ys : List Bool}
    (good : (strip d xs).result=some ys) : ys.length≤xs.length := by
  induction d generalizing xs ys with
  | zero =>
    change some xs=some ys at good
    rw [Option.some.inj good]
  | succ d ih =>
    cases xs with
    | nil => simp [strip] at good
    | cons bit xs =>
      cases bit
      · have hh : (strip d xs).result=some ys := good
        exact (ih hh).trans (Nat.le_succ _)
      · simp [strip] at good

theorem normalize_cell_bound (d : ℕ) (r : Raw) :
    (J6R21Ancestor.normalize d r).result.1.length≤r.1.length+1 := by
  unfold J6R21Ancestor.normalize
  dsimp only
  cases e : (strip d r.1).result with
  | none => simp
  | some tail =>
    change tail.length+1≤r.1.length+1
    exact Nat.succ_le_succ (strip_return_length e)

theorem actual_normalized_tape_length (a d : ℕ) (raw : List Raw) :
    let out := (normalizeTape a d raw).result
    out.length=raw.length ∧ (rawBits out).length≤(rawBits raw).length+raw.length := by
  let map := (normalizeTape_exact a d raw).1
  change (normalizeTape a d raw).result.length=raw.length ∧
    (rawBits (normalizeTape a d raw).result).length≤_
  rw [map,List.length_map]
  refine ⟨rfl,?_⟩
  unfold rawBits
  rw [List.flatMap_map]
  induction raw with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.flatMap_cons,List.length_cons,List.length_nil,List.length_append] at ih ⊢
    have cap := normalize_cell_bound d r
    omega

theorem actual_route_named_tapes
    {a : ℕ} (d : ℕ) (rs cs : List (J6R15ModeCost.Word a)) (raw : List Raw) :
    let N := (normalizeTape a d raw).result
    let P := (readTape a N).result
    let R := (routeTrace d rs cs raw).result
    R.1.length=rs.length ∧ R.2.length=cs.length ∧
    (rawBits raw).length+(rawBits N).length+(P.flatMap parsedWords).length+
      (R.1.flatMap slotBitWords).length+(R.2.flatMap slotBitWords).length≤
      2*(rawBits raw).length+raw.length*(a+3)+(rs.length+cs.length)*(a+1) := by
  let N := (normalizeTape a d raw).result
  let P := (readTape a N).result
  let R := (routeTrace d rs cs raw).result
  obtain ⟨normalLen,normalCap⟩ := actual_normalized_tape_length a d raw
  obtain ⟨rowLen,colLen,_⟩ := raw_route_caps d rs cs raw
  have card : P.length≤raw.length := (raw_tape_parse_caps a N).1.trans_eq normalLen
  have parsed : (P.flatMap parsedWords).length≤raw.length*(a+2) := by
    rw [flatWidth P parsedWords (a+2) (fun x _=>by
      simp only [parsedWords,List.length_append,x.1.slot.size,List.length_cons,List.length_nil])]
    exact Nat.mul_le_mul_right _ card
  have rlen : (R.1.flatMap slotBitWords).length=rs.length*(a+1) := by
    rw [flatWidth R.1 slotBitWords (a+1) (fun x _=>by
      simp only [slotBitWords,List.length_append,x.slot.size,List.length_cons,List.length_nil]),rowLen]
  have clen : (R.2.flatMap slotBitWords).length=cs.length*(a+1) := by
    rw [flatWidth R.2 slotBitWords (a+1) (fun x _=>by
      simp only [slotBitWords,List.length_append,x.slot.size,List.length_cons,List.length_nil]),colLen]
  change R.1.length=rs.length ∧ R.2.length=cs.length ∧
    (rawBits raw).length+(rawBits N).length+(P.flatMap parsedWords).length+
      (R.1.flatMap slotBitWords).length+(R.2.flatMap slotBitWords).length≤_
  refine ⟨rowLen,colLen,?_⟩
  rw [rlen,clen]
  calc
    _ ≤ (rawBits raw).length+((rawBits raw).length+raw.length)+raw.length*(a+2)+
        rs.length*(a+1)+cs.length*(a+1) :=
      Nat.add_le_add_right (Nat.add_le_add_right
        (Nat.add_le_add (Nat.add_le_add_left normalCap _) parsed) _) _
    _ = _ := by ring

#print axioms actual_gather_result_width
#print axioms actual_normalized_tape_length
#print axioms actual_route_named_tapes
end J6R68.LeafPeak.Packet


/-! The real exponentially long choice search can be deep without
holding even a single table of its candidate leaves. It can hold older
right-fold siblings, and the inequalities charge those actual blocks. -/
namespace J6R68.LeafPeak.Packet
open AOracleMachineTime A1R10 A1R12 J6R18ChildWrite J6R21Leaf
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 6500000
set_option Elab.async false

variable {p ell : ℕ} {fw : List (A1R10.Word p)}
def choiceOperation (hp : 0<p) (b q : ℕ) (checks : List (List Bool×List Bool))
    (rest : List (List (Term fw ell))) (picked : List (List Bool)) (acc : UVBlock fw ell)
    (t : Term fw ell) : Meter (UVBlock fw ell) :=
  let z := uvMul hp acc t.value
  let got := evalRows hp b q checks rest (t.code::picked) z.result
  ⟨got.result,got.steps+z.steps+b+2*(A1R11.uvWidth fw.length ell p)+8⟩

theorem actual_row_branch_has_exact_suffix_context
    (hp : 0<p) (b q : ℕ) (checks : List (List Bool×List Bool))
    (rest : List (List (Term fw ell))) (picked : List (List Bool))
    (acc : UVBlock fw ell) (before after : List (Term fw ell)) (t : Term fw ell) :
    let choose := choiceOperation hp b q checks rest picked acc
    let earlier := before.map choose
    let tail := sumUV hp choose after
    evalRows hp b q checks ((before++t::after)::rest) picked acc=
      earlier.foldr (addM hp) (addM hp (choose t) tail) := by
  let choose := choiceOperation hp b q checks rest picked acc
  change sumUV hp choose (before++t::after) =
    (before.map choose).foldr (addM hp) (addM hp (choose t) (sumUV hp choose after))
  induction before with
  | nil => rfl
  | cons u us ih =>
    change addM hp (choose u) (sumUV hp choose (us++t::after)) =
      addM hp (choose u) ((us.map choose).foldr (addM hp) (addM hp (choose t) (sumUV hp choose after)))
    rw [ih]

/-- The blocks held during the deeper call consist of the actual
parent product (needed for later choices), and the completed strict
left operands of the current row's right-nested sum. -/
inductive ChoiceCut (hp : 0<p) (b q : ℕ) (checks : List (List Bool×List Bool))
    (whole : List (List (Term fw ell))) (start : UVBlock fw ell) :
    List (List (Term fw ell))→List (List Bool)→UVBlock fw ell→List (UVBlock fw ell)→Prop
  | enter : ChoiceCut hp b q checks whole start whole [] start []
  | descend {rest : List (List (Term fw ell))} {picked : List (List Bool)} {acc : UVBlock fw ell}
      {before after : List (Term fw ell)} {x : Term fw ell} {held : List (UVBlock fw ell)}
      (parent : ChoiceCut hp b q checks whole start ((before++x::after)::rest) picked acc held) :
      ChoiceCut hp b q checks whole start rest (x.code::picked) (uvMul hp acc x.value).result
        (acc::(before.map (fun u=>(choiceOperation hp b q checks rest picked acc u).result))++held)

theorem actual_choice_cut_has_only_real_depth_and_prior_results
    {hp : 0<p} {b q cap : ℕ} {checks : List (List Bool×List Bool)}
    {whole rest : List (List (Term fw ell))} {start acc : UVBlock fw ell}
    {picked : List (List Bool)} {held : List (UVBlock fw ell)}
    (fits : ∀ r∈whole,r.length≤cap ∧ ∀ t∈r,t.code.length=b)
    (cut : ChoiceCut hp b q checks whole start rest picked acc held) :
    (∀ r∈rest,r∈whole) ∧
      rest.length+picked.length=whole.length ∧
      (picked.flatten).length=picked.length*b ∧ held.length≤picked.length*cap := by
  induction cut with
  | enter => simp
  | @descend rest picked acc before after x held parent ih =>
    have real := fits (before++x::after) (ih.1 _ List.mem_cons_self)
    have chosen := real.2 x (List.mem_append_right _ List.mem_cons_self)
    have visited : before.length+1≤cap := by
      have h := real.1
      rw [List.length_append,List.length_cons] at h
      omega
    refine ⟨fun r hr=>ih.1 r (List.mem_cons_of_mem _ hr),?_,?_,?_⟩
    · have h := ih.2.1
      simp only [List.length_cons] at h ⊢
      omega
    · rw [List.flatten_cons,List.length_append,chosen,ih.2.2.1,List.length_cons,Nat.succ_mul]
      exact Nat.add_comm _ _
    · simp only [List.length_cons,List.length_append,List.length_map,Nat.succ_mul]
      have hl := ih.2.2.2
      omega

def choiceBudget (r cap b width : ℕ) : ℕ :=
  r*(cap*width+b)+4*width

/-- A reached row-loop cut includes the genuine prior siblings, the
actual parent product, current child value, tail sum, and combined result.
These are a named lifetime bound and no claim about unlisted primitive
arithmetic internals. -/
theorem actual_choice_add_cut_uses_bounded_named_registers
    {hp : 0<p} {b q cap : ℕ} {checks : List (List Bool×List Bool)}
    {whole rest : List (List (Term fw ell))} {start acc : UVBlock fw ell}
    {picked : List (List Bool)} {held : List (UVBlock fw ell)}
    (before after : List (Term fw ell)) (x : Term fw ell)
    (fits : ∀ r∈whole,r.length≤cap ∧ ∀ t∈r,t.code.length=b)
    (cut : ChoiceCut hp b q checks whole start ((before++x::after)::rest) picked acc held) :
    let g := choiceOperation hp b q checks rest picked acc
    let done := before.map (fun t=>(g t).result)
    let tail := sumUV hp g after
    let next := addM hp (g x) tail
    (held.flatMap leafPayload).length+(picked.flatten).length+
      (done.flatMap leafPayload).length+(leafPayload acc).length+
      (leafPayload (g x).result).length+(leafPayload tail.result).length+
      (leafPayload next.result).length≤choiceBudget whole.length cap b (ell*(fw.length*p)) := by
  let W := ell*(fw.length*p)
  let g := choiceOperation hp b q checks rest picked acc
  obtain ⟨on,hh,pref,old⟩ := actual_choice_cut_has_only_real_depth_and_prior_results fits cut
  have this := (fits _ (on _ List.mem_cons_self)).1
  simp only [List.length_append,List.length_cons] at this hh
  have count : held.length+before.length≤whole.length*cap := by
    refine (Nat.add_le_add old (show before.length≤cap from by omega)).trans ?_
    rw [←Nat.succ_mul]
    exact Nat.mul_le_mul_right _ (by omega)
  have prelen : picked.length≤whole.length := by omega
  change (held.flatMap leafPayload).length+(picked.flatten).length+
    ((before.map (fun t=>(g t).result)).flatMap leafPayload).length+
    (leafPayload acc).length+(leafPayload (g x).result).length+
    (leafPayload (sumUV hp g after).result).length+
    (leafPayload (addM hp (g x) (sumUV hp g after)).result).length≤_
  rw [encoded_blocks_width,encoded_blocks_width,List.length_map,pref,
    leaf_payload_width,leaf_payload_width,leaf_payload_width,leaf_payload_width]
  change held.length*W+picked.length*b+before.length*W+W+W+W+W≤_
  have h₁ := Nat.mul_le_mul_right W count
  have h₂ := Nat.mul_le_mul_right b prelen
  calc
    _ = (held.length+before.length)*W+picked.length*b+4*W := by ring
    _ ≤ whole.length*cap*W+whole.length*b+4*W :=
      Nat.add_le_add_right (Nat.add_le_add h₁ h₂) _
    _ = _ := by simp only [choiceBudget]; ring

/-- At a tested complete choice the only selected allocation is its
own picked; the rest of the live choice words are actual older row
results. Count current accumulator and returned word separately. -/
theorem actual_choice_test_cut_uses_bounded_named_registers
    {hp : 0<p} {b q cap : ℕ} {checks : List (List Bool×List Bool)}
    {whole : List (List (Term fw ell))} {start acc : UVBlock fw ell}
    {picked : List (List Bool)} {held : List (UVBlock fw ell)}
    (fits : ∀ r∈whole,r.length≤cap ∧ ∀ t∈r,t.code.length=b)
    (cut : ChoiceCut hp b q checks whole start [] picked acc held) :
    let now := evalRows hp b q checks [] picked acc
    now.result=(if (A1R9.checkModes q picked checks).result then acc else uvZero hp fw ell) ∧
    (held.flatMap leafPayload).length+(picked.flatten).length+(leafPayload acc).length+
      (leafPayload now.result).length≤choiceBudget whole.length cap b (ell*(fw.length*p)) := by
  obtain ⟨_,total,pbytes,hcount⟩ := actual_choice_cut_has_only_real_depth_and_prior_results fits cut
  have len : picked.length=whole.length := by simpa only [List.length_nil,Nat.zero_add] using total
  rw [len] at pbytes hcount
  refine ⟨rfl,?_⟩
  dsimp only
  rw [encoded_blocks_width,pbytes,leaf_payload_width,leaf_payload_width]
  let W := ell*(fw.length*p)
  calc
    _ ≤ whole.length*cap*W+whole.length*b+W+W :=
      Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right
        (Nat.mul_le_mul_right W hcount) _) _) _
    _ ≤ whole.length*cap*W+whole.length*b+4*W := by omega
    _ = _ := by unfold choiceBudget; ring

#print axioms actual_row_branch_has_exact_suffix_context
#print axioms actual_choice_cut_has_only_real_depth_and_prior_results
#print axioms actual_choice_add_cut_uses_bounded_named_registers
#print axioms actual_choice_test_cut_uses_bounded_named_registers
end J6R68.LeafPeak.Packet


/-! Named native words in the one-entry arithmetic on the actual
creation frame. Neither the source moment loop nor exponentiation
is an oracle. This is separate from UV primitive scratch. -/
namespace J6R68.LeafPeak.Packet
open AOracleMachineTime AOracleMachineTimeTape AOracleMachineTimeMul
open A1R10 A1R12 J6R18ChildWrite J6R19Retained J6R21Leaf
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 6200000
set_option Elab.async false

variable {p ell : ℕ} {fw : List (A1R10.Word p)}

theorem packet_source_product_holds_actual_factors
    {a q : ℕ} (hp : 0<p) (he : 0<fw.length) (pos : 0<ell) (i : Fin a) (cs : List (SlotBit a))
    (pre tail : List (ModeInput a p i q)) (x : ModeInput a p i q) :
    let column := sourcePower (q:=q) hp he pos i cs
    let older := pre.map column
    let current := column x
    let suffix := sourceProduct hp he pos i cs tail
    sourceProduct hp he pos i cs (pre++x::tail)=
      older.foldr (mulM hp) (mulM hp current suffix) ∧
    ((older.map Meter.result).flatMap leafPayload).length+
      (leafPayload current.result).length+(leafPayload suffix.result).length+
        (leafPayload (mulM hp current suffix).result).length=
      (pre.length+3)*(ell*(fw.length*p)) := by
  let column := sourcePower (q:=q) hp he pos i cs
  let older := pre.map column
  let current := column x
  let suffix := sourceProduct hp he pos i cs tail
  constructor
  · change foldM hp he pos column (pre++x::tail)=
      (pre.map column).foldr (mulM hp) (mulM hp current suffix)
    induction pre with
    | nil => rfl
    | cons u us ih =>
      change mulM hp (column u) (foldM hp he pos column (us++x::tail))=
        mulM hp (column u) ((us.map column).foldr (mulM hp) (mulM hp current suffix))
      rw [ih]
  · change ((older.map Meter.result).flatMap leafPayload).length+
      (leafPayload current.result).length+(leafPayload suffix.result).length+
      (leafPayload (mulM hp current suffix).result).length=_
    rw [encoded_blocks_width,List.length_map,show older.length=pre.length from List.length_map _,
      leaf_payload_width,leaf_payload_width,leaf_payload_width]
    ring

inductive PowerCut (hp : 0<p) (he : 0<fw.length) (pos : 0<ell)
    (whole : List Bool) (seed : UVBlock fw ell) :
    List Bool→UVBlock fw ell→List (UVBlock fw ell)→Prop
  | enter : PowerCut hp he pos whole seed whole seed []
  | step {b : Bool} {tail : List Bool} {x : UVBlock fw ell} {held : List (UVBlock fw ell)}
      (cur : PowerCut hp he pos whole seed (b::tail) x held) :
      PowerCut hp he pos whole seed tail (uvMul hp x x).result (x::held)

theorem power_cut_depth
    {hp : 0<p} {he : 0<fw.length} {pos : 0<ell}
    {all rest : List Bool} {seed x : UVBlock fw ell} {held : List (UVBlock fw ell)}
    (cut : PowerCut hp he pos all seed rest x held) :
    rest.length+held.length=all.length := by
  induction cut with
  | enter => simp
  | step cur ih =>
    simp only [List.length_cons] at ih ⊢
    omega

theorem live_power_uses_only_actual_earlier_bases_and_one_return
    {hp : 0<p} {he : 0<fw.length} {pos : 0<ell} {all tail : List Bool}
    {seed x : UVBlock fw ell} {held : List (UVBlock fw ell)} (b : Bool)
    (cut : PowerCut hp he pos all seed (b::tail) x held) :
    let sq := uvMul hp x x
    let child := powBits hp he pos tail sq.result
    let out := if b then uvMul hp x child.result else Meter.pure child.result
    (powBits hp he pos (b::tail) x).result=out.result ∧
    (held.flatMap leafPayload).length+(leafPayload x).length+(leafPayload sq.result).length+
      (leafPayload child.result).length+(leafPayload out.result).length≤
      (all.length+3)*(ell*(fw.length*p)) := by
  have depth := power_cut_depth cut
  have reserve : held.length+4≤all.length+3 := by
    simp only [List.length_cons] at depth
    omega
  refine ⟨rfl,?_⟩
  dsimp only
  rw [encoded_blocks_width,leaf_payload_width,leaf_payload_width,leaf_payload_width,leaf_payload_width]
  calc
    _ = (held.length+4)*(ell*(fw.length*p)) := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ reserve

theorem packet_word_resize_keeps_a_real_old_operand_and_return
    {q : ℕ} {new : List (A1R10.Word q)} (compat : fw.length=new.length)
    (pre : UVBlock fw ell) (cursor : ℕ) :
    (leafPayload pre).length+((leafPayload (resizeUV compat pre).result).take cursor).length≤
      ell*(fw.length*p)+ell*(new.length*q) := by
  rw [leaf_payload_width,List.length_take,leaf_payload_width]
  exact Nat.add_le_add_left (Nat.min_le_right _ _) _

/-- Unconditional width of the implemented count, even before its
numeric non-overflow assumptions are supplied. -/
theorem raw_count_word_fixed_width (q : ℕ) (key : List Bool) (path : List (List Bool)) :
    (A1R9.countWord q key path).result.length=q := by
  induction path with
  | nil => simp [A1R9.countWord]
  | cons t ts ih =>
    simp only [A1R9.countWord]
    split
    · exact (addBits_exact (A1R9.countWord q key ts).result (encodeBits q 1)
        (ih.trans (encodeBits_length _ _).symm)).1.trans ih
    · exact ih

/-- An actual counter unwind, including the tail word, the width-q
unit read and the newly returned count; plus the raw equality zip of
the precise two compared keys. -/
theorem actual_counter_unwind_words
    (q : ℕ) (key x : List Bool) (tail : List (List Bool)) :
    let pc := A1R9.countWord q key tail
    let now := A1R9.countWord q key (x::tail)
    let unit := encodeBits q 1
    ((key.zip x).flatMap (fun ab=>[ab.1,ab.2])).length+
      pc.result.length+unit.length+now.result.length≤2*key.length+3*q := by
  change ((key.zip x).flatMap (fun ab=>[ab.1,ab.2])).length+
    (A1R9.countWord q key tail).result.length+(encodeBits q 1).length+
      (A1R9.countWord q key (x::tail)).result.length≤_
  rw [flatWidth _ _ 2 (fun _ _=>rfl),List.length_zip,raw_count_word_fixed_width,
    encodeBits_length,raw_count_word_fixed_width]
  have ht := Nat.mul_le_mul_right 2 (Nat.min_le_left key.length x.length)
  omega

#print axioms packet_source_product_holds_actual_factors
#print axioms live_power_uses_only_actual_earlier_bases_and_one_return
#print axioms packet_word_resize_keeps_a_real_old_operand_and_return
#print axioms raw_count_word_fixed_width
#print axioms actual_counter_unwind_words
end J6R68.LeafPeak.Packet
