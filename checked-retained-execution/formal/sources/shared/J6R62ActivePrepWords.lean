import J6R50SourceProducerReplay

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 7500000
set_option maxRecDepth 1900
set_option Elab.async false

/-! Native mode weight compilation before any outgoing address.  This
uses the same canonical all-cell scratch headers as actual R50 replay;
only the exact physical copy and receiving precision words are needed.
Their bit copies, all scratch headers, and the R17 roster scan are
charged explicitly.  This is not a compiler for the chosen packing. -/
namespace J6R62ActivePrep
open AOracleMachineTime J6R15ModeCost J6R17ModeTape
open J6R14LayoutCost J6R21Ancestor J6R24LegalLayout J6R27OriginalGate
open J6R31RootResidentTables J6R32ChildResidentTransfer J6R50SourceProducer
open J6R12CollisionEdges

def canonicalRaw {q : ℕ} (hq : 0<q) (a i : ℕ)
    (copies precision : Word q) : Meter (RawTape q) :=
  let H := makeHeaders a
  let C := copyFixed copies
  let P := copyFixed precision
  let R := buildTape hq a i 0 H.result C.result P.result
  ⟨R.result,H.steps+C.steps+P.steps+R.steps+4⟩

def canonicalCap (a q i b p : ℕ) : ℕ :=
  headerBankFee a+2*(3*q+1)+
    buildCap a q (2^(6*a)*2^(6*a)) 0 0 b (2^(i+1)) p+4

theorem actual_replay_raw_tape {a q : ℕ} (i : Fin a)
    (cp pr : Word (q+1)) (masks : List (MaskRow (q+1)))
    (seats : List (SeatField a ((q-a)+13*a))) :
    (canonicalRaw (Nat.succ_pos q) a i.val cp pr).result=
      (replaySelected a q i.val cp pr masks seats).result.raw.roster := rfl

theorem canonical_raw_mode_order {a q b p : ℕ}
    (hq : 0<q) (i : Fin a) (hi : i.val+1<q) (cp pr : Word q)
    (hc : cp.val=b) (hp : pr.val=p) (pos : 0<p) :
    (canonicalRaw hq a i.val cp pr).result.modes =
      (physicalRoster i (typedCells a) b (2^(i.val+1)) p).map (encodeMode i) := by
  let H := (makeHeaders a).result
  let hdr := extractHeaders 0 a H
  let keys := keptKeys a i.val hdr.result
  let B := wordSpan hq cp
  let U := tileBound q i.val
  let S := wordSpan hq U.result
  let W := positiveSpan hq pr
  have hH : hdr.result=(typedCells a).map encodeHeader :=
    (extractHeaders_exact 0 a H).1.trans (actual_header_fields a).1
  have key : keys.result=((typedCells a).filter (crossingSpec i)).map wordCell := by
    unfold keys
    rw [hH]
    exact (keptKeys_exact i (typedCells a)).1
  have bR : B.result=(List.range' 0 b).map (word (q:=q)) := by
    simpa only [B,hc] using (wordSpan_exact hq cp).1
  have sR : S.result=(List.range' 0 (2^(i.val+1))).map (word (q:=q)) := by
    simpa only [S,U,(tileBound_exact q i.val hi).1] using (wordSpan_exact hq U.result).1
  have wR : W.result=(List.range' 1 (p-1)).map (word (q:=q)) := by
    simpa only [W,hp] using (positiveSpan_exact hq pr (hp.symm ▸ pos)).1
  have raw := (keyStage_exact a keys.result B.result S.result W.result).1
  simp only [canonicalRaw,copy_fixed_exact,buildTape]
  change (keyStage a keys.result B.result S.result W.result).result=_
  rw [raw,key,bR,sR,wR]
  exact encode_rawJoin i (typedCells a) b (2^(i.val+1)) p

theorem canonical_raw_weights {a q b p : ℕ}
    (hq : 0<q) (i : Fin a) (hi : i.val+1<q) (cp pr : Word q)
    (hc : cp.val=b) (hp : pr.val=p) (pos : 0<p) :
    let z := canonicalRaw hq a i.val cp pr
    z.result.weights.map Word.val =
      (physicalRoster i (typedCells a) b (2^(i.val+1)) p).map modeWeight ∧
      z.result.precision=pr := by
  let z := canonicalRaw hq a i.val cp pr
  have weights : z.result.weights=z.result.modes.map RawMode.weight := by
    simp only [z,canonicalRaw,copy_fixed_exact,buildTape]
    apply (weighTape_exact a _).1
  refine ⟨?_,by simp only [canonicalRaw,copy_fixed_exact,buildTape]⟩
  have fits : p<2^q := hp ▸ val_lt pr
  change z.result.weights.map Word.val=_
  rw [weights,canonical_raw_mode_order hq i hi cp pr hc hp pos,List.map_map,List.map_map]
  apply List.map_congr_left
  intro m _
  exact encoded_weight i fits m

theorem canonical_raw_bound {a q b p : ℕ}
    (hq : 0<q) (i : Fin a) (hi : i.val+1<q) (cp pr : Word q)
    (hc : cp.val=b) (hp : pr.val=p) (pos : 0<p) :
    (canonicalRaw hq a i.val cp pr).steps≤canonicalCap a q i.val b p := by
  let H := makeHeaders a
  obtain ⟨headers,rows,card⟩ := actual_header_fields a
  obtain ⟨_,_,_,_,_,_,_,bound⟩ := buildTape_exact hq i hi 0 H.result (typedCells a) headers
    (typed_cells_exact a).1 (typed_cells_exact a).2.1 cp pr hc hp pos
  rw [rows,card] at bound
  have h := (header_bank_exact a).2
  change H.steps≤headerBankFee a at h
  simp only [canonicalRaw,copy_fixed_exact,canonicalCap]
  change H.steps+(3*q+1)+(3*q+1)+(buildTape hq a i.val 0 H.result cp pr).steps+4≤_
  omega

#print axioms actual_replay_raw_tape
#print axioms canonical_raw_mode_order
#print axioms canonical_raw_weights
#print axioms canonical_raw_bound
end J6R62ActivePrep

