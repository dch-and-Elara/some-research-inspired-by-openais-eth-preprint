import J6R17ModeTapeCodec
import J6R16ModeCostTotals

/-! The actual producer. Inputs are already serialized layout and
the legal center precision. The weight list is produced from those
inputs, not supplied. The output simultaneously retains the physical
descriptor order for pairing with emitted exponent vectors. -/
namespace J6R17ModeTape
open AOracleMachineTime AOracleMachineTimeTape AOracleMachineTimeLocal
open J6R15ModeCost J6R14LayoutCost P11FullPacking J6R12CollisionEdges

structure RawTape (q : ℕ) where
  modes : List (RawMode q)
  weights : List (Word q)
  precision : Word q

def weighTape {q : ℕ} (a : ℕ) (ms : List (RawMode q)) : Meter (List (Word q)) :=
  mapMeter (fun m=>⟨m.weight,recordStride a q⟩) ms

theorem weighTape_exact {q : ℕ} (a : ℕ) (ms : List (RawMode q)) :
    (weighTape a ms).result=ms.map RawMode.weight ∧
      (weighTape a ms).steps≤(recordStride a q+6)*ms.length :=
  mapMeter_exact _ RawMode.weight (recordStride a q) ms (fun _ _=>⟨rfl,le_rfl⟩)

def buildTape {q : ℕ} (hq : 0<q) (a i rowWidth : ℕ) (xs : List ExportBox)
    (pages precision : Word q) : Meter (RawTape q) :=
  let h := extractHeaders rowWidth a xs
  let k := keptKeys a i h.result
  let b := wordSpan hq pages
  let u := tileBound q i
  let t := wordSpan hq u.result
  let w := positiveSpan hq precision
  let m := keyStage a k.result b.result t.result w.result
  let v := weighTape a m.result
  ⟨⟨m.result,v.result,precision⟩,
    h.steps+k.steps+b.steps+u.steps+t.steps+w.steps+m.steps+v.steps+8*q+24⟩

def buildCap (a q hd rows traffic pages tiles p : ℕ) : ℕ :=
  hd*(headerTraffic a+(32*a+16))+rows*traffic+
    spanFee q pages+spanFee q tiles+spanFee q p+
    keyCap a q hd pages tiles (p-1)+
    (recordStride a q+6)*(hd*(pages*(tiles*(p-1))))+12*q+36

theorem buildCap_mono (a q : ℕ) {hd rows traffic pages tiles p H R U B T P : ℕ}
    (hH : hd≤H) (hR : rows≤R) (hU : traffic≤U) (hB : pages≤B)
    (hT : tiles≤T) (hP : p≤P) :
    buildCap a q hd rows traffic pages tiles p≤buildCap a q H R U B T P := by
  have hk := keyCap_mono a q hH hB hT (Nat.sub_le_sub_right hP 1)
  unfold buildCap spanFee
  gcongr

theorem buildTape_exact {q a pages p : ℕ} (hq : 0<q) (i : Fin a) (hi : i.val+1<q)
    (traffic : ℕ) (xs : List ExportBox) (cs : List (Ordered a))
    (hc : xs.map headerOf=cs.map encodeHeader) (hn : cs.Nodup) (hall : ∀ c,c∈cs)
    (b pre : Word q) (hB : b.val=pages) (hP : pre.val=p) (hp : 0<p) :
    let z := buildTape hq a i.val traffic xs b pre
    ∃ ms : List (PacketMode i pages (2^(i.val+1)) p),
      ms.Nodup ∧ (∀ m,m∈ms) ∧ z.result.modes=ms.map (encodeMode i) ∧
      z.result.modes.Nodup ∧
      z.result.weights.map Word.val=ms.map modeWeight ∧ z.result.precision.val=p ∧
      z.steps≤buildCap a q xs.length (exportRows xs) traffic pages (2^(i.val+1)) p := by
  let h := extractHeaders traffic a xs
  let k := keptKeys a i.val h.result
  let n := wordSpan hq b
  let u := tileBound q i.val
  let t := wordSpan hq u.result
  let w := positiveSpan hq pre
  let m := keyStage a k.result n.result t.result w.result
  let v := weighTape a m.result
  let tiles := 2^(i.val+1)
  let ms := physicalRoster i cs pages tiles p
  obtain ⟨hh,htH⟩ := extractHeaders_exact traffic a xs
  change h.result=_ at hh
  change h.steps=_ at htH
  rw [hc] at hh
  obtain ⟨hk,htK⟩ := keptKeys_exact i cs
  have hk' : k.result=(cs.filter (crossingSpec i)).map wordCell := by
    unfold k
    rw [hh]
    exact hk
  have hK : k.steps≤(32*a+16)*cs.length := by
    unfold k
    rw [hh]
    exact htK
  have hL : cs.length=xs.length := by
    have R := congrArg List.length hc.symm
    rwa [List.length_map,List.length_map] at R
  rw [hL] at hK
  have hKs : k.result.length≤xs.length := by
    rw [hk',List.length_map,← hL]
    exact List.length_filter_le _ _
  obtain ⟨hN,htN⟩ := wordSpan_exact hq b
  change n.result=_ at hN
  change n.steps=_ at htN
  rw [hB] at hN htN
  obtain ⟨hU,htU⟩ := tileBound_exact q i.val hi
  change u.result.val=tiles at hU
  change u.steps=_ at htU
  obtain ⟨hT,htT⟩ := wordSpan_exact hq u.result
  change t.result=_ at hT
  change t.steps=_ at htT
  rw [hU] at hT htT
  obtain ⟨hW,htW⟩ := positiveSpan_exact hq pre (hP.symm ▸ hp)
  change w.result=_ at hW
  change w.steps=_ at htW
  rw [hP] at hW htW
  have hnb : n.result.length=pages := by rw [hN,List.length_map,List.length_range']
  have hnt : t.result.length=tiles := by rw [hT,List.length_map,List.length_range']
  have hnw : w.result.length=p-1 := by rw [hW,List.length_map,List.length_range']
  obtain ⟨hm,hmL,htM⟩ := keyStage_exact a k.result n.result t.result w.result
  change m.result=_ at hm
  change m.result.length=_ at hmL
  change m.steps≤_ at htM
  rw [hk',hN,hT,hW,encode_rawJoin] at hm
  have hLen : m.result.length≤xs.length*(pages*(tiles*(p-1))) := by
    rw [hmL,hnb,hnt,hnw]
    exact Nat.mul_le_mul_right _ hKs
  rw [hnb,hnt,hnw] at htM
  have htM' := htM.trans (keyCap_mono a q hKs le_rfl le_rfl le_rfl)
  obtain ⟨hhW,htV⟩ := weighTape_exact a m.result
  change v.result=_ at hhW
  change v.steps≤_ at htV
  have htV' := htV.trans (Nat.mul_le_mul_left _ hLen)
  have hFitP : p<2^q := hP ▸ val_lt pre
  have hFitB : pages<2^q := hB ▸ val_lt b
  have hFitT : tiles<2^q := hU ▸ val_lt u.result
  obtain ⟨hD,hA⟩ := physicalRoster_complete i cs pages tiles p hn hall
  refine ⟨ms,hD,hA,hm,?_,?_,hP,?_⟩
  · change m.result.Nodup
    rw [hm]
    exact hD.map (encodeMode_inj i hFitB hFitT hFitP)
  · change v.result.map Word.val=ms.map modeWeight
    rw [hhW,hm,List.map_map,List.map_map]
    exact List.map_congr_left (fun x _=>encoded_weight i hFitP x)
  · change h.steps+k.steps+n.steps+u.steps+t.steps+w.steps+m.steps+v.steps+8*q+24 ≤
      buildCap a q xs.length (exportRows xs) traffic pages tiles p
    rw [htH,htN,htU,htT,htW,buildCap,Nat.mul_add,Nat.mul_comm xs.length (32*a+16)]
    omega

#print axioms weighTape_exact
#print axioms buildCap_mono
#print axioms buildTape_exact
end J6R17ModeTape


