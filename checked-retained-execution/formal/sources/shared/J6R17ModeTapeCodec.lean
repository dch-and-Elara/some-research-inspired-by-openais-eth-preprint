import J6R17ModeTapeCross
import Mathlib.Data.List.FinRange

/-! The typed, proof-side correspondence for emitted addresses. The
per-packet selector is not discarded: the P11 cell chart represents it
by the ordered key word, with its padded copy number separate. -/
namespace J6R17ModeTape
open P11FullPacking J6R14LayoutCost J6R15ModeCost

abbrev Ordered (a : ℕ) := Cell (Fin a) (Fin 64)
abbrev HotCell {a : ℕ} (i : Fin a) := {c : Ordered a // (c i).1≠(c i).2}

noncomputable def orderedPage (a pages : ℕ) : Page a pages (Fin 64) ≃ Ordered a×Fin pages :=
  (Equiv.sigmaCongrRight fun k : Key (Fin a) (Fin 64) => Equiv.prodComm (Fin pages) (Orient k)).trans
    ((Equiv.sigmaProdDistrib (fun k : Key (Fin a) (Fin 64) => Orient k) (Fin pages)).symm.trans
      (Equiv.prodCongr cellChart (Equiv.refl _)))

theorem ordered_page_hot {a pages : ℕ} (i : Fin a) (t : Page a pages (Fin 64)) :
    ((orderedPage a pages t).1 i).1≠((orderedPage a pages t).1 i).2 ↔
      (t.1.val i).1≠(t.1.val i).2 := by
  change (cell t.1 t.2.2 i).1≠(cell t.1 t.2.2 i).2 ↔ _
  unfold cell
  by_cases h : (t.1.val i).1≠(t.1.val i).2
  · simp only [dif_pos h]
    cases t.2.2 ⟨i,h⟩ <;> simp [h,ne_comm]
  · simp [h]

noncomputable def crossingOrdered {a : ℕ} (i : Fin a) (pages : ℕ) :
    Crossing (G:=Fin 64) (pages:=pages) i ≃ HotCell i×Fin pages where
  toFun t := (⟨(orderedPage a pages t.val).1,(ordered_page_hot i t.val).mpr t.property⟩,
    (orderedPage a pages t.val).2)
  invFun v := ⟨(orderedPage a pages).symm (v.1.val,v.2),
    (ordered_page_hot i _).mp (by rw [(orderedPage a pages).apply_symm_apply]; exact v.1.property)⟩
  left_inv t := Subtype.ext ((orderedPage a pages).symm_apply_apply t.val)
  right_inv v := by
    have h := (orderedPage a pages).apply_symm_apply (v.1.val,v.2)
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst h
    · change ((orderedPage a pages) ((orderedPage a pages).symm (v.1.val,v.2))).2=v.2
      exact congrArg Prod.snd h

abbrev PacketMode {a : ℕ} (i : Fin a) (pages tiles p : ℕ) :=
  Mode (Crossing (G:=Fin 64) (pages:=pages) i) tiles p

noncomputable def orderedMode {a : ℕ} (i : Fin a) (pages tiles p : ℕ) :
    PacketMode i pages tiles p ≃ HotCell i×Fin pages×Fin tiles×Fin (p-1) :=
  (Equiv.prodCongr (crossingOrdered i pages) (Equiv.refl _)).trans (Equiv.prodAssoc _ _ _)

def hotList {a : ℕ} (i : Fin a) (cs : List (Ordered a)) : List (HotCell i) :=
  cs.filterMap (fun c => if h : (c i).1≠(c i).2 then some ⟨c,h⟩ else none)

theorem hotList_val {a : ℕ} (i : Fin a) (cs : List (Ordered a)) :
    (hotList i cs).map Subtype.val=cs.filter (crossingSpec i) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    unfold hotList at *
    simp only [List.filterMap_cons]
    by_cases h : (c i).1≠(c i).2
    · rw [dif_pos h]
      simp only [List.map_cons,ih,List.filter_cons,crossingSpec,decide_eq_true h,if_true]
    · rw [dif_neg h]
      rw [ih,List.filter_cons]
      simp [crossingSpec,h]

theorem hotList_nodup {a : ℕ} (i : Fin a) {cs : List (Ordered a)} (h : cs.Nodup) :
    (hotList i cs).Nodup := by
  apply List.Nodup.of_map Subtype.val
  rw [hotList_val]
  exact h.filter _

theorem hotList_cover {a : ℕ} (i : Fin a) {cs : List (Ordered a)} (h : ∀ c,c∈cs)
    (c : HotCell i) : c∈hotList i cs := by
  apply List.mem_filterMap.mpr
  exact ⟨c.val,h _,dif_pos c.property⟩

noncomputable def encodeMode {q a pages tiles p : ℕ} (i : Fin a) (m : PacketMode i pages tiles p) :
    RawMode q :=
  let z := orderedMode i pages tiles p m
  ⟨wordCell z.1.val,word z.2.1.val,word z.2.2.1.val,word (z.2.2.2.val+1)⟩

theorem encoded_weight {q a pages tiles p : ℕ} (i : Fin a) (hp : p<2^q)
    (m : PacketMode i pages tiles p) :
    (encodeMode (q:=q) i m).weight.val=modeWeight m :=
  word_val ((modeWeight_bounds m).2.trans hp)

theorem encodeMode_inj {q a pages tiles p : ℕ} (i : Fin a)
    (hP : pages<2^q) (hT : tiles<2^q) (hp : p<2^q) :
    Function.Injective (encodeMode (q:=q) (pages:=pages) (tiles:=tiles) (p:=p) i) := by
  intro x y H
  apply (orderedMode i pages tiles p).injective
  let u := orderedMode i pages tiles p x
  let v := orderedMode i pages tiles p y
  change u=v
  have hA := wordCell_injective a (congrArg RawMode.key H)
  have hB := congrArg (fun z : RawMode q => z.page.val) H
  have hC := congrArg (fun z : RawMode q => z.tile.val) H
  have hW := congrArg (fun z : RawMode q => z.weight.val) H
  change (word u.2.1.val : Word q).val=(word v.2.1.val : Word q).val at hB
  change (word u.2.2.1.val : Word q).val=(word v.2.2.1.val : Word q).val at hC
  change (word (u.2.2.2.val+1) : Word q).val=(word (v.2.2.2.val+1) : Word q).val at hW
  have hu : u.2.2.2.val+1<p := by have := u.2.2.2.isLt; omega
  have hv : v.2.2.2.val+1<p := by have := v.2.2.2.isLt; omega
  rw [word_val (u.2.1.isLt.trans hP),word_val (v.2.1.isLt.trans hP)] at hB
  rw [word_val (u.2.2.1.isLt.trans hT),word_val (v.2.2.1.isLt.trans hT)] at hC
  rw [word_val (hu.trans hp),word_val (hv.trans hp)] at hW
  exact Prod.ext (Subtype.ext hA)
    (Prod.ext (Fin.ext hB) (Prod.ext (Fin.ext hC) (Fin.ext (Nat.succ.inj hW))))

noncomputable def physicalRoster {a : ℕ} (i : Fin a) (cs : List (Ordered a))
    (pages tiles p : ℕ) : List (PacketMode i pages tiles p) :=
  ((hotList i cs) ×ˢ ((List.finRange pages) ×ˢ ((List.finRange tiles) ×ˢ
    (List.finRange (p-1))))).map (orderedMode i pages tiles p).symm

theorem physicalRoster_complete {a : ℕ} (i : Fin a) (cs : List (Ordered a))
    (pages tiles p : ℕ) (hn : cs.Nodup) (hAll : ∀ c,c∈cs) :
    (physicalRoster i cs pages tiles p).Nodup ∧ ∀ x,x∈physicalRoster i cs pages tiles p := by
  refine ⟨((hotList_nodup i hn).product ((List.nodup_finRange pages).product
    ((List.nodup_finRange tiles).product (List.nodup_finRange (p-1))))).map
      (orderedMode i pages tiles p).symm.injective,?_⟩
  intro x
  unfold physicalRoster
  let t := orderedMode i pages tiles p x
  have H : t ∈ hotList i cs ×ˢ (List.finRange pages ×ˢ (List.finRange tiles ×ˢ List.finRange (p-1))) := by
    rcases t with ⟨c,y,z,w⟩
    exact List.mem_product.mpr ⟨hotList_cover i hAll c,List.mem_product.mpr ⟨List.mem_finRange y,
      List.mem_product.mpr ⟨List.mem_finRange z,List.mem_finRange w⟩⟩⟩
  exact List.mem_map.mpr ⟨t,H,(orderedMode i pages tiles p).symm_apply_apply x⟩

theorem rawJoin_map {q : ℕ} {A B D W : Type*} (ks : List A) (ps : List B)
    (ts : List D) (ws : List W) (K : A→CellWord) (P : B→Word q)
    (T : D→Word q) (R : W→Word q) :
    rawJoin (ks.map K) (ps.map P) (ts.map T) (ws.map R)=
      (ks ×ˢ (ps ×ˢ (ts ×ˢ ws))).map
        (fun z=>⟨K z.1,P z.2.1,T z.2.2.1,R z.2.2.2⟩) := by
  simp only [rawJoin,SProd.sprod,List.product,List.flatMap_map,List.map_flatMap,
    List.map_map,Function.comp_def]

theorem range_words {q : ℕ} (n : ℕ) :
    (List.range' 0 n).map (word (q:=q))=(List.finRange n).map (fun k=>word k.val) := by
  rw [← List.range_eq_range',← List.map_coe_finRange,List.map_map]
  rfl

theorem positive_words {q : ℕ} (n : ℕ) :
    (List.range' 1 n).map (word (q:=q))=(List.finRange n).map (fun k=>word (k.val+1)) := by
  rw [List.range'_eq_map_range,← List.map_coe_finRange,List.map_map,List.map_map]
  simp only [Function.comp_def,Nat.add_comm 1]

theorem encode_rawJoin {q a : ℕ} (i : Fin a) (cs : List (Ordered a)) (pages tiles p : ℕ) :
    rawJoin (q:=q) ((cs.filter (crossingSpec i)).map wordCell) ((List.range' 0 pages).map word)
      ((List.range' 0 tiles).map word) ((List.range' 1 (p-1)).map word)=
        (physicalRoster i cs pages tiles p).map (encodeMode i) := by
  rw [← hotList_val,List.map_map,range_words,range_words,positive_words,rawJoin_map,
    physicalRoster,List.map_map]
  apply List.map_congr_left
  intro z _
  change RawMode.mk _ _ _ _=encodeMode i ((orderedMode i pages tiles p).symm z)
  simp only [encodeMode,Equiv.apply_symm_apply,Function.comp_def]

#print axioms ordered_page_hot
#print axioms crossingOrdered
#print axioms encodeMode_inj
#print axioms physicalRoster_complete
#print axioms encode_rawJoin
end J6R17ModeTape


