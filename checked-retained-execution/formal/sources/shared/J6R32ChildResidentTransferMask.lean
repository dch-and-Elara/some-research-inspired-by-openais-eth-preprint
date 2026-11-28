import J6R31RootResidentTablesRoster
import J6R31RootResidentTablesGeometry
import J6R27OriginalGateMaskBank
import J6R24LegalLayoutMaskTape

/-! A deterministic legal descendant convention: at a hot coordinate use
the *page's* own selector as its mask. It need not be zero. The writer
computes the flags from the actual ordered page headers and copy span. -/
namespace J6R32ChildResidentTransfer
open scoped Classical
open AOracleMachineTime AOracleMachineTimeTape AOracleMachineTimeLocal
open P11FullPacking J6R15ModeCost J6R17ModeTape J6R27OriginalGate
open J6R30GeneratedRootLayout J6R14LayoutCost J6R24LegalLayout J6R31RootResidentTables J6R12CollisionEdges
set_option maxHeartbeats 12000000
set_option maxRecDepth 2100

def childMask (a b : ℕ) : MaskFamily a b (Fin 64) := fun _ p=>p.2

theorem child_mask_bit_at_ordered_page {a b : ℕ} (c : CellType a) (j : Fin b) (i : Fin a) :
    selectedMaskBit (childMask a b) ((orderedPage a b).symm (c,j)) i =
      decide ((c i).2<(c i).1) := by
  have hPage : (orderedPage a b).symm (c,j)=⟨key c,(j,orientation c)⟩ := by
    apply (orderedPage a b).injective
    rw [Equiv.apply_symm_apply]
    change (c,j)=(cell (key c) (orientation c),j)
    rw [cell_decode]
  rw [hPage]
  change (if h : ((key c).val i).1≠((key c).val i).2 then orientation c ⟨i,h⟩ else false)=_
  by_cases h : ((key c).val i).1≠((key c).val i).2
  · rw [dif_pos h]
    rfl
  · rw [dif_neg h]
    have he : (c i).1=(c i).2 := not_ne_iff.mp (fun hc=>h ((sorted_hot _ _).mp hc))
    rw [he]
    simp

theorem descendant_mask_need_not_be_zero (j : Fin 1) :
    selectedMaskBit (childMask 1 1)
      ((orderedPage 1 1).symm ((fun _ => ((1:Fin 64),0)),j)) 0=true := by
  rw [child_mask_bit_at_ordered_page]
  decide

noncomputable def orderedChildPages (a b : ℕ) : List (Page a b (Fin 64)) :=
  ((typedCells a).product (List.finRange b)).map (orderedPage a b).symm

theorem child_pages_complete (a b : ℕ) :
    (orderedChildPages a b).Nodup ∧ (∀ p,p∈orderedChildPages a b) ∧
      (orderedChildPages a b).length=(2^(6*a)*2^(6*a))*b := by
  obtain ⟨nd,all,key⟩ := typed_cells_exact a
  unfold orderedChildPages
  refine ⟨(nd.product (List.nodup_finRange _)).map (orderedPage _ _).symm.injective,?_,?_⟩
  · intro v
    exact List.mem_map.mpr ⟨(orderedPage _ _) v,List.mem_product.mpr ⟨all _,List.mem_finRange _⟩,
      (orderedPage _ _).symm_apply_apply v⟩
  · have h := congrArg List.length key
    rw [List.length_map,allPairs_len] at h
    rw [List.length_map]
    change ((typedCells a) ×ˢ List.finRange b).length=(2^(6*a)*2^(6*a))*b
    rw [List.length_product,h,List.length_finRange]

def maskRowSpec {q : ℕ} (h : ExportBox) (cp : Word q) : MaskRow q :=
  ⟨⟨h.key,cp⟩,h.flags.map Prod.snd⟩

def issueChildMask {q : ℕ} (h : ExportBox) (cp : Word q) : Meter (MaskRow q) :=
  let l := appendBits h.key.1 []
  let r := appendBits h.key.2 []
  let p := copyFixed cp
  let f := mapMeter (fun x : Bool×Bool=>⟨x.2,2⟩) h.flags
  ⟨⟨⟨(l.result,r.result),p.result⟩,f.result⟩,l.steps+r.steps+p.steps+f.steps+11⟩

def childMaskIssueFee (a q : ℕ) := 56*a+3*q+16

theorem issue_child_mask_exact {q a : ℕ} (c : CellType a) (cp : Word q) :
    (issueChildMask (headerBox c) cp).result=maskRowSpec (headerBox c) cp ∧
      (issueChildMask (headerBox c) cp).steps≤childMaskIssueFee a q := by
  obtain ⟨m,n⟩ := mapMeter_exact (fun x : Bool×Bool=>⟨x.2,2⟩) Prod.snd 2
    (marksOf c) (fun _ _=>⟨rfl,le_rfl⟩)
  rw [marksOf_len] at n
  have l : (wordCell c).1.length=6*a := by simp only [wordCell,coordinateLabel_len]
  have r : (wordCell c).2.length=6*a := by simp only [wordCell,coordinateLabel_len]
  unfold issueChildMask maskRowSpec headerBox
  simp only [append_bits_exact,List.append_nil,copy_fixed_exact,m]
  exact ⟨True.intro,by unfold childMaskIssueFee; omega⟩

theorem mask_word_is_typed {q a b : ℕ} (c : CellType a) (j : Fin b) :
    maskRowSpec (headerBox c) (word (q:=q) j.val)=
      encodeMaskRow (childMask a b) ((orderedPage a b).symm (c,j)) := by
  unfold maskRowSpec encodeMaskRow pageRef headerBox
  simp only [Equiv.apply_symm_apply]
  congr 1
  simp only [marksOf,List.map_ofFn]
  exact congrArg List.ofFn (funext fun i=>(child_mask_bit_at_ordered_page c j i).symm)

def childMaskSlice {q : ℕ} (words : List (Word q)) (h : ExportBox) : Meter (List (MaskRow q)) :=
  mapMeter (issueChildMask h) words

def writeChildMaskBank {q : ℕ} (hq : 0<q) (a : ℕ) (copies : Word q) : Meter (List (MaskRow q)) :=
  let keys := makeHeaders a
  let c := wordSpan hq copies
  let b := flatMeter (childMaskIssueFee a q) (childMaskSlice c.result) keys.result
  ⟨b.result,keys.steps+c.steps+b.steps+4⟩

def childMaskBankFee (a q b : ℕ) :=
  headerBankFee a + spanFee q b + (2^(6*a)*2^(6*a))*((2*childMaskIssueFee a q+6)*b+8)+4

theorem child_mask_bank_exact {q b : ℕ} (hq : 0<q) (a : ℕ) (copies : Word q) (count : copies.val=b) :
    let O := writeChildMaskBank hq a copies
    O.result=(orderedChildPages a b).map (encodeMaskRow (childMask a b)) ∧
      O.result.length=(2^(6*a)*2^(6*a))*b ∧ O.steps≤childMaskBankFee a q b := by
  let H := makeHeaders a
  let Q := wordSpan hq copies
  obtain ⟨HR,HC⟩ := header_bank_exact a
  obtain ⟨QL,QC⟩ := wordSpan_exact hq copies
  change H.result=_ at HR
  change H.steps≤_ at HC
  change Q.result=_ at QL
  change Q.steps=_ at QC
  rw [count,range_words] at QL
  have qLen : Q.result.length=b := by rw [QL,List.length_map,List.length_finRange]
  have hLen : H.result.length=2^(6*a)*2^(6*a) := (actual_header_fields a).2.2
  let B := flatMeter (childMaskIssueFee a q) (childMaskSlice Q.result) H.result
  have sh (x : ExportBox) (hs : x∈H.result) :
      (childMaskSlice Q.result x).result=Q.result.map (maskRowSpec x) ∧
        (childMaskSlice Q.result x).steps≤(childMaskIssueFee a q+6)*b ∧
        (Q.result.map (maskRowSpec x)).length=b := by
    rw [HR,List.mem_map] at hs
    obtain ⟨c,_,rfl⟩ := hs
    obtain ⟨ex,cap⟩ := mapMeter_exact (issueChildMask (headerBox c)) (maskRowSpec (headerBox c))
      (childMaskIssueFee a q) Q.result (fun p _=>issue_child_mask_exact c p)
    rw [qLen] at cap
    exact ⟨ex,cap,by rw [List.length_map,qLen]⟩
  obtain ⟨BO,BL,BC⟩ := flatMeter_exact (childMaskIssueFee a q)
    ((childMaskIssueFee a q+6)*b) b (childMaskSlice Q.result)
    (fun k=>Q.result.map (maskRowSpec k)) H.result sh
  change B.result=_ at BO
  change B.result.length=_ at BL
  change B.steps≤_ at BC
  rw [hLen] at BL BC
  have EM : B.result=(orderedChildPages a b).map (encodeMaskRow (childMask a b)) := by
    rw [BO,HR,QL]
    unfold orderedChildPages
    simp only [List.flatMap_map,List.map_map,List.product,List.map_flatMap]
    apply congrArg (fun f : CellType a→List (MaskRow q)=>(typedCells a).flatMap f)
    funext c
    apply List.map_congr_left
    intro j _
    exact mask_word_is_typed c j
  change B.result=_ ∧ B.result.length=_ ∧ H.steps+Q.steps+B.steps+4≤_
  refine ⟨EM,BL,?_⟩
  have N : (childMaskIssueFee a q+6)*b+childMaskIssueFee a q*b+8=
      (2*childMaskIssueFee a q+6)*b+8 := by ring
  rw [N] at BC
  rw [count] at QC
  unfold childMaskBankFee
  omega

#print axioms child_mask_bit_at_ordered_page
#print axioms descendant_mask_need_not_be_zero
#print axioms child_pages_complete
#print axioms issue_child_mask_exact
#print axioms mask_word_is_typed
#print axioms child_mask_bank_exact
end J6R32ChildResidentTransfer