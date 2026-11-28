
import J6R30GeneratedRootLayoutReceipt
import J6R27OriginalGateMaskBank

/-! The mask bank has a record at every true ordered page, including
all orientations and padded copies. The all-zero flags are legitimate
only for the deterministic stable root. A slot's ordered cell is not
used as though it were this packet page's ordered key. -/
namespace J6R31RootResidentTables
open scoped Classical
open AOracleMachineTime AOracleMachineTimeLocal AOracleMachineTimeTape
open J6R30GeneratedRootLayout J6R24LegalLayout J6R14LayoutCost
open J6Mesh P11FullPacking J6R15ModeCost J6R17ModeTape J6R27OriginalGate J6R12CollisionEdges
set_option maxRecDepth 1900
set_option maxHeartbeats 11500000

abbrev zeroMask (a b : ℕ) : MaskFamily a b (Fin 64) := fun _ _ _=>false

theorem selected_zero {a b : ℕ} (p : Page a b (Fin 64)) (i : Fin a) :
    selectedMaskBit (zeroMask a b) p i=false := by
  unfold selectedMaskBit
  split <;> rfl

noncomputable def orderedRootPages (m : ℕ) : List (Page (a m) (K m) (Fin 64)) :=
  ((typedCells (a m)).product (List.finRange (K m))).map (orderedPage (a m) (K m)).symm

theorem all_root_pages (m : ℕ) :
    (orderedRootPages m).Nodup ∧ (∀ p,p∈orderedRootPages m) ∧
      (orderedRootPages m).length=D m*K m := by
  obtain ⟨nd,all,key⟩ := typed_cells_exact (a m)
  unfold orderedRootPages
  refine ⟨(nd.product (List.nodup_finRange _)).map (orderedPage _ _).symm.injective,?_,?_⟩
  · intro v
    exact List.mem_map.mpr ⟨(orderedPage _ _) v,List.mem_product.mpr ⟨all _,List.mem_finRange _⟩,
      (orderedPage _ _).symm_apply_apply v⟩
  · have h := congrArg List.length key
    rw [List.length_map,allPairs_len,printed_menu_identity m] at h
    rw [List.length_map]
    change ((typedCells (a m)) ×ˢ List.finRange (K m)).length=D m*K m
    rw [List.length_product,h,List.length_finRange]

def maskBytes {q : ℕ} (a : ℕ) (ord : CellWord) (cp : Word q) : MaskRow q :=
  ⟨⟨ord,cp⟩,List.replicate a false⟩

def issueMask {q : ℕ} (a : ℕ) (ord : CellWord) (cp : Word q) : Meter (MaskRow q) :=
  let l := appendBits ord.1 []
  let r := appendBits ord.2 []
  let p := copyFixed cp
  ⟨⟨⟨(l.result,r.result),p.result⟩,List.replicate a false⟩,
    l.steps+r.steps+p.steps+3*a+11⟩

def maskIssueFee (a q : ℕ) := 51*a+3*q+16

theorem issue_mask_exact {q : ℕ} (a : ℕ) (k : CellWord) (cp : Word q)
    (h : k.1.length=6*a ∧ k.2.length=6*a) :
    issueMask a k cp=⟨maskBytes a k cp,maskIssueFee a q⟩ := by
  unfold issueMask maskBytes maskIssueFee
  simp only [append_bits_exact,List.append_nil,copy_fixed_exact,h.1,h.2]
  congr 1
  omega

theorem mask_row_is_typed {q a b : ℕ} (c : CellType a) (j : Fin b) :
    maskBytes a (wordCell c) (word (q:=q) j.val)=
      encodeMaskRow (zeroMask a b) ((orderedPage a b).symm (c,j)) := by
  unfold maskBytes encodeMaskRow pageRef
  simp only [Equiv.apply_symm_apply]
  have W : (selectedMaskBit (zeroMask a b) ((orderedPage a b).symm (c,j)))=fun _=>false :=
    funext fun i=>selected_zero _ i
  rw [W,List.ofFn_const]

def maskSlice {q : ℕ} (a : ℕ) (ps : List (Word q)) (k : CellWord) :
    Meter (List (MaskRow q)) :=
  mapMeter (issueMask a k) ps

theorem mask_slice_exact {q : ℕ} (a : ℕ) (ps : List (Word q)) (k : CellWord)
    (h : k.1.length=6*a ∧ k.2.length=6*a) :
    (maskSlice a ps k).result=ps.map (maskBytes a k) ∧
      (maskSlice a ps k).steps≤(maskIssueFee a q+6)*ps.length := by
  exact mapMeter_exact _ _ _ ps (fun x _=>by
    rw [issue_mask_exact a k x h]
    exact ⟨rfl,le_rfl⟩)

def rootMaskBank {q : ℕ} (hq : 0<q) (m : ℕ) (copies : Word q) : Meter (List (MaskRow q)) :=
  let K := allPairsMachine (6*a m)
  let C := wordSpan hq copies
  let B := flatMeter (maskIssueFee (a m) q) (maskSlice (a m) C.result) K.result
  ⟨B.result,K.steps+C.steps+B.steps+4⟩

def maskBankFee (m q : ℕ) :=
  allPairsCap (6*a m)+spanFee q (K m)+D m*((2*maskIssueFee (a m) q+6)*K m+8)+4

theorem root_mask_bank_exact {q : ℕ} (hq : 0<q) (m : ℕ) (copies : Word q) (cp : copies.val=K m) :
    let O := rootMaskBank hq m copies
    O.result=(orderedRootPages m).map (encodeMaskRow (zeroMask (a m) (K m))) ∧
      O.result.length=D m*K m ∧ O.steps≤maskBankFee m q := by
  let R := allPairsMachine (6*a m)
  let Q := wordSpan hq copies
  obtain ⟨RK,RC⟩ := allPairsMachine_exact (6*a m)
  obtain ⟨QL,QC⟩ := wordSpan_exact hq copies
  change R.result=_ at RK
  change R.steps≤_ at RC
  change Q.result=_ at QL
  change Q.steps=_ at QC
  rw [cp,range_words] at QL
  have qLen : Q.result.length=K m := by rw [QL,List.length_map,List.length_finRange]
  have rLen : R.result.length=D m := by rw [RK,allPairs_len,printed_menu_identity m]
  let B := flatMeter (maskIssueFee (a m) q) (maskSlice (a m) Q.result) R.result
  have sh (x) (hs : x∈R.result) :
      (maskSlice (a m) Q.result x).result=Q.result.map (maskBytes (a m) x) ∧
        (maskSlice (a m) Q.result x).steps≤(maskIssueFee (a m) q+6)*K m ∧
        (Q.result.map (maskBytes (a m) x)).length=K m := by
    have ok := (allPairs_mem (6*a m) x).mp (RK ▸ hs)
    obtain ⟨e,b⟩ := mask_slice_exact (a m) Q.result x ok
    rw [qLen] at b
    exact ⟨e,b,by rw [List.length_map,qLen]⟩
  obtain ⟨BO,BL,BC⟩ := flatMeter_exact (maskIssueFee (a m) q)
    ((maskIssueFee (a m) q+6)*K m) (K m) (maskSlice (a m) Q.result)
    (fun k=>Q.result.map (maskBytes (a m) k)) R.result sh
  change B.result=_ at BO
  change B.result.length=_ at BL
  change B.steps≤_ at BC
  rw [rLen] at BL BC
  have EM : B.result=(orderedRootPages m).map (encodeMaskRow (zeroMask (a m) (K m))) := by
    rw [BO,RK,←(typed_cells_exact (a m)).2.2,QL]
    unfold orderedRootPages
    simp only [List.flatMap_map,List.map_map,List.product,List.map_flatMap]
    apply congrArg (fun f : CellType (a m)→List (MaskRow q)=>(typedCells (a m)).flatMap f)
    funext c
    apply List.map_congr_left
    intro j _
    exact mask_row_is_typed c j
  change B.result=_ ∧ B.result.length=_ ∧ R.steps+Q.steps+B.steps+4≤_
  refine ⟨EM,BL,?_⟩
  have N : (maskIssueFee (a m) q+6)*K m+maskIssueFee (a m) q*K m+8=
        (2*maskIssueFee (a m) q+6)*K m+8 := by ring
  rw [N] at BC
  rw [cp] at QC
  unfold maskBankFee
  omega

#print axioms all_root_pages
#print axioms mask_row_is_typed
#print axioms root_mask_bank_exact
end J6R31RootResidentTables
