
import J6R27OriginalGateModeRoster
import J6R21AncestorGather

/-! One immutable per-page mask file suffices for all emitted tuples.
A candidate takes the actual full page key from its R17 mode; the
compiler copies every visited row body, charges comparisons and a
sequential axis read, and computes the per-mode bit. This is not a
supplied list of answers to individual modes. -/
namespace J6R27OriginalGate
open AOracleMachineTime J6R15ModeCost J6R17ModeTape J6R14LayoutCost
open P11FullPacking J6R21Ancestor

structure MaskRow (q : ℕ) where
  address : PageRef q
  bits : List Bool

def scanMask {q : ℕ} (axis : List Bool) (address : PageRef q) :
    List (MaskRow q)→Meter (Option Bool)
  | [] => ⟨none,4⟩
  | row::rest =>
    let p := cmpPage address row.address
    let copy := copyBytes row.bits
    if p.result then
      let read := readSkip axis copy.result
      ⟨some read.result,p.steps+copy.steps+read.steps+10⟩
    else
      let tail := scanMask axis address rest
      ⟨tail.result,p.steps+copy.steps+tail.steps+10⟩

noncomputable def encodeMaskRow {a b q : ℕ} (mask : MaskFamily a b (Fin 64))
    (k : Page a b (Fin 64)) : MaskRow q :=
  ⟨pageRef q k,List.ofFn (selectedMaskBit mask k)⟩

def maskSearchStride (a q : ℕ) := 67*a+10*q+38

theorem mask_bank_nominal {a b q : ℕ} (fit : b≤2^q) (mask : MaskFamily a b (Fin 64))
    (i : Fin a) (axis : List Bool) (clock : axis.length=i.val)
    (page : Page a b (Fin 64)) (pages : List (Page a b (Fin 64))) (has : page∈pages) :
    let out := scanMask axis (pageRef q page) (pages.map (encodeMaskRow (q:=q) mask))
    out.result=some (selectedMaskBit mask page i) ∧
      out.steps≤4+pages.length*maskSearchStride a q := by
  have W1 : (pageRef q page).labels.1.length=6*a := by simp only [pageRef,wordCell,coordinateLabel_len]
  have W2 : (pageRef q page).labels.2.length=6*a := by simp only [pageRef,wordCell,coordinateLabel_len]
  induction pages with
  | nil => simp at has
  | cons row rest ih =>
    let k := pageRef q page
    let D := encodeMaskRow (q:=q) mask row
    let C := cmpPage k D.address
    let B := copyBytes D.bits
    have ok : C.result=true↔page=row :=
      (cmp_page_exact _ _).1.trans ((page_ref_injective fit).eq_iff)
    have fee := (cmp_page_exact k D.address).2
    change C.steps≤5*(pageRef q page).labels.1.length+5*(pageRef q page).labels.2.length+10*q+15 at fee
    rw [W1,W2] at fee
    have tick : axis.length≤a := by rw [clock]; exact i.isLt.le
    have hCopy : B=⟨D.bits,3*a+1⟩ := by
      change copyBytes (List.ofFn (selectedMaskBit mask row))=_
      rw [copyBytes_exact,List.length_ofFn]
      rfl
    change copyBytes (encodeMaskRow (q:=q) mask row).bits=⟨(encodeMaskRow (q:=q) mask row).bits,3*a+1⟩ at hCopy
    by_cases same : page=row
    · dsimp only
      rw [List.map_cons,scanMask]
      dsimp only
      rw [if_pos (ok.mpr same),hCopy]
      let z := readSkip axis (List.ofFn (selectedMaskBit mask row))
      have hR : z.result=selectedMaskBit mask page i := by
        rw [show z.result=_ from (readSkip_exact _ _).1,clock,getD_ofFn_exact,same]
      have hF : z.steps≤4*axis.length+2 := (readSkip_exact _ _).2
      refine ⟨congrArg some hR,?_⟩
      change C.steps+(3*a+1)+z.steps+10≤4+(row::rest).length*maskSearchStride a q
      rw [List.length_cons,Nat.add_mul,Nat.one_mul]
      have nonnegative := Nat.zero_le (rest.length*maskSearchStride a q)
      unfold maskSearchStride
      omega
    · have ht := ih ((List.mem_cons.mp has).resolve_left same)
      dsimp only
      rw [List.map_cons,scanMask]
      dsimp only
      rw [if_neg (fun h=>same (ok.mp h)),hCopy]
      refine ⟨ht.1,?_⟩
      change C.steps+(3*a+1)+(scanMask axis k (rest.map (encodeMaskRow mask))).steps+10≤_
      have hT := ht.2
      change (scanMask axis k (rest.map (encodeMaskRow mask))).steps≤_ at hT
      rw [List.length_cons,Nat.add_mul,Nat.one_mul]
      unfold maskSearchStride at hT ⊢
      omega

def bindModeMasks {q : ℕ} (a : ℕ) (axis : List Bool) (bank : List (MaskRow q)) :
    List (RawMode q)→List (Word q)→Meter (Option (List (ModeCandidate q)))
  | [],[] => ⟨some [],5⟩
  | [],_::_ => ⟨none,5⟩
  | _::_,[] => ⟨none,5⟩
  | m::ms,e::es =>
    let f := scanMask axis (modePage m) bank
    let copy := copyFixed e
    let z := bindModeMasks a axis bank ms es
    ⟨f.result.bind (fun bit=>z.result.map (⟨m,bit,copy.result⟩::·)),
      f.steps+copy.steps+z.steps+recordStride a q+12⟩

def modeBindingFee (a q n : ℕ) : ℕ := 4+n*maskSearchStride a q+3*q+1+recordStride a q+12

theorem bind_source_mask_tape {a pages p q : ℕ} (fit : pages≤2^q)
    (i : Fin a) (axis : List Bool) (clock : axis.length=i.val)
    (mask : MaskFamily a pages (Fin 64)) (allPages : List (Page a pages (Fin 64)))
    (cover : ∀ k,k∈allPages) (xs : List (TypedModePair i pages p q)) :
    let out := bindModeMasks a axis (allPages.map (encodeMaskRow mask))
      (xs.map (fun x=>encodeMode (q:=q) i x.1)) (xs.map Prod.snd)
    out.result=some (xs.map (encodeCandidate i mask)) ∧
      out.steps≤5+xs.length*modeBindingFee a q allPages.length := by
  induction xs with
  | nil =>
    simp only [List.map_nil,bindModeMasks,List.length_nil,Nat.zero_mul,Nat.add_zero,le_refl,and_self]
  | cons x xs ih =>
    let h := mask_bank_nominal fit mask i axis clock x.1.1.val allPages (cover _)
    have e : modePage (encodeMode (q:=q) i x.1)=pageRef q x.1.1.val := rfl
    let z := bindModeMasks a axis (allPages.map (encodeMaskRow mask))
      (xs.map (fun x=>encodeMode (q:=q) i x.1)) (xs.map Prod.snd)
    let H := scanMask axis (pageRef q x.1.1.val) (allPages.map (encodeMaskRow mask))
    change H.result=some (selectedMaskBit mask x.1.1.val i) ∧
      H.steps≤4+allPages.length*maskSearchStride a q at h
    dsimp only
    simp only [List.map_cons,bindModeMasks,e,copy_fixed_exact]
    change (H.result.bind (fun bit=>z.result.map (⟨encodeMode i x.1,bit,x.2⟩::·)))=some _ ∧
      H.steps+(3*q+1)+z.steps+recordStride a q+12≤_
    rw [h.1,ih.1]
    refine ⟨rfl,?_⟩
    have hF := h.2
    have hf : z.steps≤5+xs.length*modeBindingFee a q allPages.length := ih.2
    rw [List.length_cons,Nat.add_mul,Nat.one_mul]
    unfold modeBindingFee at hf ⊢
    omega

#print axioms mask_bank_nominal
#print axioms bind_source_mask_tape
end J6R27OriginalGate





