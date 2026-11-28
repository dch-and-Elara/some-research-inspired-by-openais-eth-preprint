import J6R33PageIndexedBirthBoundary
import J6R24LegalLayoutTensor

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 6500000

/-! Counterexample for the actual physical row scanner, not just
two inconsistent user-supplied capsules at different keys. Both
true pages are occupied in the same group of the full printed chart. -/
namespace J6R33PageIndexedBirth
open scoped Classical
open AOracleMachineTime J6R15ModeCost
open J6R9PacketScopes J6R10Repack J6R18ChildWrite J6R20Ancestor
open P11FullPacking J6R27OriginalGate J6R32ChildResidentTransfer
open J6R24LegalLayout J6OrientedHost J6Mesh J6RecursiveOrientation

def uniformPacket {a b : ℕ} (j : Fin b) : Page a b (Fin 64) :=
  ⟨⟨fun _=>((0 : Fin 64),0),fun _=>le_rfl⟩,j,fun _=>false⟩

def mixedPacket {a b : ℕ} (j : Fin b) : Page a b (Fin 64) :=
  ⟨⟨fun _=>((0 : Fin 64),1),fun _=>by change (0:Fin 64)≤1; decide⟩,j,fun _=>false⟩

private theorem mixed_hot {a b : ℕ} (j : Fin b) (i : Fin a) :
    ((mixedPacket (a:=a) j).1.val i).1≠((mixedPacket (a:=a) j).1.val i).2 := by change (0:Fin 64)≠1; decide

theorem uniform_row_is_zero {a b : ℕ} (M : MaskFamily a b (Fin 64)) (j : Fin b)
    (i : Fin a) (z : Fin (2^a)) : rowGroup M i (uniformPacket j,z)=0 := by
  unfold rowGroup physicalCell cell
  rw [dif_neg (not_not.mpr (show ((uniformPacket (a:=a) j).1.val i).1=
    ((uniformPacket (a:=a) j).1.val i).2 from rfl))]
  rfl

noncomputable def mixedSeat {a b : ℕ} (M : MaskFamily a b (Fin 64)) (j : Fin b) (want : Bool) :
    Fin (2^a) :=
  let k := mixedPacket (a:=a) j
  (bitsChart a).symm (fun i=>decide (M k.1 k.2 ⟨i,mixed_hot j i⟩≠want))

theorem mixed_seat_row {a b : ℕ} (M : MaskFamily a b (Fin 64)) (j : Fin b)
    (i : Fin a) (want : Bool) :
    rowGroup M i (mixedPacket j,mixedSeat M j want)=if want then 1 else 0 := by
  let k := mixedPacket (a:=a) j
  let r : Hot k.1 := ⟨i,mixed_hot j i⟩
  have hBit : bits a (mixedSeat M j want) i=decide (M k.1 k.2 r≠want) :=
    congrFun ((bitsChart a).apply_symm_apply (fun u=>decide (M k.1 k.2 ⟨u,mixed_hot j u⟩≠want))) i
  have hv : slotOrient k.1 (M k.1 k.2) (mixedSeat M j want) r=want := by
    change (if bits a (mixedSeat M j want) i then !(M k.1 k.2 r) else M k.1 k.2 r)=want
    rw [hBit]
    cases M k.1 k.2 r <;> cases want <;> rfl
  change (cell k.1 (slotOrient k.1 (M k.1 k.2) (mixedSeat M j want)) i).1=_
  unfold cell
  rw [dif_pos (mixed_hot j i),hv]
  cases want <;> rfl

variable {E A B : Type} {N : Network E A B} {a : ℕ}

theorem actual_slot_words_cannot_broadcast
    (P : PhysicalPacking N a (Fin 64)) (i : Fin a)
    [DecidableEq (Page a P.copies (Fin 64))]
    (j : Fin P.copies) (full : Function.Surjective P.seat) (edges : List E)
    (all : ∀ e,e∈edges) :
    let rows (k : Page a P.copies (Fin 64)) :=
      (sourceRows P i 0 k edges).map (fun r=>slotWord P r.val)
    rows (uniformPacket j)≠[] ∧ rows (mixedPacket j)≠[] ∧
      ¬∃ z, z=rows (uniformPacket j) ∧ z=rows (mixedPacket j) := by
  let kd := uniformPacket (a:=a) j
  let kh := mixedPacket (a:=a) j
  let x := mixedSeat P.mask j true
  let y := mixedSeat P.mask j false
  obtain ⟨rd,dr⟩ := full (kd,x)
  obtain ⟨rh,hr⟩ := full (kh,y)
  let A := (sourceRows P i 0 kd edges).map (fun r=>slotWord P r.val)
  let B := (sourceRows P i 0 kh edges).map (fun r=>slotWord P r.val)
  have bd : childBlock P i rd=(0,kd) := by
    unfold childBlock rowBlock
    rw [dr]
    exact Prod.ext (uniform_row_is_zero P.mask j i x) rfl
  have bh : childBlock P i rh=(0,kh) := by
    unfold childBlock rowBlock
    rw [hr]
    exact Prod.ext (mixed_seat_row P.mask j i false) rfl
  have memD : word x.val∈A := by
    have h : (⟨rd,bd⟩ : RowsOf P i 0 kd)∈sourceRows P i 0 kd edges :=
      (scan_subtype_mem _ _ _).mpr (all rd)
    refine List.mem_map.mpr ⟨⟨rd,bd⟩,h,?_⟩
    unfold slotWord
    rw [dr]
  have memH : word y.val∈B := by
    have h : (⟨rh,bh⟩ : RowsOf P i 0 kh)∈sourceRows P i 0 kh edges :=
      (scan_subtype_mem _ _ _).mpr (all rh)
    refine List.mem_map.mpr ⟨⟨rh,bh⟩,h,?_⟩
    unfold slotWord
    rw [hr]
  have missH : word x.val∉B := by
    intro m
    obtain ⟨u,_,eq⟩ := List.mem_map.mp m
    have slot : (P.seat u.val).2=x := by
      apply Fin.ext
      have v := congrArg (fun z : Word a=>z.val) eq
      change (word (q:=a) (P.seat u.val).2.val).val=(word (q:=a) x.val).val at v
      rwa [word_val (P.seat u.val).2.isLt,word_val x.isLt] at v
    have ⟨row,page⟩ := row_scope P i u
    rw [show P.seat u.val=(kh,x) from Prod.ext page slot,mixed_seat_row P.mask j i true] at row
    exact (by decide : (1 : Fin 64)≠0) row
  change A≠[] ∧ B≠[] ∧ ¬∃ z,z=A ∧ z=B
  refine ⟨fun eq=>by rw [eq] at memD; exact List.not_mem_nil memD,
    fun eq=>by rw [eq] at memH; exact List.not_mem_nil memH,?_⟩
  rintro ⟨_,d,h⟩
  exact missH (d.symm.trans h ▸ memD)

theorem actual_two_scans_cannot_broadcast
    (P : PhysicalPacking N a (Fin 64)) (i : Fin a)
    [DecidableEq (Page a P.copies (Fin 64))]
    (j : Fin P.copies) (full : Function.Surjective P.seat)
    (w : ℕ) (fits : P.copies≤2^w) (edges : List E)
    (nd : edges.Nodup) (all : ∀ e,e∈edges) :
    let raw := edges.map (physicalSeatField P i (childPageKey w))
    let scan (k : Page a P.copies (Fin 64)) :=
      (selectedSlots (childPageKey w k) (word 0) raw).result.1
    scan (uniformPacket j)≠[] ∧ scan (mixedPacket j)≠[] ∧
      ¬∃ z, z=scan (uniformPacket j) ∧ z=scan (mixedPacket j) := by
  let raw := edges.map (physicalSeatField P i (childPageKey w))
  let scan (k : Page a P.copies (Fin 64)) :=
    (selectedSlots (childPageKey w k) (word 0) raw).result.1
  have align (k : Page a P.copies (Fin 64)) :
      scan k=(sourceRows P i 0 k edges).map (fun r=>slotWord P r.val) :=
    congrArg Prod.fst (physical_slots_emitted P i (childPageKey w)
      (child_page_key_injective w fits) 0 k edges nd all raw rfl).1
  change scan (uniformPacket j)≠[] ∧ scan (mixedPacket j)≠[] ∧
    ¬∃ z,z=scan (uniformPacket j) ∧ z=scan (mixedPacket j)
  rw [align (uniformPacket j),align (mixedPacket j)]
  exact actual_slot_words_cannot_broadcast P i j full edges all


/-- This is an instance of the physical stable padded root from the
native source, not an independently selected abstract layout. -/
theorem stable_root_seat_is_full {V : Type} [Fintype V] (m l q width : ℕ)
    (T : Plant V m q) (w : Fin (J6Mesh.a m)→Fin 64)
    (hm : m≤K m) (hL : 2*l=L m) (ha : J6Mesh.a m≤width) (cap : K m*L m≤2^width) :
    Function.Surjective (stableRootPacking m l q width T w hm hL ha cap).seat :=
  (deterministicLegal ha cap w hm hL).seats.surjective

#print axioms uniform_row_is_zero
#print axioms mixed_seat_row
#print axioms actual_slot_words_cannot_broadcast
#print axioms actual_two_scans_cannot_broadcast
#print axioms stable_root_seat_is_full
end J6R33PageIndexedBirth
