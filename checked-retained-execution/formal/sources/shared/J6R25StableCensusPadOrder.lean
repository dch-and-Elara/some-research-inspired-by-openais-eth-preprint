
import J6R24LegalLayoutTable

/-! Exact wire identities in the stable padded tail of each cell.
A two-port gadget occupies ranks start+2j and start+2j+1 in the
*ordered-cell rank*, not necessarily consecutive physical slots. -/
namespace J6R25StableCensus
open scoped Classical BigOperators
open P11FullPacking J6OrientedHost J6RecursiveOrientation J6PhysicalPacking J6R24LegalLayout
set_option maxHeartbeats 15000000
set_option linter.unusedSectionVars false

def padSpan {a : ℕ} (m b l : ℕ) (w : Fin a→Fin 64) (c : CellType a) :=
  (b-offset (diagonal w) m c)*l

def padStart {a : ℕ} (m : ℕ) (w : Fin a→Fin 64) (c : CellType a) :=
  offset (diagonal w) m c*2^a

def localPad {a : ℕ} (m b l : ℕ) (w : Fin a→Fin 64) (c : CellType a)
    (j : Fin (padSpan m b l w c)) : J6OrientedHost.Pad w m b l :=
  ⟨c,finProdFinEquiv.symm j⟩

theorem local_pad_injective {a m b l : ℕ} (w : Fin a→Fin 64) (c : CellType a) :
    Function.Injective (localPad m b l w c) := by
  intro i j h
  apply finProdFinEquiv.symm.injective
  exact eq_of_heq (Sigma.mk.inj_iff.mp h).2

def padsInCell {a : ℕ} (m b l : ℕ) (w : Fin a→Fin 64) (c : CellType a) :
    List (J6OrientedHost.Pad w m b l) :=
  (List.finRange (padSpan m b l w c)).map (localPad m b l w c)

noncomputable def exactPadOrder {a : ℕ} (m b l : ℕ) (w : Fin a→Fin 64) :
    List (J6OrientedHost.Pad w m b l) :=
  (typedCells a).flatMap (padsInCell m b l w)

theorem exact_pad_order {a : ℕ} (m b l : ℕ) (w : Fin a→Fin 64) :
    (exactPadOrder m b l w).Nodup ∧ (exactPadOrder m b l w).toFinset=Finset.univ := by
  constructor
  · unfold exactPadOrder
    rw [List.nodup_flatMap]
    refine ⟨fun c _=>(List.nodup_finRange _).map (local_pad_injective w c),?_⟩
    apply (typed_cells_exact a).1.imp
    intro k c ne d hx hy
    obtain ⟨i,_,a0⟩ := List.mem_map.mp hx
    obtain ⟨j,_,a1⟩ := List.mem_map.mp hy
    apply ne
    have e0 := congrArg Sigma.fst a0
    have e1 := congrArg Sigma.fst a1
    exact e0.trans e1.symm
  · ext d
    simp only [Finset.mem_univ,List.mem_toFinset,iff_true]
    rcases d with ⟨c,p⟩
    refine List.mem_flatMap.mpr ⟨c,(typed_cells_exact a).2.1 c,List.mem_map.mpr ?_⟩
    let j : Fin (padSpan m b l w c) := finProdFinEquiv p
    refine ⟨j,List.mem_finRange j,?_⟩
    unfold localPad
    rw [finProdFinEquiv.symm_apply_apply]

theorem pad_range_exact_tail {a m b l : ℕ} (w : Fin a→Fin 64) (hm : m≤b) (hL : 2*l=2^a)
    (c : CellType a) :
    padStart m w c+2*padSpan m b l w c=b*2^a := by
  have g := (offset_le (diagonal w) m c).trans hm
  unfold padStart padSpan
  rw [←hL,show 2*((b-offset (diagonal w) m c)*l)=(b-offset (diagonal w) m c)*(2*l) by ring,
    ←Nat.add_mul,Nat.add_sub_of_le g]

theorem placed_rank_pad_address {a m b l : ℕ} (w : Fin a→Fin 64) (hm : m≤b) (hL : 2*l=2^a)
    (c : CellType a) (j : Fin (padSpan m b l w c)) (side : Bool) :
    let r := placedRank w hm hL (.inr (localPad m b l w c j,side))
    r.1=c ∧ r.2.val=padStart m w c+2*j.val+siteBit side := by
  let x := finProdFinEquiv.symm j
  have E := congrArg Fin.val (finProdFinEquiv.apply_symm_apply j)
  change x.2.val+l*x.1.val=j.val at E
  refine ⟨rfl,?_⟩
  change 2*x.2.val+siteBit side+(2^a)*(offset (diagonal w) m c+x.1.val) =
    offset (diagonal w) m c*2^a+2*j.val+siteBit side
  rw [←hL,←E]
  ring

#print axioms local_pad_injective
#print axioms exact_pad_order
#print axioms pad_range_exact_tail
#print axioms placed_rank_pad_address
end J6R25StableCensus
