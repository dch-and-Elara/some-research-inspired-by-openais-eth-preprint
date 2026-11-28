
import J6R14LayoutCostStable
import J6R14LayoutCostPlant
import J6R23PaddingCensusLegalChart

/-! Complete the R14 stable, occurrence-ordered addresses to a true
legal root chart. It is a new deterministic chart, not a claim about
the older nonconstructive tie-break in the frozen chart. -/
namespace J6R24LegalLayout
open scoped BigOperators Classical
open P11FullPacking J6RecursiveOrientation J6OrientedHost J6R23PaddingCensus
open J6R14LayoutCost AOracleMachineTime AOracleMachineTimeTape
set_option maxHeartbeats 15000000
set_option linter.unusedSectionVars false

abbrev FullRank (a b : ℕ) := Cell (Fin a) (Fin 64)×Fin (b*2^a)

def stableRank {a b q : ℕ} (cap : b*2^a≤2^q) (x : FullRank a b) : AddressRank a b q :=
  (x.1,Fin.cast (Nat.min_eq_right cap).symm x.2)

noncomputable def fullStable {a b q : ℕ} (ha : a≤q) (cap : b*2^a≤2^q)
    (r : FullRank a b) : Physical a b (Fin 64) :=
  stableAddr ha (stableRank cap r)

theorem full_stable_cell {a b q : ℕ} (ha : a≤q) (cap : b*2^a≤2^q)
    (r : FullRank a b) :
    physicalCell (fun _ _ _=>false) (fullStable ha cap r)=r.1 :=
  stableAddr_cell ha (stableRank cap r)

theorem full_stable_injective {a b q : ℕ} (ha : a≤q) (cap : b*2^a≤2^q) :
    Function.Injective (fullStable ha cap) := by
  intro x y h
  have h' := stableAddr_injective ha h
  have A := congrArg (fun t : AddressRank a b q=>t.1) h'
  have B := congrArg (fun t : AddressRank a b q=>t.2.val) h'
  exact Prod.ext A (Fin.ext B)

theorem full_stable_surjective {a b q : ℕ} (ha : a≤q) (cap : b*2^a≤2^q) :
    Function.Surjective (fullStable ha cap) := by
  have hcard : Fintype.card (FullRank a b) = Fintype.card (Physical a b (Fin 64)) :=
    (Fintype.card_congr (fullSlotChart (fun _ _ _=>false) :
      Physical a b (Fin 64) ≃ FullRank a b)).symm
  exact ((Fintype.bijective_iff_injective_and_card _).2 ⟨full_stable_injective ha cap,hcard⟩).2

noncomputable def stableChart {a b q : ℕ} (ha : a≤q) (cap : b*2^a≤2^q) :
    FullRank a b ≃ Physical a b (Fin 64) :=
  Equiv.ofBijective _ ⟨full_stable_injective ha cap,full_stable_surjective ha cap⟩

theorem stable_diagonal_slots {a b q : ℕ} (ha : a≤q) (cap : b*2^a≤2^q)
    (w : Fin a→Fin 64) (k : Fin b) (j : Fin (2^a)) :
    fullStable ha cap (diagonal w,finProdFinEquiv (k,j))=diagonalSlot w k j := by
  let r := finProdFinEquiv (k,j)
  let z := fullStable ha cap (diagonal w,r)
  have val : r.val=k.val*2^a+j.val := by
    change j.val+2^a*k.val=k.val*2^a+j.val
    rw [Nat.mul_comm k.val (2^a),Nat.add_comm]
  have fit : k.val*2^a+j.val<2^q := val ▸ r.isLt.trans_le cap
  obtain ⟨hslot,hpage⟩ := diagonal_planted_rank w k.val j.val ha fit k.isLt j.isLt
  have js : z.2.val=j.val := by
    change ((bitsChart a).symm (fun i=>(seatWords (marksOf (diagonal w))
      (encodeBits q r.val)).result.slot.getD i.val false)).val=j.val
    rw [val]
    exact hslot
  have ks : z.1.2.1.val=k.val := by
    change bitsValue (seatWords (marksOf (diagonal w)) (encodeBits q r.val)).result.page=k.val
    rw [val]
    exact hpage
  refine Prod.ext ?_ (Fin.ext js)
  change (Sigma.mk (key (diagonal w)) z.1.2)=(Sigma.mk (key (diagonal w)) (k,orientation (diagonal w)))
  apply congrArg (Sigma.mk (key (diagonal w)))
  refine Prod.ext (Fin.ext ks) ?_
  funext i
  exact (diagonal_no_hot w).false i |>.elim

noncomputable def placedRank {a b m l : ℕ} (w : Fin a→Fin 64)
    (hm : m≤b) (hL : 2*l=2^a) : Wire w m b l ≃ FullRank a b :=
  (J6PhysicalPacking.placement (diagonal w) m b l hm).trans
    (Equiv.prodCongr (Equiv.refl _) ((Equiv.prodCongr (Equiv.refl _) (finCongr hL)).trans finProdFinEquiv))

noncomputable def deterministicLegal {a b m l q : ℕ} (ha : a≤q) (cap : b*2^a≤2^q)
    (w : Fin a→Fin 64) (hm : m≤b) (hL : 2*l=2^a) :
    LegalRootChart w hm hL where
  seats := (placedRank w hm hL).trans (stableChart ha cap)
  plant u j := stable_diagonal_slots ha cap w (Fin.castLE hm u) (Fin.cast hL j)

theorem deterministic_legal_cell {a b m l q : ℕ} (ha : a≤q) (cap : b*2^a≤2^q)
    (w : Fin a→Fin 64) (hm : m≤b) (hL : 2*l=2^a) (e : Wire w m b l) :
    physicalCell (fun _ _ _=>false) ((deterministicLegal ha cap w hm hL).seats e) =
      (J6PhysicalPacking.place (diagonal w) m b l hm e).1 := by
  exact full_stable_cell ha cap (placedRank w hm hL e)

#print axioms full_stable_cell
#print axioms full_stable_injective
#print axioms full_stable_surjective
#print axioms stable_diagonal_slots
#print axioms deterministic_legal_cell
end J6R24LegalLayout
