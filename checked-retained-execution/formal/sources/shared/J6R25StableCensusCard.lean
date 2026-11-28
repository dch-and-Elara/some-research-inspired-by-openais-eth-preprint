
import J6R25StableCensusPadOrder

/-! Closed count of the actual stable padding tape, from the typed full
plant/pad placement, including the distinguished-cell prefix. -/
namespace J6R25StableCensus
open scoped Classical
open P11FullPacking J6OrientedHost J6PhysicalPacking J6RecursiveOrientation J6R24LegalLayout
set_option maxHeartbeats 4500000
set_option linter.unusedSectionVars false

theorem actual_pad_tape_count {a : ℕ} (m b l : ℕ) (w : Fin a→Fin 64) (hm : m≤b) :
    (exactPadOrder m b l w).length=(Fintype.card (CellType a)*b-m)*l := by
  obtain ⟨nd,all⟩ := exact_pad_order m b l w
  have H : (exactPadOrder m b l w).length=Fintype.card (J6OrientedHost.Pad w m b l) := by
    rw [←List.toFinset_card_of_nodup nd,all,Finset.card_univ]
  let C := Fintype.card (CellType a)
  let D := Fintype.card (J6OrientedHost.Pad w m b l)
  have E := Fintype.card_congr (J6PhysicalPacking.placement (diagonal w) m b l hm)
  rw [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,Fintype.card_fin,
    Fintype.card_prod,Fintype.card_bool,Fintype.card_prod,Fintype.card_prod,
    Fintype.card_fin,Fintype.card_fin] at E
  change m*(2*l)+D*2=C*(b*(2*l)) at E
  have A : m*(2*l)=(m*l)*2 := by ring
  have B : C*(b*(2*l))=((C*b)*l)*2 := by ring
  rw [A,B] at E
  have K : D=(C*b)*l-m*l := by omega
  rw [H]
  change D=(C*b-m)*l
  exact K.trans (Nat.sub_mul _ _ _).symm

#print axioms actual_pad_tape_count
end J6R25StableCensus
