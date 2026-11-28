
import J6R14LayoutCostExport
import J6R14LayoutCostDriver

/-! The physically generated binary key menu contains each full ordered
cell exactly once, with no decoder for missing or guessed labels. -/
namespace J6R24LegalLayout
open scoped BigOperators Classical
open J6R14LayoutCost P11FullPacking AOracleMachineTime
open J6R12CollisionEdges
set_option maxHeartbeats 9500000
set_option linter.unusedSectionVars false

abbrev CellType (a : ℕ) := Cell (Fin a) (Fin 64)
abbrev KeyToken (a : ℕ) := ↥((allPairs (6*a)).toFinset)

theorem word_cell_injective (a : ℕ) : Function.Injective (@wordCell a) := by
  intro x y H
  have h₁ := coordinateLabel_inj (congrArg Prod.fst H)
  have h₂ := coordinateLabel_inj (congrArg Prod.snd H)
  funext i
  exact Prod.ext (congrFun h₁ i) (congrFun h₂ i)

def encodeToken (a : ℕ) (c : CellType a) : KeyToken a :=
  ⟨wordCell c,by
    apply List.mem_toFinset.mpr
    apply (allPairs_mem (6*a) _).mpr
    exact ⟨coordinateLabel_len _,coordinateLabel_len _⟩⟩

theorem encode_token_bijective (a : ℕ) : Function.Bijective (encodeToken a) := by
  have I : Function.Injective (encodeToken a) := fun _ _ h=>word_cell_injective a (congrArg Subtype.val h)
  have cardinal : Fintype.card (CellType a)=Fintype.card (KeyToken a) := by
    rw [Fintype.card_coe,List.toFinset_card_of_nodup (allPairs_nodup _),allPairs_len]
    simp only [CellType,Cell,Fintype.card_fun,Fintype.card_fin,Fintype.card_prod]
    rw [mul_pow,show (64:ℕ)=2^6 by decide,←pow_mul]
  exact (Fintype.bijective_iff_injective_and_card _).2 ⟨I,cardinal⟩

noncomputable def tokenChart (a : ℕ) : CellType a≃KeyToken a :=
  Equiv.ofBijective _ (encode_token_bijective a)

theorem emitted_cells_exact (a : ℕ) :
    let A := allPairsMachine (6*a)
    (∀ c : CellType a,wordCell c∈A.result) ∧
      (∀ k∈A.result,∃! c : CellType a,wordCell c=k) ∧
      A.result.Nodup ∧ A.result.length=2^(6*a)*2^(6*a) ∧ A.steps≤allPairsCap (6*a) := by
  obtain ⟨e,b⟩ := allPairsMachine_exact (6*a)
  dsimp only
  refine ⟨?_,?_,?_,?_,b⟩
  · intro c
    rw [e]
    exact List.mem_toFinset.mp (encodeToken a c).property
  · intro k h
    rw [e] at h
    let x : KeyToken a := ⟨k,List.mem_toFinset.mpr h⟩
    let y := (tokenChart a).symm x
    have P : wordCell y=k := congrArg Subtype.val ((tokenChart a).apply_symm_apply x)
    exact ⟨y,P,fun c h=>word_cell_injective a (h.trans P.symm)⟩
  · rw [e]
    exact allPairs_nodup _
  · rw [e,allPairs_len]

#print axioms word_cell_injective
#print axioms encode_token_bijective
#print axioms emitted_cells_exact
end J6R24LegalLayout
