import J4R43LiteralOutsideVariance

/-! Apply the finite fair-mark experiment to exactly the physical wire
types and their immutable ordered cells, retaining the distinguished pin.
The only quantitative margins below are explicit numeric input guards. -/
namespace J4R43LiteralOutside
open scoped Classical BigOperators
open P11FullPacking J6R10Repack IndependentThinning
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4300000

variable {E A B G : Type} [Fintype E] [Fintype G] [LinearOrder G] {a : ℕ}
variable {N : Network E A B} (P : PhysicalPacking N a G) (pin : E)

def realColour (e : Eligible N pin) : Cell (Fin a) G :=
  declaredCell N P.rowLabel P.colLabel e.val

abbrev EligibleAt (c : Cell (Fin a) G) :=
  {e : Eligible N pin//realColour P pin e=c}

abbrev RetainedAt (marks : Eligible N pin→Bool) (c : Cell (Fin a) G) :=
  {e : Eligible N pin//realColour P pin e=c ∧ Keep N pin marks e}

theorem actual_count_is_real_natural (w : Outcome (Eligible N pin))
    (h : 0<markProbability w) (c : Cell (Fin a) G) :
    countAt (block N pin) (realColour P pin) c w =
      (Nat.card (RetainedAt P pin (fun q=>(w q).1) c):ℚ) := by
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype,Finset.natCast_card_filter]
  unfold countAt
  refine Finset.sum_congr (Finset.ext (fun e=>by simp)) fun e _=>?_
  rw [real_count_for_supported_marks (block N pin) w h e]
  by_cases eq : realColour P pin e=c
  · simp [colourWeight,eq,Keep]
  · simp [colourWeight,eq,Keep]

theorem retained_fits_input_fiber (marks : Eligible N pin→Bool) (c : Cell (Fin a) G) :
    Nat.card (RetainedAt P pin marks c)≤
      Nat.card {w : InputCell P c//kept N pin marks w.val} := by
  let e : RetainedAt P pin marks c→{w : InputCell P c//kept N pin marks w.val} :=
    fun w=>⟨⟨w.val.val,w.prop.1⟩,Or.inr ⟨w.val,rfl,w.prop.2⟩⟩
  apply Nat.card_le_card_of_injective e
  intro p q h
  have hh : p.val.val=q.val.val :=
    congrArg (fun z : {w : InputCell P c//kept N pin marks w.val}=>z.val.val) h
  exact Subtype.ext (Subtype.ext hh)

theorem input_minus_closed_pin (c : Cell (Fin a) G) :
    Nat.card (InputCell P c)≤Nat.card (EligibleAt P pin c)+(close N pin).card := by
  let X := InputCell P c
  let active (x : X) := ¬adjacent N pin x.val
  let good : {x : X//active x} ≃ EligibleAt P pin c := by
    refine ⟨fun x=>⟨⟨x.val.val,x.prop⟩,x.val.prop⟩,
      fun x=>⟨⟨x.val.val,x.prop⟩,x.val.prop⟩,?_ ,?_⟩ <;> intro x <;> rfl
  let prune : {x : X//¬active x}→↥(close N pin) :=
    fun q=>⟨q.val.val,Finset.mem_filter.mpr ⟨Finset.mem_univ _,Classical.not_not.mp q.prop⟩⟩
  have prune_inj : Function.Injective prune := by
    intro p q h
    exact Subtype.ext (Subtype.ext
      (show p.val.val=q.val.val from congrArg (fun z : ↥(close N pin)=>z.val) h))
  have hp := Nat.card_le_card_of_injective prune prune_inj
  rw [Nat.card_eq_fintype_card (α:=↥(close N pin)),Fintype.card_coe] at hp
  calc
    _ = Nat.card ({x : X//active x} ⊕ {x : X//¬active x}) :=
      Nat.card_congr (Equiv.sumCompl active).symm
    _ = Nat.card (EligibleAt P pin c)+Nat.card {x : X//¬active x} := by
      rw [Nat.card_sum,Nat.card_congr good]
    _ ≤ _ := Nat.add_le_add_left hp _

theorem mean_in_actual_cell (c : Cell (Fin a) G) (D : ℕ)
    (hc : ∀ e : Eligible N pin,(block N pin e).card≤D) :
    (Nat.card (EligibleAt P pin c):ℚ)*(1/2:ℚ)^D ≤
      meanAt (block N pin) (realColour P pin) c := by
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype,Finset.natCast_card_filter,Finset.sum_mul]
  unfold meanAt 
  refine Finset.sum_le_sum fun e _=>?_
  by_cases eq : realColour P pin e=c
  · simp only [if_pos eq,one_mul,colourWeight,retention]
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (hc e)
  · simp [colourWeight,eq]

theorem finite_original_matching_supply (h degree : ℕ) (copies : 0<P.copies)
    (dr : ∀ u : A,Nat.card {e : E//N.row e=u}≤degree)
    (dc : ∀ u : B,Nat.card {e : E//N.col e=u}≤degree)
    (margin : ℚ) (margin_nonneg : 0≤margin)
    (large : 4*(Nat.card E:ℚ)*((2*degree-1)*(2*degree-1):ℕ)≤margin^2)
    (census : ∀ c : Cell (Fin a) G,
      ((2*h*P.copies:ℕ):ℚ)+margin≤(Nat.card (EligibleAt P pin c):ℚ)*(1/2:ℚ)^(2*degree-1)) :
    Nonempty (BandSupply P h pin) := by
  let D := 2*degree-1
  let BC := block N pin
  have size : ∀ e : Eligible N pin,(BC e).card≤D := literal_block_count N degree dr dc pin
  have hE : Fintype.card (Eligible N pin)≤Nat.card E := by
    rw [←Nat.card_eq_fintype_card]
    exact Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  have hsize : 4*(Fintype.card (Eligible N pin):ℚ)*(D*D:ℕ)≤margin^2 := by
    have q : (Fintype.card (Eligible N pin):ℚ)≤(Nat.card E:ℚ) := by exact_mod_cast hE
    apply LE.le.trans ?_ large
    gcongr
  obtain ⟨w,pos,all⟩ := all_cells_close BC (realColour P pin) D (block_contains N pin)
    (block_symmetric N pin) size margin margin_nonneg hsize
  let marks := fun q : Eligible N pin=>(w q).1
  have fit (c : Cell (Fin a) G) : 2*h*P.copies≤Nat.card (RetainedAt P pin marks c) := by
    have H := (census c).trans (mean_in_actual_cell P pin c D size)
    have A := (abs_le.mp (all c)).1
    have E := actual_count_is_real_natural P pin w pos c
    change -margin≤countAt BC (realColour P pin) c w-meanAt BC (realColour P pin) c at A
    have good : ((2*h*P.copies:ℕ):ℚ)≤(Nat.card (RetainedAt P pin marks c):ℚ) := by
      rw [←E]
      linarith
    exact_mod_cast good
  exact ⟨actual_marking_band_supply N pin P h copies marks
    (fun c=>(fit c).trans (retained_fits_input_fiber P pin marks c))⟩

#print axioms actual_count_is_real_natural
#print axioms retained_fits_input_fiber
#print axioms input_minus_closed_pin
#print axioms mean_in_actual_cell
#print axioms finite_original_matching_supply
end
end J4R43LiteralOutside

