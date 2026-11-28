import V8NativeMessageC2PhysicalNeighborhood
import V8NativeMessageMatchCount

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

/-! Deterministic greedy induced matching at the original constant 17,
followed by orientation into the literal Pairs chart in the same graph. -/
namespace V8NativeMessage.C2Physical
open scoped Classical BigOperators
open V8PooledRange
noncomputable section

variable {V E : Type*} [Fintype E] (G : Graph V E)

def separated (M : Finset E) : Prop :=
  ∀ e∈M, ∀ f∈M, e≠f→¬withinTwo G e f

theorem greedy_separated (p : ThreePorts G) (S : Finset E) :
    ∃ M ⊆ S, separated G M ∧ S.card≤17*M.card := by
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    by_cases hS : S.Nonempty
    · obtain ⟨e,he⟩ := hS
      let R := S \ ball G e
      have hn : e∉R := fun a => (Finset.mem_sdiff.mp a).2 (ball_contains G e)
      have hRS : R ⊂ S := Finset.ssubset_iff_subset_ne.mpr
        ⟨Finset.sdiff_subset,fun h => hn (h.symm ▸ he)⟩
      obtain ⟨M,hMR,hsep,hcard⟩ := ih R hRS
      have hes : e∉M := fun h => hn (hMR h)
      have hms : M⊆S := hMR.trans (Finset.sdiff_subset)
      refine ⟨insert e M,Finset.insert_subset_iff.mpr ⟨he,hms⟩,?_,?_⟩
      · intro f hf z hz hne hzNear
        rcases Finset.mem_insert.mp hf with hhf | hfM
        · subst f
          rcases Finset.mem_insert.mp hz with hhz | hzM
          · exact hne hhz.symm
          · exact (Finset.mem_sdiff.mp (hMR hzM)).2 (ball_contains_two G hzNear)
        · rcases Finset.mem_insert.mp hz with hhz | hzM
          · subst z
            exact (Finset.mem_sdiff.mp (hMR hfM)).2
              (ball_contains_two G (withinTwo_symm G hzNear))
          · exact hsep f hfM z hzM hne hzNear
      · have hcap : (S ∩ ball G e).card≤17 :=
          (Finset.card_le_card Finset.inter_subset_right).trans (ball_cap G p e)
        have heq := Finset.card_sdiff_add_card_inter S (ball G e)
        change R.card+(S ∩ ball G e).card=S.card at heq
        rw [Finset.card_insert_of_notMem hes]
        omega
    · have he : S=∅ := Finset.not_nonempty_iff_eq_empty.mp hS
      subst S
      refine ⟨∅,Finset.Subset.rfl,?_,by simp⟩
      simp [separated]

def cutLabel (S : Finset V) (x : V) : Bool := decide (x∈S)

theorem cutLabel_eq_true (S : Finset V) (x : V) : cutLabel S x=true ↔ x∈S := by
  simp [cutLabel]

theorem cutLabel_eq_false (S : Finset V) (x : V) : cutLabel S x=false ↔ x∉S :=
  decide_eq_false_iff_not

def boundary (S : Finset V) : Finset E :=
  Finset.univ.filter (fun e => cutLabel S (G e false)≠cutLabel S (G e true))

theorem boundary_iff (S : Finset V) (e : E) :
    e∈boundary G S ↔ cutLabel S (G e false)≠cutLabel S (G e true) := by
  simp only [boundary,Finset.mem_filter,Finset.mem_univ,true_and]

def leftDir (S : Finset V) (e : E) : Bool := !cutLabel S (G e false)

def turn (S : Finset V) (e : E) (b : Bool) : Bool :=
  if b then !(leftDir G S e) else leftDir G S e

theorem leftDir_left (S : Finset V) (e : E) (h : e∈boundary G S) :
    G e (leftDir G S e)∈S := by
  apply (cutLabel_eq_true _ _).mp
  have hc := (boundary_iff G S e).mp h
  cases hm : cutLabel S (G e false) <;> cases hn : cutLabel S (G e true) <;>
    simp_all [leftDir]

theorem leftDir_right (S : Finset V) (e : E) (h : e∈boundary G S) :
    G e (!(leftDir G S e))∉S := by
  apply (cutLabel_eq_false _ _).mp
  have hc := (boundary_iff G S e).mp h
  cases hm : cutLabel S (G e false) <;> cases hn : cutLabel S (G e true) <;>
    simp_all [leftDir]

omit [Fintype E] in
theorem turn_injective (S : Finset V) (e : E) : Function.Injective (turn G S e) := by
  intro b c h
  cases h' : leftDir G S e <;> cases b <;> cases c <;> simp_all [turn]

def enum (M : Finset E) : Fin M.card ≃ M :=
  (Fintype.equivFinOfCardEq (Fintype.card_coe M)).symm

variable (S : Finset V) (M : Finset E) (hs : M⊆boundary G S) (hi : separated G M)
    (hloop : ∀ e, G e false≠G e true)

def makePairs : V8NativeMessage.Pairs G M.card where
  seat :=
    { toFun := fun x => G (enum M x.1).val (turn G S (enum M x.1).val x.2)
      inj' := by
        rintro ⟨i,b⟩ ⟨j,c⟩ hb
        by_cases h : i=j
        · subst j
          have hinj : Function.Injective (G (enum M i).val) := by
            intro a d he
            have hne := hloop (enum M i).val
            cases a <;> cases d <;> simp_all
          exact Prod.ext rfl (turn_injective G S _ (hinj hb))
        · have hne : (enum M i).val≠(enum M j).val := fun e =>
            h ((enum M).injective (Subtype.ext e))
          exact False.elim (hi _ (enum M i).property _ (enum M j).property hne
            (Or.inl ⟨_,_,hb⟩)) }
  edge := fun i => (enum M i).val
  reverse := fun i => leftDir G S (enum M i).val
  left := fun _ => rfl
  right := fun _ => rfl
  only := by
    intro e x y hx hy
    have he : x.1=y.1 := by
      by_contra hn
      have hne : (enum M x.1).val≠(enum M y.1).val := fun hh => hn
        ((enum M).injective (Subtype.ext hh))
      exact hi _ (enum M x.1).property _ (enum M y.1).property hne
        (Or.inr ⟨e,⟨_,false,hx.symm⟩,⟨true,_,hy⟩⟩)
    refine ⟨he,fun h => hloop e ?_⟩
    have hxy : x=y := Prod.ext he h
    rw [hxy] at hx
    exact hx.trans hy.symm

include hs in
theorem makePairs_left (j : Fin M.card) :
    (makePairs G S M hi hloop).seat (j,false)∈S :=
  leftDir_left G S _ (hs (enum M j).property)

include hs in
theorem makePairs_right (j : Fin M.card) :
    (makePairs G S M hi hloop).seat (j,true)∉S :=
  leftDir_right G S _ (hs (enum M j).property)

include hloop in
/-- The endpoints of the produced matching and its density live on the
same cut; no existential choice of a different graph after packing. -/
theorem crossing_pairs (p : ThreePorts G) :
    ∃ m : ℕ, ∃ K : V8NativeMessage.Pairs G m,
      (boundary G S).card≤17*m ∧
        (∀ j, K.seat (j,false)∈S) ∧ (∀ j,K.seat (j,true)∉S) := by
  obtain ⟨M,hM,hsep,hcap⟩ := greedy_separated G p (boundary G S)
  exact ⟨M.card,makePairs G S M hsep hloop,hcap,
    makePairs_left G S M hM hsep hloop,makePairs_right G S M hM hsep hloop⟩

#print axioms greedy_separated
#print axioms leftDir_left
#print axioms leftDir_right
#print axioms makePairs
#print axioms makePairs_left
#print axioms makePairs_right
#print axioms crossing_pairs
end
end V8NativeMessage.C2Physical
