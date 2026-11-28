import J1MainSourceLabels
import J1MainSourcePlacement
import Mathlib.Tactic

/-! The literal finite collision potentials for MAIN. The ordered pairs
that can share a random coordinate are charged individually; all other
pairs cancel exactly in the expected square-deviation score. -/
namespace J1MainSourceCollision
open scoped BigOperators Classical
open DiagonalAbundance J1MainSourceLabels J1MainSourcePlacement
noncomputable section
universe u v w
variable {A : Type u} {C : Type v} {Ω : Type w}

def indicator (p : Prop) : ℚ := if p then 1 else 0

def load [Fintype A] (color : A → C) (c : C) : ℚ :=
  ∑ a, indicator (color a = c)

def deviation [Fintype A] [Fintype C] (color : A → C) : ℚ :=
  ∑ c, (load color c - (Fintype.card A : ℚ) / (Fintype.card C : ℚ))^2

theorem deviation_nonneg [Fintype A] [Fintype C] (color : A → C) :
    0 ≤ deviation color :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem sum_load [Fintype A] [Fintype C] (color : A → C) :
    (∑ c, load color c) = Fintype.card A := by
  unfold load
  rw [Finset.sum_comm]
  simp [indicator,eq_comm]

theorem sum_load_square [Fintype A] [Fintype C] (color : A → C) :
    (∑ c, load color c ^ 2) =
      ∑ p : A×A, indicator (color p.1 = color p.2) := by
  have hs (c : C) : load color c ^ 2 =
      ∑ a, ∑ b, indicator (color a = c) * indicator (color b = c) := by
    rw [load,pow_two,Finset.sum_mul]
    simp_rw [Finset.mul_sum]
  rw [Fintype.sum_prod_type]
  simp_rw [hs]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_eq_single_of_mem (color a) (Finset.mem_univ _)]
  · simp [indicator,eq_comm]
  · intro c _ hc
    simp [indicator,Ne.symm hc]

/-- The exact centered collision expansion, including equal incidences in
the ordered pair list. -/
theorem deviation_eq_pairs [Fintype A] [Fintype C] [Nonempty C] (color : A → C) :
    deviation color =
      ∑ p : A×A, (indicator (color p.1 = color p.2) - 1/(Fintype.card C : ℚ)) := by
  let n : ℚ := Fintype.card A
  let D : ℚ := Fintype.card C
  have hD : D ≠ 0 := by
    dsimp [D]
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card C ≠ 0)
  have hs (c : C) : (load color c-n/D)^2 =
      (load color c)^2 - (2*(n/D))*load color c + (n/D)^2 := by ring
  change (∑ c, (load color c-n/D)^2) = _
  simp_rw [hs]
  rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.mul_sum,sum_load,
    sum_load_square,Finset.sum_sub_distrib]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_prod,Nat.cast_mul]
  change (_ - 2*(n/D)*n + D*(n/D)^2) = _ - n*n*(1/D)
  field_simp
  ring

theorem expected_deviation_bad_pairs [Fintype A] [Fintype C] [Nonempty C] [Fintype Ω]
    [Nonempty Ω] (colors : Ω → A → C) (bad : Finset (A×A))
    (good : ∀ p : A×A, p ∉ bad →
      mean (fun x => indicator (colors x p.1 = colors x p.2)) = 1/(Fintype.card C : ℚ)) :
    mean (fun x => deviation (colors x)) ≤ bad.card := by
  simp_rw [deviation_eq_pairs,mean_sum,mean_lin_sub,mean_const]
  calc
    _ ≤ ∑ p : A×A, indicator (p ∈ bad) := by
      apply Finset.sum_le_sum
      intro p _
      by_cases hb : p ∈ bad
      · have hh : mean (fun x => indicator (colors x p.1 = colors x p.2)) ≤ 1 := by
          have hs := mean_mono (fun x => indicator (colors x p.1 = colors x p.2))
            (fun _ => 1) (fun x => by
              change (if colors x p.1 = colors x p.2 then (1:ℚ) else 0) ≤ 1
              split <;> norm_num)
          rwa [mean_const] at hs
        simp only [indicator,if_pos hb] at *
        have h0 : 0 ≤ 1/(Fintype.card C : ℚ) := by positivity
        exact (sub_le_self _ h0).trans hh
      · rw [good p hb,sub_self]
        simp [indicator,hb]
    _ = _ := by
      unfold indicator
      have hh := Finset.sum_filter (s := (Finset.univ : Finset (A×A)))
        (p := fun x => x ∈ bad) (f := fun _ => (1:ℚ))
      rw [Finset.filter_univ_mem] at hh
      have hones : (∑ _p ∈ bad, (1:ℚ)) = (bad.card:ℚ) := by simp
      calc
        _ = ∑ p : A×A, @ite ℚ (p ∈ bad) (Finset.decidableMem p bad) 1 0 := by
          apply Finset.sum_congr rfl
          intro p _
          by_cases hp : p ∈ bad <;> simp [hp]
        _ = _ := hh.symm.trans hones

/-- Two distinct primitive coordinates give exact coincidence probability
inverse alphabet size, with no full-words hypothesis. -/
theorem independent_coincidence {P D : Type*} [Fintype P] [DecidableEq P]
    [Fintype D] [Nonempty D] (p q : P) (hne : q ≠ p) :
    mean (fun x : P→D => indicator (x p = x q)) = 1/(Fintype.card D : ℚ) := by
  have hs (x : P→D) : indicator (x p = x q) =
      ∑ d : D, indicator (x p = d)*indicator (x q = d) := by
    rw [Finset.sum_eq_single_of_mem (x p) (Finset.mem_univ _)]
    · simp [indicator,eq_comm]
    · intro d _ hd
      simp [indicator,Ne.symm hd]
  have he : mean (fun x : P→D => indicator (x p=x q)) =
      mean (fun x : P→D => ∑ d, indicator (x p=d)*indicator (x q=d)) :=
    congrArg (fun f : (P→D)→ℚ => mean f) (funext hs)
  rw [he,mean_sum]
  have hind (d : D) :
      mean (fun x : P→D => indicator (x p=d)*indicator (x q=d)) =
        mean (fun a : D => indicator (a=d)) * mean (fun a : D => indicator (a=d)) :=
    mean_coordinates_mul p q hne (fun a => indicator (a=d)) (fun a => indicator (a=d))
  simp_rw [hind]
  have hcol (d : D) : mean (fun a : D => indicator (a=d)) = 1/(Fintype.card D : ℚ) := by
    simp [mean,indicator]
  simp_rw [hcol]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hd : (Fintype.card D : ℚ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card D ≠ 0)
  field_simp

/-- A finite diagonal set of ordered pairs retaining just the self-pairs. -/
def samePairs [Fintype A] : Finset (A×A) :=
  Finset.univ.map ⟨fun a => (a,a),fun _ _ h => congrArg Prod.fst h⟩

theorem mem_samePairs [Fintype A] (p : A×A) : p ∈ samePairs ↔ p.1 = p.2 := by
  constructor
  · intro h
    obtain ⟨p,_,rfl⟩ := Finset.mem_map.mp h
    rfl
  · intro h
    exact Finset.mem_map.mpr ⟨p.1,Finset.mem_univ _,Prod.ext rfl h⟩

theorem samePairs_card [Fintype A] : (samePairs (A := A)).card = Fintype.card A := by
  simp [samePairs]

section Original
universe i s e vv f b
variable {I : Type i} {S : Type s} {E : Type e} {V : Type vv} {F : Type f} {B : Type b}
variable [Fintype I] [DecidableEq I] [Fintype S] [Nonempty S]
variable [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F] [Fintype B] [DecidableEq B]

def variableCost (cfg : Primitive V F B I → S) : ℚ :=
  ∑ t : I, deviation (fun v : V => J1MainSourceLabels.variableWord cfg v t)

/-- The actual Xi expectation is at most Q times the number of variables.
No source tie alters the left-side primitive symbols. -/
theorem expected_variableCost :
    mean (variableCost (V := V) (F := F) (B := B) (I := I) (S := S)) ≤
      (Fintype.card I : ℚ) * (Fintype.card V : ℚ) := by
  unfold variableCost
  rw [mean_sum]
  have h (t : I) :
      mean (fun cfg : Primitive V F B I → S =>
        deviation (fun v : V => J1MainSourceLabels.variableWord cfg v t)) ≤ Fintype.card V := by
    rw [←samePairs_card]
    apply expected_deviation_bad_pairs _ samePairs
    intro p hp
    have hneq : p.2 ≠ p.1 := fun h => hp ((mem_samePairs p).2 h.symm)
    exact independent_coincidence
      (Sum.inl (p.1,t) : Primitive V F B I) (Sum.inl (p.2,t))
      (by simp [hneq])
  have hh := Finset.sum_le_sum (s := (Finset.univ : Finset I)) (fun t _ => h t)
  simpa [nsmul_eq_mul] using hh
end Original

#print axioms deviation_eq_pairs
#print axioms expected_deviation_bad_pairs
#print axioms independent_coincidence
#print axioms expected_variableCost

section Incidences
universe ii ss ee vv' ff bb
variable {I : Type ii} {S : Type ss} {E : Type ee} {V : Type vv'} {F : Type ff} {B : Type bb}
variable [Fintype I] [DecidableEq I] [Fintype S] [Nonempty S]
variable [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F] [Fintype B] [DecidableEq B]

def twoDistinct {T : Type*} (x y : T) (h : x ≠ y) : Bool ↪ T where
  toFun b := if b then y else x
  inj' := by intro a b hh; cases a <;> cases b <;> simp_all

def literalCell (special : I) (tie : F → Option B) (var : E → V) (fac : E → F)
    (cfg : Primitive V F B I → S) (e : E) : Draw I S :=
  (J1MainSourceLabels.variableWord cfg (var e),factorWord special tie cfg (fac e))

/-- For two non-adjacent, non-tied physical incidences, the actual pair of
ordered words occupies independent Cartesian blocks, so its equality
probability is exactly inverse cell count. -/
theorem original_cells_coincide (special : I) (tie : F → Option B)
    (var : E → V) (fac : E → F) (e e' : E)
    (hv : var e ≠ var e') (hf : fac e ≠ fac e')
    (ht : ¬∃ b, tie (fac e) = some b ∧ tie (fac e') = some b) :
    mean (fun cfg : Primitive V F B I → S =>
      indicator (literalCell special tie var fac cfg e = literalCell special tie var fac cfg e')) =
        1/(Fintype.card (Draw I S) : ℚ) := by
  let pv := twoDistinct (var e) (var e') hv
  let pf := twoDistinct (fac e) (fac e') hf
  have hblock : ∀ a a' b, tie (pf a) = some b → tie (pf a') = some b → a = a' := by
    intro a a' b ha hb
    cases a <;> cases a'
    · rfl
    · exact False.elim (ht ⟨b,ha,hb⟩)
    · exact False.elim (ht ⟨b,hb,ha⟩)
    · rfl
  let key : Bool × Bool × I ↪ Primitive V F B I :=
    ⟨drawKey special tie pv pf,drawKey_injective special tie pv pf hblock⟩
  let Tail := {p // p ∉ Set.range key} → S
  letI : Fintype Tail := Fintype.ofFinite Tail
  letI : Nonempty Tail := ⟨fun _ => Classical.choice inferInstance⟩
  let split := chart (S := S) key
  let h : (Bool → Draw I S) → ℚ := fun p => indicator (p false = p true)
  let H : (Bool → Draw I S) × Tail → ℚ := fun p => h p.1
  have point (cfg : Primitive V F B I → S) (a : Bool) :
      (split cfg).1 a =
      literalCell special tie var fac cfg (if a then e' else e) := by
    apply Prod.ext
    · funext t
      rw [(chart_first_of_key key cfg a t).1]
      cases a <;> rfl
    · funext t
      rw [(chart_first_of_key key cfg a t).2]
      cases a <;> rfl
  have hfn :
      (fun cfg : Primitive V F B I → S => indicator
        (literalCell special tie var fac cfg e = literalCell special tie var fac cfg e')) =
        fun cfg => H (split cfg) := by
    funext cfg
    unfold H h
    rw [point cfg false,point cfg true]
    rfl
  rw [hfn,mean_equiv split H,show mean H = mean h from mean_extra h]
  exact independent_coincidence (D := Draw I S) false true (by decide)

variable [Fintype E]

def badPairs (tie : F → Option B) (var : E → V) (fac : E → F) : Finset (E×E) :=
  Finset.univ.filter (fun p => var p.1 = var p.2 ∨ fac p.1 = fac p.2 ∨
    ∃ b, tie (fac p.1) = some b ∧ tie (fac p.2) = some b)

def incidenceCost (special : I) (tie : F → Option B) (var : E → V) (fac : E → F)
    (cfg : Primitive V F B I → S) : ℚ :=
  deviation (literalCell special tie var fac cfg)

theorem expected_incidenceCost (special : I) (tie : F → Option B) (var : E → V) (fac : E → F) :
    mean (incidenceCost (S := S) special tie var fac) ≤ (badPairs tie var fac).card := by
  apply expected_deviation_bad_pairs (literalCell special tie var fac) (badPairs tie var fac)
  intro p hp
  have hs : ¬ (var p.1 = var p.2 ∨ fac p.1 = fac p.2 ∨
      ∃ b, tie (fac p.1) = some b ∧ tie (fac p.2) = some b) := by
    simpa [badPairs] using hp
  exact original_cells_coincide special tie var fac p.1 p.2
    (fun h => hs (Or.inl h)) (fun h => hs (Or.inr (Or.inl h)))
    (fun h => hs (Or.inr (Or.inr h)))
end Incidences

#print axioms original_cells_coincide
#print axioms expected_incidenceCost


section PairCount
variable {E V F B : Type*} [Fintype E] [DecidableEq E]
  [DecidableEq V] [DecidableEq F] [DecidableEq B]

def varFibre (var : E → V) (v : V) : Finset E :=
  Finset.univ.filter (fun e => var e = v)

def facFibre (fac : E → F) (f : F) : Finset E :=
  Finset.univ.filter (fun e => fac e = f)

def tagFibre (tag : E → Option B) (b : B) : Finset E :=
  Finset.univ.filter (fun e => tag e = some b)

def tiedSlots (tag : E → Option B) : Finset E :=
  Finset.univ.filter (fun e => (tag e).isSome)

def badNeighbors (tag : E → Option B) (var : E → V) (fac : E → F) (e : E) : Finset E :=
  (varFibre var (var e) ∪ (facFibre fac (fac e)).erase e) ∪
    ((tag e).elim ∅ (fun b => (tagFibre tag b).erase e))

theorem bad_neighbor_exists (tie : F → Option B) (var : E → V) (fac : E → F) (e e' : E) :
    (e,e') ∈ badPairs tie var fac ↔ e' ∈ badNeighbors (tie ∘ fac) var fac e := by
  by_cases he : e' = e
  · subst e'
    simp [badPairs,badNeighbors,varFibre]
  · cases hh : tie (fac e) <;>
      simp [badPairs,badNeighbors,varFibre,facFibre,tagFibre,he,hh,eq_comm]

theorem bad_pair_count (tie : F → Option B) (var : E → V) (fac : E → F) (N : ℕ)
    (hv : ∀ v, (varFibre var v).card ≤ 3)
    (hf : ∀ f, (facFibre fac f).card ≤ 2)
    (ht : ∀ b, (tagFibre (tie ∘ fac) b).card ≤ 3)
    (hn : (tiedSlots (tie ∘ fac)).card ≤ N) :
    (badPairs tie var fac).card ≤ 4*Fintype.card E+2*N := by
  let tag := tie ∘ fac
  have hb (e : E) : (badNeighbors tag var fac e).card ≤
      4 + 2*(if e ∈ tiedSlots tag then 1 else 0) := by
    have hfac : ((facFibre fac (fac e)).erase e).card ≤ 1 := by
      have he : e∈facFibre fac (fac e) := by simp [facFibre]
      rw [Finset.card_erase_of_mem he]
      have hh := hf (fac e)
      omega
    have hvar := hv (var e)
    have hsum :
        (badNeighbors tag var fac e).card ≤ 4 +
          ((tag e).elim ∅ (fun b => (tagFibre tag b).erase e)).card := by
      unfold badNeighbors
      exact (Finset.card_union_le _ _).trans (Nat.add_le_add_right
        ((Finset.card_union_le _ _).trans (by omega)) _)
    cases he : tag e with
    | none => simpa [tiedSlots,he] using hsum
    | some b =>
      have hm : e ∈ tagFibre tag b := by simp [tagFibre,he]
      have he' : ((tagFibre tag b).erase e).card ≤ 2 := by
        rw [Finset.card_erase_of_mem hm]
        have hh : (tagFibre tag b).card ≤ 3 := ht b
        omega
      simp only [he,Option.elim_some] at hsum
      have hb' := hsum.trans (Nat.add_le_add_left he' 4)
      simpa [tiedSlots,he] using hb'
  have hcard : (badPairs tie var fac).card = ∑ e : E, (badNeighbors tag var fac e).card := by
    have hs : badPairs tie var fac =
        Finset.univ.filter (fun p : E×E => p.2 ∈ badNeighbors tag var fac p.1) := by
      ext q
      exact (bad_neighbor_exists tie var fac q.1 q.2).trans (by simp [tag])
    rw [hs,Finset.card_filter,Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro e _
    have hs' := Finset.card_filter (s := (Finset.univ : Finset E))
       (p := fun e' => e' ∈ badNeighbors tag var fac e)
    rw [Finset.filter_univ_mem] at hs'
    exact hs'.symm
  have hs : (∑ e : E, if e ∈ tiedSlots tag then (1:ℕ) else 0) = (tiedSlots tag).card := by
    have h := Finset.card_filter (s := (Finset.univ : Finset E)) (p := fun e => e ∈ tiedSlots tag)
    rw [Finset.filter_univ_mem] at h
    exact h.symm
  calc
    (badPairs tie var fac).card = ∑ e : E, (badNeighbors tag var fac e).card := hcard
    _ ≤ ∑ e : E, (4+2*(if e ∈ tiedSlots tag then 1 else 0)) :=
      Finset.sum_le_sum (fun e _ => hb e)
    _ = 4 * Fintype.card E + 2 * (tiedSlots tag).card := by
      rw [Finset.sum_add_distrib,←Finset.mul_sum,hs]
      simp [Nat.mul_comm]
    _ ≤ _ := Nat.add_le_add_left (Nat.mul_le_mul_left 2 hn) _


end PairCount

#print axioms bad_neighbor_exists
#print axioms bad_pair_count


section MainBudget
universe i' s' e' v' f' b'
variable {I : Type i'} {S : Type s'} {E : Type e'} {V : Type v'} {F : Type f'} {B : Type b'}
variable [Fintype I] [DecidableEq I] [Fintype S] [Nonempty S]
variable [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F] [Fintype B] [DecidableEq B]
variable [Fintype E] [DecidableEq E]

/-- The printed J1 coefficient 4M+2N now follows from the original
random keys and just the actual degree and tied-block size constraints. -/
theorem expected_main_phi (special : I) (tie : F → Option B) (var : E → V) (fac : E → F)
    (N : ℕ)
    (hv : ∀ v, (varFibre var v).card ≤ 3)
    (hf : ∀ f, (facFibre fac f).card ≤ 2)
    (ht : ∀ b, (tagFibre (tie ∘ fac) b).card ≤ 3)
    (hn : (tiedSlots (tie ∘ fac)).card ≤ N) :
    mean (incidenceCost (S := S) special tie var fac) ≤
      4*(Fintype.card E : ℚ)+2*(N:ℚ) := by
  refine (expected_incidenceCost special tie var fac).trans ?_
  exact_mod_cast bad_pair_count tie var fac N hv hf ht hn

end MainBudget

#print axioms expected_main_phi


end
end J1MainSourceCollision
