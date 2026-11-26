import SolverPacketProduct

noncomputable section
namespace RootSeparation.Solver
open Classical
open scoped BigOperators
set_option linter.unusedSectionVars false

variable {P R : Type*} [Fintype P] [CommSemiring R]
variable {Rows Modes : P → Type*} [∀ k, Fintype (Rows k)] [∀ k, Fintype (Modes k)]

def combineChoices (c : ∀ p, Rows p → Option (Modes p)) (r : Σ p, Rows p) :
    Option (Σ p, Modes p) :=
  (c r.1 r.2).map (Sigma.mk r.1)

def ChoiceFits (c : (Σ p, Rows p) → Option (Σ p, Modes p)) : Prop :=
  ∀ r z, c r = some z → z.1 = r.1

private theorem combine_fits (c : ∀ p, Rows p → Option (Modes p)) :
    ChoiceFits (combineChoices c) := by
  intro r z h
  unfold combineChoices at h
  obtain ⟨k,_,rfl⟩ := Option.map_eq_some_iff.1 h
  rfl

private def splitChoice {p : P} (o : Option (Σ p, Modes p))
    (h : ∀ z, o = some z → z.1 = p) : Option (Modes p) :=
  match o with
  | none => none
  | some z => some (h z rfl ▸ z.2)

private theorem splitChoice_map {p : P} (o : Option (Σ p, Modes p))
    (h : ∀ z, o = some z → z.1 = p) :
    (splitChoice o h).map (Sigma.mk p) = o := by
  cases o with
  | none => rfl
  | some z =>
    obtain ⟨k,z⟩ := z
    have e : k = p := h ⟨k,z⟩ rfl
    subst k
    rfl

private theorem splitChoice_left {p : P} (q : Option (Modes p))
    (h : ∀ z, q.map (Sigma.mk p) = some z → z.1 = p) :
    splitChoice (q.map (Sigma.mk p)) h = q := by
  cases q <;> rfl

private def choiceEquiv : (∀ p, Rows p → Option (Modes p)) ≃
    {c : (Σ p, Rows p) → Option (Σ p, Modes p) // ChoiceFits c} where
  toFun c := ⟨combineChoices c,combine_fits c⟩
  invFun c p r := splitChoice (c.val ⟨p,r⟩) (c.property ⟨p,r⟩)
  left_inv c := by
    funext p r
    change splitChoice ((c p r).map (Sigma.mk p)) _ = c p r
    exact splitChoice_left _ _
  right_inv c := by
    apply Subtype.ext
    funext r
    exact splitChoice_map _ _

private def countChoicesEquiv (c : ∀ p, Rows p → Option (Modes p)) (p : P) (z : Modes p) :
    {r // combineChoices c r = some ⟨p,z⟩} ≃ {r // c p r = some z} := by
  refine (Equiv.ofBijective (fun r : {r // c p r = some z} =>
    (⟨⟨p,r.val⟩, by change (c p r.val).map (Sigma.mk p) = _; rw [r.property]; rfl⟩ :
      {r // combineChoices c r = some ⟨p,z⟩})) ?_).symm
  constructor
  · intro r r' he
    have hh : (⟨p,r.val⟩ : Σ q, Rows q) = ⟨p,r'.val⟩ := congrArg Subtype.val he
    exact Subtype.ext ((Sigma.mk.inj_iff.1 hh).2.eq)
  · rintro ⟨⟨k,r⟩,hr⟩
    change (c k r).map (Sigma.mk k) = some ⟨p,z⟩ at hr
    obtain ⟨z',hz',he⟩ := Option.map_eq_some_iff.1 hr
    have hk := congrArg Sigma.fst he
    dsimp only at hk
    subst k
    have hzz : z' = z := (Sigma.mk.inj_iff.1 he).2.eq
    subst z'
    exact ⟨⟨r,hz'⟩,rfl⟩

theorem countChoices_packet (c : ∀ p, Rows p → Option (Modes p)) (p : P) (z : Modes p) :
    Fintype.card {r // combineChoices c r = some ⟨p,z⟩} =
      Fintype.card {r // c p r = some z} :=
  Fintype.card_congr (countChoicesEquiv c p z)

def globalRow (rows : ∀ p, Rows p → Option (Modes p) → R)
    (r : Σ p, Rows p) : Option (Σ p, Modes p) → R
  | none => rows r.1 r.2 none
  | some z => if h : z.1 = r.1 then rows r.1 r.2 (some (h ▸ z.2)) else 0

theorem globalRow_combine (rows : ∀ p, Rows p → Option (Modes p) → R)
    (c : ∀ p, Rows p → Option (Modes p)) (p : P) (r : Rows p) :
    globalRow rows ⟨p,r⟩ (combineChoices c ⟨p,r⟩) = rows p r (c p r) := by
  unfold combineChoices
  dsimp only
  cases c p r with
  | none => rfl
  | some z => simp [globalRow]

set_option maxHeartbeats 1800000 in
theorem packetCoeff_split (rows : ∀ p, Rows p → Option (Modes p) → R)
    (β : ∀ p, Modes p → ℕ) :
    packetCoeff (globalRow rows) (fun z => β z.1 z.2) =
      ∏ p, packetCoeff (rows p) (β p) := by
  classical
  rw [packetCoeff_product]
  letI : DecidableEq (Σ p, Modes p) := fun a b => Classical.propDecidable (a = b)
  let A := (Σ p, Rows p) → Option (Σ p, Modes p)
  letI : Fintype A := @Pi.instFintype (Σ p, Rows p) (fun _ => Option (Σ p, Modes p))
    (fun a b => Classical.propDecidable (a = b)) inferInstance (fun _ => inferInstance)
  let term (c : A) : R :=
    if ∀ z, Fintype.card {r // c r = some z} = β z.1 z.2 then
      ∏ r, globalRow rows r (c r) else 0
  have hterm : (∑ c : A, term c) = packetCoeff (globalRow rows) (fun z => β z.1 z.2) := by
    unfold packetCoeff
    apply Finset.sum_congr (Finset.ext fun _ => by simp)
    intro c _
    unfold term
    split_ifs <;> rfl
  rw [← hterm]
  have hzero (c : A) (h : ¬ ChoiceFits c) : term c = 0 := by
    unfold term
    split
    · unfold ChoiceFits at h
      push_neg at h
      obtain ⟨r,z,he,hn⟩ := h
      exact Finset.prod_eq_zero (Finset.mem_univ r) (by rw [he,globalRow,dif_neg hn])
    · rfl
  trans ∑ c : {c : A // ChoiceFits c}, term c.val
  · rw [← Finset.sum_subtype (p := fun c : A => ChoiceFits c)
      (Finset.univ.filter (fun c : A => ChoiceFits c)) (fun x => by simp) term]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro c _
    split
    · rfl
    · exact hzero c (by assumption)
  · symm
    apply Fintype.sum_equiv choiceEquiv
    intro c
    change _ = term (combineChoices c)
    unfold term
    have h : (∀ z : Σ p, Modes p,
        Fintype.card {r // combineChoices c r = some z} = β z.1 z.2) ↔
      (∀ p z, Fintype.card {r // c p r = some z} = β p z) := by
      constructor
      · intro h p z
        exact (Fintype.card_congr (countChoicesEquiv c p z).symm).trans (h ⟨p,z⟩)
      · rintro h ⟨p,z⟩
        exact (Fintype.card_congr (countChoicesEquiv c p z)).trans (h p z)
    by_cases hc : ∀ p z, Fintype.card {r // c p r = some z} = β p z
    · rw [if_pos hc, if_pos (h.mpr hc), Fintype.prod_sigma]
      simp only [globalRow_combine]
    · rw [if_neg hc, if_neg (fun hg => hc (h.mp hg))]

end RootSeparation.Solver

#print axioms RootSeparation.Solver.countChoices_packet
#print axioms RootSeparation.Solver.packetCoeff_split
