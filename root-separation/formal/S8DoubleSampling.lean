import S8CertifiedPlacement
import S8Simple

namespace S8

open scoped BigOperators
open SourceDensity

section Neighbors
variable {V W G H : Type*} [Fintype V] [Fintype W] [DecidableEq W]

theorem pinNeighbors_characterize {J : Type*} [Fintype J] [DecidableEq J]
    (pin : V ↪ W) (owner : V ≃ G × J) (e f : W) :
    f ∈ pinNeighbors pin owner e ↔ ∃ v w, pin v = e ∧ pin w = f ∧
      (owner v).1 = (owner w).1 ∧ v ≠ w := by
  classical
  by_cases h : ∃ v, pin v = e
  · obtain ⟨v,rfl⟩ := h
    constructor
    · rw [pinNeighbors_at, Finset.mem_map]
      rintro ⟨k,hk,rfl⟩
      refine ⟨v, owner.symm ((owner v).1,k), rfl, rfl, by simp, ?_⟩
      intro he
      have hk' := (Finset.mem_erase.mp hk).1
      exact hk' (by simpa using (congrArg (fun x => (owner x).2) he).symm)
    · rintro ⟨x,w,hx,rfl,g,diff⟩
      have hx' := pin.injective hx
      subst x
      exact pinNeighbors_mem pin owner v w g diff
  · rw [pinNeighbors, dif_neg h]
    exact ⟨fun he => (Finset.notMem_empty f he).elim, fun ⟨v,_,he,_⟩ => (h ⟨v,he⟩).elim⟩

noncomputable def doubleNeighbors (pin : V ↪ W) (tri : V ≃ G × Fin 3)
    (extm : V ≃ H × Bool) (w : W) : Finset W :=
  pinNeighbors pin tri w ∪ pinNeighbors pin extm w

/-- On the actual triangle replacement the extra ordered pairs are disjoint:
a distinct exterior mate belongs to a different triangle. -/
theorem doubleNeighbors_card (base : Finset (G × G))
    [Fintype G] [DecidableEq G] (reg : ∀ g, GraphCutMoments.degree base g = 3)
    (loopless : ∀ g, (g,g) ∉ base) (pin : Triangle.Vertex G ↪ W) :
    (∑ w, (doubleNeighbors pin (Equiv.refl _) (Triangle.exteriorOwner base reg) w).card) =
      3 * Fintype.card (Triangle.Vertex G) := by
  classical
  let tri := Equiv.refl (Triangle.Vertex G)
  let extm := Triangle.exteriorOwner base reg
  have hd (w : W) : Disjoint (pinNeighbors pin tri w) (pinNeighbors pin extm w) := by
    rw [Finset.disjoint_left]
    intro f htri hext
    obtain ⟨v,u,hv,hu,ht,hn⟩ := (pinNeighbors_characterize pin tri w f).1 htri
    obtain ⟨x,y,hx,hy,he,_⟩ := (pinNeighbors_characterize pin extm w f).1 hext
    have hx' := pin.injective (hx.trans hv.symm)
    have hy' := pin.injective (hy.trans hu.symm)
    subst x
    subst y
    let e := (extm v).1
    have hv₁ : Triangle.endpoint base reg e (extm v).2 = v := extm.symm_apply_apply v
    have hu₁ : Triangle.endpoint base reg e (extm u).2 = u := by
      change (extm v).1 = (extm u).1 at he
      rw [show e = (extm u).1 from he]
      exact extm.symm_apply_apply u
    have hb : (extm v).2 ≠ (extm u).2 := fun hb => hn (extm.injective (Prod.ext he hb))
    have hd' : e.1.1 ≠ e.1.2 := by
      rcases e with ⟨⟨a,b⟩,hab⟩
      rintro (rfl : a = b)
      exact loopless a hab
    have ht' : (Triangle.endpoint base reg e (extm v).2).1 =
        (Triangle.endpoint base reg e (extm u).2).1 :=
      (congrArg Prod.fst hv₁).trans (ht.trans (congrArg Prod.fst hu₁).symm)
    generalize (extm v).2 = b at hb ht'
    generalize (extm u).2 = c at hb ht'
    cases b <;> cases c
    · exact hb rfl
    · exact hd' ht'
    · exact hd' ht'.symm
    · exact hb rfl
  have hunion (w : W) : (doubleNeighbors pin tri extm w).card =
      (pinNeighbors pin tri w).card + (pinNeighbors pin extm w).card :=
    Finset.card_union_of_disjoint (hd w)
  change (∑ w, (doubleNeighbors pin tri extm w).card) = _
  simp_rw [hunion]
  rw [Finset.sum_add_distrib, pinNeighbors_sum, pinNeighbors_sum, Fintype.card_fin, Fintype.card_bool]
  omega
end Neighbors

section Sampling
variable {W X Y LX LY I A : Type*} [Fintype W] [DecidableEq W] [Fintype X] [DecidableEq X]
  [Fintype Y] [DecidableEq Y] [Fintype LX] [DecidableEq LX] [Fintype LY] [DecidableEq LY]
  [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A] [Nonempty A]

/-- Each coordinate has its own sharing map. The coordinate itself remains
part of the primitive index, preserving independence between tied coordinates. -/
def multiSite (left : W → X) (right : W → Y) (shareL : I → X → Option LX)
    (shareR : I → Y → Option LY) (w : W) (q : Bool × I) : Primitive X Y LX LY I :=
  site left right (shareL q.2) (shareR q.2) q.2 w q

def multiWords (left : W → X) (right : W → Y) (shareL : I → X → Option LX)
    (shareR : I → Y → Option LY) (ω : Primitive X Y LX LY I → A) (w : W) : (I → A) × (I → A) :=
  (fun i => ω (multiSite left right shareL shareR w (false,i)),
   fun i => ω (multiSite left right shareL shareR w (true,i)))

theorem multi_separate_sites (left : W → X) (right : W → Y) (shareL : I → X → Option LX)
    (shareR : I → Y → Option LY) (extra : W → Finset W)
    (extrasL : ∀ i e f z, shareL i (left e) = some z → shareL i (left f) = some z →
      left e ≠ left f → f ∈ extra e)
    (extrasR : ∀ i e f z, shareR i (right e) = some z → shareR i (right f) = some z →
      right e ≠ right f → f ∈ extra e)
    (e f : W) (good : (e,f) ∉ conflictPairs left right extra) :
    Function.Injective (Sum.elim (multiSite left right shareL shareR e)
      (multiSite left right shareL shareR f)) := by
  have aux (i : I) := separate_sites left right (shareL i) (shareR i) extra i
    (extrasL i) (extrasR i) e f good
  intro a b hab
  have coord (p : (Bool × I) ⊕ (Bool × I)) :
      (Sum.elim (multiSite left right shareL shareR e)
        (multiSite left right shareL shareR f) p).1 = Sum.elim Prod.snd Prod.snd p := by
    cases p <;> rfl
  have hi := congrArg Prod.fst hab
  rw [coord, coord] at hi
  apply aux (Sum.elim Prod.snd Prod.snd a)
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      change a.2 = b.2 at hi
      simpa only [Sum.elim_inl, multiSite, ← hi] using hab
    | inr b =>
      change a.2 = b.2 at hi
      simpa only [Sum.elim_inl, Sum.elim_inr, multiSite, ← hi] using hab
  | inr a =>
    cases b with
    | inl b =>
      change a.2 = b.2 at hi
      simpa only [Sum.elim_inl, Sum.elim_inr, multiSite, ← hi] using hab
    | inr b =>
      change a.2 = b.2 at hi
      simpa only [Sum.elim_inr, multiSite, ← hi] using hab

theorem multi_mean_words (left : W → X) (right : W → Y) (shareL : I → X → Option LX)
    (shareR : I → Y → Option LY) (bad : Finset (W × W))
    (good : ∀ e f, (e,f) ∉ bad → Function.Injective
      (Sum.elim (multiSite left right shareL shareR e) (multiSite left right shareL shareR f))) :
    (∑ ω : Primitive X Y LX LY I → A,
      ProductVariance.uniformWeight (Primitive X Y LX LY I → A) *
        collision (multiWords left right shareL shareR ω)) ≤ bad.card := by
  let toWords := (Equiv.curry Bool I A).trans (Equiv.boolArrowEquivProd (I → A))
  have h (ω : Primitive X Y LX LY I → A) :
      multiWords left right shareL shareR ω =
      toWords ∘ (fun w => ω ∘ multiSite left right shareL shareR w) := rfl
  simp only [h, collision_equiv]
  exact primitive_collision_bound _ bad good

end Sampling

#print axioms pinNeighbors_characterize
#print axioms doubleNeighbors_card
#print axioms multi_separate_sites
#print axioms multi_mean_words

end S8
