import LayerRecovery
import Mathlib.Tactic

/-! A negative unary and a free unary meet one binary subdivision.
Their physical successor ports may lie in arbitrary different
packets. The exact padding factor depends only on the incoming
number of matched negative rows, never on adjacent seats. -/
namespace J6OrientedPadding
open scoped BigOperators Polynomial
variable {D : Type*} [Fintype D] [DecidableEq D]

abbrev P (D : Type*) := D×Bool

def incoming (shift : P D → Option (P D)) (p : P D) : Option D :=
  if p.2 then none else (shift p).map Prod.fst

def count (shift : P D → Option (P D)) (d : D) : ℕ :=
  (Finset.univ.filter (fun p => incoming shift p = some d)).card

theorem count_le_two (shift : P D → Option (P D))
    (hi : ∀ p r q, shift p=some q → shift r=some q → p=r) (d : D) :
    count shift d ≤ 2 := by
  classical
  let s := Finset.univ.filter (fun p => incoming shift p = some d)
  have h (p : P D) (hp : p∈s) :
      ∃ side, shift p=some (d,side) := by
    have hm := (Finset.mem_filter.mp hp).2
    cases hb : p.2
    · cases hs : shift p with
      | none => simp [incoming,hb,hs] at hm
      | some q =>
        rcases q with ⟨e,bit⟩
        have he : e = d := by simpa [incoming,hb,hs] using hm
        subst e
        exact ⟨bit,rfl⟩
    · simp [incoming,hb] at hm
  have hb : s.card ≤ (Finset.univ : Finset Bool).card := by
    apply Finset.card_le_card_of_injOn (fun p => ((shift p).map Prod.snd).getD false)
    · intro _ _
      exact Finset.mem_univ _
    · intro p hp r hr he
      obtain ⟨u,hu⟩ := h p hp
      obtain ⟨v,hv⟩ := h r hr
      simp [hu,hv] at he
      subst v
      exact hi p r (d,u) hu hv
  simpa [count,s] using hb

noncomputable def contract (shift : P D → Option (P D)) (c : ℚ) : ℚ := by
  classical
  exact ∑ y : P D → Bool, ∑ x : P D → Bool,
    (if ∀ d : D, x (d,false)=x (d,true) then 1 else 0) *
    ∏ p, (if p.2 ∨ ¬y p then 1 else 0) *
      (LayerRecovery.wireFactor (y p) (((shift p).map x).getD false)).eval c

private theorem row_read (isFree v : Bool) (c : ℚ) :
    (∑ b : Bool, (if isFree ∨ ¬b then 1 else 0) *
      (LayerRecovery.wireFactor b v).eval c) =
      if !isFree && v then 1-c else 1 := by
  cases isFree <;> cases v <;> simp [LayerRecovery.wireFactor]

theorem factor_actual_padding (shift : P D → Option (P D)) (c : ℚ) :
    contract shift c = ∏ d, (1+(1-c)^count shift d) := by
  classical
  unfold contract
  rw [Finset.sum_comm]
  let good := fun x : P D → Bool => ∀ d : D, x (d,false)=x (d,true)
  let f := fun (x : P D → Bool) (p : P D) (bit : Bool) =>
    (if p.2 ∨ ¬bit then (1:ℚ) else 0) *
      (LayerRecovery.wireFactor bit (((shift p).map x).getD false)).eval c
  change (∑ x, ∑ y : P D → Bool, (if good x then (1:ℚ) else 0) * ∏ p, f x p (y p)) = _
  let F : (P D → Bool) → ℚ := fun x =>
    ∏ p, if !p.2 && ((shift p).map x).getD false then 1-c else 1
  have hz (x : P D → Bool) :
      (∑ y : P D → Bool, (if good x then (1:ℚ) else 0) * ∏ p, f x p (y p)) =
      if good x then F x else 0 := by
    rw [← Finset.mul_sum,← Fintype.prod_sum (f x)]
    by_cases hg : good x
    · simp only [if_pos hg,one_mul,F]
      exact Finset.prod_congr rfl (fun p _ => row_read p.2 ((shift p).map x |>.getD false) c)
    · simp [hg]
  simp only [hz]
  rw [← Finset.sum_filter]
  let E : (D → Bool) ≃ ↥(Finset.univ.filter good) :=
    { toFun := fun z => ⟨fun p => z p.1,by simp [good]⟩
      invFun := fun x d => x.val (d,false)
      left_inv := fun _ => rfl
      right_inv := by
        intro x
        apply Subtype.ext
        funext p
        rcases p with ⟨d,side⟩
        cases side
        · rfl
        · exact (Finset.mem_filter.mp x.property).2 d }
  change (∑ x ∈ Finset.univ.filter good, F x)=_
  rw [← Finset.sum_attach]
  change (∑ x : ↥(Finset.univ.filter good), F x.val)=_
  rw [← Equiv.sum_comp E (fun x => F x.val)]
  have hF (z : D → Bool) :
      F (fun p => z p.1) =
        ∏ d : D, (if z d then 1-c else 1)^count shift d := by
    unfold F
    have he (p : P D) :
        (if !p.2 && ((shift p).map (fun q => z q.1)).getD false then 1-c else 1) =
          (if ((incoming shift p).map z).getD false then 1-c else 1) := by
      cases bh : p.2 <;> cases hs : shift p <;> simp [incoming,bh,hs]
    simp only [he]
    rw [← Finset.prod_fiberwise' Finset.univ (incoming shift)
      (fun v => if (v.map z).getD false then 1-c else 1)]
    simp [Fintype.prod_option,count]
  have hE (z : D → Bool) : (E z).val=fun p => z p.1 := rfl
  simp only [hE,hF]
  rw [← Fintype.prod_sum (fun (d:D) (u:Bool) => (if u then 1-c else 1)^count shift d)]
  exact Finset.prod_congr rfl fun d _ => LayerRecovery.padding_column_factor c (count shift d)

#print axioms count_le_two
#print axioms factor_actual_padding
end J6OrientedPadding
