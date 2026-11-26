import P5MainBalanceLayout
import P5MainBalanceSize
import Mathlib.Data.ZMod.Basic

/-! M.4 for the actual frozen sign-owner chart and literal printed
r,Q schedule. In particular a global sign function is not given to
an arbitrary group for free: the finite proof needs its balanced cut. -/
namespace P5MainBalance
open scoped BigOperators Classical
open Filter

set_option maxHeartbeats 11200000 in
theorem eventual_physical_M4 (a C : ℕ) (ha : 0<a) (hC : 0<C)
    (γ : ℚ) (hγ : 0<γ) (hγ1 : γ≤1) :
    ∀ᶠ n : ℕ in atTop,
      ∀ {V U E F Copy T : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
        [Fintype E] [Fintype T],
      ∀ (graph : Finset (V×V))
        (L : P5MainIterator.SourceLayout E U F Copy (Fin (mainNodes n)) (Fin (mainAlphabet n)))
        (mark : V↪E),
        n≤a*Fintype.card V →
        0<mainNodes n →
        2*Fintype.card E≤C*Fintype.card V →
        (∀ u,P5MainIterator.cellLoad L u*Fintype.card (P5MainIterator.WordCell
          (Fin (mainNodes n)) (Fin (mainAlphabet n)))≤2*Fintype.card E) →
        (∀ v,(v,v)∉graph) →
        (∀ v,GraphCutMoments.degree graph v=3) →
        (∀ U : Finset V,γ*(min U.card (Fintype.card V-U.card) : ℕ)≤
          ((GraphCutMoments.boundary graph U).card:ℚ)) →
        ∀ (out : (V→Bool)→ℤ)
          (pieces : T→GroupProducts.GroupTerm (MainIncidence.labels mark (realCell L)) ℚ),
        (∀ σ,(out σ:ℚ)=∑ t,(pieces t).value σ) →
        (∀ σ,(out σ:ZMod 2)=(PinnedCNF.modelCount (PinnedCNF.formula graph σ):ZMod 2)) →
        ∃ d : ℕ, (FiniteGrowth.coefficient γ (1/4)*Fintype.card V)^2≤
          16*(C:ℚ)*(mainNodes n:ℚ)*(d:ℚ)^2 ∧ 2^d≤Fintype.card T := by
  filter_upwards [printed_balance_threshold C,printed_thinning_threshold a C ha γ hγ] with n hr hsz
  intro V U E F Copy T _ _ _ _ _ graph L mark hN hQ hPorts hLoad hLoop hReg hExpand out pieces hRep hOut
  letI : Nonempty (Fin (mainNodes n)) := ⟨⟨0,hQ⟩⟩
  letI : Nonempty (Fin (mainAlphabet n)) := ⟨⟨0,by omega⟩⟩
  let G := layoutFromPhysical L mark graph C hC hPorts hLoad (by simpa only [Fintype.card_fin] using hr)
    hLoop hReg γ hγ hγ1 hExpand
  have hWide : 7776*(Fintype.card (Fin (mainNodes n)):ℚ)*(4*C*(Fintype.card (Fin (mainNodes n)):ℚ))/
      (FiniteGrowth.coefficient G.gamma (1/4))^2 < Fintype.card V := by
    simpa only [Fintype.card_fin,G,layoutFromPhysical] using hsz (Fintype.card V) hN
  have h := MainIncidence.main_modular_group_barrier G hWide
    (Int.castRingHom ℚ) (Int.castRingHom (ZMod 2))
    (Int.cast_injective) out pieces hRep hOut
  simpa only [Fintype.card_fin,G,layoutFromPhysical] using h

variable {V I B : Type*} [Fintype B]

/-- Without the per-node balanced sign union a single real group may read
the complete sign word. There is then a one-term representation of any
terminal function, not only the pinned CNF count. -/
noncomputable def collapsedOnlyGroup (L : V→I→B) (t : I) (a : B)
    (h : ∀ v,L v t=a) (F : (V→Bool)→ℚ) :
    GroupProducts.GroupTerm L ℚ where
  coordinate := t
  coeff := 1
  factor b x := if hb : a=b then F (fun v => x ⟨v,(h v).trans hb⟩) else 1

theorem collapsed_group_represents_everything (L : V→I→B) (t : I) (a : B)
    (h : ∀ v,L v t=a) (F : (V→Bool)→ℚ) (σ : V→Bool) :
    (collapsedOnlyGroup L t a h F).value σ=F σ := by
  unfold GroupProducts.GroupTerm.value
  rw [show (collapsedOnlyGroup L t a h F).coeff=1 from rfl,one_mul]
  rw [Finset.prod_eq_single a]
  · simp [collapsedOnlyGroup]
  · intro b _ hne
    simp [collapsedOnlyGroup,Ne.symm hne]
  · simp

#print axioms eventual_physical_M4
#print axioms collapsed_group_represents_everything
end P5MainBalance
