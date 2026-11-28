import MainIncidence
import Mathlib.Tactic

/-! Exact minimal on-cut representation length, additive across a
fixed readout of different native coefficients without treating those
per-use costs as actual execution charges. -/
namespace P5MainBalance
open scoped BigOperators Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

def CutLengthWitness (S : Finset V) (f : (V→Bool)→ℚ) (n : ℕ) : Prop :=
  ∃ pieces : Fin n→SeparatedRank.VertexTerm V ℚ,
    (∀ p,(pieces p).side=S) ∧ ∀ σ,f σ=∑ p,(pieces p).value σ

def deltaPiece (S : Finset V) (f : (V→Bool)→ℚ) (σ : V→Bool) :
    SeparatedRank.VertexTerm V ℚ where
  side := S
  coeff := f σ
  onCut x := if x=SeparatedRank.CutTerm.restrict S σ then 1 else 0
  offCut x := if x=SeparatedRank.CutTerm.restrict Sᶜ σ then 1 else 0

theorem restrict_complement_identifies (S : Finset V) (σ ρ : V→Bool)
    (h₁ : SeparatedRank.CutTerm.restrict S σ=SeparatedRank.CutTerm.restrict S ρ)
    (h₂ : SeparatedRank.CutTerm.restrict Sᶜ σ=SeparatedRank.CutTerm.restrict Sᶜ ρ) : σ=ρ := by
  funext v
  by_cases h : v∈S
  · exact congrFun h₁ ⟨v,h⟩
  · exact congrFun h₂ ⟨v,Finset.mem_compl.mpr h⟩

theorem deltaPiece_value (S : Finset V) (f : (V→Bool)→ℚ) (σ ρ : V→Bool) :
    (deltaPiece S f σ).value ρ = if ρ=σ then f σ else 0 := by
  by_cases h : ρ=σ
  · subst ρ; simp [deltaPiece,SeparatedRank.VertexTerm.value]
  rw [if_neg h]
  by_cases h₁ : SeparatedRank.CutTerm.restrict S ρ=SeparatedRank.CutTerm.restrict S σ
  · have h₂ : SeparatedRank.CutTerm.restrict Sᶜ ρ≠SeparatedRank.CutTerm.restrict Sᶜ σ :=
      fun he=>h (restrict_complement_identifies S ρ σ h₁ he)
    simp [deltaPiece,SeparatedRank.VertexTerm.value,h₂]
  · simp [deltaPiece,SeparatedRank.VertexTerm.value,h₁]

theorem cut_length_exists (S : Finset V) (f : (V→Bool)→ℚ) :
    ∃ n,CutLengthWitness S f n := by
  let e := Fintype.equivFin (V→Bool)
  refine ⟨_,fun i=>deltaPiece S f (e.symm i),fun _=>rfl,?_⟩
  intro σ
  rw [e.symm.sum_comp (fun ρ => (deltaPiece S f ρ).value σ)]
  simp_rw [deltaPiece_value]
  rw [Finset.sum_eq_single σ]
  · simp
  · intro ρ _ hr
    simp [Ne.symm hr]
  · simp

noncomputable def cutLength (S : Finset V) (f : (V→Bool)→ℚ) : ℕ :=
  Nat.find (cut_length_exists S f)

theorem cut_length_achieved (S : Finset V) (f : (V→Bool)→ℚ) :
    CutLengthWitness S f (cutLength S f) :=
  Nat.find_spec (cut_length_exists S f)

theorem cut_length_minimal (S : Finset V) (f : (V→Bool)→ℚ) (n : ℕ)
    (h : CutLengthWitness S f n) : cutLength S f≤n :=
  Nat.find_min' (cut_length_exists S f) h

def scaleTerm (w : ℚ) (p : SeparatedRank.VertexTerm V ℚ) : SeparatedRank.VertexTerm V ℚ :=
  { p with coeff := w*p.coeff }

theorem scaleTerm_value (w : ℚ) (p : SeparatedRank.VertexTerm V ℚ) (σ : V→Bool) :
    (scaleTerm w p).value σ = w*p.value σ := by unfold scaleTerm SeparatedRank.VertexTerm.value; ring

section Aggregate

variable {A I P B : Type*} [Fintype A] [Fintype I] [DecidableEq I] [Nonempty I]
  [Fintype P] [Fintype B] [DecidableEq B] [Nonempty B] [Nonempty V]
  {G : Finset (V×V)} {pin : V ↪ P} {cell : P→(I→B) × (I→B)} {C : ℕ}

set_option maxHeartbeats 5000000 in
theorem fixed_readout_coefficient_budget (L : MainIncidence.Layout G pin cell C)
    (hsize : 7776*(Fintype.card I:ℚ)*(4*C*(Fintype.card I:ℚ))/
      (FiniteGrowth.coefficient L.gamma (1/4))^2 < Fintype.card V)
    {R S : Type*} [CommRing R] [CommRing S] [Nontrivial S]
    (embed : R→+*ℚ) (residue : R→+*S) (hein : Function.Injective embed)
    (output : (V→Bool)→R) (K : A→(V→Bool)→ℚ) (node : A→I) (weight : A→ℚ)
    (hread : ∀ σ,embed (output σ)=∑ a,weight a*K a σ)
    (hcorrect : ∀ σ,residue (output σ)=(PinnedCNF.modelCount (PinnedCNF.formula G σ):S)) :
    ∃ d : ℕ, (FiniteGrowth.coefficient L.gamma (1/4)*Fintype.card V)^2 ≤
      16*(C:ℚ)*(Fintype.card I:ℚ)*(d:ℚ)^2 ∧
      2^d≤∑ a,cutLength (EmpiricalCutMoments.labelCut
        (MainIncidence.labels pin cell) id L.symbols (node a)) (K a) := by
  let side (a : A) := EmpiricalCutMoments.labelCut
    (MainIncidence.labels pin cell) id L.symbols (node a)
  let r (a : A) := cutLength (side a) (K a)
  choose p hp hre using fun a : A => cut_length_achieved (side a) (K a)
  let T := Σ a:A, Fin (r a)
  let pieces (z : T) := scaleTerm (weight z.1) (p z.1 z.2)
  have hs (z : T) : (pieces z).side=side z.1 := hp z.1 z.2
  have hv (σ : V→Bool) : embed (output σ)=∑ z : T,(pieces z).value σ := by
    rw [hread,Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro a _
    rw [hre a σ,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    exact (scaleTerm_value _ _ _).symm
  obtain ⟨d,hd,hcard⟩ := MainIncidence.main_modular_cut_barrier L hsize embed residue hein output
    pieces (fun z=>node z.1) hs hv hcorrect
  refine ⟨d,hd,?_⟩
  simpa only [T,r,Fintype.card_sigma,Fintype.card_fin,side] using hcard

end Aggregate

#print axioms restrict_complement_identifies
#print axioms deltaPiece_value
#print axioms cut_length_exists
#print axioms cut_length_achieved
#print axioms cut_length_minimal
#print axioms fixed_readout_coefficient_budget
end P5MainBalance
