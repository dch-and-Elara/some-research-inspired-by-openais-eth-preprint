import P5D1LiteralTerms
import P5HybridClosureAffine

/-! The literal menu lower bound on the same common matching.
A paid trace with every literal root slot is a separate premise. -/
namespace Paper5.D1Literal
open scoped Classical Polynomial BigOperators
open Polynomial J6R10Repack J6R11Repack J6R11Blueprint J6ActiveRun 
  J6R12Blueprint J6R10Reachable J6R9Recursive J6R9PacketScopes
  P11FullPacking Paper5.HybridClosure J1PPrinted J6R12Integral
  GroupProducts SeparatedRank

variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W × W)) (cubic : ∀ v, GraphCutMoments.degree F v=3)
variable (f : ℤ[X])
local notation "S" => (printedParams (f:=f) (ell:=1) (oldRowSize F))
local notation "Δ" => sourceDelta (oldRowSize F)
local notation "r*" => (oldRowRoot F cubic f (fun _ => false))
variable (P : RootPacking F cubic f)

noncomputable def sourceModTwo : IntRing f 1 →+* NativeProbeRing.Residue f :=
  (NativeProbeRing.residueMap 1 (by decide) f).comp
    ((zeroCoordinate (NativeProbeRing.Scalar 1 f)).comp (reduce 1 f 1))

omit [DecidableEq W] in
theorem mod_two_of_count_at_creation (hf : f.Monic) {out : IntRing f 1} {k : ℕ}
    (h : reduce (4*Fintype.card W+1) f 1 out = (k : Residue f 1 (4*Fintype.card W+1))) :
    sourceModTwo f out = (k : NativeProbeRing.Residue f) := by
  have hc : (2 : IntRing f 1)^(4*Fintype.card W+1) ∣ out - (k : IntRing f 1) := by
    apply (reduce_zero_iff (4*Fintype.card W+1) f hf 1 _).mp
    rw [map_sub,h,map_natCast,sub_self]
  have hr := root_congruence_reduces_mod_two f hf 1 (4*Fintype.card W+1) (by omega) hc
  unfold sourceModTwo
  rw [RingHom.comp_apply,RingHom.comp_apply,hr]
  simp only [map_natCast]

set_option maxHeartbeats 20000000 in
theorem literal_menu_card_from_matching {I : Type} [Fintype I] [DecidableEq I]
    (cfg : RootBounds (oldRowSize F) 3 f) (hΔ : 3 ≤ Δ)
    (hf : f.Monic) (hF : 0 < f.natDegree) [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (d : Ready S Δ r*) (matching : PinnedCNF.InducedMatching F I)
    (symbols : rootKept F f → Finset (Fin 64))
    (D : ℕ) (small : D ≤ Fintype.card I)
    (gap : ∀ i, D ≤ endpointImbalance matching.endpoint
      (EmpiricalCutMoments.labelCut (rootLabels F cubic f P) id symbols i)) :
    2^D ≤ Fintype.card (PublicSlot F cubic f P d) := by
  classical
  letI : Fact (Irreducible (ratPoly f)) := ⟨source_rat_irreducible f hf Fact.out⟩
  let output : (W → Bool) → IntRing f 1 := fun σ =>
    (common_agenda_field_count F cubic f P cfg hΔ hf hF d σ).choose
  have repr (σ : W → Bool) :
      sourceFieldMap f (output σ) =
        (∑ t : Fin 0, ((fun t => Fin.elim0 t) t :
          GroupTerm (fun (_ : W) (_ : Unit) => ()) (RatScalar f)).value σ) +
        ∑ u : PublicSlot F cubic f P d, (agendaGroupTerm F cubic f P d hf u).value σ := by
    have h := (common_agenda_field_count F cubic f P cfg hΔ hf hF d σ).choose_spec.1
    rw [Fin.sum_univ_zero,zero_add,sum_agendaGroupTerm_value F cubic f P d hf σ]
    exact congrArg (zeroCoordinate (RatScalar f)) h
  have correct (σ : W → Bool) :
      sourceModTwo f (output σ) =
        (PinnedCNF.modelCount (MainClonedCNF.formula F (MainClonedCNF.leftSlot F cubic)
          (MainClonedCNF.rightSlot F cubic) σ) : NativeProbeRing.Residue f) :=
    mod_two_of_count_at_creation f hf
      (common_agenda_field_count F cubic f P cfg hΔ hf hF d σ).choose_spec.2
  have h := cloned_fixed_mixed_affine_residue F (MainClonedCNF.leftSlot F cubic)
    (MainClonedCNF.rightSlot F cubic) matching (fun (_ : W) (_ : Unit) => ())
    (rootLabels F cubic f P) (fun _ => ∅) symbols
    (fun t : Fin 0 => Fin.elim0 t) (agendaGroupTerm F cubic f P d hf)
    0 D (Nat.zero_le _) small (fun _ => Nat.zero_le _) gap
    (sourceFieldMap f) (sourceModTwo f) (sourceFieldMap_injective f hf) output repr correct
  simp only [Fintype.card_fin,Nat.cast_zero,zero_div,zero_add] at h
  have hh := (le_div_iff₀ (show (0:ℚ)<(2:ℚ)^D by positivity)).mp h
  rw [one_mul] at hh
  exact_mod_cast hh

#print axioms mod_two_of_count_at_creation
#print axioms literal_menu_card_from_matching
end Paper5.D1Literal
