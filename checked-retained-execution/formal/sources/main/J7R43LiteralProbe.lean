import J6R15SpecializedBoxFrame
import J6R14ZeroModeProbe
import J6R16SpecializedBoxSelected

/-! The paper permits any list of distinct binary probes. A source list
with zero can actually be chosen under the normal cardinality guard.
This makes no assertion that an already-fixed printed prefix has zero. -/
namespace J7R43Literal
open scoped BigOperators Classical Polynomial
open Polynomial NativeProbeRing J6ActiveInterpolation J6R14SpecializedBox
open J6ActiveRun J6R9Recursive J6R12Blueprint J6R11Blueprint
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false

def zeroWordIndex (e : ℕ) : ℕ :=
  ((Fintype.equivFin (Fin e → Bool)) (fun _ => false)).val

theorem fixed_prefix_contains_zero_iff (e n : ℕ) (fit : n≤2^e) :
    (∃ j : Fin n, chosenRep e n fit j = fun _ => false) ↔ zeroWordIndex e < n := by
  let eq := Fintype.equivFin (Fin e → Bool)
  constructor
  · rintro ⟨j,hj⟩
    have h' : Fin.castLE (fit.trans (menu_card e).ge) j = eq (fun _ => false) := by
      apply eq.symm.injective
      rw [eq.symm_apply_apply]
      exact hj
    have hi : j.val = zeroWordIndex e := congrArg Fin.val h'
    exact hi ▸ j.prop
  · intro hn
    refine ⟨⟨zeroWordIndex e,hn⟩,?_⟩
    change eq.symm (Fin.castLE _ _) = _
    have he : Fin.castLE (fit.trans (menu_card e).ge) (⟨zeroWordIndex e,hn⟩ : Fin n) =
        eq (fun _ => false) := Fin.ext rfl
    rw [he,eq.symm_apply_apply]

def zeroFirstWords (e n : ℕ) (fit : n≤2^e) (hn : 0<n) : Fin n → Fin e → Bool :=
  Equiv.swap (chosenRep e n fit ⟨0,hn⟩) (fun _ => false) ∘ chosenRep e n fit

theorem zeroFirstWords_injective (e n : ℕ) (fit : n≤2^e) (hn : 0<n) :
    Function.Injective (zeroFirstWords e n fit hn) :=
  (Equiv.swap _ _).injective.comp (chosenRep_injective e n fit)

theorem zeroFirstWords_first (e n : ℕ) (fit : n≤2^e) (hn : 0<n) :
    zeroFirstWords e n fit hn ⟨0,hn⟩ = fun _ => false := by
  unfold zeroFirstWords
  rw [Function.comp_apply,Equiv.swap_apply_left]

variable {f : ℤ[X]} {ell : ℕ}

theorem scalar_probe_zero_iff (p : ℕ) (hp : 0<p) (hℓ : 0<ell)
    (hf : f.Monic) (hF : 0<f.natDegree) (b : Fin f.natDegree → Bool) :
    scalarIn p f ell (probe p f b) = 0 ↔ b = fun _ => false := by
  constructor
  · intro hz
    rw [← map_zero (scalarIn p f ell)] at hz
    have h := scalarIn_injective p f ell hℓ hz
    rw [← J6R14ZeroMode.actual_probe_zero p f] at h
    exact binary_residues_injective p hp f hf hF (congrArg (residueMap p hp f) h)
  · intro hb
    rw [hb,J6R14ZeroMode.actual_probe_zero,map_zero]

theorem zero_first_list_units (p : ℕ) (hp : 0<p) (hf : f.Monic)
    (hF : 0<f.natDegree) [Fact (Irreducible (residuePoly f))]
    (n : ℕ) (fit : n≤2^f.natDegree) (hn : 0<n)
    (i j : Fin n) (hij : i≠j) :
    IsUnit (scalarIn p f ell (probe p f (zeroFirstWords f.natDegree n fit hn j)) -
      scalarIn p f ell (probe p f (zeroFirstWords f.natDegree n fit hn i))) := by
  rw [← map_sub]
  apply IsUnit.map (scalarIn p f ell)
  apply unit_of_residue p hp f hf
  rw [map_sub,sub_ne_zero]
  intro he
  exact hij (zeroFirstWords_injective _ _ _ _
    (binary_residues_injective p hp f hf hF he.symm))

variable {S : Params (f:=f) (ell:=ell)} {Δ : ℕ}
variable {c : Call (PhysicalHost f ell)}

theorem fixed_sample_contains_zero_iff (d : Ready S Δ c) (t : Center S c)
    (hℓ : 0<ell) (hf : f.Monic) (hF : 0<f.natDegree) :
    (∃ j : Probe S c, sampleNode S f ell c d.fit t j = 0) ↔
      zeroWordIndex f.natDegree < J9PrintedSchedule.probeCount c.edges (2^S.levelBits c.depth) := by
  rw [← fixed_prefix_contains_zero_iff f.natDegree (J9PrintedSchedule.probeCount c.edges (2^S.levelBits c.depth)) d.fit]
  constructor <;> rintro ⟨j,hj⟩ <;> refine ⟨j,?_⟩
  · rw [literal_address_at_sample S Δ c d t j] at hj
    exact (scalar_probe_zero_iff _ (register_positive d t) hℓ hf hF _).mp hj
  · rw [literal_address_at_sample S Δ c d t j]
    exact (scalar_probe_zero_iff _ (register_positive d t) hℓ hf hF _).mpr hj

#print axioms fixed_prefix_contains_zero_iff
#print axioms zeroFirstWords_injective
#print axioms zeroFirstWords_first
#print axioms scalar_probe_zero_iff
#print axioms zero_first_list_units
#print axioms fixed_sample_contains_zero_iff
end
end J7R43Literal