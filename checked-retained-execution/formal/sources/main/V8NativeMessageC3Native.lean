import V8NativeMessageC3Rank
import V8NativeMessageC3Main
import V8NativeMessageC3D
import V8NativeMessageLower
import Mathlib.RingTheory.AdjoinRoot

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2700000

namespace V8NativeMessage.C3
open scoped Classical BigOperators Polynomial
open Polynomial Module
open V8PooledRange V8PooledRange.NativeOrigin V8PooledMenu.FiveCopy V8NativeMessage.Five

noncomputable section

/-- The scalarized MAIN calculation uses this literal quotient chart
with κ retained coefficients, including κ=0. -/
abbrev Jet (K : Type*) [Field K] (κ : ℕ) :=
  AdjoinRoot ((X : K[X])^κ)

def jetBasis (K : Type*) [Field K] (κ : ℕ) : Basis (Fin κ) K (Jet K κ) :=
  ((AdjoinRoot.powerBasis' (monic_X.pow κ)).basis).reindex
    (finCongr (by simp [AdjoinRoot.powerBasis']))

variable {V E : Type} [Fintype V] [Fintype E] {G : Graph V E} {p : ThreePorts G} {f : ℤ[X]}
variable {K Gₘ : Type*} [Field K] [Fintype Gₘ] {m : ℕ}
variable (M : Pairs G m) (P : Packing G p) (hu : 0<rootU V) (huM : rootU V≤wireSize V)
    (i : Fin (rootU V)) (T : Finset (Fin 64))
    (probes : Probes V f) (hf : f.Monic)

section OneBlock
variable {J : Type*} [CommRing J] [Algebra K J] {b : Gₘ→ℕ}
variable (lists : MainLists (V:=V) (J:=J) b) (ρ : J→ₗ[K]K)
    (lift : Fin 64 → HighChildView P hu huM i f → K)

def sourceBlock (s : V → Bool) : K :=
  ρ (mainCompleted lists s) * ∏ g, lift g (highChildView P hu huM i probes hf s g)

def Dleft (x : RowWords P i T) : K :=
  ∏ g∈T, lift g (highChildView P hu huM i probes hf (rowFill P i T x) g)

def Dright (y : ColWords P i T) : K :=
  ∏ g∈Tᶜ, lift g (highChildView P hu huM i probes hf (colFill P i T y) g)

theorem sourceBlock_eq (hd : 0<f.natDegree) (dcross : Crosses M P i T)
    (U : Finset Gₘ) (mcross : MainCross lists M U) (x y : Fin m→Bool) :
    sourceBlock P hu huM i probes hf lists ρ lift (activeSigns M x y) =
      ∑ q : ((g : Gₘ) → Fin (b g)),
      ρ (mainPart lists U (activeSigns M x (fun _=>false)) q *
        mainPart lists Uᶜ (activeSigns M (fun _=>false) y) q) *
      (Dleft P hu huM i T probes hf lift (matchRow M P i T x) *
        Dright P hu huM i T probes hf lift (matchCol M P i T y)) := by
  have ed := C3_D_separate_lifts P hu huM i T probes hf hd lift
    (matchRow M P i T x) (matchCol M P i T y)
  rw [matchSigns M P i T dcross] at ed
  rw [sourceBlock,real_main_completion_split lists M U mcross x y,map_sum,Finset.sum_mul,ed]
  rfl

end OneBlock

variable {H O : Type*} [Fintype H] [CommRing O] [Algebra O K]
variable (χ : O→+*ZMod 2) (hinj : Function.Injective (algebraMap O K))
variable (κ : H→ℕ) (b : H→Gₘ→ℕ) {J : H→Type*}
variable [∀ h, CommRing (J h)] [∀ h, Algebra K (J h)]

include hinj in
/-- Actual same-input restricted C3 comparison. The point jets and
separate lifts are graph-fixed inputs; the high D child is an actual
contracted EntryFile. The assembly, but not each scalar term, must
have the exact origin parity after integral reduction. -/
theorem C3_literal_fixed
    (basis : ∀ h, Basis (Fin (κ h)) K (J h))
    (lists : ∀h, MainLists (V:=V) (J:=J h) (b h)) (ρ : ∀h, J h→ₗ[K]K)
    (lift : H → Fin 64 → HighChildView P hu huM i f → K)
    (hd : 0<f.natDegree) (dcross : Crosses M P i T)
    (U : H→Finset Gₘ) (mcross : ∀h, MainCross (lists h) M (U h))
    (correct : ∀ x y, ∃ o : O, algebraMap O K o=
      (∑ h, sourceBlock P hu huM i probes hf (lists h) (ρ h) (lift h) (activeSigns M x y)) ∧
        χ o=(originCount G p (activeSigns M x y):ZMod 2)) :
    2^m≤∑h, κ h * ∏g, b h g := by
  let L (h : H) (q : Choices b h) (x : Fin m→Bool) : J h :=
    mainPart (lists h) (U h) (activeSigns M x (fun _=>false)) q
  let R (h : H) (q : Choices b h) (y : Fin m→Bool) : J h :=
    mainPart (lists h) (U h)ᶜ (activeSigns M (fun _=>false) y) q
  let dr (h : H) (x : Fin m→Bool) : K :=
    Dleft P hu huM i T probes hf (lift h) (matchRow M P i T x)
  let dc (h : H) (y : Fin m→Bool) : K :=
    Dright P hu huM i T probes hf (lift h) (matchCol M P i T y)
  apply C3_rank_budget κ b p M χ hinj basis ρ L R dr dc
  intro x y
  obtain ⟨o,ho,he⟩ := correct x y
  refine ⟨o,ho.trans ?_,he⟩
  simp only [Matrix.sum_apply,mixedTerm,Matrix.of_apply]
  exact Finset.sum_congr rfl fun h _ =>
    sourceBlock_eq M P hu huM i T probes hf (lists h) (ρ h) (lift h) hd dcross (U h) (mcross h) x y

#print axioms jetBasis
#print axioms sourceBlock_eq
#print axioms C3_literal_fixed

end
end V8NativeMessage.C3