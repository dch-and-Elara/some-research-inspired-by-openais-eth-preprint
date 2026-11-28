
import J6R26StablePreparedRootZero

/-! A native probe job with the ready certificate, centre and word frame
fixed by its type. Assembling this record reuses supplied descriptors;
it neither produces those descriptors nor accepts an answer as input. -/
namespace J6R26StablePreparedRoot
open scoped Polynomial
open Polynomial A1R10 AOracleMachineTime J6R24MeteredRecursion
open J6ActiveRun J6R11Blueprint J6R12Blueprint J1PPrinted J6R14ZeroMode
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false

structure SuppliedProbeBits {f : ℤ[X]} {D : ℕ} (W : Prescribed f D) (n : ℕ) where
  read : Fin (D+1)→Meter {x : List Bool // x.length=n}
  consistent : ∀ j,(read j).result.val=List.ofFn (W.word j)

noncomputable abbrev FixedProbeInput (f : ℤ[X]) (ell s C : ℕ)
    (cfg : RootBounds s C f)
    (sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s))
    (c : Call (PhysicalHost f ell)) (hf : f.Monic)
    (d : Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c)
    (t : Center (printedParams (f:=f) (ell:=ell) s) c)
    (F : Frame f (registerPrecision (printedParams (f:=f) (ell:=ell) s) c t)) : Type 1 :=
  Σ W : Prescribed f (externalProbeDegree s c), SuppliedProbeBits W F.words.length ×
    (∀ (j : Fin (externalProbeDegree s c+1)) (g : Fin 64),
      @ProbePrepared f ell s C cfg hf sel c d t W j g)

noncomputable def FixedProbeInput.toJob
    {f : ℤ[X]} {ell s C : ℕ} {cfg : RootBounds s C f}
    {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
    {c : Call (PhysicalHost f ell)} {hf : f.Monic}
    {d : Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c}
    {t : Center (printedParams (f:=f) (ell:=ell) s) c}
    {F : Frame f (registerPrecision (printedParams (f:=f) (ell:=ell) s) c t)}
    (I : FixedProbeInput f ell s C cfg sel c hf d t F) : ProbeJob f ell s C cfg sel c hf :=
  ⟨d,t,I.1,F,I.2.2⟩

#print axioms FixedProbeInput.toJob
end J6R26StablePreparedRoot
