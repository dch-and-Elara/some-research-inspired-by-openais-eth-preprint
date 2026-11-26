import P5HybridDUnclonedSource

namespace Paper5.HybridDUncloned.Review
open scoped Classical Polynomial
open Polynomial J6R10Repack J6R9Recursive J6R11Blueprint J6ActiveRun J6R12Blueprint J1PPrinted Paper5.HybridClosure Paper5.D1Literal

variable {V : Type} [Fintype V] [DecidableEq V]
variable (F : Finset (V×V)) (reg : ∀v,GraphCutMoments.degree F v=3)
variable (f : ℤ[X]) (σ : V → Bool)
local notation "r" => Paper5.HybridDUncloned.root F reg f σ
local notation "SP" => printedParams (f:=f) (ell:=1) (sourceSize F)

theorem actual_uncloned_register_precision
    (d : Ready SP (sourceDelta (sourceSize F)) r) (t : Center SP r) :
    registerPrecision SP r t =
      J9PrintedSchedule.precision (Fintype.card V+1)
        (HermiteLoss.sourceH (10*Fintype.card V) ((SP).levelWidth 0))
        (2^((SP).levelBits 0-(centerIndex d t).val)) (10*Fintype.card V) ((SP).levelBits 0) := by
  have h := J6R9Recursive.precision_same (Fintype.card V+1) ((SP).levelBits 0)
      (Fintype.card (Wire F)) ((SP).levelWidth 0) t.property
  change registerPrecision SP r t = _ at h
  rw [physical_wire_count F reg] at h
  exact h

#print axioms actual_uncloned_register_precision
end Paper5.HybridDUncloned.Review
