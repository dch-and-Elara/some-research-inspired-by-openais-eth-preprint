
import A2R45LiteralDiagonal
import A2R45LiteralOrigin
import A2R45LiteralRoot

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5700000
set_option synthInstance.maxHeartbeats 120000
set_option maxRecDepth 2050
set_option linter.unusedSectionVars false

/-! The two honest comparisons, on the same binary switch input:
the actual padded source register counts the minimal logical host, but
the actual public origin has one extra free bit per untrimmed vertex.
No equality of the physical padded and minimal atlases is asserted. -/
namespace A2R45Literal
open scoped Classical BigOperators Polynomial
open Polynomial FixedHostAcquisition J6R11Blueprint J6R12Blueprint
open J6R10Repack J6R9Recursive J1PPrinted
noncomputable section
attribute [local irreducible] A2R45Literal.rootCall J6R12Blueprint.printedParams

variable {k : ℕ}
local notation "n" => k+1
local notation "D" => DistinctOccurrence (k+1)
local notation "m" => simCount (k+1)
local notation "s" => A1R43Literal.starSize m

theorem actual_origin_counts_public_diagonal_factor {P : Type} [Fintype P]
    (u : Input n) (f : ℤ[X]) (base : ℕ) (hb : 0<base) (hf : f.Monic) (hF : 0<f.natDegree) :
    trueContraction (nativeNetwork n P) (file u f base) hf =
      (2:IntRing f 1)^(k+2)*(Nat.card (D→Bool):IntRing f 1) := by
  rw [true_source_origin u f base hb hf hF (Nat.succ_pos _)]
  have h := congrArg (fun x : ℕ => (x:IntRing f 1)) (public_origin_diagonal_factor (k:=k))
  simpa only [Nat.cast_pow,Nat.cast_mul,Nat.cast_ofNat] using h

theorem actual_source_count_matches_trimmed_fixed_graph (W : Plan n) (u : Input n) (f : ℤ[X])
    (guard : A1R43Literal.PrintedMargins m)
    (d : @J6R12Blueprint.Ready f 1 (printedParams (f:=f) (ell:=1) s)
      (sourceDelta s) (rootCall W u f))
    (cfg : RootBounds s 1 f) (hf : f.Monic) (hF : 0<f.natDegree)
    [Fact (Irreducible (NativeProbeRing.residuePoly f))] :
    @zeroRead f s (fixedSelector W u f guard) (rootCall W u f) d
      (negativeCenter W u f guard) hf = Nat.card (TrimmedAccepted u.enabled) := by
  exact (actual_fixed_slot_integer W u f guard d cfg hf hF (Nat.succ_pos _)).trans
    (trimmed_exact_graph_count u.enabled).symm

#print axioms actual_origin_counts_public_diagonal_factor
#print axioms actual_source_count_matches_trimmed_fixed_graph
end
end A2R45Literal
