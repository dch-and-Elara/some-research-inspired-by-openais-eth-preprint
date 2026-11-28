import P6JointAllCloneLow
import J9R20SameFilePrinted

namespace Paper6JointSeating
open scoped Polynomial Classical BigOperators
open Polynomial P11FullPacking J6R9Recursive J6R10Repack J6R9PacketScopes J6R9PacketChild
open J6ActiveRun J6R12Blueprint J6R11Blueprint J6R12Integral J1PPrinted
open NativeProbeRing J8Physical J8EndToEnd J8J9Grouped DyadicProbeCompiler
open J9R15FrozenErasurePhysical J9R15FrozenErasurePrecision J6R14SpecializedBox J9R20SameFile
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3500000

variable {R S V : Type} {U : V→Type}
variable [Fintype R] [Fintype S] [Fintype V] [(v:V)→Fintype (U v)]
variable (size C b : ℕ) (f : ℤ[X]) (ell created : ℕ)
local notation "a" => stepA (Nat.clog 2 size) 0
local notation "L" => ((2:ℕ)^a)
variable (d : Layout (Page (stepA (Nat.clog 2 size) 0) b (Fin 64)) R S V (Fin 64) U
  ((2:ℕ)^(stepA (Nat.clog 2 size) 0)))
variable (F : OldTables d) (sign : S→Bool)
local notation "r" => orientedRootCall d f ell created F sign
local notation "S₀" => printedParams (f:=f) (ell:=ell) size
variable (sel : Selector (printedParams (f:=f) (ell:=ell) size) (sourceDelta size))
variable (ready : Ready (printedParams (f:=f) (ell:=ell) size) (sourceDelta size)
  (orientedRootCall d f ell created F sign))

theorem printed_all_nonzero_center_erasure
    (cfg : RootBounds size C f) (stable : Stable size C r)
    (hf : f.Monic) (hF : 0<f.natDegree) (hℓ : 0<ell) (hc : 0<created)
    [Fact (Irreducible (residuePoly f))]
    (n : ℕ) (cert : CloneCertificate d F n)
    (gs : Bool → Finset (Option (S⊕V))) (hgs : ∀ s, gs s ⊆ cert.old)
    (q : ℕ) (hq : ∀ s, q≤(gs s).card)
    (reserved : letI := (r).host.finiteEdge
      letI := (r).host.finiteRow
      letI := (r).host.finiteCol
      ∀ s (e : J8Physical.Wire R), some ((orientedNetwork d).col e) ∈ gs s →
        ((packing sel ready).seat e).2.val = GuardedPacking.endpoint L s)
    (t : Center S₀ r) (z : Probe S₀ r) (β : LiteralMenu sel ready t)
    (hqp : q ≤ registerPrecision S₀ r t) :
    lowerBox (registerPrecision S₀ r t) q hqp f ell
      (printedPacketProduct (s:=size) (c:=r) sel ready t z β hf)=0 := by
  rw [printedPacketProduct_exact (s:=size) (c:=r) sel ready t z β hf cfg stable hF]
  letI := (r).host.finiteEdge
  letI := (r).host.finiteRow
  letI := (r).host.finiteCol
  let P := packing sel ready
  let p := registerPrecision S₀ r t
  change lowerBox p q hqp f ell (actualProjection P (centerIndex ready t) (centerNonzero t) rfl
    p (sampleNode S₀ f ell r ready.fit t z) (orientedEntryFile d f ell created F sign) hf β.val)=0
  exact actual_all_clone_nonzero_menu_zero d P F n cert sign gs hgs reserved f ell created q
    hf hc hF hℓ hq _ (centerNonzero t) (centerIndex ready t) rfl p hqp _ β.val

#print axioms printed_all_nonzero_center_erasure
end
end Paper6JointSeating
