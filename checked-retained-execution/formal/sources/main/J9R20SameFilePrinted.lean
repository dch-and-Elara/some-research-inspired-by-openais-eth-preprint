
import J9R20SameFileCatalog
import J6R16SpecializedBoxRunProduct
import J6R16SpecializedBoxRoot

/-! The low receiver acts on the actual high printed recursive product.
The high β and binary address are neither transported nor rebuilt. -/
namespace J9R20SameFile
open scoped Polynomial Classical BigOperators
open Polynomial P11FullPacking J6R9Recursive J6R10Repack J6R9PacketScopes J6R9PacketChild
open J6ActiveRun J6R12Blueprint J6R11Blueprint J6R12Integral J1PPrinted
open NativeProbeRing J8Physical J8EndToEnd J8J9Grouped DyadicProbeCompiler
open J9R15FrozenErasurePhysical J9R15FrozenErasurePrecision J6R14SpecializedBox
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3500000

variable {R S V : Type} {U : V→Type}
variable [Fintype R] [Fintype S] [Fintype V] [(v:V)→Fintype (U v)]
variable (size C b : ℕ) (f : ℤ[X]) (ell created : ℕ)
local notation "a" => stepA (Nat.clog 2 size) 0
local notation "L" => ((2:ℕ)^a)
variable (d : Layout (Page (stepA (Nat.clog 2 size) 0) b (Fin 64)) R S V (Fin 64) U ((2:ℕ)^(stepA (Nat.clog 2 size) 0)))
variable (F : OldTables d) (sign : S→Bool)
local notation "r" => orientedRootCall d f ell created F sign
local notation "S₀" => printedParams (f:=f) (ell:=ell) size
local notation "∆" => sourceDelta size
variable (sel : Selector (printedParams (f:=f) (ell:=ell) size) (sourceDelta size))
variable (ready : Ready (printedParams (f:=f) (ell:=ell) size) (sourceDelta size) (orientedRootCall d f ell created F sign))
variable (cfg : RootBounds size C f) (stable : Stable size C (orientedRootCall d f ell created F sign))

include cfg stable in
theorem printed_product_low_erases
    (ha : 0<a) (hu : 0<(S₀).levelWidth (r).depth) (huM : (S₀).levelWidth (r).depth≤(r).edges)
    (hf : f.Monic) (hF : 0<f.natDegree) (hℓ : 0<ell) (hc : 0<created)
    [Fact (Irreducible (residuePoly f))]
    (n : ℕ) (cert : CloneCertificate d F n)
    (q : ℕ) (hq : (q:ℚ)≤(24*(n:ℚ))/6-3*(24*(n:ℚ))/(L:ℕ)) :
    let t := extremeCenter S₀ r ha hu huM
    let p := registerPrecision S₀ r t
    ∀ hqp : q≤p, ∀ z : Probe S₀ r, ∀ β : LiteralMenu sel ready t,
      lowerBox p q hqp f ell (printedPacketProduct (s:=size) (c:=r) sel ready t z β hf)=0 := by
  dsimp only
  intro hqp z β
  let t := extremeCenter S₀ r ha hu huM
  let p := registerPrecision S₀ r t
  change lowerBox p q hqp f ell (printedPacketProduct (s:=size) (c:=r) sel ready t z β hf)=0
  rw [printedPacketProduct_exact (s:=size) (c:=r) sel ready t z β hf cfg stable hF]
  letI := (r).host.finiteEdge
  letI := (r).host.finiteRow
  letI := (r).host.finiteCol
  let P := packing sel ready
  change lowerBox p q hqp f ell (actualProjection P (centerIndex ready t) (centerNonzero t) rfl
    p (sampleNode S₀ f ell r ready.fit t z) (orientedEntryFile d f ell created F sign) hf β.val)=0
  exact four_clone_same_oriented_low_bits d P F n cert sign f ell created p q hf hc hF hℓ
    hqp hq (centerIndex ready t) (centerNonzero t) rfl
    (sampleNode S₀ f ell r ready.fit t z) β.val

#print axioms printed_product_low_erases

end
end J9R20SameFile
