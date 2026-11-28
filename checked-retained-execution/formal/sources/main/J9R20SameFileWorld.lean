
import J9R20SameFileFourClone
import J9R20SameFileGeometry
import J9R20SameFileGuards
import J9R20SameFileLiteralTables

/-! The actual printed source with one sign-independent scored seating
and no supplied layout/Ready/Stable or local CNF witness. -/
namespace J9R20SameFile
open scoped Polynomial Classical BigOperators
open Polynomial P11FullPacking J6R9Recursive J6R10Repack J6R9PacketScopes J6R9PacketChild
open J6ActiveRun J6R12Blueprint J6R11Blueprint J6R12Integral J1PPrinted
open NativeProbeRing J8Physical J8EndToEnd J8J9Grouped DyadicProbeCompiler
open J6R14SpecializedBox J9R17AllPins J9R15FrozenErasurePrecision LiteralPortCompiler
open J7SourceLabels J7PrintedParams J7PrintedParamsGraph J7ToJ8Incidence
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 12000000
local instance (priority := 10000) classicalPageWorld (a b : ℕ) :
    DecidableEq (Page a b (Fin 64)) := fun x y => Classical.propDecidable (x=y)

variable {Pair H : Type} [Fintype Pair] [Fintype H]
variable (ends : H×Bool≃Pin Pair×Fin 3)
local notation "N" => Fintype.card (Pin Pair)
local notation "R" => Subdivision Pair (OrdinaryRow Pair H)
local notation "M" => Fintype.card (J8Physical.Wire R)
local notation "s₀" => sourceSize N
local notation "u₀" => stepU (Nat.clog 2 (sourceSize (Fintype.card (Pin Pair)))) 0
local notation "a₀" => stepA (Nat.clog 2 (sourceSize (Fintype.card (Pin Pair)))) 0
local notation "L" => ((2:ℕ)^a₀)
variable (f : ℤ[X]) (ell created : ℕ)
local notation "S₀" => printedParams (f:=f) (ell:=ell) s₀
local notation "∆" => sourceDelta s₀
variable {b : ℕ}
variable (G : SourceGeometry ends (stepA (Nat.clog 2 (sourceSize (Fintype.card (Pin Pair)))) 0) b)
local notation "d" => G.layout
local notation "F" => originalOldTables ends G.layout
local notation "MASK" => (J7SeatPacking.balancedMask (K:=Fin 64) a₀ b)
local notation "q" => 2*N
local notation "idx" => (Fintype.equivFin (J8Physical.Wire R))
variable (sign : Pin Pair→Bool)
local notation "r" => (orientedRootCall G.layout f ell created (originalOldTables ends G.layout) sign)
variable (hf : f.Monic) (hℓ : 0<ell)

/-- The high and low claims refer to the same boxed product of recursive
children on the fixed sign-independent world. The low precision is
exactly two bits per original pin. No valuation/uncomputed callback is
ascribed to another file or another root packing. -/
def OriginalWorldReceipt : Prop :=
    ∃ ha : 0<a₀, ∃ hu : 0<u₀, ∃ huM : u₀≤M,
    ∃ ready : Ready S₀ ∆ r,
    ∃ he : Even L, ∃ hCube : L^3≤M,
    let t := extremeCenter S₀ r ha hu huM
    let p := registerPrecision S₀ r t
    let sel := exactSeatSelector S₀ ∆ r
      (seatedParentPacking d MASK G.wordsR G.wordsC G.declared G.budget)
    ∃ hP : 10*M≤p,
    ∃ hMenu : 10*M+1≤J9PrintedSchedule.probeCount M L,
    ∃ hqp : q≤p,
    ∃ choices : Orders d→Fin (10*M+1)→LiteralMenu sel ready t,
      (∀ w i, (choices w i).val.support.card=1) ∧
      (let mPos : 0<M := (show 0<L^3 by positivity).trans_le hCube
       publicAllPinDecoder d G.endpoint he F (fun w => publicCoefficient d (anchor d w.1) idx w.2 p ell
        hP hℓ f hf (hMenu.trans ready.fit) mPos (fun i =>
          printedPacketProduct (s:=s₀) (c:=r) sel ready t (Fin.castLE hMenu i) (choices w i) hf)) = sign) ∧
      (∀ z : Probe S₀ r, ∀ β : LiteralMenu sel ready t,
        lowerBox p q hqp f ell (printedPacketProduct (s:=s₀) (c:=r) sel ready t z β hf)=0)

theorem original_world_receipt (hF : 0<f.natDegree) (hc : 0<created)
    (large : 2^(9*131072-1) < sourceSize (Fintype.card (Pin Pair)))
    (cfg : RootBounds (sourceSize (Fintype.card (Pin Pair))) 3 f)
    [Fact (Irreducible (residuePoly f))] :
    OriginalWorldReceipt ends f ell created G sign hf hℓ := by
  obtain ⟨stable,ready,ha,hu,huM,he,hL,hCube⟩ :=
    four_clone_ready_and_printed_guards ends d F sign f ell created large cfg
  refine ⟨ha,hu,huM,ready,he,hCube,?_⟩
  have six : 6≤L := (by decide : (6:ℕ)≤36).trans hL
  exact same_original_four_clone_high_low ends s₀ 3 b f ell created d F sign
    G.wordsR G.wordsC G.declared G.budget ha hu huM ready cfg stable hf hF hℓ hc G.endpoint he six
    (G.rowHead ⟨0,ha⟩ rfl) (G.colHead ⟨0,ha⟩ rfl) G.off (original_old_tables_satisfiable ends d)
    idx hCube G.capacity (original_tables_preserve_all_clones ends d) q (by
      simpa only [Nat.cast_mul,Nat.cast_ofNat] using linear_low_budget L N hL)

/-- One actual graph-only J7 certificate works for every private sign.
No unfolded address/entry/precision-oracle premise is needed. -/
theorem original_four_clone_printed_J9
    (hF : 0<f.natDegree) (hc : 0<created)
    (large : 2^(9*131072-1) < sourceSize (Fintype.card (Pin Pair)))
    (cfg : RootBounds (sourceSize (Fintype.card (Pin Pair))) 3 f)
    [Fact (Irreducible (residuePoly f))] :
    ∃ (copyCount : ℕ), ∃ geom : SourceGeometry ends (stepA (Nat.clog 2 (sourceSize (Fintype.card (Pin Pair)))) 0) copyCount,
      ∀ sign : Pin Pair→Bool,
        OriginalWorldReceipt ends f ell created geom sign hf hℓ := by
  obtain ⟨b,⟨G⟩⟩ := original_source_geometry_at_printed_root ends large
  exact ⟨b,G,fun bit => original_world_receipt ends f ell created G bit hf hℓ hF hc large cfg⟩

#print axioms OriginalWorldReceipt
#print axioms original_world_receipt
#print axioms original_four_clone_printed_J9
end
end J9R20SameFile
