import P6JointGeometryModel
import P6JointPrintedLow
import J9R21ImplicationPublicWorld

namespace Paper6JointSeating
open scoped Classical Polynomial BigOperators
open Polynomial P11FullPacking J6R9Recursive J6R10Repack J6R9PacketScopes J6R9PacketChild
open J6ActiveRun J6R12Blueprint J6R11Blueprint J6R12Integral J1PPrinted
open NativeProbeRing J8Physical J8EndToEnd J8J9Grouped DyadicProbeCompiler
open J9R15FrozenErasurePhysical J9R15FrozenErasurePrecision J6R14SpecializedBox J9R20SameFile
open J7SourceLabels J7PrintedParams J7PrintedParamsGraph J7ToJ8Incidence J7SeatSource
open J9R21Implication
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 5500000

variable {Pair H : Type} [Fintype Pair] [Fintype H]
variable (ends : H×Bool ≃ Pin Pair×Fin 3)
local notation "N" => Fintype.card (Pin Pair)
local notation "s₀" => sourceSize N
local notation "a" => stepA (Nat.clog 2 s₀) 0
local notation "L" => ((2:ℕ)^a)
local notation "R" => Subdivision Pair (OrdinaryRow Pair H)
local notation "A" => Fin 64
local notation "D" => PrintedOld Pair H
local notation "C" => PrintedOwners Pair H
variable {b : ℕ} (geom : JointSourceGeometry ends (stepA (Nat.clog 2 (sourceSize (Fintype.card (Pin Pair)))) 0) b)
local notation "d" => geom.layout
local notation "F" => implicationOldTables ends geom.layout
local notation "MASK" => (J7SeatPacking.balancedMask (K:=A) a b)
local notation "Q" => seatedParentPacking d MASK geom.wordsR geom.wordsC geom.declared geom.budget

def guardEncode : Clones Pair → Option C := fun pin => some (.inr (cloneOwner pin))

theorem guardEncode_inj : Function.Injective (guardEncode (Pair:=Pair) (H:=H)) := by
  intro x y eq
  exact cloneOwner_injective (Sum.inr.inj (Option.some.inj eq))

local instance (priority := 12000) ownerEq : DecidableEq (Option C) :=
  fun x y => Classical.propDecidable (x=y)

def guardHosts (s : Bool) : Finset (Option C) :=
  (geom.keep s).image (guardEncode (Pair:=Pair) (H:=H))

theorem guardHosts_card (s : Bool) :
    (guardHosts ends geom s).card = (geom.keep s).card :=
  Finset.card_image_of_injective _ guardEncode_inj

def actualCloneCert : CloneCertificate d F N where
  old := allCloneOwners
  typed := by
    intro u hu
    obtain ⟨x,hx⟩ := (mem_allCloneOwners u).1 hu
    exact ⟨cloneOwner x,hx⟩
  truth := implication_tables_preserve_clone_variables ends d
  port := by
    intro u hu
    obtain ⟨x,rfl⟩ := (mem_allCloneOwners u).1 hu
    obtain ⟨e,he⟩ := allClones_have_literal_port ends x
    let j : Ports (column ends cycle) (cloneOwner x) := ⟨e,he⟩
    exact ⟨ordinaryWire d ⟨cloneOwner x,j⟩,congrArg some (standard_port_owner d _ j)⟩
  four := allCloneOwners_card
  wireCount := (Fintype.card_congr ((d).column.trans (colWire (column ends cycle)))).trans (actual_incidence ends).1

variable (f : ℤ[X]) (ell created : ℕ) (sign : Pin Pair→Bool)
local notation "r" => orientedRootCall d f ell created F sign
local notation "S₀" => printedParams (f:=f) (ell:=ell) s₀
local notation "∆" => sourceDelta s₀
local notation "SEL" => exactSeatSelector S₀ ∆ r Q
theorem joint_atlas_same_geometry_all_nonzero_erases
    (ready : Ready S₀ ∆ (orientedRootCall d f ell created F sign))
    (cfg : RootBounds s₀ 3 f) (stable : Stable s₀ 3 r)
    (hf : f.Monic) (hF : 0<f.natDegree) (he : 0<ell) (hc : 0<created)
    [Fact (Irreducible (residuePoly f))]
    (q : ℕ) (hq : ∀ side, q≤(geom.keep side).card)
    (t : Center S₀ r) (z : Probe S₀ r) (β : LiteralMenu SEL ready t)
    (hqp : q≤registerPrecision S₀ r t) :
    lowerBox (registerPrecision S₀ r t) q hqp f ell
      (printedPacketProduct SEL ready t z β hf)=0 := by
  have hs : ∀ side, guardHosts ends geom side ⊆ (actualCloneCert ends geom).old := by
    intro side u hu
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hu
    exact (mem_allCloneOwners _).2 ⟨x,rfl⟩
  have hn : ∀ side, q≤(guardHosts ends geom side).card := by
    intro side
    rw [guardHosts_card]
    exact hq side
  refine printed_all_nonzero_center_erasure s₀ 3 b f ell created d F sign SEL ready cfg stable
    hf hF he hc N (actualCloneCert ends geom) (guardHosts ends geom) hs q hn ?_ t z β hqp
  intro side e he'
  obtain ⟨x,hx,hex⟩ := Finset.mem_image.mp he'
  rw [exactSeatSelector_at_root]
  change ((d).seat e).2.val = _
  apply geom.guard_seated side x hx e
  exact (Option.some.inj hex).symm

#print axioms actualCloneCert
#print axioms joint_atlas_same_geometry_all_nonzero_erases
end
end Paper6JointSeating



