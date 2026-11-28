import J7R43LiteralPublicAll
import J7R43LiteralGeometryHeads
import J7R43LiteralAllowedAddress
import J9R20SameFileGuards
import J9R20SameFileCubic

/-! J7 on the original four-clone graph, with runtime-independent
addresses for all signs. The physical chart and local CNFs are from the
audited source, not abstract generator inputs. -/
namespace J7R43Literal
open scoped Polynomial Classical BigOperators
open Polynomial P11FullPacking J6R9Recursive J6R10Repack J6R9PacketScopes J6R9PacketChild
open J6ActiveRun J6R12Blueprint J6R11Blueprint J6R12Integral J1PPrinted J6R11Integral
open NativeProbeRing J8Physical J8EndToEnd J8J9Grouped DyadicProbeCompiler J6R14SpecializedBox
open J7SourceLabels J7PrintedParams J7PrintedParamsGraph J7ToJ8Incidence J9R20SameFile
open J9R17AllPins J6ActiveInterpolation J7LiteralGraph
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option quotPrecheck false
set_option maxRecDepth 5000

local instance (priority := 17000) j7RealPageEq (a b : ℕ) :
    DecidableEq (Page a b (Fin 64)) := fun x y => Classical.propDecidable (x=y)

section World
variable {Pair H : Type} [Fintype Pair] [Fintype H]
variable (ends : H×Bool≃Pin Pair×Fin 3)
local notation "N" => Fintype.card (Pin Pair)
local notation "R" => Subdivision Pair (OrdinaryRow Pair H)
local notation "M" => Fintype.card (J8Physical.Wire R)
local notation "size" => sourceSize N
local notation "u" => stepU (Nat.clog 2 size) 0
local notation "a" => stepA (Nat.clog 2 size) 0
local notation "L" => ((2:ℕ)^a)
variable (f : ℤ[X]) (ell created : ℕ)
local notation "S₀" => printedParams (f:=f) (ell:=ell) size
local notation "∆" => sourceDelta size
variable {b : ℕ}
variable (G : SourceGeometry ends (stepA (Nat.clog 2 (sourceSize (Fintype.card (Pin Pair)))) 0) b)
local notation "d" => G.layout
local notation "F" => originalOldTables ends G.layout
local notation "MASK" => (J7SeatPacking.balancedMask (K:=Fin 64) a b)
local notation "ROOT" => orientedRootCall G.layout f ell created (originalOldTables ends G.layout)
local notation "Q" => seatedParentPacking d MASK G.wordsR G.wordsC G.declared G.budget
variable (hf : f.Monic) (hℓ : 0<ell)

set_option maxHeartbeats 10000000 in
def ActualPublicZeroReceipt : Prop :=
    ∃ ha : 0<a, ∃ hu : 0<u, ∃ huM : u≤M,
    ∃ ready : ∀ sign, Ready S₀ ∆ (ROOT sign), ∃ he : Even L,
    let fixed : Pin Pair→Bool := fun _ => false
    let t := extremeCenter S₀ (ROOT fixed) ha hu huM
    let p := registerPrecision S₀ (ROOT fixed) t
    ∃ words : Probe S₀ (ROOT fixed) → Fin f.natDegree→Bool,
      Function.Injective words ∧
      (∀ i j, i≠j → IsUnit (scalarIn p f ell (probe p f (words j)) -
        scalarIn p f ell (probe p f (words i)))) ∧
      (∃ j, j.val=0 ∧ scalarIn p f ell (probe p f (words j))=0) ∧
    ∃ (zero : PublicMenu MASK ⟨0,ha⟩ p) (pick : Orders d→PublicMenu MASK ⟨0,ha⟩ p),
      zero.val=0 ∧ (∀ w, (pick w).val.support.card=1) ∧
      ∀ sign : Pin Pair→Bool,
        let received := publicZeroChild size b f ell created d F Q ha hu huM ready hf sign
        let recover := fun k : Occupied d =>
          let s := anchor d k
          NativeMomentReconstruction.decodeBits (coordinates d s)
            (fun _ => (readUnsigned p hf hℓ (received zero ((d).pinLabel s)) : ℚ))
            (fun j => actualPublicMoment d G.endpoint he F s j.val)
            (fun j => (readUnsigned p hf hℓ (received (pick ⟨k,j⟩) ((d).pinLabel s)) : ℚ))
        (fun s => recover ((orderPin d).symm s).1 ((orderPin d).symm s).2) = sign

set_option maxHeartbeats 12000000 in
theorem fixed_public_geometry_zero_receipt
    (hc : 0<created) (cfg : RootBounds (sourceSize (Fintype.card (Pin Pair))) 3 f)
    [Fact (Irreducible (residuePoly f))] :
    ActualPublicZeroReceipt ends f ell created G hf hℓ := by
  obtain ⟨hF,large⟩ := root_bounds_force_j9_range _ f cfg
  have source (sign : Pin Pair→Bool) :=
    four_clone_ready_and_printed_guards ends d F sign f ell created large cfg
  let ready : ∀ sign, Ready S₀ ∆ (ROOT sign) := fun sign => (source sign).2.1
  have stable : ∀ sign, Stable size 3 (ROOT sign) := fun sign => (source sign).1
  obtain ⟨_,_,ha,hu,huM,he,hL,hCube⟩ := source (fun _=>false)
  let i : Fin a := ⟨0,ha⟩
  let fixed : Pin Pair→Bool := fun _=>false
  let t := extremeCenter S₀ (ROOT fixed) ha hu huM
  let p := registerPrecision S₀ (ROOT fixed) t
  have hp : 10*M≤p :=
    native_register_precision_ge_tenM created a M u t.val ha
  obtain ⟨words,hinj,hunits,hzero⟩ := chosen_legal_list_with_zero (s:=size) (ready fixed) t hf hF
  refine ⟨ha,hu,huM,ready,he,words,hinj,hunits,hzero,?_⟩
  exact same_public_zero_decodes_all_signs size 3 b f ell created d F MASK
    G.wordsR G.wordsC G.declared G.budget ha hu huM ready hf cfg stable hF hℓ hc G.endpoint he
    ((by decide : (3:ℕ)≤36).trans hL) (G.rowHead i rfl) (G.colHead i rfl)
    (original_geometry_row_words ends G i rfl) (original_geometry_pin_words ends G i rfl)
    (original_geometry_old_words ends G i rfl) G.off (original_old_tables_satisfiable ends d)
    hCube G.capacity hp

#print axioms ActualPublicZeroReceipt
#print axioms fixed_public_geometry_zero_receipt
end World

set_option maxHeartbeats 6500000 in
theorem actual_cubic_graph_public_J7
    {V : Type} [LinearOrder V] [Fintype V] (B : SimpleGraph V) [DecidableRel B.Adj]
    (cubic : Cubic B) (f : ℤ[X]) (ell created : ℕ)
    (hf : f.Monic) (hℓ : 0<ell) (hc : 0<created)
    (cfg : RootBounds (sourceSize (Fintype.card (Pin (Edge B)))) 3 f)
    [Fact (Irreducible (residuePoly f))] :
    ∃ copies : ℕ,
      ∃ geom : SourceGeometry (atlas B cubic)
        (stepA (Nat.clog 2 (sourceSize (Fintype.card (Pin (Edge B))))) 0) copies,
        ActualPublicZeroReceipt (atlas B cubic) f ell created geom hf hℓ ∧
        Fintype.card (SingleChildOrders geom.layout) = Fintype.card (Pin (Edge B)) ∧
        Fintype.card (WithBaselines geom.layout) = Fintype.card (Pin (Edge B))+64 := by
  have range := root_bounds_force_j9_range _ f cfg
  obtain ⟨copies,⟨geom⟩⟩ := original_source_geometry_at_printed_root (atlas B cubic) range.2
  exact ⟨copies,geom,fixed_public_geometry_zero_receipt (atlas B cubic) f ell created geom hf hℓ hc cfg,
    actual_individual_request_count geom.layout,with_all_baselines_request_count geom.layout⟩

#print axioms actual_cubic_graph_public_J7
end
end J7R43Literal
