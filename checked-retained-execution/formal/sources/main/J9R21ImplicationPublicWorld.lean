import J9R21ImplicationTables
import J9R20SameFileCubic
import J9R20SameFilePrecision

/-! The common public high/low world with the *literal directed
implication* at every copy-cycle edge; no equality-cycle values are
identified with these values. The public address construction is inherited
from R20 and instantiated here on the corrected, unchanged file. -/
namespace J9R21Implication
open scoped Polynomial Classical BigOperators
open Polynomial P11FullPacking J6R9Recursive J6R10Repack J6R9PacketScopes J6R9PacketChild
open J6ActiveRun J6R12Blueprint J6R11Blueprint J6R12Integral J1PPrinted
open NativeProbeRing J8Physical J8EndToEnd J8J9Grouped DyadicProbeCompiler
open J6R14SpecializedBox J9R17AllPins J9R15FrozenErasurePrecision LiteralPortCompiler
open J7SourceLabels J7PrintedParams J7PrintedParamsGraph J7ToJ8Incidence
open J9R20SameFile J7LiteralGraph
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 12000000
local instance (priority := 10000) classicalPagePublicWorld (a b : ℕ) :
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
local notation "F" => implicationOldTables ends G.layout
local notation "MASK" => (J7SeatPacking.balancedMask (K:=Fin 64) a₀ b)
local notation "q" => 2*N
local notation "idx" => (Fintype.equivFin (J8Physical.Wire R))

local notation "ROOT" => orientedRootCall G.layout f ell created (implicationOldTables ends G.layout)
local notation "W" => J9PrintedSchedule.probeCount M L
variable (hf : f.Monic) (hℓ : 0<ell)

def ImplicationPublicWorld : Prop :=
    ∃ ha : 0<a₀, ∃ hu : 0<u₀, ∃ huM : u₀≤M,
    ∃ ready : ∀ sign, Ready S₀ ∆ (ROOT sign),
    ∃ he : Even L, ∃ hCube : L^3≤M,
    let i₀ := (Fin.mk 0 ha : Fin a₀)
    let fixed := fun _ : Pin Pair => false
    let ctr := extremeCenter S₀ (ROOT fixed) ha hu huM
    let p := registerPrecision S₀ (ROOT fixed) ctr
    let Q := seatedParentPacking d MASK G.wordsR G.wordsC G.declared G.budget
    ∃ hP : 10*M≤p, ∃ hMenu : 10*M+1≤W, ∃ hqp : q≤p,
    let fit := hMenu.trans (ready fixed).fit
    let hM : 0<M := (show 0<L^3 by positivity).trans_le hCube
    let raw := publicHighObservation s₀ b f ell created d F Q ha hu huM ready hf
    let low := publicLowerObservation s₀ b f ell created d F Q ha hu huM ready hf q hqp
    ∃ pick : Orders d→PublicMenu MASK i₀ p,
      Fintype.card (Orders d × Fin (10*M+1))=N*(10*M+1) ∧
      (∀ w, (pick w).val.support.card=1) ∧
      (∀ sign, publicAllPinDecoder d G.endpoint he F (fun w =>
        publicCoefficient d (anchor d w.1) idx w.2 p ell hP hℓ f hf fit hM
          (fun j => raw sign (Fin.castLE hMenu j) (pick w)))=sign) ∧
      (∀ sign z η, low sign z η = lowerBox p q hqp f ell (raw sign z η)) ∧
      (∀ sign z η, low sign z η = 0) ∧
      ¬∃ decode : (Fin W × PublicMenu MASK i₀ p → Box f ell q) → Pin Pair→Bool,
         ∀ sign, decode (fun z => low sign z.1 z.2)=sign

theorem implication_public_world_complete (hF : 0<f.natDegree) (hc : 0<created)
    (large : 2^(9*131072-1) < sourceSize (Fintype.card (Pin Pair)))
    (cfg : RootBounds (sourceSize (Fintype.card (Pin Pair))) 3 f)
    [Fact (Irreducible (residuePoly f))] :
    ImplicationPublicWorld ends f ell created G hf hℓ := by
  have receipts (sign : Pin Pair→Bool) :=
    four_clone_ready_and_printed_guards ends d F sign f ell created large cfg
  obtain ⟨_,_,ha,hu,huM,he,hL,hCube⟩ := receipts (fun _=>false)
  let ready (sign : Pin Pair→Bool) := (receipts sign).2.1
  let stable (sign : Pin Pair→Bool) := (receipts sign).1
  refine ⟨ha,hu,huM,ready,he,hCube,?_⟩
  let i₀ := (Fin.mk 0 ha : Fin a₀)
  let fixed := fun _ : Pin Pair => false
  let ctr := extremeCenter S₀ (ROOT fixed) ha hu huM
  let p := registerPrecision S₀ (ROOT fixed) ctr
  let Q := seatedParentPacking d MASK G.wordsR G.wordsC G.declared G.budget
  have hP : 10*M≤p := native_register_precision_ge_tenM created a₀ M u₀ ctr.val ha
  have h3 : 3≤L := (by decide : (3:ℕ)≤36).trans hL
  have h6 : 6≤L := (by decide : (6:ℕ)≤36).trans hL
  have hMenu : 10*M+1≤W := native_probe_menu_contains_signed_prefix M L h6
  have hM : 0<M := (show 0<L^3 by positivity).trans_le hCube
  have hw : M=24*N :=
    (Fintype.card_congr (G.layout.column.trans (colWire (column ends cycle)))).trans (actual_incidence ends).1
  have hqp : q≤p := calc
    q≤24*N := Nat.mul_le_mul_right N (by decide)
    _=M := hw.symm
    _≤10*M := Nat.le_mul_of_pos_left _ (by decide)
    _≤p := hP
  have pinPos : 0<N := by
    by_contra h
    have hn := Nat.eq_zero_of_not_pos h
    rw [hw,hn,Nat.mul_zero] at hM
    exact (Nat.lt_irrefl 0 hM)
  letI : Nonempty (Pin Pair) := Fintype.card_pos_iff.mp pinPos
  have lowBound : ((q:ℕ):ℚ)≤(24*(N:ℚ))/6-3*(24*(N:ℚ))/(L:ℕ) := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using linear_low_budget L N hL
  let hr := G.rowHead i₀ rfl
  let hc' := G.colHead i₀ rfl
  let pick : Orders d → PublicMenu MASK i₀ p := fun w =>
      publicAnchoredMenu d MASK i₀ hr hc' (anchor d w.1) (G.off _)
        ⟨w.2.val, all_physical_orders_legal d he (by positivity) M p hCube hP _ w.2⟩
  have high := same_public_high_decodes_all_signs s₀ 3 b f ell created d F MASK
    G.wordsR G.wordsC G.declared G.budget ha hu huM ready hf cfg stable hF hℓ hc
    G.endpoint he h3 hr hc' G.off (implication_tables_locally_satisfiable ends d) hCube G.capacity hP hMenu
  obtain ⟨cert⟩ := full_source_clone_certificate ends d F (implication_tables_preserve_clone_variables ends d)
  refine ⟨hP,hMenu,hqp,pick,completed_gather_count d M,high.1,high.2,?_,?_,?_⟩
  · exact lower_projects_public_high s₀ b f ell created d F Q ha hu huM ready hf q hqp
  · exact public_lower_menu_zero s₀ 3 b f ell created d F Q ha hu huM ready hf cfg stable
      hF hℓ hc N cert q lowBound hqp
  · exact no_sign_decoder_from_public_low_menu s₀ 3 b f ell created d F Q ha hu huM ready hf cfg stable
      hF hℓ hc N cert q lowBound hqp

theorem literal_implication_atlas_public_J9
    (hF : 0<f.natDegree) (hc : 0<created)
    (large : 2^(9*131072-1) < sourceSize (Fintype.card (Pin Pair)))
    (cfg : RootBounds (sourceSize (Fintype.card (Pin Pair))) 3 f)
    [Fact (Irreducible (residuePoly f))] :
    ∃ (copyCount : ℕ), ∃ geom : SourceGeometry ends (stepA (Nat.clog 2 (sourceSize (Fintype.card (Pin Pair)))) 0) copyCount,
      ImplicationPublicWorld ends f ell created geom hf hℓ := by
  obtain ⟨b,⟨G⟩⟩ := original_source_geometry_at_printed_root ends large
  exact ⟨b,G,implication_public_world_complete ends f ell created G hf hℓ hF hc large cfg⟩


/-- Full printed J9 on a genuine simple cubic graph's triangle replacement,
with all four original implication clauses at each pin vertex. The graph,
layout, public modes and probe prefix are fixed before the sign assignment;
the low channel is a projection of the same unchanged high register. -/
theorem cubic_graph_implication_public_J9
    {V : Type} [LinearOrder V] [Fintype V] (B : SimpleGraph V) [DecidableRel B.Adj]
    (cubic : Cubic B) (f : ℤ[X]) (ell created : ℕ)
    (hf : f.Monic) (hℓ : 0<ell) (hc : 0<created)
    (cfg : RootBounds (sourceSize (Fintype.card (Pin (Edge B)))) 3 f)
    [Fact (Irreducible (residuePoly f))] :
    ∃ copies : ℕ,
      ∃ geom : SourceGeometry (atlas B cubic)
        (stepA (Nat.clog 2 (sourceSize (Fintype.card (Pin (Edge B))))) 0) copies,
          ImplicationPublicWorld (atlas B cubic) f ell created geom hf hℓ := by
  have range := root_bounds_force_j9_range _ f cfg
  exact literal_implication_atlas_public_J9 (atlas B cubic) f ell created hf hℓ range.1 hc range.2 cfg

#print axioms ImplicationPublicWorld
#print axioms implication_public_world_complete
#print axioms literal_implication_atlas_public_J9
#print axioms cubic_graph_implication_public_J9
end
end J9R21Implication
