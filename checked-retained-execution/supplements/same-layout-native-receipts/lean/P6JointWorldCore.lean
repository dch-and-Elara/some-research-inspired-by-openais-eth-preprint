import J8RelaxedPublicHigh
import P6JointWorldLow
import P6JointGeometryModel

namespace Paper6JointSeating
open scoped Polynomial Classical BigOperators
open Polynomial P11FullPacking J6R9Recursive J6R10Repack J6R9PacketScopes J6R9PacketChild
open J6ActiveRun J6R12Blueprint J6R11Blueprint J6R12Integral J1PPrinted
open NativeProbeRing J8Physical J8EndToEnd J8J9Grouped DyadicProbeCompiler
open J9R15FrozenErasurePrecision J6R14SpecializedBox J9R20SameFile
open J7SourceLabels J7PrintedParams J7PrintedParamsGraph J7ToJ8Incidence J7SeatSource
open J9R21Implication J9R17AllPins J7LiteralGraph
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 9000000
local instance (priority := 10000) pageEq (a b : ℕ) : DecidableEq (Page a b (Fin 64)) :=
  fun x y => Classical.propDecidable (x=y)

variable {Pair H : Type} [Fintype Pair] [Fintype H]
variable (ends : H×Bool ≃ Pin Pair×Fin 3)
local notation "N" => Fintype.card (Pin Pair)
local notation "s₀" => sourceSize N
local notation "a₀" => stepA (Nat.clog 2 s₀) 0
local notation "u₀" => stepU (Nat.clog 2 s₀) 0
local notation "L" => ((2:ℕ)^a₀)
local notation "R" => Subdivision Pair (OrdinaryRow Pair H)
local notation "M" => Fintype.card (J8Physical.Wire R)
local notation "W" => J9PrintedSchedule.probeCount M L
variable {b : ℕ} (geom : JointSourceGeometry ends (stepA (Nat.clog 2 (sourceSize (Fintype.card (Pin Pair)))) 0) b)
local notation "d" => geom.layout
local notation "F" => implicationOldTables ends geom.layout
local notation "MASK" => (J7SeatPacking.balancedMask (K:=Fin 64) a₀ b)
local notation "Q" => seatedParentPacking d MASK geom.wordsR geom.wordsC geom.declared geom.budget
variable (f : ℤ[X]) (ell created : ℕ) (hf : f.Monic) (hℓ : 0<ell)
local notation "ROOT" => orientedRootCall d f ell created F
local notation "S₀" => printedParams (f:=f) (ell:=ell) s₀
local notation "∆" => sourceDelta s₀


/-- One selected geometry and one original file per sign input; no
regeneration or narrowing of addresses in the low receiver. -/
def JointImplicationWorld : Prop :=
  ∃ ha : 0<a₀, ∃ hu : 0<u₀, ∃ huM : u₀≤M,
  ∃ ready : ∀ sign, Ready S₀ ∆ (ROOT sign),
  ∃ he : Even L, ∃ hCube : L^3≤M,
    let i₀ := (Fin.mk 0 ha : Fin a₀)
    let fixed := fun _ : Pin Pair => false
    let ctr := extremeCenter S₀ (ROOT fixed) ha hu huM
    let p := registerPrecision S₀ (ROOT fixed) ctr
    ∃ hP : 10*M≤p, ∃ hMenu : 10*M+1≤W,
      let fit := hMenu.trans (ready fixed).fit
      let hM : 0<M := (show 0<L^3 by positivity).trans_le hCube
      let raw := publicHighObservation s₀ b f ell created d F Q ha hu huM ready hf
      ∃ pick : Orders d → PublicMenu MASK i₀ p,
        Fintype.card (Orders d × Fin (10*M+1))=N*(10*M+1) ∧
        (∀ w, (pick w).val.support.card=1) ∧
        (∀ sign, J8Physical.Relaxed.publicAllPinDecoder d geom.endpoint he F (fun w =>
          publicCoefficient d (anchor d w.1) (Fintype.equivFin (J8Physical.Wire R))
            w.2 p ell hP hℓ f hf fit hM
            (fun j => raw sign (Fin.castLE hMenu j) (pick w)))=sign) ∧
        (∀ (sign : Pin Pair→Bool)
            (t : Center S₀ (ROOT sign)) (z : Probe S₀ (ROOT sign))
            (β : LiteralMenu (exactSeatSelector S₀ ∆ (ROOT sign) Q) (ready sign) t),
          ∃ hq : min (geom.keep false).card (geom.keep true).card ≤ registerPrecision S₀ (ROOT sign) t,
          lowerBox (registerPrecision S₀ (ROOT sign) t) (min (geom.keep false).card (geom.keep true).card) hq f ell
            (printedPacketProduct (exactSeatSelector S₀ ∆ (ROOT sign) Q)
              (ready sign) t z β hf)=0)

theorem joint_literal_world_complete
    (hF : 0<f.natDegree) (hc : 0<created)
    (large : 2^(9*131072-1) < s₀)
    (cfg : RootBounds s₀ 3 f) [Fact (Irreducible (residuePoly f))] :
    JointImplicationWorld ends geom f ell created hf hℓ := by
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
  have hP : 10*M≤p := native_register_precision_ge_tenM created a₀ M u₀ ctr.val ha
  have h3 : 3≤L := (by decide : (3:ℕ)≤36).trans hL
  have h6 : 6≤L := (by decide : (6:ℕ)≤36).trans hL
  have hMenu : 10*M+1≤W := native_probe_menu_contains_signed_prefix M L h6
  let hr := geom.rowHead i₀ rfl
  let hc' := geom.colHead i₀ rfl
  let pick : Orders d → PublicMenu MASK i₀ p := fun w =>
    publicAnchoredMenu d MASK i₀ hr hc' (anchor d w.1) (geom.off _)
      ⟨w.2.val, all_physical_orders_legal d he (by positivity) M p hCube hP _ w.2⟩
  have high := J8Physical.Relaxed.same_public_high_decodes_all_signs s₀ 3 b f ell created
    d F MASK geom.wordsR geom.wordsC geom.declared geom.budget ha hu huM ready hf cfg stable hF
    hℓ hc geom.endpoint he h3 hr hc' geom.off (implication_tables_locally_satisfiable ends d)
    hCube geom.capacity hP hMenu
  refine ⟨hP,hMenu,pick,completed_gather_count d M,high.1,high.2,?_⟩
  intro sign t z β
  have hw : M=24*N := (actualCloneCert ends geom).wireCount
  have heq : Fintype.card (Clones Pair) = 4*N := by
    simp [Clones,Index,Fintype.card_prod,Nat.mul_comm]
  have capM : min (geom.keep false).card (geom.keep true).card ≤ M := by
    have hwF := Finset.card_le_card (Finset.subset_univ (geom.keep false))
    rw [Finset.card_univ,heq] at hwF
    exact (min_le_left _ _).trans (hwF.trans ((Nat.mul_le_mul_right N (by decide : 4≤24)).trans_eq hw.symm))
  have capP : 10*M ≤ registerPrecision S₀ (ROOT sign) t :=
    native_register_precision_ge_tenM created a₀ M u₀ t.val ha
  have hqp := (capM.trans (Nat.le_mul_of_pos_left M (by decide : 0<10))).trans capP
  refine ⟨hqp,?_⟩
  have both : ∀ side, (min (geom.keep false).card (geom.keep true).card)≤(geom.keep side).card := by
    intro s
    cases s
    · exact min_le_left _ _
    · exact min_le_right _ _
  exact joint_atlas_same_geometry_all_nonzero_erases ends geom f ell created sign (ready sign) cfg
    (stable sign) hf hF hℓ hc (min (geom.keep false).card (geom.keep true).card) both t z β hqp

#print axioms JointImplicationWorld
#print axioms joint_literal_world_complete
end
end Paper6JointSeating



