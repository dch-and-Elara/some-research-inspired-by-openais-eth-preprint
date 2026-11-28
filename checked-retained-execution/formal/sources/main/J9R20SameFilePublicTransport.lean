
import J9R20SameFileMenu

/-! A public address alphabet for the whole menu does not depend on the
hidden signs. The dependency on the physical root in the native types is
only to select its exact retained packing, depth, size and creation tag. -/
namespace J9R20SameFile
open scoped Polynomial Classical BigOperators
open Polynomial P11FullPacking J6R9Recursive J6R10Repack J6R9PacketScopes
open J6ActiveRun J6R12Blueprint J6R11Blueprint J6R12Integral J1PPrinted
open NativeProbeRing J8Physical J6R14SpecializedBox J9R15FrozenErasurePrecision J9R15FrozenErasurePhysical
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 5500000

variable {R S V : Type} {U : V→Type}
variable [Fintype R] [Fintype S] [Fintype V] [(v:V)→Fintype (U v)]
variable (size C b : ℕ) (f : ℤ[X]) (ell created : ℕ)
local notation "a" => stepA (Nat.clog 2 size) 0
local notation "L" => ((2:ℕ)^a)
local notation "M" => Fintype.card (Wire R)
local notation "S₀" => printedParams (f:=f) (ell:=ell) size
local notation "∆" => sourceDelta size
variable (d : Layout (Page (stepA (Nat.clog 2 size) 0) b (Fin 64)) R S V (Fin 64) U ((2:ℕ)^(stepA (Nat.clog 2 size) 0)))
variable (F : OldTables d)
local notation "ROOT" => orientedRootCall d f ell created F
variable (Q : PhysicalPacking (orientedNetwork d) (stepA (Nat.clog 2 size) 0) (Fin 64))
variable (ha : 0<stepA (Nat.clog 2 size) 0) (hu : 0<stepU (Nat.clog 2 size) 0)
  (huM : stepU (Nat.clog 2 size) 0≤Fintype.card (Wire R))
local notation "CENTER" => fun sign => extremeCenter S₀ (ROOT sign) ha hu huM
local notation "p₀" => registerPrecision S₀ (ROOT (fun _=>false)) (CENTER (fun _=>false))
local notation "W" => J9PrintedSchedule.probeCount M L
variable (ready : ∀ sign, Ready (printedParams (f:=f) (ell:=ell) size) (sourceDelta size)
  (orientedRootCall d f ell created F sign))
variable (hf : f.Monic)


/-- Honest run transport at a graph-public address. These two functions do
not acquire a low file or infer a mode from the received value. -/
def publicHighObservation
    (sign : S→Bool) (z : Fin W) (η : PublicMenu Q.mask (⟨0,ha⟩ : Fin a) p₀) :
    Box f ell p₀ :=
  printedPacketProduct (s:=size) (c:=ROOT sign)
    (exactSeatSelector S₀ ∆ (ROOT sign) Q) (ready sign) (CENTER sign) z
    ((actual_extreme_address_type size b f ell created d F Q
      ha hu huM ready sign).mpr η) hf

theorem lower_projects_public_high (q : ℕ) (hqP : q≤p₀)
    (sign : S→Bool) (z : Fin W) (η : PublicMenu Q.mask (⟨0,ha⟩ : Fin a) p₀) :
    publicLowerObservation size b f ell created d F Q ha hu huM ready hf q hqP sign z η =
      lowerBox p₀ q hqP f ell
        (publicHighObservation size b f ell created d F Q ha hu huM ready hf sign z η) := rfl

set_option maxHeartbeats 7500000 in
theorem public_high_uses_literal_projection
    (cfg : RootBounds size C f) (stable : ∀ sign, Stable size C (ROOT sign))
    (hF : 0<f.natDegree) [Fact (Irreducible (residuePoly f))]
    (sign : S→Bool) (z : Fin W) (η : PublicMenu Q.mask (⟨0,ha⟩ : Fin a) p₀) :
    publicHighObservation size b f ell created d F Q ha hu huM ready hf sign z η =
      actualProjection Q (⟨0,ha⟩ : Fin a) (centerNonzero (CENTER sign))
        (extremeCenter_index S₀ ∆ (ROOT sign) (ready sign) ha hu huM) p₀
        (sampleNode S₀ f ell (ROOT sign) (ready sign).fit (CENTER sign) z)
        (orientedEntryFile d f ell created F sign) hf η.val := by
  unfold publicHighObservation
  let r := ROOT sign
  let t := CENTER sign
  let sel := exactSeatSelector S₀ ∆ r Q
  let P := packing sel (ready sign)
  let i₀ : Fin a := ⟨0,ha⟩
  let i' := centerIndex (ready sign) t
  let z₀ := sampleNode S₀ f ell r (ready sign).fit t z
  let hNZ := centerNonzero t
  let hv := extremeCenter_index S₀ ∆ r (ready sign) ha hu huM
  have htQ : P=Q := exactSeatSelector_at_root S₀ ∆ r Q (ready sign)
  have hti : i'=i₀ := Fin.ext hv
  rw [printedPacketProduct_exact (s:=size) (c:=r) sel (ready sign) t z _ hf cfg (stable sign) hF]
  letI := r.host.finiteEdge
  letI := r.host.finiteRow
  letI := r.host.finiteCol
  have transport : ∀ (P' : PhysicalPacking (orientedNetwork d) a (Fin 64)) (j : Fin a),
      P'=Q → j=i₀ → ∀ (hjs : padicValInt 2 t.val=j.val)
      (eq : PublicMenu P'.mask j p₀ = PublicMenu Q.mask i₀ p₀),
      actualProjection P' j hNZ hjs p₀ z₀ (orientedEntryFile d f ell created F sign) hf
        (eq.mpr η).val =
      actualProjection Q i₀ hNZ hv p₀ z₀ (orientedEntryFile d f ell created F sign) hf η.val := by
    intro P' j samePack sameIndex hjs eq
    subst P' j
    rfl
  exact transport P i' htQ hti rfl
    (actual_extreme_address_type size b f ell created d F Q ha hu huM ready sign)

#print axioms publicHighObservation
#print axioms lower_projects_public_high
#print axioms public_high_uses_literal_projection
end
end J9R20SameFile
