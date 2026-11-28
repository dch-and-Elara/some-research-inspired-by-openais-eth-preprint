
import J9R20SameFilePrinted
import J6R16SpecializedBoxBinding

/-! A public address alphabet for the whole menu does not depend on the
hidden signs. The dependency on the physical root in the native types is
only to select its exact retained packing, depth, size and creation tag. -/
namespace J9R20SameFile
open scoped Polynomial Classical BigOperators
open Polynomial P11FullPacking J6R9Recursive J6R10Repack J6R9PacketScopes
open J6ActiveRun J6R12Blueprint J6R11Blueprint J6R12Integral J1PPrinted
open NativeProbeRing J8Physical J6R14SpecializedBox J9R15FrozenErasurePrecision
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 5500000

abbrev PublicMenu {a b : ℕ} (mask : MaskFamily a b (Fin 64)) (i : Fin a) (p : ℕ) :=
  ↥(J6RecursiveMenu.menu p (J6R10RowAffine.weight i p mask))

theorem literal_menu_on_exact_seat {f : ℤ[X]} {ell Δ : ℕ}
    (S : Params (f:=f) (ell:=ell)) (r : Call (PhysicalHost f ell))
    (Q : PhysicalPacking r.host.network (S.levelBits r.depth) (Fin 64))
    (ready : Ready S Δ r) (t : Center S r) :
    LiteralMenu (exactSeatSelector S Δ r Q) ready t =
      PublicMenu Q.mask (centerIndex ready t) (registerPrecision S r t) := by
  let T (P : PhysicalPacking r.host.network (S.levelBits r.depth) (Fin 64)) : Type :=
    PublicMenu P.mask (centerIndex ready t) (registerPrecision S r t)
  change T (packing (exactSeatSelector S Δ r Q) ready) = T Q
  exact congrArg T (exactSeatSelector_at_root S Δ r Q ready)

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

theorem actual_extreme_address_type (sign : S→Bool) :
    LiteralMenu (exactSeatSelector S₀ ∆ (ROOT sign) Q) (ready sign) (CENTER sign) =
      PublicMenu Q.mask (⟨0,ha⟩ : Fin a) p₀ := by
  have h := literal_menu_on_exact_seat S₀ (ROOT sign) Q (ready sign) (CENTER sign)
  refine h.trans ?_
  have hHead : centerIndex (ready sign) (CENTER sign) = (⟨0,ha⟩ : Fin a) :=
    Fin.ext (extremeCenter_index S₀ ∆ (ROOT sign) (ready sign) ha hu huM)
  change PublicMenu Q.mask (centerIndex (ready sign) (CENTER sign)) p₀ = _
  rw [hHead]

/-- Both argument alphabets are public finite address sets, not a
sign-dependent reindexing by output value. -/
def publicLowerObservation (q : ℕ) (hqP : q≤p₀)
    (sign : S→Bool) (z : Fin W) (η : PublicMenu Q.mask (⟨0,ha⟩ : Fin a) p₀) :
    Box f ell q :=
  lowerBox p₀ q hqP f ell
    (printedPacketProduct (s:=size) (c:=ROOT sign)
      (exactSeatSelector S₀ ∆ (ROOT sign) Q) (ready sign) (CENTER sign) z
      ((actual_extreme_address_type size b f ell created d F Q
        ha hu huM ready sign).mpr η) hf)

theorem public_lower_menu_zero
    (cfg : RootBounds size C f) (stable : ∀ sign, Stable size C (ROOT sign))
    (hF : 0<f.natDegree) (hℓ : 0<ell) (hc : 0<created)
    [Fact (Irreducible (residuePoly f))]
    (n : ℕ) (cert : CloneCertificate d F n)
    (q : ℕ) (hq : (q:ℚ)≤(24*(n:ℚ))/6-3*(24*(n:ℚ))/(L:ℕ)) (hqP : q≤p₀) :
    ∀ (sign : S→Bool) (z : Fin W) (η : PublicMenu Q.mask (⟨0,ha⟩ : Fin a) p₀),
      publicLowerObservation size b f ell created d F Q ha hu huM ready hf q hqP sign z η = 0 := by
  intro sign z η
  unfold publicLowerObservation
  exact printed_product_low_erases size C b f ell created d F sign
    (exactSeatSelector S₀ ∆ (ROOT sign) Q) (ready sign) cfg (stable sign)
    ha hu huM hf hF hℓ hc n cert q hq hqP z
    ((actual_extreme_address_type size b f ell created d F Q
      ha hu huM ready sign).mpr η)

theorem no_sign_decoder_from_identical_menu {D A B : Type} [Nonempty D] [Zero B]
    (observations : (D→Bool)→A→B) (zero : ∀ s x, observations s x=0) :
    ¬∃ decode : (A→B)→D→Bool, ∀ s, decode (observations s)=s := by
  rintro ⟨decode,perfect⟩
  let s : D→Bool := fun _=>false
  let t : D→Bool := fun _=>true
  have eq : observations s=observations t := by
    funext ix
    exact (zero s ix).trans (zero t ix).symm
  have bad : s=t := (perfect s).symm.trans ((congrArg decode eq).trans (perfect t))
  let d := Classical.choice (inferInstance : Nonempty D)
  have := congrFun bad d
  contradiction

/-- No decoder using only the complete quoted low output channel, even
with unlimited computation and full access to every slot. The physical
layout and native address alphabet remain fixed across the adversarial
all-zero and all-one sign words. -/
theorem no_sign_decoder_from_public_low_menu [Nonempty S]
    (cfg : RootBounds size C f) (stable : ∀ sign, Stable size C (ROOT sign))
    (hF : 0<f.natDegree) (hℓ : 0<ell) (hc : 0<created)
    [Fact (Irreducible (residuePoly f))]
    (n : ℕ) (cert : CloneCertificate d F n)
    (q : ℕ) (hq : (q:ℚ)≤(24*(n:ℚ))/6-3*(24*(n:ℚ))/(L:ℕ)) (hqP : q≤p₀) :
    ¬∃ decode : (Fin W × PublicMenu Q.mask (⟨0,ha⟩ : Fin a) p₀ → Box f ell q) → S→Bool,
      ∀ sign, decode (fun z => publicLowerObservation size b f ell created d F Q
        ha hu huM ready hf q hqP sign z.1 z.2)=sign := by
  apply no_sign_decoder_from_identical_menu
  intro sign ix
  exact public_lower_menu_zero size C b f ell created d F Q
    ha hu huM ready hf cfg stable hF hℓ hc n cert q hq hqP sign ix.1 ix.2

#print axioms no_sign_decoder_from_public_low_menu
#print axioms literal_menu_on_exact_seat
#print axioms actual_extreme_address_type
#print axioms publicLowerObservation
#print axioms public_lower_menu_zero
#print axioms no_sign_decoder_from_identical_menu
end
end J9R20SameFile
