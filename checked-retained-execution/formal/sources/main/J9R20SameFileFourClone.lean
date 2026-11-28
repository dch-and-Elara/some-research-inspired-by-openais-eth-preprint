
import J9R20SameFileJoint

/-! The J9 precision split on one original orientation, exact balanced
mask, declared seat and recursive parent. The same menus are in both
clauses of the result, at their original high precision. -/
namespace J9R20SameFile
open scoped Polynomial Classical BigOperators
open Polynomial P11FullPacking J6R9Recursive J6R10Repack J6R9PacketScopes J6R9PacketChild
open J6ActiveRun J6R12Blueprint J6R11Blueprint J6R12Integral J1PPrinted
open NativeProbeRing J8Physical J8EndToEnd J8J9Grouped DyadicProbeCompiler
open J6R14SpecializedBox J9R17AllPins J9R15FrozenErasurePrecision LiteralPortCompiler
open J7SourceLabels J7PrintedParamsGraph J7ToJ8Incidence
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 12000000

variable {Pair H R : Type} [Fintype Pair] [Fintype H] [Fintype R]
variable (ends : H×Bool≃Pin Pair×Fin 3)
local notation "S" => Pin Pair
local notation "V" => PrintedOld Pair H
local notation "nPin" => Fintype.card (Pin Pair)
local instance (priority := 10000) r20CloneClassicalPageEq (a b : ℕ) :
    DecidableEq (Page a b (Fin 64)) := fun x y => Classical.propDecidable (x=y)

variable (size C b : ℕ) (f : ℤ[X]) (ell created : ℕ)
local notation "a" => stepA (Nat.clog 2 size) 0
local notation "L" => ((2:ℕ)^a)
local notation "MASK" => (J7SeatPacking.balancedMask (K:=Fin 64) a b)
variable (d : Layout (Page (stepA (Nat.clog 2 size) 0) b (Fin 64)) R (Pin Pair) (PrintedOld Pair H) (Fin 64) (Ports (column ends cycle)) ((2:ℕ)^(stepA (Nat.clog 2 size) 0)))
variable (F : OldTables d) (sign : Pin Pair→Bool)
local notation "r" => orientedRootCall d f ell created F sign
local notation "S₀" => printedParams (f:=f) (ell:=ell) size
local notation "∆" => sourceDelta size

theorem same_original_four_clone_high_low
    (wordsR : R→Fin a→Fin 64) (wordsC : S⊕V→Fin a→Fin 64)
    (hC : ∀ w : Wire R, physicalCell MASK (d.seat w) = declaredCell (orientedNetwork d) wordsR wordsC w)
    (hB : Nat.card (Cell (Fin a) (Fin 64)) * (b*L) ≤ 3*Nat.card (Wire R))
    (ha : 0<a) (hu : 0<(S₀).levelWidth (r).depth) (huM : (S₀).levelWidth (r).depth≤(r).edges)
    (ready : Ready S₀ ∆ r) (cfg : RootBounds size C f) (stable : Stable size C r)
    (hf : f.Monic) (hF : 0<f.natDegree) (hℓ : 0<ell) (hc : 0<created)
    [Fact (Irreducible (residuePoly f))]
    (e : EndpointSeating d) (he : Even L) (hL : 6≤L)
    (hrow : ∀ w : Wire R, rowGroup MASK (Fin.mk 0 ha) (d.seat w)=d.rowLabel w.1)
    (hcol : ∀ w : Wire R, colGroup MASK (Fin.mk 0 ha) (d.seat w)=actualColLabel d w)
    (off : ∀ s, d.rowLabel (pinWire d s).1≠d.pinLabel s)
    (sat : ∀ g v, ∃ x, satisfied (F g v) x=true)
    {M : ℕ} (idx : Wire R≃Fin M)
    (hCube : L^3≤M) (capacity : L*Fintype.card (Page a b (Fin 64))≤3*M)
    (validClones : LocalCloneLaw d F (allCloneOwners (Pair:=Pair) (H:=H)))
    (q : ℕ) (hq : (q:ℚ)≤(24*(nPin:ℚ))/6-3*(24*(nPin:ℚ))/(L:ℕ)) :
    let t := extremeCenter S₀ r ha hu huM
    let p := registerPrecision S₀ r t
    let sel := exactSeatSelector S₀ ∆ r (seatedParentPacking d MASK wordsR wordsC hC hB)
    ∃ hP : 10*M≤p,
    ∃ hMenu : 10*M+1≤J9PrintedSchedule.probeCount (Fintype.card (Wire R)) L,
    ∃ hqp : q≤p,
    ∃ choices : Orders d→Fin (10*M+1)→LiteralMenu sel ready t,
      (∀ w i, (choices w i).val.support.card=1) ∧
      (let mPos : 0<M := (show 0<L^3 by positivity).trans_le hCube
       publicAllPinDecoder d e he F (fun w => publicCoefficient d (anchor d w.1) idx w.2 p ell
        hP hℓ f hf (hMenu.trans ready.fit) mPos (fun i =>
          printedPacketProduct (s:=size) (c:=r) sel ready t (Fin.castLE hMenu i) (choices w i) hf)) = sign) ∧
      (∀ z : Probe S₀ r, ∀ β : LiteralMenu sel ready t,
        lowerBox p q hqp f ell (printedPacketProduct (s:=size) (c:=r) sel ready t z β hf)=0) := by
  obtain ⟨cert⟩ := full_source_clone_certificate ends d F validClones
  exact same_balanced_file_high_low size C b f ell created d F sign wordsR wordsC hC hB 
    ha hu huM ready cfg stable hf hF hℓ hc e he hL hrow hcol off sat idx hCube capacity nPin cert q hq

#print axioms same_original_four_clone_high_low

end
end J9R20SameFile
