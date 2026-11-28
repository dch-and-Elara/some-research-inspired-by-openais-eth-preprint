import J9R15FrozenErasureSum
import J9R14LowPrecisionMenu

/-! A reusable literal-file precision bridge. The only nonalgebraic input
is the actual pointwise factorization of its frozen old table product. -/
namespace J9R15FrozenErasureGeneric
open scoped Polynomial Classical BigOperators
open Polynomial P11FullPacking J6R9Recursive J6R10Repack J6R11Integral J6R10Integral
open J9R14LowPrecisionGeometry J9R14LowPrecisionSlots J9R14LowPrecisionTiedCube
open J9R14LowPrecisionNative J9R14LowPrecisionComplete J9R14LowPrecisionMenu
open J9R15FrozenErasurePhysical J9R15FrozenErasureProjection
open J6R9PacketScopes DenominatorBudget

noncomputable section
set_option maxHeartbeats 1400000

set_option autoImplicit false
set_option linter.unusedSectionVars false

variable {E A B G V : Type*} [Fintype E] [Fintype A] [Fintype B] [LinearOrder G] [Fintype G]
variable {a : ℕ} {N : Network E A B} {f : ℤ[X]} {ell : ℕ}
variable (P : PhysicalPacking N a G) (i : Fin a) {t : ℤ}
variable (ht : t≠0) (hv : padicValInt 2 t=i.val) (p : ℕ) (z : Box f ell p)
variable (file : EntryFile f ell N) (hf : f.Monic)
variable (old : Finset V) (own : Physical a P.copies G → V)
local notation "ρ" => (fun e : E => P.seat e)
local notation "D" => nativeSeats ρ ρ
local notation "PR" => protectedOwner D old own t
local notation "M" => Mode i p P.mask
local notation "TICKET" => legalTicket (R:=E) P.mask i p
local notation "nilp" => box_two_nil p f ell
local notation "ψ" => J6ZeroTransport.reduceAt p nilp

abbrev TailType := (E → Bool) → (Rest PR → Bool) → TwoLocal

def FrozenSplit (tails : TailType P old own (t:=t)) : Prop :=
  ∀ Y X : E → Bool,
    (reduce p f ell (rowProduct N file hf Y) * reduce p f ell (colProduct N file hf X) : Box f ell p) =
      (guardWeight PR X : Box f ell p) * ψ (tails Y (restrict PR X))

variable (tails : TailType P old own (t:=t))
variable (hTail : FrozenSplit P p file hf old own (t:=t) tails)

include hTail

theorem literal_guarded (β : M →₀ ℕ) :
    literalSlot P i ht hv p z file hf β =
      slot ρ ρ P.mask i ht hv p old own nilp z (TICKET β) Prod.fst Prod.snd (fun c => tails c.1) := by
  let L (Y X : E → Bool) (α : E → Option M) : Box f ell p :=
    ∏ e : E, actualLeg ρ ρ P.mask i ht hv p nilp z Y X e (α e)
  let F (Y X : E → Bool) : Box f ell p :=
    (guardWeight PR X : Box f ell p) * ψ (tails Y (restrict PR X))
  let accept (α : E → Option M) : Prop := allocationExponent α=β
  let U (Y X : E → Bool) : Box f ell p := ∑ α : E → Option M,
    @ite _ (accept α) (Classical.propDecidable _) (L Y X α) 0
  let YType := (E → Bool) × (E → Option M)
  let s : Finset YType :=
    @Finset.filter YType (fun c => accept c.2) (fun _ => Classical.propDecidable _) Finset.univ
  have hS : TICKET β = s := by
    ext c
    simp only [legalTicket, s, Finset.mem_filter, Finset.mem_univ, true_and, accept, allocationExponent]
  calc
    _ = (∑ Y : E → Bool, ∑ X : E → Bool, F Y X * U Y X) := by
      unfold literalSlot
      refine Finset.sum_congr rfl (fun Y _ => ?_)
      refine Finset.sum_congr rfl (fun X _ => ?_)
      rw [show _=F Y X from hTail Y X]
      apply congrArg ((F Y X) * ·)
      unfold U
      apply Finset.sum_congr rfl
      intro α _
      by_cases he : allocationExponent α=β
      · rw [if_pos he, if_pos (show accept α from he)]
      · rw [if_neg he, if_neg (show ¬accept α from he)]
    _ = ∑ c ∈ s, ∑ X : E → Bool, F c.1 X * L c.1 X c.2 :=
      J9R15FrozenErasureSum.equal_sweeps F L accept
    _ = _ := by
      rw [← hS]
      rfl

theorem projected_dvd {R : Type*} [CommRing R] (σ : Box f ell p →+* R)
    (hPorts : ∀ u∈old, ∃ q : E, own (ρ q)=u) (β : M →₀ ℕ) :
    (2:R)^(normalizedCost P.mask i p β+((kept D old own t).card-∑ m : M, β m)) ∣
      σ (actualProjection P i ht hv p z file hf β) := by
  rw [← exact_literal_projection P i ht hv p z file hf β,
    literal_guarded P i ht hv p z file hf old own tails hTail]
  have hβ : ∀ c∈TICKET β, (∑ r : E, LiteralPortCompiler.exponent (c.2 r))=β :=
    fun c hc => (legal_exact P.mask i p β c).mp hc
  rw [slot_normalized ρ ρ P.mask i ht hv p old own nilp z (TICKET β) Prod.fst Prod.snd
    (fun c => tails c.1) β hβ]
  simp only [map_mul,map_pow,map_ofNat,hom_eval₂]
  exact PrecisionErasure.completed_slot_dvd (σ.comp ψ) _ (σ z)
    (kept D old own t).card (∑ m : M, β m) (normalizedCost P.mask i p β)
    (menu_coefficients D old own t a (take ρ ρ P.mask i) (kernel ρ P.mask i ht hv p)
      (momentCoeff ρ P.mask i p) (TICKET β) Prod.fst Prod.snd (fun c => tails c.1)
      (old_ports_supply ρ ρ old own (t:=t) hPorts) β hβ)

theorem projected_zero {R : Type*} [CommRing R] (σ : Box f ell p →+* R)
    (hPorts : ∀ u∈old, ∃ q : E, own (ρ q)=u) (q : ℕ) (hNil : (2:R)^q=0)
    (hprec : q≤(kept D old own t).card) (β : M →₀ ℕ) :
    σ (actualProjection P i ht hv p z file hf β)=0 := by
  have hk := native_cost_ge_count P.mask i p β
  have hq : q≤normalizedCost P.mask i p β+((kept D old own t).card-∑ m : M, β m) := by omega
  have hh := (pow_dvd_pow (2:R) hq).trans (projected_dvd P i ht hv p z file hf old own tails hTail σ hPorts β)
  rwa [hNil,zero_dvd_iff] at hh

#print axioms literal_guarded
#print axioms projected_dvd
#print axioms projected_zero
end
end J9R15FrozenErasureGeneric
