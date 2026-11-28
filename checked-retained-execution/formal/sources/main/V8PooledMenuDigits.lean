import V8PooledMenuKernel

set_option autoImplicit false
set_option warningAsError true

namespace V8PooledMenu
open scoped Polynomial
open Polynomial DenominatorBudget

local instance : IsLocalization atTwoPrime.primeCompl TwoLocal := by
  unfold TwoLocal twoLocalSubalgebra
  infer_instance

private theorem archivedUnit (d : atTwoPrime.primeCompl) :
    IsUnit ((d:ℤ) : TruncatedProbeMenu.Base) := by
  have hd : ¬(2:ℤ)∣(d:ℤ) := by
    simpa only [atTwoPrime,Ideal.mem_primeCompl_iff,Ideal.mem_span_singleton] using d.property
  have hc : Nat.Coprime (d:ℤ).natAbs 2 := by
    apply Nat.Coprime.symm
    apply Nat.prime_two.coprime_iff_not_dvd.mpr
    intro hv
    exact hd (Int.natCast_dvd.mpr hv)
  have hu := IsLocalization.map_units TruncatedProbeMenu.Base (⟨(d:ℤ),hc⟩ : TruncatedProbeMenu.oddDenominators)
  have hh : algebraMap ℤ TruncatedProbeMenu.Base = Int.castRingHom TruncatedProbeMenu.Base :=
    Subsingleton.elim _ _
  rw [hh] at hu
  exact hu

/-- The archived tape localization and the native rational subalgebra
use the same integer denominators. -/
noncomputable def tapeBase : TwoLocal →+* TruncatedProbeMenu.Base :=
  IsLocalization.lift (M:=atTwoPrime.primeCompl) (g:=Int.castRingHom TruncatedProbeMenu.Base)
    archivedUnit

noncomputable def digits (p : ℕ) (U : TwoLocal[X]) : TruncatedProbeMenu.NodeMessage p :=
  TruncatedProbeMenu.encode p (U.map tapeBase)

theorem digit_exact (p : ℕ) (U : TwoLocal[X]) (j : Fin p) :
    digits p U j = J6ZeroTransport.reduceBase (p-j.val) (U.coeff j.val) := by
  unfold digits TruncatedProbeMenu.encode
  rw [Polynomial.coeff_map]
  exact RingHom.congr_fun (J6ZeroTransport.ringHom_unique
    ((TruncatedProbeMenu.reduce (p-j.val)).comp tapeBase) (J6ZeroTransport.reduceBase (p-j.val))) _

/-- One base tape receives every extension-valued probe, including
different receivers at each signed node. -/
theorem receive_digits {S : Type*} [CommRing S] {p : ℕ} (hnil : (2:S)^p=0)
    (ψ : TwoLocal →+* S) (U : TwoLocal[X]) (z : S) :
    TruncatedProbeMenu.reconstruct (digits p U) z = U.eval₂ ψ (2*z) := by
  let g := (TruncatedProbeMenu.residueCast hnil).comp (TruncatedProbeMenu.reduce p)
  rw [digits,TruncatedProbeMenu.reconstruct_eq_eval hnil g,Polynomial.eval₂_map]
  rw [J6ZeroTransport.ringHom_unique (g.comp tapeBase) ψ]

#print axioms tapeBase
#print axioms digit_exact
#print axioms receive_digits
end V8PooledMenu
