import J8R59SignedReceipt

/-! At the actual high receiving precision, Lagrange takes p+1
arbitrary allowed binary lifts of the same physical singleton. There
is no reduction or re-evaluation of the underlying observations. -/
namespace J8R64
open scoped Polynomial BigOperators Classical
open Polynomial NativeProbeRing DyadicProbeCompiler J8Physical J8EndToEnd J8J9Grouped
open J6R14SpecializedBox J6R9Recursive
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-- Read the first coordinate at the *same* high precision as the input. -/
def highFirstFromBoxes (p : ℕ) (hp : 0<p) (f : ℤ[X]) (ell : ℕ) (hℓ : 0<ell)
    (W : J8R59.Roster f (Fin (p+1))) (received : Fin (p+1) → Box f ell p) : Scalar p f :=
  NativeInterpolation.decode (fun i => probe p f (W i))
    (fun i => atZero p f ell hℓ (received i)) ⟨1,by omega⟩

variable {Packet R S V G : Type*} {U : V→Type*} {L M : ℕ}
variable (d : Layout Packet R S V G U L)
variable [Fintype R] [Fintype S] [Fintype V] [Fintype G] [Fintype Packet]
variable [∀ v, Fintype (U v)]

/-- The actual grouped source polynomial's normalized coefficient, before
multiplication by the printed power of two. -/
def physicalFirstBeforeScale (e : EndpointSeating d) (he : Even L) (hL : 2<L)
    (s : S) (F : OldTables d) (sign : S→Bool) (tail : IntegralArguments d)
    (b : Fin (Fintype.card (PinTile d s))) (kt : TargetPorts d s→Source[X]) : Source :=
  (groupedNormalized (groupedTargets d s) (groupedPublic d e he s F sign tail)
    (groupedSource d e he s F sign tail b) (groupedTarget d e he s F sign tail)
    (physicalKernel d s he hL (J9FactorBounds.kernel L) b kt)).coeff 0

theorem full_precision_first_from_grouped_boxes
    (e : EndpointSeating d) (he : Even L) (hL : 2<L)
    (s : S) (F : OldTables d) (sign : S→Bool) (tail : IntegralArguments d)
    (b : Fin (Fintype.card (PinTile d s))) (kt : TargetPorts d s→Source[X])
    (a p ell : ℕ) (hp : 0<p) (hℓ : 0<ell) (f : ℤ[X]) (hf : f.Monic) (hd : 0<f.natDegree)
    [Fact (Irreducible (residuePoly f))] (W : J8R59.Roster f (Fin (p+1)))
    (received : Fin (p+1) → Box f ell p)
    (hx : ∀ i, received i = J6ActiveInterpolation.scalarIn p f ell
      (highObservation d e he hL s F sign tail b kt a p f (W i))) :
    highFirstFromBoxes p hp f ell hℓ W received =
      scaledValue p f (a+1+b.val) (physicalFirstBeforeScale d e he hL s F sign tail b kt) := by
  simp only [highFirstFromBoxes,hx,atZero_scalarIn,highObservation,physicalFirstBeforeScale]
  exact grouped_decode_binary p hp f hf hd _ (by omega) W W.injective _ _ _ _ _

/-- Exact centered integer lifting at the full precision is valid even
though the necessary height was separately certified already at 10M. -/
theorem full_precision_signed_first_from_grouped_boxes
    (e : EndpointSeating d) (he : Even L) (hL : 2<L) (a : ℕ) (hpow : L=2^a)
    (s : S) (off : d.rowLabel (pinWire d s).1≠d.pinLabel s)
    (idx : Wire R≃Fin M) (cube : L^3≤M) (capacity : L * Fintype.card Packet≤3*M)
    (F : OldTables d) (sign : S→Bool) (tail : IntegralArguments d) (higher : RestArguments d)
    (b : Fin (Fintype.card (PinTile d s))) (kt : TargetPorts d s→Source[X])
    (rest : TargetPorts d s→ℚ[X])
    (p ell : ℕ) (hp : 0<p) (hP : 10*M≤p) (hℓ : 0<ell) (f : ℤ[X]) (hf : f.Monic) (hd : 0<f.natDegree)
    [Fact (Irreducible (residuePoly f))] (W : J8R59.Roster f (Fin (p+1)))
    (received : Fin (p+1) → Box f ell p)
    (hx : ∀ i, received i = J6ActiveInterpolation.scalarIn p f ell
      (highObservation d e he hL s F sign tail b kt a p f (W i))) :
    readRational p f hf (clear d s b) (highFirstFromBoxes p hp f ell hℓ W received) =
      physicalCoeff d e he s F sign higher b rest := by
  rw [full_precision_first_from_grouped_boxes d e he hL s F sign tail b kt a p ell hp hℓ f hf hd W received hx]
  have fit10 := exactNum_centered d e he s off idx F sign b (by omega) cube capacity
  have widen : (2:ℤ)^(10*M) ≤ (2:ℤ)^p := pow_le_pow_right₀ (by decide) hP
  have fit : exactNum d e he s F sign b * 2 ∈
      Set.Ioc (-(↑((2:ℕ)^p)) : ℤ) ↑((2:ℕ)^p) := by
    push_cast
    exact ⟨(neg_le_neg widen).trans_lt fit10.1,fit10.2.trans widen⟩
  have lifting := lift_observed_first p hp f hf hd (a+1+b.val)
    (physicalFirstBeforeScale d e he hL s F sign tail b kt) (clear d s b)
    (exactNum d e he s F sign b) (clear_positive_odd d he hL s b).1.ne' fit
    (exactNum_native d e he hL a hpow s F sign tail b kt)
  exact lifting.trans (native_matches_physicalCoeff d e he hL a hpow s F sign tail higher b kt rest)

#print axioms highFirstFromBoxes
#print axioms physicalFirstBeforeScale
#print axioms full_precision_first_from_grouped_boxes
#print axioms full_precision_signed_first_from_grouped_boxes
end
end J8R64