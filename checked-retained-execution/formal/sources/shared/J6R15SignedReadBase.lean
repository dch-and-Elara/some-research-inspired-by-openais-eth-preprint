import J7R10Readout
import J6R10IntegralFinite

/-! Signed first readout in the receiver used by the native recursion.
The base projection is a left inverse on embedded residues only. Clearing
is performed at finite precision, and signed lifting and exact odd-root
inversion are then carried out on integers. -/
namespace J6R15SignedRead
set_option maxHeartbeats 3200000
open scoped Classical BigOperators Polynomial
open Polynomial J6R9Recursive J6ActiveInterpolation NativeProbeRing

noncomputable def boxBase (p : ℕ) (f : ℤ[X]) (ell : ℕ) :
    Base p →+* Box f ell p :=
  (scalarIn p f ell).comp (AdjoinRoot.of (liftPoly p f))

noncomputable def boxAtZero (p : ℕ) (f : ℤ[X]) (ell : ℕ) (hℓ : 0<ell) :
    Box f ell p →+* Scalar p f :=
  AdjoinRoot.lift (RingHom.id _) 0 (by simp [hℓ.ne'])

noncomputable def boxProject (p : ℕ) (f : ℤ[X]) (ell : ℕ) (hf : f.Monic)
    (hℓ : 0<ell) (x : Box f ell p) : Base p :=
  projectBase p f hf (boxAtZero p f ell hℓ x)

theorem boxProject_base (p : ℕ) (f : ℤ[X]) (ell : ℕ) (hf : f.Monic)
    (hp : 0<p) (hF : 0<f.natDegree) (hℓ : 0<ell) (x : Base p) :
    boxProject p f ell hf hℓ (boxBase p f ell x) = x := by
  unfold boxProject boxBase
  rw [RingHom.comp_apply]
  change projectBase p f hf
    (AdjoinRoot.lift (RingHom.id _) 0 _ (AdjoinRoot.of _ (AdjoinRoot.of _ x))) = x
  rw [AdjoinRoot.lift_of]
  exact projectBase_left p hp f hf hF x

theorem boxBase_reduce (p : ℕ) (f : ℤ[X]) (ell : ℕ)
    (x : DenominatorBudget.TwoLocal) :
    boxBase p f ell (J6ZeroTransport.reduceBase p x) =
      J6ZeroTransport.reduceAt p (J6R10Integral.box_two_nil p f ell) x := by
  exact DFunLike.congr_fun (J6ZeroTransport.ringHom_unique
    ((boxBase p f ell).comp (J6ZeroTransport.reduceBase p))
    (J6ZeroTransport.reduceAt p (J6R10Integral.box_two_nil p f ell))) x

section Slot
variable {P R T : Type*} [Fintype P] [DecidableEq P] [CommRing R] [CommRing T]

theorem map_slot (ψ : R →+* T) (A B : (P → Bool) → Bool)
    (read : P → (P → Bool) → Bool) (x : R) :
    ψ (J6NativeHeightResidue.residueSlot A B read x) =
        J6NativeHeightResidue.residueSlot A B read (ψ x) := by
  unfold J6NativeHeightResidue.residueSlot
  simp only [map_sum]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => ?_
  by_cases h : A y && B z
  · simp only [h, if_true, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    cases hy : y i <;> cases hz : read i z <;>
      simp [J6NativeHeightResidue.ringEntry]
  · simp [h]
end Slot

open P11FullPacking J6Mesh J6OrientedHost J6OrientedHostEval J6RepairedCentered
open J6NativeHeightMesh J6NativeHeightDyadic J6NativeHeightResidue J6IntegerDecode

section Read
variable {W S : Type*} [LinearOrder S] [Fintype S] [Fintype W]

noncomputable def literalRead
    (m q base l : ℕ) (T : Plant W m q)
    (mask : MaskFamily (a m) (K m) S) (w : Fin (a m) → S)
    (hm : m≤K m) (hL : 2*l=L m) (i : J6Recovery.Addr m) :
    Base (J6SourcePrecision.printed m base) := by
  letI : DecidableEq (Pad w m (K m) l) := Classical.decEq _
  exact residueSlot (oldOK T w) (newOK T w)
    (fun k x => ((shiftAt m l mask w hm hL i k).map x).getD false)
    (J6ZeroTransport.reduceBase _ (scalar m i))

noncomputable def receiverNumeral
    (f : ℤ[X]) (ell m q base l : ℕ)
    (mask : MaskFamily (a m) (K m) S) (w : Fin (a m) → S)
    (hm : m≤K m) (hL : 2*l=L m) (i : J6Recovery.Addr m)
    (hf : f.Monic) (hℓ : 0<ell) (x : Box f ell (J6SourcePrecision.printed m base)) : ℤ × ℕ :=
  integerDecode (J6SourcePrecision.printed m base) (J6Recovery.exp m i)
    (M m) (sampleDen m i)
    (J6IntegerLayers.factor (P:=Fin m) (sampleNum m i) (sampleDen m i) (index m i) q
       (J6PhysicalInteger.loads m l mask w hm hL i)) (boxProject _ f ell hf hℓ x)

/-- The signed decoder sees the actual printed base residue once the
received Box value has been identified with the genuine literal root
contraction. No numerator magnitude or odd-root oracle is assumed. -/
theorem receiverNumeral_exact
    (f : ℤ[X]) (ell m q base l : ℕ) (T : Plant W m q)
    (mask : MaskFamily (a m) (K m) S) (w : Fin (a m) → S)
    (hm : m≤K m) (hL : 2*l=L m) (i : J6Recovery.Addr m)
    (hf : f.Monic) (hp : 0<J6SourcePrecision.printed m base) (hF : 0<f.natDegree)
    (hℓ : 0<ell) (x : Box f ell (J6SourcePrecision.printed m base))
    (hS : Fintype.card S=64) (hz : coreA T (fun _ => false)=true)
    (recv : x = boxBase _ f ell (literalRead m q base l T mask w hm hL i)) :
    receiverNumeral f ell m q base l mask w hm hL i hf hℓ x =
      (J6IntegerLayers.oldLayer (coreA T) (coreB T) (sampleNum m i) (sampleDen m i),
        J6SourcePrecision.printed m base) := by
  unfold receiverNumeral
  rw [recv,boxProject_base _ _ _ _ hp hF]
  unfold literalRead
  exact J6PhysicalInteger.printed_receiver_no_fit_assumption
    m base l q mask w hm hL T hz i hS

theorem receiverSample_exact
    (f : ℤ[X]) (ell m q base l : ℕ) (T : Plant W m q)
    (mask : MaskFamily (a m) (K m) S) (w : Fin (a m) → S)
    (hm : m≤K m) (hL : 2*l=L m) (i : J6Recovery.Addr m)
    (hf : f.Monic) (hp : 0<J6SourcePrecision.printed m base) (hF : 0<f.natDegree)
    (hℓ : 0<ell) (x : Box f ell (J6SourcePrecision.printed m base))
    (hS : Fintype.card S=64) (hz : coreA T (fun _ => false)=true)
    (recv : x = boxBase _ f ell (literalRead m q base l T mask w hm hL i)) :
    ((receiverNumeral f ell m q base l mask w hm hL i hf hℓ x).1:ℚ)/(sampleDen m i:ℚ)^m =
      (J7R10Readout.layer m q T).eval (point m i) := by
  have hnum := receiverNumeral_exact f ell m q base l T mask w hm hL i hf hp hF hℓ x hS hz recv
  rw [hnum]
  exact (congrArg (fun x : ℤ => (x : ℚ)/(sampleDen m i:ℚ)^m)
    (J7R10Readout.numeral_exact m q base l T mask w hm hL hS hz i).symm).trans
    (J7R10Readout.sample_exact m q base l T mask w hm hL hS hz i)

end Read

#print axioms boxProject_base
#print axioms boxBase_reduce
#print axioms map_slot
#print axioms receiverNumeral_exact
#print axioms receiverSample_exact
end J6R15SignedRead