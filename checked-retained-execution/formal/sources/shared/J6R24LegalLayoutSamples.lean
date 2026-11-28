
import J6R24LegalLayoutMode

/-! Close the same-chart signed normalized sample. The positive factor
depends on the deterministic layout's own physical targets. This is
not a transport of any old frozen raw receiver. -/
namespace J6R24LegalLayout
open scoped Classical BigOperators Polynomial
open Polynomial DenominatorBudget P11FullPacking J6Mesh J6OrientedHost J6OrientedHostEval
open J6R9Recursive J6R11Repack J6R10Integral J6R11Integral J6R15SignedRead
open J6R23PaddingCensus J6NativeHeightMesh
set_option linter.unusedSectionVars false
set_option maxHeartbeats 20000000
set_option maxRecDepth 1850

section Samples
variable {V : Type} [Fintype V]

noncomputable def chartReceiverNumeral (f : ℤ[X]) (ell b m l q : ℕ) (w : Fin (a m)→Fin 64)
    (hm : m≤K m) (hL : 2*l=L m) (C : LegalRootChart w hm hL)
    (hf : f.Monic) (hℓ : 0<ell) (i : J6Recovery.Addr m)
    (z : Box f ell (J6SourcePrecision.printed m b)) : ℤ×ℕ :=
  J6IntegerDecode.integerDecode (J6SourcePrecision.printed m b) (J6Recovery.exp m i) (M m)
    (sampleDen m i)
    (J6IntegerLayers.factor (P:=Fin m) (sampleNum m i) (sampleDen m i) (index m i) q
      (chartLoads m l w hm hL C i))
    (boxProject _ f ell hf hℓ z)

private theorem slot_irrel {E R : Type*} [CommRing R]
    (F F' : Fintype E) (D D' : DecidableEq E)
    (A B : (E→Bool)→Bool) (read : E→(E→Bool)→Bool) (x : R) :
    @J6NativeHeightResidue.residueSlot R E _ F D A B read x =
    @J6NativeHeightResidue.residueSlot R E _ F' D' A B read x := by
  rw [Subsingleton.elim F F',Subsingleton.elim D D']

theorem literal_chart_receiver_exact (f : ℤ[X]) (ell b m l q : ℕ) (T : Plant V m q)
    (w : Fin (a m)→Fin 64) (hm : m≤K m) (hL : 2*l=L m) (C : LegalRootChart w hm hL)
    (hf : f.Monic) (hF : 0<f.natDegree) (hℓ : 0<ell) (i : J6Recovery.Addr m)
    (hz : coreA T (fun _=>false)=true)
    (z : Box f ell (J6SourcePrecision.printed m b))
    (received : z=J6ZeroTransport.reduceAt (J6SourcePrecision.printed m b) (box_two_nil (J6SourcePrecision.printed m b) f ell) (chartScalar (V:=V) m l q T w hm hL C i)) :
    chartReceiverNumeral f ell b m l q w hm hL C hf hℓ i z=
      (J6IntegerLayers.oldLayer (coreA T) (coreB T) (sampleNum m i) (sampleDen m i),
        J6SourcePrecision.printed m b) := by
  letI : DecidableEq (Pad w m (K m) l) := Classical.decEq _
  let p := J6SourcePrecision.printed m b
  let R := fun x y=>((layoutShift w hm hL C (index m i) x).map y).getD false
  let s := J6NativeHeightDyadic.scalar m i
  have h : J6ZeroTransport.reduceBase p (chartScalar (V:=V) m l q T w hm hL C i)=
      J6NativeHeightResidue.residueSlot (oldOK T w) (newOK T w) R
        (J6ZeroTransport.reduceBase p s) := by
    calc
      _ = J6ZeroTransport.reduceBase p (J6NativeHeightResidue.residueSlot (oldOK T w) (newOK T w) R s) := by
        unfold chartScalar
        apply congrArg (J6ZeroTransport.reduceBase p)
        apply slot_irrel
      _ = _ := map_slot (J6ZeroTransport.reduceBase p) _ _ _ _
  unfold chartReceiverNumeral
  rw [received,←boxBase_reduce,boxProject_base _ _ _ _ (printed_precision_pos m b) hF hℓ,h]
  exact legal_chart_same_normalized_sample m l q b w hm hL C T (Fintype.card_fin 64) hz i

theorem completed_stable_sample_exact (f : ℤ[X]) (ell base b m l q width : ℕ) (T : Plant V m q)
    (w : Fin (a m)→Fin 64) (hm : m≤K m) (hL : 2*l=L m) (ha : a m≤width) (cap : K m*L m≤2^width)
    (hf : f.Monic) (hbase : 0<base) (hF : 0<f.natDegree) (hℓ : 0<ell)
    (hz : coreA T (fun _=>false)=true) (i : J6Recovery.Addr m) :
    let C := deterministicLegal ha cap w hm hL
    let pack := stableRootPacking (V:=V) m l q width T w hm hL ha cap
    let z : Box f ell (J6SourcePrecision.printed m b) := (J6R14ZeroMode.polynomial pack (oddAxis m) (index m i:ℤ) (J6SourcePrecision.printed m b)
      (rootEntryFile (V:=V) f ell base T w) hf).eval 0
    chartReceiverNumeral f ell b m l q w hm hL C hf hℓ i z=
      (J6IntegerLayers.oldLayer (coreA T) (coreB T) (sampleNum m i) (sampleDen m i),
        J6SourcePrecision.printed m b) := by
  exact literal_chart_receiver_exact f ell b m l q T w hm hL _ hf hF hℓ i hz _
    (completed_stable_zero_expansion f ell base (J6SourcePrecision.printed m b) m l q width
      T w hm hL ha cap hf hbase (printed_precision_pos m b) hF hℓ i)

end Samples

#print axioms literal_chart_receiver_exact
#print axioms completed_stable_sample_exact
end J6R24LegalLayout
