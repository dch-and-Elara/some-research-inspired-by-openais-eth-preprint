
import J6R25StableCensusGeometry
import J6R24LegalLayoutSamples
import J6R15SignedReadCleared
import J6R22RootReadoutNativeFactor

/-! Derive the signed integer numerator and its fit from the *new*
chart's very own register. This is stronger than mere equality of
already-normalized samples across layouts. -/
namespace J6R25StableCensus
open scoped Classical BigOperators Polynomial
open Polynomial P11FullPacking J6Mesh J6OrientedHost J6OrientedHostEval J6RepairedCentered
open J6R23PaddingCensus J6R24LegalLayout J6R22RootReadout J6R15SignedRead
open J6NativeHeight J6NativeHeightDyadic J6NativeHeightMesh J6NativeHeightResidue
open J6R9Recursive J6R10Integral J6NativeHeightClearing J6OrientedSplitSides
open J6IntegerLayers
set_option maxHeartbeats 24500000
set_option maxRecDepth 2100
set_option linter.unusedSectionVars false

variable {V : Type} [Fintype V]

def legalRead (m l : ℕ) (w : Fin (a m)→Fin 64) (hm : m≤K m) (hL : 2*l=L m)
    (C : LegalRootChart w hm hL) (i : J6Recovery.Addr m) :
    Ports m l w→(Ports m l w→Bool)→Bool :=
  fun p x=>((layoutShift w hm hL C (index m i) p).map x).getD false

noncomputable def legalFactor (m l q : ℕ) (w : Fin (a m)→Fin 64)
    (hm : m≤K m) (hL : 2*l=L m) (C : LegalRootChart w hm hL)
    (i : J6Recovery.Addr m) : ℤ :=
  J6IntegerLayers.factor (P:=Fin m) (sampleNum m i) (sampleDen m i) (index m i) q
    (chartLoads m l w hm hL C i)

theorem legal_factor_positive (m l q : ℕ) (w : Fin (a m)→Fin 64)
    (hm : m≤K m) (hL : 2*l=L m) (C : LegalRootChart w hm hL)
    (i : J6Recovery.Addr m) :
    0<legalFactor m l q w hm hL C i := by
  apply J6IntegerLayers.public_pos _ _ _ _ _ (mesh_bounds m i).1
  unfold sampleNum
  exact neg_nonpos.mpr (Int.natCast_nonneg _)

noncomputable def legalNumerator (m l q : ℕ) (T : Plant V m q) (w : Fin (a m)→Fin 64)
    (hm : m≤K m) (hL : 2*l=L m) (C : LegalRootChart w hm hL)
    (i : J6Recovery.Addr m) : ℤ := by
  letI : DecidableEq (Pad w m (K m) l) := Classical.decEq _
  exact numerator (oldOK T w) (newOK T w) (legalRead m l w hm hL C i) (sampleNum m i) (sampleDen m i)

theorem legal_rational_shape (m l q : ℕ) (T : Plant V m q) (w : Fin (a m)→Fin 64)
    (hm : m≤K m) (hL : 2*l=L m) (C : LegalRootChart w hm hL)
    (i : J6Recovery.Addr m) (hz : coreA T (fun _=>false)=true) :
    letI : DecidableEq (Pad w m (K m) l) := Classical.decEq _
    rationalSlot (oldOK T w) (newOK T w) (legalRead m l w hm hL C i) (point m i) =
      J6Recovery.layerSum m q (oldWeight (coreA T)) (oldWeight (coreB T))
        (chartLoads m l w hm hL C) i := by
  letI : DecidableEq (Pad w m (K m) l) := Classical.decEq _
  have h := (address_index m i).2.2.2
  have ht : index m i≤2*l := by omega
  unfold legalRead
  rw [oldOK_split,newOK_split,chart_read_split,split_rationalSlot,
    J6OrientedPlantValue.planted_factors _ _ _ _ ht,padding_table_factor,J6Recovery.layerSum_factorization]
  have hB : (∑ x : Fin m→Bool, J6OrientedPlantValue.wt (coreB T) x)=(2:ℚ)^q := coreB_count T
  have hA : J6OrientedPlantValue.wt (coreA T) (fun _=>false)=1 := by simp [J6OrientedPlantValue.wt,hz]
  have hR : 2*l-index m i=J6Recovery.exp m i := by unfold J6Recovery.exp; rw [hL]
  rw [hB,hA,one_pow,mul_one,←pow_mul,hR]
  unfold J6Recovery.publicFactor chartLoads J6OrientedPlantValue.wt oldWeight
  exact (mul_assoc _ _ _).trans (mul_comm _ _)

theorem legal_numerator_factorization (m l q : ℕ) (T : Plant V m q) (w : Fin (a m)→Fin 64)
    (hm : m≤K m) (hL : 2*l=L m) (C : LegalRootChart w hm hL)
    (i : J6Recovery.Addr m) (hz : coreA T (fun _=>false)=true) :
    legalNumerator m l q T w hm hL C i=
      legalFactor m l q w hm hL C i*(rootOldNumerator m q T i)^J6Recovery.exp m i := by
  letI : DecidableEq (Pad w m (K m) l) := Classical.decEq _
  have e := (address_index m i).2.2.2
  have full : index m i+J6Recovery.exp m i=L m := by unfold J6Recovery.exp; omega
  have hCard : Fintype.card (Ports m l w)=
      (index m i+J6Recovery.exp m i)*Fintype.card (Fin m)+2*Fintype.card (Pad w m (K m) l) := by
    rw [full,Fintype.card_fin,←hL,Nat.mul_comm (2*l) m]
    exact wire_cardinality (m:=m) (b:=K m) (l:=l) w
  exact J6FactorToInteger.clear_factorization (oldOK T w) (newOK T w) (legalRead m l w hm hL C i)
    (coreA T) (coreB T) m q (chartLoads m l w hm hL C) i
    (legal_loads_le_two m l w hm hL C i) hCard (legal_rational_shape m l q T w hm hL C i hz)

theorem legal_numerator_fits (m l q b : ℕ) (T : Plant V m q) (w : Fin (a m)→Fin 64)
    (hm : m≤K m) (hL : 2*l=L m) (C : LegalRootChart w hm hL)
    (i : J6Recovery.Addr m) :
    2*|legalNumerator m l q T w hm hL C i| < (↑((2:ℕ)^J6SourcePrecision.printed m b):ℤ) := by
  letI : DecidableEq (Pad w m (K m) l) := Classical.decEq _
  have hc := J6RepairedCapacity.actual_wire_count m l w hm hL (Fintype.card_fin 64)
  apply J6SourcePrecision.centered_fit_printed m b i
  unfold legalNumerator
  exact physical_height m (index m i) (P:=Ports m l w) hc (oldOK T w) (newOK T w)
    (legalRead m l w hm hL C i) (sampleNum m i) (sampleDen m i) (mesh_bounds m i).2.1 (mesh_bounds m i).2.2

theorem legal_old_root_fits (m l q b : ℕ) (T : Plant V m q) (w : Fin (a m)→Fin 64)
    (hm : m≤K m) (hL : 2*l=L m) (C : LegalRootChart w hm hL)
    (i : J6Recovery.Addr m) (hz : coreA T (fun _=>false)=true) :
    (rootOldNumerator m q T i).natAbs<2^J6SourcePrecision.printed m b := by
  apply centered_root_bound _ _ (J6Recovery.odd_exp m i)
    (legalFactor m l q w hm hL C i) _ (legal_factor_positive m l q w hm hL C i)
  rw [←legal_numerator_factorization m l q T w hm hL C i hz]
  exact legal_numerator_fits m l q b T w hm hL C i

private theorem slot_irrel {E R : Type*} [CommRing R]
    (F F' : Fintype E) (D D' : DecidableEq E) (A B : (E→Bool)→Bool)
    (read : E→(E→Bool)→Bool) (x : R) :
    @residueSlot R E _ F D A B read x=@residueSlot R E _ F' D' A B read x := by
  rw [Subsingleton.elim F F',Subsingleton.elim D D']

theorem centered_legal_raw_exact (f : ℤ[X]) (ell b m l q : ℕ) (T : Plant V m q)
    (w : Fin (a m)→Fin 64) (hm : m≤K m) (hL : 2*l=L m) (C : LegalRootChart w hm hL)
    (hf : f.Monic) (hF : 0<f.natDegree) (hℓ : 0<ell) (i : J6Recovery.Addr m)
    (raw : Box f ell (J6SourcePrecision.printed m b))
    (received : raw=J6ZeroTransport.reduceAt (J6SourcePrecision.printed m b)
      (box_two_nil (J6SourcePrecision.printed m b) f ell) (chartScalar (V:=V) m l q T w hm hL C i)) :
    (((sampleDen m i : NativeProbeRing.Base (J6SourcePrecision.printed m b))^M m *
      boxProject (J6SourcePrecision.printed m b) f ell hf hℓ raw).valMinAbs)=
        legalNumerator m l q T w hm hL C i := by
  letI : DecidableEq (Pad w m (K m) l) := Classical.decEq _
  let p := J6SourcePrecision.printed m b
  let P := Ports m l w
  let s := scalar m i
  let R := legalRead m l w hm hL C i
  letI : NeZero ((2:ℕ)^p) := ⟨by positivity⟩
  have v : J6ZeroTransport.reduceBase p (chartScalar (V:=V) m l q T w hm hL C i)=
      residueSlot (oldOK T w) (newOK T w) R (J6ZeroTransport.reduceBase p s) := by
    calc
      _ = J6ZeroTransport.reduceBase p (residueSlot (oldOK T w) (newOK T w) R s) := by
        unfold chartScalar
        apply congrArg (J6ZeroTransport.reduceBase p)
        apply slot_irrel
      _ = _ := map_slot (J6ZeroTransport.reduceBase p) _ _ _ _
  rw [received,←boxBase_reduce,boxProject_base _ _ _ _ (printed_precision_pos m b) hF hℓ,v]
  apply (ZMod.valMinAbs_spec _ _).mpr
  have hf := legal_numerator_fits m l q b T w hm hL C i
  constructor
  · have h := residueClearing (P:=P) (oldOK T w) (newOK T w) R
      (sampleNum m i) (sampleDen m i) ((J6ZeroTransport.reduceBase p) s)
      (actual_scalar_clearing (J6ZeroTransport.reduceBase p) m i)
    have c := J6RepairedCapacity.actual_wire_count m l w hm hL (Fintype.card_fin 64)
    rw [c] at h
    exact h.symm
  · let x := legalNumerator m l q T w hm hL C i
    change -(↑((2:ℕ)^p):ℤ)<x*2 ∧ x*2≤↑((2:ℕ)^p)
    change 2*|x|<(↑((2:ℕ)^p):ℤ) at hf
    constructor <;> linarith [le_abs_self x,neg_le_abs x]

#print axioms legal_factor_positive
#print axioms legal_rational_shape
#print axioms legal_numerator_factorization
#print axioms legal_numerator_fits
#print axioms legal_old_root_fits
#print axioms centered_legal_raw_exact
end J6R25StableCensus
