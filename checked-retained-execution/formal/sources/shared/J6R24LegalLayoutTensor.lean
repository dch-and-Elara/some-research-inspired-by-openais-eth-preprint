
import J6R24LegalLayoutStable
import J6R15PlantedIdentityRoot
import J6R15PlantedIdentityCenter
import J6R15SignedReadBase

/-! Retarget the actual root network and EntryFile onto a new legal
physical chart. Every finite Cauchy coefficient is expanded at the
new page and slot. Equality of raw values across layouts is neither a
premise nor a conclusion. -/
namespace J6R24LegalLayout
open scoped Classical BigOperators Polynomial
open Polynomial DenominatorBudget P11FullPacking J6Mesh J6OrientedHost J6OrientedHostEval
open J6RecursiveOrientation J6RepairedCentered J6R23PaddingCensus J6R15PlantedIdentity
open J6R10Repack J6R10Integral J6R11Integral J6R11Repack J6R9Recursive J6R15SignedRead
open J6R9PacketLocal
set_option linter.unusedSectionVars false
set_option maxHeartbeats 22000000
set_option maxRecDepth 1750

section Root
variable {V : Type} [Fintype V]

noncomputable def rechartPacking
    (m l q : ℕ) (T : Plant V m q) (w : Fin (a m)→Fin 64)
    (mask : MaskFamily (a m) (K m) (Fin 64)) (hm : m≤K m) (hL : 2*l=L m)
    (C : LegalRootChart w hm hL)
    (good : ∀ e,physicalCell mask (C.seats e)=
      (J6PhysicalPacking.place (diagonal w) m (K m) l hm e).1) :
    PhysicalPacking (rootNetwork (b:=K m) (l:=l) T w) (a m) (Fin 64) :=
  let P := rootPacking m l q T w mask hm hL (Fintype.card_fin 64)
  { P with
    seat := C.seats.toEmbedding
    exactCell := fun e=> (good e).trans
      ((orientation_preserved mask w m l hm hL e).symm.trans (P.exactCell e)) }

noncomputable def stableRootPacking
    (m l q width : ℕ) (T : Plant V m q) (w : Fin (a m)→Fin 64)
    (hm : m≤K m) (hL : 2*l=L m) (ha : a m≤width) (cap : K m * L m≤2^width) :
    PhysicalPacking (rootNetwork (b:=K m) (l:=l) T w) (a m) (Fin 64) :=
  rechartPacking m l q T w (fun _ _ _=>false) hm hL (deterministicLegal ha cap w hm hL)
    (deterministic_legal_cell ha cap w hm hL)

noncomputable def chartKernel (p : ℕ) (f : ℤ[X]) (ell m l : ℕ) (w : Fin (a m)→Fin 64)
    (hm : m≤K m) (hL : 2*l=L m) (C : LegalRootChart w hm hL)
    (t : ℤ) (z : Box f ell p) (r s : Ports m l w) : Box f ell p :=
  letI : DecidableEq (Page (a m) (K m) (Fin 64)) := Classical.decEq _
  if (C.seats r).1=(C.seats s).1 then
    (W (a m) t ((C.seats s).2.val-(C.seats r).2.val : ℤ)).eval₂
      (J6ZeroTransport.reduceAt p (box_two_nil p f ell)) z
  else 0

theorem native_chart_tensor_expansion
    (f : ℤ[X]) (ell base p m l q : ℕ) (T : Plant V m q) (w : Fin (a m)→Fin 64)
    (mask : MaskFamily (a m) (K m) (Fin 64)) (hm : m≤K m) (hL : 2*l=L m)
    (C : LegalRootChart w hm hL)
    (good : ∀ e,physicalCell mask (C.seats e)=
      (J6PhysicalPacking.place (diagonal w) m (K m) l hm e).1)
    (hf : f.Monic) (hbase : 0<base) (hF : 0<f.natDegree) (hℓ : 0<ell)
    (t : ℤ) (z : Box f ell p) :
    ((parentJet (rechartPacking m l q T w mask hm hL C good)
      (rootEntryFile f ell base T w) hf t).map (reduce p f ell)).eval z =
      J6R10Integral.contract (chartKernel p f ell m l w hm hL C t z)
        (fun y : Ports m l w→Bool=>if oldOK T w y then 1 else 0)
        (fun x : Ports m l w→Bool=>if newOK T w x then 1 else 0) := by
  letI : DecidableEq (Page (a m) (K m) (Fin 64)) := Classical.decEq _
  rw [parentJet,network_finite]
  let E := Ports m l w
  let N := rootNetwork (b:=K m) (l:=l) T w
  let file := rootEntryFile (b:=K m) (l:=l) f ell base T w
  have hleft : (reduce p f ell) ∘ rowProduct N file hf = fun y : E→Bool =>
      if oldOK T w y then 1 else 0 :=
    funext (old_table_receives f ell base p T w hf hbase hF hℓ)
  have hright : (reduce p f ell) ∘ colProduct N file hf = fun x : E→Bool =>
      if newOK T w x then 1 else 0 :=
    funext (new_table_receives f ell base p T w hf hbase hF hℓ)
  change J6R10Integral.contract (chartKernel p f ell m l w hm hL C t z)
    ((reduce p f ell) ∘ rowProduct N file hf) ((reduce p f ell) ∘ colProduct N file hf)=_
  rw [hleft,hright]

theorem chart_kernel_at_odd_zero (p : ℕ) (f : ℤ[X]) (ell m l : ℕ) (w : Fin (a m)→Fin 64)
    (hm : m≤K m) (hL : 2*l=L m) (C : LegalRootChart w hm hL)
    (i : J6Recovery.Addr m) (r s : Ports m l w) :
    chartKernel p f ell m l w hm hL C (index m i:ℤ) 0 r s =
      if layoutShift w hm hL C (index m i) r=some s then
        J6ZeroTransport.reduceAt p (box_two_nil p f ell) (J6NativeHeightDyadic.scalar m i)
      else 0 := by
  let x := C.seats r
  let y := C.seats s
  have H : layoutShift w hm hL C (index m i) r=some s ↔
      x.1=y.1 ∧ (y.2.val:ℤ)-x.2.val=(index m i:ℤ) := by
    rw [chart_shift_iff w hm hL C]
    change (x.1=y.1 ∧ x.2.val+index m i=y.2.val)↔_
    exact and_congr_right (fun _=>by omega)
  unfold chartKernel
  by_cases hs : layoutShift w hm hL C (index m i) r=some s
  · obtain ⟨A,B⟩ := H.mp hs
    rw [if_pos hs,if_pos (show (C.seats r).1=(C.seats s).1 from A),W_eval_zero,
      if_pos (show ((C.seats s).2.val:ℤ)-(C.seats r).2.val=(index m i:ℤ) from B),rho_eq_scalar]
  · rw [if_neg hs]
    by_cases A : (C.seats r).1=(C.seats s).1
    · have B : ¬ ((C.seats s).2.val:ℤ)-(C.seats r).2.val=(index m i:ℤ) :=
        fun E=>hs (H.mpr ⟨A,E⟩)
      rw [if_pos A,W_eval_zero,if_neg B]
    · rw [if_neg A]

noncomputable def chartScalar (m l q : ℕ) (T : Plant V m q) (w : Fin (a m)→Fin 64)
    (hm : m≤K m) (hL : 2*l=L m) (C : LegalRootChart w hm hL)
    (i : J6Recovery.Addr m) : TwoLocal :=
  J6NativeHeightResidue.residueSlot (oldOK T w) (newOK T w)
    (fun r x=>((layoutShift w hm hL C (index m i) r).map x).getD false)
    (J6NativeHeightDyadic.scalar m i)

theorem stable_root_at_odd_zero (f : ℤ[X]) (ell base p m l q width : ℕ)
    (T : Plant V m q) (w : Fin (a m)→Fin 64)
    (hm : m≤K m) (hL : 2*l=L m) (ha : a m≤width) (cap : K m*L m≤2^width)
    (hf : f.Monic) (hbase : 0<base) (hF : 0<f.natDegree) (hℓ : 0<ell)
    (i : J6Recovery.Addr m) :
    let C := deterministicLegal ha cap w hm hL
    ((parentJet (stableRootPacking m l q width T w hm hL ha cap)
      (rootEntryFile f ell base T w) hf (index m i:ℤ)).map (reduce p f ell)).eval 0 =
      J6ZeroTransport.reduceAt p (box_two_nil p f ell) (chartScalar m l q T w hm hL C i) := by
  let C := deterministicLegal ha cap w hm hL
  let φ := J6ZeroTransport.reduceAt p (box_two_nil p f ell)
  dsimp only [stableRootPacking]
  rw [native_chart_tensor_expansion f ell base p m l q T w (fun _ _ _=>false) hm hL C
    (deterministic_legal_cell ha cap w hm hL) hf hbase hF hℓ]
  have W := funext fun r=>funext (chart_kernel_at_odd_zero p f ell m l w hm hL C i r)
  rw [show chartKernel p f ell m l w hm hL C (index m i:ℤ) 0= _ from W,contract_flags,
    J6ZeroTransport.contraction_of_partial]
  exact (map_slot φ (oldOK T w) (newOK T w)
    (fun r x=>((layoutShift w hm hL C (index m i) r).map x).getD false) _).symm
end Root

#print axioms native_chart_tensor_expansion
#print axioms chart_kernel_at_odd_zero
#print axioms stable_root_at_odd_zero
end J6R24LegalLayout
