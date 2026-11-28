import J6R33OriginalJ6Count
import J6R24MeteredRecursionFee

/-! Pay the actual implementation of a legal completed slot inside the
unchanged original communication, interpolation and final readout.
Delta separates that added expense from the original oracle boundary;
no underlying run is assumed to cost zero. -/
namespace J6R36SharedGateway
open scoped Polynomial Classical BigOperators
open Polynomial AOracleMachineTime AOracleMachineTimeTape A1R10 A1R11 A1R12
open J6R22Active J6R24MeteredRecursion J6R26StablePreparedRoot J6R33OriginalJ6
open J6R27PrescribedProbe J6R14ZeroMode J6Mesh J6OrientedHost
set_option maxHeartbeats 11000000
set_option maxRecDepth 2350
set_option linter.unusedSectionVars false

theorem interp_zero_delta {p ell d : ℕ} {fw : List (Word p)}
    (hp : 0<p) (he : 0<fw.length) (hv : 0<ell)
    (node paid base : Fin (d+1)→Meter (UVBlock fw ell))
    (fee : Fin (d+1)→ℕ) (data : ∀ j,Delta (paid j) (base j) (fee j)) :
    Delta (interpolateAt0 hp he hv node paid) (interpolateAt0 hp he hv node base)
      ((probeOrder (d+1)).map fee).sum := by
  have h := prefix_delta hp he hv (k:=1) (by decide) node paid base fee data
  refine ⟨?_,?_⟩
  · simp only [interpolateAt0,h.value]
  · simp only [interpolateAt0,h.value,h.fee]
    omega

theorem restore_delta {f : ℤ[X]} {p q ell : ℕ} (e : p=q) (F : Frame f q)
    (paid base : Meter (Block (siteFrame e F) ell))
    (fee : ℕ) (d : Delta paid base fee) :
    Delta (restoreFrame e F paid) (restoreFrame e F base) fee := by
  subst q
  exact d

theorem gather_delta {f : ℤ[X]} {p ell B R : ℕ} (F : Frame f p)
    (hb : 0<B) (hr : 0<R) (m l q width : ℕ) (cell : J6R14LayoutCost.CellWord)
    (paid base : J6Recovery.Addr m→Meter (Block F ell))
    (fee : J6Recovery.Addr m→ℕ) (d : ∀ i,Delta (paid i) (base i) (fee i)) :
    Delta (countFromMeasuredSlots F hb hr m l q width cell paid)
      (countFromMeasuredSlots F hb hr m l q width cell base) (∑ i,fee i) := by
  have data : (rowsOfSites F m paid).map Meter.result=(rowsOfSites F m base).map Meter.result := by
    unfold rowsOfSites
    simp only [List.map_ofFn]
    exact congrArg List.ofFn (funext (fun i=>(d i).value))
  have time : ((rowsOfSites F m paid).map Meter.steps).sum=
      ((rowsOfSites F m base).map Meter.steps).sum+ ∑ i,fee i := by
    unfold rowsOfSites
    simp only [List.map_ofFn,List.sum_ofFn]
    rw [←Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _=>(d i).fee)
  refine ⟨?_,?_⟩
  · simp only [countFromMeasuredSlots,data]
  · simp only [countFromMeasuredSlots,data,time]
    omega

section Address
variable {V : Type} [Fintype V]
variable {f : ℤ[X]} {m n l base native width ell : ℕ} {T : Plant V m n}
variable {w : Fin (a m)→Fin 64}
variable (G : RootShape f m l base native width T w)
variable {F : Frame f (J6SourcePrecision.printed m base)} {hf : f.Monic}

abbrev SlotProgram :=
  ∀ (i : J6Recovery.Addr m), Fin (literalDegree m native+1) →
    List Bool→Meter (Block (SiteFrame G ell F i) ell)

def paidCall
    (bank : SuppliedProbeBits (rootPreset G ell) f.natDegree) (impl : SlotProgram (ell:=ell) (F:=F) G)
    (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) :
    Meter (Block (SiteFrame G ell F i) ell) :=
  let bits := bank.read j
  let packet := signedQuery m i bits.result.val
  let received := peelRequest (m+3) packet.result
  let go := impl i j received.result
  ⟨go.result,bits.steps+packet.steps+received.steps+jetEntryWidth f.natDegree ell
    (J6SourcePrecision.printed m base)+4+go.steps⟩

theorem legal_call_delta
    (bank : SuppliedProbeBits (rootPreset G ell) f.natDegree) (impl : SlotProgram (ell:=ell) (F:=F) G)
    (O : CompletedOracle G ell F hf) (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1))
    (valid : ∀ raw,raw=List.ofFn ((rootPreset G ell).word j)→
      (impl i j raw).result=O.reply i j raw) :
    Delta (paidCall G bank impl i j) (callSlot G bank O i j)
      (impl i j (bank.read j).result.val).steps := by
  let bits := bank.read j
  let p := signedQuery m i bits.result.val
  let Q := peelRequest (m+3) p.result
  have read : Q.result=bits.result.val := congrArg Meter.result (query_payload_exact m i bits.result.val)
  have val : (impl i j Q.result).result=O.reply i j Q.result :=
    valid _ (read.trans (bank.consistent j))
  refine ⟨val,?_⟩
  change bits.steps+p.steps+Q.steps+jetEntryWidth f.natDegree ell (J6SourcePrecision.printed m base)+4+
    (impl i j Q.result).steps=bits.steps+p.steps+Q.steps+jetEntryWidth f.natDegree ell
      (J6SourcePrecision.printed m base)+4+(impl i j bits.result.val).steps
  rw [read]

noncomputable def paidSite
    (bank : SuppliedProbeBits (rootPreset G ell) f.natDegree) (impl : SlotProgram (ell:=ell) (F:=F) G)
    (hf : f.Monic) (hv : 0<ell) (i : J6Recovery.Addr m) : Meter (Block F ell) :=
  let E := SiteFrame G ell F i
  let node := readPrescribed E.hp hv (siteReader (F:=F) (hf:=hf) G bank i)
  restoreFrame (G.precision ell i) F
    (interpolateAt0 E.hp E.sizePos hv node (paidCall G bank impl i))

theorem actual_paid_site_delta
    (bank : SuppliedProbeBits (rootPreset G ell) f.natDegree) (impl : SlotProgram (ell:=ell) (F:=F) G)
    (O : CompletedOracle G ell F hf)
    (good : ∀ i j raw,raw=List.ofFn ((rootPreset G ell).word j)→(impl i j raw).result=O.reply i j raw)
    (hv : 0<ell) (i : J6Recovery.Addr m) :
    Delta (paidSite G bank impl hf hv i) (oracleSite G bank O hv i)
      ((probeOrder (literalDegree m native+1)).map
        (fun j=>(impl i j (bank.read j).result.val).steps)).sum := by
  let E := SiteFrame G ell F i
  let node := readPrescribed E.hp hv (siteReader (F:=F) (hf:=hf) G bank i)
  exact restore_delta (G.precision ell i) F _ _ _
    (interp_zero_delta E.hp E.sizePos hv node _ _ (fun j=>(impl i j (bank.read j).result.val).steps)
      (fun j=>legal_call_delta G bank impl O i j (good i j)))

end Address

#print axioms interp_zero_delta
#print axioms restore_delta
#print axioms gather_delta
#print axioms legal_call_delta
#print axioms actual_paid_site_delta
end J6R36SharedGateway
