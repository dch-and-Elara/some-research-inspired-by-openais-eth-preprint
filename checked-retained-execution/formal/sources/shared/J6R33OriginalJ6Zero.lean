import J6R33OriginalJ6Count

/-! The source's shorter query path when the binary coordinate 0
is legal. Only one completed slot per physical odd centre; no
outer probe interpolation or whole child/group tables. -/
namespace J6R33OriginalJ6
open scoped Classical Polynomial BigOperators
open Polynomial Std.Sat A1R10 A1R11 AOracleMachineTime AOracleMachineTimeTape
open J6Mesh J6OrientedHost J7R10Plant J6R9Recursive J6R11Repack J6R12Repack
open J6R14ZeroMode J6R22Active J6R22RootReadout J6R24LegalLayout J6R24MeteredRecursion
open J6R25StableCensus J6R26StablePreparedRoot
set_option maxHeartbeats 14000000
set_option maxRecDepth 2200
set_option linter.unusedSectionVars false

section DirectSite
variable {V : Type} [Fintype V]
variable {f : ℤ[X]} {m l q base native width ell : ℕ}
variable {T : Plant V m q} {w : Fin (a m)→Fin 64}
variable (G : RootShape f m l base native width T w)
variable {F : Frame f (J6SourcePrecision.printed m base)} {hf : f.Monic}

structure DirectZeroOracle (ell : ℕ) (F : Frame f (J6SourcePrecision.printed m base)) (hf : f.Monic) where
  reply : ∀ i : J6Recovery.Addr m,List Bool→Block (SiteFrame G ell F i) ell
  correct : ∀ (i : J6Recovery.Addr m) (raw : List Bool),
    raw=List.replicate f.natDegree false →
    (SiteFrame G ell F i).decode (reply i raw)=
      zeroRuntime (G.selector ell) (G.ready ell) (G.centre ell i) hf 0

def directSite (O : DirectZeroOracle G ell F hf) (i : J6Recovery.Addr m) : Meter (Block F ell) :=
  let zeros := List.replicate f.natDegree false
  let address := signedQuery m i zeros
  let input := peelRequest (m+3) address.result
  let raw : Meter (Block (SiteFrame G ell F i) ell) :=
    ⟨O.reply i input.result,address.steps+input.steps+jetEntryWidth f.natDegree ell
      (J6SourcePrecision.printed m base)+3*f.natDegree+4⟩
  restoreFrame (G.precision ell i) F raw

theorem direct_site_exact [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (O : DirectZeroOracle G ell F hf) (i : J6Recovery.Addr m) :
    F.decode (directSite G O i).result=
      (polynomial (stableRootPacking m l q width T w G.room G.half G.rankA G.rankFit.le)
        (oddAxis m) (index m i:ℤ) (J6SourcePrecision.printed m base) (rootEntryFile f ell base T w) hf).eval 0 ∧
    (directSite G O i).steps≤
      queryFee m f.natDegree+3*(m+3)+2+jetEntryWidth f.natDegree ell
        (J6SourcePrecision.printed m base)+3*f.natDegree+4 := by
  let zeros := List.replicate f.natDegree false
  let Q := signedQuery m i zeros
  let I := peelRequest (m+3) Q.result
  let raw : Meter (Block (SiteFrame G ell F i) ell) :=
    ⟨O.reply i I.result,Q.steps+I.steps+jetEntryWidth f.natDegree ell
      (J6SourcePrecision.printed m base)+3*f.natDegree+4⟩
  have inp : I=⟨zeros,3*(m+3)+2⟩ := query_payload_exact m i zeros
  have cost : Q.steps≤queryFee m f.natDegree := by
    simpa only [zeros,List.length_replicate] using (signed_query_exact m i zeros).2
  have restored := restore_frame_receipt (G.precision ell i) F raw
  constructor
  · change F.decode (restoreFrame (G.precision ell i) F raw).result=_
    rw [restored.1]
    have R : (SiteFrame G ell F i).decode raw.result=
        zeroRuntime (G.selector ell) (G.ready ell) (G.centre ell i) hf 0 :=
      O.correct i I.result (congrArg Meter.result inp)
    rw [R]
    have hF : 0<f.natDegree := F.natDegree hf ▸ F.sizePos
    rw [←physicalZeroP_eval (G.selector ell) (G.ready ell) (G.centre ell i) G.bounds (G.stable ell) hf hF 0]
    exact physical_zero_is_stable base m l q native width T w G.room G.half G.nativeFits
      G.rankA G.rankFit.le (G.ready ell) hf i
  · change (restoreFrame (G.precision ell i) F raw).steps≤_
    rw [restored.2]
    change Q.steps+I.steps+jetEntryWidth f.natDegree ell
      (J6SourcePrecision.printed m base)+3*f.natDegree+4≤_
    rw [inp]
    exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right
      (Nat.add_le_add_right cost _) _) _) _

end DirectSite

section CNF
variable {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]
variable {f : ℤ[X]} {ell : ℕ}
local notation "ms" => J7R10Readout.mCNF
local notation "qs" => J7R10Readout.qCNF
local notation "inp" => J7R10Readout.H
local notation "pm" => J6SourcePrecision.printed

theorem direct_zero_CNF [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (F : CNF V) (base l native width B R : ℕ) (w : Fin (a (ms F))→Fin 64)
    (G : RootShape f (ms F) l base native width (physicalPlant (inp F)) w)
    (widthPos : 0<width) (frame : Frame f (pm (ms F) base)) (hf : f.Monic)
    (hbase : 0<base) (hv : 0<ell) (hb : 0<B) (hr : 0<R)
    (O : DirectZeroOracle G ell frame hf)
    (factorFit : publicFactorWidth (ms F) (qs F) (exactPadOrder (ms F) (K (ms F)) l w).length+2≤B)
    (outerFit : (baseTermWidth (ms F) (outerMeshWidth (ms F)) (pm (ms F) base)+1)*(ms F+1)+3≤R) :
    let m := ms F
    let e := f.natDegree
    let sites := fun i=>directSite G O i
    let out := countFromMeasuredSlots frame hb hr m l (qs F) width
      (J6R14LayoutCost.wordCell (J6RecursiveOrientation.diagonal w)) sites
    bitsValue out.result.val=PinnedCNF.modelCount F ∧
    out.steps≤stablePadBudget (a m) (K m) l width+
      legalRootBudget (pm m base) B R ell e (width-a m+13*a m) m
        (exactPadOrder m (K m) l w).length+8+
      gatheredOracleFee m e ell (pm m base) (queryFee m e+3*(m+3)+2+
        jetEntryWidth e ell (pm m base)+3*e+4) ∧
    (probeOrder (m+1)).length=m+1 := by
  let m := ms F
  let q := qs F
  let sites (i : J6Recovery.Addr m) := directSite G O i
  let slots (i : J6Recovery.Addr m) := (slotRead frame m sites i).result
  have hF : 0<f.natDegree := frame.natDegree hf ▸ frame.sizePos
  have word (i : J6Recovery.Addr m) :
      frame.decode (slots i)=
        (polynomial (stableRootPacking m l q width (physicalPlant (inp F)) w G.room G.half G.rankA G.rankFit.le)
          (oddAxis m) (index m i:ℤ) (pm m base)
          (rootEntryFile f ell base (physicalPlant (inp F)) w) hf).eval 0 := by
    change frame.decode (slotRead frame m sites i).result=_
    rw [(stored_slot_exact frame m sites i).1]
    exact (direct_site_exact G O i).1
  have Q := compact_stable_raw_count F base base l B R width w G.room G.half widthPos
    G.rankA G.rankFit hf hbase hF hv frame.hp hb hr frame.exactMod slots
    (fun i=>by
      have h := word i
      change boxTransport frame.exactMod (uvRead frame.hp frame.words ell (slots i))=_ at h
      simpa only [boxTransport_cast] using h) factorFit outerFit
  have D := metered_slot_append frame hb hr m l q width
    (J6R14LayoutCost.wordCell (J6RecursiveOrientation.diagonal w)) sites
  have g := gather_site_bill frame m _ sites (fun i=>(direct_site_exact G O i).2)
  rw [frame.natDegree hf] at g
  have ret := D.2.trans (Nat.add_le_add_right Q.2 _)
  change _≤stablePadBudget (a m) (K m) l width+
    legalRootBudget (pm m base) B R ell frame.words.length (width-a m+13*a m) m
      (exactPadOrder m (K m) l w).length+8+gatherCost frame m sites at ret
  rw [frame.natDegree hf] at ret
  exact ⟨(congrArg (fun x : Word R=>bitsValue x.val) D.1).trans Q.1,
    ret.trans (Nat.add_le_add_left g _),List.length_ofFn⟩

end CNF
#print axioms direct_site_exact
#print axioms direct_zero_CNF
end J6R33OriginalJ6
