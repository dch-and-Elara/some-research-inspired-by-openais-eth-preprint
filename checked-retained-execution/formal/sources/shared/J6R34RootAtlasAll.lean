import J6R34RootAtlasCommon

/-! A single exterior (t, j, g) uses one shared root resident/probe
read. The complete actual cell/copy request generator feeds the
separate R27 page compilers. The resulting list is not supplied. -/
namespace J6R34RootAtlas
open scoped Classical Polynomial
open Polynomial AOracleMachineTime AOracleMachineTimeTape
open J6Mesh J6OrientedHost P11FullPacking J6R24LegalLayout J6R24MeteredRecursion
open J6R31RootResidentTables J6R30GeneratedRootLayout J6R30ProducedGateRegistry
open J6R32RootGeneratedRegistryInputs J6R33PageIndexedBirth J6R32ChildResidentTransfer
open J6R15ModeCost J6R27OriginalGate J6R17ModeTape J6R18ChildWrite J6R21Ancestor
open J6R14ZeroMode J6R27PrescribedProbe J6R26StablePreparedRoot J6R16ModeCost J6R20Ancestor
set_option maxHeartbeats 9500000

def buildRootAtlas {f : ℤ[X]} {D p q ell : ℕ} {W : Prescribed f D}
    (F : Frame f p) (hf : f.Monic) (probeBank : SuppliedProbeBits W f.natDegree)
    (m : ℕ) (hq : 0<q) (i : Fin (a m)) (fit : i.val+1≤q)
    (copies prec : Word q) {r c d : ℕ} (source : List (SignedHalfPort r c d))
    (g : Fin 64) (j : Fin (D+1)) (codeWidth : ℕ) (hv : 0<ell) :
    Meter (Option (List (PageRow (a m) p ell q (pageKeyWidth m) F.words i))) :=
  let raw := commonRoot F hf probeBank m hq i copies prec source g j codeWidth
  let pages := compileAtlas (w:=RootKey m) raw.result F.hp hv fit hq copies
  ⟨pages.result,raw.steps+pages.steps⟩

noncomputable def rootTable {m p ell q : ℕ} {i : Fin (a m)} {fw : List (A1R10.Word p)}
    (fields : Page (a m) (K m) (Fin 64)→OriginFields (a m) p ell q fw i) :
    List (PageRow (a m) p ell q (pageKeyWidth m) fw i) :=
  (orderedChildPages (a m) (K m)).map (fun k=>⟨residentPageKey m k,fields k⟩)

theorem actual_prescribed_root_atlas
    {V : Type} [Fintype V] {m n r c d p q ell Dg : ℕ} {T : Plant V m n}
    (source : LiteralPortFile T r c d) {f : ℤ[X]} {W : Prescribed f Dg}
    (F : Frame f p) (hf : f.Monic) (hv : 0<ell)
    (bank : SuppliedProbeBits W f.natDegree) (j : Fin (Dg+1))
    (hq : 0<q) (i : Fin (a m)) (hi : i.val+1<q)
    (copies prec : Word q) (hCopies : copies.val=K m) (hPrec : prec.val=p)
    (g : Fin 64) (codeWidth : ℕ) (codePos : 0<codeWidth)
    (refFit : 1+(writeResidents m hq i copies prec source.raw).result.roster.modes.length<2^codeWidth)
    (addrFit : K m≤2^RootKey m) :
    let R := buildRootAtlas F hf bank m hq i hi.le copies prec source.raw g j codeWidth hv
    let N := (writeResidents m hq i copies prec source.raw).result.roster.modes.length
    let P := rootChart T
    ∃ fields : Page (a m) (K m) (Fin 64)→OriginFields (a m) p ell q F.words i,
      R.result=some (rootTable fields) ∧ ((rootTable fields).map RefRow.address).Nodup ∧
      (∀ k,(locate (residentPageKey m k) (rootTable fields)).result=some (fields k)) ∧
      (∀ k,∃ ξ : Fin N≃PacketMode i (K m) (2^(i.val+1)) p,
         ∃ ms : Fin N→ModeInput (a m) p i q,
           J6R22Active.boxTransport F.exactMod (A1R10.uvRead F.hp F.words ell (fields k).probe)=
             prescribedNode W p ell j ∧
           (fields k).rows=(sourceRows P i g k (actualWires m)).map (fun row=>slotWord P row.val) ∧
           (fields k).cols=(sourceCols P i g k (actualWires m)).map (fun col=>slotWord P col.val) ∧
           (fields k).modes=List.ofFn ms ∧
           ModeMeaning P i g k (ξ.trans (packet_mode_equiv P.mask i p).symm) 0 ms ∧
           ∀ u,(ms u).code=encodeBits codeWidth u.succ.val) ∧
      R.steps≤residentsFee m q i.val p r c d+(bank.read j).steps+3*codeWidth+12+
        requestsFee (a m) (RootKey m) q (K m)+
        pagesCount (a m) (K m)*(framePayloadFee p ell F.words.length (a m) i.val q codeWidth
          (pageKeyWidth m) (M m) N (D m*K m)+onePageFee (pageKeyWidth m)+5)+6 := by
  classical
  let C := commonRoot F hf bank m hq i copies prec source.raw g j codeWidth
  let RR := writeResidents m hq i copies prec source.raw
  let P := rootChart T
  let N := RR.result.roster.modes.length
  let fee := framePayloadFee p ell F.words.length (a m) i.val q codeWidth
    (pageKeyWidth m) (M m) N (D m*K m)
  obtain ⟨_,_,_,_,_,⟨N0,ξ0,raw,_⟩,rFee⟩ :=
    actual_root_resident_tables source hq i hi copies prec hCopies hPrec F.hp
  have hn0 : N=N0 := by
    change RR.result.roster.modes.length=N0
    change RR.result.roster.modes=_ at raw
    rw [raw,List.length_ofFn]
  have point (k : Page (a m) (K m) (Fin 64)) :
      ∃ (F0 : OriginFields (a m) p ell q F.words i),
        ((C.result.atRequest (sourceRequest q (RootKey m) k)).compile F.hp hv hi.le).result=some F0 ∧
        ((C.result.atRequest (sourceRequest q (RootKey m) k)).compile F.hp hv hi.le).steps≤fee ∧
        ∃ ξ : Fin N≃PacketMode i (K m) (2^(i.val+1)) p,
          ∃ ms : Fin N→ModeInput (a m) p i q,
            J6R22Active.boxTransport F.exactMod (A1R10.uvRead F.hp F.words ell F0.probe)=prescribedNode W p ell j ∧
            F0.rows=(sourceRows P i g k (actualWires m)).map (fun row=>slotWord P row.val) ∧
            F0.cols=(sourceCols P i g k (actualWires m)).map (fun col=>slotWord P col.val) ∧
            F0.modes=List.ofFn ms ∧ ModeMeaning P i g k (ξ.trans (packet_mode_equiv P.mask i p).symm) 0 ms ∧
            ∀ u,(ms u).code=encodeBits codeWidth u.succ.val := by
    obtain ⟨fields,n,ξ,ms,ok,e,rows,cols,modes,trueModes,codes,_,paid⟩ :=
      shared_exterior_page_exact source F hf hv bank j hq i hi copies prec hCopies hPrec g codeWidth codePos refFit k
    have eq : n=N := by
      rw [hn0]
      simpa only [Fintype.card_fin] using Fintype.card_congr (ξ.trans ξ0.symm)
    subst n
    exact ⟨fields,ok,paid,ξ,ms,e,rows,cols,modes,trueModes,codes⟩
  choose fields correct foot laws using point
  obtain ⟨yes,uniq,present,amount⟩ := compile_atlas_exact (w:=RootKey m) C.result F.hp hv hi.le hq
    copies hCopies addrFit fields correct foot
  have keys (k : Page (a m) (K m) (Fin 64)) : childPageKey (RootKey m) k=residentPageKey m k := rfl
  have keysTable :
      (orderedChildPages (a m) (K m)).map (fun k=>⟨childPageKey (RootKey m) k,fields k⟩)=rootTable fields := by
    simp only [rootTable,keys]
  rw [keysTable] at yes uniq present
  refine ⟨fields,yes,uniq,(fun k=>by simpa only [keys] using present k),laws,?_⟩
  have readFee := (outer_coordinate_exact F hf bank j).2
  have shared : C.steps≤residentsFee m q i.val p r c d+(bank.read j).steps+3*codeWidth+12 := by
    change RR.steps+(outerCoordinate F hf bank j).steps+3*codeWidth+12≤_
    rw [readFee]
    exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right rFee _) _) _
  change C.steps+(compileAtlas (w:=RootKey m) C.result F.hp hv hi.le hq copies).steps≤_
  change (compileAtlas (w:=RootKey m) C.result F.hp hv hi.le hq copies).steps≤_ at amount
  change _≤residentsFee m q i.val p r c d+(bank.read j).steps+3*codeWidth+12+
    requestsFee (a m) (RootKey m) q (K m)+pagesCount (a m) (K m)*(fee+onePageFee (RootKey m+13*a m)+5)+6
  omega

#print axioms actual_prescribed_root_atlas
end J6R34RootAtlas
