import J6R33StatefulArithmeticPageProducer
import J6R33PageIndexedBirthBoundary
import J6R32RootGeneratedRegistryInputsFrames

/-! The existing literal root residents and the actual *exterior*
prescribed-probe bank are shared once across the physical Pages.
A native interpolation ordinal is neither necessary nor manufactured. -/
namespace J6R34RootAtlas
open scoped Classical Polynomial
open Polynomial AOracleMachineTime AOracleMachineTimeTape
open J6Mesh J6OrientedHost P11FullPacking J6R24LegalLayout J6R24MeteredRecursion
open J6R31RootResidentTables J6R30GeneratedRootLayout J6R30ProducedGateRegistry
open J6R32RootGeneratedRegistryInputs J6R33PageIndexedBirth
open J6R15ModeCost J6R27OriginalGate J6R17ModeTape J6R18ChildWrite J6R21Ancestor
open J6R14ZeroMode J6R27PrescribedProbe J6R26StablePreparedRoot J6R16ModeCost J6R20Ancestor
set_option maxHeartbeats 6000000

def commonRoot {f : ℤ[X]} {D p q : ℕ} {W : Prescribed f D}
    (F : Frame f p) (hf : f.Monic) (probeBank : SuppliedProbeBits W f.natDegree)
    (m : ℕ) (hq : 0<q) (i : Fin (a m)) (copies prec : Word q)
    {r c d : ℕ} (source : List (SignedHalfPort r c d))
    (g : Fin 64) (j : Fin (D+1)) (codeWidth : ℕ) :
    Meter (Common F.words (a m) q codeWidth (pageKeyWidth m)) :=
  let G := writeResidents m hq i copies prec source
  let Z := outerCoordinate F hf probeBank j
  ⟨⟨G.result.axis,word g.val,word 1,G.result.roster.modes,[],G.result.mask,G.result.seats,Z.result⟩,
     G.steps+Z.steps+3*codeWidth+12⟩

noncomputable def canonicalQuery {m q : ℕ} (k : Page (a m) (K m) (Fin 64)) (g : Fin 64) : QueryKey m q :=
  ⟨residentPageKey m k,pageRef q k,word g.val⟩

theorem root_common_is_exact_outer_frames {f : ℤ[X]} {D p q m r c d : ℕ} {W : Prescribed f D}
    (F : Frame f p) (hf : f.Monic) (probeBank : SuppliedProbeBits W f.natDegree)
    (hq : 0<q) (i : Fin (a m)) (copies prec : Word q)
    (source : List (SignedHalfPort r c d)) (g : Fin 64) (j : Fin (D+1)) (codeWidth : ℕ)
    (k : Page (a m) (K m) (Fin 64)) :
    let C := commonRoot F hf probeBank m hq i copies prec source g j codeWidth
    let one := makeOuterFrames F hf probeBank m hq i copies prec source (canonicalQuery k g) j codeWidth
    C.result.atRequest (sourceRequest q (RootKey m) k)=one.result ∧ C.steps=one.steps := by
  exact ⟨rfl,rfl⟩

set_option maxHeartbeats 9500000 in
theorem shared_exterior_page_exact
    {V : Type} [Fintype V] {m n r c d p q ell Dg : ℕ} {T : Plant V m n}
    (source : LiteralPortFile T r c d) {f : ℤ[X]} {W : Prescribed f Dg}
    (F : Frame f p) (hf : f.Monic) (hv : 0<ell)
    (bank : SuppliedProbeBits W f.natDegree) (j : Fin (Dg+1))
    (hq : 0<q) (i : Fin (a m)) (hi : i.val+1<q)
    (copies prec : Word q) (hCopies : copies.val=K m) (hPrec : prec.val=p)
    (g : Fin 64) (codeWidth : ℕ) (codePos : 0<codeWidth)
    (refFit : 1+(writeResidents m hq i copies prec source.raw).result.roster.modes.length<2^codeWidth)
    (k : Page (a m) (K m) (Fin 64)) :
    let C := commonRoot F hf bank m hq i copies prec source.raw g j codeWidth
    let one := (C.result.atRequest (sourceRequest q (RootKey m) k)).compile F.hp hv hi.le
    let P := rootChart T
    let rs := sourceRows P i g k (actualWires m)
    let cs := sourceCols P i g k (actualWires m)
    ∃ (out : OriginFields (a m) p ell q F.words i) (N : ℕ), ∃ ξ : Fin N≃PacketMode i (K m) (2^(i.val+1)) p,
      ∃ ms : Fin N→ModeInput (a m) p i q,
        one.result=some out ∧
        J6R22Active.boxTransport F.exactMod (A1R10.uvRead F.hp F.words ell out.probe)=prescribedNode W p ell j ∧
        out.rows=rs.map (fun u=>slotWord P u.val) ∧ out.cols=cs.map (fun u=>slotWord P u.val) ∧
        out.modes=List.ofFn ms ∧
        ModeMeaning P i g k (ξ.trans (packet_mode_equiv P.mask i p).symm) 0 ms ∧
        (∀ u,(ms u).code=encodeBits codeWidth u.succ.val) ∧
        C.steps≤residentsFee m q i.val p r c d+(bank.read j).steps+3*codeWidth+12 ∧
        one.steps≤framePayloadFee p ell F.words.length (a m) i.val q codeWidth
          (pageKeyWidth m) (M m) N (D m*K m) :=
  root_prescribed_frames_exact source F hf hv bank j hq i hi copies prec hCopies hPrec
    k g (canonicalQuery k g) ⟨rfl,rfl,rfl⟩ codeWidth codePos refFit

#print axioms root_common_is_exact_outer_frames
#print axioms shared_exterior_page_exact
end J6R34RootAtlas
