import J6R53PublicMountAggregate
import J6R52FreshExteriorWordsShell

/-! The actual installed exterior group uses the freshly produced
root words, with no template Setup or assumed code-valid materialized
menu. Mountability still contains the selected native rooted machine,
resident leaf data and live directory conditions. -/
namespace J6R53WordIngress
open scoped Classical Polynomial BigOperators
open Polynomial AOracleMachineTime J6Mesh J6OrientedHost
open J6R24LegalLayout J6R24MeteredRecursion J6R26StablePreparedRoot
open J6R28GeneratedRootFrame J6R34RootAtlas J6R30GeneratedRootLayout
open J6R52FreshExterior J6R53PublicMount J6R15ModeCost J6R27PrescribedProbe
open J6R14ZeroMode J6R33OriginalJ6 J6R32RootGeneratedRegistryInputs
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 3100
set_option maxHeartbeats 14500000
set_option linter.unusedSectionVars false
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {f : ℤ[X]} {m n base native : ℕ} {T : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) T (constantRootWord m)}
variable {ell q rr cc dd edgew tc tj key prec tw bw rate pad : ℕ}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]





structure RetainedMounted (G : RootShape f m (printedHalf m) base native (printedRankWidth m)
    T (constantRootWord m)) (ell q rr cc dd edgew tc tj key prec tw bw rate pad : ℕ)
    (i : J6Recovery.Addr m) (j : Fin (J6R14ZeroMode.literalDegree m native+1)) (g : Fin 64) where
  outside : SetupOutsideWords G ell edgew tc tj key tw bw
  raw : LiteralPortFile T rr cc dd
  oldWidth : ℕ
  retained : Word oldWidth
  retainedTag : retained.val=J6SourcePrecision.printed m base
  copyFit : K m<2^q
  preFit : J6SourcePrecision.printed m base<2^q
  birthFit : J6SourcePrecision.printed m base<2^prec
  sameCentre : outside.centre=i
  sameSample : outside.sample.val=j.val
  sameGroup : outside.group=g
  mounted : MountedGroup (rate:=rate) (pad:=pad) G
    (attachWithRetainedPaidWords (q:=q) (prec:=prec) outside raw retained retainedTag copyFit preFit birthFit).result

variable {i : J6Recovery.Addr m} {j : Fin (J6R14ZeroMode.literalDegree m native+1)} {g : Fin 64}
variable (R : RetainedMounted G ell q rr cc dd edgew tc tj key prec tw bw rate pad i j g)

def retainedAttachment : Meter (StableExterior G ell q rr cc dd edgew tc tj key prec tw bw) :=
  attachWithRetainedPaidWords R.outside R.raw R.retained R.retainedTag R.copyFit R.preFit R.birthFit

def issueRetainedMounted : Meter (AddressGroup (ell:=ell) (q:=q) (rr:=rr) (cc:=cc) (dd:=dd)
    (edgew:=edgew) (tc:=tc) (tj:=tj) (key:=key) (prec:=prec) (tw:=tw) (bw:=bw)
    (rate:=rate) (pad:=pad) G i j g) :=
  let S := retainedAttachment R
  let h := retained_paid_words_attached_same_occurrence R.outside R.raw
    R.retained R.retainedTag R.copyFit R.preFit R.birthFit
  ⟨⟨S.result,R.mounted,h.2.1.trans R.sameCentre,(congrArg Fin.val h.2.2.1).trans R.sameSample,
    h.2.2.2.1.trans R.sameGroup⟩,S.steps+3⟩

theorem issued_retained_uses_same_site :
    (issueRetainedMounted R).result.source=(retainedAttachment R).result ∧
      (issueRetainedMounted R).result.source.source.raw=R.raw.raw :=
  ⟨rfl,rfl⟩

theorem issued_retained_fee :
    (issueRetainedMounted R).steps=exteriorRegistersFee R.oldWidth q prec+11 := by
  have H := retained_paid_words_attached_same_occurrence R.outside R.raw
    R.retained R.retainedTag R.copyFit R.preFit R.birthFit
  change (attachWithRetainedPaidWords R.outside R.raw
    R.retained R.retainedTag R.copyFit R.preFit R.birthFit).steps+3=_
  rw [H.2.2.2.2.2.2.2.2.2.2]

#print axioms issueRetainedMounted
#print axioms issued_retained_uses_same_site
#print axioms issued_retained_fee
end
end J6R53WordIngress

