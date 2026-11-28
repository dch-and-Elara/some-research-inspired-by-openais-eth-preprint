import J6R24MeteredRecursionActive
import J6R24MeteredRecursionSource
import J6R22ActiveSiteReceipt

/-! Literal origin weights consume the finite quotient delivered by the
same centre. The only reply premise here concerns the child interpreter
and is discharged by the whole-tree induction, not assumed at the root. -/
namespace J6R24MeteredRecursion
open scoped Polynomial Classical
open Polynomial A1R10 A1R12 AOracleMachineTime
open J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable
open J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R19Retained J6R22Active J6R23ScheduleWeight HermiteLoss

variable {f : ℤ[X]} {ell s : ℕ}
variable (sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s))
variable (r : Call (PhysicalHost f ell)) (hf : f.Monic)
variable [DecidableEq (Envelope (N sel) (Childs sel) r)]
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "Sh" => (paddedShape (N sel) (Childs sel) r)
variable {c : Call (PhysicalHost f ell)}
variable (hc : NativeReach (Plan sel) r c)
variable (d : Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c)
variable {t : Center (printedParams (f:=f) (ell:=ell) s) c}
local notation "Alev" => (Shape.levelBits S (Call.depth c))
local notation "Ulev" => (Shape.levelWidth S (Call.depth c))
local notation "pₜ" => (registerPrecision S c t)
local notation "kₜ" => (order (Call.edges c) Ulev (Subtype.val t))
variable {bank : Bank f}

include hc in
set_option maxHeartbeats 5800000 in
theorem centre_scaled_term {q B j : ℕ} (hv : 0<ell) (high : Frame f q)
    (D : CentreDesc sel d t bank)
    (child : CentreChild (sel:=sel) (d:=d) (t:=t) bank)
    (hu : 0<Ulev) (huM : Ulev≤c.edges) (hB : commonLoss Alev c.edges Ulev≤B)
    (hj : j<kₜ)
    (hChild : ∀ z β g,(bank pₜ (register_positive d t)).decode (child z β g).result =
      (J6R12Blueprint.sourceBlueprint sel r hf).program.run
        ((Plan sel).child c ⟨⟨t,z,β,g⟩,d.active⟩)) :
    let J := (D.site hv child).run Alev t.val
    high.decode (D.term hv hf high B J.result j).result=
      reduce q f ell (localScalar f ell (scaledWeight Alev Ulev (sourceH c.edges Ulev) B j t.val)*
        approxJet Sh f ell c d.fit (sourceReplies sel r hf c) t.val j) := by
  let K := (D.site hv child)
  let L := bank pₜ (register_positive d t)
  let τ : Center Sh c := ⟨t.val,t.property⟩
  let E : (Box f ell pₜ)[X] := (integralE f ell Alev c.edges Ulev t.val).map (reduce pₜ f ell)
  let Φ := quotientAt Sh f ell c d.fit (sourceReplies sel r hf c) τ E
  have hJ : jetMap (boxTransport L.exactMod) kₜ (jetRead L.hp L.sizePos (K.run Alev t.val).result)=
      AdjoinRoot.mk (X^kₜ) Φ := by
    exact (actual_finite_centre sel r hf t hc d K (L.natDegree hf) L.exactMod D.literal D.roster.distinct
      D.roster.complete D.roster.exponents D.modeUnique D.modeComplete hChild).1
  have hLoss : totalLoss Alev (sourceH c.edges Ulev) j t.val≤B :=
    (actual_weight_loss_le (a:=Alev) hu huM hj).trans hB
  have h := (termM_exact L.hp L.sizePos high.hp high.sizePos hv hf L.exactMod high.exactMod
    t.property hLoss D.roster (K.run Alev t.val).result hj Φ hJ).1
  change high.decode (D.term hv hf high B (K.run Alev t.val).result j).result=_
  unfold approxJet
  have ht : t.val∈active ((Sh).levelBits c.depth) c.edges ((Sh).levelWidth c.depth) := t.property
  rw [dif_pos ht]
  exact h

#print axioms centre_scaled_term
end J6R24MeteredRecursion



