import J6R17ModeTapeBuild
import J6R17ModeTapeLayout

/-! Exact handoff into the R16 SiteTape for the same dependent site.
The only numerical operands supplied to the new producer are the
certified physical copy count, the center index, and register word. -/
namespace J6R17ModeTape
open scoped Classical Polynomial BigOperators
open AOracleMachineTime J6ActiveRun J6R12Blueprint J6R10Reachable J6R11Blueprint
open J6R16ModeCost J6R15ModeCost J6R10Repack J1PPrinted J6R14LayoutCost

variable {f : ℤ[X]} {ell : ℕ} {S : Params (f:=f) (ell:=ell)} {Δ q : ℕ}
variable (sel : Selector S Δ) {c : Call (PhysicalHost f ell)}

theorem siteTape_from_layout (hq : 0<q) (d : Ready S Δ c) (t : Center S c)
    (hi : (centerIndex d t).val+1<q) (traffic : ℕ)
    (L : LayoutReceipt (S.levelBits c.depth) (packing sel d).copies q c.edges)
    (pre : Word q) (hp : pre.val=registerPrecision S c t) :
    let a := S.levelBits c.depth
    let i := centerIndex d t
    let z := buildTape hq a i.val traffic L.boxes L.copies pre
    ∃ I : SiteTape sel d t q,
      z.result.modes=I.modes.map (encodeMode i) ∧ z.result.modes.Nodup ∧
      z.result.weights=I.words ∧ z.result.precision=I.precision ∧
      z.steps≤buildCap a q (2^(6*a)*2^(6*a)) c.edges traffic
        (packing sel d).copies (2^(i.val+1)) (registerPrecision S c t) := by
  obtain ⟨cs,he,hn,ha⟩ := L.headerMeaning
  let z := buildTape hq (S.levelBits c.depth) (centerIndex d t).val traffic L.boxes L.copies pre
  obtain ⟨ms,hN,hA,hM,hD,hW,hP,hC⟩ :=
    buildTape_exact hq (centerIndex d t) hi traffic L.boxes cs he hn ha L.copies pre
      L.copiesMeaning hp (register_positive d t)
  exact ⟨⟨ms,hN,hA,z.result.weights,z.result.precision,hW,hP⟩,hM,hD,rfl,rfl,
    by simpa only [L.boxCount,L.rowCount] using hC⟩

/-- Isolate a physical input layout receipt for every active site
occurrence. This interface never supplies a mode list or its weights. -/
structure CallLayout {s C : ℕ}
    (sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s))
    {c : Call (PhysicalHost f ell)}
    (d : Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c) where
  leftWidth : ℕ
  rightWidth : ℕ
  leftFit : leftWidth≤uniformWidth s C
  rightFit : rightWidth≤uniformWidth s C
  layout : LayoutReceipt ((printedParams (f:=f) (ell:=ell) s).levelBits c.depth)
    (packing sel d).copies (uniformWidth s C) c.edges
  precision : Center (printedParams (f:=f) (ell:=ell) s) c → Word (uniformWidth s C)
  exactPrecision : ∀ t,(precision t).val=registerPrecision (printedParams (f:=f) (ell:=ell) s) c t

#print axioms siteTape_from_layout
end J6R17ModeTape

