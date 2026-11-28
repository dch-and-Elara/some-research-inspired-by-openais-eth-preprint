import J6R21AncestorLeafQuery
import J6R21LeafOrigin
import J6R11RepackRootHost

/-! Both source entry kinds connect to the same leaf callback ABI.
A retained original gate uses the scanned port-address gate tape.
A generated entry uses the valid found bank result, not the fallback.
Preparation/registration of the two types of verified tapes is separate. -/
namespace J6R21Ancestor
open scoped Polynomial
open A1R10 A1R11 A1R12 AOracleMachineTime AOracleCoordinates
open J6R18ChildWrite J6R10Repack J6R11Blueprint J6R11Repack J6OrientedHost J6R21Leaf

def requireWord {p ell : ℕ} (hp : 0<p) {fw : List (Word p)}
    (d : Meter (Option (UVBlock fw ell))) : Meter (UVBlock fw ell) :=
  match d.result with
  | some v => ⟨v,d.steps+2⟩
  | none => ⟨uvZero hp fw ell,d.steps+uvWidth fw.length ell p+4⟩

theorem requireWord_hit {p ell : ℕ} (hp : 0<p) {fw : List (Word p)}
    (d : Meter (Option (UVBlock fw ell))) (u : UVBlock fw ell)
    (h : d.result=some u) :
    requireWord hp d=⟨u,d.steps+2⟩ := by
  simp only [requireWord,h]

noncomputable def tracedSlot {f : ℤ[X]} {ell n : ℕ} {root cur : Point f ell}
    (tr : Trace root cur) (ord : Fin n≃cur.host.Edge) (p : PortAt root) : Fin n :=
  ord.symm (edge (tr.back.symm p).val)

theorem traced_slot_input {f : ℤ[X]} {ell n : ℕ} {root cur : Point f ell}
    (tr : Trace root cur) (ord : Fin n≃cur.host.Edge) (x : Fin n→Bool) :
    (assignment cur.host.network (x∘ord.symm) cur.vertex) ∘ tr.back.symm =
      x ∘ tracedSlot tr ord := rfl

variable {S V : Type} [LinearOrder S] [Fintype S] [Fintype V]

noncomputable def actualOriginalPoint {f : ℤ[X]} {ell created m l q : ℕ}
    (T : Plant V m q) (w : Fin (J6Mesh.a m)→S) (v : PlantNode (b:=J6Mesh.K m) (l:=l) T w) :
    Point f ell :=
  ⟨physicalRootHost f ell created m l q T w,v⟩

set_option maxHeartbeats 1200000 in
theorem original_through_trace {f : ℤ[X]} {ell created current m l q M width : ℕ}
    (T : Plant V m q) (w : Fin (J6Mesh.a m)→S) (hf : f.Monic)
    (hp : 0<created) (hq : 0<current) (hF : 0<f.natDegree) (hell : 0<ell)
    {fw : List (Word current)} (he : 0<fw.length)
    (hPoly : Modulus current hq fw=NativeProbeRing.liftPoly current f)
    (v : PlantNode (b:=J6Mesh.K m) (l:=l) T w)
    {cur : Point f ell} (tr : Trace (actualOriginalPoint (created:=created) T w v) cur)
    (ord : Fin M≃cur.host.Edge) (fit : M≤2^width)
    (tape : OriginalGateTape M width)
    (design : tape=gateTape fit (tracedSlot tr ord ∘ (originalPortGate T w v).port)
      (originalPortGate T w v).gate)
    (x : Fin M→Bool) :
    let out := uvGate hq he hell tape (List.ofFn x)
    castBox hPoly (uvRead hq fw ell out.result)=
      (entry cur).read hf current (assignment cur.host.network (x∘ord.symm) cur.vertex) ∧
      (entry cur).created=created ∧
      out.steps≤originalGateFee M width (originalPortGate T w v).degree+uvWidth fw.length ell current+4 := by
  subst tape
  obtain ⟨H,fee⟩ := actual_original_at_descendant_ports T w hf hp hq hF hell he hPoly v (tracedSlot tr ord) fit x
  refine ⟨?_,?_,fee⟩
  · rw [tr.read hf current,traced_slot_input]
    exact H
  · rw [tr.tag]
    cases v <;> rfl

#print axioms requireWord_hit
#print axioms traced_slot_input
#print axioms original_through_trace
end J6R21Ancestor


