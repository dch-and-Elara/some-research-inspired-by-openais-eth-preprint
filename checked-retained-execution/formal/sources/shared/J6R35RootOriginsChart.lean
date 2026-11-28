import J6R26StablePreparedRootCalls
import J6R21AncestorRun

/-! At a genuine prescribed exterior source, a vertex is either an
actual retained row of the parent or precisely its newly generated
physical Page. This statement uses no ordinary prefix Probe ordinal
and supplies no runtime trace lookup or fee. -/
namespace J6R35RootOrigins
open scoped Polynomial Classical
open Polynomial
open J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable J6R10Repack J6R11Blueprint J6R12Blueprint
open J1PPrinted J6R21Ancestor P11FullPacking J6R9PacketScopes
open J6R26StablePreparedRoot J6R14ZeroMode

variable {f : ℤ[X]} {ell s : ℕ}
variable (sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s))
variable {c : Call (PhysicalHost f ell)}
variable (d : Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c)
variable (t : Center (printedParams (f:=f) (ell:=ell) s) c)
variable (W : Prescribed f (externalProbeDegree s c)) (j : Fin (externalProbeDegree s c+1)) (g : Fin 64)
local notation "SP" => (printedParams (f:=f) (ell:=ell) s)
local notation "B" => (packing sel d)
local notation "α" => (centerIndex d t)
local notation "P" => (registerPrecision SP c t)
local notation "Q" => (externalZeroCall sel d t W j g)

abbrev exteriorRows :=
  Old (atGroup (packing sel d) (centerIndex d t)) g
abbrev exteriorPages :=
  Page ((SP).levelBits c.depth) (packing sel d).copies (Fin 64)

def point (H : PhysicalHost f ell) (v : H.Row⊕H.Col) : Point f ell := ⟨H,v⟩

noncomputable def retainedFromExterior (u : exteriorRows sel d t g) : Move (point c.host u.val) := by
  letI := c.host.finiteEdge
  letI := c.host.finiteRow
  letI := c.host.finiteCol
  exact ⟨Fin 64,exteriorPages sel d,inferInstance,inferInstance,atGroup B α,atPacket B,g,u.property,P,
    compiledPacket B α g P (actualPacket B α (centerNonzero t) rfl P
      (J6R10Integral.box_two_nil P f ell) (prescribedNode W P ell j) 0 g)⟩

theorem retained_prescribed_point (u : exteriorRows sel d t g) :
    (retainedFromExterior sel d t W j g u).next=point (Q).host (.inl u) := rfl

noncomputable def exteriorPagePoint (k : exteriorPages sel d) : Point f ell :=
  point (Q).host (.inr k)

theorem exterior_page_is_real (k : exteriorPages sel d) :
    letI := c.host.finiteEdge
    letI := c.host.finiteRow
    letI := c.host.finiteCol
    exteriorPagePoint sel d t W j g k=generatedPoint B α (centerNonzero t) rfl
      (prescribedNode W P ell j) c.host.file 0 g k := rfl

theorem real_exterior_vertex_origin (v : (Q).host.Row⊕(Q).host.Col) :
    (∃ u : c.host.Row⊕c.host.Col,Nonempty (Trace (point c.host u) (point (Q).host v))) ∨
    (∃ k : exteriorPages sel d,Nonempty (Trace (exteriorPagePoint sel d t W j g k) (point (Q).host v))) := by
  rcases v with u|k
  · left
    exact ⟨u.val,⟨(retained_prescribed_point sel d t W j g u) ▸
      Trace.keep Trace.start (retainedFromExterior sel d t W j g u)⟩⟩
  · exact Or.inr ⟨k,⟨Trace.start⟩⟩

theorem exterior_generated_birth_tag (k : exteriorPages sel d) :
    (entry (exteriorPagePoint sel d t W j g k)).created=(Q).prec := rfl

#print axioms retained_prescribed_point
#print axioms exterior_page_is_real
#print axioms real_exterior_vertex_origin
#print axioms exterior_generated_birth_tag
end J6R35RootOrigins
