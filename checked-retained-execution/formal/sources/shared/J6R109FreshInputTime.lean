import J6R54PublicFamilyFresh

/-! Account for both literal passes through the original raw CNF, the
physical roster compiler, and the independent incidence copy. The
actual raw compiler result, not a supplied signed port file, is used. -/
namespace J6R109FreshInputTime
open scoped Classical
open Std.Sat AOracleMachineTime A1R10
open J6R51Ingress J6R54PublicFamily J6R50RootIngress J6R30GeneratedRootLayout
open J6R12CollisionEdges J6R49RootIngress J7R9Compiler J7R9Subdivision J7R10Plant
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxHeartbeats 10000000

theorem the_triangular_pipeline_has_the_actual_three_debits
    {h d j r c : ℕ} (declares : List (List Bool)) (F : BitsCNF)
    (file : SerializedFrame r c d)
    (accepted : (serializeRawCNF (r:=r) (c:=c) (d:=d) h j declares F).result=some file) :
    let G := compilePortRoster (h:=h) (d:=d) (j:=j) declares F
    let A := buildPhysicalFrame (r:=r) (c:=c) G.result
    let raw := serializeRawCNF (r:=r) (c:=c) (d:=d) h j declares F
    raw.steps=G.steps+A.steps+(mapMeter copyEndpoints file.ports).steps+9 ∧
    raw.steps≤G.steps+A.steps+(16+4*r+4*c)*file.ports.length+9 := by
  let G := compilePortRoster (h:=h) (d:=d) (j:=j) declares F
  let A := buildPhysicalFrame (r:=r) (c:=c) G.result
  cases hit : A.result with
  | none =>
    have hA : (buildPhysicalFrame (r:=r) (c:=c) G.result).result=none := hit
    unfold serializeRawCNF at accepted
    dsimp only at accepted
    rw [hA] at accepted
    cases accepted
  | some p =>
    have hA : (buildPhysicalFrame (r:=r) (c:=c) G.result).result=some p := hit
    unfold serializeRawCNF at accepted
    dsimp only at accepted
    rw [hA] at accepted
    dsimp only at accepted
    have same : p.ports=file.ports := congrArg SerializedFrame.ports (Option.some.inj accepted)
    have charges : (serializeRawCNF (r:=r) (c:=c) (d:=d) h j declares F).steps=
        G.steps+A.steps+(mapMeter copyEndpoints file.ports).steps+9 := by
      unfold serializeRawCNF
      dsimp only
      rw [hA]
      simp only [same]
      rfl
    refine ⟨charges,?_⟩
    change (serializeRawCNF (r:=r) (c:=c) (d:=d) h j declares F).steps≤
      G.steps+A.steps+(16+4*r+4*c)*file.ports.length+9
    rw [charges]
    have b := (raw_endpoint_tape_fee file.ports).2
    omega

noncomputable section
variable {V : Type} [DecidableEq V] [Fintype V] (F : CNF V) (order : DeclaredOrder V)
variable {h d j r c e : ℕ}

theorem genuine_literal_preparation_has_the_actual_roster_and_frame_debits
    (g : SerialGuards F order h d j r c e)
    (code : V → List Bool) (inj : Function.Injective code)
    (declared : List (List Bool)) (body : BitsCNF)
    (declaredExact : declared=order.roster.map code) (bodyExact : body=codeCNF code F) :
    let fresh := actualFreshSerialization F order g code inj declared body declaredExact bodyExact
    let G := compilePortRoster (h:=h) (d:=d) (j:=j) declared body
    let A := buildPhysicalFrame (r:=r) (c:=c) G.result
    (materializeLiteral fresh).steps≤G.steps+A.steps+
      (16+4*r+4*c)*nWires (guardedInOrder F order.roster)+12 := by
  let fresh := actualFreshSerialization F order g code inj declared body declaredExact bodyExact
  obtain ⟨file,hit,ports⟩ := fresh.accepted
  have emit := (literal_is_actual_accept fresh file hit).2.2
  have tariff := (the_triangular_pipeline_has_the_actual_three_debits declared body file hit).2
  have size : file.ports.length=nWires (guardedInOrder F order.roster) := by
    rw [ports,List.length_ofFn]
  dsimp only at tariff ⊢
  have fee : fresh.emit.steps=(serializeRawCNF (r:=r) (c:=c) (d:=d) h j declared body).steps := rfl
  rw [emit,fee]
  rw [size] at tariff
  omega

#print axioms the_triangular_pipeline_has_the_actual_three_debits
#print axioms genuine_literal_preparation_has_the_actual_roster_and_frame_debits
end
end J6R109FreshInputTime
