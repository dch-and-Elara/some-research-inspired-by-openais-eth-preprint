import J6R54PublicFamilyCommon
import J6R51IngressSerialConsumers
import J6R52FreshShapePaidSetup

/-! The shared chart is the actual surviving raw serialization branch,
not an existentially chosen unrelated source file. The same constructor
runs the accepted field search and emits its native register frame. -/
namespace J6R54PublicFamily
open scoped Classical Polynomial
open Polynomial Std.Sat AOracleMachineTime
open J6Mesh J6OrientedHost J7R9Compiler J7R9Subdivision J7R10Plant
open J6R24LegalLayout J6R24MeteredRecursion J6R26StablePreparedRoot
open J6R28GeneratedRootFrame J6R30GeneratedRootLayout J6R51Ingress
open J6R49RootIngress J6R50RootIngress J6R52FreshShape J6R52FreshExterior J6R15ModeCost
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 15000000
set_option maxRecDepth 3300
set_option Elab.async false

section Accepted
variable {V : Type*} {m n rr cc dd : ℕ} {T : Plant V m n}

structure AcceptedSerialization (T : Plant V m n) (rr cc dd : ℕ) where
  codec : LiteralCodec T rr cc dd
  emit : Meter (Option (SerializedFrame rr cc dd))
  accepted : ∃ f : SerializedFrame rr cc dd,
    emit.result=some f ∧ f.ports=List.ofFn (plantHalfPort T codec)

variable (A : AcceptedSerialization T rr cc dd)

theorem accepted_file_exact (f : SerializedFrame rr cc dd) (hit : A.emit.result=some f) :
    f.ports=List.ofFn (plantHalfPort T A.codec) := by
  obtain ⟨x,hx,raw⟩ := A.accepted
  exact (congrArg SerializedFrame.ports (Option.some.inj (hit.symm.trans hx))).trans raw

def materializeLiteral : Meter (LiteralPortFile T rr cc dd) :=
  match h : A.emit.result with
  | some file => ⟨⟨A.codec,file.ports,accepted_file_exact A file h⟩,A.emit.steps+3⟩
  | none => False.elim (by
      obtain ⟨x,hx,_⟩ := A.accepted
      rw [h] at hx
      cases hx)

theorem literal_is_actual_accept (f : SerializedFrame rr cc dd) (hit : A.emit.result=some f) :
    (materializeLiteral A).result.raw=f.ports ∧
      (materializeLiteral A).result.codec=A.codec ∧
      (materializeLiteral A).steps=A.emit.steps+3 := by
  unfold materializeLiteral
  split
  next y h =>
    have eq := Option.some.inj (h.symm.trans hit)
    exact ⟨congrArg SerializedFrame.ports eq,rfl,rfl⟩
  next h =>
    rw [h] at hit
    cases hit
end Accepted

noncomputable section
variable {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]
variable (F : CNF V) (order : DeclaredOrder V)
variable {h d j r c e : ℕ}

def actualFreshSerialization (g : SerialGuards F order h d j r c e)
    (code : V→List Bool) (inj : Function.Injective code)
    (declared : List (List Bool)) (body : BitsCNF)
    (declaredExact : declared=order.roster.map code) (bodyExact : body=codeCNF code F) :
    AcceptedSerialization (freshPlant (guardedInOrder F order.roster) (guardRoster order)) r c d where
  codec := freshCodec (guardedInOrder F order.roster) (guardRoster order) r c d g.rowFit g.columnFit g.portFit
  emit := serializeRawCNF (r:=r) (c:=c) (d:=d) h j declared body
  accepted := by
    obtain ⟨file,E,_,H,_⟩ := serialized_actual_fresh_input F order code inj h d j r c 0 e
      g.hpos g.dpos g.jpos g.rpos g.cpos g.clausesFit g.rawLegFit g.localsFit
      g.edgesFit g.rowFit g.columnFit g.portFit
    rw [declaredExact,bodyExact]
    exact ⟨file,E,H⟩

structure FreshWords (m base q prec kp bw : ℕ) where
  baseWord : Word q
  baseTag : baseWord.val=base
  copyFit : K m<2^q
  preFit : J6SourcePrecision.printed m base<2^q
  birthFit : J6SourcePrecision.printed m base<2^prec
  code : ℕ
  codeBound : rootCodeWidth m base≤code
  codeFit : code<2^bw
  codePositive : 0<bw
  mark : Word kp

def freshSharedInputs (base ell q prec kp bw : ℕ)
    (three : ∀ row∈F,row.length≤3)
    (large : printedGuard (nWires (guardedInOrder F order.roster)) (Paper6SourceSize.sourceNativeSize F order))
    (positive : 0<ell) (W : FreshWords (nWires (guardedInOrder F order.roster)) base q prec kp bw)
    (g : SerialGuards F order h d j r c e)
    (code : V→List Bool) (inj : Function.Injective code)
    (declared : List (List Bool)) (body : BitsCNF)
    (declaredExact : declared=order.roster.map code) (bodyExact : body=codeCNF code F) :
    SharedInputs (freshSearchedRootShape F order base three large) ell q r c d prec kp bw where
  positive := positive
  hf := (generated_fresh_field_is_permitted F order).1
  literal := materializeLiteral (actualFreshSerialization F order g code inj declared body declaredExact bodyExact)
  field := paidFreshFieldFrame F order base
  baseWord := W.baseWord
  baseTag := W.baseTag
  copyFit := W.copyFit
  preFit := W.preFit
  birthFit := W.birthFit
  code := W.code
  codeBound := W.codeBound
  codeFit := W.codeFit
  codeWordWidthPositive := W.codePositive
  mark := W.mark

#print axioms accepted_file_exact
#print axioms literal_is_actual_accept
#print axioms actualFreshSerialization
#print axioms freshSharedInputs
end
end J6R54PublicFamily

