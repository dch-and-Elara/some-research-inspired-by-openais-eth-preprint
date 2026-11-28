import J6R54PublicFamilyIdentity
import J6R51OnlineDepth

/-! The installed bank and the initial counter are the physical ones
from the emitted R54 exterior site. A single shared bound on the
older directory is sufficient; no per-group Ready or Live proof is
an input to the new binder. The native increment schedule is checked
separately against the actual boot and descendant occurrences. -/
namespace J6R55Public
open scoped Classical Polynomial
open Polynomial AOracleMachineTime AOracleMachineTimeTape
open J6Mesh J6OrientedHost J6R24LegalLayout J6R24MeteredRecursion
open J6R26StablePreparedRoot J6R28GeneratedRootFrame J6R14ZeroMode
open J6R34RootAtlas J6R32RootGeneratedRegistryInputs
open J6R15ModeCost J6R25PreparedSupply J6R30ProducedGateRegistry
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R31RootResidentTables
open J6R54PublicFamily J6R51 J6R16ModeCost
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 16000000
set_option maxRecDepth 3500
set_option Elab.async false

theorem append_unsigned_value (xs ys : List Bool) :
    bitsValue (xs++ys)=bitsValue xs+2^xs.length*bitsValue ys := by
  induction xs with
  | nil => simp [bitsValue]
  | cons x xs ih =>
    simp only [List.cons_append,bitsValue,List.length_cons,pow_succ,ih]
    ring

theorem joined_unsigned_value {a b : ℕ} (x : Word a) (y : Word b) :
    (joinKey x y).val=x.val+2^a*y.val := by
  change bitsValue (x.bits++y.bits)=_
  rw [append_unsigned_value,x.size]
  rfl

noncomputable section
variable {V : Type} [Fintype V] {f : ℤ[X]} {m n base native : ℕ} {T : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) T (constantRootWord m)}
variable {ell q rr cc dd prec kp bw tc tj tw edgew : ℕ}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (W : Widths m native tc tj tw edgew) (C : Compiled G ell q rr cc dd prec kp bw)
variable (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) (g : Fin 64)

abbrev literalSite : StableExterior G ell q rr cc dd edgew tc tj (KeyWidth kp tc tj) prec tw bw :=
  (siteFromHead W g C (prepareHead W i j).result).result

theorem emitted_public_root_id_above_mark :
    C.mark.val<(literalSite W C i j g).issue.result.val := by
  let H := (prepareHead W i j).result
  let A := (realAddress H.data g).result
  have et : A.centre.val=index m i :=
    (congrArg Word.val (real_address_exact H.data g).1).trans H.centreOK
  have pos : 0<A.centre.val := by rw [et]; unfold index; omega
  change C.mark.val<(issueExterior C.mark A).result.val
  rw [(issued_exterior_exact C.mark A).1,joined_unsigned_value,joined_unsigned_value]
  have H : 0<A.centre.val+2^tc*(joinKey A.sample A.group).val := by omega
  have p : 0<(2:ℕ)^kp := by positivity
  have u := Nat.mul_pos p H
  omega

theorem real_exterior_depth_one
    (X : StableExterior G ell q rr cc dd edgew tc tj (KeyWidth kp tc tj) prec tw bw) :
    (exteriorChild G ell X.centre X.sample X.group).depth=1 := rfl

abbrev reservedBank (pad : ℕ) :=
  PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad)

variable (pad : ℕ) (B : reservedBank (f:=f) (ell:=ell) (kp:=kp) (tc:=tc) (tj:=tj)
  (prec:=prec) (tw:=tw) (bw:=bw) (m:=m) pad)

def actualInstalledBank : reservedBank (f:=f) (ell:=ell) (kp:=kp) (tc:=tc) (tj:=tj)
    (prec:=prec) (tw:=tw) (bw:=bw) (m:=m) pad :=
  (((literalSite W C i j g).seed pad).install B).result.1

theorem real_public_install_and_reserve
    (sync : B.synced) (old : ∀ row∈B.headers,row.id.val≤C.mark.val) :
    let X := literalSite W C i j g
    let J := X.seed pad
    let bank := actualInstalledBank W C i j g pad B
    (J.install B).result.2=true ∧ IsLive J bank ∧ Reserved bank X.issue.result := by
  let X := literalSite W C i j g
  let J := X.seed pad
  let earlier := word (q:=KeyWidth kp tc tj) (X.issue.result.val-1)
  have id : J.identifier=X.issue.result := (stable_exterior_header X).1
  have hi : C.mark.val<X.issue.result.val := emitted_public_root_id_above_mark W C i j g
  have he : earlier.val=X.issue.result.val-1 :=
    word_val ((Nat.sub_le _ 1).trans_lt (val_lt X.issue.result))
  have Hb : Reserved B earlier := by
    refine ⟨sync,?_⟩
    intro row hrow
    have ho := old row hrow
    rw [he]
    omega
  have after : J.identifier.val=earlier.val+1 := by rw [id,he]; omega
  have exactMount := next_actual_job_preserves_reserved B earlier J Hb after
  have eq := (next_job_exact B J [] (next_actual_job_fresh B earlier J Hb after)).1
  change (J.install B).result.2=true ∧ IsLive J (J.install B).result.1 ∧
    Reserved (J.install B).result.1 X.issue.result
  refine ⟨exactMount.1,?_,?_⟩
  · rw [eq]
    exact new_is_live J B
  · rw [←id]
    exact exactMount.2

#print axioms append_unsigned_value
#print axioms joined_unsigned_value
#print axioms emitted_public_root_id_above_mark
#print axioms real_exterior_depth_one
#print axioms real_public_install_and_reserve
end
end J6R55Public

