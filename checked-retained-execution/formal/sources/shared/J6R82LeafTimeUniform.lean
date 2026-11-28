import J6R82LeafTimeCreators
import J6R82LeafTimeEnvelope
import J6R82LeafTimeSyntax
import J6R65LeafRatePrepGeometry

/-! The common scalar is charged to every already-compiled row of the
same actual stopped leaf. It is a size bound, not a new entry routine. -/
namespace J6R82LeafTime
open scoped Polynomial Classical
open Polynomial AOracleMachineTime A1R10 A1R12 J6R15ModeCost J6R21Ancestor J6R21Leaf
open J6R18ChildWrite J6R20Ancestor J6R22Active J6R24MeteredRecursion J6R30ProducedGateRegistry
open J6R33StatefulArithmeticPage J6R32StatefulArithmetic J6R34RootAtlas
open J6R12Blueprint J6R11Blueprint J6ActiveRun J6ActiveSchedule J1PPrinted
open J6R48Leaf J6R50Leaf J6R62Leaf J6R65LeafRate J6R66LeafTariff J6R58LeafScale
open J6R26DescriptorTree J6R34ChildPath J6R49SourceLayout J6R32ChildResidentTransfer
open P11FullPacking J6R10Repack J6R51Online J6R50SourceProducer J6R48DFS
open J6Mesh J6OrientedHost J6R27OriginalGate J6R24LegalLayout J6R26StablePreparedRoot
open J6R35RootOrigins J6R31RootResidentTables J6R28GeneratedRootFrame J6R32RootGeneratedRegistryInputs
open J6R15ModeCost J6R52Terminal J6R53TerminalGate J6R54TerminalBoot J6R57Public
open J6R53OldOwner J6R36ChildFramedRoute J6R10Reachable J6R16ModeCost
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 41000000
set_option maxRecDepth 5500
set_option Elab.async false

def commonSize (s C body arity significant directory : ℕ) : ℕ :=
  1+4*Nat.clog 2 s+regulator s C+3*(C*s)+3*(C*s)*regulator s C+2*s+
    body+arity+significant+directory

theorem commonSize_pos (s C body arity significant directory : ℕ) :
    0<commonSize s C body arity significant directory := by unfold commonSize; omega

variable {f : ℤ[X]} {ell key prec tw bw page : ℕ}

def ActualEncodingFits (B : PageBank f ell key prec tw bw page) (significant : ℕ) : Prop :=
  ∀ addr R,(locate addr B.records).result=some R →
    R.payload.shape.w≤significant ∧ R.context.codeWidth.val≤significant

theorem generated_command_bounded_at_its_real_page
    (B : PageBank f ell key prec tw bw page) (addr : J6R15ModeCost.Word key) (pg : J6R15ModeCost.Word page)
    (s C e width n depth : ℕ) (wires : List WireRead)
    (src : CurrentPacketReceipt B addr pg s C e width n depth wires)
    (hf : f.Monic) (fieldDegree : f.natDegree=4*Nat.clog 2 s) (sz : 1<s)
    (body arity significant directory : ℕ)
    (enc : ActualEncodingFits B significant) (count : B.records.length≤directory)
    (receiver : width≤regulator s C) (edges : n≤C*s)
    (dep : depth≤body) (number : wires.length≤n)
    (raw : ∀ a,rawWireFee (depth+a+2) wires≤n*(3*body+4*n+(body+a+2)+12)) :
    let K := commonSize s C body arity significant directory
    readCmdFee B e width n (.packet addr pg depth wires)≤2^(6*leafH s)*
      rowPrefix ell key prec tw bw page (Nat.clog 2 s) K
        (commonSize_pos s C body arity significant directory) := by
  let K := commonSize s C body arity significant directory
  let lam := Nat.clog 2 s
  let R := src.record
  let S := R.payload.shape
  let fields := src.data
  let positive := commonSize_pos s C body arity significant directory
  have h : K=1+4*lam+regulator s C+3*(C*s)+3*(C*s)*regulator s C+2*s+
      body+arity+significant+directory := rfl
  let F : J6R24MeteredRecursion.Frame f S.p := ⟨S.pPos,S.old,S.degreePos,S.algebra⟩
  have degree : S.old.length=4*lam := (F.natDegree hf).trans fieldDegree
  have good := enc addr R src.outer
  obtain ⟨dep0,axis⟩ := src.geometry.axis
  have a : S.a≤lam := axis.trans_le (printed_axis_fits_logarithmic_uniform_prefactor s dep0)
  have cells : 2^S.a≤K := (Nat.pow_le_pow_right (by decide) a).trans
    ((printed_clog_power_le_twice_size s sz).trans (by omega))
  have nn : n≤K := by have := edges; omega
  have rb := src.geometry.pMax
  have mb := src.geometry.modes
  have pb := src.geometry.pages
  have limited : PacketLimits B R fields width depth wires lam K :=
    ⟨count.trans (by omega),pb.trans (by omega),a,degree.le.trans (by omega),
      rb.trans (by omega),good.1.trans (by omega),good.2.trans (by omega),
      src.geometry.rows.trans cells,src.geometry.cols.trans cells,mb.trans (by omega),
      receiver.trans (by omega),dep.trans (by omega),number.trans nn,
      one_uniform_wire_tariff wires nn (show body≤K by omega) a (raw S.a)⟩
  have u := actual_packet_prefactor_has_one_uniform_scalar B R fields width depth wires lam K positive limited
  have tariff := src.rate
  exact tariff.trans (Nat.mul_le_mul_left _
    (u.trans (Nat.le_add_left _ _)))

#print axioms commonSize_pos
#print axioms generated_command_bounded_at_its_real_page
end J6R82LeafTime
