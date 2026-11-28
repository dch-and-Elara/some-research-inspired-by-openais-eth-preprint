import J6R53TerminalGateSuffix
import J6R37StructuredRootPorts
import J6R21AncestorOriginReads

/-! Specialization to the source's own printed stable-root prefix.
The root gate suffix is the real physical (page, slot), not the signed
half-address or the unrelated compact input column rank. -/
namespace J6R53TerminalGate
open scoped Polynomial Classical
open Polynomial AOracleMachineTime AOracleMachineTimeTape
open J6R15ModeCost J6R21Ancestor J6R27OriginalGate J6R21Leaf J6OrientedHost
open J6R35RootOrigins J6R37StructuredRoot J6R31RootResidentTables J6R32RootGeneratedRegistryInputs
open J6Mesh J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun
open J6R26DescriptorTree J6R34ChildPath J6R36ChildFramedRoute J6R24MeteredRecursion J6R22Active
open J6R30GeneratedRootLayout J6R24LegalLayout
open J6R33StatefulArithmeticPage
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 33000000
set_option maxRecDepth 4100
set_option Elab.async false

theorem one_side_per_owner {E R C : Type} (N : Network E R C) (u : R⊕C) :
    Function.Injective (fun h : {h : Port E // owner N h=u} => edge h.val) := by
  rintro ⟨a,ha⟩ ⟨b,hb⟩ h
  apply Subtype.ext
  cases a with
  | inl a =>
    cases b with
    | inl b => exact congrArg Sum.inl h
    | inr b => cases ha.trans hb.symm
  | inr a =>
    cases b with
    | inl b => cases ha.trans hb.symm
    | inr b => exact congrArg Sum.inr h

noncomputable section
variable {V : Type} [Fintype V] {m n : ℕ}
variable (P : Plant V m n)

def rootWireSuffix (e : RootWire m) : Word (pageKeyWidth m+a m) :=
  let s := physicalSeatField (rootChart P) (oddAxis m) (residentPageKey m) e
  ⟨s.page.bits++s.slot.bits,by rw [List.length_append,s.page.size,s.slot.size]⟩

theorem physical_root_suffix_injective : Function.Injective (rootWireSuffix P) := by
  intro e q h
  apply Sum.inl.inj
  apply half_addresses_unique P (oddAxis m)
  apply word_bits_inj
  change false::(rootWireSuffix P e).bits=false::(rootWireSuffix P q).bits
  rw [h]

variable {f : ℤ[X]} {ell s C key prec tw bw page base : ℕ}

def rootSuffixAt (x : SourceVertex P) (h : PortAt (stableOriginal (f:=f) (ell:=ell) (base:=base) x)) :
    Word (pageKeyWidth m+a m) := rootWireSuffix P (edge h.val)

theorem actual_gate_body_is_root_suffix (x : SourceVertex P)
    (h : PortAt (stableOriginal (f:=f) (ell:=ell) (base:=base) x)) :
    rootGateBody x h=(rootSuffixAt P x h).bits := rfl

theorem actual_owned_root_suffix_injective (x : SourceVertex P) :
    Function.Injective (rootSuffixAt (f:=f) (ell:=ell) (base:=base) P x) :=
  (physical_root_suffix_injective P).comp (one_side_per_owner _ _)


end
#print axioms one_side_per_owner
#print axioms physical_root_suffix_injective
#print axioms actual_gate_body_is_root_suffix
#print axioms actual_owned_root_suffix_injective
end J6R53TerminalGate
