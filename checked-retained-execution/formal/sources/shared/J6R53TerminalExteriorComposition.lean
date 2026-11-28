import J6R52TerminalAncestorOrigin
import J6R37StructuredRootChain

/-! Only the actual initial exterior port bodies need an anchor
certificate. All later retained prefixes are produced by the proven
online source state; composition does not request a per-path wire law. -/
namespace J6R53TerminalExterior
open scoped Polynomial
open Polynomial J6R15ModeCost J6R21Ancestor J6R26DescriptorTree J6R34ChildPath
open J6R37StructuredRoot J6R41StructuredAllPaths J6R32StatefulArithmetic
open J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R24MeteredRecursion J6ActiveRun
open J6R50SourceProducer J6R51Online J6R52Terminal J6R36ChildFramedRoute
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 17000000
set_option maxRecDepth 3700
set_option Elab.async false

theorem two_true_prefixes {f : ℤ[X]} {ell : ℕ} {root firstAt here : Point f ell}
    (first : Trace root firstAt) (tail : Trace firstAt here)
    (seed : PortAt root→List Bool) (p : PortAt here) :
    tail.literal (first.literal seed) p=(J6R35RootOrigins.concatenate first tail).literal seed p := by
  have v := continuation_starts_at_same_port first tail seed p
  rw [carry_body_exact] at v
  rw [tail.literal_exact (first.literal seed) p]
  exact v

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page rate : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
variable (M : OnlineMachine T key prec tw bw page rate)
variable {tags : r.host.Row⊕r.host.Col→Origin key prec page}
variable {ports : Port r.host.Edge→Payload key prec page}

theorem actual_birth_prefix_extends_the_exterior_seed
    {c : Call (PhysicalHost f ell)} (p : Path sel r c) (w : (Plan sel).Slot c)
    (u : c.host.Row⊕c.host.Col)
    (A : ExteriorOrigin M tags ports p w u)
    {root : Point f ell} (seed : PortAt root→List Bool)
    (first : Trace root (point r.host A.vertex))
    (boot : ∀ x : PortAt (point r.host A.vertex),(ports x.val).2=first.literal seed x) :
    ∀ x : PortAt (point c.host u),
      ((sourceState M p w).birth.native.physical.record x.val).body=
        (J6R35RootOrigins.concatenate first A.trace).literal seed x := by
  intro x
  refine (A.body x).trans ?_
  have seedEq : (fun q : PortAt (point r.host A.vertex)=>(ports q.val).2)=first.literal seed :=
    funext boot
  rw [seedEq]
  exact two_true_prefixes first A.trace seed x

end
#print axioms two_true_prefixes
#print axioms actual_birth_prefix_extends_the_exterior_seed
end J6R53TerminalExterior
