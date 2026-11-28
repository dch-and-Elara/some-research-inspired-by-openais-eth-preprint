import J6R108FinalDriverReady
import J6R75OuterTimeSlotData

/-! Readiness belongs to the ACTUAL bank returned by the literal R57
admission. The R55 bank is compared at its acknowledged value only.
The proof performs no additional publication and transports no fee. -/
namespace J6R108FinalDriver
open scoped Polynomial Classical
open J6R25PreparedSupply
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R21Leaf J6OrientedHost
open J6Mesh J6R34RootAtlas J6R35RootOrigins J6R26DescriptorTree J6R34ChildPath
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R24MeteredRecursion
open J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R48DFS
open J6R9Recursive J6R50SourceProducer J6R51Online J6R52FreshExterior
open J6R57PublicRequest J6R54PublicFamily J6R22Active
open J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R31RootResidentTables J6R28GeneratedRootFrame
open J6R32RootGeneratedRegistryInputs J6R37StructuredRoot J6R41StructuredAllPaths
open J6R55CachedLedger J6R56PrintedExponent J6R49Cost J6R16ModeCost J6R10Reachable
open J6R64Active J6R66Active J6R66.BootPeak J6R57Public
open J6R67UnifiedRate J6R68ActiveInputs J6R68ActiveInputs.Sweep J6R57ScopeFee
open J6R75OuterTime J6R14ZeroMode J6R55Public

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 4900
set_option maxHeartbeats 22000000
set_option maxSynthPendingDepth 12
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ} {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q rr cc dd prec kp bw tc tj tw edgew : ℕ}
variable {W : Widths m native tc tj tw edgew}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (D : Compiled G ell q rr cc dd prec kp bw) (S : InstalledRequestInputs W D)
variable (pad : ℕ)
variable (prior : PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad))
variable {rate : ℕ}
variable (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) (g : Fin 64)
variable {T : Prepared G.bounds (G.selector ell) (exteriorChild G ell i j g) (literalSite W D i j g).hf}
local notation "Row" => (sourceRow (W:=W) D i j g)
local notation "X" => (literalSite W D i j g)


/-- The key format really appends the public address above the shared
mark. A guard on the remaining low-tag bucket therefore certifies the
whole native suffix for every public address, not just one site. -/
theorem path_limit_fits_every_actual_public_address
    (reservedLow : D.mark.val + pathLimit (physicalSize m native) 2 ≤ 2^kp) :
    nativeDepthCapacity W D i j g := by
  let h := (prepareHead W i j).result
  let a := (realAddress h.data g).result
  let high := joinKey a.centre (joinKey a.sample a.group)
  have packed : (literalSite W D i j g).issue.result.val=D.mark.val+2^kp*high.val := by
    change (issueExterior D.mark a).result.val=D.mark.val+2^kp*high.val
    rw [(issued_exterior_exact D.mark a).1,joined_unsigned_value]
  have highFits : high.val+1 ≤ 2^(tc+(tj+6)) := Nat.succ_le_of_lt (val_lt high)
  have wholeFits := Nat.mul_le_mul_left (2^kp) highFits
  rw [Nat.mul_add, Nat.mul_one] at wholeFits
  have pos : 0<(literalSite W D i j g).issue.result.val :=
    (Nat.zero_le D.mark.val).trans_lt (emitted_public_root_id_above_mark W D i j g)
  change (literalSite W D i j g).issue.result.val-1+pathLimit (physicalSize m native) 2
    < 2^(kp+(tc+(tj+6)))
  rw [Nat.pow_add]
  rw [packed] at pos ⊢
  omega

theorem zero_mark_with_the_printed_path_bits_fits
    (zero : D.mark.val=0)
    (allocate : pathLimit (physicalSize m native) 2 ≤ 2^kp) :
    nativeDepthCapacity W D i j g :=
  path_limit_fits_every_actual_public_address D i j g (by simpa only [zero,Nat.zero_add] using allocate)

theorem zero_mark_needs_only_the_printed_depth_counter_width
    (zero : D.mark.val=0)
    (allocate : Nat.clog 2 (pathLimit (physicalSize m native) 2) ≤ kp) :
    nativeDepthCapacity W D i j g :=
  zero_mark_with_the_printed_path_bits_fits D i j g zero
    ((Nat.clog_le_iff_le_pow (by decide : 1<(2:ℕ))).mp allocate)

#print axioms zero_mark_needs_only_the_printed_depth_counter_width
#print axioms path_limit_fits_every_actual_public_address
#print axioms zero_mark_with_the_printed_path_bits_fits
end
end J6R108FinalDriver

