import J6R55PublicCapacity
import J6R55PublicReady

/-! Bind concrete replay to the first source state of the joined paid
machine, and tie public issuer cost to the same original exterior address.
The retained template table is not assumed to have exactly one row/slot. -/
namespace J6R68RateJoint.RootWords
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R16ModeCost J6R21Ancestor J6R27OriginalGate
open J6Mesh J6OrientedHost J6R24LegalLayout J6R31RootResidentTables J6R26StablePreparedRoot J6R28GeneratedRootFrame
open J6R26DescriptorTree J6R33GeneratedChildSite J6R34RootAtlas J6R32RootGeneratedRegistryInputs
open J6R30ProducedGateRegistry J6R54PublicFamily
open J6R24MeteredRecursion J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R49SourceLayout
open J6R55Public J6R51Online J6R14ZeroMode J6R31RootResidentTables J6R32StatefulArithmetic

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 5100
set_option maxHeartbeats 31000000
set_option Elab.async false
noncomputable section
attribute [local irreducible] J6R12Blueprint.printedParams

variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q ro co de edgew tc tj prec tw bw : ℕ}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable {kp : ℕ}
variable (W : Widths m native tc tj tw edgew) (H : Compiled G ell q ro co de prec kp bw)
variable (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) (g : Fin 64)

theorem literal_exterior_first_key_has_room_and_exact_fee
    (slack : 2*m+1+pathLimit (physicalSize m native) 2<2^tc) :
    let x := (literalSite W H i j g).issue.result
    x.val+1<2^KeyWidth kp tc tj ∧
      (issuedAtFirstDepth W H i j g).result.val=x.val+1 ∧
      (issuedAtFirstDepth W H i j g).steps=13*KeyWidth kp tc tj+4 := by
  let x := (literalSite W H i j g).issue.result
  have cap : x.val-1+pathLimit (physicalSize m native) 2<2^KeyWidth kp tc tj :=
    real_issuance_has_uniform_depth_capacity W H i j g slack
  have xPos : 0<x.val := (Nat.zero_le H.mark.val).trans_lt (emitted_public_root_id_above_mark W H i j g)
  have wide : 0<KeyWidth kp tc tj := by unfold KeyWidth; omega
  have lh := G.bounds.size
  have lam : 16≤Nat.clog 2 (physicalSize m native) :=
    (by decide : 16≤(2*epsDen)^30*2^10).trans lh
  have low : 4≤(Nat.clog 2 (physicalSize m native)).sqrt := Nat.le_sqrt.mpr lam
  have big : 8≤2*(Nat.clog 2 (physicalSize m native)).sqrt := by omega
  have logPos : 1≤Nat.log 8 (2*(Nat.clog 2 (physicalSize m native)).sqrt) := by
    exact (Nat.le_log_iff_pow_le (by decide) (by omega)).mpr (by simpa only [pow_one] using big)
  have depth : 2≤pathLimit (physicalSize m native) 2 := by unfold pathLimit; omega
  have room : x.val+1<2^KeyWidth kp tc tj := by omega
  exact ⟨room,(increment_exact wide x room).1,(increment_exact wide x room).2⟩

#print axioms literal_exterior_first_key_has_room_and_exact_fee
end
end J6R68RateJoint.RootWords
