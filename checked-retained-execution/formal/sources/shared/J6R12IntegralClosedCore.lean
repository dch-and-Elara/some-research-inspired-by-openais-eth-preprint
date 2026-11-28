import J6R12IntegralMenu
import J6R11IntegralFrozenRun
import J6R11IntegralStep
import J6R12BlueprintFactory
import J6R12BlueprintGrouped

/-! Combined native parent/child replay preserving the actual edge types. -/

/-! The actual child's host contains the very entry file in the physical
source theorem. Identify its exact odd-local contraction before
reducing it; no oracle-produced child value is assumed. -/
namespace J6R12Integral
open scoped Classical BigOperators Polynomial
open Polynomial J6R11Blueprint J6R11Integral J6R10Integral
open J6R9Recursive J6R10Repack P11FullPacking J6R9PacketScopes

variable {f : ℤ[X]} {ell : ℕ}
variable {E A B K G : Type} [Fintype E] [Fintype A] [Fintype B] [Fintype K] [DecidableEq G]

set_option maxHeartbeats 2200000 in
theorem physicalChildHost_contract (N : Network E A B) (group : A ⊕ B → G)
    (packet : E → K) (g : G) (oldFile : EntryFile f ell N) (p : ℕ)
    (packetValue : ∀ k : K, (PacketPorts N group packet g k → Bool) → Residue f ell p)
    (hf : f.Monic) :
    (physicalChildHost N group packet g oldFile p packetValue).contract hf =
      trueContraction (child N group packet g)
        (compileChild N group packet g oldFile p packetValue) hf := by
  unfold physicalChildHost physicalHost PhysicalHost.contract trueContraction
  refine Finset.sum_congr (Finset.ext (fun _ => by simp only [Finset.mem_univ])) (fun x _ => ?_)
  exact Finset.prod_congr (Finset.ext (fun _ => by simp only [Finset.mem_univ])) (fun _ _ => rfl)

section Physical
variable {H : Type} [LinearOrder H] [Fintype H]
variable {a : ℕ} {N : Network E A B}

theorem actualPacketHost_truth (P : PhysicalPacking N a H) (i : Fin a) {t : ℤ}
    (ht : t ≠ 0) (hv : padicValInt 2 t = i.val) (p : ℕ)
    (z : Box f ell p) (file : EntryFile f ell N) (hf : f.Monic)
    (β : Mode i p P.mask →₀ ℕ) (g : H) :
    (actualPacketHost P i ht hv p (box_two_nil p f ell) z file β g).contract hf =
      actualChildTruth P i ht hv p z file hf β g :=
  physicalChildHost_contract N (atGroup P i) (atPacket P) g file p _ hf
end Physical

#print axioms physicalChildHost_contract
#print axioms actualPacketHost_truth
end J6R12Integral


namespace J6R12Integral
open scoped Classical Polynomial
open Polynomial J6R12Blueprint J6R11Blueprint
open J6ActiveRun J6R9Recursive J6R10Reachable J6R9PacketScopes J6R9PacketChild P11FullPacking

variable {f : ℤ[X]} {ell : ℕ}
variable {S : Params (f:=f) (ell:=ell)} {Δ : ℕ}
variable (sel : Selector S Δ)
variable {c : Call (H (f:=f) (ell:=ell))}

abbrev LiteralMenu (d : Ready S Δ c) (t : Center S c) :=
  ↥(J6RecursiveMenu.menu (registerPrecision S c t) (siteWeight sel d t))

noncomputable def siteMenuEquiv (d : Ready S Δ c) (t : Center S c) :
    NativeMenu (shape S Δ sel) c t ≃ LiteralMenu sel d t := by
  letI : Fintype (modeAt S Δ sel c t) := (shape S Δ sel).finiteMode c t
  letI : DecidableEq (modeAt S Δ sel c t) := (shape S Δ sel).decideMode c t
  let e := Equiv.cast (modeAt_eq S Δ sel d t)
  have hw (m : modeAt S Δ sel c t) :
      siteWeight sel d t (e m) = weightAt S Δ sel c t m := by
    have h := weightAt_mode S Δ sel d t (e m)
    change weightAt S Δ sel c t (e.symm (e m)) = _ at h
    rw [Equiv.symm_apply_apply] at h
    exact h.symm
  exact menuReindex (registerPrecision S c t) (J6R12Blueprint.register_positive d t) e
    (weightAt S Δ sel c t) (siteWeight sel d t) (weightAt_pos S Δ sel c t) hw

theorem siteMenuEquiv_tuple (d : Ready S Δ c) (t : Center S c) (z : Probe S c)
    (β : NativeMenu (shape S Δ sel) c t) (g : Fin 64) :
    (siteMenuEquiv sel d t β).val = siteTuple sel d ⟨t,z,β,g⟩ := rfl

#print axioms siteMenuEquiv
#print axioms siteMenuEquiv_tuple
end J6R12Integral


/-! At a genuine call/centre/probe, the computed slot host and the
site child appearing in the exact finite contraction are identical as
immutable entry-file inputs. -/
namespace J6R12Integral
open scoped Classical BigOperators Polynomial
open Polynomial J6R12Blueprint J6R11Blueprint J6R11Integral
open J6ActiveRun J6R9Recursive J6R10Reachable J6R10Repack
  J6R9PacketScopes J6R9PacketChild P11FullPacking

variable {f : ℤ[X]} {ell : ℕ}
variable {S : Params (f:=f) (ell:=ell)} {Δ : ℕ}
variable (sel : Selector S Δ)
variable {c : Call (H (f:=f) (ell:=ell))}

theorem packetOfSite_truth (d : Ready S Δ c) (t : Center S c) (z : Probe S c)
    (β : SiteMode sel d t →₀ ℕ) (g : Fin 64) (hf : f.Monic) :
    (packetOfSite sel d t z β g).contract hf =
      (letI := c.host.finiteEdge
       letI := c.host.finiteRow
       letI := c.host.finiteCol
       actualChildTruth (packing sel d) (centerIndex d t) (centerNonzero t) rfl
         (registerPrecision S c t) (sampleNode S f ell c d.fit t z) c.host.file hf β g) := by
  letI := c.host.finiteEdge
  letI := c.host.finiteRow
  letI := c.host.finiteCol
  exact actualPacketHost_truth (packing sel d) (centerIndex d t) (centerNonzero t) rfl
    (registerPrecision S c t) (sampleNode S f ell c d.fit t z) c.host.file hf β g

set_option maxHeartbeats 2500000 in
theorem native_parent_probe (d : Ready S Δ c) (t : Center S c) (z : Probe S c) (hf : f.Monic) :
    let p := registerPrecision S c t
    (letI := c.host.finiteEdge
     letI := c.host.finiteRow
     letI := c.host.finiteCol
     ((parentJet (packing sel d) c.host.file hf t.val).map (reduce p f ell)).eval
       (sampleNode S f ell c d.fit t z)) =
      ∑ β : LiteralMenu sel d t, ∏ g : Fin 64,
        reduce p f ell ((packetOfSite sel d t z β.val g).contract hf) := by
  letI := c.host.finiteEdge
  letI := c.host.finiteRow
  letI := c.host.finiteCol
  let p := registerPrecision S c t
  have ht := active_grid _ _ _ t.property
  dsimp only
  rw [native_finite_step (packing sel d) (centerIndex d t) ht.1 ht.2 rfl p
    (J6R12Blueprint.register_positive d t) (sampleNode S f ell c d.fit t z) c.host.file hf]
  let menu := J6RecursiveMenu.menu p (siteWeight sel d t)
  let fromChild (β : SiteMode sel d t →₀ ℕ) : Box f ell p :=
    ∏ g : Fin 64, reduce p f ell ((packetOfSite sel d t z β g).contract hf)
  change _ = ∑ β : (↥menu), fromChild β.val
  rw [Finset.sum_coe_sort menu fromChild]
  refine Finset.sum_congr rfl (fun β _ => ?_)
  refine Finset.prod_congr rfl (fun g _ => ?_)
  rw [packetOfSite_truth sel d t z β g hf]

#print axioms packetOfSite_truth
#print axioms native_parent_probe
end J6R12Integral


/-! The reply in the padded recursive envelope is the actual child
file's exact contraction. Address reindexing changes neither the
physical child nor the Finsupp tuple it is constructed from. -/
namespace J6R12Integral
open scoped Classical BigOperators Polynomial
open Polynomial J6ActiveRun J6R9Recursive J6R10Reachable J6R10Repack
open J6R12Blueprint J6R11Blueprint

variable {f : ℤ[X]} {ell : ℕ}
variable (S : Params (f:=f) (ell:=ell)) (Δ : ℕ) (sel : Selector S Δ)
variable (r : Call (H (f:=f) (ell:=ell)))
local notation "Nₛ" => shape S Δ sel
local notation "Cₛ" => children S Δ sel

variable [envDec : DecidableEq (Envelope Nₛ Cₛ r)]

def factoryPositive : PositiveData Nₛ Cₛ r :=
  fun c _ _ t m => weightAt_pos S Δ sel c t m

noncomputable def sourceBlueprint (hf : f.Monic) :
    Blueprint (paddedShape Nₛ Cₛ r) f ell :=
  paddedBlueprint Nₛ Cₛ r (factoryPositive S Δ sel r) f ell (physicalEntries hf)

variable {c : Call (H (f:=f) (ell:=ell))}

omit envDec in
set_option maxHeartbeats 3000000 in
theorem nativeChild_truth (hf : f.Monic) (d : Ready S Δ c) (t : Center S c) (z : Probe S c)
    (β : NativeMenu Nₛ c t) (g : Fin 64) :
    let w : NativeAddress Nₛ c := ⟨t,z,β,g⟩
    (sourceBlueprint S Δ sel r hf).truth ((nativePlan Nₛ Cₛ).child c ⟨w,d.active⟩) =
      (packetOfSite sel d t z (siteTuple sel d w) g).contract hf := by
  let w : NativeAddress Nₛ c := ⟨t,z,β,g⟩
  let c' := (nativePlan Nₛ Cₛ).child c ⟨w,d.active⟩
  let dest := packetOfSite sel d t z (siteTuple sel d w) g
  change (sourceBlueprint S Δ sel r hf).truth c' = dest.contract hf
  have hchild : c' = ⟨dest,c.depth+1,dest.edgeCount,registerPrecision S c t⟩ :=
    child_exact sel d w
  have hsized : c'.host.edgeCount = c'.edges := by rw [hchild]
  rw [physicalBlueprint_truth hf (sourceBlueprint S Δ sel r hf) rfl c' hsized]
  exact congrArg (fun H : PhysicalHost f ell => H.contract hf) (congrArg Call.host hchild)

omit envDec in
set_option maxHeartbeats 3500000 in
theorem nativeGrouped_literal (hf : f.Monic) (d : Ready S Δ c) (t : Center S c) (z : Probe S c) :
    nativeGrouped Nₛ Cₛ r (factoryPositive S Δ sel r) f ell (physicalEntries hf) c d.active t z =
      ∑ β : LiteralMenu sel d t, ∏ g : Fin 64,
        reduce (registerPrecision S c t) f ell ((packetOfSite sel d t z β.val g).contract hf) := by
  letI := nativeMenuFinite Nₛ c t
  let p := registerPrecision S c t
  let lhs (β : NativeMenu Nₛ c t) : Box f ell p :=
    ∏ g : Fin 64, reduce p f ell
      ((sourceBlueprint S Δ sel r hf).truth ((nativePlan Nₛ Cₛ).child c ⟨⟨t,z,β,g⟩,d.active⟩))
  let rhs (β : LiteralMenu sel d t) : Box f ell p :=
    ∏ g : Fin 64, reduce p f ell ((packetOfSite sel d t z β.val g).contract hf)
  change (∑ β, lhs β) = ∑ β, rhs β
  refine Fintype.sum_equiv (siteMenuEquiv sel d t) lhs rhs (fun β => ?_)
  unfold lhs rhs
  refine Finset.prod_congr rfl (fun g _ => ?_)
  apply congrArg (reduce p f ell)
  exact (nativeChild_truth S Δ sel r hf d t z β g).trans
    (congrArg (fun e => (packetOfSite sel d t z e g).contract hf)
      (siteMenuEquiv_tuple sel d t z β g).symm)

#print axioms nativeChild_truth
#print axioms nativeGrouped_literal
end J6R12Integral


/-! Direct native recursion: keep the parent's actual Edge type in the
deformation and the child's actual Edge type in its file. The audited
edge-order transport occurs in physicalBlueprint_truth, not in a
change of graph or a matrix-rank surrogate. -/
namespace J6R12Integral
open scoped Classical BigOperators Polynomial
open Polynomial J6ActiveRun J6R9Recursive J6R10Reachable J6R10Repack
open J6R12Blueprint J6R11Blueprint J6R11Integral P1DyadicGrid

variable {f : ℤ[X]} {ell : ℕ}
variable (S : Params (f:=f) (ell:=ell)) (Δ : ℕ) (sel : Selector S Δ)
variable (r : Call (H (f:=f) (ell:=ell)))
local notation "Nₛ" => shape S Δ sel
local notation "Cₛ" => children S Δ sel
local notation "Bₛ" => sourceBlueprint S Δ sel r

structure NativeGuards where
  ready : ∀ c, IsNative Nₛ Cₛ r c → S.cutoff < c.edges → Ready S Δ c
  taper : ∀ c, IsNative Nₛ Cₛ r c → S.cutoff < c.edges →
    0 < S.levelWidth c.depth ∧ S.levelWidth c.depth ≤ c.edges

variable {S Δ}
variable {c : Call (H (f:=f) (ell:=ell))}

noncomputable def actualF (d : Ready S Δ c) (hf : f.Monic) : (RatRing f ell)[X] := by
  letI := c.host.finiteEdge
  letI := c.host.finiteRow
  letI := c.host.finiteCol
  exact parentF (packing sel d) c.host.file hf

noncomputable def actualJet (d : Ready S Δ c) (hf : f.Monic) (t : ℤ) : (IntRing f ell)[X] := by
  letI := c.host.finiteEdge
  letI := c.host.finiteRow
  letI := c.host.finiteCol
  exact parentJet (packing sel d) c.host.file hf t

theorem actualF_degree (d : Ready S Δ c) (hf : f.Monic) :
    (actualF sel d hf).natDegree ≤ J9PrintedSchedule.degreeBound c.edges (2^S.levelBits c.depth) := by
  letI := c.host.finiteEdge
  letI := c.host.finiteRow
  letI := c.host.finiteCol
  rw [← d.edgeCount]
  exact parentF_degree (packing sel d) c.host.file hf

theorem actualJet_local (d : Ready S Δ c) (hf : f.Monic) (t : Center S c) :
    (actualJet sel d hf t.val).map (embed f ell) =
      J6ActiveUniqueness.atNode (J6ActivePrintedHermite.dyadicUnit (S.levelBits c.depth))
        (t.val:RatRing f ell) (actualF sel d hf) := by
  letI := c.host.finiteEdge
  letI := c.host.finiteRow
  letI := c.host.finiteCol
  exact parentF_local (packing sel d) c.host.file hf (active_grid _ _ _ t.property).1

theorem actualF_origin (d : Ready S Δ c) (hf : f.Monic) :
    (actualF sel d hf).eval 0 = embed f ell (c.host.contract hf) := by
  letI := c.host.finiteEdge
  letI := c.host.finiteRow
  letI := c.host.finiteCol
  exact parentF_origin (packing sel d) c.host.file hf

variable (S Δ)
variable [envDec : DecidableEq (Envelope Nₛ Cₛ r)]

set_option maxHeartbeats 6000000 in
noncomputable def actualSourceSpec (G : NativeGuards S Δ sel r) (hf : f.Monic) :
    (Bₛ hf).SourceSpec := by
  classical
  exact {
    Valid := IsNative Nₛ Cₛ r
    child_valid := paddedBlueprint_closed Nₛ Cₛ r (factoryPositive S Δ sel r) f ell (physicalEntries hf)
    deformation := fun c =>
      if h : IsNative Nₛ Cₛ r c ∧ S.cutoff < c.edges then actualF sel (G.ready c h.1 h.2) hf else 0
    jets := fun c t =>
      if h : IsNative Nₛ Cₛ r c ∧ S.cutoff < c.edges then actualJet sel (G.ready c h.1 h.2) hf t else 0
    fit := fun c hc ha => (G.ready c hc ha).fit
    taper := G.taper
    degree := fun c hc ha => by
      rw [dif_pos ⟨hc,ha⟩]
      exact actualF_degree sel (G.ready c hc ha) hf
    integral := fun c hc ha t => by
      rw [dif_pos ⟨hc,ha⟩,dif_pos ⟨hc,ha⟩]
      exact actualJet_local sel (G.ready c hc ha) hf t
    origin := fun c hc ha => by
      rw [dif_pos ⟨hc,ha⟩,physicalBlueprint_truth hf (Bₛ hf) rfl c (G.ready c hc ha).edgeCount]
      exact actualF_origin sel (G.ready c hc ha) hf
    grouped := fun c hc ha t z => by
      let d := G.ready c hc ha
      rw [dif_pos ⟨hc,ha⟩]
      change paddedGroupedAt Nₛ Cₛ r (factoryPositive S Δ sel r) f ell (physicalEntries hf) c t z =
        ((actualJet sel d hf t.val).map (reduce (registerPrecision S c t) f ell)).eval
          (sampleNode S f ell c d.fit t z)
      rw [paddedBlueprint_grouped Nₛ Cₛ r (factoryPositive S Δ sel r) f ell
          (physicalEntries hf) c hc ha t z,nativeGrouped_literal S Δ sel r hf d t z]
      exact (native_parent_probe sel d t z hf).symm }

omit envDec in
theorem native_run_reachable (G : NativeGuards S Δ sel r) (hf : f.Monic)
    (hF : 0 < f.natDegree) [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (c : Call (H (f:=f) (ell:=ell))) (hc : IsNative Nₛ Cₛ r c) :
    (Bₛ hf).program.run c = reduce c.prec f ell ((Bₛ hf).truth c) :=
  (Bₛ hf).run_exact (actualSourceSpec S Δ sel r G hf) hf hF c hc

omit envDec in
theorem native_run_root (G : NativeGuards S Δ sel r) (hf : f.Monic)
    (hF : 0 < f.natDegree) [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (hs : r.host.edgeCount = r.edges) :
    (Bₛ hf).program.run r = reduce r.prec f ell (r.host.contract hf) := by
  rw [native_run_reachable S Δ sel r G hf hF r (NativeReach.reflexive _),
    physicalBlueprint_truth hf (Bₛ hf) rfl r hs]

#print axioms actualF_degree
#print axioms actualJet_local
#print axioms actualF_origin
#print axioms actualSourceSpec
#print axioms native_run_root
end J6R12Integral
