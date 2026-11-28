import J6R12BlueprintSite
import J6R10RepackRounded

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

/-! The N2 collision proof belongs to the exact labels of the returned
PhysicalPacking. Preserve it before selection; the projected chart is
one legal R12 Selector used unchanged by the existing packet factory. -/
namespace V8NativeMessage.N2DLabels
open scoped Classical Polynomial
open J6R10Repack J6R11Repack J6R11CollisionReindex P11FullPacking
open J6R12Blueprint J6R11Blueprint J6ActiveRun J6R9Recursive

section Graph
variable {E R C : Type*} {a : ℕ}

def CollisionCertified {N : Network E R C} (Δ : ℕ)
    (P : PhysicalPacking N a (Fin 64)) : Prop :=
  varianceScore (declaredCell N P.rowLabel P.colLabel) ≤ 2*(Nat.card E:ℚ)*Δ

abbrev CertifiedPacking (N : Network E R C) (a Δ : ℕ) :=
  {P : PhysicalPacking N a (Fin 64) // CollisionCertified Δ P}

def RoundsExactly {N : Network E R C} (P : PhysicalPacking N a (Fin 64)) : Prop :=
  P.copies=ceilCopies (2^a) (maxFiber (declaredCell N P.rowLabel P.colLabel))

theorem certified_by_same_labels {N : Network E R C} {Δ : ℕ}
    {P Q : PhysicalPacking N a (Fin 64)}
    (row : Q.rowLabel=P.rowLabel) (col : Q.colLabel=P.colLabel)
    (h : CollisionCertified Δ P) : CollisionCertified Δ Q := by
  unfold CollisionCertified at *
  rwa [row,col]

theorem exists_certified_rounded [Fintype E] [Fintype R] [Fintype C]
    (N : Network E R C) (Δ : ℕ)
    (hr : ∀ v,Nat.card {e : E // N.row e=v}≤Δ)
    (hc : ∀ v,Nat.card {e : E // N.col e=v}≤Δ)
    (size : 2*(J9PrintedSchedule.arrayCard a)^2*Δ≤Nat.card E)
    (slots : 2^a*J9PrintedSchedule.arrayCard a≤Nat.card E) :
    ∃ P : CertifiedPacking N a Δ, RoundsExactly P.val := by
  obtain ⟨rl,cl,balanced⟩ := declared_variance_witness (G:=Fin 64) (a:=a) N Δ hr hc
  obtain ⟨P,row,col,copy⟩ := actual_rounded_packing N (by simp) rl cl Δ balanced size slots
  have cert : CollisionCertified Δ P := by
    unfold CollisionCertified
    rwa [row,col]
  exact ⟨⟨P,cert⟩, (show RoundsExactly P from by unfold RoundsExactly; rwa [row,col])⟩
end Graph

section Selector
variable {f : ℤ[X]} {ell Δ : ℕ} {S : Params (f:=f) (ell:=ell)}

abbrev CertifiedSelector (S : Params (f:=f) (ell:=ell)) (Δ : ℕ) :=
  ∀ c : Call (PhysicalHost f ell), Ready S Δ c →
    CertifiedPacking c.host.network (S.levelBits c.depth) Δ

def forget (sel : CertifiedSelector S Δ) : Selector S Δ :=
  fun c d => (sel c d).val

theorem projected_exact (sel : CertifiedSelector S Δ) {c : Call (PhysicalHost f ell)}
    (d : Ready S Δ c) : packing (forget sel) d=(sel c d).val := rfl

theorem selected_variance (sel : CertifiedSelector S Δ) {c : Call (PhysicalHost f ell)}
    (d : Ready S Δ c) : CollisionCertified Δ (packing (forget sel) d) :=
  (sel c d).property

theorem ready_certified_rounded {c : Call (PhysicalHost f ell)} (d : Ready S Δ c) :
    ∃ P : CertifiedPacking c.host.network (S.levelBits c.depth) Δ, RoundsExactly P.val := by
  letI := c.host.finiteEdge
  letI := c.host.finiteRow
  letI := c.host.finiteCol
  have M : Nat.card c.host.Edge=c.edges := (host_card c.host).trans d.edgeCount
  exact exists_certified_rounded c.host.network Δ d.degree.1 d.degree.2
    (M.symm ▸ d.collision) (M.symm ▸ d.paddedSlots)

/-- Choice is applied to certified layouts, not to the older predicate
that kept only rounding. There is no claim that the selected layout is
definitionally the result of the old defaultSelector. -/
noncomputable def certifiedDefault (S : Params (f:=f) (ell:=ell)) (Δ : ℕ) :
    CertifiedSelector S Δ :=
  fun _ d => Classical.choose (ready_certified_rounded d)

theorem certified_default_rounding {c : Call (PhysicalHost f ell)} (d : Ready S Δ c) :
    RoundsExactly (packing (forget (certifiedDefault S Δ)) d) :=
  Classical.choose_spec (ready_certified_rounded d)

/-- The externally selected tied root is allowed only with a receipt on
its own labels. This wrapper does not identify a nonroot tape with it. -/
noncomputable def pinCertified (base : CertifiedSelector S Δ) (root : Call (PhysicalHost f ell))
    (special : CertifiedPacking root.host.network (S.levelBits root.depth) Δ) :
    CertifiedSelector S Δ :=
  fun c d => if h : c=root then h.symm ▸ special else base c d

theorem pin_certified_root (base : CertifiedSelector S Δ) (root : Call (PhysicalHost f ell))
    (special : CertifiedPacking root.host.network (S.levelBits root.depth) Δ)
    (d : Ready S Δ root) :
    packing (forget (pinCertified base root special)) d=special.val := by
  simp [packing,forget,pinCertified]

theorem pin_certified_other (base : CertifiedSelector S Δ) (root : Call (PhysicalHost f ell))
    (special : CertifiedPacking root.host.network (S.levelBits root.depth) Δ)
    {c : Call (PhysicalHost f ell)} (d : Ready S Δ c) (h : c≠root) :
    packing (forget (pinCertified base root special)) d=packing (forget base) d := by
  simp [packing,forget,pinCertified,h]
end Selector

#print axioms certified_by_same_labels
#print axioms exists_certified_rounded
#print axioms projected_exact
#print axioms selected_variance
#print axioms ready_certified_rounded
#print axioms certified_default_rounding
#print axioms pin_certified_root
#print axioms pin_certified_other
end V8NativeMessage.N2DLabels
