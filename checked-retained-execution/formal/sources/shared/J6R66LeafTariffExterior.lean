import J6R66LeafTariffNumbers
import J6R65LeafRateEntry
import J6R49LeafExterior
import J6R52FreshExteriorWordsMenu

/-! The original paid exterior atlas, not an arbitrary packet with
compatible output. Its finite page contains no more physical rows or
columns than its seats; its creation parameter is the depth-zero
mesh, although the exterior child's actual absolute depth is one. -/
namespace J6R66LeafTariff
open scoped Polynomial Classical
open AOracleMachineTime J6Mesh J6OrientedHost P11FullPacking J6R24LegalLayout
open J6R34RootAtlas J6R35RootOrigins J6R49Leaf J6R52FreshExterior
open J6R26StablePreparedRoot J6R27PrescribedProbe J6R32RootGeneratedRegistryInputs
open J6R30ProducedGateRegistry J6R14ZeroMode
open J6R27OriginalGate J6R18ChildWrite J6R21Ancestor J6R31RootResidentTables
open J6R30GeneratedRootLayout J6R32ChildResidentTransfer J6R32StatefulArithmetic
open J6R33StatefulArithmeticPage J6R48Leaf J6R65LeafRate J6R24MeteredRecursion

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 20000000
set_option maxRecDepth 3300
set_option Elab.async false

variable {V : Type} [Fintype V]
variable {f : ℤ[X]} {m n base native : ℕ} {T : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) T
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q ro co d edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q ro co d edgew tc tj key prec tw bw)

private theorem length_of_injective_seats {A : Type*} {n : ℕ} (l : List A) (nd : l.Nodup)
    (seat : A→Fin n) (inj : Function.Injective seat) : l.length≤n := by
  simpa only [List.length_map,Fintype.card_fin] using (nd.map inj).length_le_card

theorem printed_exterior_page_dimensions (k : CanonicalPage m) :
    (X.chosenFields k).rows.length≤L m ∧
    (X.chosenFields k).cols.length≤L m ∧
    (X.chosenFields k).modes.length≤M m*(J6SourcePrecision.printed m base-1) := by
  let P := rootChart T
  let i := oddAxis m
  obtain ⟨hrow,hcol,rn,cn,_,_,ξ,ms,hm,_,_⟩ := stable_seed_true_page_law X k
  have rInj : Function.Injective (fun u : RowsOf P i X.group k=>(P.seat u.val).2) := by
    intro u v e
    apply Subtype.ext
    apply P.seat.injective
    have hu : (P.seat u.val).1=k := congrArg Prod.snd u.property
    have hv : (P.seat v.val).1=k := congrArg Prod.snd v.property
    exact Prod.ext (hu.trans hv.symm) e
  have cInj : Function.Injective (fun u : ColsOf P i X.group k=>(P.seat u.val).2) := by
    intro u v e
    apply Subtype.ext
    apply P.seat.injective
    exact Prod.ext (u.property.2.trans v.property.2.symm) e
  constructor
  · rw [hrow,List.length_map]
    exact length_of_injective_seats _ rn _ rInj
  constructor
  · rw [hcol,List.length_map]
    exact length_of_injective_seats _ cn _ cInj
  · rw [hm,List.length_ofFn]
    have card := Fintype.card_congr ξ
    simp only [Fintype.card_fin] at card
    rw [card]
    exact packet_mode_count_printed m _ i

theorem printed_exterior_atlas_count (pad : ℕ) :
    (X.seed pad).immutable.payload.payload.pages.length=D m*K m ∧
    (X.seed pad).immutable.payload.payload.pages.length*L m=M m := by
  have shape : (X.seed pad).immutable.payload.payload.pages.length=D m*K m := by
    change ((rootTable X.chosenFields).map (mappedRow pad)).length=D m*K m
    rw [List.length_map,rootTable,List.length_map,(child_pages_complete (a m) (K m)).2.2]
    have cells : (2^(6*a m)*2^(6*a m))=D m := by
      rw [←pow_add]
      unfold a D
      congr 1
      omega
    rw [cells]
  exact ⟨shape,by rw [shape,Nat.mul_assoc,mesh_product]⟩

theorem literal_exterior_start_precision_quadratic (hn : native≤m) {C : ℕ}
    (Cpos : 0<C) (baseFit : base≤C*physicalSize m native) :
    (exteriorChild G ell X.centre X.sample X.group).prec≤161*C*(physicalSize m native)^2 := by
  have birth := (stable_exterior_header X).2.2
  rw [←birth,X.birthOK]
  exact printed_exterior_register_size m native base C hn Cpos baseFit

theorem physical_exterior_source_lambda_large (m native : ℕ) (hn : native≤m) :
    1024≤Nat.clog 2 (physicalSize m native) := by
  rw [(physicalSize_ceiling m native hn).2.2]
  unfold lambda
  have ht := b_pos m
  omega
/-- Exact reader on the published exterior packet: the exponential
comes from the actual mode and row counts, not a fee supplied at leaf.
The remaining local factor exposes its supplied widths and wire tape. -/
theorem actual_exterior_reader_geometric (hn : native≤m) {C : ℕ}
    (Cpos : 0<C) (Csmall : C≤physicalSize m native) (baseFit : base≤C*physicalSize m native)
    (large : 1024≤Nat.clog 2 (physicalSize m native))
    (pad : ℕ) (k : CanonicalPage m)
    (B : PageBank f ell key prec tw bw (pageKeyWidth m+pad)) (alive : IsLive (X.seed pad) B)
    {p e edges : ℕ} (dep : ℕ) (wires : List WireRead) :
    let r := (X.seed pad).immutable.payload
    let fld : pageFields r := X.chosenFields k
    let s := physicalSize m native
    rawPageFee e p edges B (.generated (X.seed pad).identifier
        (widened pad (residentPageKey m k)).result dep wires)≤
      2^(6*J9PrintedSchedule.leafThreshold s (Nat.clog 2 s))*actualPacketPrefactor B r fld p dep wires := by
  let job := X.seed pad
  let record := job.immutable.payload
  let fld : pageFields record := X.chosenFields k
  let s := physicalSize m native
  have axes : record.payload.shape.a=J1PPrinted.stepA (Nat.clog 2 s) 0 :=
    (same_printed_source_mesh m native hn).symm
  have dims := printed_exterior_page_dimensions X k
  have area : fld.modes.length≤3*(C*s)*(J6SourcePrecision.printed m base) := by
    calc
      _≤M m*(J6SourcePrecision.printed m base-1) := dims.2.2
      _≤M m*J6SourcePrecision.printed m base := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _≤(2*s)*J6SourcePrecision.printed m base :=
        Nat.mul_le_mul_right _ (actual_mesh_M_at_most_twice_source m native hn)
      _≤_ := by
        apply Nat.mul_le_mul_right
        have cs : s≤C*s := Nat.le_mul_of_pos_left _ Cpos
        omega
  have pfit : J6SourcePrecision.printed m base≤321*C*s^2 := by
    exact (printed_exterior_register_size m native base C hn Cpos baseFit).trans
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right C (by decide : 161≤321)))
  have modes := native_mode_count_at_absolute_receiver large Csmall pfit area
  exact found_generated_reader_rate_from_created_page_dimensions B record fld job.identifier
    (widened pad (residentPageKey m k)).result alive.2 (true_seed_payload_page X pad k)
    s 0 large axes dims.1 modes e p edges dep wires

#print axioms printed_exterior_page_dimensions
#print axioms printed_exterior_atlas_count
#print axioms literal_exterior_start_precision_quadratic
#print axioms physical_exterior_source_lambda_large
#print axioms actual_exterior_reader_geometric
end J6R66LeafTariff
