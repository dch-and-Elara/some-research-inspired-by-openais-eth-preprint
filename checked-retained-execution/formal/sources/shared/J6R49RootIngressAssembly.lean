import J6R49RootIngressPorts

/-! The exact metered CNF → signed compact root file is fed directly
into the existing same-chart R30 padded ingress. The sole declared
chart input is a serialized position atlas in the original old
wire order, not a supplied signed port table or padded seat file. -/
namespace J6R49RootIngress
open scoped Classical
open Std.Sat J6OrientedHost J7R10Ports J7R10Plant A1R10 AOracleMachineTime
open J6R30GeneratedRootLayout J6Mesh
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 9000000
set_option maxRecDepth 2900

def signAtlas {r c d h : ℕ} (rows : BitsCNF) :
    List (Position r c d h)→Meter (Option (List (SignedHalfPort r c d)))
  | [] => ⟨some [],1⟩
  | x::xs =>
    let a := signPosition rows x
    let b := signAtlas rows xs
    ⟨a.result.bind (fun y => b.result.map (y::·)),a.steps+b.steps+4⟩

theorem signed_atlas_map {I : Type*} {r c d h : ℕ}
    (rows : BitsCNF) (ids : List I) (pos : I→Position r c d h) (expected : I→SignedHalfPort r c d)
    (exactPos : ∀ j,(signPosition rows (pos j)).result=some (expected j)) :
    (signAtlas rows (ids.map pos)).result=some (ids.map expected) := by
  induction ids with
  | nil => rfl
  | cons j ids ih => simp [signAtlas,exactPos j,ih]

def signFee (r c d h maxrow rows : ℕ) : ℕ :=
  26+rows*(10*h+8)+maxrow*(10*d+8)+seedFee r c d

theorem signed_atlas_steps {r c d h : ℕ}
    (rows : BitsCNF) (pos : List (Position r c d h)) (maxrow : ℕ)
    (legal : ∀ c∈rows,c.length≤maxrow) :
    (signAtlas rows pos).steps ≤ 1+pos.length*signFee r c d h maxrow rows.length := by
  induction pos with
  | nil => simp [signAtlas]
  | cons x xs ih =>
    have fee := sign_position_fee rows x maxrow legal
    simp only [signAtlas,List.length_cons]
    rw [Nat.add_mul,Nat.one_mul]
    simp only [signFee] at ih ⊢
    omega

theorem exact_compact_chart_rows {V : Type*} [DecidableEq V] [Fintype V]
    (H : CNF V) (code : V→List Bool) {r c d h : ℕ}
    (C : LiteralCodec (physicalPlant H) r c d) (fit : H.length≤2^h)
    (pos : List (Position r c d h))
    (chart : pos=List.ofFn (positionForWire H C)) :
    (signAtlas (codeCNF code H) pos).result=some (List.ofFn (plantHalfPort (physicalPlant H) C)) := by
  rw [chart]
  have hh := signed_atlas_map (codeCNF code H) (List.ofFn (fun j : Fin (nWires H) => j))
    (positionForWire H C) (plantHalfPort (physicalPlant H) C)
    (sign_wire_exact H code C fit)
  simpa only [List.map_ofFn] using hh

def compileRootIngress {r c d h : ℕ}
    (declares : List (List Bool)) (raw : BitsCNF) (pos : List (Position r c d h)) :
    Meter (Option (List (SignedHalfPort r c d))) :=
  let a := guardedMeter declares raw
  let b := signAtlas a.result pos
  ⟨b.result,a.steps+b.steps+5⟩

noncomputable abbrev guarded {V : Type*} [DecidableEq V] [Fintype V] (F : CNF V) := J7R9SourceInput.H F

theorem paid_compact_root_ingress {V : Type} [DecidableEq V] [Fintype V]
    (F : CNF V) (code : V→List Bool) (inj : Function.Injective code)
    {r c d h : ℕ} (C : LiteralCodec (physicalPlant (guarded F)) r c d)
    (fit : (guarded F).length≤2^h)
    (pos : List (Position r c d h)) (chart : pos=List.ofFn (positionForWire (guarded F) C)) :
    ∃ output : CNFPortFile F r c d,
      (compileRootIngress ((Finset.univ : Finset V).toList.map code) (codeCNF code F) pos).result=
        some output.raw ∧ output.codec=C := by
  let out := List.ofFn (plantHalfPort (physicalPlant (guarded F)) C)
  refine ⟨⟨C,out,rfl⟩,?_,rfl⟩
  change (signAtlas (guardedMeter ((Finset.univ : Finset V).toList.map code) (codeCNF code F)).result pos).result=
    some out
  rw [paid_guard_original_syntax code inj F]
  exact exact_compact_chart_rows (guarded F) (guardCode code) C fit pos chart

def mountIngress {r c d h : ℕ} (m : ℕ) (declares : List (List Bool)) (raw : BitsCNF)
    (pos : List (Position r c d h)) : Meter (Option (List (MountedPort r c d))) :=
  let a := compileRootIngress declares raw pos
  match a.result with
  | none => ⟨none,a.steps+4⟩
  | some x =>
    let b := generatedPaddedPorts m x
    ⟨some b.result,a.steps+b.steps+5⟩

theorem paid_same_chart_padded_ingress {V : Type} [DecidableEq V] [Fintype V]
    (F : CNF V) (code : V→List Bool) (inj : Function.Injective code)
    {r c d h : ℕ} (C : LiteralCodec (physicalPlant (guarded F)) r c d)
    (fit : (guarded F).length≤2^h)
    (pos : List (Position r c d h)) (chart : pos=List.ofFn (positionForWire (guarded F) C)) :
    let m := J7R10Readout.mCNF F
    let input := mountIngress m ((Finset.univ : Finset V).toList.map code) (codeCNF code F) pos
    ∃ compact : CNFPortFile F r c d,
      compact.codec=C ∧ input.result=some ((actualWires m).map (trueMounted compact)) := by
  obtain ⟨compact,exactRaw,eq⟩ := paid_compact_root_ingress F code inj C fit pos chart
  refine ⟨compact,eq,?_⟩
  dsimp only [mountIngress]
  rw [exactRaw]
  change some (generatedPaddedPorts (J7R10Readout.mCNF F) compact.raw).result=_
  exact congrArg some (generated_padded_ports_exact compact).1

#print axioms signed_atlas_map
#print axioms signed_atlas_steps
#print axioms exact_compact_chart_rows
#print axioms paid_compact_root_ingress
#print axioms paid_same_chart_padded_ingress
end J6R49RootIngress
