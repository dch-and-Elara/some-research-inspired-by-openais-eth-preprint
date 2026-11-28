import J6R20AncestorRoute

/-! The address on the retained input wire is the literal nested
half-port identifier. Its unchanged tail is the ancestor packet's
source slot; it is not obtained by invoking the logical reindex. -/
namespace J6R20Ancestor
open J6R10Repack P11FullPacking J6R9PacketScopes

variable {E A B G : Type} [LinearOrder G] [Fintype G] {a : ℕ} {N : Network E A B}

def literalPort {H K : Type} {P : PhysicalPacking N a G} {i : Fin a} {g : G}
    {h : H} (grp : GroupMap P i g H) (pkt : PacketMap P i g K)
    (k : Page a P.copies G) (stay : grp (.inr k)=h)
    (y : HopPorts grp pkt k stay) (value : Bool) : Raw :=
  let mid := (edge y.val).val
  let base := (edge mid).val
  (side y.val::side mid::side base::(slotWord P (edge base)).bits,value)

theorem literalPort_is_nested {H K : Type} {P : PhysicalPacking N a G} {i : Fin a} {g : G}
    {h : H} (grp : GroupMap P i g H) (pkt : PacketMap P i g K)
    (k : Page a P.copies G) (stay : grp (.inr k)=h)
    (y : HopPorts grp pkt k stay) (b : Bool) :
    literalPort grp pkt k stay y b=nested (originKey P i g k (hop grp pkt k stay y),b) := by
  rcases y with ⟨q,hq⟩
  cases q with
  | inr e => cases hq
  | inl e =>
    have hm : owner (OriginNet P i g) e.val=(Sum.inr k) :=
      congrArg Subtype.val (Sum.inl.inj hq)
    rcases e with ⟨e,he⟩
    cases e with
    | inl p => cases hm
    | inr p => rfl

theorem literalTape_is_payload {H K : Type} {P : PhysicalPacking N a G} {i : Fin a} {g : G}
    {h : H} (grp : GroupMap P i g H) (pkt : PacketMap P i g K)
    (k : Page a P.copies G) (stay : grp (.inr k)=h)
    (assign : HopPorts grp pkt k stay→Bool) (ps : List (HopPorts grp pkt k stay)) :
    ps.map (fun y=>literalPort grp pkt k stay y (assign y)) =
      (portPayloads grp pkt k stay assign ps).map nested := by
  unfold portPayloads
  rw [List.map_map]
  exact List.map_congr_left (fun y _=>literalPort_is_nested grp pkt k stay y (assign y))

#print axioms literalPort_is_nested
#print axioms literalTape_is_payload
end J6R20Ancestor

