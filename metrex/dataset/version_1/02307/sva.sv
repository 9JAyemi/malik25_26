// SVA for sky130_fd_sc_hdll__einvn (tri-state inverter with active-low enable)
// notif0: TE_B==0 -> Z = ~A; TE_B==1 -> Z = 'z

module sky130_fd_sc_hdll__einvn_sva (
  input  logic A,
  input  logic TE_B,
  input  wire  Z
);

  // Disabled -> tri-state
  property p_tristate_when_disabled;
    @(A or TE_B or Z) (TE_B === 1'b1) |-> ##0 (Z === 1'bz);
  endproperty
  assert property (p_tristate_when_disabled);

  // Enabled -> not tri-state
  property p_not_tristate_when_enabled;
    @(A or TE_B or Z) (TE_B === 1'b0) |-> ##0 (Z !== 1'bz);
  endproperty
  assert property (p_not_tristate_when_enabled);

  // Enabled with known A -> invert
  property p_invert_when_enabled_known;
    @(A or TE_B or Z) (TE_B === 1'b0 && !$isunknown(A)) |-> ##0 (Z === ~A);
  endproperty
  assert property (p_invert_when_enabled_known);

  // Enabled with unknown A -> Z must be unknown (but not 'z)
  property p_xprop_from_input_when_enabled;
    @(A or TE_B or Z) (TE_B === 1'b0 &&  $isunknown(A)) |-> ##0 ($isunknown(Z) && Z !== 1'bz);
  endproperty
  assert property (p_xprop_from_input_when_enabled);

  // Unknown enable -> unknown output
  property p_xprop_from_enable;
    @(A or TE_B or Z) ($isunknown(TE_B)) |-> ##0 ($isunknown(Z));
  endproperty
  assert property (p_xprop_from_enable);

  // Coverage: driven 0/1, tri-state, and enable edges
  cover property (@(A or TE_B or Z) (TE_B===1'b0 && A===1'b0) ##0 (Z===1'b1));
  cover property (@(A or TE_B or Z) (TE_B===1'b0 && A===1'b1) ##0 (Z===1'b0));
  cover property (@(A or TE_B or Z) (TE_B===1'b1) ##0 (Z===1'bz));
  cover property (@(posedge TE_B) ##0 (Z===1'bz));
  cover property (@(negedge TE_B) ##0 (!$isunknown(A) && (Z===~A)));

endmodule

bind sky130_fd_sc_hdll__einvn sky130_fd_sc_hdll__einvn_sva u_einvn_sva (
  .A(A),
  .TE_B(TE_B),
  .Z(Z)
);