// SVA checker for Multiplexer_AC__parameterized30
module Multiplexer_AC__parameterized30_sva
(
  input logic       ctrl,
  input logic [0:0] D0,
  input logic [0:0] D1,
  input logic [0:0] S
);

  // Check on any relevant edge of inputs/outputs
  default clocking cb @(
      posedge ctrl or negedge ctrl or
      posedge D0[0] or negedge D0[0] or
      posedge D1[0] or negedge D1[0] or
      posedge S[0]  or negedge S[0]
  ); endclocking

  // Functional equivalence (4-state aware)
  ap_func_eq: assert property ( S[0] === (ctrl ? D1[0] : D0[0]) )
    else $error("MUX func mismatch: S=%0b ctrl=%0b D1=%0b D0=%0b", S[0],ctrl,D1[0],D0[0]);

  // No X/Z on output when inputs are known
  ap_no_x_on_known_in: assert property ( (!$isunknown({ctrl,D0[0],D1[0]})) |-> ##0 !$isunknown(S[0]) )
    else $error("MUX produced X/Z on S with known inputs");

  // Selected data follows immediately
  ap_follow_d0: assert property ( (!ctrl && $changed(D0[0])) |-> ##0 (S[0] == D0[0]) )
    else $error("MUX failed to follow D0 when ctrl=0");
  ap_follow_d1: assert property ( ( ctrl && $changed(D1[0])) |-> ##0 (S[0] == D1[0]) )
    else $error("MUX failed to follow D1 when ctrl=1");

  // Unselected input does not influence output
  ap_block_d1_when_sel0: assert property ( (!ctrl && $changed(D1[0])) |-> ##0 !$changed(S[0]) )
    else $error("MUX S changed due to D1 while ctrl=0");
  ap_block_d0_when_sel1: assert property ( ( ctrl && $changed(D0[0])) |-> ##0 !$changed(S[0]) )
    else $error("MUX S changed due to D0 while ctrl=1");

  // Control edge behavior (same-cycle selection)
  ap_ctrl_rise: assert property ( $rose(ctrl) |-> ##0 (S[0] == D1[0]) )
    else $error("MUX S not equal to D1 on ctrl rise");
  ap_ctrl_fall: assert property ( $fell(ctrl) |-> ##0 (S[0] == D0[0]) )
    else $error("MUX S not equal to D0 on ctrl fall");

  // Coverage
  cp_ctrl0_path: cover property ( !ctrl && $changed(D0[0]) && S[0]==D0[0] );
  cp_ctrl1_path: cover property (  ctrl && $changed(D1[0]) && S[0]==D1[0] );
  cp_ctrl_rise:  cover property ( $rose(ctrl) );
  cp_ctrl_fall:  cover property ( $fell(ctrl) );
  cp_block_d1:   cover property ( !ctrl && $changed(D1[0]) && !$changed(S[0]) );
  cp_block_d0:   cover property (  ctrl && $changed(D0[0]) && !$changed(S[0]) );

endmodule

// Bind into the DUT
bind Multiplexer_AC__parameterized30 Multiplexer_AC__parameterized30_sva mux_sva (.*);