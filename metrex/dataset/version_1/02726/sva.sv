// SVA for mux_1bit. Bind this to the DUT.
module mux_1bit_sva (
  input logic        ctrl,
  input logic  [0:0] D0,
  input logic  [0:0] D1,
  input logic  [0:0] S
);

  // Control must be known (avoids latch-on-X behavior)
  a_ctrl_known: assert property ( !$isunknown(ctrl) )
    else $error("mux_1bit: ctrl is X/Z");

  // Functional correctness (4-state exact)
  a_sel0: assert property ( (ctrl === 1'b0) |-> (S === D0) )
    else $error("mux_1bit: ctrl=0, S != D0");
  a_sel1: assert property ( (ctrl === 1'b1) |-> (S === D1) )
    else $error("mux_1bit: ctrl=1, S != D1");

  // No X on output when selected data is known
  a_no_x_out0: assert property ( (ctrl === 1'b0 && !$isunknown(D0)) |-> !$isunknown(S) )
    else $error("mux_1bit: S X/Z with ctrl=0 and known D0");
  a_no_x_out1: assert property ( (ctrl === 1'b1 && !$isunknown(D1)) |-> !$isunknown(S) )
    else $error("mux_1bit: S X/Z with ctrl=1 and known D1");

  // Minimal functional coverage (both selects and both data values pass through)
  c_sel0_0: cover property ( ctrl===1'b0 && D0===1'b0 && S===1'b0 );
  c_sel0_1: cover property ( ctrl===1'b0 && D0===1'b1 && S===1'b1 );
  c_sel1_0: cover property ( ctrl===1'b1 && D1===1'b0 && S===1'b0 );
  c_sel1_1: cover property ( ctrl===1'b1 && D1===1'b1 && S===1'b1 );

endmodule

bind mux_1bit mux_1bit_sva u_mux_1bit_sva (.ctrl(ctrl), .D0(D0), .D1(D1), .S(S));