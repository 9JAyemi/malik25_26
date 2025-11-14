// SVA for mux_stall
// Quality-focused, concise checks and coverage

`ifndef MUX_STALL_SVA
`define MUX_STALL_SVA

module mux_stall_sva
  #(parameter int W = 23)
(
  input logic [W-1:0] cw_from_cu,
  input logic         mux_op,
  input logic [W-1:0] cw_from_mux
);

  // Functional equivalence: bitwise mask by mux_op
  assert property (cw_from_mux === (cw_from_cu & {W{mux_op}}))
    else $error("mux_stall: mask equation violated");

  // Corner cases
  assert property ((!mux_op) |-> (cw_from_mux === '0))
    else $error("mux_stall: output not zero when mux_op=0");

  assert property (( mux_op) |-> (cw_from_mux === cw_from_cu))
    else $error("mux_stall: output not pass-through when mux_op=1");

  // Safety: output cannot set bits not set on input
  assert property ( (cw_from_mux & ~cw_from_cu) == '0 )
    else $error("mux_stall: output has bits not present on input");

  // Stability: no output glitch without input change
  assert property ( $stable({cw_from_cu,mux_op}) |-> $stable(cw_from_mux) )
    else $error("mux_stall: output glitches without input change");

  // Coverage
  cover property (!mux_op);
  cover property ( mux_op);
  cover property ($rose(mux_op));
  cover property ($fell(mux_op));
  cover property ( mux_op && (|cw_from_cu) && (cw_from_mux === cw_from_cu) );
  cover property (!mux_op && (|cw_from_cu) && (cw_from_mux === '0) );

endmodule

bind mux_stall mux_stall_sva #(.W(23)) u_mux_stall_sva (.*);

`endif