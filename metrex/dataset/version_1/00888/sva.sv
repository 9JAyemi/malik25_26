// SVA for sky130_fd_sc_lp__udp_mux_2to1_N
// Bindable, concise, and 4-state accurate (includes X-prop checks)

module sky130_fd_sc_lp__udp_mux_2to1_N_sva (
  input logic A0, A1, S, Y
);

  // Sample on any relevant edge
  default clocking cb @(
    posedge A0 or negedge A0 or
    posedge A1 or negedge A1 or
    posedge S  or negedge S  or
    posedge Y  or negedge Y
  ); endclocking

  // Combinational functional equivalence (race-free)
  always_comb
    assert (#0 (Y === ((~S & A0) | (S & A1))))
      else $error("MUX func mismatch Y=%b S=%b A1=%b A0=%b", Y, S, A1, A0);

  // Deterministic selection when select and chosen input are known
  assert property ((S===1'b0 && !$isunknown(A0)) |-> (Y===A0));
  assert property ((S===1'b1 && !$isunknown(A1)) |-> (Y===A1));

  // If S is known and selected input is X/Z, Y must be unknown
  assert property ((S===1'b0 && $isunknown(A0)) |-> $isunknown(Y));
  assert property ((S===1'b1 && $isunknown(A1)) |-> $isunknown(Y));

  // X-propagation behavior with unknown select
  assert property (($isunknown(S) && A0===1'b0 && A1===1'b0) |-> (Y===1'b0)); // pessimism collapses to 0
  assert property (($isunknown(S) && !$isunknown(A0) && !$isunknown(A1) && (A0!==A1)) |-> $isunknown(Y));
  assert property (($isunknown(S) && A0===1'b1 && A1===1'b1) |-> $isunknown(Y)); // gate-level pessimism

  // Minimal functional coverage
  cover property (S===1'b0 && A0===1'b0 && Y===1'b0);
  cover property (S===1'b0 && A0===1'b1 && Y===1'b1);
  cover property (S===1'b1 && A1===1'b0 && Y===0);
  cover property (S===1'b1 && A1===1'b1 && Y===1);
  cover property ($isunknown(S) && A0===1'b0 && A1===1'b0 && Y===0);
  cover property ($isunknown(S) && A0===1'b1 && A1===1'b1 && $isunknown(Y));
  cover property ($rose(Y));
  cover property ($fell(Y));

endmodule

bind sky130_fd_sc_lp__udp_mux_2to1_N sky130_fd_sc_lp__udp_mux_2to1_N_sva sva_inst (.*);