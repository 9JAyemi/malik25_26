// SVA for sky130_fd_sc_lp__bufinv
// Bind-in assertions with concise functional/structural checks and basic coverage.

`ifndef SYNTHESIS
module bufinv_sva (
  input logic A,
  input logic Y,
  input logic not0_out_Y
);

  // Use any edge on relevant nets as the assertion clock; sample after ##0 to avoid races.
  default clocking cb @(
      posedge A or negedge A or
      posedge not0_out_Y or negedge not0_out_Y or
      posedge Y or negedge Y
  ); endclocking

  // Functional and stage-by-stage equivalence (accepts X/Z propagation via 4-state compare).
  property p_func_struct;
    1'b1 |-> ##0 ((Y === ~A) && (not0_out_Y === ~A) && (Y === not0_out_Y));
  endproperty
  assert property (p_func_struct)
    else $error("bufinv: functional/structural mismatch: Y=%b not0_out_Y=%b A=%b", Y, not0_out_Y, A);

  // On any A change, both internal and output must change in the next delta.
  assert property ($changed(A) |-> ##0 ($changed(not0_out_Y) && $changed(Y)))
    else $error("bufinv: output/internal did not react to A change");

  // Basic behavioral coverage.
  cover property ($rose(A) ##0 $fell(Y)); // rising A causes falling Y
  cover property ($fell(A) ##0 $rose(Y)); // falling A causes rising Y
  cover property ((A === 1'b0) ##0 (Y === 1'b1));
  cover property ((A === 1'b1) ##0 (Y === 1'b0));
  cover property ((A === 1'bx) ##0 (Y === 1'bx)); // X-propagation observed
  cover property ($changed(not0_out_Y));

endmodule

bind sky130_fd_sc_lp__bufinv bufinv_sva u_bufinv_sva (.*);
`endif