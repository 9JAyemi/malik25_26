// SVA for top_module and mux2to1
// Concise, combinational (clockless) checks with functional and X-prop coverage

`ifndef SYNTHESIS

// Generic SVA for any mux2to1 instance
module mux2to1_sva;
  default clocking cb @(*); endclocking

  // Functional correctness
  a_func: assert property (out === (sel ? b : a));

  // X-propagation semantics of ?: 
  a_x_equal: assert property ($isunknown(sel) && (a===b) |-> out===a);
  a_x_diff:  assert property ($isunknown(sel) && (a!==b) |-> $isunknown(out));

  // Basic coverage
  c_sel0: cover property (sel===1'b0 && out===a);
  c_sel1: cover property (sel===1'b1 && out===b);

  // Pass-through change coverage
  c_passthru_a: cover property (sel===1'b0 && $changed(a) ##0 $changed(out));
  c_passthru_b: cover property (sel===1'b1 && $changed(b) ##0 $changed(out));
endmodule

bind mux2to1 mux2to1_sva mux2to1_sva_i();


// Top-level SVA
module top_module_sva;
  default clocking cb @(*); endclocking

  // Final stage consistency with intermediate muxes
  a_top_stage: assert property (out_mux === (sel[1] ? mux2_out : mux1_out));

  // End-to-end mapping (4 paths)
  a_map00: assert property (sel===2'b00 |-> out_mux===a);
  a_map01: assert property (sel===2'b01 |-> out_mux===b);
  a_map10: assert property (sel===2'b10 |-> out_mux===c);
  a_map11: assert property (sel===2'b11 |-> out_mux===d);

  // X-propagation on top select bit
  a_top_x_equal: assert property ($isunknown(sel[1]) && (mux1_out===mux2_out) |-> out_mux===mux1_out);
  a_top_x_diff:  assert property ($isunknown(sel[1]) && (mux1_out!==mux2_out) |-> $isunknown(out_mux));

  // Coverage: hit all select combinations
  c_sel00: cover property (sel===2'b00 && out_mux===a);
  c_sel01: cover property (sel===2'b01 && out_mux===b);
  c_sel10: cover property (sel===2'b10 && out_mux===c);
  c_sel11: cover property (sel===2'b11 && out_mux===d);

  // Coverage: data change propagates while selection fixed
  c_path_a: cover property (sel===2'b00 && $changed(a) ##0 $changed(out_mux));
  c_path_b: cover property (sel===2'b01 && $changed(b) ##0 $changed(out_mux));
  c_path_c: cover property (sel===2'b10 && $changed(c) ##0 $changed(out_mux));
  c_path_d: cover property (sel===2'b11 && $changed(d) ##0 $changed(out_mux));

  // Coverage: exercise unknowns on select bits
  c_x0: cover property ($isunknown(sel[0]));
  c_x1: cover property ($isunknown(sel[1]));
endmodule

bind top_module top_module_sva top_module_sva_i();

`endif