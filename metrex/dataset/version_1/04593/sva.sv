// SVA for OR_gate_pipeline
module OR_gate_pipeline_sva(
  input logic a, b, clk,
  input logic out,
  input logic p1_out
);
  default clocking cb @(posedge clk); endclocking

  // Combo stage correct at sampling instants
  ap_comb_func: assert property ( !$isunknown({a,b}) |-> (p1_out == (a | b)) );

  // Pipeline register transfers previous p1_out
  ap_reg_xfer:  assert property ( !$isunknown($past({a,b})) |-> (out == $past(p1_out)) );

  // End-to-end 1-cycle latency from a|b to out
  ap_e2e:       assert property ( !$isunknown($past({a,b})) |-> (out == $past(a | b)) );

  // No X on out when previous inputs were known
  ap_no_x_out:  assert property ( !$isunknown($past({a,b})) |-> !$isunknown(out) );

  // Coverage: observe 0->1 and 1->0 propagation through the pipeline
  cp_rise: cover property ( !$past(a|b) && (a|b) ##1 out );
  cp_fall: cover property (  $past(a|b) && !(a|b) ##1 !out );
endmodule

bind OR_gate_pipeline OR_gate_pipeline_sva u_or_gate_pipeline_sva(
  .a(a), .b(b), .clk(clk), .out(out), .p1_out(p1_out)
);

// Optional top-level bind (redundant but ensures end-to-end at top)
module top_module_sva(input logic a, b, clk, out);
  default clocking cb @(posedge clk); endclocking
  ap_top_e2e: assert property ( !$isunknown($past({a,b})) |-> (out == $past(a | b)) );
endmodule

bind top_module top_module_sva u_top_module_sva(
  .a(a), .b(b), .clk(clk), .out(out)
);