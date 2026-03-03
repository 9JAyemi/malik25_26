// SVA for top_module. Concise, high-quality end-to-end checks and coverage.
// Bind this checker to top_module.

module top_module_sva (
  input logic        clk,
  input logic        reset,
  input logic [7:0]  in1,
  input logic [7:0]  in2,
  input logic        select,
  input logic [7:0]  out
);
  // Clock/reset policy
  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Sanity: no X/Z on key I/Os
  a_no_x: assert property ( !$isunknown({in1,in2,select,out}) )
    else $error("X/Z on inputs/outputs");

  // Functional correctness (covers AND stage, XOR stage, and final mux)
  a_and_path: assert property ( !select |-> out == (in1 & in2) )
    else $error("AND path mismatch");

  a_xor_path: assert property (  select |-> out == ((in1 & in2) ^ in2) )
    else $error("XOR path mismatch");

  // Optional combined check (redundant with the two above; uncomment if preferred)
  // a_mux: assert property ( out == (select ? ((in1 & in2) ^ in2) : (in1 & in2)) )
  //   else $error("MUX output mismatch");

  // Coverage: exercise both paths with non-trivial data, select toggles, and bit activity
  c_sel0: cover property ( !select && (in1|in2)!=8'b0 && out == (in1 & in2) );
  c_sel1: cover property (  select && (in1|in2)!=8'b0 && out == ((in1 & in2) ^ in2) );
  c_sel_up:   cover property ( !select ##1 select );
  c_sel_down: cover property (  select ##1 !select );
  c_out_change: cover property ( $changed(out) );

  // Per-bit toggle coverage
  genvar i;
  generate
    for (i=0; i<8; i++) begin : g_cov_bits
      c_out_rise: cover property ( $rose(out[i]) );
      c_out_fall: cover property ( $fell(out[i]) );
    end
  endgenerate
endmodule

// Bind the checker to all instances of top_module
bind top_module top_module_sva top_module_sva_i (.*);