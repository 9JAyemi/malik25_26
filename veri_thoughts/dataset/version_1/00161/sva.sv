// SVA for mux_2_1_syncreset
// Bind this to the DUT to check functionality and provide concise coverage.

module mux_2_1_syncreset_sva (
  input logic        clk,
  input logic        rst,
  input logic        sel,
  input logic [31:0] in1,
  input logic [31:0] in2,
  input logic [31:0] out
);
  default clocking cb @(posedge clk); endclocking

  // Core behavior: synchronous reset dominates
  assert property (rst |-> (out == 32'h0))
    else $error("mux_2_1_syncreset: out not 0 during rst");

  // Core behavior: registered mux selection when not in reset
  assert property (!rst |-> (out === (sel ? in1 : in2)))
    else $error("mux_2_1_syncreset: out != selected input");

  // Sanity: sel must be 0/1 when not in reset (avoid X-driven path selection)
  assert property (!rst |-> !$isunknown(sel))
    else $error("mux_2_1_syncreset: sel is X/Z when not in reset");

  // Optional: out is known during reset
  assert property (rst |-> !$isunknown(out))
    else $error("mux_2_1_syncreset: out X/Z during rst");

  // Functional coverage
  cover property (rst);                   // reset seen
  cover property (rst ##1 !rst);          // reset deasserted
  cover property (!rst && sel);           // sel=1 path exercised
  cover property (!rst && !sel);          // sel=0 path exercised
  cover property (!rst && sel  ##1 !rst && !sel); // sel 1->0
  cover property (!rst && !sel ##1 !rst && sel ); // sel 0->1
endmodule

bind mux_2_1_syncreset mux_2_1_syncreset_sva sva_bind (
  .clk(clk), .rst(rst), .sel(sel), .in1(in1), .in2(in2), .out(out)
);