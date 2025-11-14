// SVA for multiplier_block
// Concise, high-signal-coverage checks and a few targeted coverpoints.
// Bind these assertions to the DUT; provide a clock/reset from your TB.

module multiplier_block_sva #(
  parameter int WIDTH = 32
)(
  input  logic                   clk,
  input  logic                   rst_n,

  // DUT ports
  input  logic [WIDTH-1:0]       i_data0,
  input  logic [WIDTH-1:0]       o_data0,

  // DUT internals (bound hierarchically)
  input  logic [WIDTH-1:0]       w1,
  input  logic [WIDTH-1:0]       w2048,
  input  logic [WIDTH-1:0]       w2049,
  input  logic [WIDTH-1:0]       w8196,
  input  logic [WIDTH-1:0]       w6147,
  input  logic [WIDTH-1:0]       w64,
  input  logic [WIDTH-1:0]       w6211,
  input  logic [WIDTH-1:0]       w24844
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // Known-ness: when input is known, no X/Z should appear on internal nets or output
  assert property ( !$isunknown(i_data0) |-> !$isunknown({w1,w2048,w2049,w8196,w6147,w64,w6211,w24844,o_data0}) )
    else $error("multiplier_block: X/Z propagation detected");

  // Structural equivalence chain (shift/add/sub graph)
  assert property ( !$isunknown(i_data0) |-> w1     == i_data0 ) else $error("w1 mismatch");
  assert property ( !$isunknown(i_data0) |-> w2048  == (w1    << 11) ) else $error("w2048 mismatch");
  assert property ( !$isunknown(i_data0) |-> w2049  == (w1    +  w2048) ) else $error("w2049 mismatch");
  assert property ( !$isunknown(i_data0) |-> w64    == (w1    << 6) ) else $error("w64 mismatch");
  assert property ( !$isunknown(i_data0) |-> w8196  == (w2049 << 2) ) else $error("w8196 mismatch");
  assert property ( !$isunknown(i_data0) |-> w6147  == (w8196 -  w2049) ) else $error("w6147 mismatch");
  assert property ( !$isunknown(i_data0) |-> w6211  == (w6147 +  w64) ) else $error("w6211 mismatch");
  assert property ( !$isunknown(i_data0) |-> w24844 == (w6211 << 2) ) else $error("w24844 mismatch");
  assert property ( !$isunknown(i_data0) |-> o_data0 == w24844 ) else $error("o_data0 mismatch to w24844");

  // Functional end-to-end check: o = (i * 24844) mod 2^32
  assert property ( !$isunknown(i_data0) |-> o_data0 == ( (i_data0 * 32'd24844) [WIDTH-1:0] ) )
    else $error("End-to-end multiply-by-24844 mismatch");

  // Minimal but meaningful coverage
  cover property ( !$isunknown(i_data0) && i_data0 == '0 && o_data0 == '0 );                  // zero maps to zero
  cover property ( !$isunknown(i_data0) && i_data0 == '1 );                                   // LSB-only stimulus
  cover property ( !$isunknown(i_data0) && i_data0 == 32'hFFFF_FFFF );                        // max input
  cover property ( !$isunknown(i_data0) && i_data0 == 32'h4000_0000 && o_data0 == '0 );       // wrap-to-zero case
  cover property ( !$isunknown(i_data0) && i_data0 == 32'h8000_0000 && o_data0 == '0 );       // wrap-to-zero case
  cover property ( !$isunknown(i_data0) && i_data0 != '0 && o_data0 != '0 );                  // non-zero maps to non-zero (typical)

endmodule

// Example bind (place in TB or a separate bind file; provide clk/rst_n):
// bind multiplier_block multiplier_block_sva sva (
//   .clk    (clk),
//   .rst_n  (rst_n),
//   .i_data0(i_data0),
//   .o_data0(o_data0),
//   .w1(w1), .w2048(w2048), .w2049(w2049), .w8196(w8196),
//   .w6147(w6147), .w64(w64), .w6211(w6211), .w24844(w24844)
// );