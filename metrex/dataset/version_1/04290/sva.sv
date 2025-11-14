// SVA for multiplier_block: o_data0 must equal i_data0 * 11405 (mod 2^32)
// Bind this checker into multiplier_block and drive clk/rst_n from your env.

module multiplier_block_sva (input logic clk, input logic rst_n);
  // Checker is bound inside multiplier_block scope; it can see internal nets.
  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n)

  sequence in_known; !$isunknown(i_data0); endsequence

  // Golden functional check (mod-2^32 multiply by constant 11405)
  assert property (in_known |-> o_data0 == (i_data0 * 32'd11405)[31:0])
    else $fatal(1, "multiplier_block: o_data0 != i_data0*11405 (mod 2^32)");

  // Structural invariants on key partials (concise but meaningful)
  assert property (in_known |-> w4096 == (i_data0 << 12));
  assert property (in_known |-> w256  == (i_data0 << 8));
  assert property (in_known |-> w16   == (i_data0 << 4));
  assert property (in_known |-> w128  == (i_data0 << 7));

  assert property (in_known |-> w4095  == (w4096 - w1));
  assert property (in_known |-> w3839  == (w4095 - w256));
  assert property (in_known |-> w15356 == (w3839 << 2));
  assert property (in_known |-> w11517 == (w15356 - w3839));
  assert property (in_known |-> w11533 == (w11517 + w16));
  assert property (in_known |-> w11405 == (w11533 - w128));
  assert property (in_known |-> w1 == i_data0);
  assert property (in_known |-> o_data0 == w11405);

  // X-propagation sanity: known input implies all outputs/partials known
  assert property (in_known |-> !$isunknown({w4096,w256,w16,w128,w4095,w3839,w15356,w11517,w11533,w11405,o_data0}));

  // Concise but targeted coverage
  cover property (i_data0==32'd0         && o_data0==32'd0);
  cover property (i_data0==32'd1         && o_data0==32'd11405);
  cover property (i_data0==32'hFFFF_FFFF && o_data0==((32'hFFFF_FFFF*32'd11405)[31:0]));
  cover property (i_data0 inside {32'h0000_0001,32'h0000_0100,32'h0001_0000,32'h8000_0000});
  cover property (((i_data0 * 32'd11405) >> 32) != 0); // overflow occurs
endmodule

// Example bind (edit clk/rst as appropriate):
// bind multiplier_block multiplier_block_sva u_multiplier_block_sva(.clk(tb.clk), .rst_n(tb.rst_n));