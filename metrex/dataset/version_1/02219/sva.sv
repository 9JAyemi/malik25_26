// SVA checker for multiplier_block
// Binds to DUT and verifies functional equivalence, X-prop, and provides focused coverage.
module multiplier_block_sva (
  input logic        clk,
  input logic        rst_n
);
  // We are bound into multiplier_block scope, so i_data0/o_data0 are visible here via ports of the DUT.
  // If your tool requires explicit ports, use the alternative checker below.

  // 32-bit reference model using the same 32-bit shift/add/sub semantics as the DUT
  function automatic logic [31:0] calc(input logic [31:0] i);
    logic [31:0] t0, t1, t2, t3;
    t0 = (i << 15) + i;     // w32769
    t1 = t0 - (i << 13);    // w24577
    t2 = t1 + (i << 4);     // w24593
    t3 = t2 - (i << 7);     // w24465
    return t3;
  endfunction

  // Basic sanity: no X/Z on sampled inputs/outputs
  assert property (@(posedge clk) disable iff (!rst_n)
    !$isunknown(i_data0) && !$isunknown(o_data0)
  ) else $error("multiplier_block: X/Z detected on i_data0/o_data0");

  // Functional equivalence to shift/add/sub implementation
  assert property (@(posedge clk) disable iff (!rst_n)
    o_data0 == calc(i_data0)
  ) else $error("multiplier_block: functional mismatch vs calc()");

  // Cross-check vs constant multiplication modulo 2^32
  assert property (@(posedge clk) disable iff (!rst_n)
    o_data0 == ( (i_data0 * 32'd24465) [31:0] )
  ) else $error("multiplier_block: functional mismatch vs *24465 mod 2^32");

  // Focused coverage (hit once each)
  cover property (@(posedge clk) disable iff (!rst_n) i_data0 == 32'h0000_0000);  // zero
  cover property (@(posedge clk) disable iff (!rst_n) i_data0 == 32'hFFFF_FFFF);  // all ones
  cover property (@(posedge clk) disable iff (!rst_n) i_data0 == 32'h0000_0001);  // one
  cover property (@(posedge clk) disable iff (!rst_n) $onehot(i_data0));          // any one-hot
  // Exercise shift boundaries that drive MSB
  cover property (@(posedge clk) disable iff (!rst_n) ((i_data0 << 15)[31]));     // (i<<15) sets MSB
  cover property (@(posedge clk) disable iff (!rst_n) ((i_data0 << 13)[31]));     // (i<<13) sets MSB
  // Input toggle to expose different combinational results
  cover property (@(posedge clk) disable iff (!rst_n) $changed(i_data0));

endmodule

// Alternative form if your tool requires explicit ports instead of implicit access:
module multiplier_block_sva_explicit (
  input  logic        clk,
  input  logic        rst_n,
  input  logic [31:0] i_data0,
  input  logic [31:0] o_data0
);
  function automatic logic [31:0] calc(input logic [31:0] i);
    logic [31:0] t0, t1, t2, t3;
    t0 = (i << 15) + i;
    t1 = t0 - (i << 13);
    t2 = t1 + (i << 4);
    t3 = t2 - (i << 7);
    return t3;
  endfunction

  assert property (@(posedge clk) disable iff (!rst_n)
    !$isunknown(i_data0) && !$isunknown(o_data0)
  );

  assert property (@(posedge clk) disable iff (!rst_n)
    o_data0 == calc(i_data0)
  );

  assert property (@(posedge clk) disable iff (!rst_n)
    o_data0 == ((i_data0 * 32'd24465)[31:0])
  );

  cover property (@(posedge clk) disable iff (!rst_n) i_data0 == 32'h0000_0000);
  cover property (@(posedge clk) disable iff (!rst_n) i_data0 == 32'hFFFF_FFFF);
  cover property (@(posedge clk) disable iff (!rst_n) i_data0 == 32'h0000_0001);
  cover property (@(posedge clk) disable iff (!rst_n) $onehot(i_data0));
  cover property (@(posedge clk) disable iff (!rst_n) ((i_data0 << 15)[31]));
  cover property (@(posedge clk) disable iff (!rst_n) ((i_data0 << 13)[31]));
  cover property (@(posedge clk) disable iff (!rst_n) $changed(i_data0));
endmodule

// Typical bind usage (choose one checker form):
// bind multiplier_block multiplier_block_sva u_sva (.clk(tb_clk), .rst_n(tb_rst_n));
// or
// bind multiplier_block multiplier_block_sva_explicit u_sva ( .clk(tb_clk), .rst_n(tb_rst_n),
//                                                            .i_data0(i_data0), .o_data0(o_data0) );