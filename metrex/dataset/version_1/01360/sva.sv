// SVA for macc_module
module macc_module_sva(
  input logic        clk,
  input logic        reset,
  input logic [31:0] a,
  input logic [31:0] b,
  input logic [31:0] accum,
  input logic [31:0] out
);
  default clocking cb @(posedge clk); endclocking

  // Basic integrity
  ap_out_eq_accum:          assert property (out == accum);
  ap_no_x_after_reset:      assert property (disable iff (reset) (!$isunknown(accum) && !$isunknown(out)));

  // Reset behavior
  ap_reset_clears_next:     assert property (reset |=> (accum == 32'd0 && out == 32'd0));
  ap_reset_holds_zero:      assert property ((reset && $past(reset)) |-> (accum == 32'd0 && out == 32'd0));
  ap_first_update_post_rst: assert property ($fell(reset) |=> (accum == (($past(a)*$past(b)))[31:0]));

  // Functional MAC update (mod 2^32)
  ap_mac_update: assert property (disable iff (reset)
    1'b1 |=> accum == ($past(accum) + ($past(a)*$past(b)))[31:0]);

  // Zero-product should not change accumulator
  ap_zero_product_no_change: assert property (disable iff (reset)
    ($past(a) == 32'd0 || $past(b) == 32'd0) |=> (accum == $past(accum)));

  // Coverage
  cp_reset_seen:     cover property (reset |=> accum == 32'd0);
  cp_nontrivial_mac: cover property (disable iff (reset)
                        ($past(a) != 32'd0 && $past(b) != 32'd0));
  cp_truncation:     cover property (disable iff (reset)
                        (($past(a)*$past(b))[63:32] != 0)); // exercised upper product bits
  cp_wraparound:     cover property (disable iff (reset)
                        ((($past(accum) + ($past(a)*$past(b)))[31:0]) < $past(accum)));
endmodule

// Bind into DUT (gains visibility of internal 'accum')
bind macc_module macc_module_sva u_macc_module_sva (
  .clk   (clk),
  .reset (reset),
  .a     (a),
  .b     (b),
  .accum (accum),
  .out   (out)
);