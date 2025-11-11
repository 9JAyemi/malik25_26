// SVA for shift_and_add_multiplier
// Bind this to the DUT. Focused, high-quality checks and coverage.

module shift_and_add_multiplier_sva
  (input logic        clk,
   input logic        reset,
   input logic [3:0]  a,
   input logic [3:0]  b,
   input logic [7:0]  product);

  default clocking cb @(posedge clk); endclocking

  // Basic sanity: no X on key signals after reset releases
  ap_no_x: assert property (disable iff (reset) $past(!reset) |-> !$isunknown({a,b,product}));

  // Reset behavior: clears in 1 cycle and holds at 0 while asserted
  ap_rst_clears_next: assert property (reset |=> product == 8'h00);
  ap_rst_holds_zero:  assert property ((reset && $past(reset)) |-> product == 8'h00);

  // Functional correctness (1-cycle latency): product equals a*b from previous cycle
  ap_mul_correct: assert property (disable iff (reset)
                                   $past(!reset) |-> product == ($past(a) * $past(b)));

  // Equivalent partial-sum check (redundant with multiply but pinpoints bitwise composition)
  ap_partial_sum: assert property (disable iff (reset)
                                   $past(!reset) |-> product ==
                                   (($past(b[0]) ? ( {4'h0,$past(a)} << 0) : 8'h00) +
                                    ($past(b[1]) ? ( {4'h0,$past(a)} << 1) : 8'h00) +
                                    ($past(b[2]) ? ( {4'h0,$past(a)} << 2) : 8'h00) +
                                    ($past(b[3]) ? ( {4'h0,$past(a)} << 3) : 8'h00)));

  // Coverage: exercise reset, extremes, and each partial path
  cp_reset:    cover property ($rose(reset) ##1 product == 8'h00);
  cp_zero_in:  cover property (disable iff (reset)
                               $past(!reset) && ($past(a)==0 || $past(b)==0) && product==8'h00);
  cp_max_max:  cover property (disable iff (reset)
                               $past(!reset) && $past(a)==4'hF && $past(b)==4'hF && product==8'd225);

  genvar i;
  generate
    for (i=0;i<4;i++) begin : gen_cov_bit
      cp_single_bit: cover property (disable iff (reset)
                          $past(!reset) &&
                          $past(b) == (4'b0001 << i) &&
                          product == ( {4'h0,$past(a)} << i) );
    end
  endgenerate

endmodule

bind shift_and_add_multiplier shift_and_add_multiplier_sva sva_i
  (.clk(clk), .reset(reset), .a(a), .b(b), .product(product));