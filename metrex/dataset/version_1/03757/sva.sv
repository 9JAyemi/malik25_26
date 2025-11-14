// SVA for module filter. Bind these to the DUT.
// Focused, concise checks for reset, timing, state updates, and functional correctness.

module filter_sva (
  input  logic        clk,
  input  logic        resetn,
  input  logic        din_valid,
  input  logic [7:0]  din00, din01, din02,
  input  logic [7:0]  din10, din11, din12,
  input  logic [7:0]  din20, din21, din22,
  input  logic [7:0]  dout,
  input  logic        dout_valid,
  input  logic [7:0]  sum,          // internal
  input  logic [3:0]  count         // internal
);

  default clocking cb @(posedge clk); endclocking

  // Helper to compute full 12-bit sum of 9 inputs
  function automatic [11:0] sum9(
    input [7:0] a0,a1,a2,a3,a4,a5,a6,a7,a8
  );
    sum9 = a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8;
  endfunction

  // Reset drives all state low while asserted (async reset sampled at clk)
  ap_reset_clears: assert property (!resetn |-> (dout_valid==0 && dout==0 && sum==0 && count==0));

  // No X on key outputs/regs out of reset
  ap_no_x: assert property (disable iff (!resetn) !$isunknown({dout_valid,dout,sum,count}));

  // Handshake/timing: one-cycle latency, no spurious valid
  ap_dv_timing:       assert property (disable iff (!resetn) $past(din_valid) |-> dout_valid);
  ap_no_spurious_dv:  assert property (disable iff (!resetn) !$past(din_valid) |-> !dout_valid);

  // State updates driven by prior-cycle din_valid
  ap_count_set: assert property (disable iff (!resetn) $past(din_valid)  |-> count==4'd9);
  ap_count_clr: assert property (disable iff (!resetn) !$past(din_valid) |-> count==4'd0);
  ap_sum_update: assert property (disable iff (!resetn)
                      $past(din_valid) |-> sum == sum9($past(din00),$past(din01),$past(din02),
                                                       $past(din10),$past(din11),$past(din12),
                                                       $past(din20),$past(din21),$past(din22))[7:0]);

  // Idle drives zeros next cycle
  ap_idle_zero: assert property (disable iff (!resetn) !$past(din_valid) |-> (sum==0 && count==0 && dout==0));

  // Count legal values only
  ap_count_legal: assert property (disable iff (!resetn) count inside {4'd0,4'd9});

  // Functional correctness (intended spec): dout is average of 9 inputs with 1-cycle latency
  ap_avg_correct: assert property (disable iff (!resetn)
                      $past(din_valid) |-> dout == (sum9($past(din00),$past(din01),$past(din02),
                                                         $past(din10),$past(din11),$past(din12),
                                                         $past(din20),$past(din21),$past(din22)) / 9));

  // Coverage
  cp_one_txn:      cover property (disable iff (!resetn) $past(din_valid) && dout_valid);
  cp_all_zero:     cover property (disable iff (!resetn)
                        $past(din_valid) && (sum9($past(din00),$past(din01),$past(din02),
                                                   $past(din10),$past(din11),$past(din12),
                                                   $past(din20),$past(din21),$past(din22))==12'd0)
                        && dout==8'd0 && dout_valid);
  cp_all_max:      cover property (disable iff (!resetn)
                        $past(din_valid) && (sum9($past(din00),$past(din01),$past(din02),
                                                   $past(din10),$past(din11),$past(din12),
                                                   $past(din20),$past(din21),$past(din22))==12'd2295)
                        && dout==8'd255 && dout_valid);
  cp_overflow_sum: cover property (disable iff (!resetn)
                        $past(din_valid) &&
                        (sum9($past(din00),$past(din01),$past(din02),
                              $past(din10),$past(din11),$past(din12),
                              $past(din20),$past(din21),$past(din22)) > 12'h0FF));
  cp_back2back:    cover property (disable iff (!resetn) din_valid[*2]);

endmodule

// Bind to DUT and connect internals sum/count
bind filter filter_sva u_filter_sva (
  .clk(clk),
  .resetn(resetn),
  .din_valid(din_valid),
  .din00(din00), .din01(din01), .din02(din02),
  .din10(din10), .din11(din11), .din12(din12),
  .din20(din20), .din21(din21), .din22(din22),
  .dout(dout),
  .dout_valid(dout_valid),
  .sum(sum),
  .count(count)
);