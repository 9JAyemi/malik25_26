// SVA for top_module (bind this file to the DUT)
// Focus: functional correctness, X-propagation, counter behavior, and key coverage.

module top_module_sva;

  // past_valid to guard $past usage
  logic past_valid;
  always @(posedge clk) past_valid <= 1'b1;

  // Basic X checks (after design starts running)
  ap_no_x_core: assert property (@(posedge clk) !$isunknown({mult_out, count_out, result}));

  // Multiplier correctness as seen at top (and connectivity)
  ap_mult_correct: assert property (@(posedge clk)
    disable iff ($isunknown({A,B}))
    mult_out == (A * B)
  );

  // Top-level combinational add correctness (zero-extend count_out)
  ap_top_add_correct: assert property (@(posedge clk)
    disable iff ($isunknown({A,B,count_out}))
    result == (A * B) + {4'h0, count_out}
  );

  // Result stability when inputs to comb path are stable
  ap_result_stable: assert property (@(posedge clk)
    past_valid && $stable({A,B,count_out}) |-> $stable(result)
  );

  // Counter behavior
  // Reset action (next cycle is 0)
  ap_cnt_reset_next: assert property (@(posedge clk) reset |=> count_out == 4'd0);

  // Hold at 0 while reset stays asserted
  ap_cnt_reset_hold: assert property (@(posedge clk)
    disable iff (!past_valid)
    reset && $past(reset) |-> count_out == 4'd0
  );

  // Increment when enabled (mod-16)
  ap_cnt_inc: assert property (@(posedge clk)
    disable iff (!past_valid)
    (!reset && enable) |=> count_out == $past(count_out) + 4'd1
  );

  // Hold when not enabled
  ap_cnt_hold: assert property (@(posedge clk)
    disable iff (!past_valid)
    (!reset && !enable) |=> count_out == $past(count_out)
  );

  // Count can only change due to reset or when enable was asserted
  ap_cnt_changes_only_on_en_or_reset: assert property (@(posedge clk)
    disable iff (!past_valid)
    (count_out != $past(count_out)) |-> ($past(reset) || (!reset && $past(enable)))
  );

  // Key coverage
  // Reset pulse and release
  c_reset_release: cover property (@(posedge clk) reset ##1 !reset);

  // Wrap-around (15 -> 0) when enabled
  c_wrap: cover property (@(posedge clk)
    past_valid && !reset && enable && $past(count_out)==4'hF ##1 count_out==4'h0
  );

  // Zero product
  c_zero_prod: cover property (@(posedge clk)
    (A==4'd0 || B==4'd0) && mult_out==8'd0
  );

  // Max product (15*15) and max sum with count=15
  c_max_prod:  cover property (@(posedge clk) A==4'd15 && B==4'd15 && mult_out==8'd225);
  c_max_sum:   cover property (@(posedge clk) A==4'd15 && B==4'd15 && count_out==4'd15 && result==8'd240);

endmodule

bind top_module top_module_sva top_module_sva_i();