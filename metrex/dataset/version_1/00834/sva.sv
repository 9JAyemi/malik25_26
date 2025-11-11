// SVA for ff_sub: functional, control, and coverage checks (concise, quality-focused)
module ff_sub_sva #(parameter W=256) (
  input  logic                 clk,
  input  logic                 reset,
  input  logic [W-1:0]         rx_a,
  input  logic [W-1:0]         rx_b,
  input  logic [W-1:0]         rx_p,
  input  logic                 tx_done,
  input  logic [W-1:0]         tx_a,
  input  logic                 carry
);
  default clocking cb @(posedge clk); endclocking

  // Helper inline expressions (force W+1 width arithmetic)
  `define DIFF_PAST   (({1'b0,$past(rx_a)} - {1'b0,$past(rx_b)}))
  `define DIFF_CURR   (({1'b0,$past(rx_a)} - {1'b0,$past(rx_b)})) // alias for brevity

  // 1) Synchronous reset computes raw subtraction and clears done on the next cycle
  ap_reset_load: assert property (reset |=> {carry, tx_a} == `DIFF_PAST && !tx_done);

  // 2) Completion one cycle after reset deasserts (if reset falls)
  ap_done_on_fall: assert property ($fell(reset) |-> tx_done);

  // 3) Output stability once done until next reset
  ap_hold_after_done: assert property (tx_done && !reset |=> tx_done && $stable(tx_a) && $stable(carry));

  // 4) If not in reset and not done, must complete in one cycle
  ap_progress: assert property (!reset && !tx_done |=> tx_done);

  // 5) Carry/borrow correctness captured at reset cycle
  ap_carry_correct: assert property ($fell(reset) |-> carry == `DIFF_PAST[W]);

  // 6) Final result correctness at completion:
  //    tx_a == (a-b) when no borrow, else (a-b)+p (mod 2^W).
  ap_result_correct: assert property ($fell(reset) |-> 
    tx_a == ( `DIFF_PAST[W-1:0] + ((~`DIFF_PAST[W]) ? $past(rx_p) : '0) )
  );

  // 7) No spurious updates during reset (recompute only the raw subtract)
  ap_no_add_during_reset: assert property (reset |=> tx_a == `DIFF_PAST[W-1:0]);

  // 8) Optional X-checks on inputs during compute (when reset=1, operands should be known)
  ap_no_x_on_inputs_during_reset: assert property (reset |-> !$isunknown({rx_a,rx_b,rx_p}));

  // Coverage: exercise both no-borrow and borrow paths and observe completion
  cp_no_borrow: cover property ($fell(reset) && ($past(rx_a) >= $past(rx_b)) ##1 tx_done &&
                                (tx_a == `DIFF_CURR[W-1:0]));
  cp_borrow:    cover property ($fell(reset) && ($past(rx_a) <  $past(rx_b)) ##1 tx_done &&
                                (tx_a == (`DIFF_CURR[W-1:0] + $past(rx_p))));
  cp_done_hold: cover property ($rose(tx_done) ##1 tx_done [*5]);

  `undef DIFF_PAST
  `undef DIFF_CURR
endmodule

// Bind into the DUT (carry is internal to ff_sub; bind can connect it)
bind ff_sub ff_sub_sva #(.W(256)) ff_sub_sva_i (
  .clk(clk),
  .reset(reset),
  .rx_a(rx_a),
  .rx_b(rx_b),
  .rx_p(rx_p),
  .tx_done(tx_done),
  .tx_a(tx_a),
  .carry(carry)
);