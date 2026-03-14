module xor_module_sva (
  input logic clk,
  input logic rst,
  input logic A,
  input logic B,
  input logic Y
);

  ///// Reset behavior /////
  // After any cycle with rst=1, Y must be 0 on the next clock.
  reset_clears_Y_next: assert property (
    @(posedge clk) rst |=> (Y == 1'b0)
  );

  // If the previous cycle was in reset, Y must be 0 now.
  y_zero_if_prev_reset: assert property (
    @(posedge clk) $past(rst) |-> (Y == 1'b0)
  );

  ///// Functional behavior /////
  // When the previous cycle was not in reset, Y equals A^B from the previous cycle.
  y_matches_prev_xor_no_reset: assert property (
    @(posedge clk) disable iff (rst) (!$past(rst)) |-> (Y == ($past(A) ^ $past(B)))
  );

  // If previous inputs differed (and prev cycle not in reset), Y is 1 now.
  y_is_one_when_prev_inputs_differ: assert property (
    @(posedge clk) disable iff (rst) (!$past(rst) && ($past(A) ^ $past(B))) |-> (Y == 1'b1)
  );

  // If previous inputs were equal (and prev cycle not in reset), Y is 0 now.
  y_is_zero_when_prev_inputs_equal: assert property (
    @(posedge clk) disable iff (rst) (!$past(rst) && ($past(A) == $past(B))) |-> (Y == 1'b0)
  );

  // If XOR did not change across two non-reset cycles, Y holds its value next cycle.
  y_holds_if_xor_unchanged: assert property (
    @(posedge clk) disable iff (rst) (!$past(rst) && !rst && (($past(A) ^ $past(B)) == (A ^ B))) |=> (Y == $past(Y))
  );

  // If XOR toggled between two non-reset cycles, Y toggles on the next cycle.
  y_toggles_if_xor_toggled: assert property (
    @(posedge clk) disable iff (rst) (!$past(rst) && !rst && (($past(A) ^ $past(B)) != (A ^ B))) |=> (Y != $past(Y))
  );

  // On the first non-reset cycle after reset deasserts, Y remains 0.
  y_zero_on_reset_release: assert property (
    @(posedge clk) ($past(rst) && !rst) |-> (Y == 1'b0)
  );

endmodule