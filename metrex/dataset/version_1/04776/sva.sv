// SVA for dff: concise checks and coverage
module dff_sva(input logic data, q, clk, reset);

  // Reset dominates: if reset is high at a clock edge, q must be 0
  assert property (@(posedge clk) reset |-> (q == 1'b0));

  // Registered behavior: q equals previous-cycle data when not in reset
  assert property (@(posedge clk) disable iff (reset)
                   q == $past(data, 1, reset));

  // No spurious toggles: q must not change on negedge clk when not in reset
  assert property (@(negedge clk) disable iff (reset) $stable(q));

  // Known-value checks at sampling edges
  assert property (@(posedge clk) !$isunknown(q));
  assert property (@(posedge clk) !reset |-> !$isunknown(data));
  assert property (@(posedge clk) !$isunknown(reset));

  // Coverage: reset activity
  cover property (@(posedge reset) 1);
  cover property (@(negedge reset) 1);

  // Coverage: capture both 0 and 1 through the flop
  cover property (@(posedge clk) disable iff (reset) (data == 1'b0) ##1 (q == 1'b0));
  cover property (@(posedge clk) disable iff (reset) (data == 1'b1) ##1 (q == 1'b1));

  // Coverage: observe q toggling across cycles while not in reset
  cover property (@(posedge clk) disable iff (reset) $changed(q));

endmodule

// Bind to DUT
bind dff dff_sva u_dff_sva(.data(data), .q(q), .clk(clk), .reset(reset));