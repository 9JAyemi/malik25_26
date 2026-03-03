// SVA for up_counter — concise, high-quality checks and coverage
module up_counter_sva (
  input logic       clk,
  input logic       rst,
  input logic [3:0] count
);
  default clocking cb @(posedge clk); endclocking

  // Track availability of $past()
  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  // Basic sanity: no X/Z after the first sampled cycle
  ap_known: assert property (disable iff (!past_valid) !$isunknown({rst,count}));

  // Synchronous reset drives 0 on the same clock edge
  ap_sync_reset: assert property (rst |-> count == 4'd0);

  // Increment by exactly 1 (with 4-bit wrap-around) whenever not in reset
  ap_inc: assert property (disable iff (!past_valid or rst)
                           count == $past(count) + 4'd1);

  // Explicit wrap-around check (redundant with ap_inc, but clear intent)
  ap_wrap: assert property (disable iff (!past_valid)
                            !rst && $past(count)==4'hF |-> count==4'h0);

  // Coverage: see reset then first post-reset increment to 1
  cp_reset_exit: cover property (rst ##1 !rst ##1 count==4'd1);

  // Coverage: observe a short increment run
  cp_run: cover property (disable iff (!past_valid or rst)
                          count==4'd0 ##1 count==4'd1 ##1 count==4'd2 ##1 count==4'd3);

  // Coverage: observe the wrap-around F -> 0
  cp_wrap: cover property (disable iff (!past_valid)
                           !rst && $past(count)==4'hF ##1 count==4'h0);
endmodule

// Bind into the DUT
bind up_counter up_counter_sva u_up_counter_sva (.clk(clk), .rst(rst), .count(count));