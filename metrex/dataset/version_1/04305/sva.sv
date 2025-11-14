// SVA for up_counter_4bit_sync_reset
module up_counter_4bit_sync_reset_sva (
  input logic        clk,
  input logic        rst,
  input logic [3:0]  count
);

  default clocking cb @ (posedge clk); endclocking

  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  // No X/Z on key signals after first sampled cycle
  a_no_x: assert property (past_valid |-> !$isunknown({rst, count}));

  // Single-step next-state check (covers reset, post-deassert, increment, and wrap)
  a_next_state: assert property (
    past_valid |-> count ==
      (rst ? 4'd0 :
            ($past(rst) ? 4'd1 : ($past(count) + 4'd1)))
  );

  // Explicit wrap-around check (redundant, but makes intent clear)
  a_wrap: assert property (past_valid && !rst && $past(!rst) && $past(count)==4'hF |-> count==4'h0);

  // Coverage
  c_reset_seen:   cover property (past_valid && rst);
  c_deassert:     cover property (past_valid && $fell(rst));
  c_first_inc:    cover property (past_valid && $past(rst) && !rst && count==4'd1);
  c_wrap_event:   cover property (past_valid && !rst && $past(!rst) && $past(count)==4'hF && count==4'h0);

endmodule

bind up_counter_4bit_sync_reset up_counter_4bit_sync_reset_sva u_sva (.*);