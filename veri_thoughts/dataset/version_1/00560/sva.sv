// SVA for counter
module counter_sva (input clk, input rst, input [3:0] count);
  default clocking cb @(posedge clk); endclocking

  bit past_valid, seen_reset;
  initial begin past_valid = 0; seen_reset = 0; end
  always @(posedge clk) begin
    past_valid <= 1'b1;
    if (rst) seen_reset <= 1'b1;
  end

  // Reset behavior
  ap_rst_forces_zero: assert property (past_valid && $past(rst) |-> count == 4'd0);

  // Increment by 1 mod-16 when not in reset
  ap_inc_no_rst: assert property (past_valid && !$past(rst) && !rst |-> count == $past(count + 4'd1));

  // Explicit wrap check (15 -> 0) without reset
  ap_wrap: assert property (past_valid && !$past(rst) && !rst && $past(count)==4'hF |-> count==4'h0);

  // No X/Z on count after a reset has been seen at least once
  ap_no_x_after_reset: assert property (seen_reset |-> !$isunknown(count));

  // Coverage
  cp_reset_assert:  cover property (past_valid && $rose(rst));
  cp_reset_release: cover property (past_valid && $fell(rst));
  cp_wrap_seq:      cover property (disable iff (rst) (count==4'hE ##1 count==4'hF ##1 count==4'h0));
endmodule

bind counter counter_sva sva_i (.*);