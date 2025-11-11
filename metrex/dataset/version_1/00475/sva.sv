// SVA checker for up_down_counter
module up_down_counter_sva #(parameter int WIDTH = 4)(
  input logic              clk,
  input logic              rst,
  input logic              up_down,
  input logic [WIDTH-1:0]  count
);

  default clocking cb @(posedge clk); endclocking

  // Track first valid cycle for $past()
  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  // Basic sanity: controls known each cycle; count known after first cycle
  ap_ctrl_known:  assert property ( !$isunknown({rst, up_down}) );
  ap_count_known: assert property ( past_valid |-> !$isunknown(count) );

  // Reset behavior: when rst was 1 last cycle, count must be zero now
  ap_reset_forces_zero: assert property ( past_valid && $past(rst) |-> count == '0 );

  // Counting behavior (synchronous; reset in current cycle takes precedence)
  ap_inc: assert property (
    past_valid && !$past(rst) && !rst && $past(up_down) |-> count == $past(count) + 1
  );

  ap_dec: assert property (
    past_valid && !$past(rst) && !rst && !$past(up_down) |-> count == $past(count) - 1
  );

  // Optional: ensure count always changes when not in reset
  ap_progress: assert property (
    past_valid && !$past(rst) && !rst |-> count != $past(count)
  );

  // Coverage
  cv_reset_seen:      cover property ( rst );
  cv_inc_seen:        cover property ( past_valid && !$past(rst) && !rst && $past(up_down) );
  cv_dec_seen:        cover property ( past_valid && !$past(rst) && !rst && !$past(up_down) );
  cv_wrap_up:         cover property ( past_valid && !$past(rst) && !rst && $past(up_down)
                                       && $past(count) == {WIDTH{1'b1}} && count == '0 );
  cv_wrap_down:       cover property ( past_valid && !$past(rst) && !rst && !$past(up_down)
                                       && $past(count) == '0 && count == {WIDTH{1'b1}} );

endmodule

// Bind SVA to DUT
bind up_down_counter up_down_counter_sva #(.WIDTH(4))
  up_down_counter_sva_i (.clk(clk), .rst(rst), .up_down(up_down), .count(count));