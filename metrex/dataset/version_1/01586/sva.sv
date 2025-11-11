// SVA for first_counter
// Bind into DUT: bind first_counter first_counter_sva sva(.clock(clock), .reset(reset), .enable(enable), .counter_out(counter_out));

module first_counter_sva (
  input logic        clock,
  input logic        reset,
  input logic        enable,
  input logic [3:0]  counter_out
);

  // Clocking
  default clocking cb @(posedge clock); endclocking

  // Track that at least one clock has occurred (for safe $past use)
  bit past_valid;
  initial past_valid = 1'b0;
  always @(posedge clock) past_valid <= 1'b1;

  // Basic sanity: no X/Z on controls and output
  a_known_ctrl:  assert property (past_valid |-> !$isunknown({reset, enable}));
  a_known_count: assert property (past_valid |-> !$isunknown(counter_out));

  // Synchronous reset takes effect on the next cycle
  a_sync_reset:  assert property (past_valid && $past(reset) |-> (counter_out == 4'h0));

  // Counting behavior (mod-16)
  // If previously not in reset and enable was 1, increment by 1 (wrap allowed by 4-bit math)
  a_inc_when_en: assert property (past_valid && !$past(reset) && $past(enable)
                                  |-> counter_out == $past(counter_out) + 4'd1);

  // If previously not in reset and enable was 0, hold value
  a_hold_when_dis: assert property (past_valid && !$past(reset) && !$past(enable)
                                    |-> counter_out == $past(counter_out));

  // Any change must be caused by prior enable or prior reset
  a_change_cause: assert property (past_valid && (counter_out != $past(counter_out))
                                   |-> ($past(reset) || $past(enable)));

  // Explicit wrap check: F -> 0 when enabled and not reset
  a_wrap: assert property (past_valid && !$past(reset) && $past(enable) && ($past(counter_out) == 4'hF)
                           |-> (counter_out == 4'h0));

  // Coverage
  c_reset_effect: cover property (past_valid && $past(reset) && (counter_out == 4'h0));
  c_increment:    cover property (past_valid && !$past(reset) && $past(enable)
                                  && counter_out == $past(counter_out) + 4'd1);
  c_hold:         cover property (past_valid && !$past(reset) && !$past(enable)
                                  && counter_out == $past(counter_out));
  c_wrap:         cover property (past_valid && !$past(reset) && $past(enable)
                                  && ($past(counter_out) == 4'hF) && (counter_out == 4'h0));

endmodule

// Example bind (place in a bind file or a package included by your testbench)
// bind first_counter first_counter_sva sva (.*);