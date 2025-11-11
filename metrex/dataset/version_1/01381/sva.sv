// SVA for counter: checks sync reset, up/down behavior, wrap, X-safety, and provides concise coverage.
// Bind this module to the DUT.
module counter_sva (
  input logic        clk,
  input logic        reset,
  input logic        up_down,
  input logic [3:0]  out
);
  default clocking cb @ (posedge clk); endclocking

  // Track past-valid to safely use $past()
  bit past_valid;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // X-safety
  assert property (past_valid |-> !$isunknown(out));
  assert property (past_valid && !reset |-> !$isunknown(up_down));

  // Synchronous reset: sets and holds zero
  assert property (reset |=> out == 4'd0);
  assert property (past_valid && reset && $past(reset) |-> out == 4'd0);

  // Functional behavior: on every non-reset cycle, out changes by +/-1 modulo-16
  assert property (past_valid && !reset |-> out == ($past(out) + (up_down ? 4'd1 : 4'hF)));
  assert property (past_valid && !reset |-> out != $past(out));

  // Explicit wrap checks (redundant with main behavior but clearer for debug)
  assert property (past_valid && !reset && $past(out) == 4'hF && up_down  |-> out == 4'h0);
  assert property (past_valid && !reset && $past(out) == 4'h0 && !up_down |-> out == 4'hF);

  // Coverage
  cover property (past_valid && reset ##1 out == 4'd0);                 // reset drives zero
  cover property (past_valid && !reset && up_down  [*16]);              // 16 ups in a row
  cover property (past_valid && !reset && !up_down [*16]);              // 16 downs in a row
  cover property (past_valid && !reset && $past(out)==4'hF && up_down  && out==4'h0); // up wrap
  cover property (past_valid && !reset && $past(out)==4'h0 && !up_down && out==4'hF); // down wrap
  cover property (past_valid && !reset && up_down ##1 !up_down);        // direction change up->down
  cover property (past_valid && !reset && !up_down ##1 up_down);        // direction change down->up
endmodule

bind counter counter_sva u_counter_sva(.clk(clk), .reset(reset), .up_down(up_down), .out(out));