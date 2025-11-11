// SVA for counter. Bind this module to the DUT instance.

module counter_sva (
  input logic        clk,
  input logic        rst,
  input logic        load,
  input logic [3:0]  init,
  input logic [3:0]  out
);

  default clocking cb @(posedge clk); endclocking

  // Guard for $past
  bit past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  // Single concise functional assertion capturing priority and behavior
  assert property (past_valid |->
      ( $past(rst)                         ? (out == 4'h0) :
        $past(load)                        ? (out == $past(init)) :
        ($past(out) == 4'hF)               ? (out == 4'h0) :
                                             (out == $past(out) + 4'd1) ));

  // No X/Z on output after first tick
  assert property (past_valid |-> !$isunknown(out));

  // Coverage: reset effect
  cover property (past_valid && $past(rst) && out == 4'h0);

  // Coverage: load effect (with rst low)
  cover property (past_valid && $past(load) && !$past(rst) && out == $past(init));

  // Coverage: increment (non-wrap)
  cover property (past_valid && !$past(rst) && !$past(load) && ($past(out) != 4'hF) &&
                  out == $past(out) + 4'd1);

  // Coverage: wrap 15 -> 0
  cover property (past_valid && !$past(rst) && !$past(load) && ($past(out) == 4'hF) &&
                  out == 4'h0);

  // Coverage: simultaneous rst and load -> reset wins
  cover property (past_valid && $past(rst && load) && out == 4'h0);

endmodule

bind counter counter_sva u_counter_sva (.clk(clk), .rst(rst), .load(load), .init(init), .out(out));