// SVA for glitch_filter
// Bind this file to the DUT

module glitch_filter_sva #(parameter int N = 4)
(
  input logic clk,
  input logic in,
  input logic out
);

default clocking cb @(posedge clk); endclocking

bit past_valid;
initial past_valid = 0;
always @(posedge clk) past_valid <= 1'b1;

// 2-state sanity
assert property (past_valid |-> !$isunknown({in,out}));

// Output may change only to the current input value
assert property (past_valid && $changed(out) |-> out == in);

// Output may change only after N consecutive identical input samples
genvar k;
generate
  for (k = 1; k < N; k++) begin : G_N_CONSEC_REQ
    assert property (past_valid && $changed(out) |-> in === $past(in, k));
  end
endgenerate

// Rising transition acceptance: after a 0->1 on input and N-1 further 1's, output must rise
assert property (past_valid && $rose(in) && !$past(out) |-> in[* (N-1)] ##1 $rose(out));

// Falling transition acceptance: after a 1->0 on input and N-1 further 0's, output must fall
assert property (past_valid && $fell(in) && $past(out) |-> !in[* (N-1)] ##1 $fell(out));

// No early update before N cycles of stability
assert property (past_valid && $rose(in) && !$past(out) |-> !$rose(out) [* (N-1)]);
assert property (past_valid && $fell(in) &&  $past(out) |-> !$fell(out) [* (N-1)]);

// Coverage: accept both polarities and reject short glitches
cover property (past_valid && $rose(in) ##1 in[* (N-1)] ##1 $rose(out));
cover property (past_valid && $fell(in) ##1 !in[* (N-1)] ##1 $fell(out));

// 1-cycle glitches do not toggle output
cover property (past_valid && $rose(in) ##1 $fell(in) ##0 $stable(out)[*2]);
cover property (past_valid && $fell(in) ##1 $rose(in) ##0 $stable(out)[*2]);

endmodule

bind glitch_filter glitch_filter_sva #(.N(n)) u_glitch_filter_sva (.clk(clk), .in(in), .out(out));