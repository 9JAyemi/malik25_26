// SVA checker for glitch_filter
// Binds to DUT; focuses on timer behavior, history/glitch detection, and output update.

module glitch_filter_sva #(parameter int n=10, t=5, v=0)
(
  input logic         clk,
  input logic         in,
  input logic         out,
  input logic [n-1:0] timer,
  input logic         glitch_detected,
  input logic  [1:0]  input_history,
  input logic         input_above_threshold
);

  default clocking cb @(posedge clk); endclocking

  bit started;
  initial started = 0;
  always_ff @(posedge clk) started <= 1'b1;

  // Combinational definition check
  assert property (input_above_threshold == (in > t));

  // Timer progression and wrap
  assert property (disable iff (!started) $past(timer)==n-1 |-> timer==0);
  assert property (disable iff (!started) $past(timer)!=n-1 |-> timer==$past(timer)+1);

  // input_history update/hold
  assert property (disable iff (!started)
                   $past(timer)!=n-1 |-> input_history == {$past(input_history[0]), $past(input_above_threshold)});
  assert property (disable iff (!started)
                   $past(timer)==n-1 |-> input_history == $past(input_history));

  // glitch_detected behavior
  assert property (disable iff (!started)
                   $past(timer)==n-1 |-> glitch_detected==0);
  assert property (disable iff (!started)
                   $past(timer)!=n-1 && $past(input_history)==2'b10 |-> glitch_detected==1);
  assert property (disable iff (!started)
                   $past(timer)!=n-1 && $past(input_history)!=2'b10 |-> glitch_detected==$past(glitch_detected));

  // out update on wrap and hold otherwise
  assert property (disable iff (!started)
                   $past(timer)==n-1 |-> out == ($past(glitch_detected) ? (v!=0) : $past(in)));
  assert property (disable iff (!started)
                   $past(timer)!=n-1 |-> out==$past(out));

  // Basic X-check after first cycle
  assert property (disable iff (!started) !$isunknown({out, timer, glitch_detected, input_history}));

  // Coverage
  cover property (disable iff (!started)
                  $past(timer)==n-1 && !$past(glitch_detected) ##1 out==$past(in));
  cover property (disable iff (!started)
                  $past(timer)!=n-1 && $past(input_history)==2'b10 ##1 glitch_detected);
  cover property (disable iff (!started)
                  $past(timer)==n-1 && $past(glitch_detected) ##1 out==(v!=0));
  cover property (disable iff (!started)
                  input_above_threshold ##1 !input_above_threshold); // 1->0 seen
  cover property (disable iff (!started)
                  !input_above_threshold ##1 input_above_threshold); // 0->1 seen

endmodule

bind glitch_filter glitch_filter_sva #(.n(n), .t(t), .v(v))
  glitch_filter_sva_i (.*);