// Bind these SVA to the DUT
bind altera_std_synchronizer altera_std_synchronizer_sva #(.depth(depth)) u_altera_std_synchronizer_sva (.*);

// SVA checker
module altera_std_synchronizer_sva #(parameter int depth = 2)
(
  input logic clk,
  input logic reset_n,
  input logic din,
  input logic dout,
  input logic [depth-1:0] ff
);
  // Parameter sanity
  initial assert (depth >= 2)
    else $error("altera_std_synchronizer: depth (%0d) must be >= 2", depth);

  default clocking cb @(posedge clk); endclocking

  // Asynchronous reset drives all flops low (checked at each clk edge while in reset)
  assert property (!reset_n |-> ff == {depth{1'b0}});
  assert property (!reset_n |-> (dout == 1'b0));

  // One-cycle shift behavior when not in or coming from reset
  assert property (reset_n && $past(reset_n)
                   |-> ff == { $past(ff[depth-2:0]), $past(din) });

  // End-to-end latency: after depth consecutive reset_n=1 cycles, dout == din delayed by depth
  assert property (reset_n[*depth] |-> (dout == $past(din, depth)));

  // After reset deassertion, dout must remain 0 for depth-1 cycles
  assert property ($rose(reset_n) |-> (dout == 1'b0)[*(depth-1)]);

  // No glitches on dout between clock edges when not in reset
  assert property (@(negedge clk) disable iff (!reset_n) $stable(dout));

  // Coverage: observe reset pulse
  cover property ($fell(reset_n) ##1 $rose(reset_n));

  // Coverage: a rising edge on din propagates to dout after exactly depth cycles (while out of reset)
  cover property (reset_n && $rose(din) ##1 reset_n[*(depth-1)] ##0 $rose(dout));

  // Coverage: a falling edge on din propagates to dout after exactly depth cycles (while out of reset)
  cover property (reset_n && $fell(din) ##1 reset_n[*(depth-1)] ##0 $fell(dout));
endmodule