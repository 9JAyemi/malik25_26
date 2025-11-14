// SVA for my_module
// Bind this to the DUT to check key behaviors concisely with good coverage.

module my_module_sva (
  input logic        clk,
  input logic        reset,
  input logic [3:0]  output1,
  input logic [3:0]  output2,
  input integer      count
);
  // Start checking after a reset has been observed
  bit rst_seen;
  always_ff @(posedge clk or posedge reset) if (reset) rst_seen <= 1'b1;

  // 1) Reset behavior: hold clear
  assert property (@(posedge clk) reset |-> (count==0 && output1==4'h0 && output2==4'hF))
    else $error("Reset did not clear state/outputs to 0/F");

  // 2) Count increments by 1 each cycle when not in reset
  assert property (@(posedge clk) disable iff (reset || !rst_seen)
                   count == $past(count) + 1)
    else $error("Count failed to increment by 1");

  // 3) Outputs reflect count[3:0] and its complement
  assert property (@(posedge clk) disable iff (!rst_seen)
                   (output1 == count[3:0]) && (output2 == ~count[3:0]))
    else $error("Outputs not consistent with count[3:0]");

  // 4) Outputs are complementary (redundant but strong)
  assert property (@(posedge clk) output2 == ~output1)
    else $error("output2 is not bitwise NOT of output1");

  // 5) No X/Z on outputs after reset has been seen
  assert property (@(posedge clk) disable iff (!rst_seen)
                   !$isunknown({output1, output2}))
    else $error("Unknown (X/Z) detected on outputs");

  // 6) No mid-cycle glitches on outputs (only change on posedge clk or during reset)
  assert property (@(negedge clk) disable iff (reset || !rst_seen)
                   $stable(output1) && $stable(output2))
    else $error("Mid-cycle glitch on outputs");

  // 7) Mod-16 step on output1 (derived behavior)
  assert property (@(posedge clk) disable iff (reset || !rst_seen)
                   output1 == ($past(output1)+1))
    else $error("output1 did not step mod-16");

  // Coverage
  // a) See a reset pulse (assert then deassert)
  cover property (@(posedge clk) $rose(reset) ##[1:$] $fell(reset));

  // b) Observe a few consecutive counts after reset release: 0->1->2->3
  cover property (@(posedge clk) disable iff (reset || !rst_seen)
                  output1==4'h0 ##1 output1==4'h1 ##1 output1==4'h2 ##1 output1==4'h3);

  // c) Observe wrap-around F->0
  cover property (@(posedge clk) disable iff (reset || !rst_seen)
                  output1==4'hF ##1 output1==4'h0);
endmodule

// Bind into the DUT; connects to internal 'count' for stronger checking.
bind my_module my_module_sva u_my_module_sva (
  .clk     (clk),
  .reset   (reset),
  .output1 (output1),
  .output2 (output2),
  .count   (count)
);