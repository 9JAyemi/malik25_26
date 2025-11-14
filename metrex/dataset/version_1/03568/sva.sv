// SVA for top_module
// Bind into the DUT to access internal 'counter'
module top_module_sva;
  // These names resolve in the bound scope (top_module)
  // clk, reset, q, count_ones, counter

  default clocking cb @(posedge clk); endclocking

  // Reset behavior: while reset is high, all outputs/regs are zero
  assert property (@cb reset |-> (counter==4'd0 && q==4'd0 && count_ones==3'd0))
    else $error("Reset did not drive outputs/regs to zero");

  // q mirrors counter (combinationally sampled on clock)
  assert property (@cb q == counter)
    else $error("q != counter");

  // Counter increments by 1 each cycle when not in or just exiting reset
  assert property (@cb (!reset && !$past(reset)) |-> counter == $past(counter) + 4'd1)
    else $error("Counter did not increment by 1");

  // Count-ones correctness (popcount) and range
  assert property (@cb disable iff (reset) count_ones == $countones(counter)[2:0])
    else $error("count_ones != popcount(counter)");
  assert property (@cb disable iff (reset) count_ones <= 3'd4)
    else $error("count_ones out of range");

  // Stronger equivalences for extreme cases
  assert property (@cb disable iff (reset) (count_ones==3'd0) <-> (counter==4'h0))
    else $error("count_ones==0 mismatch");
  assert property (@cb disable iff (reset) (count_ones==3'd4) <-> (counter==4'hF))
    else $error("count_ones==4 mismatch");

  // No X/Z on key state/outputs after reset
  assert property (@cb disable iff (reset) !$isunknown({counter,q,count_ones}))
    else $error("X/Z detected on counter/q/count_ones");

  // Coverage
  cover property (@cb $rose(reset));
  cover property (@cb $fell(reset));
  cover property (@cb disable iff (reset) $past(counter)==4'hF && counter==4'h0); // wrap-around
  cover property (@cb disable iff (reset) count_ones==3'd0);
  cover property (@cb disable iff (reset) count_ones==3'd1);
  cover property (@cb disable iff (reset) count_ones==3'd2);
  cover property (@cb disable iff (reset) count_ones==3'd3);
  cover property (@cb disable iff (reset) count_ones==3'd4);
endmodule

bind top_module top_module_sva tmsva();