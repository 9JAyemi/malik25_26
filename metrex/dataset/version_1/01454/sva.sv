// SVA for DelayTest
module DelayTest_sva (
  input logic        clk,
  input logic        reset,
  input logic [3:0]  data,
  input logic [3:0]  out1,
  input logic [3:0]  out2,
  input logic [3:0]  out3
);
  default clocking @(posedge clk); endclocking

  // Synchronous reset clears by next sample
  assert property (reset |-> (out1=='0 && out2=='0 && out3=='0))
    else $error("DelayTest: outputs not cleared by reset");

  // No Xs when active
  assert property (disable iff (reset) !$isunknown({out1,out2,out3}))
    else $error("DelayTest: X/Z on outputs while not in reset");

  // Stage behavior (1-cycle links), gated across reset boundary
  assert property (disable iff (reset || $past(reset,1,1'b1))
                   out1 == $past(data))
    else $error("DelayTest: out1 != $past(data)");

  assert property (disable iff (reset || $past(reset,1,1'b1))
                   out2 == $past(out1))
    else $error("DelayTest: out2 != $past(out1)");

  assert property (disable iff (reset || $past(reset,1,1'b1))
                   out3 == $past(out2))
    else $error("DelayTest: out3 != $past(out2)");

  // End-to-end check: 3-cycle latency from data to out3
  assert property (disable iff (reset
                                || $past(reset,1,1'b1)
                                || $past(reset,2,1'b1)
                                || $past(reset,3,1'b1))
                   out3 == $past(data,3))
    else $error("DelayTest: out3 != $past(data,3)");

  // Coverage: see full 3-stage propagation with no intervening resets
  cover property (!$past(reset,3,1'b1) && !reset
                  && out1 == $past(data)
                  && out2 == $past(data,2)
                  && out3 == $past(data,3));

  // Coverage: observe reset activity
  cover property ($rose(reset));
  cover property ($fell(reset));
endmodule

// Bind into DUT
bind DelayTest DelayTest_sva sva (
  .clk   (clk),
  .reset (reset),
  .data  (data),
  .out1  (out1),
  .out2  (out2),
  .out3  (out3)
);