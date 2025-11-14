// SVA for counter_module
// Bind this checker to the DUT.
module counter_module_sva (
  input logic        clk,
  input logic        reset,      // sync, active-high
  input logic [5:0]  q,
  input logic [3:0]  out1,
  input logic [3:0]  out2
);
  default clocking cb @ (posedge clk); endclocking

  // 1) Sanity: no X/Z on key signals at clock edges
  assert property (!$isunknown({reset,q,out1,out2}))
    else $error("X/Z detected on reset/q/out1/out2");

  // 2) Reset effect: one cycle after reset high, all outputs are zero
  assert property (reset |=> (q==6'd0 && out1==4'd0 && out2==4'd0))
    else $error("Reset did not clear outputs in 1 cycle");

  // 3) Out1/Out2 count up by 1 each cycle when not crossing reset
  assert property ((!reset && !$past(reset)) |-> (out1 == $past(out1) + 4'd1))
    else $error("out1 failed +1 increment");
  assert property ((!reset && !$past(reset)) |-> (out2 == $past(out2) + 4'd1))
    else $error("out2 failed +1 increment");

  // 4) Alignment between q and registered outputs (accounting for one-cycle lag and truncation)
  //    q[3:0] is current counter1; out1 is previous counter1
  assert property ((!reset && !$past(reset)) |-> (q[3:0] == out1 + 4'd1))
    else $error("q[3:0] not aligned to out1+1");
  //    q[5:4] are the 2 LSBs of current counter2; out2 is previous counter2
  assert property ((!reset && !$past(reset)) |-> (q[5:4] == out2[1:0] + 2'd1))
    else $error("q[5:4] not aligned to out2[1:0]+1");

  // 5) Optional: q low/high fields increment when not crossing reset
  assert property ((!reset && !$past(reset)) |-> (q[3:0] == $past(q[3:0]) + 4'd1))
    else $error("q[3:0] failed +1 increment");
  assert property ((!reset && !$past(reset)) |-> (q[5:4] == $past(q[5:4]) + 2'd1))
    else $error("q[5:4] failed +1 increment");

  // 6) Coverage
  // Reset sequence observed
  cover property (reset ##1 (q==6'd0 && out1==4'd0 && out2==4'd0));
  // Wrap-around coverage on both counters and q slices (no reset in between)
  cover property ((!reset && !$past(reset)) && ($past(out1)==4'hF) && (out1==4'h0));
  cover property ((!reset && !$past(reset)) && ($past(out2)==4'hF) && (out2==4'h0));
  cover property ((!reset && !$past(reset)) && ($past(q[3:0])==4'hF) && (q[3:0]==4'h0));
  cover property ((!reset && !$past(reset)) && ($past(q[5:4])==2'h3) && (q[5:4]==2'h0));
endmodule

// Bind into the DUT
bind counter_module counter_module_sva u_counter_module_sva (
  .clk  (clk),
  .reset(reset),
  .q    (q),
  .out1 (out1),
  .out2 (out2)
);