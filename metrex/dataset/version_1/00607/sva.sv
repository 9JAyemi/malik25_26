// SVA for RegisterAdd_4
module RegisterAdd_4_sva(
    input logic        CLK,
    input logic        reset,
    input logic [3:0]  in1,
    input logic [3:0]  in2,
    input logic [3:0]  out
);
  default clocking cb @(posedge CLK); endclocking

  // become valid after first clock edge
  logic past_valid;
  always_ff @(posedge CLK) past_valid <= 1'b1;

  // 5-bit past-sum (captures overflow bit)
  let sum5_past = {1'b0,$past(in1)} + {1'b0,$past(in2)};

  // Core functional checks
  // 1) Synchronous reset clears output on next cycle
  assert property (disable iff (!past_valid)
                   reset |=> out == 4'd0);

  // 2) When not in reset last cycle, out equals 4-bit sum of past inputs (mod 16)
  assert property (disable iff (!past_valid)
                   !$past(reset) |-> out == sum5_past[3:0]);

  // Sanity/robustness checks
  // Inputs known when used (last cycle) and output known now
  assert property (disable iff (!past_valid)
                   !$past(reset) |-> !$isunknown($past({in1,in2})));
  assert property (disable iff (!past_valid)
                   !$isunknown(out));
  // Reset itself should be known
  assert property (@cb !$isunknown(reset));

  // Coverage: reset behavior, normal add, overflow wrap, corner cases
  cover property (disable iff (!past_valid)
                  reset ##1 out == 4'd0);

  cover property (disable iff (!past_valid)
                  !$past(reset) && (out == sum5_past[3:0]));

  cover property (disable iff (!past_valid)
                  !$past(reset) && sum5_past[4] && (out == sum5_past[3:0])); // overflow wrap-around

  cover property (disable iff (!past_valid)
                  !$past(reset) && ($past(in1)==4'hF) && ($past(in2)==4'hF) && (out==4'hE)); // 15+15 -> 14

  cover property (disable iff (!past_valid)
                  !$past(reset) && ($past(in1)==4'd0) && ($past(in2)==4'd0) && (out==4'd0)); // 0+0 -> 0
endmodule

// Bind into DUT
bind RegisterAdd_4 RegisterAdd_4_sva sva_i(.CLK(CLK), .reset(reset), .in1(in1), .in2(in2), .out(out));