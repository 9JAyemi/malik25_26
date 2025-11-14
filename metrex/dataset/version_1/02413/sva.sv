// SVA checker for twos_complement_adder
// Focus: functional correctness (C and overflow), internal state (sum/carry), reset, and key coverage.
module twos_complement_adder_sva #(parameter int W=4)
(
  input  logic                     clk,
  input  logic                     reset,
  input  logic signed [W-1:0]      A,
  input  logic signed [W-1:0]      B,
  input  logic signed [W:0]        C,
  input  logic                     overflow,
  // internal regs (bound hierarchically)
  input  logic signed [W-1:0]      sum,
  input  logic                     carry
);

  default clocking cb @ (posedge clk); endclocking
  default disable iff (reset);

  function automatic logic signed [W:0] gold(input logic signed [W-1:0] a,
                                             input logic signed [W-1:0] b,
                                             input logic                cin);
    gold = $signed(a) + $signed(b) + cin;
  endfunction

  // Reset outputs clear
  assert property (@cb reset |-> (C == '0 && overflow == 1'b0));

  // Functional result: 5-bit signed sum equals sign-extended A+B+carry_in (carry_in is previous carry)
  assert property (@cb $past(!reset) |-> C == gold(A, B, $past(carry)));

  // Overflow is MSB mismatch of the 5-bit golden sum
  assert property (@cb $past(!reset) |-> overflow == (gold(A,B,$past(carry))[W] ^ gold(A,B,$past(carry))[W-1]));

  // Internal pipeline state matches golden decomposition
  assert property (@cb $past(!reset) |-> sum   == gold(A,B,$past(carry))[W-1:0]);
  assert property (@cb $past(!reset) |-> carry == gold(A,B,$past(carry))[W]);

  // No X/Z on outputs when not in reset
  assert property (@cb !$isunknown({C,overflow}));

  // Coverage: hit both overflow polarities (golden), both carry_in values, and a zero result
  cover property (@cb $past(!reset) && (gold(A,B,$past(carry))[W] ^ gold(A,B,$past(carry))[W-1]) && (A[W-1]==1'b0) && (B[W-1]==1'b0)); // +overflow
  cover property (@cb $past(!reset) && (gold(A,B,$past(carry))[W] ^ gold(A,B,$past(carry))[W-1]) && (A[W-1]==1'b1) && (B[W-1]==1'b1)); // -overflow
  cover property (@cb $past(!reset) && ($past(carry)==1'b0));
  cover property (@cb $past(!reset) && ($past(carry)==1'b1));
  cover property (@cb $past(!reset) && (gold(A,B,$past(carry))[W-1:0] == '0));

endmodule

// Bind into DUT (ports A,B,C,overflow come from DUT; sum/carry are DUT internals)
bind twos_complement_adder twos_complement_adder_sva #(.W(4)) i_twos_complement_adder_sva (.*);