// SVA checker for incrementer
module incrementer_sva(input logic clk,
                       input logic signed [31:0] in,
                       input logic signed [31:0] out);

  // past_valid to guard $past usage (no reset provided)
  logic past_valid;
  initial past_valid = 1'b0;
  always_ff @(posedge clk) past_valid <= 1'b1;

  default clocking cb @(posedge clk); endclocking

  // Functional correctness: out == (prev in) + 1 (signed, with wrap)
  // Compare in 33-bit signed space to capture overflow correctly.
  property p_inc_correct;
    past_valid && !$isunknown($past(in))
      |-> {out[31],out} == $signed({$past(in)[31],$past(in)}) + 33'sd1;
  endproperty
  assert property (p_inc_correct);

  // Out must be known when prev in was known
  assert property (past_valid && !$isunknown($past(in)) |-> !$isunknown(out));

  // Coverage: key scenarios
  // Simple increment from 0 -> 1
  cover property (past_valid && $past(in) == 32'sd0 && out == 32'sd1);
  // -1 -> 0 boundary
  cover property (past_valid && $past(in) == -32'sd1 && out == 32'sd0);
  // Signed positive overflow: 0x7fffffff -> 0x80000000
  cover property (past_valid && $past(in) == 32'sh7fffffff && out == 32'sh80000000);
  // A generic negative value increments
  cover property (past_valid && $past(in) == -32'sd2 && out == -32'sd1);

endmodule

// Bind into DUT
bind incrementer incrementer_sva u_incrementer_sva(.clk(clk), .in(in), .out(out));