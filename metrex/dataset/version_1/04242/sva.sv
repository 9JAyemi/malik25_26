// SVA for binary_adder
// Bind as: bind binary_adder binary_adder_sva u_sva (.*);
module binary_adder_sva (
  input clk,
  input rst,             // active-low synchronous reset (!rst = reset)
  input [7:0] A,
  input [7:0] B,
  input [8:0] result,
  input overflow
);
  default clocking cb @(posedge clk); endclocking

  // Reset behavior (synchronous, active-low)
  property p_reset_clears_next;
    (!rst) |=> (result == 9'd0 && overflow == 1'b0);
  endproperty
  assert property (p_reset_clears_next);

  property p_reset_holds_zero;
    (!rst && $past(!rst)) |-> (result == 9'd0 && overflow == 1'b0);
  endproperty
  assert property (p_reset_holds_zero);

  // No X on outputs during normal operation
  assert property (disable iff (!rst) !$isunknown({result, overflow}));

  // Functional correctness (one-cycle latency)
  // Next result is the 9-bit sum of A and B sampled this cycle
  assert property (disable iff (!rst) 1'b1 |=> (result == (A + B)));

  // Next overflow is carry-out of A+B; must match MSB of result
  assert property (disable iff (!rst) 1'b1 |=> (overflow == ((A + B) > 8'hFF)));
  assert property (disable iff (!rst) 1'b1 |=> (overflow == result[8]));

  // Low bits match sum low bits
  assert property (disable iff (!rst) 1'b1 |=> (result[7:0] == (A + B)[7:0]));

  // Corner/behavior coverage
  cover property (disable iff (!rst) (A+B) <= 8'hFF |=> (!overflow && !result[8]));
  cover property (disable iff (!rst) (A+B) >  8'hFF |=> ( overflow &&  result[8]));
  cover property (disable iff (!rst) (A+B) == 8'hFF |=> (!overflow && result == 9'd255));
  cover property (disable iff (!rst) (A+B) == 9'd256 |=> (overflow && result == 9'd256));
  cover property (disable iff (!rst) (A==8'h00 && B==8'h00) |=> (result==9'd0 && !overflow));
  cover property (disable iff (!rst) (A==8'hFF && B==8'hFF) |=> (result==9'd510 && overflow));

  // Reset sequence coverage
  cover property ($fell(rst) ##1 $rose(rst));
endmodule