// SVA checker for adder_subtractor
module adder_subtractor_sva (
  input logic        clk,
  input logic [3:0]  A,
  input logic [3:0]  B,
  input logic        mode,
  input logic [3:0]  out
);
  default clocking cb @(posedge clk); endclocking

  // Track past validity to safely use $past
  bit past_valid;
  always @(posedge clk) past_valid <= 1'b1;

  // Expected result computed from previous-cycle inputs (matches NBA update timing)
  function automatic logic [3:0] exp_prev;
    input logic [3:0] a, b;
    input logic       m;
    exp_prev = m ? ((a + b) & 4'hF) : ((a - b) & 4'hF);
  endfunction

  // Functional correctness: registered output equals previous-cycle expected result
  property p_correct;
    past_valid && !$isunknown({$past(A),$past(B),$past(mode)}) |-> out == exp_prev($past(A),$past(B),$past(mode));
  endproperty
  assert property (p_correct);

  // Output must be known whenever previous-cycle inputs were known
  assert property (past_valid && !$isunknown({$past(A),$past(B),$past(mode)}) |-> !$isunknown(out));

  // Minimal functional coverage
  // Mode usage
  cover property (mode);                 // add seen
  cover property (!mode);                // sub seen
  cover property (past_valid && mode != $past(mode)); // mode toggle

  // Addition: no overflow and overflow wrap
  cover property (past_valid && $past(mode) && (($past(A)+$past(B)) <= 4'hF) && (out == (($past(A)+$past(B)) & 4'hF)));
  cover property (past_valid && $past(mode) && (($past(A)+$past(B)) >  4'hF) && (out == (($past(A)+$past(B)) & 4'hF)));

  // Subtraction: no borrow and borrow wrap
  cover property (past_valid && !$past(mode) && ($past(A) >= $past(B)) && (out == (($past(A)-$past(B)) & 4'hF)));
  cover property (past_valid && !$past(mode) && ($past(A) <  $past(B)) && (out == (($past(A)-$past(B)) & 4'hF)));

  // Corner outcomes
  cover property (out == 4'h0);
  cover property (out == 4'hF);
  cover property (past_valid && !$past(mode) && ($past(A) == $past(B)) && (out == 4'h0)); // A-B==0
  cover property (past_valid && $past(mode)  && (($past(A)==0) || ($past(B)==0)));        // add with zero
endmodule

// Bind into DUT
bind adder_subtractor adder_subtractor_sva sva_i (.*);