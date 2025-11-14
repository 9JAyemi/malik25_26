// SVA for comparator_4bit
module comparator_4bit_sva (
  input clk,
  input reset,
  input [3:0] A,
  input [3:0] B,
  input greater,
  input less,
  input equal
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset)

  // Functional equivalence to previous-cycle inputs (guarded against Xs on inputs)
  a_func_equiv: assert property (
    !$isunknown($past({A,B})) |->
    {greater,less,equal} == {($past(A) > $past(B)), ($past(A) < $past(B)), ($past(A) == $past(B))}
  ) else $error("Comparator outputs don't match previous-cycle inputs");

  // One-hot output (out of reset)
  a_onehot: assert property ( $onehot({greater,less,equal}) )
    else $error("Outputs not one-hot");

  // Outputs known (out of reset)
  a_no_x_out: assert property ( !$isunknown({greater,less,equal}) )
    else $error("X/Z detected on outputs");

  // Synchronous reset clears outputs on next cycle
  a_reset_clears: assert property ( disable iff (1'b0)
    reset |=> {greater,less,equal} == 3'b000
  ) else $error("Reset did not clear outputs");

  // Coverage: hit each outcome
  c_gt:  cover property ( greater && !$past(reset) );
  c_lt:  cover property ( less    && !$past(reset) );
  c_eq:  cover property ( equal   && !$past(reset) );

  // Coverage: observe at least one state transition between outcomes
  c_state_change: cover property (
    $onehot({greater,less,equal}) ##1
    ($onehot({greater,less,equal}) && ({greater,less,equal} != $past({greater,less,equal})))
  );

endmodule

// Bind into DUT
bind comparator_4bit comparator_4bit_sva u_comparator_4bit_sva (
  .clk(clk),
  .reset(reset),
  .A(A),
  .B(B),
  .greater(greater),
  .less(less),
  .equal(equal)
);