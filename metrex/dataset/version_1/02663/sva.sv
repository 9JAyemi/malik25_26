// SVA checker for four_to_one (function is 4-input AND with X-masking to 0)
module four_to_one_sva (
  input logic in0, in1, in2, in3,
  input logic out
);

  // Function: out==1 iff all inputs are 1; otherwise out==0
  property p_all1_out1;
    @(in0 or in1 or in2 or in3 or out)
      (in0===1 && in1===1 && in2===1 && in3===1) |-> ##0 (out===1);
  endproperty
  assert property (p_all1_out1);

  property p_notall1_out0;
    @(in0 or in1 or in2 or in3 or out)
      !(in0===1 && in1===1 && in2===1 && in3===1) |-> ##0 (out===0);
  endproperty
  assert property (p_notall1_out0);

  // Output is always known
  assert property (@(in0 or in1 or in2 or in3 or out) ##0 !$isunknown(out));

  // Coverage: all-0s, all-1s, mixed, and output toggles
  cover property (@(in0 or in1 or in2 or in3 or out)
                  (in0===0 && in1===0 && in2===0 && in3===0) && out===0);
  cover property (@(in0 or in1 or in2 or in3 or out)
                  (in0===1 && in1===1 && in2===1 && in3===1) && out===1);
  cover property (@(in0 or in1 or in2 or in3 or out)
                  !((in0===0 && in1===0 && in2===0 && in3===0) ||
                    (in0===1 && in1===1 && in2===1 && in3===1)) && out===0);
  cover property (@(posedge out) 1);
  cover property (@(negedge out) 1);

endmodule

// Bind into DUT
bind four_to_one four_to_one_sva sva_i (.*);