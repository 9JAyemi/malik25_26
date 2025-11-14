// SVA checker for adder_subtractor
// Bind this module to the DUT for assertions and coverage.

module adder_subtractor_sva;

  // We bind inside the DUT scope, so we can reference in0,in1,SUB,out,sum1,sum2 directly.
  default clocking cb @(in0 or in1 or SUB or sum1 or sum2 or out); endclocking

  function automatic logic [3:0] exp(input logic [3:0] a, b, input logic sub);
    exp = a + (sub ? (~b + 4'd1) : b);
  endfunction

  function automatic bit add_carry(input logic [3:0] a, b);
    add_carry = ({1'b0,a} + {1'b0,b})[4];
  endfunction

  // Functional correctness through the internal pipeline (3 delta cycles)
  property p_pipeline_correct;
    ($changed(in0) or $changed(in1) or $changed(SUB)) && !$isunknown({in0,in1,SUB})
    |-> ##0 (sum1 == exp(in0,in1,SUB))
        ##0 (sum2 == sum1)
        ##0 (out  == sum2 && out == exp(in0,in1,SUB));
  endproperty
  assert property (p_pipeline_correct);

  // Output becomes known when inputs are known (after propagation)
  property p_known_out_if_known_in;
    !$isunknown({in0,in1,SUB}) |-> ##0 ##0 ##0 !$isunknown(out);
  endproperty
  assert property (p_known_out_if_known_in);

  // Once settled, result holds until a new input change
  property p_hold_until_next_input_change;
    (($changed(in0) or $changed(in1) or $changed(SUB)) && !$isunknown({in0,in1,SUB}))
    |-> ##0 ##0 ##0 (out == exp(in0,in1,SUB)) until ($changed(in0) or $changed(in1) or $changed(SUB));
  endproperty
  assert property (p_hold_until_next_input_change);

  // Internal pipeline signals must be known when inputs are known
  property p_known_internal_if_known_in;
    !$isunknown({in0,in1,SUB})
    |-> ##0 !$isunknown(sum1) ##0 !$isunknown(sum2) ##0 !$isunknown(out);
  endproperty
  assert property (p_known_internal_if_known_in);

  // Coverage: exercise add and sub, carry/borrow, zero, extremes
  sequence s_trig; ($changed(in0) or $changed(in1) or $changed(SUB)) && !$isunknown({in0,in1,SUB}); endsequence

  cover property (s_trig && !SUB ##0 ##0 ##0 (out == exp(in0,in1,SUB)));                // add
  cover property (s_trig &&  SUB ##0 ##0 ##0 (out == exp(in0,in1,SUB)));                // sub
  cover property (s_trig && !SUB && add_carry(in0,in1));                                 // add with carry (wrap)
  cover property (s_trig &&  SUB && (in0 < in1));                                        // sub with borrow (wrap)
  cover property (s_trig &&  SUB && (in0 == in1) ##0 ##0 ##0 (out == 4'd0));             // zero from subtract
  cover property (s_trig && (in0 == 4'd0)  && (in1 == 4'd0));                            // all zeros
  cover property (s_trig && (in0 == 4'hF) && (in1 == 4'hF));                             // all ones
  cover property ($changed(SUB));                                                        // SUB toggles

endmodule

bind adder_subtractor adder_subtractor_sva;