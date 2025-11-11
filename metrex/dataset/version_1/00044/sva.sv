// Bind these SVA to the adder without modifying the DUT
bind adder adder_sva u_adder_sva();

module adder_sva;

  // Correctness: when inputs are known, sum must be A+B (allowing delta update)
  property p_add_correct;
    @(A or B or sum) (!$isunknown({A,B})) |-> ##0 (sum == A + B);
  endproperty
  assert property (p_add_correct);

  // No spurious output changes when inputs are stable
  property p_sum_stable_when_inputs_stable;
    @(A or B or sum) $stable({A,B}) |-> ##0 $stable(sum);
  endproperty
  assert property (p_sum_stable_when_inputs_stable);

  // Sum must not contain X/Z when inputs are known
  property p_sum_no_x_when_inputs_known;
    @(A or B or sum) (!$isunknown({A,B})) |-> ##0 !$isunknown(sum);
  endproperty
  assert property (p_sum_no_x_when_inputs_known);

  // Function getName must always return "gmod"
  property p_getName_const;
    @(A or B or sum) 1 |-> (getName(0) == "gmod");
  endproperty
  assert property (p_getName_const);

  // globali must initialize to INITVAL and remain constant via getGlob()
  initial assert (getGlob(0) == INITVAL);
  property p_getGlob_const;
    @(A or B or sum) 1 |-> (getGlob(0) == INITVAL);
  endproperty
  assert property (p_getGlob_const);

  // Coverage: key scenarios
  cover property (@(A or B or sum) (!$isunknown({A,B})) && A==32'h0 && B==32'h0 && sum==32'h0);
  cover property (@(A or B or sum) (!$isunknown({A,B})) && A==32'hFFFF_FFFF && B==32'h1 && sum==32'h0);       // wraparound
  cover property (@(A or B or sum) (!$isunknown({A,B})) && A==32'h8000_0000 && B==32'h8000_0000 && sum==32'h0);// signed overflow pattern
  cover property (@(A or B or sum) (!$isunknown({A,B})) && (A == ~B) && (sum == 32'hFFFF_FFFF));               // complementary operands

endmodule