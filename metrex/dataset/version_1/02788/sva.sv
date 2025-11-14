// SVA checker for adder_4bit_carry
module adder_4bit_carry_sva (
  input logic [3:0] a,
  input logic [3:0] b,
  input logic       cin,
  input logic [3:0] sum,
  input logic       cout
);

  // Known inputs => known outputs
  property p_known_inputs_imply_known_outputs;
    !$isunknown({a,b,cin}) |-> !$isunknown({sum,cout});
  endproperty
  assert property (p_known_inputs_imply_known_outputs);

  // Functional correctness (5-bit add)
  property p_functional_correctness;
    !$isunknown({a,b,cin}) |-> {cout, sum} == ({1'b0, a} + {1'b0, b} + cin);
  endproperty
  assert property (p_functional_correctness);

  // No spurious output toggles when inputs are stable (zero-time)
  property p_no_spurious_output_toggle;
    $stable({a,b,cin}) |-> ##0 $stable({sum,cout});
  endproperty
  assert property (p_no_spurious_output_toggle);

  // Basic coverage
  cover property (!$isunknown({a,b,cin}) && cin==1'b0);
  cover property (!$isunknown({a,b,cin}) && cin==1'b1);
  cover property (!$isunknown({a,b,cin}) && cout==1'b0);
  cover property (!$isunknown({a,b,cin}) && cout==1'b1);

  // Corner cases
  cover property ({a,b,cin} == {4'h0,4'h0,1'b0});            // 0+0+0
  cover property ({a,b,cin} == {4'hF,4'hF,1'b1});            // 15+15+1 -> 31
  cover property (a==4'hF && b==4'h0 && cin && sum==4'h0 && cout); // full propagate
  cover property (a==4'h1 && b==4'h1 && !cin && sum==4'h2 && !cout);// single generate
  cover property (sum==4'h0 && !cout);                       // zero w/o carry
  cover property (sum==4'h0 && cout);                        // zero with carry

  // Sum distribution (hits all 16 sum values)
  genvar i;
  generate
    for (i=0; i<16; i++) begin : gen_sum_bins
      cover property (sum == i[3:0]);
    end
  endgenerate

endmodule

// Bind into DUT instance(s):
// bind adder_4bit_carry adder_4bit_carry_sva u_adder_4bit_carry_sva (.*)