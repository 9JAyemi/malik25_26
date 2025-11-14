// SVA for priority_encoder and final_output_generator
// Concise, bound to DUT instances; clockless concurrent assertions

// Assertions for priority_encoder
module priority_encoder_sva (
  input [3:0] in1,
  input [3:0] in2,
  input [3:0] priority_output
);
  // Functional correctness (when inputs are known)
  assert property ( !$isunknown({in1,in2})
                    |-> (priority_output == ((in1 > in2) ? in1 : in2)) );

  // No X/Z on output when inputs are known
  assert property ( !$isunknown({in1,in2}) |-> !$isunknown(priority_output) );

  // Functional coverage
  cover property (in1 > in2);
  cover property (in1 < in2);
  cover property (in1 == in2);
endmodule

bind priority_encoder priority_encoder_sva (.*);


// Assertions for final_output_generator
module final_output_generator_sva (
  input [3:0] in1,
  input [3:0] in2,
  input [3:0] final_output
);
  // Local recomputation of priority
  let prio = (in1 > in2) ? in1 : in2;

  // Expected final_output function of inputs
  let expected_final =
      (prio == 4'b0001) ? in1 :
      (prio == 4'b0010) ? in2 :
      (prio == 4'b0100) ? {in1[3:1], in2[0]} :
      (prio == 4'b1000) ? {in2[3:1], in1[0]} :
                          4'b0000;

  // Functional correctness (guard unknown inputs)
  assert property ( !$isunknown({in1,in2})
                    |-> (final_output == expected_final) );

  // No X/Z on output when inputs are known
  assert property ( !$isunknown({in1,in2}) |-> !$isunknown(final_output) );

  // Functional coverage: hit each case arm and the default
  cover property (prio == 4'b0001);
  cover property (prio == 4'b0010);
  cover property (prio == 4'b0100);
  cover property (prio == 4'b1000);
  cover property (!(prio inside {4'b0001,4'b0010,4'b0100,4'b1000}));

  // Relation coverage to ensure both encoder paths get exercised upstream
  cover property (in1 > in2);
  cover property (in1 < in2);
  cover property (in1 == in2);
endmodule

bind final_output_generator final_output_generator_sva (.*);