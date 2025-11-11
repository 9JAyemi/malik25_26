// SVA bind module for digital_circuit
module digital_circuit_sva (
    input logic input_1,
    input logic input_2,
    input logic input_3,
    input logic input_4,
    input logic output_1,
    input logic output_2
);

  // Combinational functional equivalence (4-state accurate)
  always_comb begin
    assert (output_1 === (input_1 & input_2))
      else $error("digital_circuit: output_1 != (input_1 & input_2)");
    assert (output_2 === (input_3 | input_4))
      else $error("digital_circuit: output_2 != (input_3 | input_4)");

    // X-propagation/cleanliness: known inputs imply known outputs
    if (!$isunknown({input_1, input_2}))
      assert (!$isunknown(output_1))
        else $error("digital_circuit: output_1 unknown despite known inputs");
    if (!$isunknown({input_3, input_4}))
      assert (!$isunknown(output_2))
        else $error("digital_circuit: output_2 unknown despite known inputs");
  end

  // Functional implication sanity (redundant but clarifies intent)
  always_comb begin
    if (output_1 === 1'b1) assert (input_1 === 1'b1 && input_2 === 1'b1)
      else $error("digital_circuit: output_1=1 requires input_1=input_2=1");
    if (output_2 === 1'b0) assert (input_3 === 1'b0 && input_4 === 1'b0)
      else $error("digital_circuit: output_2=0 requires input_3=input_4=0");
  end

  // Coverage: output toggles
  cover property (@(posedge output_1) 1);
  cover property (@(negedge output_1) 1);
  cover property (@(posedge output_2) 1);
  cover property (@(negedge output_2) 1);

  // Coverage: all output combinations observed when any input changes
  cover property (@(posedge input_1 or negedge input_1 or
                    posedge input_2 or negedge input_2 or
                    posedge input_3 or negedge input_3 or
                    posedge input_4 or negedge input_4)
                  {output_1, output_2} == 2'b00);
  cover property (@(posedge input_1 or negedge input_1 or
                    posedge input_2 or negedge input_2 or
                    posedge input_3 or negedge input_3 or
                    posedge input_4 or negedge input_4)
                  {output_1, output_2} == 2'b01);
  cover property (@(posedge input_1 or negedge input_1 or
                    posedge input_2 or negedge input_2 or
                    posedge input_3 or negedge input_3 or
                    posedge input_4 or negedge input_4)
                  {output_1, output_2} == 2'b10);
  cover property (@(posedge input_1 or negedge input_1 or
                    posedge input_2 or negedge input_2 or
                    posedge input_3 or negedge input_3 or
                    posedge input_4 or negedge input_4)
                  {output_1, output_2} == 2'b11);

endmodule

// Bind into the DUT
bind digital_circuit digital_circuit_sva u_digital_circuit_sva (
  .input_1 (input_1),
  .input_2 (input_2),
  .input_3 (input_3),
  .input_4 (input_4),
  .output_1(output_1),
  .output_2(output_2)
);