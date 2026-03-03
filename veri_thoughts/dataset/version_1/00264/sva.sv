// SVA for s6: bindable, concise, and complete

module s6_sva (
  input  logic [5:0] stage1_input,
  input  logic [3:0] stage1_output
);

  // Golden lookup table
  localparam logic [3:0] S6_LUT [0:63] = '{
    4'd12,4'd10,4'd1, 4'd15,4'd10,4'd4, 4'd15,4'd2,
    4'd9, 4'd7, 4'd2, 4'd12,4'd6, 4'd9, 4'd8, 4'd5,
    4'd0, 4'd6, 4'd13,4'd1, 4'd3, 4'd13,4'd4, 4'd14,
    4'd14,4'd0, 4'd7, 4'd11,4'd5, 4'd3, 4'd11,4'd8,
    4'd9, 4'd4, 4'd14,4'd3, 4'd15,4'd2, 4'd5, 4'd12,
    4'd2, 4'd9, 4'd8, 4'd5, 4'd12,4'd15,4'd3, 4'd10,
    4'd7, 4'd11,4'd0, 4'd14,4'd4, 4'd1, 4'd10,4'd7,
    4'd1, 4'd6, 4'd13,4'd0, 4'd11,4'd8, 4'd6, 4'd13
  };

  // Basic sanity (no X/Z on ports)
  a_in_known:  assert property (!$isunknown(stage1_input))
    else $error("s6: stage1_input has X/Z");
  a_out_known: assert property (!$isunknown(stage1_output))
    else $error("s6: stage1_output has X/Z");

  // Functional equivalence to golden LUT (continuous, clockless)
  a_map: assert property (stage1_output == S6_LUT[stage1_input])
    else $error("s6: output %0d != LUT[%0d]=%0d",
                stage1_output, stage1_input, S6_LUT[stage1_input]);

  // Output range check (redundant with LUT mapping but explicit)
  a_out_range: assert property (stage1_output inside {[4'd0:4'd15]})
    else $error("s6: stage1_output out of 4-bit range: %0d", stage1_output);

  // Coverage: hit all 64 inputs and all 16 outputs
  genvar i;
  for (i = 0; i < 64; i++) begin : C_IN
    cover property (stage1_input == i[5:0]);
  end
  genvar o;
  for (o = 0; o < 16; o++) begin : C_OUT
    cover property (stage1_output == o[3:0]);
  end

endmodule

// Bind into DUT
bind s6 s6_sva u_s6_sva (.stage1_input(stage1_input),
                         .stage1_output(stage1_output));