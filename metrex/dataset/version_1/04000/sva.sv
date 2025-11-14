// SVA for module s8. Bind these assertions to the DUT.
// Focus: exact combinational mapping, no X/Z after valid input,
// zero-latency response, and concise functional coverage.

module s8_sva (
  input logic [5:0] stage1_input,
  input logic [3:0] stage1_output
);
  // Reference LUT for s8
  localparam logic [3:0] S8_LUT [0:63] = '{
    4'd13,4'd1 ,4'd2 ,4'd15,4'd8 ,4'd13,4'd4 ,4'd8 ,
    4'd6 ,4'd10,4'd15,4'd3 ,4'd11,4'd7 ,4'd1 ,4'd4 ,
    4'd10,4'd12,4'd9 ,4'd5 ,4'd3 ,4'd6 ,4'd14,4'd11,
    4'd5 ,4'd0 ,4'd0 ,4'd14,4'd12,4'd9 ,4'd7 ,4'd2 ,
    4'd7 ,4'd2 ,4'd11,4'd1 ,4'd4 ,4'd14,4'd1 ,4'd7 ,
    4'd9 ,4'd4 ,4'd12,4'd10,4'd14,4'd8 ,4'd2 ,4'd13,
    4'd0 ,4'd15,4'd6 ,4'd12,4'd10,4'd9 ,4'd13,4'd0 ,
    4'd15,4'd3 ,4'd3 ,4'd5 ,4'd5 ,4'd6 ,4'd8 ,4'd11
  };

  // Correctness and zero-latency: on any input change, output must match LUT in the same delta
  property s8_map_zero_latency;
    @(stage1_input)
      !$isunknown(stage1_input) |-> ##0 (! $isunknown(stage1_output) && stage1_output == S8_LUT[stage1_input]);
  endproperty
  assert property (s8_map_zero_latency)
    else $error("s8: stage1_output=%0d does not match LUT[%0d]=%0d", stage1_output, stage1_input, S8_LUT[stage1_input]);

  // Optional: output should never be X/Z once driven by a known input (redundant with the assertion above)
  property s8_no_x_after_known_in;
    @(stage1_input or stage1_output)
      !$isunknown(stage1_input) |-> ##0 ! $isunknown(stage1_output);
  endproperty
  assert property (s8_no_x_after_known_in)
    else $error("s8: stage1_output has X/Z with known input");

  // Functional coverage: exercise all 64 inputs and observe the correct mapped output
  genvar i;
  generate
    for (i = 0; i < 64; i++) begin : COV_IN_ALL
      cover property (@(stage1_input) stage1_input == i ##0 stage1_output == S8_LUT[i]);
    end
  endgenerate

  // Functional coverage: see all 16 possible output values at least once
  genvar v;
  generate
    for (v = 0; v < 16; v++) begin : COV_OUT_ALL
      cover property (@(stage1_output) stage1_output == v);
    end
  endgenerate
endmodule

bind s8 s8_sva s8_sva_i(.stage1_input(stage1_input), .stage1_output(stage1_output));