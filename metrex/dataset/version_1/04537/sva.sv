// SVA for seven_segment_display
// Concise, full functional check + key coverage

module seven_segment_display_sva (
  input  logic [3:0] binary_input,
  input  logic [6:0] seven_segment_output
);
  // Sample on any change of input; check outputs in same timestep (##0)
  default clocking cb @(binary_input); endclocking

  // Golden LUT derived from the DUT's segment equations (A..G == [6:0])
  localparam logic [6:0] EXP [0:15] = '{
    7'b1001011, // 0
    7'b1011111, // 1
    7'b0110111, // 2
    7'b0101000, // 3
    7'b0011111, // 4
    7'b0011110, // 5
    7'b0110000, // 6
    7'b1101010, // 7
    7'b0011111, // 8
    7'b0000000, // 9
    7'b0001101, // A(10)
    7'b0011111, // b(11)
    7'b0000000, // C(12)
    7'b0000000, // d(13)
    7'b0000000, // E(14)
    7'b1011111  // F(15)
  };

  // Inputs must be known
  assert property (!$isunknown(binary_input))
    else $error("seven_segment_display: binary_input has X/Z");

  // Functional correctness and outputs known when inputs are known
  assert property (!$isunknown(binary_input) |-> ##0
                   (! $isunknown(seven_segment_output) &&
                    seven_segment_output == EXP[binary_input]))
    else $error("seven_segment_display: output mismatch for input %0h", binary_input);

  // Input space coverage (all 16 values)
  genvar i;
  generate
    for (i = 0; i < 16; i++) begin : C_IN
      cover property (binary_input == i[3:0]);
    end
  endgenerate

  // Segment toggle coverage (each segment rises and falls at least once)
  genvar j;
  generate
    for (j = 0; j < 7; j++) begin : C_SEG
      cover property ($rose(seven_segment_output[j]));
      cover property ($fell(seven_segment_output[j]));
    end
  endgenerate
endmodule

bind seven_segment_display seven_segment_display_sva sva_inst (
  .binary_input(binary_input),
  .seven_segment_output(seven_segment_output)
);