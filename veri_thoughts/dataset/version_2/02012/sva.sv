module decoder_4to16_sva (
  input logic clk,
  input logic [3:0] input_lines,
  input logic [15:0] output_lines
);

  // Output vector must equal 1 << input_lines for all inputs 0..15.
  check_vector_mapping: assert property (
    @(posedge clk) output_lines == (16'h0001 << input_lines)
  );

  // Outputs are always exactly one-hot.
  check_onehot_outputs: assert property (
    @(posedge clk) $onehot(output_lines)
  );

  genvar idx;
  generate
    for (idx = 0; idx < 16; idx++) begin : g_decode
      // When input_lines == idx, output_lines must be one-hot at bit idx.
      check_decode_map: assert property (
        @(posedge clk) (input_lines == idx) |-> (output_lines == (16'h0001 << idx))
      );
    end
  endgenerate

endmodule