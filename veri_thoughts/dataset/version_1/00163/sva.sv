// SVA for decoder_4to16
module decoder_4to16_sva (
  input  logic [3:0]  input_bits,
  input  logic [15:0] output_bits
);

  default clocking cb @(*); endclocking

  // Outputs are always known (no X/Z)
  a_no_x_on_out: assert property (!$isunknown(output_bits));

  // Known input -> exact one-hot mapping
  a_map_eq: assert property (!$isunknown(input_bits) |-> (output_bits == (16'h0001 << input_bits)));

  // Known input -> bit at selected index is 1
  a_index_one: assert property (!$isunknown(input_bits) |-> output_bits[input_bits]);

  // X/Z on input -> all outputs zero
  a_xin_zero_out: assert property ($isunknown(input_bits) |-> (output_bits == 16'h0000));

  // Functional coverage: hit every input value with correct one-hot output
  genvar i;
  generate
    for (i = 0; i < 16; i++) begin : g_cov
      c_each_code: cover property ((input_bits == i) && (output_bits == (16'h0001 << i)));
    end
  endgenerate

  // Coverage for X/Z input behavior
  c_x_case: cover property ($isunknown(input_bits) && (output_bits == 16'h0000));

endmodule

// Bind into DUT
bind decoder_4to16 decoder_4to16_sva sva_inst (.input_bits(input_bits), .output_bits(output_bits));