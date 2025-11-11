// SVA for decoder_5bit
// Bindable, concise, and covers functional correctness and one-hotness.

module decoder_5bit_sva (
  input logic [4:0]  in,
  input logic [31:0] out
);

  // Input must be known whenever it changes
  a_in_known: assert property (@(in) !$isunknown(in));

  // Output must never be X/Z and must be one-hot whenever it changes
  a_out_onehot: assert property (@(out) (!$isunknown(out) && $onehot(out)));

  // Correct decode mapping (use ##0 to observe updated out in same timestep)
  a_decode_eq: assert property (@(in) !$isunknown(in) |=> ##0 (out == (32'h1 << in)));

  // Selected bit must match index 'in'
  a_bit_index: assert property (@(in) !$isunknown(in) |=> ##0 out[in]);

  // Output only changes in response to input change
  a_out_only_on_in_change: assert property (@(out) $changed(in));

  // Functional coverage: hit all 32 input codes and corresponding one-hot output bit
  genvar i;
  generate
    for (i = 0; i < 32; i++) begin : COV
      c_code_i: cover property (@(in) (in == i) |=> ##0 (out[i] && $onehot(out)));
    end
  endgenerate

endmodule

bind decoder_5bit decoder_5bit_sva u_decoder_5bit_sva (.in(in), .out(out));