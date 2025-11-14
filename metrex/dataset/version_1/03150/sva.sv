// SVA for gray_code. Bind this to the DUT; provide a sampling clk for temporal checks.

module gray_code_sva #(parameter int WIDTH = 8) (
  input  logic              clk,       // sampling clock for temporal checks
  input  logic [WIDTH-1:0]  data_in,
  input  logic [WIDTH-1:0]  gray_out
);

  // Combinational functional equivalence (LSB-oriented Gray): g = b ^ (b << 1)
  default clocking cb_comb @(*); endclocking
  assert property (gray_out == (data_in ^ (data_in << 1)));

  // If inputs are known, outputs must be known
  assert property (!$isunknown(data_in) |-> !$isunknown(gray_out));

  // Inverse mapping must reconstruct the input
  function automatic [WIDTH-1:0] gray2bin_lsb (input [WIDTH-1:0] g);
    automatic logic [WIDTH-1:0] b;
    b[0] = g[0];
    for (int i = 1; i < WIDTH; i++) b[i] = g[i] ^ b[i-1];
    return b;
  endfunction
  assert property (gray2bin_lsb(gray_out) == data_in);

  // Temporal: toggling exactly one input bit toggles only the expected output bit(s)
  logic past_valid;
  always_ff @(posedge clk) past_valid <= 1'b1;

  genvar k;
  generate
    for (k = 0; k < WIDTH; k++) begin : GEN_ONEBIT_TOG
      localparam logic [WIDTH-1:0] EXP_MASK =
        (logic[WIDTH-1:0]'(1) << k) |
        ((k < WIDTH-1) ? (logic[WIDTH-1:0]'(1) << (k+1)) : '0);

      property onebit_input_toggle_expected_outputs;
        @(posedge clk)
          past_valid &&
          (($past(data_in) ^ data_in) == (logic[WIDTH-1:0]'(1) << k))
        |-> (($past(gray_out) ^ gray_out) == EXP_MASK);
      endproperty
      assert property (onebit_input_toggle_expected_outputs);
      cover  property (onebit_input_toggle_expected_outputs);
    end
  endgenerate

endmodule

// Bind to DUT (provide a sampling clock from your TB)
bind gray_code gray_code_sva #(.WIDTH(8))
  i_gray_code_sva (.clk(tb_clk), .data_in(data_in), .gray_out(gray_out));