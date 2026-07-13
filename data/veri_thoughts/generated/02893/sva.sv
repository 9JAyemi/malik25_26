module gray_converter_sva #(
  parameter int n = 4
)(
  input logic clk,
  input logic [n-1:0] binary_in,
  input logic [n-1:0] gray_out
);

  // LSB of gray equals LSB of binary.
  check_gray_lsb: assert property (
    @(posedge clk) gray_out[0] == binary_in[0]
  );

  generate
    genvar i;
    for (i = 1; i < n; i++) begin : gray_chain
      // Each gray bit is XOR of its binary bit with previous gray bit.
      check_gray_chain: assert property (
        @(posedge clk) gray_out[i] == (binary_in[i] ^ gray_out[i-1])
      );
    end
  endgenerate

  generate
    genvar j;
    for (j = 1; j < n; j++) begin : binary_from_gray
      // Each binary bit equals XOR of adjacent gray bits.
      check_binary_from_gray: assert property (
        @(posedge clk) binary_in[j] == (gray_out[j] ^ gray_out[j-1])
      );
    end
  endgenerate

endmodule