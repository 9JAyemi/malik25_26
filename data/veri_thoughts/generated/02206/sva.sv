module twos_complement_sva (
  input logic clk,
  input logic [3:0] in,
  input logic [3:0] out
);

  // Output equals two's complement of input (mod 16).
  check_twos_complement_mapping: assert property (
    @(posedge clk) out == (~in + 4'b0001)
  );

  // Two's complement is involutive: applying it to out yields in.
  check_involution: assert property (
    @(posedge clk) ((~out + 4'b0001) == in)
  );

  // Zero input maps to zero output.
  check_zero_in_to_zero_out: assert property (
    @(posedge clk) (in == 4'b0000) |-> (out == 4'b0000)
  );

  // Zero output implies zero input.
  check_zero_out_implies_zero_in: assert property (
    @(posedge clk) (out == 4'b0000) |-> (in == 4'b0000)
  );

  // -8 (1000) is a fixed point under two's complement.
  check_neg8_fixed_point: assert property (
    @(posedge clk) (in == 4'b1000) |-> (out == 4'b1000)
  );

  // Input and output sum to zero modulo 16.
  check_sum_zero_mod16: assert property (
    @(posedge clk) ((out + in) == 4'b0000)
  );

endmodule