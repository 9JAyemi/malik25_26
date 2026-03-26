module GrayCode_sva #(
  parameter n = 4,
  parameter m = 4
)(
  input logic         clk,
  input logic [n-1:0] in,
  input logic [m-1:0] out
);

  function automatic [m-1:0] binary_to_gray(input logic [n-1:0] binary_value);
    begin
      binary_to_gray = binary_value ^ (binary_value >> 1);
    end
  endfunction

  // out is the Gray code of the input sampled on the previous clock.
  check_out_is_previous_input_gray: assert property (
    @(posedge clk) ##1 out == binary_to_gray($past(in))
  );

  // A stable sampled input keeps the output stable on the following clock.
  check_stable_input_keeps_output_stable: assert property (
    @(posedge clk) $stable(in) |=> $stable(out)
  );

  genvar i;
  generate
    for (i = 0; i < m; i = i + 1) begin : gen_out_bits
      if (i < n-1) begin : gen_xor_bit
        // Lower Gray bits are XORs of adjacent prior input bits.
        check_gray_xor_bit: assert property (
          @(posedge clk) ##1 out[i] == ($past(in[i+1]) ^ $past(in[i]))
        );
      end else if (i == n-1) begin : gen_msb_bit
        // The Gray MSB matches the prior input MSB.
        check_gray_msb_bit: assert property (
          @(posedge clk) ##1 out[i] == $past(in[i])
        );
      end else begin : gen_zero_bit
        // Output bits above the input width remain zero.
        check_gray_zero_extended_bit: assert property (
          @(posedge clk) ##1 out[i] == 1'b0
        );
      end
    end
  endgenerate

endmodule