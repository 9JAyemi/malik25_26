```systemverilog
module odd_even_sva (
  input logic [2:0] input_bits,
  output logic [1:0] output_bits
);
  // Sequential logic is not present, so we use @(posedge clk) for assertions.

  // Check if the output_bits are correctly set based on the input_bits
  // If the LSB of input_bits is 1, output_bits should be 2'b01
  // If the LSB of input_bits is 0, output_bits should be 2'b10
  check_output_bits: assert property (
    @(posedge clk) disable iff (!reset) (input_bits[0] == 1'b1) |-> (output_bits == 2'b01)
  );
  check_output_bits_2: assert property (
    @(posedge clk) disable iff (!reset) (input_bits[0] == 1'b0) |-> (output_bits == 2'b10)
  );

  // Check that output_bits does not change when input_bits does not change
  check_stability: assert property (
    @(posedge clk) disable iff (!reset) (input_bits == prev_input_bits) |-> (output_bits == prev_output_bits)
  ) else $error("Output bits changed unexpectedly when input bits did not change");

  // Store previous values for stability check
  logic [2:0] prev_input_bits;
  logic [1:0] prev_output_bits;

  always @(posedge clk) begin
    prev_input_bits <= input_bits;
    prev_output_bits <= output_bits;
  end

  // Check that reset properly resets the output_bits to 2'b10
  reset_output_bits: assert property (
    @(posedge clk) disable iff (reset) (output_bits == 2'b10)
  );

endmodule
```