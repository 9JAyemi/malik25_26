module odd_even_sva (
    input logic clk,
    input logic [2:0] input_bits,
    input logic [1:0] output_bits
);

// Output is 01 when LSB is 1.
    check_output_01_when_lsb1: assert property (
        @(posedge clk) input_bits[0] |-> (output_bits == 2'b01)
    );

// Output is 10 when LSB is 0.
    check_output_10_when_lsb0: assert property (
        @(posedge clk) !input_bits[0] |-> (output_bits == 2'b10)
    );

// Output is always one-hot.
    check_output_onehot: assert property (
        @(posedge clk) $onehot(output_bits)
    );

// Output never equals 00.
    check_output_not_zero: assert property (
        @(posedge clk) output_bits != 2'b00
    );

endmodule
