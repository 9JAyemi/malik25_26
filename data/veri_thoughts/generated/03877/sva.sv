module twos_complement_sva (
    input logic clk,
    input logic [3:0] binary_input,
    input logic [3:0] twos_complement_output
);

    // Output matches bitwise invert plus one.
    check_twos_complement_exact: assert property (
        @(posedge clk) twos_complement_output == (~binary_input + 4'b0001)
    );

    // Output is the 4-bit arithmetic negation of the input.
    check_arithmetic_negation: assert property (
        @(posedge clk) twos_complement_output == (4'b0000 - binary_input)
    );

    // Zero is its own two's complement.
    check_zero_maps_to_zero: assert property (
        @(posedge clk) (binary_input == 4'b0000) |-> (twos_complement_output == 4'b0000)
    );

    // 4'b1000 is its own two's complement in 4 bits.
    check_most_negative_self_inverse: assert property (
        @(posedge clk) (binary_input == 4'b1000) |-> (twos_complement_output == 4'b1000)
    );

    // Nonzero inputs sum with their two's complement to zero modulo 16.
    check_nonzero_sum_wraps_to_zero: assert property (
        @(posedge clk) (binary_input != 4'b0000) |-> ((twos_complement_output + binary_input) == 4'b0000)
    );

endmodule