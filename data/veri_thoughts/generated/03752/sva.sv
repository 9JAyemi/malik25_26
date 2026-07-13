module twos_complement_sva (
    input logic [3:0] num_in,
    input logic [3:0] num_out
);

    // Sample the combinational function on the formal global clock.
    // Output must equal bitwise inversion of input plus one.
    check_twos_complement_equation: assert property (
        @($global_clock) num_out == (~num_in + 4'b0001)
    );

    // Applying two's complement to the output must recover the input.
    check_twos_complement_involution: assert property (
        @($global_clock) ((~num_out) + 4'b0001) == num_in
    );

    // Input and output must sum to zero modulo 16.
    check_additive_inverse: assert property (
        @($global_clock) (num_in + num_out) == 4'b0000
    );

    // Zero must remain unchanged.
    check_zero_fixed_point: assert property (
        @($global_clock) (num_in == 4'b0000) |-> (num_out == 4'b0000)
    );

    // 4'b1000 must remain unchanged.
    check_most_negative_fixed_point: assert property (
        @($global_clock) (num_in == 4'b1000) |-> (num_out == 4'b1000)
    );

    // All other inputs must produce a different output value.
    check_non_fixed_points_change: assert property (
        @($global_clock) ((num_in != 4'b0000) && (num_in != 4'b1000)) |-> (num_out != num_in)
    );

endmodule