module twos_comp_sva (
    input logic [3:0] in,
    input logic [3:0] out
);

    // Combinational DUT; sampled on the formal global clock.
    logic [3:0] neg_in;
    assign neg_in = ~in + 4'b0001;

    // Output matches the implemented sign-based selection.
    check_output_function: assert property (
        @($global_clock) out == ((in[3] == 1'b0) ? in : neg_in)
    );

    // Non-negative inputs pass through unchanged.
    check_non_negative_passthrough: assert property (
        @($global_clock) (in[3] == 1'b0) |-> (out == in)
    );

    // Negative inputs produce the two's-complement value.
    check_negative_twos_comp: assert property (
        @($global_clock) (in[3] == 1'b1) |-> (out == neg_in)
    );

    // Zero maps to zero.
    check_zero_maps_to_zero: assert property (
        @($global_clock) (in == 4'b0000) |-> (out == 4'b0000)
    );

    // The most-negative 4-bit value maps to itself.
    check_most_negative_maps_to_self: assert property (
        @($global_clock) (in == 4'b1000) |-> (out == 4'b1000)
    );

    // For negative inputs, input plus output is zero modulo 16.
    check_negative_sum_zero: assert property (
        @($global_clock) (in[3] == 1'b1) |-> ((out + in) == 4'b0000)
    );

    // Negative inputs except 1000 produce a non-negative output.
    check_negative_non_min_sign_clear: assert property (
        @($global_clock) ((in[3] == 1'b1) && (in != 4'b1000)) |-> (out[3] == 1'b0)
    );

endmodule