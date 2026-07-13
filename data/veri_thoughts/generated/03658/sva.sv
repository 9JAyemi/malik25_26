module twos_complement_sva(
    input logic [3:0] in,
    input logic [3:0] out
);

    // Non-negative inputs pass through unchanged.
    check_non_negative_passthrough: assert property (
        @($global_clock) (!in[3]) |-> (out == in)
    );

    // Negative inputs are converted by bitwise invert plus one.
    check_negative_invert_plus_one: assert property (
        @($global_clock) (in[3]) |-> (out == ((~in) + 4'd1))
    );

    // The most-negative 4-bit input maps to itself.
    check_most_negative_preserved: assert property (
        @($global_clock) (in == 4'b1000) |-> (out == 4'b1000)
    );

endmodule