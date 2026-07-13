module bitwise_or_logical_or_not_sva (
    input logic [2:0] a,
    input logic [2:0] b,
    input logic [2:0] out_or_bitwise,
    input logic out_or_logical,
    input logic [5:0] out_not
);

    // out_or_bitwise[0] is the OR of a[0] and b[0].
    check_out_or_bitwise_bit0: assert property (
        @($global_clock) out_or_bitwise[0] == (a[0] | b[0])
    );

    // out_or_bitwise[1] is the OR of a[1] and b[1].
    check_out_or_bitwise_bit1: assert property (
        @($global_clock) out_or_bitwise[1] == (a[1] | b[1])
    );

    // out_or_bitwise[2] is the OR of a[2] and b[2].
    check_out_or_bitwise_bit2: assert property (
        @($global_clock) out_or_bitwise[2] == (a[2] | b[2])
    );

    // out_or_logical is the OR reduction of out_or_bitwise.
    check_out_or_logical_reduction: assert property (
        @($global_clock) out_or_logical == (|out_or_bitwise)
    );

    // out_not[5:3] is the inverted a vector.
    check_out_not_upper_bits: assert property (
        @($global_clock) out_not[5:3] == ~a
    );

    // out_not[2:0] is the inverted b vector.
    check_out_not_lower_bits: assert property (
        @($global_clock) out_not[2:0] == ~b
    );

    // out_not is the concatenation of the inverted a and b vectors.
    check_out_not_concatenation: assert property (
        @($global_clock) out_not == {~a, ~b}
    );

endmodule