module bitwise_or_logical_or_not_sva (
    input logic [2:0] a,
    input logic [2:0] b,
    input logic [2:0] out_or_bitwise,
    input logic out_or_logical,
    input logic [5:0] out_not
);

    // out_or_bitwise[0] is the OR of a[0] and b[0].
    check_out_or_bitwise0: assert property (
        @($global_clock) out_or_bitwise[0] == (a[0] | b[0])
    );

    // out_or_bitwise[1] is the OR of a[1] and b[1].
    check_out_or_bitwise1: assert property (
        @($global_clock) out_or_bitwise[1] == (a[1] | b[1])
    );

    // out_or_bitwise[2] is the OR of a[2] and b[2].
    check_out_or_bitwise2: assert property (
        @($global_clock) out_or_bitwise[2] == (a[2] | b[2])
    );

    // out_or_logical is the OR of the three out_or_bitwise bits.
    check_out_or_logical: assert property (
        @($global_clock) out_or_logical == (out_or_bitwise[0] | out_or_bitwise[1] | out_or_bitwise[2])
    );

    // out_not[2:0] is the bitwise NOT of a.
    check_out_not_a: assert property (
        @($global_clock) out_not[2:0] == ~a
    );

    // out_not[5:3] is the bitwise NOT of b.
    check_out_not_b: assert property (
        @($global_clock) out_not[5:3] == ~b
    );

    // out_not is the concatenation of the two NOT vectors.
    check_out_not_concat: assert property (
        @($global_clock) out_not == {~b, ~a}
    );

endmodule