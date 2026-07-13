module bitwise_or_logical_or_not_sva (
    input logic clk,
    input logic [2:0] a,
    input logic [2:0] b,
    input logic [2:0] out_or_bitwise,
    input logic out_or_logical,
    input logic [5:0] out_not
);

    // External sampling clock; the DUT itself is combinational and has no reset.

    // out_or_bitwise[0] is the OR of a[0] and b[0].
    check_or_bit0: assert property (
        @(posedge clk) out_or_bitwise[0] == (a[0] | b[0])
    );

    // out_or_bitwise[1] is the OR of a[1] and b[1].
    check_or_bit1: assert property (
        @(posedge clk) out_or_bitwise[1] == (a[1] | b[1])
    );

    // out_or_bitwise[2] is the OR of a[2] and b[2].
    check_or_bit2: assert property (
        @(posedge clk) out_or_bitwise[2] == (a[2] | b[2])
    );

    // out_or_logical is the OR-reduction of the bitwise OR result.
    check_logical_or_reduce: assert property (
        @(posedge clk) out_or_logical == (out_or_bitwise[0] | out_or_bitwise[1] | out_or_bitwise[2])
    );

    // out_not[3] is the inversion of a[0].
    check_not_a_bit0: assert property (
        @(posedge clk) out_not[3] == ~a[0]
    );

    // out_not[4] is the inversion of a[1].
    check_not_a_bit1: assert property (
        @(posedge clk) out_not[4] == ~a[1]
    );

    // out_not[5] is the inversion of a[2].
    check_not_a_bit2: assert property (
        @(posedge clk) out_not[5] == ~a[2]
    );

    // out_not[0] is the inversion of b[0].
    check_not_b_bit0: assert property (
        @(posedge clk) out_not[0] == ~b[0]
    );

    // out_not[1] is the inversion of b[1].
    check_not_b_bit1: assert property (
        @(posedge clk) out_not[1] == ~b[1]
    );

    // out_not[2] is the inversion of b[2].
    check_not_b_bit2: assert property (
        @(posedge clk) out_not[2] == ~b[2]
    );

endmodule