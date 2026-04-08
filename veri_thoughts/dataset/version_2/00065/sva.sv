module top_module_sva (
    input logic clk,
    input logic [2:0] a,
    input logic [2:0] b,
    input logic [2:0] out_or_bitwise,
    input logic out_or_logical,
    input logic [5:0] out_not
);

    // Bitwise OR output equals a | b.
    check_out_or_bitwise_value: assert property (
        @(posedge clk) out_or_bitwise === (a | b)
    );

    // Bit 0 of the bitwise OR output matches a[0] | b[0].
    check_out_or_bitwise_bit0: assert property (
        @(posedge clk) out_or_bitwise[0] === (a[0] | b[0])
    );

    // Bit 1 of the bitwise OR output matches a[1] | b[1].
    check_out_or_bitwise_bit1: assert property (
        @(posedge clk) out_or_bitwise[1] === (a[1] | b[1])
    );

    // Bit 2 of the bitwise OR output matches a[2] | b[2].
    check_out_or_bitwise_bit2: assert property (
        @(posedge clk) out_or_bitwise[2] === (a[2] | b[2])
    );

    // Logical OR output matches the RTL non-zero test.
    check_out_or_logical_value: assert property (
        @(posedge clk) out_or_logical === ((a != 3'b000) || (b != 3'b000))
    );

    // Lower half of out_not is the bitwise inversion of a.
    check_out_not_lower_half: assert property (
        @(posedge clk) out_not[2:0] === (~a)
    );

    // Upper half of out_not is the bitwise inversion of b.
    check_out_not_upper_half: assert property (
        @(posedge clk) out_not[5:3] === (~b)
    );

    // Full out_not matches the concatenation {~b, ~a}.
    check_out_not_concat: assert property (
        @(posedge clk) out_not === {~b, ~a}
    );

endmodule