module bitwise_operators_sva #(
    parameter n = 8
) (
    input logic clk,
    input logic [n-1:0] a,
    input logic [n-1:0] b,
    input logic [n-1:0] and_out,
    input logic [n-1:0] or_out,
    input logic [n-1:0] xor_out,
    input logic [n-1:0] not_out
);

    // and_out must equal the bitwise AND of a and b.
    check_and_function: assert property (
        @(posedge clk) and_out == (a & b)
    );

    // or_out must equal the bitwise OR of a and b.
    check_or_function: assert property (
        @(posedge clk) or_out == (a | b)
    );

    // xor_out must equal the bitwise XOR of a and b.
    check_xor_function: assert property (
        @(posedge clk) xor_out == (a ^ b)
    );

    // not_out must equal the bitwise NOT of a.
    check_not_function: assert property (
        @(posedge clk) not_out == (~a)
    );

    // and_out must match the AND of a and the inverted b.
    check_and_complement: assert property (
        @(posedge clk) and_out == (a & ~b)
    );

    // or_out must match the OR of a and the inverted b.
    check_or_complement: assert property (
        @(posedge clk) or_out == (a | ~b)
    );

    // xor_out must match the XOR of a and the inverted b.
    check_xor_complement: assert property (
        @(posedge clk) xor_out == (a ^ ~b)
    );

    // not_out must match the inverted AND of a and b.
    check_not_complement: assert property (
        @(posedge clk) not_out == ~(a & b)
    );

    // and_out and or_out must always be equal.
    check_and_or_equal: assert property (
        @(posedge clk) and_out == or_out
    );

    // xor_out must equal the bitwise NOT of the inverted XOR.
    check_xor_not_complement: assert property (
        @(posedge clk) xor_out == ~((~a) ^ (~b))
    );

endmodule