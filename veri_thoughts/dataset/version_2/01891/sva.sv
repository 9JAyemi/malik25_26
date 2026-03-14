module adder_2bit_sva (
    input logic CLK,
    input logic [1:0] A,
    input logic [1:0] B,
    input logic [1:0] S,
    input logic [1:0] O,
    input logic [1:0] sum,
    input logic [1:0] diff,
    input logic       s_not
);
    // sum must equal A+B (2-bit modulo arithmetic).
    check_sum_def: assert property (
        @(posedge CLK) sum == (A + B)
    );

    // sum[0] equals A[0] XOR B[0].
    check_sum_bit0_xor: assert property (
        @(posedge CLK) sum[0] == (A[0] ^ B[0])
    );

    // sum[1] equals A[1] XOR B[1] XOR carry from bit0.
    check_sum_bit1: assert property (
        @(posedge CLK) sum[1] == (A[1] ^ B[1] ^ (A[0] & B[0]))
    );

    // diff equals truncated 2 LSBs of the 3-bit addition per RTL.
    check_diff_def: assert property (
        @(posedge CLK) diff == ( {A[1]^B[1], A[0]^B[0]} + {~B[1], ~B[0], 1'b0} )[1:0]
    );

    // diff[0] equals A[0] XOR B[0].
    check_diff_bit0_xor: assert property (
        @(posedge CLK) diff[0] == (A[0] ^ B[0])
    );

    // diff[1] equals (A[1] XOR B[1]) XOR (~B[0]).
    check_diff_bit1_expr: assert property (
        @(posedge CLK) diff[1] == ((A[1] ^ B[1]) ^ ~B[0])
    );

    // Output O must select sum when s_not is 1, else diff.
    check_o_mux: assert property (
        @(posedge CLK) O == (s_not ? sum : diff)
    );

    // When s_not is 1, O equals sum.
    check_o_when_snot_1: assert property (
        @(posedge CLK) s_not |-> (O == sum)
    );

    // When s_not is 0, O equals diff.
    check_o_when_snot_0: assert property (
        @(posedge CLK) !s_not |-> (O == diff)
    );
endmodule