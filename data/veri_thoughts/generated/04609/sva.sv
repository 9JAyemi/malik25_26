module adder_sva (
    input logic       clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] Sum
);

    // Sum equals the 4-bit addition of A and B.
    check_sum_matches_addition: assert property (
        @(posedge clk) Sum == (A + B)
    );

    // Bit 0 is the XOR of the input LSBs.
    check_sum_bit0: assert property (
        @(posedge clk) Sum[0] == (A[0] ^ B[0])
    );

    // Bit 1 includes the carry from bit 0.
    check_sum_bit1: assert property (
        @(posedge clk) Sum[1] == (A[1] ^ B[1] ^ (A[0] & B[0]))
    );

    // Bit 2 includes the carry propagated from lower bits.
    check_sum_bit2: assert property (
        @(posedge clk) Sum[2] == (A[2] ^ B[2] ^ ((A[1] & B[1]) | ((A[1] ^ B[1]) & (A[0] & B[0]))))
    );

    // Bit 3 includes the carry propagated from bits 0 through 2.
    check_sum_bit3: assert property (
        @(posedge clk) Sum[3] == (A[3] ^ B[3] ^ ((A[2] & B[2]) | ((A[2] ^ B[2]) & ((A[1] & B[1]) | ((A[1] ^ B[1]) & (A[0] & B[0]))))))
    );

    // A zero A operand passes B through to Sum.
    check_zero_a_passthrough: assert property (
        @(posedge clk) (A == 4'b0000) |-> (Sum == B)
    );

    // A zero B operand passes A through to Sum.
    check_zero_b_passthrough: assert property (
        @(posedge clk) (B == 4'b0000) |-> (Sum == A)
    );

endmodule