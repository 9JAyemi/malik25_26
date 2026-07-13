module adder_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] S
);
    localparam logic [3:0] B = 4'hA;

    // S must equal A plus the constant 4'hA.
    check_sum_matches_constant: assert property (
        @(posedge clk) S == (A + B)
    );

    // Bit 0 passes through because B[0] is 0.
    check_bit0_passthrough: assert property (
        @(posedge clk) S[0] == A[0]
    );

    // Bit 1 inverts because B[1] is 1 and bit 0 generates no carry.
    check_bit1_relation: assert property (
        @(posedge clk) S[1] == ~A[1]
    );

    // Bit 2 is A[2] XOR the carry from bit 1.
    check_bit2_relation: assert property (
        @(posedge clk) S[2] == (A[2] ^ A[1])
    );

    // Bit 3 includes the constant 1 and the carry from bit 2.
    check_bit3_relation: assert property (
        @(posedge clk) S[3] == (A[3] ^ 1'b1 ^ (A[2] & A[1]))
    );
endmodule