module alu_16bit_sva (
    input logic        clk,
    input logic [15:0] A,
    input logic [15:0] B,
    input logic [3:0]  op,
    input logic [15:0] Y
);

    // op 0000 selects 16-bit addition.
    check_add_operation: assert property (
        @(posedge clk) (op == 4'b0000) |-> (Y == (A + B))
    );

    // op 0001 selects 16-bit subtraction.
    check_sub_operation: assert property (
        @(posedge clk) (op == 4'b0001) |-> (Y == (A - B))
    );

    // op 0010 selects bitwise AND.
    check_and_operation: assert property (
        @(posedge clk) (op == 4'b0010) |-> (Y == (A & B))
    );

    // op 0011 selects bitwise OR.
    check_or_operation: assert property (
        @(posedge clk) (op == 4'b0011) |-> (Y == (A | B))
    );

    // op 0100 selects bitwise XOR.
    check_xor_operation: assert property (
        @(posedge clk) (op == 4'b0100) |-> (Y == (A ^ B))
    );

    // op 0101 selects bitwise NOT of A.
    check_not_a_operation: assert property (
        @(posedge clk) (op == 4'b0101) |-> (Y == (~A))
    );

    // op 0110 selects logical left shift by one.
    check_shift_left_operation: assert property (
        @(posedge clk) (op == 4'b0110) |-> (Y == ({A[14:0], 1'b0}))
    );

    // op 0111 selects logical right shift by one.
    check_shift_right_operation: assert property (
        @(posedge clk) (op == 4'b0111) |-> (Y == ({1'b0, A[15:1]}))
    );

    // op 1000 selects rotate left by one.
    check_rotate_left_operation: assert property (
        @(posedge clk) (op == 4'b1000) |-> (Y == ({A[14:0], A[15]}))
    );

    // op 1001 selects rotate right by one.
    check_rotate_right_operation: assert property (
        @(posedge clk) (op == 4'b1001) |-> (Y == ({A[0], A[15:1]}))
    );

    // Any unlisted op code drives zero.
    check_default_zero_operation: assert property (
        @(posedge clk)
        ((op != 4'b0000) && (op != 4'b0001) && (op != 4'b0010) &&
         (op != 4'b0011) && (op != 4'b0100) && (op != 4'b0101) &&
         (op != 4'b0110) && (op != 4'b0111) && (op != 4'b1000) &&
         (op != 4'b1001)) |-> (Y == 16'h0000)
    );

endmodule