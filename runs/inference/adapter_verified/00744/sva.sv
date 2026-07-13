module alu_16bit_sva (
    input logic        clk,
    input logic [15:0] A,
    input logic [15:0] B,
    input logic [3:0]  op,
    input logic [15:0] Y
);

// Addition opcode drives the sum of A and B.
    check_addition: assert property (
        @(posedge clk) (op == 4'b0000) |-> (Y == (A + B))
    );

// Subtraction opcode drives A minus B.
    check_subtraction: assert property (
        @(posedge clk) (op == 4'b0001) |-> (Y == (A - B))
    );

// AND opcode drives the bitwise AND of A and B.
    check_and_operation: assert property (
        @(posedge clk) (op == 4'b0010) |-> (Y == (A & B))
    );

// OR opcode drives the bitwise OR of A and B.
    check_or_operation: assert property (
        @(posedge clk) (op == 4'b0011) |-> (Y == (A | B))
    );

// XOR opcode drives the bitwise XOR of A and B.
    check_xor_operation: assert property (
        @(posedge clk) (op == 4'b0100) |-> (Y == (A ^ B))
    );

// NOT-A opcode drives the bitwise complement of A.
    check_not_a_operation: assert property (
        @(posedge clk) (op == 4'b0101) |-> (Y == (~A))
    );

// Shift-left opcode drives A shifted left by one bit.
    check_shift_left_operation: assert property (
        @(posedge clk) (op == 4'b0110) |-> (Y == ({A[14:0], 1'b0}))
    );

// Shift-right opcode drives A shifted right by one bit.
    check_shift_right_operation: assert property (
        @(posedge clk) (op == 4'b0111) |-> (Y == ({1'b0, A[15:1]}))
    );

// Rotate-left opcode drives A rotated left by one bit.
    check_rotate_left_operation: assert property (
        @(posedge clk) (op == 4'b1000) |-> (Y == ({A[14:0], A[15]}))
    );

// Rotate-right opcode drives A rotated right by one bit.
    check_rotate_right_operation: assert property (
        @(posedge clk) (op == 4'b1001) |-> (Y == ({A[0], A[15:1]}))
    );

// Any unimplemented opcode drives zero.
    check_default_zero: assert property (
        @(posedge clk) (op >= 4'b1010) |-> (Y == 16'h0000)
    );

endmodule
