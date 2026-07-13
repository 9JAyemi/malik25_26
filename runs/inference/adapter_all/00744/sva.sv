module alu_16bit_sva (
    input logic        clk,
    input logic [15:0] A,
    input logic [15:0] B,
    input logic [3:0]  op,
    input logic [15:0] Y
);

    // op 0000 selects addition.
    check_add_result: assert property (
        @(posedge clk) (op == 4'b0000) |-> (Y == (A + B))
    );

    // op 0001 selects subtraction.
    check_sub_result: assert property (
        @(posedge clk) (op == 4'b0001) |-> (Y == (A - B))
    );

    // op 0010 selects bitwise AND.
    check_and_result: assert property (
        @(posedge clk) (op == 4'b0010) |-> (Y == (A & B))
    );

    // op 0011 selects bitwise OR.
    check_or_result: assert property (
        @(posedge clk) (op == 4'b0011) |-> (Y == (A | B))
    );

    // op 0100 selects bitwise XOR.
    check_xor_result: assert property (
        @(posedge clk) (op == 4'b0100) |-> (Y == (A ^ B))
    );

    // op 0101 selects bitwise NOT of A.
    check_not_a_result: assert property (
        @(posedge clk) (op == 4'b0101) |-> (Y == (~A))
    );

    // op 0110 selects left shift by 1.
    check_shift_left_result: assert property (
        @(posedge clk) (op == 4'b0110) |-> (Y == ({A[14:0], 1'b0}))
    );

    // op 0111 selects right shift by 1.
    check_shift_right_result: assert property (
        @(posedge clk) (op == 4'b0111) |-> (Y == ({1'b0, A[15:1]}))
    );

    // op 1000 selects left rotate by 1.
    check_rotate_left_result: assert property (
        @(posedge clk) (op == 4'b1000) |-> (Y == ({A[14:0], A[15]}))
    );

    // op 1001 selects right rotate by 1.
    check_rotate_right_result: assert property (
        @(posedge clk) (op == 4'b1001) |-> (Y == ({A[0], A[15:1]}))
    );

    // Any unsupported op code drives zero.
    check_default_zero_result: assert property (
        @(posedge clk) (op inside {4'b1010, 4'b1011, 4'b1100, 4'b1101, 4'b1110, 4'b1111}) |-> (Y == 16'h0000)
    );

endmodule