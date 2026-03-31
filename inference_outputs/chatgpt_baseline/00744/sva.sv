module alu_16bit_sva (
    input logic clk,
    input logic [15:0] A,
    input logic [15:0] B,
    input logic [3:0] op,
    input logic [15:0] Y
);
    // op=0000: Y equals A + B
    check_add: assert property (
        @(posedge clk) disable iff (1'b0) (op == 4'b0000) |-> (Y == A + B)
    );
    // op=0001: Y equals A - B
    check_sub: assert property (
        @(posedge clk) disable iff (1'b0) (op == 4'b0001) |-> (Y == A - B)
    );
    // op=0010: Y equals A & B
    check_and: assert property (
        @(posedge clk) disable iff (1'b0) (op == 4'b0010) |-> (Y == (A & B))
    );
    // op=0011: Y equals A | B
    check_or: assert property (
        @(posedge clk) disable iff (1'b0) (op == 4'b0011) |-> (Y == (A | B))
    );
    // op=0100: Y equals A ^ B
    check_xor: assert property (
        @(posedge clk) disable iff (1'b0) (op == 4'b0100) |-> (Y == (A ^ B))
    );
    // op=0101: Y equals bitwise NOT of A
    check_notA: assert property (
        @(posedge clk) disable iff (1'b0) (op == 4'b0101) |-> (Y == ~A)
    );
    // op=0110: Y equals A shifted left by 1 with LSB=0
    check_shift_left: assert property (
        @(posedge clk) disable iff (1'b0) (op == 4'b0110) |-> (Y == {A[14:0], 1'b0})
    );
    // op=0111: Y equals A shifted right by 1 with MSB=0
    check_shift_right: assert property (
        @(posedge clk) disable iff (1'b0) (op == 4'b0111) |-> (Y == {1'b0, A[15:1]})
    );
    // op=1000: Y equals A rotated left by 1
    check_rotate_left: assert property (
        @(posedge clk) disable iff (1'b0) (op == 4'b1000) |-> (Y == {A[14:0], A[15]})
    );
    // op=1001: Y equals A rotated right by 1
    check_rotate_right: assert property (
        @(posedge clk) disable iff (1'b0) (op == 4'b1001) |-> (Y == {A[0], A[15:1]})
    );
    // Default case: Y is zero for unimplemented opcodes (1010..1111)
    check_default_zero: assert property (
        @(posedge clk) disable iff (1'b0) (op inside {[4'hA:4'hF]}) |-> (Y == 16'b0)
    );
endmodule