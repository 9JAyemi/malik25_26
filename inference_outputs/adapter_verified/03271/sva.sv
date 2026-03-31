module alu_sva (
    input logic clk,
    input logic [3:0] alu_ctl,
    input logic signed [31:0] A,
    input logic signed [31:0] B,
    input logic zero,
    input logic [31:0] result
);

// Zero flag matches result being zero.
    check_zero_matches_result_zero: assert property (
        @(posedge clk) (zero == (result == 32'd0))
    );

// ALU opcode 0001 adds A and B.
    check_add_result: assert property (
        @(posedge clk) (alu_ctl == 4'b0001) |-> (result == (A + B))
    );

// ALU opcode 0010 subtracts B from A.
    check_sub_result: assert property (
        @(posedge clk) (alu_ctl == 4'b0010) |-> (result == (A - B))
    );

// ALU opcode 0011 performs bitwise AND.
    check_and_result: assert property (
        @(posedge clk) (alu_ctl == 4'b0011) |-> (result == (A & B))
    );

// ALU opcode 0100 performs bitwise OR.
    check_or_result: assert property (
        @(posedge clk) (alu_ctl == 4'b0100) |-> (result == (A | B))
    );

// ALU opcode 0101 performs bitwise XOR.
    check_xor_result: assert property (
        @(posedge clk) (alu_ctl == 4'b0101) |-> (result == (A ^ B))
    );

// ALU opcode 0110 performs bitwise NOR.
    check_nor_result: assert property (
        @(posedge clk) (alu_ctl == 4'b0110) |-> (result == ~(A | B))
    );

// ALU opcode 0111 shifts B right by one bit.
    check_shift_right_result: assert property (
        @(posedge clk) (alu_ctl == 4'b0111) |-> (result == (B >> 1))
    );

// ALU opcode 1000 shifts B left by 16 bits.
    check_shift_left_result: assert property (
        @(posedge clk) (alu_ctl == 4'b1000) |-> (result == {B[15:0], 16'd0})
    );

// ALU opcode 1001 compares A and B (signed).
    check_lt_result: assert property (
        @(posedge clk) (alu_ctl == 4'b1001) |-> (result == ((A < B) ? 32'd1 : 32'd0))
    );

// Default opcode 1111 drives zero and zero-extended result.
    check_default_result: assert property (
        @(posedge clk) (alu_ctl == 4'b1111) |-> ((result == 32'd0) && (zero == 1'b1))
    );

endmodule
