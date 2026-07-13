module alu_sva (
    input logic        clk,
    input logic [3:0]  alu_ctl,
    input logic signed [31:0] A,
    input logic signed [31:0] B,
    input logic        zero,
    input logic signed [31:0] result
);

    // No RTL clock or reset; sample combinational behavior on clk.

    // Add opcode drives result to A + B.
    check_add_result: assert property (
        @(posedge clk) (alu_ctl == 4'b0001) |-> (result == (A + B))
    );

    // Subtract opcode drives result to A - B.
    check_sub_result: assert property (
        @(posedge clk) (alu_ctl == 4'b0010) |-> (result == (A - B))
    );

    // AND opcode drives result to A & B.
    check_and_result: assert property (
        @(posedge clk) (alu_ctl == 4'b0011) |-> (result == (A & B))
    );

    // OR opcode drives result to A | B.
    check_or_result: assert property (
        @(posedge clk) (alu_ctl == 4'b0100) |-> (result == (A | B))
    );

    // XOR opcode drives result to A ^ B.
    check_xor_result: assert property (
        @(posedge clk) (alu_ctl == 4'b0101) |-> (result == (A ^ B))
    );

    // NOR opcode drives result to ~(A | B).
    check_nor_result: assert property (
        @(posedge clk) (alu_ctl == 4'b0110) |-> (result == ~(A | B))
    );

    // Logical right shift opcode drives result to B >> 1.
    check_srl_result: assert property (
        @(posedge clk) (alu_ctl == 4'b0111) |-> (result == (B >> 1))
    );

    // Zero-extend opcode drives result to {B[15:0], 16'b0}.
    check_zext_result: assert property (
        @(posedge clk) (alu_ctl == 4'b1000) |-> (result == {B[15:0], 16'b0})
    );

    // Less-than opcode drives result to (A < B).
    check_lt_result: assert property (
        @(posedge clk) (alu_ctl == 4'b1001) |-> (result == (A < B))
    );

    // Default opcode drives result to zero.
    check_default_result: assert property (
        @(posedge clk) (alu_ctl[3] == 1'b1) |-> (result == 32'sd0)
    );

    // Zero flag matches whether result is zero.
    check_zero_flag: assert property (
        @(posedge clk) zero == (result == 32'sd0)
    );

endmodule