module alu_sva (
    input logic clk,
    input logic [3:0] alu_ctl,
    input logic signed [31:0] A,
    input logic signed [31:0] B,
    input logic zero,
    input logic [31:0] result
);

    // zero must reflect whether result is zero.
    check_zero_matches_result: assert property (
        @(posedge clk) zero == (result == 32'd0)
    );

    // ADD mode computes A + B.
    check_add_mode: assert property (
        @(posedge clk) (alu_ctl == 4'b0001) |-> (result == (A + B))
    );

    // SUB mode computes A - B.
    check_sub_mode: assert property (
        @(posedge clk) (alu_ctl == 4'b0010) |-> (result == (A - B))
    );

    // AND mode computes A & B.
    check_and_mode: assert property (
        @(posedge clk) (alu_ctl == 4'b0011) |-> (result == (A & B))
    );

    // OR mode computes A | B.
    check_or_mode: assert property (
        @(posedge clk) (alu_ctl == 4'b0100) |-> (result == (A | B))
    );

    // XOR mode computes A ^ B.
    check_xor_mode: assert property (
        @(posedge clk) (alu_ctl == 4'b0101) |-> (result == (A ^ B))
    );

    // NOR mode computes ~(A | B).
    check_nor_mode: assert property (
        @(posedge clk) (alu_ctl == 4'b0110) |-> (result == ~(A | B))
    );

    // SRA mode computes B >> 1.
    check_sra_mode: assert property (
        @(posedge clk) (alu_ctl == 4'b0111) |-> (result == (B >> 1))
    );

    // SLL mode computes zero-extended B[15:0].
    check_sll_mode: assert property (
        @(posedge clk) (alu_ctl == 4'b1000) |-> (result == {B[15:0], 16'd0})
    );

    // LT mode computes A < B.
    check_lt_mode: assert property (
        @(posedge clk) (alu_ctl == 4'b1001) |-> (result == ((A < B) ? 32'd1 : 32'd0))
    );

    // Unsupported opcodes drive zero and zero-extend the opcode.
    check_default_mode: assert property (
        @(posedge clk) ((alu_ctl != 4'b0001) && (alu_ctl != 4'b0010) && (alu_ctl != 4'b0011) &&
                        (alu_ctl != 4'b0100) && (alu_ctl != 4'b0101) && (alu_ctl != 4'b0110) &&
                        (alu_ctl != 4'b0111) && (alu_ctl != 4'b1000) && (alu_ctl != 4'b1001))
        |-> ((result == {24'd0, alu_ctl}) && (zero == 1'b0))
    );

endmodule