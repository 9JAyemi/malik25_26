module alu_sva (
    input logic clk,
    input logic [3:0] alu_ctl,
    input logic signed [31:0] A,
    input logic signed [31:0] B,
    input logic zero,
    input logic [31:0] result
);

    // zero must match whether result is zero.
    check_zero_flag_consistency: assert property (
        @(posedge clk) (zero == (result == 32'b0))
    );

    // alu_ctl 0001 selects signed addition.
    check_add_result: assert property (
        @(posedge clk) (alu_ctl == 4'b0001) |-> (result == (A + B))
    );

    // alu_ctl 0010 selects signed subtraction.
    check_sub_result: assert property (
        @(posedge clk) (alu_ctl == 4'b0010) |-> (result == (A - B))
    );

    // alu_ctl 0011 selects bitwise AND.
    check_and_result: assert property (
        @(posedge clk) (alu_ctl == 4'b0011) |-> (result == (A & B))
    );

    // alu_ctl 0100 selects bitwise OR.
    check_or_result: assert property (
        @(posedge clk) (alu_ctl == 4'b0100) |-> (result == (A | B))
    );

    // alu_ctl 0101 selects bitwise XOR.
    check_xor_result: assert property (
        @(posedge clk) (alu_ctl == 4'b0101) |-> (result == (A ^ B))
    );

    // alu_ctl 0110 selects bitwise NOR.
    check_nor_result: assert property (
        @(posedge clk) (alu_ctl == 4'b0110) |-> (result == ~(A | B))
    );

    // alu_ctl 0111 shifts B right by one bit.
    check_shift_right_result: assert property (
        @(posedge clk) (alu_ctl == 4'b0111) |-> (result == (B >> 1))
    );

    // alu_ctl 1000 places B[15:0] in the upper half and clears the lower half.
    check_upper_half_load_result: assert property (
        @(posedge clk) (alu_ctl == 4'b1000) |-> (result == {B[15:0], 16'b0})
    );

    // alu_ctl 1001 returns the signed less-than comparison in bit 0.
    check_signed_less_than_result: assert property (
        @(posedge clk) (alu_ctl == 4'b1001) |-> (result == {{31{1'b0}}, (A < B)})
    );

    // Any unlisted alu_ctl value drives result to zero.
    check_default_result_zero: assert property (
        @(posedge clk)
        !((alu_ctl == 4'b0001) || (alu_ctl == 4'b0010) || (alu_ctl == 4'b0011) ||
          (alu_ctl == 4'b0100) || (alu_ctl == 4'b0101) || (alu_ctl == 4'b0110) ||
          (alu_ctl == 4'b0111) || (alu_ctl == 4'b1000) || (alu_ctl == 4'b1001))
        |-> (result == 32'b0)
    );

endmodule