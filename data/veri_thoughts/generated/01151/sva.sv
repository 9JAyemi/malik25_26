module alu_sva (
    input logic [31:0] a,
    input logic [31:0] b,
    input logic [3:0]  ctrl,
    input logic [31:0] result,
    input logic        carry_out,
    input logic        zero
);
    // Combinational ALU with no clock/reset; assertions are clocked on $global_clock.

    // Addition result when ctrl==0000.
    check_add_result: assert property (
        @(posedge $global_clock) (ctrl == 4'b0000) |-> (result == (a + b))
    );

    // Subtraction result when ctrl==0001.
    check_sub_result: assert property (
        @(posedge $global_clock) (ctrl == 4'b0001) |-> (result == (a - b))
    );

    // Bitwise AND result when ctrl==0010.
    check_and_result: assert property (
        @(posedge $global_clock) (ctrl == 4'b0010) |-> (result == (a & b))
    );

    // Bitwise OR result when ctrl==0011.
    check_or_result: assert property (
        @(posedge $global_clock) (ctrl == 4'b0011) |-> (result == (a | b))
    );

    // Bitwise XOR result when ctrl==0100.
    check_xor_result: assert property (
        @(posedge $global_clock) (ctrl == 4'b0100) |-> (result == (a ^ b))
    );

    // Logical shift left by b[4:0] when ctrl==0101.
    check_sll_result: assert property (
        @(posedge $global_clock) (ctrl == 4'b0101) |-> (result == (a << b[4:0]))
    );

    // Logical shift right by b[4:0] when ctrl==0110.
    check_srl_result: assert property (
        @(posedge $global_clock) (ctrl == 4'b0110) |-> (result == (a >> b[4:0]))
    );

    // Default case drives result to zero for all other ctrl values.
    check_default_zero_result: assert property (
        @(posedge $global_clock) (!(ctrl inside {4'b0000,4'b0001,4'b0010,4'b0011,4'b0100,4'b0101,4'b0110})) |-> (result == 32'd0)
    );

    // carry_out equals MSB of result for add/sub.
    check_carry_for_add_sub: assert property (
        @(posedge $global_clock) ((ctrl == 4'b0000) || (ctrl == 4'b0001)) |-> (carry_out == (result[31] == 1'b1))
    );

    // carry_out is zero for non add/sub operations.
    check_carry_zero_for_others: assert property (
        @(posedge $global_clock) (!(ctrl inside {4'b0000,4'b0001})) |-> (carry_out == 1'b0)
    );

    // zero flag is 1 iff result is zero.
    check_zero_flag_true_when_result_zero: assert property (
        @(posedge $global_clock) (result == 32'd0) |-> (zero == 1'b1)
    );

    // zero flag is 0 iff result is nonzero.
    check_zero_flag_false_when_result_nonzero: assert property (
        @(posedge $global_clock) (result != 32'd0) |-> (zero == 1'b0)
    );

endmodule