module alu2_sva(
    input logic        clk,
    input logic [31:0] srca,
    input logic [31:0] srcb,
    input logic [1:0]  alucontrol,
    input logic [31:0] aluresult,
    input logic [3:0]  aluflags
);

    // External sampling clock for this combinational DUT; no reset exists in the RTL.

    // Add mode drives result and carry from srca + srcb.
    check_add_result_and_carry: assert property (
        @(posedge clk)
        (alucontrol == 2'b00) |-> ({aluflags[1], aluresult} == ({1'b0, srca} + {1'b0, srcb}))
    );

    // Subtract mode drives result and carry from srca + ~srcb + 1.
    check_sub_result_and_carry: assert property (
        @(posedge clk)
        (alucontrol == 2'b01) |-> ({aluflags[1], aluresult} == ({1'b0, srca} + {1'b0, ~srcb} + 33'd1))
    );

    // AND mode returns the bitwise AND of the operands.
    check_and_result: assert property (
        @(posedge clk)
        (alucontrol == 2'b10) |-> (aluresult == (srca & srcb))
    );

    // OR mode returns the bitwise OR of the operands.
    check_or_result: assert property (
        @(posedge clk)
        (alucontrol == 2'b11) |-> (aluresult == (srca | srcb))
    );

    // Logical modes force the carry flag low.
    check_logic_modes_clear_carry: assert property (
        @(posedge clk)
        alucontrol[1] |-> (aluflags[1] == 1'b0)
    );

    // Flag[3] reflects the result sign bit.
    check_negative_flag: assert property (
        @(posedge clk)
        (aluflags[3] == aluresult[31])
    );

    // Flag[2] reflects whether the result is zero.
    check_zero_flag: assert property (
        @(posedge clk)
        (aluflags[2] == (aluresult == 32'b0))
    );

    // Flag[0] follows the implemented overflow equation.
    check_overflow_flag: assert property (
        @(posedge clk)
        (aluflags[0] == ((~(alucontrol[0] ^ srca[31] ^ srca[31])) & (~alucontrol[1]) & (aluresult[31] ^ srca[31])))
    );

endmodule