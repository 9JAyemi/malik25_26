module logic_operation_sva (
    input logic clk,
    input logic [1:0] logic_op_x,
    input logic [31:0] operand_0_x,
    input logic [31:0] operand_1_x,
    input logic [31:0] logic_result_x
);

    // AND opcode yields bitwise AND of operands.
    check_and_mapping: assert property (
        @(posedge clk) (logic_op_x == 2'b00) |-> (logic_result_x == (operand_0_x & operand_1_x))
    );

    // OR opcode yields bitwise OR of operands.
    check_or_mapping: assert property (
        @(posedge clk) (logic_op_x == 2'b01) |-> (logic_result_x == (operand_0_x | operand_1_x))
    );

    // XOR opcode yields bitwise XOR of operands.
    check_xor_mapping: assert property (
        @(posedge clk) (logic_op_x == 2'b10) |-> (logic_result_x == (operand_0_x ^ operand_1_x))
    );

    // Default opcode (2'b11) yields zero.
    check_default_zero: assert property (
        @(posedge clk) (logic_op_x == 2'b11) |-> (logic_result_x == 32'h0000_0000)
    );

    // Output stable across cycles when all inputs are stable.
    check_output_stable_when_inputs_stable: assert property (
        @(posedge clk) ($stable(logic_op_x) && $stable(operand_0_x) && $stable(operand_1_x)) |-> $stable(logic_result_x)
    );

    // AND absorbing element: if any operand is zero, result is zero.
    check_and_zero_absorbing: assert property (
        @(posedge clk) (logic_op_x == 2'b00 && ((operand_0_x == 32'h0000_0000) || (operand_1_x == 32'h0000_0000))) |-> (logic_result_x == 32'h0000_0000)
    );

    // AND identity with all-ones on operand_0 passes operand_1.
    check_and_ones_identity_op0: assert property (
        @(posedge clk) (logic_op_x == 2'b00 && (operand_0_x == 32'hFFFF_FFFF)) |-> (logic_result_x == operand_1_x)
    );

    // AND identity with all-ones on operand_1 passes operand_0.
    check_and_ones_identity_op1: assert property (
        @(posedge clk) (logic_op_x == 2'b00 && (operand_1_x == 32'hFFFF_FFFF)) |-> (logic_result_x == operand_0_x)
    );

    // OR absorbing element: if any operand is all-ones, result is all-ones.
    check_or_ones_absorbing: assert property (
        @(posedge clk) (logic_op_x == 2'b01 && ((operand_0_x == 32'hFFFF_FFFF) || (operand_1_x == 32'hFFFF_FFFF))) |-> (logic_result_x == 32'hFFFF_FFFF)
    );

    // XOR with equal operands yields zero.
    check_xor_equal_operands_zero: assert property (
        @(posedge clk) (logic_op_x == 2'b10 && (operand_0_x == operand_1_x)) |-> (logic_result_x == 32'h0000_0000)
    );

endmodule