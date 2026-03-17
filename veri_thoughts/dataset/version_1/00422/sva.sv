module logic_unit_sva (
    input logic        clk,
    input logic [31:0] opB,
    input logic [31:0] opA,
    input logic [1:0]  op,
    input logic [31:0] result
);

    // AND mode drives result with opA & opB.
    check_and_operation: assert property (
        @(posedge clk) disable iff (1'b0)
        (op == 2'b00) |-> (result == (opA & opB))
    );

    // OR mode drives result with opA | opB.
    check_or_operation: assert property (
        @(posedge clk) disable iff (1'b0)
        (op == 2'b01) |-> (result == (opA | opB))
    );

    // XOR mode drives result with opA ^ opB.
    check_xor_operation: assert property (
        @(posedge clk) disable iff (1'b0)
        (op == 2'b10) |-> (result == (opA ^ opB))
    );

    // NOR mode drives result with ~(opA | opB).
    check_nor_operation: assert property (
        @(posedge clk) disable iff (1'b0)
        (op == 2'b11) |-> (result == ~(opA | opB))
    );

    // Unchanged inputs and opcode keep the output unchanged.
    check_stable_inputs_stable_result: assert property (
        @(posedge clk) disable iff (1'b0)
        ($stable(opA) && $stable(opB) && $stable(op)) |-> $stable(result)
    );

    // Any output change must be caused by an input or opcode change.
    check_result_change_has_cause: assert property (
        @(posedge clk) disable iff (1'b0)
        $changed(result) |-> ($changed(opA) || $changed(opB) || $changed(op))
    );

endmodule