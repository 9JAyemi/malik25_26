module arithmetic_sva (
    input logic clk,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [1:0] opcode,
    input logic [7:0] result
);
    // For opcode 00, result equals a+b (8-bit truncation).
    check_add_result: assert property (
        @(posedge clk) (opcode == 2'b00) |-> (result == (a + b)[7:0])
    );

    // For opcode 01, result equals a-b (8-bit truncation).
    check_sub_result: assert property (
        @(posedge clk) (opcode == 2'b01) |-> (result == (a - b)[7:0])
    );

    // For opcode 10, result equals a & b.
    check_and_result: assert property (
        @(posedge clk) (opcode == 2'b10) |-> (result == (a & b))
    );

    // For opcode 11, result equals a | b.
    check_or_result: assert property (
        @(posedge clk) (opcode == 2'b11) |-> (result == (a | b))
    );

    // For invalid opcode (X/Z), result drives 0.
    check_invalid_opcode_zero: assert property (
        @(posedge clk) ((opcode !== 2'b00) && (opcode !== 2'b01) && (opcode !== 2'b10) && (opcode !== 2'b11)) |-> (result == 8'h00)
    );

    // If inputs are stable, result remains stable.
    check_result_stable_when_inputs_stable: assert property (
        @(posedge clk) ($stable(a) && $stable(b) && $stable(opcode)) |-> $stable(result)
    );

    // AND result is subset of both inputs.
    check_and_subset_of_inputs: assert property (
        @(posedge clk) (opcode == 2'b10) |-> (((result & ~a) == 8'h00) && ((result & ~b) == 8'h00))
    );

    // OR result is superset of both inputs.
    check_or_superset_of_inputs: assert property (
        @(posedge clk) (opcode == 2'b11) |-> (((a & ~result) == 8'h00) && ((b & ~result) == 8'h00))
    );

    // Addition identity: adding zero returns a.
    check_add_identity_zero: assert property (
        @(posedge clk) ((opcode == 2'b00) && (b == 8'h00)) |-> (result == a)
    );

    // Subtraction of equal operands yields zero.
    check_sub_equal_operands_zero: assert property (
        @(posedge clk) ((opcode == 2'b01) && (a == b)) |-> (result == 8'h00)
    );
endmodule