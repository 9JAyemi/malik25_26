module alu_sva(
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [2:0] Op,
    input logic [3:0] result
);

    // Addition opcode produces A + B.
    check_addition_result: assert property (
        @(posedge clk)
        (Op == 3'b000) |-> (result == (A + B))
    );

    // Subtraction opcode produces A - B.
    check_subtraction_result: assert property (
        @(posedge clk)
        (Op == 3'b001) |-> (result == (A - B))
    );

    // AND opcode produces A & B.
    check_and_result: assert property (
        @(posedge clk)
        (Op == 3'b010) |-> (result == (A & B))
    );

    // OR opcode produces A | B.
    check_or_result: assert property (
        @(posedge clk)
        (Op == 3'b011) |-> (result == (A | B))
    );

    // XOR opcode produces A ^ B.
    check_xor_result: assert property (
        @(posedge clk)
        (Op == 3'b100) |-> (result == (A ^ B))
    );

    // Shift-left opcode produces A shifted left by one.
    check_shift_left_result: assert property (
        @(posedge clk)
        (Op == 3'b101) |-> (result == (A << 1))
    );

    // Shift-right opcode produces A shifted right by one.
    check_shift_right_result: assert property (
        @(posedge clk)
        (Op == 3'b110) |-> (result == (A >> 1))
    );

    // Increment opcode produces A + 1.
    check_increment_result: assert property (
        @(posedge clk)
        (Op == 3'b111) |-> (result == (A + 1))
    );

    // Stable inputs keep the combinational result stable.
    check_result_stable_when_inputs_stable: assert property (
        @(posedge clk)
        $stable({A, B, Op}) |-> $stable(result)
    );

endmodule