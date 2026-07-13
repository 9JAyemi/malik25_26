module calculator_sva (
    input logic CLK,
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [1:0] opcode,
    input logic [15:0] result
);
    // For opcode 00, result is zero-extended 8-bit sum of A and B.
    check_add_value: assert property (
        @(posedge CLK) (opcode == 2'b00) |-> (result == {8'h00, (A + B)})
    );

    // For opcode 01, result is zero-extended 8-bit difference A - B.
    check_sub_value: assert property (
        @(posedge CLK) (opcode == 2'b01) |-> (result == {8'h00, (A - B)})
    );

    // For opcode 10, result equals 16-bit product A * B.
    check_mul_value: assert property (
        @(posedge CLK) (opcode == 2'b10) |-> (result == (A * B))
    );

    // For opcode 11 with B!=0, result is zero-extended 8-bit quotient A / B.
    check_div_value: assert property (
        @(posedge CLK) (opcode == 2'b11) && (B != 8'h00) |-> (result == {8'h00, (A / B)})
    );

    // Multiply by zero on A yields 0.
    check_mul_zero_A: assert property (
        @(posedge CLK) (opcode == 2'b10) && (A == 8'h00) |-> (result == 16'h0000)
    );

    // Multiply by zero on B yields 0.
    check_mul_zero_B: assert property (
        @(posedge CLK) (opcode == 2'b10) && (B == 8'h00) |-> (result == 16'h0000)
    );

    // Addition with A == 0 returns zero-extended B.
    check_add_zero_A: assert property (
        @(posedge CLK) (opcode == 2'b00) && (A == 8'h00) |-> (result == {8'h00, B})
    );

    // Addition with B == 0 returns zero-extended A.
    check_add_zero_B: assert property (
        @(posedge CLK) (opcode == 2'b00) && (B == 8'h00) |-> (result == {8'h00, A})
    );

    // Subtraction with A == B yields zero.
    check_sub_equal_zero: assert property (
        @(posedge CLK) (opcode == 2'b01) && (A == B) |-> (result == 16'h0000)
    );

    // Division by one returns zero-extended A.
    check_div_by_one: assert property (
        @(posedge CLK) (opcode == 2'b11) && (B == 8'h01) |-> (result == {8'h00, A})
    );
endmodule