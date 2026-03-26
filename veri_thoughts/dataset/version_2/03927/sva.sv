module calculator_sva (
    input logic        clk,
    input logic [31:0] A,
    input logic [31:0] B,
    input logic [1:0]  OPCODE,
    input logic        RESET,
    input logic [31:0] RESULT
);

    // Reset forces the output to zero.
    check_reset_forces_zero: assert property (
        @(posedge clk) RESET |-> (RESULT == 32'd0)
    );

    // Opcode 00 selects addition.
    check_add_operation: assert property (
        @(posedge clk) disable iff (RESET)
        (OPCODE == 2'b00) |-> (RESULT == (A + B))
    );

    // Opcode 01 selects subtraction.
    check_sub_operation: assert property (
        @(posedge clk) disable iff (RESET)
        (OPCODE == 2'b01) |-> (RESULT == (A - B))
    );

    // Opcode 10 selects multiplication.
    check_mul_operation: assert property (
        @(posedge clk) disable iff (RESET)
        (OPCODE == 2'b10) |-> (RESULT == (A * B))
    );

    // Opcode 11 selects division when the divisor is nonzero.
    check_div_operation: assert property (
        @(posedge clk) disable iff (RESET)
        ((OPCODE == 2'b11) && (B != 32'd0)) |-> (RESULT == (A / B))
    );

endmodule