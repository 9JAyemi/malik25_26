module calculator_assertions (
    input logic clk,
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [1:0] opcode,
    input logic en,
    input logic [7:0] R
);

    // No RTL clock/reset; sample this combinational logic on an external clock.

    // When disabled, the result is forced to zero.
    check_disable_forces_zero: assert property (
        @(posedge clk) !en |-> (R == 8'h00)
    );

    // Opcode 00 performs 8-bit addition when enabled.
    check_addition_result: assert property (
        @(posedge clk) en && (opcode == 2'b00) |-> (R == ((A + B) & 8'hFF))
    );

    // Opcode 01 performs 8-bit subtraction when enabled.
    check_subtraction_result: assert property (
        @(posedge clk) en && (opcode == 2'b01) |-> (R == ((A - B) & 8'hFF))
    );

    // Opcode 10 performs 8-bit truncated multiplication when enabled.
    check_multiplication_result: assert property (
        @(posedge clk) en && (opcode == 2'b10) |-> (R == ((A * B) & 8'hFF))
    );

    // Opcode 11 performs division when enabled with a nonzero divisor.
    check_division_result: assert property (
        @(posedge clk) en && (opcode == 2'b11) && (B != 8'h00) |-> (R == ((A / B) & 8'hFF))
    );

endmodule