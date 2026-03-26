module alu_04_sva(
    input logic clk,
    input logic [3:0] Z,
    input logic [1:0] op,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] C
);

    // No reset in RTL; clk is a sampling clock for combinational checks.

    // op 00 selects 4-bit addition of A, B, and C.
    check_addition_result: assert property (
        @(posedge clk) (op == 2'b00) |-> (Z == (A + B + C))
    );

    // op 01 selects 4-bit subtraction of B and C from A.
    check_subtraction_result: assert property (
        @(posedge clk) (op == 2'b01) |-> (Z == (A - B - C))
    );

    // op 10 selects bitwise AND across A, B, and C.
    check_and_result: assert property (
        @(posedge clk) (op == 2'b10) |-> (Z == (A & B & C))
    );

    // op 11 selects bitwise OR across A, B, and C.
    check_or_result: assert property (
        @(posedge clk) (op == 2'b11) |-> (Z == (A | B | C))
    );

    // Stable inputs must keep the sampled output stable.
    check_stable_inputs_hold_output: assert property (
        @(posedge clk) $stable({op, A, B, C}) |-> $stable(Z)
    );

endmodule