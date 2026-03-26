module xor3_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic Y,
    input logic nand1_out,
    input logic nand2_out
);

    // First NAND implements ~(A & B).
    check_nand1_function: assert property (
        @(posedge clk) nand1_out == ~(A & B)
    );

    // Second NAND implements ~(nand1_out & C).
    check_nand2_function: assert property (
        @(posedge clk) nand2_out == ~(nand1_out & C)
    );

    // Final self-NAND inverts nand2_out onto Y.
    check_output_inverter_function: assert property (
        @(posedge clk) Y == ~(nand2_out & nand2_out)
    );

    // Y is the AND of C and nand1_out.
    check_output_equals_c_and_nand1: assert property (
        @(posedge clk) Y == (nand1_out & C)
    );

    // End-to-end output is C & ~(A & B).
    check_output_boolean_function: assert property (
        @(posedge clk) Y == (C & ~(A & B))
    );

    // C low forces Y low.
    check_c_low_forces_y_low: assert property (
        @(posedge clk) (C == 1'b0) |-> (Y == 1'b0)
    );

    // With C high, Y reduces to ~(A & B).
    check_c_high_reduces_to_not_ab: assert property (
        @(posedge clk) (C == 1'b1) |-> (Y == ~(A & B))
    );

    // A and B both high force Y low.
    check_ab_high_forces_y_low: assert property (
        @(posedge clk) ((A == 1'b1) && (B == 1'b1)) |-> (Y == 1'b0)
    );

    // C high with either A or B low forces Y high.
    check_c_high_and_not_ab_drives_y_high: assert property (
        @(posedge clk) ((C == 1'b1) && ((A == 1'b0) || (B == 1'b0))) |-> (Y == 1'b1)
    );

endmodule