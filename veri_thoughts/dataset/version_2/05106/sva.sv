module BinaryMultiplier_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic Z
);

    // External sampling clock for this combinational DUT.

    // Z matches the implemented OR of A and B.
    check_z_is_or_of_inputs: assert property (
        @(posedge clk) Z == (A | B)
    );

    // Input 00 drives Z low.
    check_zero_zero_case: assert property (
        @(posedge clk) (!A && !B) |-> !Z
    );

    // Input 01 drives Z high.
    check_zero_one_case: assert property (
        @(posedge clk) (!A && B) |-> Z
    );

    // Input 10 drives Z high.
    check_one_zero_case: assert property (
        @(posedge clk) (A && !B) |-> Z
    );

    // Input 11 drives Z high.
    check_one_one_case: assert property (
        @(posedge clk) (A && B) |-> Z
    );

    // Z low can only occur for input 00.
    check_z_low_requires_both_inputs_low: assert property (
        @(posedge clk) !Z |-> (!A && !B)
    );

endmodule