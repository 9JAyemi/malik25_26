module and3_not_A_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic X
);

    // X must equal the implemented NOT-A/AND-B-C function.
    check_output_function: assert property (
        @(posedge clk) X == ((~A) & B & C)
    );

    // A high forces X low.
    check_a_high_forces_x_low: assert property (
        @(posedge clk) A |-> !X
    );

    // B low forces X low.
    check_b_low_forces_x_low: assert property (
        @(posedge clk) !B |-> !X
    );

    // C low forces X low.
    check_c_low_forces_x_low: assert property (
        @(posedge clk) !C |-> !X
    );

    // A low with B and C high drives X high.
    check_a_low_with_b_c_high_drives_x_high: assert property (
        @(posedge clk) (!A && B && C) |-> X
    );

    // X high requires A to be low and B and C to be high.
    check_x_high_requires_inputs: assert property (
        @(posedge clk) X |-> (!A && B && C)
    );

endmodule