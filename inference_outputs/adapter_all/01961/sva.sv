module and3_not_A_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic X
);

    // X must match the implemented combinational function.
    check_x_matches_function: assert property (
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

    // With A low and both B and C high, X must be high.
    check_all_enables_drive_x_high: assert property (
        @(posedge clk) (!A && B && C) |-> X
    );

    // X high requires A low and both B and C high.
    check_x_high_requires_all_enables: assert property (
        @(posedge clk) X |-> (!A && B && C)
    );

endmodule