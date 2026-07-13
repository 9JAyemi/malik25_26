module four_input_and_sva (
    input logic clk,
    input logic A1,
    input logic A2,
    input logic B1_N,
    input logic C1,
    input logic X
);

    // X must match the implemented AND function.
    check_x_matches_function: assert property (
        @(posedge clk) X == (A1 & A2 & ~B1_N)
    );

    // A low A1 input forces X low.
    check_a1_low_forces_x_low: assert property (
        @(posedge clk) !A1 |-> !X
    );

    // A low A2 input forces X low.
    check_a2_low_forces_x_low: assert property (
        @(posedge clk) !A2 |-> !X
    );

    // A high B1_N input forces X low.
    check_b1n_high_forces_x_low: assert property (
        @(posedge clk) B1_N |-> !X
    );

    // With A1 and A2 high and B1_N low, X must be high.
    check_all_enables_drive_x_high: assert property (
        @(posedge clk) (A1 && A2 && !B1_N) |-> X
    );

    // A high X requires A1 and A2 to be high and B1_N to be low.
    check_x_high_requires_inputs: assert property (
        @(posedge clk) X |-> (A1 && A2 && !B1_N)
    );

endmodule