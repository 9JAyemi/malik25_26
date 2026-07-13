module mux2to1_txg_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic SEL,
    input logic Y
);

    // Y equals the implemented A & B & SEL logic.
    check_y_function: assert property (
        @(posedge clk) Y == (A & B & SEL)
    );

    // SEL low forces Y low.
    check_sel_low_forces_y_low: assert property (
        @(posedge clk) !SEL |-> !Y
    );

    // With SEL high, Y matches A & B.
    check_sel_high_y_matches_a_and_b: assert property (
        @(posedge clk) SEL |-> (Y == (A & B))
    );

    // A low forces Y low.
    check_a_low_forces_y_low: assert property (
        @(posedge clk) !A |-> !Y
    );

    // B low forces Y low.
    check_b_low_forces_y_low: assert property (
        @(posedge clk) !B |-> !Y
    );

    // All inputs high drive Y high.
    check_all_inputs_high_drive_y_high: assert property (
        @(posedge clk) (A & B & SEL) |-> Y
    );

endmodule