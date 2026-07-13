module and_en_sva(
    input logic clk,
    input logic A,
    input logic B,
    input logic C1,
    input logic Y
);

    // Y equals the enabled AND of A and B.
    check_y_matches_and_enable: assert property (
        @(posedge clk) Y == (A & B & C1)
    );

    // Y high requires all three inputs high.
    check_y_high_requires_all_inputs_high: assert property (
        @(posedge clk) Y |-> (A && B && C1)
    );

    // All three inputs high drive Y high.
    check_all_inputs_high_drive_y_high: assert property (
        @(posedge clk) (A && B && C1) |-> Y
    );

    // C1 low forces Y low.
    check_c1_low_forces_y_low: assert property (
        @(posedge clk) !C1 |-> !Y
    );

    // A low forces Y low.
    check_a_low_forces_y_low: assert property (
        @(posedge clk) !A |-> !Y
    );

    // B low forces Y low.
    check_b_low_forces_y_low: assert property (
        @(posedge clk) !B |-> !Y
    );

    // With C1 high, Y matches the AND of A and B.
    check_c1_high_passes_and_result: assert property (
        @(posedge clk) C1 |-> (Y == (A & B))
    );

endmodule