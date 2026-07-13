module and_gate_enable_assertions (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic A4,
    input logic EN
);

    // Y equals EN-gated AND of A1, A2, A3, and A4.
    check_y_matches_enabled_and: assert property (
        @(posedge clk) Y == (EN & A1 & A2 & A3 & A4)
    );

    // All inputs high with EN high drives Y high.
    check_all_high_drives_y_high: assert property (
        @(posedge clk) (EN & A1 & A2 & A3 & A4) |-> Y
    );

    // Y high requires EN and all data inputs high.
    check_y_high_requires_all_inputs_high: assert property (
        @(posedge clk) Y |-> (EN & A1 & A2 & A3 & A4)
    );

    // EN low forces Y low.
    check_en_low_forces_y_low: assert property (
        @(posedge clk) !EN |-> !Y
    );

    // A1 low forces Y low.
    check_a1_low_forces_y_low: assert property (
        @(posedge clk) !A1 |-> !Y
    );

    // A2 low forces Y low.
    check_a2_low_forces_y_low: assert property (
        @(posedge clk) !A2 |-> !Y
    );

    // A3 low forces Y low.
    check_a3_low_forces_y_low: assert property (
        @(posedge clk) !A3 |-> !Y
    );

    // A4 low forces Y low.
    check_a4_low_forces_y_low: assert property (
        @(posedge clk) !A4 |-> !Y
    );

endmodule