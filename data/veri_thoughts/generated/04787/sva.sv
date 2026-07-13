module three_input_gate_assertions (
    input logic clk,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic Y
);

    // If A1 is low, the next registered output must be high.
    check_a1_low_forces_y_high: assert property (
        @(posedge clk) (!A1) |=> (Y == 1'b1)
    );

    // If A1 and A2 are high, the next registered output must be low.
    check_a1_a2_high_forces_y_low: assert property (
        @(posedge clk) (A1 && A2) |=> (Y == 1'b0)
    );

    // If B1 is selected and high, the next registered output must be high.
    check_selected_b1_high_passes_to_y: assert property (
        @(posedge clk) (A1 && !A2 && B1) |=> (Y == 1'b1)
    );

    // If B1 is selected and low, the next registered output must be low.
    check_selected_b1_low_passes_to_y: assert property (
        @(posedge clk) (A1 && !A2 && !B1) |=> (Y == 1'b0)
    );

endmodule