module and4_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic Y
);

    // Y must equal the AND of all four inputs.
    check_y_matches_and4: assert property (
        @(posedge clk) Y == (A & B & C & D)
    );

    // If all inputs are high, Y must be high.
    check_all_high_implies_y_high: assert property (
        @(posedge clk) (A & B & C & D) |-> Y
    );

    // If any input is low, Y must be low.
    check_any_low_implies_y_low: assert property (
        @(posedge clk) ((!A) || (!B) || (!C) || (!D)) |-> !Y
    );

endmodule